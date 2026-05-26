# =============================================================================
#  trial3_phase3.jl  --  Amortized per-target DLP solver (Phase 3)
#
#  Phase 3 takes the tables produced by Phase 2's β=0 precomputation and
#  solves discrete logarithms for one or more target divisors T_i = k_i · G.
#
#  ARCHITECTURE
#  ────────────
#  The precompute phase built:
#    • atom_log_dict   : pt → log_G(pt) ∈ Z/ell  for every FB atom
#    • shared_lp1_pre  : 1-LP table (lp_pt → stored partial relation)
#    • shared_lp2_pre  : LP2 spanning-tree graph (affine)
#    • shared_lp1_conj_pre, shared_lp2_conj_pre  : extension-field analogues
#
#  For each target T, we run a β≠0 walk and look for relations of the form
#
#       fb_row  ≡  neg_al · G  +  neg_be · T       (*)
#
#  where fb_row is a pure FB row (all atoms in atom_log_dict).  Substituting
#  known logs:
#
#       log_sum  =  neg_al  +  neg_be · k   (mod ell)
#       k  =  (log_sum − neg_al) · neg_be⁻¹   mod ell
#
#  CLOSURE STRATEGIES (fastest to slowest)
#  ────────────────────────────────────────
#  Strategy 0 — Direct 0-LP:
#    All three of {P0, R, S} are in atom_log_dict → solve immediately.
#    Rate ≈ (|FB|/p)²  per valid step.
#
#  Strategy 1 — 1-LP closure against shared_lp1_pre:
#    Exactly one of {P0, R, S} is not in atom_log_dict (call it lp_pt).
#    We check: is lp_pt already stored in shared_lp1_pre from the β=0 walk?
#    If so, the precompute entry gives:
#        atom(lp_pt) + fb_row_pre  ≡  neg_al_pre · G       (β_pre = 0)
#    Combining with the current β≠0 step:
#        atom(lp_pt) + fb_row_cur  ≡  neg_al_cur · G  +  neg_be_cur · T
#    Subtracting eliminates lp_pt, yielding a pure FB relation with β≠0:
#        (fb_row_cur − fb_row_pre)  ≡  (neg_al_cur − neg_al_pre) · G
#                                       +  neg_be_cur · T
#    This has rate ≈ 2·(|FB|/p)·(|lp1_pre|/p) per valid step.
#    Since |lp1_pre| ≈ |FB| at precompute end, this is ~2× the 0-LP rate —
#    but the lp1_pre table can be much larger if the precompute ran long, so
#    the real gain is multiplicative in table density.
#
#  Strategy 2 — Local 1-LP birthday:
#    Maintain a small per-trial lp1 dict.  When two steps share the same
#    lp_pt the LP atom cancels and we get a pure FB relation.  Expected
#    closure at √(p/|FB|) ≈ 32 steps for our parameters.  This is the
#    fallback when shared_lp1_pre doesn't have the key.
#
#  PARALLELISM
#  ───────────
#  We parallelize over targets with Threads.@spawn.  The shared_lp1_pre
#  table is READ ONLY after precompute — no locking needed.  Each trial
#  owns its own local lp1 dict, alpha/beta accumulators, and walk state.
#
#  EXPORTED INTERFACE
#  ──────────────────
#    Phase2Tables      — struct bundling everything phase2 hands to phase3
#    phase3_solve_targets(tables, targets, G, ell; ...) → Vector{Phase3Result}
# =============================================================================

# ---------------------------------------------------------------------------
#  Phase2Tables  —  everything phase 3 needs from the precompute
# ---------------------------------------------------------------------------
struct Phase2Tables
    # Factor base
    fb             ::Vector{NTuple{2,Int}}
    pt2idx         ::Dict{NTuple{2,Int}, Int}

    # Solved atom logs: pt → log_G(pt) mod ell
    atom_log_dict  ::Dict{NTuple{2,Int}, Int}

    # LP tables from the β=0 walk (READ ONLY in phase 3)
    # shared_lp1 entry: lp_pt → (fb_row::Dict{Int,Int}, neg_al::Int, neg_be::Int, step::Int)
    # Here neg_be is always 0 (β=0 walk), but we keep the full tuple for uniformity.
    shared_lp1     ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}}
    shared_lp2     ::LP2Graph

    # Extension-field LP tables (optional; may be empty)
    # Stored as a plain Dict snapshot — the LSM is closed and freed in main2
    # before Phase2Tables is constructed, so this field never holds the LSM.
    # Plain Dict: no locks, zero contention across all phase-3 worker threads.
    shared_lp1_conj::Dict{CanonicalLP1Key, LP1ConjVal}
    shared_lp2_conj::LP2ConjGraph

    # Group order
    ell            ::BigInt

    # IDEA 4: hot-basin anchor indices from the precompute walk.
    hot_basin_anchors ::Vector{Int}

    # β=0 relation rows and α coefficients from the precompute walk.
    # Used by phase3 to run cycle_union_solve and enrich atom_log_dict beyond
    # what the dense RREF recovered (the DSU label-propagation can pin atoms
    # that are graph-reachable from the RREF seeds even when algebraic rank is low).
    rel_rows_pre   ::Vector{Dict{Int,Int}}
    alpha_vec_pre  ::Vector{BigInt}

    # Empirical LP1-conj mean inter-arrival gap from the β=0 precompute walk,
    # measured in valid-phi-step units.  Used by phase3 to set burst-band
    # thresholds relative to the actual closure hazard scale, rather than
    # hard-coded step counts.
    # = total_valid_phi_steps / n_lp1_conj_steps  (not emissions — steps).
    # Set to 0.0 if no LP1-conj steps were observed (disables band scaling).
    lp1_conj_mean_gap_steps::Float64
end

# ---------------------------------------------------------------------------
#  Phase3Result  —  result record for a single target
# ---------------------------------------------------------------------------
struct Phase3Result
    target_idx      ::Int
    k_recovered     ::Union{Int, Nothing}
    k_true          ::Union{Int, Nothing}   # nothing if not a test run
    n_steps         ::Int
    n_0lp_hits      ::Int
    n_1lp_preclose  ::Int   # closures against shared_lp1_pre
    n_1lp_local     ::Int   # closures against local lp1 dict
    n_alog_extended ::Int   # new atom logs derived locally from β=0 closures
    elapsed_s       ::Float64
    success         ::Bool
end

# ---------------------------------------------------------------------------
#  phase3_trial_worker
#
#  Runs the β≠0 walk for a single target T and returns a Phase3Result.
#  Mirrors all LP branches from phase2_worker — conjugate and affine — but
#  instead of building shared tables, closes against the read-only precomputed
#  tables from Phase2Tables.  A small per-trial local lp1 dict provides
#  birthday-closure fallback for both affine and conj when the precomputed
#  table misses.
#
#  Branch structure (mirrors phase2_worker exactly):
#
#  BRANCH A — conjugate residual (!rs_split):
#    A1. i0 in FB → 1-LP-conj: close lp_key against shared_lp1_conj_pre
#        (shard lookup, read-only).  Fallback: local_lp1_conj birthday dict.
#    A2. i0 not in FB → 2-LP-conj: skip (no spanning tree in phase 3).
#
#  BRANCH B — split residual (rs_split):
#    B0. n_lp == 0 → 0-LP: direct solve from atom_log_dict.
#    B1. n_lp == 1 → 1-LP-affine: close lp_pt against shared_lp1_pre
#        (read-only).  Fallback: local_lp1_affine birthday dict.
#    B2. n_lp == 2 → 2-LP: skip.
#    B3. n_lp == 3 → discard.
# ---------------------------------------------------------------------------
function phase3_trial_worker(
        trial_idx        ::Int,
        T                ::Div2,
        k_true           ::Union{Int,Nothing},
        tables           ::Phase2Tables,
        G                ::Div2;
        step_cap         ::Int   = -1,   # -1 → auto-scaled via phase3_default_step_cap(ell)
        local_lp_cap     ::Int   = -1,   # -1 → auto-scaled via phase3_local_lp_cap(ell)
        n_steps_prebuilt ::Int   = 512,
        verbose          ::Bool  = false,
        conj_dict        ::Union{Dict{CanonicalLP1Key, LP1ConjVal}, Nothing} = nothing,
        hot_anchors      ::Union{Vector{Int}, Nothing} = nothing,
        seeded_rel_rows  ::Union{Vector{Dict{Int,Int}}, Nothing} = nothing,
        seeded_rel_be    ::Union{Vector{Int},           Nothing} = nothing,
        seeded_rel_al    ::Union{Vector{BigInt},        Nothing} = nothing,
        prebuilt_step_D  ::Union{Vector{Div2}, Nothing} = nothing,
        prebuilt_step_a  ::Union{Vector{Int},  Nothing} = nothing,
        prebuilt_step_b  ::Union{Vector{Int},  Nothing} = nothing)::Phase3Result

    t0    = time()
    # ── DIAG checkpoint helper (thread-safe: @printf is atomic per-call) ──────
    _cp(tag) = (@printf("[p3 trial %2d | %+8.3fs | %s]\n", trial_idx, time()-t0, tag); flush(stdout))

    @printf("[p3 trial %2d] worker entered on thread %d  seeded_rows=%d  seeded_al=%d\n",
            trial_idx, Threads.threadid(),
            seeded_rel_rows !== nothing ? length(seeded_rel_rows) : -1,
            seeded_rel_al   !== nothing ? length(seeded_rel_al)   : -1)
    flush(stdout)

    ell   = tables.ell
    ellI  = Int(ell)
    # mulmod: multiply two values that may each be O(ell) and reduce mod ellI.
    # For ell ~ 2^38 the product is ~2^76, which overflows Int64 (max 2^63-1).
    # widemul(Int64, Int64) -> Int128 is exact; the final mod fits back in Int64.
    @inline mulmod(a::Int, b::Int) = Int(mod(widemul(a, b), ellI))
    # step_cap and local_lp_cap are pre-computed in the main thread before spawning
    # to avoid 30 workers simultaneously calling isqrt(BigInt(ell)) via GMP.
    step_cap     = step_cap     < 0 ? phase3_default_step_cap(ell) : step_cap
    local_lp_cap = local_lp_cap < 0 ? phase3_local_lp_cap(ell)    : local_lp_cap
    pt2idx        = tables.pt2idx
    fb            = tables.fb
    nF            = length(fb)
    alog          = tables.atom_log_dict
    lp1_pre       = tables.shared_lp1        # READ ONLY — affine 1-LP
    # Use the pre-snapshotted plain Dict for conj lookups — no locks, no file_lock
    # contention across the 30+ simultaneous phase3 threads.
    lp1_conj_dict = conj_dict   # Dict{CanonicalLP1Key, LP1ConjVal} or nothing

    # ── Prebuilt step table for the β≠0 walk ─────────────────────────────────
    # If pre-built tables were passed in from the main thread (to avoid 30-way
    # GMP contention), use them directly.  Otherwise build locally (fallback).
    local step_D::Vector{Div2}
    local step_a::Vector{Int}
    local step_b::Vector{Int}
    if prebuilt_step_D !== nothing
        step_D = prebuilt_step_D
        step_a = prebuilt_step_a
        step_b = prebuilt_step_b
        @printf("[p3 trial %2d] using pre-built step table (%d steps)\n",
                trial_idx, length(step_D)); flush(stdout)
    else
        @printf("[p3 trial %2d] building step table (n_steps_prebuilt=%d)...\n",
                trial_idx, n_steps_prebuilt); flush(stdout)
        step_D = Vector{Div2}(undef, n_steps_prebuilt)
        step_a = Vector{Int}(undef,  n_steps_prebuilt)
        step_b = Vector{Int}(undef,  n_steps_prebuilt)
        for i in 1:n_steps_prebuilt
            a = rand(1:ellI-1); b = rand(1:ellI-1)
            step_D[i] = jac_add(jac_mul(G, a, ellI), jac_mul(T, b, ellI))
            step_a[i] = a; step_b[i] = b
        end
        @printf("[p3 trial %2d] step table built (%.2fs)\n", trial_idx, time()-t0); flush(stdout)
    end

    # ── Walk state ────────────────────────────────────────────────────────────
    alpha_cur = rand(1:ellI-1)
    beta_cur  = rand(1:ellI-1)
    D_cur = jac_add(jac_mul(G, alpha_cur, ellI), jac_mul(T, beta_cur, ellI))

    # IDEA 4: The hot-anchor snapshot is created in the parent thread and
    # passed in as a plain vector.  This keeps worker startup read-only.
    if hot_anchors !== nothing && !isempty(hot_anchors)
        hot_len  = length(hot_anchors)
        hot_pos  = mod(trial_idx - 1, hot_len) + 1
        basin_idx = hot_anchors[hot_pos]
        basin_idx = clamp(basin_idx, 1, nF)
        cur_pt    = fb[basin_idx]
    else
        cur_pt    = fb[rand(1:nF)]
    end

    # ── Local birthday fallback tables ────────────────────────────────────────
    # affine: lp_pt → (fb_row, neg_al, neg_be)
    local_lp1_affine = Dict{NTuple{2,Int},   Tuple{Dict{Int,Int}, Int, Int}}()
    # conj:   lp_key → LP1ConjValFull
    # Local birthday dict runs β≠0, so we need to store neg_be.
    # The precomputed table uses LP1ConjVal (amortized, neg_be=0 implicit).
    local_lp1_conj   = Dict{CanonicalLP1Key, LP1ConjValFull}()

    # ── Local alog extension ──────────────────────────────────────────────────
    # When a closure yields a β=0 combined row (c_neg_be == 0), the relation is
    # a pure G-relation that may let us extend atom logs beyond what phase 2
    # computed.  We store these in a local overlay rather than mutating the
    # shared read-only tables.atom_log_dict.
    #
    # Helper: look up atom log, checking local extension first.

    # ── IDEA 2 & 4: Phase3 inertia + mini basin memory ────────────────────────
    # Mirror the phase2 inertia mechanism in phase3 to keep the β≠0 walk near
    # productive geometric configurations.  Basin steering uses the precomputed
    # hot_basin_anchors (seeded via warm-start) and a local dry-streak counter.
    
    _small_primes_p3 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)

    # Calculate initial stride using 1-based indexing safety
    anchor_stride_p3 = if nF > 1
        prime_target = _small_primes_p3[mod1(trial_idx, length(_small_primes_p3))]
        mod1(prime_target, nF - 1)
    else
        1
    end

    # Step by 1 within the [1, nF] boundary using standard Base.gcd
    while nF > 1 && gcd(anchor_stride_p3, nF) != 1
        anchor_stride_p3 = mod1(anchor_stride_p3 + 1, nF)
    end

    # Start cursor at the warm-start position if available
    anchor_cursor_p3 = if isempty(hot_anchors)
        rand(1:nF)
    else
        target_anchor = hot_anchors[mod1(trial_idx, length(hot_anchors))]
        clamp(target_anchor, 1, nF)
    end

    inertia_dir_p3 = anchor_stride_p3
    p3_dry_streak  = 0

    # ── Burst-orbit exploitation ──────────────────────────────────────────────
    # When a conj closure fires, D_cur is geometrically hot — its neighbourhood
    # produces conj hits at elevated rate for ~tau* ≈ mu/3 steps.  Rather than
    # drifting away via the cumulative walk, we save the hot divisor and spend
    # burst_budget steps probing it with fresh independent offsets each time:
    #   D_probe = hot_D + step_D[si_burst]   (single fresh step, not accumulated)
    # D_cur keeps accumulating normally during burst mode so resumption is
    # seamless when the budget runs out.
    _burst_budget_default = let mg = tables.lp1_conj_mean_gap_steps
        mg >= 100.0 ? round(Int, mg / 3.0) : 2000
    end
    burst_budget  = 0
    burst_active  = false
    hot_D         = D_cur
    hot_alpha     = alpha_cur
    hot_beta      = beta_cur

    @inline function p3_record_hit!()
        hot_D         = D_cur
        hot_alpha     = alpha_cur
        hot_beta      = beta_cur
        burst_budget  = _burst_budget_default
        burst_active  = true
        p3_dry_streak = 0
    end

    # IS: lightweight ε-greedy restart using hot_anchors from precompute.
    # Phase3 inherits the IS philosophy but has no full reservoir — it just
    # uses the precomputed hot_anchors list with a small random perturbation.
    p3_ε_expl   = 0.30   # 30% exploration (phase3 walks shorter so keep high)
    p3_hot_idx  = 0      # round-robin pointer into hot_anchors

    @inline function p3_next_anchor()
        if !isempty(hot_anchors) && rand() >= p3_ε_expl
            # Exploitation: rotate through hot_anchors with jitter.
            hot_len = length(hot_anchors)
            p3_hot_idx = mod(p3_hot_idx, hot_len) + 1
            base = hot_anchors[p3_hot_idx]
            base = clamp(base, 1, nF)
            jitter = rand(-3:3)
            anchor_cursor_p3 = mod(base - 1 + jitter, nF) + 1
        end
        pt = fb[anchor_cursor_p3]
        anchor_cursor_p3 = mod(anchor_cursor_p3 - 1 + inertia_dir_p3, nF) + 1
        return pt
    end
    local_alog = Dict{NTuple{2,Int}, Int}()
    @inline alog_get(pt) = get(local_alog, pt, get(alog, pt, -1))

    # Counters ──────────────────────────────────────────────────────────────
    n_steps          = 0
    n_0lp            = 0
    n_1lp_aff_pre    = 0   # affine closure against shared_lp1_pre
    n_1lp_aff_local  = 0   # affine closure against local birthday dict
    n_1lp_conj_pre   = 0   # conj closure against shared_lp1_conj_pre
    n_1lp_conj_local = 0   # conj closure against local birthday dict
    n_conj_branch    = 0   # times we entered A1 (i0∈FB, conj residual), before haskey
    n_alog_extended  = 0   # new atom logs derived from β=0 closures
    n_burst_steps    = 0   # raw burst iterations (pre-gate)
    n_burst_valid    = 0   # burst iterations that passed all gates (same units as n_steps)
    n_burst_hits     = 0   # conj closures that fired during burst mode
    k_rec            = nothing

    # ── Helper: attempt to extend local_alog from a β=0 combined row ─────────
    # combined_row maps FB index → coefficient.  The relation is:
    #   Σ coeff[j] · log(fb[j])  ≡  neg_al   (mod ell)   with neg_be == 0
    # If exactly one atom is unknown we can solve for it.
    function try_extend_alog!(combined_row::Dict{Int,Int}, neg_al::Int)
        unknown_idx = 0
        unknown_coeff = 0
        known_sum = 0
        for (j, coeff) in combined_row
            l = alog_get(fb[j])
            if l == -1
                if unknown_idx != 0
                    return   # two unknowns — can't solve
                end
                unknown_idx   = j
                unknown_coeff = coeff
            else
                known_sum = mod(known_sum + coeff * l, ellI)
            end
        end
        unknown_idx == 0 && return   # fully determined row — nothing new to store
        # Solve: unknown_coeff · log(fb[unknown_idx]) ≡ neg_al - known_sum (mod ell)
        rhs = mod(neg_al - known_sum, ellI)
        # unknown_coeff must be invertible mod ell (ell is prime)
        @assert gcd(unknown_coeff, ellI) == 1 "non-invertible coefficient in try_extend_alog!"
        log_new = mulmod(rhs, Int(powermod(unknown_coeff, ell - 2, ell)))
        local_alog[fb[unknown_idx]] = log_new
        n_alog_extended += 1
    end

    # ── Local relation accumulator for self-contained GF(ell) solve ──────────
    # Each relation row contributes one equation to the system:
    #   Σ_j coef[j]·log(fb[j])  +  neg_be·k  ≡  neg_al   (mod ell)
    # Unknowns: atom logs (columns 1..nF) and k (column nF+1).
    # β=0 rows (neg_be=0) constrain atom logs only; β≠0 rows pin k.
    # Seeded with the precomputed β=0 relation set so the null space is
    # already constrained before the walk adds β≠0 rows.
    # Use pre-allocated seeded vectors built in the main thread before spawning.
    # Building these inside the worker (esp. the BigInt copies) causes all 30
    # threads to contend on the GMP allocator simultaneously → deadlock.
    local_rel_rows  = seeded_rel_rows !== nothing ? seeded_rel_rows : copy(tables.rel_rows_pre)
    local_rel_be    = seeded_rel_be   !== nothing ? seeded_rel_be   : zeros(Int, length(tables.rel_rows_pre))
    local_rel_al    = seeded_rel_al   !== nothing ? seeded_rel_al   : copy(tables.alpha_vec_pre)
    # The β=0 rows already seeded (~nF of them from phase1+phase2) constrain the
    # atom log subspace; each β≠0 row adds one equation involving k.  The system
    # has nF+1 unknowns total, so once the seeded β=0 rows already span rank ~nF
    # we need only O(1) β≠0 rows to pin k.  Attempt solve after every new β≠0
    # row (with a small backoff on failure to avoid spending time on under-determined
    # prefixes); never wait for nF more rows.
    n_local_be_rows  = 0    # count of β≠0 rows added during the walk
    n_local_linalg   = 0    # how many times we attempted elimination
    _next_linalg_at  = 1    # attempt when n_local_be_rows reaches this

    # GF(ell) Gaussian elimination on the augmented system.
    # Columns 1..nF = atom log unknowns; column nF+1 = k; column nF+2 = RHS (neg_al).
    # Returns k::Int if uniquely determined and group-law verified, else nothing.
    function try_local_linalg_solve()::Union{Int,Nothing}
        n_local_linalg += 1
        m   = length(local_rel_rows)
        nc  = nF + 2   # nF atom cols + k col + RHS col
        @printf("[p3 trial %2d | linalg #%d] m=%d  nc=%d  matrix %.1f MB\n",
                trial_idx, n_local_linalg, m, nc, m*nc*8/1024^2)
        flush(stdout)
        # Build dense matrix mod ell.
        # Use Int128 so that products A[r,cc]*f and A[pr,cc]*inv_piv (both ∈ [0,ell-1])
        # do not overflow; for ell ~ 2^38 the product is ~2^76 > Int64 max.
        #
        # Relation semantics: Σ_j coef[j]·log(fb[j])  =  neg_al + neg_be·k  (mod ell)
        # Rearranged as a linear system with unknowns x[j]=log(fb[j]) and k:
        #   Σ_j coef[j]·x[j]  +  (-neg_be)·k  =  neg_al
        # So column nF+1 carries the coefficient of k, which is -neg_be mod ell.
        # Using +neg_be here would flip the sign of k in the linalg solution,
        # giving k_try = (neg_al - log_sum)/neg_be instead of (log_sum - neg_al)/neg_be.
        A = zeros(Int128, m, nc)
        for ri in 1:m
            for (j, v) in local_rel_rows[ri]
                1 <= j <= nF || continue
                A[ri, j] = mod(v, ellI)
            end
            A[ri, nF+1] = mod(ellI - local_rel_be[ri], ellI)    # coefficient of k = -neg_be mod ell
            A[ri, nF+2] = Int128(mod(local_rel_al[ri], ellI))   # RHS (handle BigInt seed rows)
        end
        # Forward elimination with partial pivoting over GF(ell).
        pivot_col = zeros(Int, m)   # pivot_col[r] = column of pivot in row r, 0 if zero row
        pr = 1   # next pivot row
        for c in 1:nF+1
            # Find pivot in column c at or below row pr.
            piv = 0
            for r in pr:m
                A[r, c] != 0 && (piv = r; break)
            end
            piv == 0 && continue
            # Swap rows piv ↔ pr.
            A[pr, :], A[piv, :] = A[piv, :], A[pr, :]
            # Normalise pivot row so A[pr,c] = 1.
            inv_piv = Int128(powermod(Int(A[pr, c]), ellI - 2, ellI))
            for cc in c:nc
                A[pr, cc] = mod(A[pr, cc] * inv_piv, ellI)
            end
            # Eliminate column c in all other rows.
            for r in 1:m
                r == pr && continue
                A[r, c] == 0 && continue
                f = A[r, c]
                for cc in c:nc
                    A[r, cc] = mod(A[r, cc] - f * A[pr, cc], ellI)
                end
            end
            pivot_col[pr] = c
            pr += 1
        end
        # Look for a row whose only nonzero variable is k (column nF+1).
        for r in 1:m
            pivot_col[r] == nF+1 || continue
            # Row reads: k = A[r, nF+2]
            k_try = Int(A[r, nF+2])
            jac_mul(G, k_try, ell) == T && return k_try
            # Pivot on k but verify failed.  This means a corrupt relation slipped
            # through (most likely an overflow bug upstream).  Crash loudly rather
            # than silently discarding the result and continuing — a wrong k that
            # accidentally passes the group-law check is far worse than a crash.
            @assert false "try_local_linalg_solve: k_try=$(k_try) failed group-law verification — relation accumulator is corrupt (overflow?)"
        end
        return nothing
    end

    # ── Helper: solve k from a pure-FB row ───────────────────────────────────
    # First tries direct solve from alog_get (fast path when atom logs are known).
    # Falls back to accumulating the relation for local GF(ell) elimination.
    # β=0 rows go to try_extend_alog! instead.
    @inline function try_solve(fb_row::Dict{Int,Int}, neg_al::Int, neg_be::Int)::Union{Int,Nothing}
        if neg_be == 0
            # β=0 relation: pure G row, try to extend alog rather than solve for k.
            try_extend_alog!(fb_row, neg_al)
            return nothing
        end
        # Fast path: all atom logs already known.
        log_sum = 0
        all_known = true
        for (j, v) in fb_row
            l = alog_get(fb[j])
            if l == -1
                all_known = false
                break
            end
            log_sum = mod(log_sum + v * l, ellI)
        end
        if all_known
            k_try = mulmod(mod(log_sum - neg_al, ellI), Int(powermod(neg_be, ell - 2, ell)))
            if jac_mul(G, k_try, ell) == T
                return k_try
            end
            @assert false "try_solve: bad relation — all atom logs present, β≠0, but k_try=$(k_try) failed verification (neg_al=$(neg_al), neg_be=$(neg_be))"
        end
        # Slow path: accumulate relation and attempt local linalg solve.
        push!(local_rel_rows, fb_row)
        push!(local_rel_be,   neg_be)
        push!(local_rel_al,   neg_al)
        n_local_be_rows += 1
        n_local_be_rows >= _next_linalg_at || return nothing
        _next_linalg_at += 10   # backoff: try again after 10 more β≠0 rows
        return try_local_linalg_solve()
    end

    # ── Helper: solve k from a conj closure ──────────────────────────────────
    # A conj closure gives:  atom(fb[i0_cur]) - atom(fb[i0_pre]) ≡ c_al·G + c_be·T
    # Both atoms are in atom_log_dict (or local_alog), so:
    #   c_al + c_be·k  ≡  alog[fb[i0_cur]] - alog[fb[i0_pre]]  (mod ell)
    # Returns k::Int on success, nothing on soft inapplicable (missing logs, β=0).
    # Asserts on internal inconsistency (all logs present, β≠0, k fails verify).

    function try_solve_conj(i0_cur::Int, i0_pre::Int, c_al::Int, c_be::Int)::Union{Int,Nothing}
        # Self-closure: same atom on both sides → row cancels.
        # The relation collapses to 0 = c_al·G + c_be·T, which is a pure
        # scalar equation giving k = -c_al · c_be⁻¹ mod ell directly.
        # No atom logs needed — just verify and return.
        if i0_cur == i0_pre
            c_be == 0 && return nothing   # 0 = c_al·G, degenerate
            k_try = mulmod(mod(-c_al, ellI), Int(powermod(c_be, ell - 2, ell)))
            if jac_mul(G, k_try, ell) == T
                return k_try
            end
            @assert false "try_solve_conj: self-closure bad relation — k_try=$(k_try) failed verification (c_al=$(c_al), c_be=$(c_be))"
        end

        if c_be == 0
            # β=0 self-opposite conj closure: pure G relation between two atoms.
            # Attempt to extend alog: atom(fb[i0_cur]) - atom(fb[i0_pre]) ≡ c_al·G
            l_pre = alog_get(fb[i0_pre])
            l_cur = alog_get(fb[i0_cur])
            if l_pre != -1 && l_cur == -1
                local_alog[fb[i0_cur]] = mod(c_al + l_pre, ellI)
                n_alog_extended += 1
            elseif l_cur != -1 && l_pre == -1
                local_alog[fb[i0_pre]] = mod(l_cur - c_al, ellI)
                n_alog_extended += 1
            end
            return nothing
        end

        pt_cur = fb[i0_cur]
        pt_pre = fb[i0_pre]
        l_cur  = alog_get(pt_cur)
        l_pre  = alog_get(pt_pre)

        if l_cur == -1 || l_pre == -1
            # Atom logs missing: express as a 2-atom relation and accumulate.
            # atom(fb[i0_cur]) - atom(fb[i0_pre]) ≡ c_al·G + c_be·T  (mod ell)
            # → 1·log(fb[i0_cur]) + (-1)·log(fb[i0_pre]) ≡ c_al + c_be·k  (mod ell)
            # Stored as (row_conj, c_be, al_adj): linalg puts -c_be in column nF+1.
            row_conj = Dict{Int,Int}(i0_cur => 1)
            i0_cur != i0_pre && (row_conj[i0_pre] = get(row_conj, i0_pre, 0) - 1)
            # If l_cur or l_pre is known, fold it into c_al to reduce unknowns.
            al_adj = c_al
            if l_cur != -1
                al_adj = mod(al_adj - l_cur, ellI)
                delete!(row_conj, i0_cur)
            end
            if l_pre != -1
                al_adj = mod(al_adj + l_pre, ellI)
                # remove pre contribution (was -1 coef)
                nv = get(row_conj, i0_pre, 0) + 1
                nv == 0 ? delete!(row_conj, i0_pre) : (row_conj[i0_pre] = nv)
            end
            push!(local_rel_rows, row_conj)
            push!(local_rel_be,   c_be)
            push!(local_rel_al,   al_adj)
            n_local_be_rows += 1
            n_local_be_rows >= _next_linalg_at || return nothing
            _next_linalg_at += 5
            return try_local_linalg_solve()
        end

        lhs   = mod(l_cur - l_pre, ellI)
        k_try = mulmod(mod(lhs - c_al, ellI), Int(powermod(c_be, ell - 2, ell)))

        if jac_mul(G, k_try, ell) == T
            return k_try
        end
        # Both atom logs present, β≠0, but k failed to verify — internal inconsistency.
        @assert false "try_solve_conj: bad relation — all atom logs present, β≠0, but k_try=$(k_try) failed verification (i0_cur=$(i0_cur), i0_pre=$(i0_pre), c_al=$(c_al), c_be=$(c_be), lhs=$(lhs))"
    end

    # ── Main walk loop ────────────────────────────────────────────────────────
    t_last_heartbeat = time()
    @printf("[p3 trial %2d] entering main walk loop (step_cap=%d)\n", trial_idx, step_cap)
    flush(stdout)

    for _raw_step in 1:step_cap
        if _raw_step & 0xffff == 0   # every 65536 raw steps
            now = time()
            if now - t_last_heartbeat >= 30.0
                @printf("[phase3 trial %d | heartbeat] raw_step=%d  n_steps=%d  n_conj_branch=%d  n_linalg=%d  elapsed=%.1fs\n",
                        trial_idx, _raw_step, n_steps, n_conj_branch, n_local_linalg, now - t0)
                flush(stdout)
                t_last_heartbeat = now
            end
        end
        si        = rand(1:n_steps_prebuilt)
        # Always advance the cumulative walk (keeps D_cur fresh for after burst).
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a[si], ellI)
        beta_cur  = mod(beta_cur  + step_b[si], ellI)

        # In burst mode: probe the hot divisor with a fresh independent offset.
        # All three of (D_probe, alpha_probe, beta_probe) must use the same step
        # index so that D_probe = hot_D + step_D[si_burst] is consistent with
        # alpha_probe = hot_alpha + step_a[si_burst] and beta_probe = hot_beta + step_b[si_burst].
        # Using si (the main walk's index) for alpha/beta but rand() for D was the bug.
        this_step_was_burst = burst_active
        if burst_active
            si_burst    = rand(1:n_steps_prebuilt)
            D_probe     = jac_add(hot_D, step_D[si_burst])
            alpha_probe = mod(hot_alpha + step_a[si_burst], ellI)
            beta_probe  = mod(hot_beta  + step_b[si_burst], ellI)
            n_burst_steps += 1
            burst_budget  -= 1
            burst_active   = burst_budget > 0
        else
            D_probe     = D_cur
            alpha_probe = alpha_cur
            beta_probe  = beta_cur
        end

        beta_probe == 0 && continue
        # Use probe values for the rest of this step.
        D_eff     = D_probe
        alpha_eff = alpha_probe
        beta_eff  = beta_probe

        # Gate 1: degree-2 divisor
        fp3_deg(D_eff.u) != 2 && continue
        u0 = D_eff.u[1]; u1 = D_eff.u[2]
        v0 = D_eff.v[1]; v1 = D_eff.v[2]
        px, py = cur_pt

        # Gate 2: P0 not in support of D_eff
        fp(fp(px*px) + fp(u1*px) + u0) == 0 && continue

        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a_c, b_c, c_c, _ = phi_c

        res_R, res_S, RS_mumford = phi_residual_mumford(a_c, b_c, c_c, px, u0, u1)
        RS_mumford === SENTINEL_MUMFORD && continue

        n_steps += 1
        this_step_was_burst && (n_burst_valid += 1)

        neg_al = mod(ellI - alpha_eff, ellI)
        neg_be = mod(ellI - beta_eff,  ellI)
        i0     = get(pt2idx, cur_pt, 0)

        # ======================================================================
        #  BRANCH A: conjugate residual
        # ======================================================================
        if res_R === SENTINEL_PT
            lp_key = canonical_lp1_conj_key(RS_mumford::NTuple{4,Int})

            if i0 != 0
                # A1: 1-LP-conj — P0 is in FB, RS pair is the LP atom
                n_conj_branch += 1

                # Lockless lookup into the pre-snapshotted plain dict.
                _conj_v = lp1_conj_dict !== nothing ? get(lp1_conj_dict, lp_key, nothing) : nothing
                if _conj_v !== nothing
                    v = _conj_v
                    prev_col = Int(v.i0)
                    prev_al  = Int(v.neg_al)
                    c_al = mod(neg_al - prev_al, ellI)
                    c_be = neg_be
                    n_1lp_conj_pre += 1
                    burst_active && (n_burst_hits += 1)
                    p3_record_hit!()
                    k_rec = try_solve_conj(i0, prev_col, c_al, c_be)
                    k_rec !== nothing && break

                elseif haskey(local_lp1_conj, lp_key)
                    v = local_lp1_conj[lp_key]
                    prev_col, prev_al, prev_be = Int(v.i0), Int(v.neg_al), Int(v.neg_be)
                    c_al = mod(neg_al - prev_al, ellI)
                    c_be = mod(neg_be - prev_be, ellI)
                    delete!(local_lp1_conj, lp_key)
                    n_1lp_conj_local += 1
                    burst_active && (n_burst_hits += 1)
                    p3_record_hit!()
                    k_rec = try_solve_conj(i0, prev_col, c_al, c_be)
                    k_rec !== nothing && break
                else
                    if length(local_lp1_conj) < local_lp_cap
                        # neg_al and neg_be are both in [0, ellI-1] after mod above,
                        # so UInt64 is safe for ell < 2^64.  Assert to catch any future
                        # regression where ellI is set wider than 64 bits.
                        @assert neg_al >= 0 && neg_be >= 0 "negative neg_al/neg_be before UInt64 cast"
                        @assert ell < typemax(UInt64) "ell too large for UInt64 LP1ConjValFull fields — widen struct"
                        local_lp1_conj[lp_key] = LP1ConjValFull(UInt16(i0), UInt64(neg_al), UInt64(neg_be))
                    end
                    p3_dry_streak += 1
                end
            else
                p3_dry_streak += 1
            end
            # A2: i0 not in FB → 2-LP-conj, skip
            cur_pt = i0 != 0 ? cur_pt : p3_next_anchor()
            continue
        end

        # ======================================================================
        #  BRANCH B: split residual
        # ======================================================================
        R  = res_R; S = res_S
        iR = get(pt2idx, R, 0)
        iS = get(pt2idx, S, 0)
        n_lp = (i0 == 0 ? 1 : 0) + (iR == 0 ? 1 : 0) + (iS == 0 ? 1 : 0)

        if n_lp == 0
            # B0: 0-LP direct solve
            fb_row = Dict{Int,Int}()
            for idx in (i0, iR, iS)
                fb_row[idx] = get(fb_row, idx, 0) + 1
            end
            n_0lp += 1
            k_rec = try_solve(fb_row, neg_al, neg_be)
            k_rec !== nothing && break
            # IDEA 4: 0-LP is productive — reset dry streak.
            p3_dry_streak = 0
            cur_pt = p3_next_anchor()

        elseif n_lp == 1
            # B1: 1-LP-affine
            lp_pt  = i0 == 0 ? cur_pt : iR == 0 ? R : S
            fb_row = Dict{Int,Int}()
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row[idx] = get(fb_row, idx, 0) + 1
            end

            if haskey(lp1_pre, lp_pt)
                pre_row, pre_neg_al, pre_neg_be, _ = lp1_pre[lp_pt]
                combined = copy(fb_row)
                for (j, v) in pre_row
                    nv = get(combined, j, 0) - v
                    nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                end
                c_neg_al = mod(neg_al - pre_neg_al, ellI)
                c_neg_be = mod(neg_be - pre_neg_be, ellI)
                n_1lp_aff_pre += 1
                k_rec = try_solve(combined, c_neg_al, c_neg_be)
                k_rec !== nothing && break

            elseif haskey(local_lp1_affine, lp_pt)
                prev_row, prev_neg_al, prev_neg_be = local_lp1_affine[lp_pt]
                combined = copy(fb_row)
                for (j, v) in prev_row
                    nv = get(combined, j, 0) - v
                    nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                end
                c_neg_al = mod(neg_al - prev_neg_al, ellI)
                c_neg_be = mod(neg_be - prev_neg_be, ellI)
                delete!(local_lp1_affine, lp_pt)
                n_1lp_aff_local += 1
                k_rec = try_solve(combined, c_neg_al, c_neg_be)
                k_rec !== nothing && break
            else
                if length(local_lp1_affine) < local_lp_cap
                    local_lp1_affine[lp_pt] = (copy(fb_row), neg_al, neg_be)
                end
                p3_dry_streak += 1
            end

            cur_pt = iR != 0 ? R : iS != 0 ? S : p3_next_anchor()

        else
            # B2/B3: 2-LP or 3-LP, discard
            p3_dry_streak += 1
            cur_pt = p3_next_anchor()
        end
    end

    elapsed  = time() - t0
    success  = k_rec !== nothing
    verified = k_true === nothing || k_rec == k_true

    if verbose
        k_rec_s  = k_rec  === nothing ? "none" : string(k_rec)
        k_true_s = k_true === nothing ? "?"    : string(k_true)
        match_s  = verified ? "ok" : "MISMATCH"
        burst_hit_rate = n_burst_valid > 0 ? Float64(n_burst_hits) / Float64(n_burst_valid) : 0.0
        cold_steps     = n_steps - n_burst_valid
        cold_hits      = (n_1lp_conj_pre + n_1lp_conj_local) - n_burst_hits
        cold_hit_rate  = cold_steps > 0 ? Float64(cold_hits) / Float64(cold_steps) : 0.0
        @printf("[phase3 trial %d | t=%.3fs] k_rec=%s  k_true=%s  match=%s  steps=%d  0lp=%d  1lp_aff_pre=%d  1lp_aff_local=%d  1lp_conj_pre=%d  1lp_conj_local=%d  conj_branch=%d  linalg_attempts=%d\n",
                trial_idx, elapsed, k_rec_s, k_true_s, match_s,
                n_steps, n_0lp, n_1lp_aff_pre, n_1lp_aff_local, n_1lp_conj_pre, n_1lp_conj_local, n_conj_branch, n_local_linalg)
        @printf("[phase3 trial %d | burst] budget=%d  burst_steps=%d  burst_valid=%d  burst_hits=%d  burst_rate=%.4f  cold_rate=%.4f  lift=%.2f\n",
                trial_idx, _burst_budget_default, n_burst_steps, n_burst_valid, n_burst_hits, burst_hit_rate, cold_hit_rate,
                cold_hit_rate > 0 ? burst_hit_rate / cold_hit_rate : 0.0)
        flush(stdout)
    end

    return Phase3Result(
        trial_idx,
        k_rec,
        k_true,
        n_steps,
        n_0lp,
        n_1lp_aff_pre + n_1lp_conj_pre,
        n_1lp_aff_local + n_1lp_conj_local,
        n_alog_extended,
        elapsed,
        success && verified)
end

# ---------------------------------------------------------------------------
#  phase3_solve_targets
#
#  Public entry point.  Solves DLPs for a list of (T, k_true) pairs in
#  parallel over all available threads, using the precomputed Phase2Tables.
#
#  Arguments:
#    tables       — Phase2Tables from the precompute block in main2()
#    targets      — Vector of (T::Div2, k_true::Union{Int,Nothing})
#    G            — generator
#    step_cap     — per-trial walk step limit (default 10M)
#    verbose      — per-trial progress lines
#
#  Returns Vector{Phase3Result} (one per target, in order).
# ---------------------------------------------------------------------------
function phase3_solve_targets(
        tables   ::Phase2Tables,
        targets  ::Vector{<:Tuple{Div2, <:Union{Int,Nothing}}},
        G        ::Div2;
        step_cap ::Int  = -1,   # -1 → auto-scaled via phase3_default_step_cap(ell)
        verbose  ::Bool = true)::Vector{Phase3Result}

    n = length(targets)
    results = Vector{Phase3Result}(undef, n)

    println("── Phase 3: amortised DLP solves ────────────────────────────────────")
    eff_step_cap  = step_cap < 0 ? phase3_default_step_cap(tables.ell) : step_cap
    eff_local_cap = phase3_local_lp_cap(tables.ell)
    @printf("   targets=%d  threads=%d  FB=%d  lp1_pre_entries=%d  step_cap=%d (%.1f×√ell)  local_lp_cap=%d\n",
            n, Threads.nthreads(), length(tables.fb),
            length(tables.shared_lp1), eff_step_cap,
            eff_step_cap / sqrt(Float64(tables.ell)), eff_local_cap)
    @printf("   RSS at phase3 start: %.1f MB  |  GC live: %.1f MB\n",
            Sys.maxrss() / 1024^2, Base.gc_live_bytes() / 1024^2)
    flush(stdout)

    # ── Enrich atom_log_dict via seeded BFS over the β=0 relation set ─────────
    # The dense RREF in the precompute phase pins only pivot-column atoms —
    # typically ~10% of the FB when β=0 relations are nearly linearly dependent
    # due to the chained walk structure.  The remaining atoms are not algebraically
    # underdetermined; they just weren't chosen as pivots.  Many are graph-reachable
    # from the RREF seeds via the relation graph: if a β=0 row has exactly one
    # unknown atom and all others are pinned, we can solve for the unknown directly.
    #
    # Algorithm: BFS work-queue.  Seeds are the RREF-verified atom_log_dict entries.
    # For each relation with exactly one unknown atom, solve and pin it, then re-scan
    # all relations that touch the newly-pinned atom.  O(|rel_rows| × avg_weight).
    #
    # Every derived value is verified against the group law before being accepted —
    # this catches any gauge-freedom inconsistency (which would manifest as a
    # verification failure rather than a wrong log slipping through).
    if !isempty(tables.atom_log_dict) && !isempty(tables.rel_rows_pre)
        t_enrich  = time()
        n_pre     = length(tables.atom_log_dict)
        ellI_e    = Int(tables.ell)
        nF_e      = length(tables.fb)
        # mulmod_e: safe multiply mod ellI_e for values that may each be O(ell ~ 2^38).
        # coef from RREF-reduced rel_rows_pre can be in [0, ell-1]; lj likewise.
        # Their product needs ~76 bits — overflows Int64.  widemul -> Int128 is exact.
        @inline mulmod_e(a::Int, b::Int) = Int(mod(widemul(a, b), ellI_e))

        # Working log array: index → log, -1 if unknown.  Seeded from atom_log_dict.
        work_logs = fill(-1, nF_e)
        for (pt, l) in tables.atom_log_dict
            idx = get(tables.pt2idx, pt, 0)
            idx != 0 && (work_logs[idx] = l)
        end

        # For each atom index, which rows contain it?
        atom_rows = [Int[] for _ in 1:nF_e]
        for (ri, row) in enumerate(tables.rel_rows_pre)
            for (j, _) in row
                1 <= j <= nF_e && push!(atom_rows[j], ri)
            end
        end

        # Row → number of unknowns (initialise from work_logs).
        n_unknown = Vector{Int}(undef, length(tables.rel_rows_pre))
        for (ri, row) in enumerate(tables.rel_rows_pre)
            n_unknown[ri] = count(p -> 1 <= p[1] <= nF_e && work_logs[p[1]] == -1, row)
        end

        # Work queue: rows with exactly one unknown (initially).
        in_queue = falses(length(tables.rel_rows_pre))
        queue    = Int[]
        for ri in eachindex(tables.rel_rows_pre)
            if n_unknown[ri] == 1
                push!(queue, ri)
                in_queue[ri] = true
            end
        end

        n_enriched  = 0
        n_verified  = 0

        while !isempty(queue)
            ri  = pop!(queue)
            in_queue[ri] = false
            row     = tables.rel_rows_pre[ri]
            neg_al  = Int(tables.alpha_vec_pre[ri])

            # Re-count unknowns (state may have changed since enqueue).
            unk_j    = 0
            unk_coef = 0
            known_sum = 0
            valid    = true
            for (j, coef) in row
                (1 <= j <= nF_e) || (valid = false; break)
                lj = work_logs[j]
                if lj == -1
                    if unk_j != 0
                        valid = false; break   # two unknowns now — skip
                    end
                    unk_j    = j
                    unk_coef = coef
                else
                    known_sum = mod(known_sum + mulmod_e(coef, lj), ellI_e)
                end
            end
            (!valid || unk_j == 0) && continue   # 0 or 2+ unknowns

            # Solve: unk_coef * log(fb[unk_j]) ≡ neg_al - known_sum  (mod ell)
            rhs = mod(neg_al - known_sum, ellI_e)
            gcd(unk_coef, ellI_e) != 1 && continue   # non-invertible (shouldn't happen, ell prime)
            log_new = Int(mod(widemul(rhs, powermod(unk_coef, ellI_e - 2, ellI_e)), ellI_e))

            # Verify against the group law before accepting.
            pt = tables.fb[unk_j]
            if !jac_isid(jac_sub(jac_mul(G, log_new, tables.ell), mumford1(pt[1], pt[2])))
                continue   # gauge-inconsistent — skip
            end

            n_verified += 1
            work_logs[unk_j] = log_new

            if !haskey(tables.atom_log_dict, pt)
                tables.atom_log_dict[pt] = log_new
                n_enriched += 1
            end

            # Decrement unknown count for all rows containing unk_j, enqueue new unit-unknowns.
            for ri2 in atom_rows[unk_j]
                n_unknown[ri2] > 0 && (n_unknown[ri2] -= 1)
                if n_unknown[ri2] == 1 && !in_queue[ri2]
                    push!(queue, ri2)
                    in_queue[ri2] = true
                end
            end
        end

        @printf("   [enrich] BFS propagation: %d → %d / %d atom logs  (+%d new, %d verified, %.3fs)\n",
                n_pre, length(tables.atom_log_dict), nF_e,
                n_enriched, n_verified, time() - t_enrich)
        flush(stdout)
    end

    t0 = time()

    # tables.shared_lp1_conj is already a plain Dict{CanonicalLP1Key, LP1ConjVal}
    # snapshot — the LSM was closed and freed in main2 before Phase2Tables was
    # constructed.  No conversion needed here; no lock contention across workers.
    conj_snap = tables.shared_lp1_conj
    @printf("   [phase3] conj dict: %d entries (pre-snapshotted, no conversion needed)\n",
            length(conj_snap))
    flush(stdout)

    # Pre-allocate seeded relation vectors and the hot-anchor snapshot in the
    # main thread before spawning.  Doing this inside the spawned tasks can
    # create allocator / GC contention and reintroduce launch-time stalls.
    #
    # CRITICAL: seeded_rel_rows must be a DEEP copy — each worker appends to its
    # local_rel_rows (which aliases seeded_rel_rows[i]) and may mutate individual
    # Dict entries.  A shallow copy (copy(tables.rel_rows_pre)) copies the vector
    # spine but leaves all Dict objects shared across workers, causing concurrent
    # mutation → GMP allocator deadlock at phase 3 start.
    n_pre_rows = length(tables.rel_rows_pre)
    @printf("   [phase3 prealloc] n=%d  n_pre_rows=%d  alpha_vec_pre length=%d\n",
            n, n_pre_rows, length(tables.alpha_vec_pre))
    @printf("   [phase3 prealloc] RSS=%.1f MB  GC-live=%.1f MB\n",
            Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
    flush(stdout)

    t_prealloc = time()
    @printf("   [phase3 prealloc] deep-copying rel_rows (30×%d Dicts)...\n", n_pre_rows)
    flush(stdout)
    seeded_rel_rows = [[copy(d) for d in tables.rel_rows_pre] for _ in 1:n]
    @printf("   [phase3 prealloc] rel_rows done (%.2fs)  RSS=%.1f MB  GC-live=%.1f MB\n",
            time()-t_prealloc, Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
    flush(stdout)

    t_be = time()
    @printf("   [phase3 prealloc] allocating rel_be...\n"); flush(stdout)
    seeded_rel_be   = [zeros(Int, n_pre_rows)                 for _ in 1:n]
    @printf("   [phase3 prealloc] rel_be done (%.2fs)\n", time()-t_be); flush(stdout)

    t_al = time()
    @printf("   [phase3 prealloc] deep-copying alpha_vec_pre (30×%d BigInts)...\n",
            length(tables.alpha_vec_pre)); flush(stdout)
    seeded_rel_al   = [copy(tables.alpha_vec_pre)             for _ in 1:n]
    @printf("   [phase3 prealloc] alpha_vec done (%.2fs)  RSS=%.1f MB  GC-live=%.1f MB\n",
            time()-t_al, Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
    flush(stdout)

    hot_anchor_snap = copy(tables.hot_basin_anchors)
    @printf("   [phase3 prealloc] total prealloc time: %.2fs  hot_anchors=%d\n",
            time()-t_prealloc, length(hot_anchor_snap))

    # ── Pre-build step tables in the MAIN thread (sequential, avoids GMP deadlock) ──
    # Building 30×512 jac_mul calls simultaneously in spawned workers causes all
    # threads to contend on GMP's global allocator lock → deadlock.
    # Build all per-worker step tables here sequentially; pass in as plain arrays.
    ellI_pre = Int(tables.ell)
    n_steps_prebuilt = 512
    @printf("   [phase3 prealloc] building %d step tables (%d steps each) in main thread...\n",
            n, n_steps_prebuilt); flush(stdout)
    t_steptab = time()
    all_step_D = Vector{Vector{Div2}}(undef, n)
    all_step_a = Vector{Vector{Int}}(undef,  n)
    all_step_b = Vector{Vector{Int}}(undef,  n)
    for i in 1:n
        T_i, _ = targets[i]
        sd = Vector{Div2}(undef, n_steps_prebuilt)
        sa = Vector{Int}(undef,  n_steps_prebuilt)
        sb = Vector{Int}(undef,  n_steps_prebuilt)
        for j in 1:n_steps_prebuilt
            a = rand(1:ellI_pre-1); b = rand(1:ellI_pre-1)
            sd[j] = jac_add(jac_mul(G, a, ellI_pre), jac_mul(T_i, b, ellI_pre))
            sa[j] = a; sb[j] = b
        end
        all_step_D[i] = sd
        all_step_a[i] = sa
        all_step_b[i] = sb
    end
    @printf("   [phase3 prealloc] step tables done (%.2fs)  RSS=%.1f MB  GC-live=%.1f MB\n",
            time()-t_steptab, Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
    @printf("   [phase3 prealloc] RSS=%.1f MB  GC-live=%.1f MB  — spawning %d workers\n",
            Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2, n)
    flush(stdout)

    @sync for i in 1:n
        @printf("   [phase3 spawn] launching worker %d/%d\n", i, n); flush(stdout)
        Threads.@spawn begin
            @printf("   [phase3 worker %d] started on thread %d\n", i, Threads.threadid())
            flush(stdout)
            T_i, k_true_i = targets[i]
            results[i] = phase3_trial_worker(i, T_i, k_true_i, tables, G;
                                              step_cap=eff_step_cap, local_lp_cap=eff_local_cap,
                                              verbose=verbose,
                                              conj_dict=conj_snap,
                                              hot_anchors=hot_anchor_snap,
                                              seeded_rel_rows=seeded_rel_rows[i],
                                              seeded_rel_be=seeded_rel_be[i],
                                              seeded_rel_al=seeded_rel_al[i],
                                              prebuilt_step_D=all_step_D[i],
                                              prebuilt_step_a=all_step_a[i],
                                              prebuilt_step_b=all_step_b[i])
            @printf("   [phase3 worker %d] finished: success=%s  steps=%d  elapsed=%.1fs\n",
                    i, string(results[i].success), results[i].n_steps, results[i].elapsed_s)
            flush(stdout)
        end
    end

    # ── Summary ───────────────────────────────────────────────────────────────
    n_ok        = count(r -> r.success, results)
    total_steps = sum(r -> r.n_steps, results)
    avg_steps   = total_steps / max(1, n)
    n_pre       = sum(r -> r.n_1lp_preclose, results)
    n_loc       = sum(r -> r.n_1lp_local, results)
    n_0lp_tot   = sum(r -> r.n_0lp_hits, results)
    n_alog_ext  = sum(r -> r.n_alog_extended, results)
    println()
    @printf("── Phase 3 summary ──────────────────────────────────────────────────\n")
    @printf("  %d / %d targets solved correctly\n", n_ok, n)
    @printf("  total steps: %d  (avg %.1f/target)\n", total_steps, avg_steps)
    @printf("  closure breakdown: 0-LP=%d  1LP-preclose=%d  1LP-local=%d\n",
            n_0lp_tot, n_pre, n_loc)
    @printf("  alog extensions from β=0 closures: %d\n", n_alog_ext)
    @printf("  wall time: %.3fs\n", time() - t0)
    @printf("  Process RSS at phase3 exit: %.1f MB  |  GC live: %.1f MB\n",
            Sys.maxrss() / 1024^2, Base.gc_live_bytes() / 1024^2)
    println("="^70)
    flush(stdout)

    return results
end
