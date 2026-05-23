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
    # V = LP1ConjVal (amortized) or LP1ConjValFull (single-shot)
    shared_lp1_conj::Union{ShardedLP1Conj{LP1ConjVal}, LP1ConjLSM{LP1ConjVal}}
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
        n_steps_prebuilt ::Int   = 512,
        verbose          ::Bool  = false)::Phase3Result

    t0    = time()
    ell   = tables.ell
    ellI  = Int(ell)
    # Auto-scale step_cap and local LP table caps from ell.
    step_cap     = step_cap < 0 ? phase3_default_step_cap(ell) : step_cap
    local_lp_cap = phase3_local_lp_cap(ell)
    pt2idx        = tables.pt2idx
    fb            = tables.fb
    nF            = length(fb)
    alog          = tables.atom_log_dict
    lp1_pre       = tables.shared_lp1        # READ ONLY — affine 1-LP
    lp1_conj_pre  = tables.shared_lp1_conj  # READ ONLY — conj 1-LP (ShardedLP1Conj)

    # ── Prebuilt step table for the β≠0 walk ─────────────────────────────────
    step_D = Vector{Div2}(undef, n_steps_prebuilt)
    step_a = Vector{Int}(undef,  n_steps_prebuilt)
    step_b = Vector{Int}(undef,  n_steps_prebuilt)
    for i in 1:n_steps_prebuilt
        a = rand(1:ellI-1); b = rand(1:ellI-1)
        step_D[i] = jac_add(jac_mul(G, a, ell), jac_mul(T, b, ell))
        step_a[i] = a; step_b[i] = b
    end

    # ── Walk state ────────────────────────────────────────────────────────────
    alpha_cur = rand(1:ellI-1)
    beta_cur  = rand(1:ellI-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur, ell), jac_mul(T, beta_cur, ell))

    # IDEA 4: Warm-start anchor from the hot-basin indices recorded during
    # the β=0 precompute.  Rather than picking a random FB point, we start
    # near a region that was productive for LP1-conj events.  Each trial
    # picks a different entry from the basin buffer (using trial_idx as
    # selector) to spread trials across multiple hot regions rather than
    # crowding one.  If the basin is empty (first run, no hits), fall back
    # to the standard random init.
    hot_anchors = tables.hot_basin_anchors
    if !isempty(hot_anchors)
        basin_idx = hot_anchors[mod(trial_idx - 1, length(hot_anchors)) + 1]
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
    _small_primes_p3 = (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53)
    function _gcd_p3(a, b); while b != 0; a, b = b, a % b; end; a; end

    anchor_stride_p3 = nF > 1 ?
        mod(_small_primes_p3[mod(trial_idx - 1, length(_small_primes_p3)) + 1], nF - 1) + 1 : 1
    while nF > 1 && _gcd_p3(anchor_stride_p3, nF) != 1
        anchor_stride_p3 = mod(anchor_stride_p3 + 1, nF) + 1
    end
    # Start cursor at the warm-start position if available.
    anchor_cursor_p3 = isempty(hot_anchors) ? rand(1:nF) :
                       clamp(hot_anchors[mod(trial_idx - 1, length(hot_anchors)) + 1], 1, nF)

    inertia_dir_p3 = anchor_stride_p3
    P3_INERTIA_FLIP  = 0.05
    P3_BASIN_TRIGGER = 500
    p3_dry_streak = 0

    # Mini basin buffer: track LP-conj hits locally within this trial.
    p3_basin_buf   = zeros(Int, 8)
    p3_basin_head  = 1
    p3_basin_count = 0

    @inline function p3_record_basin!(idx::Int)
        p3_basin_buf[p3_basin_head] = idx
        p3_basin_head  = mod(p3_basin_head, 8) + 1
        p3_basin_count = min(p3_basin_count + 1, 8)
        p3_dry_streak  = 0
    end

    @inline function p3_next_anchor()
        # Basin steer if cold long enough.
        if p3_dry_streak >= P3_BASIN_TRIGGER && p3_basin_count > 0
            base = p3_basin_buf[mod(p3_basin_head - 2 + 8, 8) + 1]
            if base != 0
                anchor_cursor_p3 = mod(base - 1 + rand(-2:2), nF) + 1
                p3_dry_streak    = 0
            end
        end
        pt = fb[anchor_cursor_p3]
        # Inertia flip.
        if rand() < P3_INERTIA_FLIP
            nd = _small_primes_p3[mod(anchor_cursor_p3 + trial_idx, length(_small_primes_p3)) + 1]
            while nF > 1 && _gcd_p3(nd, nF) != 1; nd = mod(nd + 1, nF) + 1; end
            inertia_dir_p3 = nd
        end
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
        log_new = mod(rhs * powermod(unknown_coeff, ell - 2, ell), ellI)
        local_alog[fb[unknown_idx]] = log_new
        n_alog_extended += 1
    end

    # ── Helper: solve k from a pure-FB row ───────────────────────────────────
    # Returns k on success, nothing on inapplicable (β=0 or missing logs),
    # and ASSERTS on internal inconsistency (all logs present but k fails to verify).
    @inline function try_solve(fb_row::Dict{Int,Int}, neg_al::Int, neg_be::Int)::Union{Int,Nothing}
        if neg_be == 0
            # β=0 relation: pure G row, try to extend alog rather than solve for k.
            try_extend_alog!(fb_row, neg_al)
            return nothing
        end
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
        # Soft skip: one or more atom logs still unknown.
        all_known || return nothing
        k_try = mod((log_sum - neg_al) * powermod(neg_be, ell - 2, ell), ellI)
        if jac_mul(G, k_try, ell) == T
            return k_try
        end
        # All atom logs were present and β≠0, but k failed to verify.
        # This indicates an inconsistency in the relation or atom logs.
        @assert false "try_solve: bad relation — all atom logs present, β≠0, but k_try=$(k_try) failed verification (neg_al=$(neg_al), neg_be=$(neg_be))"
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
            k_try = mod(-c_al * powermod(c_be, ell - 2, ell), ellI)
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

        # Soft skip: atom log not yet known.
        (l_cur == -1 || l_pre == -1) && return nothing

        lhs   = mod(l_cur - l_pre, ellI)
        k_try = mod((lhs - c_al) * powermod(c_be, ell - 2, ell), ellI)

        if jac_mul(G, k_try, ell) == T
            return k_try
        end
        # Both atom logs present, β≠0, but k failed to verify — internal inconsistency.
        @assert false "try_solve_conj: bad relation — all atom logs present, β≠0, but k_try=$(k_try) failed verification (i0_cur=$(i0_cur), i0_pre=$(i0_pre), c_al=$(c_al), c_be=$(c_be), lhs=$(lhs))"
    end

    # ── Main walk loop ────────────────────────────────────────────────────────

    for _ in 1:step_cap
        si        = rand(1:n_steps_prebuilt)
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a[si], ellI)
        beta_cur  = mod(beta_cur  + step_b[si], ellI)
        beta_cur == 0 && continue

        # Gate 1: degree-2 divisor
        fp3_deg(D_cur.u) != 2 && continue
        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]
        px, py = cur_pt

        # Gate 2: P0 not in support of D_cur
        fp(fp(px*px) + fp(u1*px) + u0) == 0 && continue

        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a_c, b_c, c_c, _ = phi_c

        res_R, res_S, RS_mumford = phi_residual_mumford(a_c, b_c, c_c, px, u0, u1)
        RS_mumford === SENTINEL_MUMFORD && continue

        n_steps += 1

        neg_al = mod(ellI - alpha_cur, ellI)
        neg_be = mod(ellI - beta_cur,  ellI)
        i0     = get(pt2idx, cur_pt, 0)

        # ======================================================================
        #  BRANCH A: conjugate residual
        # ======================================================================
        if res_R === SENTINEL_PT
            lp_key = canonical_lp1_conj_key(RS_mumford::NTuple{4,Int})

            if i0 != 0
                # A1: 1-LP-conj — P0 is in FB, RS pair is the LP atom
                n_conj_branch += 1
                si_shard = conj_shard_idx(lp_key)

                if conj_haskey(lp1_conj_pre, si_shard, lp_key)
                    # Close against precomputed entry (read-only — no delete).
                    # Precomputed table is amortized: neg_be was always 0.
                    v = conj_getval(lp1_conj_pre, si_shard, lp_key)
                    prev_col = Int(v.i0)
                    prev_al  = Int(v.neg_al)
                    c_al = mod(neg_al - prev_al, ellI)
                    c_be = neg_be   # mod(neg_be - 0, ellI) == neg_be
                    n_1lp_conj_pre += 1
                    k_rec = try_solve_conj(i0, prev_col, c_al, c_be)
                    k_rec !== nothing && break
                    # IDEA 4: successful LP1-conj step — record basin hit.
                    p3_record_basin!(anchor_cursor_p3)

                elseif haskey(local_lp1_conj, lp_key)
                    # Close against local birthday entry
                    v = local_lp1_conj[lp_key]
                    prev_col, prev_al, prev_be = Int(v.i0), Int(v.neg_al), Int(v.neg_be)
                    c_al = mod(neg_al - prev_al, ellI)
                    c_be = mod(neg_be - prev_be, ellI)
                    delete!(local_lp1_conj, lp_key)
                    n_1lp_conj_local += 1
                    k_rec = try_solve_conj(i0, prev_col, c_al, c_be)
                    k_rec !== nothing && break
                    # IDEA 4: record basin hit for local closure too.
                    p3_record_basin!(anchor_cursor_p3)
                else
                    if length(local_lp1_conj) < local_lp_cap
                        local_lp1_conj[lp_key] = LP1ConjValFull(UInt16(i0), UInt64(neg_al), UInt64(neg_be))
                    end
                    # Non-productive conj step: advance dry streak.
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
        @printf("[phase3 trial %d | t=%.3fs] k_rec=%s  k_true=%s  match=%s  steps=%d  0lp=%d  1lp_aff_pre=%d  1lp_aff_local=%d  1lp_conj_pre=%d  1lp_conj_local=%d  conj_branch=%d  alog_ext=%d\n",
                trial_idx, elapsed, k_rec_s, k_true_s, match_s,
                n_steps, n_0lp, n_1lp_aff_pre, n_1lp_aff_local, n_1lp_conj_pre, n_1lp_conj_local, n_conj_branch, n_alog_extended)
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
    if !isempty(tables.rel_rows_pre)
        t_enrich  = time()
        n_pre     = length(tables.atom_log_dict)
        ellI_e    = Int(tables.ell)
        nF_e      = length(tables.fb)

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
                    known_sum = mod(known_sum + coef * lj, ellI_e)
                end
            end
            (!valid || unk_j == 0) && continue   # 0 or 2+ unknowns

            # Solve: unk_coef * log(fb[unk_j]) ≡ neg_al - known_sum  (mod ell)
            rhs = mod(neg_al - known_sum, ellI_e)
            gcd(unk_coef, ellI_e) != 1 && continue   # non-invertible (shouldn't happen, ell prime)
            log_new = mod(rhs * powermod(unk_coef, ellI_e - 2, ellI_e), ellI_e)

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
    @sync for i in 1:n
        Threads.@spawn begin
            T_i, k_true_i = targets[i]
            results[i] = phase3_trial_worker(i, T_i, k_true_i, tables, G;
                                              step_cap=step_cap, verbose=verbose)
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
