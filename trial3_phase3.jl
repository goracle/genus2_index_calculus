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
    shared_lp1_conj::ShardedLP1Conj
    shared_lp2_conj::LP2ConjGraph

    # Group order
    ell            ::BigInt
end

# ---------------------------------------------------------------------------
#  Phase3Result  —  result record for a single target
# ---------------------------------------------------------------------------
struct Phase3Result
    target_idx     ::Int
    k_recovered    ::Union{Int, Nothing}
    k_true         ::Union{Int, Nothing}   # nothing if not a test run
    n_steps        ::Int
    n_0lp_hits     ::Int
    n_1lp_preclose ::Int   # closures against shared_lp1_pre
    n_1lp_local    ::Int   # closures against local lp1 dict
    elapsed_s      ::Float64
    success        ::Bool
end

# ---------------------------------------------------------------------------
#  Internal: one walk step evaluation.
#
#  Returns the phi residual (P0, R, S) and the fb_row dict (sparse vector of
#  FB column indices → coefficients for the three atoms that appear), or
#  nothing if the step is degenerate.
#
#  Reuses the same phi infrastructure as phase2_worker.
# ---------------------------------------------------------------------------
@inline function _p3_eval_step(
        D_cur  ::Div2,
        cur_pt ::NTuple{2,Int},
        pt2idx ::Dict{NTuple{2,Int}, Int})

    fp3_deg(D_cur.u) != 2 && return nothing
    u0 = D_cur.u[1]; u1 = D_cur.u[2]
    v0 = D_cur.v[1]; v1 = D_cur.v[2]
    px, py = cur_pt

    fp(fp(px*px) + fp(u1*px) + u0) == 0 && return nothing

    phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
    phi_c === nothing && return nothing
    a, b, c, _ = phi_c

    R, S, rs_mumford = phi_residual_mumford(a, b, c, px, u0, u1)
    rs_mumford === SENTINEL_MUMFORD && return nothing
    R === SENTINEL_PT && return nothing    # conjugate pair — skip for now

    i0 = get(pt2idx, cur_pt, 0)
    iR = get(pt2idx, R,      0)
    iS = get(pt2idx, S,      0)

    return (P0=cur_pt, R=R, S=S, i0=i0, iR=iR, iS=iS)
end

# ---------------------------------------------------------------------------
#  _p3_build_fb_row  —  build the sparse FB row dict for a step
#
#  Returns Dict{Int,Int} with entries for the in-FB atoms, and the lp_pt
#  (the single out-of-FB atom) if exactly one is missing, or nothing if
#  ≥2 are missing.
# ---------------------------------------------------------------------------
function _p3_build_fb_row(hit, pt2idx)
    i0, iR, iS = hit.i0, hit.iR, hit.iS
    n_lp = (i0 == 0 ? 1 : 0) + (iR == 0 ? 1 : 0) + (iS == 0 ? 1 : 0)

    # Build the partial FB row (only in-FB atoms).
    fb_row = Dict{Int,Int}()
    i0 != 0 && (fb_row[i0] = get(fb_row, i0, 0) + 1)
    iR != 0 && (fb_row[iR] = get(fb_row, iR, 0) + 1)
    iS != 0 && (fb_row[iS] = get(fb_row, iS, 0) + 1)

    lp_pt = n_lp == 1 ? (i0 == 0 ? hit.P0 : iR == 0 ? hit.R : hit.S) : nothing

    return (fb_row=fb_row, n_lp=n_lp, lp_pt=lp_pt)
end

# ---------------------------------------------------------------------------
#  phase3_trial_worker
#
#  Runs the β≠0 walk for a single target T and returns a Phase3Result.
#
#  Arguments:
#    trial_idx   — index for logging
#    T           — target divisor (T = k·G, k unknown)
#    k_true      — ground truth for verification runs (nothing in production)
#    tables      — Phase2Tables from precompute
#    G           — generator
#    step_cap    — maximum walk steps before giving up
#    n_steps_prebuilt — size of the prebuilt random step table
# ---------------------------------------------------------------------------
function phase3_trial_worker(
        trial_idx        ::Int,
        T                ::Div2,
        k_true           ::Union{Int,Nothing},
        tables           ::Phase2Tables,
        G                ::Div2;
        step_cap         ::Int   = 10_000_000,
        n_steps_prebuilt ::Int   = 512,
        verbose          ::Bool  = false)::Phase3Result

    t0 = time()
    ell      = tables.ell
    ellI     = Int(ell)
    pt2idx   = tables.pt2idx
    fb       = tables.fb
    nF       = length(fb)
    alog     = tables.atom_log_dict
    lp1_pre  = tables.shared_lp1    # READ ONLY

    # ── Prebuilt step table for the β≠0 walk ─────────────────────────────────
    step_D  = Vector{Div2}(undef, n_steps_prebuilt)
    step_a  = Vector{Int}(undef,  n_steps_prebuilt)
    step_b  = Vector{Int}(undef,  n_steps_prebuilt)
    for i in 1:n_steps_prebuilt
        a = rand(1:ellI-1); b = rand(1:ellI-1)
        step_D[i] = jac_add(jac_mul(G, a, ell), jac_mul(T, b, ell))
        step_a[i] = a; step_b[i] = b
    end

    # ── Walk state ────────────────────────────────────────────────────────────
    alpha_cur = rand(1:ellI-1)
    beta_cur  = rand(1:ellI-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur, ell), jac_mul(T, beta_cur, ell))
    cur_pt    = fb[rand(1:nF)]

    # ── Local 1-LP birthday table ─────────────────────────────────────────────
    # Entry: lp_pt → (fb_row::Dict{Int,Int}, neg_al::Int, neg_be::Int)
    local_lp1 = Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}}()

    # ── Counters ──────────────────────────────────────────────────────────────
    n_steps        = 0
    n_0lp          = 0
    n_1lp_preclose = 0
    n_1lp_local    = 0
    k_rec          = nothing

    # ── Helper: attempt to solve k from a pure-FB relation ───────────────────
    @inline function try_solve(fb_row::Dict{Int,Int}, neg_al::Int, neg_be::Int)::Union{Int,Nothing}
        neg_be == 0 && return nothing    # β=0 can't give k

        log_sum = 0
        for (j, v) in fb_row
            log_sum = mod(log_sum + v * get(alog, fb[j], 0), ellI)
        end
        # relation: log_sum ≡ neg_al + neg_be · k  (mod ell)
        k_try = mod((log_sum - neg_al) * powermod(neg_be, ell - 2, ell), ellI)

        # Verify: jac_mul(G, k_try, ell) should equal T
        jac_mul(G, k_try, ell) == T && return k_try
        return nothing
    end

    # ── Walk ──────────────────────────────────────────────────────────────────
    for _ in 1:step_cap
        # Advance walk state
        si         = rand(1:n_steps_prebuilt)
        D_cur      = jac_add(D_cur, step_D[si])
        alpha_cur  = mod(alpha_cur + step_a[si], ellI)
        beta_cur   = mod(beta_cur  + step_b[si], ellI)
        beta_cur  == 0 && continue

        n_steps += 1

        hit = _p3_eval_step(D_cur, cur_pt, pt2idx)
        hit === nothing && continue

        # neg_al = ell - alpha_cur,  neg_be = ell - beta_cur
        # relation: [P0]+[R]+[S]  ≡  neg_al·G + neg_be·T
        neg_al = mod(ellI - alpha_cur, ellI)
        neg_be = mod(ellI - beta_cur,  ellI)

        row_info = _p3_build_fb_row(hit, pt2idx)
        n_lp     = row_info.n_lp
        fb_row   = row_info.fb_row

        # ── Strategy 0: 0-LP direct solve ────────────────────────────────────
        if n_lp == 0
            n_0lp += 1
            k_rec = try_solve(fb_row, neg_al, neg_be)
            k_rec !== nothing && break
            cur_pt = hit.R    # advance anchor
            continue
        end

        # ── Strategy 1 & 2: 1-LP ─────────────────────────────────────────────
        if n_lp == 1
            lp_pt = row_info.lp_pt

            # Strategy 1: close against precompute shared_lp1
            # The stored entry has neg_be_pre = 0 (β=0 walk).
            if haskey(lp1_pre, lp_pt)
                pre_row, pre_neg_al, pre_neg_be, _ = lp1_pre[lp_pt]
                # Eliminate lp_pt:
                #   (fb_row_cur + atom(lp_pt))  -  (pre_row + atom(lp_pt))
                #   = fb_row_cur - pre_row  ≡  (neg_al - pre_neg_al)·G + neg_be·T
                combined = copy(fb_row)
                for (j, v) in pre_row
                    nv = get(combined, j, 0) - v
                    nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                end
                c_neg_al = mod(neg_al - pre_neg_al, ellI)
                c_neg_be = mod(neg_be - pre_neg_be, ellI)   # pre_neg_be == 0

                n_1lp_preclose += 1
                k_rec = try_solve(combined, c_neg_al, c_neg_be)
                k_rec !== nothing && break

            # Strategy 2: close against local birthday table
            elseif haskey(local_lp1, lp_pt)
                prev_row, prev_neg_al, prev_neg_be = local_lp1[lp_pt]
                combined = copy(fb_row)
                for (j, v) in prev_row
                    nv = get(combined, j, 0) - v
                    nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                end
                c_neg_al = mod(neg_al - prev_neg_al, ellI)
                c_neg_be = mod(neg_be - prev_neg_be, ellI)

                delete!(local_lp1, lp_pt)
                n_1lp_local += 1
                k_rec = try_solve(combined, c_neg_al, c_neg_be)
                k_rec !== nothing && break
            else
                # Park in local table for a future closure
                local_lp1[lp_pt] = (copy(fb_row), neg_al, neg_be)
            end
        end

        # Advance the anchor to a known FB point
        cur_pt = hit.iR != 0 ? hit.R : (hit.iS != 0 ? hit.S : fb[rand(1:nF)])
    end

    elapsed = time() - t0
    success = k_rec !== nothing
    verified = k_true === nothing || k_rec == k_true

    if verbose
        k_rec_s   = k_rec   === nothing ? "none" : string(k_rec)
        k_true_s  = k_true  === nothing ? "?"    : string(k_true)
        match_s   = verified ? "ok" : "MISMATCH"
        @printf("[phase3 trial %d | t=%.3fs] k_rec=%s  k_true=%s  match=%s  steps=%d  0lp=%d  1lp_pre=%d  1lp_local=%d\n",
                trial_idx, elapsed, k_rec_s, k_true_s, match_s,
                n_steps, n_0lp, n_1lp_preclose, n_1lp_local)
        flush(stdout)
    end

    return Phase3Result(
        trial_idx,
        k_rec,
        k_true,
        n_steps,
        n_0lp,
        n_1lp_preclose,
        n_1lp_local,
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
        step_cap ::Int  = 10_000_000,
        verbose  ::Bool = true)::Vector{Phase3Result}

    n = length(targets)
    results = Vector{Phase3Result}(undef, n)

    println("── Phase 3: amortised DLP solves ────────────────────────────────────")
    @printf("   targets=%d  threads=%d  FB=%d  lp1_pre_entries=%d  step_cap=%d\n",
            n, Threads.nthreads(), length(tables.fb),
            length(tables.shared_lp1), step_cap)
    flush(stdout)

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

    println()
    @printf("── Phase 3 summary ──────────────────────────────────────────────────\n")
    @printf("  %d / %d targets solved correctly\n", n_ok, n)
    @printf("  total steps: %d  (avg %.1f/target)\n", total_steps, avg_steps)
    @printf("  closure breakdown: 0-LP=%d  1LP-preclose=%d  1LP-local=%d\n",
            n_0lp_tot, n_pre, n_loc)
    @printf("  wall time: %.3fs\n", time() - t0)
    println("="^70)
    flush(stdout)

    return results
end
