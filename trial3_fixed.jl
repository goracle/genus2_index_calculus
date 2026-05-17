#!/usr/bin/env julia
# =============================================================================
#  trial3_fixed.jl  --  Index calculus via Markov-walk / phi-function relations
#
#  File layout:
#    trial3_config.jl   constants, shared structs (ShardedLP1Conj, WorkerStats)
#    trial3_phi.jl      phi construction, residual, relation-integrity asserts
#    trial3_tree.jl     WalkGuidance, LPStageTree, sparse helpers, lp2 wrappers
#    trial3_linalg.jl   left_kernel_all, matrix diagnostics
#    trial3_phase2.jl   phase2_worker and its LP-closure helpers
#    lp2.jl             LP2Graph spanning-tree (affine)
#    lp2_conj.jl        LP2ConjGraph (mixed affine/Mumford-pair)
#
#  Entry points:
#    main2()            run with keyword args
#    main2_from_argv()  parse ARGS and call main2()
#
#  Generator bootstrap:
#    Instead of Pollard rho (O(√#J) expected), we shell out to Sage for the
#    exact Frobenius polynomial → #J(F_p), factor with Oscar/FLINT, take the
#    largest prime factor as ell, and multiply a random divisor by the cofactor.
#    This is deterministic and O(p^{1/2} polylog p) via Kedlaya / hypellfrob.
# =============================================================================

include("trial1_autoell_p10.jl")   # all Fp/poly/Jacobian/curve utilities
using LinearAlgebra
using Base.Threads
using Random
using Nemo
using Dates

include("lp_residual_stats.jl")   # LP residual diagnostics
include("kernel_phase_diag.jl")   # phase-transition instrumentation
include("early_solve_monitor.jl") # online b₁ / 2-core / DSU diagnostics

include("trial3_config.jl")
include("trial3_phi.jl")

# ---------------------------------------------------------------------------
#  mem_checkpoint — fine-grained RSS/GC-live probe with delta tracking
# ---------------------------------------------------------------------------
let _mem_prev = Ref(0.0)
    global function mem_checkpoint(tag::String)
        rss  = Sys.maxrss() / 1024^2
        live = Base.gc_live_bytes() / 1024^2
        Δ    = live - _mem_prev[]
        @printf("[MEM @%-38s]  RSS=%7.1f MB  GC-live=%7.1f MB  Δlive=%+7.1f MB\n",
                tag, rss, live, Δ)
        flush(stdout)
        _mem_prev[] = live
        return live
    end
end
include("trial3_tree.jl")
include("lp2.jl")
include("lp2_conj.jl")
include("trial3_linalg.jl")
include("trial3_phase2.jl")
include("trial3_amortized.jl")
include("trial3_phase3.jl")

# Safe wrapper around the kernel-phase diagnostics.  These are helpful, but
# they should never be able to abort a successful solve.
function safe_kernel_phase_instrumentation(args...; kwargs...)
    if !@isdefined(kernel_phase_instrumentation)
        return nothing
    end
    try
        return kernel_phase_instrumentation(args...; kwargs...)
    catch kpe
        @printf("  [kernel_phase_diag] skipped: %s\n", string(kpe))
        return nothing
    end
end

# ---------------------------------------------------------------------------
#  Exact #J(F_p) via Sage frobenius_polynomial
# ---------------------------------------------------------------------------
"""
    frobenius_jacobian_order() -> (N, ell, h)

Shell out to Sage to compute the Frobenius polynomial of J(C/F_p), evaluate
at 1 to get N = #J(F_p), then factor with Oscar/FLINT to extract
ell = largest prime factor and cofactor h = N/ell.

Sage uses Kedlaya's p-adic algorithm (hypellfrob) — O(p^{1/2} polylog p) —
so this is fast even for p ~ 10^6.
"""
function frobenius_jacobian_order()::Tuple{BigInt,BigInt,BigInt}
    sage_script = """
p = $(p)
F = GF(p)
R.<x> = F[]
f = x^5 + 3*x^3 + 2*x^2 + 5*x + 4
H = HyperellipticCurve(f)
chi = H.frobenius_polynomial()
N = ZZ(chi(1))
print(int(N))
"""
    mem_checkpoint("before sage shell-out")
    raw     = readchomp(`sage -c $sage_script`)
    N_big   = parse(BigInt, strip(raw))
    oz      = Oscar.ZZ(N_big)
    fac     = Oscar.factor(oz)
    ell_big = BigInt(maximum(q for (q, _) in fac))
    h_big   = N_big ÷ ell_big
    return N_big, ell_big, h_big
end

# ---------------------------------------------------------------------------
#  Generator bootstrap via exact Frobenius order
# ---------------------------------------------------------------------------
function frobenius_find_ell_generator(pts::Vector{NTuple{2,Int}})::Tuple{Div2,Int}
    t0 = time()
    print("  Computing #J via Sage frobenius_polynomial... ")
    flush(stdout)
    N, ell_big, h = frobenius_jacobian_order()
    @printf("done (%.3fs)\n", time() - t0)
    @printf("  #J = %d\n", N)
    @printf("  factorisation: %s\n", string(Oscar.factor(Oscar.ZZ(N))))
    mem_checkpoint("after Oscar bootstrap")
    @printf("  ell = %d  (%.1f bits)\n", ell_big, log2(ell_big))
    @printf("  cofactor h = %d\n", h)
    ell_big <= typemax(Int) || throw(OverflowError(
        "ell=$ell_big exceeds typemax(Int)=$(typemax(Int)); p is too large for Int64 arithmetic"))
    ell_found = Int(ell_big)

    n = length(pts)
    n < 2 && error("Not enough rational affine points on the curve")

    attempts = 0
    while true
        attempts += 1
        P = pts[rand(1:n)]
        Q = pts[rand(1:n)]
        D = mumford_from_pts(P, Q)
        jac_isid(D) && continue
        G = jac_mul_raw(D, h)
        jac_isid(G) && continue    # unlucky; retry

        @assert jac_isid(jac_mul_raw(G, ell_found)) "ell*G != id — Frobenius order wrong?"
        @printf("  found G in %d attempt(s), total bootstrap time: %.3fs\n",
                attempts, time() - t0)
        return G, ell_found
    end
end

# ---------------------------------------------------------------------------
#  Phase 1: self-building factor base via the phi walk
#
#  Walk until the FB reaches fb_cap points.  At each step:
#    - P0 is the current anchor (guaranteed in FB from previous step).
#    - Pick random α, β; form D = αG + βT.
#    - Build φ through P0 and D; recover R, S.
#    - Check membership of P0, R, S BEFORE growing the FB.
#    - If all three were already in FB, bank the relation.
#    - Add R and S to FB if new (P0 is always already in FB).
#    - Set cur_pt = R for the next step.
#
#  Conjugate-pair residuals (R, S over F_p²) are skipped in phase 1 —
#  the FB consists only of affine F_p-rational points.
#
#  Returns (fb, pt2idx, alpha_vec, beta_vec, rel_rows).
# ---------------------------------------------------------------------------
function phase1_walk(G::Div2, T::Div2, fb_cap::Int; verbose::Bool = true,
                     beta_zero::Bool = false)
    seed_pts = curve_points()
    isempty(seed_pts) && error("No rational points on curve for phase-1 seed")

    fb     = sizehint!(NTuple{2,Int}[], fb_cap)
    pt2idx = sizehint!(Dict{NTuple{2,Int},Int}(), fb_cap)

    alpha_vec = BigInt[]
    beta_vec  = BigInt[]
    rel_rows  = Vector{Dict{Int,Int}}()

    function maybe_add!(pt::NTuple{2,Int})
        haskey(pt2idx, pt) && return
        length(fb) >= fb_cap && return
        push!(fb, pt)
        pt2idx[pt] = length(fb)
    end

    cur_pt = seed_pts[rand(1:length(seed_pts))]
    maybe_add!(cur_pt)   # seed is always the first FB entry

    raw_steps   = 0
    hits_valid  = 0
    hits_banked = 0
    t0 = time()

    while true
        raw_steps += 1
        α = rand(1:ell-1)
        β = beta_zero ? 0 : rand(0:ell-1)
        D = beta_zero ? jac_mul(G, α, ell) :
                        jac_add(jac_mul(G, α, ell), jac_mul(T, β, ell))

        fp3_deg(D.u) != 2 && continue

        u0 = D.u[1]; u1 = D.u[2]
        v0 = D.v[1]; v1 = D.v[2]

        px, py = cur_pt
        upx = fp(fp(px*px) + fp(u1*px) + u0)
        upx == 0 && continue

        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a, b, c, _ = phi_c

        R, S, rs_mumford = phi_residual_mumford(a, b, c, px, u0, u1)
        rs_mumford === SENTINEL_MUMFORD && continue
        R === SENTINEL_PT && continue   # conjugate pair — skip in phase 1

        hits_valid += 1

        # How many new points would this step add?
        r_new = !haskey(pt2idx, R)
        s_new = !haskey(pt2idx, S)
        slots_needed = (r_new ? 1 : 0) + (s_new ? 1 : 0)
        slots_free   = fb_cap - length(fb)

        if slots_needed > slots_free
            # FB is full enough — stop and let phase 2 collect LP relations.
            break
        end

        maybe_add!(R)
        maybe_add!(S)

        i0 = pt2idx[cur_pt]
        iR = pt2idx[R]
        iS = pt2idx[S]

        neg_al = mod(ell - α, ell)
        neg_be = mod(ell - β, ell)
        row = Dict{Int,Int}()
        for idx in (i0, iR, iS)
            row[idx] = get(row, idx, 0) + 1
        end
        push!(alpha_vec, neg_al); push!(beta_vec, neg_be); push!(rel_rows, row)
        hits_banked += 1

        cur_pt = R   # chain: next anchor is R
        length(fb) >= fb_cap && break
    end

    if verbose
        @printf("── Phase 1 done ────────────────────────────────────────────────────\n")
        @printf("  raw steps:        %d\n", raw_steps)
        @printf("  valid phi hits:   %d\n", hits_valid)
        @printf("  FB built:         %d / %d cap\n", length(fb), fb_cap)
        @printf("  relations banked: %d\n", hits_banked)
        @printf("  wall time:        %.3fs\n", time() - t0)
        flush(stdout)
    end

    return fb, pt2idx, alpha_vec, beta_vec, rel_rows
end

# ---------------------------------------------------------------------------
#  index_calculus_walk — orchestrates phase 1, phase 2, and LA solve
# ---------------------------------------------------------------------------
function index_calculus_walk(G::Div2, T::Div2;
                             fb_size          ::Int  = 650,
                             verbose          ::Bool = true,
                             analyze_matrix   ::Bool = true,
                             asymptotic       ::Bool = true,
                             solve            ::Bool = true,
                             guided           ::Bool = true,
                             enable_lp2       ::Bool = true,
                             enable_lp2_conj  ::Bool = true,
                             max_lp2_nodes    ::Int  = DEFAULT_MAX_LP2_NODES,
                             max_lp2_conj_nodes::Int = DEFAULT_MAX_LP2_CONJ_NODES,
                             use_cycle_union  ::Bool = false)

    t_walk_start = time()

    # ── Phase 1: build the factor base ───────────────────────────────────────
    if verbose
        println()
        @printf("── Phase 1: building factor base ───────────────────────────────────\n")
        @printf("  FB cap:    %d  (walk until full)\n", fb_size)
        flush(stdout)
    end

    fb, pt2idx, p1_alpha, p1_beta, p1_rows =
        phase1_walk(G, T, fb_size; verbose=verbose)

    nF    = length(fb)
    n_all = length(curve_points())   # full curve count for step_cap formula

    if verbose
        cov = nF / max(1, n_all)
        println()
        @printf("── Factor base (after phase 1) ─────────────────────────────────────\n")
        @printf("  FB size:          %d / %d cap\n", nF, fb_size)
        @printf("  relations banked: %d\n", length(p1_rows))
        @printf("  curve coverage:   %.4f%%  (FB / ~%d total curve pts)\n",
                100.0 * cov, n_all)
        @printf("  x-range of FB:    [%d, %d]\n",
                minimum(pt[1] for pt in fb), maximum(pt[1] for pt in fb))
        @printf("  expected full-rel prob per valid step: ~%.2e  (FB/total)^2\n", cov^2)
        @printf("  expected full-rel prob incl. LP:       ~%.2e\n", 2*cov*(1-cov))
        flush(stdout)
    end

    # ── Precompute walk steps ─────────────────────────────────────────────────
    t_step_build = time()
    N_STEPS = 256
    step_D  = Vector{Div2}(undef, N_STEPS)
    step_a  = Vector{BigInt}(undef, N_STEPS)
    step_b  = Vector{BigInt}(undef, N_STEPS)
    for i in 1:N_STEPS
        a = BigInt(rand(1:ell-1)); b = BigInt(rand(1:ell-1))
        step_D[i] = jac_add(jac_mul(G, Int(a), ell), jac_mul(T, Int(b), ell))
        step_a[i] = a; step_b[i] = b
    end
    t_step_done = time() - t_step_build

    # ── Relation target and step cap ─────────────────────────────────────────
    target_excess      = max(20, nF ÷ 10)
    rel_target_total   = nF + 1 + target_excess
    p1_banked          = length(p1_rows)
    rel_target         = max(1, rel_target_total - p1_banked)
    rel_counter        = Threads.Atomic{Int}(0)

    # Step cap derived from smoothness geometry (no magic number):
    #   p_smooth = (nF/n_all)^2 + 2*(nF/n_all)*(1-nF/n_all)   (0-LP + 1-LP closure)
    #   phi_valid_rate ≈ (nF/n_all)^2  (conservative; 0-LP alone)
    #   steps_per_rel ≈ 1 / (p_smooth * phi_valid_rate)
    p_smooth_step      = (nF/n_all)^2 + 2*(nF/n_all)*(1-nF/n_all)
    phi_valid_rate_est = clamp((nF/n_all)^2, 1e-8, 1.0)
    steps_per_rel_est  = 1.0 / (p_smooth_step * phi_valid_rate_est)
    step_cap           = round(Int, steps_per_rel_est * rel_target / Threads.nthreads()) *
                         Threads.nthreads()

    # ── Shared walk state ─────────────────────────────────────────────────────
    shared_lp1            = Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}}()
    shared_lp1_lock       = ReentrantLock()
    shared_lp2            = LP2Graph()
    shared_lp2_lock       = ReentrantLock()
    shared_lp_doubled     = Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}}()
    shared_lp1_conj       = ShardedLP1Conj(ell)
    shared_lp2_conj       = LP2ConjGraph()
    shared_lp2_conj_lock  = ReentrantLock()

    set_lp2_principal_check_context!(fb, G, T)

    if verbose
        println()
        @printf("── Walk setup ──────────────────────────────────────────────────────\n")
        @printf("  N_STEPS (precomputed):  %d\n", N_STEPS)
        @printf("  step table build time:  %.3fs\n", t_step_done)
        @printf("  rel_target:             %d total  (%d after phase-1 credit of %d)\n",
                rel_target_total, rel_target, p1_banked)
        @printf("  p_smooth per step:      %.3e  (0-LP + LP-closure estimate)\n", p_smooth_step)
        @printf("  step_cap per thread:    %d  (derived from smoothness geometry)\n",
                step_cap ÷ Threads.nthreads())
        @printf("  2-LP (affine) enabled:  %s\n", string(enable_lp2))
        @printf("  2-LP cap (affine):      %d nodes\n", max_lp2_nodes)
        @printf("  conj LP2 enabled:       %s\n", string(enable_lp2_conj))
        @printf("  2-LP cap (conj):        %d nodes\n", max_lp2_conj_nodes)
        @printf("  threads:                %d\n", Threads.nthreads())
        @printf("  launching walkers at:   %s\n", string(Dates.now()))
        flush(stdout)
    end

    # ── Phase 2: multithreaded walk ───────────────────────────────────────────
    # One collector per thread: no locking needed during walk, merged after.
    thread_collectors = [LPResidualCollector() for _ in 1:Threads.nthreads()]
    results           = Vector{Any}(undef, Threads.nthreads())

    # Instantiate the tracker here so all threads can stream rows into it
    # (Ensure OnlineRankTracker is thread-safe or locked if your code requires it!)
    rank_tracker      = OnlineRankTracker(ell)

    t_phase2_start = time()
    @sync for tid in 1:Threads.nthreads()
        Threads.@spawn begin
            results[tid] = phase2_worker(
                G, T, fb, BigInt(ell), pt2idx,
                step_D, step_a, step_b,
                rel_counter, rel_target, step_cap ÷ Threads.nthreads(),
                shared_lp1, shared_lp1_lock,
                shared_lp2, shared_lp2_lock,
                shared_lp_doubled,
                shared_lp1_conj,
                shared_lp2_conj, shared_lp2_conj_lock,
                enable_lp2, enable_lp2_conj, max_lp2_nodes, max_lp2_conj_nodes,
                thread_collectors[tid], rank_tracker; verbose=verbose)
        end
    end
    t_phase2_done = time() - t_phase2_start

    # ── Merge results ─────────────────────────────────────────────────────────
    # Seed accumulators with phase-1 banked relations.
    alpha_vec     = copy(p1_alpha)
    beta_vec      = copy(p1_beta)
    rel_rows      = copy(p1_rows)
    all_samples   = similar(results[1].sample_rels, 0)

    hits_total    = 0; hits_full  = 0; hits_0lp  = 0
    hits_lp1      = 0; hits_1lp_emit = 0
    hits_lp2seen  = 0; hits_lp2emit  = 0
    hits_lp2_odd  = 0; hits_skip     = 0

    thread_hits  = Int[]; thread_full  = Int[]
    thread_lp1   = Int[]; thread_steps = Int[]

    for r in results
        append!(alpha_vec, r.alpha_vec)
        append!(beta_vec,  r.beta_vec)
        append!(rel_rows,  r.rel_rows)
        hits_total    += r.hits_total;  hits_full     += r.hits_full
        hits_0lp      += r.hits_0lp;    hits_lp1      += r.hits_lp1
        hits_1lp_emit += r.hits_1lp_emit
        hits_lp2seen  += r.hits_lp2seen; hits_lp2emit += r.hits_lp2emit
        hits_lp2_odd  += r.hits_lp2_odd; hits_skip    += r.hits_skip
        append!(all_samples, r.sample_rels)
        push!(thread_hits, r.hits_total); push!(thread_full, r.hits_full)
        push!(thread_lp1,  r.hits_lp1);  push!(thread_steps, r.total_steps)
    end
    nrel = length(rel_rows)

    if verbose
        println()
        @printf("── Walk results ────────────────────────────────────────────────────\n")
        @printf("  phase-1 banked relations: %d\n", length(p1_rows))
        @printf("  phase-2 wall time:     %.3fs\n", t_phase2_done)
        @printf("  total raw steps:       %d  (across all threads)\n", sum(thread_steps))
        @printf("  valid phi steps:       %d\n", hits_total)
        @printf("  phi validity rate:     %.4f%%\n",
                100.0 * hits_total / max(1, sum(thread_steps)))
        println()
        @printf("  smoothness breakdown:\n")
        @printf("    0-LP (pure FB):      %d  (%.2f%% of valid steps)\n",
                hits_0lp,      100.0 * hits_0lp      / max(1, hits_total))
        @printf("    1-LP steps:          %d  (%.2f%%)\n",
                hits_lp1,      100.0 * hits_lp1      / max(1, hits_total))
        @printf("    1-LP closures emit:  %d  (%.2f%%)\n",
                hits_1lp_emit, 100.0 * hits_1lp_emit / max(1, hits_total))
        @printf("    2-LP seen:           %d  (%.2f%%)\n",
                hits_lp2seen,  100.0 * hits_lp2seen  / max(1, hits_total))
        @printf("    2-LP closures emit:  %d  (%.2f%%)\n",
                hits_lp2emit,  100.0 * hits_lp2emit  / max(1, hits_total))
        @printf("    2-LP odd stored:     %d  (%.2f%%)\n",
                hits_lp2_odd,  100.0 * hits_lp2_odd  / max(1, hits_total))
        @printf("    3-LP skips:          %d  (%.2f%%)\n",
                hits_skip,     100.0 * hits_skip      / max(1, hits_total))
        println()
        @printf("  2-LP graph stats (affine):\n")
        @printf("    edges inserted:      %d\n",  shared_lp2.n_edges_inserted)
        @printf("    cycles found:        %d\n",  shared_lp2.n_cycles_found)
        @printf("    relations emitted:   %d\n",  shared_lp2.n_emitted)
        @printf("    depth-pruned:        %d\n",  shared_lp2.n_depth_pruned)
        @printf("    weight-pruned:       %d\n",  shared_lp2.n_weight_pruned)
        @printf("    parity-pruned:       %d\n",  shared_lp2.n_parity_pruned)
        @printf("    odd-cycle stored:    %d\n",  shared_lp2.n_odd_stored)
        @printf("    LP nodes in graph:   %d\n",  lp2_graph_node_count(shared_lp2))
        @printf("    lp_doubled residual: %d entries\n", length(shared_lp_doubled))
        @printf("  2-LP graph stats (QLP/conj):\n")
        @printf("    edges inserted:      %d\n",  shared_lp2_conj.n_edges_inserted)
        @printf("    cycles found:        %d\n",  shared_lp2_conj.n_cycles_found)
        @printf("    relations emitted:   %d\n",  shared_lp2_conj.n_emitted)
        @printf("    depth-pruned:        %d\n",  shared_lp2_conj.n_depth_pruned)
        @printf("    weight-pruned:       %d\n",  shared_lp2_conj.n_weight_pruned)
        @printf("    parity-pruned:       %d\n",  shared_lp2_conj.n_parity_pruned)
        cycle_rate = shared_lp2.n_cycles_found  / max(1, shared_lp2.n_edges_inserted)
        emit_rate  = shared_lp2.n_emitted       / max(1, shared_lp2.n_cycles_found)
        @printf("    cycle/edge rate:     %.4f\n", cycle_rate)
        @printf("    emit/cycle rate:     %.4f  (pruning loss)\n", emit_rate)
        println()
        @printf("  total relations collected:   %d\n", nrel)
        @printf("  FB size (nF):                %d\n", nF)
        @printf("  relation surplus:            %+d\n", nrel - (nF + 1))
        @printf("  relation yield rate:         %.4e rels/sec\n",
                nrel / max(1e-9, t_phase2_done))
        @printf("  full-rel yield rate:         %.4e rels/sec\n",
                hits_full / max(1e-9, t_phase2_done))
        @printf("  steps per full relation:     %.1f\n",
                sum(thread_steps) / max(1, hits_full))
        @printf("  1-LP table size (residual):  %d entries\n", length(shared_lp1))
        @printf("  1-LP pair rate:              %.4f  (LP-closures / LP-steps)\n",
                hits_1lp_emit / max(1, hits_lp1))
        println()
        @printf("  per-thread breakdown:\n")
        for tid in 1:length(thread_hits)
            @printf("    thread %d: steps=%d  valid=%d  full=%d  1-LP=%d\n",
                    tid, thread_steps[tid], thread_hits[tid],
                    thread_full[tid], thread_lp1[tid])
        end
        flush(stdout)
    end

    analyze_matrix && analyze_relation_matrix(rel_rows, nF; verbose=verbose)
    analyze_matrix && spectral_gap_report(rel_rows, nF; verbose=verbose)
    asymptotic && asymptotic_report(rel_rows, nF;
                                    hits_total=hits_total,
                                    walk_steps=sum(thread_steps),
                                    hits_full=hits_full, hits_tree=hits_0lp,
                                    hits_lp=hits_lp1, hits_lp2=hits_lp2emit,
                                    verbose=verbose)

    if verbose
        merged_col = merge_collectors(thread_collectors)
        lp_residual_report(merged_col; p_field=p, verbose=true)
    end

    if !solve
        return (k=nothing, rel_rows=rel_rows, alpha_vec=alpha_vec,
                beta_vec=beta_vec, nF=nF, shortfall=false)
    end

    # ── Pre-solve cleanup ─────────────────────────────────────────────────────
    empty!(shared_lp1); clear_lp2_graph!(shared_lp2); empty!(all_samples)
    GC.gc()
    ccall((:flint_set_num_threads, :libflint), Cvoid, (Cint,), 1)  # avoid FLINT/Julia pthread deadlock

    if verbose
        println()
        @printf("── Pre-solve diagnostics ───────────────────────────────────────────\n")
        @printf("  nrel=%d, nF=%d\n", nrel, nF)
        @printf("  alpha_vec range: [%d, %d]\n", extrema(alpha_vec)...)
        @printf("  beta_vec range:  [%d, %d]\n", extrema(beta_vec)...)
        weights = [length(rel_rows[i]) for i in 1:nrel]
        @printf("  row weight: min=%d, max=%d, mean=%.2f, median=%d\n",
                minimum(weights), maximum(weights),
                sum(weights)/nrel, sort(weights)[(length(weights)+1)÷2])
        n_zero_row = count(isempty, rel_rows)
        n_zero_ab  = count(i -> alpha_vec[i]==0 && beta_vec[i]==0, 1:nrel)
        @printf("  zero rows: %d,  zero-alpha-and-beta: %d\n", n_zero_row, n_zero_ab)

        all_rg = vcat([r.rank_growth for r in results]...)
        if !isempty(all_rg)
            total_raw = sum(r.total_steps for r in results)
            @printf("  rank growth: %d emissions logged across threads\n", length(all_rg))
            @printf("  total raw steps (all threads): %d\n", total_raw)
            @printf("  raw steps per full emission (global): %.1f\n",
                    total_raw / max(1, hits_full))
        end

        agg_hist = zeros(Int, 4)
        for r in results; agg_hist .+= r.smooth_hist; end
        @printf("  global smoothness histogram (0-LP 1-LP 2-LP 3-LP): %d %d %d %d\n",
                agg_hist...)
        total_smooth = sum(agg_hist)
        if total_smooth > 0
            @printf("  smoothness fractions: 0-LP=%.3f  1-LP=%.3f  2-LP=%.3f  3-LP=%.3f\n",
                    agg_hist[1]/total_smooth, agg_hist[2]/total_smooth,
                    agg_hist[3]/total_smooth, agg_hist[4]/total_smooth)
        end

        @printf("  spot-checking %d full relations:\n", min(5, length(all_samples)))
        n_ok = 0; n_bad = 0
        for (D_stored, fb_row, neg_al, neg_be, P0, R, S) in all_samples[1:min(5,end)]
            lhs    = jac_add(jac_mul(G, neg_al, ell), jac_mul(T, neg_be, ell))
            neg_D  = jac_neg(D_stored)
            step_ok = (lhs == neg_D)
            @printf("    neg_al=%d neg_be=%d  neg_al*G+neg_be*T == -D_cur: %s\n",
                    neg_al, neg_be, step_ok)
            step_ok ? (n_ok += 1) : (n_bad += 1)
        end
        @printf("  spot-check: %d ok, %d BAD\n", n_ok, n_bad)
        @printf("  ell*G == id: %s,  ell = %d\n", jac_isid(jac_mul_raw(G, ell)), ell)
        flush(stdout)
    end

    # ── Incremental solve: add phase-2 relations in 5% chunks ────────────────
    verbose && @printf("\n── Kernel solve ────────────────────────────────────────────────────\n")
    verbose && @printf("  Left-kernel search over GF(%d)...\n", ell)

    p1_count    = length(p1_rows)
    total_count = length(rel_rows)
    p2_step     = max(1, (total_count - p1_count) ÷ 20)

    # Build the early-solve monitor from all collected relations.
    # check_interval mirrors the 5% chunk size so core/rank updates are cheap.
    esm = build_monitor_from_relations(rel_rows, nF, ell;
                                        check_interval = p2_step)

    println("\n── Incremental retrieval attempt ────────────────────────────────────")
    for current_limit in [p1_count; (p1_count + p2_step):p2_step:(total_count - 1); total_count]
        sub_rel = rel_rows[1:current_limit]
        sub_al  = alpha_vec[1:current_limit]
        sub_be  = beta_vec[1:current_limit]

        @printf("Rows: %d/%d (Phase 1 + %d) — checking phase-transition signals...\n",
                current_limit, total_count, current_limit - p1_count)

        # Force rank computation at every chunk boundary for a dense Betti trace.
        sig = monitor_check(esm, sub_rel, sub_al, sub_be;
                             force_rank = true, verbose = verbose)

        # Only attempt the expensive left_kernel_all when b₁ > 0 — i.e. rank
        # deficiency is confirmed.  core_solvable and support2_found are
        # informational only; they do not imply a kernel exists yet.
        if !sig.b1_positive
            println("  -> b₁=0; skipping kernel attempt.")
            continue
        end

        @printf("  -> b₁=%d at m=%d — attempting kernel solve.\n",
                sig.b1, current_limit)

        @printf("Rows: %d/%d (Phase 1 + %d) — attempting kernel solve...\n",
                current_limit, total_count, current_limit - p1_count)

        # ── Chain-path O(nF) attempt (phase-1 chain structure) ──────────────
        cp = chain_path_solve(sub_rel, sub_al, sub_be, nF, ell, p1_count;
                               G=G, T=T, verbose=verbose)
        if cp.chain_path_succeeded
            @printf("  -> chain_path_solve succeeded: k=%d  (equations=%d)\n",
                    cp.k, cp.n_equations)
            monitor_print_history(esm)
            return (k=cp.k, rel_rows=rel_rows, alpha_vec=alpha_vec,
                    beta_vec=beta_vec, nF=nF, shortfall=false)
        end

        # ── Cycle-union O(n) attempt (H₂=0 conjecture) ──────────────────────
        if use_cycle_union
            cu = cycle_union_solve(sub_rel, sub_al, sub_be, nF, ell;
                                   G=G, T=T, verbose=verbose)
            if cu.cycle_solver_succeeded
                @printf("  -> cycle_union_solve succeeded: k=%d  (cycles=%d, deferred=%d)\n",
                        cu.k, cu.n_cycles_found, cu.n_deferred_resolved)
                monitor_print_history(esm)
                return (k=cu.k, rel_rows=rel_rows, alpha_vec=alpha_vec,
                        beta_vec=beta_vec, nF=nF, shortfall=false)
            end
            verbose && @printf("  -> cycle_union_solve: no k found (cycles=%d); falling back to Gaussian elim.\n",
                               cu.n_cycles_found)
        end

        kernels = left_kernel_all(sub_rel, nF, ell)
        if isempty(kernels)
            println("  -> No kernel found for this subset.")
            continue
        end

        found_k = false
        for γ in kernels
            Sa = mod(sum(BigInt(γ[i]) * sub_al[i] for i in eachindex(γ)), ell)
            Sb = mod(sum(BigInt(γ[i]) * sub_be[i] for i in eachindex(γ)), ell)
            Sb == 0 && continue
            k_cand = mod(-Sa * powermod(Sb, ell - 2, ell), ell)
            if jac_mul(G, k_cand, ell) == T
                @printf("  >> SUCCESS! Secret k found with %d relations: %d\n",
                        current_limit, k_cand)
                monitor_print_history(esm)
                if verbose
                    safe_kernel_phase_instrumentation(sub_rel, sub_al, sub_be, nF, ell;
                                                      G=G, T=T, verbose=true)
                end
                return (k=k_cand, rel_rows=rel_rows, alpha_vec=alpha_vec,
                        beta_vec=beta_vec, nF=nF, shortfall=false)
            end
        end
        println("  -> Kernel found, but k_true not retrieved (insufficient rank or dependency).")
    end

    monitor_print_history(esm)

    # ── Final full kernel solve on all relations ──────────────────────────────
    t_solve_start = time()

    # Try chain-path solve first (O(nF), exploits phase-1 chain structure).
    verbose && println("  Attempting chain_path_solve on full relation set...")
    cp = chain_path_solve(rel_rows, alpha_vec, beta_vec, nF, ell, p1_count;
                          G=G, T=T, verbose=verbose)
    if cp.chain_path_succeeded
        t_solve_done = time() - t_solve_start
        verbose && @printf("  chain_path_solve succeeded: k=%d  time=%.3fs  (equations=%d)\n",
                           cp.k, t_solve_done, cp.n_equations)
        return (k=cp.k, rel_rows=rel_rows, alpha_vec=alpha_vec,
                beta_vec=beta_vec, nF=nF, shortfall=false)
    end

    # Try cycle-union next (O(n), H₂=0 conjecture).
    if use_cycle_union
        verbose && println("  Attempting cycle_union_solve on full relation set...")
        cu = cycle_union_solve(rel_rows, alpha_vec, beta_vec, nF, ell;
                               G=G, T=T, verbose=verbose)
        if cu.cycle_solver_succeeded
            t_solve_done = time() - t_solve_start
            verbose && @printf("  cycle_union_solve succeeded: k=%d  time=%.3fs  (cycles=%d, deferred=%d)\n",
                               cu.k, t_solve_done, cu.n_cycles_found, cu.n_deferred_resolved)
            return (k=cu.k, rel_rows=rel_rows, alpha_vec=alpha_vec,
                    beta_vec=beta_vec, nF=nF, shortfall=false)
        end
        verbose && @printf("  cycle_union_solve: no k found (cycles=%d); falling back to Gaussian elim.\n",
                           cu.n_cycles_found)
    end

    kernels       = left_kernel_all(rel_rows, nF, ell)
    t_solve_done  = time() - t_solve_start
    isempty(kernels) && error("Kernel not found — collect more relations")

    verbose && @printf("  kernel solve time: %.3fs\n", t_solve_done)
    verbose && @printf("  kernel dimension:  %d\n", length(kernels))

    n_tried = 0
    for γ in kernels
        Sa = mod(sum(BigInt(γ[i]) * alpha_vec[i] for i in 1:nrel), ell)
        Sb = mod(sum(BigInt(γ[i]) * beta_vec[i]  for i in 1:nrel), ell)
        Sb == 0 && continue
        k_cand = mod(-Sa * powermod(Sb, ell - 2, ell), ell)
        n_tried += 1
        if verbose && n_tried <= 5
            @printf("  kernel vec %d: Sa=%d Sb=%d k_cand=%d  match=%s\n",
                    n_tried, Sa, Sb, k_cand, jac_mul(G, k_cand, ell) == T)
        end
        if jac_mul(G, k_cand, ell) == T
            verbose && @printf("  ✓  k = %d   (k*G == T)  [kernel vec %d of %d]\n",
                               k_cand, n_tried, length(kernels))
            verbose && @printf("  total walk+solve time: %.3fs\n", time() - t_walk_start)
            verbose && safe_kernel_phase_instrumentation(rel_rows, alpha_vec, beta_vec, nF, ell;
                                                         G=G, T=T, verbose=true)
            return (k=k_cand, rel_rows=rel_rows, alpha_vec=alpha_vec,
                    beta_vec=beta_vec, nF=nF, shortfall=false)
        end
    end

    verbose && @printf("  tried %d kernel vectors, none matched\n", n_tried)
    verbose && println("  No usable kernel vector found; will retry with fresh walk.")
    return (k=nothing, rel_rows=rel_rows, alpha_vec=alpha_vec,
            beta_vec=beta_vec, nF=nF, shortfall=false)
end

# ---------------------------------------------------------------------------
#  CLI helpers
# ---------------------------------------------------------------------------
function parse_trial3_cli(args::Vector{String})
    fb_size            = nothing
    enable_lp2         = true
    enable_lp2_conj    = true
    max_lp2_nodes      = DEFAULT_MAX_LP2_NODES
    max_lp2_conj_nodes = DEFAULT_MAX_LP2_CONJ_NODES
    # New flags:
    #   --amortized          run amortize_alpha_phase + amortized_dlp instead of
    #                        the standard walk+kernel flow
    #   --cycle-union        use cycle_union_solve (O(n)) before left_kernel_all
    #                        fallback in the standard flow
    #   --n-targets=N        number of DLP targets when --amortized is set
    amortized          = false
    use_cycle_union    = false
    n_targets          = 3

    for arg in args
        if arg == "--no-lp2"
            enable_lp2      = false
            enable_lp2_conj = false   # lp2_conj is a subset; disable both
        elseif arg == "--no-conj"
            enable_lp2_conj = false
        elseif startswith(arg, "--fb-size=")
            fb_size = parse(Int, split(arg, "=", limit=2)[2])
        elseif startswith(arg, "--max-lp2-nodes=")
            max_lp2_nodes = parse(Int, split(arg, "=", limit=2)[2])
        elseif startswith(arg, "--max-lp2-conj-nodes=")
            max_lp2_conj_nodes = parse(Int, split(arg, "=", limit=2)[2])
        elseif arg == "--amortized"
            amortized = true
        elseif arg == "--cycle-union"
            use_cycle_union = true
        elseif startswith(arg, "--n-targets=")
            n_targets = parse(Int, split(arg, "=", limit=2)[2])
        end
    end
    return (fb_size=fb_size, enable_lp2=enable_lp2, enable_lp2_conj=enable_lp2_conj,
            max_lp2_nodes=max_lp2_nodes, max_lp2_conj_nodes=max_lp2_conj_nodes,
            amortized=amortized, use_cycle_union=use_cycle_union, n_targets=n_targets)
end

# ---------------------------------------------------------------------------
#  mem_report_phase2tables — print a per-structure memory breakdown
#
#  Uses Sys.maxrss() for process RSS and Base.gc_live_bytes() for GC-tracked
#  live heap.  Per-structure sizes are estimated from known layout:
#
#    shared_lp1      : Dict{NTuple{2,Int}, Tuple{Dict,Int,Int,Int}}
#      each entry owns a fb_row Dict; row weight sampled from first 100 entries
#    shared_lp1_conj : Dict{NTuple{4,Int}, Tuple{Int,Int,Int}}
#      key(32) + val(24) + ~1.43x slot overhead ≈ 80 B/entry
#    fb / pt2idx     : NTuple{2,Int} = 16 B; Dict slot ~1.43x load factor
#    atom_log_dict   : same key + Int value ≈ 40 B/entry
# ---------------------------------------------------------------------------
function mem_report_phase2tables(tables::Phase2Tables,
                                 results_pre,
                                 thread_collectors_pre)
    rss_mb  = Sys.maxrss() / 1024^2
    live_mb = Base.gc_live_bytes() / 1024^2

    nF      = length(tables.fb)
    n_lp1   = length(tables.shared_lp1)
    n_alog  = length(tables.atom_log_dict)

    sh      = tables.shared_lp1_conj.shards
    n_conj  = sum(length(sh[i]) for i in eachindex(sh))

    # Sample first 100 lp1 entries to estimate average fb_row Dict weight.
    avg_row_weight = if n_lp1 > 0
        sample_n = min(100, n_lp1)
        s = 0
        for (_, v) in Iterators.take(tables.shared_lp1, sample_n)
            s += length(v[1])   # v[1] is the fb_row Dict{Int,Int}
        end
        s / sample_n
    else
        0.0
    end

    # Layout estimates (conservative):
    #   fb_row Dict: 56 B header + 16 B/slot × nextpow2(weight) at ~70% load
    fb_row_bytes  = (56 + avg_row_weight * 16 * 2) * n_lp1
    lp1_key_bytes = n_lp1 * 16 * 1.43      # NTuple{2,Int} + slot overhead
    lp1_val_bytes = n_lp1 * 32             # pointer + 3 Ints (row, neg_al, neg_be, step)
    lp1_est_mb    = (lp1_key_bytes + lp1_val_bytes + fb_row_bytes) / 1024^2

    conj_est_mb   = n_conj  * 80  / 1024^2   # 32+24+overhead ≈ 80 B/entry
    fb_est_mb     = nF      * 16  * 1.43 * 2 / 1024^2   # vec + pt2idx dict
    alog_est_mb   = n_alog  * 40  * 1.43 / 1024^2

    # Walk survivors: rel_rows still alive in results_pre.
    # Each rel_row is a Dict{Int,Int}; estimate ~(56 + weight*32) bytes each.
    total_rel_rows = sum(r !== nothing ? length(r.rel_rows) : 0 for r in results_pre)
    avg_rel_weight = begin
        s = 0; n = 0
        for r in results_pre
            r === nothing && continue
            for row in Iterators.take(r.rel_rows, 10)
                s += length(row); n += 1
            end
        end
        n > 0 ? s/n : 2.0
    end
    walk_rels_est_mb = total_rel_rows * (56 + avg_rel_weight * 32) / 1024^2

    # alpha_vec / beta_vec: BigInt per entry ≈ 48 B for single-limb values.
    total_scalars = sum(r !== nothing ? length(r.alpha_vec) + length(r.beta_vec) : 0
                        for r in results_pre)
    scalars_est_mb = total_scalars * 48 / 1024^2

    est_total = fb_est_mb + alog_est_mb + lp1_est_mb + conj_est_mb +
                walk_rels_est_mb + scalars_est_mb

    println("── Memory diagnostics (post-precompute, after GC.gc(true)) ──────────")
    @printf("  Process RSS:                    %8.1f MB\n", rss_mb)
    @printf("  GC live heap:                   %8.1f MB\n", live_mb)
    println("  Estimated per-structure:")
    @printf("    fb + pt2idx  (%6d pts):                        %6.1f MB\n", nF,     fb_est_mb)
    @printf("    atom_log_dict(%6d pts):                        %6.1f MB\n", n_alog, alog_est_mb)
    @printf("    shared_lp1   (%6d entries, avg_row_wt=%.1f):   %6.1f MB\n",
            n_lp1, avg_row_weight, lp1_est_mb)
    @printf("    shared_lp1_conj (%d entries @ ~80 B/entry):    %6.1f MB\n",
            n_conj, conj_est_mb)
    @printf("    walk rel_rows (%d rows, avg_wt=%.1f):           %6.1f MB\n",
            total_rel_rows, avg_rel_weight, walk_rels_est_mb)
    @printf("    walk alpha/beta vecs (%d BigInts):              %6.1f MB\n",
            total_scalars, scalars_est_mb)
    @printf("  Estimated Julia heap total:     %8.1f MB\n", est_total)
    @printf("  Unaccounted Julia heap:         %8.1f MB  ← Nemo/FLINT/Oscar C heap + runtime\n",
            max(0.0, live_mb - est_total))
    @printf("  RSS − GC-live gap:              %8.1f MB  ← fragmentation + mapped libs\n",
            max(0.0, rss_mb - live_mb))
    println("─"^70)
    flush(stdout)
end

# Backward-compat single-arg form (for call sites without walk results).
mem_report_phase2tables(tables::Phase2Tables) =
    mem_report_phase2tables(tables, Any[], [])

# ---------------------------------------------------------------------------
#  main2 — top-level entry point
# ---------------------------------------------------------------------------
function main2(; fb_size            ::Union{Nothing,Int} = nothing,
                 enable_lp2         ::Bool = true,
                 enable_lp2_conj    ::Bool = true,
                 max_lp2_nodes      ::Int  = DEFAULT_MAX_LP2_NODES,
                 max_lp2_conj_nodes ::Int  = DEFAULT_MAX_LP2_CONJ_NODES,
                 amortized          ::Bool = false,
                 use_cycle_union    ::Bool = false,
                 n_targets          ::Int  = 3)
    t_main_start = time()
    println("="^70)
    println("  trial3: Markov-walk phi-relation index calculus")
    println("  y^2 = x^5+3x^3+2x^2+5x+4  /F_$p,  ell=<auto>")
    println("  threads = $(Threads.nthreads())  |  start: $(Dates.now())")
    amortized       && println("  mode: AMORTIZED (α-only precompute + single β≠0 DLP)")
    !amortized      && println("  LA mode: chain-path O(nF) solver (always) + cycle-union (if --cycle-union)")
    println("="^70, "\n")

    t_pts = time()
    pts   = curve_points()
    mem_checkpoint("after curve_points()")
    t_pts_done = time() - t_pts
    length(pts) < 2 && error("No affine points found on curve.")
    @printf("Curve enumeration: %d affine rational points in %.3fs\n", length(pts), t_pts_done)
    @printf("  expected ~p = %d points (density check: %.4f)\n",
            p, length(pts) / Float64(p))
    println()

    println("── Generator search (Frobenius / Sage) ─────────────────────────────")
    t_ell = time()
    G, ell_found = frobenius_find_ell_generator(pts)
    t_ell_done = time() - t_ell
    global ell = ell_found

    @printf("  bootstrap total time = %.3fs\n", t_ell_done)
    @printf("  G.u = %s\n  G.v = %s\n", G.u, G.v)
    @printf("  ell = %d  (%.1f bits)\n", ell, log2(ell))
    @printf("  ell/p ratio = %.6f\n", ell / p)

    @assert jac_isid(jac_mul_raw(G, ell)) "G does not have order ell"
    println("  Confirmed: ell*G = identity\n")

    # ── Amortised mode: β=0 precompute via normal phase1+phase2, then one β≠0 per target ──
    if amortized
        fb_run = fb_size === nothing ? clamp(round(Int, p^(1/2)), 200, 20_000) : fb_size
        @printf("── Amortised precomputation (β=0 walk, FB=%d) ───────────────────────\n", fb_run)
        t_pre = time()

        # ── Phase 1 (β=0) ────────────────────────────────────────────────────
        # T is a dummy here — not used since beta_zero=true.  We still need a
        # valid Div2 to satisfy the type signature; use G itself.
        T_dummy = G
        fb_pre, pt2idx_pre, p1_alpha_pre, p1_beta_pre, p1_rows_pre =
            phase1_walk(G, T_dummy, fb_run; verbose=true, beta_zero=true)
        nF_pre = length(fb_pre)
        mem_checkpoint("after phase1_walk (amortized)")

        # ── β=0 step table (no T term) ───────────────────────────────────────
        N_STEPS_pre = 256
        step_D_pre  = Vector{Div2}(undef, N_STEPS_pre)
        step_a_pre  = Vector{BigInt}(undef, N_STEPS_pre)
        step_b_pre  = fill(BigInt(0), N_STEPS_pre)   # unused but required by signature
        for i in 1:N_STEPS_pre
            a = BigInt(rand(1:ell-1))
            step_D_pre[i] = jac_mul(G, Int(a), ell)
            step_a_pre[i] = a
        end
        mem_checkpoint("after step-table precompute")

        # ── Phase 2 (β=0, multithreaded) ─────────────────────────────────────
        target_excess_pre = max(20, nF_pre ÷ 10)
        rel_target_pre    = max(1, nF_pre + 1 + target_excess_pre - length(p1_rows_pre))
        rel_counter_pre   = Threads.Atomic{Int}(0)
        n_all_pre         = length(curve_points())
        cov_pre           = nF_pre / max(1, n_all_pre)
        step_cap_pre      = round(Int, rel_target_pre * 1.0 / max(1e-8, cov_pre^2) /
                                  Threads.nthreads()) * Threads.nthreads()

        shared_lp1_pre       = Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}}()
        shared_lp1_lock_pre  = ReentrantLock()
        shared_lp2_pre       = LP2Graph()
        shared_lp2_lock_pre  = ReentrantLock()
        shared_lp_doubled_pre = Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}}()
        shared_lp1_conj_pre  = ShardedLP1Conj(ell)
        mem_checkpoint("after ShardedLP1Conj() (cap=$(shared_lp1_conj_pre.max_entries))")
        shared_lp2_conj_pre  = LP2ConjGraph()
        shared_lp2_conj_lock_pre = ReentrantLock()
        set_lp2_principal_check_context!(fb_pre, G, T_dummy)
        rank_tracker_pre = OnlineRankTracker(ell)
        thread_collectors_pre = [LPResidualCollector() for _ in 1:Threads.nthreads()]
        results_pre = Vector{Any}(undef, Threads.nthreads())

        @printf("  [MEM] before phase2 walk:  RSS=%.1f MB  GC-live=%.1f MB\n",
                Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
        flush(stdout)

        @sync for tid in 1:Threads.nthreads()
            Threads.@spawn begin
                results_pre[tid] = phase2_worker(
                    G, T_dummy, fb_pre, BigInt(ell), pt2idx_pre,
                    step_D_pre, step_a_pre, step_b_pre,
                    rel_counter_pre, rel_target_pre, step_cap_pre ÷ Threads.nthreads(),
                    shared_lp1_pre, shared_lp1_lock_pre,
                    shared_lp2_pre, shared_lp2_lock_pre,
                    shared_lp_doubled_pre,
                    shared_lp1_conj_pre,
                    shared_lp2_conj_pre, shared_lp2_conj_lock_pre,
                    enable_lp2, enable_lp2_conj, max_lp2_nodes, max_lp2_conj_nodes,
                    thread_collectors_pre[tid], rank_tracker_pre;
                    verbose=true, beta_zero=true, amortized_precompute=true)
            end
        end

        @printf("  [MEM] after  phase2 walk:  RSS=%.1f MB  GC-live=%.1f MB\n",
                Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
        flush(stdout)

        alpha_vec_pre = copy(p1_alpha_pre)
        beta_vec_pre  = copy(p1_beta_pre)
        rel_rows_pre  = copy(p1_rows_pre)
        for r in results_pre
            append!(alpha_vec_pre, r.alpha_vec)
            append!(beta_vec_pre,  r.beta_vec)
            append!(rel_rows_pre,  r.rel_rows)
        end

        @printf("  β=0 walk done: %d relations, %d FB atoms (%.3fs)\n",
                length(rel_rows_pre), nF_pre, time() - t_pre)

        # ── RREF solve: atom_log_dict ─────────────────────────────────────────
        atom_log_dict = Dict{NTuple{2,Int}, Int}()
        try
            @printf("  [MEM] before RREF solve:   RSS=%.1f MB  GC-live=%.1f MB\n",
                    Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
            flush(stdout)
            F_pre = Nemo.GF(ell)
            m_pre = length(rel_rows_pre)
            aug   = zero_matrix(F_pre, m_pre, nF_pre + 1)
            for i in 1:m_pre
                for (j, v) in rel_rows_pre[i]
                    1 <= j <= nF_pre || continue
                    aug[i, j] = mod(v, ell)
                end
                aug[i, nF_pre + 1] = mod(alpha_vec_pre[i], ell)
            end
            _, R_mat = rref(aug)
            @printf("  [MEM] after  rref():       RSS=%.1f MB  GC-live=%.1f MB\n",
                    Sys.maxrss()/1024^2, Base.gc_live_bytes()/1024^2)
            flush(stdout)
            logs = zeros(Int, nF_pre)
            for r in 1:size(R_mat, 1)
                pc = 0
                for c in 1:nF_pre
                    R_mat[r, c] != 0 && (pc = c; break)
                end
                pc == 0 && continue
                logs[pc] = Int(lift(ZZ, R_mat[r, nF_pre + 1]))
            end
            for (pt, idx) in pt2idx_pre
                atom_log_dict[pt] = logs[idx]
            end
        catch e
            error("amortized RREF solve failed: $e")
        end

        @printf("  atom_log_dict: %d entries (%.3fs total precompute)\n",
                length(atom_log_dict), time() - t_pre)

        # ── Sanity-check atom logs against known G ────────────────────────────
        n_verified = 0; n_failed = 0
        for i in 1:min(20, length(rel_rows_pre))
            row    = rel_rows_pre[i]
            neg_al = alpha_vec_pre[i]
            lhs    = sum(get(atom_log_dict, fb_pre[j], 0) * v
                         for (j, v) in row if 1 <= j <= nF_pre)
            lhs    = mod(lhs, ell)
            rhs    = mod(Int(neg_al), ell)
            if lhs == rhs
                n_verified += 1
            else
                n_failed += 1
                n_failed <= 3 && @printf("  [DIAG] relation %d FAILS: lhs=%d rhs=%d\n",
                                         i, lhs, rhs)
            end
        end
        @printf("  [DIAG] relation self-check: %d ok, %d failed (of first 20)\n\n",
                n_verified, n_failed)

        # ── Bundle precompute output into Phase2Tables ────────────────────────
        tables = Phase2Tables(
            fb_pre,
            pt2idx_pre,
            atom_log_dict,
            shared_lp1_pre,       # READ ONLY in phase 3
            shared_lp2_pre,
            shared_lp1_conj_pre,
            shared_lp2_conj_pre,
            BigInt(ell))

        @printf("  Phase2Tables ready: FB=%d  atom_logs=%d  lp1_entries=%d\n",
                length(fb_pre), length(atom_log_dict), length(shared_lp1_pre))
        let sh = shared_lp1_conj_pre.shards
            conj_total    = sum(length(sh[i]) for i in eachindex(sh))
            conj_nonempty = count(i -> !isempty(sh[i]), eachindex(sh))
            @printf("  shared_lp1_conj_pre: %d entries across %d/%d nonempty shards\n",
                    conj_total, conj_nonempty, length(sh))
        end
        @printf("  total precompute time: %.3fs\n\n", time() - t_pre)

        # ── Memory diagnostics ────────────────────────────────────────────────
        # Force a full GC before reporting so dead walk allocations are collected
        # and we see the true live set (Nemo/FLINT native heap will still show in RSS).
        GC.gc(true)
        mem_checkpoint("after final GC.gc(true) post-precompute")
        mem_report_phase2tables(tables, results_pre, thread_collectors_pre)

        # ── Build per-target list ─────────────────────────────────────────────
        println("── Generating targets ───────────────────────────────────────────────")
        targets = Vector{Tuple{Div2, Union{Int,Nothing}}}(undef, n_targets)
        for i in 1:n_targets
            k_true_i = rand(2:Int(ell)-1)
            T_i      = jac_mul(G, k_true_i, ell)
            targets[i] = (T_i, k_true_i)
            @printf("  [target %d/%d] k_true = %d\n", i, n_targets, k_true_i)
        end
        flush(stdout)

        # ── Phase 3: parallel per-target DLP solves ───────────────────────────
        results = phase3_solve_targets(tables, targets, G;
                                       step_cap = 10_000_000,
                                       verbose  = true)

        n_ok = count(r -> r.success, results)
        @printf("\n── Final amortized summary ──────────────────────────────────────────\n")
        @printf("  %d / %d DLP trials recovered correctly\n", n_ok, n_targets)
        @printf("  total wall time: %.3fs\n", time() - t_main_start)
        println("="^70)
        return
    end

    k_true = rand(2:ell-1)
    T      = jac_mul(G, k_true, ell)
    @printf("Secret k = %d  (%.1f bits)\n\n", k_true, log2(k_true + 1))

    # Auto FB size: p^(1/2) is the standard smoothness bound for genus-2 index calculus.
    fb_auto = clamp(round(Int, p^(1/2)), 200, 20_000)
    @printf("Auto FB size: %d  (= ceil(p^(1/2)) clamped to [200,20000])\n", fb_auto)
    @printf("  target relations: %d + excess\n", fb_auto + 1)
    @printf("  expected smoothness prob per step: ~(fb_auto/p)^2 ~ %.2e\n",
            (fb_auto / p)^2)
    println()

    println("── Index calculus walk ─────────────────────────────────────────────")
    t_walk = time()
    fb_run = fb_size === nothing ? fb_auto : fb_size
    wres   = index_calculus_walk(G, T;
                                  fb_size=fb_run, verbose=true,
                                  analyze_matrix=true, asymptotic=true,
                                  solve=true, guided=true,
                                  enable_lp2=enable_lp2,
                                  enable_lp2_conj=enable_lp2_conj,
                                  max_lp2_nodes=max_lp2_nodes,
                                  max_lp2_conj_nodes=max_lp2_conj_nodes,
                                  use_cycle_union=use_cycle_union)
    t_walk_done = time() - t_walk
    k_rec = wres === nothing ? nothing : wres.k

    println()
    println("── Final results ───────────────────────────────────────────────────")
    @printf("  walk+solve wall time: %.3fs\n", t_walk_done)
    @printf("  total wall time:      %.3fs\n", time() - t_main_start)
    if k_rec !== nothing
        @printf("  Recovered k = %-10d  true k = %-10d  match = %s\n",
                k_rec, k_true, k_rec == k_true)
    else
        println("  DLP not recovered.")
    end
    println("="^70)
end

function main2_from_argv()
    opts = parse_trial3_cli(ARGS)
    main2(; fb_size=opts.fb_size, enable_lp2=opts.enable_lp2,
          enable_lp2_conj=opts.enable_lp2_conj,
          max_lp2_nodes=opts.max_lp2_nodes, max_lp2_conj_nodes=opts.max_lp2_conj_nodes,
          amortized=opts.amortized, use_cycle_union=opts.use_cycle_union,
          n_targets=opts.n_targets)
end

if abspath(PROGRAM_FILE) == @__FILE__
    main2_from_argv()
end
