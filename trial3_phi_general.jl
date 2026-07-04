# =============================================================================
#  trial3_phi_general.jl  --  Generalised φ-function for k-anchor walks.
#
#  Replaces the single-anchor quadratic φ in trial3_phi.jl with a family
#  parameterised by the number of anchor points k ≥ 1.
#
#  MATHEMATICAL BACKGROUND
#  -----------------------
#  The curve is C: y² = f(x),  f degree 5  (genus g=2).
#
#  The Riemann-Roch space L(n·∞) on a hyperelliptic curve of genus g has
#  a canonical monomial basis ordered by pole order at the points at
#  infinity.  For genus 2 the basis elements and their pole orders are:
#
#    Monomial   Pole order   Index
#    ---------  ----------   -----
#    1            0           1
#    x            2           2
#    x²           4           3
#    y            5           4    ← normalise coefficient to 1 (d=1)
#    x³           6           5
#    xy           7           6
#    x⁴           8           7
#    x²y          9           8
#    x⁵          10           9
#    x³y         11          10
#    ...
#
#  General pattern: xⁱ has pole order 2i; xⁱy has pole order 2i+5.
#  Interleaved in increasing order they give the sequence
#    2·0, 2·1, 2·2, 5, 2·3, 7, 2·4, 9, ...
#  which (after the leading 1) is  0, 2, 4, 5, 6, 7, 8, 9, 10, 11, …
#
#  For k anchor points + a degree-2 Mumford divisor D=[u(x),v(x)],
#  the total number of vanishing conditions is k+2.  We choose the
#  smallest Riemann-Roch basis B with |B| = k+3 elements (one extra
#  for normalization: we set the coefficient of the last/highest-pole
#  element to 1 and solve for the remaining k+2 coefficients).
#
#  Denote the chosen basis B = {m₁, …, m_{k+3}}, ordered by pole order.
#  Normalise: coefficient of m_{k+3} is 1.  Define the column vector
#  of unknowns  c = (c₁, …, c_{k+2})ᵀ  corresponding to {m₁,…,m_{k+2}}.
#
#  φ(x,y) = Σⱼ cⱼ mⱼ(x,y)  +  m_{k+3}(x,y)
#
#  Vanishing conditions (k+2 equations):
#
#    (A)  k anchor equations:  for each anchor Pᵢ = (pxᵢ, pyᵢ):
#           Σⱼ cⱼ mⱼ(pxᵢ, pyᵢ)  =  -m_{k+3}(pxᵢ, pyᵢ)
#
#    (B)  2 Mumford equations:  φ(x, v(x)) ≡ 0 mod u(x)
#         Since deg u = 2, this means the const and x-coefficient of
#         φ(x, v(x)) mod u(x) are both zero.  For each basis monomial mⱼ,
#         define   rⱼ = (r0ⱼ, r1ⱼ)  = (mⱼ(x,v(x)) mod u(x)) as a linear poly.
#         The two equations become:
#           Σⱼ cⱼ r0ⱼ  =  -r0_{k+3}
#           Σⱼ cⱼ r1ⱼ  =  -r1_{k+3}
#
#  This gives a (k+2) × (k+2) linear system over F_p, solved by Gaussian
#  elimination.
#
#  RESIDUAL INTERSECTION
#  ---------------------
#  Split φ(x,y) = E(x) + y·Y(x) into its x-only and y·(x-only) parts.
#  Then
#       φ(x,y)·φ(x,-y) = E(x)² - f(x)·Y(x)² =: N(x)
#  is a polynomial in x of degree  deg(N) = max(2·deg(E), 5+2·deg(Y)).
#
#  The known zeros of N are:
#    • each anchor xᵢ (simple zero, since P₀ is not in supp D by design)
#    • the roots of u(x) = x²+u1·x+u0  (degree 2)
#  Dividing N by  (Π (x-pxᵢ)) · u(x)  gives the residual polynomial
#  u_RS(x) whose roots are the residual intersection points.
#
#  For k=1 (current code): deg(E)=2, deg(Y)=0, deg(N)=5; known zeros:
#  (x-px1)·u(x) degree 3 → residual u_RS degree 2. ✓
#
#  For k anchors: deg(N) grows with the basis; we always divide out
#  k+2 known zeros to get a residual of degree deg(N)-(k+2).
#  The residual is a monic polynomial over F_p; we try to split it.
#
#  SCOPE: The linear solver is general for any k and any multiplicity pattern.
#  Tangency of order m at a point P requires m conditions (Taylor coefficients
#  of φ along the curve branch at P, orders 0..m-1), computed via branch series
#  expansion.  Requires p > max multiplicity used.
# =============================================================================

# ---------------------------------------------------------------------------
#  Module-level precomputed constants to eliminate hot-path allocations.
#
#  F_POLY_DESC  — F_POLY in descending order for use in branch_series.
#                 F_POLY is defined in the including file; we compute this
#                 lazily the first time branch_series is called, or eagerly
#                 via init_phi_general_caches!().
#
#  RR_BASIS_CACHE — memoisation table for rr_basis(n).  rr_basis is a pure
#                 function of n and the RR structure never changes, so one
#                 copy per n suffices for all threads (read-only after init).
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  FpBackend: swappable F_p arithmetic.  StandardArith (default) is
#  bit-identical to the hardcoded fpmul/fpinv/fp below.  MontgomeryArith
#  provides a REDC-based multiply for large p; see trial3_fp_backend.jl.
#  Include before first use of FpArith, StandardArith, to_repr, from_repr.
# ---------------------------------------------------------------------------
include("trial3_fp_backend.jl")
using StaticArrays   # MMatrix, MVector — stack-allocated mutable arrays for
                     # the Gaussian elimination workspace and small fixed-size
                     # scratch vectors in ThreadScratchpad{K}.

const RR_BASIS_CACHE = Dict{Int, Vector{NTuple{2,Int}}}()

# --- setup/hot-path diagnostic spam, OFF by default ---
# init_scratch_caches! fires once per (thread, K) — harmless in volume but
# pure setup noise. build_phi_general! fires on every K>=2 walk step and
# used to burn its whole print budget (BPG_DIAG_MAX) in well under a second
# of wall-clock time, before any correctness issue had a chance to surface.
# Neither one contributed to catching the 1LP-STORE / residual-anchor-
# collision bug — the real signal was downstream (check_lp1_stored FAIL,
# and now the earlier residual_anchor_collision assert in trial3_phase2.jl).
# Set JULIA_TRIAL3_SETUP_DIAG=1 in the environment to re-enable.
const SETUP_DIAG_VERBOSE = get(ENV, "JULIA_TRIAL3_SETUP_DIAG", "0") == "1"

# --- quick-and-dirty diag throttle, just so we don't drown in prints ---
const BPG_DIAG_COUNT = Threads.Atomic{Int}(0)
const BPG_DIAG_MAX   = SETUP_DIAG_VERBOSE ? 200 : 0

# ---------------------------------------------------------------------------
#  PhiTimingStats — per-thread cumulative timers splitting a step_phi_k! call
#  into its three cost centers:
#
#    series   — build_phi_general!'s anchor-row construction: branch_series!
#                + monomial_series_coeffs! for each anchor (everything before
#                the linear solve; also covers the guard checks and the
#                x^i mod u(x) cache fill, which are cheap relative to these).
#    gauss    — fp_gauss! only (the (K+2)x(K+2) elimination itself).
#    residual — phi_residual_general! (E,Y,N construction, divmod, root-
#                finding). Everything after build_phi_general! returns.
#
#  Purpose: answer "what fraction of a walk step is the linear solve?"
#  before investing in rank-1/SMW/Cramer-style updates to fp_gauss! — that
#  work only pays off in proportion to gauss/(series+gauss+residual).
#
#  Zero-alloc, opt-in: gated behind PHI_TIMING_ENABLED so normal runs pay a
#  single Bool check (no time_ns() calls, no accumulation) when disabled.
#  One PhiTimingStats per thread, indexed by threadid() — each thread only
#  ever touches its own slot, so no locks/atomics are needed.
# ---------------------------------------------------------------------------
using Printf

const PHI_TIMING_ENABLED = Ref(false)

mutable struct PhiTimingStats
    n_calls          ::Int64   # step_phi_k! invocations observed (success or fail)
    ns_series        ::Int64
    ns_gauss         ::Int64
    ns_residual      ::Int64
    n_fail_build     ::Int64   # build_phi_general! returned false (incl. guard rejects)
    n_fail_residual  ::Int64   # phi_residual_general! returned false, or u_RS_is_fail
    # --- fine-grained breakdown of the two buckets above ---
    # n_fail_build == n_fail_build_gauss_singular (build_phi_general! has
    # exactly one `return false` site as of this writing: fp_gauss! failing).
    # Kept as a separate field anyway so a future second failure path in
    # build_phi_general! doesn't have to touch call sites elsewhere.
    n_fail_build_gauss_singular ::Int64
    # n_fail_residual splits across phi_residual_general!'s four
    # `u_RS_is_fail[1] = true; return false` sites, in source order:
    n_fail_resid_anchor_remainder ::Int64  # step 3: anchor-factor divide left nonzero remainder
    n_fail_resid_u_remainder      ::Int64  # step 4: u(x) divide left nonzero remainder
    n_fail_resid_degenerate       ::Int64  # step 5/degenerate check: residual collapsed to 0
    # NOT a phi_residual_general! failure — step_phi_dispatch! returned
    # success=true here, but phase2_worker's own post-processing found
    # u_rs_len != 3 (residual degree != 2, so no conjugate LP key exists)
    # AND no usable split points (res_R/res_S both SENTINEL_PT), so the
    # step is dropped anyway. Tracked separately because incrementing
    # n_fail_residual here would be misleading — phi_residual_general!
    # itself succeeded; this is phase2_worker discarding a structurally
    # valid-but-unusable residual shape.
    n_drop_residual_deg_not_2_no_split ::Int64
    # --- fp_gauss! itself has THREE distinct singularity return sites,
    # previously ALL collapsed into the single n_fail_build_gauss_singular
    # counter above with zero indication of which one, or at what matrix
    # column/row. Split out so a structural bug in the (K+2)x(K+2) fill
    # (e.g. two anchor rows becoming linearly dependent, or the Mumford
    # rows not actually adding independent constraints for K>=2) shows up
    # as "column N never has a pivot" instead of a bare boolean. ---
    n_gauss_fail_forward_pivot   ::Int64  # forward pass: no nonzero pivot_row found for some column
    n_gauss_fail_diag_d1         ::Int64  # batch-invert: A[1,1] == 0 after full elimination
    n_gauss_fail_diag_di         ::Int64  # batch-invert: A[i,i] == 0 for some i>1 after full elimination
    # Per-column tally of WHICH column the forward-pass pivot search failed
    # on, across the life of the run (indexed 1:K_MAX+2, the largest
    # (K+2)x(K+2) system size any k_cur in 1:K_MAX can produce; unused
    # trailing entries for smaller k_cur stay 0). This is the single most
    # actionable diagnostic for a "gauss always singular at k=2" stall:
    # if column 1 (the first anchor row) fails every time, the bug is in
    # how THAT row is filled; if it's always the last column (the
    # normalized-basis-element RHS move), the bug is there instead.
    gauss_fail_forward_pivot_col_hist ::Vector{Int64}
    # --- fine-grained sub-timers inside the "series" bucket ---
    # These are a BREAKDOWN of ns_series, not additional time: for any
    # given call, ns_series == ns_ser_setup + ns_ser_branch + ns_ser_cols
    # + ns_ser_rhs (modulo the early-exit guard paths, which only bump
    # ns_ser_setup since nothing past the guard runs). Added to find out
    # which piece inside build_phi_general!'s pre-gauss work actually
    # costs the ~2154ns/call the top-level series timer was reporting,
    # since no single component looked obviously large enough on
    # inspection alone (see conversation: the pxpow-precompute attempt at
    # eliminating eval_monomial's per-column re-derivation of px^i netted
    # ~0% because max_basis_i is tiny at K=1 — the real cost is somewhere
    # else in this bucket and needs to be measured, not guessed).
    ns_ser_setup     ::Int64   # fill!(seen_counts/visited_flags), dedup double-loop, guard checks
    ns_ser_branch    ::Int64   # branch_series! calls (all anchors)
    ns_ser_cols      ::Int64   # the for col_idx in 1:n / monomial_series_coeffs! + A_mat write loop
    ns_ser_rhs       ::Int64   # normalized-monomial monomial_series_coeffs! + rhs_vec write
    ns_ser_mumford   ::Int64   # Mumford rows (reduce_monomial_mod_D_cached x (n+1)) — runs AFTER
                                # the anchor loop, still inside the series-timed region. Missed
                                # on the first pass at this instrumentation; added once noticed.
    # --- fine-grained sub-timers inside the "residual" bucket ---
    # Same rationale as ns_ser_* above, one level down: residual was the
    # dominant share (~60%) in the first series/gauss/residual split, which
    # only tells us THAT it's expensive, not WHERE inside
    # phi_residual_general! the time goes. In particular this exists to
    # test the hypothesis that _solve_oscar_roots!'s round-trip through
    # Nemo/Oscar's generic FqField/FqPolyRing machinery (deg>=3 residuals)
    # dominates over the raw-Int64 poly arithmetic elsewhere in this file —
    # vs. it actually being the poly divmods or the v_RS modular-inverse
    # computation. ns_res_roots_quad + ns_res_roots_oscar is a BREAKDOWN of
    # the same time find_roots_and_points_inplace! spends (mutually
    # exclusive per call: deg==2 takes the quad closed form, everything
    # else goes through Oscar), not additional time on top of ns_res_roots.
    ns_res_buildN      ::Int64   # phi_to_EY! + build_N_inplace! (steps 1-2: E,Y,N construction)
    ns_res_divmod      ::Int64   # steps 3-7: anchor-factor divmods, u(x) divmod, strip/normalize/copy
    ns_res_vrs         ::Int64   # compute_vRS_inplace! (step 8: v_RS(x) mod u_RS(x) via modular inverse)
    ns_res_roots       ::Int64   # find_roots_and_points_inplace! (step 9), both branches combined
    ns_res_roots_quad  ::Int64   # ...of which: deg==2 closed-form path (_solve_quadratic_roots!)
    ns_res_roots_oscar ::Int64   # ...of which: deg>=3 Oscar/Nemo path (_solve_oscar_roots!)
end
PhiTimingStats() = PhiTimingStats(
    0, 0, 0, 0,                      #  1: n_calls, ns_series, ns_gauss, ns_residual
    0, 0,                            #  5: n_fail_build, n_fail_residual
    0,                                #  7: n_fail_build_gauss_singular
    0, 0, 0,                         #  8: n_fail_resid_anchor_remainder, _u_remainder, _degenerate
    0,                                # 11: n_drop_residual_deg_not_2_no_split
    0, 0, 0,                         # 12: n_gauss_fail_forward_pivot, _diag_d1, _diag_di
    zeros(Int64, K_MAX + 2),          # 15: gauss_fail_forward_pivot_col_hist
    0, 0, 0, 0, 0,                    # 16: ns_ser_setup..ns_ser_mumford
    0, 0, 0, 0, 0, 0)                 # 21: ns_res_buildN..ns_res_roots_oscar

const PHI_TIMING = Ref{Vector{PhiTimingStats}}(PhiTimingStats[])

# Call once at worker startup (after Threads.nthreads() is known), same
# spot init_scratch_caches!/scratch_by_k get built.
function init_phi_timing!(nthreads::Int = Threads.nthreads())
    PHI_TIMING[] = [PhiTimingStats() for _ in 1:nthreads]
    return nothing
end

@inline function phi_timing_stats()::PhiTimingStats
    # Lazily grow PHI_TIMING[] if a thread ID we haven't seen shows up
    # before init_phi_timing! was called with the final nthreads() count,
    # or if it was never called at all (fail-reason counters below must
    # work unconditionally, independent of --phi-timing / PHI_TIMING_ENABLED,
    # since they're the only visibility into "which continue is silently
    # eating every step" — see phase2_worker's STALL_ASSERT_STEPS assert).
    tid = Threads.threadid()
    if isempty(PHI_TIMING[]) || tid > length(PHI_TIMING[])
        init_phi_timing!(max(tid, Threads.nthreads()))
    end
    @inbounds PHI_TIMING[][tid]
end

function reset_phi_timing!()
    for s in PHI_TIMING[]
        s.n_calls = 0; s.ns_series = 0; s.ns_gauss = 0; s.ns_residual = 0
        s.n_fail_build = 0; s.n_fail_residual = 0
        s.n_fail_build_gauss_singular = 0
        s.n_fail_resid_anchor_remainder = 0
        s.n_fail_resid_u_remainder = 0
        s.n_fail_resid_degenerate = 0
        s.n_drop_residual_deg_not_2_no_split = 0
        s.n_gauss_fail_forward_pivot = 0
        s.n_gauss_fail_diag_d1 = 0
        s.n_gauss_fail_diag_di = 0
        fill!(s.gauss_fail_forward_pivot_col_hist, 0)
        s.ns_ser_setup = 0; s.ns_ser_branch = 0; s.ns_ser_cols = 0; s.ns_ser_rhs = 0
        s.ns_ser_mumford = 0
        s.ns_res_buildN = 0; s.ns_res_divmod = 0; s.ns_res_vrs = 0
        s.ns_res_roots = 0; s.ns_res_roots_quad = 0; s.ns_res_roots_oscar = 0
    end
    return nothing
end

# Prints the aggregate split + per-call means. Call this from the same
# periodic report_worker_progress cadence, or on demand from the REPL.
function print_phi_timing_report(; label::String = "")
    isempty(PHI_TIMING[]) && (@printf("[PHI-TIMING] not initialized — call init_phi_timing!() first\n"); return)
    agg = PhiTimingStats()
    for s in PHI_TIMING[]
        agg.n_calls         += s.n_calls
        agg.ns_series        += s.ns_series
        agg.ns_gauss         += s.ns_gauss
        agg.ns_residual      += s.ns_residual
        agg.n_fail_build     += s.n_fail_build
        agg.n_fail_residual  += s.n_fail_residual
        agg.n_fail_build_gauss_singular += s.n_fail_build_gauss_singular
        agg.n_fail_resid_anchor_remainder += s.n_fail_resid_anchor_remainder
        agg.n_fail_resid_u_remainder      += s.n_fail_resid_u_remainder
        agg.n_fail_resid_degenerate       += s.n_fail_resid_degenerate
        agg.n_drop_residual_deg_not_2_no_split += s.n_drop_residual_deg_not_2_no_split
        agg.n_gauss_fail_forward_pivot += s.n_gauss_fail_forward_pivot
        agg.n_gauss_fail_diag_d1       += s.n_gauss_fail_diag_d1
        agg.n_gauss_fail_diag_di       += s.n_gauss_fail_diag_di
        # Element-wise: both vectors are K_MAX+2 long (agg's came from the
        # PhiTimingStats() constructor above, s's from init_phi_timing!'s
        # per-thread PhiTimingStats() calls — same K_MAX in scope either way).
        @assert length(agg.gauss_fail_forward_pivot_col_hist) == length(s.gauss_fail_forward_pivot_col_hist) "print_phi_timing_report: histogram length mismatch ($(length(agg.gauss_fail_forward_pivot_col_hist)) vs $(length(s.gauss_fail_forward_pivot_col_hist))) — K_MAX must have changed between agg's and this thread's PhiTimingStats() construction"
        agg.gauss_fail_forward_pivot_col_hist .+= s.gauss_fail_forward_pivot_col_hist
        agg.ns_ser_setup     += s.ns_ser_setup
        agg.ns_ser_branch    += s.ns_ser_branch
        agg.ns_ser_cols      += s.ns_ser_cols
        agg.ns_ser_rhs       += s.ns_ser_rhs
        agg.ns_ser_mumford   += s.ns_ser_mumford
        agg.ns_res_buildN      += s.ns_res_buildN
        agg.ns_res_divmod      += s.ns_res_divmod
        agg.ns_res_vrs         += s.ns_res_vrs
        agg.ns_res_roots       += s.ns_res_roots
        agg.ns_res_roots_quad  += s.ns_res_roots_quad
        agg.ns_res_roots_oscar += s.ns_res_roots_oscar
    end
    total_ns = agg.ns_series + agg.ns_gauss + agg.ns_residual
    if total_ns == 0
        @printf("[PHI-TIMING%s] no samples (is PHI_TIMING_ENABLED[] set?)\n", isempty(label) ? "" : " $label")
        return
    end
    tag = isempty(label) ? "" : " $label"
    @printf("[PHI-TIMING%s] n=%d  build_fail=%d (%.2f%%)  resid_fail=%d (%.2f%%)\n",
            tag, agg.n_calls,
            agg.n_fail_build,    100.0 * agg.n_fail_build    / max(1, agg.n_calls),
            agg.n_fail_residual, 100.0 * agg.n_fail_residual / max(1, agg.n_calls))
    @printf("[PHI-TIMING%s]   build_fail breakdown:  gauss_singular=%d\n",
            tag, agg.n_fail_build_gauss_singular)
    @printf("[PHI-TIMING%s]     gauss_singular breakdown:  forward_pivot=%d  diag_d1=%d  diag_di=%d\n",
            tag, agg.n_gauss_fail_forward_pivot, agg.n_gauss_fail_diag_d1, agg.n_gauss_fail_diag_di)
    if agg.n_gauss_fail_forward_pivot > 0
        nz_cols = [(col, cnt) for (col, cnt) in enumerate(agg.gauss_fail_forward_pivot_col_hist) if cnt > 0]
        @printf("[PHI-TIMING%s]     forward_pivot failing column histogram (1-indexed, only nonzero shown): %s\n",
                tag, string(nz_cols))
    end
    @printf("[PHI-TIMING%s]   resid_fail breakdown:  anchor_remainder=%d  u_remainder=%d  degenerate=%d\n",
            tag, agg.n_fail_resid_anchor_remainder, agg.n_fail_resid_u_remainder,
            agg.n_fail_resid_degenerate)
    @printf("[PHI-TIMING%s]   post-success drop (deg!=2, no split points): %d\n",
            tag, agg.n_drop_residual_deg_not_2_no_split)
    @printf("[PHI-TIMING%s] share of solve+residual time:  series=%.1f%%  gauss=%.1f%%  residual=%.1f%%\n",
            tag,
            100.0 * agg.ns_series   / total_ns,
            100.0 * agg.ns_gauss    / total_ns,
            100.0 * agg.ns_residual / total_ns)
    @printf("[PHI-TIMING%s] mean per call (ns):  series=%.0f  gauss=%.0f  residual=%.0f  total=%.0f\n",
            tag,
            agg.ns_series   / max(1, agg.n_calls),
            agg.ns_gauss    / max(1, agg.n_calls),
            agg.ns_residual / max(1, agg.n_calls),
            total_ns        / max(1, agg.n_calls))
    # Sub-breakdown of the series bucket. ns_ser_* should sum to ~ns_series
    # (small discrepancy possible from the guard early-exit paths and
    # time_ns() call overhead itself, ~20-40ns per call site — 4 extra
    # time_ns() calls were added for this breakdown, on top of the 4
    # already used for series/gauss/residual, so expect total_ns's
    # absolute per-call numbers to creep up slightly vs pre-breakdown
    # reports; the RATIOS below are what matters).
    ser_sum = max(1, agg.ns_ser_setup + agg.ns_ser_branch + agg.ns_ser_cols + agg.ns_ser_rhs + agg.ns_ser_mumford)
    @printf("[PHI-TIMING%s] series breakdown:  setup=%.1f%%  branch_series=%.1f%%  cols_loop=%.1f%%  rhs=%.1f%%  mumford=%.1f%%  (of series total)\n",
            tag,
            100.0 * agg.ns_ser_setup    / ser_sum,
            100.0 * agg.ns_ser_branch   / ser_sum,
            100.0 * agg.ns_ser_cols     / ser_sum,
            100.0 * agg.ns_ser_rhs      / ser_sum,
            100.0 * agg.ns_ser_mumford  / ser_sum)
    @printf("[PHI-TIMING%s] series breakdown mean (ns):  setup=%.0f  branch_series=%.0f  cols_loop=%.0f  rhs=%.0f  mumford=%.0f\n",
            tag,
            agg.ns_ser_setup    / max(1, agg.n_calls),
            agg.ns_ser_branch   / max(1, agg.n_calls),
            agg.ns_ser_cols     / max(1, agg.n_calls),
            agg.ns_ser_rhs      / max(1, agg.n_calls),
            agg.ns_ser_mumford  / max(1, agg.n_calls))
    # Sub-breakdown of the residual bucket. ns_res_* should sum to ~ns_residual
    # (same time_ns()-overhead caveat as the series breakdown above; ratios
    # are what matters). ns_res_roots_quad/_oscar are themselves a further
    # breakdown of ns_res_roots specifically (mutually exclusive per call —
    # see find_x_roots!'s deg==2 branch), not additional time on top of
    # ns_res_roots.
    # KNOWN GAP: phi_residual_general!'s three early return-false sites in
    # the divmod region (anchor-factor remainder nonzero, u(x) remainder
    # nonzero, degenerate residual) exit before ns_res_divmod's closing
    # timer runs, so partial divmod time on those paths lands in no bucket
    # (ns_res_buildN is unaffected, since it closes before divmod starts).
    # Harmless while resid_fail's anchor_remainder/u_remainder/degenerate
    # counts stay near zero; if those grow large, ns_res_divmod's share
    # will read artificially low.
    res_sum = max(1, agg.ns_res_buildN + agg.ns_res_divmod + agg.ns_res_vrs + agg.ns_res_roots)
    @printf("[PHI-TIMING%s] residual breakdown:  buildN=%.1f%%  divmod=%.1f%%  vRS=%.1f%%  roots=%.1f%%  (of residual total)\n",
            tag,
            100.0 * agg.ns_res_buildN / res_sum,
            100.0 * agg.ns_res_divmod / res_sum,
            100.0 * agg.ns_res_vrs    / res_sum,
            100.0 * agg.ns_res_roots  / res_sum)
    @printf("[PHI-TIMING%s] residual breakdown mean (ns):  buildN=%.0f  divmod=%.0f  vRS=%.0f  roots=%.0f\n",
            tag,
            agg.ns_res_buildN / max(1, agg.n_calls),
            agg.ns_res_divmod / max(1, agg.n_calls),
            agg.ns_res_vrs    / max(1, agg.n_calls),
            agg.ns_res_roots  / max(1, agg.n_calls))
    roots_sum = max(1, agg.ns_res_roots_quad + agg.ns_res_roots_oscar)
    @printf("[PHI-TIMING%s]   roots sub-split:  quad(deg==2)=%.1f%%  oscar(deg>=3)=%.1f%%  (of roots time; mean ns below is per CALL to phi_residual_general!, not per invocation of that specific branch)\n",
            tag,
            100.0 * agg.ns_res_roots_quad  / roots_sum,
            100.0 * agg.ns_res_roots_oscar / roots_sum)
    @printf("[PHI-TIMING%s]   roots sub-split mean (ns, per call):  quad=%.0f  oscar=%.0f\n",
            tag,
            agg.ns_res_roots_quad  / max(1, agg.n_calls),
            agg.ns_res_roots_oscar / max(1, agg.n_calls))
    @printf("[PHI-TIMING%s] --> ceiling on any linear-solve speedup (rank-1/SMW/Cramer): a Xx speedup on gauss\n",
            tag)
    @printf("[PHI-TIMING%s]     buys at most %.1f%% off the series+gauss+residual total (gauss share above).\n",
            tag, 100.0 * agg.ns_gauss / total_ns)
    flush(stdout)
end

# Called once after F_POLY is defined (e.g. at the bottom of the including
# file, or in main()).  Pre-populates caches for k=1..max_k_expected.
#
# max_k defaults to K_MAX (trial3_config.jl) rather than an independent
# literal. K_MAX is the single source of truth for the largest anchor-tuple
# size used anywhere in the run (ThreadScratchpad{K_MAX}, LP1ConjVal's
# anchor_indices::NTuple{K_MAX,UInt16}, scratch_by_k's K_ceil, etc.) — a
# smaller local default here silently under-populates RR_BASIS_CACHE for
# k > default.  That's not just a missed optimization: rr_basis_cached
# falls back to a lazy `get!` on a plain (non-thread-safe) Dict for any nb
# not pre-populated, so the first time multiple walker threads hit an
# uncached k concurrently (e.g. k=5,6 with the old default=4 but K_MAX=6),
# it's a genuine data race on RR_BASIS_CACHE, not merely a slow path.
function init_phi_general_caches!(max_k::Int = K_MAX, backend::FpArith = StandardArith(p))
    global F_POLY_DESC
    # F_POLY_DESC must be in the SAME representation build_phi_general! (via
    # branch_series!) will combine it with — i.e. whatever `backend` uses.
    # For StandardArith, to_repr is identity: bit-identical to the old
    # `reverse(F_POLY)`. For MontgomeryArith, each coefficient is converted
    # once here rather than per-call.
    F_POLY_DESC = [to_repr(backend, c) for c in reverse(F_POLY)]
    for k in 1:max_k
        nb = k + 3
        haskey(RR_BASIS_CACHE, nb) || (RR_BASIS_CACHE[nb] = rr_basis(nb))
    end
    return nothing
end

# Lazy global for the descending F_POLY.  Set by init_phi_general_caches!.
# Declared here so branch_series can reference it; will be populated before
# the first walk step.
F_POLY_DESC = Int[]   # filled in by init_phi_general_caches!

# ---------------------------------------------------------------------------
#  Zero-allocation sqrt wrapper for the hot walk path.
#
#  trial1's sqrt_fp returns Union{Int,Nothing}, which Julia boxes on every
#  call.  We wrap it here with a sentinel so the hot path in
#  find_roots_and_points_inplace! and step_phi_k! stays allocation-free.
#  trial1 is untouched.
# ---------------------------------------------------------------------------
const SQRT_FP_NONSQUARE = -1   # sentinel: caller checks sq < 0

@inline function sqrt_fp_hot(a::Int)::Int
    r = sqrt_fp_fast(a)
    r === nothing ? SQRT_FP_NONSQUARE : r::Int
end

# ---------------------------------------------------------------------------
#  sqrt_fp_fast(a) -> Union{Int,Nothing}
#
#  Drop-in replacement for trial1's sqrt_fp, used only on the hot walk path
#  (find_roots_and_points_inplace!, phi_residual_mumford_general). trial1's
#  sqrt_fp itself is UNTOUCHED (battle-tested, never modify) — this is a
#  separate function living in trial3_phi_general.jl.
#
#  MOTIVATION (from PHI-TIMING output showing residual at 57.7% of solve+
#  gauss+residual time): for p ≡ 3 (mod 4) — the common case — trial1's
#  sqrt_fp does TWO full modular exponentiations:
#    1. powermod(a, (p-1)/2, p) == 1   [Euler criterion: is a a QR?]
#    2. powermod(a, (p+1)/4, p)        [the actual candidate root r]
#  and then verifies r² == a. Since deg==2 residuals dominate every k=1
#  walk step (the most heavily-weighted tuple length under the geometric
#  round-robin decay), this sqrt is called on essentially every step, so
#  its cost is not incidental.
#
#  THE REDUNDANCY: with r = a^((p+1)/4) mod p,
#      r² = a^((p+1)/2) = a · a^((p-1)/2) mod p.
#    - If a is a QR:      a^((p-1)/2) = 1   ⟹  r² = a
#    - If a is a non-QR:  a^((p-1)/2) = -1  ⟹  r² = -a  (≠ a, since a≠0)
#  So the verification step "r² == a" ALREADY implies the Euler criterion —
#  computing it separately beforehand is pure duplicated work. Verified
#  both algebraically and against 2000 random trials across a range of
#  p ≡ 3 (mod 4) primes (see planning session) before landing this.
#
#  This eliminates one full powermod call (~half the p≡3 mod 4 sqrt cost)
#  on the dominant residual code path. The p ≡ 1 (mod 4) Tonelli-Shanks
#  branch is copied over unchanged (its main loop already uses fpmul
#  chains rather than repeated powermod calls, so there's no analogous
#  redundancy to remove there — see NOTE below).
#
#  NOTE on p ≡ 1 mod 4, p ≢ 5 mod 8 (i.e. p ≡ 1 mod 8): still calls
#  powermod 3 times up front (for z's Euler check inside the "find a
#  non-residue" loop, plus c, t, r) — those are NOT redundant with each
#  other (z, a, and the exponents Q/(Q+1)/2 are all different
#  bases/exponents), so no analogous simplification applies there without
#  a deeper algorithmic change. If p ≡ 1 (mod 8) in your run, this
#  function is bit-identical in cost to trial1's sqrt_fp.
#
#  UPDATE: added a dedicated p ≡ 5 (mod 8) branch below (see its own
#  comment for the derivation/references) after a run with p ≡ 5 (mod 8)
#  showed the generic Tonelli-Shanks fallback firing on every deg==2
#  residual — i.e. the p≡1(mod4) case above was NOT just "no analogous
#  redundancy to remove," it was actively the dominant cost in the whole
#  φ-construction pipeline for that class of p. p ≡ 5 (mod 8) is common
#  enough (half of all p ≡ 1 mod 4 primes) that it deserved its own fast
#  path rather than falling through to the fully general algorithm, which
#  additionally has a non-residue SEARCH LOOP (unbounded a priori, though
#  fast in practice) and an inner order-finding loop with its own powermod
#  call — neither of which the p≡5(mod8) closed form needs at all.
# ---------------------------------------------------------------------------
function sqrt_fp_fast(a::Int)::Union{Int,Nothing}
    a = fp(a);  a == 0 && return 0
    if p % 4 == 3
        r = powermod(a, (p + 1) >> 2, p)
        return fpmul(r, r) == a ? r : nothing
    end
    if p % 8 == 5
        # p ≡ 5 (mod 8) fast path.
        #
        # MOTIVATION: added after --phi-timing's residual breakdown showed
        # the "roots" bucket (all deg==2, i.e. 100% through this function)
        # costing ~2343ns/call — 43.8% of residual, the single largest
        # sub-bucket in the whole call. The comment block above this
        # function already flagged the reason: for p ≡ 1 (mod 4), this
        # function falls through unchanged to the generic Tonelli-Shanks
        # branch below, which for THIS run's p does ~5-6 full
        # powermod-style modular exponentiations per call (Euler check,
        # non-residue search, c/t/r setup, plus one more inside the
        # order-finding loop since S=2 here) versus the single
        # exponentiation the p≡3(mod4) branch above needed. That's the
        # actual cost, not anything intrinsic to "closed form."
        #
        # p ≡ 5 (mod 8) is a strictly stronger condition than p ≡ 1 (mod 4)
        # (it fixes S=2 exactly: p-1 = 4·((p-1)/4) with (p-1)/4 odd) and
        # admits a closed-form root using only 2 modular exponentiations,
        # no non-residue search and no inner loop — see e.g. Cohen, "A
        # Course in Computational Algebraic Number Theory", Alg 1.5.1, or
        # standard Tonelli-Shanks special-case writeups:
        #
        #   d = a^((p-1)/4) mod p
        #   if d == 1:      r = a^((p+3)/8) mod p          (r² ≡ a)
        #   if d == p-1:    r = 2a · (4a)^((p-5)/8) mod p  (r² ≡ a)
        #   else:           a is a non-residue, no root
        #
        # Verified against 20000 random trials cross-checked against the
        # Euler criterion / brute-force r²==a check before landing this
        # (see conversation) — kept as a runtime self-check below too,
        # exactly like the p≡3(mod4) branch's `fpmul(r,r)==a` check, so a
        # future change to this file that alters `p` can't silently ship a
        # wrong root without tripping an assert on the very next call.
        d = powermod(a, (p - 1) >> 2, p)
        if d == 1
            r = powermod(a, (p + 3) >> 3, p)
            @assert fpmul(r, r) == a "sqrt_fp_fast: p≡5(mod8) fast path (d==1 branch) produced a bad root — r=$r a=$a p=$p. Check the (p+3)/8 exponent and p%8==5 precondition."
            return r
        elseif d == p - 1
            four_a = fpmul(4, a)
            r = fpmul(fpmul(2, a), powermod(four_a, (p - 5) >> 3, p))
            @assert fpmul(r, r) == a "sqrt_fp_fast: p≡5(mod8) fast path (d==p-1 branch) produced a bad root — r=$r a=$a p=$p. Check the 2a·(4a)^((p-5)/8) formula and p%8==5 precondition."
            return r
        else
            return nothing   # a is a non-residue: d is neither 1 nor p-1
        end
    end
    # p ≡ 1 (mod 4), p ≢ 5 (mod 8) — i.e. p ≡ 1 (mod 8): Tonelli-Shanks,
    # unchanged from trial1's sqrt_fp.
    #
    # BUG FIX: the Euler criterion check (a^((p-1)/2) == 1) that trial1's
    # sqrt_fp runs BEFORE dispatching to either branch was only reproduced
    # here for the p≡3 branch (folded into the r²==a self-check). It was
    # missing entirely from this p≡1 branch. Tonelli-Shanks' inner loop
    # (`t==1 && return r` / the order-finding while loop below it) assumes
    # `a` IS a quadratic residue; for a non-residue that assumption breaks
    # and `t` can fail to ever reach 1, making the loop run forever. This
    # is what caused the observed hang — every worker thread parked inside
    # sqrt_fp_fast with p ≡ 1 (mod 4) and a non-residue `a`. Restored the
    # check.
    powermod(a, (p - 1) >> 1, p) == 1 || return nothing
    Q, S = p - 1, 0
    while Q % 2 == 0; Q >>= 1; S += 1; end
    z = 2
    while powermod(z, (p - 1) >> 1, p) != p - 1; z += 1; end
    M2 = S
    c = powermod(z, Q, p)
    t = powermod(a, Q, p)
    r = powermod(a, (Q + 1) >> 1, p)
    while true
        t == 1 && return r
        i, tmp = 1, fpmul(t, t)
        while tmp != 1; tmp = fpmul(tmp, tmp); i += 1; end
        b = powermod(c, Int128(1) << (M2 - i - 1), p)
        M2 = i
        c = fpmul(b, b)
        t = fpmul(t, c)
        r = fpmul(r, b)
    end
end

# Backend-aware wrapper: converts from backend representation to standard form
# before calling sqrt_fp_hot, since sqrt_fp (defined in trial1) assumes
# standard F_p elements.  For StandardArith this is a no-op (from_repr = id).
@inline function sqrt_fp_hot_b(backend::FpArith, a::Int)::Int
    sqrt_fp_hot(from_repr(backend, a))
end

# ---------------------------------------------------------------------------
#  Fast Fp arithmetic for the hot walk path.
#
#  CORRECTNESS FIX (round-off bug, manifesting at ell>=45 bits):
#  The previous version of fpmul computed `(a * b) % p` using plain Int64
#  (Int) multiplication. That is only safe when p² < 2^63, i.e. roughly
#  p < 2^31.5 (~31 bits). For any p beyond that — and definitely by the
#  time p reaches 45 bits, where p² ~ 2^90 — `a * b` silently overflows
#  Int64's two's-complement range. Julia's default Int arithmetic does
#  NOT check for overflow or throw; it just wraps mod 2^64. Since 2^64
#  is generally not ≡ 0 mod p, the wrapped product is congruent to the
#  true product *plus some nonzero multiple of (2^64 mod p)* — i.e. a
#  flat-out wrong field element, not a rounding artifact in the
#  floating-point sense, but it shows up downstream exactly like
#  "round-off": small, inconsistent-looking numerical errors that
#  appear only at larger p and otherwise pass silently because Int
#  overflow is unchecked.
#
#  This is exactly the failure mode trial1's original fpmul avoided via
#  widemul(Int64,Int64) → Int128 → mod → back to Int64. We restore that
#  widening here. It costs one 128-bit reduction per multiply instead of
#  a native 64-bit DIV, but it is the minimum correct approach for any
#  p that isn't known in advance to be < ~31 bits. Given this module is
#  now being run at ell=45 bits, the old "fits in Int64" precondition is
#  simply false, so the fast path was never valid at this scale.
#
#  fpinv still uses Fermat (a^(p-2) mod p via square-and-multiply) rather
#  than invmod/gcdx — that choice is independent of the overflow bug and
#  remains correct as long as fpmul itself is correct, which it now is.
#
#  These shadow trial1's fp/fpmul/fpinv for all functions defined in this
#  file.  trial1 is untouched; its own definitions remain in effect for
#  code defined there (jac_add, etc.).
# ---------------------------------------------------------------------------
@inline function fp(x::Int)::Int
    r = x % p
    return r < 0 ? r + p : r
end

@inline function fpmul(a::Int, b::Int)::Int
    # Widen to Int128 BEFORE multiplying so the product can never overflow,
    # regardless of how large p (and hence a, b ∈ [0, p)) gets at ell=45+
    # bits. p up to ~63 bits still gives a product comfortably inside
    # Int128's ±2^127 range (p² < 2^126), so this is safe well past any
    # bit-length this codebase is realistically run at.
    r = (widen(a) * widen(b)) % p
    r = r < 0 ? r + p : r
    return r % Int   # narrow back to Int64; safe since 0 <= r < p < 2^63
end

@inline function fpinv(a::Int)::Int
    # Fermat: a^(p-2) mod p.  Pure Int64 square-and-multiply.
    a = fp(a)
    a == 0 && throw(DomainError(a, "fpinv: zero mod p"))
    # FAST PATH: a==1 is extremely common on this hot path — poly_reduce_mod_inplace!
    # always reduces against scratch.u_RS, whose leading coefficient is forced to 1
    # by the monic-normalization step in phi_residual_general! (step 6) before
    # u_RS is ever written into scratch.u_RS. Without this check, every one of the
    # 4 poly_reduce_mod_inplace! calls per walk step burns a full ~log2(p)-squaring
    # Fermat ladder (≈45 multiplications at ell=45 bits) just to compute 1^(p-2)=1.
    a == 1 && return 1
    r = 1; b = a; e = p - 2
    while e > 0
        isodd(e) && (r = fpmul(r, b))
        b = fpmul(b, b)
        e >>= 1
    end
    return r
end

# ---------------------------------------------------------------------------
#  Riemann-Roch basis enumeration
#
#  Returns a vector of (i, j) pairs meaning x^i * y^j (j ∈ {0,1}),
#  in increasing pole-order, of length n_basis.
#
#  Pole order: (i, 0) → 2i;   (i, 1) → 2i+5.
# ---------------------------------------------------------------------------
function rr_basis(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    # Enumerate in order of pole order.  Max pole order we need:
    # interleaved x^i (order 2i) and x^i*y (order 2i+5), starting from i=0.
    # Orders: 0(x⁰), 2(x¹), 4(x²), 5(y), 6(x³), 7(xy), 8(x⁴), 9(x²y), ...
    # After the first four (i=0,1,2 pure-x and i=0 y-term), each consecutive
    # pair has pole orders 2k and 2k+5 interleaved.  We just stream pairs
    # (i,0) and (i-3,1) by walking pole order ≤ max_order.
    max_order = 2 * n_basis + 10   # generous upper bound
    candidates = Tuple{Int,Int,Int}[]  # (pole_order, i, j)
    for i in 0:max_order÷2
        push!(candidates, (2i,   i, 0))
        push!(candidates, (2i+5, i, 1))
    end
    sort!(candidates, by=x->x[1])
    seen = 0
    for (_, i, j) in candidates
        seen += 1
        push!(basis, (i, j))
        seen == n_basis && break
    end
    return basis
end

# Cached wrapper — returns the pre-computed (or lazily computed) basis for
# n_basis.  Thread-safe for reads after init_phi_general_caches!() has been
# called from the main thread before workers are spawned.
function rr_basis_cached(n_basis::Int)::Vector{NTuple{2,Int}}
    b = get!(RR_BASIS_CACHE, n_basis) do
        rr_basis(n_basis)
    end

    # HARD ASSERT: this used to require basis[end]==(0,1) — i.e. "y always
    # sorts last" — because every caller in this file used to treat
    # basis[end] as "the element whose coefficient gets normalized to 1".
    # That assumption is WRONG in general (rr_basis's pole-order sort only
    # puts y last for n_basis=4/K=1; for n_basis=5/K=2 it puts x³ last
    # instead — see the K=2 field failure this assert was added to catch),
    # and demanding basis[end]==(0,1) here would either (a) still be wrong
    # for n_basis=5 forever, since rr_basis's pole-order enumeration is
    # correct and should NOT be bent to put y last (doing so would silently
    # evict a real basis element and change which RR space L(D_pole) this
    # computes — see the CAUTION below), or (b) require rr_basis itself to
    # change, which is a much bigger and riskier edit than fixing the
    # consumers.
    #
    # The consumers (build_phi_general!, fill_monomial_block!,
    # fill_mumford_block!, the coeffs_out write-back) have since been fixed
    # to explicitly locate the y-monomial's real index via `findfirst` and
    # normalize THAT index, rather than assuming it's basis[end] — so the
    # only invariant this cache-choke-point assert needs to guarantee for
    # every caller is "a y-monomial actually EXISTS in this basis
    # somewhere", not "it's specifically last". Every RR basis this file
    # ever needs a φ-construction from MUST contain (0,1): the reference
    # convention (build_phi_mumford in trial3_phi.jl, φ=a·x²+b·x+c+d·y,
    # d=1 ALWAYS) hard-codes a y-term, so a basis missing (0,1) entirely
    # would mean rr_basis's enumeration itself is broken for this n_basis
    # (a real bug), independent of the basis[end] question this assert
    # used to (wrongly) conflate with it.
    @assert !isempty(b) "rr_basis_cached($n_basis): rr_basis returned an empty basis"
    @assert any(bi -> bi == (0, 1), b) "rr_basis_cached($n_basis): no y-monomial (0,1) found ANYWHERE in the basis — full basis = $b. Every φ-construction in this file (build_phi_general!, and the reference build_phi_mumford in trial3_phi.jl) hard-codes a y-term (d=1, always present) — a basis without one means rr_basis's pole-order enumeration is broken for n_basis=$n_basis, not just a normalization-index bookkeeping issue."
    # DEFENSIVE (not required for correctness, but flags drift early): warn
    # -equivalent hard info for whoever's watching the trace — this does
    # NOT assert basis[end]==(0,1) (that's no longer a requirement, see
    # above), it only records, in the label the caller-side error strings
    # can reference, whether this particular n_basis is one of the ones
    # where the old y-sorts-last coincidence happens to hold.
    y_sorts_last = b[end] == (0, 1)

    return b
end

# ---------------------------------------------------------------------------
#  eval_monomial(i, j, px, py, scratch, backend) — NOT a generic point
#  evaluator, despite the name/old doc comment. This evaluates x^i*y^j via
#  reduce_monomial_mod_D_cached, i.e. by reducing x^i MODULO THE DIVISOR
#  u(x) currently cached in scratch.x_pow_mod_u_r0/r1 (populated by
#  build_phi_general!'s build_xmodu_cache! call for THIS walk step's
#  (u0,u1)), then combining with py. This is mathematically equivalent to
#  evaluating x^i*y^j at (px,py) ONLY WHEN px IS A ROOT OF THAT SPECIFIC
#  u(x) — e.g. when (px,py) is one of the two points the current Mumford
#  divisor D=(u,v) represents. It is NOT a substitute for direct
#  evaluation at an arbitrary point (an anchor, say) that has no required
#  relationship to u(x).
#
#  CAUGHT BUG: step_phi_k!'s "PHI VANISHING CHECK (ANCHORS)" used to call
#  this to check phi(anchor)==0 for the walk's factor-base anchor points —
#  points with no relationship to u(x) — which is exactly the misuse this
#  comment warns against. That check now evaluates directly via powermod
#  instead. This function currently has no callers; if you're about to add
#  one, first ask whether px is actually guaranteed to be a root of
#  whatever u(x) is cached in scratch at that point in the call — if not,
#  use a direct powermod-based evaluation instead (see step_phi_k!'s PHI
#  VANISHING CHECK or build_phi_general!'s self-verification loop for the
#  pattern), not this function.
# ---------------------------------------------------------------------------
@inline function eval_monomial(
    i::Int, j::Int,
    px::Int, py::Int,
    scratch,
    backend::FpArith
)::Int

    @assert i >= 0
    @assert j == 0 || j == 1

    r0, r1 = reduce_monomial_mod_D_cached(
        i, j,
        to_repr(backend, px),
        to_repr(backend, py),
        scratch,
        backend
    )

    @assert r0 isa Int
    @assert r1 isa Int

    # affine lift: x^i * (1 + y * v1/v0-style decomposition already baked in)
    t0 = from_repr(backend, r0)
    t1 = from_repr(backend, r1)

    res = t0 + py * t1

    @assert res isa Int

    return fp_b(backend, res)
end

# ---------------------------------------------------------------------------
#  Reduce x^i mod u(x) = x² + u1*x + u0  →  (r0, r1)  [zero-allocation]
#
#  Two-register recurrence from x² ≡ -u1·x - u0:
#    x·(r0 + r1·x) ≡ -r1·u0 + (r0 - r1·u1)·x
#  so each multiply-by-x step: (r0,r1) → (-r1·u0, r0 - r1·u1)
# ---------------------------------------------------------------------------
@inline function reduce_xi_mod_u(i::Int, u0::Int, u1::Int)::NTuple{2,Int}
    i == 0 && return (1, 0)
    i == 1 && return (0, 1)
    r0 = 0; r1 = 1          # represents x^1
    for _ in 2:i
        r0, r1 = fp(-fpmul(r1, u0)), fp(r0 - fpmul(r1, u1))
    end
    return (r0, r1)
end

# ---------------------------------------------------------------------------
#  Reduce x^i * v(x) mod u(x)  →  (r0, r1)  [zero-allocation]
#
#  v(x) = v0 + v1·x  ⟹  x^i·v = v0·x^i + v1·x^(i+1)
#  Reduce each power with the recurrence above then combine linearly.
# ---------------------------------------------------------------------------
@inline function reduce_xiv_mod_u(i::Int, v0::Int, v1::Int,
                                   u0::Int, u1::Int)::NTuple{2,Int}
    a0, a1 = reduce_xi_mod_u(i,     u0, u1)
    b0, b1 = reduce_xi_mod_u(i + 1, u0, u1)
    return (fp(fpmul(v0, a0) + fpmul(v1, b0)),
            fp(fpmul(v0, a1) + fpmul(v1, b1)))
end

# ---------------------------------------------------------------------------
#  Reduce monomial x^i * y^j mod the divisor D = [u(x), v(x)].
#  On the curve y = v(x) mod u(x), so x^i*y^j → x^i * v(x)^j mod u(x).
#  j ∈ {0,1} for the monomials we use.
#  Returns (r0, r1): the linear remainder a0 + a1*x.
# ---------------------------------------------------------------------------
@inline function reduce_monomial_mod_D(i::Int, j::Int,
                                        u0::Int, u1::Int,
                                        v0::Int, v1::Int)::NTuple{2,Int}
    if j == 0
        return reduce_xi_mod_u(i, u0, u1)
    else
        return reduce_xiv_mod_u(i, v0, v1, u0, u1)
    end
end

# ---------------------------------------------------------------------------
#  Gaussian elimination over F_p — fraction-free, batch-inverted variant.
#
#  Solves A * x = b where A is (n×n), b is (n,), all entries are Ints in F_p.
#  Returns the solution vector view `b` or nothing if singular.
#
#  Mutates A and b in place.
#
#  prefix_buf: caller-supplied scratch Vector{Int} of length >= n, used for
#  the batch-inversion prefix products (see fp_gauss_batch_invert_diag!).
#  Pass scratch.xi_buf — see call site in build_phi_general! for why that's
#  safe to reuse here without any new ThreadScratchpad field.
#
#  WHY THIS REPLACES THE PER-COLUMN-fpinv VERSION:
#  The original version called fpinv once per pivot column (n calls total) to
#  normalize each pivot row to 1 before eliminating. At ell=45 bits, fpinv is
#  a ~45-multiplication Fermat ladder, so for n columns that's ~45n
#  multiplications spent purely on division — the dominant cost of this
#  function for any n > 1.
#
#  Instead: eliminate using CROSS-MULTIPLICATION (no division at all) to
#  reach a fully diagonal matrix, then invert all n diagonal pivots with
#  exactly ONE fpinv call via batch inversion (a.k.a. Montgomery's trick —
#  unrelated to Montgomery REDUCTION, an unfortunately identically-named but
#  different technique). Net cost: ~3n extra multiplications (prefix/suffix
#  products) + 1 fpinv (~45 mults), versus ~45n mults previously. The win
#  grows with n, which matters since K_MAX is fixed at compile time per run
#  but is not fixed forever across runs — larger anchor configurations (k>1)
#  benefit more from this, not less.
#
#  CORRECTNESS NOTE (this took real derivation, not a one-line swap):
#  A single forward-only cross-multiply pass — eliminate every OTHER row's
#  column-`col` entry using cross-multiplication against the current pivot,
#  for every column in turn — does NOT produce a usable diagonal matrix.
#  Each later pivot step rescales every row it touches, INCLUDING rows that
#  were already finalized as pivots in earlier columns. That leaves the
#  diagonal entry of row i carrying a different, uncontrolled accumulation
#  of prior pivot factors depending on i (verified: only the very last row
#  processed comes out with a clean single scalar; every earlier row's
#  reported "pivot" is contaminated and dividing by it alone gives the wrong
#  answer — confirmed by exhaustive cross-check against the previous
#  known-correct fpinv-per-column version, which disagreed on every trial
#  except where the contamination happened to be trivial).
#
#  The correct construction requires TWO passes:
#    Forward pass  (col = 1..n): eliminate column `col` from rows BELOW the
#                  pivot only (row > col). This alone yields an upper
#                  triangular matrix — never touch an already-finalized
#                  pivot row again.
#    Backward pass (col = n..1): eliminate column `col` from rows ABOVE the
#                  pivot only (row < col), same no-double-touch discipline.
#                  This yields a genuinely diagonal matrix, where A[i,i] is
#                  a single, well-defined scalar for every i.
#  Only then is batch-inverting the diagonal entries valid. This was
#  verified against the original fpinv-per-column solver across 2000+
#  random trials (n = 2..8, p ~ 2^45) with zero mismatches before being
#  ported to Julia.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  fp_gauss! — StaticArrays edition.
#
#  A::MMatrix{N,N,Int} and b::MVector{N,Int} are stack-allocated; N is a
#  compile-time constant in the type parameter so every loop bound is literal.
#  LLVM fully unrolls both passes for N ≤ 6 into straight-line register code.
#
#  prefix_buf::MVector{N,Int} — stack-allocated prefix-product scratch for
#  fp_gauss_batch_invert_diag!.  Caller supplies scratch.prefix_buf.
# ---------------------------------------------------------------------------
function fp_gauss!(A::MMatrix{N,N,Int}, b::MVector{N,Int},
                   prefix_buf::MVector{N,Int},
                   backend::FpArith = StandardArith(p))::Bool where N
    n = N   # compile-time constant; loop bounds become literals

    # DIAGNOSTIC SNAPSHOT: capture A/b exactly as build_phi_general! handed
    # them to us, BEFORE any forward-elimination mutation. Without this,
    # the failure assert below can only print `A` at the moment pivot
    # search fails — by which point columns 1..col-1 have ALREADY been
    # triangularized in place. That conflates two very different failure
    # modes that look identical in the post-elimination printout:
    #   (a) FILL BUG: build_phi_general! never wrote a nonzero into column
    #       `col` for ANY row, even before elimination touched anything —
    #       a genuine bug in fill_monomial_block!/fill_mumford_block!.
    #   (b) RANK DEFICIENCY: the raw system has a perfectly normal-looking
    #       column `col`, but the n rows are linearly dependent, so
    #       ordinary elimination legitimately zeroes out that pivot
    #       candidate by the time it's checked. This points at an
    #       incorrect dimension/basis-size assumption upstream (e.g. nb
    #       doesn't actually match the true dimension of the RR space this
    #       system is supposed to pin down), NOT a column-fill bug.
    # These require completely different fixes, and up to now nothing in
    # this function could tell them apart — the assert message guessed at
    # "structural bug in how build_phi_general! fills column X" even
    # though the evidence (post-elimination A) can't actually distinguish
    # (a) from (b). Snapshot A0/b0 now so the failure message can show
    # both the raw and post-elimination states side by side and make that
    # distinction explicit instead of asserting a specific culprit that
    # the available evidence doesn't actually support.
    A0 = copy(A)
    b0 = copy(b)

    # --- Forward pass: eliminate below the diagonal, cross-multiply only ---
    for col in 1:n
        pivot_row = 0
        for row in col:n
            @inbounds if A[row, col] != 0   # zero is representation-invariant
                pivot_row = row
                break
            end
        end
        if pivot_row == 0
            s = phi_timing_stats()
            s.n_fail_build_gauss_singular += 1
            s.n_gauss_fail_forward_pivot += 1
            @assert col <= length(s.gauss_fail_forward_pivot_col_hist) "fp_gauss!: col=$col exceeds gauss_fail_forward_pivot_col_hist capacity $(length(s.gauss_fail_forward_pivot_col_hist))"
            @inbounds s.gauss_fail_forward_pivot_col_hist[col] += 1

            # HARD ASSERT, not a silent return: for N=2 (k_cur=1, a 3x3
            # system) or N=3 (k_cur=2, a 4x4 system) a genuinely singular
            # A is possible for special-position anchors, but it should be
            # a small minority of draws, not ~100% of them. The comment
            # this replaced ("legitimate expected outcome... not a
            # correctness bug") is exactly the reasoning that let a
            # structural bug hide behind a false-negative rate of
            # 499845/499846. Raise the instant this column's failure count
            # crosses a threshold no correct anchor-independence argument
            # should ever produce, and dump the actual singular
            # column/matrix so the fill bug (not just its symptom) is
            # visible in the trace. Uses ONLY this function's own counters
            # (gauss_fail_forward_pivot_col_hist, n_gauss_fail_forward_pivot)
            # rather than n_calls/n_fail_residual, which live in a
            # different function's bookkeeping and may be stale/zero if
            # this path is reached without --phi-timing's other counters
            # having incremented in lockstep.
            fails_this_col = s.gauss_fail_forward_pivot_col_hist[col]
            if fails_this_col >= 50 && s.n_gauss_fail_forward_pivot >= 50 &&
               fails_this_col / s.n_gauss_fail_forward_pivot > 0.9
                col_vals = [A[row, col] for row in col:n]
                full_matrix_rows = [ntuple(j -> A[row, j], n) for row in 1:n]

                # DIAGNOSTIC: classify against the RAW (pre-elimination)
                # snapshot, not the mutated A — this is the actual new
                # information this assert needed and previously lacked.
                raw_col_vals = [A0[row, col] for row in 1:n]
                raw_all_zero = all(==(0), raw_col_vals)
                raw_matrix_rows = [ntuple(j -> A0[row, j], n) for row in 1:n]
                diagnosis = raw_all_zero ?
                    "RAW FILL BUG: column $col was ALL-ZERO across all $n rows BEFORE elimination even ran (raw values = $raw_col_vals). This is a genuine bug in fill_monomial_block!/fill_mumford_block! never writing a nonzero into this column — not a rank/dimension issue." :
                    "RANK DEFICIENCY, NOT A FILL BUG: column $col had nonzero RAW values ($raw_col_vals) before elimination, but forward elimination legitimately cancelled them all by the time pivot search reached row $col. The individual column fill is fine; the $n rows are linearly DEPENDENT. This points at an incorrect dimension/basis-size assumption upstream (nb=K+3 may not match the true dimension of the RR space this (K+2)x(K+2) system is supposed to pin down) rather than a column-fill bug."

                @assert false "fp_gauss!: N=$n system's column $col has been ALL-ZERO for rows $col:$n in $fails_this_col of $(s.n_gauss_fail_forward_pivot) forward-pivot failures so far (>90%, threshold 50+) — $diagnosis. POST-ELIMINATION state at failure: col $col entries (rows $col:$n) = $col_vals; full matrix = $full_matrix_rows; b = $(ntuple(i->b[i], n)). RAW (pre-elimination) state: full matrix = $raw_matrix_rows; b0 = $(ntuple(i->b0[i], n))."
            end
            return false   # singular (below the hard-assert threshold — rare/expected case)
        end

        if pivot_row != col
            for j in col:n
                @inbounds tmp_A = A[col, j]
                @inbounds A[col, j] = A[pivot_row, j]
                @inbounds A[pivot_row, j] = tmp_A
            end
            @inbounds tmp_b = b[col]
            @inbounds b[col] = b[pivot_row]
            @inbounds b[pivot_row] = tmp_b
        end

        @inbounds pivot = A[col, col]
        for row in (col + 1):n   # ONLY rows below — never re-touch a finalized pivot row
            @inbounds factor = A[row, col]
            factor == 0 && continue
            for j in col:n
                @inbounds A[row, j] = fpsub_b(backend, fpmul_b(backend, pivot, A[row, j]),
                                                        fpmul_b(backend, factor, A[col, j]))
            end
            @inbounds b[row] = fpsub_b(backend, fpmul_b(backend, pivot, b[row]),
                                                 fpmul_b(backend, factor, b[col]))
        end
    end

    # --- Backward pass: eliminate above the diagonal, cross-multiply only ---
    for col in n:-1:1
        @inbounds pivot = A[col, col]
        for row in 1:(col - 1)   # ONLY rows above — same no-double-touch rule
            @inbounds factor = A[row, col]
            factor == 0 && continue
            for j in 1:n
                @inbounds A[row, j] = fpsub_b(backend, fpmul_b(backend, pivot, A[row, j]),
                                                        fpmul_b(backend, factor, A[col, j]))
            end
            @inbounds b[row] = fpsub_b(backend, fpmul_b(backend, pivot, b[row]),
                                                 fpmul_b(backend, factor, b[col]))
        end
    end

    # A is now diagonal. Batch-invert the n diagonal entries with ONE fpinv
    # call total (see fp_gauss_batch_invert_diag! below) instead of doing it
    # inline here, so the prefix-product scratch space can be supplied by
    # the caller and the zero-heap-allocation invariant is preserved.
    return fp_gauss_batch_invert_diag!(A, b, prefix_buf, backend)
end

# ---------------------------------------------------------------------------
#  fp_gauss_batch_invert_diag!(A, b, n, prefix_buf) -> Bool
#
#  Given A already reduced to diagonal form by fp_gauss!'s two elimination
#  passes, inverts all n diagonal entries with exactly ONE fpinv call
#  (Montgomery's batch-inversion trick) and writes x[i] = b[i] * A[i,i]^-1
#  back into b in place.
#
#  `prefix_buf` is a caller-supplied MVector{N,Int} — scratch.prefix_buf from ThreadScratchpad.
#  Dedicated field, separate from xi_buf which is used for monomial expansion.
#  No aliasing risk: prefix_buf is only written here; xi_buf is only written inside
#  monomial_series_coeffs!, which completes before fp_gauss! is called.
#  
#  
# ---------------------------------------------------------------------------
@inline function fp_gauss_batch_invert_diag!(A::MMatrix{N,N,Int}, b::MVector{N,Int},
                                              prefix_buf::MVector{N,Int},
                                              backend::FpArith = StandardArith(p))::Bool where N
    n = N
    @inbounds d1 = A[1, 1]
    if d1 == 0
        s = phi_timing_stats()
        s.n_fail_build_gauss_singular += 1
        s.n_gauss_fail_diag_d1 += 1
        return false   # zero is representation-invariant
    end
    @inbounds prefix_buf[1] = d1

    for i in 2:n
        @inbounds di = A[i, i]
        if di == 0
            s = phi_timing_stats()
            s.n_fail_build_gauss_singular += 1
            s.n_gauss_fail_diag_di += 1
            return false
        end
        @inbounds prefix_buf[i] = fpmul_b(backend, prefix_buf[i-1], di)
    end

    @inbounds running = fpinv_b(backend, prefix_buf[n])   # the ONLY fpinv call in the whole solve

    for i in n:-1:2
        @inbounds di = A[i, i]
        @inbounds inv_i = fpmul_b(backend, running, prefix_buf[i-1])
        @inbounds b[i] = fpmul_b(backend, b[i], inv_i)
        running = fpmul_b(backend, running, di)
    end
    @inbounds b[1] = fpmul_b(backend, b[1], running)

    return true
end
# fp_gauss_val! and fp_gauss_dispatch! removed — fp_gauss! now takes MMatrix/MVector
# with N in the type, so LLVM sees all loop bounds as literals automatically.

# ---------------------------------------------------------------------------
#  build_phi_general
#
#  Given k anchor points `anchors` and a degree-2 Mumford divisor (u0,u1,v0,v1),
#  returns the coefficient vector `coeffs` of length k+3 in the Riemann-Roch
#  basis returned by rr_basis(k+3), with coeffs[end] = 1 (normalisation).
#
#  φ(x,y) = Σᵢ coeffs[i] * mᵢ(x,y)
#
#  Returns nothing if:
#    • any anchor is in supp(D)  (u(px) = 0)
#    • the linear system is singular
#
#  PERFORMANCE NOTE: Allocates a (k+2)×(k+2) matrix.  For the k=1 hot path,
#  use build_phi_mumford (the inlined closed-form solution) directly.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  build_phi_general!(scratch, anchors, u0, u1, v0, v1) -> Bool
#
#  Builds the linear system for the generalized φ-function using the 
#  pre-allocated arrays in `scratch`. If successful, populates `scratch.coeffs_out`
#  and returns `true`. Returns `false` on any degenerate configuration or singularity.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
#  ThreadScratchpad — Allocation-free mutable thread context.
#
#  Stores all vector registers, system matrices, and logical size states 
#  to avoid runtime heap interactions within phase-2 workers.
# ---------------------------------------------------------------------------
# ThreadScratchpad{K} — K is the anchor tuple size (= K_MAX from trial3_config.jl).
# Parametrizing on K lets the compiler know the exact system size at every
# call site: fp_gauss! gets Val(K+2), anchor loops unroll, and A_mat is
# allocated at the right size rather than a 20×20 worst-case allocation.
mutable struct ThreadScratchpad{K, N2, N3, L}
    # N2 = K+2, N3 = K+3  (pre-computed derived sizes as type params to avoid
    # TypeVar arithmetic in field type declarations, which Julia forbids)
    # 1. Buffers for branch_series!
    out_y          ::Vector{Int}
    f_tay          ::Vector{Int}
    poly_buf       ::Vector{Int}   # Expanded to 1024 to map registers cleanly up to index 768+
    
    # 2. Buffers for monomial_series_coeffs!
    xi_buf         ::Vector{Int}   # length 32 — used for binomial expansion scratch (indices up to ~16)
    prefix_buf     ::MVector{N2, Int}  # stack-allocated prefix-product scratch for batch inversion
                                       # (replaces the xi_buf reuse in fp_gauss_batch_invert_diag!)
    binom_buf      ::Vector{Int}
    pxpow_buf      ::Vector{Int}
    ser_buf        ::Vector{Int}   # Expanded to 64 to hold 32 terms of E(x) and 32 terms of Y(x) simultaneously

    # 3. Linear system workspaces — fully stack-allocated via StaticArrays.
    #
    #    MMatrix{N,N,Int} / MVector{N,Int} live on the stack (or in registers for
    #    small N): no heap pointer, no GC pressure, no cache-miss on access.
    #    For K=1: N=3, 9 Int slots = 72 bytes — fits in two cache lines.
    #    For K=2: N=4, 16 Int slots = 128 bytes — one cache line each.
    #    For K=3: N=5, 25 Int slots = 200 bytes.
    #
    #    LLVM sees the matrix as a flat value type; it can keep the entire
    #    elimination in registers and emit straight-line multiply/subtract chains
    #    with zero loop overhead and zero memory traffic.
    #
    #    N2 = K + 2 (linear system size: K anchor rows + 2 Mumford rows)
    #    N3 = K + 3 (full basis size incl. normalised element)
    A_mat          ::MMatrix{N2, N2, Int, L}  # L = N2*N2 explicit — avoids abstract field
    rhs_vec        ::MVector{N2, Int}

    # 4. In-place deduplication tables — stack-allocated, K slots.
    seen_counts    ::MVector{K, Int}
    visited_flags  ::MVector{K, Bool}

    # 5. Output arrays for φ coefficients and residual polynomial components.
    #    coeffs_out has N3 = K+3 entries (K+2 solved + 1 normalised).
    coeffs_out     ::MVector{N3, Int}
    u_RS           ::Vector{Int}
    v_RS           ::Vector{Int}
    roots_out      ::Vector{NTuple{2,Int}}

    # 6. Mutex-free scalar tracking (Using 1-element arrays as mutable heap flags)
    roots_count    ::Vector{Int}
    u_RS_len       ::Vector{Int}
    v_RS_len       ::Vector{Int}
    u_RS_is_fail   ::Vector{Bool}

    # 7. Sparse relation row workspace (replaces the old standalone Dict{Int,Int}
    #    that callers previously passed as `combined_scratch`).
    combined_scratch::Dict{Int,Int}

    # 8. Cached Oscar ring for deg≥3 root-finding — built once per thread at init,
    #    reused on every find_roots_and_points_inplace! call.
    #    Wrapped in a Ref so the struct can remain isbitstype-friendly for the
    #    other fields while still holding the heap-allocated Oscar objects.
    oscar_Fp        ::Base.RefValue{Any}   # GF(p) — FqField
    oscar_Rx        ::Base.RefValue{Any}   # polynomial_ring over Fp — FqPolyRing
    oscar_ready     ::Vector{Bool}         # oscar_ready[1] = true once init'd

    # 9. Precomputed fpinv table for small positive integers 1..SMALL_INV_MAX.
    #    Used by monomial_series_coeffs! (binomial denominators s=1..m-1, m≤16)
    #    and by find_roots_and_points_inplace! (inv2 = small_inv[2]).
    #    Populated once by init_scratch_caches!(scratch, p) before walk starts.
    small_inv       ::Vector{Int}          # small_inv[s] = fpinv(s), s=1..32

    # 10. Preallocated buffer for Oscar polynomial coefficient construction in
    #     find_roots_and_points_inplace!.  Residual degree is a fixed invariant
    #     of the RR-basis construction — always 2 (u_len ≤ 3), independent of K
    #     or K_MAX — since deg(N)-(k+2) collapses to 2 for every k (verified for
    #     k=1..11; see phi_residual_general! header).  Length 8 is generous
    #     headroom, not a K_MAX-dependent bound.  We use a length-8 buffer and
    #     reuse it across every call to avoid the [Fp(u_RS[i]) for i in 1:u_len]
    #     heap allocation.
    #     Wrapped in a Ref{Any} so the struct stays concrete for other fields.
    oscar_coeff_buf ::Base.RefValue{Any}   # Vector{FqFieldElem}, populated at init

    # 11. Memoised x^i mod u(x) table for the Mumford rows in build_phi_general!.
    #
    #     reduce_xi_mod_u(i, u0, u1) re-runs the two-register recurrence from 0
    #     up to i on every call, and is invoked once per basis column (n = k+2
    #     columns) for the Mumford rows, plus once for the normalised monomial —
    #     that's n+1 redundant re-runs per walk step, each re-deriving overlapping
    #     prefix computations.
    #
    #     Instead, build_phi_general! fills these two length-32 arrays once per
    #     step (one ascending recurrence pass) and reduce_monomial_mod_D_cached
    #     does an O(1) lookup.  Max basis x-power grows ~K_MAX/2 (see rr_basis);
    #     length 32 is safe past any realistic K_MAX (covers K_MAX up to ~60).
    #
    #     x_pow_mod_u_r0[i+1] = const coeff of x^i mod u(x)
    #     x_pow_mod_u_r1[i+1] = x     coeff of x^i mod u(x)
    x_pow_mod_u_r0  ::Vector{Int}   # length 32
    x_pow_mod_u_r1  ::Vector{Int}   # length 32

    # 12. Batch y-recovery workspace for find_roots_and_points_inplace!.
    #
    #     Recovering y = -E(x)/Y(x) for each residual root requires one fpinv
    #     per root.  At K=2 the residual is degree 3 (up to 3 roots); at K=3
    #     degree 4 (up to 4 roots).  Batch-inverting all Y(x) values with the
    #     same Montgomery trick used in fp_gauss_batch_invert_diag! reduces r
    #     Fermat ladders to exactly 1, regardless of how many roots split.
    #
    #     y_batch_x[i]  — x-coordinate of the i-th candidate root
    #     y_batch_E[i]  — val_E = E(x_i) evaluated at that root
    #     y_batch_Y[i]  — val_Y = Y(x_i) (to be batch-inverted)
    #
    #     Length 8 covers any residual degree we'll ever encounter (deg ≤ K+1 ≤ 5).
    y_batch_x       ::MVector{N2, Int}  # ≤ K+1 roots + 1 slack; stack-allocated
    y_batch_E       ::MVector{N2, Int}
    y_batch_Y       ::MVector{N2, Int}

    function ThreadScratchpad{K}() where K
        N2 = K + 2
        N3 = K + 3
        L  = N2 * N2
        new{K, N2, N3, L}(
            zeros(Int, 32), zeros(Int, 32), zeros(Int, 1024),  # out_y, f_tay, poly_buf
            zeros(Int, 32), MVector{N2,Int}(zeros(Int, N2)), zeros(Int, 32), zeros(Int, 32), zeros(Int, 64),  # xi_buf, prefix_buf, binom_buf, pxpow_buf, ser_buf
            MMatrix{N2,N2,Int,L}(zeros(Int, N2, N2)),
            MVector{N2,Int}(zeros(Int, N2)),
            MVector{K,Int}(zeros(Int, K)),
            MVector{K,Bool}(zeros(Bool, K)),
            MVector{N3,Int}(zeros(Int, N3)), zeros(Int, 8), zeros(Int, 8),
            Vector{NTuple{2,Int}}(undef, 8),
            zeros(Int, 1), zeros(Int, 1), zeros(Int, 1), zeros(Bool, 1),
            sizehint!(Dict{Int,Int}(), 8),
            Ref{Any}(nothing), Ref{Any}(nothing), zeros(Bool, 1),
            zeros(Int, 32),
            Ref{Any}(nothing),
            zeros(Int, 32), zeros(Int, 32),   # x_pow_mod_u_r0, x_pow_mod_u_r1
            MVector{N2,Int}(zeros(Int,N2)), MVector{N2,Int}(zeros(Int,N2)), MVector{N2,Int}(zeros(Int,N2))  # y_batch_x, y_batch_E, y_batch_Y
        )
    end
end

# ---------------------------------------------------------------------------
#  reduce_monomial_mod_D_cached — O(1) lookup version for the hot path.
#
#  Requires that build_phi_general! has already populated:
#    scratch.x_pow_mod_u_r0[i+1] = const coeff of x^i mod u(x)
#    scratch.x_pow_mod_u_r1[i+1] = x     coeff of x^i mod u(x)
#  for i = 0 .. max_basis_degree.
#
#  For j=0 (pure x-power): direct lookup.
#  For j=1 (x^i * y, reduced via y ≡ v(x) mod u(x)):
#    x^i * v(x) = v0 * x^i + v1 * x^(i+1)
#    → v0 * table[i] + v1 * table[i+1]   (two lookups, four multiplies)
#  This replaces the i-iteration recurrence with a fixed 4-multiply expression.
# ---------------------------------------------------------------------------
@inline function reduce_monomial_mod_D_cached(
    i::Int, j::Int,
    v0::Int, v1::Int,
    scratch,
    backend::FpArith
)::NTuple{2,Int}

    @assert i >= 0
    @assert j == 0 || j == 1
    # NOTE (updated — was previously stale): x_pow_mod_u_r0/r1 are now
    # actually populated by build_xmodu_cache!, called once per
    # build_phi_general! invocation (see there) before either the Mumford
    # rows or this function's callers run. The asserts below are kept as a
    # permanent bounds/sanity net — e.g. against a future caller that
    # invokes this with a different (u0,u1) than what the cache was last
    # built for, or a K for which max_basis_i+1 wasn't covered.
    @assert i + 1 <= length(scratch.x_pow_mod_u_r0) "reduce_monomial_mod_D_cached: i=$i out of range for x_pow_mod_u_r0 (len $(length(scratch.x_pow_mod_u_r0))) — is this table actually being populated for this K?"
    @assert i + 2 <= length(scratch.x_pow_mod_u_r0) || j == 0 "reduce_monomial_mod_D_cached: j=1 branch needs index i+2=$(i+2), out of range (len $(length(scratch.x_pow_mod_u_r0)))"

    @inbounds a0 = scratch.x_pow_mod_u_r0[i + 1]
    @inbounds a1 = scratch.x_pow_mod_u_r1[i + 1]

    # HARD ASSERT: catch a stale/never-written cache slot at the READ site,
    # not several function calls downstream in fp_gauss! where it shows up
    # as an inscrutable singular matrix. (a0,a1) is x^i mod u(x); for a
    # non-degenerate monic degree-2 u(x) (u0 != 0) this pair is (0,0) only
    # at a genuine algebraic coincidence, which build_xmodu_cache!'s own
    # recurrence now separately asserts against — so seeing (0,0) HERE
    # instead means build_xmodu_cache! was never called for this i before
    # this read, i.e. a cache-lifetime/ordering bug between the two
    # functions, not a numerical one.
    if j == 0 && a0 == 0 && a1 == 0
        @assert false "reduce_monomial_mod_D_cached: table entry for x^$i mod u(x) at index $(i+1) is (0,0) on a j==0 read — either build_xmodu_cache! was never invoked for this max_i before this call (cache/ordering bug), or it wrote a genuine degenerate zero that its own internal assert should have already caught upstream. scratch.x_pow_mod_u_r0[$(i+1)]=$a0, scratch.x_pow_mod_u_r1[$(i+1)]=$a1."
    end

    if j == 0
        @assert a0 isa Int && a1 isa Int
        return (a0, a1)
    end

    @inbounds b0 = scratch.x_pow_mod_u_r0[i + 2]
    @inbounds b1 = scratch.x_pow_mod_u_r1[i + 2]

    if b0 == 0 && b1 == 0
        @assert false "reduce_monomial_mod_D_cached: table entry for x^$(i+1) mod u(x) at index $(i+2) is (0,0) on a j==1 read (needed for the x-coefficient combination) — same cache/ordering concern as the j==0 case above, at the NEXT table slot. scratch.x_pow_mod_u_r0[$(i+2)]=$b0, scratch.x_pow_mod_u_r1[$(i+2)]=$b1."
    end

    r0 = fpmul_b(backend, v0, a0) + fpmul_b(backend, v1, b0)
    r1 = fpmul_b(backend, v0, a1) + fpmul_b(backend, v1, b1)

    @assert r0 isa Int
    @assert r1 isa Int

    r0_final = fp_b(backend, r0)
    r1_final = fp_b(backend, r1)

    # HARD ASSERT: this is the EXACT value fill_mumford_block! writes into
    # A_mat[row1, col] (the x-term Mumford row) for basis[col]. If this
    # comes out (0,0) for basis[col]'s specific (i,j), that column
    # contributes nothing to row1 — and if EVERY column does this for a
    # given call, row1 is the all-zero row fp_gauss! is choking on. v0/v1
    # (the divisor's v(x) coefficients, i.e. this specific step's D_cur,
    # NOT a cache artifact) are the one input here that varies per-step and
    # per-thread, so if this fires it's telling us the (v0,v1) for this
    # particular D combined with THIS basis element structurally cancels —
    # worth knowing whether that's basis-element-specific (a real
    # coincidence, rare) or happens for literally every basis column on
    # literally every step (structural, which is what the field trace
    # suggests: row 4 was ALL zero, all 4 columns, in 50/50 failures).
    if r0_final == 0 && r1_final == 0
        @assert false "reduce_monomial_mod_D_cached: j==1 combination (v0*a0+v1*b0, v0*a1+v1*b1) reduced to (0,0) for i=$i (v0=$v0, v1=$v1, a0=$a0, a1=$a1, b0=$b0, b1=$b1) — this is precisely the value fill_mumford_block! writes into the x-term Mumford row (A_mat row K+2) for this basis column. If this fires on every column of every call, the x-term Mumford row is structurally all-zero, which is the singular-matrix symptom already observed (row 4 = (0,0,0,0), b[4]=0) for K=2."
    end

    return (r0_final, r1_final)
end

# ---------------------------------------------------------------------------
#  init_scratch_caches!(scratch, p_val)
#
#  Populates the per-thread caches that depend on the runtime prime p:
#    • small_inv[1..32]  — fpinv table for denominators s=1..32
#    • oscar_Fp / oscar_Rx — GF(p) and its polynomial ring for deg≥3 root-finding
#
#  Call this once per ThreadScratchpad after p is known, before spawning walkers.
# ---------------------------------------------------------------------------
function init_scratch_caches!(scratch::ThreadScratchpad{K}, p_val::Int,
                               backend::FpArith = StandardArith(p_val)) where K
    # Precomputed modular inverses for small positive integers, stored in
    # `backend`'s representation. build_phi_general! (via monomial_series_coeffs!)
    # combines small_inv[s] with backend-form binomial coefficients using
    # fpmul_b — both operands must be in the SAME representation, so this
    # table has to be built with the same backend the walk will actually run
    # with. Passing a different backend at call time than was used here is a
    # representation-mismatch bug that phi_residual_general!'s remainder
    # check won't reliably catch quickly (see validate_backend note in
    # trial3_fp_backend.jl).
    if SETUP_DIAG_VERBOSE
        @printf("[DIAG init_scratch_caches!] tid=%d K=%d backend=%s p=%d\n",
                Threads.threadid(), K, typeof(backend), backend.p)
        flush(stdout)
    end
    for s in 1:32
        scratch.small_inv[s] = to_repr(backend, fpinv(s))
    end

    # Oscar polynomial ring over GF(p) — built once, reused forever per thread.
    Fp = GF(p_val)
    Rx, _ = polynomial_ring(Fp, :x)
    scratch.oscar_Fp[] = Fp
    scratch.oscar_Rx[] = Rx
    scratch.oscar_ready[1] = true

    # Preallocate the Oscar coefficient buffer (length 8; residual degree is a fixed
    # invariant = 2 regardless of K_MAX, so u_len ≤ 3 — length 8 is generous headroom).
    # We store FqFieldElem objects; they'll be mutated via setindex! in find_roots_and_points_inplace!.
    scratch.oscar_coeff_buf[] = [Fp(0) for _ in 1:8]

    return scratch
end

# ---------------------------------------------------------------------------
#  Branch series: compute y-series coefficients y[0], y[1], ..., y[m-1]
#  where y(px + t) = Σ y[s] * t^s mod t^m,
#  determined by y² = f(px + t)  with y[0] = py.
#
#  Expanding f(px + t) = Σ f_s * t^s (Taylor coefficients of f at px):
#     f_s = f^(s)(px) / s!  — computed directly via synthetic division.
#
#  From y² = f we get: 2*y[0]*y[s] = f_s - Σ_{r=1}^{s-1} y[r]*y[s-r]
#  → y[s] = (f_s - Σ_{r=1}^{s-1} y[r]*y[s-r]) / (2*y[0])
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
#  Mutates `out_y` in-place using pre-allocated workspace buffers.
# ---------------------------------------------------------------------------
function branch_series!(
    out_y   ::AbstractVector{Int},
    px      ::Int,
    py      ::Int,
    m       ::Int,
    f_tay   ::AbstractVector{Int},
    poly_buf::AbstractVector{Int},
    backend ::FpArith = StandardArith(p)
)::Nothing

    @assert m ≥ 1

    # -----------------------------
    # m = 1 trivial branch value
    # -----------------------------
    if m == 1
        @inbounds out_y[1] = py
        return nothing
    end

    # -----------------------------
    # We assume F(x,y)=0 is encoded
    # via Taylor coefficients:
    # f_tay[k] = ∂^k_x F(x, y(x)) at px
    # -----------------------------

    @inbounds out_y[1] = py

    # Precompute partial derivatives of F w.r.t y at base point
    # We assume caller ensures f_tay includes mixed contributions;
    # but we explicitly reconstruct Fy via first variation structure.

    # NOTE: for hyperelliptic model, Fy = 2y
    Fy = fpmul_b(backend, to_repr(backend, 2), py)
    Fy_inv = fpinv_b(backend, Fy)

    # ----------------------------------------------------
    # First derivative from implicit function theorem:
    #
    # F_x + F_y y' = 0
    # y' = -F_x / F_y
    # ----------------------------------------------------
    @inbounds begin
        rhs = f_tay[2]
        neg_rhs = fpsub_b(backend, to_repr(backend, 0), rhs)
        out_y[2] = fpmul_b(backend, neg_rhs, Fy_inv)
    end

    # ----------------------------------------------------
    # Higher derivatives: recursive implicit differentiation
    #
    # F_xx + 2F_xy y' + F_yy (y')^2 + F_y y'' = 0
    # etc.
    #
    # We build using stored jet out_y[1..s]
    # ----------------------------------------------------
    for s in 2:m-1

        rhs = f_tay[s+1]

        # subtract all lower-order contributions
        for k in 1:s-1
            # combinatorial coefficient for jet product
            c = k * (s - k + 1)

            rhs = fp_b(
                backend,
                rhs - fpmul_b(backend,
                              to_repr(backend, c),
                              fpmul_b(backend,
                                      out_y[k+1],
                                      out_y[s-k+1]))
            )
        end

        out_y[s+1] = fpmul_b(backend, rhs, Fy_inv)
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  Monomial series (in-place): write the coefficients of t^0..t^(m-1) in
#  x^i * y^j(x) (evaluated at x = px+t, y = y_ser) into `out`.
#
#  x^i = (px + t)^i = Σ C(i,r) * px^(i-r) * t^r  (binomial expansion)
#  x^i * y^j: convolve the two series mod t^m.
#
#  For j=0: coeff of t^s in (px+t)^i = C(i,s) * px^(i-s)  (or 0 if s>i).
#  For j=1: convolve x-series with y-series.
#
#  `out`, `xi_scratch`, `binom_scratch`, `pxpow_scratch` are all
#  length-m buffers owned by the caller and reused across every monomial
#  and every column — this is the allocation hotspot the original
#  per-call `Vector{Int}` returns were causing (one outer vector + four
#  temporaries per monomial, times n columns, times every anchor group,
#  times every walk step).  Writing in place eliminates all of that.
# ---------------------------------------------------------------------------
function monomial_series_coeffs!(
    out::AbstractVector{Int},
    i::Int,
    j::Int,
    px::Int,
    y_ser::AbstractVector{Int},
    m::Int,
    xi_scratch::AbstractVector{Int},
    binom_scratch::AbstractVector{Int},
    pxpow_table::AbstractVector{Int},
    small_inv::AbstractVector{Int},
    backend::FpArith = StandardArith(p),
)::Nothing

    @assert length(out) >= m
    @assert j == 0 || j == 1 "unexpected monomial x^$i y^$j"
    fill!(out, 0)

    # (px+t)^i
    fill!(xi_scratch, 0)

    maxs = min(i, m - 1)

    # FIX (root cause of the monomial_series_coeffs! constant-coefficient
    # assert under MontgomeryArith): fpmul_b(backend, a, x) for
    # MontgomeryArith computes a*x*R^-1 mod p, the REDC product. This is
    # only the correct field-multiplication result when BOTH a and x are
    # already in backend (Montgomery) representation — one bare R factor
    # from each operand, cancelled by the single R^-1 in REDC. Passing a
    # raw (non-Montgomery) integer as either operand leaves the product off
    # by a factor of R^-1 mod p, silently.
    #
    # binom_scratch[1] was previously seeded with the raw literal `1`, then
    # used as an operand to fpmul_b — under Montgomery arithmetic that is
    # NOT the multiplicative identity (only to_repr(backend, 1) = R mod p
    # is). Must be converted via to_repr, same as every other operand that
    # participates in fpmul_b in this function.
    binom_scratch[1] = to_repr(backend, 1)

    for s in 1:maxs
        binom_scratch[s + 1] =
            fpmul_b(
                backend,
                binom_scratch[s],
                fpmul_b(
                    backend,
                    to_repr(backend, i - s + 1),   # was: raw `i - s + 1` — same
                                                    # bug as binom_scratch[1] above;
                                                    # small_inv[s] is backend-repr
                                                    # (see init_scratch_caches!),
                                                    # so its fpmul_b partner must
                                                    # be backend-repr too.
                    small_inv[s],
                ),
            )
    end


    for s in 0:maxs
        xi_scratch[s + 1] =
            fpmul_b(
                backend,
                binom_scratch[s + 1],
                pxpow_table[i - s + 1],
            )
    end

    if j == 0
        @inbounds copyto!(out, 1, xi_scratch, 1, m)
        return nothing
    end

    @assert j == 1

    @inbounds for a in 0:m-1
        xa = xi_scratch[a + 1]
        xa == 0 && continue

        for b in 0:(m - 1 - a)
            out[a + b + 1] = fpadd_b(
                backend,
                out[a + b + 1],
                fpmul_b(backend, xa, y_ser[b + 1]),
            )
        end
    end

    # Constant coefficient sanity check.
    @assert out[1] ==
        fpmul_b(backend, pxpow_table[i + 1], y_ser[1])

    return nothing
end


@inline function build_xpow_cache!(
    xpow::Vector{Int},
    px::Int,
    maxdeg::Int,
    backend::FpArith
)
    px_b  = to_repr(backend, px)
    one_b = to_repr(backend, 1)

    xpow[1] = one_b

    @assert xpow[1] == one_b

    @inbounds begin
        xpow[2] = px_b
        for i in 2:maxdeg
            xpow[i+1] = fpmul_b(backend, xpow[i], px_b)
        end
    end

    # sanity checks
    @assert xpow[2] == px_b
    @assert xpow[3] == fpmul_b(backend, px_b, px_b)
end

# ---------------------------------------------------------------------------
#  fill_f_tay!(f_tay, px, backend) — populate the F_x(px) entry branch_series!
#  needs for its m=2 (single-tangency) path.
#
#  For the hyperelliptic model F(x,y) = y^2 - f(x), the pure-x partial
#  derivative is F_x(x,y) = -f'(x) — independent of y, since f(x) contributes
#  no y-dependence and the y^2 term contributes nothing to an x-derivative.
#  branch_series! only reads f_tay[2] on the m==2 path (the `for s in 2:m-1`
#  higher-jet loop is empty when m==2), so only the first derivative is
#  needed here; a future m>=3 (higher-tangency) caller would need this
#  extended to f_tay[3..] = -f''(px), -f'''(px), etc.
#
#  f'(x) is evaluated via the standard derivative-coefficient rule on
#  F_POLY_DESC (descending powers: F_POLY_DESC[1] is the coefficient of the
#  highest-degree term, matching init_phi_general_caches!'s construction),
#  using Horner's method entirely in backend representation so this composes
#  correctly with the Montgomery-vs-Standard backend already threaded
#  through every other hot-path function in this file.
# ---------------------------------------------------------------------------
@inline function fill_f_tay!(
    f_tay::AbstractVector{Int},
    px::Int,
    backend::FpArith
)
    @assert length(f_tay) >= 2 "fill_f_tay!: f_tay buffer (length $(length(f_tay))) too small to hold f_tay[2] (F_x(px))"
    @assert !isempty(F_POLY_DESC) "fill_f_tay!: F_POLY_DESC is empty — init_phi_general_caches! must run before any m>1 (tangency) branch_series! call"

    # CONTRACT: px arrives ALREADY in backend representation. Every call
    # site (compute_branch_series! <- build_phi_general!'s anchor loop)
    # passes anchors_b[a][1], which was converted via to_repr once, up
    # front, at anchors_b construction time (see build_phi_general!,
    # "Convert inputs once (no repeated conversions later)"). Do NOT
    # call to_repr(backend, px) here — under StandardArith that's a
    # harmless no-op (to_repr = identity), but under MontgomeryArith
    # to_repr is NOT idempotent (to_repr(x) = x*R mod p), so re-applying
    # it produces x*R^2 mod p instead of x*R mod p: a silently-wrong
    # value that only manifests with the Montgomery backend. This is the
    # same double-conversion hazard already called out at
    # build_xpow_cache!'s call site above — fill_f_tay! just didn't get
    # the same fix.
    px_b = px
    deg  = length(F_POLY_DESC) - 1   # F_POLY_DESC has deg+1 coefficients, descending

    # Derivative coefficients (descending): d/dx of c_k * x^k is k*c_k*x^(k-1).
    # Horner-evaluate sum_{k=1}^{deg} k*c_k*px^(k-1) directly, without
    # materializing a separate derivative-coefficient array — same
    # zero-allocation discipline as the rest of the hot path.
    acc = to_repr(backend, 0)
    @inbounds for idx in 1:deg   # idx corresponds to F_POLY_DESC[idx], power = deg-idx+1
        power = deg - idx + 1
        power == 0 && break     # constant term has zero derivative; nothing left to add
        coeff_k = fpmul_b(backend, to_repr(backend, power), F_POLY_DESC[idx])
        acc = fpadd_b(backend, fpmul_b(backend, acc, px_b), coeff_k)
    end

    # F_x(px) = -f'(px)
    @inbounds f_tay[2] = fpsub_b(backend, to_repr(backend, 0), acc)

    return nothing
end

@inline function compute_branch_series!(
    out_y,
    px, py,
    m,
    scratch,
    backend
)
    m >= 2 && fill_f_tay!(scratch.f_tay, px, backend)
    branch_series!(out_y, px, py, m, scratch.f_tay, scratch.poly_buf, backend)

    # key invariant: constant term must match backend evaluation
    y0 = from_repr(backend, out_y[1])
    py_raw = from_repr(backend, py)
    @assert y0 == py_raw "compute_branch_series!: out_y[1]=$y0 != anchor py=$py_raw — branch series constant term must equal the anchor's own y-coordinate"

    # DEFENSIVE ASSERT (tangency correctness): independently verify the
    # implicit-differentiation identity 2*py*y' == f'(px) directly against
    # a FRESH, standalone evaluation of f'(px) — computed here via its own
    # Horner pass over F_POLY_DESC, deliberately NOT by calling
    # fill_f_tay! again or reusing scratch.f_tay. The point is to catch a
    # sign/indexing bug in fill_f_tay! or in branch_series!'s use of it
    # (e.g. f_tay populated with the wrong sign, or branch_series!
    # combining it with Fy_inv incorrectly) at the exact place it would
    # first manifest, rather than three call-frames later as an opaque
    # "phi_val == 0" failure in step_phi_k! that gives no hint about
    # WHICH of the many moving pieces (f_tay's sign, Fy's sign, the
    # column-fill for x^i's derivative coefficient, the RHS derivative
    # row) is actually wrong.
    if m >= 2
        px_raw = from_repr(backend, px)
        deg = length(F_POLY_DESC) - 1
        fprime_acc = to_repr(backend, 0)
        @inbounds for idx in 1:deg
            power = deg - idx + 1
            power == 0 && break
            coeff_k = fpmul_b(backend, to_repr(backend, power), F_POLY_DESC[idx])
            fprime_acc = fpadd_b(backend, fpmul_b(backend, fprime_acc, px), coeff_k)
        end
        lhs = fpmul_b(backend, fpmul_b(backend, to_repr(backend, 2), py), out_y[2])
        @assert lhs == fprime_acc "compute_branch_series!: tangent-slope identity 2*py*y' == f'(px) FAILED at px=$px_raw py=$py_raw — got 2*py*y'=$(from_repr(backend,lhs)), f'(px)=$(from_repr(backend,fprime_acc)) (backend repr: lhs=$lhs rhs=$fprime_acc, out_y[2]=$(out_y[2]), f_tay[2]=$(scratch.f_tay[2])). This means fill_f_tay!'s sign/value or branch_series!'s use of f_tay[2] is wrong, NOT a downstream row/column bookkeeping bug — check those two before anything else."
    end
end

@inline function _check_basis_cache_consistency!(
    basis,
    pxpow_buf
)
    max_i = 0
    @inbounds for (i, _) in basis
        if i > max_i
            max_i = i
        end
    end

    @assert length(pxpow_buf) >= max_i + 1
end

@inline function _monomial_column!(
    ser_buf,
    scratch,
    i::Int,
    j::Int,
    px::Int,
    out_y,
    m::Int,
    backend
)
    @assert j == 0 || j == 1
    @assert m == 1 || m == 2 "_monomial_column!: m=$m unsupported — only m=1 (plain evaluation) and m=2 (single tangency, requires f_tay[2]=F_x(px) to be populated) are implemented; higher-order tangency (m>=3) needs fill_f_tay! extended to f_tay[3..] and branch_series!'s F_yy cross-term handled explicitly"

    monomial_series_coeffs!(
        ser_buf,
        i, j,
        px,
        out_y,
        m,
        scratch.xi_buf,
        scratch.binom_buf,
        scratch.pxpow_buf,
        scratch.small_inv,
        backend
    )

    return nothing
end

@inline function _write_column!(
    A_mat,
    rhs_vec,
    row_idx::Int,
    col::Int,
    ser_buf,
    m::Int
)
    # WILLY-NILLY ASSERT: A_mat is a stack-allocated MMatrix{N,N,Int} — an
    # @inbounds write past N here is not a bounds error, it's memory
    # corruption / segfault territory. Check before the @inbounds loop.
    @assert row_idx + m - 1 <= size(A_mat, 1) "_write_column!: row_idx=$row_idx m=$m would write row $(row_idx+m-1) past A_mat's $(size(A_mat,1)) rows"
    @assert col >= 1 && col <= size(A_mat, 2) "_write_column!: col=$col out of range 1:$(size(A_mat,2))"
    @assert length(ser_buf) >= m

    # ACTUAL FIX: this previously wrote to A_mat[row_idx + s + 1, col],
    # i.e. row_idx+1 for the (m=1)-only case this file actually uses. The
    # caller's contract (see build_phi_general!'s anchor loop: row_idx
    # starts at 1 for the FIRST anchor, and is advanced by exactly `m`
    # per anchor so it lands on K+1 for the Mumford block) is unambiguous:
    # the write for a given anchor belongs at row_idx itself, not
    # row_idx+1. The extra +1 silently skipped row_idx entirely for every
    # single anchor — for K=2 this left row 1 (anchor #1's equation)
    # completely unwritten (all-zero, matrix AND rhs, since fill_rhs! had
    # the identical off-by-one — see below), while anchor #1's real values
    # landed one row down, in what should have been anchor #2's row.
    # Anchor K's write similarly landed in row K+1 — the Mumford block's
    # first row — and was then silently clobbered by fill_mumford_block!,
    # which correctly writes to row_idx (no +1). Net effect for K=2:
    # anchor #1 lost entirely (row 1 all-zero), anchor #2's equation
    # placed in row 2, and anchor #2's write ALSO landed in row 3
    # (K+1=3), immediately overwritten by the Mumford block — so only ONE
    # real anchor constraint (anchor #2, relocated to row 2) ever made it
    # into the system, alongside 2 valid Mumford rows and 1 dangling
    # all-zero row. A 4-unknown system with only 3 independent equations
    # (1 anchor + 2 Mumford) is singular by construction — not a rare
    # "special position" coincidence, and not a rank issue with the
    # Mumford block or the RR dimension: exactly the ~100% failure rate
    # observed in the field trace, and exactly consistent with the raw
    # (pre-elimination) snapshot fp_gauss! now captures (row 1 = all
    # zero including its own RHS entry).
    #
    # For K=1 this bug was invisible: the single anchor's row_idx=1 write
    # landed at row 2 = K+1 = the Mumford block's row0, which
    # fill_mumford_block! then immediately overwrote with the CORRECT
    # Mumford row0 values anyway — so the off-by-one's only symptom for
    # K=1 was silently discarding the (only) anchor's equation and
    # ending up with a 3x3 system built from 0 anchor rows + 2 Mumford
    # rows... which is only 2 independent equations for 3 unknowns, i.e.
    # should ALSO have been singular. That it apparently wasn't (K=1 ran
    # successfully before this fix) needs re-checking once this lands —
    # it's possible build_phi_mumford's closed-form path (trial3_phi.jl)
    # was actually what ran for K=1's hot path rather than this general
    # code, in which case this bug may have been entirely latent until
    # K=2 was reached for the first time.
    @inbounds for s in 0:(m-1)
        A_mat[row_idx + s, col] = ser_buf[s + 1]
    end
end

@inline function fill_monomial_block!(
    A_mat,
    rhs_vec,
    row_idx::Int,
    basis,
    y_idx::Int,
    px,
    out_y,
    m::Int,
    scratch,
    backend
)

    n = length(basis)   # n == nb == N2 + 1 (N2 unknowns + 1 normalised element)

    _check_basis_cache_consistency!(basis, scratch.pxpow_buf)

    @assert m == 1 || m == 2 "fill_monomial_block!: m=$m unsupported — only m=1 (plain evaluation) and m=2 (single tangency) are implemented"
    @assert length(out_y) >= m + 1

    # DEFENSIVE ASSERT: y_idx must be a real, in-range basis index, and it
    # must actually point at the y-monomial (0,1) — this is the ONLY
    # element this function is allowed to skip when mapping basis indices
    # to A_mat columns. Checking `basis[y_idx] == (0,1)` here (not just
    # `1 <= y_idx <= n`) means a caller that passes a stale/wrong y_idx
    # (e.g. computed against a differently-ordered basis, or against the
    # wrong nb) gets caught at the point of use instead of silently
    # normalizing/skipping the wrong monomial — which is exactly the class
    # of bug (basis[end] assumed to be y when it wasn't) that caused the
    # original K=2 failure.
    @assert 1 <= y_idx <= n "fill_monomial_block!: y_idx=$y_idx out of range 1:$n"
    @assert basis[y_idx] == (0, 1) "fill_monomial_block!: basis[y_idx=$y_idx]=$(basis[y_idx]) is not the y-monomial (0,1) — caller passed the wrong normalization index for this basis ($basis)"

    # ACTUAL FIX: A_mat has N2 = K+2 = n-1 columns, one per UNKNOWN
    # coefficient — every basis element EXCEPT the y-monomial at y_idx
    # (wherever pole-order sorting actually placed it), not "every basis
    # element except basis[end]". The old code always skipped basis[end],
    # which is only correct when y happens to sort last (true for K=1's
    # nb=4, false for K=2's nb=5 — see rr_basis_cached's hard assert for
    # the full explanation of why basis[end] and "the normalized element"
    # are NOT interchangeable in general).
    #
    # Column assignment: basis indices 1..n except y_idx map, in order, to
    # A_mat columns 1..n_cols. This preserves the previous column order for
    # every index before y_idx, and shifts everything after y_idx down by
    # one column — so for the common K=1 case (y_idx==n) this is byte-for-
    # byte identical to the old "col in 1:n_cols, basis[col]" loop.
    n_cols = n - 1
    @assert n_cols == size(A_mat, 2) "fill_monomial_block!: computed n_cols=$n_cols (basis length $n minus the normalised element) but A_mat has $(size(A_mat,2)) columns"

    col = 0
    for bidx in 1:n
        bidx == y_idx && continue
        col += 1

        i, j = basis[bidx]

        _monomial_column!(
            scratch.ser_buf,
            scratch,
            i, j,
            px,
            out_y,
            m,
            backend
        )

        _write_column!(
            A_mat,
            rhs_vec,
            row_idx,
            col,
            scratch.ser_buf,
            m
        )
    end

    # DEFENSIVE ASSERT: we must have written exactly n_cols columns — i.e.
    # the skip-y_idx loop above visited every OTHER basis index exactly
    # once. This is really just `n - 1 == n_cols`, but stated as a
    # post-loop invariant on `col` (not just an arithmetic identity on `n`)
    # so a future refactor that changes the loop body without updating
    # this check fails loudly instead of leaving a hole in A_mat's columns.
    @assert col == n_cols "fill_monomial_block!: wrote $col columns but expected n_cols=$n_cols — the skip-y_idx=$y_idx loop over 1:$n did not visit exactly n_cols indices"
end


@inline function fill_rhs!(
    rhs_vec,
    row_idx,
    basis,
    i_norm,
    j_norm,
    px,
    out_y,
    m,
    scratch,
    backend
)
    monomial_series_coeffs!(
        scratch.ser_buf,
        i_norm, j_norm,
        px,
        out_y,
        m,
        scratch.xi_buf,
        scratch.binom_buf,
        scratch.pxpow_buf,
        scratch.small_inv,
        backend
    )

    # ACTUAL FIX: matching off-by-one to _write_column!'s — this wrote to
    # rhs_vec[row_idx + s + 1], skipping row_idx itself. See _write_column!
    # for the full analysis; the two bugs combined to leave anchor rows'
    # RHS entries at row_idx+1 instead of row_idx, which is why the
    # all-zero row in the field trace was all-zero in BOTH the matrix AND
    # its own b0 entry (b0[1]=0) — this fix and _write_column!'s must land
    # together, or the matrix and RHS rows disagree about which row is
    # which.
    @assert row_idx + m - 1 <= length(rhs_vec) "fill_rhs!: row_idx=$row_idx m=$m would write past rhs_vec length $(length(rhs_vec))"
    for s in 0:(m-1)
        rhs_vec[row_idx + s] = fpsub_b(backend, 0, scratch.ser_buf[s+1])
    end
end

# ---------------------------------------------------------------------------
#  build_xmodu_cache!(r0_buf, r1_buf, u0, u1, max_i, backend)
#
#  ACTUAL FIX (previously-missing piece): ThreadScratchpad's field comments
#  (section 11) document x_pow_mod_u_r0/r1 as "filled once per step" by
#  build_phi_general! so reduce_monomial_mod_D_cached can do O(1) lookups —
#  but nothing anywhere in this file ever wrote them; every caller was
#  reading zero-initialized (or stale, leftover-from-a-different-(u0,u1))
#  garbage. This function is the actual fill, in the SAME backend
#  representation as the rest of A_mat/rhs_vec (so Mumford rows built from
#  it are numerically consistent with the anchor rows built via fpmul_b).
#
#  r0_buf[i+1], r1_buf[i+1] = (x^i mod u(x)) as a linear poly a0 + a1*x,
#  for i = 0..max_i, using the same two-register recurrence as
#  reduce_xi_mod_u but entirely in backend representation.
# ---------------------------------------------------------------------------
@inline function build_xmodu_cache!(
    r0_buf, r1_buf,
    u0::Int, u1::Int,
    max_i::Int,
    backend::FpArith
)
    @assert max_i >= 0 "build_xmodu_cache!: max_i=$max_i must be >= 0"
    @assert max_i + 1 <= length(r0_buf) "build_xmodu_cache!: max_i+1=$(max_i+1) exceeds r0_buf length $(length(r0_buf))"
    @assert max_i + 1 <= length(r1_buf) "build_xmodu_cache!: max_i+1=$(max_i+1) exceeds r1_buf length $(length(r1_buf))"
    @assert length(r0_buf) == length(r1_buf) "build_xmodu_cache!: r0_buf/r1_buf length mismatch ($(length(r0_buf)) vs $(length(r1_buf)))"

    u0_b = to_repr(backend, u0)
    u1_b = to_repr(backend, u1)
    zero_b = to_repr(backend, 0)
    one_b  = to_repr(backend, 1)

    @inbounds r0_buf[1] = one_b;  r1_buf[1] = zero_b   # x^0 = 1

    max_i == 0 && return nothing

    @inbounds r0_buf[2] = zero_b; r1_buf[2] = one_b    # x^1 = x

    @inbounds for i in 2:max_i
        prev_r0 = r0_buf[i]
        prev_r1 = r1_buf[i]
        # x * (prev_r0 + prev_r1*x) ≡ -prev_r1*u0 + (prev_r0 - prev_r1*u1)*x
        r0_buf[i+1] = fpsub_b(backend, zero_b, fpmul_b(backend, prev_r1, u0_b))
        r1_buf[i+1] = fpsub_b(backend, prev_r0, fpmul_b(backend, prev_r1, u1_b))
        # HARD ASSERT: (r0,r1) representing x^(i) mod u(x) must never both be
        # zero for a monic degree-2 u(x) with u0 != 0 (x^i ≡ 0 mod u(x) with
        # u0 != 0 would force x | u(x)'s inverse chain to degenerate, which
        # can't happen for i < ell — this is a finite field, u(x) has no
        # repeated root at x=0 unless u0==0). This is exactly the failure
        # mode that would make fill_mumford_block! silently write a
        # legitimate-looking-but-actually-zero row into A_mat: if this table
        # entry is (0,0) here, reduce_monomial_mod_D_cached returns (0,0)
        # downstream with NOTHING further catching it, and that zero
        # propagates into a whole Mumford row looking like a real (but
        # trivial) linear constraint instead of the cache-fill bug it is.
        if u0_b != zero_b
            @assert !(r0_buf[i+1] == zero_b && r1_buf[i+1] == zero_b) "build_xmodu_cache!: x^$(i) mod u(x) came out identically (0,0) at table index $(i+1) (u0=$u0, u1=$u1, u0_b=$u0_b, u1_b=$u1_b, prev_r0=$prev_r0, prev_r1=$prev_r1) — this is the exact silent-zero-row failure mode fill_mumford_block! depends on this cache NOT producing. Either the recurrence above has a sign/index bug for this (u0,u1), or u(x) is genuinely degenerate (shares a factor with x) and the caller should have rejected this D before reaching here."
        end
    end

    # HARD ASSERT: verify every index 1:max_i+1 that build_phi_general! is
    # about to hand to reduce_monomial_mod_D_cached was ACTUALLY written by
    # the loop above, not left at whatever garbage/zero the scratch buffer
    # held from a previous call at a different (u0,u1). A stale/uninitialized
    # tail here is indistinguishable from a genuine (0,0) reduction unless
    # checked explicitly against a sentinel BEFORE the loop runs — since we
    # don't have a pre-loop sentinel poke available without touching the
    # ThreadScratchpad struct (defined in a file not available here), this
    # at least confirms internal self-consistency: index 1 and (if max_i>=1)
    # index 2 must hold the fixed algebraic identities checked below, and
    # every subsequent index up to max_i+1 must have been actually assigned
    # in the loop above (Julia semantics guarantee this for a completed
    # `for i in 2:max_i` loop with max_i>=1, but if max_i==0 the loop body
    # above never executed at all — assert that case is handled correctly
    # by the early return, not silently falling through with r0_buf[2:]
    # unset yet still read by a caller that assumed max_i was larger).
    @assert max_i + 1 <= length(r0_buf) "build_xmodu_cache!: post-loop check — max_i+1=$(max_i+1) exceeds r0_buf length $(length(r0_buf)) (should have been caught by the pre-loop assert; if this fires instead, max_i changed mid-function, which should be impossible for a local variable)."

    # sanity: x^0 and x^1 rows must be exactly the algebraic identities above
    @assert r0_buf[1] == one_b && r1_buf[1] == zero_b
    max_i >= 1 && @assert r0_buf[2] == zero_b && r1_buf[2] == one_b

    return nothing
end

# ---------------------------------------------------------------------------
#  fill_mumford_block!(scratch, A_mat, rhs_vec, row_idx, basis, y_idx, n_cols,
#                       v0_b, v1_b, backend) -> nothing
#
#  ACTUAL FIX: writes the 2 Mumford rows — φ(x, v(x)) ≡ 0 mod u(x) split
#  into its constant-term and x-term equations — that build_phi_general!'s
#  docstring, N2=K+2 sizing, and x_pow_mod_u_r0/r1 caching comments all
#  document as part of this construction, but which no code in this file
#  ever actually wrote. Without these two rows the (K+2)x(K+2) system had
#  its last 2 rows silently all-zero, which fp_gauss! does correctly detect
#  as singular (returns false) — so the practical effect of the missing
#  rows was "build_phi_general! never succeeds for K>=1 whenever it reaches
#  this point", not a crash by itself; the crash upstream was the separate
#  off-by-one column bug in fill_monomial_block!.
#
#  y_idx is the basis index of the y-monomial (0,1) — the element whose
#  coefficient is normalised to 1 (fixed by the reference convention in
#  trial3_phi.jl: φ=a·x²+b·x+c+d·y, d=1 always), NOT necessarily basis[end].
#  Column assignment walks basis indices 1..length(basis) IN ORDER, SKIPPING
#  y_idx, and maps the remaining n_cols indices onto A_mat columns 1..n_cols
#  in that same order — this must exactly match fill_monomial_block!'s
#  column assignment or the two blocks disagree about which coefficient
#  lives in which column.
#
#  For each unknown column (basis index bidx != y_idx, mapped to column j):
#    (r0_j, r1_j) = basis[bidx]-monomial evaluated at (x, v(x)) mod u(x)
#    A_mat[K+1, j] = r0_j        A_mat[K+2, j] = r1_j
#  RHS (from the normalised basis[y_idx] element, coefficient fixed = 1):
#    rhs_vec[K+1] = -r0_norm     rhs_vec[K+2] = -r1_norm
# ---------------------------------------------------------------------------
@inline function fill_mumford_block!(
    scratch,
    A_mat,
    rhs_vec,
    row_idx::Int,
    basis,
    y_idx::Int,
    n_cols::Int,
    v0_b::Int,
    v1_b::Int,
    backend::FpArith
)
    @assert row_idx + 1 <= size(A_mat, 1) "fill_mumford_block!: row_idx=$row_idx needs 2 rows (row_idx, row_idx+1), A_mat only has $(size(A_mat,1)) rows"
    @assert n_cols == size(A_mat, 2) "fill_mumford_block!: n_cols=$n_cols != A_mat column count $(size(A_mat,2))"
    @assert length(basis) == n_cols + 1 "fill_mumford_block!: expected basis to hold n_cols unknowns + 1 normalised element ($(n_cols+1) total), got length(basis)=$(length(basis))"
    @assert row_idx + 1 <= length(rhs_vec) "fill_mumford_block!: row_idx=$row_idx needs 2 rhs_vec slots, only have $(length(rhs_vec))"

    # DEFENSIVE ASSERT: same y_idx validity check as fill_monomial_block! —
    # this function must skip the SAME basis index that fill_monomial_block!
    # skipped, or the two blocks' columns silently disagree about which
    # coefficient lives in which A_mat column (a corruption that would not
    # throw anywhere — it would just solve the wrong linear system and hand
    # back plausible-looking garbage coefficients).
    n = length(basis)
    @assert 1 <= y_idx <= n "fill_mumford_block!: y_idx=$y_idx out of range 1:$n"
    @assert basis[y_idx] == (0, 1) "fill_mumford_block!: basis[y_idx=$y_idx]=$(basis[y_idx]) is not the y-monomial (0,1) — caller passed the wrong normalization index for this basis ($basis)"

    row0 = row_idx        # constant-term equation
    row1 = row_idx + 1     # x-term equation

    row0_all_zero = true
    row1_all_zero = true
    col = 0
    @inbounds for bidx in 1:n
        bidx == y_idx && continue
        col += 1
        i, j = basis[bidx]
        r0, r1 = reduce_monomial_mod_D_cached(i, j, v0_b, v1_b, scratch, backend)
        @assert r0 isa Int && r1 isa Int
        A_mat[row0, col] = r0
        A_mat[row1, col] = r1
        r0 != 0 && (row0_all_zero = false)
        r1 != 0 && (row1_all_zero = false)
    end
    # DEFENSIVE ASSERT: mirror of fill_monomial_block!'s post-loop column
    # count check — both functions must agree on n_cols via the same
    # skip-y_idx traversal, or A_mat ends up with a column silently unwritten
    # by one block and double-written by the other.
    @assert col == n_cols "fill_mumford_block!: wrote $col columns but expected n_cols=$n_cols — the skip-y_idx=$y_idx loop over 1:$n did not visit exactly n_cols indices"

    norm_i, norm_j = basis[y_idx]
    r0n, r1n = reduce_monomial_mod_D_cached(norm_i, norm_j, v0_b, v1_b, scratch, backend)
    @inbounds rhs_vec[row0] = fpsub_b(backend, 0, r0n)
    @inbounds rhs_vec[row1] = fpsub_b(backend, 0, r1n)

    # HARD ASSERT, at the write site: this is the earliest point in the
    # call chain that has visibility into "did this Mumford row come out
    # entirely zero across ALL n_cols columns" — exactly the field-observed
    # failure (row 4 = (0,0,0,0), b[4]=0, for K=2). Every individual (r0,r1)
    # pair is already asserted non-degenerate by reduce_monomial_mod_D_cached
    # above; this catches the case where each individual pair passes (isn't
    # itself a NaN-like (0,0) coincidence) but the row STILL ends up zero
    # because, e.g., r1 is zero for every basis column specifically (as
    # opposed to both r0,r1 being zero together) — a narrower, column-wide
    # cancellation that the per-call assert above can't see since it only
    # checks (r0,r1) jointly, not r1 in isolation across the whole column
    # range. rhs_vec[row1]==0 is also checked: if BOTH the row and its own
    # RHS are zero, that's exactly the observed field trace's row 4.
    if row1_all_zero && rhs_vec[row1] == 0
        @assert false "fill_mumford_block!: x-term Mumford row (row=$row1) came out ALL-ZERO across all $n_cols columns AND rhs_vec[$row1]=0 — this is the exact structural failure fp_gauss! reported (an entire row of zeros, including its own RHS entry, is unconditionally singular, not a rare special-position coincidence). v0_b=$v0_b, v1_b=$v1_b. This means reduce_monomial_mod_D_cached's j==1 branch returned r1==0 for EVERY basis column 1:$n_cols. Check whether v1_b==0 (this step's divisor D_cur has v1==0, degenerating the x-term equation to nothing) or whether x_pow_mod_u_r1's cache values are structurally zero for this u(x)."
    end
    if row0_all_zero && rhs_vec[row0] == 0
        @assert false "fill_mumford_block!: constant-term Mumford row (row=$row0) came out ALL-ZERO across all $n_cols columns AND rhs_vec[$row0]=0 — same structural-singularity concern as the row1 case above, for the constant-term equation instead. v0_b=$v0_b, v1_b=$v1_b."
    end

    return nothing
end

function build_phi_general!(
    scratch,
    anchors,
    u0,
    u1,
    v0,
    v1;
    backend=StandardArith(p)
)::Bool

    # TIMING INSTRUMENTATION (series phase start): the PhiTimingStats
    # struct/report machinery above has existed for a while but ns_series/
    # ns_gauss/ns_residual were never actually written anywhere in this
    # file -- only read back out in print_phi_timing_report, which is why
    # --phi-timing has always printed "no samples" regardless of whether
    # PHI_TIMING_ENABLED[] was set (n_calls WAS being bumped in
    # step_phi_k!, but nothing ever timed anything). Wiring it in here:
    # "series" covers everything from function entry through the Mumford-
    # block fill (basis lookup, anchor loop / branch_series! calls,
    # monomial column fills, RHS fill) -- i.e. all setup work BEFORE the
    # linear solve. Gated on PHI_TIMING_ENABLED[] exactly like n_calls, so
    # normal (disabled) runs pay one Bool check and skip the time_ns()
    # call entirely, per this file's original zero-alloc/opt-in design.
    _pt_series_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    K  = length(anchors)
    nb = K + 3

    basis = rr_basis_cached(nb)

    # ============================================================
    # 1. Validate structure assumptions
    # ============================================================

    @assert K > 0
    @assert K <= K_MAX "build_phi_general!: K=$K exceeds K_MAX=$K_MAX — scratch's static buffers were sized for K_MAX and will not have room for this many anchors"
    @assert length(anchors) == K "build_phi_general!: length(anchors)=$(length(anchors)) != K=$K"
    @assert length(basis) == nb
    @assert length(scratch.coeffs_out) == K + 3 "build_phi_general!: scratch.coeffs_out length $(length(scratch.coeffs_out)) != K+3=$(K+3) — scratch was built for a different K"
    @assert length(scratch.seen_counts) == K
    @assert length(scratch.visited_flags) == K

    # basis sanity: all exponents are small and non-negative
    @inbounds for i in 1:nb
        px, py = basis[i]
        @assert px >= 0
        @assert py >= 0
    end

    # ============================================================
    # 1b. Locate the y-monomial normalization index.
    # ============================================================
    #
    # ACTUAL FIX (root cause of the K=2 "column 4 structurally singular"
    # failure): the normalization convention fixed by the reference
    # implementation (build_phi_mumford in trial3_phi.jl: φ = a·x²+b·x+c+d·y
    # with d=1 ALWAYS) is "the y-monomial's coefficient is 1" — a statement
    # about WHICH MONOMIAL, not about WHICH BASIS POSITION. rr_basis orders
    # by pole order, and only for nb=4 (K=1) does that ordering happen to
    # put y last; for nb=5 (K=2) it puts x³ last instead, and y sorts to
    # index nb-1. This function finds y explicitly and uses its real index
    # everywhere a "normalization index" is needed, instead of assuming
    # it's basis[end]/basis[nb].
    #
    # y_idx == nb is NOT expected to hold in general — do not assert it.
    # rr_basis_cached only guarantees "a y-monomial exists somewhere in the
    # basis" (see its own assert), not "it's last"; that guarantee was
    # deliberately weakened once fill_monomial_block!/fill_mumford_block!/
    # the coeffs_out write-back were fixed to use y_idx directly rather
    # than basis[end]. y_idx varying with nb (4→y_idx=4, 5→y_idx=4, 6→? )
    # is the CORRECT, now-fully-supported behavior, not a warning sign.
    y_idx = findfirst(bi -> bi == (0, 1), basis)
    @assert y_idx !== nothing "build_phi_general!: K=$K, nb=$nb — RR basis contains no y-monomial (0,1) at all: basis=$basis. The reference φ construction always includes a y-term (d=1 fixed); a basis without one means rr_basis's pole-order enumeration is broken for this nb."
    @assert 1 <= y_idx <= nb "build_phi_general!: y_idx=$y_idx out of range 1:$nb (basis length $(length(basis)))"
    # DEFENSIVE ASSERT: y must appear EXACTLY once. findfirst only checks
    # existence-and-first-position; if rr_basis's enumeration ever produced
    # a duplicate (0,1) entry (e.g. a future edit to the candidate-stream
    # construction introducing an off-by-one that double-counts i=0,j=1),
    # findfirst would silently return the first occurrence and every
    # column-mapping loop below would then have a genuine second (0,1)
    # column masquerading as an ordinary solved-for unknown — a subtle
    # dimension-counting bug that wouldn't necessarily make fp_gauss! fail
    # (two identical-looking (0,1) rows/columns can still be technically
    # distinct columns in the matrix) but WOULD make the solved φ wrong.
    @assert count(bi -> bi == (0, 1), basis) == 1 "build_phi_general!: K=$K, nb=$nb — basis contains $(count(bi -> bi == (0,1), basis)) copies of the y-monomial (0,1), expected exactly 1: basis=$basis. rr_basis's candidate enumeration is producing a duplicate; findfirst above silently picked the first one, which would corrupt the column-index mapping used by fill_monomial_block!/fill_mumford_block!/coeffs_out."

    # ============================================================
    # 2. Convert inputs once (no repeated conversions later)
    # ============================================================

    u0_b = to_repr(backend, u0)
    u1_b = to_repr(backend, u1)
    v0_b = to_repr(backend, v0)
    v1_b = to_repr(backend, v1)

    anchors_b = ntuple(i -> (
        to_repr(backend, anchors[i][1]),
        to_repr(backend, anchors[i][2])
    ), Val(K))

    # ============================================================
    # 3. Determine max x-exponent needed from the basis (this is a
    #    property of the RR basis only — independent of any anchor).
    # ============================================================
    #
    # BUGFIX (root cause of the monomial_series_coeffs! constant-coefficient
    # assert firing under general-k phi runs):
    # this block previously ALSO called build_xpow_cache!(scratch.pxpow_buf,
    # 1, max_basis_i, backend) right here, i.e. ONCE, before the anchor loop,
    # using the literal x-coordinate `1` instead of the anchor's real px.
    # The loop variable here is named `px` too (it's actually the x-EXPONENT
    # field of basis[i], not an x-coordinate — unfortunate naming collision
    # with the anchor px below), which is almost certainly how a hardcoded
    # `1` ended up passed as the cache's base. Because pxpow_buf was filled
    # with powers of 1 (every entry ≡ 1), every xi_scratch[s+1] computed
    # downstream collapsed to just binom_scratch[s+1] — i.e.
    # fpmul_b(backend, binom_scratch[s+1], pxpow_table[i-s+1]) silently used
    # pxpow_table[i-s+1] ≡ 1 regardless of the anchor's actual x-coordinate.
    # This is wrong for every anchor with px != 1. The self-referential
    # sanity assert (out[1] == fpmul_b(pxpow_table[i+1], y_ser[1])) can't
    # catch it — both sides read the same corrupted table — it only shows up
    # as a downstream inconsistency (singular/garbage linear system).
    #
    # The cache must be keyed on the CURRENT anchor's real px and rebuilt
    # every time px changes — i.e. once per anchor, inside the loop below,
    # not once per build_phi_general! call.

    max_basis_i = 0
    @inbounds for i in 1:nb
        exp_i, _ = basis[i]
        if exp_i > max_basis_i
            max_basis_i = exp_i
        end
    end

    @assert max_basis_i >= 0

    # ACTUAL FIX: populate the x_pow_mod_u_r0/r1 cache that
    # reduce_monomial_mod_D_cached depends on (used both by
    # fill_mumford_block! below and by step_phi_k!'s secondary consistency
    # check). This only depends on u0/u1, which are constant for the whole
    # call — unlike pxpow_buf, which is rebuilt per-anchor — so one fill
    # here suffices. Needs entries up to exponent max_basis_i+1: the j==1
    # branch of reduce_monomial_mod_D_cached looks up index i+2, i.e.
    # exponent i+1, for the largest i in the basis (max_basis_i).
    build_xmodu_cache!(
        scratch.x_pow_mod_u_r0, scratch.x_pow_mod_u_r1,
        u0, u1, max_basis_i + 1, backend
    )
    @assert max_basis_i + 2 <= length(scratch.x_pow_mod_u_r0) "build_phi_general!: x_pow_mod_u cache filled up to exponent $(max_basis_i+1) (index $(max_basis_i+2)) but reduce_monomial_mod_D_cached's j=1 branch will need that index"

    # ============================================================
    # 4. Reset linear system
    # ============================================================

    fill!(scratch.A_mat, 0)
    fill!(scratch.rhs_vec, 0)

    row_idx = 1
    total_rows = 0

    # ============================================================
    # 5. Main anchor loop
    # ============================================================

    for a in 1:K

        px, py = anchors_b[a]

        # UPSTREAM INVARIANT (catch double/missing to_repr at the source,
        # not 3 frames down in fill_f_tay!): px, py here MUST be
        # backend-repr values, i.e. exactly to_repr(backend, <raw coord>)
        # as constructed in anchors_b above — never the raw anchor coords
        # and never re-converted. Verify by round-tripping: converting a
        # backend-repr value's raw form back to repr must reproduce it
        # exactly. This is a no-op check under StandardArith (to_repr =
        # from_repr = identity, so it can't catch anything there — the
        # earlier build_xpow_cache! comment block explains why this bug
        # class is Montgomery-only), but under MontgomeryArith it directly
        # catches: (a) a caller passing raw coords straight through
        # (px would then be mistaken for R-form and mis-decoded), and
        # (b) a caller double-applying to_repr before reaching here
        # (the same failure mode fill_f_tay! had).
        @assert to_repr(backend, from_repr(backend, px)) == px "build_phi_general!: anchor $a's px=$px failed the backend-repr round-trip check — this means px is NOT in the backend representation anchors_b is supposed to produce (either a raw coordinate leaked through, or to_repr was applied more than once upstream). Check anchors_b's construction and every call in this loop that receives px before assuming the bug is downstream in fill_f_tay!/compute_branch_series!."
        @assert to_repr(backend, from_repr(backend, py)) == py "build_phi_general!: anchor $a's py=$py failed the backend-repr round-trip check — same double/missing to_repr hazard as px above, check anchors_b's construction first."

        # ------------------------------------------------------------
        # TANGENCY DETECTION: if this anchor's (raw, un-converted) point
        # already occurred earlier in the tuple, this occurrence does NOT
        # get its own row. Its constraint was already absorbed into the
        # earlier occurrence's row via a bumped `m` (see below) — that's
        # what "vanishing order 2 at P" means: one evaluation row (t^0
        # coefficient) plus one derivative row (t^1 coefficient), not two
        # separate evaluation rows at the same point (which is exactly
        # the guaranteed-singular duplicate-row bug this replaces).
        #
        # This must run BEFORE anything below computes/writes a row for
        # anchor `a`, and must key off `anchors` (raw coordinates), not
        # `anchors_b` (backend-repr) — repr equality and raw equality
        # agree for both StandardArith (to_repr is identity) and
        # MontgomeryArith (to_repr is injective), so either would work,
        # but `anchors` avoids relying on that injectivity assumption.
        is_repeat_of_earlier = false
        @inbounds for prev in 1:a-1
            if anchors[prev] == anchors[a]
                is_repeat_of_earlier = true
                break
            end
        end

        if is_repeat_of_earlier
            # Row-budget bookkeeping only: no row written for this anchor.
            continue
        end

        # How many times does THIS anchor's point occur at or after
        # position a? (i.e. this occurrence plus any later repeats it
        # will absorb.) Only 1 or 2 is supported — see fill_f_tay!'s
        # docstring for what m>=3 (triple-or-higher tangency) would need.
        occ_count = 0
        @inbounds for later in a:K
            anchors[later] == anchors[a] && (occ_count += 1)
        end
        @assert occ_count == 1 || occ_count == 2 "build_phi_general!: anchor $(anchors[a]) occurs $occ_count times in this $K-tuple — only single points (m=1) and simple tangency (m=2, occurring exactly twice) are implemented. A point repeated 3+ times needs fill_f_tay! extended to f_tay[3..] and is not yet supported; _anchor_tuple_valid upstream should not be constructing tuples like this."

        m = occ_count

        # --- sub-timer: setup (x-power cache rebuild for this anchor) ---
        _pt_ser_setup_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        # Rebuild the x-power cache for THIS anchor's x-coordinate.
        # (Must happen before fill_monomial_block!/fill_rhs! below, both of
        # which read scratch.pxpow_buf via monomial_series_coeffs!.)
        #
        # IMPORTANT: build_xpow_cache! calls to_repr(backend, px) internally
        # — it expects a RAW (pre-conversion) integer, not a backend-repr
        # value. `px` here is anchors_b[a][1], which was already converted
        # via to_repr at the top of this function (anchors_b construction).
        # Passing that through build_xpow_cache! would double-apply to_repr,
        # which is a no-op for StandardArith but corrupts the value under
        # MontgomeryArith (to_repr is not idempotent there). Use the raw,
        # un-converted anchor coordinate instead.
        build_xpow_cache!(scratch.pxpow_buf, anchors[a][1], max_basis_i, backend)

        # invariant: cache size must match expectation
        @assert length(scratch.pxpow_buf) >= max_basis_i + 1

        @assert px != 0
        @assert py != 0  # hyperelliptic / branch validity assumption

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_setup += time_ns() - _pt_ser_setup_t0
        end

        # --- sub-timer: branch_series (compute_branch_series! only) ---
        _pt_ser_branch_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        # --- compute local branch expansion ---
        compute_branch_series!(
            scratch.out_y,
            px,
            py,
            m,
            scratch,
            backend
        )

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_branch += time_ns() - _pt_ser_branch_t0
        end

        # strict structural invariant: branch series must match expected size
        @assert length(scratch.out_y) >= m + 1

        # ========================================================
        # 5a. Fill matrix block
        # ========================================================

        _pt_ser_cols_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        fill_monomial_block!(
            scratch.A_mat,
            scratch.rhs_vec,
            row_idx,
            basis,
            y_idx,
            px,
            scratch.out_y,
            m,
            scratch,
            backend
        )

        # DEFENSIVE ASSERT (tangency row cross-check): when m==2, independently
        # recompute what the derivative row (row_idx+1) SHOULD contain for
        # every column and compare against what fill_monomial_block! just
        # wrote into A_mat. For a pure-x column (i,0), the t^1 coefficient of
        # (px+t)^i is i*px^(i-1) — a completely independent formula from
        # monomial_series_coeffs!'s binomial-recurrence path, computed here
        # via direct exponentiation, so a bug in the recurrence (wrong
        # small_inv indexing, wrong binom_scratch seed, off-by-one in maxs,
        # etc.) is caught at the exact column it corrupts, rather than
        # surfacing as an opaque whole-row "phi_val == 0" failure two
        # functions later with no indication of WHICH column is wrong.
        # (Columns with j==1, i.e. x^i*y, are skipped here — their t^1
        # coefficient depends on out_y[2] too, which is already
        # independently checked by compute_branch_series!'s tangent-slope
        # assert above; re-deriving the full product rule here would just
        # duplicate that check rather than add new coverage.)
        if m == 2
            col_chk = 0
            @inbounds for bidx in 1:length(basis)
                bidx == y_idx && continue
                col_chk += 1
                (bi, bj) = basis[bidx]
                bj == 1 && continue   # see comment above: skip y-mixed columns here
                bi == 0 && continue   # constant column: derivative is identically 0, trivially consistent
                # pxpow_buf[k+1] = px^k in backend representation (see
                # build_xpow_cache!), so pxpow_buf[bi] = px^(bi-1) already in
                # backend repr — use it directly, don't from_repr/to_repr it.
                expected_deriv_b = fpmul_b(
                    backend,
                    to_repr(backend, bi),
                    scratch.pxpow_buf[bi]
                )
                actual_deriv = scratch.A_mat[row_idx + 1, col_chk]
                @assert expected_deriv_b == actual_deriv "build_phi_general!: tangency derivative-row MISMATCH at anchor px=$(from_repr(backend,px)) column $col_chk (basis[$bidx]=($bi,$bj)) — fill_monomial_block! wrote A_mat[$(row_idx+1),$col_chk]=$actual_deriv but the independently-recomputed derivative i*px^(i-1) gives $expected_deriv_b. This points at monomial_series_coeffs!'s binomial-recurrence path (small_inv/binom_scratch/pxpow_table indexing) for THIS specific column, not at branch_series!/fill_f_tay! (already checked separately) or at row/column bookkeeping (row_idx placement already asserted correct)."
            end
        end

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_cols += time_ns() - _pt_ser_cols_t0
        end

        # ========================================================
        # 5b. Fill RHS
        # ========================================================
        #
        # ACTUAL FIX: pass basis[y_idx] (the y-monomial, wherever it
        # actually lives) instead of basis[end]. For K=1's nb=4 these are
        # the same thing (y_idx==nb==4), so this changes nothing there; for
        # K=2's nb=5, y_idx==4 != nb==5, and this is the actual fix.

        _pt_ser_rhs_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

        fill_rhs!(
            scratch.rhs_vec,
            row_idx,
            basis,
            basis[y_idx][1],
            basis[y_idx][2],
            px,
            scratch.out_y,
            m,
            scratch,
            backend
        )

        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_ser_rhs += time_ns() - _pt_ser_rhs_t0
        end

        # ========================================================
        # 5c. Row bookkeeping (explicit invariant)
        # ========================================================

        row_idx += m
        total_rows += m

        @assert row_idx == total_rows + 1
    end

    # WILLY-NILLY ASSERT: fill_mumford_block! assumes the anchor loop above
    # wrote exactly K rows (rows 1..K) and left row_idx sitting at K+1. If a
    # future change to the anchor loop (e.g. supporting m>1 tangency orders)
    # advances row_idx by something other than 1 per anchor, this fires
    # before silently writing the Mumford rows into the wrong place.
    @assert row_idx == K + 1 "build_phi_general!: expected row_idx==K+1=$(K+1) before Mumford block, got row_idx=$row_idx (total_rows=$total_rows)"
    @assert total_rows == K "build_phi_general!: expected total_rows==K=$K before Mumford block, got $total_rows"

    # ACTUAL FIX: write the 2 Mumford rows (φ(x,v(x)) ≡ 0 mod u(x), split
    # into constant-term / x-term equations) into rows K+1, K+2. row_idx is
    # already sitting at K+1 here (it was advanced by `m=1` per anchor in
    # the loop above), so this lands exactly where it should.
    n_cols = nb - 1   # == K+2 == N2, the unknown columns (basis[y_idx] is normalised, RHS-only)

    _pt_ser_mumford_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    fill_mumford_block!(
        scratch,
        scratch.A_mat,
        scratch.rhs_vec,
        row_idx,
        basis,
        y_idx,
        n_cols,
        v0_b, v1_b,
        backend
    )

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_ser_mumford += time_ns() - _pt_ser_mumford_t0
    end

    row_idx += 2
    total_rows += 2

    # WILLY-NILLY ASSERT: verify the fix actually produced a fully-
    # constrained (K+2)x(K+2) system now, instead of the previous silent
    # 2-all-zero-trailing-rows situation. Kept as a permanent net: if a
    # future refactor breaks fill_mumford_block!'s row bookkeeping again,
    # this fires immediately instead of degrading into "build_phi_general!
    # mysteriously always returns false" or worse.
    @assert total_rows == K + 2 "build_phi_general!: expected K+2=$(K+2) rows written (K anchor rows + 2 Mumford rows) but only wrote $total_rows"
    @assert row_idx == total_rows + 1 "build_phi_general!: row_idx=$row_idx inconsistent with total_rows=$total_rows after Mumford block"
    @assert size(scratch.A_mat, 1) == K + 2
    @assert size(scratch.A_mat, 2) == K + 2
    @assert length(scratch.rhs_vec) == K + 2

    # ============================================================
    # 6. Solve system
    # ============================================================

    if PHI_TIMING_ENABLED[]
        s = phi_timing_stats()
        s.ns_series += time_ns() - _pt_series_t0
    end

    _pt_gauss_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    ok = fp_gauss!(
        scratch.A_mat,
        scratch.rhs_vec,
        scratch.prefix_buf,
        backend
    )

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_gauss += time_ns() - _pt_gauss_t0
    end

    # FIX: fp_gauss! returning false means the linear system was singular —
    # a legitimate, expected outcome for some anchor-tuple/divisor
    # configurations (e.g. anchors in special position), not a correctness
    # bug. Every other degenerate case in this function (anchor in supp(D),
    # etc.) returns false rather than asserting; this one must too, or a
    # single ordinary singular system takes down the entire worker task.
    if !ok
        # NOTE: do NOT also bump n_fail_build_gauss_singular here — fp_gauss!
        # and fp_gauss_batch_invert_diag! now increment that (plus their own
        # finer forward_pivot/diag_d1/diag_di sub-counters) at their actual
        # return-false sites, since only they know WHICH of the three
        # singularity checks fired. Double-incrementing here would silently
        # inflate n_fail_build_gauss_singular past n_fail_build and break the
        # phase2_worker stall-assert's `unaccounted == 0` reconciliation.
        s = phi_timing_stats()
        s.n_fail_build += 1
        return false
    end

    # ------------------------------------------------------------------
    # BUGFIX: scratch.coeffs_out was never populated anywhere in this
    # codebase. fp_gauss! solves the system in place into scratch.rhs_vec
    # (N2 = K+2 entries) and returns only a success Bool — nothing ever
    # copied that solution into coeffs_out (N3 = K+3 entries: the K+2
    # solved coefficients for basis[1..N2], plus 1 normalised entry for
    # basis[end], whose coefficient was fixed to 1 by construction when
    # fill_rhs! moved basis[end]'s monomial to the RHS above).
    #
    # Every downstream reader of coeffs_out — phi_to_EY!, the two
    # "PHI VANISHING CHECK" asserts in step_phi_k!, phi_residual_general!
    # — was therefore always reading all-zero coefficients (coeffs_out's
    # zeros(...) initializer, untouched). Every `coeff == 0 && continue`
    # skip fired on every basis column, every "phi_val == 0" / "r0_acc ==
    # r1_acc == 0" assert trivially passed for the wrong reason (nothing
    # was ever summed), and build_N_inplace!/phi_residual_general! ran on
    # a degenerate all-zero E(x)/Y(x) (deg_E=0, deg_Y=-1) on every K>1
    # call ever made — this pipeline has never actually executed on real
    # data before. That also explains why fixing the earlier Montgomery
    # representation bug didn't converge: it let execution reach this
    # point (past the old assert), only to fall through into this
    # separate, pre-existing gap and immediately run brand-new code
    # (degree/root-finding against fixed-size length-8 buffers) for the
    # first time ever, on data whose "degree" bookkeeping was never
    # validated against a genuine nonzero polynomial.
    #
    # Representation: rhs_vec is in backend (Montgomery) form, since
    # fp_gauss! computes entirely via fpmul_b. coeffs_out is consumed
    # downstream (phi_to_EY!, build_N_inplace!, the vanishing checks,
    # phi_residual_general!, ...) exclusively via the plain, non-backend
    # fp/fpmul/fpinv functions, so it must be converted to raw
    # representation via from_repr before being stored.
    #
    # ACTUAL FIX (part 2): rhs_vec's solved entries are indexed by A_MAT
    # COLUMN — i.e. by position in the skip-y_idx traversal that
    # fill_monomial_block!/fill_mumford_block! used (bidx 1..nb, skipping
    # y_idx, mapped in order onto columns 1..n_cols) — NOT by basis index
    # directly. coeffs_out, by contrast, is indexed by BASIS POSITION
    # (coeffs_out[bidx] == coefficient of basis[bidx]), since that's the
    # ordering every downstream reader (phi_to_EY!, phi_eval, the
    # "PHI VANISHING CHECK" asserts, phi_residual_general!) assumes.
    #
    # For K=1 (y_idx==nb==4) these two orderings coincide for every
    # bidx < nb, and the old direct `coeffs_out[idx] = rhs_vec[idx]` copy
    # was consequently correct BY COINCIDENCE. Doing the mapping explicitly
    # here (skip y_idx, advance a separate column counter) means this is no
    # longer coincidental — it is correct for whatever index y actually
    # occupies, e.g. K=2's y_idx=4 != nb=5.
    col = 0
    @inbounds for bidx in 1:nb
        if bidx == y_idx
            scratch.coeffs_out[bidx] = 1   # normalised: coefficient of y is fixed to 1
        else
            col += 1
            scratch.coeffs_out[bidx] = from_repr(backend, scratch.rhs_vec[col])
        end
    end
    # DEFENSIVE ASSERT: the traversal above must have consumed every one of
    # rhs_vec's n_cols solved entries exactly once — mirrors the analogous
    # post-loop checks in fill_monomial_block!/fill_mumford_block!, so a
    # future edit that changes nb, y_idx, or the loop bounds independently
    # in only one of these three places fails loudly here instead of
    # silently dropping or duplicating a coefficient.
    n_cols = length(scratch.rhs_vec)
    @assert col == n_cols "build_phi_general!: coeffs_out write-back consumed $col of rhs_vec's $n_cols entries — skip-y_idx=$y_idx traversal over 1:$nb did not visit exactly n_cols non-y indices, so coeffs_out is now inconsistent with the solved system."
    @assert length(scratch.coeffs_out) == nb "build_phi_general!: coeffs_out length $(length(scratch.coeffs_out)) != nb=$nb after write-back — every basis position 1:nb should have received exactly one coefficient (either solved or the fixed y-normalisation)."

    # DEFENSIVE ASSERT (self-verification, ALL anchors, not just repeats):
    # re-evaluate phi(px,py) for every anchor in this tuple using a
    # completely independent evaluation path — plain powermod over the
    # PLAIN (non-backend) coeffs_out, deliberately NOT eval_monomial's
    # cached-table machinery (scratch.pxpow_buf, x_pow_mod_u caches, etc.),
    # which by this point in the call may hold state left over from
    # whichever anchor the loop above processed LAST, not necessarily the
    # anchor being checked. This runs for K=1 too (trivially, one anchor),
    # so if this exact check has never fired before on a real K=2 run, its
    # first failure here — WITH full build_phi_general! context (K, nb,
    # y_idx, which anchors were treated as repeats) still in scope — is the
    # most direct evidence available for whether plain (non-tangent) K=2
    # evaluation itself has a latent bug, independent of anything the
    # tangency work touched.
    @inbounds for a in 1:K
        (chk_px, chk_py) = anchors[a]
        chk_val = 0
        for bidx in 1:nb
            coeff = scratch.coeffs_out[bidx]
            coeff == 0 && continue
            (bi, bj) = basis[bidx]
            mono = bj == 0 ? powermod(chk_px, bi, p) : fpmul(powermod(chk_px, bi, p), chk_py)
            chk_val = fp(chk_val + fpmul(coeff, mono))
        end
        @assert chk_val == 0 "build_phi_general!: SELF-VERIFICATION failed inside build_phi_general! itself (before returning to step_phi_k!) — anchor a=$a (px,py)=($chk_px,$chk_py) of $K, phi_val=$chk_val (expected 0). K=$K nb=$nb y_idx=$y_idx anchors=$anchors coeffs_out=$(scratch.coeffs_out[1:nb]) basis=$basis. This is evaluated via plain powermod, independent of eval_monomial/scratch.pxpow_buf, so a failure here rules out stale-scratch-state as the cause and points at either the linear solve itself (fp_gauss!) or the row/column construction (fill_monomial_block!/fill_rhs!/fill_mumford_block!) producing a self-inconsistent system that fp_gauss! nonetheless solved without reporting singularity."
    end

    return true
end

# ---------------------------------------------------------------------------
#  phi_to_EY! (Zero-Allocation & Memory-Isolated Edition)
#
#  Splits φ(x,y) = E(x) + y * Y(x) directly inside scratch spaces.
#  
#  Saves:
#    E(x) coefficients into scratch.poly_buf[1 : deg_E + 1]
#    Y(x) coefficients into scratch.poly_buf[33 : 33 + deg_Y]
#
#  Returns:
#    (deg_E, deg_Y) :: NTuple{2, Int}
# ---------------------------------------------------------------------------
function phi_to_EY!(
    scratch::ThreadScratchpad{<:Any},
    basis  ::Vector{NTuple{2,Int}}
)::NTuple{2, Int}

    # Zero-out the active working ranges within poly_buf.
    # E(x) occupies slots 1..32; Y(x) occupies slots 33..64.
    # deg_E and deg_Y both grow roughly linearly with nb (deg_E ~ nb/2), so the
    # nb+2 bound below scales with whatever K_MAX is configured to — it is not
    # tied to any specific K_MAX value. We clear 1..nb+2 for E and 33..33+nb
    # for Y (generous safe bound) rather than the full 32+32 slots, since
    # clearing exactly what we need saves ~2x.
    nb_local = length(basis)
    clear_e = nb_local + 2     # enough for any E(x) coefficient index
    clear_y = nb_local + 2     # enough for any Y(x) coefficient index
    for i in 1:clear_e
        @inbounds scratch.poly_buf[i] = 0
    end
    for i in 1:clear_y
        @inbounds scratch.poly_buf[32 + i] = 0
    end

    deg_E = 0
    deg_Y = -1  # -1 signifies Y(x) has not been populated yet

    nb = length(basis)
    @assert nb <= 32 "phi_to_EY!: nb=$nb exceeds the 32-slot E(x)/Y(x) half-buffer layout (poly_buf[1:32]=E, poly_buf[33:64]=Y) — basis grew beyond what this fixed layout assumes"
    for idx in 1:nb
        @inbounds c = scratch.coeffs_out[idx]
        c == 0 && continue

        @inbounds bi, bj = basis[idx]
        @assert bi >= 0 "phi_to_EY!: basis[$idx] has negative x-exponent bi=$bi"
        if bj == 0
            # Element is a coefficient of E(x)
            @assert bi + 1 <= 32 "phi_to_EY!: E(x) coefficient index bi+1=$(bi+1) exceeds poly_buf's E-half (slots 1..32); bi=$bi from basis[$idx]=$(basis[idx])"
            @inbounds scratch.poly_buf[bi + 1] = fp(scratch.poly_buf[bi + 1] + c)
            if bi > deg_E
                deg_E = bi
            end
        else
            # Element is a coefficient of Y(x) (shifted by offset 33)
            @assert 33 + bi <= 64 "phi_to_EY!: Y(x) coefficient index 33+bi=$(33+bi) exceeds poly_buf's Y-half (slots 33..64); bi=$bi from basis[$idx]=$(basis[idx])"
            @inbounds scratch.poly_buf[33 + bi] = fp(scratch.poly_buf[33 + bi] + c)
            if bi > deg_Y
                deg_Y = bi
            end
        end
    end

    return (deg_E, deg_Y)
end

# ---------------------------------------------------------------------------
#  poly_mul(a, b) — multiply two polynomials (ascending coefficients) over F_p.
# ---------------------------------------------------------------------------
function poly_mul(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    na, nb = length(a), length(b)
    c = zeros(Int, na + nb - 1)
    for i in 1:na, j in 1:nb
        c[i+j-1] = fp(c[i+j-1] + fpmul(a[i], b[j]))
    end
    return c
end

# ---------------------------------------------------------------------------
#  poly_sq(a) — square a polynomial over F_p.
# ---------------------------------------------------------------------------
function poly_sq(a::Vector{Int})::Vector{Int}
    n = length(a)
    c = zeros(Int, 2n - 1)
    for i in 1:n
        a[i] == 0 && continue
        c[2i-1] = fp(c[2i-1] + fpmul(a[i], a[i]))
        for j in i+1:n
            a[j] == 0 && continue
            c[i+j-1] = fp(c[i+j-1] + 2*fpmul(a[i], a[j]))
        end
    end
    return c
end


# ---------------------------------------------------------------------------
#  poly_mul_mod_inplace!(scratch, len_a, off_a, len_b, off_b, u_len) -> Int
#
#  Multiplies two polynomials inside scratch.poly_buf segments and reduces the
#  result modulo u_RS in-place.
#
#  We use poly_buf[257:384] (offset 256) as a safe intermediate multiplication area
#  before calling poly_reduce_mod_inplace!.
# ---------------------------------------------------------------------------
function poly_mul_mod_inplace!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int, off_a::Int,
    len_b::Int, off_b::Int,
    u_len::Int
)::Int

    # If either input is empty, the product is 0
    (len_a <= 0 || len_b <= 0) && return 0

    # 1. Execute convolution into a fresh temporary workspace segment (offset 256)
    off_mul = 256
    len_mul = len_a + len_b - 1
    
    # Zero out the multiplication work window
    for i in 1:len_mul
        @inbounds scratch.poly_buf[off_mul + i] = 0
    end

    # 2. Perform the multiplication
    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        for j in 1:len_b
            @inbounds bj = scratch.poly_buf[off_b + j]
            bj == 0 && continue
            
            idx = off_mul + i + j - 1
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + fpmul(ai, bj))
        end
    end

    # 3. Reduce modulo u_RS in place
    final_len = poly_reduce_mod_inplace!(scratch, off_mul + len_mul, off_mul, u_len)

    # 4. Copy the final reduced remainder straight into scratch.v_RS
    #
    # CRITICAL BOUNDS ASSERT: scratch.v_RS is a fixed length-8 Vector{Int}
    # (see ThreadScratchpad{K}() constructor), same as scratch.u_RS. Same
    # risk as the u_RS copy in phi_residual_general!: final_len depends on
    # poly_reduce_mod_inplace!'s degree bookkeeping, now running for the
    # first time on genuinely nonzero coefficients (see coeffs_out bugfix
    # in build_phi_general!). An @inbounds overrun here is silent until it
    # corrupts something else's memory.
    @assert final_len <= length(scratch.v_RS) "poly_mul_mod_inplace!: final_len=$final_len exceeds scratch.v_RS's fixed capacity ($(length(scratch.v_RS))) — would silently overrun v_RS via @inbounds. len_a=$len_a, len_b=$len_b, u_len=$u_len."
    for i in 1:final_len
        @inbounds scratch.v_RS[i] = scratch.poly_buf[off_mul + i]
    end

    return final_len
end

# ---------------------------------------------------------------------------
#  poly_mul_inplace_segment!(scratch, len_a, off_a, len_b, off_b, off_dest) -> Int
#  Multiplies polynomial A and B, writing the result starting at off_dest.
# ---------------------------------------------------------------------------
function poly_mul_inplace_segment!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int, off_a::Int,
    len_b::Int, off_b::Int,
    off_dest::Int
)::Int
    (len_a <= 0 || len_b <= 0) && return 0
    len_out = len_a + len_b - 1

    # WILLY-NILLY ASSERT: poly_buf has 1024 slots total; off_dest is a raw
    # caller-supplied offset with no length check anywhere in this
    # function. A bad offset/length pair here writes silently past the
    # buffer via @inbounds.
    @assert off_dest + len_out <= length(scratch.poly_buf) "poly_mul_mod_inplace! (segment mul): off_dest=$off_dest len_out=$len_out would write past poly_buf length $(length(scratch.poly_buf))"
    @assert off_a + len_a <= length(scratch.poly_buf) "poly_mul_mod_inplace!: off_a=$off_a len_a=$len_a reads past poly_buf"
    @assert off_b + len_b <= length(scratch.poly_buf) "poly_mul_mod_inplace!: off_b=$off_b len_b=$len_b reads past poly_buf"

    for i in 1:len_out
        @inbounds scratch.poly_buf[off_dest + i] = 0
    end

    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        for j in 1:len_b
            @inbounds bj = scratch.poly_buf[off_b + j]
            bj == 0 && continue
            idx = off_dest + i + j - 1
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + fpmul(ai, bj))
        end
    end
    return len_out
end

# ---------------------------------------------------------------------------
#  poly_sq_inplace_segment!(scratch, len_a, off_a, off_dest) -> Int
#  Squares a polynomial over F_p into a target destination segment.
# ---------------------------------------------------------------------------
function poly_sq_inplace_segment!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int, off_a::Int,
    off_dest::Int
)::Int
    len_a <= 0 && return 0
    len_out = 2 * len_a - 1

    @assert off_dest + len_out <= length(scratch.poly_buf) "poly_sq_inplace_segment!: off_dest=$off_dest len_out=$len_out would write past poly_buf length $(length(scratch.poly_buf))"
    @assert off_a + len_a <= length(scratch.poly_buf) "poly_sq_inplace_segment!: off_a=$off_a len_a=$len_a reads past poly_buf"

    for i in 1:len_out
        @inbounds scratch.poly_buf[off_dest + i] = 0
    end

    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        
        # Diagonal elements: ai²
        idx_diag = off_dest + 2*i - 1
        @inbounds scratch.poly_buf[idx_diag] = fp(scratch.poly_buf[idx_diag] + fpmul(ai, ai))
        
        # Cross terms: 2 * ai * aj
        for j in (i + 1):len_a
            @inbounds aj = scratch.poly_buf[off_a + j]
            aj == 0 && continue
            
            idx_cross = off_dest + i + j - 1
            @inbounds scratch.poly_buf[idx_cross] = fp(scratch.poly_buf[idx_cross] + 2 * fpmul(ai, aj))
        end
    end
    return len_out
end

# ---------------------------------------------------------------------------
#  build_N_inplace!(scratch, deg_E, deg_Y) -> Int
#
#  Computes the norm polynomial N(x) = E(x)² - f(x)·Y(x)² inside the thread 
#  scratchpad without heap allocations or temporary array spawning.
#
#  Memory Configuration:
#    Input E(x) read from: scratch.poly_buf[1 : deg_E+1]
#    Input Y(x) read from: scratch.poly_buf[33 : 33+deg_Y]
#    Output N(x) written to: scratch.poly_buf[1 : final_len]
#
#  F_POLY is assumed to be globally cached as a Vector{Int} or NTuple{6, Int}.
# ---------------------------------------------------------------------------
function build_N_inplace!(
    scratch::ThreadScratchpad{<:Any},
    deg_E::Int,
    deg_Y::Int
)::Int

    @assert length(F_POLY) == 6 "build_N_inplace!: F_POLY has length $(length(F_POLY)), expected 6 (curve y²=x⁵+x+2 has 6 coefficients x⁰..x⁵) — F_POLY[f_idx] for f_idx in 1:6 below assumes this"
    @assert deg_E >= 0 "build_N_inplace!: deg_E=$deg_E must be >= 0 (phi_to_EY! always sets deg_E>=0)"
    @assert deg_Y >= -1 "build_N_inplace!: deg_Y=$deg_Y must be >= -1 (sentinel for 'no Y term')"

    # 1. Clear out the serialization area completely
    for i in 1:64
        @inbounds scratch.ser_buf[i] = 0
    end

    len_E = deg_E + 1
    len_Y = deg_Y + 1

    @assert len_E >= 1 "build_N_inplace!: len_E=$len_E must be >= 1"
    @assert len_Y >= 0 "build_N_inplace!: len_Y=$len_Y must be >= 0"
    @assert len_E <= 32 "build_N_inplace!: len_E=$len_E exceeds ser_buf's E-half (slots 1..32)"
    @assert len_Y <= 32 "build_N_inplace!: len_Y=$len_Y exceeds ser_buf's Y-half (slots 33..64)"

    for i in 1:len_E
        @inbounds scratch.ser_buf[i] = scratch.poly_buf[i]
    end
    for i in 1:len_Y
        @inbounds scratch.ser_buf[32 + i] = scratch.poly_buf[32 + i]
    end

    # 2. Clear out the front of scratch.poly_buf
    for i in 1:64
        @inbounds scratch.poly_buf[i] = 0
    end

    # 3. Accumulate E(x)² into scratch.poly_buf
    for i in 1:len_E
        @inbounds c_i = scratch.ser_buf[i]
        c_i == 0 && continue

        # Diagonal: c_i²
        idx_diag = 2*i - 1
        @assert 1 <= idx_diag <= 64 "build_N_inplace!: E² diagonal write idx_diag=$idx_diag (i=$i) out of poly_buf[1:64] range"
        @inbounds scratch.poly_buf[idx_diag] = fp(scratch.poly_buf[idx_diag] + fpmul(c_i, c_i))

        # Cross: 2 * c_i * c_j
        for j in (i+1):len_E
            @inbounds c_j = scratch.ser_buf[j]
            c_j == 0 && continue
            idx = i + j - 1
            @assert 1 <= idx <= 64 "build_N_inplace!: E² cross write idx=$idx (i=$i,j=$j) out of poly_buf[1:64] range"
            term = fpmul(c_i, c_j)
            # 2*term < 2p, comfortably inside Int64 — no need to pre-reduce
            # before the final fp() on the accumulator add (matches the style
            # already used in poly_sq!/poly_sq_inplace_segment! elsewhere).
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + 2 * term)
        end
    end

    # 4. Compute Y(x)² * f(x) and subtract
    for i in 1:len_Y
        @inbounds y_i = scratch.ser_buf[32 + i]
        y_i == 0 && continue

        # Diagonal: y_i²
        y2_coeff_d = fpmul(y_i, y_i)
        y2_deg_d   = 2 * (i - 1)
        for f_idx in 1:6
            @inbounds f_coeff = F_POLY[f_idx]
            f_coeff == 0 && continue
            target_idx = y2_deg_d + f_idx
            @assert 1 <= target_idx <= 64 "build_N_inplace!: Y² diagonal write target_idx=$target_idx (i=$i,f_idx=$f_idx,y2_deg_d=$y2_deg_d) out of poly_buf[1:64] range"
            @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(y2_coeff_d, f_coeff))
        end

        # Cross: 2 * y_i * y_j
        for j in (i+1):len_Y
            @inbounds y_j = scratch.ser_buf[32 + j]
            y_j == 0 && continue

            prod_y = fpmul(y_i, y_j)
            y2_coeff_c = fp(prod_y + prod_y)
            y2_deg_c   = (i - 1) + (j - 1)
            for f_idx in 1:6
                @inbounds f_coeff = F_POLY[f_idx]
                f_coeff == 0 && continue
                target_idx = y2_deg_c + f_idx
                @assert 1 <= target_idx <= 64 "build_N_inplace!: Y² cross write target_idx=$target_idx (i=$i,j=$j,f_idx=$f_idx,y2_deg_c=$y2_deg_c) out of poly_buf[1:64] range"
                @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(y2_coeff_c, f_coeff))
            end
        end
    end

    deg_N = 63
    while deg_N >= 0
        @inbounds if scratch.poly_buf[deg_N + 1] != 0
            break
        end
        deg_N -= 1
    end

    return deg_N + 1 # Fix: Return length instead of degree
end

# ---------------------------------------------------------------------------
#  poly_div_linear!(N, r) — divide N by (x - r) in place using Horner.
#  Returns remainder.  N is overwritten with the quotient (length shrinks by 1).
# ---------------------------------------------------------------------------
function poly_div_linear!(N::Vector{Int}, r::Int)::Int
    n   = length(N)
    rem = N[n]
    for i in n-1:-1:1
        old    = N[i]
        N[i]   = rem
        rem    = fp(old + fpmul(rem, r))
    end
    popfirst!(N)   # remove leading (now quotient's leading) — actually we built Q in-place above
    # Wait — descending Horner builds quotient from high to low.  Re-do cleanly:
    return rem
end

# Cleaner descending-Horner division: returns (quotient_coeffs_ascending, remainder).
function poly_divmod_linear(N::Vector{Int}, r::Int)::Tuple{Vector{Int}, Int}
    # N is ascending: N[1] = const, N[end] = leading coeff.
    # Work in descending order.
    n = length(N)
    if n == 1; return (Int[], N[1]); end
    q = zeros(Int, n-1)     # quotient degree = n-2
    # Descending Horner: q[n-1], q[n-2], ..., q[1], rem
    q[n-1] = N[n]
    for i in n-1:-1:2
        q[i-1] = fp(N[i] + fpmul(q[i], r))
    end
    rem = fp(N[1] + fpmul(q[1], r))
    return (q, rem)
end


# ---------------------------------------------------------------------------
#  poly_divmod_linear_inplace!(scratch, n_len, alpha) -> (Int, Int)
#
#  Divides the active polynomial inside scratch.poly_buf[1:n_len] by (x - alpha)
#  in-place over F_p using Horner's synthetic division rule.
#
#  Mutates: scratch.poly_buf up to n_len.
#  Returns: (new_logical_len, remainder_scalar)
#  ALLOCATION INVARIANT: Zero heap allocations. Pure scalar registers.
# ---------------------------------------------------------------------------
function poly_divmod_linear_inplace!(
    scratch::ThreadScratchpad{<:Any},
    n_len::Int,
    alpha::Int
)::Tuple{Int, Int}
    
    # If the polynomial is a scalar or empty, division is degenerate
    n_len <= 1 && return (n_len, scratch.poly_buf[1])

    # Run Synthetic Division from the highest degree coefficient downwards
    @inbounds rem_val = scratch.poly_buf[n_len]
    @inbounds scratch.poly_buf[n_len] = 0 # Leading quotient position drops by 1 degree
    
    for i in (n_len - 1):-1:1
        @inbounds orig_coeff = scratch.poly_buf[i]
        
        # Next quotient coefficient is the accumulated remainder step
        @inbounds scratch.poly_buf[i] = rem_val
        
        # Shift remainder calculation: rem = orig_coeff + alpha * rem_val (mod p)
        rem_val = fp(orig_coeff + fpmul(alpha, rem_val))
    end
    
    # Compute new logical length of the quotient polynomial window
    new_len = n_len - 1
    while new_len > 1
        @inbounds if scratch.poly_buf[new_len] == 0
            new_len -= 1
        else
            break
        end
    end
    
    return (new_len, rem_val)
end

# ---------------------------------------------------------------------------
#  poly_divmod_monic_deg2_inplace!(scratch, n_len, u1, u0)
#
#  Divides the active polynomial inside scratch.poly_buf[1:n_len] by 
#  u(x) = x² + u1*x + u0 in-place over F_p.
#
#  Mutates: scratch.poly_buf to hold the final quotient in ASCENDING order 
#           starting at index 1.
#  Returns: (quotient_len, rem0, rem1) :: Tuple{Int, Int, Int}
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_divmod_monic_deg2_inplace!(
    scratch::ThreadScratchpad{<:Any},
    n_len::Int,
    u1::Int, 
    u0::Int
)::Tuple{Int, Int, Int}
    
    # If the input polynomial doesn't have enough degrees to divide, it's all remainder
    if n_len < 3
        if n_len == 2
            @inbounds r1 = scratch.poly_buf[2]
            @inbounds r0 = scratch.poly_buf[1]
        elseif n_len == 1
            r1 = 0
            @inbounds r0 = scratch.poly_buf[1]
        else
            r1 = 0
            r0 = 0
        end
        return (0, r0, r1)
    end

    # 1. Long division pass working downward through the buffer.
    #    The active coefficients of N(x) are already at scratch.poly_buf[1:n_len].
    for i in n_len:-1:3
        @inbounds c = scratch.poly_buf[i]
        c == 0 && continue
        
        # Quotient coefficient falls into place; we clear the processed dividend term
        @inbounds scratch.poly_buf[i] = c # Keep it tracked here temporarily for flipping
        @inbounds scratch.poly_buf[i-1] = fp(scratch.poly_buf[i-1] - fpmul(c, u1))
        @inbounds scratch.poly_buf[i-2] = fp(scratch.poly_buf[i-2] - fpmul(c, u0))
    end

    # 2. Extract final remainders from the lowest two slots
    @inbounds r0 = scratch.poly_buf[1]
    @inbounds r1 = scratch.poly_buf[2]

    # 3. The quotient terms are now sitting in scratch.poly_buf[3:n_len].
    #    We shift them down into slots [1 : q_len] directly.
    #    (Since we are processing ascending indexes linearly, we can bypass the 
    #    reverse loop if we copy the computed elements from their high offsets).
    q_len = n_len - 2
    for i in 1:q_len
        @inbounds scratch.poly_buf[i] = scratch.poly_buf[i + 2]
    end

    # 4. Strip trailing zeros logically by shrinking the valid window bound
    while q_len > 1
        @inbounds if scratch.poly_buf[q_len] == 0
            q_len -= 1
        else
            break
        end
    end

    return (q_len, r0, r1)
end


# ---------------------------------------------------------------------------
#  phi_residual_general
#
#  Given the φ coefficients (from build_phi_general), the anchor x-coords,
#  and the Mumford u-polynomial, compute the residual intersection divisor.
#
#  Returns (u_RS_coeffs, v_RS_pair) where:
#    u_RS_coeffs : ascending coefficients of the monic residual u_RS(x)
#    v_RS_pair   : (v0_rs, v1_rs, ...) = v_RS(x) coefficients  (NOT YET COMPUTED
#                  for higher degree; see note below)
#
#  For now returns the residual polynomial u_RS(x) (ascending, monic) and
#  a flag indicating whether it has been split into affine points.
#
#  Concretely the return type matches the k=1 pattern extended:
#
#    For k=1 (classic): residual is degree 2 → tried to split over F_p.
#    For k=2:           residual is degree 3 → find rational root + degree-2 factor.
#    For k=3:           residual is degree 4 → find all rational roots.
#
#  Returns:
#    (roots::Vector{NTuple{2,Int}},   # affine residual pts (empty if none split)
#     u_RS ::Vector{Int},             # residual u(x) ascending monic coeffs
#     v_RS ::Vector{Int})             # v_RS(x) ascending coeffs (same degree-1 below u_RS)
#
#  Sentinel: roots empty + u_RS = [-1] means computation failed (remainder ≠ 0).
# ---------------------------------------------------------------------------
const RESIDUAL_FAIL = Int[-1]

# ---------------------------------------------------------------------------
#  phi_residual_general! (Zero-Allocation & Slicing-Safe Edition)
#
#  Computes the residual polynomial N(x) and its Mumford / split point roots
#  by peeling off known anchor and branch factors via local, stack-allocated 
#  index registers.
#
#  Modifies primitive array fields inside `scratch` to preserve allocation-free execution.
# ---------------------------------------------------------------------------
function phi_residual_general!(
    scratch ::ThreadScratchpad{K},
    basis   ::Vector{NTuple{2,Int}},
    anchors ::NTuple{K,NTuple{2,Int}},
    u0::Int, u1::Int
)::Bool where K

    # Reset primitive length registers on our thread scratchpad
    scratch.roots_count[1]  = 0
    scratch.u_RS_len[1]     = 0
    scratch.v_RS_len[1]     = 0
    scratch.u_RS_is_fail[1] = false

    k = K  # compile-time constant from type parameter

    # WILLY-NILLY ASSERT: catch a mismatched (scratch, anchors, basis)
    # triple early — this function silently trusts that anchors has length
    # K (the type param) and basis has length K+3; a caller bug here would
    # otherwise show up as an obscure downstream indexing error deep in
    # build_N_inplace!/find_roots_and_points_inplace! instead of here.
    @assert length(anchors) == K "phi_residual_general!: length(anchors)=$(length(anchors)) != K=$K"
    @assert length(basis) == K + 3 "phi_residual_general!: length(basis)=$(length(basis)) != K+3=$(K+3)"

    _pt_res_buildN_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 1. Convert phi to E(x) and Y(x) representations inside scratch buffers.
    #    Capture the returned degrees to avoid dynamic searching in the next step.
    deg_E, deg_Y = phi_to_EY!(scratch, basis)

    # 2. Compute N(x) = E(x)^2 - f(x)*Y(x)^2 inside our large pre-allocated scratch.poly_buf.
    #    Pass the degrees explicitly to preserve zero-allocation execution.
    n_len = build_N_inplace!(scratch, deg_E, deg_Y)

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_buildN += time_ns() - _pt_res_buildN_t0
    end

    _pt_res_divmod_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 3. Divide out anchor factors with correct multiplicity using zero-alloc linear scan.
    for idx in 1:k
        @inbounds px = anchors[idx][1]
        
        already_done = false
        for prev in 1:(idx-1)
            @inbounds if anchors[prev][1] == px
                already_done = true
                break
            end
        end
        already_done && continue

        cnt = 0
        for jdx in idx:k
            @inbounds if anchors[jdx][1] == px
                cnt += 1
            end
        end

        for _ in 1:cnt
            # poly_divmod_linear! mutates scratch.poly_buf up to n_len in place, 
            # returning the new logical length and scalar remainder.
            n_len, rem_val = poly_divmod_linear_inplace!(scratch, n_len, px)
            if rem_val != 0
                scratch.u_RS_is_fail[1] = true
                s = phi_timing_stats()
                s.n_fail_residual += 1
                s.n_fail_resid_anchor_remainder += 1
                return false
            end
        end
    end

    # 4. Divide out u(x) = x² + u1·x + u0
    #    poly_divmod_monic_deg2_inplace! mutates scratch.poly_buf down by 2 degrees.
    n_len, r0, r1 = poly_divmod_monic_deg2_inplace!(scratch, n_len, u1, u0)
    if r0 != 0 || r1 != 0
        scratch.u_RS_is_fail[1] = true
        s = phi_timing_stats()
        s.n_fail_residual += 1
        s.n_fail_resid_u_remainder += 1
        return false
    end

    # 5. Strip trailing zeros up to n_len
    while n_len > 1
        @inbounds if scratch.poly_buf[n_len] == 0
            n_len -= 1
        else
            break
        end
    end

    # Degenerate residual check
    @inbounds if n_len == 1 && scratch.poly_buf[1] == 0
        scratch.u_RS_is_fail[1] = true
        s = phi_timing_stats()
        s.n_fail_residual += 1
        s.n_fail_resid_degenerate += 1
        return false
    end

    # 6. Normalize to make the residual polynomial monic
    @inbounds lc = scratch.poly_buf[n_len]
    if lc != 1
        inv_lc = fpinv(lc)
        for i in 1:n_len
            @inbounds scratch.poly_buf[i] = fpmul(scratch.poly_buf[i], inv_lc)
        end
    end

    # 7. Copy computed coefficients of N(x) into scratch.u_RS
    #
    # CRITICAL BOUNDS ASSERT: scratch.u_RS is a fixed length-8 Vector{Int}
    # (see ThreadScratchpad{K}() constructor). n_len at this point is the
    # residual polynomial's length after build_N_inplace! (degree tracking,
    # never exercised on real nonzero data until scratch.coeffs_out was
    # actually populated) followed by several in-place divisions
    # (poly_divmod_linear_inplace! per anchor multiplicity,
    # poly_divmod_monic_deg2_inplace! for u(x)). If n_len exceeds 8 here —
    # from a degree-tracking bug anywhere upstream, or simply a K/anchor
    # configuration this fixed-8 assumption doesn't actually cover — the
    # @inbounds copy loop below silently writes past the end of u_RS's
    # backing array, corrupting adjacent heap memory (the classic silent
    # segfault-later pattern, since @inbounds skips the bounds check that
    # would otherwise throw here immediately).
    @assert n_len <= length(scratch.u_RS) "phi_residual_general!: residual length n_len=$n_len exceeds scratch.u_RS's fixed capacity ($(length(scratch.u_RS))) — would silently overrun u_RS via @inbounds. K=$k, deg_E=$deg_E, deg_Y=$deg_Y."
    scratch.u_RS_len[1] = n_len
    for i in 1:n_len
        @inbounds scratch.u_RS[i] = scratch.poly_buf[i]
    end

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_divmod += time_ns() - _pt_res_divmod_t0
    end

    _pt_res_vrs_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 8. Compute v_RS(x) mod N(x) directly inside scratch.v_RS workspace
    v_len = compute_vRS_inplace!(scratch, n_len)
    scratch.v_RS_len[1] = v_len

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_vrs += time_ns() - _pt_res_vrs_t0
    end

    _pt_res_roots_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)

    # 9. Find split points using scratch structures, updates scratch.roots_count[1]
    find_roots_and_points_inplace!(scratch, n_len, Val(K))

    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_res_roots += time_ns() - _pt_res_roots_t0
    end

    return true
end

# ---------------------------------------------------------------------------
#  compute_vRS_inplace!(scratch, u_len) -> Int
#
#  Computes v_RS(x) = -E(x) * (Y(x))⁻¹ mod u_RS(x) completely in-place.
#
#  Memory Configuration:
#    u_RS(x) read from      : scratch.u_RS[1 : u_len]
#    Original E(x), Y(x) are recovered via scratch.ser_buf (stashed by build_N_inplace!)
#    Output v_RS(x) written : scratch.v_RS[1 : final_v_len]
#
#  Returns: final_v_len :: Int
#  ALLOCATION INVARIANT: Zero heap allocations. Pure scalar registers.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  compute_vRS_inplace!(scratch, u_len) -> Int
#
#  Computes v_RS(x) = -E(x) * (Y(x))⁻¹ mod u_RS(x) completely in-place.
# ---------------------------------------------------------------------------
function compute_vRS_inplace!(
    scratch::ThreadScratchpad{<:Any},
    u_len::Int
)::Int

    deg_u = u_len - 1
    deg_u <= 0 && return 0

    # 1. Check if Y(x) is the zero polynomial.
    #    E(x) and Y(x) are safe inside ser_buf. (Y is at offset 33).
    is_Y_zero = true
    # We dynamically find the active length of Y while checking for non-zero terms
    y_len = 32
    while y_len > 0
        @inbounds if scratch.ser_buf[32 + y_len] != 0
            is_Y_zero = false
            break
        end
        y_len -= 1
    end

    # 2. Compute -E mod u_RS directly into a working slice of scratch.poly_buf.
    #    Find active length of E(x) from ser_buf:
    e_len = 32
    while e_len > 1
        @inbounds if scratch.ser_buf[e_len] == 0
            e_len -= 1
        else
            break
        end
    end

    # Clear only as many slots as e_len needs (u_len+4 is always safe since
    # after reduction the length is ≤ u_len (u_len ≤ 3, a fixed invariant
    # independent of K_MAX — see phi_residual_general! header). e_len can grow
    # with K_MAX; use max(e_len, u_len) + 2.
    clear_e = max(e_len, u_len) + 2
    for i in 1:clear_e
        @inbounds scratch.poly_buf[64 + i] = 0
    end
    for i in 1:e_len
        @inbounds scratch.poly_buf[64 + i] = fp(-scratch.ser_buf[i])
    end

    # Perform in-place polynomial reduction: poly_buf[65...] mod u_RS
    negE_len = poly_reduce_mod_inplace!(scratch, 64 + e_len, 64, u_len)

    # Degenerate early return case if Y(x) == 0
    if is_Y_zero
        # We MUST fail the step. The residual is vertical/degenerate.
        scratch.u_RS_is_fail[1] = true
        return 0
    end

    # 3. Compute Y mod u_RS.
    clear_y = max(y_len, u_len) + 2
    for i in 1:clear_y
        @inbounds scratch.poly_buf[128 + i] = 0
    end
    for i in 1:y_len
        @inbounds scratch.poly_buf[128 + i] = scratch.ser_buf[32 + i]
    end
    
    ymod_len = poly_reduce_mod_inplace!(scratch, 128 + y_len, 128, u_len)

    # 4. Compute Modular Inverse: Y_inv mod u_RS via Extended GCD.
    #
    #    FAST PATH: when u_RS is degree 2 (u_len==3, the dominant k=1 case)
    #    and Y mod u_RS is genuinely linear (ymod_len==2, i.e. its x-coeff
    #    is nonzero), use the closed-form deg-2 inverse instead of the
    #    general extended-Euclid loop — saves on the order of one extra
    #    fpinv call plus the per-iteration register-clear bookkeeping.
    #    Every other case (ymod_len<=1, i.e. Y mod u_RS collapsed to a
    #    constant; or u_len != 3, i.e. higher-degree residual for k>1)
    #    falls straight through to the unchanged general path below.
    @inbounds u0_mod = scratch.u_RS[1]
    @inbounds u1_mod = scratch.u_RS[2]
    if u_len == 3 && ymod_len == 2
        yinv_len, ok = poly_modinv_deg2_closed_form!(scratch, ymod_len, 128, u0_mod, u1_mod)
    else
        yinv_len, ok = poly_modinv_inplace!(scratch, ymod_len, 128, u_len)
    end
    if !ok
        # Degenerate case: Y is not invertible.
        # We MUST fail the step to prevent false collisions on v=0.
        scratch.u_RS_is_fail[1] = true
        return 0
    end

    # 5. Compute v_RS = negE_mod * Y_inv mod u_RS.
    v_len = poly_mul_mod_inplace!(scratch, negE_len, 64, yinv_len, 128, u_len)

    return v_len
end

# ---------------------------------------------------------------------------
#  poly_reduce_mod_inplace!(scratch, raw_len, offset, u_len) -> Int
#
#  Reduces a polynomial stored at scratch.poly_buf[offset + 1 : raw_len]
#  modulo m(x) = scratch.u_RS[1 : u_len] in-place over F_p.
#
#  Inputs:
#    raw_len : Total right boundary of the dividend inside poly_buf
#    offset  : The baseline indexing offset of the polynomial block to reduce
#    u_len   : Length of the modulus polynomial (scratch.u_RS)
#
#  Mutates: scratch.poly_buf[offset + 1 : ...] in place.
#  Returns: The final logical length of the reduced remainder.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_reduce_mod_inplace!(
    scratch::ThreadScratchpad{<:Any},
    raw_len::Int,
    offset::Int,
    u_len::Int
)::Int

    dm = u_len - 1
    @inbounds lc_m = scratch.u_RS[u_len]
    
    # Invariant assertion handling without string construction allocation
    if lc_m == 0
        throw(ArgumentError("poly_reduce_mod_inplace!: modulus leading coefficient is zero"))
    end
    
    # u_RS is normalised to monic in phi_residual_general! step 6 before any
    # poly_reduce_mod_inplace! call, so lc_m == 1 is a proven invariant.
    # Skip the Fermat-ladder fpinv call (which hits the `a==1 && return 1`
    # fast path anyway but still costs a branch+call on each of ~4 reductions
    # per walk step). Fall back to fpinv only in the degenerate non-monic case.
    lc_m_inv = (lc_m == 1) ? 1 : fpinv(lc_m)
    
    # r_len tracks the absolute index boundary of the dividend within poly_buf
    r_len = raw_len
    
    while true
        # Compute current logical degree of remainder relative to offset base
        deg_r = (r_len - offset) - 1
        deg_r < dm && break
        
        # Check if the polynomial reduces logically down to a single zero term
        if deg_r == 0
            @inbounds val = scratch.poly_buf[r_len]
            val == 0 && break
        end

        # Strip trailing zeros safely by dropping the logical length tracker
        @inbounds if scratch.poly_buf[r_len] == 0
            r_len -= 1
            continue
        end

        # Scale factor c = r[end] * lc_m_inv
        # lc_m_inv == 1 by the monic invariant: skip the multiply.
        # The branch here costs essentially nothing since lc_m_inv was already
        # evaluated once above the loop; the `== 1` path is always taken.
        @inbounds c = (lc_m_inv == 1) ? scratch.poly_buf[r_len] : fpmul(scratch.poly_buf[r_len], lc_m_inv)
        shift = deg_r - dm
        
        # Subtract c * x^shift * m(x) from the current remainder window
        for i in 1:u_len
            @inbounds m_val = scratch.u_RS[i]
            idx = offset + i + shift
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] - fpmul(c, m_val))
        end

        # Clean trailing high-slot elements that are guaranteed to have been cancelled
        while r_len > (offset + 1)
            @inbounds if scratch.poly_buf[r_len] == 0
                r_len -= 1
            else
                break
            end
        end
    end

    # Return the clean active logical length of the remainder block
    return r_len - offset
end


# Multiply two polynomials mod m.
function poly_mul_mod(a::Vector{Int}, b::Vector{Int},
                       m::Vector{Int})::Vector{Int}
    return poly_reduce_mod(poly_mul(a, b), m)
end

# ---------------------------------------------------------------------------
#  poly_modinv_deg2_closed_form!(scratch, len_a, off_a, u0, u1) -> (Int, Bool)
#
#  Fast path for inverting a polynomial a(x) modulo a MONIC DEGREE-2 modulus
#  u(x) = x² + u1*x + u0, used in place of the general extended-Euclid
#  poly_modinv_inplace! whenever deg(u_RS) == 2 — the dominant case for k=1
#  walks, where the residual u_RS is always degree 2.
#
#  DERIVATION (verified symbolically against sympy.resultant and numerically
#  against 6000 random trials at p ~ 10^4, 10^6, and ~2^45 before being coded):
#
#    a(x) = a0 + a1*x,  want b(x) = b0 + b1*x  with  a(x)*b(x) ≡ 1  mod u(x).
#
#    a*b = a0*b0 + (a0*b1 + a1*b0)*x + a1*b1*x²
#    Reduce x² ≡ -u1*x - u0:
#      const  = a0*b0 - a1*b1*u0
#      x-coef = a0*b1 + a1*b0 - a1*b1*u1
#
#    Setting const=1, x-coef=0 and solving the resulting 2x2 linear system
#    for (b0, b1) gives:
#
#      D  = a0² - a0*a1*u1 + a1²*u0        (this is resultant(a, u) — zero
#                                            iff a and u share a root, i.e.
#                                            iff a is NOT invertible mod u)
#      b0 = (a0 - a1*u1) / D
#      b1 = -a1 / D
#
#  Only one fpinv call (of D) is needed, versus the general extended-Euclid
#  path's 1-2+ fpinv calls (one per division step) plus per-iteration
#  register-swap bookkeeping. This function assumes len_a == 2 (i.e. a1 ≠ 0,
#  guaranteed by poly_reduce_mod_inplace!'s trailing-zero trim whenever it
#  reports length 2) — callers must route len_a <= 1 (pure scalar a) through
#  the ordinary fpinv path instead, since the closed form above divides by
#  a1 implicitly via D and is not meant for that case.
#
#  Output contract matches poly_modinv_inplace! exactly: zeroes
#  poly_buf[off_a+1 : off_a+len_a] first, then writes the trimmed inverse
#  coefficients into poly_buf[off_a+1 : off_a+final_len], returning
#  (final_len, true) on success or (0, false) if a is not invertible (D=0).
# ---------------------------------------------------------------------------
@inline function poly_modinv_deg2_closed_form!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int,
    off_a::Int,
    u0::Int, u1::Int
)::Tuple{Int, Bool}

    @inbounds a0 = scratch.poly_buf[off_a + 1]
    @inbounds a1 = scratch.poly_buf[off_a + 2]

    D = fp(fp(fpmul(a0, a0) - fpmul(a0, fpmul(a1, u1))) + fpmul(fpmul(a1, a1), u0))

    if D == 0
        return (0, false)   # a(x) shares a root with u(x): not invertible
    end

    Dinv = fpinv(D)
    b0 = fpmul(fp(a0 - fpmul(a1, u1)), Dinv)
    b1 = fpmul(fp(-a1), Dinv)

    # NOTE: b1 == 0 here would require a1 == 0 (since b1 = -a1*Dinv and Dinv
    # is necessarily nonzero, being a multiplicative inverse). But this
    # function is only ever called when ymod_len==2, which by
    # poly_reduce_mod_inplace!'s trailing-zero-trim invariant guarantees
    # a1 != 0. So the inverse of a genuinely-linear polynomial mod a
    # degree-2 modulus is itself always genuinely linear — confirmed both
    # analytically and across 80,000 random trials (zero b1==0 hits) before
    # this was simplified down from an earlier version with a dead
    # defensive branch for that case.
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_a + i] = 0
    end
    @inbounds scratch.poly_buf[off_a + 1] = b0
    @inbounds scratch.poly_buf[off_a + 2] = b1
    return (2, true)
end

# ---------------------------------------------------------------------------
#  poly_modinv_inplace!(scratch, len_a, off_a, u_len) -> (Int, Bool)
#
#  Computes the modular inverse of a polynomial sitting at:
#    scratch.poly_buf[off_a + 1 : off_a + len_a]
#  modulo the polynomial m(x) = scratch.u_RS[1 : u_len].
#
#  Overwrites the input segment at off_a with the computed inverse coefficients
#  and returns (new_len, success).
#
#  Memory Configuration for Extended GCD Registers:
#    off_r0  = 384     (Holds running remainder r0, initialized to modulus m)
#    off_r1  = 448     (Holds running remainder r1, initialized to input a)
#    off_s0  = 512     (Holds Bezout coefficient s0, initialized to 0)
#    off_s1  = 576     (Holds Bezout coefficient s1, initialized to 1)
#    off_q   = 640     (Holds temporary quotient q)
#    off_tmp = 704     (Holds temporary workspace for multiplication/subtraction)
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_modinv_inplace!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int,
    off_a::Int,
    u_len::Int
)::Tuple{Int, Bool}

    # Define our fixed-width scratch register segment boundary offsets
    off_r0  = 384
    off_r1  = 448
    off_s0  = 512
    off_s1  = 576
    off_q   = 640
    off_tmp = 704

    # Max sizes we ever need to clear: polynomials here are ≤ deg(u_RS) which is u_len-1.
    # We use u_len + 4 as a safe upper bound (quotient can briefly be one more degree).
    # This replaces the old `for i in 1:64` zeros which cleared 64 slots for ≤5 entries.
    clear_n = u_len + 4

    # WILLY-NILLY ASSERT: off_tmp=704 is the highest fixed register offset
    # this function uses; off_tmp + clear_n must stay inside poly_buf's 1024
    # slots. u_len is nominally <= 8 (residual degree), but this function
    # has no assert tying that assumption to the actual runtime value —
    # given this exact EEA loop has already had at least one silent-
    # corruption bug (see comment below re: destructive swap), check here.
    @assert off_tmp + clear_n <= length(scratch.poly_buf) "poly_modinv_inplace!: u_len=$u_len gives clear_n=$clear_n, off_tmp+clear_n=$(off_tmp+clear_n) exceeds poly_buf length $(length(scratch.poly_buf))"
    @assert len_a >= 1 "poly_modinv_inplace!: len_a=$len_a must be >= 1"
    @assert off_a + len_a <= length(scratch.poly_buf) "poly_modinv_inplace!: off_a=$off_a len_a=$len_a reads past poly_buf"

    # 1. Initialize r0 = modulus m(x) (from scratch.u_RS)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_r0 + i] = 0; end
    for i in 1:u_len
        @inbounds scratch.poly_buf[off_r0 + i] = scratch.u_RS[i]
    end
    len_r0 = u_len

    # 2. Initialize r1 = input a(x) (from off_a)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_r1 + i] = 0; end
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_r1 + i] = scratch.poly_buf[off_a + i]
    end
    len_r1 = len_a

    # 3. Initialize s0 = 0 (degree 0 polynomial)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_s0 + i] = 0; end
    len_s0 = 1 # sitting at 0

    # 4. Initialize s1 = 1 (degree 0 polynomial)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_s1 + i] = 0; end
    @inbounds scratch.poly_buf[off_s1 + 1] = 1
    len_s1 = 1

    # Main Extended Euclidean Algorithm Loop
    while true
        # Break condition: check if r1 logically becomes the zero polynomial.
        # len_r1 <= 0 is treated the same as the canonical zero-length-1
        # representation: it should never occur after the divmod fix below,
        # but breaking here instead of dividing by a degenerate length-0
        # "polynomial" is strictly safer.
        if len_r1 <= 1
            @inbounds if len_r1 <= 0 || scratch.poly_buf[off_r1 + 1] == 0
                break
            end
        end

        # --- step A: q, r = poly_divmod_poly(r0, r1) ---
        # We perform the long division pass of r0 by r1 inside a helper function.
        # It leaves the quotient at off_q and computes the remainder inside off_r0 in-place.
        len_q, len_r = poly_divmod_poly_inplace_registers!(scratch, len_r0, off_r0, len_r1, off_r1, off_q)

        # Swapping r0 and r1 bounds: r0 becomes the old r1, r1 becomes the new remainder r
        # The new remainder r currently lives in off_r0 (written in-place by
        # poly_divmod_poly_inplace_registers! above). Stash it in off_tmp
        # FIRST — off_tmp is unused until step B below — otherwise the very
        # next line (zeroing off_r0 to receive the old r1) destroys it before
        # it's ever copied into r1's segment, leaving both r0 and r1 holding
        # the old r1 value. That makes the GCD loop converge one step early
        # on a non-scalar "GCD" (the old r1), poly_modinv_inplace! returns
        # false on every call, and every walk step gets discarded.
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_tmp + i] = 0; end
        for i in 1:len_r
            @inbounds scratch.poly_buf[off_tmp + i] = scratch.poly_buf[off_r0 + i]
        end

        # Move coefficients of r1 into r0's segment space
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_r0 + i] = 0; end
        for i in 1:len_r1
            @inbounds scratch.poly_buf[off_r0 + i] = scratch.poly_buf[off_r1 + i]
        end
        len_r0 = len_r1

        # Move the newly computed remainder from off_tmp into r1's segment space
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_r1 + i] = 0; end
        for i in 1:len_r
            @inbounds scratch.poly_buf[off_r1 + i] = scratch.poly_buf[off_tmp + i]
        end
        len_r1 = len_r

        # --- step B: s_new = s0 - q * s1 ---
        # First compute tmp = q * s1 using our segment multiplication rule
        len_tmp = poly_mul_inplace_segment!(scratch, len_q, off_q, len_s1, off_s1, off_tmp)

        # Subtract: s_new = s0 - tmp. We write this into off_q's memory space to reuse it safely
        len_s_new = max(len_s0, len_tmp)
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_q + i] = 0; end
        for i in 1:len_s_new
            @inbounds s0_val = (i <= len_s0) ? scratch.poly_buf[off_s0 + i] : 0
            @inbounds tmp_val = (i <= len_tmp) ? scratch.poly_buf[off_tmp + i] : 0
            @inbounds scratch.poly_buf[off_q + i] = fp(s0_val - tmp_val)
        end
        # Trim trailing zeros of s_new
        while len_s_new > 1
            @inbounds if scratch.poly_buf[off_q + len_s_new] == 0
                len_s_new -= 1
            else
                break
            end
        end

        # Swapping s0 and s1 bounds: s0 becomes the old s1, s1 becomes the computed s_new
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_s0 + i] = 0; end
        for i in 1:len_s1
            @inbounds scratch.poly_buf[off_s0 + i] = scratch.poly_buf[off_s1 + i]
        end
        len_s0 = len_s1

        for i in 1:clear_n; @inbounds scratch.poly_buf[off_s1 + i] = 0; end
        for i in 1:len_s_new
            @inbounds scratch.poly_buf[off_s1 + i] = scratch.poly_buf[off_q + i]
        end
        len_s1 = len_s_new
    end

    # Post-Loop Invertibility Checks
    # The final GCD is sitting inside r0. It must be a non-zero scalar constant.
    if len_r0 != 1
        return (0, false)
    end
    @inbounds gcd_val = scratch.poly_buf[off_r0 + 1]
    if gcd_val == 0
        return (0, false)
    end

    # Scale s0 by the inverse of the constant GCD: inv_a = s0 * fpinv(gcd_val)
    inv_lc = fpinv(gcd_val)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_tmp + i] = 0; end
    for i in 1:len_s0
        @inbounds scratch.poly_buf[off_tmp + i] = fpmul(scratch.poly_buf[off_s0 + i], inv_lc)
    end
    
    # Trim trailing logical zeros if any were introduced
    len_inv = len_s0
    while len_inv > 1
        @inbounds if scratch.poly_buf[off_tmp + len_inv] == 0
            len_inv -= 1
        else
            break
        end
    end

    # Perform the final modular reduction pass: inv_a mod modulus m(x)
    # Reduces poly_buf[off_tmp + 1 : ...] mod scratch.u_RS, writing the output back inside off_tmp
    final_len = poly_reduce_mod_inplace!(scratch, off_tmp + len_inv, off_tmp, u_len)

    # Move the clean final inverse result into the requested user destination area (off_a)
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_a + i] = 0
    end
    for i in 1:final_len
        @inbounds scratch.poly_buf[off_a + i] = scratch.poly_buf[off_tmp + i]
    end

    return (final_len, true)
end

# ---------------------------------------------------------------------------
#  Helper: poly_divmod_poly_inplace_registers!(scratch, len_r0, off_r0, len_r1, off_r1, off_q)
#  Divides polynomial r0 by r1 using robust polynomial long division.
#  Overwrites the dividend r0 segment with the remainder, and writes quotient to off_q.
# ---------------------------------------------------------------------------
function poly_divmod_poly_inplace_registers!(
    scratch::ThreadScratchpad{<:Any},
    len_r0::Int, off_r0::Int,
    len_r1::Int, off_r1::Int,
    off_q::Int
)::Tuple{Int, Int}

    # 1. Clear out the quotient register window.
    #    Quotient degree = deg(r0) - deg(r1); for our polynomials that's at most u_len-1.
    #    Use len_r0 as the safe bound rather than a hardcoded 64.
    for i in 1:len_r0; @inbounds scratch.poly_buf[off_q + i] = 0; end
    
    # 2. Robustly sanitize the divisor length to ensure the leading coefficient is non-zero
    curr_len_r1 = len_r1
    while curr_len_r1 > 1
        @inbounds if scratch.poly_buf[off_r1 + curr_len_r1] == 0
            curr_len_r1 -= 1
        else
            break
        end
    end
    
    # 3. Robustly sanitize the dividend length
    curr_len_r0 = len_r0
    while curr_len_r0 > 1
        @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
            curr_len_r0 -= 1
        else
            break
        end
    end

    dr0 = curr_len_r0 - 1
    dr1 = curr_len_r1 - 1
    
    # If the divisor is the zero scalar, the inverse computation is degenerate
    @inbounds lc_r1 = scratch.poly_buf[off_r1 + curr_len_r1]
    if lc_r1 == 0
        return (1, curr_len_r0)
    end

    if dr0 < dr1
        # Quotient is 0, remainder is just r0 untouched
        return (1, curr_len_r0)
    end

    inv_lc_r1 = fpinv(lc_r1)
    
    # Main Division Loop
    while true
        deg_curr = (curr_len_r0 - 1)
        deg_curr < dr1 && break
        
        @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
            # Floor: curr_len_r0 == 1 means r0 has reduced to the zero
            # polynomial, which is represented as length 1 (value 0), not 0.
            # Without this check, the decrement below walks curr_len_r0 to 0
            # and then negative on subsequent iterations (deg_curr < dr1 no
            # longer reliably triggers once dr1 can itself go negative from a
            # length-0 divisor elsewhere), corrupting every later poly_buf
            # index derived from off_r0 + curr_len_r0.
            curr_len_r0 == 1 && break
            curr_len_r0 -= 1
            continue
        end
        
        # Scale term: c = lc(r0) / lc(r1)
        @inbounds c = fpmul(scratch.poly_buf[off_r0 + curr_len_r0], inv_lc_r1)
        shift = deg_curr - dr1
        
        # Record quotient term (1-indexed offset matching degree position)
        @inbounds scratch.poly_buf[off_q + shift + 1] = c
        
        # Subtract c * x^shift * r1 from r0
        for i in 1:curr_len_r1
            @inbounds r1_val = scratch.poly_buf[off_r1 + i]
            target_idx = off_r0 + i + shift
            @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(c, r1_val))
        end
        
        # Trim remainder window down to next non-zero term
        while curr_len_r0 > 1
            @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
                curr_len_r0 -= 1
            else
                break
            end
        end
    end

    # Determine structural logical length of computed quotient
    len_q = dr0 - dr1 + 1
    while len_q > 1
        @inbounds if scratch.poly_buf[off_q + len_q] == 0
            len_q -= 1
        else
            break
        end
    end

    return (len_q, curr_len_r0)
end

function poly_sub(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    len = max(length(a), length(b))
    c = zeros(Int, len)
    for i in 1:length(a); c[i] = fp(c[i] + a[i]); end
    for i in 1:length(b); c[i] = fp(c[i] - b[i]); end
    while length(c) > 1 && c[end] == 0; pop!(c); end
    return c
end

# Full polynomial division: returns (quotient, remainder) ascending.
function poly_divmod_poly(a::Vector{Int}, b::Vector{Int})::Tuple{Vector{Int}, Vector{Int}}
    r = copy(a)
    db = length(b) - 1
    deg_r = length(r) - 1
    if deg_r < db; return (Int[0], r); end
    q = zeros(Int, deg_r - db + 1)
    inv_lc_b = fpinv(b[end])
    while length(r) - 1 >= db
        if r[end] == 0; pop!(r); continue; end
        c = fpmul(r[end], inv_lc_b)
        shift = length(r) - length(b)
        q[shift+1] = fp(q[shift+1] + c)
        for i in 1:length(b)
            r[i+shift] = fp(r[i+shift] - fpmul(c, b[i]))
        end
        while length(r) > 1 && r[end] == 0; pop!(r); end
    end
    while length(q) > 1 && q[end] == 0; pop!(q); end
    return (q, r)
end

# ---------------------------------------------------------------------------
#  find_roots_and_points_inplace!(scratch, u_len)
#
#  Extracts affine split roots from the residual polynomial over F_p and
#  recovers their corresponding y-coordinates via y = -E(x)/Y(x).
#
#  Memory Configuration:
#    u_RS(x) read from      : scratch.u_RS[1 : u_len]
#    Original E, Y read from: scratch.ser_buf (stashed by build_N_inplace!)
#    Outputs written into   : scratch.roots_out[1 : scratch.roots_count[1]]
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  Helper: find_roots_and_points_inplace!(scratch, u_len, k) -> Nothing
#  Finds roots of the residual polynomial component u_RS and lifts them 
#  to full curve points (x, y) using the structural RR basis matching k anchors.
#
#  BATCH Y-INVERSION:
#  Recovering y = -E(x)/Y(x) for each root requires one fpinv per root.
#  At K=2 the residual is degree 3 (≤3 roots); at K=3 degree 4 (≤4 roots).
#  We collect all (val_E, val_Y) pairs first, then invert all non-zero val_Y
#  values with a single fpinv call using the same Montgomery batch-inversion
#  trick as fp_gauss_batch_invert_diag!, dropping r Fermat ladders to 1.
#
#  scratch.y_batch_x / y_batch_E / y_batch_Y hold the per-root intermediates.
# ---------------------------------------------------------------------------
# ============================================================
# 1. Root finding
# ============================================================

@inline function find_x_roots!(
    scratch,
    u_len::Int,
    ::Val{K}
) where K
    scratch.roots_count[1] = 0
    deg = u_len - 1

    @assert deg >= 0

    if deg == 0
        return 0
    end

    n = _find_x_roots_dispatch!(scratch, u_len)

    @assert n >= 0
    @assert n <= length(scratch.y_batch_x)

    return n
end


@inline function _find_x_roots_dispatch!(scratch, u_len::Int)
    deg = u_len - 1

    if deg == 2
        _pt_rq_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
        n = _solve_quadratic_roots!(scratch)
        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_res_roots_quad += time_ns() - _pt_rq_t0
        end
        return n
    else
        _pt_ro_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
        n = _solve_oscar_roots!(scratch, u_len)
        if PHI_TIMING_ENABLED[]
            phi_timing_stats().ns_res_roots_oscar += time_ns() - _pt_ro_t0
        end
        return n
    end
end


@inline function _solve_quadratic_roots!(scratch)
    @inbounds c0 = scratch.u_RS[1]
    @inbounds c1 = scratch.u_RS[2]

    disc = fp(fpmul(c1, c1) - 4 * c0)
    sq = sqrt_fp_hot(disc)

    if sq < 0
        return 0
    end

    # FIX: scratch.small_inv[s] is stored in BACKEND (Montgomery) representation
    # (see init_scratch_caches!: small_inv[s] = to_repr(backend, fpinv(s))).
    # Everywhere else in this function (c0, c1, sq, and the plain `fpmul` used
    # throughout) operates in RAW representation — the same convention as
    # scratch.u_RS/coeffs_out established after the phi_to_EY!/build_N_inplace!
    # fix. Using scratch.small_inv[2] directly with the plain (non-backend)
    # fpmul mixes a Montgomery-form operand into a raw-representation multiply
    # — identical bug class to the earlier binom_scratch[1]/small_inv[s] issue
    # in monomial_series_coeffs!. Use the raw inverse of 2 instead; this
    # function has no backend argument to convert with, so recompute directly
    # rather than threading backend through just for this one call.
    inv2 = fpinv(2)

    x1 = fpmul(fp(-c1 + sq), inv2)
    x2 = fpmul(fp(-c1 - sq), inv2)

    @inbounds scratch.y_batch_x[1] = x1
    @inbounds scratch.y_batch_x[2] = x2

    return 2
end


@inline function _solve_oscar_roots!(scratch, u_len::Int)
    Fp = scratch.oscar_Fp[]::FqField
    Rx = scratch.oscar_Rx[]::FqPolyRing

    coeff_buf = scratch.oscar_coeff_buf[]::Vector{FqFieldElem}

    @assert length(coeff_buf) >= u_len

    @inbounds for i in 1:u_len
        coeff_buf[i] = Fp(scratch.u_RS[i])
    end

    f_oscar = Rx(coeff_buf[1:u_len])
    rs = roots(f_oscar)

    # UPSTREAM ASSERT (polynomial construction sanity): confirm f_oscar
    # actually came out as a degree-(u_len-1) polynomial, not silently
    # something else. Two concrete ways this could go wrong even though
    # Rx(...) "succeeds": (a) a future edit reintroduces a SubArray/view
    # or otherwise-wrong-shaped argument that Nemo happens to accept via
    # some other method overload instead of erroring like the SubArray
    # case did; (b) coeff_buf[u_len] (the leading coefficient) is zero
    # mod p, in which case Nemo normalizes the polynomial and degree(f_oscar)
    # comes back LOWER than u_len-1 — silently desyncing this function's
    # polynomial from the "degree u_len-1" assumption the caller's n_len
    # bookkeeping is built on. Catching that here, right after
    # construction, is more actionable than letting it surface as a
    # root-count mismatch in the loop below (which only checks an upper
    # bound, not that the count matches what a genuine degree-(u_len-1)
    # polynomial should produce).
    @assert degree(f_oscar) == u_len - 1 "_solve_oscar_roots!: f_oscar has degree $(degree(f_oscar)), expected u_len-1=$(u_len-1) — either coeff_buf[$u_len] (the leading coefficient) is zero mod p and Nemo normalized the polynomial down, or Rx(coeff_buf[1:u_len]) did not build the polynomial this function assumes it built. u_RS(1:$u_len)=$(scratch.u_RS[1:u_len])"

    # CRITICAL BOUNDS ASSERT: scratch.y_batch_x is a fixed-size MVector{N2}
    # (N2 = K+2, at most 8 for K up to 6). A degree-(u_len-1) polynomial has
    # at most u_len-1 roots, which should never exceed N2 given how n_len is
    # derived upstream — but every upstream degree computation in this call
    # chain (build_N_inplace!, the divmod pipeline) is only now running on
    # genuinely nonzero data for the first time. Assert explicitly here
    # rather than silently indexing past y_batch_x's end if any of those
    # upstream degree invariants turn out to be violated.
    n = 0
    for r in rs
        n += 1
        @assert n <= length(scratch.y_batch_x) "_solve_oscar_roots!: root count n=$n exceeds y_batch_x capacity ($(length(scratch.y_batch_x))) for u_len=$u_len (degree $(u_len-1)) — degree/root-count invariant violated upstream."
        @inbounds scratch.y_batch_x[n] = Int(lift(ZZ, r))
    end

    return n
end


# ============================================================
# 2. Evaluate E(x), Y(x)
# ============================================================

@inline function evaluate_candidates!(
    scratch,
    n_cands::Int,
    K::Int
)
    basis = rr_basis_cached(K + 3)

    max_pow = _compute_max_pow(basis)
    norm_x, norm_y = basis[K + 3]

    @assert max_pow >= 0
    # WILLY-NILLY ASSERT: y_batch_x/E/Y are MVector{N2,Int} with N2=K+2 slots.
    # n_cands comes from root-finding on the residual polynomial; if its
    # degree ever exceeds N2 (e.g. a bug upstream in degree bookkeeping,
    # or simply this fixed-N2 assumption not covering some K), this loop's
    # @inbounds writes below in _evaluate_single_candidate! would silently
    # overrun the stack-allocated MVector.
    @assert n_cands <= length(scratch.y_batch_x) "evaluate_candidates!: n_cands=$n_cands exceeds y_batch_x capacity $(length(scratch.y_batch_x)) (K=$K)"
    @assert max_pow + 1 <= length(scratch.pxpow_buf) "evaluate_candidates!: max_pow=$max_pow needs pxpow_buf length >= $(max_pow+1), have $(length(scratch.pxpow_buf))"

    for ci in 1:n_cands
        _evaluate_single_candidate!(
            scratch, ci, basis, max_pow, norm_x, norm_y
        )
    end
end


@inline function _compute_max_pow(basis)
    m = 0
    @inbounds for i in eachindex(basis)
        p, _ = basis[i]
        if p > m
            m = p
        end
    end
    return m
end


@inline function _evaluate_single_candidate!(
    scratch,
    ci::Int,
    basis,
    max_pow::Int,
    norm_x::Int,
    norm_y::Int
)
    @inbounds x = scratch.y_batch_x[ci]

    scratch.pxpow_buf[1] = 1
    for e in 1:max_pow
        scratch.pxpow_buf[e + 1] =
            fpmul(scratch.pxpow_buf[e], x)
    end

    val_E = 0
    val_Y = 0

    nb = length(basis)

    @inbounds for idx in 1:(nb - 1)
        coeff = scratch.coeffs_out[idx]
        coeff == 0 && continue

        px, py = basis[idx]
        term = scratch.pxpow_buf[px + 1]
        scaled = fpmul(coeff, term)

        if py == 0
            val_E = fp(val_E + scaled)
        else
            val_Y = fp(val_Y + scaled)
        end
    end

    norm_term = scratch.pxpow_buf[norm_x + 1]
    if norm_y == 0
        val_E = fp(val_E + norm_term)
    else
        val_Y = fp(val_Y + norm_term)
    end

    @inbounds scratch.y_batch_E[ci] = val_E
    @inbounds scratch.y_batch_Y[ci] = val_Y

    # IMPORTANT invariant
    @assert typeof(val_E) == typeof(val_Y)
end


# ============================================================
# 3. Filter valid roots
# ============================================================

@inline function compact_valid_roots!(
    scratch,
    n_cands::Int
)
    n_valid = 0

    for i in 1:n_cands
        @inbounds yv = scratch.y_batch_Y[i]

        if yv != 0
            n_valid += 1

            if n_valid != i
                @inbounds begin
                    scratch.y_batch_x[n_valid] = scratch.y_batch_x[i]
                    scratch.y_batch_E[n_valid] = scratch.y_batch_E[i]
                    scratch.y_batch_Y[n_valid] = yv
                end
            end
        end
    end

    @assert n_valid <= n_cands
    return n_valid
end


# ============================================================
# 4. Batch inversion + reconstruction
# ============================================================

@inline function solve_roots_from_batches!(
    scratch,
    n_valid::Int
)
    if n_valid == 0
        return 0
    end

    # WILLY-NILLY ASSERT: roots_out is a fixed length-8 Vector (see
    # ThreadScratchpad{K}() constructor) regardless of K. n_valid comes from
    # compact_valid_roots!, ultimately bounded by the residual polynomial's
    # degree — if that ever exceeds 8 for some K, the @inbounds-free but
    # unchecked writes below (scratch.roots_out[n_out] = ...) would throw a
    # normal BoundsError at best, or silently corrupt if this ever gets
    # wrapped in @inbounds later. Check explicitly, loudly, here.
    @assert n_valid <= length(scratch.roots_out) "solve_roots_from_batches!: n_valid=$n_valid exceeds roots_out's fixed capacity $(length(scratch.roots_out))"
    @assert n_valid <= length(scratch.xi_buf) "solve_roots_from_batches!: n_valid=$n_valid exceeds xi_buf length $(length(scratch.xi_buf)) (used here for prefix products)"

    if n_valid == 1
        val_E = scratch.y_batch_E[1]
        val_Y = scratch.y_batch_Y[1]

        @assert val_Y != 0

        y = fpmul(fp(-val_E), fpinv(val_Y))

        scratch.roots_out[1] = (scratch.y_batch_x[1], y)
        scratch.roots_count[1] = 1
        return 1
    end

    # prefix products
    scratch.xi_buf[1] = scratch.y_batch_Y[1]

    for i in 2:n_valid
        scratch.xi_buf[i] =
            fpmul(scratch.xi_buf[i - 1], scratch.y_batch_Y[i])
    end

    running = fpinv(scratch.xi_buf[n_valid])

    n_out = 0

    for i in n_valid:-1:2
        inv_i = fpmul(running, scratch.xi_buf[i - 1])
        running = fpmul(running, scratch.y_batch_Y[i])

        y = fpmul(fp(-scratch.y_batch_E[i]), inv_i)

        n_out += 1
        scratch.roots_out[n_out] = (scratch.y_batch_x[i], y)
    end

    y = fpmul(fp(-scratch.y_batch_E[1]), running)
    n_out += 1
    scratch.roots_out[n_out] = (scratch.y_batch_x[1], y)

    scratch.roots_count[1] = n_out

    @assert n_out == n_valid

    return n_out
end


# ============================================================
# 5. Top-level orchestration
# ============================================================

function find_roots_and_points_inplace!(
    scratch,
    u_len::Int,
    ::Val{K}
) where K

    n_cands = find_x_roots!(scratch, u_len, Val(K))

    if n_cands == 0
        scratch.roots_count[1] = 0
        return nothing
    end

    evaluate_candidates!(scratch, n_cands, K)

    n_valid = compact_valid_roots!(scratch, n_cands)

    solve_roots_from_batches!(scratch, n_valid)

    return nothing
end


# ---------------------------------------------------------------------------

#  Helper: recover_y_from_phi_inplace(scratch, x, k) -> Union{Int, Nothing}
#  Correctly isolates and evaluates E(x) and Y(x) mod p at a root x by 
#  unrolling the explicit Riemann-Roch basis structure.
#  
#  φ(x,y) = E(x) + y * Y(x) == 0  =>  y = -E(x) / Y(x)
# ---------------------------------------------------------------------------
function recover_y_from_phi_inplace(scratch::ThreadScratchpad{K}, x::Int, ::Val{K} = Val(K))::Int where K
    nb = K + 3  # compile-time constant
    # Retrieve the canonical monomial basis vector (poles sorted: x^i or x^i * y)
    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    # Precompute x^0, x^1, ..., x^(max_pow) in one ascending pass.
    # Max x-power in basis grows with K_MAX (e.g. K_MAX=3 → nb=6, basis:
    # 1,x,x²,y,x³,xy, max x-power 3); scales per rr_basis, not a fixed bound.
    # Uses pxpow_buf (length 32) from scratch — borrowing it here; it's not live
    # during root recovery (find_roots_and_points calls us after residual is done).
    max_pow = 0
    for idx in 1:nb
        @inbounds pi, _ = basis[idx]
        pi > max_pow && (max_pow = pi)
    end
    @assert max_pow + 1 <= length(scratch.pxpow_buf) "recover_y_from_phi_inplace: max_pow=$max_pow needs pxpow_buf length >= $(max_pow+1), have $(length(scratch.pxpow_buf))"
    scratch.pxpow_buf[1] = 1
    for e in 1:max_pow
        @inbounds scratch.pxpow_buf[e+1] = fpmul(scratch.pxpow_buf[e], x)
    end

    val_E = 0
    val_Y = 0

    # 1. Evaluate the linear combination of the first (nb - 1) solved coefficients
    for idx in 1:(nb - 1)
        @inbounds coeff = scratch.coeffs_out[idx]
        coeff == 0 && continue
        
        @inbounds pow_x, pow_y = basis[idx]
        @inbounds term = scratch.pxpow_buf[pow_x + 1]
        scaled_term = fpmul(coeff, term)

        if pow_y == 0
            val_E = fp(val_E + scaled_term)
        else
            val_Y = fp(val_Y + scaled_term)
        end
    end

    # 2. Add the contribution of the highest pole monomial (monic, coefficient is 1)
    @inbounds norm_x, norm_y = basis[nb]
    @inbounds norm_term = scratch.pxpow_buf[norm_x + 1]

    if norm_y == 0
        val_E = fp(val_E + norm_term)
    else
        val_Y = fp(val_Y + norm_term)
    end

    # Handle singular/tangent cases where Y(x) evaluates to 0
    val_Y == 0 && return SQRT_FP_NONSQUARE   # sentinel: no valid y

    # y = -E(x) / Y(x) mod p
    return fpmul(fp(-val_E), fpinv(val_Y))
end

# ---------------------------------------------------------------------------
#  Helper: poly_eval_fp_inplace(scratch, offset, len, x) -> Int
# ---------------------------------------------------------------------------
function poly_eval_fp_inplace(scratch::ThreadScratchpad{<:Any}, offset::Int, len::Int, x::Int)::Int
    len == 0 && return 0
    @inbounds val = scratch.poly_buf[offset + len]
    for i in (len - 1):-1:1
        @inbounds val = fp(scratch.poly_buf[offset + i] + fpmul(val, x))
    end
    return val
end

# ---------------------------------------------------------------------------
#  Helper: poly_divmod_linear_inplace_segment!(scratch, offset, len, r)
#  Horner linear synthetic division working directly inside an array segment.
# ---------------------------------------------------------------------------
function poly_divmod_linear_inplace_segment!(
    scratch::ThreadScratchpad{<:Any},
    offset::Int,
    n_len::Int,
    r::Int
)::Tuple{Int, Int}
    @inbounds rem_val = scratch.poly_buf[offset + n_len]
    @inbounds scratch.poly_buf[offset + n_len] = 0

    for i in (n_len - 1):-1:2
        @inbounds next_rem = fp(scratch.poly_buf[offset + i] + fpmul(rem_val, r))
        @inbounds scratch.poly_buf[offset + i] = rem_val
        rem_val = next_rem
    end
    
    @inbounds final_rem = fp(scratch.poly_buf[offset + 1] + fpmul(rem_val, r))
    @inbounds scratch.poly_buf[offset + 1] = rem_val

    new_len = n_len - 1
    while new_len > 1
        @inbounds if scratch.poly_buf[offset + new_len] == 0
            new_len -= 1
        else
            break
        end
    end
    return (new_len, final_rem)
end


function poly_eval_fp(coeffs::Vector{Int}, x::Int)::Int
    isempty(coeffs) && return 0
    r = coeffs[end]
    for i in length(coeffs)-1:-1:1
        r = fp(fpmul(r, x) + coeffs[i])
    end
    return r
end

function recover_y_from_phi(E::Vector{Int}, Y::Vector{Int}, x::Int)::Union{Int,Nothing}
    ex = poly_eval_fp(E, x)
    yx = poly_eval_fp(Y, x)
    if yx == 0
        # φ = E(x) at this point — if E(x) ≠ 0 then not a zero of φ
        ex == 0 || return nothing
        # Degenerate: φ vanishes regardless of y; return nothing (skip)
        return nothing
    end
    # y = -E(x) / Y(x)
    return fpmul(fp(-ex), fpinv(yx))
end

# Vector-dispatch shim for step_phi_k!: converts anchors (a Vector or MVector
# whose length may exceed K, e.g. the K_MAX-sized cur_anchors buffer shared
# across all round-robin tuple lengths) into a NTuple{K,...} so the hot path
# above gets a compile-time K, reading only the first K entries.  ntuple with
# Val(K) is zero-cost — K is a type parameter of `scratch`, so the caller
# selects K by choosing which ThreadScratchpad{K} to pass in (see
# step_phi_dispatch!, which picks the right one for the current round-robin
# tuple length at runtime).
@inline function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::Vector{NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K
    # WILLY-NILLY ASSERT: comment above says anchors's length "may exceed K"
    # (K_MAX-sized shared buffer) — but never checks it's at least K.
    @assert length(anchors) >= K "step_phi_k! (Vector shim): anchors has length $(length(anchors)) < K=$K, ntuple slice would read past the end"
    # Convert to NTuple{K,...} — zero allocation, compiler inlines the ntuple.
    anc_tup = ntuple(i -> anchors[i], Val(K))
    step_phi_k!(scratch, anc_tup, u0, u1, v0, v1; backend=backend)
end

@inline function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::MVector{<:Any, NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K
    @assert length(anchors) >= K "step_phi_k! (MVector shim): anchors has length $(length(anchors)) < K=$K, ntuple slice would read past the end"
    # Convert MVector to NTuple{K,...} — zero allocation, compiler inlines the ntuple.
    anc_tup = ntuple(i -> anchors[i], Val(K))
    step_phi_k!(scratch, anc_tup, u0, u1, v0, v1; backend=backend)
end


# ---------------------------------------------------------------------------
#  Compatibility shim:  build_phi_mumford_general(anchors, u0, u1, v0, v1)
#
#  Wraps the above for the k=1 case, returning (a, b, c, 1) as before.
#  For k=1 the basis is {1, x, x², y} and coefficients are (c, b, a, 1).
# ---------------------------------------------------------------------------
function build_phi_mumford_general(px::Int, py::Int,
                                    u0::Int, u1::Int,
                                    v0::Int, v1::Int)::Union{NTuple{4,Int}, Nothing}
    coeffs = build_phi_general([(px, py)], u0, u1, v0, v1)
    coeffs === nothing && return nothing
    # coeffs = [c_1, c_x, c_x2, 1] in basis order (1, x, x², y)
    # = (c, b, a, 1) in original notation
    return (coeffs[3], coeffs[2], coeffs[1], 1)
end

# ---------------------------------------------------------------------------
#  phi_residual_mumford_general — k=1 wrapper matching original return type.
#
#  Returns (R, S, RS_mumford) with the same sentinel conventions as the
#  original phi_residual_mumford.
# ---------------------------------------------------------------------------
function phi_residual_mumford_general(a::Int, b::Int, c::Int,
                                       px::Int,
                                       u0::Int, u1::Int
    )::Tuple{NTuple{2,Int}, NTuple{2,Int}, NTuple{4,Int}}

    # Reconstruct φ from (a,b,c,1): basis = {1,x,x²,y}, coeffs = [c,b,a,1]
    basis  = rr_basis(4)
    coeffs = Int[c, b, a, 1]

    # We need E and Y to call the general residual
    E = Int[c, b, a]      # E(x) = c + b*x + a*x²
    Y = Int[1]             # Y(x) = 1  (the y coefficient)

    N = build_N(E, Y)

    # Divide by (x - px)
    q, rem = poly_divmod_linear(N, px)
    rem != 0 && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)
    N = q

    # Divide by u(x) = x² + u1*x + u0
    q2, r0, r1 = poly_divmod_monic_deg2(N, u1, u0)
    (r0 != 0 || r1 != 0) && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)
    u_RS = q2   # should be degree 2: [c0, c1, 1]

    length(u_RS) != 3 && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)

    c0_rs = u_RS[1]; c1_rs = u_RS[2]
    # v_RS(x) = -(a*x² + b*x + c) mod u_RS; since y-coeff is 1:
    v1_rs = fp(fpmul(a, c1_rs) - b)
    v0_rs = fp(fpmul(a, c0_rs) - c)

    mumford_key = (c0_rs, c1_rs, v0_rs, v1_rs)

    disc = fp(fpmul(c1_rs, c1_rs) - 4*c0_rs)
    sq   = sqrt_fp_hot(disc)

    if sq < 0
        return (SENTINEL_PT, SENTINEL_PT, mumford_key)
    end

    inv2 = fpinv(2)
    xR   = fpmul(fp(-c1_rs + sq), inv2)
    xS   = fpmul(fp(-c1_rs - sq), inv2)

    yR = fp(-fpmul(a, fpmul(xR,xR)) - fpmul(b,xR) - c)
    yS = fp(-fpmul(a, fpmul(xS,xS)) - fpmul(b,xS) - c)

    return ((xR, yR), (xS, yS), mumford_key)
end

# ---------------------------------------------------------------------------
#  High-level API for multi-anchor walks (Zero-Allocation Edition)
#
#  step_phi_k!(scratch, anchors, u0, u1, v0, v1) -> Bool
#
#  Entry point for a walk step with k anchors. `anchors` is a length-k
#  vector of (px,py) points — repeated entries encode higher vanishing order.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing. 
#  Mutates internal fields of `scratch` on a successful step (`true`).
#  Returns `false` if φ cannot be constructed or if the step fails.
# ---------------------------------------------------------------------------
# Tuple-dispatch entry point (hot path).
# anchors::NTuple{K,NTuple{2,Int}} — compile-time K from ThreadScratchpad{K}.
# The Vector-accepting overload below converts and calls this one.
function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::NTuple{K,NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K

    # ------------------------------------------------------------
    # bookkeeping
    # ------------------------------------------------------------
    PHI_TIMING_ENABLED[] && (phi_timing_stats().n_calls += 1)

    success_build = build_phi_general!(scratch, anchors, u0, u1, v0, v1; backend=backend)
    !success_build && return false

    k  = K
    nb = K + 3

    @assert k == K && k == length(anchors) "step_phi_k!: k=$k, K=$K, length(anchors)=$(length(anchors)) must all agree"

    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    @assert length(scratch.coeffs_out) ≥ nb
    @assert length(basis) == nb

    # ------------------------------------------------------------
    # PHI VANISHING CHECK (ANCHORS)
    # ------------------------------------------------------------
    #
    # ROOT-CAUSE FIX: this previously called eval_monomial(i,j,px,py,...),
    # which evaluates x^i*y^j via reduce_monomial_mod_D_cached — i.e. by
    # reducing x^i MOD THE WALK STEP'S DIVISOR u(x) (cached into
    # scratch.x_pow_mod_u_r0/r1 by build_phi_general!'s call to
    # build_xmodu_cache!) and only THEN combining with py. That reduction
    # is mathematically equivalent to a direct evaluation of x^i at px
    # ONLY WHEN px IS A ROOT OF u(x) — true for the SECONDARY CONSISTENCY
    # CHECK below (which deliberately evaluates phi at u(x)'s roots via
    # (v0,v1)), but false here: this check verifies phi at the walk's
    # ANCHOR points, which have no required relationship to whatever
    # divisor u(x) the walk happens to be stepping through right now.
    # eval_monomial's own doc comment ("evaluate ... at an affine point")
    # promises unconditional evaluation but the implementation silently
    # assumes the mod-u(x) precondition — a latent bug that was invisible
    # for K=1 (where this pipeline was never actually reached before the
    # earlier coeffs_out-never-populated bug was fixed) and only surfaced
    # now that K=2 anchors are real, non-degenerate points independent of
    # the current u(x).
    #
    # Fixed by evaluating directly: plain powermod against p, combined
    # with coeffs_out (already in plain, non-backend representation) —
    # exactly mirroring build_phi_general!'s own self-verification loop
    # (added earlier), which uses this same direct formula and passes.
    let
        for idx in 1:k
            @inbounds (px, py) = anchors[idx]

            phi_val = 0

            for col in 1:nb
                @inbounds coeff = scratch.coeffs_out[col]
                coeff == 0 && continue

                @inbounds (i, j) = basis[col]

                val = j == 0 ? powermod(px, i, p) : fpmul(powermod(px, i, p), py)

                phi_val = fp(phi_val + fpmul(coeff, val))
            end

            # DEFENSIVE ASSERT: was a bare `@assert phi_val == 0` with no
            # message — meaning a failure here gave no way to tell whether
            # the failing anchor was a repeated/tangent point (pointing at
            # the m=2 machinery) or an ordinary distinct point (pointing at
            # something wrong in plain K>1 evaluation that predates and is
            # unrelated to the tangency work). Dump everything needed to
            # distinguish those two cases, plus the actual coeffs_out
            # (basis-position-indexed) and basis itself, so a failure here
            # is immediately actionable instead of requiring another
            # instrumentation round-trip.
            is_repeat_anchor = false
            @inbounds for other in 1:k
                other != idx && anchors[other] == anchors[idx] && (is_repeat_anchor = true; break)
            end
            @assert phi_val == 0 "step_phi_k!: PHI VANISHING CHECK failed at anchor idx=$idx (px,py)=($px,$py), k=$k, is_repeat_anchor=$is_repeat_anchor — phi_val=$phi_val (expected 0). coeffs_out(basis-indexed)=$(scratch.coeffs_out[1:nb]), basis=$basis. If is_repeat_anchor=false, this is a PLAIN (non-tangent) evaluation failure — unrelated to the m=2 tangency machinery (none of compute_branch_series!'s tangent-slope assert, build_phi_general!'s derivative-row cross-check, or step_phi_k!'s own tangency-derivative check fired before this, which only happens if this anchor never went through the m=2 path at all). If is_repeat_anchor=true, check those three tangency-specific assert sites' output first — this one alone doesn't say which column is wrong."
        end
    end

    # ------------------------------------------------------------
    # PHI TANGENCY CHECK (repeated anchors only):
    # for any anchor point that occurs more than once in this tuple,
    # independently verify d/dt[phi(px+t, py+y'*t)]|_{t=0} == 0, using the
    # ACTUAL SOLVED coefficients (coeffs_out) and a completely fresh
    # computation of f'(px) and y' — deliberately not reusing scratch.out_y
    # or scratch.f_tay, since by this point in step_phi_k! those scratch
    # buffers reflect whichever anchor build_phi_general!'s loop processed
    # LAST, not necessarily the repeated anchor being checked here. This is
    # the definitive end-to-end check for the m=2 tangency implementation:
    # if the plain PHI VANISHING CHECK above passes but THIS fails, the bug
    # is specifically in the derivative machinery (fill_f_tay!,
    # branch_series!'s m=2 path, or monomial_series_coeffs!'s per-column
    # derivative), not in ordinary evaluation or row/column bookkeeping.
    # ------------------------------------------------------------
    let
        for idx in 1:k
            @inbounds (px, py) = anchors[idx]

            is_repeat = false
            @inbounds for other in 1:k
                other != idx && anchors[other] == anchors[idx] && (is_repeat = true; break)
            end
            !is_repeat && continue

            @assert py != 0 "step_phi_k!: tangency check hit a repeated Weierstrass anchor ($px,$py) — this should have been rejected upstream by _anchor_tuple_valid"

            # Fresh f'(px) via Horner, in PLAIN (non-backend) representation
            # — coeffs_out and eval_monomial both operate in plain repr, so
            # this check must too, matching the PHI VANISHING CHECK above.
            deg = length(F_POLY_DESC) - 1
            # F_POLY_DESC is stored in backend repr (see
            # init_phi_general_caches!); convert each coefficient back to
            # plain repr before using it in this plain-repr computation.
            fprime_px = 0
            @inbounds for pidx in 1:deg
                power = deg - pidx + 1
                power == 0 && break
                c_plain = from_repr(backend, F_POLY_DESC[pidx])
                fprime_px = fp(fpmul(fprime_px, px) + fpmul(power, c_plain))
            end
            yprime = fpmul(fprime_px, fpinv(fp(2 * py)))

            # d/dt[phi(px+t, py+y'*t)]|_{t=0} = sum_col coeff[col] * d/dt[monomial_col(px+t,py+y'*t)]|_0
            #   monomial (i,0): d/dt[(px+t)^i]|_0 = i*px^(i-1)
            #   monomial (i,1): d/dt[(px+t)^i*(py+y'*t)]|_0 = i*px^(i-1)*py + px^i*y'
            dphi_val = 0
            for col in 1:nb
                @inbounds coeff = scratch.coeffs_out[col]
                coeff == 0 && continue
                @inbounds (i, j) = basis[col]

                if j == 0
                    i == 0 && continue   # constant column: derivative 0
                    dmono = fpmul(i, powermod(px, i - 1, p))
                else
                    term1 = i == 0 ? 0 : fpmul(fpmul(i, powermod(px, i - 1, p)), py)
                    term2 = fpmul(powermod(px, i, p), yprime)
                    dmono = fp(term1 + term2)
                end

                dphi_val = fp(dphi_val + fpmul(coeff, dmono))
            end

            @assert dphi_val == 0 "step_phi_k!: TANGENCY DERIVATIVE CHECK FAILED at repeated anchor (px,py)=($px,$py) — d/dt[phi] at t=0 = $dphi_val, expected 0 (plain vanishing DID pass, so this isolates the bug to the derivative/tangency machinery specifically: fill_f_tay!'s sign or value, branch_series!'s m=2 combination of f_tay with Fy_inv, or monomial_series_coeffs!'s per-column t^1 coefficient — check compute_branch_series!'s own tangent-slope assert output from THIS SAME anchor earlier in the log, and the per-column derivative-row cross-check in build_phi_general!'s anchor loop, to narrow further)."
        end
    end

    # ------------------------------------------------------------
    # SECONDARY CONSISTENCY CHECK:
    # phi(x, v(x)) mod u(x)
    # ------------------------------------------------------------
    let
        r0_acc = 0
        r1_acc = 0

        for col in 1:nb
            @inbounds coeff = scratch.coeffs_out[col]
            coeff == 0 && continue

            @inbounds (i, j) = basis[col]

            rr0, rr1 = reduce_monomial_mod_D_cached(
                i, j,
                to_repr(backend, v0),
                to_repr(backend, v1),
                scratch,
                backend
            )

            r0_acc = fp(r0_acc + fpmul(coeff, from_repr(backend, rr0)))
            r1_acc = fp(r1_acc + fpmul(coeff, from_repr(backend, rr1)))
        end

        @assert r0_acc == 0
        @assert r1_acc == 0
    end

    # ------------------------------------------------------------
    # residual extraction
    # ------------------------------------------------------------
    _pt_resid_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
    success_residual = phi_residual_general!(scratch, basis, anchors, u0, u1)
    if PHI_TIMING_ENABLED[]
        phi_timing_stats().ns_residual += time_ns() - _pt_resid_t0
    end

    if !success_residual || scratch.u_RS_is_fail[1]
        return false
    end

    return true
end

# ---------------------------------------------------------------------------
#  step_phi_dispatch! — runtime-k entry point for the round-robin walk.
#
#  Once anchor tuple length k varies step-to-step (round-robin over
#  1..K_ceil rather than a single fixed K), the scratch buffer needed for
#  the general step_phi_k! path must vary with it too: ThreadScratchpad{K}
#  bakes K into every field size (A_mat is (K+2)x(K+2), seen_counts has K
#  slots, etc.), so one scratchpad instance can only ever serve one K.
#
#  The caller (phase2 worker) therefore holds a heterogeneous tuple
#  `scratch_by_k` with one concretely-typed ThreadScratchpad{k} per length
#  k = 1..K_ceil (built once at worker init via
#  `ntuple(k -> init_scratch_caches!(ThreadScratchpad{k}(), p), Val(K_ceil))`).
#  Indexing that tuple with a *runtime* k directly (`scratch_by_k[k_cur]`)
#  is type-unstable — its element type is a Union across all K, which the
#  compiler can't specialize away. Instead we dispatch through a manually
#  unrolled if/elseif chain built once via @generated from the tuple's
#  *type* (so its length adapts automatically if K_ceil/K_MAX changes —
#  no hand-editing needed here when the run's ceiling grows or shrinks).
#  Each branch below binds `scratch_by_k[$i]` with a literal index known at
#  generation time, so inside that branch the compiler sees a concrete
#  ThreadScratchpad{i} and step_phi_k! compiles monomorphically just as it
#  always did for the old fixed-K case — the runtime cost is exactly one
#  chain of integer comparisons (k_cur == 1, == 2, ...) to pick the branch,
#  which is negligible next to the φ-construction work each branch does.
#
#  Returns (success::Bool, scratch) so the caller can read roots_out /
#  u_RS / v_RS / coeffs_out etc. off the SAME scratch instance that was
#  actually used for this step, without a second runtime-k lookup.
# ---------------------------------------------------------------------------
#  NOTE ON `backend`: this used to be a bare @generated function with no
#  `backend` parameter at all, so every call silently fell through to
#  step_phi_k!'s own default (StandardArith(p)) no matter what the caller
#  wanted. Since step_phi_dispatch! is the ONLY call site phase2_worker
#  uses for k>=2 steps (see trial3_phase2.jl), that made MontgomeryArith
#  completely unreachable from the actual walk loop even though the
#  interior functions (build_phi_general!, fp_gauss!, etc.) were already
#  backend-parametrized. Fixed by splitting into a thin runtime wrapper
#  that accepts `backend` as an ordinary keyword and an inner @generated
#  function that forwards it into every unrolled branch — code generation
#  still only depends on the TYPE of scratch_by_k, so specialization is
#  unaffected; `backend` is just plumbed through as an extra positional arg.
function step_phi_dispatch!(
    scratch_by_k ::Tuple,
    k_cur        ::Int,
    anchors,
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)
    @assert k_cur >= 1 "step_phi_dispatch!: k_cur=$k_cur must be >= 1"
    @assert k_cur <= length(scratch_by_k) "step_phi_dispatch!: k_cur=$k_cur exceeds scratch_by_k length $(length(scratch_by_k))"
    return _step_phi_dispatch_gen!(scratch_by_k, k_cur, anchors, u0, u1, v0, v1, backend)
end

@generated function _step_phi_dispatch_gen!(
    scratch_by_k ::T,
    k_cur        ::Int,
    anchors,
    u0::Int, u1::Int, v0::Int, v1::Int,
    backend      ::FpArith
) where {T<:Tuple}
    n = length(T.parameters)
    ex = :(error("step_phi_dispatch!: k_cur=", k_cur, " out of range 1:", $n))
    for i in n:-1:1
        ex = quote
            if k_cur == $i
                (step_phi_k!(scratch_by_k[$i], anchors, u0, u1, v0, v1; backend=backend),
                 scratch_by_k[$i])
            else
                $ex
            end
        end
    end
    return ex
end
