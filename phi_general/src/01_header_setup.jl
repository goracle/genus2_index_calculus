# ==============================================================================
# 01_header_setup.jl
# Split fragment of trial3_phi_general.jl (lines 1-475 of original).
# NOT standalone-includable yet -- wiring/includes to be sorted out separately.
# ==============================================================================

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
const SENTINEL_PT      = (-1, -1)::NTuple{2,Int}
const SENTINEL_MUMFORD = (-1, -1, -1, -1)::NTuple{4,Int}
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

# compute_branch_series!'s tangent-slope identity check (2*py*y' == f'(px))
# independently re-derives f'(px) from F_POLY_DESC via its own Horner pass,
# duplicating the exact work fill_f_tay! just did, on EVERY m>=2 call —
# i.e. every anchor, every walk step, for the entire run. That duplication
# was deliberate while fill_f_tay!/branch_series! were under active
# development (see their bugfix comments) and is worth keeping available,
# but it should not tax every production run once both are trusted. Set
# JULIA_TRIAL3_BRANCH_SERIES_CHECK=1 to re-enable it for debugging; the
# cheap constant-term check (out_y[1] == py) in compute_branch_series!
# always runs regardless, since it costs one comparison, not a Horner pass.
const BRANCH_SERIES_TANGENT_CHECK = get(ENV, "JULIA_TRIAL3_BRANCH_SERIES_CHECK", "0") == "1"

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
