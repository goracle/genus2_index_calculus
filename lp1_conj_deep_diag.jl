# =============================================================================
#  lp1_conj_deep_diag.jl  --  Entry point for LP1-conj deep diagnostics.
#
#  Includes the four sub-modules in dependency order, then defines the
#  top-level print_conj_deep_report dispatcher.
#
#  Sub-module layout
#  ─────────────────
#  lp1_conj_deep_diag_core.jl    — constants, ConjDeepStat struct + ctor,
#                                   merge_conj_deep_stats, recording helpers
#                                   (record_conj_deep_miss!, record_conj_deep_step!,
#                                   record_conj_deep_opcode!, record_d16_emission!),
#                                   math helpers (_gini, _hill_exponent,
#                                   _top_share, _deep_fp64, _deep_bucket)
#  lp1_conj_deep_diag_d1_d6.jl   — report sections D1 – D6  (_report_d1_d6)
#  lp1_conj_deep_diag_d7_d11.jl  — report sections D7 – D11 (_report_d7_d11)
#  lp1_conj_deep_diag_d12_d18.jl — report sections D12 – D18 (_report_d12_d18)
#  lp1_conj_deep_diag_d28.jl     — report section D28 (_report_d28): pre-
#                                   emission LP-aff anchor distribution at
#                                   lag-k
#  lp1_conj_deep_diag_d30.jl     — report section D30 (_report_d30): closure
#                                   FB-point geometric (x-coordinate)
#                                   short-range adjacency — circular mod-p
#                                   distance min(Δx,p-Δx) between the
#                                   closing and storing FB anchor points,
#                                   vs an exact circular-uniform null.
#                                   Coordinate-space analogue of D36 (tests
#                                   geometric adjacency directly rather than
#                                   relying on FB-array-index order as a
#                                   proxy for it).
#  lp1_conj_deep_diag_d32.jl     — report section D32 (_report_d32): LP1-conj
#                                   key recurrence-gap (store→close depth)
#                                   short-lag concentration vs geometric null
#  lp1_conj_deep_diag_d33.jl     — report section D33 (_report_d33): φ
#                                   a-coefficient residue bias against
#                                   small-prime uniform nulls, marginal +
#                                   joint (mod 3, mod 5) tables
#  lp1_conj_deep_diag_d34.jl     — report section D34 (_report_d34): x-bucket
#                                   smoothing-probability (draining hypothesis)
#  lp1_conj_deep_diag_d35.jl     — report section D35 (_report_d35): closure
#                                   difference-process concentration —
#                                   Rényi-2 effective support of Δα/Δβ
#                                   (combined_al/combined_be) vs ΔP proxy
#                                   (FB anchor x-difference), plus a
#                                   co-localization test between the two
#  lp1_conj_deep_diag_d36.jl     — report section D36 (_report_d36):
#                                   next_anchor() short-range autocorrelation
#                                   at closure — raw FB-index distance
#                                   |i0-prev_col| between the closing and
#                                   storing anchor cursors, vs a uniform-pair
#                                   null. Direct follow-up to D32's closing
#                                   pointer ("consider next_anchor()'s
#                                   short-range autocorrelation directly").
#                                   See D30 for the coordinate-space (rather
#                                   than index-space) version of this test.
#  lp1_conj_deep_diag_d29.jl     — report section D29 (_report_d29):
#                                   wide-lag burst-memory trackers — α mod-q
#                                   circular autocorrelation (phase-locking,
#                                   esp. q=7 per D33's χ²/dof spike), p_x
#                                   spatial autocorrelation (basin trapping)
#                                   over lags [500,5000], and rolling
#                                   (α mod q, p_x) mutual information
#                                   (dynamic steering) — direct follow-up to
#                                   the CIR-ACF burst result (τ* ≈ 4128).
#
#  Wiring (unchanged from the monolithic version)
#  ───────────────────────────────────────────────
#  1. include("lp1_conj_deep_diag.jl") in trial3_fixed.jl (already done).
#  2. Allocate one ConjDeepStat per thread alongside PhiBiasStat.
#  3a. Call record_conj_deep_miss!  from handle_1lp_conj! on every STORE.
#  3b. Call record_conj_deep_step! from handle_1lp_conj! on every CLOSE.
#  4. Call merge_conj_deep_stats + print_conj_deep_report from main2 after
#     the phase-2 phi bias report, passing the merged PhiBiasStat and the
#     conj snapshot dict.
# =============================================================================

include("lp1_conj_deep_diag_core.jl")
include("lp1_conj_deep_diag_d1_d6.jl")
include("lp1_conj_deep_diag_d7_d11.jl")
include("lp1_conj_deep_diag_d12_d18.jl")
include("lp1_conj_deep_diag_d19.jl")
include("lp1_conj_deep_diag_d20_d21.jl")
include("lp1_conj_deep_diag_d22_d24.jl")
include("lp1_conj_deep_diag_d25.jl")
include("lp1_conj_deep_diag_d26.jl")
include("lp1_conj_deep_diag_d27.jl")  # <-- Add this line to include the D27 sub-module
include("lp1_conj_deep_diag_d28.jl")
include("lp1_conj_deep_diag_d30.jl")  # D30 — closure FB-point geometric (x-coordinate) short-range adjacency
include("lp1_conj_deep_diag_d32.jl")  # D32 — LP1-conj key recurrence-gap concentration (short-lag focus)
include("lp1_conj_deep_diag_d33.jl")  # D33 — φ a-coefficient residue bias (small-prime modular structure)
include("lp1_conj_deep_diag_d34.jl")  # D34 — x-bucket smoothing-probability (draining hypothesis test)
include("lp1_conj_deep_diag_d35.jl")  # D35 — closure difference-process concentration (Δα/Δβ vs ΔP proxy)
include("lp1_conj_deep_diag_d36.jl")  # D36 — next_anchor() short-range autocorrelation (FB-index distance)
include("lp1_conj_deep_diag_d29.jl")  # D29 — wide-lag burst-memory trackers (α-ACF, p_x spatial ACF, α/p_x CCF)

# ---------------------------------------------------------------------------
#  print_conj_deep_report — top-level dispatcher.
#
#  Arguments:
#    phi_stat  — merged PhiBiasStat (arrivals, keys, bucket log)
#    deep_stat — merged ConjDeepStat (transition matrix, ancestry, D7–D17)
#    conj_snap — plain Dict or AbstractVector snapshot from precompute
#                (needed for D7; pass nothing to skip)
#    p         — field characteristic (for D13/D14/D15/D17/D18)
#    lsm_peers — optional LSM peer list (passed through to D7)
# ---------------------------------------------------------------------------
function print_conj_deep_report(phi_stat ::PhiBiasStat,
                                 deep_stat::ConjDeepStat;
                                 conj_snap::Union{Dict, AbstractVector, Nothing} = nothing,
                                 p        ::Int = 0,
                                 ell      ::Int = 0,
                                 lsm_peers::Union{Vector, Nothing} = nothing,
                                 fb_size  ::Int = 0,
                                 n_threads::Int = 1,
                                 fb       ::Union{Vector{NTuple{2,Int}}, Nothing} = nothing)

    arrivals  = phi_stat.lp1_conj_arrivals
    keys_u128 = phi_stat.lp1_conj_keys
    n_emit    = length(arrivals)

    @printf("\n══ LP1-conj deep diagnostics ════════════════════════════════════════\n")
    @printf("  Total LP1-conj emissions analyzed : %d\n", n_emit)
    n_emit == 0 && (@printf("  (no emissions — skipping all sections)\n\n"); return)

    # --- Chao1 Latent Cardinality Estimation ---
    # Tally observed frequencies from the emission keys
    key_counts = Dict{UInt128, Int}()
    for k in keys_u128
        key_counts[k] = get(key_counts, k, 0) + 1
    end

    s_obs = length(key_counts)
    f1 = 0
    f2 = 0
    for (k, count) in key_counts
        if count < 1
            throw(ArgumentError("Malformed state: key count cannot be less than 1."))
        end
        if count == 1
            f1 += 1
        elseif count == 2
            f2 += 1
        end
    end

    chao_predicted = _chao1_estimate(f1, f2, s_obs)

    @printf("  Unique keys observed (S_obs)      : %d\n", s_obs)
    @printf("  Singletons (f1) / Doubletons (f2) : %d / %d\n", f1, f2)
    if chao_predicted > s_obs * 100
        @printf("  Chao1 Latent Population Estimate  : >100x S_obs (Exploration is wide open)\n")
    else
        @printf("  Chao1 Latent Population Estimate  : %.2f total unique states predicted\n", chao_predicted)
    end
    @printf("---------------------------------------------------------------------\n")

    emit_bkt = [_deep_bucket(k) for k in keys_u128]   # Vector{Int}, 0-based

    _report_d1_d6(phi_stat, deep_stat, arrivals, keys_u128, emit_bkt, n_emit)
    _report_d7_d11(phi_stat, deep_stat, n_emit; conj_snap=conj_snap)
    _report_d12_d18(deep_stat; p=p, fb=fb)
    _report_d19(deep_stat; fb_size=fb_size)
    _report_d20_d21(deep_stat)
    _report_d22_d24(deep_stat; n_threads=n_threads)
    _report_d25(deep_stat, deep_stat.d12_store_alpha, deep_stat.d12_store_px, ell, p)
    _report_d26(deep_stat)
    _report_d27(deep_stat; ell=ell, p=p)  # <-- Add this line to run the D27 analysis
    _report_d28(deep_stat; p=p, ell=ell)
    _report_d30(deep_stat; p=p)
    _report_d32(deep_stat)
    _report_d33(deep_stat)
    _report_d34(deep_stat; p=p)
    _report_d35(deep_stat; p=p, ell=ell)
    _report_d36(deep_stat)
    _report_d29(deep_stat; p=p, ell=ell)

    @printf("\n== End LP1-conj deep diagnostics ====================================================\n")
    flush(stdout)
end
