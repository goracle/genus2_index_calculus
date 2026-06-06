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
                                 lsm_peers::Union{Vector, Nothing} = nothing,
                                 fb_size  ::Int = 0)

    arrivals  = phi_stat.lp1_conj_arrivals
    keys_u128 = phi_stat.lp1_conj_keys
    n_emit    = length(arrivals)

    @printf("\n══ LP1-conj deep diagnostics ════════════════════════════════════════\n")
    @printf("  Total LP1-conj emissions analyzed : %d\n", n_emit)
    n_emit == 0 && (@printf("  (no emissions — skipping all sections)\n\n"); return)

    emit_bkt = [_deep_bucket(k) for k in keys_u128]   # Vector{Int}, 0-based

    _report_d1_d6(phi_stat, deep_stat, arrivals, keys_u128, emit_bkt, n_emit)
    _report_d7_d11(phi_stat, deep_stat, n_emit; conj_snap=conj_snap)
    _report_d12_d18(deep_stat; p=p)
    _report_d19(deep_stat; fb_size=fb_size)

    @printf("\n== End LP1-conj deep diagnostics ====================================================\n")
    flush(stdout)
end
