# =============================================================================
#  phi_bias_report_surfaces.jl  --  Report header, Surface 1–3, and Seq 1.
#
#  Called by print_phi_bias_report; not intended to be called directly.
#  Writes to stdout via @printf.
# =============================================================================

# ---------------------------------------------------------------------------
#  _report_header_and_surfaces! — print the preamble, Surface 1–3 sections,
#  and Seq 1 run-length KS test.  Returns (total, nb, n_split, n_nonspl).
# ---------------------------------------------------------------------------
function _report_header_and_surfaces!(stat::PhiBiasStat; p::Int = 0)
    total    = stat.total
    nb       = length(stat.split_hist)
    n_split  = sum(stat.split_hist)
    n_nonspl = sum(stat.nonsplit_hist)

    @printf("\n── φ a-parameter bias report ─────────────────────────────────────────\n")
    @printf("  valid phi steps recorded : %d\n", total)
    @printf("  split steps              : %d  (%.2f%% of recorded)\n",
            n_split, 100.0 * n_split / max(1, total))
    @printf("  non-split steps          : %d  (%.2f%%)\n",
            n_nonspl, 100.0 * n_nonspl / max(1, total))
    println()

    # --- Surface 3: a=0 slice ---
    @printf("  Surface 3 — a=0 slice:\n")
    @printf("    a=0 steps              : %d  (%.4f%% of recorded)\n",
            stat.a_zero, 100.0 * stat.a_zero / max(1, total))
    @printf("    a=0 split rate         : %.2f%%  (overall split: %.2f%%)\n",
            100.0 * stat.a_zero_split / max(1, stat.a_zero),
            100.0 * n_split / max(1, total))
    @printf("    a=0 FB-smooth rate     : %.2f%%  (of a=0 split steps)\n",
            100.0 * stat.a_zero_fb / max(1, stat.a_zero_split))
    println()

    # --- Surface 1: image collisions ---
    @printf("  Surface 1 — residual image collisions:\n")
    @printf("    (c₁,c₀) collisions     : %d  (%.4f%% of recorded)\n",
            stat.image_collisions, 100.0 * stat.image_collisions / max(1, total))
    @printf("    interpretation: if > 0, two distinct a-values from the same D\n")
    @printf("    produced identical residual Mumford pairs — algebraic thinness.\n")
    println()

    # --- Surface 2: discriminant bias (χ²/dof summary only) ---
    # Raw split/non-split χ² values dropped: consistently χ²/dof ≈ 1 (uniform)
    # by walk construction.  Only the ratio is printed; > 2.0 flags a real problem.
    @printf("  Surface 2 — discriminant bias (split histogram χ² test):\n")
    @printf("    histogram buckets      : %d  (each ~%s wide in 𝔽ₚ)\n",
            nb, p > 0 ? string(p ÷ nb) : "p/√p")
    if n_split > 0
        expected   = n_split / nb
        chi2_split = sum((x - expected)^2 / max(1.0, expected) for x in stat.split_hist)
        ratio      = chi2_split / max(1.0, Float64(nb - 1))
        flag       = ratio > 2.0 ? " ← NON-UNIFORM (investigate)" : " (consistent with uniform)"
        @printf("    split χ²/dof           : %.3f%s\n", ratio, flag)
    else
        @printf("    (no split steps recorded)\n")
    end
    # (non-split χ² and top-bucket table removed: always uniform, no signal)

    # --- Seq 1: Run-length distribution (compressed — always i.i.d. at this scale) ---
    # Full histogram rows removed: KS vs Geometric(1/2) is always consistent with
    # i.i.d. by construction (each φ-step is independently Bernoulli(≈1/2)).
    # Single summary line per series; only printed if KS ever exceeds 0.05.
    @printf("  Seq 1 — Run-length distribution (KS vs Geometric(1/2)):\n")
    for (label, hist) in (("split", stat.run_hist_split), ("non-split", stat.run_hist_nonsplit))
        n_runs = sum(hist)
        if n_runs >= 10
            ks_stat = 0.0; cumul = 0.0
            for k in 1:MAX_RUN_LEN
                cumul   += hist[k] / n_runs
                ks_stat  = max(ks_stat, abs(cumul - (1.0 - 0.5^k)))
            end
            mean_run = sum(k * hist[k] for k in 1:MAX_RUN_LEN) / n_runs
            flag = ks_stat > 0.05 ? (mean_run > 2.0 ? " ← LONG RUNS (positive autocorr)" :
                                                        " ← SHORT RUNS (anti-corr)") :
                                    " (consistent with i.i.d.)"
            @printf("    %-9s runs: n=%d  mean_len=%.2f  KS=%.4f%s\n",
                    label, n_runs, mean_run, ks_stat, flag)
        else
            @printf("    %-9s runs: n=%d  (too few)\n", label, n_runs)
        end
    end
    println()

    return (total, nb, n_split, n_nonspl)
end
