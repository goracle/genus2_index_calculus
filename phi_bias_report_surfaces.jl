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

    # --- Surface 2: discriminant bias (χ² on split histogram) ---
    @printf("  Surface 2 — discriminant bias (split histogram χ² test):\n")
    @printf("    histogram buckets      : %d  (each ~%s wide in 𝔽ₚ)\n",
            nb, p > 0 ? string(p ÷ nb) : "p/√p")
    if n_split > 0
        expected  = n_split / nb
        chi2_split = sum((x - expected)^2 / max(1.0, expected)
                         for x in stat.split_hist)
        dof = nb - 1
        @printf("    split χ²               : %.2f  (dof=%d; uniform expected ≈ %.1f)\n",
                chi2_split, dof, Float64(dof))
        # Rule of thumb: χ² / dof >> 1 indicates non-uniformity.
        ratio = chi2_split / max(1.0, Float64(dof))
        flag  = ratio > 2.0 ? " ← NON-UNIFORM" : " (consistent with uniform)"
        @printf("    χ²/dof                 : %.3f%s\n", ratio, flag)
    else
        @printf("    (no split steps recorded — χ² not computed)\n")
    end

    # Also χ² for non-split steps (should be uniform if Δ is random).
    if n_nonspl > 0
        expected2   = n_nonspl / nb
        chi2_nonspl = sum((x - expected2)^2 / max(1.0, expected2)
                          for x in stat.nonsplit_hist)
        dof2 = nb - 1
        @printf("    non-split χ²           : %.2f  (dof=%d)\n", chi2_nonspl, dof2)
    end

    # --- Top buckets (show the 5 most-populated split buckets) ---
    if n_split > 0 && nb >= 5
        indexed  = collect(enumerate(stat.split_hist))
        top5     = sort(indexed, by=x->-x[2])[1:min(5, end)]
        @printf("    top split buckets (bucket_idx, count):\n")
        for (bi, cnt) in top5
            frac = p > 0 ? @sprintf(" [a ∈ [%d,%d))", (bi-1)*p÷nb, bi*p÷nb) : ""
            @printf("      bucket %4d%s : %d  (%.2f%% of splits)\n",
                    bi, frac, cnt, 100.0*cnt/n_split)
        end
    end

    # --- Seq 1: Run-length distribution KS test ---
    @printf("  Seq 1 — Run-length distribution (KS vs Geometric(1/2)):\n")
    for (label, hist) in (("split", stat.run_hist_split), ("non-split", stat.run_hist_nonsplit))
        n_runs = sum(hist)
        if n_runs >= 10
            # Empirical CDF vs Geometric(1/2) CDF: P(L ≤ k) = 1 - (1/2)^k
            ks_stat = 0.0
            cumul   = 0.0
            for k in 1:MAX_RUN_LEN
                cumul     += hist[k] / n_runs
                geo_cdf    = 1.0 - 0.5^k
                ks_stat    = max(ks_stat, abs(cumul - geo_cdf))
            end
            mean_run = sum(k * hist[k] for k in 1:MAX_RUN_LEN) / n_runs
            # Geometric(1/2) has mean = 2.
            flag = ks_stat > 0.05 ? (mean_run > 2.0 ? " ← LONG RUNS (pos corr)" :
                                                        " ← SHORT RUNS (anti-corr)") :
                                    " (consistent with i.i.d.)"
            @printf("    %-9s runs: n=%d  mean_len=%.2f  KS=%.4f%s\n",
                    label, n_runs, mean_run, ks_stat, flag)
            # Show run-length histogram up to k=10
            @printf("      len:  %s\n", join([@sprintf("%4d", k) for k in 1:min(10,MAX_RUN_LEN)], " "))
            @printf("      cnt:  %s\n", join([@sprintf("%4d", hist[k]) for k in 1:min(10,MAX_RUN_LEN)], " "))
            if MAX_RUN_LEN > 10
                overflow = sum(hist[11:end])
                @printf("      cnt[11+]: %d\n", overflow)
            end
        else
            @printf("    %-9s runs: n=%d  (too few for KS test)\n", label, n_runs)
        end
    end
    println()

    return (total, nb, n_split, n_nonspl)
end
