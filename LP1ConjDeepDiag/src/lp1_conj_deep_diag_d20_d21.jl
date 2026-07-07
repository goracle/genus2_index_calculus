# =============================================================================
#  lp1_conj_deep_diag_d20_d21.jl
#
#  D20 — Pre-emission opcode sequence fingerprint.
#        Asks: "is there a characteristic step-type pattern that precedes
#        LP1-conj emissions?"  If so, the walk rule (not coordinates) is
#        structuring the emission process.
#
#  D21 — Refractory gap: steps to next eligible-state proxy.
#        After each emission, counts steps until the next 1LP_CONJ opcode
#        appears (regardless of whether it closes).  Measures the hard
#        refractory window seen in D4/CIR and provides its structural length.
#
#  Both diagnostics are low-volume (≤2000 emission snapshots, ≤5000 gaps).
# =============================================================================

# Opcode label table (index = opcode byte + 1, matching OPCODE_* constants)
const _D20_OPCODE_LABELS = ["0-LP", "1LP-aff", "1LP-conj", "2LP-aff", "2LP-conj", "skip"]

# ---------------------------------------------------------------------------
#  _report_d20_d21
# ---------------------------------------------------------------------------
function _report_d20_d21(deep_stat::ConjDeepStat)

    @printf("\n  D20 — Pre-emission opcode sequence fingerprint\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    ns = deep_stat.d20_n_snapshots
    nb = deep_stat.d20_n_baseline

    @printf("    Emission snapshots collected : %d  (cap %d)\n", ns, D20_MAX_SNAPSHOTS)
    @printf("    Baseline windows collected   : %d  (cap %d)\n", nb, D20_BASELINE_CAP)

    if ns < 4 || nb < 10
        @printf("    (insufficient data — need ≥4 emission snapshots and ≥10 baseline windows)\n")
        @printf("\n  D21 — Refractory gap to next eligible-state proxy\n")
        @printf("  ─────────────────────────────────────────────────────────────────\n")
        _report_d21(deep_stat)
        return
    end

    # ── Build emission opcode frequency table: position k × opcode ────────
    # d20_pre_snapshots is stored as [lag-1, lag-2, …, lag-D20_HIST_WINDOW]
    # per emission, row-major (most recent first).
    n_win   = D20_HIST_WINDOW
    n_oc    = 6
    emit_counts = zeros(Int, n_win, n_oc)
    snaps   = deep_stat.d20_pre_snapshots
    for snap_i in 1:ns
        base = (snap_i - 1) * n_win
        for k in 1:n_win
            oc = Int(snaps[base + k])
            oc == 0xff && continue    # sentinel: no data at this lag
            oc_idx = oc + 1           # 1-based
            1 <= oc_idx <= n_oc && (emit_counts[k, oc_idx] += 1)
        end
    end

    # ── Baseline table: already accumulated as opcode counts per position ─
    base_counts = deep_stat.d20_baseline_opcode_counts  # D20_HIST_WINDOW × 6 UInt32

    # ── Compute lift = (emit_frac / base_frac) per (lag, opcode) ─────────
    @printf("\n    Pre-emission opcode lift table  (lag k = steps before emission)\n")
    @printf("    lift = P(opcode | k steps before emit) / P(opcode | baseline)\n")
    @printf("    %-12s", "opcode")
    for k in 1:min(n_win, 8)
        @printf("  lag-%-3d", k)
    end
    @printf("\n")

    # Compute baseline fractions per position (normalize each row of base_counts)
    base_frac = zeros(Float64, n_win, n_oc)
    for k in 1:n_win
        row_sum = Float64(sum(base_counts[k, :]))
        if row_sum > 0
            for oc in 1:n_oc
                base_frac[k, oc] = Float64(base_counts[k, oc]) / row_sum
            end
        end
    end

    # Compute emission fractions per position
    emit_frac = zeros(Float64, n_win, n_oc)
    for k in 1:n_win
        row_sum = Float64(sum(emit_counts[k, :]))
        if row_sum > 0
            for oc in 1:n_oc
                emit_frac[k, oc] = Float64(emit_counts[k, oc]) / row_sum
            end
        end
    end

    max_lift_global = 0.0
    max_lift_oc     = 1
    max_lift_lag    = 1

    for oc_idx in 1:n_oc
        @printf("    %-12s", _D20_OPCODE_LABELS[oc_idx])
        for k in 1:min(n_win, 8)
            ef = emit_frac[k, oc_idx]
            bf = base_frac[k, oc_idx]
            if bf > 1e-9
                lift = ef / bf
                if lift > max_lift_global
                    max_lift_global = lift
                    max_lift_oc  = oc_idx
                    max_lift_lag = k
                end
                @printf("  %6.2f×", lift)
            else
                @printf("  %6s ", "—")
            end
        end
        @printf("\n")
    end

    @printf("\n    Peak lift: %.2f× for opcode '%s' at lag-%d\n",
            max_lift_global, _D20_OPCODE_LABELS[max_lift_oc], max_lift_lag)

    if max_lift_global > 1.5
        @printf("    ↑ OPCODE PATTERN BEFORE EMISSION: walk-rule signature detected.\n")
        @printf("      Emissions are preceded by a non-random opcode sequence —\n")
        @printf("      the algebraic structure lives in the step dynamics, not coordinates.\n")
    elseif max_lift_global > 1.1
        @printf("    ↑ Mild opcode bias before emission (lift %.2f×); verify with more data.\n",
                max_lift_global)
    else
        @printf("    ↔ No significant pre-emission opcode pattern (max lift %.2f×).\n",
                max_lift_global)
        @printf("      Walk rule does not structurally gate emissions — consistent with\n")
        @printf("      renewal process driven by rare algebraic coincidences.\n")
    end

    # ── χ² test: are emission opcode fractions at lag-1 different from baseline? ─
    lag1_emit = emit_counts[1, :]
    lag1_base = Float64.(base_counts[1, :])
    n_emit_lag1 = sum(lag1_emit)
    n_base_lag1 = sum(lag1_base)
    if n_emit_lag1 >= 5 && n_base_lag1 >= 5
        base_norm = lag1_base ./ max(1.0, n_base_lag1)
        chi2 = 0.0
        dof  = 0
        for oc in 1:n_oc
            expected = base_norm[oc] * n_emit_lag1
            if expected > 0.5
                chi2 += (lag1_emit[oc] - expected)^2 / expected
                dof  += 1
            end
        end
        dof = max(dof - 1, 1)
        @printf("\n    χ² test (lag-1, dof=%d): χ²=%.2f  χ²/dof=%.3f  %s\n",
                dof, chi2, chi2/dof,
                chi2/dof > 3.0 ? "← SIGNIFICANT DEVIATION from baseline" :
                chi2/dof > 1.5 ? "(mild deviation)" : "(consistent with baseline)")
    end

    # ── D21 ───────────────────────────────────────────────────────────────
    @printf("\n  D21 — Refractory gap to next eligible-state proxy\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    _report_d21(deep_stat)
end

# ---------------------------------------------------------------------------
#  _report_d21 — separate helper so D21 can be printed even if D20 has no data.
# ---------------------------------------------------------------------------
function _report_d21(deep_stat::ConjDeepStat)
    gaps = deep_stat.d21_return_gaps
    n_emit = deep_stat.d21_n_emitted

    @printf("    Total emissions tracked      : %d\n", n_emit)
    @printf("    Return-gap samples collected : %d  (cap %d)\n", length(gaps), D21_MAX_GAPS)

    if length(gaps) < 4
        @printf("    (insufficient samples — need ≥4)\n")
        return
    end

    ng     = length(gaps)
    μ      = sum(gaps) / ng
    var    = sum((g - μ)^2 for g in gaps) / ng
    σ      = sqrt(var)
    med    = sort(gaps)[ng ÷ 2 + 1]
    pct5   = sort(gaps)[max(1, round(Int, 0.05 * ng))]
    pct95  = sort(gaps)[min(ng, round(Int, 0.95 * ng))]

    @printf("    Gap = steps from emission to next 1LP_CONJ opcode (any hit)\n")
    @printf("    n   = %d  μ = %.1f  σ = %.1f  median = %d\n", ng, μ, σ, med)
    @printf("    p5  = %d  p95 = %d\n", pct5, pct95)

    # Fraction of gaps below thresholds — shows hard refractory structure
    @printf("\n    Cumulative distribution:\n")
    for thresh in [100, 500, 1000, 5000, 10000, 50000]
        frac = count(g <= thresh for g in gaps) / ng
        bar  = repeat("█", round(Int, frac * 20))
        @printf("      ≤%7d steps : %5.1f%%  %s\n", thresh, 100*frac, bar)
    end

    # Compare to Poisson expectation: if rate is λ per step, P(return ≤ T) = 1 - exp(-λT)
    # λ estimated from overall emission rate = n_emit / total_steps
    # We don't have total_steps here, but we can estimate from mean gap.
    # Under Poisson: E[gap] = 1/λ_1LP_CONJ (where 1LP_CONJ hits ≈ 50% of steps from D11)
    # From D11: ~50% of steps are 1LP_CONJ opcodes, so λ ≈ 0.5 steps between any 1LP_CONJ.
    # E[gap to next 1LP_CONJ | Poisson] ≈ 2 steps (immediate).
    # If our observed μ >> 2, the refractory is structural, not sampling noise.
    @printf("\n    Poisson-null E[return gap] ≈ 2 steps (50%% of opcodes are 1LP_CONJ).\n")
    @printf("    Observed μ = %.1f steps  →  ratio = %.1f× above Poisson null.\n",
            μ, μ / 2.0)
    if μ > 100.0
        @printf("    ↑ HARD REFRACTORY: walk is structurally excluded from LP1-conj\n")
        @printf("      for ~%.0f steps after each emission.  This is algebraic, not random.\n", μ)
    elseif μ > 10.0
        @printf("    ↑ Moderate refractory (%.0f×); may indicate partial exclusion.\n", μ / 2.0)
    else
        @printf("    ↔ No significant refractory structure.\n")
    end

    # Short-gap frequency test: are there any very-short gaps (would disprove hard exclusion)?
    n_short = count(g <= 10 for g in gaps)
    @printf("\n    Gaps ≤ 10 steps (tests hard-exclusion hypothesis): %d / %d (%.1f%%)\n",
            n_short, ng, 100.0 * n_short / ng)
    if n_short == 0
        @printf("    ✓ Consistent with hard post-emission exclusion.\n")
    else
        @printf("    ! Short gaps present — exclusion is soft or incomplete.\n")
    end
end
