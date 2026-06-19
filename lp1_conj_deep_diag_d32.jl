# =============================================================================
#  lp1_conj_deep_diag_d32.jl  --  D32: LP1-conj key recurrence-gap concentration.
#
#  Revised framing (see constants block in lp1_conj_deep_diag_core.jl for the
#  full rationale). The original "u-polynomial self-return" framing doesn't
#  apply directly to this codebase, since the walk's Jacobian divisor D_cur
#  is not fed back from the φ residual RS_mumford. What IS directly testable,
#  and what the CIR-ACF result (peak post-emission lift 15.18× at Δ=3 steps,
#  decaying to baseline by Δ≈30-60 steps) motivates, is whether the recurrence
#  gap of an LP1-conj key — depth = close_step - store_step — is itself
#  concentrated at short lags beyond what a memoryless (geometric) process
#  predicts at the same empirical mean.
#
#  If D32 finds excess short-lag mass: the same residual Mumford key tends
#  to recur within a handful of steps of being stored, independent of (and
#  consistent with) CIR-ACF's emission-rate burst — i.e. the walk is
#  effectively forming short cycles in u-space in practice, even though no
#  exact algebraic fixed point was required for this to happen.
#
#  If D32 finds no excess (geometric-consistent): the recurrence gap has no
#  memory beyond what a uniform/Poisson collision process implies, and the
#  CIR-ACF burst must be explained by some OTHER mechanism (e.g. anchor
#  sequence correlation feeding multiple distinct keys in quick succession,
#  rather than literal key revisits) — pointing diagnostics toward the
#  anchor distribution (next_anchor()) instead of the u-space map.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d32_geometric_null — expected counts under Geometric(q) with the same
#  mean as the empirical short-lag sample, evaluated at depth = 1..k_max.
#
#  For a memoryless arrival process with mean gap μ (closures occur at rate
#  1/μ per step), P(depth = k) ≈ q·(1-q)^(k-1) with q = 1/μ (discrete
#  geometric on {1,2,3,...}). Returns expected COUNTS (not probabilities)
#  scaled to n_total observed closures, restricted to k=1..k_max — this is
#  deliberately NOT renormalized to the short-lag subsample, so that an
#  excess of short-lag closures shows up as observed >> expected rather
#  than being absorbed by renormalization.
# ---------------------------------------------------------------------------
function _d32_geometric_null(mean_depth::Float64, n_total::Int, k_max::Int)
    expected = Vector{Float64}(undef, k_max)
    mean_depth <= 0 && (fill!(expected, 0.0); return expected)
    q = 1.0 / mean_depth
    q = clamp(q, 1e-12, 1.0 - 1e-12)
    for k in 1:k_max
        expected[k] = n_total * q * (1.0 - q)^(k - 1)
    end
    return expected
end

# ---------------------------------------------------------------------------
#  _report_d32 — print the D32 section.
# ---------------------------------------------------------------------------
function _report_d32(deep_stat::ConjDeepStat)
    n = deep_stat.d32_n_closures

    @printf("\n── D32: LP1-conj key recurrence-gap concentration (short-lag focus) ──\n")
    if n == 0
        @printf("  (no closures with valid store_step — skipping)\n")
        return
    end

    mean_depth = deep_stat.d32_depth_sum / n
    @printf("  Closures analyzed (depth >= 0)     : %d\n", n)
    @printf("  Mean recurrence gap (depth)        : %.1f steps\n", mean_depth)

    # --- Log2-bucketed shape over the full range ---
    @printf("\n  Full-range shape (log2-bucketed depth):\n")
    @printf("  %-18s %-10s %s\n", "depth range", "count", "frac")
    for b in 0:(D32_LOG_BUCKETS - 1)
        c = deep_stat.d32_depth_log_hist[b + 1]
        c == 0 && continue
        lo = b == 0 ? 0 : (1 << b)
        hi = b == 0 ? 1 : (1 << (b + 1)) - 1
        @printf("  [%-8d,%8d] %-10d %.4f\n", lo, hi, c, c / n)
    end

    # --- Short-lag fine-grained test against geometric null ---
    n_short = sum(deep_stat.d32_short_lag_hist)
    @printf("\n  Short-lag test (depth = 1..%d, fine-grained, vs Geometric(1/mean) null):\n", D32_SHORT_LAG_MAX)
    @printf("  Closures with depth <= %d           : %d  (%.4f%% of all closures)\n",
            D32_SHORT_LAG_MAX, n_short, 100 * n_short / n)

    expected = _d32_geometric_null(mean_depth, n, D32_SHORT_LAG_MAX)
    expected_short = sum(expected)
    @printf("  Geometric null predicts            : %.1f  (%.4f%% of all closures)\n",
            expected_short, 100 * expected_short / n)

    if expected_short > 0
        excess_ratio = n_short / expected_short
        @printf("  Observed / expected ratio           : %.3fx\n", excess_ratio)
    end

    # χ² over the short-lag histogram vs the geometric null (cell-by-cell,
    # not just the aggregate), with a final overflow cell for depth > k_max
    # so the test is a proper partition of all n closures.
    chi2 = 0.0
    dof  = 0
    for k in 1:D32_SHORT_LAG_MAX
        e = expected[k]
        e < 1.0 && continue   # skip tiny-expectation cells (chi2 unstable there)
        o = deep_stat.d32_short_lag_hist[k]
        d = o - e
        chi2 += d * d / e
        dof += 1
    end
    e_tail = n - expected_short
    o_tail = n - n_short
    if e_tail >= 1.0
        d = o_tail - e_tail
        chi2 += d * d / e_tail
        dof += 1
    end
    dof = max(dof - 1, 1)
    @printf("  chi2/dof (short-lag shape vs geometric null) : %.4f  (dof=%d)\n", chi2 / dof, dof)

    # --- Direct readout in the CIR-ACF burst window (Δ=3..30 steps) ---
    cir_lo, cir_hi = 3, 30
    n_cir = sum(@view deep_stat.d32_short_lag_hist[cir_lo:cir_hi])
    e_cir = sum(@view expected[cir_lo:cir_hi])
    @printf("\n  CIR-ACF burst window readout (depth = %d..%d steps):\n", cir_lo, cir_hi)
    @printf("    observed closures with depth in window : %d\n", n_cir)
    @printf("    geometric-null expectation              : %.1f\n", e_cir)
    if e_cir > 0
        @printf("    observed / expected                     : %.3fx\n", n_cir / e_cir)
    end

    @printf("---------------------------------------------------------------------\n")
    if expected_short > 0 && n_short / expected_short > 1.5 && chi2 / dof > 3.0
        @printf("  => Short-lag EXCESS detected: recurrence gaps cluster at depth <= %d\n", D32_SHORT_LAG_MAX)
        @printf("     beyond what a memoryless process predicts. Consistent with CIR-ACF's\n")
        @printf("     burst (peak lift at Δ=3, decay by Δ≈30-60): the same residual Mumford\n")
        @printf("     key is literally recurring within the burst window, not just the\n")
        @printf("     emission RATE rising. This is real (if non-algebraic) short-cycling\n")
        @printf("     in u-space and a strong candidate driver of the α2 gap.\n")
    else
        @printf("  => No significant short-lag excess: recurrence-gap shape is consistent\n")
        @printf("     with a memoryless process at this mean. The CIR-ACF burst likely\n")
        @printf("     reflects correlated NEW key arrivals (anchor-sequence structure)\n")
        @printf("     rather than literal revisits of the same key. Consider checking\n")
        @printf("     next_anchor()'s short-range autocorrelation directly.\n")
    end
end
