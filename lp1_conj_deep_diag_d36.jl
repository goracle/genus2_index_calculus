# =============================================================================
#  lp1_conj_deep_diag_d36.jl  --  D36: next_anchor() short-range
#  autocorrelation at closure (anchor-cursor FB-index distance).
#
#  Direct follow-up to D32. D32 tested whether the store→close recurrence
#  GAP, measured in walk-step TIME, is concentrated at short lags beyond a
#  memoryless null — it found no excess, and its closing interpretation
#  pointed elsewhere: "the CIR-ACF burst likely reflects correlated NEW key
#  arrivals (anchor-sequence structure) rather than literal revisits of the
#  same key. Consider checking next_anchor()'s short-range autocorrelation
#  directly."
#
#  next_anchor() (trial3_phase2.jl) is a deterministic per-thread round-robin
#  cursor over a fixed contiguous FB-index slice: it advances by exactly 1
#  per call and wraps at the slice boundary. There is no randomness in the
#  generator itself to test — the only thing that varies closure-to-closure
#  is WHICH two cursor positions get paired together: i0 (the anchor index
#  live at close time) and prev_col (the anchor index that was live when the
#  partner key was originally stored, possibly by a different thread).
#
#  D36 asks the index-space analogue of D32's time-space question: is
#  d = |i0 - prev_col| concentrated at small values beyond what pairing two
#  cursor positions independently/uniformly over the FB would predict? If
#  yes, the anchor SEQUENCE itself (not the recurrence-gap clock) is the
#  source of short-range correlation feeding the CIR-ACF burst — e.g.
#  because nearby FB indices index nearby curve points whose φ-images are
#  more likely to collide in quick succession. If no, the burst's source is
#  still unlocated, but it is now doubly ruled out as either a time-domain
#  memory effect (D32) or an index-domain one (D36) in this direct sense.
#
#  Null model: under the uniform-pair null, prev_col is an independent draw
#  from Uniform{1,...,fb_size} relative to i0 (the closing thread's own
#  cursor position). The distribution of d = |i0 - prev_col| over a uniform
#  ambient [1, M] is the standard "spacing of two uniform draws" triangular
#  law: P(d = k) = 2(M - k) / (M(M - 1)) for k = 1..M-1 (each ordered pair
#  (i0, prev_col) with i0 != prev_col equally likely; d and -d collapse
#  together via the absolute value, hence the factor of 2). For the
#  short-lag regime (k << M) this is closely linear with a slight negative
#  slope: P(d=k) ≈ 2/M · (1 - k/M) ≈ 2/M, i.e. very nearly flat compared to
#  D32's exponential geometric null. fb_size M is not reliably available at
#  the report call site (see D36 constants-block rationale in
#  lp1_conj_deep_diag_core.jl for why we don't depend on it), so we instead
#  fit M from the empirical mean exactly as D32 fits its geometric q from
#  the empirical mean: E[d] under the triangular law is (M+1)/3, so
#  M_hat = 3*mean_d - 1. This makes the null self-calibrating from the data,
#  at the cost of being unable to cross-check the fitted M against the
#  true fb_size — a caveat the report states explicitly.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d36_uniform_pair_null — expected counts under the triangular spacing
#  law for two independent Uniform{1,...,M} draws, evaluated at d = 1..k_max,
#  with M fitted from the empirical mean via M_hat = 3*mean_d - 1.
#
#  Returns expected COUNTS (not probabilities) scaled to n_total observed
#  closures, restricted to k=1..k_max — deliberately NOT renormalized to the
#  short-lag subsample, mirroring _d32_geometric_null's convention so an
#  excess shows up as observed >> expected rather than being absorbed by
#  renormalization.
# ---------------------------------------------------------------------------
function _d36_uniform_pair_null(mean_dist::Float64, n_total::Int, k_max::Int)
    expected = Vector{Float64}(undef, k_max)
    if mean_dist <= 0
        fill!(expected, 0.0)
        return expected, 0.0
    end
    m_hat = 3.0 * mean_dist - 1.0
    if m_hat < 2.0
        # Degenerate fit (shouldn't happen for any real FB size, but guard
        # against a pathological mean_dist near 0 making the law ill-posed).
        fill!(expected, 0.0)
        return expected, m_hat
    end
    denom = m_hat * (m_hat - 1.0)
    for k in 1:k_max
        if k >= m_hat
            expected[k] = 0.0
        else
            expected[k] = n_total * 2.0 * (m_hat - k) / denom
        end
    end
    return expected, m_hat
end

# ---------------------------------------------------------------------------
#  _report_d36 — print the D36 section.
# ---------------------------------------------------------------------------
function _report_d36(deep_stat::ConjDeepStat)
    n = deep_stat.d36_n_closures

    @printf("\n── D36: next_anchor() short-range autocorrelation (FB-index distance) ──\n")
    if n == 0
        @printf("  (no closures with valid i0/prev_col — skipping)\n")
        return
    end

    mean_dist = deep_stat.d36_dist_sum / n
    @printf("  Closures analyzed (d = |i0-prev_col| >= 1) : %d\n", n)
    @printf("  Mean anchor-index distance                 : %.1f\n", mean_dist)

    # --- Log2-bucketed shape over the full range ---
    @printf("\n  Full-range shape (log2-bucketed distance):\n")
    @printf("  %-18s %-10s %s\n", "distance range", "count", "frac")
    for b in 0:(D36_LOG_BUCKETS - 1)
        c = deep_stat.d36_dist_hist[b + 1]
        c == 0 && continue
        lo = b == 0 ? 0 : (1 << b)
        hi = b == 0 ? 1 : (1 << (b + 1)) - 1
        @printf("  [%-8d,%8d] %-10d %.4f\n", lo, hi, c, c / n)
    end

    # --- Short-lag fine-grained test against the uniform-pair null ---
    n_short = sum(deep_stat.d36_short_hist)
    @printf("\n  Short-lag test (d = 1..%d, fine-grained, vs Uniform-pair null):\n", D36_SHORT_MAX)
    @printf("  Closures with d <= %d                       : %d  (%.4f%% of all closures)\n",
            D36_SHORT_MAX, n_short, 100 * n_short / n)

    expected, m_hat = _d36_uniform_pair_null(mean_dist, n, D36_SHORT_MAX)
    expected_short = sum(expected)
    @printf("  Fitted ambient size M_hat (from mean_dist)  : %.0f\n", m_hat)
    @printf("    [M_hat = 3*mean_dist - 1 under the triangular spacing law;\n")
    @printf("     not cross-checked against the true FB size — see file header.]\n")
    @printf("  Uniform-pair null predicts                  : %.1f  (%.4f%% of all closures)\n",
            expected_short, 100 * expected_short / n)

    if expected_short > 0
        excess_ratio = n_short / expected_short
        @printf("  Observed / expected ratio                   : %.3fx\n", excess_ratio)
    end

    # χ² over the short-lag histogram vs the uniform-pair null (cell-by-cell,
    # not just the aggregate), with a final overflow cell for d > k_max so
    # the test is a proper partition of all n closures — same construction
    # as D32's chi2 block.
    chi2 = 0.0
    dof  = 0
    for k in 1:D36_SHORT_MAX
        e = expected[k]
        e < 1.0 && continue   # skip tiny-expectation cells (chi2 unstable there)
        o = deep_stat.d36_short_hist[k]
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
    @printf("  chi2/dof (short-lag shape vs uniform-pair null) : %.4f  (dof=%d)\n", chi2 / dof, dof)

    # --- Direct readout in the CIR-ACF burst window (Δ=3..30 steps), same
    #     window D32 reports, for direct cross-comparison between the two
    #     candidate mechanisms (time-domain vs index-domain).
    cir_lo, cir_hi = 3, 30
    n_cir = sum(@view deep_stat.d36_short_hist[cir_lo:cir_hi])
    e_cir = sum(@view expected[cir_lo:cir_hi])
    @printf("\n  CIR-ACF burst window readout (d = %d..%d):\n", cir_lo, cir_hi)
    @printf("    observed closures with distance in window : %d\n", n_cir)
    @printf("    uniform-pair-null expectation              : %.1f\n", e_cir)
    if e_cir > 0
        @printf("    observed / expected                        : %.3fx\n", n_cir / e_cir)
    end

    @printf("---------------------------------------------------------------------\n")
    if expected_short > 0 && n_short / expected_short > 1.5 && chi2 / dof > 3.0
        @printf("  => Short-range EXCESS detected: closures preferentially pair anchor-\n")
        @printf("     cursor positions that are close in FB-index, beyond what pairing\n")
        @printf("     two uniform cursor draws predicts. The deterministic anchor\n")
        @printf("     SEQUENCE itself is a candidate driver of CIR-ACF's burst (peak\n")
        @printf("     lift at Δ=3, decay by Δ≈30-60) and of the α2 gap: nearby FB\n")
        @printf("     indices appear to index curve points whose φ-images collide more\n")
        @printf("     often than chance. Check the FB's construction order (is it sorted\n")
        @printf("     by x-coordinate or by discovery order?) against this distance scale.\n")
    else
        @printf("  => No significant short-range excess: anchor-index distance at\n")
        @printf("     closure is consistent with pairing two uniformly-placed cursor\n")
        @printf("     positions. Combined with D32 (no excess in walk-step time either),\n")
        @printf("     the CIR-ACF burst is not explained by either of the two direct\n")
        @printf("     short-range mechanisms this diagnostic pair can see — gap/time\n")
        @printf("     (D32) and cursor-index/sequence (D36). The burst's source remains\n")
        @printf("     open; it is not a literal key revisit and not an anchor-sequence\n")
        @printf("     adjacency effect. Consider whether it is a property of the FB's\n")
        @printf("     point GEOMETRY itself (D25/D27 already show a moderate but partial\n")
        @printf("     KL signal there) rather than of either cursor's motion through it.\n")
    end
end
