# =============================================================================
#  lp1_conj_deep_diag_d30.jl  --  D30: closure FB-point geometric
#  (x-coordinate) short-range adjacency.
#
#  Direct follow-up to D36, itself a follow-up to D32. D36 tested whether
#  closures preferentially pair anchor-cursor positions close in FB-ARRAY-
#  INDEX and found no excess. D30 asks the related but distinct question:
#  are closures preferentially pairing FB points close in the curve's own
#  COORDINATE space, regardless of where those points sit in the fb[]
#  array? Index-adjacency (D36) and coordinate-adjacency (D30) are the same
#  question only if the FB happens to be sorted by x — not something this
#  diagnostic layer can assume, so both are tested independently.
#
#  Proxy: Δx = mod(x_close - x_store, p), the same quantity D35 already
#  computes for its GLOBAL Rényi-2/Gini/Hill concentration test. D30 is the
#  SHORT-RANGE complement: a global Δx distribution can look uniform (as
#  D35 found) while still having excess mass at small circular distance —
#  the same "marginal looks boring, conditional/local structure doesn't"
#  point D35's own docstring makes about Δα. x ranges over F_p, so the
#  relevant distance is circular: dist = min(Δx, p - Δx).
#
#  Null model: under independence (x_store drawn from the FB's x-marginal,
#  independent of x_close), and treating the FB's x-coordinates as
#  approximately filling [0, p) (a simplification — the true x-marginal is
#  whatever the FB construction produces, not necessarily uniform; see the
#  caveat printed in the report), dist = min(Δx, p-Δx) for two independent
#  Uniform(0,p) draws follows P(dist = k) = 2/p for 1 <= k < p/2 (each of
#  the two circular directions equally likely, hence the factor of 2; this
#  is flatter than D32's geometric null or D36's triangular null — a
#  uniform circular difference has no preferred scale). This needs only p,
#  not a fitted parameter, so — unlike D32/D36 — the null is exact given p
#  rather than estimated from the empirical mean.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d30_circular_uniform_null — expected counts under two independent
#  Uniform(0,p) draws' circular distance, evaluated at dist = 1..k_max.
#
#  Returns expected COUNTS (not probabilities) scaled to n_total observed
#  closures, restricted to k=1..k_max — deliberately NOT renormalized to
#  the short-lag subsample, mirroring _d32_geometric_null's and
#  _d36_uniform_pair_null's convention.
# ---------------------------------------------------------------------------
function _d30_circular_uniform_null(p::Int, n_total::Int, k_max::Int)
    expected = Vector{Float64}(undef, k_max)
    if p <= 2
        fill!(expected, 0.0)
        return expected
    end
    rate = 2.0 / p
    half = p / 2.0
    for k in 1:k_max
        expected[k] = k < half ? n_total * rate : 0.0
    end
    return expected
end

# ---------------------------------------------------------------------------
#  _report_d30 — print the D30 section.
# ---------------------------------------------------------------------------
function _report_d30(deep_stat::ConjDeepStat; p::Int = 0)
    n_seen = deep_stat.d30_n_closures
    n      = length(deep_stat.d30_x_close)

    @printf("\n── D30: closure FB-point geometric (x-coordinate) short-range adjacency ──\n")
    if n == 0
        @printf("  (no closures with valid x_close/x_store — skipping)\n")
        return
    end
    if p <= 2
        @printf("  (p not available or degenerate — skipping; D30 needs the field\n")
        @printf("   characteristic to compute the mod-p circular null. Pass p= to\n")
        @printf("   print_conj_deep_report.)\n")
        return
    end

    @printf("  Closures analyzed                  : %d", n)
    if n < n_seen
        @printf("  (capped sample of %d total closures seen)\n", n_seen)
    else
        @printf("\n")
    end

    # --- Compute Δx, the circular distance, and the exact-zero count ---
    dist      = Vector{Int}(undef, n)
    n_zero    = 0
    dist_sum  = 0
    for i in 1:n
        dx = mod(deep_stat.d30_x_close[i] - deep_stat.d30_x_store[i], p)
        d  = min(dx, p - dx)
        dist[i] = d
        if d == 0
            n_zero += 1
        else
            dist_sum += d
        end
    end
    n_nonzero = n - n_zero
    @printf("  Exact x-coincidences (x_close == x_store) : %d  (%.4f%% of analyzed)\n",
            n_zero, 100 * n_zero / n)
    @printf("    [Possible even for DISTINCT FB points on a hyperelliptic curve —\n")
    @printf("     the two points above/below a shared x. Excluded from the mean/\n")
    @printf("     null fit below; a true zero would not fit a 1..k_max null anyway.]\n")

    if n_nonzero == 0
        @printf("  (all analyzed closures were exact x-coincidences — skipping shape test)\n")
        return
    end
    mean_dist = dist_sum / n_nonzero
    @printf("  Mean circular distance (excl. exact coincidences) : %.1f\n", mean_dist)
    @printf("    [Null-predicted mean under Uniform(0,p) circular distance: %.1f]\n",
            p / 4.0)

    # --- Log2-bucketed shape over the full range ---
    log_hist = zeros(Int, D30_LOG_BUCKETS)
    for d in dist
        d == 0 && continue
        log_bkt = d <= 1 ? 0 : min(D30_LOG_BUCKETS - 1, (64 - leading_zeros(d)) - 1)
        log_hist[log_bkt + 1] += 1
    end
    @printf("\n  Full-range shape (log2-bucketed circular distance, excl. exact coincidences):\n")
    @printf("  %-18s %-10s %s\n", "distance range", "count", "frac")
    for b in 0:(D30_LOG_BUCKETS - 1)
        c = log_hist[b + 1]
        c == 0 && continue
        lo = b == 0 ? 0 : (1 << b)
        hi = b == 0 ? 1 : (1 << (b + 1)) - 1
        @printf("  [%-8d,%8d] %-10d %.4f\n", lo, hi, c, c / n_nonzero)
    end

    # --- Short-lag fine-grained test against the exact circular-uniform null ---
    short_hist = zeros(Int, D30_SHORT_MAX)
    for d in dist
        1 <= d <= D30_SHORT_MAX && (short_hist[d] += 1)
    end
    n_short = sum(short_hist)
    @printf("\n  Short-lag test (dist = 1..%d, fine-grained, vs circular-Uniform(0,p) null):\n",
            D30_SHORT_MAX)
    @printf("  Closures with dist <= %d                     : %d  (%.4f%% of non-coincident)\n",
            D30_SHORT_MAX, n_short, 100 * n_short / n_nonzero)

    expected = _d30_circular_uniform_null(p, n_nonzero, D30_SHORT_MAX)
    expected_short = sum(expected)
    @printf("  Circular-uniform null predicts              : %.1f  (%.4f%% of non-coincident)\n",
            expected_short, 100 * expected_short / n_nonzero)
    @printf("    [Null assumes the FB's x-coordinates fill [0,p) uniformly; if the FB\n")
    @printf("     construction itself concentrates x (e.g. only x with smooth-friendly\n")
    @printf("     structure), this null is too generous and a real excess could be\n")
    @printf("     masked. Not cross-checked against the FB's true x-marginal here.]\n")

    if expected_short > 0
        excess_ratio = n_short / expected_short
        @printf("  Observed / expected ratio                    : %.3fx\n", excess_ratio)
    end

    chi2 = 0.0
    dof  = 0
    for k in 1:D30_SHORT_MAX
        e = expected[k]
        e < 1.0 && continue
        o = short_hist[k]
        d = o - e
        chi2 += d * d / e
        dof += 1
    end
    e_tail = n_nonzero - expected_short
    o_tail = n_nonzero - n_short
    if e_tail >= 1.0
        d = o_tail - e_tail
        chi2 += d * d / e_tail
        dof += 1
    end
    dof = max(dof - 1, 1)
    @printf("  chi2/dof (short-lag shape vs circular-uniform null) : %.4f  (dof=%d)\n",
            chi2 / dof, dof)

    # --- Direct readout in the CIR-ACF burst window (Δ=3..30), matching
    #     D32's/D36's window for direct cross-comparison across all three
    #     candidate mechanisms (time, index, coordinate).
    cir_lo, cir_hi = 3, 30
    n_cir = sum(@view short_hist[cir_lo:cir_hi])
    e_cir = sum(@view expected[cir_lo:cir_hi])
    @printf("\n  CIR-ACF burst window readout (dist = %d..%d):\n", cir_lo, cir_hi)
    @printf("    observed closures with distance in window : %d\n", n_cir)
    @printf("    circular-uniform-null expectation          : %.1f\n", e_cir)
    if e_cir > 0
        @printf("    observed / expected                        : %.3fx\n", n_cir / e_cir)
    end

    @printf("---------------------------------------------------------------------\n")
    if expected_short > 0 && n_short / expected_short > 1.5 && chi2 / dof > 3.0
        @printf("  => Short-range EXCESS detected: closures preferentially pair FB points\n")
        @printf("     close in x-coordinate, beyond what the circular-uniform null\n")
        @printf("     predicts. Unlike D36 (no excess in FB-array-index), this implicates\n")
        @printf("     the curve's own coordinate GEOMETRY rather than the order next_anchor()\n")
        @printf("     happens to visit points in. Combined with D25/D27's moderate KL signal,\n")
        @printf("     this is a strong candidate driver of the α2 gap — check whether the\n")
        @printf("     excess concentrates among specific x-bands (cross-reference D34's\n")
        @printf("     per-bucket table) or is uniform across x (broad coordinate-scale effect).\n")
    else
        @printf("  => No significant short-range excess: closure x-distance is consistent\n")
        @printf("     with pairing two independently-placed points (subject to the FB\n")
        @printf("     x-marginal caveat above). Combined with D32 (no time-domain excess)\n")
        @printf("     and D36 (no index-domain excess), all three direct short-range\n")
        @printf("     mechanisms this diagnostic trio can see have come back negative.\n")
        @printf("     The CIR-ACF burst and the α2 gap remain unexplained by short-range\n")
        @printf("     pairwise structure in time, cursor-index, or x-coordinate alone —\n")
        @printf("     the explanation, if mechanical rather than purely statistical, likely\n")
        @printf("     requires a higher-dimensional or non-pairwise invariant (full (x,y)\n")
        @printf("     or Jacobian-distance geometry, not just x; or N-way burst structure,\n")
        @printf("     not pairwise store/close coincidence).\n")
    end
end
