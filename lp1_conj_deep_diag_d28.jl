# =============================================================================
#  lp1_conj_deep_diag_d28.jl
#
#  D28 — LP-aff anchor (px, al) state at lag-k before LP1-conj emission.
#
#  Motivation
#  ──────────
#  D20 shows a sharp 1LP-aff opcode lift at lags 3–5 before each LP1-conj
#  emission.  This diagnostic asks: *which* affine LP point fires at those
#  lags?  Specifically, is its px value drawn from the same distribution as
#  baseline 1LP-aff steps, or does the lag-3/4/5 hit preferentially land in
#  the hot px bucket that D12 identified as anomalously concentrated?
#
#  If the lag-k 1LP-aff hit is already inside the hot px band, the precursor
#  and the emission share a common geometric locus — the walk enters the hot
#  region via an affine LP, then a few steps later emits a conj LP from the
#  same neighbourhood.  That would unify the D12 px concentration and the D20
#  lag signal into a single geometric attractor.
#
#  If the lag-k px is uniform (indistinguishable from baseline), the structure
#  is in the *trajectory shape* (k steps of a particular opcode pattern) rather
#  than a fixed locus in coordinate space.
#
#  Output
#  ──────
#  For each lag k = 1..D20_HIST_WINDOW where the D20 opcode lift for 1LP-aff
#  exceeds 1.5× (i.e. the lag is "hot" in D20 terms), we report:
#
#    • n_aff_at_lag    : number of emission snapshots where lag-k was 1LP-aff
#    • px distribution : p10/p50/p90 and hot-bucket fraction at lag-k vs baseline
#    • al distribution : p10/p50/p90 at lag-k vs baseline
#    • KS statistic    : KS(lag-k px vs baseline px), small → same distribution
#    • Lift table      : px bucketed to 32 coarse bands; per-band lift vs baseline
#
#  We also report the full lag-1..D20_HIST_WINDOW table of (n_aff, px_median,
#  al_median, ks_px) to make it easy to scan for which lags are structurally
#  interesting.
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d28_percentile — exact percentile from a sorted vector (0-based p ∈ [0,1]).
# ---------------------------------------------------------------------------
function _d28_percentile(sorted_v::Vector{Int}, p::Float64)::Float64
    isempty(sorted_v) && return NaN
    idx = p * (length(sorted_v) - 1)
    lo  = floor(Int, idx) + 1
    hi  = min(lo + 1, length(sorted_v))
    frac = idx - (lo - 1)
    return sorted_v[lo] * (1 - frac) + sorted_v[hi] * frac
end

# ---------------------------------------------------------------------------
#  _d28_ks2 — two-sample KS statistic between two unsorted Int vectors.
#  Returns D ∈ [0,1]; small → consistent with same distribution.
# ---------------------------------------------------------------------------
function _d28_ks2(a::Vector{Int}, b::Vector{Int})::Float64
    (isempty(a) || isempty(b)) && return NaN
    sa = sort(a)
    sb = sort(b)
    n  = length(sa)
    m  = length(sb)
    D  = 0.0
    i = j = 1
    while i <= n && j <= m
        xi = sa[i]; xj = sb[j]
        x  = min(xi, xj)
        while i <= n && sa[i] <= x; i += 1; end
        while j <= m && sb[j] <= x; j += 1; end
        d = abs((i - 1) / n - (j - 1) / m)
        D = max(D, d)
    end
    return D
end

# ---------------------------------------------------------------------------
#  _report_d28 — top-level entry point called from print_conj_deep_report.
# ---------------------------------------------------------------------------
function _report_d28(deep_stat::ConjDeepStat; p::Int = 0, ell::Int = 0)
    @printf("\n  D28 — Pre-emission LP-aff anchor (px, al) distribution at lag-k\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    n_snap = deep_stat.d28_n_snapshots
    n_base = deep_stat.d28_n_baseline

    @printf("    Emission snapshots collected : %d\n", n_snap)
    @printf("    Baseline 1LP-aff steps seen  : %d  (reservoir: %d)\n",
            n_base, length(deep_stat.d28_baseline_px))

    if n_snap < 5
        @printf("    (too few snapshots — need ≥5; skipping D28)\n")
        return
    end
    if length(deep_stat.d28_baseline_px) < 10
        @printf("    (too few baseline aff steps — skipping D28)\n")
        return
    end

    base_px = deep_stat.d28_baseline_px
    base_al = deep_stat.d28_baseline_al
    sort!(base_px); sort!(base_al)

    # ── Per-lag summary table ─────────────────────────────────────────────
    @printf("\n    Per-lag summary (lag k = steps before emission)\n")
    @printf("    %-6s  %-8s  %-10s  %-10s  %-10s  %-10s  %-8s\n",
            "lag", "n_aff", "px_p10", "px_med", "px_p90", "al_med", "KS_px")
    @printf("    %s\n", "─"^72)

    # Collect per-lag px and al vectors from snapshots.
    # d28_pre_snapshots is stored row-major: snapshot i, lag k → index (i-1)*W + k.
    W = D20_HIST_WINDOW
    lag_px = [Int[] for _ in 1:W]
    lag_al = [Int[] for _ in 1:W]

    for i in 1:n_snap
        base_idx = (i - 1) * W
        for k in 1:W
            entry = deep_stat.d28_pre_snapshots[base_idx + k]
            px_v, py_v, al_v = entry
            px_v >= 0 || continue   # sentinel: opcode at this lag was not 1LP-aff
            push!(lag_px[k], px_v)
            push!(lag_al[k], al_v)
        end
    end

    hot_lags = Int[]   # lags with n_aff ≥ 3 for detailed analysis

    for k in 1:W
        px_k = sort(lag_px[k])
        al_k = sort(lag_al[k])
        n_aff = length(px_k)

        if n_aff == 0
            @printf("    %-6d  %-8d  %s\n", k, 0, "(no 1LP-aff at this lag)")
            continue
        end

        px_p10 = _d28_percentile(px_k, 0.10)
        px_med = _d28_percentile(px_k, 0.50)
        px_p90 = _d28_percentile(px_k, 0.90)
        al_med = _d28_percentile(al_k, 0.50)
        ks     = _d28_ks2(px_k, base_px)

        @printf("    %-6d  %-8d  %-10.0f  %-10.0f  %-10.0f  %-10.0f  %-8.4f\n",
                k, n_aff, px_p10, px_med, px_p90, al_med, ks)

        n_aff >= 3 && push!(hot_lags, k)
    end

    # ── Baseline marginal summary ─────────────────────────────────────────
    @printf("\n    Baseline 1LP-aff px distribution (n=%d):\n", length(base_px))
    @printf("      p10=%.0f  p50=%.0f  p90=%.0f\n",
            _d28_percentile(base_px, 0.10),
            _d28_percentile(base_px, 0.50),
            _d28_percentile(base_px, 0.90))
    @printf("    Baseline 1LP-aff al distribution (n=%d):\n", length(base_al))
    @printf("      p10=%.0f  p50=%.0f  p90=%.0f\n",
            _d28_percentile(base_al, 0.10),
            _d28_percentile(base_al, 0.50),
            _d28_percentile(base_al, 0.90))

    # ── Detailed px lift table for each hot lag ───────────────────────────
    N_BANDS = 32
    p_eff   = p > 0 ? p : 2_500_000   # fallback if p not passed

    for k in hot_lags
        px_k  = lag_px[k]
        n_aff = length(px_k)
        n_aff < 3 && continue

        @printf("\n    Lag k=%d — px lift table (%d aff hits vs %d baseline)\n",
                k, n_aff, length(base_px))
        @printf("    %-30s  %-8s  %-8s  %-6s\n",
                "px_band", "n_lag", "n_base", "lift")
        @printf("    %s\n", "─"^58)

        # Count lag-k hits per band
        lag_counts  = zeros(Int, N_BANDS)
        base_counts = zeros(Int, N_BANDS)
        for v in px_k
            b = clamp((v * N_BANDS) ÷ p_eff, 0, N_BANDS - 1) + 1
            lag_counts[b] += 1
        end
        for v in base_px
            b = clamp((v * N_BANDS) ÷ p_eff, 0, N_BANDS - 1) + 1
            base_counts[b] += 1
        end

        total_lag  = max(1, sum(lag_counts))
        total_base = max(1, sum(base_counts))

        for b in 1:N_BANDS
            n_l = lag_counts[b]
            n_b = base_counts[b]
            n_l == 0 && n_b == 0 && continue
            frac_l = n_l / total_lag
            frac_b = n_b / total_base
            lift   = frac_b > 1e-9 ? frac_l / frac_b : (n_l > 0 ? Inf : 0.0)
            lo     = (b - 1) * p_eff ÷ N_BANDS
            hi     = b * p_eff ÷ N_BANDS - 1
            @printf("    px∈[%7d,%7d)  %-8d  %-8d  %.3f%s\n",
                    lo, hi, n_l, n_b,
                    lift,
                    lift >= 2.0 ? "  ← HOT" : (lift <= 0.5 ? "  ← COLD" : ""))
        end

        # KS p-value approximation (asymptotic formula)
        ks_val = _d28_ks2(px_k, base_px)
        n1     = length(px_k)
        n2     = length(base_px)
        z      = ks_val * sqrt(n1 * n2 / (n1 + n2))
        @printf("    KS(lag-%d px vs baseline) = %.4f  (z=%.2f; z>1.36 → p<0.05)\n",
                k, ks_val, z)

        # al distribution at this lag
        al_k = sort(lag_al[k])
        @printf("    al at lag-%d: p10=%.0f  p50=%.0f  p90=%.0f  (baseline p50=%.0f)\n",
                k,
                _d28_percentile(al_k, 0.10),
                _d28_percentile(al_k, 0.50),
                _d28_percentile(al_k, 0.90),
                _d28_percentile(base_al, 0.50))
    end

    # ── Interpretation ────────────────────────────────────────────────────
    @printf("\n    D28 Interpretation guide:\n")
    @printf("      KS(lag-k) << baseline KS → lag-k px is drawn from a different\n")
    @printf("        (more concentrated) distribution than random 1LP-aff steps.\n")
    @printf("      HOT px bands at lag-k overlapping D12's hot px bucket → the\n")
    @printf("        lag-k affine LP and the conj emission share a geometric locus.\n")
    @printf("      Uniform lift across px bands → structure is in trajectory shape,\n")
    @printf("        not a fixed coordinate-space attractor.\n")

    return nothing
end
