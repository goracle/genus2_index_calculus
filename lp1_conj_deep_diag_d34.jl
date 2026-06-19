# =============================================================================
#  lp1_conj_deep_diag_d34.jl
#
#  D34 — x-bucket smoothing-probability diagnostic (draining hypothesis test).
#
#  Measures Pr(full relation | x-bucket) and Pr(LP1-conj STORE | x-bucket)
#  across D34_X_BUCKETS equal-width bins of the anchor x-coordinate, to test
#  whether FB x-hotspot "draining" suppresses LP1-conj residual production in
#  the same x-bands where smoothing is elevated.
#
#  Three mutually exclusive regimes:
#    (A) corr(r_full, r_store) < 0 (strongly negative):
#          FB x-hotspots drain residuals before they reach LP1-conj → draining
#          hypothesis confirmed; flatness of closure geometry is mechanistically
#          explained.
#    (B) corr(r_full, r_store) > 0 (positive):
#          x-biased FB feeds forward into residual bias → LP1-conj closures
#          are elevated by the ∑g(x)² mechanism; draining is not the driver.
#    (C) corr ≈ 0:
#          The LP1-conj map T(x_FB, α, P, …) strongly mixes x; FB bias neither
#          concentrates nor drains LP1-conj residuals.
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  _report_d34 — print the x-bucket smoothing-probability diagnostic.
#
#  Arguments:
#    deep_stat — merged ConjDeepStat
#    p         — field characteristic (used only to label x-axis; 0 → "x-coord")
# ---------------------------------------------------------------------------
function _report_d34(deep_stat::ConjDeepStat; p::Int = 0)

    @printf("\n─── D34: x-bucket smoothing-probability (draining hypothesis) ───────\n")

    n_steps = deep_stat.d34_n_steps
    n_0lp   = deep_stat.d34_n_0lp
    n_store = deep_stat.d34_n_store

    total_steps = sum(n_steps)
    total_0lp   = sum(n_0lp)
    total_store = sum(n_store)

    if total_steps == 0
        @printf("  (no D34 data — record_d34_step! not called from walker)\n")
        return
    end

    B = D34_X_BUCKETS

    # -----------------------------------------------------------------------
    #  Per-bucket rates
    # -----------------------------------------------------------------------
    r_full  = zeros(Float64, B)
    r_store = zeros(Float64, B)

    for b in 1:B
        ns = n_steps[b]
        ns == 0 && continue
        r_full[b]  = n_0lp[b]   / ns
        r_store[b] = n_store[b] / ns
    end

    # Global mean rates (for lift normalisation).
    mean_r_full  = total_steps > 0 ? total_0lp   / total_steps : 0.0
    mean_r_store = total_steps > 0 ? total_store / total_steps : 0.0

    # -----------------------------------------------------------------------
    #  Pearson correlation between r_full and r_store across occupied buckets.
    # -----------------------------------------------------------------------
    occupied = [b for b in 1:B if n_steps[b] > 0]
    n_occ    = length(occupied)

    corr_val = NaN
    if n_occ >= 3
        xs = [r_full[b]  for b in occupied]
        ys = [r_store[b] for b in occupied]
        mx = sum(xs) / n_occ
        my = sum(ys) / n_occ
        num   = sum((xs[i] - mx) * (ys[i] - my) for i in 1:n_occ)
        var_x = sum((x - mx)^2 for x in xs)
        var_y = sum((y - my)^2 for y in ys)
        denom = sqrt(var_x * var_y)
        corr_val = denom > 0 ? num / denom : NaN
    end

    # -----------------------------------------------------------------------
    #  Header summary
    # -----------------------------------------------------------------------
    @printf("  Total walk steps logged : %d\n", total_steps)
    @printf("  Total 0-LP (full rel)   : %d  (mean rate %.3e per step)\n",
            total_0lp, mean_r_full)
    @printf("  Total LP1-conj stores   : %d  (mean rate %.3e per step)\n",
            total_store, mean_r_store)
    @printf("  Occupied x-buckets      : %d / %d\n", n_occ, B)
    @printf("\n")

    if !isnan(corr_val)
        @printf("  corr(Pr[full|x], Pr[store|x])  =  %+.4f\n", corr_val)
        if corr_val < -0.3
            @printf("  → NEGATIVE correlation: draining hypothesis SUPPORTED.\n")
            @printf("    Hot x-bands are consumed into full relations before LP1-conj\n")
            @printf("    residuals accumulate, flattening the closure distribution.\n")
        elseif corr_val > 0.3
            @printf("  → POSITIVE correlation: feed-forward bias SUPPORTED.\n")
            @printf("    x-biased FB inflates LP1-conj residuals in the same bands,\n")
            @printf("    increasing Σg(x)² and raising α₂.\n")
        else
            @printf("  → NEAR-ZERO correlation: x-mixing hypothesis supported.\n")
            @printf("    The LP1-conj map T(x, α, …) mixes x; FB bias neither\n")
            @printf("    concentrates nor drains LP1-conj residuals.\n")
        end
    else
        @printf("  corr(Pr[full|x], Pr[store|x])  =  N/A (too few occupied buckets)\n")
    end

    # -----------------------------------------------------------------------
    #  Renyi-2 concentration of store-rate distribution vs uniform
    #   Σ_b (r_store[b])^2 / (Σ_b r_store[b])^2 × B
    #  = 1 for uniform, > 1 for concentrated.
    # -----------------------------------------------------------------------
    sum_r2  = sum(r_store[b]^2 for b in occupied)
    sum_r   = sum(r_store[b]   for b in occupied)
    renyi2_store = (sum_r > 0 && n_occ > 0) ?
                   (sum_r2 / (sum_r^2 / n_occ)) : NaN

    sum_r2f  = sum(r_full[b]^2 for b in occupied)
    sum_rf   = sum(r_full[b]   for b in occupied)
    renyi2_full = (sum_rf > 0 && n_occ > 0) ?
                  (sum_r2f / (sum_rf^2 / n_occ)) : NaN

    @printf("\n")
    @printf("  Rényi-2 concentration (1 = uniform, >1 = concentrated):\n")
    isnan(renyi2_full)  || @printf("    Pr[full|x]  :  %.4f\n", renyi2_full)
    isnan(renyi2_store) || @printf("    Pr[store|x] :  %.4f\n", renyi2_store)

    # -----------------------------------------------------------------------
    #  Per-bucket table: show top-20 x-buckets by n_steps, with both rates.
    # -----------------------------------------------------------------------
    @printf("\n")
    @printf("  Per-bucket table (top 20 by step count):\n")
    @printf("  %-6s  %-14s  %-10s  %-8s  %-10s  %-8s  %-10s  %-8s\n",
            "bucket", "x-range", "n_steps", "n_0lp", "r_full", "n_store", "r_store", "lift_store")
    @printf("  %s\n", "─"^84)

    # Sort by n_steps descending; show top 20.
    order = sortperm(n_steps, rev=true)
    shown = 0
    for b in order
        shown >= 20 && break
        n_steps[b] == 0 && break
        shown += 1

        # x-range label
        lo_frac = (b - 1) / B
        hi_frac = b       / B
        x_lo = p > 0 ? round(Int, lo_frac * p) : round(Int, lo_frac * 1000)
        x_hi = p > 0 ? round(Int, hi_frac * p) : round(Int, hi_frac * 1000)
        x_label = p > 0 ? @sprintf("[%d,%d)", x_lo, x_hi) :
                           @sprintf("[%.3f,%.3f)", lo_frac, hi_frac)

        lift_store = mean_r_store > 0 ? r_store[b] / mean_r_store : NaN

        @printf("  %-6d  %-14s  %-10d  %-8d  %-8.3e  %-10d  %-8.3e  %-8.3f\n",
                b, x_label,
                n_steps[b], n_0lp[b], r_full[b],
                n_store[b], r_store[b],
                isnan(lift_store) ? 0.0 : lift_store)
    end

    # -----------------------------------------------------------------------
    #  Scatter-plot proxy: ASCII sparklines of r_full and r_store across all
    #  occupied buckets in x-order, so the reader can see the profile visually.
    # -----------------------------------------------------------------------
    @printf("\n")
    @printf("  ASCII profile across x-buckets (occupied only, x-order):\n")
    _d34_sparkline("  Pr[full|x] ", r_full,  occupied, 50)
    _d34_sparkline("  Pr[store|x]", r_store, occupied, 50)

    @printf("\n")
    flush(stdout)
    return nothing
end

# ---------------------------------------------------------------------------
#  _d34_sparkline — print a single-row ASCII bar chart of rate[b] for b in
#  `occ` (assumed x-ordered), scaled to `width` chars.
# ---------------------------------------------------------------------------
function _d34_sparkline(label::String,
                         rate ::Vector{Float64},
                         occ  ::Vector{Int},
                         width::Int)
    isempty(occ) && return
    max_r = maximum(rate[b] for b in occ)
    max_r <= 0.0 && return

    # 1. Collect as a Vector of Chars to maintain safe 1-based indexing per character
    bars = Vector{Char}(undef, length(occ))
    chars = ['▁','▂','▃','▄','▅','▆','▇','█']
    for (i, b) in enumerate(occ)
        frac = rate[b] / max_r
        idx  = clamp(round(Int, frac * (length(chars) - 1)) + 1, 1, length(chars))
        bars[i] = chars[idx]
    end

    # 2. Downsample directly on the Vector{Char} instead of a raw String
    if length(bars) > width
        step_d = length(bars) / width
        compressed = Vector{Char}(undef, width)
        for i in 1:width
            lo = round(Int, (i-1) * step_d) + 1
            hi = round(Int, i     * step_d)
            hi = clamp(hi, lo, length(bars))
            
            # This slice is now perfectly safe because it operates on a Vector{Char}
            seg = bars[lo:hi]
            compressed[i] = maximum(seg)
        end
        bars = compressed
    end

    # 3. Convert to String only at the very end for display
    @printf("  %s │%s│  peak=%.3e\n", label, String(bars), max_r)
end
