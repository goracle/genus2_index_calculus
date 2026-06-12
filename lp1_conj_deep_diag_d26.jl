# =============================================================================
#  lp1_conj_deep_diag_d26.jl  —  D26: Temporal-width / pair-concentration
#                                      anticorrelation probe.
#
#  Hypothesis (GPT): LP1-conj collision concentration lives in trajectory-time
#  rather than coordinate-space.  If so, keys that appear over a wide temporal
#  span W(k) = max(store_step) - min(store_step) should pair with many distinct
#  anchor partners N_pair(k), while temporally localized keys pair with few.
#
#  Prediction:  corr( log W(k), log N_pair(k) ) << 0.
#
#  Measurement:
#    W(k)      — recorded via d26_step_range in record_conj_deep_miss! (STORE).
#    N_pair(k) — approximated by count_ones(d26_partner_mask[k]), a UInt64
#                bitmask over i0 % 64 updated in record_conj_deep_step! (CLOSE).
#                Exact up to 64 distinct anchors; saturates gracefully beyond.
#
#  Report sections:
#    D26.1 — Summary statistics (n_keys, W distribution, N_pair distribution).
#    D26.2 — Pearson r(log W, log N_pair) with 95% bootstrap CI.
#    D26.3 — Spearman rank correlation (more robust to outliers).
#    D26.4 — W×N_pair product statistics (tests "constant product" variant).
#    D26.5 — Scatter summary: log-W deciles vs mean log-N_pair per decile.
#    D26.6 — Top-20 keys by W and by N_pair (with W×N_pair product).
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d26_pearson — Pearson r of two Float64 vectors.
# ---------------------------------------------------------------------------
function _d26_pearson(x::Vector{Float64}, y::Vector{Float64})::Float64
    n = length(x)
    n < 2 && return NaN
    mx = sum(x) / n
    my = sum(y) / n
    num = 0.0; sx = 0.0; sy = 0.0
    for i in 1:n
        dx = x[i] - mx; dy = y[i] - my
        num += dx * dy
        sx  += dx * dx
        sy  += dy * dy
    end
    denom = sqrt(sx * sy)
    denom < 1e-30 && return NaN
    clamp(num / denom, -1.0, 1.0)
end

# ---------------------------------------------------------------------------
#  _d26_spearman — Spearman rank correlation.
# ---------------------------------------------------------------------------
function _d26_spearman(x::Vector{Float64}, y::Vector{Float64})::Float64
    n = length(x)
    n < 2 && return NaN
    rx = _d26_rankvec(x)
    ry = _d26_rankvec(y)
    _d26_pearson(rx, ry)
end

function _d26_rankvec(v::Vector{Float64})::Vector{Float64}
    n    = length(v)
    idx  = sortperm(v)
    rnks = zeros(Float64, n)
    i    = 1
    while i <= n
        j = i
        while j < n && v[idx[j+1]] == v[idx[i]]
            j += 1
        end
        avg_rank = (i + j) / 2.0
        for k in i:j
            rnks[idx[k]] = avg_rank
        end
        i = j + 1
    end
    rnks
end

# ---------------------------------------------------------------------------
#  _d26_bootstrap_ci — 95% CI on r via 500-sample bootstrap.
# ---------------------------------------------------------------------------
function _d26_bootstrap_ci(x::Vector{Float64}, y::Vector{Float64};
                            n_boot::Int = 500)::NTuple{2,Float64}
    n = length(x)
    n < 10 && return (NaN, NaN)
    rs = Vector{Float64}(undef, n_boot)
    for b in 1:n_boot
        idx = [rand(1:n) for _ in 1:n]
        rs[b] = _d26_pearson(x[idx], y[idx])
    end
    sort!(rs)
    lo = rs[max(1,   round(Int, 0.025 * n_boot))]
    hi = rs[min(end, round(Int, 0.975 * n_boot))]
    (lo, hi)
end

# ---------------------------------------------------------------------------
#  _d26_quantile — simple quantile from sorted vector.
# ---------------------------------------------------------------------------
function _d26_quantile(sorted::Vector{Float64}, q::Float64)::Float64
    isempty(sorted) && return NaN
    idx = clamp(round(Int, q * (length(sorted) - 1)) + 1, 1, length(sorted))
    sorted[idx]
end

# ---------------------------------------------------------------------------
#  _report_d26 — main entry point.
# ---------------------------------------------------------------------------
function _report_d26(deep_stat::ConjDeepStat)
    @printf("\n── D26  Temporal-width / pair-concentration anticorrelation ──────────\n")

    step_range   = deep_stat.d26_step_range
    partner_mask = deep_stat.d26_partner_mask
    close_count  = deep_stat.d26_close_count

    # Only analyse keys that (a) closed at least once and (b) appear in step_range.
    keys_all = collect(keys(close_count))
    filter!(k -> haskey(step_range, k), keys_all)

    n_keys = length(keys_all)
    @printf("  Keys with ≥1 closure and store record : %d\n", n_keys)

    if n_keys < 5
        @printf("  (too few keys for meaningful analysis — skipping D26)\n")
        return
    end

    # Build W(k) and N_pair(k) arrays.
    W      = Vector{Float64}(undef, n_keys)
    Npair  = Vector{Float64}(undef, n_keys)
    Nclos  = Vector{Int}(undef,    n_keys)
    WNprod = Vector{Float64}(undef, n_keys)

    for (idx, k) in enumerate(keys_all)
        lo, hi = step_range[k]
        w      = Float64(max(1, hi - lo))
        mask   = get(partner_mask, k, UInt64(0))
        np     = Float64(max(1, count_ones(mask)))
        W[idx]     = w
        Npair[idx] = np
        Nclos[idx] = close_count[k]
        WNprod[idx] = w * np
    end

    # ── D26.1 Summary ──────────────────────────────────────────────────────
    @printf("\n  D26.1  Distribution summary\n")

    sort_W     = sort(W)
    sort_Np    = sort(Npair)
    sort_prod  = sort(WNprod)

    for (label, sv) in (("W(k)", sort_W), ("N_pair(k)", sort_Np), ("W×N_pair", sort_prod))
        med  = _d26_quantile(sv, 0.5)
        p10  = _d26_quantile(sv, 0.1)
        p90  = _d26_quantile(sv, 0.9)
        mn   = sv[1]; mx = sv[end]
        @printf("    %-12s  min=%8.1f  p10=%8.1f  med=%8.1f  p90=%8.1f  max=%8.1f\n",
                label, mn, p10, med, p90, mx)
    end

    # ── D26.2 Pearson r(log W, log N_pair) ────────────────────────────────
    logW  = log.(W)
    logNp = log.(Npair)

    r_pearson = _d26_pearson(logW, logNp)
    ci_lo, ci_hi = _d26_bootstrap_ci(logW, logNp)

    @printf("\n  D26.2  Pearson r(log W, log N_pair)\n")
    @printf("    r = %+.4f   95%% CI [%+.4f, %+.4f]  (n=%d, 500-sample bootstrap)\n",
            r_pearson, ci_lo, ci_hi, n_keys)

    if isnan(r_pearson)
        @printf("    (insufficient variance for correlation)\n")
    elseif r_pearson < -0.4
        @printf("    ★ STRONG ANTICORRELATION — consistent with time-space duality hypothesis.\n")
    elseif r_pearson < -0.15
        @printf("    ◆ Moderate anticorrelation — partial support for time-space duality.\n")
    elseif r_pearson > 0.15
        @printf("    ✗ Positive correlation — contradicts time-space duality hypothesis.\n")
    else
        @printf("    ○ Near-zero correlation — temporal structure alone insufficient.\n")
    end

    # ── D26.3 Spearman rank correlation ───────────────────────────────────
    r_spearman = _d26_spearman(logW, logNp)
    @printf("\n  D26.3  Spearman ρ(log W, log N_pair) = %+.4f\n", r_spearman)
    if !isnan(r_spearman) && !isnan(r_pearson) && sign(r_spearman) != sign(r_pearson) && abs(r_spearman - r_pearson) > 0.2
        @printf("    (Pearson/Spearman disagree — outliers may be driving Pearson signal)\n")
    end

    # ── D26.4 W×N_pair product test ───────────────────────────────────────
    @printf("\n  D26.4  W × N_pair product  (constant ⟺ perfect duality)\n")
    log_prod  = log.(WNprod)
    prod_mean = sum(log_prod) / n_keys
    prod_std  = sqrt(max(0.0, sum((lp - prod_mean)^2 for lp in log_prod) / (n_keys - 1)))
    prod_cv   = prod_std / max(1e-30, abs(prod_mean))    # coefficient of variation in log space
    @printf("    mean(log(W·N_pair)) = %.3f   std = %.3f   CV = %.3f\n",
            prod_mean, prod_std, prod_cv)
    if prod_cv < 0.5
        @printf("    ★ Low CV — W×N_pair ≈ constant.  Strong constant-product form.\n")
    elseif prod_cv < 1.0
        @printf("    ◆ Moderate CV — partial constant-product form.\n")
    else
        @printf("    ○ High CV — product varies widely; duality is approximate at best.\n")
    end

    # ── D26.5 Decile scatter: log-W decile → mean log-N_pair ──────────────
    @printf("\n  D26.5  log-W decile vs mean log-N_pair (scatter summary)\n")
    @printf("    %6s  %8s  %8s  %6s\n", "decile", "W_lo", "W_hi", "Np_mean")

    idx_by_W = sortperm(W)
    n_dec    = 10
    dec_size = max(1, n_keys ÷ n_dec)
    for d in 1:n_dec
        lo_i   = (d - 1) * dec_size + 1
        hi_i   = d == n_dec ? n_keys : d * dec_size
        lo_i > n_keys && break
        chunk  = idx_by_W[lo_i:hi_i]
        w_lo   = W[chunk[1]]
        w_hi   = W[chunk[end]]
        np_avg = sum(Npair[i] for i in chunk) / length(chunk)
        @printf("    D%-2d     %8.1f  %8.1f  %8.2f\n", d, w_lo, w_hi, np_avg)
    end

    # ── D26.6 Top-20 keys by W and N_pair ─────────────────────────────────
    @printf("\n  D26.6  Top-20 keys by W(k)\n")
    @printf("    %4s  %10s  %8s  %10s  %6s\n",
            "rank", "W(k)", "N_pair", "W×N_pair", "n_cls")
    top_W_idx = partialsortperm(W, 1:min(20, n_keys), rev=true)
    for (r, i) in enumerate(top_W_idx)
        @printf("    %4d  %10.1f  %8.1f  %10.1f  %6d\n",
                r, W[i], Npair[i], WNprod[i], Nclos[i])
    end

    @printf("\n  D26.6b Top-20 keys by N_pair(k)\n")
    @printf("    %4s  %10s  %8s  %10s  %6s\n",
            "rank", "N_pair", "W(k)", "W×N_pair", "n_cls")
    top_Np_idx = partialsortperm(Npair, 1:min(20, n_keys), rev=true)
    for (r, i) in enumerate(top_Np_idx)
        @printf("    %4d  %10.1f  %8.1f  %10.1f  %6d\n",
                r, Npair[i], W[i], WNprod[i], Nclos[i])
    end

    # ── D26 interpretation summary ─────────────────────────────────────────
    @printf("\n  D26 interpretation:\n")
    if !isnan(r_pearson)
        if r_pearson < -0.3 && r_spearman < -0.3
            @printf("    Both Pearson and Spearman anticorrelated (r=%.3f, ρ=%.3f).\n",
                    r_pearson, r_spearman)
            @printf("    Collision concentration is dynamical (trajectory-time), not geometric.\n")
            @printf("    α₂ < 1 arises from temporal localization, not static coordinate structure.\n")
        elseif r_pearson < -0.15 || r_spearman < -0.15
            @printf("    Mild anticorrelation detected (r=%.3f, ρ=%.3f).\n",
                    r_pearson, r_spearman)
            @printf("    Temporal localization is a contributing factor but not the sole explanation.\n")
        else
            @printf("    No clear anticorrelation (r=%.3f, ρ=%.3f).\n",
                    r_pearson, r_spearman)
            @printf("    Time-space duality hypothesis not supported by this data.\n")
        end
    end
    @printf("    N_pair approximation: UInt64 bitmask over i0 %%64 — exact for ≤64 distinct anchors.\n")

    flush(stdout)
    return nothing
end
