# =============================================================================
#  lp1_conj_deep_diag_d26.jl  —  D26: X1/X2 occurrence-set spread asymmetry.
#
#  Hypothesis (GPT): take the set of LP1-conj keys that have a closure. Each
#  such key has exactly two recorded occurrences: the STORE (first occurrence,
#  step = store_step) and the CLOSE (second occurrence, step = close_step =
#  raw_steps at closure time).
#
#  Form two populations across all closed keys:
#    X1 = { store_step(k) : k closed }   — first-occurrence steps
#    X2 = { close_step(k) : k closed }   — second-occurrence steps
#
#  The hypothesis: spread(X1) and spread(X2) (max−min, or std) will NOT both
#  be large or both be small. One of the two populations will be temporally
#  diffuse (wide spread) while the other is temporally concentrated (narrow
#  spread) — an asymmetry between "when keys first appear" and "when they
#  close", rather than both tracking the same overall walk-length spread.
#
#  This is a population-level comparison, not a per-key correlation: we are
#  comparing the spread of the set of first-occurrence times against the
#  spread of the set of second-occurrence times.
#
#  Data used (per LP1-conj key, from record_conj_deep_step!/record_conj_deep_miss!):
#    d26_step_range   : Dict{UInt128,(min_step,max_step)} — (store_step, close_step)
#                        per key (lo=store/first occurrence, hi=close/second occurrence)
#    d26_close_count  : Dict{UInt128,Int} — number of closures per key (≥1 selects
#                        keys that have both a store and a close occurrence)
#    d26_partner_mask : Dict{UInt128,UInt64} — bloom over i0 % 64 (retained for
#                        secondary partner-diversity context, not central to the
#                        X1/X2 test)
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  _d26_pearson / _d26_spearman / _d26_bootstrap_ci / _d26_quantile
#  — unchanged math helpers.
#  — unchanged math helpers.
# ---------------------------------------------------------------------------
function _d26_pearson(x::Vector{Float64}, y::Vector{Float64})::Float64
    n = length(x)
    n < 2 && return NaN
    mx = sum(x) / n;  my = sum(y) / n
    num = 0.0; sx = 0.0; sy = 0.0
    for i in 1:n
        dx = x[i] - mx; dy = y[i] - my
        num += dx * dy; sx += dx * dx; sy += dy * dy
    end
    denom = sqrt(sx * sy)
    denom < 1e-30 && return NaN
    clamp(num / denom, -1.0, 1.0)
end

function _d26_rankvec(v::Vector{Float64})::Vector{Float64}
    n = length(v); idx = sortperm(v); rnks = zeros(Float64, n)
    i = 1
    while i <= n
        j = i
        while j < n && v[idx[j+1]] == v[idx[i]]; j += 1; end
        avg_rank = (i + j) / 2.0
        for k in i:j; rnks[idx[k]] = avg_rank; end
        i = j + 1
    end
    rnks
end

function _d26_spearman(x::Vector{Float64}, y::Vector{Float64})::Float64
    length(x) < 2 && return NaN
    _d26_pearson(_d26_rankvec(x), _d26_rankvec(y))
end

function _d26_bootstrap_ci(x::Vector{Float64}, y::Vector{Float64};
                            n_boot::Int = 500)::NTuple{2,Float64}
    n = length(x); n < 10 && return (NaN, NaN)
    rs = Vector{Float64}(undef, n_boot)
    for b in 1:n_boot
        idx = [rand(1:n) for _ in 1:n]
        rs[b] = _d26_pearson(x[idx], y[idx])
    end
    sort!(rs)
    (rs[max(1, round(Int, 0.025*n_boot))], rs[min(end, round(Int, 0.975*n_boot))])
end

function _d26_quantile(sv::Vector{Float64}, q::Float64)::Float64
    isempty(sv) && return NaN
    sv[clamp(round(Int, q*(length(sv)-1))+1, 1, length(sv))]
end

# ---------------------------------------------------------------------------
#  _report_d26 — X1 (first-occurrence / store) vs X2 (second-occurrence /
#  close) spread asymmetry across all keys that have a closure.
# ---------------------------------------------------------------------------
function _report_d26(deep_stat::ConjDeepStat)
    @printf("\n── D26  X1/X2 occurrence-set spread asymmetry ──────────────────────────\n")

    step_range = deep_stat.d26_step_range
    pmask      = deep_stat.d26_partner_mask
    ccount     = deep_stat.d26_close_count

    # Keys that have at least one closure AND a recorded (store, close) step pair.
    # step_range[k] = (lo, hi) where lo = store_step (first occurrence),
    #                                hi = close_step (second occurrence, raw_steps at close).
    keys_with_close = [k for k in keys(ccount) if ccount[k] >= 1 && haskey(step_range, k)]
    n = length(keys_with_close)

    n_close_total = length(keys(ccount))
    n_missing     = count(k -> !haskey(step_range, k), keys(ccount))

    @printf("  Keys with ≥1 closure          : %d\n", n_close_total)
    @printf("  ...with recorded (X1,X2) pair : %d\n", n)
    if n_missing > 0
        @printf("  (note: %d closed keys lack a recorded store_step — excluded from X1/X2)\n",
                n_missing)
    end

    if n < 2
        @printf("  (too few keys with both occurrences recorded — skipping D26)\n")
        return
    end

    X1 = Float64[Float64(step_range[k][1]) for k in keys_with_close]   # store steps
    X2 = Float64[Float64(step_range[k][2]) for k in keys_with_close]   # close steps

    # ── D26.1 X1 / X2 distributions ─────────────────────────────────────────
    @printf("\n  D26.1  X1 (first occurrence / store step) distribution  (n=%d)\n", n)
    sort_X1 = sort(X1)
    @printf("    min=%.0f  p10=%.0f  p25=%.0f  med=%.0f  p75=%.0f  p90=%.0f  max=%.0f\n",
            sort_X1[1],
            _d26_quantile(sort_X1, 0.10), _d26_quantile(sort_X1, 0.25),
            _d26_quantile(sort_X1, 0.50), _d26_quantile(sort_X1, 0.75),
            _d26_quantile(sort_X1, 0.90), sort_X1[end])

    @printf("\n  D26.2  X2 (second occurrence / close step) distribution  (n=%d)\n", n)
    sort_X2 = sort(X2)
    @printf("    min=%.0f  p10=%.0f  p25=%.0f  med=%.0f  p75=%.0f  p90=%.0f  max=%.0f\n",
            sort_X2[1],
            _d26_quantile(sort_X2, 0.10), _d26_quantile(sort_X2, 0.25),
            _d26_quantile(sort_X2, 0.50), _d26_quantile(sort_X2, 0.75),
            _d26_quantile(sort_X2, 0.90), sort_X2[end])

    # ── D26.3 Spread comparison ─────────────────────────────────────────────
    range_X1 = sort_X1[end] - sort_X1[1]
    range_X2 = sort_X2[end] - sort_X2[1]

    mean_X1 = sum(X1) / n;  mean_X2 = sum(X2) / n
    std_X1  = sqrt(sum((x - mean_X1)^2 for x in X1) / (n - 1))
    std_X2  = sqrt(sum((x - mean_X2)^2 for x in X2) / (n - 1))

    cv_X1 = std_X1 / max(1.0, mean_X1)
    cv_X2 = std_X2 / max(1.0, mean_X2)

    @printf("\n  D26.3  Spread comparison: X1 (store) vs X2 (close)\n")
    @printf("    range(X1) = %.0f   std(X1) = %.1f   CV(X1) = %.4f\n", range_X1, std_X1, cv_X1)
    @printf("    range(X2) = %.0f   std(X2) = %.1f   CV(X2) = %.4f\n", range_X2, std_X2, cv_X2)

    ratio_range = range_X1 / max(1.0, range_X2)
    ratio_std   = std_X1   / max(1.0, std_X2)
    @printf("    range(X1)/range(X2) = %.4f      std(X1)/std(X2) = %.4f\n",
            ratio_range, ratio_std)

    # Asymmetry classification: hypothesis predicts one population diffuse,
    # the other concentrated — NOT both wide or both narrow relative to each
    # other. Use the CV ratio as the primary signal (scale-free).
    cv_ratio = cv_X1 / max(1e-12, cv_X2)
    @printf("    CV(X1)/CV(X2) = %.4f\n", cv_ratio)

    if cv_ratio > 3.0
        @printf("    ★ ASYMMETRIC: X1 (store steps) is far more spread than X2 (close steps).\n")
        @printf("      First occurrences are temporally diffuse; closures cluster narrowly.\n")
        @printf("      Consistent with the trajectory-time concentration hypothesis.\n")
    elseif cv_ratio < 1.0/3.0
        @printf("    ★ ASYMMETRIC: X2 (close steps) is far more spread than X1 (store steps).\n")
        @printf("      Closures are temporally diffuse while first occurrences cluster narrowly.\n")
        @printf("      Consistent with the trajectory-time concentration hypothesis (reversed).\n")
    else
        @printf("    ○ SYMMETRIC: X1 and X2 have comparable spread (CV ratio within 3×).\n")
        @printf("      No strong diffuse/concentrated asymmetry detected between\n")
        @printf("      first- and second-occurrence populations.\n")
    end

    # ── D26.4 Per-key (X1,X2) deviation-sign table ──────────────────────────
    # For each key, is it "early/late in X1" vs "early/late in X2" relative to
    # its own population median? Counts of (above,above)/(above,below)/etc.
    # combinations probe whether individual keys swap diffuse/concentrated
    # roles between occurrences, beyond the aggregate spread comparison above.
    med_X1 = _d26_quantile(sort_X1, 0.5)
    med_X2 = _d26_quantile(sort_X2, 0.5)
    n_hh = 0; n_hl = 0; n_lh = 0; n_ll = 0
    for i in 1:n
        a = X1[i] > med_X1
        b = X2[i] > med_X2
        if a && b
            n_hh += 1
        elseif a && !b
            n_hl += 1
        elseif !a && b
            n_lh += 1
        else
            n_ll += 1
        end
    end
    @printf("\n  D26.4  Per-key quadrant counts (relative to medians)\n")
    @printf("    X1>med & X2>med (both late)  : %d  (%.1f%%)\n", n_hh, 100*n_hh/n)
    @printf("    X1>med & X2≤med (early-close): %d  (%.1f%%)\n", n_hl, 100*n_hl/n)
    @printf("    X1≤med & X2>med (late-close) : %d  (%.1f%%)\n", n_lh, 100*n_lh/n)
    @printf("    X1≤med & X2≤med (both early) : %d  (%.1f%%)\n", n_ll, 100*n_ll/n)
    diag_frac = (n_hh + n_ll) / n
    if diag_frac > 0.6
        @printf("    ↑ Diagonal-dominant: X1 and X2 rank order together per key (no swap).\n")
    elseif diag_frac < 0.4
        @printf("    ↑ Off-diagonal-dominant: keys swap early/late between occurrences.\n")
    else
        @printf("    ○ No strong per-key ordering pattern.\n")
    end

    # ── D26.5 Secondary context: partner-mask popcount ──────────────────────
    NP = Float64[Float64(count_ones(get(pmask, k, UInt64(0)))) for k in keys_with_close]
    @printf("\n  D26.5  Distinct (i0 %% 64) partner buckets per key  (popcount of bloom mask)\n")
    sort_NP = sort(NP)
    @printf("    min=%.0f  med=%.0f  p90=%.0f  max=%.0f\n",
            sort_NP[1], _d26_quantile(sort_NP, 0.5), _d26_quantile(sort_NP, 0.9), sort_NP[end])

    # ── D26 summary ───────────────────────────────────────────────────────
    @printf("\n  D26 summary: %d keys with closures. CV(X1)/CV(X2) = %.4f.\n", n, cv_ratio)
    @printf("    X1 = store-step set, X2 = close-step set across closed keys.\n")
    flush(stdout)
    return nothing
end
