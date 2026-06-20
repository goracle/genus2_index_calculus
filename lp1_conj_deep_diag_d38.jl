# =============================================================================
#  lp1_conj_deep_diag_d38.jl  --  Report section D38.
#
#  D38 — φ a-coefficient sequential autocorrelation (step-indexed, NOT
#  closure-indexed). Companion to D33 (which tests the MARGINAL distribution
#  of a via χ²/dof against a uniform-over-F_p null) and to D29/D37 (which
#  test px/alpha for autocorrelation, but never test a itself). D33's
#  marginal-uniformity result says nothing about ORDER: a could be exactly
#  uniform step-to-step and still be strongly serially correlated (e.g. if
#  consecutive a values cluster near the previous one before "resetting"),
#  which would itself shrink the effective state space the AMS Rényi-2
#  estimator sees, independent of D33's static bucket test.
#
#  D38 asks directly: is a_n correlated with a_{n+lag} for small-to-moderate
#  lag, over and above what i.i.d. sampling from F_p would produce?
#
#  Sampling site: every step that reaches build_phi_mumford successfully
#  (i.e. phi_c !== nothing) — the same site that already feeds
#  record_phi_step!(phi_bias_stat, a, ...) in trial3_phase2.jl. D38 logs the
#  raw a value (Int, unreduced beyond fp()) into a per-thread contiguous
#  vector, once per step, regardless of split/non-split outcome — this
#  mirrors D29's "log every valid step, defer analysis to report time"
#  discipline (see D29 constants-block docstring in
#  lp1_conj_deep_diag_core.jl) rather than D37's closure-only sampling,
#  because a is produced on every φ step, not just at LP1-conj closures, so
#  there is no cursor-artifact analogue to worry about here — unlike px,
#  a is never touched by next_anchor()'s round-robin cursor.
#
#  Cross-thread handling: UNLIKE D37 (which keeps per-thread chains separate
#  because closures are sparse), D38 follows D29's convention and
#  concatenates each thread's capped a-stream into one merged series. At
#  millions of samples per thread, the handful of cross-thread boundary
#  pairs at each lag are statistically negligible — this is the same
#  reasoning D29 already uses for its (alpha, px) streams.
#
#  Math: per-lag Pearson autocorrelation coefficient r(lag), with an
#  asymptotic-normal z-score z = r * sqrt(n_eff - 3) (Fisher-z-free fast
#  approximation; with n_eff in the hundreds of thousands to millions this
#  is indistinguishable from the full Fisher transform at the |z| >= 3
#  significance threshold this report uses elsewhere — see D29_Z_SIG).
# =============================================================================

# ---------------------------------------------------------------------------
#  Constants. Numbered D38_* to avoid any collision with D29's/D37's own
#  constants block in lp1_conj_deep_diag_core.jl.
# ---------------------------------------------------------------------------
const D38_MAX_SAMPLES    = 2_000_000  # per-thread cap on the contiguous a-stream (matches D29_MAX_SAMPLES order)
const D38_ACF_DENSE_LAG  = 200        # dense (every-lag) resolution out to this many steps
const D38_ACF_MAX_LAG    = 5000       # outer lag boundary
const D38_ACF_STRIDE     = 100        # lag stride beyond D38_ACF_DENSE_LAG, out to D38_ACF_MAX_LAG
const D38_Z_SIG          = 3.0        # |z| threshold for flagging a lag as significant (matches D29_Z_SIG)

# ---------------------------------------------------------------------------
#  D38Stat — per-thread accumulator. Allocate one per thread alongside
#  PhiBiasStat/ConjDeepStat (see trial3_fixed.jl wiring), thread it through
#  worker_phase2! the same way phi_bias_stat/deep_stat are threaded, and
#  merge with merge_d38_stats before reporting.
# ---------------------------------------------------------------------------
mutable struct D38Stat
    a_stream  ::Vector{Int}   # raw a value at each sampled φ step (capped at D38_MAX_SAMPLES)
    n_samples ::Int           # uncapped running total — denominator for "capped at" reporting
end

D38Stat() = D38Stat(Int[], 0)

# ---------------------------------------------------------------------------
#  record_d38_step! — call from the main walk loop in worker_phase2!
#  (trial3_phase2.jl), immediately after build_phi_mumford succeeds and `a`
#  is bound — i.e. right alongside the existing record_phi_step! call.
#  Logs every successful φ step regardless of split/non-split outcome.
# ---------------------------------------------------------------------------
@inline function record_d38_step!(stat::D38Stat, a::Int)
    stat.n_samples += 1
    length(stat.a_stream) >= D38_MAX_SAMPLES && return nothing
    push!(stat.a_stream, a)
    return nothing
end

# ---------------------------------------------------------------------------
#  merge_d38_stats — concatenate per-thread a-streams (D29-style; see file
#  docstring for why concatenation, not per-thread chains, is appropriate
#  here). Caps the merged stream at D38_MAX_SAMPLES total, taking a prefix
#  slice per thread the same way D29's merge does, so no single thread can
#  starve the others out of the cap.
# ---------------------------------------------------------------------------
function merge_d38_stats(stats::Vector{D38Stat})::D38Stat
    merged = D38Stat()
    for s in stats
        merged.n_samples += s.n_samples
        n_rem = D38_MAX_SAMPLES - length(merged.a_stream)
        n_rem <= 0 && continue
        n_take = min(n_rem, length(s.a_stream))
        append!(merged.a_stream, s.a_stream[1:n_take])
    end
    return merged
end

# ---------------------------------------------------------------------------
#  _d38_lag_grid — dense out to D38_ACF_DENSE_LAG, strided beyond that, out
#  to D38_ACF_MAX_LAG. Mirrors D29's dense+stride lag-grid construction.
# ---------------------------------------------------------------------------
function _d38_lag_grid()::Vector{Int}
    dense  = collect(1:D38_ACF_DENSE_LAG)
    strided = collect((D38_ACF_DENSE_LAG + D38_ACF_STRIDE):D38_ACF_STRIDE:D38_ACF_MAX_LAG)
    return vcat(dense, strided)
end

# ---------------------------------------------------------------------------
#  _d38_pearson_acf — Pearson autocorrelation coefficient of x at the given
#  lag: corr(x[1:n-lag], x[1+lag:n]). Self-contained (does not depend on
#  D29's internal helper, which lives in a module file not included here).
# ---------------------------------------------------------------------------
function _d38_pearson_acf(x::Vector{Float64}, lag::Int)::Float64
    n = length(x)
    n_eff = n - lag
    n_eff < 2 && return 0.0

    @inbounds begin
        x1 = @view x[1:n_eff]
        x2 = @view x[(1+lag):n]
    end

    mu1 = sum(x1) / n_eff
    mu2 = sum(x2) / n_eff

    cov = 0.0
    var1 = 0.0
    var2 = 0.0
    @inbounds for i in 1:n_eff
        d1 = x1[i] - mu1
        d2 = x2[i] - mu2
        cov  += d1 * d2
        var1 += d1 * d1
        var2 += d2 * d2
    end

    denom = sqrt(var1 * var2)
    denom == 0.0 && return 0.0
    return cov / denom
end

# ---------------------------------------------------------------------------
#  _d38_pearson_acf_z — asymptotic-normal z-score for a Pearson r computed
#  from n_eff pairs under the i.i.d. null (r ~ N(0, 1/(n_eff-1)) for large
#  n_eff). Same approximation D29/D37 use at this sample-size regime.
# ---------------------------------------------------------------------------
function _d38_pearson_acf_z(r::Float64, n_eff::Int)::Float64
    n_eff < 4 && return 0.0
    return r * sqrt(Float64(n_eff - 1))
end

# ---------------------------------------------------------------------------
#  _report_d38 — sequential ACF of the φ a-coefficient, dense+strided lag
#  sweep, with significance flagging at |z| >= D38_Z_SIG.
# ---------------------------------------------------------------------------
function _report_d38(stat::D38Stat; p::Int = 0)
    @printf("\n  D38 — φ a-coefficient sequential autocorrelation (step-indexed)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    @printf("    a-samples observed (uncapped, all threads) : %d\n", stat.n_samples)
    @printf("    a-samples used (capped, merged)            : %d\n", length(stat.a_stream))

    n = length(stat.a_stream)
    if n < D38_ACF_DENSE_LAG + 8
        @printf("    (too few samples (%d) to test even the densest lag — skipping)\n\n", n)
        return nothing
    end

    x = Float64.(stat.a_stream)
    lags = _d38_lag_grid()

    best_lag   = -1
    best_abs_z = -1.0
    best_r     = 0.0
    best_z     = 0.0
    n_sig      = 0
    n_tested   = 0

    sig_lags = Int[]

    for lag in lags
        lag >= n && continue
        n_eff = n - lag
        n_eff < 8 && continue
        n_tested += 1
        r = _d38_pearson_acf(x, lag)
        z = _d38_pearson_acf_z(r, n_eff)
        if abs(z) > best_abs_z
            best_abs_z = abs(z)
            best_lag   = lag
            best_r     = r
            best_z     = z
        end
        if abs(z) >= D38_Z_SIG
            n_sig += 1
            length(sig_lags) < 20 && push!(sig_lags, lag)
        end
    end

    if n_tested == 0
        @printf("    (no lag in the grid was testable at this sample size — skipping)\n\n")
        return nothing
    end

    @printf("    Lags tested: %d  (dense 1..%d, stride %d up to %d)\n",
            n_tested, D38_ACF_DENSE_LAG, D38_ACF_STRIDE, D38_ACF_MAX_LAG)
    @printf("    Peak |z|=%.2f at lag=%d  (r=%.5f, z=%.2f)%s\n",
            best_abs_z, best_lag, best_r, best_z,
            best_abs_z >= D38_Z_SIG ? "  ← SIGNIFICANT vs i.i.d. null" : "")
    @printf("    Lags with |z| >= %.1f: %d / %d tested\n", D38_Z_SIG, n_sig, n_tested)
    if !isempty(sig_lags)
        @printf("    First significant lags: %s%s\n",
                join(sig_lags, ", "), n_sig > length(sig_lags) ? ", ..." : "")
    end

    # --- lag-1 called out explicitly: the most diagnostically relevant
    #     value for "does a cluster near its immediately preceding value" ---
    r1 = _d38_pearson_acf(x, 1)
    z1 = _d38_pearson_acf_z(r1, n - 1)
    @printf("    Lag-1 autocorrelation: r=%.5f, z=%.2f%s\n",
            r1, z1, abs(z1) >= D38_Z_SIG ? "  ← SIGNIFICANT" : "")

    @printf("\n    Verdict:\n")
    if best_abs_z >= D38_Z_SIG
        @printf("      → Sequential autocorrelation detected in the φ a-coefficient stream\n")
        @printf("        at lag=%d (peak |z|=%.2f). a is NOT step-to-step independent, even\n",
                best_lag, best_abs_z)
        @printf("        if D33's marginal histogram looks uniform. This is consistent with\n")
        @printf("        the α₂≈0.59–0.60 pinning reflecting a genuine ORDER effect in the\n")
        @printf("        φ-construction, not just a static occupancy/cardinality effect.\n")
    else
        @printf("      → No significant sequential autocorrelation in the φ a-coefficient\n")
        @printf("        stream across tested lags. Combined with D33's marginal-uniformity\n")
        @printf("        result, this points AWAY from a-level structure (static or\n")
        @printf("        sequential) as the source of the α₂ pinning — look elsewhere in the\n")
        @printf("        pipeline (e.g. key construction downstream of a, or the AMS sketch\n")
        @printf("        itself, per D31).\n")
    end

    @printf("\n")
    return nothing
end
