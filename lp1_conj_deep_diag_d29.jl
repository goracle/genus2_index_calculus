# =============================================================================
#  lp1_conj_deep_diag_d29.jl  --  Report section D29.
#
#  D29 — wide-lag burst-memory trackers: α mod-q autocorrelation (phase-
#  locking), p_x spatial autocorrelation (basin trapping), and (α,p_x)
#  rolling cross-correlation / mutual information (dynamic steering).
#
#  See the D29 constants-block docstring in lp1_conj_deep_diag_core.jl for
#  the full hypothesis writeup (CIR-ACF burst follow-up: Fano-factor
#  blowup, τ* ≈ 4128 steps). This file is included by lp1_conj_deep_diag.jl
#  and operates on the merged ConjDeepStat's d29_alpha / d29_px vectors,
#  which hold a CONTIGUOUS, full-rate sample of (alpha_cur, px) recorded
#  once per valid walk step.
#
#  All math here (mod-q reduction, circular autocorrelation, p_x bucketing,
#  joint-histogram MI) operates on the raw stored values — nothing is
#  pre-reduced at record time, per this file's deferred-computation
#  convention (see D30/D35/D34 for precedent).
# =============================================================================

# ---------------------------------------------------------------------------
#  _d29_circular_acf — circular autocorrelation of a residue stream mod q
#  at a given lag, defined as mean(cos(2π/q * (r[i] - r[i+lag]))).
#
#  Why circular rather than linear (Pearson) correlation: residues mod q
#  live on a cycle (0 and q-1 are adjacent, not far apart), so a phase-
#  locking effect that wraps around (e.g. r alternating between q-1 and 0)
#  would be INVISIBLE to a naive linear correlation of the integer residue
#  values but is exactly what this statistic is built to detect. Under the
#  null (residues i.i.d. uniform over Z_q, or any two residues at this lag
#  independent), E[stat] = 0 and Var[stat] = 1/(2*n_eff) for q > 2 (q=2 is
#  degenerate — cos(π*Δ) = ±1 always, so for q=2 this reduces to the
#  ordinary ±1 correlation, which is fine and still has the same null
#  variance form).
#
#  Throws if lag is out of range — silently clamping would produce a
#  plausible-looking but wrong ACF value at the wrong lag.
# ---------------------------------------------------------------------------
function _d29_circular_acf(residues::Vector{Int}, q::Int, lag::Int)::Float64
    n = length(residues)
    if lag <= 0 || lag >= n
        throw(ArgumentError("_d29_circular_acf: lag=$lag out of range for n=$n"))
    end
    n_eff = n - lag
    two_pi_over_q = 2.0 * pi / q
    acc = 0.0
    @inbounds for i in 1:n_eff
        dtheta = two_pi_over_q * Float64(residues[i] - residues[i + lag])
        acc += cos(dtheta)
    end
    return acc / n_eff
end

# ---------------------------------------------------------------------------
#  _d29_circular_acf_z — z-score of the circular ACF statistic against the
#  i.i.d.-uniform null (stderr = 1/sqrt(2*n_eff)).
# ---------------------------------------------------------------------------
function _d29_circular_acf_z(acf_val::Float64, n_eff::Int)::Float64
    n_eff <= 0 && throw(ArgumentError("_d29_circular_acf_z: n_eff=$n_eff must be positive"))
    stderr_null = 1.0 / sqrt(2.0 * n_eff)
    return acf_val / stderr_null
end

# ---------------------------------------------------------------------------
#  _d29_pearson_acf — ordinary (linear) Pearson autocorrelation of a
#  Float64 series at a given lag. Used for p_x, which is NOT treated as
#  circular here: unlike D30's closure-pair Δx (where wraparound near the
#  p-1/0 boundary matters for a single difference), a basin-trapping
#  signal over a wide window is a local/linear effect — the walk dwelling
#  near one region of [0,p) — and standard correlation is the right tool.
#
#  Throws if lag is out of range, same rationale as _d29_circular_acf.
# ---------------------------------------------------------------------------
function _d29_pearson_acf(x::Vector{Float64}, lag::Int)::Float64
    n = length(x)
    if lag <= 0 || lag >= n
        throw(ArgumentError("_d29_pearson_acf: lag=$lag out of range for n=$n"))
    end
    n_eff = n - lag
    @views x1 = x[1:n_eff]
    @views x2 = x[(1 + lag):n]
    mu1 = sum(x1) / n_eff
    mu2 = sum(x2) / n_eff
    num  = 0.0
    var1 = 0.0
    var2 = 0.0
    @inbounds for i in 1:n_eff
        d1 = x1[i] - mu1
        d2 = x2[i] - mu2
        num  += d1 * d2
        var1 += d1 * d1
        var2 += d2 * d2
    end
    denom = sqrt(var1 * var2)
    return denom > 0.0 ? num / denom : 0.0
end

# ---------------------------------------------------------------------------
#  _d29_pearson_acf_z — z-score of the Pearson ACF against the i.i.d. null
#  (stderr ≈ 1/sqrt(n_eff)).
# ---------------------------------------------------------------------------
function _d29_pearson_acf_z(acf_val::Float64, n_eff::Int)::Float64
    n_eff <= 0 && throw(ArgumentError("_d29_pearson_acf_z: n_eff=$n_eff must be positive"))
    return acf_val * sqrt(Float64(n_eff))
end

# ---------------------------------------------------------------------------
#  _d29_px_bucket — bucket px into [0, D29_MI_GRID_SIZE) using the OBSERVED
#  min/max of the sample (same convention as D12's data-range bucketing —
#  see filtered_output's "grid: 64 × 64 (..., px_range=[0,2363907])" — p is
#  not threaded into a fixed bucket width here for the same reason D12
#  doesn't use it: the observed sample range is what the MI estimate
#  actually conditions on).
# ---------------------------------------------------------------------------
@inline function _d29_px_bucket(px::Int, lo::Int, hi::Int)::Int
    hi <= lo && return 0
    bkt = Int(floor((px - lo) * D29_MI_GRID_SIZE / (hi - lo + 1)))
    return clamp(bkt, 0, D29_MI_GRID_SIZE - 1)
end

# ---------------------------------------------------------------------------
#  _d29_mutual_information_bits — plug-in MI estimate (bits) from a joint
#  count matrix. No bias correction is applied here; the caller compares
#  against the standard finite-sample bias estimate
#  (rows-1)*(cols-1) / (2*N*ln2) (Miller-Madow-style) rather than treating
#  the raw value as exact.
# ---------------------------------------------------------------------------
function _d29_mutual_information_bits(joint::Matrix{Int})::Float64
    total = sum(joint)
    total == 0 && return 0.0
    nr, nc = size(joint)
    row_sums = vec(sum(joint, dims = 2))
    col_sums = vec(sum(joint, dims = 1))
    mi = 0.0
    @inbounds for j in 1:nc, i in 1:nr
        cij = joint[i, j]
        cij == 0 && continue
        pij = cij / total
        pi_ = row_sums[i] / total
        pj_ = col_sums[j] / total
        mi += pij * log2(pij / (pi_ * pj_))
    end
    return mi
end

# ---------------------------------------------------------------------------
#  _d29_lag_grid — dense lags 1..D29_ACF_DENSE_LAG, then strided lags out
#  to D29_ACF_MAX_LAG.
# ---------------------------------------------------------------------------
function _d29_lag_grid()::Vector{Int}
    lags = collect(1:D29_ACF_DENSE_LAG)
    nxt = D29_ACF_DENSE_LAG + D29_ACF_STRIDE
    while nxt <= D29_ACF_MAX_LAG
        push!(lags, nxt)
        nxt += D29_ACF_STRIDE
    end
    return lags
end

# ---------------------------------------------------------------------------
#  _report_d29 — α mod-q ACF, p_x spatial ACF, (α,p_x) rolling cross-MI.
# ---------------------------------------------------------------------------
function _report_d29(deep_stat::ConjDeepStat; p::Int = 0, ell::Int = 0)
    @printf("\n  D29 — Wide-lag burst-memory trackers (α mod-q ACF, p_x spatial ACF, α/p_x CCF)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    n_seen = deep_stat.d29_n_samples
    alpha_v = deep_stat.d29_alpha
    px_v    = deep_stat.d29_px
    n = length(alpha_v)

    if length(px_v) != n
        throw(AssertionError("_report_d29: d29_alpha/d29_px length mismatch " *
            "($n vs $(length(px_v))) — recording or merge invariant violated"))
    end

    @printf("    Steps observed (uncapped)   : %d\n", n_seen)
    @printf("    Samples in merged buffer    : %d  (capped at %d)\n", n, D29_MAX_SAMPLES)

    min_required = 2 * D29_ACF_MAX_LAG
    if n < min_required
        @printf("    (too few samples for wide-lag ACF/CCF: need >= %d, have %d)\n\n",
                min_required, n)
        return nothing
    end

    # ── 1. α mod-q circular autocorrelation (phase-locking) ────────────────
    @printf("\n    1. α mod-q circular autocorrelation (phase-locking)\n")
    @printf("    -----------------------------------------------------------------\n")
    primary_q = D29_PRIMES[1]
    dense_grid = _d29_lag_grid()

    for (qi, q) in enumerate(D29_PRIMES)
        residues = mod.(alpha_v, q)
        lags = qi == 1 ? dense_grid : collect(D29_MI_LAG_STRIDE:D29_MI_LAG_STRIDE:D29_ACF_MAX_LAG)

        best_lag = -1
        best_abs = -1.0
        best_val = 0.0
        best_z   = 0.0
        decorr_lag = -1   # first lag (scanning upward) at which |z| < D29_Z_SIG, after having seen a significant lag

        seen_significant = false
        for lag in lags
            n_eff = n - lag
            val = _d29_circular_acf(residues, q, lag)
            z   = _d29_circular_acf_z(val, n_eff)
            if abs(val) > best_abs
                best_abs = abs(val)
                best_val = val
                best_lag = lag
                best_z   = z
            end
            if abs(z) >= D29_Z_SIG
                seen_significant = true
            elseif seen_significant && decorr_lag == -1
                decorr_lag = lag
            end
        end

        @printf("      q=%-2d : peak |circ-ACF|=%.5f at lag=%d  (z=%.2f)%s\n",
                q, best_abs, best_lag, best_z,
                abs(best_z) >= D29_Z_SIG ? "  ← SIGNIFICANT vs uniform null" : "")
        if decorr_lag != -1
            @printf("              decorrelation lag (first |z|<%.1f after a significant lag): %d steps\n",
                    D29_Z_SIG, decorr_lag)
        elseif seen_significant
            @printf("              decorrelation lag: not reached within %d steps (still significant at max lag)\n",
                    D29_ACF_MAX_LAG)
        else
            @printf("              no lag reached |z|>=%.1f — α mod %d ACF is consistent with the uniform null\n",
                    D29_Z_SIG, q)
        end
    end

    # ── 2. p_x spatial autocorrelation (basin trapping) ────────────────────
    @printf("\n    2. p_x spatial autocorrelation (basin trapping), lags [%d,%d]\n",
            D29_PX_LAG_LO, D29_PX_LAG_HI)
    @printf("    -----------------------------------------------------------------\n")
    px_f = Float64.(px_v)
    px_lags = collect(D29_PX_LAG_LO:D29_PX_LAG_STRIDE:D29_PX_LAG_HI)

    best_px_lag = -1
    best_px_abs = -1.0
    best_px_val = 0.0
    best_px_z   = 0.0
    n_sig_px    = 0
    for lag in px_lags
        n_eff = n - lag
        val = _d29_pearson_acf(px_f, lag)
        z   = _d29_pearson_acf_z(val, n_eff)
        if abs(val) > best_px_abs
            best_px_abs = abs(val)
            best_px_val = val
            best_px_lag = lag
            best_px_z   = z
        end
        abs(z) >= D29_Z_SIG && (n_sig_px += 1)
    end

    @printf("      peak |ACF|=%.5f at lag=%d  (z=%.2f)%s\n",
            best_px_abs, best_px_lag, best_px_z,
            abs(best_px_z) >= D29_Z_SIG ? "  ← SIGNIFICANT vs i.i.d. null" : "")
    @printf("      lags with |z|>=%.1f out of %d tested: %d\n", D29_Z_SIG, length(px_lags), n_sig_px)
    if n_sig_px > 0
        @printf("      ↑ positive long-range p_x autocorrelation: consistent with basin trapping\n")
        @printf("        (φ-transition graph has dense components the walk needs many steps to escape)\n")
    else
        @printf("      ↓ no significant p_x autocorrelation at lags %d..%d: no basin trapping at this scale\n",
                D29_PX_LAG_LO, D29_PX_LAG_HI)
    end

    # ── 3. (α mod q, p_x) rolling cross-correlation / mutual information ──
    @printf("\n    3. (α mod %d, p_x) rolling cross-MI (dynamic steering), lags 0..%d\n",
            primary_q, D29_ACF_MAX_LAG)
    @printf("    -----------------------------------------------------------------\n")

    px_lo = minimum(px_v)
    px_hi = maximum(px_v)
    residues_q = mod.(alpha_v, primary_q)
    ccf_lags = collect(0:D29_MI_LAG_STRIDE:D29_ACF_MAX_LAG)

    @printf("      %6s  %10s  %12s  %8s\n", "lag", "I(bits)", "bias_null", "lift")
    n_sig_mi = 0
    for lag in ccf_lags
        n_eff = n - lag
        joint = zeros(Int, primary_q, D29_MI_GRID_SIZE)
        @inbounds for i in 1:n_eff
            r  = residues_q[i] + 1
            pb = _d29_px_bucket(px_v[i + lag], px_lo, px_hi) + 1
            joint[r, pb] += 1
        end
        mi = _d29_mutual_information_bits(joint)
        # Finite-sample MI bias under independence (Miller-Madow-style):
        # E[MI_plugin | independent] ≈ (rows-1)(cols-1) / (2*N*ln2)
        bias_null = (primary_q - 1) * (D29_MI_GRID_SIZE - 1) / (2.0 * n_eff * log(2.0))
        lift = bias_null > 0 ? mi / bias_null : (mi > 0 ? Inf : 1.0)
        is_sig = mi > 3.0 * bias_null
        is_sig && (n_sig_mi += 1)
        @printf("      %6d  %10.5f  %12.5f  %8.2f%s\n",
                lag, mi, bias_null, lift, is_sig ? "  ←" : "")
    end
    @printf("      lags with I > 3x finite-sample null bias: %d / %d\n", n_sig_mi, length(ccf_lags))
    if n_sig_mi > 0
        @printf("      ↑ excess mutual information at nonzero lag: divisor state appears to dynamically\n")
        @printf("        steer which p_x anchors become productive — a lagged-steering effect D12's\n")
        @printf("        single-lag (k=0) test (I=0.0057 bits, NMI=0.0010) could not see.\n")
    else
        @printf("      ↓ no lag shows excess MI beyond the finite-sample null: α mod %d and p_x\n", primary_q)
        @printf("        remain independent even at wide lags — no dynamic-steering effect detected.\n")
    end

    @printf("\n")
    return nothing
end
