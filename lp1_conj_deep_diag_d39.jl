# =============================================================================
#  lp1_conj_deep_diag_d39.jl  --  report section D39: closure-indexed
#  sequential autocorrelation of α, P_fb, and the difference process Δα.
#
#  See the D39 constants-block docstring in lp1_conj_deep_diag_core.jl for
#  the full hypothesis writeup. Short version: the closure identity
#
#      atom(R) + atom(S)  ==  neg_al·G  -  atom(P_fb)                    (*)
#
#  means that if LP1-conj keys (which encode atom(R)+atom(S)) carry real
#  sequential autocorrelation, it must show up on the RHS too. This module
#  tests the RHS directly via two tractable proxies — the raw scalar
#  neg_al (standing in for neg_al·G, since G is a fixed generator for the
#  whole run) and px_anchor (= fb[i0][1], standing in for atom(P_fb)) —
#  plus the difference process combined_al (Δα), which is the *sequential*
#  complement to D35's *support-concentration* test on the same quantity.
#
#  Design mirrors D37 throughout:
#    - per-thread closure-ordered chains, NOT concatenated across threads
#      (closures are sparse; splicing would inject spurious lag pairs at
#      thread boundaries — see merge_conj_deep_stats D39 comment)
#    - ACF computed within each chain separately (sample Pearson
#      autocorrelation at each lag), then z-scores are pooled across
#      chains via an inverse-variance-weighted mean (each chain's ACF
#      estimate at lag L has approximate variance 1/(n_chain - L) under
#      the i.i.d. null, by the standard Bartlett large-sample formula)
#    - only chains with at least D39_MIN_CHAIN_LEN points contribute to a
#      given lag, exactly mirroring D37's "pooled over k/n chains" readout
# =============================================================================

const D39_MIN_CHAIN_LEN = 4   # need at least a few points before ACF at lag 1 is meaningful

# ---------------------------------------------------------------------------
#  _seq_acf_z(x, lag) -> (r, z, n_pairs)
#
#  Sample Pearson autocorrelation of vector x at the given lag, plus its
#  z-score against the i.i.d.-null standard error 1/sqrt(n - lag) (Bartlett,
#  first-lag large-sample approximation — same convention D29 already uses
#  for its circular-ACF z-scores in this codebase).
#
#  Returns (NaN, NaN, 0) if there are fewer than 2 valid pairs.
# ---------------------------------------------------------------------------
function _seq_acf_z(x::Vector{Int}, lag::Int)::Tuple{Float64,Float64,Int}
    n = length(x)
    n_pairs = n - lag
    n_pairs < 2 && return (NaN, NaN, 0)

    xf = Float64.(x)
    mu = sum(xf) / n
    denom = 0.0
    @inbounds for i in 1:n
        d = xf[i] - mu
        denom += d * d
    end
    denom == 0.0 && return (NaN, NaN, 0)   # degenerate (constant series)

    numer = 0.0
    @inbounds for i in 1:n_pairs
        numer += (xf[i] - mu) * (xf[i+lag] - mu)
    end
    r = numer / denom
    se = 1.0 / sqrt(Float64(n_pairs))
    z = r / se
    return (r, z, n_pairs)
end

# ---------------------------------------------------------------------------
#  _pooled_acf_over_chains(chains, field, lags; min_len) -> Vector{(lag, pooled_z, n_chains_used, max_abs_r)}
#
#  For each lag, computes per-chain (r, z) via _seq_acf_z on chains long
#  enough to support that lag, then pools the z-scores with inverse-
#  variance weighting (weight = n_pairs, since Var(z) ≈ 1 under the null
#  by construction — so this reduces to a pairs-weighted mean of z, the
#  natural pooling rule when each chain's z is already on a common scale).
# ---------------------------------------------------------------------------
function _pooled_acf_over_chains(chains::Vector{Vector{Int}}, lags::AbstractVector{Int};
                                  min_len::Int = D39_MIN_CHAIN_LEN)
    results = NamedTuple{(:lag,:pooled_z,:n_chains,:max_abs_r),Tuple{Int,Float64,Int,Float64}}[]
    for lag in lags
        wsum   = 0.0
        zsum   = 0.0
        nchain = 0
        max_abs_r = 0.0
        for ch in chains
            length(ch) < max(min_len, lag + 2) && continue
            r, z, n_pairs = _seq_acf_z(ch, lag)
            isnan(z) && continue
            w = Float64(n_pairs)
            wsum += w
            zsum += w * z
            nchain += 1
            max_abs_r = max(max_abs_r, abs(r))
        end
        pooled_z = nchain > 0 ? zsum / sqrt(wsum) : NaN
        # ^ pooling rule: Σ w_i z_i / sqrt(Σ w_i) is the standard inverse-
        #   variance-weighted combination when Var(z_i) ≈ 1/w_i under H0,
        #   so the combined statistic is again ~N(0,1) under H0.
        push!(results, (lag=lag, pooled_z=pooled_z, n_chains=nchain, max_abs_r=max_abs_r))
    end
    return results
end

# ---------------------------------------------------------------------------
#  _report_d39 — top-level report section.
# ---------------------------------------------------------------------------
function _report_d39(deep_stat::ConjDeepStat)
    chains = deep_stat.d39_chains
    n_total = deep_stat.d39_n_closures

    @printf("\n  D39 — Closure-indexed sequential autocorrelation (α, P_fb, Δα)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    @printf("    Closures observed (uncapped, all threads) : %d\n", n_total)

    if isempty(chains)
        @printf("    (no chains recorded — skipping; D39 needs at least one closure\n")
        @printf("     to build a chain. Was record_d39_closure! wired into the\n")
        @printf("     handle_1lp_conj! close path?)\n")
        return nothing
    end

    chain_lens = [length(c.neg_al) for c in chains]
    sorted_lens = sort(chain_lens)
    median_len = sorted_lens[cld(length(sorted_lens), 2)]
    @printf("    Threads contributing a closure chain      : %d\n", length(chains))
    @printf("    Per-chain closure counts: min=%d  median=%d  max=%d\n",
            minimum(chain_lens), median_len, maximum(chain_lens))

    max_len = maximum(chain_lens)
    # Cap tested lags at both the configured ceiling and what the data can
    # actually support (no point testing lag 500 against chains of length 10).
    lag_hi = min(D39_ACF_LAG_HI, max(1, max_len - D39_MIN_CHAIN_LEN))
    lags = D39_ACF_LAG_LO:D39_ACF_LAG_STRIDE:lag_hi
    if isempty(lags)
        @printf("    (chains too short for any tested lag — skipping ACF tables)\n")
        return nothing
    end

    series_defs = (
        (label = "neg_al      (proxy for α·a)",   field = c -> c.neg_al),
        (label = "px_anchor   (proxy for P_fb)",  field = c -> c.px_anchor),
        (label = "combined_al (Δα, difference process)", field = c -> c.combined_al),
    )

    for sd in series_defs
        vecs = [sd.field(c) for c in chains]
        results = _pooled_acf_over_chains(vecs, lags)
        valid = filter(r -> !isnan(r.pooled_z), results)

        @printf("\n    %s\n", sd.label)
        @printf("    -----------------------------------------------------------------\n")
        if isempty(valid)
            @printf("      (no chain long enough to support any tested lag)\n")
            continue
        end

        best = valid[argmax(abs.(getfield.(valid, :pooled_z)))]
        @printf("      peak pooled |z|=%.2f at lag=%d closures  (pooled over %d/%d chains)\n",
                abs(best.pooled_z), best.lag, best.n_chains, length(chains))

        n_sig = count(r -> abs(r.pooled_z) >= 3.0, valid)
        @printf("      lags with pooled |z|>=3.0 out of %d tested: %d\n", length(valid), n_sig)

        if n_sig > 0
            sig_lags = [r.lag for r in valid if abs(r.pooled_z) >= 3.0]
            shown = sig_lags[1:min(10, length(sig_lags))]
            @printf("      significant lags (first %d): %s%s\n",
                    length(shown), join(shown, ", "),
                    length(sig_lags) > length(shown) ? ", ..." : "")
        end
    end

    # --- Verdict ---
    @printf("\n    Verdict:\n")
    al_vecs = [c.neg_al for c in chains]
    px_vecs = [c.px_anchor for c in chains]
    dal_vecs = [c.combined_al for c in chains]
    al_res  = filter(r -> !isnan(r.pooled_z), _pooled_acf_over_chains(al_vecs, lags))
    px_res  = filter(r -> !isnan(r.pooled_z), _pooled_acf_over_chains(px_vecs, lags))
    dal_res = filter(r -> !isnan(r.pooled_z), _pooled_acf_over_chains(dal_vecs, lags))

    al_sig  = any(r -> abs(r.pooled_z) >= 3.0, al_res)
    px_sig  = any(r -> abs(r.pooled_z) >= 3.0, px_res)
    dal_sig = any(r -> abs(r.pooled_z) >= 3.0, dal_res)

    if al_sig
        @printf("      → SIGNIFICANT sequential autocorrelation in neg_al (α). Under the\n")
        @printf("        fixed-generator argument (see constants-block docstring), this is\n")
        @printf("        real structure in the walk's α trajectory and is consistent with\n")
        @printf("        the closure-identity hypothesis: autocorrelation in atom(R)+atom(S)\n")
        @printf("        showing up on the α side of (*). Caveat: this does NOT by itself\n")
        @printf("        prove autocorrelation in the group element α·a — only in the\n")
        @printf("        scalar α — see docstring for why that gap cannot be closed without\n")
        @printf("        per-closure Jacobian scalar multiplication (out of scope here).\n")
    else
        @printf("      → No significant sequential autocorrelation detected in neg_al (α)\n")
        @printf("        at the tested lags/sample size. Does not rule out structure at\n")
        @printf("        lags beyond %d closures or below this n's detection power.\n", lag_hi)
    end

    if px_sig
        @printf("      → SIGNIFICANT sequential autocorrelation in px_anchor (P_fb).\n")
    else
        @printf("      → No significant sequential autocorrelation detected in px_anchor\n")
        @printf("        (P_fb) at the tested lags/sample size.\n")
    end

    if dal_sig
        @printf("      → SIGNIFICANT sequential autocorrelation in combined_al (Δα). This\n")
        @printf("        is the autocorrelation question D35 could not ask (D35 tests\n")
        @printf("        whether Δα's SUPPORT is narrow, not whether consecutive Δα values\n")
        @printf("        are correlated) — a positive result here is direct evidence for\n")
        @printf("        the autocorrelated-keys hypothesis driving α₂≈0.59–0.60.\n")
    else
        @printf("      → No significant sequential autocorrelation detected in combined_al\n")
        @printf("        (Δα) at the tested lags/sample size.\n")
    end

    if !al_sig && !px_sig && !dal_sig
        @printf("\n      Combined: none of the three closure-indexed proxies show\n")
        @printf("      significant sequential autocorrelation at n=%d closures / lags up\n", n_total)
        @printf("      to %d. Either the α₂ pinning's autocorrelation signature lives\n", lag_hi)
        @printf("      below this layer's detection power at current sample size, or it\n")
        @printf("      is not visible through these particular proxies — consider rerunning\n")
        @printf("      D39 once closure count has grown substantially (cf. D35's caveat),\n")
        @printf("      or revisit the key-construction-downstream-of-a hypothesis from D31.\n")
    end

    _report_d39b(chains)

    return nothing
end

# =============================================================================
#  D39b — phase-locked closure diagnostic (addendum).
#
#  See the D39b constants-block docstring in lp1_conj_deep_diag_core.jl for
#  the full hypothesis writeup. Short version: D39's autocorrelation result
#  could be genuine algebraic/spatial structure, OR it could be an artifact
#  of closures preferentially landing on a repeating step-table slot (which
#  would inherit a fixed increment, manufacturing spurious sequential
#  structure). This section tests for that confound directly using the
#  newly-recorded d39_phase series (step-table slot `si` at each closure).
# =============================================================================

# ---------------------------------------------------------------------------
#  _discretize(x, n_bins) -> Vector{Int}  (1-based bin index)
#
#  Quantile-ish bucketing: equal-width bins over [min(x), max(x)]. Used to
#  discretize α/P/Δα (which are integers over a wide range) into a small
#  number of bins for the MI estimate — plain integer values would make
#  every value its own bin, giving a degenerate (maximal, meaningless) MI.
# ---------------------------------------------------------------------------
function _discretize(x::Vector{Int}, n_bins::Int)::Vector{Int}
    isempty(x) && return Int[]
    lo, hi = minimum(x), maximum(x)
    hi == lo && return ones(Int, length(x))
    width = (hi - lo) / n_bins
    return [clamp(1 + Int(floor((xi - lo) / width)), 1, n_bins) for xi in x]
end

# ---------------------------------------------------------------------------
#  _conditional_mi(joint_with, phase_t, phase_t1; n_bins, n_shuffle) ->
#      (mi_bits, null_mean_bits, null_std_bits, z)
#
#  Estimates I((α_t,P_t,Δα_t); phase_{t+1} | phase_t) via the standard
#  decomposition I(X;Y|Z) = H(Y|Z) - H(Y|X,Z), implemented as plug-in
#  (maximum-likelihood) entropy estimates over discretized joint counts —
#  consistent with how D29's mutual-information readout is described in
#  the existing log output (binned MI against a shuffle null).
#
#  joint_with : Vector{Int}, the discretized (α_t,P_t,Δα_t) JOINT label at
#               each consecutive-pair index (one combined label per pair;
#               see _report_d39b for how the three series are combined)
#  phase_t    : Vector{Int}, phase at closure t (the EARLIER of the pair)
#  phase_t1   : Vector{Int}, phase at closure t+1 (the LATER of the pair)
#
#  Null: phase_t1 is randomly shuffled n_shuffle times (breaking any real
#  t -> t+1 phase relationship while preserving each series' own marginal),
#  and the conditional MI is recomputed each time. z is the observed MI's
#  z-score against this null distribution.
# ---------------------------------------------------------------------------
function _conditional_mi(joint_with::Vector{Int}, phase_t::Vector{Int}, phase_t1::Vector{Int};
                          n_shuffle::Int = 200, rng = Random.Xoshiro())::NTuple{4,Float64}
    n = length(joint_with)
    (n != length(phase_t) || n != length(phase_t1)) &&
        throw(ArgumentError("_conditional_mi: length mismatch"))
    n < 8 && return (NaN, NaN, NaN, NaN)

    function cmi(jw::Vector{Int}, pt::Vector{Int}, pt1::Vector{Int})::Float64
        # H(Y|Z): Y=pt1, Z=pt
        n_ = length(jw)
        cz   = Dict{Int,Int}()
        cyz  = Dict{Tuple{Int,Int},Int}()
        cxz  = Dict{Tuple{Int,Int},Int}()
        cxyz = Dict{Tuple{Int,Int,Int},Int}()
        for i in 1:n_
            phz, y, x = pt[i], pt1[i], jw[i]
            cz[phz]        = get(cz, phz, 0) + 1
            cyz[(y,phz)]   = get(cyz, (y,phz), 0) + 1
            cxz[(x,phz)]   = get(cxz, (x,phz), 0) + 1
            cxyz[(x,y,phz)]= get(cxyz, (x,y,phz), 0) + 1
        end
        h_y_given_z = 0.0
        for ((y,phz), c) in cyz
            p_yz = c / n_
            p_z  = cz[phz] / n_
            h_y_given_z -= p_yz * log2(p_yz / p_z)
        end
        h_y_given_xz = 0.0
        for ((x,y,phz), c) in cxyz
            p_xyz = c / n_
            p_xz  = cxz[(x,phz)] / n_
            h_y_given_xz -= p_xyz * log2(p_xyz / p_xz)
        end
        return max(0.0, h_y_given_z - h_y_given_xz)
    end

    mi_obs = cmi(joint_with, phase_t, phase_t1)

    null_vals = Vector{Float64}(undef, n_shuffle)
    perm = collect(1:n)
    for k in 1:n_shuffle
        shuffle!(rng, perm)
        null_vals[k] = cmi(joint_with, phase_t, phase_t1[perm])
    end
    null_mean = sum(null_vals) / n_shuffle
    null_var  = sum((v - null_mean)^2 for v in null_vals) / max(1, n_shuffle - 1)
    null_std  = sqrt(null_var)
    z = null_std > 0 ? (mi_obs - null_mean) / null_std : NaN

    return (mi_obs, null_mean, null_std, z)
end

# ---------------------------------------------------------------------------
#  _phase_stratified_lag1_corr(combined_al, phase) ->
#      (r_same, n_same, r_diff, n_diff)
#
#  Splits consecutive closure pairs (t, t+1) within each chain into
#  "same phase" (phase[t] == phase[t+1]) vs "different phase", and computes
#  the lag-1 Pearson correlation of combined_al separately within each
#  stratum, pooling pairs across ALL chains (not per-chain — see D39b
#  constants-block docstring's sample-size caveat: same-phase pairs are
#  rare, expected ~n/N_STEPS total, so per-chain stratification would
#  leave most chains with zero same-phase pairs).
# ---------------------------------------------------------------------------
function _phase_stratified_lag1_corr(chains)
    same_x = Float64[]; same_y = Float64[]
    diff_x = Float64[]; diff_y = Float64[]
    for c in chains
        n = length(c.combined_al)
        n < 2 && continue
        for t in 1:(n-1)
            if c.phase[t] == c.phase[t+1]
                push!(same_x, Float64(c.combined_al[t]))
                push!(same_y, Float64(c.combined_al[t+1]))
            else
                push!(diff_x, Float64(c.combined_al[t]))
                push!(diff_y, Float64(c.combined_al[t+1]))
            end
        end
    end
    function pearson(x, y)
        n = length(x)
        n < 2 && return NaN
        mx, my = sum(x)/n, sum(y)/n
        sxy = sum((x[i]-mx)*(y[i]-my) for i in 1:n)
        sxx = sum((xi-mx)^2 for xi in x)
        syy = sum((yi-my)^2 for yi in y)
        (sxx == 0.0 || syy == 0.0) && return NaN
        return sxy / sqrt(sxx*syy)
    end
    return (pearson(same_x, same_y), length(same_x), pearson(diff_x, diff_y), length(diff_x))
end

# ---------------------------------------------------------------------------
#  _report_d39b — phase-locked closure diagnostic report section.
# ---------------------------------------------------------------------------
function _report_d39b(chains)
    @printf("\n  D39b — Phase-locked closure diagnostic (table-resonance check)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")

    all_phases = Int[]
    for c in chains; append!(all_phases, c.phase); end
    if isempty(all_phases) || all(p -> p < 0, all_phases)
        @printf("    (no phase data recorded — step_phase was not passed at the\n")
        @printf("     handle_1lp_conj! call site; skipping D39b)\n")
        return nothing
    end
    n_steps_observed = maximum(all_phases)
    @printf("    Step-table size (inferred from max observed slot) : %d\n", n_steps_observed)

    # --- Build consecutive-pair joint label for the MI test ---
    # Combine (α_t,P_t,Δα_t) into one discretized joint label per pair via
    # a small mixed-radix code over per-series bins, pooling pairs across
    # all chains (same rationale as the phase-stratified corr test below).
    n_bins = 4
    joint_with = Int[]
    phase_t    = Int[]
    phase_t1   = Int[]
    for c in chains
        n = length(c.neg_al)
        n < 2 && continue
        al_b  = _discretize(c.neg_al,      n_bins)
        px_b  = _discretize(c.px_anchor,   n_bins)
        dal_b = _discretize(c.combined_al, n_bins)
        for t in 1:(n-1)
            (c.phase[t] < 0 || c.phase[t+1] < 0) && continue
            label = (al_b[t]-1) + n_bins*(px_b[t]-1) + n_bins*n_bins*(dal_b[t]-1) + 1
            push!(joint_with, label)
            push!(phase_t,  c.phase[t])
            push!(phase_t1, c.phase[t+1])
        end
    end

    n_pairs = length(joint_with)
    @printf("    Consecutive closure pairs available (pooled, all chains) : %d\n", n_pairs)

    if n_pairs < 8
        @printf("    (too few consecutive pairs for the conditional-MI test — skipping)\n")
    else
        mi_obs, null_mean, null_std, mi_z = _conditional_mi(joint_with, phase_t, phase_t1)
        @printf("\n    1. I((α_t,P_t,Δα_t); phase_t+1 | phase_t)\n")
        @printf("    -----------------------------------------------------------------\n")
        if isnan(mi_z)
            @printf("      (degenerate — could not estimate; too few pairs or zero variance)\n")
        else
            @printf("      observed conditional MI : %.5f bits\n", mi_obs)
            @printf("      shuffle-null mean ± std : %.5f ± %.5f bits  (n_shuffle=200)\n", null_mean, null_std)
            @printf("      z = (obs - null_mean) / null_std : %.2f\n", mi_z)
            if mi_z >= 3.0
                @printf("      → SIGNIFICANT: this closure's (α,P,Δα) carries information about\n")
                @printf("        the NEXT closure's table slot beyond what the current slot alone\n")
                @printf("        predicts. This is the opposite of pure resonance (resonance would\n")
                @printf("        predict phase_t alone explains phase_t+1; this says the WALK STATE\n")
                @printf("        does too) — consistent with the autocorrelation being more than a\n")
                @printf("        table artifact, though it does not on its own rule out resonance\n")
                @printf("        contributing part of the D39 signal.\n")
            else
                @printf("      → Not significant at this n: no detectable extra information beyond\n")
                @printf("        phase_t. Consistent with (but does not prove) D39's autocorrelation\n")
                @printf("        being explainable by phase_t alone — see test 2 below for a more\n")
                @printf("        direct check.\n")
            end
        end
    end

    # --- Test 2: phase-stratified lag-1 Δα correlation ---
    r_same, n_same, r_diff, n_diff = _phase_stratified_lag1_corr(chains)
    @printf("\n    2. corr(Δα_t, Δα_t+1), stratified by phase(t)==phase(t+1)\n")
    @printf("    -----------------------------------------------------------------\n")
    if isnan(r_same)
        @printf("      same-phase   pairs : n=%d   r=n/a (too few pairs)\n", n_same)
    else
        @printf("      same-phase   pairs : n=%d   r=%.4f\n", n_same, r_same)
    end
    if isnan(r_diff)
        @printf("      different-phase pairs : n=%d   r=n/a (too few pairs)\n", n_diff)
    else
        @printf("      different-phase pairs : n=%d   r=%.4f\n", n_diff, r_diff)
    end

    if n_same < 5
        @printf("      → same-phase stratum too sparse (n=%d) at current closure count to\n", n_same)
        @printf("        draw a conclusion — expected ~n_pairs/%d same-phase pairs by chance;\n", n_steps_observed)
        @printf("        rerun once closure count has grown substantially.\n")
    elseif !isnan(r_same) && !isnan(r_diff)
        if abs(r_same) > abs(r_diff) + 0.2   # crude practical-significance margin, not a formal test
            @printf("      → same-phase correlation notably exceeds different-phase correlation.\n")
            @printf("        Some of D39's Δα autocorrelation may be table-resonance — closures\n")
            @printf("        that happen to share a step-table slot inherit a shared fixed\n")
            @printf("        increment. Does not rule out a genuine component too; compare\n")
            @printf("        magnitudes once n_same has grown.\n")
        else
            @printf("      → same-phase and different-phase correlations are comparable. D39's\n")
            @printf("        Δα autocorrelation does NOT appear to be explained by step-table\n")
            @printf("        phase resonance — the original interpretation (real algebraic/\n")
            @printf("        spatial structure) survives this check.\n")
        end
    end

    return nothing
end
