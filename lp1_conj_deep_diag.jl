# =============================================================================
#  lp1_conj_deep_diag.jl  --  Seven deep diagnostics for LP1-conj emissions.
#
#  These diagnostics answer *which algebraic object is responsible for the
#  clustering* observed in LP1-conj emissions, as opposed to the phenomeno-
#  logical structure diagnostics already in phi_bias_diag.jl.
#
#  All seven diagnostics operate post-hoc on the merged PhiBiasStat (or on
#  supplementary accumulator structs described below) and the conj snapshot.
#  They print to stdout under the phi bias report.
#
#  Diagnostic catalogue
#  ────────────────────
#  D1 — Recurrence fingerprinting
#       For each emitted key, track recurrence times and build return-process
#       structure: recurrence-time histogram, recurrence ACF, same-key burst
#       conditional probability P(same key within τ | same key previously).
#       Compared to shuffled-gap null.
#
#  D2 — Conditional entropy of emitted keys
#       Estimate H₂(X_t | X_{t-1}) (lag-1 conditional collision entropy) by
#       maintaining transition counts between coarse key buckets.  Reveals
#       whether observing one emission reduces uncertainty about the next.
#
#  D3 — Branch ancestry clustering
#       Track (step_parity, a_bucket, recent_key_hash) tuples at each emission
#       as a proxy for "branch family."  Cluster emissions by ancestry signature
#       and report top motifs.  Detects whether a tiny subset of transition
#       patterns drives most emissions.
#
#  D4 — Local Jacobian linearization (perturbation survival)
#       Using the lp1_conj_arrivals sequence, estimate persistence: given a
#       known emission at step t, how likely is the next emission within τ steps
#       vs a shuffled-gap baseline?  Provides C(τ) = P(LP-hit within τ steps).
#
#  D5 — Multiplicity collapse (Zipf / Gini / Hill)
#       Rank-frequency analysis of emitted key buckets: Gini coefficient,
#       top-k mass fractions, Hill tail exponent, Zipf log-log slope.
#       Distinguishes "many medium-multiplicity keys" from "microscopic set
#       with absurd multiplicity."
#
#  D6 — Emission-conditioned return maps
#       In emission-index space (not step space), analyse the map k_n → k_{n+1}
#       via transition entropy, cycle frequency, and strongly-connected component
#       sizes.  Reveals whether the emission process lives on a small automaton.
#
#  D7 — Marginal utility of LP1-conj table entries
#       Simulate incremental closure: given the conj snapshot, what fraction of
#       closures in the phase-2 run were enabled by the first X% of entries?
#       Reports ΔT_solve(N) as a function of precompute size, to quantify
#       saturation and guide table size decisions.
#
#  D8 — Closure-depth distribution
#       "Branch depth" is the number of raw walk steps between when a conj key
#       is first stored in the LP1-conj table and when it is subsequently closed
#       by a second hit on the same key.  This measures the dynamical lifetime
#       of the metastable algebraic states that drive LP1-conj closures.
#
#       Reports:
#         • Empirical depth distribution (histogram, percentiles, mean/CV).
#         • Hazard function h(d) = P(close at depth d+1 | not closed before d).
#         • Conditional success probability P(closure at depth d | not before).
#         • Depth-conditioned emission entropy H(key | depth band).
#         • Depth-conditioned collision entropy α₂(depth band).
#         • Depth autocorrelation: are consecutive closure depths correlated?
#         • Depth-band transition matrix: local walk structure between bands.
#         • Lyapunov proxy: variance of depth as a function of a-bucket.
#
#       Uses a per-thread shadow side-table (lp_key → store_step) in
#       ConjDeepStat to compute depth without modifying LP1ConjVal.
#       The shadow table is populated at miss (store) and consumed at close.
#
#  Supplementary accumulators (per-thread, merged before calling report)
#  ──────────────────────────────────────────────────────────────────────
#  ConjDeepStat  — carries branch ancestry log, transition count matrix,
#                  and the D8 shadow depth table + closure depth log.
#  Thin enough to allocate per thread without OOM risk.
#
#  Wiring
#  ──────
#  1. `include("lp1_conj_deep_diag.jl")` in trial3_fixed.jl (already done
#     by the patch to trial3_fixed.jl).
#  2. Allocate one ConjDeepStat per thread alongside PhiBiasStat.
#  3a. Call record_conj_deep_miss!  from handle_1lp_conj! on every STORE
#      (prev === nothing path, after conj_insert_or_pop!).
#  3b. Call record_conj_deep_step! from handle_1lp_conj! on every CLOSE
#      (prev !== nothing path, after the relation is emitted).
#  4. Call merge_conj_deep_stats + print_conj_deep_report from main2 after
#     the phase-2 phi bias report, passing the merged PhiBiasStat and the
#     conj snapshot dict.
# =============================================================================

# ---------------------------------------------------------------------------
#  Constants
# ---------------------------------------------------------------------------
const DEEP_DIAG_BUCKET_BITS = 10          # 2^10 = 1024 coarse buckets for conditional entropy / return map
const DEEP_DIAG_N_BUCKETS   = 1 << DEEP_DIAG_BUCKET_BITS
const DEEP_DIAG_MAX_ANCESTRY = 500_000    # cap on ancestry log entries per thread
const DEEP_DIAG_COND_ENT_LAG = 4         # max lag for conditional collision entropy
const DEEP_DIAG_MAX_OPCODE_LOG = 2_000_000  # cap on opcode log entries per thread (~2 MB)

# ---------------------------------------------------------------------------
#  ConjDeepStat — per-thread accumulator
# ---------------------------------------------------------------------------
mutable struct ConjDeepStat
    # D2 — transition matrix: n_trans[from_bucket+1, to_bucket+1] = count.
    # UInt32 to keep memory: 1024×1024×4B = 4 MB per thread.
    n_trans         ::Matrix{UInt32}     # (DEEP_DIAG_N_BUCKETS, DEEP_DIAG_N_BUCKETS)
    _prev_bucket    ::Int                # -1 if no previous emission yet

    # D3 — branch ancestry log: each entry is (a_bucket, step_parity, key_hash_lo).
    # We cap at DEEP_DIAG_MAX_ANCESTRY entries to bound memory.
    ancestry_log_a      ::Vector{UInt16}   # a_bucket (1-based, mapped to UInt16)
    ancestry_log_parity ::Vector{UInt8}    # step parity (raw_step & 0x3)
    ancestry_log_keyhash::Vector{UInt32}   # low 32 bits of lp_key hash

    # D7 — per-emission closure-enabled flag.
    # True if this emission was the *first* closure for its key (i.e. it consumed
    # a stored entry that was not yet consumed).  This is the information needed
    # to simulate incremental table saturation.
    is_first_closure::Vector{Bool}
    n_emissions     ::Int

    # D8 — closure-depth distribution.
    # Shadow side-table: lp_key → store_step.  Populated at miss (store), consumed
    # at close.  Per-thread so no locking is needed.  Int32 store_step is fine
    # since raw_steps fits in 32 bits for any realistic run length.
    d8_shadow       ::Dict{UInt128, Int}   # lp_key → raw_steps at store time
    # Parallel vectors accumulated at close time:
    d8_depths       ::Vector{Int}          # closure depth = close_step − store_step
    d8_close_bkt    ::Vector{UInt16}       # coarse key bucket at close (DEEP_DIAG_BUCKET_BITS bits)
    d8_close_abkt   ::Vector{UInt16}       # a_bucket at close (clamped to UInt16)
    # Depth of the previous closure, for autocorrelation.
    d8_prev_depth   ::Int                  # -1 if no previous closure yet

    # D9 — step-opcode conditional entropy H(opcode | recent LP1-conj).
    # opcode_log: one UInt8 per VALID phi step recording the step type:
    #   0 = 0-LP (full relation)
    #   1 = 1-LP affine (store or close)
    #   2 = 1-LP conj (store or close)
    #   3 = 2-LP affine
    #   4 = 2-LP conj
    #   5 = 3-LP / skip
    # Capped at DEEP_DIAG_MAX_OPCODE_LOG entries to bound memory.
    # opcode_is_lp1c: parallel Bool — true iff this step was a 1-LP-conj EMISSION
    # (i.e. a relation was produced).  Used to find "recent LP1-conj" windows.
    opcode_log      ::Vector{UInt8}
    opcode_is_lp1c  ::Vector{Bool}
end

function ConjDeepStat()
    ConjDeepStat(
        zeros(UInt32, DEEP_DIAG_N_BUCKETS, DEEP_DIAG_N_BUCKETS),
        -1,
        UInt16[], UInt8[], UInt32[],
        Bool[],
        0,
        Dict{UInt128,Int}(),
        Int[], UInt16[], UInt16[],
        -1,
        UInt8[], Bool[],
    )
end

# ---------------------------------------------------------------------------
#  merge_conj_deep_stats — reduce per-thread structs.
# ---------------------------------------------------------------------------
function merge_conj_deep_stats(stats::Vector{ConjDeepStat})::ConjDeepStat
    isempty(stats) && error("merge_conj_deep_stats: empty input")
    merged = ConjDeepStat()
    for s in stats
        merged.n_trans .+= s.n_trans
        append!(merged.ancestry_log_a,       s.ancestry_log_a)
        append!(merged.ancestry_log_parity,  s.ancestry_log_parity)
        append!(merged.ancestry_log_keyhash, s.ancestry_log_keyhash)
        append!(merged.is_first_closure,     s.is_first_closure)
        merged.n_emissions += s.n_emissions
        # D8: merge parallel depth/bucket vectors; shadow table is not merged
        # (per-thread keys are disjoint in expectation; any residual open entries
        # are simply unclosed and would distort the depth distribution).
        append!(merged.d8_depths,     s.d8_depths)
        append!(merged.d8_close_bkt,  s.d8_close_bkt)
        append!(merged.d8_close_abkt, s.d8_close_abkt)
        # D9: merge opcode log (cap to DEEP_DIAG_MAX_OPCODE_LOG total)
        n_remaining = DEEP_DIAG_MAX_OPCODE_LOG - length(merged.opcode_log)
        if n_remaining > 0
            n_take = min(n_remaining, length(s.opcode_log))
            append!(merged.opcode_log,     s.opcode_log[1:n_take])
            append!(merged.opcode_is_lp1c, s.opcode_is_lp1c[1:n_take])
        end
    end
    return merged
end

# ---------------------------------------------------------------------------
#  record_conj_deep_miss! — call from handle_1lp_conj! at every STORE (miss).
#
#  Records raw_step into the per-thread shadow table so that when the key is
#  later closed, we can compute closure_depth = close_step - store_step.
#  Does nothing if the key is already in the shadow table (duplicate store from
#  a race or useless close that re-inserts; we keep the first store_step).
# ---------------------------------------------------------------------------
@inline function record_conj_deep_miss!(stat    ::ConjDeepStat,
                                         lp_key  ::UInt128,
                                         raw_step::Int)
    haskey(stat.d8_shadow, lp_key) || (stat.d8_shadow[lp_key] = raw_step)
    return nothing
end

# ---------------------------------------------------------------------------
#  record_conj_deep_step! — call from handle_1lp_conj! at every emission.
#
#  Arguments:
#    stat       — per-thread ConjDeepStat
#    lp_key     — CanonicalLP1Key (UInt128) of the emitted key
#    a_bucket   — 1-based a-bucket from PhiBiasStat (same scale)
#    raw_step   — s.raw_steps at the time of emission
#    is_first   — true if this is the first closure for lp_key (consumed a stored
#                 entry that had not been consumed before in this run)
# ---------------------------------------------------------------------------
@inline function record_conj_deep_step!(stat    ::ConjDeepStat,
                                         lp_key  ::UInt128,
                                         a_bucket::Int,
                                         raw_step::Int,
                                         is_first::Bool)
    stat.n_emissions += 1

    # Coarse bucket for D2 transition matrix: top DEEP_DIAG_BUCKET_BITS of hash.
    h64    = _deep_fp64(lp_key)
    bkt    = Int(h64 >> (64 - DEEP_DIAG_BUCKET_BITS))   # 0-based, in [0, 1023]

    if stat._prev_bucket >= 0
        @inbounds stat.n_trans[stat._prev_bucket + 1, bkt + 1] += 0x00000001
    end
    stat._prev_bucket = bkt

    # D3 ancestry log (capped)
    if length(stat.ancestry_log_a) < DEEP_DIAG_MAX_ANCESTRY
        push!(stat.ancestry_log_a,       UInt16(clamp(a_bucket, 0, 65535)))
        push!(stat.ancestry_log_parity,  UInt8(raw_step & 0x3))
        push!(stat.ancestry_log_keyhash, UInt32(h64 & 0xffffffff))
    end

    # D7 closure flag
    push!(stat.is_first_closure, is_first)

    # D8 closure depth: consume shadow table entry if present.
    store_step = get(stat.d8_shadow, lp_key, -1)
    if store_step >= 0
        delete!(stat.d8_shadow, lp_key)
        depth = raw_step - store_step
        if depth >= 0
            push!(stat.d8_depths,     depth)
            push!(stat.d8_close_bkt,  UInt16(bkt))
            push!(stat.d8_close_abkt, UInt16(clamp(a_bucket, 0, 65535)))
        end
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_conj_deep_opcode! — call from the main walk loop on EVERY valid phi
#  step, to build the opcode log for D9 conditional entropy analysis.
#
#  opcode values:
#    OPCODE_0LP      = 0x00   full relation (0-LP)
#    OPCODE_1LP_AFF  = 0x01   1-LP affine (store or close)
#    OPCODE_1LP_CONJ = 0x02   1-LP conj (store or close — any handle_1lp_conj! call)
#    OPCODE_2LP_AFF  = 0x03   2-LP affine
#    OPCODE_2LP_CONJ = 0x04   2-LP conj
#    OPCODE_SKIP     = 0x05   3-LP or disabled branch (skip)
#
#  is_emission: true iff this specific step produced an LP1-conj relation.
#  Only meaningful when opcode == OPCODE_1LP_CONJ.
# ---------------------------------------------------------------------------
const OPCODE_0LP      = 0x00
const OPCODE_1LP_AFF  = 0x01
const OPCODE_1LP_CONJ = 0x02
const OPCODE_2LP_AFF  = 0x03
const OPCODE_2LP_CONJ = 0x04
const OPCODE_SKIP     = 0x05

@inline function record_conj_deep_opcode!(stat       ::ConjDeepStat,
                                           opcode     ::UInt8,
                                           is_emission::Bool)
    length(stat.opcode_log) >= DEEP_DIAG_MAX_OPCODE_LOG && return nothing
    push!(stat.opcode_log,     opcode)
    push!(stat.opcode_is_lp1c, is_emission)
    return nothing
end
@inline function _deep_fp64(key::UInt128)::UInt64
    lo = UInt64(key & 0xffffffffffffffff)
    hi = UInt64(key >> 64)
    h  = lo * UInt64(0x9e3779b97f4a7c15) ⊻ hi * UInt64(0x6c62272e07bb0142)
    h  ⊻= h >> 32; h *= UInt64(0x45d9f3b37197344d); h ⊻= h >> 32
    h
end

@inline function _deep_bucket(key::UInt128)::Int
    Int(_deep_fp64(key) >> (64 - DEEP_DIAG_BUCKET_BITS))
end

# ---------------------------------------------------------------------------
#  _gini — Gini coefficient of a count vector (0 = uniform, 1 = one-hitter)
# ---------------------------------------------------------------------------
function _gini(counts::Vector{Int})::Float64
    n = length(counts)
    n == 0 && return NaN
    s = sum(counts)
    s == 0 && return NaN
    sorted = sort(counts)
    num = 0.0
    for (i, x) in enumerate(sorted)
        num += (2*i - n - 1) * x
    end
    return num / (n * s)
end

# ---------------------------------------------------------------------------
#  _hill_exponent — Hill tail exponent from top-k order statistics.
#  Uses log-ratio estimator: α̂ = 1/H̄ where H̄ = mean log(x_i/x_k) for i<k.
# ---------------------------------------------------------------------------
function _hill_exponent(sorted_desc::Vector{Int}; k::Int = 50)::Float64
    n = length(sorted_desc)
    k = min(k, n - 1)
    k < 2 && return NaN
    xk = Float64(max(1, sorted_desc[k + 1]))
    s  = 0.0
    for i in 1:k
        s += log(max(1.0, Float64(sorted_desc[i])) / xk)
    end
    return k / max(1e-30, s)   # Hill estimator α̂
end

# ---------------------------------------------------------------------------
#  _top_share — fraction of total mass in top frac×n items (sorted desc).
# ---------------------------------------------------------------------------
function _top_share(counts::Vector{Int}, frac::Float64)::Float64
    isempty(counts) && return 0.0
    total = sum(counts)
    total == 0 && return 0.0
    sorted = sort(counts, rev=true)
    k = max(1, round(Int, frac * length(sorted)))
    sum(sorted[1:k]) / total
end
#
#  Arguments:
#    phi_stat  — merged PhiBiasStat (for arrivals, keys, bucket log)
#    deep_stat — merged ConjDeepStat (for transition matrix, ancestry, D7)
#    conj_snap — plain Dict{CanonicalLP1Key, LP1ConjVal} snapshot from precompute
#                (only needed for D7; pass nothing to skip D7)
#    p         — field characteristic (for display)
# ---------------------------------------------------------------------------
function print_conj_deep_report(phi_stat ::PhiBiasStat,
                                 deep_stat::ConjDeepStat;
                                 conj_snap::Union{Dict, Nothing} = nothing,
                                 p        ::Int = 0)

    arrivals  = phi_stat.lp1_conj_arrivals    # Vector{Int} of raw_step at each emission
    keys_u128 = phi_stat.lp1_conj_keys        # Vector{UInt128} parallel to arrivals
    n_emit    = length(arrivals)

    @printf("\n══ LP1-conj deep diagnostics ════════════════════════════════════════\n")
    @printf("  Total LP1-conj emissions analyzed : %d\n", n_emit)
    n_emit == 0 && (@printf("  (no emissions — skipping all sections)\n\n"); return)

    # Coarse bucket for each emission (top DEEP_DIAG_BUCKET_BITS of hash)
    emit_bkt = [_deep_bucket(k) for k in keys_u128]   # Vector{Int}, 0-based

    # ──────────────────────────────────────────────────────────────────────
    #  D1 — Recurrence fingerprinting
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D1 — Recurrence fingerprinting\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        # Map each key to its emission indices (in sorted order).
        key_to_indices = Dict{UInt128, Vector{Int}}()
        sizehint!(key_to_indices, min(n_emit, 4096))
        for (i, k) in enumerate(keys_u128)
            v = get!(key_to_indices, k, Int[])
            push!(v, i)
        end

        # Build recurrence-time histogram (in units of emissions, not steps).
        max_tau = min(200, n_emit ÷ 4)
        rec_hist = zeros(Int, max(1, max_tau))    # rec_hist[τ] = #(same-key pairs at emission-lag τ)
        n_returns = 0
        for (_, idxs) in key_to_indices
            length(idxs) < 2 && continue
            for j in 2:length(idxs)
                τ = idxs[j] - idxs[j-1]
                if 1 <= τ <= max_tau
                    rec_hist[τ] += 1
                    n_returns += 1
                end
            end
        end

        @printf("    Distinct keys emitted          : %d  (%.1f%% of %d)\n",
                length(key_to_indices), 100.0 * length(key_to_indices) / n_emit, n_emit)
        @printf("    Keys with ≥2 emissions         : %d\n",
                count(v -> length(v) >= 2, values(key_to_indices)))
        @printf("    Total same-key recurrences     : %d\n", n_returns)

        if n_returns > 0
            # Recurrence-time mean and CV.
            rtimes = Int[]
            for (_, idxs) in key_to_indices
                for j in 2:length(idxs)
                    push!(rtimes, idxs[j] - idxs[j-1])
                end
            end
            μ_r   = sum(rtimes) / length(rtimes)
            var_r = length(rtimes) < 2 ? 0.0 :
                    sum((x - μ_r)^2 for x in rtimes) / (length(rtimes) - 1)
            cv_r  = μ_r > 0 ? sqrt(var_r) / μ_r : NaN
            @printf("    Recurrence-time (in emissions): mean=%.2f  CV=%.3f\n", μ_r, cv_r)
            if cv_r > 1.5
                @printf("      ↑ CV > 1.5: HIGHLY BURSTY recurrences (algebraic attractor suspected)\n")
            elseif cv_r > 1.0
                @printf("      ↑ CV > 1.0: moderately bursty recurrences\n")
            else
                @printf("      ↑ CV ≤ 1.0: recurrences roughly geometric (Poisson-like)\n")
            end

            # Recurrence autocorrelation at lag 1: corr(r_i, r_{i+1}).
            if length(rtimes) >= 4
                n_r = length(rtimes)
                μ2  = μ_r  # already computed
                cov = sum((rtimes[i] - μ2) * (rtimes[i+1] - μ2)
                          for i in 1:n_r-1) / (n_r - 1)
                var2 = sum((x - μ2)^2 for x in rtimes) / n_r
                acf1 = var2 > 0 ? cov / var2 : 0.0
                @printf("    Recurrence-time ACF(1)         : %.4f  %s\n", acf1,
                        acf1 > 0.2 ? "← POSITIVE: recurrence times cluster (burst epochs)" :
                        acf1 < -0.2 ? "← NEGATIVE: recurrences alternate short/long" :
                        "(≈ uncorrelated)")
            end
        end

        # P(same key within τ_win emissions | same key previously) vs shuffled null.
        # τ_win values to probe.
        τ_wins = [1, 2, 5, 10, 20, 50]
        n_pairs_total = n_emit * (n_emit - 1) ÷ 2   # ignored; use sequential pairs
        @printf("    Burst conditional prob P(same within τ | same previously):\n")
        @printf("      %5s  %8s  %8s  %8s\n", "τ", "P_obs", "P_null", "lift")
        # P_null: probability that a uniformly random emission-pair is same-key.
        n_per_key  = [length(v) for v in values(key_to_indices)]
        p_null_num = sum(c*(c-1) for c in n_per_key; init=0)
        p_null_den = n_emit * (n_emit - 1)
        P_null_sk  = p_null_den > 0 ? p_null_num / p_null_den : 0.0
        for τ_win in τ_wins
            τ_win >= max_tau && continue
            # Count: among consecutive same-key recurrences, how many have τ ≤ τ_win?
            n_cond = n_returns == 0 ? 0 :
                     count(τ -> τ <= τ_win, [idxs[j] - idxs[j-1]
                                             for (_, idxs) in key_to_indices
                                             for j in 2:length(idxs)])
            p_obs  = n_returns > 0 ? n_cond / n_returns : 0.0
            # Null: P(next emission within τ_win is same key) ≈ τ_win × P_null_sk (approximate)
            p_null = min(1.0, τ_win * P_null_sk)
            lift   = p_null > 1e-12 ? p_obs / p_null : (p_obs > 0 ? Inf : 1.0)
            @printf("      %5d  %8.5f  %8.5f  %8.3f  %s\n", τ_win, p_obs, p_null, lift,
                    lift > 3.0 ? "← STRONG burst attractor" :
                    lift > 1.5 ? "← moderate burst attractor" :
                    "(≈ random)")
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D2 — Conditional entropy of emitted keys
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D2 — Conditional collision entropy H₂(X_t | X_{{t-1}})\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        nb  = DEEP_DIAG_N_BUCKETS
        T_mat = deep_stat.n_trans   # (nb × nb) UInt32

        row_totals = [Int(sum(T_mat[i, :])) for i in 1:nb]
        grand_total = sum(row_totals)

        if grand_total < 4
            @printf("    (insufficient transition data: %d transitions)\n", grand_total)
        else
            # Marginal distribution p_i = row_total[i] / grand_total.
            # H₂(X) = -log₂ Σᵢ pᵢ² (marginal collision entropy).
            p_marg = [row_totals[i] / grand_total for i in 1:nb]
            H2_marginal = -log2(max(1e-300, sum(x^2 for x in p_marg)))

            # H₂(X_t | X_{t-1}) estimated via conditional collision probability:
            #   P(X_{t+1}=j | X_t=i) ≈ T_mat[i,j] / row_totals[i]
            #   P_coll(X_{t+1}=X_{t+1}' | X_t=i) = Σⱼ (T[i,j]/rowsum_i)²
            #   H₂(X|X₋₁) = -log₂ Σᵢ pᵢ · P_coll(·|i)
            #
            # Rows with rt=1 contribute collision probability 1.0 (the single
            # observed transition is perfectly predictable given that row was
            # visited).  Rows with rt=0 are unvisited and contribute nothing.
            # We must sum over ALL visited rows (rt ≥ 1), not just rt ≥ 2,
            # so that H2_cond_sum integrates over the full marginal and
            # -log₂(H2_cond_sum) is a valid entropy in [0, H2_marginal].
            H2_cond_sum = 0.0
            for i in 1:nb
                rt = row_totals[i]
                rt == 0 && continue
                if rt == 1
                    # Only one observed transition: conditional collision prob = 1.
                    H2_cond_sum += p_marg[i] * 1.0
                else
                    row_sq = sum(Float64(T_mat[i, j])^2 for j in 1:nb)
                    H2_cond_sum += p_marg[i] * (row_sq / (Float64(rt)^2))
                end
            end
            # H2_cond_sum is now a valid collision probability in (0,1].
            # H₂(X|X₋₁) ≤ H₂(X) always; reduction ≥ 0 means conditioning helps.
            H2_conditional = -log2(max(1e-300, H2_cond_sum))

            red = H2_marginal - H2_conditional   # information gained from previous emission
            rel_red = H2_marginal > 0 ? red / H2_marginal : 0.0

            @printf("    Transitions analyzed           : %d\n", grand_total)
            @printf("    Coarse buckets                 : %d  (%d bits)\n",
                    nb, DEEP_DIAG_BUCKET_BITS)
            @printf("    H₂(X)    marginal entropy      : %.4f bits\n", H2_marginal)
            @printf("    H₂(X|X₋₁) conditional entropy  : %.4f bits\n", H2_conditional)
            @printf("    Reduction (H₂ − H₂|cond)       : %.4f bits  (%.1f%%)\n",
                    red, 100 * rel_red)
            if rel_red > 0.20
                @printf("    ↑ >20%% reduction: STRONG dynamical state persistence\n")
                @printf("      → emission process retains predictive information across steps.\n")
            elseif rel_red > 0.05
                @printf("    ↑ 5-20%% reduction: moderate persistence (weak algebraic channel)\n")
            else
                @printf("    ↑ <5%% reduction: bursts are mostly independent repeats (no channel)\n")
            end

            # Lag-k conditional entropy for k = 1..DEEP_DIAG_COND_ENT_LAG using the
            # raw bucket sequence from emit_bkt (lags 1..k with sliding window).
            if n_emit >= 2 * DEEP_DIAG_COND_ENT_LAG
                @printf("    Lag-k conditional collision entropy (from full emission sequence):\n")
                @printf("      %4s  %10s  %10s  %8s\n", "lag", "H₂(X|X₋ₖ)", "H₂(X)", "reduction%")
                for lag in 1:DEEP_DIAG_COND_ENT_LAG
                    pairs_by_from = Dict{Int,Vector{Int}}()
                    for t in (lag+1):n_emit
                        from_bkt = emit_bkt[t - lag]
                        v = get!(pairs_by_from, from_bkt, Int[])
                        push!(v, emit_bkt[t])
                    end
                    n_pairs = n_emit - lag
                    p_from  = Dict(k => length(v)/n_pairs for (k, v) in pairs_by_from)
                    cond_coll = 0.0
                    for (from_bkt, tos) in pairs_by_from
                        ntos = length(tos)
                        cnt = Dict{Int,Int}()
                        for b in tos; cnt[b] = get(cnt, b, 0) + 1; end
                        row_c2 = sum(c^2 for c in values(cnt)) / (ntos^2)
                        cond_coll += get(p_from, from_bkt, 0.0) * row_c2
                    end
                    H2_c = -log2(max(1e-300, cond_coll))
                    rr   = H2_marginal > 0 ? (H2_marginal - H2_c) / H2_marginal : 0.0
                    @printf("      %4d  %10.4f  %10.4f  %8.1f%%\n",
                            lag, H2_c, H2_marginal, 100 * rr)
                end
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D3 — Branch ancestry clustering
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D3 — Branch ancestry clustering\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_anc = length(deep_stat.ancestry_log_a)
        if n_anc < 10
            @printf("    (ancestry log too short: %d entries)\n", n_anc)
        else
            # Pack 3-field signature into a UInt64 for counting.
            sig_counts = Dict{UInt64, Int}()
            for i in 1:n_anc
                a_b = UInt64(deep_stat.ancestry_log_a[i])
                par = UInt64(deep_stat.ancestry_log_parity[i])
                kh  = UInt64(deep_stat.ancestry_log_keyhash[i])
                # Coarsen: use top 6 bits of a_bucket (64 a-groups), parity (2 bits),
                # top 10 bits of key hash (1024 key families).
                sig = ((a_b >> 2) & 0x3f) | (par << 6) | ((kh >> 22) << 8)
                sig_counts[sig] = get(sig_counts, sig, 0) + 1
            end

            top_k = 10
            sorted_sigs = sort(collect(sig_counts), by = x -> -x[2])
            total_anc   = sum(values(sig_counts))
            n_sig       = length(sig_counts)

            @printf("    Ancestry entries              : %d\n", n_anc)
            @printf("    Distinct ancestry signatures  : %d  (coarsened: 6 a-bits + 2 parity + 10 key-bits)\n", n_sig)

            cumulative = 0
            @printf("    Top-%d ancestry motifs by emission count:\n", top_k)
            @printf("      %5s  %8s  %8s  %8s\n", "rank", "count", "share%", "cumul%")
            for (rank, (sig, cnt)) in enumerate(sorted_sigs[1:min(top_k, end)])
                cumulative += cnt
                @printf("      %5d  %8d  %8.2f%%  %8.2f%%\n",
                        rank, cnt,
                        100.0 * cnt / total_anc,
                        100.0 * cumulative / total_anc)
            end

            top1_share  = sorted_sigs[1][2] / total_anc
            top10_share = sum(x[2] for x in sorted_sigs[1:min(10, end)]) / total_anc
            @printf("    Top-1  motif mass             : %.2f%%\n", 100 * top1_share)
            @printf("    Top-10 motif mass             : %.2f%%\n", 100 * top10_share)
            if top10_share > 0.5
                @printf("    ↑ >50%% in top-10 motifs: FEW TRANSITION FAMILIES drive most emissions\n")
                @printf("      → reconciles high support + low α₂ + weak geometric bias.\n")
            elseif top10_share > 0.25
                @printf("    ↑ 25-50%%: moderate ancestry concentration\n")
            else
                @printf("    ↑ <25%%: ancestry fairly spread — no dominant transition family\n")
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D4 — Local Jacobian linearization (burst persistence under "perturbation")
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D4 — Burst persistence / Jacobian linearization proxy\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        # We estimate C(τ) = P(LP-hit within τ steps | LP-hit just occurred) using
        # the inter-arrival sequence.  This is the empirical survivorship complement.
        # Baseline: marginal rate λ = n_emit / total_steps ≈ 1/mean_gap.
        if n_emit < 4
            @printf("    (need ≥ 4 emissions; got %d)\n", n_emit)
        else
            arr_sorted = sort(arrivals)
            gaps = [arr_sorted[i] - arr_sorted[i-1] for i in 2:n_emit]
            μ_gap = sum(gaps) / length(gaps)
            λ_base = μ_gap > 0 ? 1.0 / μ_gap : 0.0

            # C_obs(τ): fraction of inter-arrival gaps ≤ τ (empirical CDF of gaps).
            # C_null(τ): 1 - exp(-λ_base × τ) (Poisson null with same rate).
            τ_grid = [1, 2, 5, 10, 20, 50, 100, 200, 500]
            @printf("    Mean inter-arrival gap         : %.2f steps\n", μ_gap)
            @printf("    C(τ) = P(next hit within τ steps):\n")
            @printf("      %5s  %8s  %8s  %8s\n", "τ", "C_obs", "C_null(Poisson)", "lift")
            n_gaps = length(gaps)
            for τ in τ_grid
                c_obs  = count(<=(τ), gaps) / n_gaps
                c_null = 1.0 - exp(-λ_base * τ)
                lift   = c_null > 1e-6 ? c_obs / c_null : (c_obs > 0 ? Inf : 1.0)
                @printf("      %5d  %8.5f  %8.5f  %8.3f  %s\n", τ, c_obs, c_null, lift,
                        lift > 2.0 ? "← PERSISTENT algebraic channel" :
                        lift > 1.3 ? "← moderate persistence" :
                        lift < 0.7 ? "← CHAOTIC (burst destroys next hit)" :
                        "(≈ Poisson)")
            end

            # Persistence score: area under C_obs / C_null ratio up to τ=100.
            # > 1.5 → genuine algebraic channels survive; < 0.8 → chaotic artifacts.
            persist_score = let
                τ_pts = [1, 2, 5, 10, 20, 50, 100]
                lifts  = Float64[]
                for τ in τ_pts
                    c_obs  = count(<=(τ), gaps) / n_gaps
                    c_null = 1.0 - exp(-λ_base * τ)
                    push!(lifts, c_null > 1e-6 ? c_obs / c_null : 1.0)
                end
                sum(lifts) / length(lifts)
            end
            @printf("    Persistence score (mean lift)  : %.4f  %s\n", persist_score,
                    persist_score > 1.5 ? "← GENUINE algebraic channels" :
                    persist_score > 1.1 ? "← mild persistence" :
                    persist_score < 0.8 ? "← CHAOTIC: bursts are coincidence artifacts" :
                    "(≈ Poisson / no structure)")
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D5 — Multiplicity collapse (Zipf / Gini / Hill)
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D5 — Multiplicity collapse (Zipf / Gini / Hill)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        # Build per-key multiplicity from keys_u128.
        key_counts = Dict{UInt128, Int}()
        for k in keys_u128; key_counts[k] = get(key_counts, k, 0) + 1; end

        mult = sort(collect(values(key_counts)), rev=true)
        n_k  = length(mult)
        total_emits = sum(mult)

        @printf("    Distinct keys                  : %d\n", n_k)
        @printf("    Total emissions                : %d\n", total_emits)
        if n_k == 0 || total_emits == 0
            @printf("    (no data)\n")
        else
            @printf("    Max / median multiplicity      : %d / %.1f\n",
                    mult[1], mult[clamp(n_k ÷ 2, 1, n_k)])

            gini = _gini(collect(values(key_counts)))
            @printf("    Gini coefficient               : %.4f  %s\n", gini,
                    gini > 0.7 ? "← EXTREME concentration (tiny set dominates)" :
                    gini > 0.4 ? "← moderate concentration" :
                    "← fairly uniform")

            # Top-k mass fractions.
            for frac in [0.001, 0.01, 0.05, 0.10]
                share = _top_share(collect(values(key_counts)), frac)
                k_count = max(1, round(Int, frac * n_k))
                @printf("    Top %.1f%% of keys (%d keys)      : %.2f%% of emissions\n",
                        100*frac, k_count, 100*share)
            end

            # Hill tail exponent.
            hill_k = min(50, n_k - 1)
            if hill_k >= 2
                # Degenerate case: all multiplicities are 1 (every key is unique).
                # Hill estimator is undefined because all log-ratios vanish.
                if mult[1] == 1
                    @printf("    Hill exponent α̂ (k=%d)         : undefined (all multiplicities = 1, no tail structure)\n",
                            hill_k)
                else
                    α_hill = _hill_exponent(mult; k=hill_k)
                    @printf("    Hill exponent α̂ (k=%d)         : %.3f  %s\n",
                            hill_k, α_hill,
                            α_hill < 1.5 ? "← HEAVY TAIL (α<1.5: power-law multiplicity)" :
                            α_hill < 3.0 ? "← moderate tail" :
                            "← thin tail (quasi-geometric)")
                end
            end

            # Zipf log-log slope from top-100 rank-frequency.
            top_n = min(100, n_k)
            if top_n >= 5
                log_ranks  = [log(Float64(i)) for i in 1:top_n]
                log_counts = [log(Float64(mult[i])) for i in 1:top_n]
                μ_lr, μ_lc = sum(log_ranks)/top_n, sum(log_counts)/top_n
                cov_num = sum((log_ranks[i]-μ_lr)*(log_counts[i]-μ_lc) for i in 1:top_n)
                var_den = sum((log_ranks[i]-μ_lr)^2 for i in 1:top_n)
                zipf_slope = var_den > 0 ? cov_num / var_den : NaN
                @printf("    Zipf log-log slope (top-%d)     : %.4f  %s\n",
                        top_n, zipf_slope,
                        !isnan(zipf_slope) && zipf_slope < -0.8 ?
                            "← Zipf-like rank-frequency (algebraic structure)" :
                        !isnan(zipf_slope) && zipf_slope > -0.3 ?
                            "← flat rank-frequency (uniform keys)" :
                        "← intermediate")
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D6 — Emission-conditioned return maps
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D6 — Emission-conditioned return maps (emission-index space)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_emit < 4 && (@printf("    (need ≥ 4 emissions)\n"); @goto d6_done)

        nb = DEEP_DIAG_N_BUCKETS
        # Build transition count matrix over coarse buckets in emission space.
        trans_cnt = Dict{Tuple{Int,Int}, Int}()
        for i in 2:n_emit
            b_from = emit_bkt[i-1]
            b_to   = emit_bkt[i]
            k = (b_from, b_to)
            trans_cnt[k] = get(trans_cnt, k, 0) + 1
        end

        # Marginal and transition entropy.
        n_trans_total = n_emit - 1
        p_joint = Dict((k[1], k[2]) => v / n_trans_total for (k, v) in trans_cnt)
        p_from  = Dict{Int,Float64}()
        for ((b_f, _), p) in p_joint
            p_from[b_f] = get(p_from, b_f, 0.0) + p
        end

        # H(X_t) marginal from emit_bkt.
        marginal_cnt = Dict{Int,Int}()
        for b in emit_bkt; marginal_cnt[b] = get(marginal_cnt, b, 0) + 1; end
        H_marg = -sum((c/n_emit)*log2(c/n_emit) for c in values(marginal_cnt))

        # H(X_t | X_{t-1}) via chain rule.
        H_joint  = -sum(p * log2(max(1e-300, p)) for p in values(p_joint))
        H_from   = -sum(p * log2(max(1e-300, p)) for p in values(p_from))
        H_cond_e = H_joint - H_from

        @printf("    Active (from,to) pairs         : %d\n", length(trans_cnt))
        @printf("    H(X_t) marginal emission entropy: %.4f bits\n", H_marg)
        @printf("    H(X_t|X_{{t-1}}) in emission space: %.4f bits\n", H_cond_e)
        @printf("    Effective automaton size        : 2^%.2f ≈ %.1f states\n",
                H_cond_e, 2.0^H_cond_e)

        # Self-loop fraction: fraction of transitions with b_from == b_to.
        n_self = sum(v for ((f,t), v) in trans_cnt if f == t; init=0)
        @printf("    Self-loop fraction              : %.4f  (%.1f%% of transitions)\n",
                n_self / n_trans_total, 100.0 * n_self / n_trans_total)

        # Strongly-connected component sizes via naive Union-Find on the top-100
        # most-visited states (computational guardrail).
        active_buckets = sort(collect(keys(marginal_cnt)), by=b->-marginal_cnt[b])[1:min(100, end)]
        bkt_set = Set(active_buckets)
        parent = Dict{Int,Int}(b => b for b in active_buckets)
        function uf_find(x); while parent[x] != x; parent[x] = parent[parent[x]]; x = parent[x] end; x end
        function uf_union(x, y); rx, ry = uf_find(x), uf_find(y); rx != ry && (parent[rx] = ry); end
        for ((f, t), _) in trans_cnt
            (f in bkt_set && t in bkt_set) && uf_union(f, t)
        end
        root_sizes = Dict{Int,Int}()
        for b in active_buckets
            r = uf_find(b)
            root_sizes[r] = get(root_sizes, r, 0) + 1
        end
        scc_sizes = sort(collect(values(root_sizes)), rev=true)
        @printf("    Top active buckets analyzed     : %d\n", length(active_buckets))
        @printf("    Strongly-connected component sizes (top 5): %s\n",
                join(string.(scc_sizes[1:min(5,end)]), ", "))
        if length(scc_sizes) == 1
            @printf("    ↑ Single giant SCC: emission process is strongly connected\n")
        else
            n_singletons = count(==(1), scc_sizes)
            @printf("    ↑ %d SCCs (%d singletons): %s\n",
                    length(scc_sizes), n_singletons,
                    length(scc_sizes) <= 3 ? "few large components — structured automaton" :
                    "fragmented — emission lives on multiple disjoint fibers")
        end

        @label d6_done
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D7 — Marginal utility of LP1-conj table entries
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D7 — Marginal utility of LP1-conj table entries\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        is_first = deep_stat.is_first_closure
        n_first  = length(is_first)
        if n_first == 0
            @printf("    (no closure data recorded — check ConjDeepStat wiring)\n")
        else
            n_novel      = count(identity, is_first)
            n_redundant  = n_first - n_novel
            @printf("    Total closures recorded        : %d\n", n_first)
            @printf("    Novel closures (first for key) : %d  (%.1f%%)\n",
                    n_novel, 100.0 * n_novel / n_first)
            @printf("    Redundant closures             : %d  (%.1f%%)\n",
                    n_redundant, 100.0 * n_redundant / n_first)

            # ΔT_solve(N): simulate which fraction of closures is enabled when
            # only the first N% of the conj snapshot entries are used.
            # We approximate this by treating each novel closure as "enabling a solve"
            # and measuring the cumulative solve fraction vs emission index.
            fracs = [0.10, 0.20, 0.30, 0.50, 0.70, 0.90, 1.0]
            @printf("    Cumulative solve-enabling closures vs emission fraction:\n")
            @printf("      %8s  %10s  %10s  %8s\n",
                    "emit%", "n_closures", "n_novel", "marginal_util")
            cumul_novel = 0
            prev_novel  = 0
            for frac in fracs
                idx  = clamp(round(Int, frac * n_first), 1, n_first)
                cumul_novel = count(identity, is_first[1:idx])
                marginal    = idx > 1 ?
                    (cumul_novel - prev_novel) / max(1, round(Int, (fracs[1])*n_first)) :
                    NaN
                @printf("      %8.1f%%  %10d  %10d  %8s\n",
                        100*frac, idx, cumul_novel,
                        isnan(marginal) ? "  n/a" : @sprintf("%.4f", cumul_novel / idx))
                prev_novel = cumul_novel
            end

            # Saturation point: first fraction where marginal novel rate < 10%.
            sat_frac = 1.0
            cum_prev  = 0
            for frac in [0.05, 0.10, 0.20, 0.30, 0.40, 0.50, 0.60, 0.70, 0.80, 0.90]
                idx  = clamp(round(Int, frac * n_first), 1, n_first)
                cum_now = count(identity, is_first[1:idx])
                marginal_rate = n_novel > 0 ? (cum_now - cum_prev) / n_novel : 0.0
                cum_prev = cum_now
                # marginal_rate is the fraction of all novel closures contributed by
                # this 5-10% slice; saturation when <5% additional from next slice.
                if marginal_rate < 0.05 && sat_frac == 1.0
                    sat_frac = frac
                end
            end
            if sat_frac < 1.0
                @printf("    Saturation point (≥95%% novel closures): ~%.0f%% of table\n",
                        100 * sat_frac)
                @printf("    → Table could be reduced by ~%.0f%% with <5%% closure penalty\n",
                        100 * (1.0 - sat_frac))
            else
                @printf("    No saturation detected: table is efficiently used\n")
            end
        end

        # If conj_snap available, report overall snapshot density.
        if conj_snap !== nothing
            snap_sz = length(conj_snap)
            @printf("    Conj snapshot size             : %d entries\n", snap_sz)
            @printf("    Closures / snapshot entry      : %.4f\n",
                    snap_sz > 0 ? n_first / snap_sz : 0.0)
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D8 — Closure-depth distribution
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D8 — Closure-depth distribution\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        depths = deep_stat.d8_depths
        nd = length(depths)

        if nd < 2
            @printf("    (need ≥ 2 closures with depth data; got %d — check miss-path wiring)\n", nd)
            @goto d8_done
        end

        # ── Basic moments ──────────────────────────────────────────────────
        d_min  = minimum(depths)
        d_max  = maximum(depths)
        d_mean = sum(depths) / nd
        d_var  = nd < 2 ? 0.0 : sum((x - d_mean)^2 for x in depths) / (nd - 1)
        d_std  = sqrt(d_var)
        d_cv   = d_mean > 0 ? d_std / d_mean : NaN
        d_sorted = sort(depths)
        p10 = d_sorted[max(1, round(Int, 0.10 * nd))]
        p50 = d_sorted[max(1, round(Int, 0.50 * nd))]
        p90 = d_sorted[max(1, round(Int, 0.90 * nd))]
        p99 = d_sorted[max(1, round(Int, 0.99 * nd))]

        @printf("    Closures with depth data       : %d\n", nd)
        @printf("    Depth min/p10/p50/p90/p99/max  : %d / %d / %d / %d / %d / %d\n",
                d_min, p10, p50, p90, p99, d_max)
        @printf("    Mean depth / CV                : %.1f / %.4f\n", d_mean, d_cv)
        if d_cv > 1.5
            @printf("    ↑ CV > 1.5: HIGHLY HEAVY-TAILED depth distribution\n")
            @printf("      → consistent with metastable basin hopping: most closures fast,\n")
            @printf("        rare closures survive extremely long.\n")
        elseif d_cv > 1.0
            @printf("    ↑ CV > 1.0: moderately heavy tail (over-dispersed)\n")
        else
            @printf("    ↑ CV ≤ 1.0: depth distribution near-geometric (memoryless)\n")
        end

        # ── Depth histogram with log-spaced bins ───────────────────────────
        # Bins: [0,1), [1,5), [5,20), [20,50), [50,150), [150,400), [400,∞)
        bins      = [0, 1, 5, 20, 50, 150, 400, typemax(Int)]
        bin_names = ["[0,1)", "[1,5)", "[5,20)", "[20,50)", "[50,150)", "[150,400)", "[400,∞)"]
        bin_cnts  = zeros(Int, length(bins) - 1)
        for d in depths
            for bi in 1:(length(bins)-1)
                if d >= bins[bi] && d < bins[bi+1]
                    bin_cnts[bi] += 1; break
                end
            end
        end
        @printf("    Closure-depth histogram:\n")
        @printf("      %12s  %7s  %7s\n", "depth range", "count", "frac%")
        for bi in 1:length(bin_cnts)
            @printf("      %12s  %7d  %7.2f%%\n",
                    bin_names[bi], bin_cnts[bi], 100.0 * bin_cnts[bi] / nd)
        end

        # ── Hazard function h(d) ───────────────────────────────────────────
        # h(d) = P(close at step d | not closed before d)
        # Use same log-spaced bins; survivors = nd - cumulative closed before bin.
        @printf("    Hazard h(band) = P(close in band | survived to band start):\n")
        @printf("      %12s  %7s  %7s  %7s\n", "band", "closed", "survived", "h(band)")
        surviving = nd
        for bi in 1:length(bin_cnts)
            closed_in_band = bin_cnts[bi]
            h = surviving > 0 ? closed_in_band / surviving : 0.0
            @printf("      %12s  %7d  %7d  %7.4f%s\n",
                    bin_names[bi], closed_in_band, surviving,
                    h, h > 0.5 ? "  ← dominant" : "")
            surviving -= closed_in_band
        end

        # ── Conditional success P(close in band d | not before) ───────────
        # Same as hazard above but expressed as cumulative survival complement.
        # Already printed implicitly via h(d); skip duplication.

        # ── Depth autocorrelation ACF(1) ──────────────────────────────────
        if nd >= 8
            μd  = d_mean
            cov_d = sum((depths[i] - μd) * (depths[i+1] - μd)
                        for i in 1:(nd-1)) / (nd - 1)
            var_d = nd > 1 ? sum((x - μd)^2 for x in depths) / nd : 1.0
            acf1_d = var_d > 0 ? cov_d / var_d : 0.0
            @printf("    Depth ACF(1)                   : %.4f  %s\n", acf1_d,
                    acf1_d > 0.15  ? "← POSITIVE: consecutive depths correlated (basin memory)" :
                    acf1_d < -0.15 ? "← NEGATIVE: depth alternates (repulsion between long closures)" :
                    "(≈ uncorrelated)")
        end

        # ── Depth-band transition matrix (3 coarse bands) ─────────────────
        # Bands: short=[0,20), medium=[20,150), long=[150,∞)
        band_of(d) = d < 20 ? 1 : d < 150 ? 2 : 3
        band_names = ["short(<20)", "med(20-150)", "long(≥150)"]
        trans_bd = zeros(Int, 3, 3)
        for i in 1:(nd-1)
            bf = band_of(depths[i])
            bt = band_of(depths[i+1])
            trans_bd[bf, bt] += 1
        end
        @printf("    Depth-band transition matrix (rows=from, cols=to):\n")
        @printf("      %12s  %12s  %12s  %12s\n", "from\\to", band_names[1], band_names[2], band_names[3])
        for r in 1:3
            row_sum = sum(trans_bd[r, :])
            if row_sum > 0
                @printf("      %12s  %12.3f  %12.3f  %12.3f\n",
                        band_names[r],
                        trans_bd[r,1]/row_sum, trans_bd[r,2]/row_sum, trans_bd[r,3]/row_sum)
            end
        end

        # ── Depth-conditioned emission entropy H(key | depth band) ────────
        # For each depth band, compute Shannon entropy of coarse key bucket.
        @printf("    Depth-conditioned key entropy H(bucket | depth band):\n")
        @printf("      %12s  %7s  %7s  %8s\n", "band", "n", "H(bits)", "H/H_max")
        close_bkt = deep_stat.d8_close_bkt
        for (bi, bname) in enumerate(band_names)
            band_bkts = Int[]
            for ci in 1:nd
                band_of(depths[ci]) == bi && push!(band_bkts, Int(close_bkt[ci]))
            end
            nb_band = length(band_bkts)
            nb_band < 2 && continue
            cnt_b = Dict{Int,Int}()
            for b in band_bkts; cnt_b[b] = get(cnt_b, b, 0) + 1; end
            H_band = -sum((c/nb_band)*log2(c/nb_band) for c in values(cnt_b))
            H_max  = log2(Float64(DEEP_DIAG_N_BUCKETS))
            @printf("      %12s  %7d  %7.4f  %8.4f\n", bname, nb_band, H_band, H_max > 0 ? H_band/H_max : 0.0)
        end

        # ── Depth-conditioned α₂ (collision entropy) ──────────────────────
        @printf("    Depth-conditioned collision entropy α₂(bucket | depth band):\n")
        @printf("      %12s  %7s  %10s  %s\n", "band", "n", "α₂ (bits)", "interpretation")
        for (bi, bname) in enumerate(band_names)
            band_bkts = Int[]
            for ci in 1:nd
                band_of(depths[ci]) == bi && push!(band_bkts, Int(close_bkt[ci]))
            end
            nb_band = length(band_bkts)
            nb_band < 2 && continue
            cnt_b = Dict{Int,Int}()
            for b in band_bkts; cnt_b[b] = get(cnt_b, b, 0) + 1; end
            p2sum = sum((c/nb_band)^2 for c in values(cnt_b))
            a2_band = p2sum > 0 ? -log2(p2sum) : NaN
            interp = isnan(a2_band) ? "—" :
                     a2_band < 4.0  ? "← VERY LOW: tiny support (high concentration)" :
                     a2_band < 7.0  ? "← low-moderate" :
                     a2_band < 9.0  ? "← near-uniform in active set" :
                     "← near-uniform over full bucket space"
            @printf("      %12s  %7d  %10.4f  %s\n", bname, nb_band, a2_band, interp)
        end

        # ── Lyapunov proxy: depth variance conditioned on a_bucket ────────
        # Partition closures into 8 coarse a-buckets; report depth std per band.
        # High variance in a specific a-bucket → that a-value drives long-lived keys.
        close_abkt = deep_stat.d8_close_abkt
        N_ABKT_COARSE = 8
        abkt_depths = [Int[] for _ in 1:N_ABKT_COARSE]
        if !isempty(close_abkt)
            max_abkt = maximum(Int.(close_abkt))
            for ci in 1:nd
                ab = Int(close_abkt[ci])
                coarse = clamp(1 + (ab * N_ABKT_COARSE) ÷ (max_abkt + 1), 1, N_ABKT_COARSE)
                push!(abkt_depths[coarse], depths[ci])
            end
            @printf("    Lyapunov proxy — depth std dev by a-bucket band (8 coarse bands):\n")
            @printf("      %8s  %7s  %9s  %9s\n", "a-band", "n", "mean_d", "std_d")
            for ab in 1:N_ABKT_COARSE
                v = abkt_depths[ab]
                length(v) < 2 && continue
                μ_ab = sum(v) / length(v)
                σ_ab = sqrt(sum((x - μ_ab)^2 for x in v) / (length(v)-1))
                @printf("      %8d  %7d  %9.1f  %9.1f\n", ab, length(v), μ_ab, σ_ab)
            end
        end

        @label d8_done
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D9 — H(step opcode | recent LP1-conj)
    #
    #  For each step in the opcode log we ask: given that this step follows
    #  within τ* steps of an LP1-conj emission, does the distribution of step
    #  opcodes change?  H(opcode | in_window) vs H(opcode | baseline) reveals
    #  whether the walk enters dynamically constrained regions post-emission.
    #
    #  We use τ* = 128 steps (from hazard decay in D8) and τ_long = 512 as a
    #  far-field baseline check.
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D9 — H(step opcode | recent LP1-conj)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_op = length(deep_stat.opcode_log)
        if n_op < 20
            @printf("    (opcode log too short: %d steps — check record_conj_deep_opcode! wiring)\n", n_op)
        else
            opcodes   = deep_stat.opcode_log
            is_lp1c   = deep_stat.opcode_is_lp1c
            opcode_names = ["0-LP", "1LP-aff", "1LP-conj", "2LP-aff", "2LP-conj", "skip"]
            N_OPCODES = 6

            # Build in_window flag: step i is "in window" if there exists j < i
            # with is_lp1c[j] == true and (i - j) ≤ τ_win.
            for (τ_win_label, τ_win) in (("τ*=128", 128), ("τ_long=512", 512))
                # Scan forward: maintain last_lp1c_idx.
                cnt_window   = zeros(Int, N_OPCODES)
                cnt_baseline = zeros(Int, N_OPCODES)
                last_lp1c    = -typemax(Int)
                for i in 1:n_op
                    is_lp1c[i] && (last_lp1c = i)
                    in_win = (i - last_lp1c) <= τ_win && last_lp1c > 0
                    opc = Int(opcodes[i]) + 1
                    1 <= opc <= N_OPCODES || continue
                    if in_win
                        cnt_window[opc] += 1
                    else
                        cnt_baseline[opc] += 1
                    end
                end

                n_win  = sum(cnt_window)
                n_base = sum(cnt_baseline)

                _ent(cnt) = begin
                    n = sum(cnt)
                    n == 0 && return 0.0
                    -sum((c / n) * log2(max(1e-300, c / n)) for c in cnt if c > 0)
                end

                H_win  = _ent(cnt_window)
                H_base = _ent(cnt_baseline)

                @printf("    Window %s  (n_win=%d  n_base=%d):\n", τ_win_label, n_win, n_base)
                @printf("      H(opcode | in_window)  : %.4f bits\n", H_win)
                @printf("      H(opcode | baseline)   : %.4f bits\n", H_base)
                Δ = H_base - H_win
                @printf("      ΔH = H_base − H_win    : %+.4f bits  %s\n", Δ,
                        Δ > 0.3  ? "← ENTROPY COLLAPSE: walk constrained post-emission" :
                        Δ > 0.1  ? "← moderate constraint post-emission" :
                        Δ < -0.1 ? "← entropy INCREASE post-emission (diversification)" :
                        "(≈ no change)")
                @printf("      %12s  %8s  %8s  %8s\n", "opcode", "P_win", "P_base", "lift")
                for k in 1:N_OPCODES
                    p_w = n_win  > 0 ? cnt_window[k]   / n_win  : 0.0
                    p_b = n_base > 0 ? cnt_baseline[k] / n_base : 0.0
                    lift = p_b > 1e-12 ? p_w / p_b : (p_w > 0 ? Inf : 1.0)
                    @printf("      %12s  %8.5f  %8.5f  %8.3f  %s\n",
                            opcode_names[k], p_w, p_b, lift,
                            lift > 2.0 ? "← OVER-REPRESENTED in window" :
                            lift < 0.5 ? "← SUPPRESSED in window" : "")
                end
                println()
            end
        end
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D10 — Transition graph compression
    #
    #  Operates on the existing n_trans matrix (D2) to estimate:
    #    1. Spectral gap of the row-stochastic emission transition matrix
    #       via power iteration (λ₁=1 − λ₂ where λ₂ is the second eigenvalue).
    #       Small gap → slow mixing; large gap → fast mixing.
    #    2. SCC persistence: identify strongly-connected components of the
    #       directed bucket graph (edges with weight ≥ threshold) and report
    #       their sizes and self-transition rates.
    #    3. Return probability to the top-5 most-visited buckets.
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D10 — Transition graph compression\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        nb  = DEEP_DIAG_N_BUCKETS
        T   = deep_stat.n_trans
        row_totals = [Int(sum(T[i, :])) for i in 1:nb]
        grand_total = sum(row_totals)

        if grand_total < 8
            @printf("    (insufficient transition data: %d transitions)\n", grand_total)
            @goto d10_done
        end

        # Build row-stochastic matrix P (only for active rows to save work).
        # Active = rows with row_total ≥ 1.
        active_rows = [i for i in 1:nb if row_totals[i] > 0]
        n_active = length(active_rows)

        # ── Spectral gap via power iteration on P ────────────────────────
        # We only iterate on the active subspace (n_active × n_active).
        # Start from a non-stationary vector, run ~50 iterations, compare
        # convergence to estimate gap.  This is a rough heuristic only.
        if n_active >= 2
            # Map active rows to 1:n_active
            row_idx = Dict(r => i for (i, r) in enumerate(active_rows))
            # Stationary vector estimate: proportional to row_totals.
            pi_vec = [Float64(row_totals[active_rows[i]]) for i in 1:n_active]
            pi_vec ./= sum(pi_vec)

            # Random starting vector orthogonal to pi_vec (approximately).
            # Use alternating ±1 signed as a simple non-pi vector.
            v = Float64[isodd(i) ? 1.0 : -1.0 for i in 1:n_active]
            v .-= sum(v .* pi_vec) .* pi_vec   # project out pi component
            v_norm = sqrt(sum(v.^2))
            v_norm < 1e-12 && (v = randn(n_active); v .-= sum(v .* pi_vec) .* pi_vec; v_norm = sqrt(sum(v.^2)))
            v ./= max(1e-30, v_norm)

            # Apply P: w[j] = Σᵢ v[i] × P[active_rows[i], active_rows[j]]
            λ2_est = NaN
            for iter in 1:60
                w = zeros(Float64, n_active)
                for (li, r) in enumerate(active_rows)
                    rt = row_totals[r]
                    rt == 0 && continue
                    vi = v[li]
                    abs(vi) < 1e-15 && continue
                    for (lj, c) in enumerate(active_rows)
                        t_rc = Int(T[r, c])
                        t_rc == 0 && continue
                        w[lj] += vi * (t_rc / rt)
                    end
                end
                # Project out pi and renormalise.
                w .-= sum(w .* pi_vec) .* pi_vec
                w_norm = sqrt(sum(w.^2))
                if w_norm < 1e-15
                    λ2_est = 0.0; break
                end
                λ2_est = w_norm   # |Pv| / |v| ≈ |λ₂|
                v = w ./ w_norm
            end

            if !isnan(λ2_est)
                spectral_gap = 1.0 - λ2_est
                @printf("    Active buckets (row_total ≥ 1)  : %d / %d\n", n_active, nb)
                @printf("    |λ₂| estimate (power iter, 60)  : %.6f\n", λ2_est)
                @printf("    Spectral gap  1 − |λ₂|          : %.6f  %s\n", spectral_gap,
                        spectral_gap > 0.5  ? "← FAST mixing: emission sequence mixes quickly" :
                        spectral_gap > 0.1  ? "← moderate mixing" :
                        spectral_gap > 0.01 ? "← SLOW mixing: persistent metastable clusters" :
                        "← NEAR-ZERO GAP: extremely slow mixing or disconnected graph")
            end
        end

        # ── SCC detection (Kosaraju on the active bucket graph) ──────────
        # Threshold: include edge (i→j) if T[i,j] / row_total[i] ≥ 1/n_active.
        # This keeps only edges that carry at least 1/(n_active) of traffic.
        edge_thresh = n_active > 0 ? 1.0 / n_active : 0.0
        # Forward DFS pass
        visited  = falses(nb)
        finish_order = Int[]
        sizehint!(finish_order, n_active)
        function dfs_forward!(u)
            visited[u] = true
            rt = row_totals[u]
            if rt > 0
                for c in active_rows
                    !visited[c] && Int(T[u, c]) / rt >= edge_thresh && dfs_forward!(c)
                end
            end
            push!(finish_order, u)
        end
        for r in active_rows; !visited[r] && dfs_forward!(r); end

        # Reverse DFS pass: follow transpose edges in reverse finish order.
        in_scc    = zeros(Int, nb)   # scc_id for each node (0 = unassigned)
        scc_id    = 0
        visited2  = falses(nb)
        function dfs_reverse!(u, sid)
            visited2[u] = true
            in_scc[u] = sid
            for r2 in active_rows
                rt2 = row_totals[r2]
                !visited2[r2] && rt2 > 0 && Int(T[r2, u]) / rt2 >= edge_thresh &&
                    dfs_reverse!(r2, sid)
            end
        end
        for u in reverse(finish_order)
            if !visited2[u] && row_totals[u] > 0
                scc_id += 1
                dfs_reverse!(u, scc_id)
            end
        end

        # Summarize SCCs.
        scc_sizes = Dict{Int, Int}()
        for r in active_rows
            sid = in_scc[r]
            sid == 0 && continue
            scc_sizes[sid] = get(scc_sizes, sid, 0) + 1
        end
        sorted_sccs = sort(collect(values(scc_sizes)), rev=true)
        n_sccs = length(sorted_sccs)
        large_sccs = count(x -> x > 1, sorted_sccs)
        singleton_sccs = count(x -> x == 1, sorted_sccs)

        @printf("    SCCs (edge_thresh=1/n_active)    : %d total  (%d large, %d singleton)\n",
                n_sccs, large_sccs, singleton_sccs)
        if !isempty(sorted_sccs)
            @printf("    Top-5 SCC sizes                 :")
            for sz in sorted_sccs[1:min(5, end)]
                @printf(" %d", sz)
            end
            @printf("\n")
            if sorted_sccs[1] > n_active ÷ 2
                @printf("    ↑ Giant SCC covers >50%% of active buckets: well-connected emission graph\n")
            elseif large_sccs <= 3 && singleton_sccs > n_active * 0.7
                @printf("    ↑ Mostly singletons: fragmented emission graph — distinct dynamical channels\n")
            end
        end

        # ── Return probabilities to top-5 most-visited buckets ───────────
        top5_by_traffic = sort(active_rows, by=r -> -row_totals[r])[1:min(5, end)]
        @printf("    Return probability to top-5 most-visited buckets:\n")
        @printf("      %6s  %8s  %8s  %8s\n", "bucket", "traffic", "p_self", "p_return(2)")
        for r in top5_by_traffic
            rt = row_totals[r]
            rt == 0 && continue
            p_self = Float64(Int(T[r, r])) / rt

            # p_return in 2 steps: Σⱼ P[r,j] × P[j,r]
            p_ret2 = 0.0
            for c in active_rows
                p_rc = Float64(Int(T[r, c])) / rt
                p_rc < 1e-12 && continue
                rtc = row_totals[c]
                rtc == 0 && continue
                p_cr = Float64(Int(T[c, r])) / rtc
                p_ret2 += p_rc * p_cr
            end
            @printf("      %6d  %8d  %8.5f  %8.5f  %s\n", r - 1, rt, p_self, p_ret2,
                    p_self > 0.3 ? "← STICKY" : p_self > 0.1 ? "← moderate self-loop" : "")
        end

        @label d10_done
    end

    # ──────────────────────────────────────────────────────────────────────
    #  D11 — Branch-conditioned α₂
    #
    #  Uses deep_stat.opcode_log and phi_stat.lp1_conj_key_blog together to
    #  compute per-opcode collision entropy α₂.  The key_blog is the full
    #  LP1-conj partial stream (every store and close), recorded by
    #  record_lp1_conj_partial! in handle_1lp_conj!.  The opcode log records
    #  a superset of steps; we extract only the 1LP-conj steps (opcode == 2).
    #
    #  Additionally, using the opcode_log, we compute:
    #    • per-opcode step fraction (traffic share),
    #    • per-opcode 1LP-conj emission lift (emissions relative to traffic),
    #    • α₂ on 1LP-conj partials: first half vs second half of key_blog
    #      (stationarity check, equivalent to D8's depth-conditioned α₂).
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D11 — Branch-conditioned α₂ and step-opcode traffic analysis\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_op = length(deep_stat.opcode_log)
        blog = phi_stat.lp1_conj_key_blog   # UInt16 bucket per LP1-conj partial
        n_blog = length(blog)

        opcode_names = ["0-LP", "1LP-aff", "1LP-conj", "2LP-aff", "2LP-conj", "skip"]
        N_OPCODES = 6

        if n_op < 10
            @printf("    (opcode log too short: %d steps)\n", n_op)
        else
            # Per-opcode step counts.
            opc_count = zeros(Int, N_OPCODES)
            opc_emit  = zeros(Int, N_OPCODES)   # LP1-conj emissions per opcode
            for i in 1:n_op
                k = Int(deep_stat.opcode_log[i]) + 1
                1 <= k <= N_OPCODES && (opc_count[k] += 1)
                deep_stat.opcode_is_lp1c[i] && k == 3 && (opc_emit[3] += 1)
            end
            total_steps = sum(opc_count)
            total_emit  = sum(opc_emit)

            @printf("    Step-opcode traffic distribution (n=%d valid phi steps):\n", total_steps)
            @printf("      %12s  %8s  %8s  %8s\n", "opcode", "count", "share%", "emit_lift")
            for k in 1:N_OPCODES
                share = total_steps > 0 ? opc_count[k] / total_steps : 0.0
                # emit_lift: fraction of LP1-conj emissions originating from this opcode
                # relative to traffic share.  Only meaningful for k==3 (1LP-conj).
                emit_frac = total_emit > 0 ? opc_emit[k] / total_emit : 0.0
                lift = share > 1e-12 ? emit_frac / share : (emit_frac > 0 ? Inf : 0.0)
                @printf("      %12s  %8d  %8.3f%%  %8.3f  %s\n",
                        opcode_names[k], opc_count[k], 100.0 * share, lift,
                        k == 3 && lift > 0 ? "(by definition)" : "")
            end
            println()
        end

        # α₂ per half of key_blog (stationarity of LP1-conj key geometry).
        if n_blog >= 8
            half = n_blog ÷ 2
            function _alpha2_blog(slice::AbstractVector{UInt16})
                n = length(slice)
                n == 0 && return NaN
                cnt = Dict{UInt16, Int}()
                for b in slice; cnt[b] = get(cnt, b, 0) + 1; end
                p2 = sum((c / n)^2 for c in values(cnt))
                p2 > 0 ? -log2(p2) : NaN
            end
            a2_first  = _alpha2_blog(blog[1:half])
            a2_second = _alpha2_blog(blog[half+1:end])
            a2_all    = _alpha2_blog(blog)
            Δa2 = a2_second - a2_first

            @printf("    LP1-conj key_blog α₂ stationarity (n=%d partials):\n", n_blog)
            @printf("      α₂ (full)        : %.4f bits\n", a2_all)
            @printf("      α₂ (first half)  : %.4f bits\n", a2_first)
            @printf("      α₂ (second half) : %.4f bits\n", a2_second)
            @printf("      Δα₂ (2nd − 1st)  : %+.4f bits  %s\n", Δa2,
                    abs(Δa2) > 1.0 ? "← NON-STATIONARY: key geometry changing over run" :
                    abs(Δa2) > 0.3 ? "← moderate drift" :
                    "(≈ stationary)")
            println()

            # Per-quartile α₂ to catch gradual drift.
            if n_blog >= 16
                q = n_blog ÷ 4
                @printf("    Per-quartile α₂:\n")
                @printf("      %6s  %8s  %8s\n", "qrt", "n", "α₂")
                for qi in 1:4
                    lo = (qi - 1) * q + 1
                    hi = qi == 4 ? n_blog : qi * q
                    a2q = _alpha2_blog(blog[lo:hi])
                    @printf("      %6d  %8d  %8.4f\n", qi, hi - lo + 1, a2q)
                end
            end
        else
            @printf("    (key_blog too short for α₂ stationarity: %d partials)\n", n_blog)
        end
    end

    @printf("\n══ End LP1-conj deep diagnostics ════════════════════════════════════\n")
    flush(stdout)
end
