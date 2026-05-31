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
#  D12 — Alpha/anchor joint support diagnostic
#       Tests the hypothesis that the x-support of {alpha·G : alpha ∈ Z_ell} is
#       small, causing LP1-conj closures to cluster in (alpha, P0.x) space.
#       At each LP1-conj store and close, records (alpha_cur, px = P0.x).
#       Post-hoc analysis:
#         • 2-D histogram (alpha_bucket × px_bucket) for stores and closes,
#           χ²/dof vs uniform to detect concentration.
#         • Mutual information I(alpha_bucket; px_bucket) across all events.
#         • Paired delta-alpha: for each matched (store→close) pair keyed on
#           lp_key, histogram of |alpha_close − alpha_store| mod ell.  A spike
#           near 0 confirms closes happen at nearly the same alpha as their store.
#         • Per-px_bucket alpha entropy H(alpha | px=b): low → anchor constrains
#           which alpha values can produce a non-split RS pair at that anchor.
#
#  D13 — Mumford coordinate support cardinality
#       For all α·a store events, computes |S| for each marginal coordinate
#       (u0, u1, v0, v1), the u-poly pair (u0,u1), the v-poly pair (v0,v1),
#       and the full 4-tuple (distinct LP keys).  Each expressed as
#       κ = log_p(|S|).  A naive bound gives κ=1; subvariety confinement
#       gives κ<1, which directly bounds LP1-conj table pressure and complexity.
#       Also reports key multiplicity (Gini, top-k mass, mean hits per key)
#       and p-adic valuation fractions (fraction of coords ≡0 mod p).
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

# ---------------------------------------------------------------------------
#  D16 — Pre-burst state fingerprinting
#
#  Whenever a repeat of an LP1-conj coarse key bucket is observed at lag
#  Δ ∈ [D16_LAG_LO, D16_LAG_HI] in emission-index space, we record the
#  fingerprint of the *earlier* emission (step_mod, partition_id = i0) as a
#  "pre-burst" sample.  We also maintain a parallel "baseline" histogram sampled
#  at the same rate from all emissions, regardless of burst.
#
#  Histograms are keyed by (step_mod::UInt8, partition_id::UInt16) packed into
#  a UInt32, stored as flat Dict{UInt32, Int} counters.  Memory is negligible.
#
#  Ring buffer: D16_RING_SIZE entries of 3 UInt16s each
#    ring_step_mod   — (raw_step % 256) at emission i, as UInt8 stored in UInt16
#    ring_partition  — i0 (partition_id) at emission i
#    ring_bkt        — coarse key bucket (DEEP_DIAG_BUCKET_BITS bits) at emission i
# ---------------------------------------------------------------------------
const D16_LAG_LO      = 10
const D16_LAG_HI      = 40
const D16_RING_SIZE   = D16_LAG_HI + 4      # ring covers at least LAG_HI slots
const D16_GATE_DENOM  = 64                  # 1/64 random sampling gate
const D16_MAX_SAMPLES = 50_000             # cap total pre-burst samples
const DEEP_DIAG_MAX_ANCESTRY = 500_000    # cap on ancestry log entries per thread
const DEEP_DIAG_COND_ENT_LAG = 4         # max lag for conditional collision entropy
const DEEP_DIAG_MAX_OPCODE_LOG = 2_000_000  # cap on opcode log entries per thread (~2 MB)
const D12_MAX_EVENTS           = 500_000    # cap on D12 store/close event records per thread (~8 MB)
const D7_MAX_CLOSURES          = 500_000    # cap on is_first_closure log per thread (~0.5 MB)
const D8_MAX_DEPTHS            = 500_000    # cap on d8_depths/close_bkt/close_abkt per thread (~5 MB)
const D8_MAX_SHADOW       = 500_000    # Cap on shadow dictionary entries per thread

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

    # D12 — Alpha/anchor joint support diagnostic.
    # At each LP1-conj store (miss), record (alpha_cur, px) so we can later
    # test whether closures cluster in alpha×px space.
    # d12_store_alpha: alpha_cur (mod ell, stored as Int) at each store event.
    # d12_store_px:    P0.x at each store event (Int).
    # d12_store_key:   lp_key (UInt128) at each store, for pairing with closes.
    # d12_close_alpha: alpha_cur at each close (emission) event.
    # d12_close_px:    P0.x at each close event.
    # d12_close_key:   lp_key at each close, for delta-alpha pairing.
    # Capped at D12_MAX_EVENTS entries each to bound memory (~8 MB at 500k).
    d12_store_alpha ::Vector{Int}
    d12_store_px    ::Vector{Int}
    d12_store_key   ::Vector{UInt128}
    d12_close_alpha ::Vector{Int}
    d12_close_px    ::Vector{Int}
    d12_close_key   ::Vector{UInt128}

    # D14/D15 — φ-coefficient 'a' at each store event, for conditional entropy
    # and residual support analysis conditioned on px_bucket.
    # Parallel to d12_store_* vectors (same cap D12_MAX_EVENTS).
    # -1 sentinel means 'a' was unavailable (caller didn't provide it).
    d14_store_a     ::Vector{Int}

    # D16 — Pre-burst state fingerprinting.
    # Ring buffer over the last D16_RING_SIZE emissions (wraps by emission index).
    d16_ring_step_mod   ::Vector{UInt8}    # (raw_step % 256) at each emission slot
    d16_ring_partition  ::Vector{UInt16}   # i0 (anchor FB column) at each emission slot
    d16_ring_bkt        ::Vector{UInt16}   # coarse key bucket at each emission slot
    d16_emission_count  ::Int              # total emissions seen (for ring index)
    d16_preburst_hist   ::Dict{UInt32, Int}  # key=(step_mod<<16)|partition_id; pre-burst counts
    d16_baseline_hist   ::Dict{UInt32, Int}  # same key schema; uniformly sampled baseline counts
    d16_n_preburst      ::Int              # total pre-burst samples recorded (for cap check)
    d16_n_baseline      ::Int              # total baseline samples recorded

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
        Int[], Int[], UInt128[],   # d12 store
        Int[], Int[], UInt128[],   # d12 close
        Int[],                     # d14 store_a
        # D16
        zeros(UInt8,  D16_RING_SIZE),
        zeros(UInt16, D16_RING_SIZE),
        zeros(UInt16, D16_RING_SIZE),
        0,
        Dict{UInt32,Int}(),
        Dict{UInt32,Int}(),
        0,
        0,
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
        let n_rem = D7_MAX_CLOSURES - length(merged.is_first_closure)
            n_rem > 0 && append!(merged.is_first_closure, s.is_first_closure[1:min(n_rem, length(s.is_first_closure))])
        end
        merged.n_emissions += s.n_emissions
        # D8: merge parallel depth/bucket vectors; shadow table is not merged
        # (per-thread keys are disjoint in expectation; any residual open entries
        # are simply unclosed and would distort the depth distribution).
        let n_rem = D8_MAX_DEPTHS - length(merged.d8_depths)
            if n_rem > 0
                n_take = min(n_rem, length(s.d8_depths))
                append!(merged.d8_depths,     s.d8_depths[1:n_take])
                append!(merged.d8_close_bkt,  s.d8_close_bkt[1:n_take])
                append!(merged.d8_close_abkt, s.d8_close_abkt[1:n_take])
            end
        end
        # D9: merge opcode log (cap to DEEP_DIAG_MAX_OPCODE_LOG total)
        n_remaining = DEEP_DIAG_MAX_OPCODE_LOG - length(merged.opcode_log)
        if n_remaining > 0
            n_take = min(n_remaining, length(s.opcode_log))
            append!(merged.opcode_log,     s.opcode_log[1:n_take])
            append!(merged.opcode_is_lp1c, s.opcode_is_lp1c[1:n_take])
        end
        # D12: merge store/close event logs (cap each to D12_MAX_EVENTS total)
        for (dst_al, dst_px, dst_key, src_al, src_px, src_key) in (
                (merged.d12_store_alpha, merged.d12_store_px, merged.d12_store_key,
                 s.d12_store_alpha,      s.d12_store_px,      s.d12_store_key),
                (merged.d12_close_alpha, merged.d12_close_px, merged.d12_close_key,
                 s.d12_close_alpha,      s.d12_close_px,      s.d12_close_key))
            n_rem = D12_MAX_EVENTS - length(dst_al)
            n_rem > 0 || continue
            n_take = min(n_rem, length(src_al))
            append!(dst_al,  src_al[1:n_take])
            append!(dst_px,  src_px[1:n_take])
            append!(dst_key, src_key[1:n_take])
        end
        # D14: merge store_a (same cap as d12 store; must track same number of events)
        let n_rem = D12_MAX_EVENTS - length(merged.d14_store_a)
            if n_rem > 0
                n_take = min(n_rem, length(s.d14_store_a))
                append!(merged.d14_store_a, s.d14_store_a[1:n_take])
            end
        end
        # D16: merge histograms; ring buffer is per-thread ephemeral (don't merge)
        for (k, v) in s.d16_preburst_hist
            merged.d16_preburst_hist[k] = get(merged.d16_preburst_hist, k, 0) + v
        end
        for (k, v) in s.d16_baseline_hist
            merged.d16_baseline_hist[k] = get(merged.d16_baseline_hist, k, 0) + v
        end
        merged.d16_n_preburst += s.d16_n_preburst
        merged.d16_n_baseline += s.d16_n_baseline
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
@inline function record_conj_deep_miss!(stat     ::ConjDeepStat,
                                         lp_key   ::UInt128,
                                         raw_step ::Int,
                                         alpha_cur::Int = -1,
                                         px       ::Int = -1,
                                         a_val    ::Int = -1)
    # ADDED CAP HERE
    if !haskey(stat.d8_shadow, lp_key) && length(stat.d8_shadow) < D8_MAX_SHADOW
        stat.d8_shadow[lp_key] = raw_step
    end
    # D12: record (alpha, px) at store time, capped.
    if alpha_cur >= 0 && length(stat.d12_store_alpha) < D12_MAX_EVENTS
        push!(stat.d12_store_alpha, alpha_cur)
        push!(stat.d12_store_px,    px)
        push!(stat.d12_store_key,   lp_key)
        # D14: record raw φ-coefficient a at the same event (sentinel -1 if unavailable).
        push!(stat.d14_store_a, a_val)
    end
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
@inline function record_conj_deep_step!(stat     ::ConjDeepStat,
                                         lp_key   ::UInt128,
                                         a_bucket ::Int,
                                         raw_step ::Int,
                                         is_first ::Bool,
                                         alpha_cur::Int = -1,
                                         px       ::Int = -1)
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
    length(stat.is_first_closure) < D7_MAX_CLOSURES && push!(stat.is_first_closure, is_first)

    # D8 closure depth: consume shadow table entry if present.
    store_step = get(stat.d8_shadow, lp_key, -1)
    if store_step >= 0
        delete!(stat.d8_shadow, lp_key)
        depth = raw_step - store_step
        if depth >= 0 && length(stat.d8_depths) < D8_MAX_DEPTHS
            push!(stat.d8_depths,     depth)
            push!(stat.d8_close_bkt,  UInt16(bkt))
            push!(stat.d8_close_abkt, UInt16(clamp(a_bucket, 0, 65535)))
        end
    end

    # D12: record (alpha, px) at close time, capped.
    if alpha_cur >= 0 && length(stat.d12_close_alpha) < D12_MAX_EVENTS
        push!(stat.d12_close_alpha, alpha_cur)
        push!(stat.d12_close_px,    px)
        push!(stat.d12_close_key,   lp_key)
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
# ---------------------------------------------------------------------------
#  record_d16_emission! — D16 pre-burst state fingerprinting.
#
#  Call on EVERY LP1-conj emission (close event), passing:
#    stat         — per-thread ConjDeepStat
#    lp_key       — CanonicalLP1Key (UInt128) of the emitted key
#    raw_step     — s.raw_steps at time of emission
#    partition_id — i0, the anchor FB column index (used as "partition" label)
#
#  Hot path cost: one ring slot write + a loop over D16_LAG_HI - D16_LAG_LO + 1
#  slots + two Dict updates (gated by 1/64).  No group-element arithmetic.
# ---------------------------------------------------------------------------
@inline function record_d16_emission!(stat        ::ConjDeepStat,
                                       lp_key      ::UInt128,
                                       raw_step    ::Int,
                                       partition_id::Int)
    ec   = stat.d16_emission_count
    ring = ec % D16_RING_SIZE + 1       # 1-based current slot (Julia)

    # Compute coarse bucket for this emission (same hash as elsewhere in deep diag)
    h64  = UInt64(lp_key & 0xffffffffffffffff) * UInt64(0x9e3779b97f4a7c15) ⊻
           UInt64(lp_key >> 64)              * UInt64(0x6c62272e07bb0142)
    h64  ⊻= h64 >> 32; h64 *= UInt64(0x45d9f3b37197344d); h64 ⊻= h64 >> 32
    cur_bkt = UInt16(h64 >> (64 - DEEP_DIAG_BUCKET_BITS))

    step_mod_cur  = UInt8(raw_step & 0xff)
    part_cur      = UInt16(clamp(partition_id, 0, 65535))

    # ── Baseline sampling: 1/D16_GATE_DENOM chance, uncapped on baseline ──
    if (rand(UInt8) & UInt8(D16_GATE_DENOM - 1)) == UInt8(0)
        bkey = UInt32(step_mod_cur) << 16 | UInt32(part_cur)
        stat.d16_baseline_hist[bkey] = get(stat.d16_baseline_hist, bkey, 0) + 1
        stat.d16_n_baseline += 1
    end

    # ── Pre-burst detection: scan ring for lag-Δ matches in [LAG_LO, LAG_HI] ─
    if ec >= D16_LAG_LO && stat.d16_n_preburst < D16_MAX_SAMPLES
        # Only fire with 1/D16_GATE_DENOM gate to cap samples
        if (rand(UInt8) & UInt8(D16_GATE_DENOM - 1)) == UInt8(0)
            @inbounds for lag in D16_LAG_LO:D16_LAG_HI
                past_slot = ((ec - lag) % D16_RING_SIZE) + 1   # 1-based
                if stat.d16_ring_bkt[past_slot] == cur_bkt
                    # Found a repeat at this lag — record fingerprint of the past state
                    sm_past   = stat.d16_ring_step_mod[past_slot]
                    part_past = stat.d16_ring_partition[past_slot]
                    bkey      = UInt32(sm_past) << 16 | UInt32(part_past)
                    stat.d16_preburst_hist[bkey] = get(stat.d16_preburst_hist, bkey, 0) + 1
                    stat.d16_n_preburst += 1
                    stat.d16_n_preburst >= D16_MAX_SAMPLES && break
                end
            end
        end
    end

    # ── Write current emission into ring ───────────────────────────────────
    @inbounds begin
        stat.d16_ring_step_mod[ring]  = step_mod_cur
        stat.d16_ring_partition[ring] = part_cur
        stat.d16_ring_bkt[ring]       = cur_bkt
    end
    stat.d16_emission_count = ec + 1
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
                                 conj_snap::Union{Dict, AbstractVector, Nothing} = nothing,
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
            snap_sz = conj_snap isa AbstractVector ?
                      sum(conj_total_entries(lsm) for lsm in conj_snap; init=0) :
                      length(conj_snap)
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

    # ──────────────────────────────────────────────────────────────────────
    #  D12 — Alpha/anchor joint support diagnostic
    #
    #  Tests the hypothesis that the x-support of {alpha·G : alpha ∈ Z_ell}
    #  is small, so LP1-conj closures cluster in (alpha, P0.x) space.
    #  Also checks whether the anchor x-coordinate itself has memory from store
    #  to close via a matched-key mutual-information test.
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D12 — Alpha/anchor joint support diagnostic\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store = length(deep_stat.d12_store_alpha)
        n_close = length(deep_stat.d12_close_alpha)
        @printf("    D12 store events recorded      : %d\n", n_store)
        @printf("    D12 close events recorded      : %d\n", n_close)

        if n_store < 4
            @printf("    (too few store events for D12 — skipping)\n")
            @goto d12_done
        end

        # Number of buckets for each axis.  Use isqrt(n_store) but cap for display.
        n_abkt = clamp(isqrt(max(1, n_store)), 8, 64)   # alpha buckets
        n_pbkt = clamp(isqrt(max(1, n_store)), 8, 64)   # px buckets

        # To bucket alpha and px we need their ranges.
        # alpha is in [0, ell-1]; px is in [0, p-1].
        # We don't have ell/p here, so infer from the data: use max+1 as the range.
        # This is correct since alpha_cur is always < ell and px < p.
        alpha_max = max(1, maximum(deep_stat.d12_store_alpha; init=1))
        px_max    = max(1, maximum(deep_stat.d12_store_px;    init=1))
        # Also include close events in the range so buckets are consistent.
        if n_close > 0
            alpha_max = max(alpha_max, maximum(deep_stat.d12_close_alpha; init=1))
            px_max    = max(px_max,    maximum(deep_stat.d12_close_px;    init=1))
        end

        function _abkt(a::Int)::Int
            clamp(1 + (a * n_abkt) ÷ (alpha_max + 1), 1, n_abkt)
        end
        function _pbkt(px_val::Int)::Int
            clamp(1 + (px_val * n_pbkt) ÷ (px_max + 1), 1, n_pbkt)
        end

        # ── 2-D histogram of store events ─────────────────────────────────
        hist2d_store = zeros(Int, n_abkt, n_pbkt)
        @inbounds for i in 1:n_store
            ab = _abkt(deep_stat.d12_store_alpha[i])
            pb = _pbkt(deep_stat.d12_store_px[i])
            hist2d_store[ab, pb] += 1
        end
        # χ²/dof vs uniform: expected = n_store / (n_abkt*n_pbkt)
        n_cells  = n_abkt * n_pbkt
        expected = Float64(n_store) / n_cells
        chi2_store = expected > 0 ?
            sum((Float64(hist2d_store[i,j]) - expected)^2 / expected
                for i in 1:n_abkt, j in 1:n_pbkt) : NaN
        dof_store = n_cells - 1

        @printf("    2-D histogram (alpha_bkt × px_bkt) of STORE events:\n")
        @printf("      grid: %d × %d  (α_range=[0,%d], px_range=[0,%d])\n",
                n_abkt, n_pbkt, alpha_max, px_max)
        @printf("      χ²/dof (vs uniform): %.3f  (dof=%d; uniform expected ≈ %.1f)\n",
                chi2_store / dof_store, dof_store, Float64(dof_store))
        if chi2_store / dof_store > 2.0
            @printf("      ↑ χ²/dof >> 1: CONCENTRATED — (alpha,px) space is not flat\n")
        elseif chi2_store / dof_store > 1.3
            @printf("      ↑ χ²/dof moderately elevated: mild concentration\n")
        else
            @printf("      (≈ uniform: no strong 2-D concentration detected)\n")
        end

        # Top-5 hottest cells.
        all_cells = vec([(hist2d_store[i,j], i, j) for i in 1:n_abkt, j in 1:n_pbkt])
        sort!(all_cells, rev=true)
        @printf("      Top-5 hottest (alpha_bkt, px_bkt, count):\n")
        for (cnt, ab, pb) in all_cells[1:min(5, end)]
            a_lo = (ab-1) * (alpha_max+1) ÷ n_abkt
            a_hi = ab     * (alpha_max+1) ÷ n_abkt - 1
            p_lo = (pb-1) * (px_max+1)    ÷ n_pbkt
            p_hi = pb     * (px_max+1)    ÷ n_pbkt - 1
            @printf("        α∈[%d,%d)  px∈[%d,%d)  count=%d  (expected=%.1f  lift=%.2f)\n",
                    a_lo, a_hi, p_lo, p_hi, cnt, expected, expected > 0 ? cnt/expected : 0.0)
        end

        # ── Mutual information I(alpha_bucket; px_bucket) for stores ──────
        # I(A;B) = Σ p(a,b) log2(p(a,b)/(p(a)p(b)))
        marginal_a = [sum(hist2d_store[i, j] for j in 1:n_pbkt) for i in 1:n_abkt]
        marginal_p = [sum(hist2d_store[i, j] for i in 1:n_abkt) for j in 1:n_pbkt]
        MI = 0.0
        if n_store > 0
            for i in 1:n_abkt, j in 1:n_pbkt
                c = hist2d_store[i, j]
                c == 0 && continue
                pij = Float64(c) / n_store
                pi  = Float64(marginal_a[i]) / n_store
                pj  = Float64(marginal_p[j]) / n_store
                pi > 0 && pj > 0 && (MI += pij * log2(pij / (pi * pj)))
            end
        end
        H_a = -sum(x/n_store * log2(max(x/n_store, 1e-300)) for x in marginal_a if x > 0)
        H_p = -sum(x/n_store * log2(max(x/n_store, 1e-300)) for x in marginal_p if x > 0)
        norm_MI = (min(H_a, H_p) > 0) ? MI / min(H_a, H_p) : 0.0
        @printf("    Mutual information I(alpha_bkt; px_bkt) for stores:\n")
        @printf("      I = %.4f bits  H(alpha)=%.4f  H(px)=%.4f  NMI=%.4f\n",
                MI, H_a, H_p, norm_MI)
        if norm_MI > 0.1
            @printf("      ↑ NMI > 0.1: ALPHA AND ANCHOR ARE CORRELATED — alpha·G x-support is structured\n")
        elseif norm_MI > 0.02
            @printf("      ↑ NMI mildly elevated: weak alpha/anchor correlation\n")
        else
            @printf("      (≈ independent: alpha and anchor px are not correlated at store time)\n")
        end

        # ── Paired MI on matched store→close keys: does anchor-x memory survive? ──
        # Here we pair the first store and first close event for each key and test
        # whether the anchor x-coordinate at store predicts the anchor x-coordinate
        # at close.  This is the cleanest version of the "px vs anchor-x" question
        # because it removes the alpha coupling and looks directly at x-memory.
        if n_store >= 4 && n_close >= 4
            @printf("    Paired mutual information I(px_store_bkt; px_close_bkt) on matched keys:\n")

            store_key_to_px = Dict{UInt128, Int}()
            @inbounds for i in 1:n_store
                haskey(store_key_to_px, deep_stat.d12_store_key[i]) ||
                    (store_key_to_px[deep_stat.d12_store_key[i]] = deep_stat.d12_store_px[i])
            end
            close_key_to_px = Dict{UInt128, Int}()
            @inbounds for i in 1:n_close
                haskey(close_key_to_px, deep_stat.d12_close_key[i]) ||
                    (close_key_to_px[deep_stat.d12_close_key[i]] = deep_stat.d12_close_px[i])
            end

            paired_px_store = Int[]
            paired_px_close = Int[]
            @inbounds for (k, p_store) in store_key_to_px
                p_close = get(close_key_to_px, k, -1)
                p_close < 0 && continue
                push!(paired_px_store, p_store)
                push!(paired_px_close, p_close)
            end

            n_pair_px = length(paired_px_store)
            @printf("      paired keys                 : %d\n", n_pair_px)
            if n_pair_px >= 4
                px_store_max = max(1, maximum(paired_px_store; init=1))
                px_close_max = max(1, maximum(paired_px_close; init=1))
                px_pair_max  = max(px_store_max, px_close_max)
                n_pxb        = clamp(isqrt(max(1, n_pair_px)), 8, 64)

                function _ppb(px_val::Int)::Int
                    clamp(1 + (px_val * n_pxb) ÷ (px_pair_max + 1), 1, n_pxb)
                end

                hist2d_px = zeros(Int, n_pxb, n_pxb)
                @inbounds for i in 1:n_pair_px
                    hist2d_px[_ppb(paired_px_store[i]), _ppb(paired_px_close[i])] += 1
                end

                px_marg_s = [sum(hist2d_px[i, j] for j in 1:n_pxb) for i in 1:n_pxb]
                px_marg_c = [sum(hist2d_px[i, j] for i in 1:n_pxb) for j in 1:n_pxb]
                mi_px = 0.0
                @inbounds for i in 1:n_pxb, j in 1:n_pxb
                    c = hist2d_px[i, j]
                    c == 0 && continue
                    pij = Float64(c) / n_pair_px
                    pi  = Float64(px_marg_s[i]) / n_pair_px
                    pj  = Float64(px_marg_c[j]) / n_pair_px
                    pi > 0 && pj > 0 && (mi_px += pij * log2(pij / (pi * pj)))
                end
                h_s = -sum(x/n_pair_px * log2(max(x/n_pair_px, 1e-300)) for x in px_marg_s if x > 0)
                h_c = -sum(x/n_pair_px * log2(max(x/n_pair_px, 1e-300)) for x in px_marg_c if x > 0)
                nmi_px = (min(h_s, h_c) > 0) ? mi_px / min(h_s, h_c) : 0.0

                # Deterministic phase-shift baseline: pair the store list with a
                # cyclically shifted version of the close list to break key-wise
                # alignment while preserving marginals.
                shift = max(1, n_pair_px ÷ 3)
                hist2d_shift = zeros(Int, n_pxb, n_pxb)
                @inbounds for i in 1:n_pair_px
                    j = 1 + mod(i - 1 + shift, n_pair_px)
                    hist2d_shift[_ppb(paired_px_store[i]), _ppb(paired_px_close[j])] += 1
                end
                px_marg_s2 = [sum(hist2d_shift[i, j] for j in 1:n_pxb) for i in 1:n_pxb]
                px_marg_c2 = [sum(hist2d_shift[i, j] for i in 1:n_pxb) for j in 1:n_pxb]
                mi_shift = 0.0
                @inbounds for i in 1:n_pxb, j in 1:n_pxb
                    c = hist2d_shift[i, j]
                    c == 0 && continue
                    pij = Float64(c) / n_pair_px
                    pi  = Float64(px_marg_s2[i]) / n_pair_px
                    pj  = Float64(px_marg_c2[j]) / n_pair_px
                    pi > 0 && pj > 0 && (mi_shift += pij * log2(pij / (pi * pj)))
                end
                excess_mi = mi_px - mi_shift

                @printf("      I = %.4f bits  H(store_px)=%.4f  H(close_px)=%.4f  NMI=%.4f\n",
                        mi_px, h_s, h_c, nmi_px)
                @printf("      shift-baseline I = %.4f bits  excess = %.4f bits\n",
                        mi_shift, excess_mi)
                if excess_mi > 0.05
                    @printf("      ↑ excess MI > 0.05 bits: anchor x carries real memory across store→close\n")
                elseif excess_mi > 0.01
                    @printf("      ↑ weak but visible x-memory across store→close\n")
                else
                    @printf("      (≈ no detectable x-memory beyond finite-sample bias)\n")
                end
            else
                @printf("      (too few matched store→close keys for px MI)\n")
            end
        end

        # ── Same analysis for close events ────────────────────────────────
        if n_close >= 4
            hist2d_close = zeros(Int, n_abkt, n_pbkt)
            @inbounds for i in 1:n_close
                ab = _abkt(deep_stat.d12_close_alpha[i])
                pb = _pbkt(deep_stat.d12_close_px[i])
                hist2d_close[ab, pb] += 1
            end
            expected_c = Float64(n_close) / n_cells
            chi2_close = expected_c > 0 ?
                sum((Float64(hist2d_close[i,j]) - expected_c)^2 / expected_c
                    for i in 1:n_abkt, j in 1:n_pbkt) : NaN
            @printf("    2-D histogram χ²/dof for CLOSE events: %.3f  (uniform expected ≈ %.1f)\n",
                    chi2_close / dof_store, Float64(dof_store))
            if chi2_close / dof_store > 2.0
                @printf("      ↑ CONCENTRATED at close time too — not just a store-side bias\n")
            end
        end

        # ── Paired delta-alpha distribution ───────────────────────────────
        # For each lp_key that appears in both store and close logs, compute
        # |alpha_close - alpha_store| mod (alpha_max+1).  If the x-support of
        # alpha·G is small, the effective alpha period is short, and delta-alpha
        # will cluster near 0 (and near that period).
        if n_store >= 4 && n_close >= 4
            @printf("    Paired delta-alpha distribution:\n")
            store_key_to_alpha = Dict{UInt128, Int}()
            @inbounds for i in 1:n_store
                # Keep the first store for each key (matches D8 shadow table logic).
                haskey(store_key_to_alpha, deep_stat.d12_store_key[i]) ||
                    (store_key_to_alpha[deep_stat.d12_store_key[i]] = deep_stat.d12_store_alpha[i])
            end
            delta_alphas = Int[]
            @inbounds for i in 1:n_close
                k = deep_stat.d12_close_key[i]
                s_alpha = get(store_key_to_alpha, k, -1)
                s_alpha < 0 && continue
                c_alpha = deep_stat.d12_close_alpha[i]
                # delta mod (alpha_max+1): take the smaller of forward/backward distance.
                raw_d = mod(c_alpha - s_alpha, alpha_max + 1)
                delta = min(raw_d, alpha_max + 1 - raw_d)
                push!(delta_alphas, delta)
            end
            n_paired = length(delta_alphas)
            @printf("      paired (store→close) events     : %d\n", n_paired)
            if n_paired >= 2
                mu_d    = sum(delta_alphas) / n_paired
                med_d   = sort(delta_alphas)[n_paired ÷ 2 + 1]
                frac_lo = count(d -> d < (alpha_max+1) ÷ 16, delta_alphas) / n_paired
                @printf("      delta-alpha: mean=%.1f  median=%d  frac<ell/16=%.3f\n",
                        mu_d, med_d, frac_lo)
                if frac_lo > 0.5
                    @printf("      ↑ >50%% of closes within ell/16 of store alpha: SMALL EFFECTIVE SUPPORT\n")
                    @printf("        → confirms hypothesis: alpha·G x-support is algebraically bounded\n")
                elseif frac_lo > 0.2
                    @printf("      ↑ >20%% within ell/16: mild alpha concentration at closure\n")
                else
                    @printf("      (delta-alpha spread broadly — alpha support appears large)\n")
                end
                # Histogram in 8 bins.
                bin_w  = max(1, (alpha_max ÷ 2) ÷ 8)
                bins   = zeros(Int, 9)
                for d in delta_alphas
                    b = clamp(1 + d ÷ bin_w, 1, 9)
                    bins[b] += 1
                end
                @printf("      delta-alpha histogram (bin_width≈%d, range [0,ell/2]):\n", bin_w)
                @printf("        %8s  %8s  %8s\n", "bin_lo", "count", "frac%")
                for b in 1:9
                    lo = (b-1)*bin_w
                    @printf("        %8d  %8d  %7.2f%%\n",
                            lo, bins[b], 100.0*bins[b]/max(1,n_paired))
                end
            else
                @printf("      (too few paired events: %d)\n", n_paired)
            end
        end

        # ── Per-px_bucket alpha entropy H(alpha | px=b) ───────────────────
        # Low entropy for some b means that anchor px=b strongly constrains
        # which alpha values appear — i.e., alpha·G's residual is non-split
        # only for a narrow set of alpha when the anchor is in that region.
        @printf("    Per-px_bucket alpha entropy H(alpha_bkt | px_bkt) for stores:\n")
        if n_store >= 4
            # For each px bucket, build alpha-bucket histogram and compute entropy.
            px_alpha_hist = [zeros(Int, n_abkt) for _ in 1:n_pbkt]
            @inbounds for i in 1:n_store
                ab = _abkt(deep_stat.d12_store_alpha[i])
                pb = _pbkt(deep_stat.d12_store_px[i])
                px_alpha_hist[pb][ab] += 1
            end
            H_alpha_given_px = Float64[]
            px_nonempty = Int[]
            for pb in 1:n_pbkt
                h = px_alpha_hist[pb]
                tot = sum(h)
                tot < 4 && continue
                ent = -sum(c/tot * log2(max(c/tot, 1e-300)) for c in h if c > 0)
                push!(H_alpha_given_px, ent)
                push!(px_nonempty, pb)
            end
            if !isempty(H_alpha_given_px)
                H_max   = log2(Float64(n_abkt))
                H_mean  = sum(H_alpha_given_px) / length(H_alpha_given_px)
                H_min_v, H_min_i = findmin(H_alpha_given_px)
                H_max_v, H_max_i = findmax(H_alpha_given_px)
                @printf("      H_max (uniform over %d alpha_bkts): %.4f bits\n", n_abkt, H_max)
                @printf("      mean H(alpha|px)                  : %.4f bits (%.1f%% of max)\n",
                        H_mean, 100.0*H_mean/max(1e-10, H_max))
                @printf("      min  H(alpha|px=b)                : %.4f bits  px_bkt=%d  ← most constrained\n",
                        H_min_v, px_nonempty[H_min_i] - 1)
                @printf("      max  H(alpha|px=b)                : %.4f bits  px_bkt=%d\n",
                        H_max_v, px_nonempty[H_max_i] - 1)
                if H_mean / H_max < 0.7
                    @printf("      ↑ mean H < 0.7×H_max: ANCHOR STRONGLY CONSTRAINS ALPHA\n")
                    @printf("        → non-split residuals occur only for narrow alpha ranges at each anchor\n")
                elseif H_mean / H_max < 0.9
                    @printf("      ↑ mild constraint: alpha somewhat restricted per anchor\n")
                else
                    @printf("      (alpha nearly uniform across anchors — no strong constraint)\n")
                end
                # List the 5 most-constrained px buckets.
                order = sortperm(H_alpha_given_px)
                @printf("      5 most-constrained px_buckets:\n")
                @printf("        %6s  %8s  %8s\n", "px_bkt", "H(bits)", "H/H_max")
                for idx in order[1:min(5, end)]
                    pb = px_nonempty[idx]
                    p_lo = (pb-1) * (px_max+1) ÷ n_pbkt
                    p_hi = pb     * (px_max+1) ÷ n_pbkt - 1
                    @printf("        px∈[%5d,%5d)  H=%.4f  H/H_max=%.4f\n",
                            p_lo, p_hi, H_alpha_given_px[idx], H_alpha_given_px[idx]/H_max)
                end
            else
                @printf("      (no px bucket had ≥4 store events)\n")
            end
        end

        @label d12_done
    end   # let D12

    # ──────────────────────────────────────────────────────────────────────
    #  D13 — Mumford coordinate support cardinality
    #
    #  Central question: if we write |S| for the number of distinct values
    #  taken by a coordinate (or tuple of coordinates) across all α·a
    #  encounters (store events), what is  κ = log_p(|S|)?
    #
    #  A naive bound gives κ = 1 for each coordinate (anything in F_p).
    #  If the walk's non-split residuals are algebraically constrained, the
    #  actual support is p^κ for κ < 1, and the collision probability —
    #  hence the effective LP1-conj table pressure — scales as p^(κ-1)
    #  rather than p^0.  That is the complexity reduction argument.
    #
    #  We measure:
    #    • |{u0}|, |{u1}|, |{v0}|, |{v1}|  (marginal supports)
    #    • |{(u0,u1)}|  (u-polynomial support — the LP key's first half)
    #    • |{(v0,v1)}|  (v-polynomial support)
    #    • |{(u0,u1,v0,v1)}|  (full Mumford support = distinct LP keys)
    #  All expressed as κ = log(|S|) / log(p).
    #
    #  We also report the multiplicity distribution of repeated keys
    #  (Zipf mass in the top 1%/10% of distinct keys) and the p-adic
    #  valuation distribution of each coordinate, as additional evidence
    #  that the support lives on a low-dimensional algebraic subvariety.
    #
    #  Source: d12_store_key (UInt128, packed as u0|u1<<32|v0<<64|v1<<96,
    #  each coordinate already reduced mod p by canonical_lp1_conj_key).
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D13 — Mumford coordinate support cardinality\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store = length(deep_stat.d12_store_key)
        @printf("    store events available : %d\n", n_store)

        if n_store < 4
            @printf("    (too few store events — skipping D13)\n")
        elseif p <= 1
            @printf("    (p not provided or ≤1 — cannot compute log_p; pass p= to print_conj_deep_report)\n")
        else
            log_p = log(Float64(p))

            # ── Unpack all keys ─────────────────────────────────────────
            # Each UInt128 key = u0 | u1<<32 | v0<<64 | v1<<96,
            # coords already mod p, stored as UInt32 limbs.
            mask32 = UInt128(0xffffffff)
            u0s = Vector{UInt32}(undef, n_store)
            u1s = Vector{UInt32}(undef, n_store)
            v0s = Vector{UInt32}(undef, n_store)
            v1s = Vector{UInt32}(undef, n_store)
            @inbounds for i in 1:n_store
                k = deep_stat.d12_store_key[i]
                u0s[i] = UInt32(k         & mask32)
                u1s[i] = UInt32((k >> 32) & mask32)
                v0s[i] = UInt32((k >> 64) & mask32)
                v1s[i] = UInt32((k >> 96) & mask32)
            end

            # ── Marginal and joint support sizes ────────────────────────
            n_u0   = length(Set(u0s))
            n_u1   = length(Set(u1s))
            n_v0   = length(Set(v0s))
            n_v1   = length(Set(v1s))

            # u-poly pairs (u0,u1)
            upairs = Set{UInt64}()
            sizehint!(upairs, n_store)
            @inbounds for i in 1:n_store
                push!(upairs, UInt64(u0s[i]) | (UInt64(u1s[i]) << 32))
            end
            n_upair = length(upairs)

            # v-poly pairs (v0,v1)
            vpairs = Set{UInt64}()
            sizehint!(vpairs, n_store)
            @inbounds for i in 1:n_store
                push!(vpairs, UInt64(v0s[i]) | (UInt64(v1s[i]) << 32))
            end
            n_vpair = length(vpairs)

            # Full 4-tuple distinct keys
            n_full = length(Set(deep_stat.d12_store_key))

            function kappa(n::Int)::Float64
                n <= 1 ? 0.0 : log(Float64(n)) / log_p
            end

            @printf("    p = %d\n", p)
            @printf("\n    Support cardinalities and exponents κ = log_p(|S|):\n")
            @printf("      %-20s  %10s  %8s  %s\n", "set", "|S|", "κ", "interpretation")
            @printf("      %-20s  %10s  %8s  %s\n", "────────────────────",
                    "──────────", "────────", "──────────────────────────────────────")

            rows = [
                ("u0  (marginal)",    n_u0,   "u-poly const term"),
                ("u1  (marginal)",    n_u1,   "u-poly linear coeff"),
                ("v0  (marginal)",    n_v0,   "v-poly const term"),
                ("v1  (marginal)",    n_v1,   "v-poly linear coeff"),
                ("(u0,u1) pairs",     n_upair,"u-polynomial support"),
                ("(v0,v1) pairs",     n_vpair,"v-polynomial support"),
                ("full (u0,u1,v0,v1)",n_full,"distinct LP keys seen"),
            ]
            for (label, n, interp) in rows
                @printf("      %-22s  %10d  %8.4f  %s\n", label, n, kappa(n), interp)
            end

            # ── Comparison to naive and birthday bounds ──────────────────
            kappa_full = kappa(n_full)
            @printf("\n    Complexity exponent summary:\n")
            @printf("      Naive LP1-conj table pressure  : p^1.00  (all of F_p × F_p × …)\n")
            @printf("      Observed LP-key support        : p^%.4f  (%d distinct keys from %d stores)\n",
                    kappa_full, n_full, n_store)
            @printf("      Observed u-poly support        : p^%.4f  (%d distinct u-polys)\n",
                    kappa(n_upair), n_upair)
            reduction = 1.0 - kappa_full
            if reduction > 0.3
                @printf("      ↑ STRONG reduction: effective LP key space is p^%.4f below naive\n",
                        reduction)
                @printf("        → collision probability scales as p^%.4f, not p^0\n",
                        kappa_full - 1.0)
                @printf("        → LP1-conj table saturates at ~p^%.4f entries, not p\n",
                        kappa_full)
            elseif reduction > 0.1
                @printf("      ↑ moderate reduction (%.2f exponent below naive)\n", reduction)
            else
                @printf("      (support close to naive — no strong algebraic confinement detected)\n")
            end

            # ── Saturation check ─────────────────────────────────────────
            # If n_store >> n_full, most stores are re-hits of existing keys.
            if n_store >= 2 && n_full >= 1
                mean_hits = Float64(n_store) / n_full
                @printf("\n    Key multiplicity (re-hit rate):\n")
                @printf("      mean hits per distinct key : %.2f\n", mean_hits)
                @printf("      distinct / total stores    : %.4f  (1.0 = no repeats)\n",
                        Float64(n_full) / n_store)

                # Build per-key hit counts for Zipf/Gini analysis.
                key_counts = Dict{UInt128, Int}()
                sizehint!(key_counts, n_full)
                @inbounds for k in deep_stat.d12_store_key
                    key_counts[k] = get(key_counts, k, 0) + 1
                end
                counts_sorted = sort(collect(values(key_counts)), rev=true)
                n_distinct = length(counts_sorted)
                total_hits  = sum(counts_sorted)

                # Top-1% and top-10% mass fraction.
                k1pct  = max(1, n_distinct ÷ 100)
                k10pct = max(1, n_distinct ÷ 10)
                mass1  = sum(counts_sorted[1:k1pct])  / total_hits
                mass10 = sum(counts_sorted[1:k10pct]) / total_hits
                @printf("      top  1%% of keys hold %.1f%% of stores\n", 100.0*mass1)
                @printf("      top 10%% of keys hold %.1f%% of stores\n", 100.0*mass10)

                # Gini coefficient.
                n_d = length(counts_sorted)
                gini = 0.0
                if n_d > 1
                    cs = cumsum(sort(counts_sorted))
                    gini = 1.0 - 2.0 * sum(cs) / (Float64(n_d) * total_hits) + 1.0/n_d
                end
                @printf("      Gini coefficient           : %.4f  (0=uniform, 1=monopoly)\n", gini)
                if gini > 0.7
                    @printf("      ↑ HIGH Gini: a tiny set of LP keys dominates stores\n")
                    @printf("        → effective support is smaller than |S| suggests\n")
                elseif gini > 0.4
                    @printf("      ↑ moderate Gini: noticeable concentration in key hits\n")
                end
            end

                # ── Recurrence-trimmed support ────────────────────────────
                # For each multiplicity threshold r, restrict to keys with
                # ≥r hits and report: key count, store%, and complexity
                # exponents κ_key, κ_α, κ_(α,px).  All slices guard against
                # empty collections so sum() never reduces over an empty range.
                @printf("\n    Recurrence-trimmed support (tail cut by key multiplicity):\n")
                @printf("      %5s  %10s  %9s  %10s  %10s  %10s\n",
                        "r", "keys≥r", "store%", "κ_key", "κ_α", "κ_(α,px)")
                @printf("      %s\n", "─"^62)

                # Parallel alpha/px slices — may be shorter than n_store if
                # alpha was unavailable for some events (alpha_cur < 0 guard).
                have_alpha = length(deep_stat.d12_store_alpha) == n_store
                have_px    = length(deep_stat.d12_store_px)    == n_store

                # Per-key sets for support cardinality of α and (α,px).
                key_to_alpha    = Dict{UInt128, Set{Int}}()
                key_to_alpha_px = Dict{UInt128, Set{Tuple{Int,Int}}}()
                if have_alpha
                    sizehint!(key_to_alpha,    n_full)
                    sizehint!(key_to_alpha_px, n_full)
                    @inbounds for i in 1:n_store
                        k  = deep_stat.d12_store_key[i]
                        al = deep_stat.d12_store_alpha[i]
                        px = have_px ? deep_stat.d12_store_px[i] : 0
                        push!(get!(key_to_alpha,    k, Set{Int}()),              al)
                        push!(get!(key_to_alpha_px, k, Set{Tuple{Int,Int}}()), (al, px))
                    end
                end

                for r in (1, 2, 3, 5, 10)
                    keys_r = [k for (k, c) in key_counts if c >= r]
                    if isempty(keys_r)
                        @printf("      %5d  %10d  %9s  %10s  %10s  %10s\n",
                                r, 0, "-", "-", "-", "-")
                        continue
                    end
                    n_keys_r  = length(keys_r)
                    n_store_r = sum(key_counts[k] for k in keys_r; init=0)
                    store_pct = 100.0 * n_store_r / max(n_store, 1)
                    κ_key_str = @sprintf("%.4f", log(p, n_keys_r))

                    κ_α_str   = "-"
                    κ_apx_str = "-"
                    if have_alpha && !isempty(key_to_alpha)
                        all_alpha    = Set{Int}()
                        all_alpha_px = Set{Tuple{Int,Int}}()
                        for k in keys_r
                            if haskey(key_to_alpha, k)
                                union!(all_alpha,    key_to_alpha[k])
                                union!(all_alpha_px, key_to_alpha_px[k])
                            end
                        end
                        n_al  = length(all_alpha)
                        n_apx = length(all_alpha_px)
                        κ_α_str   = n_al  > 0 ? @sprintf("%.4f", log(p, n_al))  : "-"
                        κ_apx_str = n_apx > 0 ? @sprintf("%.4f", log(p, n_apx)) : "-"
                    end

                    @printf("      %5d  %10d  %9.2f  %10s  %10s  %10s\n",
                            r, n_keys_r, store_pct, κ_key_str, κ_α_str, κ_apx_str)
                end

            # ── p-adic valuation distributions ───────────────────────────
            # v_p(x) = largest k s.t. p^k | x.  For x=0 we report a
            # sentinel "∞" count separately.  Coords are already mod p
            # so v_p ∈ {0, 1, …, floor(log_p(p-1))} ∪ {∞}.
            # In practice for a prime p in a genus-2 Jacobian, the
            # interesting question is whether a non-trivial fraction of
            # coords are divisible by p (i.e. v_p ≥ 1), which would
            # mean those points live on a subvariety defined over F_p
            # rather than F_{p^2}.
            @printf("\n    p-adic valuation distributions (coords mod p, so v_p ∈ {0,1,…}):\n")
            @printf("      (v_p(x)=0 means x≢0 mod p; v_p(x)≥1 means p|x)\n")

            function vp_hist(xs::Vector{UInt32})
                z = count(iszero, xs)
                nz = length(xs) - z
                # For non-split Mumford coords mod p, v_p=0 dominates unless
                # there is special structure.  We just count 0 vs ≥1 here
                # (higher valuations require knowing p^2, p^3 etc., but coords
                # are already reduced mod p so v_p ≥ 1 iff coord == 0).
                return z, nz
            end

            for (name, xs) in (("u0", u0s), ("u1", u1s), ("v0", v0s), ("v1", v1s))
                z, nz = vp_hist(xs)
                frac0 = Float64(z) / n_store
                @printf("      %s: p∤x (v_p=0): %d (%.1f%%)   p|x (v_p≥1): %d (%.1f%%)\n",
                        name, nz, 100.0*(1-frac0), z, 100.0*frac0)
            end
            n_all_zero = count(1:n_store) do i
                u0s[i] == 0 && u1s[i] == 0 && v0s[i] == 0 && v1s[i] == 0
            end
            @printf("      all-zero (trivial key) events  : %d / %d\n", n_all_zero, n_store)
            if any(>(0.05), [count(iszero,xs)/n_store for xs in (u0s,u1s,v0s,v1s)])
                @printf("      ↑ >5%% zero in some coordinate — possible subvariety confinement\n")
                @printf("        (non-split residuals with p|coord live on a degree-drop locus)\n")
            end
        end
    end   # let D13

    # ──────────────────────────────────────────────────────────────────────
    #  D14 — Conditional entropy H(a | px_bucket)
    #
    #  For each px bucket, builds the distribution of the φ-coefficient `a`
    #  recorded at each store event and computes Shannon entropy.  A drop
    #  below log₂(n_abkts) signals that u(px) division collapses the `a`
    #  distribution — i.e., the anchor constrains which coefficients survive.
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D14 — Conditional entropy H(a | px_bucket)\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store  = length(deep_stat.d12_store_key)
        have_a   = length(deep_stat.d14_store_a)  == n_store
        have_px  = length(deep_stat.d12_store_px) == n_store

        if n_store < 4 || !have_a || !have_px
            @printf("    (insufficient data: n_store=%d have_a=%s have_px=%s — skipping D14)\n",
                    n_store, have_a, have_px)
        elseif p <= 1
            @printf("    (p not provided — skipping D14)\n")
        else
            n_pbkt  = 32
            n_abkts = 64
            px_max  = p - 1
            _pbkt14(px) = clamp(1 + Int(px) * n_pbkt  ÷ max(px_max, 1), 1, n_pbkt)
            _abkt14(av) = av < 0 ? 1 : clamp(1 + av * n_abkts ÷ max(p, 1), 1, n_abkts)

            px_a_hist = [zeros(Int, n_abkts) for _ in 1:n_pbkt]
            n_valid = 0
            @inbounds for i in 1:n_store
                av = deep_stat.d14_store_a[i]
                av < 0 && continue
                pb = _pbkt14(deep_stat.d12_store_px[i])
                ab = _abkt14(av)
                px_a_hist[pb][ab] += 1
                n_valid += 1
            end

            @printf("    store events with valid a   : %d / %d\n", n_valid, n_store)

            if n_valid < 4
                @printf("    (too few valid a events — skipping entropy computation)\n")
            else
                H_max = log2(Float64(n_abkts))
                H_vals      = Float64[]
                px_nonempty = Int[]
                for pb in 1:n_pbkt
                    h = px_a_hist[pb]
                    tot = sum(h)
                    tot < 4 && continue
                    ent = -sum(c/tot * log2(max(c/tot, 1e-300)) for c in h if c > 0)
                    push!(H_vals, ent)
                    push!(px_nonempty, pb)
                end

                if isempty(H_vals)
                    @printf("    (no px bucket had >=4 valid events)\n")
                else
                    H_mean           = sum(H_vals) / length(H_vals)
                    H_min_v, H_min_i = findmin(H_vals)
                    H_max_v, H_max_i = findmax(H_vals)
                    ratio            = H_mean / max(1e-10, H_max)

                    @printf("    H_max (uniform over %d a-buckets) : %.4f bits\n", n_abkts, H_max)
                    @printf("    mean H(a | px)                    : %.4f bits  (%.1f%% of max)\n",
                            H_mean, 100.0 * ratio)
                    @printf("    min  H(a | px=b)                  : %.4f bits  px_bkt=%d  <- most constrained\n",
                            H_min_v, px_nonempty[H_min_i] - 1)
                    @printf("    max  H(a | px=b)                  : %.4f bits  px_bkt=%d\n",
                            H_max_v, px_nonempty[H_max_i] - 1)

                    if ratio < 0.7
                        @printf("    !! mean H < 0.7*H_max: ANCHOR CONSTRAINS phi\n")
                        @printf("       -> division by u(px) introduces bias; certain anchors collapse 'a'\n")
                    elseif ratio < 0.9
                        @printf("    ^ mild phi-restriction (H/H_max = %.3f)\n", ratio)
                    else
                        @printf("    (a nearly uniform across anchors — no direct phi-compression from px; %.3f)\n",
                                ratio)
                    end

                    order = sortperm(H_vals)
                    @printf("    5 most-constrained px_buckets:\n")
                    @printf("      %6s  %8s  %8s\n", "px_bkt", "H(bits)", "H/H_max")
                    for idx in order[1:min(5, lastindex(order))]
                        pb   = px_nonempty[idx]
                        p_lo = (pb-1) * (px_max+1) ÷ n_pbkt
                        p_hi = pb     * (px_max+1) ÷ n_pbkt - 1
                        @printf("      px~[%5d,%5d)  H=%.4f  H/H_max=%.4f\n",
                                p_lo, p_hi, H_vals[idx], H_vals[idx] / H_max)
                    end
                end
            end
        end
    end   # let D14

    # ──────────────────────────────────────────────────────────────────────
    #  D15 — Residual support ratio conditioned on px_bucket
    #
    #  For each px bucket, reports:
    #      support_ratio = #distinct_lp_keys / #samples
    #  Ratio near 1.0 → every sample is a new key (no local collision).
    #  Ratio << 1.0   → certain anchors collapse the residual space.
    #  This is the end-to-end version of D14: D14 tests the transfer function
    #  (does px restrict a?), D15 tests the final output (does px restrict
    #  the key space?).
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D15 — Residual support ratio conditioned on px_bucket\n")
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_store = length(deep_stat.d12_store_key)
        have_px = length(deep_stat.d12_store_px) == n_store

        if n_store < 4 || !have_px
            @printf("    (insufficient data: n_store=%d have_px=%s — skipping D15)\n",
                    n_store, have_px)
        elseif p <= 1
            @printf("    (p not provided — skipping D15)\n")
        else
            n_pbkt  = 32
            px_max  = p - 1
            _pbkt15(px) = clamp(1 + Int(px) * n_pbkt ÷ max(px_max, 1), 1, n_pbkt)

            bkt_total    = zeros(Int, n_pbkt)
            bkt_distinct = [Set{UInt128}() for _ in 1:n_pbkt]
            @inbounds for i in 1:n_store
                pb = _pbkt15(deep_stat.d12_store_px[i])
                bkt_total[pb] += 1
                push!(bkt_distinct[pb], deep_stat.d12_store_key[i])
            end

            @printf("    %-24s  %8s  %8s  %8s  %s\n",
                    "px_bucket", "samples", "distinct", "ratio", "note")
            @printf("    %s\n", "-"^70)

            ratios_nonempty = Float64[]
            min_ratio = 1.0;  min_pb = 0
            max_ratio = 0.0;  max_pb = 0
            for pb in 1:n_pbkt
                tot = bkt_total[pb]
                tot < 4 && continue
                nd  = length(bkt_distinct[pb])
                r   = Float64(nd) / tot
                push!(ratios_nonempty, r)
                p_lo = (pb-1) * (px_max+1) ÷ n_pbkt
                p_hi = pb     * (px_max+1) ÷ n_pbkt - 1
                note = r < 0.5 ? "<- LOCAL COLLAPSE (strong)" :
                       r < 0.8 ? "<- mild collision clustering" :
                                 ""
                @printf("    px~[%5d,%5d)  %8d  %8d  %8.4f  %s\n",
                        p_lo, p_hi, tot, nd, r, note)
                if r < min_ratio; min_ratio = r; min_pb = pb; end
                if r > max_ratio; max_ratio = r; max_pb = pb; end
            end

            if !isempty(ratios_nonempty)
                global_distinct = length(Set(deep_stat.d12_store_key))
                mean_ratio = sum(ratios_nonempty) / length(ratios_nonempty)
                @printf("\n    Summary:\n")
                @printf("      global support ratio (all px) : %.4f  (%d distinct / %d stores)\n",
                        Float64(global_distinct) / n_store, global_distinct, n_store)
                @printf("      mean conditional ratio        : %.4f\n", mean_ratio)
                @printf("      min  conditional ratio        : %.4f  px_bkt=%d  <- most collapsed\n",
                        min_ratio, min_pb - 1)
                @printf("      max  conditional ratio        : %.4f  px_bkt=%d\n",
                        max_ratio, max_pb - 1)

                if min_ratio < 0.5
                    @printf("      !! STRONG local collapse at px_bkt=%d (ratio=%.4f)\n",
                            min_pb - 1, min_ratio)
                    @printf("         -> walks anchored there collide far below birthday bound\n")
                    @printf("         -> steer anchor selection toward this px bucket for faster closure\n")
                elseif min_ratio < 0.8
                    @printf("      ^ mild collapse in some buckets — worth investigating anchor bias\n")
                else
                    @printf("      (no bucket shows significant local collapse)\n")
                end

                @printf("\n    D14 x D15 cross-check:\n")
                @printf("      Pattern A (D14 drops AND D15 drops) -> anchor-dependent compression; walk is steerable\n")
                @printf("      Pattern B (D14 flat, D15 drops)     -> collapse arises in later steps (div/sqrt/splitting)\n")
                @printf("      Pattern C (both flat)               -> structure is temporal/trajectory, not static\n")
            else
                @printf("    (no px bucket had >=4 store events)\n")
            end
        end
    end   # let D15

    # ──────────────────────────────────────────────────────────────────────
    #  D16 — Pre-burst state fingerprinting
    # ──────────────────────────────────────────────────────────────────────
    @printf("\n  D16 — Pre-burst state fingerprinting (lag Δ ∈ [%d, %d])\n",
            D16_LAG_LO, D16_LAG_HI)
    @printf("  ─────────────────────────────────────────────────────────────────\n")
    let
        n_pb = deep_stat.d16_n_preburst
        n_bl = deep_stat.d16_n_baseline
        pb_hist = deep_stat.d16_preburst_hist
        bl_hist = deep_stat.d16_baseline_hist

        @printf("    Pre-burst samples : %d  (gate 1/%d, cap %d)\n",
                n_pb, D16_GATE_DENOM, D16_MAX_SAMPLES)
        @printf("    Baseline samples  : %d\n", n_bl)

        if n_pb < 20 || n_bl < 20
            @printf("    (insufficient samples — collect more emissions)\n")
        else
            # Compute per-bucket ratio = pre_burst_freq / baseline_freq.
            # Normalise each hist by its total so ratios are comparable.
            all_keys = union(keys(pb_hist), keys(bl_hist))

            ratios = Dict{UInt32, Float64}()
            for k in all_keys
                pb_f = get(pb_hist, k, 0) / n_pb
                bl_f = get(bl_hist, k, 0) / n_bl
                bl_f > 0.0 && (ratios[k] = pb_f / bl_f)
            end

            # Sort by ratio descending — top spiking buckets
            sorted_keys = sort(collect(keys(ratios)), by=k -> -ratios[k])

            n_show = min(30, length(sorted_keys))
            @printf("    Top %d (step_mod, partition_id) buckets by pre-burst / baseline ratio:\n", n_show)
            @printf("    %-10s  %-12s  %10s  %10s  %10s  %s\n",
                    "step_mod", "partition_id", "pb_count", "bl_count", "ratio", "note")
            @printf("    %s\n", "-"^75)

            total_pb_top = 0
            n_spike = 0
            for i in 1:n_show
                k       = sorted_keys[i]
                sm      = (k >> 16) & 0xff
                pid     = k & 0xffff
                pb_c    = get(pb_hist, k, 0)
                bl_c    = get(bl_hist, k, 0)
                ratio_v = ratios[k]
                note    = ratio_v >= 5.0 ? "<- STRONG SPIKE" :
                          ratio_v >= 2.5 ? "<- moderate spike" :
                          ratio_v >= 1.5 ? "<- mild elevation" : ""
                @printf("    %-10d  %-12d  %10d  %10d  %10.3f  %s\n",
                        sm, pid, pb_c, bl_c, ratio_v, note)
                total_pb_top += pb_c
                ratio_v >= 2.5 && (n_spike += 1)
            end

            frac_top = Float64(total_pb_top) / max(1, n_pb)
            @printf("\n    Top-%d buckets hold %.1f%% of all pre-burst samples\n",
                    n_show, 100.0 * frac_top)
            @printf("    Buckets with ratio ≥ 2.5× : %d\n", n_spike)

            if n_spike == 0
                @printf("    -> Ratios near 1 everywhere: bursts are NOT from a specific walk regime\n")
                @printf("       (structure is emergent / global, not locally concentrated)\n")
            elseif n_spike <= 5
                @printf("    -> Few hot buckets: burst has a LOCAL cause in (step_mod, partition_id)\n")
                @printf("       Check whether spiking partition_ids correspond to small FB columns\n")
                @printf("       or periodic step_mod values → may indicate walk attractor or cycling\n")
            else
                @printf("    -> Many spiking buckets: broad concentration — may reflect periodic\n")
                @printf("       structure in step_mod or systematic anchor bias across partitions\n")
            end

            # Marginal analysis: collapse over step_mod to see partition_id alone
            pb_part = Dict{Int,Int}()
            bl_part = Dict{Int,Int}()
            for (k, v) in pb_hist; pid = Int(k & 0xffff); pb_part[pid] = get(pb_part, pid, 0) + v; end
            for (k, v) in bl_hist; pid = Int(k & 0xffff); bl_part[pid] = get(bl_part, pid, 0) + v; end

            part_ratios = Dict{Int,Float64}()
            for pid in union(keys(pb_part), keys(bl_part))
                pf = get(pb_part, pid, 0) / n_pb
                bf = get(bl_part, pid, 0) / n_bl
                bf > 0.0 && (part_ratios[pid] = pf / bf)
            end
            top_parts = sort(collect(keys(part_ratios)), by=k -> -part_ratios[k])[1:min(10,length(part_ratios))]

            @printf("\n    Marginal over step_mod — top partition_ids by ratio:\n")
            @printf("    %-14s  %10s  %10s  %10s\n", "partition_id", "pb_count", "bl_count", "ratio")
            for pid in top_parts
                @printf("    %-14d  %10d  %10d  %10.3f\n",
                        pid,
                        get(pb_part, pid, 0), get(bl_part, pid, 0), part_ratios[pid])
            end

            # Marginal analysis: collapse over partition_id to see step_mod alone
            pb_sm = Dict{Int,Int}()
            bl_sm = Dict{Int,Int}()
            for (k, v) in pb_hist; sm = Int((k >> 16) & 0xff); pb_sm[sm] = get(pb_sm, sm, 0) + v; end
            for (k, v) in bl_hist; sm = Int((k >> 16) & 0xff); bl_sm[sm] = get(bl_sm, sm, 0) + v; end

            sm_ratios = Dict{Int,Float64}()
            for sm in union(keys(pb_sm), keys(bl_sm))
                pf = get(pb_sm, sm, 0) / n_pb
                bf = get(bl_sm, sm, 0) / n_bl
                bf > 0.0 && (sm_ratios[sm] = pf / bf)
            end
            top_sms = sort(collect(keys(sm_ratios)), by=k -> -sm_ratios[k])[1:min(10,length(sm_ratios))]

            @printf("\n    Marginal over partition_id — top step_mod values by ratio:\n")
            @printf("    %-14s  %10s  %10s  %10s\n", "step_mod", "pb_count", "bl_count", "ratio")
            for sm in top_sms
                @printf("    %-14d  %10d  %10d  %10.3f\n",
                        sm,
                        get(pb_sm, sm, 0), get(bl_sm, sm, 0), sm_ratios[sm])
            end
        end
    end   # let D16

    @printf("\n== End LP1-conj deep diagnostics ====================================================\n")
    flush(stdout)
end
