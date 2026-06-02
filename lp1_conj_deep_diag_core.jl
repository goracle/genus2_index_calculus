# =============================================================================
#  lp1_conj_deep_diag_core.jl
#
#  Shared infrastructure for LP1-conj deep diagnostics:
#    • Global constants
#    • ConjDeepStat struct + constructor
#    • merge_conj_deep_stats
#    • Hot-path recording functions:
#        record_conj_deep_miss!
#        record_conj_deep_step!
#        record_conj_deep_opcode!
#        record_d16_emission!
#    • Math helpers: _gini, _hill_exponent, _top_share, _deep_fp64, _deep_bucket
#
#  Included by lp1_conj_deep_diag.jl; do not include directly.
# =============================================================================

# ---------------------------------------------------------------------------
#  Constants
# ---------------------------------------------------------------------------
const DEEP_DIAG_BUCKET_BITS      = 10          # 2^10 = 1024 coarse buckets
const DEEP_DIAG_N_BUCKETS        = 1 << DEEP_DIAG_BUCKET_BITS
const DEEP_DIAG_MAX_ANCESTRY     = 500_000
const DEEP_DIAG_COND_ENT_LAG     = 4
const DEEP_DIAG_MAX_OPCODE_LOG   = 2_000_000
const D12_MAX_EVENTS             = 500_000
const D7_MAX_CLOSURES            = 500_000
const D8_MAX_DEPTHS              = 500_000
const D8_MAX_SHADOW              = 500_000
const D17_MAX_TRACKED_KEYS       = 200_000

# D16 — Pre-burst state fingerprinting ring-buffer constants.
const D16_LAG_LO      = 10
const D16_LAG_HI      = 40
const D16_RING_SIZE   = D16_LAG_HI + 4
const D16_GATE_DENOM  = 64
const D16_MAX_SAMPLES = 50_000

# ---------------------------------------------------------------------------
#  Opcode symbols used by record_conj_deep_opcode! and the D9/D11 diagnostics.
# ---------------------------------------------------------------------------
const OPCODE_0LP      = 0x00
const OPCODE_1LP_AFF  = 0x01
const OPCODE_1LP_CONJ = 0x02
const OPCODE_2LP_AFF  = 0x03
const OPCODE_2LP_CONJ = 0x04
const OPCODE_SKIP     = 0x05

# ---------------------------------------------------------------------------
#  ConjDeepStat — per-thread accumulator
# ---------------------------------------------------------------------------
mutable struct ConjDeepStat
    # D2 — transition matrix: n_trans[from_bucket+1, to_bucket+1] = count.
    # UInt32 keeps memory: 1024×1024×4 B = 4 MB per thread.
    n_trans         ::Matrix{UInt32}
    _prev_bucket    ::Int

    # D3 — branch ancestry log (capped at DEEP_DIAG_MAX_ANCESTRY).
    ancestry_log_a      ::Vector{UInt16}
    ancestry_log_parity ::Vector{UInt8}
    ancestry_log_keyhash::Vector{UInt32}

    # D7 — per-emission first-closure flag.
    is_first_closure::Vector{Bool}
    n_emissions     ::Int

    # D8 — closure-depth distribution.
    d8_shadow       ::Dict{UInt128, Int}   # lp_key → store raw_step
    d8_depths       ::Vector{Int}
    d8_close_bkt    ::Vector{UInt16}
    d8_close_abkt   ::Vector{UInt16}
    d8_prev_depth   ::Int

    # D12 — Alpha/anchor joint support.
    d12_store_alpha ::Vector{Int}
    d12_store_px    ::Vector{Int}
    d12_store_key   ::Vector{UInt128}
    d12_close_alpha ::Vector{Int}
    d12_close_px    ::Vector{Int}
    d12_close_key   ::Vector{UInt128}

    # D14 — φ-coefficient 'a' at each store event (sentinel -1 if unavailable).
    d14_store_a     ::Vector{Int}

    # D16 — Pre-burst state fingerprinting ring buffer + histograms.
    d16_ring_step_mod   ::Vector{UInt8}
    d16_ring_partition  ::Vector{UInt16}
    d16_ring_bkt        ::Vector{UInt16}
    d16_emission_count  ::Int
    d16_preburst_hist   ::Dict{UInt32, Int}
    d16_baseline_hist   ::Dict{UInt32, Int}
    d16_n_preburst      ::Int
    d16_n_baseline      ::Int

    # D9 — step-opcode log.
    opcode_log      ::Vector{UInt8}
    opcode_is_lp1c  ::Vector{Bool}

    # D17 — per-key lifetime multiplicity counter.
    d17_lifetime_hits ::Dict{UInt128, Int}
    # D17 metadata: (px, py, a) of the anchor point P0 and φ-coefficient a
    # at the *first* store event for each key.  Keyed identically to
    # d17_lifetime_hits; populated only when px >= 0.  Used to annotate the
    # top-50 table with the walk state that first introduced the key.
    d17_key_meta      ::Dict{UInt128, NTuple{3,Int}}
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
        Dict{UInt128,Int}(),           # d17_lifetime_hits
        Dict{UInt128,NTuple{3,Int}}(), # d17_key_meta
    )
end

# ---------------------------------------------------------------------------
#  merge_conj_deep_stats — reduce per-thread structs into one.
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
            n_rem > 0 && append!(merged.is_first_closure,
                                 s.is_first_closure[1:min(n_rem, length(s.is_first_closure))])
        end
        merged.n_emissions += s.n_emissions

        # D8: merge depth/bucket vectors; shadow table is not merged.
        let n_rem = D8_MAX_DEPTHS - length(merged.d8_depths)
            if n_rem > 0
                n_take = min(n_rem, length(s.d8_depths))
                append!(merged.d8_depths,     s.d8_depths[1:n_take])
                append!(merged.d8_close_bkt,  s.d8_close_bkt[1:n_take])
                append!(merged.d8_close_abkt, s.d8_close_abkt[1:n_take])
            end
        end

        # D9: merge opcode log.
        let n_rem = DEEP_DIAG_MAX_OPCODE_LOG - length(merged.opcode_log)
            if n_rem > 0
                n_take = min(n_rem, length(s.opcode_log))
                append!(merged.opcode_log,     s.opcode_log[1:n_take])
                append!(merged.opcode_is_lp1c, s.opcode_is_lp1c[1:n_take])
            end
        end

        # D12: merge store/close event logs.
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

        # D14: merge store_a.
        let n_rem = D12_MAX_EVENTS - length(merged.d14_store_a)
            if n_rem > 0
                n_take = min(n_rem, length(s.d14_store_a))
                append!(merged.d14_store_a, s.d14_store_a[1:n_take])
            end
        end

        # D16: merge histograms; ring buffer is per-thread ephemeral.
        for (k, v) in s.d16_preburst_hist
            merged.d16_preburst_hist[k] = get(merged.d16_preburst_hist, k, 0) + v
        end
        for (k, v) in s.d16_baseline_hist
            merged.d16_baseline_hist[k] = get(merged.d16_baseline_hist, k, 0) + v
        end
        merged.d16_n_preburst += s.d16_n_preburst
        merged.d16_n_baseline += s.d16_n_baseline

        # D17: merge per-key lifetime hit counters.
        for (k, v) in s.d17_lifetime_hits
            if haskey(merged.d17_lifetime_hits, k)
                merged.d17_lifetime_hits[k] += v
            elseif length(merged.d17_lifetime_hits) < D17_MAX_TRACKED_KEYS
                merged.d17_lifetime_hits[k] = v
            end
        end
        # D17 metadata: keep first-seen (px, py, a) per key; no cap needed
        # since d17_key_meta is a subset of d17_lifetime_hits keys.
        for (k, meta) in s.d17_key_meta
            haskey(merged.d17_key_meta, k) || (merged.d17_key_meta[k] = meta)
        end
    end
    return merged
end

# ---------------------------------------------------------------------------
#  record_conj_deep_miss! — call at every STORE (miss path in handle_1lp_conj!).
# ---------------------------------------------------------------------------
@inline function record_conj_deep_miss!(stat     ::ConjDeepStat,
                                         lp_key   ::UInt128,
                                         raw_step ::Int,
                                         alpha_cur::Int = -1,
                                         px       ::Int = -1,
                                         a_val    ::Int = -1,
                                         py       ::Int = -1)
    if !haskey(stat.d8_shadow, lp_key) && length(stat.d8_shadow) < D8_MAX_SHADOW
        stat.d8_shadow[lp_key] = raw_step
    end

    # D17: lifetime hit counter + first-seen anchor metadata.
    if haskey(stat.d17_lifetime_hits, lp_key)
        stat.d17_lifetime_hits[lp_key] += 1
    elseif length(stat.d17_lifetime_hits) < D17_MAX_TRACKED_KEYS
        stat.d17_lifetime_hits[lp_key] = 1
        # Record (px, py, a) on the very first store for this key.
        px >= 0 && (stat.d17_key_meta[lp_key] = (px, py, a_val))
    end

    # D12/D14: record (alpha, px, a) at store time.
    if alpha_cur >= 0 && length(stat.d12_store_alpha) < D12_MAX_EVENTS
        push!(stat.d12_store_alpha, alpha_cur)
        push!(stat.d12_store_px,    px)
        push!(stat.d12_store_key,   lp_key)
        push!(stat.d14_store_a,     a_val)
    end
    return nothing
end

# ---------------------------------------------------------------------------
#  record_conj_deep_step! — call at every CLOSE (emission) in handle_1lp_conj!.
# ---------------------------------------------------------------------------
@inline function record_conj_deep_step!(stat     ::ConjDeepStat,
                                         lp_key   ::UInt128,
                                         a_bucket ::Int,
                                         raw_step ::Int,
                                         is_first ::Bool,
                                         alpha_cur::Int = -1,
                                         px       ::Int = -1)
    stat.n_emissions += 1

    h64 = _deep_fp64(lp_key)
    bkt = Int(h64 >> (64 - DEEP_DIAG_BUCKET_BITS))   # 0-based ∈ [0, 1023]

    if stat._prev_bucket >= 0
        @inbounds stat.n_trans[stat._prev_bucket + 1, bkt + 1] += 0x00000001
    end
    stat._prev_bucket = bkt

    # D3 ancestry log.
    if length(stat.ancestry_log_a) < DEEP_DIAG_MAX_ANCESTRY
        push!(stat.ancestry_log_a,       UInt16(clamp(a_bucket, 0, 65535)))
        push!(stat.ancestry_log_parity,  UInt8(raw_step & 0x3))
        push!(stat.ancestry_log_keyhash, UInt32(h64 & 0xffffffff))
    end

    # D7 closure flag.
    length(stat.is_first_closure) < D7_MAX_CLOSURES && push!(stat.is_first_closure, is_first)

    # D8 closure depth.
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

    # D12 close event.
    if alpha_cur >= 0 && length(stat.d12_close_alpha) < D12_MAX_EVENTS
        push!(stat.d12_close_alpha, alpha_cur)
        push!(stat.d12_close_px,    px)
        push!(stat.d12_close_key,   lp_key)
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_conj_deep_opcode! — call from the main walk loop on every valid phi step.
# ---------------------------------------------------------------------------
@inline function record_conj_deep_opcode!(stat       ::ConjDeepStat,
                                           opcode     ::UInt8,
                                           is_emission::Bool)
    length(stat.opcode_log) >= DEEP_DIAG_MAX_OPCODE_LOG && return nothing
    push!(stat.opcode_log,     opcode)
    push!(stat.opcode_is_lp1c, is_emission)
    return nothing
end

# ---------------------------------------------------------------------------
#  record_d16_emission! — call on every LP1-conj emission (close event) for D16.
# ---------------------------------------------------------------------------
@inline function record_d16_emission!(stat        ::ConjDeepStat,
                                       lp_key      ::UInt128,
                                       raw_step    ::Int,
                                       partition_id::Int)
    ec   = stat.d16_emission_count
    ring = ec % D16_RING_SIZE + 1

    h64  = UInt64(lp_key & 0xffffffffffffffff) * UInt64(0x9e3779b97f4a7c15) ⊻
           UInt64(lp_key >> 64)              * UInt64(0x6c62272e07bb0142)
    h64  ⊻= h64 >> 32; h64 *= UInt64(0x45d9f3b37197344d); h64 ⊻= h64 >> 32
    cur_bkt = UInt16(h64 >> (64 - DEEP_DIAG_BUCKET_BITS))

    step_mod_cur = UInt8(raw_step & 0xff)
    part_cur     = UInt16(clamp(partition_id, 0, 65535))

    # Baseline sampling: 1/D16_GATE_DENOM.
    if (rand(UInt8) & UInt8(D16_GATE_DENOM - 1)) == UInt8(0)
        bkey = UInt32(step_mod_cur) << 16 | UInt32(part_cur)
        stat.d16_baseline_hist[bkey] = get(stat.d16_baseline_hist, bkey, 0) + 1
        stat.d16_n_baseline += 1
    end

    # Pre-burst detection: scan ring for lag-Δ matches.
    if ec >= D16_LAG_LO && stat.d16_n_preburst < D16_MAX_SAMPLES
        if (rand(UInt8) & UInt8(D16_GATE_DENOM - 1)) == UInt8(0)
            @inbounds for lag in D16_LAG_LO:D16_LAG_HI
                past_slot = ((ec - lag) % D16_RING_SIZE) + 1
                if stat.d16_ring_bkt[past_slot] == cur_bkt
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

    @inbounds begin
        stat.d16_ring_step_mod[ring]  = step_mod_cur
        stat.d16_ring_partition[ring] = part_cur
        stat.d16_ring_bkt[ring]       = cur_bkt
    end
    stat.d16_emission_count = ec + 1
    return nothing
end

# ---------------------------------------------------------------------------
#  Internal hash helpers
# ---------------------------------------------------------------------------
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
#  Math helpers shared across diagnostic sections
# ---------------------------------------------------------------------------

"""Gini coefficient of a count vector (0 = uniform, 1 = winner-takes-all)."""
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

"""
Hill tail exponent from top-k order statistics.
Uses log-ratio estimator: α̂ = 1/H̄ where H̄ = mean log(x_i / x_k) for i < k.
"""
function _hill_exponent(sorted_desc::Vector{Int}; k::Int = 50)::Float64
    n = length(sorted_desc)
    k = min(k, n - 1)
    k < 2 && return NaN
    xk = Float64(max(1, sorted_desc[k + 1]))
    s  = 0.0
    for i in 1:k
        s += log(max(1.0, Float64(sorted_desc[i])) / xk)
    end
    return k / max(1e-30, s)
end

"""Fraction of total mass in the top `frac × n` items (sorted descending)."""
function _top_share(counts::Vector{Int}, frac::Float64)::Float64
    isempty(counts) && return 0.0
    total = sum(counts)
    total == 0 && return 0.0
    sorted = sort(counts, rev=true)
    k = max(1, round(Int, frac * length(sorted)))
    sum(sorted[1:k]) / total
end
