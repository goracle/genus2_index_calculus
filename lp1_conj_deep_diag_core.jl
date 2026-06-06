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
const D19_MAX_PAIRS              = 500_000   # cap on pair co-occurrence dict entries

# D20 — Pre-emission opcode sequence fingerprint.
# We keep a ring buffer of the last D20_WINDOW opcodes and snapshot it at
# every emission.  D20_MAX_SNAPSHOTS caps memory.
const D20_WINDOW        = 256        # opcodes to look back
const D20_RING_SIZE     = D20_WINDOW + 4
const D20_MAX_SNAPSHOTS = 2_000      # per-thread cap on full snapshots
const D20_HIST_WINDOW   = 16         # short window for opcode-N-before-emission histogram
const D20_BASELINE_CAP  = 200_000    # baseline opcode samples (reservoir)

# D21 — Refractory / eligible-state return time.
# After each emission we record how many steps until the *next* 1LP_CONJ opcode
# is seen (whether or not it becomes a close).  Measures refractory length.
const D21_MAX_GAPS      = 5_000      # per-thread cap on return-time samples

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

    # D19 — Factor-base element productivity (closure participation counts).
    # d19_fb_close_counts    : fb_index → total closures touching this element
    #                          (i0 side + prev_col side combined).
    # d19_fb_i0_counts       : fb_index → closures where element appeared as i0.
    # d19_fb_prev_counts     : fb_index → closures where element appeared as prev_col.
    # d19_fb_pair_counts     : (lo,hi) sorted pair → co-occurrence count.
    # d19_anchor_sample_rels : fb_index → up to 5 sample relations as
    #                          (i0, prev_col, combined_al, combined_be) tuples,
    #                          stored for both the i0 and prev_col sides so any
    #                          top anchor will have examples regardless of role.
    d19_fb_close_counts    ::Dict{Int, Int}
    d19_fb_i0_counts       ::Dict{Int, Int}
    d19_fb_prev_counts     ::Dict{Int, Int}
    d19_fb_pair_counts     ::Dict{NTuple{2,Int}, Int}
    d19_anchor_sample_rels ::Dict{Int, Vector{NTuple{4,Int}}}

    # D20 — Pre-emission opcode sequence fingerprint.
    # Ring buffer of recent opcodes (hot path); snapshots at emission time.
    d20_opcode_ring            ::Vector{UInt8}    # circular buffer, length D20_RING_SIZE
    d20_ring_head              ::Int              # next-write index (1-based, mod D20_RING_SIZE)
    d20_ring_filled            ::Int              # how many valid entries (up to D20_RING_SIZE)
    d20_pre_snapshots          ::Vector{UInt8}    # n_snapshots × D20_HIST_WINDOW, row-major
    d20_n_snapshots            ::Int
    d20_baseline_opcode_counts ::Matrix{UInt32}   # D20_HIST_WINDOW × 6 (opcode type)
    d20_n_baseline             ::Int

    # D21 — Refractory gap: steps from emission until next 1LP_CONJ opcode.
    d21_steps_since_emit  ::Int             # -1 = not in refractory tracking
    d21_return_gaps       ::Vector{Int}     # collected return-time samples
    d21_n_emitted         ::Int             # total emissions seen by this thread
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
        # D19
        Dict{Int,Int}(),               # d19_fb_close_counts
        Dict{Int,Int}(),               # d19_fb_i0_counts
        Dict{Int,Int}(),               # d19_fb_prev_counts
        Dict{NTuple{2,Int},Int}(),     # d19_fb_pair_counts
        Dict{Int,Vector{NTuple{4,Int}}}(), # d19_anchor_sample_rels
        # D20
        zeros(UInt8, D20_RING_SIZE),       # d20_opcode_ring
        1,                                  # d20_ring_head
        0,                                  # d20_ring_filled
        UInt8[],                            # d20_pre_snapshots
        0,                                  # d20_n_snapshots
        zeros(UInt32, D20_HIST_WINDOW, 6), # d20_baseline_opcode_counts
        0,                                  # d20_n_baseline
        # D21
        -1,                                 # d21_steps_since_emit
        Int[],                              # d21_return_gaps
        0,                                  # d21_n_emitted
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

        # D19: merge per-FB-element closure counts.
        for (k, v) in s.d19_fb_close_counts
            merged.d19_fb_close_counts[k] = get(merged.d19_fb_close_counts, k, 0) + v
        end
        for (k, v) in s.d19_fb_i0_counts
            merged.d19_fb_i0_counts[k] = get(merged.d19_fb_i0_counts, k, 0) + v
        end
        for (k, v) in s.d19_fb_prev_counts
            merged.d19_fb_prev_counts[k] = get(merged.d19_fb_prev_counts, k, 0) + v
        end
        for (k, v) in s.d19_fb_pair_counts
            if haskey(merged.d19_fb_pair_counts, k)
                merged.d19_fb_pair_counts[k] += v
            elseif length(merged.d19_fb_pair_counts) < D19_MAX_PAIRS
                merged.d19_fb_pair_counts[k] = v
            end
        end
        # D19 sample relations: keep up to 5 per anchor across threads.
        for (k, rels) in s.d19_anchor_sample_rels
            dst = get!(merged.d19_anchor_sample_rels, k, NTuple{4,Int}[])
            for r in rels
                length(dst) >= 5 && break
                push!(dst, r)
            end
        end

        # D20: merge pre-emission snapshots and baseline counts.
        n_rem = (D20_MAX_SNAPSHOTS - merged.d20_n_snapshots) * D20_HIST_WINDOW
        if n_rem > 0 && length(s.d20_pre_snapshots) > 0
            n_take = min(n_rem, length(s.d20_pre_snapshots))
            # round down to whole windows
            n_take = (n_take ÷ D20_HIST_WINDOW) * D20_HIST_WINDOW
            append!(merged.d20_pre_snapshots, s.d20_pre_snapshots[1:n_take])
            merged.d20_n_snapshots += n_take ÷ D20_HIST_WINDOW
        end
        merged.d20_baseline_opcode_counts .+= s.d20_baseline_opcode_counts
        merged.d20_n_baseline += s.d20_n_baseline

        # D21: merge return-gap samples.
        let n_rem21 = D21_MAX_GAPS - length(merged.d21_return_gaps)
            if n_rem21 > 0
                n_take = min(n_rem21, length(s.d21_return_gaps))
                append!(merged.d21_return_gaps, s.d21_return_gaps[1:n_take])
            end
        end
        merged.d21_n_emitted += s.d21_n_emitted
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
#  record_d19_closure! — call from handle_1lp_conj! at every CLOSE,
#  passing the current anchor index (i0), the stored anchor (prev_col),
#  and the relation scalars (combined_al, combined_be).
# ---------------------------------------------------------------------------
@inline function record_d19_closure!(stat       ::ConjDeepStat,
                                      i0         ::Int,
                                      prev_col   ::Int,
                                      combined_al::Int,
                                      combined_be::Int)
    # Per-element totals.
    stat.d19_fb_close_counts[i0]       = get(stat.d19_fb_close_counts, i0, 0) + 1
    stat.d19_fb_close_counts[prev_col] = get(stat.d19_fb_close_counts, prev_col, 0) + 1

    # Directional split.
    stat.d19_fb_i0_counts[i0]          = get(stat.d19_fb_i0_counts, i0, 0) + 1
    stat.d19_fb_prev_counts[prev_col]  = get(stat.d19_fb_prev_counts, prev_col, 0) + 1

    # Pair co-occurrence (canonical order: lo ≤ hi).
    if i0 != prev_col && length(stat.d19_fb_pair_counts) < D19_MAX_PAIRS
        pkey = i0 < prev_col ? (i0, prev_col) : (prev_col, i0)
        stat.d19_fb_pair_counts[pkey] = get(stat.d19_fb_pair_counts, pkey, 0) + 1
    end

    # Sample relations: store up to 5 *distinct* (i0,prev_col) pairs per anchor
    # on both sides so whichever element ends up in the top-5 will have varied
    # examples to display.  Dedup is by (i0,prev_col) pair — scalars are
    # identical for repeated closures of the same pair anyway.
    rel = (i0, prev_col, combined_al, combined_be)
    for anchor in (i0, prev_col)
        dst = get!(stat.d19_anchor_sample_rels, anchor, NTuple{4,Int}[])
        if length(dst) < 5
            already = false
            for r in dst
                if r[1] == i0 && r[2] == prev_col
                    already = true
                    break
                end
            end
            already || push!(dst, rel)
        end
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_d20_step! — call on EVERY valid phi step (hot path, inline).
#  Updates the opcode ring buffer and (1/baseline_rate) baseline reservoir.
#  Also advances the D21 refractory counter.
#
#  opcode should be one of OPCODE_0LP .. OPCODE_SKIP.
#  baseline_gate: sample baseline when (rand(UInt16) & 0x1f) == 0  (1/32 rate).
# ---------------------------------------------------------------------------
@inline function record_d20_step!(stat  ::ConjDeepStat,
                                   opcode::UInt8)
    # ── Ring buffer update ────────────────────────────────────────────────
    head = stat.d20_ring_head
    @inbounds stat.d20_opcode_ring[head] = opcode
    head = head == D20_RING_SIZE ? 1 : head + 1
    stat.d20_ring_head = head
    filled = stat.d20_ring_filled
    stat.d20_ring_filled = filled < D20_RING_SIZE ? filled + 1 : D20_RING_SIZE

    # ── Baseline reservoir (sparse: 1/32 of all steps) ───────────────────
    if stat.d20_n_baseline < D20_BASELINE_CAP && (rand(UInt8) & 0x1f) == 0x00
        # Record opcode-at-position[-k] for k=1..D20_HIST_WINDOW as a tally.
        # We use position 0 = "most recent step before now" = ring[head-1].
        ring = stat.d20_opcode_ring
        cur_filled = stat.d20_ring_filled
        cur_head   = stat.d20_ring_head - 1  # last-written slot (0→D20_RING_SIZE)
        cur_head   = cur_head == 0 ? D20_RING_SIZE : cur_head
        n_avail    = min(cur_filled, D20_HIST_WINDOW)
        for k in 1:n_avail
            slot = cur_head - k + 1
            slot = slot <= 0 ? slot + D20_RING_SIZE : slot
            oc   = Int(ring[slot]) + 1   # 1-based opcode index (1..6)
            @inbounds stat.d20_baseline_opcode_counts[k, oc] += UInt32(1)
        end
        stat.d20_n_baseline += 1
    end

    # ── D21 refractory tracker ────────────────────────────────────────────
    if stat.d21_steps_since_emit >= 0
        stat.d21_steps_since_emit += 1
        # First time we see a 1LP_CONJ opcode after an emission: record return gap.
        if opcode == OPCODE_1LP_CONJ
            if length(stat.d21_return_gaps) < D21_MAX_GAPS
                push!(stat.d21_return_gaps, stat.d21_steps_since_emit)
            end
            stat.d21_steps_since_emit = -1   # stop tracking until next emission
        end
    end

    return nothing
end

# ---------------------------------------------------------------------------
#  record_d20_emission! — call at every LP1-conj CLOSE (emission).
#  Snapshots the last D20_HIST_WINDOW opcodes from the ring buffer and
#  resets the D21 refractory counter.
# ---------------------------------------------------------------------------
@inline function record_d20_emission!(stat::ConjDeepStat)
    # ── D20 snapshot ─────────────────────────────────────────────────────
    if stat.d20_n_snapshots < D20_MAX_SNAPSHOTS
        ring      = stat.d20_opcode_ring
        cur_head  = stat.d20_ring_head - 1
        cur_head  = cur_head == 0 ? D20_RING_SIZE : cur_head
        n_avail   = min(stat.d20_ring_filled, D20_HIST_WINDOW)
        for k in 1:D20_HIST_WINDOW
            if k <= n_avail
                slot = cur_head - k + 1
                slot = slot <= 0 ? slot + D20_RING_SIZE : slot
                push!(stat.d20_pre_snapshots, stat.d20_opcode_ring[slot])
            else
                push!(stat.d20_pre_snapshots, 0xff)  # sentinel: no data
            end
        end
        stat.d20_n_snapshots += 1
    end

    # ── D21 reset ────────────────────────────────────────────────────────
    stat.d21_steps_since_emit = 0
    stat.d21_n_emitted       += 1

    return nothing
end
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
