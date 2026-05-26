# =============================================================================
#  trial3_config.jl  --  Global constants, shared data structures, and caps.
#
#  Included by trial3_fixed.jl before any other trial3_* file.
# =============================================================================

# ---------------------------------------------------------------------------
#  Relation integrity asserts
#  Set to false in production to skip Jacobian-arithmetic cross-checks.
# ---------------------------------------------------------------------------
const ASSERT_RELATIONS = true

# ---------------------------------------------------------------------------
#  1-LP table caps
#
#  MAX_LP1_ENTRIES: upper bound on shared_lp1 (affine LPs).
#    Steady-state occupancy is O(√(LP keyspace)) ≈ O(√p) entries in flight.
#    For p ≈ 164K that's ~400 expected; 100K gives 250× headroom while
#    bounding retained heap to ~20–40 MB (each entry: Dict{Int,Int} + 2 Ints).
#    The old 50M cap caused a slow memory leak: entries accumulate
#    monotonically under single-entry FIFO eviction until the cap is hit.
#
#  MAX_LP1_DOUBLED_ENTRIES: cap on shared_lp_doubled (odd-cycle residuals).
#    Previously uncapped; cross-close is rare so a small bound suffices.
#
#  MAX_LP1_CONJ_ENTRIES: cap for the conjugate-pair 1-LP table.  The keyspace
#    is ~p^2 so closures are rare; steady-state occupancy is O(min(ell,p)).
#    Cap is computed at construction as LP1_CONJ_CAP_MULTIPLIER * min(ell,p).
# ---------------------------------------------------------------------------
const MAX_LP1_ENTRIES         = 50_000_000
const MAX_LP1_DOUBLED_ENTRIES = 100_000

# MAX_LP1_CONJ_ENTRIES is no longer a fixed constant — it is computed at
# ShardedLP1Conj(ell) construction time.
#
# Theory: the conj LP key is a 4-tuple of F_p coordinates from the Mumford
# representation of a degree-2 residual over F_p².  Although the full Mumford
# keyspace has size O(p²), the walk only produces residuals whose group order
# divides ell (the large prime factor of #J).  The number of distinct conj LP
# keys the walk can encounter is therefore O(min(ell, p)), not O(p).
#
# This matters critically when ell ≪ p (e.g. p=13M, ell=196K from a highly
# composite #J): using p as the cap allocates 209M-entry capacity that is
# never needed and OOMs the process.  Using min(ell, p) keeps the cap tight.
#
# Empirical: at p≈131K, ell≈p, steady-state ≈ 8·min(ell,p).  Multiplier 16
# gives comfortable headroom in both regimes:
#   ell≈p=16K   → cap ≈  262K entries ≈    4 MB  (was ~5 MB with Dict)
#   ell≈p=131K  → cap ≈  2.1M entries ≈   27 MB  (was ~36 MB)
#   ell≈p=1.3M  → cap ≈   21M entries ≈  273 MB  (was ~360 MB)
#   ell=196K, p=13M → cap ≈ 3.1M entries ≈   40 MB  (was ~53 MB, was 209M → OOM)
#
const LP1_CONJ_CAP_MULTIPLIER = 16
# Hard ceiling regardless of p/ell — prevents catastrophic over-allocation.
const LP1_CONJ_CAP_MAX = 200_000_000

# ---------------------------------------------------------------------------
#  Sharded conjugate-pair 1-LP table
#
#  Each shard is a flat open-addressing hash table storing both the full
#  4×UInt32 Mumford key and the associated value.  Storing the full key:
#
#    • Eliminates false-positive matches entirely.  The fingerprint-only design
#      had ~5% false-positive rate per probe at 80% load, producing bad
#      relations on every closure.
#
#    • Enables backward-shift deletion (Robin Hood compaction on delete)
#      instead of tombstones.  Tombstone-based designs without stored keys
#      cannot rehash correctly during rebuild.  Backward-shift is O(1)
#      amortized per delete, keeps chains contiguous, and requires no
#      separate rebuild pass.
#
#  Memory per entry at 80% load:
#    key:  16 bytes/slot → 20 effective bytes/entry
#    val:  10 bytes/slot (amortized) → 12.5 effective bytes/entry
#    total ≈ 33 bytes/entry   vs ~110 (Dict)
#
#  N_CONJ_SHARDS must be a power of 2 for the cheap mask in conj_shard_idx.
# ---------------------------------------------------------------------------
const N_CONJ_SHARDS   = 32
const CONJ_LOAD_NUM   = 4    # max load = LOAD_NUM / LOAD_DENOM = 80%
const CONJ_LOAD_DENOM = 5

# Sentinel key — marks an empty slot.  typemax(UInt128) is never a valid
# CanonicalLP1Key because all four 32-bit limbs would need to be 0xffffffff,
# but p < 2^32 so all valid coordinates are in [0, p).
const CanonicalLP1Key = UInt128
const CONJ_KEY_EMPTY  = typemax(CanonicalLP1Key)

# ---------------------------------------------------------------------------
#  LP1ConjVal — value stored in the conj 1-LP table.
#
#  Amortized mode (beta_zero=true): neg_be is always 0 — drop the field.
#    LP1ConjVal     (10 bytes): i0::UInt16 + neg_al::UInt64
#    LP1ConjValFull (18 bytes): i0::UInt16 + neg_al::UInt64 + neg_be::UInt64
#
#  i0     — FB column index, max ~O(√p) ≈ 10^4 at p=10^8, fits UInt16.
#  neg_al — exponent mod ell.  ell ≤ #J ≈ p², fits UInt64 for p < 2^32.
#  neg_be — same range; omitted in amortized mode (always 0).
# ---------------------------------------------------------------------------
struct LP1ConjVal          # amortized mode  (10 bytes)
    i0     ::UInt16
    neg_al ::UInt64
end

struct LP1ConjValFull      # single-shot mode (18 bytes)
    i0     ::UInt16
    neg_al ::UInt64
    neg_be ::UInt64
end

# ---------------------------------------------------------------------------
#  ConjShard — one shard of the full-key open-addressing hash table.
#
#  keys[i]  ::NTuple{4,UInt32}  — full Mumford key, or CONJ_KEY_EMPTY
#  vals[i]  ::V                 — stored value (meaningful only when
#                                 keys[i] != CONJ_KEY_EMPTY)
#  count    ::Int               — live entry count
#  cap      ::Int               — slot count, always a power of 2
#  mask     ::UInt              — cap - 1, for cheap slot wrapping
#  max_entries::Int             — live-entry cap (drop threshold)
#
#  Deletion uses backward-shift (Robin Hood compaction): when a slot is
#  vacated, entries behind it in the probe chain that were displaced from
#  their natural slot are shifted back to fill the gap.  This keeps chains
#  contiguous so lookup stops on the first empty slot — no tombstones,
#  no separate rebuild pass needed.
# ---------------------------------------------------------------------------
mutable struct ConjShard{V}
    keys        ::Vector{NTuple{4,UInt32}}
    vals        ::Vector{V}
    count       ::Int   # live entries
    cap         ::Int   # slot count, always a power of 2
    mask        ::UInt  # cap - 1
    max_entries ::Int   # live-entry cap (drop threshold)
end

function ConjShard{V}(cap_entries::Int) where V
    slot_count = max(16, nextpow(2, cld(cap_entries * CONJ_LOAD_DENOM, CONJ_LOAD_NUM)))
    keys = fill(CONJ_KEY_EMPTY, slot_count)
    vals = Vector{V}(undef, slot_count)
    ConjShard{V}(keys, vals, 0, slot_count, UInt(slot_count - 1), cap_entries)
end

# ---------------------------------------------------------------------------
#  Hash — maps a Mumford 4-tuple to a starting slot (1-based).
#  Each component gets a distinct multiply constant so no XOR cancellation
#  is possible (unlike the old design which XOR'd all four together first,
#  making keys like (a,b,a,b) hash identically to (0,0,0,0) XOR-wise).
# ---------------------------------------------------------------------------
@inline function _conj_hash64(key::NTuple{4,UInt32})::UInt64
    h = UInt64(key[1]) * 0x9e3779b97f4a7c15 +
        UInt64(key[2]) * 0x6c62272e07bb0142 +
        UInt64(key[3]) * 0x94d049bb133111eb +
        UInt64(key[4]) * 0xbf58476d1ce4e5b9
    h = h ⊻ (h >> 32)
    h = h * 0x45d9f3b37197344d
    h = h ⊻ (h >> 32)
    h
end

@inline function _conj_slot_hash(key::NTuple{4,UInt32}, mask::UInt)::Int
    Int(_conj_hash64(key) & mask) + 1   # 1-based
end

# ---------------------------------------------------------------------------
#  Core primitives — all require caller to hold the shard lock.
# ---------------------------------------------------------------------------

# Find the slot holding `key`.  Returns slot > 0 if found, 0 if absent.
@inline function _conj_find(shard::ConjShard, key::NTuple{4,UInt32})::Int
    cap  = shard.cap
    keys = shard.keys
    slot = _conj_slot_hash(key, shard.mask)
    @inbounds while true
        k = keys[slot]
        k == key            && return slot
        k == CONJ_KEY_EMPTY && return 0
        slot = slot == cap ? 1 : slot + 1
    end
end

# Insert key→val.  Caller must have verified count < max_entries and that
# the key is not already present.
@inline function _conj_insert!(shard::ConjShard{V}, key::NTuple{4,UInt32}, val::V) where V
    cap  = shard.cap
    keys = shard.keys
    vals = shard.vals
    slot = _conj_slot_hash(key, shard.mask)
    @inbounds while true
        if keys[slot] == CONJ_KEY_EMPTY
            keys[slot] = key
            vals[slot] = val
            shard.count += 1
            return
        end
        slot = slot == cap ? 1 : slot + 1
    end
end

# Delete the entry at `slot` using backward-shift (Robin Hood compaction).
# Entries displaced from their natural slot are shifted back to fill the gap,
# keeping probe chains contiguous so future lookups remain correct.
# Caller must hold the shard lock.
@inline function _conj_delete_slot!(shard::ConjShard, slot::Int)
    cap  = shard.cap
    keys = shard.keys
    vals = shard.vals
    mask = shard.mask
    @inbounds begin
        keys[slot] = CONJ_KEY_EMPTY
        shard.count -= 1
        gap  = slot
        curr = slot == cap ? 1 : slot + 1
        while keys[curr] != CONJ_KEY_EMPTY
            nat = _conj_slot_hash(keys[curr], mask)
            # Entry at curr should move into gap if gap lies on the probe path
            # from nat to curr, i.e. if nat "wrapped past" gap to reach curr.
            displaced = if gap < curr
                nat <= gap || nat > curr
            else   # gap > curr (probe chain wrapped around)
                nat <= gap && nat > curr
            end
            if displaced
                keys[gap] = keys[curr]
                vals[gap] = vals[curr]
                keys[curr] = CONJ_KEY_EMPTY
                gap = curr
            end
            curr = curr == cap ? 1 : curr + 1
        end
    end
    nothing
end

# ---------------------------------------------------------------------------
#  ShardedLP1Conj — sharded flat-table conjugate 1-LP store.
#
#  Parameterised on V so it works for both LP1ConjVal (amortized) and
#  LP1ConjValFull (single-shot).  The type parameter is determined at
#  construction time based on the amortized flag passed to the constructor.
# ---------------------------------------------------------------------------
struct ShardedLP1Conj{V}
    shards      ::NTuple{N_CONJ_SHARDS, ConjShard{V}}
    locks       ::NTuple{N_CONJ_SHARDS, ReentrantLock}
    max_entries ::Int   # total cap across all shards
end

function ShardedLP1Conj(ell::Integer; amortized::Bool = true)
    cap = min(LP1_CONJ_CAP_MULTIPLIER * Int(min(ell, p)), LP1_CONJ_CAP_MAX)
    cap_per_shard = max(16, cld(cap, N_CONJ_SHARDS))
    if amortized
        shards = ntuple(_ -> ConjShard{LP1ConjVal}(cap_per_shard),    N_CONJ_SHARDS)
    else
        shards = ntuple(_ -> ConjShard{LP1ConjValFull}(cap_per_shard), N_CONJ_SHARDS)
    end
    locks = ntuple(_ -> ReentrantLock(), N_CONJ_SHARDS)
    ShardedLP1Conj(shards, locks, cap)
end

# ---------------------------------------------------------------------------
#  Public API for ShardedLP1Conj — mirrors the old Dict-based interface so
#  call sites in phase2 and phase3 change minimally.
# ---------------------------------------------------------------------------

# Route a CanonicalLP1Key to its shard index (1-based).
# Shard is determined by the low log2(N_CONJ_SHARDS) bits of the key
# (i.e. the low bits of u0 after mod-p reduction).
@inline function conj_shard_idx(key::CanonicalLP1Key)::Int
    Int(key & UInt128(N_CONJ_SHARDS - 1)) + 1
end

# THE ONLY valid canonical form for LP1-conj keys.
# All hashing, storage, lookup, serialization must use this.
@inline function canonical_lp1_conj_key(u0::Int, u1::Int, v0::Int, v1::Int)::CanonicalLP1Key
    UInt128(UInt32(mod(u0, p))) |
    (UInt128(UInt32(mod(u1, p))) << 32) |
    (UInt128(UInt32(mod(v0, p))) << 64) |
    (UInt128(UInt32(mod(v1, p))) << 96)
end
@inline canonical_lp1_conj_key(key::NTuple{4,Int})::CanonicalLP1Key =
    canonical_lp1_conj_key(key[1], key[2], key[3], key[4])

# Total live entries across all shards (for reporting).
function conj_total_entries(sc::ShardedLP1Conj)::Int
    s = 0
    for sh in sc.shards; s += sh.count; end
    s
end

# Lookup: returns true if key is present.  Caller must hold the shard lock.
@inline function conj_haskey(sc::ShardedLP1Conj, si::Int, key::NTuple{4,UInt32})::Bool
    _conj_find(sc.shards[si], key) != 0
end

# Fetch value for a known-present key.  Caller must hold the shard lock.
@inline function conj_getval(sc::ShardedLP1Conj{V}, si::Int, key::NTuple{4,UInt32})::V where V
    slot = _conj_find(sc.shards[si], key)
    @inbounds sc.shards[si].vals[slot]
end

# Fetch-and-delete.  Returns the value and removes the entry.
# Caller must hold the shard lock.
@inline function conj_pop!(sc::ShardedLP1Conj{V}, si::Int, key::NTuple{4,UInt32})::V where V
    sh   = sc.shards[si]
    slot = _conj_find(sh, key)
    val  = @inbounds sh.vals[slot]
    _conj_delete_slot!(sh, slot)
    val
end

# Insert key→val, but only if count < max_entries.
# Returns true if stored, false if dropped (at cap).
# Caller must hold the shard lock.
@inline function conj_insert!(sc::ShardedLP1Conj{V}, si::Int,
                               key::NTuple{4,UInt32}, val::V)::Bool where V
    sh = sc.shards[si]
    sh.count >= sh.max_entries && return false
    _conj_insert!(sh, key, val)
    return true
end

# ---------------------------------------------------------------------------
#  Val-type helpers — allow handle_1lp_conj! to be generic over LP1ConjVal
#  and LP1ConjValFull without any runtime branching.
# ---------------------------------------------------------------------------
@inline _conj_prev_be(v::LP1ConjVal)     = 0
@inline _conj_prev_be(v::LP1ConjValFull) = Int(v.neg_be)

@inline _conj_make_val(::Type{LP1ConjVal},     i0::UInt16, al::UInt64, be::UInt64) = LP1ConjVal(i0, al)
@inline _conj_make_val(::Type{LP1ConjValFull}, i0::UInt16, al::UInt64, be::UInt64) = LP1ConjValFull(i0, al, be)

# ---------------------------------------------------------------------------
#  conj_to_dict — snapshot a ShardedLP1Conj into a plain Dict for lockless
#  read-only use in phase3 workers.  Call once before spawning workers.
# ---------------------------------------------------------------------------
function conj_to_dict(sc::ShardedLP1Conj{V})::Dict{CanonicalLP1Key, V} where V
    d = Dict{CanonicalLP1Key, V}()
    sizehint!(d, conj_total_entries(sc) + 16)
    for si in 1:N_CONJ_SHARDS
        lock(sc.locks[si])
        sh = sc.shards[si]
        @inbounds for slot in 1:sh.cap
            k = sh.keys[slot]
            k == CONJ_KEY_EMPTY && continue
            # Reconstruct UInt128 key from NTuple{4,UInt32} — same as canonical_lp1_conj_key.
            ck = UInt128(k[1]) | (UInt128(k[2]) << 32) |
                 (UInt128(k[3]) << 64) | (UInt128(k[4]) << 96)
            d[ck] = sh.vals[slot]
        end
        unlock(sc.locks[si])
    end
    d
end

# ---------------------------------------------------------------------------
#  Phase 3 step cap  (scales with √ell)
# ---------------------------------------------------------------------------
const PHASE3_STEP_MULTIPLIER = 10
const PHASE3_STEP_CAP_MIN    = 500_000
const PHASE3_STEP_CAP_MAX    = 500_000_000

function phase3_default_step_cap(ell::Integer)::Int
    raw = PHASE3_STEP_MULTIPLIER * isqrt(BigInt(ell))
    Int(clamp(raw, PHASE3_STEP_CAP_MIN, PHASE3_STEP_CAP_MAX))
end

# ---------------------------------------------------------------------------
#  Phase 3 local LP table caps
#
#  Each per-trial worker maintains two local birthday dicts as fallbacks when
#  the precomputed tables miss.  Without a cap these grow monotonically at
#  O(√ell) expected entries in steady state, and with many threads running
#  concurrently the combined heap explodes:
#    threads × 2 dicts × O(√ell) entries × ~100 B/entry
#  At ell≈1.85×10¹², √ell≈1.36×10⁶, 32 threads → ~8 GB → OOM.
#
#  Cap strategy: store up to phase3_local_lp_cap(ell) entries per dict.
#  On overflow the incoming entry is dropped (not stored); the walk generates
#  another matchable entry at the cost of a small increase in expected steps.
#
#  PHASE3_LOCAL_LP_NUM / PHASE3_LOCAL_LP_DENOM: cap as a fraction of √ell.
#    0.5 × √ell × 2 dicts × 32 threads × ~100 B ≈ 4 GB — manageable.
#    Reduce the numerator further if RSS is still tight.
#  PHASE3_LOCAL_LP_MIN: floor so tiny-ell cases still get a usable table.
#  PHASE3_LOCAL_LP_MAX: hard ceiling regardless of ell.
# ---------------------------------------------------------------------------
const PHASE3_LOCAL_LP_NUM   = 1       # cap = (NUM/DENOM) × √ell per dict
const PHASE3_LOCAL_LP_DENOM = 2       # → 0.5 × √ell
const PHASE3_LOCAL_LP_MIN   = 1_000
const PHASE3_LOCAL_LP_MAX   = 2_000_000

function phase3_local_lp_cap(ell::Integer)::Int
    raw = (PHASE3_LOCAL_LP_NUM * isqrt(BigInt(ell))) ÷ PHASE3_LOCAL_LP_DENOM
    Int(clamp(raw, PHASE3_LOCAL_LP_MIN, PHASE3_LOCAL_LP_MAX))
end

# ---------------------------------------------------------------------------
#  2-LP graph memory caps
# ---------------------------------------------------------------------------
const DEFAULT_MAX_LP2_NODES      = 250_000
const DEFAULT_MAX_LP2_CONJ_NODES = 100_000

# ---------------------------------------------------------------------------
#  Rank-growth sampling cap (diagnostic only)
# ---------------------------------------------------------------------------
const MAX_RANK_GROWTH_SAMPLES = 10_000

# ---------------------------------------------------------------------------
#  WorkerStats — per-thread counters, zeroed at construction.
# ---------------------------------------------------------------------------
mutable struct WorkerStats
    hits_total         ::Int
    hits_full          ::Int
    hits_0lp           ::Int
    hits_lp1           ::Int
    hits_lp1_conj      ::Int
    hits_1lp_emit      ::Int
    hits_1lp_conj_emit ::Int
    hits_lp2seen       ::Int
    hits_lp2emit       ::Int
    hits_lp2_cross     ::Int
    hits_lp2_odd       ::Int
    hits_lp2_cap       ::Int
    hits_skip          ::Int
    evictions_conj     ::Int
    raw_steps          ::Int
    smooth_hist        ::Vector{Int}
    rel_local          ::Int
    # 1-LP conj diagnostics
    conj_roundtrip_fail  ::Int   # insert→haskey immediately returned false (LSM bug)
    conj_toctou_loss     ::Int   # haskey=true but pop returned nothing (race)
    conj_discard_samecol ::Int   # closed but i0==prev_col
    conj_discard_zeroalbe::Int   # closed but combined_al==combined_be==0

    WorkerStats() = new(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, zeros(Int, 4), 0,
                        0, 0, 0, 0)
end
