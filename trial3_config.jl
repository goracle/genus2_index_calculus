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
#   ell≈p=16K   → cap ≈  262K entries ≈    2 MB  (was ~5 MB with Dict)
#   ell≈p=131K  → cap ≈  2.1M entries ≈   21 MB  (was ~36 MB)
#   ell≈p=1.3M  → cap ≈   21M entries ≈  168 MB  (was ~360 MB)
#   ell=196K, p=13M → cap ≈ 3.1M entries ≈   25 MB  (was ~53 MB, was 209M → OOM)
#
const LP1_CONJ_CAP_MULTIPLIER = 16
# Hard ceiling regardless of p/ell — prevents catastrophic over-allocation.
# 2M entries ≈ 16 MB with the flat table (was ~160 MB with Dict).
const LP1_CONJ_CAP_MAX = 20_000_000

# ---------------------------------------------------------------------------
#  Sharded conjugate-pair 1-LP table
#
#  Each shard is a flat open-addressing hash table over two parallel Vectors:
#    shard_keys[i]  ::NTuple{4,UInt32}   — the Mumford 4-tuple key
#    shard_vals[i]  ::LP1ConjVal         — the stored value
#
#  A sentinel key (all UInt32 max) marks empty slots.
#  We target 80% max load (keys_per_shard = cap_per_shard × LOAD_DENOM ÷ LOAD_NUM).
#
#  This replaces the previous Dict{NTuple{4,UInt32}, LP1ConjVal} per shard.
#  Benefits:
#    • No GC tracking of individual entries — the Vectors are plain blobs.
#    • No per-entry slot byte + pointer indirection from Dict's open-addressing.
#    • Cache-sequential access: key probe touches a contiguous UInt32 array.
#    • Memory per entry: 16 (key) + 10 (val, amortized) = 26 bytes at 80% load
#      → 32.5 effective bytes/entry, vs ~100–120 bytes/entry for Dict.
#      That is a 3–4× reduction.
#
#  N_CONJ_SHARDS must be a power of 2 for the cheap mask in conj_shard_idx.
# ---------------------------------------------------------------------------
const N_CONJ_SHARDS    = 64
const CONJ_LOAD_NUM    = 4    # max load = LOAD_NUM / LOAD_DENOM = 80%
const CONJ_LOAD_DENOM  = 5

# Sentinel: marks an empty slot in the flat key array.
const CONJ_KEY_EMPTY = (typemax(UInt32), typemax(UInt32), typemax(UInt32), typemax(UInt32))

# ---------------------------------------------------------------------------
#  LP1ConjVal — value stored in the conj 1-LP table.
#
#  Amortized mode (beta_zero=true): neg_be is always 0 — drop the field
#  entirely.  Use LP1ConjVal (10 bytes) in amortized mode and LP1ConjValFull
#  (18 bytes) in single-shot mode.
#
#  i0     — FB column index, max ~O(√p) ≈ 10^4 at p=10^8, fits UInt16.
#  neg_al — exponent mod ell.  ell ≤ #J ≈ p², so ell < 2^64 for p < 2^32.
#           Requires UInt64.
#  neg_be — same range; omitted in LP1ConjVal (amortized) since it's always 0.
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
#  ConjShard — one shard of the flat open-addressing table.
#
#  Layout: parallel arrays keys[1..cap] and vals[1..cap].
#  Empty slots have keys[i] == CONJ_KEY_EMPTY.
#  count tracks live entries for cap enforcement.
#  cap = length(keys) = the allocated slot count (always a power of 2 so that
#  the probe step h = hash & (cap-1) is a single mask).
# ---------------------------------------------------------------------------
mutable struct ConjShard{V}
    keys  ::Vector{NTuple{4,UInt32}}
    vals  ::Vector{V}
    count ::Int
    cap   ::Int   # == length(keys), always a power of 2
    mask  ::UInt  # == cap - 1
    max_entries::Int  # live-entry cap (eviction threshold)
end

function ConjShard{V}(cap_entries::Int) where V
    # Round cap up to next power of 2 so mask works.
    # Allocate enough slots for 80% load.
    slot_count = max(16, nextpow(2, cld(cap_entries * CONJ_LOAD_DENOM, CONJ_LOAD_NUM)))
    keys = fill(CONJ_KEY_EMPTY, slot_count)
    vals = Vector{V}(undef, slot_count)
    ConjShard{V}(keys, vals, 0, slot_count, UInt(slot_count - 1), cap_entries)
end

# ---------------------------------------------------------------------------
#  Flat open-addressing primitives for ConjShard.
#
#  Hash function: XOR-fold the four UInt32 coords, then apply a finalizer.
#  Linear probing is used (simplest; cache-friendly for our load factors).
# ---------------------------------------------------------------------------

@inline function _conj_slot_hash(key::NTuple{4,UInt32}, mask::UInt)::Int
    h = UInt(key[1]) ⊻ UInt(key[2]) ⊻ UInt(key[3]) ⊻ UInt(key[4])
    # Finalizer borrowed from FNV/murmur style — reduces clustering on
    # arithmetic sequences of Mumford coordinates.
    h = h ⊻ (h >> 16)
    h = h * 0x45d9f3b37197344d % UInt64
    h = h ⊻ (h >> 16)
    Int(h & mask) + 1   # 1-based
end

# Returns the slot index of key if present, or 0 if absent.
@inline function _conj_find(shard::ConjShard, key::NTuple{4,UInt32})::Int
    cap  = shard.cap
    mask = shard.mask
    keys = shard.keys
    slot = _conj_slot_hash(key, mask)
    @inbounds while true
        k = keys[slot]
        k === key          && return slot
        k === CONJ_KEY_EMPTY && return 0
        slot = slot & cap == cap ? 1 : slot + 1  # wrap: if slot==cap → 1
    end
end

# Insert key→val.  Caller must have verified count < max_entries and that
# key is not already present.  Does not check for duplicates.
@inline function _conj_insert!(shard::ConjShard{V}, key::NTuple{4,UInt32}, val::V) where V
    cap  = shard.cap
    mask = shard.mask
    keys = shard.keys
    vals = shard.vals
    slot = _conj_slot_hash(key, mask)
    @inbounds while keys[slot] !== CONJ_KEY_EMPTY
        slot = slot & cap == cap ? 1 : slot + 1
    end
    @inbounds keys[slot] = key
    @inbounds vals[slot] = val
    shard.count += 1
    nothing
end

# Delete the entry at a known slot (from _conj_find).  Uses backward-shift
# deletion to maintain the linear-probe invariant without tombstones.
@inline function _conj_delete_slot!(shard::ConjShard, slot::Int)
    cap  = shard.cap
    keys = shard.keys
    vals = shard.vals
    mask = shard.mask
    @inbounds keys[slot] = CONJ_KEY_EMPTY
    shard.count -= 1
    # Backward-shift deletion for linear probing (1-based indices, cap = power of 2).
    #
    # Invariant: after we empty slot `cur`, we check the next slot `nxt = cur mod cap + 1`.
    # If keys[nxt] is not empty, it may have been pushed there by a collision that
    # originally wanted a slot ≤ cur.  We move it back to `cur` if its natural
    # slot `nat` does NOT lie in the open interval (cur, nxt] cyclically — i.e.
    # if `nat` would have probed through `cur` on the way to `nxt`, then emptying
    # `cur` breaks its chain and we must pull it back.
    #
    # Displacement condition (all indices 1-based, range [1..cap]):
    #   If nat == nxt: not displaced (it's already at its natural slot).
    #   Otherwise: cur lies in [nat, nxt) cyclically
    #     ≡  (nat <= cur) XOR (nxt < nat)     [standard circular-interval test]
    cur = slot
    @inbounds while true
        nxt = cur == cap ? 1 : cur + 1
        keys[nxt] === CONJ_KEY_EMPTY && break
        nat = _conj_slot_hash(keys[nxt], mask)
        # Circular interval: nat ∈ (cur, nxt] means NOT displaced.
        # Equivalently displaced iff nat NOT in (cur, nxt] cyclically.
        # (cur, nxt] cyclically = {nxt} since nxt = cur+1 (or wrap).
        # So: displaced iff nat != nxt AND nat is in [nat_wrap ... cur]:
        displaced = nat != nxt && ((nat <= cur) != (nxt <= cur))
        # Simplified: since nxt = cur+1 or 1:
        # • nxt = cur+1 (no wrap): (cur,nxt] = {nxt}; displaced iff nat ≠ nxt ∧ nat ≤ cur
        # • nxt = 1 (wrap):        (cur,nxt] = {1};   displaced iff nat ≠ 1 ∧ nat > cur
        # Both cases covered by: displaced = (nat != nxt) && (nxt == 1 ? nat > cur : nat <= cur)
        displaced = if nxt == 1
            nat != 1 && nat > cur
        else
            nat != nxt && nat <= cur
        end
        if displaced
            keys[cur] = keys[nxt]
            vals[cur] = vals[nxt]
            keys[nxt] = CONJ_KEY_EMPTY
            cur = nxt
        else
            break
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

# Route a key to its shard index (1-based).
@inline function conj_shard_idx(key::NTuple{4,Int})::Int
    h = key[1] ⊻ key[2] ⊻ key[3] ⊻ key[4]
    (h & (N_CONJ_SHARDS - 1)) + 1
end
@inline function conj_shard_idx(key::NTuple{4,UInt32})::Int
    h = Int(key[1]) ⊻ Int(key[2]) ⊻ Int(key[3]) ⊻ Int(key[4])
    (h & (N_CONJ_SHARDS - 1)) + 1
end

# Narrow an Int Mumford key to UInt32.
@inline conj_key32(key::NTuple{4,Int}) =
    (UInt32(key[1]), UInt32(key[2]), UInt32(key[3]), UInt32(key[4]))

# Total live entries across all shards (for reporting).
function conj_total_entries(sc::ShardedLP1Conj)::Int
    s = 0
    for sh in sc.shards; s += sh.count; end
    s
end

# Lookup: returns the slot index (>0) if found, 0 otherwise.
# Caller must hold the shard lock.
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

    WorkerStats() = new(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, zeros(Int, 4), 0)
end
