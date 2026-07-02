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
#    is ~p^2 so closures are rare; steady-state occupancy is O(ell).
#    Cap is computed at construction as LP1_CONJ_CAP_MULTIPLIER * ell.
# ---------------------------------------------------------------------------
const MAX_LP1_ENTRIES         = 50_000_000
const MAX_LP1_DOUBLED_ENTRIES = 100_000

# CONJ_ROW_STORE_CAP_BASE — REMOVED.
# The per-thread conj_row_store Dict has been eliminated.  Anchor FB indices
# are now stored directly in LP1ConjVal.anchor_indices (NTuple{K_MAX,UInt16}) and
# reconstructed at close time via _unpack_anchor_row(), so no side-channel is
# needed and row_missing drops no longer occur.

# MAX_LP1_CONJ_ENTRIES is no longer a fixed constant — it is computed at
# ShardedLP1Conj(ell) construction time.
#
# Theory: the conj LP key is a 4-tuple of F_p coordinates from the Mumford
# representation of a degree-2 residual over F_p².  Although the full Mumford
# keyspace has size O(p²), the walk only produces residuals whose group order
# divides ell (the large prime factor of #J).  The number of distinct conj LP
# keys the walk can encounter is therefore O(ell) — bounded by the size of
# the order-ell subgroup itself, independent of p.
#
# CORRECTED (was min(ell, p), which is basic-genus-2-theory wrong): an
# order-ell subgroup element doesn't care how big p is. The old min(ell, p)
# bound only happened to work when ell ≲ p (e.g. p=13M, ell=196K from a
# highly composite #J, where using p as the cap would have allocated a
# needless 209M-entry table). But whenever ell exceeds p — the common case
# for a near-prime #J ≈ p² — min(ell, p) silently truncates the cap to p,
# which is far below the true O(ell) reachable keyspace. That under-cap
# causes exactly the "early productivity then hard stagnation" failure
# mode: the table fills to its (wrongly small) cap, and every insert past
# that point is silently dropped rather than spilled, freezing the birthday
# paradox that index-calculus relation-finding depends on. Using ell keeps
# the cap correct in both regimes; LP1_CONJ_CAP_MAX below remains the real
# backstop against OOM.
#
# Empirical (ORIGINAL calibration, multiplier=16): at p≈131K, ell≈p,
# steady-state ≈ 8·ell (ell≈p here, so the old and corrected formulas
# coincide numerically for this measurement). These numbers were measured
# before four
# upstream pipeline bugs were fixed (anchor-tuple cursor hang, EEA remainder
# clobber, EEA zero-length-remainder underflow, negative-coordinate/SENTINEL_PT
# leaks) — at the time, phi_val was ~0% and the walk essentially never reached
# the LP1-conj emission path, so true steady-state occupancy under a working
# walk was never actually observed. With those bugs fixed (phi_val≈99.9%),
# a real run emits ~5.75M LP1-conj candidates in 30s against this table,
# vastly exceeding what multiplier=16 provisions — 100% of post-cap inserts
# were silently dropped (not spilled) once the cap was hit. Multiplier raised
# to 256 to give real headroom against the fixed pipeline's actual throughput;
# LP1_CONJ_CAP_MAX below is untouched and remains the real backstop. The
# regimes table is left as historical reference, not a current guarantee:
#   ell≈p=16K   → cap ≈  262K entries ≈    4 MB  (was ~5 MB with Dict)
#   ell≈p=131K  → cap ≈  2.1M entries ≈   27 MB  (was ~36 MB)
#   ell≈p=1.3M  → cap ≈   21M entries ≈  273 MB  (was ~360 MB)
#   ell=196K, p=13M → cap ≈ 3.1M entries ≈   40 MB  (was ~53 MB, was 209M → OOM)
#
const LP1_CONJ_CAP_MULTIPLIER = 256
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
const N_CONJ_SHARDS   = 64
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
#    LP1ConjVal     (16 bytes): anchor_indices(4) + store_step(4) + neg_al(8)
#    LP1ConjValFull (24 bytes): anchor_indices(4) + store_step(4) + neg_al(8) + neg_be(8)
#
#  anchor_indices — NTuple{K_MAX,UInt16} holding the FB indices of the K
#    anchor points used to build the φ function for this partial, one slot
#    per multiplicity unit (a tangency with count m fills m slots with the
#    same index).  Unused trailing slots hold ANCHOR_IDX_NONE (0xffff).
#    FB size is bounded by 20_000 < 65535 so UInt16 is always sufficient.
#
#    Storing the anchors IN the val eliminates both the hot_rows side-channel
#    (LP1ConjLSM) and the per-thread conj_row_store (phase2_worker).  The
#    stored fb_row is reconstructed at close time from anchor_indices without
#    any additional Dict lookups, and disk-resident entries can be closed just
#    as well as hot entries — no more row_missing drops.
#
#    The K_MAX UInt16 slots are also serialised into the on-disk record as
#    K_MAX consecutive 2-byte fields starting at OFF_I0 (see
#    lp1_conj_lsm_constants.jl for the full layout).
#
#  store_step -- inserting thread's raw_step truncated to UInt32 (~4B steps
#                max).  Used by D8 closure-depth diagnostic.  Serialised
#                into the OFF_STEP field of the on-disk record.
#  neg_al     -- exponent mod ell.  ell <= #J ~= p^2, fits UInt64 for p<2^32.
#  neg_be     -- same range; omitted in amortized mode (always 0).
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  K_MAX — maximum number of anchor FB indices stored per LP1-conj partial.
#
#  Set this to the largest K you intend to use (i.e. the largest anchor tuple
#  size passed to step_phi_k / handle_1lp_conj!).  Increasing K_MAX by 1
#  costs 2 bytes per on-disk record and 2 bytes per hot-table value entry;
#  there is no other overhead.  Recompile after changing.
#
#  Supported range: K_MAX ≥ 1.  K=1 (single anchor) is the default and most
#  common case.  K=2 covers two-anchor φ construction.  Higher K is supported
#  without any code change — just increase this constant.
# ---------------------------------------------------------------------------
const K_MAX = 6   # ← user-configurable; set to max K you will use

const ANCHOR_IDX_NONE = UInt16(0xffff)   # sentinel: unused slot in anchor_indices

struct LP1ConjVal          # amortized mode
    anchor_indices ::NTuple{K_MAX,UInt16}
    store_step     ::UInt32
    neg_al         ::UInt64
end

struct LP1ConjValFull      # single-shot mode
    anchor_indices ::NTuple{K_MAX,UInt16}
    store_step     ::UInt32
    neg_al         ::UInt64
    neg_be         ::UInt64
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
    cap = min(LP1_CONJ_CAP_MULTIPLIER * Int(ell), LP1_CONJ_CAP_MAX)
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

# Pack fb_row (Dict{Int,Int}, key=FB index, value=multiplicity) into a
# NTuple{K_MAX,UInt16}.  One slot is filled per multiplicity unit — a
# tangency with count m fills m consecutive slots with the same index.
# Slots are filled in ascending key order for a canonical encoding.
# Remaining slots (if total multiplicity < K_MAX) are padded with
# ANCHOR_IDX_NONE.  Total multiplicity must not exceed K_MAX (caller's
# K choice must respect K_MAX).
@inline function _pack_anchor_indices(fb_row::Dict{Int,Int})::NTuple{K_MAX,UInt16}
    isempty(fb_row) && return ntuple(_ -> ANCHOR_IDX_NONE, K_MAX)
    buf = fill(ANCHOR_IDX_NONE, K_MAX)
    pos = 1
    for k in sort!(collect(keys(fb_row)))
        m = fb_row[k]
        @assert pos + m - 1 <= K_MAX "total anchor multiplicity exceeds K_MAX=$K_MAX"
        uk = UInt16(k)
        for _ in 1:m
            buf[pos] = uk
            pos += 1
        end
    end
    return NTuple{K_MAX,UInt16}(buf)
end

# Reconstruct the fb_row Dict from stored anchor_indices.  Walks the tuple
# until it hits the first ANCHOR_IDX_NONE (slots are always filled
# contiguously from the front by _pack_anchor_indices, so the first NONE
# marks the end), accumulating per-index counts.
@inline function _unpack_anchor_row(ai::NTuple{K_MAX,UInt16})::Dict{Int,Int}
    row = Dict{Int,Int}()
    for a in ai
        a == ANCHOR_IDX_NONE && break
        row[Int(a)] = get(row, Int(a), 0) + 1
    end
    return row
end

@inline _conj_make_val(::Type{LP1ConjVal},     fb_row::Dict{Int,Int}, step::UInt32, al::UInt64, be::UInt64) =
    LP1ConjVal(_pack_anchor_indices(fb_row), step, al)
@inline _conj_make_val(::Type{LP1ConjValFull}, fb_row::Dict{Int,Int}, step::UInt32, al::UInt64, be::UInt64) =
    LP1ConjValFull(_pack_anchor_indices(fb_row), step, al, be)
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
    # phi_attempts counts steps that cleared gate 1 (D degree-2) and gate 2
    # (no anchor in supp(D)) and therefore actually invoked build_phi_mumford/
    # step_phi_k!.  hits_total/phi_attempts is the TRUE phi-construction
    # success rate.  hits_total/raw_steps (the old "phi-valid rate") also
    # bakes in rejections from the alpha-dedup Bloom filter gate
    # (phase2_alpha_first_seen!), which grows monotonically over a run's
    # duration independent of anything phi-related. Diffing the two rates
    # isolates real phi/jac_add-side degradation from that expected,
    # unrelated gate effect.
    phi_attempts       ::Int
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
    # Trivial-close breakdown (Gemini hypothesis instrumentation):
    hits_1lp_conj_trivial_same_col  ::Int   # closed but fb_row matches stored (filtered by construction)
    hits_1lp_conj_trivial_zero_dal  ::Int   # closed but Δα=Δβ=0, fb_row differs (should be ~0:
                                             # excluded by global alpha-uniqueness gate)
    hits_1lp_conj_trivial_dup       ::Int   # closed, Δα/Δβ nonzero, but (lo,hi,canon_al,canon_be)
                                             # already emitted by this thread — exact-duplicate
                                             # weight-2 row, dropped. NOT the same condition as
                                             # hits_1lp_conj_trivial_zero_dal; was previously
                                             # double-counted into that field.
    hits_1lp_conj_row_missing       ::Int   # closed (hot or disk hit), but prev fb_row unrecoverable
                                             # (disk-spilled entry with no hot_rows record, or
                                             #  cross-thread close against already-evicted row).
                                             # Close is dropped; NOT a Δα=0 event.
    # Same-col sub-breakdown: attractor (same walk path) vs birthday (different path, same anchor):
    hits_1lp_conj_attractor_exact   ::Int   # same_col AND Δα=0 → genuine walk loop
    hits_1lp_conj_attractor_birthday::Int   # same_col BUT Δα≠0 → birthday, anchor just happened to match

    # Leading 0 is the new phi_attempts field.
    WorkerStats() = new(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, zeros(Int, 4), 0,
                        0, 0, 0, 0, 0, 0, 0, 0)
end
