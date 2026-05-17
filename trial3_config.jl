# =============================================================================
#  trial3_config.jl  --  Global constants, shared data structures, and caps.
#
#  Included by trial3_fixed.jl before any other trial3_* file.
# =============================================================================

# ---------------------------------------------------------------------------
#  Relation integrity asserts
#  Set to false in production to skip Jacobian-arithmetic cross-checks.
# ---------------------------------------------------------------------------
const ASSERT_RELATIONS = false

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
#    is ~p^2 so closures are rare; steady-state occupancy is O(p) entries.
#    Cap is computed at construction as LP1_CONJ_CAP_MULTIPLIER * p — see below.
# ---------------------------------------------------------------------------
const MAX_LP1_ENTRIES         = 50_000_000
const MAX_LP1_DOUBLED_ENTRIES = 100_000

# MAX_LP1_CONJ_ENTRIES is no longer a fixed constant — it is computed at
# ShardedLP1Conj() construction time as a function of the field prime p.
#
# Theory: the conj LP key is a 4-tuple of Fp coordinates drawn from the
# Mumford representation of a degree-2 divisor over Fp².  The effective
# keyspace has size O(p²).  The birthday threshold — where a random walk
# first expects a collision — is O(√(p²)) = O(p).  Empirically at p≈131K
# steady-state occupancy is ~8p entries (observed ~1.06M ≈ 8×131101).
#
# We use a multiplier of 16 so the cap is generous (never evicts prematurely)
# while staying proportional to actual memory need at any field size:
#   p=16K   → cap ≈  262K entries ≈   21 MB
#   p=131K  → cap ≈  2.1M entries ≈  168 MB
#   p=1M    → cap ≈   16M entries ≈  1.3 GB
#
# NO sizehint! is used — Dicts grow on demand.  The cap only controls eviction.
const LP1_CONJ_CAP_MULTIPLIER = 16

# ---------------------------------------------------------------------------
#  Sharded conjugate-pair 1-LP table
#
#  The conjugate table is keyed by 4-tuple Mumford coordinates and shared
#  across all walker threads.  A single lock would be a contention bottleneck;
#  we instead shard into N_CONJ_SHARDS independent Dict+lock pairs and route
#  each key to its shard via XOR folding.  N_CONJ_SHARDS must be a power of 2
#  for the cheap mask operation in conj_shard_idx.
# ---------------------------------------------------------------------------
const N_CONJ_SHARDS = 64

# Compact value type for conjugate 1-LP entries.
# Fields use the smallest unsigned type that fits their range:
#   i0     — FB column index, max ~O(√p) ≈ 10^4 at p=10^8, fits UInt16 (max 65535).
#   neg_al — exponent mod ell.  ell is the large prime factor of #J ≈ p²,
#            so ell can be up to ~p² ≈ 10^16 at p=10^8.  Requires UInt64.
#   neg_be — same range as neg_al.
#   (Mumford key coordinates are mod p < 2^27 at p=10^8, fit in UInt32.)
struct LP1ConjVal
    i0     ::UInt16   # FB column index  (max nF ≈ √p ≪ 65535)
    neg_al ::UInt64   # discrete-log component mod ell  (ell can reach ~p²)
    neg_be ::UInt64   # discrete-log component mod ell
end

struct ShardedLP1Conj
    shards  ::NTuple{N_CONJ_SHARDS, Dict{NTuple{4,UInt32}, LP1ConjVal}}
    locks   ::NTuple{N_CONJ_SHARDS, ReentrantLock}
    max_entries::Int   # total cap across all shards, computed from p at construction
end

function ShardedLP1Conj()
    # Scale cap with the field prime.  Keyspace is O(p²), birthday threshold
    # is O(p), empirical steady-state is ~8p.  Multiplier 16 gives headroom
    # without pre-allocating anything — Dicts grow on demand.
    cap = LP1_CONJ_CAP_MULTIPLIER * p
    shards = ntuple(_ -> Dict{NTuple{4,UInt32}, LP1ConjVal}(), N_CONJ_SHARDS)
    locks  = ntuple(_ -> ReentrantLock(), N_CONJ_SHARDS)
    ShardedLP1Conj(shards, locks, cap)
end

# Map a Mumford 4-tuple key to its shard index (1-based).
# Accepts both Int and UInt32 tuples — called with Int at the assignment site
# before the key is narrowed, and with UInt32 for the actual dict lookup.
@inline function conj_shard_idx(key::NTuple{4,Int})
    h = key[1] ⊻ key[2] ⊻ key[3] ⊻ key[4]
    (h & (N_CONJ_SHARDS - 1)) + 1
end
@inline function conj_shard_idx(key::NTuple{4,UInt32})
    h = Int(key[1]) ⊻ Int(key[2]) ⊻ Int(key[3]) ⊻ Int(key[4])
    (h & (N_CONJ_SHARDS - 1)) + 1
end

# Narrow an Int Mumford key to UInt32.  All F_p coordinates satisfy 0 ≤ v < p
# and p ≤ 2^21 for our target sizes, so truncation is lossless.
@inline conj_key32(key::NTuple{4,Int}) =
    (UInt32(key[1]), UInt32(key[2]), UInt32(key[3]), UInt32(key[4]))

# ---------------------------------------------------------------------------
#  2-LP graph memory caps
#
#  These are intentionally conservative so a runaway LP graph cannot consume
#  the whole machine.  The main memory fix for LP2 growth is node pruning
#  after cycle emission (in lp2.jl); these caps are the safety net.
# ---------------------------------------------------------------------------
const DEFAULT_MAX_LP2_NODES      = 250_000
const DEFAULT_MAX_LP2_CONJ_NODES = 100_000

# ---------------------------------------------------------------------------
#  Rank-growth sampling cap (diagnostic only, not used in linear algebra)
# ---------------------------------------------------------------------------
const MAX_RANK_GROWTH_SAMPLES = 10_000

# ---------------------------------------------------------------------------
#  WorkerStats — per-thread counters, zeroed at construction.
#
#  All fields are plain Int (no atomics) because they are only written by the
#  owning thread and read only after the worker returns.
# ---------------------------------------------------------------------------
mutable struct WorkerStats
    hits_total    ::Int   # phi steps that produced a valid residual
    hits_full     ::Int   # full relations emitted (0-LP + 1-LP closures + 2-LP closures)
    hits_0lp      ::Int   # pure factor-base relations
    hits_lp1      ::Int   # phi steps with exactly one large prime (before closure)
    hits_1lp_emit ::Int   # 1-LP closures that produced a full relation
    hits_lp2seen  ::Int   # phi steps with exactly two large primes
    hits_lp2emit  ::Int   # 2-LP cycles that produced a full relation
    hits_lp2_cross::Int   # 2-LP steps resolved via existing 1-LP entry (cross-close)
    hits_lp2_odd  ::Int   # 2-LP odd-cycle events (stored in lp_doubled or cross-closed)
    hits_lp2_cap  ::Int   # 2-LP steps dropped because LP2 graph was at capacity
    hits_skip     ::Int   # phi steps with ≥3 large primes (discarded)
    raw_steps     ::Int   # total walk iterations (including non-smooth)
    smooth_hist   ::Vector{Int}  # histogram: smooth_hist[k+1] = count of k-LP steps
    rel_local     ::Int   # relations collected by this thread (for logging)

    WorkerStats() = new(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, zeros(Int, 4), 0)
end
