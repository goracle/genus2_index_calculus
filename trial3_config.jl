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
#  MAX_LP1_ENTRIES: upper bound on shared_lp1 (affine LPs).  Set very high —
#    premature eviction kills relation yield by discarding stored entries
#    before their matching half arrives.  Only lower if genuinely OOM.
#
#  MAX_LP1_CONJ_ENTRIES: cap for the conjugate-pair 1-LP table.  The keyspace
#    is ~p^2, so closures are astronomically rare — storing more than O(√ell)
#    entries is wasted memory, since each lives until a closure fires (which
#    almost never happens).
# ---------------------------------------------------------------------------
const MAX_LP1_ENTRIES      = 50_000_000
const MAX_LP1_CONJ_ENTRIES = 500_000

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

struct ShardedLP1Conj
    shards ::NTuple{N_CONJ_SHARDS, Dict{NTuple{4,Int}, Tuple{Int,BigInt,BigInt,Int}}}
    locks  ::NTuple{N_CONJ_SHARDS, ReentrantLock}
end
# Value tuple layout: (col_idx::Int, neg_al::BigInt, neg_be::BigInt, raw_steps::Int)
# neg_al/neg_be are DLP exponents mod ell and can exceed 2^31 when p > 2^15.

function ShardedLP1Conj()
    shards = ntuple(_ -> Dict{NTuple{4,Int}, Tuple{Int,BigInt,BigInt,Int}}(), N_CONJ_SHARDS)
    locks  = ntuple(_ -> ReentrantLock(), N_CONJ_SHARDS)
    ShardedLP1Conj(shards, locks)
end

# Map a Mumford 4-tuple key to its shard index (1-based).
# The key holds F_p coordinates (plain Int, always < p < 2^63 on 64-bit Julia).
@inline function conj_shard_idx(key::NTuple{4,Int})
    h = key[1] ⊻ key[2] ⊻ key[3] ⊻ key[4]
    (h & (N_CONJ_SHARDS - 1)) + 1
end

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
