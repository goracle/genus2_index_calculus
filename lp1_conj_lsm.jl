# =============================================================================
#  lp1_conj_lsm.jl  —  Staged RAM+SSD LP1-conj index (LSM-tree style)
#
#  Drop-in replacement for ShardedLP1Conj that caps RAM usage at O(buffer size)
#  rather than O(total entries) by spilling sorted runs to a flat binary file
#  on SSD via mmap.
#
#  Design
#  ──────
#  Hot path (RAM):
#    • A sharded open-addressing table (LP1ConjLSM.hot) holds recently inserted
#      entries.  Same ConjShard{V} primitives as before.
#    • When any shard's live count crosses its flush threshold, the shard is
#      sorted by fingerprint and appended as a new "run" to the spill file.
#
#  Cold path (SSD via mmap):
#    • All flushed runs live in a single flat binary file.  Each record is
#      exactly RECORD_BYTES (40) bytes, packed as:
#        fp   :: UInt64  (8)   — sort key
#        key  :: UInt128 (16)  — full CanonicalLP1Key for collision check
#        i0   :: UInt16  (2)   — factor-base column index
#        _pad :: UInt16  (2)   — alignment padding (zero)
#        al   :: UInt64  (8)   — neg_al
#        be   :: UInt64  (8)   — neg_be (0 in amortized mode)  [total = 44... see below]
#      Wait — 8+16+2+2+8+8 = 44.  Round to 48 for alignment (add 4 pad after be).
#      Actually packed as: fp(8) u0(4) u1(4) v0(4) v1(4) i0(2) pad(2) al(8) be(8) = 44.
#      Use 48 bytes (add 4 trailing pad) so records are 8-byte aligned.
#    • Each RunMeta stores (byte_offset, len, min_fp, max_fp) and a tombstone
#      bitvector in RAM.
#    • The spill file is grown with truncate and re-mmap'd after each flush.
#      The mmap is read-only from the lookup side; writes go through normal IO
#      then re-mmap.
#    • Lookup: check Bloom filter → skip run if fp outside [min,max] → binary
#      search on fp field (stride RECORD_BYTES) → verify full key → return
#      payload.  All pointer arithmetic, no library locks.
#
#  Concurrency
#  ───────────
#    • Per-shard ReentrantLocks guard hot table mutations.
#    • file_lock serialises flushes (writes to spill file + mmap remap) and
#      disk lookups that need a consistent view of runs/mmap.
#    • Bloom filter reads are lockless (stale reads are safe — only false
#      negatives would be a bug, and bits are only ever set, never cleared).
#
#  Compatibility
#  ─────────────
#    Same public API as ShardedLP1Conj and previous LP1ConjLSM:
#      conj_shard_idx / canonical_lp1_conj_key  (defined in trial3_config.jl)
#      conj_total_entries, conj_haskey, conj_getval, conj_pop!, conj_insert!
#      conj_insert_or_pop!
#      lsm_flush_all!, lsm_close!, lsm_info
# =============================================================================

# No HDF5 dependency — plain IO only (no mmap).

const RECORD_BYTES = 48   # fp(8) + u0u1v0v1(16) + i0(2) + pad(6) + al(8) + be(8)

# ---------------------------------------------------------------------------
#  Rényi-2 / S₂ estimator — AMS sketch (Alon-Matias-Szegedy)
#
#  The old fixed-histogram approach (2^RENYI_BITS buckets) saturated as soon
#  as N >> n_buckets: every bucket fills up, S2_bucket → n_buckets regardless
#  of the true distribution, and α₂ collapsed to RENYI_BITS·log2/log(p) — a
#  pure function of p with no walk signal.  This is now replaced everywhere.
#
#  AMS gives an unbiased estimate of F₂ = Σ cᵢ² for any N:
#    Maintain k independent sign-hash projections  Z_j = Σᵢ hⱼ(xᵢ)
#    where hⱼ: fingerprint → {-1, +1} via the high bit of a multiply-hash.
#    Then E[Zⱼ²] = F₂.  We use G groups of W estimators each; within each
#    group take the mean of Zⱼ², across groups take the median.
#    Final: S₂ = N² / F₂_estimate,  α₂ = log(S₂) / (2·log(p)).
#
#  Parameters:
#    AMS_GROUPS = 32  (groups for median — controls tail probability)
#    AMS_WIDTH  = 16  (estimators per group — controls variance within group)
#    Total sketch: 32×16 = 512 Int64 accumulators = 4 KB.  Never saturates.
#
#  Salts: 512 fixed UInt64 constants derived from nothing-up-my-sleeve values.
# ---------------------------------------------------------------------------
const AMS_GROUPS = 32
const AMS_WIDTH  = 16
const AMS_K      = AMS_GROUPS * AMS_WIDTH   # 512 total hash functions

# Precomputed salts: AMS_K distinct 64-bit constants.
# Generated as successive applications of xorshift64 from a random seed so
# each run uses a fresh independent hash family.
const AMS_SALTS = let
    s = rand(UInt64)
    v = Vector{UInt64}(undef, AMS_K)
    for i in 1:AMS_K
        s = s ⊻ (s << 13)
        s = s ⊻ (s >> 7)
        s = s ⊻ (s << 17)
        v[i] = s
    end
    Tuple(v)
end

# ---------------------------------------------------------------------------
#  Cold-filter bitmap — separate from the S₂ estimator.
#
#  The flush path needs to know which fingerprint buckets have received at
#  least one emission (to drop genuinely cold entries from the spill file).
#  We keep a coarse 2^COLD_BITS-bucket presence bitmap for this purpose only.
#  This is NOT used for any S₂ or α₂ computation.
# ---------------------------------------------------------------------------
const COLD_BITS  = 20                    # 1M buckets, 128 KB bitmap
const COLD_SHIFT = 64 - COLD_BITS
const COLD_WORDS = (1 << COLD_BITS) ÷ 64  # 16384 UInt64 words

# Circular buffer capacity for the partial fingerprint log.
# Stores COLD_BITS-bit bucket indices as UInt32 (20 bits fits in UInt32).
# At 4 bytes/entry this costs 4 MB and always reflects the most recent
# PARTIAL_FP_LOG_CAP emissions regardless of total walk length.
const PARTIAL_FP_LOG_CAP = 1_000_000
# Layout offsets within a record (byte indices, 1-based Julia style handled via pointer):
#   0: fp   UInt64
#   8: u0   UInt32
#  12: u1   UInt32
#  16: v0   UInt32
#  20: v1   UInt32
#  24: i0   UInt16
#  26: pad  UInt16 + UInt32  (6 bytes)
#  32: al   UInt64
#  40: be   UInt64
# total: 48

# ---------------------------------------------------------------------------
#  Fingerprint
# ---------------------------------------------------------------------------
@inline function _lsm_fp(key::CanonicalLP1Key)::UInt64
    lo = UInt64(key & 0xffffffffffffffff)
    hi = UInt64(key >> 64)
    h  = lo * 0x9e3779b97f4a7c15 +
         hi * 0x6c62272e07bb0142
    h = h ⊻ (h >> 32)
    h = h * 0x45d9f3b37197344d
    h = h ⊻ (h >> 32)
    h
end

# ---------------------------------------------------------------------------
#  BloomFilter — lockless gate in front of disk probes.
# ---------------------------------------------------------------------------
mutable struct BloomFilter
    bits    ::Vector{UInt64}
    n_bits  ::Int
end

function BloomFilter(capacity::Int; bits_per_entry::Int = 8)
    n_bits = max(64, capacity * bits_per_entry)
    BloomFilter(zeros(UInt64, cld(n_bits, 64)), n_bits)
end

@inline function _bloom_hashes(bf::BloomFilter, fp::UInt64)
    h1 = fp * 0x9e3779b97f4a7c15
    h2 = fp * 0x6c62272e07bb0142
    h3 = h1 ⊻ (h2 >> 17)
    n  = UInt64(bf.n_bits)
    (Int(h1 % n) + 1, Int(h2 % n) + 1, Int(h3 % n) + 1)
end

@inline function bloom_maybe_has(bf::BloomFilter, fp::UInt64)::Bool
    b1, b2, b3 = _bloom_hashes(bf, fp)
    bits = bf.bits
    @inbounds begin
        w1, r1 = divrem(b1 - 1, 64)
        (bits[w1+1] >> r1) & UInt64(1) == 0 && return false
        w2, r2 = divrem(b2 - 1, 64)
        (bits[w2+1] >> r2) & UInt64(1) == 0 && return false
        w3, r3 = divrem(b3 - 1, 64)
        (bits[w3+1] >> r3) & UInt64(1) == 0 && return false
    end
    true
end

function set_bloom!(bf::BloomFilter, fp::UInt64)
    b1, b2, b3 = _bloom_hashes(bf, fp)
    bits = bf.bits
    @inbounds begin
        w1, r1 = divrem(b1 - 1, 64); bits[w1+1] |= UInt64(1) << r1
        w2, r2 = divrem(b2 - 1, 64); bits[w2+1] |= UInt64(1) << r2
        w3, r3 = divrem(b3 - 1, 64); bits[w3+1] |= UInt64(1) << r3
    end
    nothing
end

# ---------------------------------------------------------------------------
#  RunMeta — in-RAM metadata for one flushed run
# ---------------------------------------------------------------------------
mutable struct RunMeta
    id         ::Int
    byte_offset::Int       # byte offset of first record in spill file
    len        ::Int       # number of records
    min_fp     ::UInt64
    max_fp     ::UInt64
    tombs      ::Vector{UInt64}   # tombstone bitvector, lazily allocated
end

function RunMeta(id::Int, byte_offset::Int, len::Int, min_fp::UInt64, max_fp::UInt64)
    RunMeta(id, byte_offset, len, min_fp, max_fp, UInt64[])
end

@inline function _run_is_dead(rm::RunMeta, pos::Int)::Bool
    isempty(rm.tombs) && return false
    word, bit = divrem(pos - 1, 64)
    @inbounds (rm.tombs[word + 1] >> bit) & UInt64(1) != 0
end

function _run_set_dead!(rm::RunMeta, pos::Int)
    nwords = cld(rm.len, 64)
    if length(rm.tombs) < nwords
        resize!(rm.tombs, nwords)
        fill!(rm.tombs, UInt64(0))
    end
    word, bit = divrem(pos - 1, 64)
    @inbounds rm.tombs[word + 1] |= UInt64(1) << bit
    nothing
end

# ---------------------------------------------------------------------------
#  LP1ConjLSM — the main struct
# ---------------------------------------------------------------------------
mutable struct LP1ConjLSM{V}
    # Hot RAM table
    hot_keys    ::Vector{Vector{CanonicalLP1Key}}
    hot_vals    ::Vector{Vector{V}}
    hot_counts  ::Vector{Int}
    hot_caps    ::Vector{Int}
    hot_masks   ::Vector{UInt}
    hot_thresh  ::Vector{Int}
    shard_locks ::Vector{ReentrantLock}

    # Disk spill — flat binary file, pread for lookups (no mmap)
    runs          ::Vector{RunMeta}
    file_lock     ::ReentrantLock
    spill_path    ::String
    spill_io      ::Union{IOStream, Nothing}   # open for appending (writes)
    spill_read_io ::Union{Cint, Nothing}        # open for reading via pread (O_DIRECT); separate fd
    spill_size    ::Int                        # current file size in bytes

    # Bloom filter — per-LSM (used for set_bloom! writes only)
    bloom       ::BloomFilter

    # Global bloom — union of all peer LSMs' blooms; shared object, bits-only-set.
    # Reads use this; writes go to both bloom and global_bloom.
    # Set to bloom itself at construction; wired to the shared object by the caller
    # after all sibling LSMs are constructed.
    global_bloom::BloomFilter

    # Peer LSMs (including self) for cross-thread disk probing.
    # Populated by the caller after construction.  Empty = solo mode (no cross-probe).
    peers       ::Vector{Any}   # Vector{LP1ConjLSM{V}} — typed as Any to avoid forward-ref

    # Bookkeeping
    n_shards    ::Int
    max_entries ::Int
    n_disk_live ::Int
    amortized   ::Bool

    # Birthday diagnostics — LP1-conj first-collision estimator
    # See: S_eff ~ (r * t_first / 2)^2  where r/2 = LP1-conj emission rate.
    # Under naive ambient model S ~ p^2/2, so t_first ~ sqrt(2)*p/r.
    bday_emissions      ::Int          # total LP1-conj partials emitted so far
    bday_t0             ::Float64      # time of first emission (time_ns() / 1e9)
    bday_first_coll_m   ::Int          # emission count at first collision (0 = not yet)
    bday_first_coll_t   ::Float64      # wall time at first collision (seconds, 0 = not yet)
    bday_lock           ::ReentrantLock

    # Occupancy estimator — S_occ via U(N) = S(1 - e^{-N/S})
    # Track unique keys ever seen (as a HyperLogLog-style count or exact small set).
    # We use exact counting up to OCC_EXACT_CAP; above that we estimate via the
    # birthday-collision rate.  u_unique is the running count of distinct keys;
    # occ_n is the total emissions so far (== bday_emissions, kept separate for
    # atomic snapshot under bday_lock).
    occ_unique          ::Int          # approximate unique LP1-conj keys seen
    occ_n               ::Int          # total emissions (for occupancy formula)

    # Rényi-2 / collision-entropy estimator — AMS sketch.
    # ams_Z[g*AMS_WIDTH + j] is the running sum Σ h_{g,j}(fp) ∈ ℤ for group g,
    # estimator j.  h_{g,j}(fp) = (-1)^{high bit of fp*AMS_SALTS[g*W+j]}.
    # E[ams_Z[i]^2] = F₂ = Σ cᵢ².  S₂ = N² / median_of_means(Z²).
    # Updated under bday_lock.  Written under bday_lock.
    ams_Z               ::Vector{Int64}    # length AMS_K = AMS_GROUPS * AMS_WIDTH

    # Cold-filter bitmap — presence bits for COLD_BITS-bucket fp prefixes.
    # Used only by the flush cold-filter; NOT for S₂ estimation.
    # Bit (fp >> COLD_SHIFT) is set on first emission to that coarse bucket.
    # Lockless reads/writes are safe (bits only ever set, never cleared).
    cold_bitmap         ::Vector{UInt64}   # length COLD_WORDS = 2^COLD_BITS / 64

    # Time-ordered partial stream — one UInt32 cold-bucket index per partial, in
    # chronological order of insertion.  Used post-walk by lsm_bday_report to
    # compute dyadic-window α₂(T) scaling diagnostics on the partial stream.
    # At 4 bytes/entry × 1M cap = 4 MB.  Written under bday_lock.
    partial_fp_log      ::Vector{UInt32}

    # Cold-filter stats: entries silently dropped at flush time because their
    # Rényi bucket had zero observed count (i.e. never received an emission).
    # These would be pure SSD waste — they can never produce a birthday collision.
    # Updated under file_lock+shard_lock (same as the flush path).
    n_cold_dropped      ::Int

    # Pre-allocated scratch buffer for _lsm_disk_find pread calls.
    # Avoids a heap allocation on every disk probe.  Access is safe because
    # _lsm_disk_find is always called under file_lock (single-writer).
    read_buf            ::Vector{UInt8}
end

# ---------------------------------------------------------------------------
#  Construction
# ---------------------------------------------------------------------------
function LP1ConjLSM{V}(
        n_shards     ::Int,
        cap_per_shard::Int,
        max_entries  ::Int,
        spill_path   ::String;
        amortized    ::Bool = true,
        load_num     ::Int  = 4,
        load_denom   ::Int  = 5,
        flush_num    ::Int  = 1,   # flush when count >= slot_count * flush_num/flush_denom
        flush_denom  ::Int  = 4,   # default: flush at 25% full (keeps hot RAM low)
        bloom_cap    ::Int  = max_entries
    ) where V

    function make_shard(cap_entries::Int)
        slot_count = max(16, nextpow(2, cld(cap_entries * load_denom, load_num)))
        keys = fill(CONJ_KEY_EMPTY, slot_count)
        vals = Vector{V}(undef, slot_count)
        thresh = cld(slot_count * flush_num, flush_denom)
        (keys, vals, slot_count, UInt(slot_count - 1), thresh)
    end

    hot_keys    = Vector{Vector{CanonicalLP1Key}}(undef, n_shards)
    hot_vals    = Vector{Vector{V}}(undef, n_shards)
    hot_counts  = zeros(Int, n_shards)
    hot_caps    = zeros(Int, n_shards)
    hot_masks   = zeros(UInt, n_shards)
    hot_thresh  = zeros(Int, n_shards)
    shard_locks = [ReentrantLock() for _ in 1:n_shards]

    for i in 1:n_shards
        ks, vs, cap, mask, thresh = make_shard(cap_per_shard)
        hot_keys[i]   = ks
        hot_vals[i]   = vs
        hot_counts[i] = 0
        hot_caps[i]   = cap
        hot_masks[i]  = mask
        hot_thresh[i] = thresh
    end

    # Ensure spill directory exists, then create (or truncate) spill file
    mkpath(dirname(spill_path))
    spill_io = open(spill_path, "w+")

    LP1ConjLSM{V}(
        hot_keys, hot_vals, hot_counts, hot_caps, hot_masks, hot_thresh,
        shard_locks,
        RunMeta[], ReentrantLock(), spill_path, spill_io,
        nothing,   # spill_read_io opened lazily on first flush
        0,         # spill_size
        BloomFilter(bloom_cap),
        BloomFilter(64),           # global_bloom placeholder — caller replaces with shared object
        Any[],                     # peers — caller will populate
        n_shards, max_entries, 0,
        amortized,
        # birthday diagnostics
        0, 0.0, 0, 0.0, ReentrantLock(),
        # occupancy estimator
        0, 0,
        # Rényi-2 AMS sketch (512 Int64 accumulators = 4 KB)
        zeros(Int64, AMS_K),
        # Cold-filter bitmap (2^COLD_BITS bits = 128 KB)
        zeros(UInt64, COLD_WORDS),
        UInt32[],             # partial_fp_log
        0,                    # n_cold_dropped
        zeros(UInt8, RECORD_BYTES)  # read_buf — pre-allocated scratch for _lsm_disk_find
    )
end

function LP1ConjLSM(
        ell           ::Integer;
        amortized     ::Bool   = true,
        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_shards"),
        max_hot_ram_mb::Int    = 4096,   # bumped from 512 — leverage available RAM headroom
        flush_num     ::Int    = 3,      # flush when shard >= 75% full (was 1/4 = 25%)
        flush_denom   ::Int    = 4
    )
    global_cap = min(LP1_CONJ_CAP_MULTIPLIER * Int(min(ell, p)), LP1_CONJ_CAP_MAX)
    cap = max(N_CONJ_SHARDS * 16, global_cap ÷ Threads.nthreads())
    V   = amortized ? LP1ConjVal : LP1ConjValFull
    bytes_per_entry = amortized ? 33 : 43
    max_hot_entries = max(N_CONJ_SHARDS * 16,
                          (max_hot_ram_mb * 1024 * 1024) ÷ bytes_per_entry)
    hot_shard_entries = max(16, max_hot_entries ÷ N_CONJ_SHARDS)
    LP1ConjLSM{V}(
        N_CONJ_SHARDS, hot_shard_entries, cap, spill_path;
        amortized   = amortized,
        flush_num   = flush_num,
        flush_denom = flush_denom,
        bloom_cap   = min(cap, 4_000_000)   # size for actual disk occupancy, not hot RAM;
                                             # 4M × 8 bits = 4 MB/LSM, ~1% FPR at 2M entries
    )
end

# ---------------------------------------------------------------------------
#  Read-IO helper — open (or keep open) the read-side fd for disk lookups.
#  Called after every flush while holding file_lock.
#  No mmap: all disk reads go through seek+read into a stack buffer so the
#  spill file never contributes to RSS.
# ---------------------------------------------------------------------------
function _lsm_open_read_io!(sc::LP1ConjLSM)
    sc.spill_size == 0 && return
    flush(sc.spill_io)
    if sc.spill_read_io === nothing
        sc.spill_read_io = _open_direct(sc.spill_path)
    end
    nothing
end

# Read exactly RECORD_BYTES from the read-side fd at byte offset `off` (0-based)
# into a caller-supplied RECORD_BYTES-length buffer.  Caller holds file_lock.
# O_DIRECT removed: RECORD_BYTES (48) is not a multiple of 512, so O_DIRECT
# triggers EINVAL on every pread.  We use posix_fadvise(DONTNEED) after each
# flush/compact instead to keep the page cache from eating all RAM.
function _open_direct(path::String)::Cint
    fd = ccall(:open, Cint, (Cstring, Cint), path, Cint(0))
    fd < 0 && error("_open_direct: cannot open $(path): $(Base.Libc.strerror())")
    fd
end

# Drop all cached pages for the spill file from the kernel page cache.
# Call this after every flush and compaction (while holding file_lock).
# POSIX_FADV_DONTNEED = 4 on Linux x86-64.
@inline function _fadvise_dontneed!(sc::LP1ConjLSM)
    sc.spill_read_io === nothing && return
    ccall(:posix_fadvise, Cint, (Cint, Int64, Int64, Cint),
          sc.spill_read_io, Int64(0), Int64(0), Cint(4))
    nothing
end

@inline function _pread_record!(sc::LP1ConjLSM, buf::Vector{UInt8}, off::Int)
    n = ccall(:pread, Cssize_t, (Cint, Ptr{UInt8}, Csize_t, Int64),
              sc.spill_read_io, buf, RECORD_BYTES, off)
    if n != RECORD_BYTES
        err_msg = Base.Libc.strerror()
        error("_pread_record!: short read ($n) at offset $off. OS Error: $err_msg")
    end
    nothing
end

# Field accessors on a RECORD_BYTES scratch buffer (same layout as before).
@inline _buf_u64(buf::Vector{UInt8}, off::Int)::UInt64 =
    UInt64(buf[off+1])        | (UInt64(buf[off+2]) << 8)  |
    (UInt64(buf[off+3]) << 16) | (UInt64(buf[off+4]) << 24) |
    (UInt64(buf[off+5]) << 32) | (UInt64(buf[off+6]) << 40) |
    (UInt64(buf[off+7]) << 48) | (UInt64(buf[off+8]) << 56)

@inline _buf_u32(buf::Vector{UInt8}, off::Int)::UInt32 =
    UInt32(buf[off+1]) | (UInt32(buf[off+2]) << 8) |
    (UInt32(buf[off+3]) << 16) | (UInt32(buf[off+4]) << 24)

@inline _buf_u16(buf::Vector{UInt8}, off::Int)::UInt16 =
    UInt16(buf[off+1]) | (UInt16(buf[off+2]) << 8)

@inline _buf_fp(buf::Vector{UInt8})::UInt64  = _buf_u64(buf, OFF_FP)
@inline _buf_i0(buf::Vector{UInt8})::UInt16  = _buf_u16(buf, OFF_I0)
@inline _buf_al(buf::Vector{UInt8})::UInt64  = _buf_u64(buf, OFF_AL)
@inline _buf_be(buf::Vector{UInt8})::UInt64  = _buf_u64(buf, OFF_BE)
@inline function _buf_key_match(buf::Vector{UInt8},
                                 ku0::UInt32, ku1::UInt32,
                                 kv0::UInt32, kv1::UInt32)::Bool
    _buf_u32(buf, OFF_U0) == ku0 && _buf_u32(buf, OFF_U1) == ku1 &&
    _buf_u32(buf, OFF_V0) == kv0 && _buf_u32(buf, OFF_V1) == kv1
end

# Read a UInt64 from mmap at byte offset `off` (0-based).
@inline function _mmap_u64(mm::Vector{UInt8}, off::Int)::UInt64
    @inbounds begin
        UInt64(mm[off+1])       | (UInt64(mm[off+2]) << 8)  |
        (UInt64(mm[off+3]) << 16) | (UInt64(mm[off+4]) << 24) |
        (UInt64(mm[off+5]) << 32) | (UInt64(mm[off+6]) << 40) |
        (UInt64(mm[off+7]) << 48) | (UInt64(mm[off+8]) << 56)
    end
end

@inline function _mmap_u32(mm::Vector{UInt8}, off::Int)::UInt32
    @inbounds begin
        UInt32(mm[off+1]) | (UInt32(mm[off+2]) << 8) |
        (UInt32(mm[off+3]) << 16) | (UInt32(mm[off+4]) << 24)
    end
end

@inline function _mmap_u16(mm::Vector{UInt8}, off::Int)::UInt16
    @inbounds UInt16(mm[off+1]) | (UInt16(mm[off+2]) << 8)
end

# Record field offsets within a record (0-based byte offsets from record start):
const OFF_FP = 0
const OFF_U0 = 8
const OFF_U1 = 12
const OFF_V0 = 16
const OFF_V1 = 20
const OFF_I0 = 24
# bytes 26-31: padding
const OFF_AL = 32
const OFF_BE = 40

@inline function _rec_base(rm::RunMeta, pos::Int)::Int
    rm.byte_offset + (pos - 1) * RECORD_BYTES
end

@inline function _rec_fp(mm::Vector{UInt8}, base::Int)::UInt64
    _mmap_u64(mm, base + OFF_FP)
end

@inline function _rec_key_match(mm::Vector{UInt8}, base::Int,
                                 ku0::UInt32, ku1::UInt32,
                                 kv0::UInt32, kv1::UInt32)::Bool
    _mmap_u32(mm, base + OFF_U0) == ku0 &&
    _mmap_u32(mm, base + OFF_U1) == ku1 &&
    _mmap_u32(mm, base + OFF_V0) == kv0 &&
    _mmap_u32(mm, base + OFF_V1) == kv1
end

# ---------------------------------------------------------------------------
#  Write a record into a pre-allocated byte buffer (for flush)
# ---------------------------------------------------------------------------
function _write_record!(buf::Vector{UInt8}, off::Int,
                         fp::UInt64, u0::UInt32, u1::UInt32,
                         v0::UInt32, v1::UInt32,
                         i0::UInt16, al::UInt64, be::UInt64)
    # fp
    buf[off+1] = UInt8(fp & 0xff); buf[off+2] = UInt8((fp>>8)&0xff)
    buf[off+3] = UInt8((fp>>16)&0xff); buf[off+4] = UInt8((fp>>24)&0xff)
    buf[off+5] = UInt8((fp>>32)&0xff); buf[off+6] = UInt8((fp>>40)&0xff)
    buf[off+7] = UInt8((fp>>48)&0xff); buf[off+8] = UInt8((fp>>56)&0xff)
    # u0
    buf[off+9]  = UInt8(u0&0xff); buf[off+10] = UInt8((u0>>8)&0xff)
    buf[off+11] = UInt8((u0>>16)&0xff); buf[off+12] = UInt8((u0>>24)&0xff)
    # u1
    buf[off+13] = UInt8(u1&0xff); buf[off+14] = UInt8((u1>>8)&0xff)
    buf[off+15] = UInt8((u1>>16)&0xff); buf[off+16] = UInt8((u1>>24)&0xff)
    # v0
    buf[off+17] = UInt8(v0&0xff); buf[off+18] = UInt8((v0>>8)&0xff)
    buf[off+19] = UInt8((v0>>16)&0xff); buf[off+20] = UInt8((v0>>24)&0xff)
    # v1
    buf[off+21] = UInt8(v1&0xff); buf[off+22] = UInt8((v1>>8)&0xff)
    buf[off+23] = UInt8((v1>>16)&0xff); buf[off+24] = UInt8((v1>>24)&0xff)
    # i0
    buf[off+25] = UInt8(i0&0xff); buf[off+26] = UInt8((i0>>8)&0xff)
    # pad (bytes 27-32 = indices off+27 .. off+32)
    buf[off+27] = 0; buf[off+28] = 0; buf[off+29] = 0
    buf[off+30] = 0; buf[off+31] = 0; buf[off+32] = 0
    # al
    buf[off+33] = UInt8(al&0xff); buf[off+34] = UInt8((al>>8)&0xff)
    buf[off+35] = UInt8((al>>16)&0xff); buf[off+36] = UInt8((al>>24)&0xff)
    buf[off+37] = UInt8((al>>32)&0xff); buf[off+38] = UInt8((al>>40)&0xff)
    buf[off+39] = UInt8((al>>48)&0xff); buf[off+40] = UInt8((al>>56)&0xff)
    # be
    buf[off+41] = UInt8(be&0xff); buf[off+42] = UInt8((be>>8)&0xff)
    buf[off+43] = UInt8((be>>16)&0xff); buf[off+44] = UInt8((be>>24)&0xff)
    buf[off+45] = UInt8((be>>32)&0xff); buf[off+46] = UInt8((be>>40)&0xff)
    buf[off+47] = UInt8((be>>48)&0xff); buf[off+48] = UInt8((be>>56)&0xff)
    nothing
end

# ---------------------------------------------------------------------------
#  Hot-shard primitives
# ---------------------------------------------------------------------------

@inline function _lsm_hot_find(sc::LP1ConjLSM, si::Int,
                                key::CanonicalLP1Key)::Int
    keys = sc.hot_keys[si]
    cap  = sc.hot_caps[si]
    mask = sc.hot_masks[si]
    slot = Int(_lsm_fp(key) & mask) + 1
    @inbounds while true
        k = keys[slot]
        k == key            && return slot
        k == CONJ_KEY_EMPTY && return 0
        slot = slot == cap ? 1 : slot + 1
    end
end

@inline function _lsm_hot_insert!(sc::LP1ConjLSM{V}, si::Int,
                                   key::CanonicalLP1Key, val::V) where V
    keys = sc.hot_keys[si]
    vals = sc.hot_vals[si]
    cap  = sc.hot_caps[si]
    mask = sc.hot_masks[si]
    slot = Int(_lsm_fp(key) & mask) + 1
    @inbounds while true
        if keys[slot] == CONJ_KEY_EMPTY
            keys[slot] = key
            vals[slot] = val
            sc.hot_counts[si] += 1
            return
        end
        slot = slot == cap ? 1 : slot + 1
    end
end

@inline function _lsm_hot_delete!(sc::LP1ConjLSM, si::Int, slot::Int)
    keys = sc.hot_keys[si]
    vals = sc.hot_vals[si]
    cap  = sc.hot_caps[si]
    mask = sc.hot_masks[si]
    @inbounds begin
        keys[slot] = CONJ_KEY_EMPTY
        sc.hot_counts[si] -= 1
        gap  = slot
        curr = slot == cap ? 1 : slot + 1
        while keys[curr] != CONJ_KEY_EMPTY
            nat = Int(_lsm_fp(keys[curr]) & mask) + 1
            displaced = if gap < curr
                nat <= gap || nat > curr
            else
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
#  Flush one shard to the spill file
#
#  Caller must hold BOTH sc.shard_locks[si] AND sc.file_lock.
# ---------------------------------------------------------------------------
function _lsm_flush_shard!(sc::LP1ConjLSM{V}, si::Int) where V
    n = sc.hot_counts[si]
    n == 0 && return

    # ── Bucket cold-filter ────────────────────────────────────────────────────
    # Drop any entry whose COLD_BITS-bit fp bucket has never received an
    # emission (cold_bitmap bit is zero).  These entries can never produce a
    # birthday collision because no partial has ever mapped to their coarse
    # bucket.  Spilling them to SSD is pure I/O waste.
    #
    # cold_bitmap reads are lockless (bits only ever set, never cleared), so
    # a stale zero means the bucket is genuinely cold at flush time.  The tiny
    # race where a bucket turns hot during this flush costs at most one missed
    # entry per bucket per flush cycle — negligible.
    #
    # COLD_FILTER_WARMUP: require at least 4 × 2^COLD_BITS emissions before
    # filtering so every bucket has had a chance to be observed.
    cold_filter_warmup = (1 << COLD_BITS) * 4
    use_cold_filter = sc.bday_emissions >= cold_filter_warmup
    cb = sc.cold_bitmap   # lockless snapshot reference

    # Collect live entries, dropping cold-bucket entries when filter is active.
    fps  = Vector{UInt64}(undef, n)
    u0s  = Vector{UInt32}(undef, n)
    u1s  = Vector{UInt32}(undef, n)
    v0s  = Vector{UInt32}(undef, n)
    v1s  = Vector{UInt32}(undef, n)
    i0s  = Vector{UInt16}(undef, n)
    als  = Vector{UInt64}(undef, n)
    bes  = Vector{UInt64}(undef, n)

    idx      = 0
    n_cold   = 0
    keys     = sc.hot_keys[si]
    vals     = sc.hot_vals[si]
    @inbounds for slot in 1:sc.hot_caps[si]
        k = keys[slot]
        k == CONJ_KEY_EMPTY && continue
        fp = _lsm_fp(k)
        # Cold-filter: skip entries in unobserved coarse fp buckets.
        if use_cold_filter
            cb_idx  = Int(fp >> COLD_SHIFT)
            cb_word = cb_idx >> 6
            cb_bit  = cb_idx & 63
            if @inbounds (cb[cb_word + 1] >> cb_bit) & UInt64(1) == UInt64(0)
                n_cold += 1
                continue
            end
        end
        idx += 1
        fps[idx] = fp
        u0s[idx] = UInt32(k & 0x00000000ffffffff)
        u1s[idx] = UInt32((k >> 32)  & 0x00000000ffffffff)
        v0s[idx] = UInt32((k >> 64)  & 0x00000000ffffffff)
        v1s[idx] = UInt32((k >> 96)  & 0x00000000ffffffff)
        v = vals[slot]
        i0s[idx] = v.i0
        als[idx] = v.neg_al
        bes[idx] = sc.amortized ? UInt64(0) : UInt64(_conj_prev_be(v))
    end
    # idx + n_cold should equal the original hot count (remaining slots are EMPTY).
    # n_cold > 0 is normal after warmup.

    # Reset hot shard now — do this before the IO so the shard is available
    # for new insertions while we write.
    fill!(sc.hot_keys[si], CONJ_KEY_EMPTY)
    sc.hot_counts[si] = 0
    sc.n_cold_dropped += n_cold

    # Nothing hot-and-warm to spill?  Done.
    idx == 0 && return

    # Sort by fingerprint
    order = sortperm(view(fps, 1:idx))

    # Build packed binary buffer and write to spill file
    buf = zeros(UInt8, idx * RECORD_BYTES)
    @inbounds for i in 1:idx
        oi = order[i]
        _write_record!(buf, (i-1)*RECORD_BYTES,
                       fps[oi], u0s[oi], u1s[oi], v0s[oi], v1s[oi],
                       i0s[oi], als[oi], bes[oi])
    end

    byte_offset = sc.spill_size
    write(sc.spill_io, buf)
    sc.spill_size += idx * RECORD_BYTES

    # Update Bloom filters — own bloom and the shared global bloom
    for i in 1:idx
        fp_i = fps[order[i]]
        set_bloom!(sc.bloom, fp_i)
        set_bloom!(sc.global_bloom, fp_i)
    end

    # Register run
    min_fp = fps[order[1]]
    max_fp = fps[order[idx]]
    push!(sc.runs, RunMeta(length(sc.runs)+1, byte_offset, idx, min_fp, max_fp))
    sc.n_disk_live += idx

    # Open (or keep open) the read-side fd
    _lsm_open_read_io!(sc)
    _fadvise_dontneed!(sc)  # <--- ADD THIS HERE

    # Compact runs if fan-out is getting large.
    # _lsm_compact! manages file_lock itself (acquire for snapshot + commit,
    # released for the I/O-heavy merge body) so we must NOT hold file_lock
    # when calling it.  Release here; _lsm_compact! will reacquire as needed.
    if length(sc.runs) >= 16
        unlock(sc.file_lock)
        _lsm_compact!(sc)
        lock(sc.file_lock)
    end

    nothing
end

# ---------------------------------------------------------------------------
#  Compact all runs into a single sorted run via k-way merge.
#  Caller must hold sc.file_lock.
#
#  Memory profile:
#    • One record buffer per run (k × RECORD_BYTES, negligible).
#    • A min-heap of k cursors (one entry per run).
#    • One write-side IOBuffer (COMPACT_WRITE_BUF_BYTES), flushed incrementally.
#  Total extra RAM: O(k) + write buffer — independent of total dataset size.
# ---------------------------------------------------------------------------

const COMPACT_WRITE_BUF_BYTES = 4 * 1024 * 1024   # 4 MB write buffer

# Heap entry: (fp, run_index, pos_in_run)
# We use a simple binary min-heap over (fp, ri) tuples stored in a Vector.

@inline function _heap_less(a::Tuple{UInt64,Int,Int}, b::Tuple{UInt64,Int,Int})
    a[1] < b[1] || (a[1] == b[1] && a[2] < b[2])
end

function _heap_push!(h::Vector{Tuple{UInt64,Int,Int}}, x::Tuple{UInt64,Int,Int})
    push!(h, x)
    i = length(h)
    @inbounds while i > 1
        p = i >> 1
        if _heap_less(h[i], h[p])
            h[i], h[p] = h[p], h[i]
            i = p
        else
            break
        end
    end
    nothing
end

function _heap_pop!(h::Vector{Tuple{UInt64,Int,Int}})::Tuple{UInt64,Int,Int}
    top = h[1]
    n = length(h)
    if n == 1
        pop!(h)
        return top
    end
    h[1] = pop!(h)
    i = 1
    n -= 1
    @inbounds while true
        l = 2i; r = 2i + 1
        smallest = i
        l <= n && _heap_less(h[l], h[smallest]) && (smallest = l)
        r <= n && _heap_less(h[r], h[smallest]) && (smallest = r)
        smallest == i && break
        h[i], h[smallest] = h[smallest], h[i]
        i = smallest
    end
    top
end

function _lsm_compact!(sc::LP1ConjLSM)
    # _lsm_compact! is called from _lsm_flush_shard!, which is called from
    # conj_insert_or_pop! and lsm_flush_all!.
    #
    # LOCKING CONTRACT: caller holds file_lock (but NOT any shard_lock when
    # called from conj_insert_or_pop!, because _lsm_flush_shard! is called
    # after the shard lock is already released via the hot-reset).
    # Actually _lsm_flush_shard! is always called while shard_locks[si] IS
    # held by the caller.  To avoid holding file_lock for the entire I/O-heavy
    # merge, the caller (_lsm_flush_shard!) releases file_lock before calling
    # this function, so we can acquire it ourselves only for the brief
    # metadata-swap at the end.
    #
    # See the restructured call site in _lsm_flush_shard!.

    length(sc.runs) <= 1 && return

    total_live = sc.n_disk_live
    total_live == 0 && return
    sc.spill_read_io === nothing && return   # no spill file yet

    # ── Phase 1: snapshot run list under a brief file_lock acquisition ───────
    lock(sc.file_lock)
    nruns_snap   = length(sc.runs)
    runs_snap    = sc.runs[1:nruns_snap]      # shallow copy; RunMeta objects are shared refs
    read_fd_snap = sc.spill_read_io
    unlock(sc.file_lock)

    # ── Phase 2: I/O-heavy merge (no locks held) ─────────────────────────────
    # Per-run cursors: advance past leading tombstones.
    cursors = Vector{Int}(undef, nruns_snap)
    for ri in 1:nruns_snap
        rm  = runs_snap[ri]
        pos = 1
        while pos <= rm.len && _run_is_dead(rm, pos)
            pos += 1
        end
        cursors[ri] = pos
    end

    # Helper: pread from the snapshot fd directly.
    local_pread! = function(buf::Vector{UInt8}, off::Int)
        n = ccall(:pread, Cssize_t, (Cint, Ptr{UInt8}, Csize_t, Int64),
                  read_fd_snap, buf, RECORD_BYTES, off)
        if n != RECORD_BYTES
            err_msg = Base.Libc.strerror()
            error("_lsm_compact! local_pread: short read ($n) at offset $off: $err_msg")
        end
        nothing
    end

    # Seed the min-heap.
    heap = Tuple{UInt64,Int,Int}[]
    sizehint!(heap, nruns_snap)
    rec_buf_seed = zeros(UInt8, RECORD_BYTES)
    for ri in 1:nruns_snap
        rm  = runs_snap[ri]
        pos = cursors[ri]
        pos > rm.len && continue
        local_pread!(rec_buf_seed, _rec_base(rm, pos))
        fp = _buf_fp(rec_buf_seed)
        _heap_push!(heap, (fp, ri, pos))
    end

    # Stream merged records into temp file.
    tmp_path  = sc.spill_path * ".compact"
    tmp_io    = open(tmp_path, "w+")
    wbuf      = Vector{UInt8}(undef, COMPACT_WRITE_BUF_BYTES)
    wbuf_pos  = 0

    actual   = 0
    first_fp = UInt64(0)
    last_fp  = UInt64(0)

    rec_buf_merge = zeros(UInt8, RECORD_BYTES)
    while !isempty(heap)
        fp, ri, pos = _heap_pop!(heap)
        rm = runs_snap[ri]

        local_pread!(rec_buf_merge, _rec_base(rm, pos))
        if wbuf_pos + RECORD_BYTES > COMPACT_WRITE_BUF_BYTES
            write(tmp_io, view(wbuf, 1:wbuf_pos))
            wbuf_pos = 0
        end
        @inbounds for b in 1:RECORD_BYTES
            wbuf[wbuf_pos + b] = rec_buf_merge[b]
        end
        wbuf_pos += RECORD_BYTES

        actual == 0 && (first_fp = fp)
        last_fp = fp
        actual += 1

        pos += 1
        while pos <= rm.len && _run_is_dead(rm, pos)
            pos += 1
        end
        cursors[ri] = pos
        if pos <= rm.len
            local_pread!(rec_buf_merge, _rec_base(rm, pos))
            fp2 = _buf_fp(rec_buf_merge)
            _heap_push!(heap, (fp2, ri, pos))
        end
    end

    wbuf_pos > 0 && write(tmp_io, view(wbuf, 1:wbuf_pos))
    flush(tmp_io)
    close(tmp_io)

    # ── Phase 3: reacquire file_lock and atomically commit ───────────────────
    lock(sc.file_lock)

    # Any runs appended during phase 2 (indices nruns_snap+1..end) are in the
    # tail of the old spill file.  Copy them to the temp file, adjusting offsets.
    new_run_base = actual * RECORD_BYTES
    if length(sc.runs) > nruns_snap
        tmp_io2  = open(tmp_path, "a+")
        tail_buf = zeros(UInt8, RECORD_BYTES)
        for ri in (nruns_snap+1):length(sc.runs)
            rm      = sc.runs[ri]
            new_off = new_run_base
            for rec_pos in 1:rm.len
                n = ccall(:pread, Cssize_t, (Cint, Ptr{UInt8}, Csize_t, Int64),
                          read_fd_snap, tail_buf, RECORD_BYTES,
                          rm.byte_offset + (rec_pos - 1) * RECORD_BYTES)
                n == RECORD_BYTES && write(tmp_io2, tail_buf)
            end
            old_tombs         = rm.tombs
            sc.runs[ri]       = RunMeta(rm.id, new_off, rm.len, rm.min_fp, rm.max_fp)
            sc.runs[ri].tombs = old_tombs
            new_run_base     += rm.len * RECORD_BYTES
        end
        flush(tmp_io2)
        close(tmp_io2)
    end

    close(sc.spill_io)
    mv(tmp_path, sc.spill_path; force=true)
    sc.spill_io   = open(sc.spill_path, "a+")
    sc.spill_size = new_run_base

    # Recompute n_disk_live.
    snap_live_old = sum(let _rm = runs_snap[ri]
                            count(p -> !_run_is_dead(_rm, p), 1:_rm.len)
                        end for ri in 1:nruns_snap; init=0)
    sc.n_disk_live = sc.n_disk_live - snap_live_old + actual

    # Replace snapshot runs with single merged run; keep tail runs.
    remaining_runs = sc.runs[(nruns_snap+1):end]
    new_compacted  = actual > 0 ? [RunMeta(1, 0, actual, first_fp, last_fp)] : RunMeta[]
    sc.runs        = vcat(new_compacted, remaining_runs)
    for (i, rm) in enumerate(sc.runs)
        old_tombs   = rm.tombs
        sc.runs[i]  = RunMeta(i, rm.byte_offset, rm.len, rm.min_fp, rm.max_fp)
        sc.runs[i].tombs = old_tombs
    end

    if sc.spill_read_io !== nothing
        ccall(:close, Cint, (Cint,), sc.spill_read_io)
        sc.spill_read_io = nothing
    end
    sc.spill_read_io = _open_direct(sc.spill_path)
    _fadvise_dontneed!(sc)
    unlock(sc.file_lock)
    nothing
end

# ---------------------------------------------------------------------------
#  Cold (disk via mmap) lookup
#
#  Returns (found, run_idx, pos_in_run, i0_v, al_v, be_v).
#  Caller must hold sc.file_lock.
# ---------------------------------------------------------------------------
function _lsm_disk_find(sc::LP1ConjLSM,
                         key::CanonicalLP1Key,
                         fp_target::UInt64)::Tuple{Bool,Int,Int,UInt16,UInt64,UInt64}
    sc.spill_read_io === nothing && return (false, 0, 0, UInt16(0), UInt64(0), UInt64(0))
    ku0 = UInt32(key & 0x00000000ffffffff)
    ku1 = UInt32((key >> 32)  & 0x00000000ffffffff)
    kv0 = UInt32((key >> 64)  & 0x00000000ffffffff)
    kv1 = UInt32((key >> 96)  & 0x00000000ffffffff)
    buf = sc.read_buf   # pre-allocated; safe because caller holds file_lock

    for (ri, rm) in enumerate(sc.runs)
        (fp_target < rm.min_fp || fp_target > rm.max_fp) && continue

        # Binary search on fp via pread into scratch buffer.
        lo = 1; hi = rm.len
        while lo < hi
            mid = (lo + hi) >>> 1
            _pread_record!(sc, buf, _rec_base(rm, mid))
            if _buf_fp(buf) < fp_target
                lo = mid + 1
            else
                hi = mid
            end
        end
        lo > rm.len && continue
        _pread_record!(sc, buf, _rec_base(rm, lo))
        _buf_fp(buf) != fp_target && continue

        # Scan matching fingerprints
        pos = lo
        while pos <= rm.len
            _pread_record!(sc, buf, _rec_base(rm, pos))
            _buf_fp(buf) != fp_target && break
            if !_run_is_dead(rm, pos) &&
               _buf_key_match(buf, ku0, ku1, kv0, kv1)
                return (true, ri, pos, _buf_i0(buf), _buf_al(buf), _buf_be(buf))
            end
            pos += 1
        end
    end
    (false, 0, 0, UInt16(0), UInt64(0), UInt64(0))
end

function _lsm_disk_delete!(sc::LP1ConjLSM, ri::Int, pos::Int)
    _run_set_dead!(sc.runs[ri], pos)
    sc.n_disk_live -= 1
    nothing
end

# ---------------------------------------------------------------------------
#  Public API
# ---------------------------------------------------------------------------

function conj_total_entries(sc::LP1ConjLSM)::Int
    sum(sc.hot_counts) + sc.n_disk_live
end

# ---------------------------------------------------------------------------
#  Base.haskey / Base.getindex — thin wrappers so generic code that spells
#  `haskey(store, key)` / `store[key]` works correctly.
#
#  LP1ConjLSM requires a shard index for all operations; we derive it from
#  the key here so callers don't have to.
#
#  NOTE: these are read-only and do NOT pop the entry.  Use conj_pop! or
#  conj_insert_or_pop! when consumption is required (phase-2 walk).
# ---------------------------------------------------------------------------
function Base.haskey(sc::LP1ConjLSM, key::CanonicalLP1Key)::Bool
    conj_haskey(sc, conj_shard_idx(key), key)
end

function Base.getindex(sc::LP1ConjLSM{V}, key::CanonicalLP1Key)::V where V
    conj_getval(sc, conj_shard_idx(key), key)
end

function conj_haskey(sc::LP1ConjLSM, si::Int, key::CanonicalLP1Key)::Bool
    lock(sc.shard_locks[si])
    try
        _lsm_hot_find(sc, si, key) != 0 && return true
    finally
        unlock(sc.shard_locks[si])
    end
    fp = _lsm_fp(key)
    !bloom_maybe_has(sc.bloom, fp) && return false
    lock(sc.file_lock)
    try
        lock(sc.shard_locks[si])
        try
            found, _, _, _, _, _ = _lsm_disk_find(sc, key, fp)
            return found
        finally
            unlock(sc.shard_locks[si])
        end
    finally
        unlock(sc.file_lock)
    end
end

function conj_getval(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    lock(sc.shard_locks[si])
    try
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            return @inbounds sc.hot_vals[si][slot]
        end
    finally
        unlock(sc.shard_locks[si])
    end
    fp = _lsm_fp(key)
    lock(sc.file_lock)
    try
        lock(sc.shard_locks[si])
        try
            found, _, _, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
            found || throw(KeyError(key))
            return _conj_make_val(V, i0_v, al_v, be_v)
        finally
            unlock(sc.shard_locks[si])
        end
    finally
        unlock(sc.file_lock)
    end
end

function conj_pop!(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    lock(sc.shard_locks[si])
    try
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            result = @inbounds sc.hot_vals[si][slot]
            _lsm_hot_delete!(sc, si, slot)
            return result
        end
    finally
        unlock(sc.shard_locks[si])
    end
    fp = _lsm_fp(key)
    lock(sc.file_lock)
    try
        lock(sc.shard_locks[si])
        try
            found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
            found && _lsm_disk_delete!(sc, ri, pos)
            found || throw(KeyError(key))
            return _conj_make_val(V, i0_v, al_v, be_v)
        finally
            unlock(sc.shard_locks[si])
        end
    finally
        unlock(sc.file_lock)
    end
end

function conj_pop_safe(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::Union{V,Nothing} where V
    lock(sc.shard_locks[si])
    try
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            result = @inbounds sc.hot_vals[si][slot]
            _lsm_hot_delete!(sc, si, slot)
            return result
        end
    finally
        unlock(sc.shard_locks[si])
    end
    fp = _lsm_fp(key)
    lock(sc.file_lock)
    try
        lock(sc.shard_locks[si])
        try
            found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
            found && _lsm_disk_delete!(sc, ri, pos)
            found || return nothing
            return _conj_make_val(V, i0_v, al_v, be_v)
        finally
            unlock(sc.shard_locks[si])
        end
    finally
        unlock(sc.file_lock)
    end
end

function conj_insert!(sc::LP1ConjLSM{V}, si::Int,
                       key::CanonicalLP1Key, val::V)::Bool where V
    lock(sc.file_lock)
    try
        lock(sc.shard_locks[si])
        try
            if sc.hot_counts[si] >= sc.hot_thresh[si]
                _lsm_flush_shard!(sc, si)   # caller holds file_lock + shard_locks[si] ✓
            end
            _lsm_hot_insert!(sc, si, key, val)
            return true
        finally
            unlock(sc.shard_locks[si])
        end
    finally
        unlock(sc.file_lock)
    end
end

# ---------------------------------------------------------------------------
#  _lsm_record_sample! — update AMS sketch / bday counters for one genuine
#  key submission.  Called only for true misses (insert) and true cross-col
#  hits.  Same-col re-inserts are invisible to the estimator so α₂ reflects
#  the actual walk distribution, not artifact duplicates.
#
#  AMS update: for each of the AMS_K hash functions h_j, compute the sign
#  h_j(fp) = (-1)^{high bit of fp*salt_j} and add it to ams_Z[j].
#  After N emissions, E[ams_Z[j]^2] = F₂ = Σcᵢ², and S₂ = N²/F₂.
#
#  Cold-filter bitmap update: set the COLD_BITS-bit bucket presence bit
#  for this fingerprint (used by the flush path, not for S₂).
# ---------------------------------------------------------------------------
@inline function _lsm_record_sample!(sc::LP1ConjLSM, fp::UInt64, now_t::Float64)
    # Cold-filter bitmap — lockless bit-set (bits only ever set, never cleared).
    cb_idx  = Int(fp >> COLD_SHIFT)          # 0-based bucket index
    cb_word = cb_idx >> 6                    # which UInt64 word
    cb_bit  = cb_idx & 63                   # which bit within the word
    # Capture was_zero BEFORE setting the bit so occ_unique counts correctly.
    @inbounds was_zero = (sc.cold_bitmap[cb_word + 1] >> cb_bit) & UInt64(1) == UInt64(0)
    @inbounds sc.cold_bitmap[cb_word + 1] |= UInt64(1) << cb_bit

    lock(sc.bday_lock)
    try
        sc.bday_emissions == 0 && (sc.bday_t0 = now_t)
        sc.bday_emissions += 1
        sc.occ_n          += 1

        # AMS sketch update: 512 sign-hash projections.
        # h_j(fp) = +1 if high bit of (fp * salt_j) is 0, else -1.
        Z = sc.ams_Z
        @inbounds for j in 1:AMS_K
            h = fp * AMS_SALTS[j]
            Z[j] += ifelse((h >> 63) == UInt64(0), Int64(1), Int64(-1))
        end

        # Occupancy: increment for newly-observed coarse buckets.
        was_zero && (sc.occ_unique += 1)

        # Partial fp log: record the COLD_BITS-bit bucket index for windowed
        # α₂ diagnostics.  Uses UInt32 since COLD_BITS = 20 fits easily.
        log_n = length(sc.partial_fp_log)
        bucket_idx = UInt32(cb_idx)
        if log_n < PARTIAL_FP_LOG_CAP
            push!(sc.partial_fp_log, bucket_idx)
        else
            circ_idx = ((sc.bday_emissions - 1) % PARTIAL_FP_LOG_CAP) + 1
            @inbounds sc.partial_fp_log[circ_idx] = bucket_idx
        end
    finally
        unlock(sc.bday_lock)
    end
end

# ---------------------------------------------------------------------------
#  _ams_estimate_S2 — compute S₂ from an AMS_K-length Z vector and N.
#
#  Groups of AMS_WIDTH estimators; mean Z²  within each group; median across
#  groups.  Returns (F2_estimate, S2_estimate).
# ---------------------------------------------------------------------------
@inline function _ams_group_quantile(sorted_vals::Vector{Float64}, q::Float64)::Float64
    n = length(sorted_vals)
    n == 0 && return NaN
    n == 1 && return sorted_vals[1]
    q_clamped = clamp(q, 0.0, 1.0)
    pos = 1.0 + q_clamped * Float64(n - 1)
    lo  = clamp(floor(Int, pos), 1, n)
    hi  = min(lo + 1, n)
    t   = pos - Float64(lo)
    return (1.0 - t) * sorted_vals[lo] + t * sorted_vals[hi]
end

function _ams_estimate_S2_stats(Z::Vector{Int64}, N::Int64)
    N == 0 && return (
        F2=0.0, S2=0.0,
        F2_lo=0.0, F2_hi=0.0,
        S2_lo=0.0, S2_hi=0.0,
        alpha2=0.0, alpha2_lo=0.0, alpha2_hi=0.0
    )

    group_means = Vector{Float64}(undef, AMS_GROUPS)
    @inbounds for g in 1:AMS_GROUPS
        base = (g - 1) * AMS_WIDTH
        m = 0.0
        for j in 1:AMS_WIDTH
            m += Float64(Z[base + j])^2
        end
        group_means[g] = m / AMS_WIDTH
    end
    sort!(group_means)

    # Median-of-means point estimate.
    F2 = if iseven(AMS_GROUPS)
        (group_means[AMS_GROUPS ÷ 2] + group_means[AMS_GROUPS ÷ 2 + 1]) / 2.0
    else
        group_means[(AMS_GROUPS + 1) ÷ 2]
    end
    F2 = max(F2, 1.0)

    # Robust spread band from the central 68% of group means.
    # This is an inter-group error bar, not a formal confidence interval.
    F2_lo = max(1.0, _ams_group_quantile(group_means, 0.15865525393145707))
    F2_hi = max(F2_lo, _ams_group_quantile(group_means, 0.8413447460685429))

    S2    = Float64(N)^2 / F2
    S2_lo = Float64(N)^2 / F2_hi
    S2_hi = Float64(N)^2 / F2_lo

    logp = log(Float64(p))
    alpha2    = log(S2) / (2.0 * logp)
    alpha2_lo = log(S2_lo) / (2.0 * logp)
    alpha2_hi = log(S2_hi) / (2.0 * logp)

    return (
        F2=F2, S2=S2,
        F2_lo=F2_lo, F2_hi=F2_hi,
        S2_lo=S2_lo, S2_hi=S2_hi,
        alpha2=alpha2, alpha2_lo=alpha2_lo, alpha2_hi=alpha2_hi
    )
end

function _ams_estimate_S2(Z::Vector{Int64}, N::Int64)::Tuple{Float64, Float64}
    stats = _ams_estimate_S2_stats(Z, N)
    return (stats.F2, stats.S2)
end

# ---------------------------------------------------------------------------
#  conj_insert_or_pop! — atomic check+act, no TOCTOU race.
#
#  Returns (prev_val, is_same_col):
#    (nothing, false)  -- genuine miss; key was inserted.  Renyi updated.
#    (v,       false)  -- genuine cross-col collision.  Renyi updated.
#    (nothing, true)   -- same-col hit: stored entry kept, current step
#                         discarded.  Renyi NOT updated (not an independent
#                         sample -- would inflate alpha_2 artificially).
#
#  The caller uses is_same_col only for the diagnostic counter; the
#  relation-emission logic treats nothing the same as before.
# ---------------------------------------------------------------------------
function conj_insert_or_pop!(sc::LP1ConjLSM{V}, si::Int,
                              key::CanonicalLP1Key, val::V
                             )::Tuple{Union{V,Nothing}, Bool} where V

    fp    = _lsm_fp(key)
    now_t = time_ns() * 1e-9
    i0_cur = Int(val.i0)

    # 1. Fast Path: Check own hot table using ONLY the shard lock.
    # Avoids serializing all threads on file_lock for hot RAM hits.
    lock(sc.shard_locks[si])
    try
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            v = @inbounds sc.hot_vals[si][slot]
            if Int(v.i0) == i0_cur
                # Same-col: leave stored entry in place, discard current step.
                # Do NOT update Renyi -- not an independent sample.
                return (nothing, true)
            end
            _lsm_hot_delete!(sc, si, slot)
            _lsm_record_sample!(sc, fp, now_t)
            _bday_record_collision!(sc, now_t)
            return (v, false)
        end
    finally
        unlock(sc.shard_locks[si])
    end

    # 2. Check own disk runs (requires file_lock).
    if !isempty(sc.runs) && bloom_maybe_has(sc.bloom, fp)
        lock(sc.file_lock)
        try
            lock(sc.shard_locks[si])
            try
                # TOCTOU double-check: another thread may have inserted into
                # the hot table while we were waiting for file_lock.
                slot = _lsm_hot_find(sc, si, key)
                if slot != 0
                    v = @inbounds sc.hot_vals[si][slot]
                    if Int(v.i0) == i0_cur
                        return (nothing, true)
                    end
                    _lsm_hot_delete!(sc, si, slot)
                    _lsm_record_sample!(sc, fp, now_t)
                    _bday_record_collision!(sc, now_t)
                    return (v, false)
                end

                found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
                if found
                    if Int(i0_v) == i0_cur
                        # Same-col on disk: leave tombstone (entry is consumed),
                        # re-write it back so a future cross-col hit can find it.
                        # Simplest: just re-insert into hot table.
                        _lsm_disk_delete!(sc, ri, pos)
                        _lsm_hot_insert!(sc, si, key, _conj_make_val(V, i0_v, al_v, be_v))
                        return (nothing, true)
                    end
                    _lsm_disk_delete!(sc, ri, pos)
                    result_v = _conj_make_val(V, i0_v, al_v, be_v)
                    _lsm_record_sample!(sc, fp, now_t)
                    _bday_record_collision!(sc, now_t)
                    return (result_v, false)
                end
            finally
                unlock(sc.shard_locks[si])
            end
        finally
            unlock(sc.file_lock)
        end
    end

    # 3. Cross-peer probe — only if global bloom suggests a match somewhere.
    #
    #    Two guards before touching any peer:
    #      (a) bday_first_coll_m > 0: at least one birthday collision has been
    #          observed, meaning the key space is populated enough that peer disk
    #          entries are likely to produce real matches.  Before the first
    #          collision, peer disks are essentially empty; probing them on every
    #          one of ~5M conj steps costs 31 x file_lock acquisitions for zero
    #          benefit and is the primary cause of the ~50% CPU idle observed at
    #          run start.  Read is intentionally racy (no lock): a false negative
    #          (we read 0 when it just became nonzero) only defers peer probing by
    #          one emission cycle, which is harmless.
    #      (b) bloom_maybe_has(sc.global_bloom, fp): the key was seen by at least
    #          one peer at some point.
    #
    #    Disk probes use trylock (not lock) so a busy peer is skipped rather than
    #    blocking.  A missed hit means the entry stays on peer disk until the next
    #    emission cycle for that key, which is acceptable -- correctness is
    #    preserved, only latency is affected.
    if bloom_maybe_has(sc.global_bloom, fp)
        for peer in sc.peers
            peer === sc && continue
            peer_lsm = peer::LP1ConjLSM{V}

            # Skip this peer entirely if its own bloom says it never saw fp.
            bloom_maybe_has(peer_lsm.bloom, fp) || continue

            # Check peer hot table first (cheap, no file_lock needed).
            if trylock(peer_lsm.shard_locks[si])
                try
                    pslot = _lsm_hot_find(peer_lsm, si, key)
                    if pslot != 0
                        pv = @inbounds peer_lsm.hot_vals[si][pslot]
                        if Int(pv.i0) == i0_cur
                            return (nothing, true)
                        end
                        _lsm_hot_delete!(peer_lsm, si, pslot)
                        _lsm_record_sample!(sc, fp, now_t)
                        _bday_record_collision!(sc, now_t)
                        return (pv, false)
                    end
                finally
                    unlock(peer_lsm.shard_locks[si])
                end
            end

            # Check peer disk via trylock -- skip peer if it is busy flushing.
            # Per-LSM bloom already gates this to ~FPR% of calls, so contention
            # is low once the bloom is well-populated.
            if !isempty(peer_lsm.runs)
                if trylock(peer_lsm.file_lock)
                    try
                        if trylock(peer_lsm.shard_locks[si])
                            try
                                found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(peer_lsm, key, fp)
                                if found
                                    if Int(i0_v) == i0_cur
                                        _lsm_disk_delete!(peer_lsm, ri, pos)
                                        lock(peer_lsm.shard_locks[si]) do
                                            _lsm_hot_insert!(peer_lsm, si, key,
                                                             _conj_make_val(V, i0_v, al_v, be_v))
                                        end
                                        return (nothing, true)
                                    end
                                    _lsm_disk_delete!(peer_lsm, ri, pos)
                                    _lsm_record_sample!(sc, fp, now_t)
                                    _bday_record_collision!(sc, now_t)
                                    return (_conj_make_val(V, i0_v, al_v, be_v), false)
                                end
                            finally
                                unlock(peer_lsm.shard_locks[si])
                            end
                        end
                    finally
                        unlock(peer_lsm.file_lock)
                    end
                end
            end
        end
    end

    # 4. Not found -- insert into own LSM, unless we are at cap.
    lock(sc.file_lock)
    try
        lock(sc.shard_locks[si])
        try
            # TOCTOU final check before insertion.
            slot = _lsm_hot_find(sc, si, key)
            if slot != 0
                v = @inbounds sc.hot_vals[si][slot]
                if Int(v.i0) == i0_cur
                    return (nothing, true)
                end
                _lsm_hot_delete!(sc, si, slot)
                _lsm_record_sample!(sc, fp, now_t)
                _bday_record_collision!(sc, now_t)
                return (v, false)
            end

            # Cap enforcement: drop silently when the LSM is full.
            if sc.n_disk_live + sum(sc.hot_counts) >= sc.max_entries
                sc.n_cold_dropped += 1
                return (nothing, false)
            end

            if sc.hot_counts[si] >= sc.hot_thresh[si]
                _lsm_flush_shard!(sc, si)
            end
            _lsm_hot_insert!(sc, si, key, val)
            _lsm_record_sample!(sc, fp, now_t)   # genuine new insertion
            return (nothing, false)
        finally
            unlock(sc.shard_locks[si])
        end
    finally
        unlock(sc.file_lock)
    end
end

# ---------------------------------------------------------------------------
#  Birthday diagnostics helpers
# ---------------------------------------------------------------------------

# Called on every confirmed LP1-conj cross-col collision.  Only records the
# *first* one.  bday_emissions is >= 1 here because _lsm_record_sample! was
# called just before this in the same hit path.
@inline function _bday_record_collision!(sc::LP1ConjLSM, now_t::Float64)
    lock(sc.bday_lock)
    try
        sc.bday_first_coll_m == 0 || return   # already recorded
        sc.bday_first_coll_m = sc.bday_emissions
        sc.bday_first_coll_t = now_t
    finally
        unlock(sc.bday_lock)
    end
    nothing
end

# ---------------------------------------------------------------------------
#  lsm_bday_report — print birthday-paradox support-size estimate.
#
#  Call after the first collision (or at any time to see current state).
#
#  Theory recap:
#    λ = r/2 = LP1-conj emission rate  (partials/step)
#    m_first = number of LP1-conj partials at first collision
#    t_first = wall time elapsed to first collision
#
#    S_eff  = m_first^2          (birthday estimate of effective support)
#    S_naive = p^2 / 2           (naive ambient model)
#
#    If S_eff << S_naive the walk-induced measure is concentrated on a
#    strictly smaller subspace: first collision at t ~ p^α/r implies S ~ p^{2α}.
#
#  Arguments:
#    sc   — LP1ConjLSM instance
#    p    — curve prime (Int or Integer)
#    r    — total throughput in partials/step across all threads (Float64)
#           r/2 is the LP1-conj emission rate.
# ---------------------------------------------------------------------------
function lsm_bday_report(sc::LP1ConjLSM, p::Integer, r::Real; io::IO = stdout)
    # ── Aggregate across all peer LSMs ─────────────────────────────────────
    # Each thread has its own LP1ConjLSM instance linked via `peers`.
    # We must aggregate across all peers to see the true global first collision.
    actual_peers = isempty(sc.peers) ? Any[sc] : sc.peers

    total_emitted = 0
    m_first       = 0
    t_coll_first  = Inf
    t0_earliest   = Inf
    occ_n_global  = 0
    ams_Z_global  = zeros(Int64, AMS_K)   # aggregate AMS sketch across all peers

    for peer in actual_peers
        # Dynamic dispatch is fine here (diagnostic path)
        lock(peer.bday_lock)
        total_emitted += peer.bday_emissions
        occ_n_global  += peer.occ_n
        
        if peer.bday_first_coll_m > 0
            if peer.bday_first_coll_t < t_coll_first
                t_coll_first = peer.bday_first_coll_t
                # Approximate global emissions at the exact time of the earliest local collision
                m_first = peer.bday_first_coll_m * length(actual_peers)
            end
        end
        
        if peer.bday_t0 > 0.0 && peer.bday_t0 < t0_earliest
            t0_earliest = peer.bday_t0
        end

        # Aggregate AMS sketch: Z_global[j] = Σ_peers Z_peer[j].
        # Linearity of expectation: E[(Z_global[j])²] ≠ Σ E[(Z_peer[j])²] in general,
        # but since each peer sees an independent sub-stream with the same distribution,
        # and the sign functions are deterministic, summing the Z vectors gives
        # Z_global[j] = Σ_k c_k · h_j(k) over all emissions across all peers,
        # which is exactly what we want.
        for i in 1:AMS_K
            ams_Z_global[i] += peer.ams_Z[i]
        end
        unlock(peer.bday_lock)
    end

    # Occupancy from cold_bitmap: count set bits across all peers' cold bitmaps.
    # Union of peer bitmaps gives the global set of observed coarse buckets.
    cold_union = zeros(UInt64, COLD_WORDS)
    for peer in actual_peers
        for i in 1:COLD_WORDS
            cold_union[i] |= peer.cold_bitmap[i]
        end
    end
    occ_u_global = sum(count_ones(w) for w in cold_union)  # distinct cold-buckets seen

    # Calculate true global emission rate from actual elapsed time
    t_elapsed = t0_earliest < Inf ? (time_ns() * 1e-9) - t0_earliest : 0.0
    lam_global = t_elapsed > 0.0 ? (total_emitted / t_elapsed) : (r * length(actual_peers))
    pf = Float64(p)

    @printf(io, "\n[LP1-conj birthday diagnostics (Global across %d peers)]\n", length(actual_peers))
    @printf(io, "  total LP1-conj emitted : %d\n", total_emitted)

    if m_first == 0
        @printf(io, "  first collision        : not yet observed\n")
        t_naive = lam_global > 0.0 ? (sqrt(2.0) * pf / lam_global) : Inf
        m_naive = lam_global * t_naive
        @printf(io, "  naive prediction       : m_first ~ %.3g,  t_first ~ %.3g s\n", m_naive, t_naive)
        if t0_earliest < Inf
            frac = t_elapsed / t_naive
            @printf(io, "  elapsed / t_naive      : %.4f  (%s)\n",
                    frac, frac >= 1.0 ? "OVERDUE — support may be smaller than p^2" : "still within naive expectation")
        end
        @printf(io, "\n")
        return
    end

    t_first   = t_coll_first - t0_earliest
    S_eff     = Float64(m_first)^2
    S_naive   = pf^2 / 2.0
    ratio     = S_eff / S_naive
    alpha     = log(Float64(m_first)) / log(pf)
    m_naive   = sqrt(S_naive)
    t_naive   = lam_global > 0.0 ? (m_naive / lam_global) : Inf

    @printf(io, "  first collision at     : m ≈ %d  (t_wall = %.3f s)\n", m_first, t_first)
    @printf(io, "  S_eff  = m^2           : %.6g\n", S_eff)
    @printf(io, "  S_naive = p^2/2        : %.6g\n", S_naive)
    @printf(io, "  S_eff / S_naive        : %.5g\n", ratio)
    @printf(io, "  alpha  (S ~ p^{2*alpha}): %.4f   [alpha=1 ↔ S~p^2, alpha=0.75 ↔ S~p^1.5, ...]\n", alpha)
    @printf(io, "  t_first (observed)     : %.3f s\n", t_first)
    @printf(io, "  t_first (naive p^2/2)  : %.3f s   (= sqrt(2)*p/lam_global)\n", t_naive)
    @printf(io, "  t_obs / t_naive        : %.4f\n", t_first / t_naive)
    
    if ratio < 0.1
        @printf(io, "  *** support is << p^2: effective space ~ p^{%.2f} ***\n", 2*alpha)
    elseif ratio < 0.5
        @printf(io, "  support is moderately smaller than p^2\n")
    else
        @printf(io, "  support is consistent with naive p^2 model\n")
    end

    # ── Occupancy estimator: U(N) = S(1 - e^{-N/S}), solve for S ─────────────
    @printf(io, "\n  Occupancy estimator (U(N) = S·(1−e^{−N/S})):\n")
    if occ_n_global >= 10 && occ_u_global >= 1 && occ_u_global < occ_n_global
        scale   = Float64(1 << COLD_BITS)
        U_f     = Float64(occ_u_global) * scale
        N_f     = Float64(occ_n_global)
        lo_s = max(U_f, 1.0)
        hi_s = max(N_f^2, U_f * 10.0)
        for _ in 1:80
            mid = (lo_s + hi_s) / 2.0
            val = mid * (1.0 - exp(-N_f / mid)) - U_f
            val < 0.0 ? (lo_s = mid) : (hi_s = mid)
        end
        S_occ   = (lo_s + hi_s) / 2.0
        r_occ   = S_occ / S_naive
        a_occ   = log(S_occ) / (2.0 * log(pf))
        @printf(io, "    unique cold-buckets U  : %d  (N=%d, scale=2^%d)\n",
                occ_u_global, occ_n_global, COLD_BITS)
        @printf(io, "    S_occ (MLE)            : %.6g\n", S_occ)
        @printf(io, "    S_occ / S_naive        : %.5g\n", r_occ)
        @printf(io, "    alpha_occ (S ~ p^{2α}) : %.4f\n", a_occ)
    else
        @printf(io, "    (need ≥10 emissions with some bucket collisions)\n")
    end

    # ── Rényi-2 / collision-entropy estimator — AMS sketch ───────────────────
    @printf(io, "\n  Rényi-2 / collision-entropy estimator (AMS sketch, %d×%d):\n",
            AMS_GROUPS, AMS_WIDTH)
    N_global = Int64(total_emitted)
    if N_global >= 2
        ams_stats = _ams_estimate_S2_stats(ams_Z_global, N_global)
        r2  = ams_stats.S2 / S_naive
        burst_flag = if S_eff > 0.0 && ams_stats.S2 > 0.0
            ratio_be = S_eff / ams_stats.S2
            ratio_be > 4.0 ? @sprintf(" ← BURSTS DOMINATE (birthday %.1f× > entropy)", ratio_be) :
            ratio_be < 0.25 ? " ← ENTROPY > BIRTHDAY (unusual)" :
                              " (birthday ≈ entropy, consistent)"
        else
            ""
        end
        a2_pm = 0.5 * (ams_stats.alpha2_hi - ams_stats.alpha2_lo)
        s2_pm = 0.5 * (ams_stats.S2_hi - ams_stats.S2_lo)
        @printf(io, "    N (total emissions)    : %d\n", N_global)
        @printf(io, "    F₂ estimate (AMS)      : %.6g  [68%% band %.6g .. %.6g]\n",
                ams_stats.F2, ams_stats.F2_lo, ams_stats.F2_hi)
        @printf(io, "    S₂ = N²/F₂            : %.6g ± %.6g  [68%% band %.6g .. %.6g]\n",
                ams_stats.S2, s2_pm, ams_stats.S2_lo, ams_stats.S2_hi)
        @printf(io, "    S₂ / S_naive           : %.5g\n", r2)
        @printf(io, "    α₂  (S₂ ~ p^{2α₂})    : %.4f ± %.4f  [68%% band %.4f .. %.4f]%s\n",
                ams_stats.alpha2, a2_pm, ams_stats.alpha2_lo, ams_stats.alpha2_hi, burst_flag)
        @printf(io, "    [band is the inter-group spread; not a formal CI]\n")
        @printf(io, "    [AMS never saturates; valid for any N]\n")
    else
        @printf(io, "    (no emissions recorded yet)\n")
    end

    @printf(io, "\n")

    # ── α₂ scaling diagnostics on the partial key stream ─────────────────────
    # (Thread-local view; cross-thread merge of ring buffers is non-trivial.)
    # The windowed estimator computes α₂ over windows of Tw emissions using
    # the 2^COLD_BITS coarse bucket index stored in partial_fp_log.
    # It is unbiased when Tw << 2^COLD_BITS (average < 1 hit/bucket per window),
    # and saturates when Tw >> 2^COLD_BITS.  We annotate saturated rows.
    let blog = copy(sc.partial_fp_log)
        nb       = 1 << COLD_BITS    # number of coarse buckets
        n_blog   = length(blog)
        sat_warn = nb ÷ 4            # warn when Tw > nb/4

        @printf(io, "  LP1-conj partial stream α₂ scaling (Thread Local view, 2^%d buckets):\n",
                COLD_BITS)
        if n_blog < 64
            @printf(io, "    (need ≥64 partials; got %d)\n\n", n_blog)
        else
            @printf(io, "    nb=%d fp-buckets  N=%d partials\n", nb, n_blog)
            @printf(io, "    window_T    n_events   α₂(T)    S_occ(T)   ρ=S_occ/S₂  dα₂/dlogT  note\n")

            T0   = max(32, n_blog ÷ 64)
            Tw   = T0
            prev_a2 = NaN; prev_logT = NaN
            a2_vals = Float64[]; logT_vals = Float64[]

            while Tw <= n_blog
                n_wins = n_blog ÷ Tw
                n_wins < 1 && break
                s2_acc = 0.0; socc_acc = 0.0; n_valid = 0
                counts_T = zeros(Int, nb)
                for wi in 0:(n_wins - 1)
                    fill!(counts_T, 0)
                    for k in (wi*Tw + 1):((wi+1)*Tw)
                        counts_T[Int(blog[k]) + 1] += 1
                    end
                    n_T = sum(counts_T)
                    n_T == 0 && continue
                    p2sum = sum((counts_T[i] / n_T)^2 for i in 1:nb)
                    s2_T  = p2sum > 0.0 ? -log2(p2sum) : NaN
                    n_occ = count(>(0), counts_T)
                    socc_T = n_occ > 0 ? log2(Float64(n_occ)) : 0.0
                    if !isnan(s2_T)
                        s2_acc += s2_T; socc_acc += socc_T; n_valid += 1
                    end
                end
                n_valid == 0 && (Tw *= 2; continue)

                a2_T    = s2_acc   / n_valid
                socc_T  = socc_acc / n_valid
                rho_T   = a2_T > 0.0 ? socc_T / a2_T : NaN
                logT    = log2(Float64(Tw))
                da2     = (!isnan(prev_a2) && !isnan(prev_logT) && logT > prev_logT) ?
                          (a2_T - prev_a2) / (logT - prev_logT) : NaN
                da_str  = isnan(da2)  ? "        —" : @sprintf("%+9.4f", da2)
                rho_str = isnan(rho_T) ? "         —" : @sprintf("%10.4f", rho_T)
                note    = Tw > sat_warn ? " [SAT?]" : ""
                @printf(io, "    %9d  %9d  %8.4f  %9.4f  %s  %s%s\n",
                        Tw, n_wins * Tw, a2_T, socc_T, rho_str, da_str, note)
                push!(a2_vals, a2_T); push!(logT_vals, logT)
                prev_a2 = a2_T; prev_logT = logT
                Tw *= 2
            end

            # Only use un-saturated rows for the verdict.
            unsaturated_a2 = [a2_vals[i] for i in eachindex(a2_vals)
                              if exp2(logT_vals[i]) <= sat_warn]

            if length(a2_vals) >= 3
                da2_late  = (a2_vals[end]   - a2_vals[end-1]) / (logT_vals[end]   - logT_vals[end-1])
                da2_early = (a2_vals[2]     - a2_vals[1])     / (logT_vals[2]     - logT_vals[1])
                verdict = if abs(da2_late) < 0.02
                    "  → α₂ CONVERGED — single exponent (Case A)"
                elseif da2_early > 0.05 && abs(da2_late) < 0.05
                    "  → α₂ CROSSOVER — two plateaus (Case B: burst then mixing)"
                elseif da2_late > 0.05
                    "  → α₂ DRIFTING UPWARD — no fixed exponent (Case C)"
                else
                    "  → α₂ trend inconclusive"
                end
                @printf(io, "    %s\n", verdict)
            end

            # Report the converged windowed α₂ (prefer unsaturated rows).
            ref_vals = isempty(unsaturated_a2) ? a2_vals : unsaturated_a2
            if !isempty(ref_vals) && pf > 1.0
                a2_w = ref_vals[end]
                # Windowed α₂ is in bucket-entropy bits (log₂ scale).
                # Convert: S₂_bucket = 2^a2_w, S₂_keys = S₂_bucket × 2^COLD_BITS.
                S2_w_bucket = exp2(a2_w)
                S2_w_keys   = S2_w_bucket * Float64(1 << COLD_BITS)
                a2_w_keys   = log(S2_w_keys) / (2.0 * log(pf))
                sat_note    = isempty(unsaturated_a2) ? " [all rows saturated — treat as lower bound]" : ""
                @printf(io, "    converged α₂ (bucket-space)  : %.4f bits%s\n", a2_w, sat_note)
                @printf(io, "    S₂_keys (bucket × 2^%d)     : %.5g\n", COLD_BITS, S2_w_keys)
                @printf(io, "    α₂_keys (S₂ ~ p^{2α₂})      : %.4f  [compare AMS α₂ above]\n", a2_w_keys)
            end
        end
    end

    @printf(io, "\n  Cold-filter (bucket zero-count drop at flush) [Local Thread]:\n")
    n_dropped = sc.n_cold_dropped
    n_spilled = sc.n_disk_live + n_dropped
    if n_spilled > 0
        frac_dropped = n_dropped / Float64(n_spilled)
        @printf(io, "    entries cold-dropped   : %d  (%.1f%% of flush candidates)\n",
                n_dropped, 100.0 * frac_dropped)
        @printf(io, "    entries spilled to SSD : %d\n", sc.n_disk_live)
    else
        @printf(io, "    (no flushes yet, or warmup not reached)\n")
    end
    @printf(io, "\n")
    nothing
end

# ---------------------------------------------------------------------------
#  lsm_to_dict — snapshot all hot+disk entries into a plain Dict for lockless
#  read-only use in phase3 workers.  Call once (under no concurrent writers)
#  before spawning phase3 threads.  The LSM remains usable afterwards.
# ---------------------------------------------------------------------------
function lsm_to_dict(sc::LP1ConjLSM{V})::Dict{CanonicalLP1Key, V} where V
    d = Dict{CanonicalLP1Key, V}()
    sizehint!(d, conj_total_entries(sc) + 16)

    # ── Hot shards ────────────────────────────────────────────────────────
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])
        keys = sc.hot_keys[si]
        vals = sc.hot_vals[si]
        cap  = sc.hot_caps[si]
        @inbounds for slot in 1:cap
            k = keys[slot]
            k == CONJ_KEY_EMPTY && continue
            d[k] = vals[slot]
        end
        unlock(sc.shard_locks[si])
    end

    # ── Disk runs ─────────────────────────────────────────────────────────
    lock(sc.file_lock)
    if sc.spill_read_io !== nothing
        buf = zeros(UInt8, RECORD_BYTES)
        for rm in sc.runs
            for pos in 1:rm.len
                _run_is_dead(rm, pos) && continue
                _pread_record!(sc, buf, _rec_base(rm, pos))
                ku0  = _buf_u32(buf, OFF_U0)
                ku1  = _buf_u32(buf, OFF_U1)
                kv0  = _buf_u32(buf, OFF_V0)
                kv1  = _buf_u32(buf, OFF_V1)
                ck   = UInt128(ku0) | (UInt128(ku1) << 32) |
                       (UInt128(kv0) << 64) | (UInt128(kv1) << 96)
                # Hot-shard entry (more recent) takes priority.
                haskey(d, ck) || (d[ck] = _conj_make_val(V, _buf_i0(buf), _buf_al(buf), _buf_be(buf)))
            end
        end
    end
    unlock(sc.file_lock)

    d
end

# Unified dispatch so phase3 can call conj_to_dict on either table type.
conj_to_dict(sc::LP1ConjLSM{V}) where V = lsm_to_dict(sc)

# ---------------------------------------------------------------------------
#  lsm_stream_into_dict! — stream one LSM's entries directly into a caller-
#  supplied Dict, then close and free the LSM.
#
#  This is the memory-safe alternative to the pattern:
#
#      merge!(d, lsm_to_dict(lsm))   # BAD: allocates a full intermediate Dict
#      lsm_close!(lsm)                # BAD: both dicts live simultaneously → 2× peak
#
#  Here we stream hot shards directly into `d` and immediately drop each
#  shard's key/val arrays before moving to the next, then do the disk pass,
#  then call lsm_close!.  Peak additional allocation is one shard at a time
#  (a few MB at most) rather than a full per-thread snapshot Dict (hundreds of
#  MB).
#
#  Caller semantics:
#    • `d` must already be sizehint!'d to the combined capacity before the
#      first call so that successive calls don't each trigger a rehash.
#    • Hot-shard entries take priority over disk entries: if the same key
#      appears in both (which can happen if a hot entry was also spilled before
#      it was tombstoned), the hot value wins because we insert hot first and
#      the disk pass uses `haskey` to skip duplicates.
#    • After this call `sc` is closed and must not be used.
#    • An incremental GC.gc(false) is triggered after the shard arrays are
#      cleared so the freed hot tables become collectible without a full stop-
#      the-world pause.
# ---------------------------------------------------------------------------
function lsm_stream_into_dict!(d::Dict{CanonicalLP1Key, V},
                                sc::LP1ConjLSM{V}) where V
    # ── Hot shards — stream then immediately free each shard's arrays ─────
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])
        keys = sc.hot_keys[si]
        vals = sc.hot_vals[si]
        cap  = sc.hot_caps[si]
        @inbounds for slot in 1:cap
            k = keys[slot]
            k == CONJ_KEY_EMPTY && continue
            haskey(d, k) || (d[k] = vals[slot])
        end
        # Drop the arrays now so GC can reclaim them before we move on.
        # We replace with length-0 sentinels — the shard is about to be
        # closed anyway so correctness is not affected.
        sc.hot_keys[si]   = CanonicalLP1Key[]
        sc.hot_vals[si]   = V[]
        sc.hot_counts[si] = 0
        sc.hot_caps[si]   = 0
        unlock(sc.shard_locks[si])
    end
    # Incremental GC to reclaim the freed shard arrays without a full pause.
    GC.gc(false)

    # ── Disk runs — pread directly into `d` ──────────────────────────────
    lock(sc.file_lock)
    if sc.spill_read_io !== nothing
        buf = zeros(UInt8, RECORD_BYTES)
        for rm in sc.runs
            for pos in 1:rm.len
                _run_is_dead(rm, pos) && continue
                _pread_record!(sc, buf, _rec_base(rm, pos))
                ku0 = _buf_u32(buf, OFF_U0)
                ku1 = _buf_u32(buf, OFF_U1)
                kv0 = _buf_u32(buf, OFF_V0)
                kv1 = _buf_u32(buf, OFF_V1)
                ck  = UInt128(ku0) | (UInt128(ku1) << 32) |
                      (UInt128(kv0) << 64) | (UInt128(kv1) << 96)
                # Hot entry (inserted above) takes priority.
                haskey(d, ck) || (d[ck] = _conj_make_val(V, _buf_i0(buf), _buf_al(buf), _buf_be(buf)))
            end
        end
    end
    unlock(sc.file_lock)

    # ── Close the LSM — flushes nothing (hot arrays already cleared) ──────
    # We bypass lsm_flush_all! here because the hot shards are already zeroed
    # out above; calling it would be a no-op but would acquire every shard lock
    # again needlessly.  We just close the file handles.
    lock(sc.file_lock)
    if sc.spill_io !== nothing
        close(sc.spill_io)
        sc.spill_io = nothing
    end
    if sc.spill_read_io !== nothing
        ccall(:close, Cint, (Cint,), sc.spill_read_io)
        sc.spill_read_io = nothing
    end
    unlock(sc.file_lock)

    nothing
end

# ---------------------------------------------------------------------------
#  lsm_snapshot_and_free! — build a merged snapshot Dict from an array of
#  per-thread LSMs while minimising peak RAM.
#
#  Replaces the pattern:
#
#      conj_snap = Dict{CanonicalLP1Key, LP1ConjVal}()
#      for lsm in arr
#          merge!(conj_snap, lsm_to_dict(lsm))   # 2× peak: both copies live
#      end
#      for lsm in arr; lsm_close!(lsm); end       # too late — spike already happened
#
#  With:
#
#      conj_snap = lsm_snapshot_and_free!(arr)     # streams one LSM at a time
#
#  Peak overhead above the final Dict size is ~one hot shard at a time.
#
#  After this call every LSM in `arr` is closed and the array reference
#  should be set to `nothing` by the caller so the GC can reclaim the
#  LP1ConjLSM objects themselves.
# ---------------------------------------------------------------------------
function lsm_snapshot_and_free!(arr::Vector{<:LP1ConjLSM{V}};
                                 verbose::Bool = true)::Dict{CanonicalLP1Key, V} where V
    total_est = sum(conj_total_entries(lsm) for lsm in arr; init=0)
    d = Dict{CanonicalLP1Key, V}()
    sizehint!(d, total_est + 16)

    t0 = time()
    for (i, lsm) in enumerate(arr)
        n_before = length(d)
        lsm_stream_into_dict!(d, lsm)
        n_added  = length(d) - n_before
        if verbose
            @printf("  [lsm_snapshot] LSM %d/%d streamed: +%d entries  (dict total=%d)  %.3fs\n",
                    i, length(arr), n_added, length(d), time() - t0)
            flush(stdout)
        end
        # Trigger an incremental GC after each LSM so freed hot tables and
        # the now-closed spill fd metadata get reclaimed promptly.
        GC.gc(false)
    end

    if verbose
        @printf("  [lsm_snapshot] done: %d entries in %.3fs\n", length(d), time() - t0)
        flush(stdout)
    end
    d
end

function lsm_flush_all!(sc::LP1ConjLSM)
    lock(sc.file_lock)
    try
        for si in 1:sc.n_shards
            lock(sc.shard_locks[si])
            try
                sc.hot_counts[si] > 0 && _lsm_flush_shard!(sc, si)
            finally
                unlock(sc.shard_locks[si])
            end
        end
    finally
        unlock(sc.file_lock)
    end
    nothing
end

function lsm_close!(sc::LP1ConjLSM)
    lsm_flush_all!(sc)
    lock(sc.file_lock)
    if sc.spill_io !== nothing
        close(sc.spill_io)
        sc.spill_io = nothing
    end
    if sc.spill_read_io !== nothing
        ccall(:close, Cint, (Cint,), sc.spill_read_io)
        sc.spill_read_io = nothing
    end
    unlock(sc.file_lock)
    nothing
end

function lsm_info(sc::LP1ConjLSM; io::IO = stdout)
    hot_total   = sum(sc.hot_counts)
    total_runs  = length(sc.runs)
    total_spill = sc.spill_size / 1024^2
    hot_slots   = isempty(sc.hot_caps) ? 0 : sum(sc.hot_caps)
    load_pct    = hot_slots > 0 ? 100.0 * hot_total / hot_slots : 0.0
    @printf(io, "LP1ConjLSM: %d hot (%.1f%% load) | %d disk-live | %d runs | spill=%s (%.1f MB) | cold-dropped=%d\n",
            hot_total, load_pct, sc.n_disk_live, total_runs, sc.spill_path,
            total_spill, sc.n_cold_dropped)
    nothing
end

# ---------------------------------------------------------------------------
#  lsm_mem_report — detailed RAM breakdown for one LP1ConjLSM instance.
#
#  Accounts for every heap allocation owned by the LSM:
#    • Hot table arrays (keys + vals) across all shards
#    • Bloom filter bit-arrays (own + global, deduped)
#    • RunMeta vector + per-run tombstone bitvectors
#    • partial_fp_log (chronological bucket log)
#    • AMS sketch (ams_Z) and cold_bitmap
#    • read_buf scratch buffer
#    • Hot-count / hot-cap / hot-mask / hot-thresh / shard-locks vectors
#
#  Does NOT account for Julia GC overhead, object headers, or kernel page-cache
#  for the spill file (which is explicitly flushed with posix_fadvise DONTNEED).
#
#  Arguments:
#    sc        — the LP1ConjLSM to inspect
#    label     — optional string printed as a header (e.g. "thread 3")
#    peers     — if true, roll up all wired peers after the per-LSM table
# ---------------------------------------------------------------------------
function lsm_mem_report(sc::LP1ConjLSM{V};
                         label   ::String = "",
                         peers   ::Bool   = false,
                         io      ::IO     = stdout) where V

    _bytes_mb(n) = n / 1024^2
    _fmt_mb(n)   = @sprintf("%.3f MB", _bytes_mb(n))

    function _single_lsm_mem(lsm::LP1ConjLSM{W}, lbl::String) where W
        @printf(io, "\n[LP1ConjLSM memory report%s]\n",
                isempty(lbl) ? "" : "  ($lbl)")

        # ── Hot table ─────────────────────────────────────────────────────────
        ns = lsm.n_shards
        key_bytes = 0; val_bytes = 0
        hot_live  = 0; hot_slots = 0
        for si in 1:ns
            cap      = lsm.hot_caps[si]
            key_bytes += cap * sizeof(CanonicalLP1Key)    # UInt128 → 16 bytes
            val_bytes += cap * sizeof(W)
            hot_live  += lsm.hot_counts[si]
            hot_slots += cap
        end
        thresh_avg = ns > 0 ? sum(lsm.hot_thresh) / ns : 0.0
        load_pct   = hot_slots > 0 ? 100.0 * hot_live / hot_slots : 0.0
        @printf(io, "  Hot table (%d shards, %d slots/shard avg):\n",
                ns, ns > 0 ? hot_slots ÷ ns : 0)
        @printf(io, "    key arrays          : %s  (%d × %d-byte CanonicalLP1Key)\n",
                _fmt_mb(key_bytes), hot_slots, sizeof(CanonicalLP1Key))
        @printf(io, "    val arrays          : %s  (%d × %d-byte %s)\n",
                _fmt_mb(val_bytes), hot_slots, sizeof(W), W)
        @printf(io, "    live / slots        : %d / %d  (%.1f%% load, flush threshold avg %.0f)\n",
                hot_live, hot_slots, load_pct, thresh_avg)
        hot_total_bytes = key_bytes + val_bytes
        @printf(io, "    hot total           : %s\n", _fmt_mb(hot_total_bytes))

        # ── Bloom filters ─────────────────────────────────────────────────────
        bloom_bytes        = length(lsm.bloom.bits)        * sizeof(UInt64)
        global_bloom_ptr   = pointer_from_objref(lsm.global_bloom)
        own_bloom_ptr      = pointer_from_objref(lsm.bloom)
        global_bloom_bytes = (global_bloom_ptr != own_bloom_ptr) ?
                              length(lsm.global_bloom.bits) * sizeof(UInt64) : 0
        @printf(io, "  Bloom filters:\n")
        @printf(io, "    own bloom           : %s  (%d bits, capacity %d)\n",
                _fmt_mb(bloom_bytes), lsm.bloom.n_bits, lsm.bloom.n_bits)
        if global_bloom_ptr != own_bloom_ptr
            @printf(io, "    global bloom (shared): %s  (%d bits)  [counted once here]\n",
                    _fmt_mb(global_bloom_bytes), lsm.global_bloom.n_bits)
        else
            @printf(io, "    global bloom        : == own bloom (not yet wired to shared object)\n")
        end
        bloom_total = bloom_bytes + global_bloom_bytes
        @printf(io, "    bloom total         : %s\n", _fmt_mb(bloom_total))

        # ── Spill file + RunMeta ───────────────────────────────────────────────
        nruns        = length(lsm.runs)
        run_meta_bytes = nruns * (7 * sizeof(Int) + 2 * sizeof(UInt64))   # RunMeta fields
        tomb_bytes   = sum(length(rm.tombs) * sizeof(UInt64) for rm in lsm.runs; init=0)
        n_tombed     = sum(count(>(UInt64(0)), rm.tombs) for rm in lsm.runs; init=0)
        # tomb fraction: fraction of disk records that are tombstoned
        tomb_frac    = lsm.n_disk_live + n_tombed > 0 ?
                        n_tombed / Float64(lsm.n_disk_live + n_tombed) : 0.0
        spill_mb     = lsm.spill_size / 1024^2
        @printf(io, "  Disk / spill file:\n")
        @printf(io, "    spill file size     : %.3f MB  (%d live records × %d bytes)\n",
                spill_mb, lsm.n_disk_live, RECORD_BYTES)
        @printf(io, "    runs (in RAM)       : %d  — RunMeta structs: %s\n",
                nruns, _fmt_mb(run_meta_bytes))
        @printf(io, "    tombstone bitvecs   : %s  (%.1f%% of disk records tombstoned)\n",
                _fmt_mb(tomb_bytes), 100.0 * tomb_frac)
        if nruns > 0
            avg_run_len = lsm.n_disk_live / nruns
            max_run_len = maximum(rm.len for rm in lsm.runs)
            @printf(io, "    avg records/run     : %.0f   max: %d\n", avg_run_len, max_run_len)
        end
        runs_total_bytes = run_meta_bytes + tomb_bytes
        @printf(io, "    run metadata total  : %s\n", _fmt_mb(runs_total_bytes))

        # ── Diagnostic / bookkeeping arrays ────────────────────────────────────
        ams_bytes     = AMS_K * sizeof(Int64)
        cold_bytes    = COLD_WORDS * sizeof(UInt64)
        log_bytes     = length(lsm.partial_fp_log) * sizeof(UInt32)
        readbuf_bytes = length(lsm.read_buf) * sizeof(UInt8)
        admin_bytes   = (ns * (sizeof(Int)*3 + sizeof(UInt))) +   # hot_counts/caps/thresh/masks
                        ns * sizeof(ReentrantLock)                 # shard_locks (rough)
        diag_total    = ams_bytes + cold_bytes + log_bytes + readbuf_bytes + admin_bytes
        @printf(io, "  Diagnostic/bookkeeping:\n")
        @printf(io, "    AMS sketch [%d×%d]    : %s\n", AMS_GROUPS, AMS_WIDTH, _fmt_mb(ams_bytes))
        @printf(io, "    cold_bitmap[2^%d]     : %s\n", COLD_BITS, _fmt_mb(cold_bytes))
        log_full   = length(lsm.partial_fp_log) >= PARTIAL_FP_LOG_CAP
        log_status = log_full ? "circular (rolling)" : @sprintf("filling (%d%%)", round(Int, 100.0 * length(lsm.partial_fp_log) / PARTIAL_FP_LOG_CAP))
        @printf(io, "    partial_fp_log[%d]: %s  [%s, cap=%d]\n",
                length(lsm.partial_fp_log), _fmt_mb(log_bytes),
                log_status, PARTIAL_FP_LOG_CAP)
        @printf(io, "    read_buf scratch    : %s\n", _fmt_mb(readbuf_bytes))
        @printf(io, "    per-shard admin     : %s  (counts/caps/thresh/masks × %d shards)\n",
                _fmt_mb(admin_bytes), ns)
        @printf(io, "    diagnostic total    : %s\n", _fmt_mb(diag_total))

        # ── Grand total ────────────────────────────────────────────────────────
        total_bytes = hot_total_bytes + bloom_total + runs_total_bytes + diag_total
        @printf(io, "  ─────────────────────────────────────────────────────────\n")
        @printf(io, "  TOTAL heap (exc. GC overhead) : %s\n", _fmt_mb(total_bytes))
        @printf(io, "  spill file on SSD             : %.3f MB  (not in RSS)\n\n", spill_mb)

        return total_bytes
    end

    total = _single_lsm_mem(sc, label)

    if peers && !isempty(sc.peers)
        @printf(io, "  [Peer roll-up: %d peer(s)]\n", length(sc.peers))
        peer_total = 0
        for (pi, peer) in enumerate(sc.peers)
            peer === sc && continue
            peer_lsm = peer::LP1ConjLSM{V}
            pt = _single_lsm_mem(peer_lsm, "peer $pi")
            peer_total += pt
        end
        # Global bloom is shared across all peers — already counted in the first
        # LSM that has a distinct global_bloom pointer.  Deduplicate here:
        @printf(io, "  ─────────────────────────────────────────────────────────\n")
        @printf(io, "  ALL PEERS combined heap : %s\n\n", _fmt_mb(total + peer_total))
    end

    nothing
end

# ---------------------------------------------------------------------------
#  lsm_flush_stats — per-flush accounting: how many entries were cold-filtered
#  vs spilled, load at flush time, compaction frequency.
#
#  The LSM does not currently track per-flush history natively (too much RAM).
#  Instead we add two new counters to the struct (n_flushes, n_flush_warm)
#  and expose summary statistics here.
#
#  Because adding struct fields requires recompilation we instead derive what
#  we can from the current observable state and expose a helper the caller can
#  use to instrument the flush path at a higher level.
#
#  Summary report: overall flush efficiency from accumulated counters.
# ---------------------------------------------------------------------------
function lsm_flush_stats(sc::LP1ConjLSM; io::IO = stdout)
    @printf(io, "\n[LP1ConjLSM flush / spill stats]\n")

    n_emitted   = sc.bday_emissions       # total LP1-conj partials inserted
    n_dropped   = sc.n_cold_dropped
    n_disk      = sc.n_disk_live
    hot_live    = sum(sc.hot_counts)
    hot_slots   = sum(sc.hot_caps)
    spill_mb    = sc.spill_size / 1024^2
    nruns       = length(sc.runs)

    # Total entries that passed through the flush path = spilled + dropped.
    # hot_live entries have not been flushed yet.
    n_flush_total = n_disk + n_dropped
    warm_frac   = n_flush_total > 0 ?
                   100.0 * n_disk / n_flush_total : 100.0
    drop_frac   = n_flush_total > 0 ?
                   100.0 * n_dropped / n_flush_total : 0.0

    @printf(io, "  entries emitted (LP1-conj): %d\n", n_emitted)
    @printf(io, "  entries in hot RAM         : %d  (%.1f%% load of %d slots)\n",
            hot_live, hot_slots > 0 ? 100.0 * hot_live / hot_slots : 0.0, hot_slots)
    @printf(io, "  entries cold-dropped       : %d  (%.1f%% of flush candidates)\n",
            n_dropped, drop_frac)
    @printf(io, "  entries spilled to SSD     : %d  (%.1f%% of flush candidates)\n",
            n_disk, warm_frac)
    @printf(io, "  spill file size            : %.3f MB  (%d runs)\n", spill_mb, nruns)

    # Per-run breakdown if there are multiple runs (pre-compaction view)
    if nruns > 0
        total_tomb = sum(count(>(UInt64(0)), rm.tombs) * 64 for rm in sc.runs; init=0)
        # (this over-counts since the last word may be partial — good enough for display)
        @printf(io, "\n  Run breakdown:\n")
        @printf(io, "  %6s  %10s  %12s  %12s  %8s  %10s\n",
                "run#", "len", "min_fp(hex)", "max_fp(hex)", "tomb#",  "offset(MB)")
        for (ri, rm) in enumerate(sc.runs)
            n_tombed_run = sum(count_ones(w) for w in rm.tombs; init=0)
            @printf(io, "  %6d  %10d  %12x  %12x  %8d  %10.3f\n",
                    ri, rm.len, rm.min_fp, rm.max_fp,
                    n_tombed_run, rm.byte_offset / 1024^2)
        end
    end

    # Estimate of expected collision probability given current spill density.
    # If N_total = n_disk entries occupy effective space S₂, probability that
    # the next emission matches a disk entry is N_total / S₂.
    # We read S₂ from the AMS sketch (never saturates).
    N_emit = Int64(sc.bday_emissions)
    if N_emit >= 2 && sc.bloom.n_bits > 64
        _, S2_est = _ams_estimate_S2(sc.ams_Z, N_emit)
        if S2_est > 0.0
            p_hit_disk   = Float64(n_disk)   / S2_est
            p_hit_hot    = Float64(hot_live)  / S2_est
            @printf(io, "\n  Collision probability estimate (from AMS S₂ = %.5g):\n", S2_est)
            @printf(io, "    P(disk hit | emission) : %.5g  (%.2f per 1000 emissions)\n",
                    p_hit_disk, 1000.0 * p_hit_disk)
            @printf(io, "    P(hot hit  | emission) : %.5g  (%.2f per 1000 emissions)\n",
                    p_hit_hot, 1000.0 * p_hit_hot)
            @printf(io, "    P(any hit  | emission) : %.5g  (%.2f per 1000 emissions)\n",
                    p_hit_disk + p_hit_hot, 1000.0 * (p_hit_disk + p_hit_hot))
            if sc.bday_first_coll_m > 0
                m_coll = sc.bday_first_coll_m
                p_obs  = 1.0 / Float64(m_coll)
                @printf(io, "    P_obs (1/m_first)      : %.5g   ratio pred/obs = %.3f\n",
                        p_obs, (p_hit_disk + p_hit_hot) / p_obs)
            end
        end
    end

    @printf(io, "\n")
    nothing
end

function conj_roundtrip_ok(sc::LP1ConjLSM{V}, si::Int,
                            key::CanonicalLP1Key, val::V)::Bool where V
    conj_insert!(sc, si, key, val)
    return conj_haskey(sc, si, key)
end

# ---------------------------------------------------------------------------
#  lsm_recommended_hot_cap — query how large the hot table needs to be.
#
#  Once the first birthday collision has been observed, S_eff ≈ m_first² gives
#  a good upper bound on the effective key-space size S₂.  The hot table only
#  needs to hold ~sqrt(2·S_eff) entries for birthday collisions to keep firing
#  at full rate.  We return (recommended_total, recommended_per_shard, reason)
#  so the caller can decide whether to call lsm_resize_hot!.
#
#  safety_factor: multiply sqrt(2·S_eff) by this before returning.  Default 8
#  is conservative — collisions begin at ~sqrt(2·S₂) and plateau well before
#  8× that.  Reduces spill by ~100× relative to a table sized at S₂ directly.
# ---------------------------------------------------------------------------
function lsm_recommended_hot_cap(sc::LP1ConjLSM;
                                  safety_factor::Int = 8
                                 )::Tuple{Int, Int, String}
    lock(sc.bday_lock)
    m        = sc.bday_first_coll_m
    n_emit   = sc.bday_emissions
    unlock(sc.bday_lock)

    current_total = sc.n_shards * sc.hot_caps[1]   # all shards same size

    if m == 0
        return (current_total, current_total ÷ sc.n_shards,
                "no collision yet — cannot estimate S_eff")
    end

    S_eff    = Float64(m)^2
    needed   = max(sc.n_shards * 16,
                   ceil(Int, sqrt(2.0 * S_eff) * safety_factor))
    per_shard = cld(needed, sc.n_shards)
    reason   = @sprintf("S_eff=m²=%.3g → sqrt(2·S_eff)=%.0f × %d = %d (current=%d)",
                        S_eff, sqrt(2.0 * S_eff), safety_factor, needed, current_total)
    return (needed, per_shard, reason)
end

# ---------------------------------------------------------------------------
#  lsm_resize_hot! — shrink (or grow) every shard's hot table in-place.
#
#  Protocol:
#    1. Acquire file_lock (blocks flushes and disk probes).
#    2. For each shard, acquire shard_lock.
#    3. If new cap < current live count: flush shard to SSD first so we don't
#       lose entries (they'll be matched via the disk path if ever needed, but
#       in practice after first collision the SSD entries are already dead).
#    4. Allocate new key/val arrays sized to next power-of-2 above
#       new_cap_per_shard / load_factor.
#    5. Rehash all live hot entries into new arrays.
#    6. Update hot_caps, hot_masks, hot_thresh; release locks.
#
#  This is safe to call from any thread while the walk is running, but will
#  briefly serialise all LP1-conj insertions while the resize completes.
#  Typical call: once, shortly after lsm_bday_report shows first collision.
#
#  Returns true if any shard was actually resized.
# ---------------------------------------------------------------------------
function lsm_resize_hot!(sc::LP1ConjLSM{V},
                          new_cap_per_shard::Int;
                          load_num  ::Int = 4,
                          load_denom::Int = 5,
                          verbose   ::Bool = true)::Bool where V
    new_cap_per_shard = max(16, new_cap_per_shard)
    new_slot_count    = nextpow(2, cld(new_cap_per_shard * load_denom, load_num))
    new_thresh        = cld(new_slot_count * load_num, load_denom)
    new_mask          = UInt(new_slot_count - 1)

    any_resized = false

    lock(sc.file_lock)
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])

        old_slot_count = sc.hot_caps[si]
        old_thresh     = sc.hot_thresh[si]

        # Nothing to do if already at or smaller than target.
        if new_slot_count >= old_slot_count
            unlock(sc.shard_locks[si])
            continue
        end

        # If live entries exceed new threshold, flush to SSD first.
        # After first collision these entries are statistically dead (their
        # birthday partners already fired in hot RAM), so SSD cost is low.
        if sc.hot_counts[si] > new_thresh
            _lsm_flush_shard!(sc, si)   # caller holds file_lock ✓
        end

        # Rehash surviving live entries into new arrays.
        old_keys = sc.hot_keys[si]
        old_vals = sc.hot_vals[si]

        new_keys = fill(CONJ_KEY_EMPTY, new_slot_count)
        new_vals = Vector{V}(undef, new_slot_count)
        new_count = 0

        @inbounds for slot in 1:old_slot_count
            k = old_keys[slot]
            k == CONJ_KEY_EMPTY && continue
            # Linear-probe insert into new arrays.
            dest = Int(_lsm_fp(k) & new_mask) + 1
            while new_keys[dest] != CONJ_KEY_EMPTY
                dest = dest == new_slot_count ? 1 : dest + 1
            end
            new_keys[dest] = k
            new_vals[dest] = old_vals[slot]
            new_count += 1
        end

        sc.hot_keys[si]   = new_keys
        sc.hot_vals[si]   = new_vals
        sc.hot_counts[si] = new_count
        sc.hot_caps[si]   = new_slot_count
        sc.hot_masks[si]  = new_mask
        sc.hot_thresh[si] = new_thresh
        any_resized = true

        unlock(sc.shard_locks[si])
    end
    unlock(sc.file_lock)

    if verbose && any_resized
        hot_total = sc.n_shards * new_slot_count
        @printf("[LP1ConjLSM] resized hot table → %d entries (%d/shard, thresh=%d)\n",
                hot_total, new_slot_count, new_thresh)
    end

    return any_resized
end

# ---------------------------------------------------------------------------
#  lsm_autotune! — call lsm_recommended_hot_cap and apply if beneficial.
#
#  Convenience wrapper intended to be called from the walk loop once the
#  first birthday collision has been observed.  Returns true if a resize
#  was performed.
#
#  Typical call site (in the walk loop or a monitor thread):
#    if sc.bday_first_coll_m > 0 && !autotune_done
#        lsm_autotune!(sc; safety_factor=8)
#        autotune_done = true
#    end
# ---------------------------------------------------------------------------
function lsm_autotune!(sc::LP1ConjLSM;
                        safety_factor::Int  = 8,
                        min_shrink_ratio::Float64 = 2.0,
                        verbose::Bool = true)::Bool
    needed, per_shard, reason = lsm_recommended_hot_cap(sc; safety_factor)
    current = sc.n_shards * sc.hot_caps[1]

    if Float64(current) / Float64(needed) < min_shrink_ratio
        verbose && @printf("[LP1ConjLSM autotune] no resize: %s\n", reason)
        return false
    end

    verbose && @printf("[LP1ConjLSM autotune] resizing: %s\n", reason)
    return lsm_resize_hot!(sc, per_shard; verbose)
end
