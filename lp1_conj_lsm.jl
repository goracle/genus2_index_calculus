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

# Rényi-2 bucket granularity.  We keep 2^RENYI_BITS buckets in a UInt32 array,
# indexed by the top RENYI_BITS bits of the 64-bit fingerprint.
# 14 bits → 16384 buckets ≈ 64 KB.  Saturates at 2^32-1 per bucket (overflow
# safe: if a bucket saturates it over-counts S₂ slightly, conservative).
const RENYI_BITS  = 14
const RENYI_SHIFT = 64 - RENYI_BITS   # right-shift to get bucket index
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
    spill_read_io ::Union{IOStream, Nothing}   # open for reading (seeks); separate fd
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

    # Rényi-2 / collision-entropy estimator — S₂ = (Σ cᵢ)² / Σ cᵢ²
    # We maintain a count-map from fingerprint bucket → multiplicity.
    # Buckets are fp >> RENYI_SHIFT (top RENYI_BITS bits of the 64-bit fingerprint)
    # so the table stays small (2^RENYI_BITS entries) while still tracking
    # concentration faithfully.  renyi_sum_c is Σcᵢ, renyi_sum_c2 is Σcᵢ².
    renyi_counts        ::Vector{UInt32}   # length 2^RENYI_BITS; count per bucket
    renyi_sum_c         ::Int64            # Σ cᵢ  (== total collisions + emissions)
    renyi_sum_c2        ::Int64            # Σ cᵢ²

    # Time-ordered partial stream — one UInt16 bucket index per partial, in
    # chronological order of insertion.  Used post-walk by lsm_bday_report to
    # compute dyadic-window α₂(T) scaling diagnostics on the partial stream.
    # At 3.7M partials × 2 bytes = ~7 MB — negligible.  Written under bday_lock.
    partial_fp_log      ::Vector{UInt16}

    # Cold-filter stats: entries silently dropped at flush time because their
    # Rényi bucket had zero observed count (i.e. never received an emission).
    # These would be pure SSD waste — they can never produce a birthday collision.
    # Updated under file_lock+shard_lock (same as the flush path).
    n_cold_dropped      ::Int
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
        bloom_cap    ::Int  = max_entries
    ) where V

    function make_shard(cap_entries::Int)
        slot_count = max(16, nextpow(2, cld(cap_entries * load_denom, load_num)))
        keys = fill(CONJ_KEY_EMPTY, slot_count)
        vals = Vector{V}(undef, slot_count)
        thresh = cld(slot_count * load_num, load_denom)
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
        # Rényi-2 estimator (2^14 = 16384 buckets — ~64 KB, negligible)
        zeros(UInt32, 1 << RENYI_BITS), Int64(0), Int64(0),
        UInt16[],             # partial_fp_log
        0                     # n_cold_dropped
    )
end

function LP1ConjLSM(
        ell           ::Integer;
        amortized     ::Bool   = true,
        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_shards"),
        max_hot_ram_mb::Int    = 512
    )
    cap = min(LP1_CONJ_CAP_MULTIPLIER * Int(min(ell, p)), LP1_CONJ_CAP_MAX)
    V   = amortized ? LP1ConjVal : LP1ConjValFull
    bytes_per_entry = amortized ? 33 : 43
    max_hot_entries = max(N_CONJ_SHARDS * 16,
                          (max_hot_ram_mb * 1024 * 1024) ÷ bytes_per_entry)
    hot_shard_entries = max(16, max_hot_entries ÷ N_CONJ_SHARDS)
    @printf("[LP1ConjLSM] hot_cap=%d entries (%d/shard), spill→%s\n",
            hot_shard_entries * N_CONJ_SHARDS, hot_shard_entries, spill_path)
    LP1ConjLSM{V}(
        N_CONJ_SHARDS, hot_shard_entries, cap, spill_path;
        amortized = amortized,
        bloom_cap = max_hot_entries
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
        sc.spill_read_io = open(sc.spill_path, "r")
    end
    nothing
end

# Read exactly RECORD_BYTES from the read-side fd at byte offset `off` (0-based)
# into a caller-supplied RECORD_BYTES-length buffer.  Caller holds file_lock.
@inline function _pread_record!(sc::LP1ConjLSM, buf::Vector{UInt8}, off::Int)
    seek(sc.spill_read_io, off)
    readbytes!(sc.spill_read_io, buf, RECORD_BYTES)
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
    # S_naive for the LP1-conj key space is p²/2.  The Rényi-2 diagnostics show
    # alpha_2 ≈ 0.727, i.e. S₂ ~ p^{1.45} — roughly p^{0.55} fewer distinct
    # hot buckets than the full keyspace.  Most fp-buckets are cold: they receive
    # emissions but will never be the other side of a birthday collision.
    # Spilling cold-bucket entries to SSD is pure waste: they consume I/O and
    # disk space but can never produce a match.
    #
    # Filter: after COLD_FILTER_WARMUP total emissions, drop any entry whose
    # RENYI_BITS-bit fp bucket has zero observed count in renyi_counts[].  A
    # lockless read of renyi_counts is safe — counts are only ever incremented
    # (never cleared), so a stale zero means the bucket is genuinely cold at the
    # time of this flush; the tiny race window where a bucket first becomes hot
    # right as we flush costs at most one missed entry per bucket per flush cycle,
    # which is negligible.
    #
    # COLD_FILTER_WARMUP: require at least 2^RENYI_BITS emissions (~16k) before
    # filtering, so the counts have had a chance to stabilise.  Below this
    # threshold every bucket looks cold and we'd drop everything.
    cold_filter_warmup = (1 << RENYI_BITS) * 4   # 4 passes over the bucket array
    use_cold_filter = sc.bday_emissions >= cold_filter_warmup
    rc = sc.renyi_counts   # lockless snapshot reference — see comment above

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
        # Cold-filter: skip entries in unobserved Rényi buckets.
        if use_cold_filter
            rb = Int(fp >> RENYI_SHIFT) + 1   # 1-based bucket
            if rc[rb] == UInt32(0)
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

    # Compact runs if fan-out is getting large.
    # Merging keeps _lsm_disk_find to a single binary search rather than
    # iterating over O(flushes) runs, each with its own binary search.
    length(sc.runs) >= 16 && _lsm_compact!(sc)

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
    length(sc.runs) <= 1 && return

    total_live = sc.n_disk_live
    total_live == 0 && return
    sc.spill_read_io === nothing && return   # no spill file yet

    # Per-run cursors: next live position to emit from each run.
    # Advance past any leading tombstones on initialisation.
    nruns   = length(sc.runs)
    cursors = Vector{Int}(undef, nruns)   # next pos (1-based) to read, or rm.len+1 if exhausted
    for ri in 1:nruns
        rm  = sc.runs[ri]
        pos = 1
        while pos <= rm.len && _run_is_dead(rm, pos)
            pos += 1
        end
        cursors[ri] = pos
    end

    # Seed the min-heap with the first live record from each run.
    heap = Tuple{UInt64,Int,Int}[]   # (fp, ri, pos)
    sizehint!(heap, nruns)
    rec_buf_seed = zeros(UInt8, RECORD_BYTES)
    for ri in 1:nruns
        rm  = sc.runs[ri]
        pos = cursors[ri]
        pos > rm.len && continue
        _pread_record!(sc, rec_buf_seed, _rec_base(rm, pos))
        fp = _buf_fp(rec_buf_seed)
        _heap_push!(heap, (fp, ri, pos))
    end

    # Open temp file; stream merged records into it via a write buffer.
    tmp_path  = sc.spill_path * ".compact"
    tmp_io    = open(tmp_path, "w+")
    wbuf      = Vector{UInt8}(undef, COMPACT_WRITE_BUF_BYTES)
    wbuf_pos  = 0   # bytes currently in wbuf

    actual    = 0
    first_fp  = UInt64(0)
    last_fp   = UInt64(0)

    rec_scratch = Vector{UInt8}(undef, RECORD_BYTES)

    rec_buf_merge = zeros(UInt8, RECORD_BYTES)
    while !isempty(heap)
        fp, ri, pos = _heap_pop!(heap)
        rm   = sc.runs[ri]

        # Read record into scratch, copy to write buffer.
        _pread_record!(sc, rec_buf_merge, _rec_base(rm, pos))
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

        # Advance cursor past next tombstones, push next live record if any.
        pos += 1
        while pos <= rm.len && _run_is_dead(rm, pos)
            pos += 1
        end
        cursors[ri] = pos
        if pos <= rm.len
            _pread_record!(sc, rec_buf_merge, _rec_base(rm, pos))
            fp2 = _buf_fp(rec_buf_merge)
            _heap_push!(heap, (fp2, ri, pos))
        end
    end

    # Flush remaining write buffer.
    wbuf_pos > 0 && write(tmp_io, view(wbuf, 1:wbuf_pos))
    flush(tmp_io)
    close(tmp_io)

    # Atomically replace spill file.
    close(sc.spill_io)
    mv(tmp_path, sc.spill_path; force=true)
    sc.spill_io    = open(sc.spill_path, "a+")
    sc.spill_size  = actual * RECORD_BYTES
    sc.n_disk_live = actual

    # Rebuild single run meta (no tombstones — all dead records were skipped).
    sc.runs = actual > 0 ? [RunMeta(1, 0, actual, first_fp, last_fp)] : RunMeta[]

    # Reopen read-side fd on the new compacted file.
    if sc.spill_read_io !== nothing
        close(sc.spill_read_io)
    end
    sc.spill_read_io = open(sc.spill_path, "r")
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
    buf = zeros(UInt8, RECORD_BYTES)

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

function conj_haskey(sc::LP1ConjLSM, si::Int, key::CanonicalLP1Key)::Bool
    lock(sc.shard_locks[si])
    hot_found = _lsm_hot_find(sc, si, key) != 0
    unlock(sc.shard_locks[si])
    hot_found && return true
    fp = _lsm_fp(key)
    !bloom_maybe_has(sc.bloom, fp) && return false
    lock(sc.shard_locks[si])
    found, _, _, _, _, _ = _lsm_disk_find(sc, key, fp)
    unlock(sc.shard_locks[si])
    found
end

function conj_getval(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        v = @inbounds sc.hot_vals[si][slot]
        unlock(sc.shard_locks[si])
        return v
    end
    fp = _lsm_fp(key)
    found, _, _, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
    unlock(sc.shard_locks[si])
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end

function conj_pop!(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        result = @inbounds sc.hot_vals[si][slot]
        _lsm_hot_delete!(sc, si, slot)
        unlock(sc.shard_locks[si])
        return result
    end
    fp = _lsm_fp(key)
    found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
    found && _lsm_disk_delete!(sc, ri, pos)
    unlock(sc.shard_locks[si])
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end

function conj_pop_safe(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::Union{V,Nothing} where V
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        result = @inbounds sc.hot_vals[si][slot]
        _lsm_hot_delete!(sc, si, slot)
        unlock(sc.shard_locks[si])
        return result
    end
    fp = _lsm_fp(key)
    found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
    found && _lsm_disk_delete!(sc, ri, pos)
    unlock(sc.shard_locks[si])
    found || return nothing
    _conj_make_val(V, i0_v, al_v, be_v)
end

function conj_insert!(sc::LP1ConjLSM{V}, si::Int,
                       key::CanonicalLP1Key, val::V)::Bool where V
    lock(sc.shard_locks[si])
    if sc.hot_counts[si] >= sc.hot_thresh[si]
        _lsm_flush_shard!(sc, si)   # caller holds shard_locks[si] ✓
    end
    _lsm_hot_insert!(sc, si, key, val)
    unlock(sc.shard_locks[si])
    true
end

# ---------------------------------------------------------------------------
#  conj_insert_or_pop! — atomic check+act, no TOCTOU race
# ---------------------------------------------------------------------------
function conj_insert_or_pop!(sc::LP1ConjLSM{V}, si::Int,
                              key::CanonicalLP1Key, val::V)::Union{V,Nothing} where V

    fp = _lsm_fp(key)

    # --- Birthday / occupancy / Rényi diagnostics: count this emission -------
    # IMPORTANT: use explicit lock/unlock rather than `lock(f) do...end`.
    # The closure form allocates a heap object for the captured environment,
    # which can trigger GC *while the lock is held*.  If the GC then tries to
    # stop-the-world, any other thread blocked on bday_lock cannot reach a
    # safepoint (it is spinning on the lock, not at an allocation site), causing
    # a GC safepoint deadlock that manifests as an intermittent hang on Ctrl-C.
    #
    # Explicit lock/unlock is allocation-free on the fast path.  All arithmetic
    # inside the critical section is kept strictly allocation-free:
    #   * old_c + 1 stays Int; saturation via ifelse avoids min(UInt32,Int)
    #     which promotes to Int64 and boxes (ijl_box_int64 in the hang trace).
    #   * Int64 arithmetic on renyi_sum_c / renyi_sum_c2 is unboxed because
    #     the struct fields are declared ::Int64.
    now_t = time_ns() * 1e-9
    lock(sc.bday_lock)
    try
        if sc.bday_emissions == 0
            sc.bday_t0 = now_t
        end
        sc.bday_emissions += 1
        sc.occ_n           += 1

        # Rényi-2: increment the fingerprint bucket and update Σcᵢ, Σcᵢ².
        # We update as:  Σcᵢ² += 2·cᵢ + 1  (because (c+1)² - c² = 2c+1).
        rb    = Int(fp >> RENYI_SHIFT) + 1          # 1-based bucket index
        old_c = Int(sc.renyi_counts[rb])
        # Saturating increment: stay allocation-free by avoiding min(UInt32,Int)
        # which boxes.  ifelse is a pure integer select with no allocation.
        sc.renyi_counts[rb] = ifelse(old_c < Int(typemax(UInt32)),
                                     UInt32(old_c + 1), typemax(UInt32))
        sc.renyi_sum_c  += Int64(1)
        sc.renyi_sum_c2 += Int64(2 * old_c + 1)

        # Occupancy: a new unique key is one whose bucket was zero before this
        # emission.
        if old_c == 0
            sc.occ_unique += 1
        end

        # Time-series log: record the fp bucket index for α₂ scaling diagnostics.
        push!(sc.partial_fp_log, UInt16(rb - 1))   # 0-based bucket, fits UInt16
    finally
        unlock(sc.bday_lock)
    end
    # -------------------------------------------------------------------------

    # Fast path: Bloom says key is definitely not on disk (or no disk yet).
    # Only need the shard lock — no file_lock contention.
    if !bloom_maybe_has(sc.global_bloom, fp)
        lock(sc.shard_locks[si])
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            v = @inbounds sc.hot_vals[si][slot]
            _lsm_hot_delete!(sc, si, slot)
            unlock(sc.shard_locks[si])
            _bday_record_collision!(sc, now_t)
            return v
        elseif sc.hot_counts[si] < sc.hot_thresh[si]
            _lsm_hot_insert!(sc, si, key, val)
            unlock(sc.shard_locks[si])
            return nothing
        end
        unlock(sc.shard_locks[si])
        # Shard is full and needs a flush — fall through to slow path.
        lock(sc.file_lock)
        lock(sc.shard_locks[si])
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            v = @inbounds sc.hot_vals[si][slot]
            _lsm_hot_delete!(sc, si, slot)
            unlock(sc.shard_locks[si])
            unlock(sc.file_lock)
            _bday_record_collision!(sc, now_t)
            return v
        end
        if sc.hot_counts[si] >= sc.hot_thresh[si]
            _lsm_flush_shard!(sc, si)
        end
        _lsm_hot_insert!(sc, si, key, val)
        unlock(sc.shard_locks[si])
        unlock(sc.file_lock)
        return nothing
    end

    # Slow path: Bloom says key may be on disk.  Need file_lock for consistent
    # view of runs + mmap during the disk probe.
    lock(sc.file_lock)
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        v = @inbounds sc.hot_vals[si][slot]
        _lsm_hot_delete!(sc, si, slot)
        unlock(sc.shard_locks[si])
        unlock(sc.file_lock)
        _bday_record_collision!(sc, now_t)
        return v
    end
    # Re-check own Bloom inside lock in case runs changed since the lockless read above.
    if !isempty(sc.runs) && bloom_maybe_has(sc.bloom, fp)
        found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
        if found
            _lsm_disk_delete!(sc, ri, pos)
            result_v = _conj_make_val(V, i0_v, al_v, be_v)
            unlock(sc.shard_locks[si])
            unlock(sc.file_lock)
            _bday_record_collision!(sc, now_t)
            return result_v
        end
    end
    unlock(sc.shard_locks[si])
    unlock(sc.file_lock)

    # Cross-peer probe: global_bloom fired but key not in our hot table or disk.
    # Check each peer (excluding self) — probe their hot shard then their disk.
    for peer in sc.peers
        peer === sc && continue
        peer_lsm = peer::LP1ConjLSM{V}
        # Hot probe first (cheap, no file_lock needed)
        lock(peer_lsm.shard_locks[si])
        pslot = _lsm_hot_find(peer_lsm, si, key)
        if pslot != 0
            pv = @inbounds peer_lsm.hot_vals[si][pslot]
            _lsm_hot_delete!(peer_lsm, si, pslot)
            unlock(peer_lsm.shard_locks[si])
            _bday_record_collision!(sc, now_t)
            return pv
        end
        unlock(peer_lsm.shard_locks[si])
        # Disk probe (needs peer's file_lock)
        !isempty(peer_lsm.runs) || continue
        bloom_maybe_has(peer_lsm.bloom, fp) || continue
        lock(peer_lsm.file_lock)
        lock(peer_lsm.shard_locks[si])
        pslot2 = _lsm_hot_find(peer_lsm, si, key)
        if pslot2 != 0
            pv = @inbounds peer_lsm.hot_vals[si][pslot2]
            _lsm_hot_delete!(peer_lsm, si, pslot2)
            unlock(peer_lsm.shard_locks[si])
            unlock(peer_lsm.file_lock)
            _bday_record_collision!(sc, now_t)
            return pv
        end
        if !isempty(peer_lsm.runs) && bloom_maybe_has(peer_lsm.bloom, fp)
            pfound, pri, ppos, pi0_v, pal_v, pbe_v = _lsm_disk_find(peer_lsm, key, fp)
            if pfound
                _lsm_disk_delete!(peer_lsm, pri, ppos)
                result_v = _conj_make_val(V, pi0_v, pal_v, pbe_v)
                unlock(peer_lsm.shard_locks[si])
                unlock(peer_lsm.file_lock)
                _bday_record_collision!(sc, now_t)
                return result_v
            end
        end
        unlock(peer_lsm.shard_locks[si])
        unlock(peer_lsm.file_lock)
    end

    # Not found anywhere — store in own LSM.
    lock(sc.file_lock)
    lock(sc.shard_locks[si])
    if sc.hot_counts[si] >= sc.hot_thresh[si]
        _lsm_flush_shard!(sc, si)
    end
    _lsm_hot_insert!(sc, si, key, val)
    unlock(sc.shard_locks[si])
    unlock(sc.file_lock)
    return nothing
end

# ---------------------------------------------------------------------------
#  Birthday diagnostics helpers
# ---------------------------------------------------------------------------

# Called on every confirmed LP1-conj collision.  Only records the *first* one.
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
    lock(sc.bday_lock)
    m        = sc.bday_first_coll_m
    t_coll   = sc.bday_first_coll_t
    t0       = sc.bday_t0
    n_emitted= sc.bday_emissions
    occ_u    = sc.occ_unique
    occ_n    = sc.occ_n
    rc       = copy(sc.renyi_counts)
    rsc      = sc.renyi_sum_c
    rsc2     = sc.renyi_sum_c2
    unlock(sc.bday_lock)

    lam = r / 2.0          # LP1-conj emission rate
    pf  = Float64(p)

    @printf(io, "\n[LP1-conj birthday diagnostics]\n")
    @printf(io, "  total LP1-conj emitted : %d\n", n_emitted)

    if m == 0
        @printf(io, "  first collision        : not yet observed\n")
        t_naive = sqrt(2.0) * pf / r
        m_naive = lam * t_naive
        @printf(io, "  naive prediction       : m_first ~ %.3g,  t_first ~ %.3g s\n",
                m_naive, t_naive)
        if t0 > 0.0
            t_elapsed = (time_ns() * 1e-9) - t0
            frac = t_elapsed / t_naive
            @printf(io, "  elapsed / t_naive      : %.4f  (%s)\n",
                    frac,
                    frac >= 1.0 ? "OVERDUE — support may be smaller than p^2" :
                                  "still within naive expectation")
        end
        @printf(io, "\n")
        return
    end

    t_first   = t_coll - t0
    S_eff     = Float64(m)^2
    S_naive   = pf^2 / 2.0
    ratio     = S_eff / S_naive
    alpha     = log(Float64(m)) / log(pf)
    m_naive   = sqrt(S_naive)
    t_naive   = m_naive / lam

    @printf(io, "  first collision at     : m = %d  (t_wall = %.3f s)\n", m, t_first)
    @printf(io, "  S_eff  = m^2           : %.6g\n", S_eff)
    @printf(io, "  S_naive = p^2/2        : %.6g\n", S_naive)
    @printf(io, "  S_eff / S_naive        : %.5g\n", ratio)
    @printf(io, "  alpha  (S ~ p^{2*alpha}): %.4f   [alpha=1 ↔ S~p^2, alpha=0.75 ↔ S~p^1.5, ...]\n", alpha)
    @printf(io, "  t_first (observed)     : %.3f s\n", t_first)
    @printf(io, "  t_first (naive p^2/2)  : %.3f s   (= sqrt(2)*p/r)\n", t_naive)
    @printf(io, "  t_obs / t_naive        : %.4f\n", t_first / t_naive)
    if ratio < 0.1
        @printf(io, "  *** support is << p^2: effective space ~ p^{%.2f} ***\n", 2*alpha)
    elseif ratio < 0.5
        @printf(io, "  support is moderately smaller than p^2\n")
    else
        @printf(io, "  support is consistent with naive p^2 model\n")
    end

    # ── Occupancy estimator: U(N) = S(1 - e^{-N/S}), solve for S ─────────────
    # U = occ_unique (distinct RENYI_BITS-resolution buckets seen), N = occ_n.
    # Solve S*(1-e^{-N/S}) = U by bisection over [U, max(N^2, U*10)].
    # The occupancy estimator is much stabler than the first-collision estimator
    # when N >> 1 but still has finite variance at moderate N.
    @printf(io, "\n  Occupancy estimator (U(N) = S·(1−e^{−N/S})):\n")
    if occ_n >= 10 && occ_u >= 1 && occ_u < occ_n
        # Scale U and N up by 2^RENYI_BITS to get actual key-space counts.
        scale   = Float64(1 << RENYI_BITS)
        U_f     = Float64(occ_u) * scale
        N_f     = Float64(occ_n)
        # Bisect: f(S) = S*(1-exp(-N/S)) - U = 0; f is increasing in S.
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
        @printf(io, "    unique buckets U       : %d  (N=%d, scale=2^%d)\n",
                occ_u, occ_n, RENYI_BITS)
        @printf(io, "    S_occ (MLE)            : %.6g\n", S_occ)
        @printf(io, "    S_occ / S_naive        : %.5g\n", r_occ)
        @printf(io, "    alpha_occ (S ~ p^{2α}) : %.4f\n", a_occ)
    else
        @printf(io, "    (need ≥10 emissions with some collisions)\n")
    end

    # ── Rényi-2 / collision-entropy estimator: S₂ = (Σcᵢ)² / Σcᵢ² ───────────
    # S₂ measures the effective support under the walk-induced measure.
    # If all weight concentrates on k keys, S₂ → k.  Compare S₂ ~ p^{2α₂}.
    # When S_eff (birthday) >> S₂ (entropy), burst structure dominates.
    @printf(io, "\n  Rényi-2 / collision-entropy estimator (S₂ = (Σcᵢ)²/Σcᵢ²):\n")
    if rsc > 0 && rsc2 > 0
        S2      = Float64(rsc)^2 / Float64(rsc2)
        # Scale by 2^RENYI_BITS: each bucket represents ~2^RENYI_BITS keys, so
        # the true S₂ estimate is S2 * scale (under uniform-within-bucket assumption).
        scale   = Float64(1 << RENYI_BITS)
        S2_true = S2 * scale
        r2      = S2_true / S_naive
        a2      = log(S2_true) / (2.0 * log(pf))
        burst_flag = if S_eff > 0.0 && S2_true > 0.0
            ratio_be = S_eff / S2_true
            ratio_be > 4.0 ? @sprintf(" ← BURSTS DOMINATE (birthday %.1f× > entropy)", ratio_be) :
            ratio_be < 0.25 ? " ← ENTROPY > BIRTHDAY (unusual)" :
                              " (birthday ≈ entropy, consistent)"
        else
            ""
        end
        @printf(io, "    Σcᵢ                    : %d  Σcᵢ²=%d\n", rsc, rsc2)
        @printf(io, "    S₂ (bucket-level)      : %.6g\n", S2)
        @printf(io, "    S₂ (key-scaled)        : %.6g\n", S2_true)
        @printf(io, "    S₂ / S_naive           : %.5g\n", r2)
        @printf(io, "    alpha_2 (S₂ ~ p^{2α₂}) : %.4f%s\n", a2, burst_flag)
    else
        @printf(io, "    (no emissions recorded yet)\n")
    end

    @printf(io, "\n")

    # ── α₂ scaling diagnostics on the partial key stream ─────────────────────
    # blog is the chronological sequence of fp-bucket indices (UInt16, 0-based)
    # for every LP1-conj partial inserted.  nb = 2^RENYI_BITS buckets.
    # We compute dyadic-window S₂(T) and S_occ(T) to measure how α₂ scales
    # with observation window — the key question for genus-2 IC asymptotics.
    let blog = copy(sc.partial_fp_log)
        nb     = 1 << RENYI_BITS
        n_blog = length(blog)
        @printf(io, "  LP1-conj partial stream α₂ scaling:\n")
        if n_blog < 64
            @printf(io, "    (need ≥64 partials; got %d)\n\n", n_blog)
        else
            @printf(io, "    nb=%d fp-buckets  N=%d partials\n", nb, n_blog)
            @printf(io, "    window_T    n_events   α₂(T)    S_occ(T)   ρ=S_occ/S₂  dα₂/dlogT\n")

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

                a2_T   = s2_acc   / n_valid
                socc_T = socc_acc / n_valid
                rho_T  = a2_T > 0.0 ? socc_T / a2_T : NaN
                logT   = log2(Float64(Tw))
                da2    = (!isnan(prev_a2) && !isnan(prev_logT) && logT > prev_logT) ?
                         (a2_T - prev_a2) / (logT - prev_logT) : NaN
                da_str  = isnan(da2) ? "        —" : @sprintf("%+9.4f", da2)
                rho_str = isnan(rho_T) ? "         —" : @sprintf("%10.4f", rho_T)
                @printf(io, "    %9d  %9d  %8.4f  %9.4f  %s  %s\n",
                        Tw, n_wins * Tw, a2_T, socc_T, rho_str, da_str)
                push!(a2_vals, a2_T); push!(logT_vals, logT)
                prev_a2 = a2_T; prev_logT = logT
                Tw *= 2
            end

            # Classify convergence
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

            # Translate the converged α₂(T) value to the key-space exponent.
            # Each fp bucket represents ~2^RENYI_BITS keys under uniform assumption,
            # so S₂_keys = S₂_buckets * 2^RENYI_BITS.  Then α₂_keys = log(S₂_keys)/(2·log p).
            if !isempty(a2_vals) && pf > 1.0
                a2_bucket_converged = a2_vals[end]
                S2_bucket = 2.0^a2_bucket_converged
                S2_keys   = S2_bucket * Float64(1 << RENYI_BITS)
                a2_keys   = log(S2_keys) / (2.0 * log(pf))
                @printf(io, "    converged α₂ (bucket-space)  : %.4f bits\n", a2_bucket_converged)
                @printf(io, "    S₂_keys (bucket × 2^%d)     : %.5g\n", RENYI_BITS, S2_keys)
                @printf(io, "    α₂_keys (S₂ ~ p^{2α₂})      : %.4f  [compare birthday α₂ above]\n", a2_keys)
            end
        end
    end

    # ── Cold-filter stats ────────────────────────────────────────────────────
    # The bucket cold-filter (activated after 4×2^RENYI_BITS emissions)
    # drops flush entries whose Rényi fp-bucket has zero observed count.
    # Since S_naive = p²/2 but S₂ ~ p^{2·α₂} (with α₂ < 1), the fraction of
    # hot buckets is ~(2^RENYI_BITS) · S₂ / (p²/2) ≈ p^{2α₂-2}, which is the
    # fraction of entries *not* dropped.  The rest are pure SSD waste.
    @printf(io, "\n  Cold-filter (bucket zero-count drop at flush):\n")
    n_dropped = sc.n_cold_dropped
    n_spilled = sc.n_disk_live + n_dropped   # approximate total that went through flush path
    if n_spilled > 0
        frac_dropped = n_dropped / Float64(n_spilled)
        @printf(io, "    entries cold-dropped   : %d  (%.1f%% of flush candidates)\n",
                n_dropped, 100.0 * frac_dropped)
        @printf(io, "    entries spilled to SSD : %d\n", sc.n_disk_live)
        if pf > 1.0 && rsc > 0 && rsc2 > 0
            # Expected fraction of hot buckets from S₂.
            S2      = Float64(rsc)^2 / Float64(rsc2)
            scale   = Float64(1 << RENYI_BITS)
            S2_true = S2 * scale
            S_naive = pf^2 / 2.0
            expected_hot_frac = S2_true / S_naive
            @printf(io, "    expected hot-frac (S₂/S_naive): %.5g  [actual spilled/total=%.5g]\n",
                    expected_hot_frac, 1.0 - frac_dropped)
        end
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

function lsm_flush_all!(sc::LP1ConjLSM)
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])
        sc.hot_counts[si] > 0 && _lsm_flush_shard!(sc, si)
        unlock(sc.shard_locks[si])
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
        close(sc.spill_read_io)
        sc.spill_read_io = nothing
    end
    unlock(sc.file_lock)
    nothing
end

function lsm_info(sc::LP1ConjLSM; io::IO = stdout)
    hot_total   = sum(sc.hot_counts)
    total_runs  = length(sc.runs)
    total_spill = sc.spill_size / 1024^2
    @printf(io, "LP1ConjLSM: %d hot | %d disk-live | %d runs | spill=%s (%.1f MB) | cold-dropped=%d\n",
            hot_total, sc.n_disk_live, total_runs, sc.spill_path,
            total_spill, sc.n_cold_dropped)
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
