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

# No HDF5 dependency — plain IO + mmap only.
using Mmap

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

    # Disk spill — flat binary file + mmap
    runs        ::Vector{RunMeta}
    file_lock   ::ReentrantLock
    spill_path  ::String
    spill_io    ::Union{IOStream, Nothing}   # open for writing/appending
    spill_mmap  ::Vector{UInt8}             # current read mmap (empty if no runs)
    spill_size  ::Int                       # current file size in bytes

    # Bloom filter
    bloom       ::BloomFilter

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
        load_denom   ::Int  = 5
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
        UInt8[],   # empty mmap until first flush
        0,         # spill_size
        BloomFilter(max_entries),
        n_shards, max_entries, 0,
        amortized,
        # birthday diagnostics
        0, 0.0, 0, 0.0, ReentrantLock(),
        # occupancy estimator
        0, 0,
        # Rényi-2 estimator (2^14 = 16384 buckets — ~64 KB, negligible)
        zeros(UInt32, 1 << RENYI_BITS), Int64(0), Int64(0)
    )
end

function LP1ConjLSM(
        ell           ::Integer;
        amortized     ::Bool   = true,
        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_lsm.bin"),
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
        amortized = amortized
    )
end

# ---------------------------------------------------------------------------
#  Mmap helpers
# ---------------------------------------------------------------------------

# Re-mmap the spill file for reading.  Called after every flush while holding
# file_lock.  If file is empty, spill_mmap stays as UInt8[].
function _lsm_remap!(sc::LP1ConjLSM)
    sc.spill_size == 0 && return
    # Flush write buffer before mapping
    flush(sc.spill_io)
    sc.spill_mmap = Mmap.mmap(sc.spill_io, Vector{UInt8}, sc.spill_size)
    nothing
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

    # Collect live entries
    fps  = Vector{UInt64}(undef, n)
    u0s  = Vector{UInt32}(undef, n)
    u1s  = Vector{UInt32}(undef, n)
    v0s  = Vector{UInt32}(undef, n)
    v1s  = Vector{UInt32}(undef, n)
    i0s  = Vector{UInt16}(undef, n)
    als  = Vector{UInt64}(undef, n)
    bes  = Vector{UInt64}(undef, n)

    idx  = 0
    keys = sc.hot_keys[si]
    vals = sc.hot_vals[si]
    @inbounds for slot in 1:sc.hot_caps[si]
        k = keys[slot]
        k == CONJ_KEY_EMPTY && continue
        idx += 1
        fp = _lsm_fp(k)
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
    idx == n || throw(AssertionError("_lsm_flush_shard!: collected $idx != $n"))

    # Sort by fingerprint
    order = sortperm(fps)

    # Build packed binary buffer and write to spill file
    buf = zeros(UInt8, n * RECORD_BYTES)
    @inbounds for i in 1:n
        oi = order[i]
        _write_record!(buf, (i-1)*RECORD_BYTES,
                       fps[oi], u0s[oi], u1s[oi], v0s[oi], v1s[oi],
                       i0s[oi], als[oi], bes[oi])
    end

    byte_offset = sc.spill_size
    write(sc.spill_io, buf)
    sc.spill_size += n * RECORD_BYTES

    # Update Bloom filter
    for i in 1:n
        set_bloom!(sc.bloom, fps[order[i]])
    end

    # Register run
    min_fp = fps[order[1]]
    max_fp = fps[order[n]]
    push!(sc.runs, RunMeta(length(sc.runs)+1, byte_offset, n, min_fp, max_fp))
    sc.n_disk_live += n

    # Remap for reads
    _lsm_remap!(sc)

    # Compact runs if fan-out is getting large.
    # Merging keeps _lsm_disk_find to a single binary search rather than
    # iterating over O(flushes) runs, each with its own binary search.
    length(sc.runs) >= 16 && _lsm_compact!(sc)

    # Reset hot shard
    fill!(sc.hot_keys[si], CONJ_KEY_EMPTY)
    sc.hot_counts[si] = 0

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

    # Snapshot the mmap and keep it alive for the entire merge loop.
    # Without this, _lsm_remap! (called by a flush in another thread, or even
    # by the GC finalizer reclaiming the previous sc.spill_mmap assignment)
    # can munmap the pages we are actively reading → SIGBUS.
    mm         = sc.spill_mmap
    total_live = sc.n_disk_live
    total_live == 0 && return

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
    for ri in 1:nruns
        rm  = sc.runs[ri]
        pos = cursors[ri]
        pos > rm.len && continue
        base = _rec_base(rm, pos)
        fp   = _rec_fp(mm, base)
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

    GC.@preserve mm begin
    while !isempty(heap)
        fp, ri, pos = _heap_pop!(heap)
        rm   = sc.runs[ri]
        base = _rec_base(rm, pos)

        # Copy record into write buffer, flushing if full.
        if wbuf_pos + RECORD_BYTES > COMPACT_WRITE_BUF_BYTES
            write(tmp_io, view(wbuf, 1:wbuf_pos))
            wbuf_pos = 0
        end
        @inbounds for b in 0:RECORD_BYTES-1
            wbuf[wbuf_pos + b + 1] = mm[base + b + 1]
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
            base2 = _rec_base(rm, pos)
            fp2   = _rec_fp(mm, base2)
            _heap_push!(heap, (fp2, ri, pos))
        end
    end
    end # GC.@preserve mm

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

    _lsm_remap!(sc)
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
    mm = sc.spill_mmap
    ku0 = UInt32(key & 0x00000000ffffffff)
    ku1 = UInt32((key >> 32)  & 0x00000000ffffffff)
    kv0 = UInt32((key >> 64)  & 0x00000000ffffffff)
    kv1 = UInt32((key >> 96)  & 0x00000000ffffffff)

    GC.@preserve mm begin
    for (ri, rm) in enumerate(sc.runs)
        (fp_target < rm.min_fp || fp_target > rm.max_fp) && continue

        # Binary search on fp within this run's slice of the mmap.
        # All arithmetic is pure pointer math — no allocations.
        lo = 1; hi = rm.len
        @inbounds while lo < hi
            mid = (lo + hi) >>> 1
            mid_fp = _rec_fp(mm, _rec_base(rm, mid))
            if mid_fp < fp_target
                lo = mid + 1
            else
                hi = mid
            end
        end
        # lo is the first position where fp >= fp_target
        lo > rm.len && continue
        _rec_fp(mm, _rec_base(rm, lo)) != fp_target && continue

        # Scan matching fingerprints
        pos = lo
        @inbounds while pos <= rm.len
            base = _rec_base(rm, pos)
            _rec_fp(mm, base) != fp_target && break
            if !_run_is_dead(rm, pos) &&
               _rec_key_match(mm, base, ku0, ku1, kv0, kv1)
                i0_v = _mmap_u16(mm, base + OFF_I0)
                al_v = _mmap_u64(mm, base + OFF_AL)
                be_v = _mmap_u64(mm, base + OFF_BE)
                return (true, ri, pos, i0_v, al_v, be_v)
            end
            pos += 1
        end
    end
    end # GC.@preserve mm
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
    hot_found = lock(sc.shard_locks[si]) do
        _lsm_hot_find(sc, si, key) != 0
    end
    hot_found && return true
    fp = _lsm_fp(key)
    !bloom_maybe_has(sc.bloom, fp) && return false
    found, _, _, _, _, _ = lock(sc.file_lock) do
        _lsm_disk_find(sc, key, fp)
    end
    found
end

function conj_getval(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    slot = lock(sc.shard_locks[si]) do
        _lsm_hot_find(sc, si, key)
    end
    slot != 0 && return @inbounds sc.hot_vals[si][slot]
    fp = _lsm_fp(key)
    found, _, _, i0_v, al_v, be_v = lock(sc.file_lock) do
        _lsm_disk_find(sc, key, fp)
    end
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end

function conj_pop!(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    result = Ref{V}()
    hot_found = lock(sc.shard_locks[si]) do
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            result[] = @inbounds sc.hot_vals[si][slot]
            _lsm_hot_delete!(sc, si, slot)
            true
        else
            false
        end
    end
    hot_found && return result[]
    fp = _lsm_fp(key)
    found, ri, pos, i0_v, al_v, be_v = lock(sc.file_lock) do
        res = _lsm_disk_find(sc, key, fp)
        res[1] && _lsm_disk_delete!(sc, res[2], res[3])
        res
    end
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end

function conj_pop_safe(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::Union{V,Nothing} where V
    result = Ref{V}()
    hot_found = lock(sc.shard_locks[si]) do
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            result[] = @inbounds sc.hot_vals[si][slot]
            _lsm_hot_delete!(sc, si, slot)
            true
        else
            false
        end
    end
    hot_found && return result[]
    fp = _lsm_fp(key)
    found, ri, pos, i0_v, al_v, be_v = lock(sc.file_lock) do
        res = _lsm_disk_find(sc, key, fp)
        res[1] && _lsm_disk_delete!(sc, res[2], res[3])
        res
    end
    found || return nothing
    _conj_make_val(V, i0_v, al_v, be_v)
end

function conj_insert!(sc::LP1ConjLSM{V}, si::Int,
                       key::CanonicalLP1Key, val::V)::Bool where V
    needs_flush = lock(sc.shard_locks[si]) do
        if sc.hot_counts[si] >= sc.hot_thresh[si]
            true
        else
            _lsm_hot_insert!(sc, si, key, val)
            false
        end
    end
    needs_flush || return true
    lock(sc.file_lock) do
        lock(sc.shard_locks[si]) do
            sc.hot_counts[si] >= sc.hot_thresh[si] && _lsm_flush_shard!(sc, si)
            _lsm_hot_insert!(sc, si, key, val)
        end
    end
    true
end

# ---------------------------------------------------------------------------
#  conj_insert_or_pop! — atomic check+act, no TOCTOU race
# ---------------------------------------------------------------------------
function conj_insert_or_pop!(sc::LP1ConjLSM{V}, si::Int,
                              key::CanonicalLP1Key, val::V)::Union{V,Nothing} where V

    fp = _lsm_fp(key)

    # --- Birthday / occupancy / Rényi diagnostics: count this emission -------
    now_t = time_ns() * 1e-9
    lock(sc.bday_lock) do
        if sc.bday_emissions == 0
            sc.bday_t0 = now_t
        end
        sc.bday_emissions += 1
        sc.occ_n           += 1

        # Rényi-2: increment the fingerprint bucket and update Σcᵢ, Σcᵢ².
        # We update as:  Σcᵢ² += 2·cᵢ + 1  (because (c+1)² - c² = 2c+1).
        rb = Int(fp >> RENYI_SHIFT) + 1          # 1-based bucket index
        old_c = Int(sc.renyi_counts[rb])
        sc.renyi_counts[rb] = UInt32(min(typemax(UInt32), old_c + 1))
        sc.renyi_sum_c  += Int64(1)
        sc.renyi_sum_c2 += Int64(2 * old_c + 1)

        # Occupancy: a new unique key is one whose bucket was zero before this
        # emission.  This is exact for RENYI_BITS-bit resolution (each bucket
        # covers 2^(64-RENYI_BITS) keys, so old_c==0 is a conservative proxy
        # for "bucket not previously seen").  It slightly over-counts unique
        # keys when RENYI_BITS is small and the walk is very diffuse, but at
        # the S~p^1.6–1.9 scales we care about the error is negligible.
        if old_c == 0
            sc.occ_unique += 1
        end
    end
    # -------------------------------------------------------------------------

    # Fast path: Bloom says key is definitely not on disk (or no disk yet).
    # Only need the shard lock — no file_lock contention.
    if isempty(sc.runs) || !bloom_maybe_has(sc.bloom, fp)
        fast_result = lock(sc.shard_locks[si]) do
            slot = _lsm_hot_find(sc, si, key)
            if slot != 0
                v = @inbounds sc.hot_vals[si][slot]
                _lsm_hot_delete!(sc, si, slot)
                Some(v)
            elseif sc.hot_counts[si] < sc.hot_thresh[si]
                _lsm_hot_insert!(sc, si, key, val)
                nothing
            else
                :needs_flush
            end
        end
        if fast_result !== :needs_flush
            if fast_result isa Some
                _bday_record_collision!(sc, now_t)
                return something(fast_result)
            end
            return nothing
        end
        # Shard is full and needs a flush — fall through to slow path.
        # (Flush requires file_lock; we do not re-check Bloom after flush since
        # this key was not on disk before and we hold no lock in between — still
        # safe to insert without a disk probe.)
        final_result = Ref{Union{V,Nothing}}(nothing)
        lock(sc.file_lock) do
            lock(sc.shard_locks[si]) do
                # Re-check hot after acquiring locks (another thread may have
                # inserted or flushed in the window).
                slot = _lsm_hot_find(sc, si, key)
                if slot != 0
                    v = @inbounds sc.hot_vals[si][slot]
                    _lsm_hot_delete!(sc, si, slot)
                    final_result[] = v
                    return
                end
                if sc.hot_counts[si] >= sc.hot_thresh[si]
                    _lsm_flush_shard!(sc, si)
                end
                _lsm_hot_insert!(sc, si, key, val)
            end
        end
        if final_result[] !== nothing
            _bday_record_collision!(sc, now_t)
        end
        return final_result[]
    end

    # Slow path: Bloom says key may be on disk.  Need file_lock for consistent
    # view of runs + mmap during the disk probe.
    final_result = Ref{Union{V,Nothing}}(nothing)
    lock(sc.file_lock) do
        lock(sc.shard_locks[si]) do
            slot = _lsm_hot_find(sc, si, key)
            if slot != 0
                v = @inbounds sc.hot_vals[si][slot]
                _lsm_hot_delete!(sc, si, slot)
                final_result[] = v
                return
            end
            # Re-check Bloom inside lock in case runs changed since the
            # lockless read above.
            if !isempty(sc.runs) && bloom_maybe_has(sc.bloom, fp)
                found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
                if found
                    _lsm_disk_delete!(sc, ri, pos)
                    final_result[] = _conj_make_val(V, i0_v, al_v, be_v)
                    return
                end
            end
            if sc.hot_counts[si] >= sc.hot_thresh[si]
                _lsm_flush_shard!(sc, si)
            end
            _lsm_hot_insert!(sc, si, key, val)
            final_result[] = nothing
        end
    end
    if final_result[] !== nothing
        _bday_record_collision!(sc, now_t)
    end
    final_result[]
end

# ---------------------------------------------------------------------------
#  Birthday diagnostics helpers
# ---------------------------------------------------------------------------

# Called on every confirmed LP1-conj collision.  Only records the *first* one.
@inline function _bday_record_collision!(sc::LP1ConjLSM, now_t::Float64)
    lock(sc.bday_lock) do
        sc.bday_first_coll_m == 0 || return   # already recorded
        sc.bday_first_coll_m = sc.bday_emissions
        sc.bday_first_coll_t = now_t
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
    m, t_coll, t0, n_emitted, occ_u, occ_n, rc, rsc, rsc2 = lock(sc.bday_lock) do
        (sc.bday_first_coll_m,
         sc.bday_first_coll_t,
         sc.bday_t0,
         sc.bday_emissions,
         sc.occ_unique,
         sc.occ_n,
         copy(sc.renyi_counts),
         sc.renyi_sum_c,
         sc.renyi_sum_c2)
    end

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
    nothing
end

function lsm_flush_all!(sc::LP1ConjLSM)
    lock(sc.file_lock) do
        for si in 1:sc.n_shards
            lock(sc.shard_locks[si]) do
                sc.hot_counts[si] > 0 && _lsm_flush_shard!(sc, si)
            end
        end
    end
    nothing
end

function lsm_close!(sc::LP1ConjLSM)
    lsm_flush_all!(sc)
    lock(sc.file_lock) do
        if sc.spill_io !== nothing
            close(sc.spill_io)
            sc.spill_io = nothing
        end
    end
    nothing
end

function lsm_info(sc::LP1ConjLSM; io::IO = stdout)
    hot_total = sum(sc.hot_counts)
    @printf(io, "LP1ConjLSM: %d hot | %d disk-live | %d runs | spill=%s (%.1f MB)\n",
            hot_total, sc.n_disk_live, length(sc.runs), sc.spill_path,
            sc.spill_size / 1024^2)
    nothing
end

function conj_roundtrip_ok(sc::LP1ConjLSM{V}, si::Int,
                            key::CanonicalLP1Key, val::V)::Bool where V
    conj_insert!(sc, si, key, val)
    return conj_haskey(sc, si, key)
end
