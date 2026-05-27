with open('/home/claire/crypto/lp1_conj_lsm.jl') as f:
    src = f.read()

# ── 1. Drop Mmap ──────────────────────────────────────────────────────────────
src = src.replace(
    '# No HDF5 dependency — plain IO + mmap only.\nusing Mmap\n',
    '# No HDF5 dependency — plain IO only (no mmap, per-shard spill files).\n'
)

# ── 2. Struct: replace single spill_io/spill_mmap/spill_size/file_lock/runs
#    with per-shard vectors ──────────────────────────────────────────────────
src = src.replace(
    '''\
    # Disk spill — flat binary file + mmap
    runs        ::Vector{RunMeta}
    file_lock   ::ReentrantLock
    spill_path  ::String
    spill_io    ::Union{IOStream, Nothing}   # open for writing/appending
    spill_mmap  ::Vector{UInt8}             # current read mmap (empty if no runs)
    spill_size  ::Int                       # current file size in bytes''',
    '''\
    # Disk spill — one spill file per shard, no mmap.
    # shard_locks[si] guards both the hot table and shard si\'s spill state.
    shard_runs      ::Vector{Vector{RunMeta}}          # per-shard run lists
    spill_path      ::String                           # directory prefix
    shard_write_io  ::Vector{Union{IOStream,Nothing}}  # append fd per shard
    shard_read_io   ::Vector{Union{IOStream,Nothing}}  # read fd per shard
    shard_spill_size::Vector{Int}                      # bytes written per shard'''
)

# ── 3. Inner constructor: replace single-spill init with per-shard init ──────
src = src.replace(
    '''\
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
        zeros(UInt32, 1 << RENYI_BITS), Int64(0), Int64(0),
        UInt16[],             # partial_fp_log
        0                     # n_cold_dropped
    )''',
    '''\
    # Ensure spill directory exists; per-shard files created lazily on first flush.
    mkpath(spill_path)

    LP1ConjLSM{V}(
        hot_keys, hot_vals, hot_counts, hot_caps, hot_masks, hot_thresh,
        shard_locks,
        [RunMeta[] for _ in 1:n_shards],   # shard_runs
        spill_path,
        Union{IOStream,Nothing}[nothing for _ in 1:n_shards],  # shard_write_io
        Union{IOStream,Nothing}[nothing for _ in 1:n_shards],  # shard_read_io
        zeros(Int, n_shards),               # shard_spill_size
        BloomFilter(max_entries),
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
    )'''
)

# ── 4. Public constructor: spill_path is now a directory ─────────────────────
src = src.replace(
    '        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_pre.h5")',
    '        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_shards")'
)
# Also fix the old lp1_conj_lsm.bin default if present
src = src.replace(
    '        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_lsm.bin")',
    '        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_shards")'
)

# ── 5. Replace _lsm_remap! with per-shard open helper ────────────────────────
src = src.replace(
    '''\
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
end''',
    '''\
# ---------------------------------------------------------------------------
#  Per-shard spill-file helpers.
#  Caller must hold shard_locks[si].
# ---------------------------------------------------------------------------

# Return the path for shard si\'s spill file.
@inline _shard_spill_path(sc::LP1ConjLSM, si::Int) =
    joinpath(sc.spill_path, @sprintf("shard_%04d.bin", si))

# Ensure write + read fds are open for shard si.  Called after first flush.
function _lsm_open_shard_ios!(sc::LP1ConjLSM, si::Int)
    p = _shard_spill_path(sc, si)
    if sc.shard_write_io[si] === nothing
        mkpath(dirname(p))
        sc.shard_write_io[si] = open(p, "w+")
    end
    if sc.shard_read_io[si] === nothing
        sc.shard_read_io[si] = open(p, "r")
    end
    nothing
end

# Read RECORD_BYTES from shard si\'s read fd at byte offset off (0-based).
@inline function _pread_record!(sc::LP1ConjLSM, si::Int, buf::Vector{UInt8}, off::Int)
    io = sc.shard_read_io[si]
    seek(io, off)
    readbytes!(io, buf, RECORD_BYTES)
    nothing
end

# Field accessors on a scratch buffer.
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
end'''
)

# ── 6. _lsm_flush_shard!: remove file_lock dependency, use per-shard IO ──────
# Replace the write section + remap call
src = src.replace(
    '''\
    byte_offset = sc.spill_size
    write(sc.spill_io, buf)
    sc.spill_size += idx * RECORD_BYTES

    # Update Bloom filter
    for i in 1:idx
        set_bloom!(sc.bloom, fps[order[i]])
    end

    # Register run
    min_fp = fps[order[1]]
    max_fp = fps[order[idx]]
    push!(sc.runs, RunMeta(length(sc.runs)+1, byte_offset, idx, min_fp, max_fp))
    sc.n_disk_live += idx

    # Remap for reads
    _lsm_remap!(sc)

    # Compact runs if fan-out is getting large.
    # Merging keeps _lsm_disk_find to a single binary search rather than
    # iterating over O(flushes) runs, each with its own binary search.
    length(sc.runs) >= 16 && _lsm_compact!(sc)''',
    '''\
    # Open per-shard fds on first flush (lazy init).
    _lsm_open_shard_ios!(sc, si)

    byte_offset = sc.shard_spill_size[si]
    write(sc.shard_write_io[si], buf)
    flush(sc.shard_write_io[si])
    sc.shard_spill_size[si] += idx * RECORD_BYTES

    # Update shared Bloom filter (lockless: bits only ever set).
    for i in 1:idx
        set_bloom!(sc.bloom, fps[order[i]])
    end

    # Register run in this shard\'s run list.
    min_fp = fps[order[1]]
    max_fp = fps[order[idx]]
    push!(sc.shard_runs[si], RunMeta(length(sc.shard_runs[si])+1, byte_offset, idx, min_fp, max_fp))
    sc.n_disk_live += idx

    # Compact this shard\'s runs if fan-out is getting large.
    length(sc.shard_runs[si]) >= 16 && _lsm_compact!(sc, si)'''
)

# ── 7. _lsm_compact!: add si parameter, use per-shard state ──────────────────
src = src.replace(
    '''\
function _lsm_compact!(sc::LP1ConjLSM)
    length(sc.runs) <= 1 && return

    # Snapshot the mmap and keep it alive for the entire merge loop.
    # Without this, _lsm_remap! (called by a flush in another thread, or even
    # by the GC finalizer reclaiming the previous sc.spill_mmap assignment)
    # can munmap the pages we are actively reading → SIGBUS.
    mm         = sc.spill_mmap
    total_live = sc.n_disk_live
    total_live == 0 && return''',
    '''\
function _lsm_compact!(sc::LP1ConjLSM, si::Int)
    length(sc.shard_runs[si]) <= 1 && return
    total_live = sum(rm.len - count(_run_is_dead(rm, p) for p in 1:rm.len)
                     for rm in sc.shard_runs[si]; init=0)
    total_live == 0 && return
    sc.shard_read_io[si] === nothing && return'''
)

src = src.replace(
    '''\
    # Per-run cursors: next live position to emit from each run.
    # Advance past any leading tombstones on initialisation.
    nruns   = length(sc.runs)''',
    '''\
    # Per-run cursors: next live position to emit from each run.
    # Advance past any leading tombstones on initialisation.
    nruns   = length(sc.shard_runs[si])'''
)

src = src.replace(
    '    for ri in 1:nruns\n        rm  = sc.runs[ri]',
    '    for ri in 1:nruns\n        rm  = sc.shard_runs[si][ri]'
)

src = src.replace(
    '    for ri in 1:nruns\n        rm  = sc.runs[ri]\n        pos = cursors[ri]',
    '    for ri in 1:nruns\n        rm  = sc.shard_runs[si][ri]\n        pos = cursors[ri]'
)

# Fix heap seed loop to use per-shard pread
src = src.replace(
    '''\
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
    end''',
    '''\
    # Seed the min-heap with the first live record from each run.
    heap = Tuple{UInt64,Int,Int}[]   # (fp, ri, pos)
    sizehint!(heap, nruns)
    seed_buf = zeros(UInt8, RECORD_BYTES)
    for ri in 1:nruns
        rm  = sc.shard_runs[si][ri]
        pos = cursors[ri]
        pos > rm.len && continue
        _pread_record!(sc, si, seed_buf, _rec_base(rm, pos))
        _heap_push!(heap, (_buf_fp(seed_buf), ri, pos))
    end'''
)

# Fix the tmp file path to be per-shard
src = src.replace(
    '    tmp_path  = sc.spill_path * ".compact"',
    '    tmp_path  = _shard_spill_path(sc, si) * ".compact"'
)

# Fix the merge loop: use per-shard pread, remove GC.@preserve mm
src = src.replace(
    '''\
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
    end # GC.@preserve mm''',
    '''\
    merge_buf = zeros(UInt8, RECORD_BYTES)
    while !isempty(heap)
        fp, ri, pos = _heap_pop!(heap)
        rm   = sc.shard_runs[si][ri]

        _pread_record!(sc, si, merge_buf, _rec_base(rm, pos))
        if wbuf_pos + RECORD_BYTES > COMPACT_WRITE_BUF_BYTES
            write(tmp_io, view(wbuf, 1:wbuf_pos))
            wbuf_pos = 0
        end
        @inbounds for b in 1:RECORD_BYTES
            wbuf[wbuf_pos + b] = merge_buf[b]
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
            _pread_record!(sc, si, merge_buf, _rec_base(rm, pos))
            _heap_push!(heap, (_buf_fp(merge_buf), ri, pos))
        end
    end'''
)

# Fix compact tail: replace single-spill file swap with per-shard
src = src.replace(
    '''\
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
end''',
    '''\
    # Atomically replace this shard\'s spill file.
    shard_path = _shard_spill_path(sc, si)
    close(sc.shard_write_io[si])
    close(sc.shard_read_io[si])
    mv(tmp_path, shard_path; force=true)
    sc.shard_write_io[si]   = open(shard_path, "a+")
    sc.shard_read_io[si]    = open(shard_path, "r")
    dead_before = sum(rm.len for rm in sc.shard_runs[si]) - sc.n_disk_live + sum(rm.len for rm in sc.shard_runs[si][1:end]) - length(sc.shard_runs[si])
    # Recount: n_disk_live was tracking global; adjust for this shard\'s tombstones removed.
    old_shard_disk = sum(rm.len for rm in sc.shard_runs[si]; init=0)
    sc.n_disk_live -= (old_shard_disk - actual)
    sc.shard_spill_size[si] = actual * RECORD_BYTES
    sc.shard_runs[si] = actual > 0 ? [RunMeta(1, 0, actual, first_fp, last_fp)] : RunMeta[]
    nothing
end''',
    1   # only first occurrence
)

# ── 8. _lsm_disk_find: add si, use per-shard runs + pread ────────────────────
src = src.replace(
    '''\
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

        # Binary search on fp within this run\'s slice of the mmap.
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
end''',
    '''\
# Caller must hold shard_locks[si].
function _lsm_disk_find(sc::LP1ConjLSM, si::Int,
                         key::CanonicalLP1Key,
                         fp_target::UInt64)::Tuple{Bool,Int,Int,UInt16,UInt64,UInt64}
    sc.shard_read_io[si] === nothing && return (false, 0, 0, UInt16(0), UInt64(0), UInt64(0))
    ku0 = UInt32(key & 0x00000000ffffffff)
    ku1 = UInt32((key >> 32)  & 0x00000000ffffffff)
    kv0 = UInt32((key >> 64)  & 0x00000000ffffffff)
    kv1 = UInt32((key >> 96)  & 0x00000000ffffffff)
    buf = zeros(UInt8, RECORD_BYTES)

    for (ri, rm) in enumerate(sc.shard_runs[si])
        (fp_target < rm.min_fp || fp_target > rm.max_fp) && continue
        lo = 1; hi = rm.len
        while lo < hi
            mid = (lo + hi) >>> 1
            _pread_record!(sc, si, buf, _rec_base(rm, mid))
            if _buf_fp(buf) < fp_target; lo = mid + 1 else hi = mid end
        end
        lo > rm.len && continue
        _pread_record!(sc, si, buf, _rec_base(rm, lo))
        _buf_fp(buf) != fp_target && continue
        pos = lo
        while pos <= rm.len
            _pread_record!(sc, si, buf, _rec_base(rm, pos))
            _buf_fp(buf) != fp_target && break
            if !_run_is_dead(rm, pos) && _buf_key_match(buf, ku0, ku1, kv0, kv1)
                return (true, ri, pos, _buf_i0(buf), _buf_al(buf), _buf_be(buf))
            end
            pos += 1
        end
    end
    (false, 0, 0, UInt16(0), UInt64(0), UInt64(0))
end'''
)

# ── 9. _lsm_disk_delete!: now only needs shard si, no file_lock ──────────────
src = src.replace(
    '''\
function _lsm_disk_delete!(sc::LP1ConjLSM, ri::Int, pos::Int)
    _run_set_dead!(sc.runs[ri], pos)
    sc.n_disk_live -= 1
    nothing
end''',
    '''\
# Caller must hold shard_locks[si].
function _lsm_disk_delete!(sc::LP1ConjLSM, si::Int, ri::Int, pos::Int)
    _run_set_dead!(sc.shard_runs[si][ri], pos)
    sc.n_disk_live -= 1
    nothing
end'''
)

# ── 10. Public API: remove file_lock, use shard lock for everything ───────────
src = src.replace(
    '''\
function conj_haskey(sc::LP1ConjLSM, si::Int, key::CanonicalLP1Key)::Bool
    lock(sc.shard_locks[si])
    hot_found = _lsm_hot_find(sc, si, key) != 0
    unlock(sc.shard_locks[si])
    hot_found && return true
    fp = _lsm_fp(key)
    !bloom_maybe_has(sc.bloom, fp) && return false
    lock(sc.file_lock)
    found, _, _, _, _, _ = _lsm_disk_find(sc, key, fp)
    unlock(sc.file_lock)
    found
end''',
    '''\
function conj_haskey(sc::LP1ConjLSM, si::Int, key::CanonicalLP1Key)::Bool
    lock(sc.shard_locks[si])
    hot_found = _lsm_hot_find(sc, si, key) != 0
    unlock(sc.shard_locks[si])
    hot_found && return true
    fp = _lsm_fp(key)
    !bloom_maybe_has(sc.bloom, fp) && return false
    lock(sc.shard_locks[si])
    found, _, _, _, _, _ = _lsm_disk_find(sc, si, key, fp)
    unlock(sc.shard_locks[si])
    found
end'''
)

src = src.replace(
    '''\
function conj_getval(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    unlock(sc.shard_locks[si])
    slot != 0 && return @inbounds sc.hot_vals[si][slot]
    fp = _lsm_fp(key)
    lock(sc.file_lock)
    found, _, _, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
    unlock(sc.file_lock)
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end''',
    '''\
function conj_getval(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        v = @inbounds sc.hot_vals[si][slot]
        unlock(sc.shard_locks[si])
        return v
    end
    fp = _lsm_fp(key)
    found, _, _, i0_v, al_v, be_v = _lsm_disk_find(sc, si, key, fp)
    unlock(sc.shard_locks[si])
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end'''
)

src = src.replace(
    '''\
function conj_pop!(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        result = @inbounds sc.hot_vals[si][slot]
        _lsm_hot_delete!(sc, si, slot)
        unlock(sc.shard_locks[si])
        return result
    end
    unlock(sc.shard_locks[si])
    fp = _lsm_fp(key)
    lock(sc.file_lock)
    found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
    found && _lsm_disk_delete!(sc, ri, pos)
    unlock(sc.file_lock)
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end''',
    '''\
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
    found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, si, key, fp)
    found && _lsm_disk_delete!(sc, si, ri, pos)
    unlock(sc.shard_locks[si])
    found || throw(KeyError(key))
    _conj_make_val(V, i0_v, al_v, be_v)
end'''
)

src = src.replace(
    '''\
function conj_pop_safe(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::Union{V,Nothing} where V
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        result = @inbounds sc.hot_vals[si][slot]
        _lsm_hot_delete!(sc, si, slot)
        unlock(sc.shard_locks[si])
        return result
    end
    unlock(sc.shard_locks[si])
    fp = _lsm_fp(key)
    lock(sc.file_lock)
    found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, key, fp)
    found && _lsm_disk_delete!(sc, ri, pos)
    unlock(sc.file_lock)
    found || return nothing
    _conj_make_val(V, i0_v, al_v, be_v)
end''',
    '''\
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
    found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, si, key, fp)
    found && _lsm_disk_delete!(sc, si, ri, pos)
    unlock(sc.shard_locks[si])
    found || return nothing
    _conj_make_val(V, i0_v, al_v, be_v)
end'''
)

src = src.replace(
    '''\
function conj_insert!(sc::LP1ConjLSM{V}, si::Int,
                       key::CanonicalLP1Key, val::V)::Bool where V
    lock(sc.shard_locks[si])
    if sc.hot_counts[si] < sc.hot_thresh[si]
        _lsm_hot_insert!(sc, si, key, val)
        unlock(sc.shard_locks[si])
        return true
    end
    unlock(sc.shard_locks[si])
    lock(sc.file_lock)
    lock(sc.shard_locks[si])
    sc.hot_counts[si] >= sc.hot_thresh[si] && _lsm_flush_shard!(sc, si)
    _lsm_hot_insert!(sc, si, key, val)
    unlock(sc.shard_locks[si])
    unlock(sc.file_lock)
    true
end''',
    '''\
function conj_insert!(sc::LP1ConjLSM{V}, si::Int,
                       key::CanonicalLP1Key, val::V)::Bool where V
    lock(sc.shard_locks[si])
    if sc.hot_counts[si] >= sc.hot_thresh[si]
        _lsm_flush_shard!(sc, si)   # caller holds shard_locks[si] ✓
    end
    _lsm_hot_insert!(sc, si, key, val)
    unlock(sc.shard_locks[si])
    true
end'''
)

# ── 11. conj_insert_or_pop!: remove all file_lock references ─────────────────
# Fast path flush
src = src.replace(
    '''\        unlock(sc.shard_locks[si])
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
    end''',
    '''\        # Shard is full — flush under the shard lock we already hold conceptually.
        lock(sc.shard_locks[si])
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            v = @inbounds sc.hot_vals[si][slot]
            _lsm_hot_delete!(sc, si, slot)
            unlock(sc.shard_locks[si])
            _bday_record_collision!(sc, now_t)
            return v
        end
        if sc.hot_counts[si] >= sc.hot_thresh[si]
            _lsm_flush_shard!(sc, si)
        end
        _lsm_hot_insert!(sc, si, key, val)
        unlock(sc.shard_locks[si])
        return nothing
    end'''
)

# Slow path
src = src.replace(
    '''\    # Slow path: Bloom says key may be on disk.  Need file_lock for consistent
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
    # Re-check Bloom inside lock in case runs changed since the lockless read above.
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
    if sc.hot_counts[si] >= sc.hot_thresh[si]
        _lsm_flush_shard!(sc, si)
    end
    _lsm_hot_insert!(sc, si, key, val)
    unlock(sc.shard_locks[si])
    unlock(sc.file_lock)
    return nothing
end''',
    '''\    # Slow path: Bloom says key may be on disk.  Only need shard_locks[si].
    lock(sc.shard_locks[si])
    slot = _lsm_hot_find(sc, si, key)
    if slot != 0
        v = @inbounds sc.hot_vals[si][slot]
        _lsm_hot_delete!(sc, si, slot)
        unlock(sc.shard_locks[si])
        _bday_record_collision!(sc, now_t)
        return v
    end
    if !isempty(sc.shard_runs[si]) && bloom_maybe_has(sc.bloom, fp)
        found, ri, pos, i0_v, al_v, be_v = _lsm_disk_find(sc, si, key, fp)
        if found
            _lsm_disk_delete!(sc, si, ri, pos)
            result_v = _conj_make_val(V, i0_v, al_v, be_v)
            unlock(sc.shard_locks[si])
            _bday_record_collision!(sc, now_t)
            return result_v
        end
    end
    if sc.hot_counts[si] >= sc.hot_thresh[si]
        _lsm_flush_shard!(sc, si)
    end
    _lsm_hot_insert!(sc, si, key, val)
    unlock(sc.shard_locks[si])
    return nothing
end'''
)

# ── 12. lsm_flush_all! / lsm_close! / lsm_info ───────────────────────────────
src = src.replace(
    '''\
function lsm_flush_all!(sc::LP1ConjLSM)
    lock(sc.file_lock)
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])
        sc.hot_counts[si] > 0 && _lsm_flush_shard!(sc, si)
        unlock(sc.shard_locks[si])
    end
    unlock(sc.file_lock)
    nothing
end''',
    '''\
function lsm_flush_all!(sc::LP1ConjLSM)
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])
        sc.hot_counts[si] > 0 && _lsm_flush_shard!(sc, si)
        unlock(sc.shard_locks[si])
    end
    nothing
end'''
)

src = src.replace(
    '''\
function lsm_close!(sc::LP1ConjLSM)
    lsm_flush_all!(sc)
    lock(sc.file_lock)
    if sc.spill_io !== nothing
        close(sc.spill_io)
        sc.spill_io = nothing
    end
    unlock(sc.file_lock)
    nothing
end''',
    '''\
function lsm_close!(sc::LP1ConjLSM)
    lsm_flush_all!(sc)
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])
        if sc.shard_write_io[si] !== nothing
            close(sc.shard_write_io[si]); sc.shard_write_io[si] = nothing
        end
        if sc.shard_read_io[si] !== nothing
            close(sc.shard_read_io[si]); sc.shard_read_io[si] = nothing
        end
        unlock(sc.shard_locks[si])
    end
    nothing
end'''
)

src = src.replace(
    '''\
function lsm_info(sc::LP1ConjLSM; io::IO = stdout)
    hot_total = sum(sc.hot_counts)
    @printf(io, "LP1ConjLSM: %d hot | %d disk-live | %d runs | spill=%s (%.1f MB) | cold-dropped=%d\\n",
            hot_total, sc.n_disk_live, length(sc.runs), sc.spill_path,
            sc.spill_size / 1024^2, sc.n_cold_dropped)
    nothing
end''',
    '''\
function lsm_info(sc::LP1ConjLSM; io::IO = stdout)
    hot_total   = sum(sc.hot_counts)
    total_runs  = sum(length(r) for r in sc.shard_runs)
    total_spill = sum(sc.shard_spill_size) / 1024^2
    @printf(io, "LP1ConjLSM: %d hot | %d disk-live | %d runs across %d shards | spill_dir=%s (%.1f MB) | cold-dropped=%d\\n",
            hot_total, sc.n_disk_live, total_runs, sc.n_shards, sc.spill_path,
            total_spill, sc.n_cold_dropped)
    nothing
end'''
)

# ── 13. lsm_to_dict: iterate per-shard runs ──────────────────────────────────
src = src.replace(
    '''\
    # ── Disk runs ─────────────────────────────────────────────────────────
    lock(sc.file_lock)
    mm = sc.spill_mmap
    if !isempty(mm)
        GC.@preserve mm begin
            for rm in sc.runs
                for pos in 1:rm.len
                    _run_is_dead(rm, pos) && continue
                    base  = _rec_base(rm, pos)
                    ku0   = _mmap_u32(mm, base + OFF_U0)
                    ku1   = _mmap_u32(mm, base + OFF_U1)
                    kv0   = _mmap_u32(mm, base + OFF_V0)
                    kv1   = _mmap_u32(mm, base + OFF_V1)
                    i0_v  = _mmap_u16(mm, base + OFF_I0)
                    al_v  = _mmap_u64(mm, base + OFF_AL)
                    be_v  = _mmap_u64(mm, base + OFF_BE)
                    ck    = UInt128(ku0) | (UInt128(ku1) << 32) |
                            (UInt128(kv0) << 64) | (UInt128(kv1) << 96)
                    # Hot-shard entry (more recent) takes priority.
                    haskey(d, ck) || (d[ck] = _conj_make_val(V, i0_v, al_v, be_v))
                end
            end
        end
    end
    unlock(sc.file_lock)''',
    '''\
    # ── Disk runs (per-shard, sequential reads) ───────────────────────────
    buf = zeros(UInt8, RECORD_BYTES)
    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])
        if sc.shard_read_io[si] !== nothing
            for rm in sc.shard_runs[si]
                for pos in 1:rm.len
                    _run_is_dead(rm, pos) && continue
                    _pread_record!(sc, si, buf, _rec_base(rm, pos))
                    ku0 = _buf_u32(buf, OFF_U0); ku1 = _buf_u32(buf, OFF_U1)
                    kv0 = _buf_u32(buf, OFF_V0); kv1 = _buf_u32(buf, OFF_V1)
                    ck  = UInt128(ku0) | (UInt128(ku1) << 32) |
                          (UInt128(kv0) << 64) | (UInt128(kv1) << 96)
                    haskey(d, ck) || (d[ck] = _conj_make_val(V, _buf_i0(buf), _buf_al(buf), _buf_be(buf)))
                end
            end
        end
        unlock(sc.shard_locks[si])
    end'''
)

# ── 14. lsm_resize_hot! / lsm_recommended_hot_cap: remove file_lock ──────────
src = src.replace(
    '''\    lock(sc.file_lock)
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
        end''',
    '''\    for si in 1:sc.n_shards
        lock(sc.shard_locks[si])

        old_slot_count = sc.hot_caps[si]

        # Nothing to do if already at or smaller than target.
        if new_slot_count >= old_slot_count
            unlock(sc.shard_locks[si])
            continue
        end

        if sc.hot_counts[si] > new_thresh
            _lsm_flush_shard!(sc, si)   # caller holds shard_locks[si] ✓
        end'''
)

src = src.replace(
    '''\        unlock(sc.shard_locks[si])
    end
    unlock(sc.file_lock)

    if verbose && any_resized:''',
    '''\        unlock(sc.shard_locks[si])
    end

    if verbose && any_resized'''
)

# Clean up any remaining file_lock references (shouldn't be any, but safety check)
remaining = src.count('file_lock')
print(f"Remaining file_lock references: {remaining}")
print(f"Remaining spill_mmap references: {src.count('spill_mmap')}")
print(f"Remaining _lsm_remap references: {src.count('_lsm_remap')}")
print(f"Remaining sc.runs[ references (non-shard): {src.count('sc.runs[')}")
print(f"shard_runs references: {src.count('shard_runs')}")

with open('lp1_conj_lsm.jl', 'w') as f:
    f.write(src)
print("done")
