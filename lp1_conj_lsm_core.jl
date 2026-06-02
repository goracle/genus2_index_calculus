# =============================================================================
#  lp1_conj_lsm_core.jl — LP1ConjLSM struct, hot-shard layer, public API
#
#  Depends on: lp1_conj_lsm_constants.jl, lp1_conj_lsm_bloom.jl,
#              lp1_conj_lsm_topk.jl, lp1_conj_lsm_disk.jl,
#              lp1_conj_lsm_renyi.jl  (for _lsm_record_sample! et al.)
# =============================================================================

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
    spill_read_io ::Union{Cint, Nothing}        # open for reading via pread; separate fd
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
    bday_emissions      ::Int          # total LP1-conj partials emitted so far
    bday_t0             ::Float64      # time of first emission (time_ns() / 1e9)
    bday_first_coll_m   ::Int          # emission count at first collision (0 = not yet)
    bday_first_coll_t   ::Float64      # wall time at first collision (seconds, 0 = not yet)
    bday_lock           ::ReentrantLock

    # Occupancy estimator — S_occ via U(N) = S(1 - e^{-N/S})
    occ_unique          ::Int          # approximate unique LP1-conj keys seen
    occ_n               ::Int          # total emissions (== bday_emissions, separate for atomic snapshot)

    # Rényi-2 / collision-entropy estimator — AMS sketch.
    # ams_Z[g*AMS_WIDTH + j] = Σ h_{g,j}(fp) ∈ ℤ.  Updated under bday_lock.
    ams_Z               ::Vector{Int64}    # length AMS_K = AMS_GROUPS * AMS_WIDTH

    # Cold-filter bitmap — presence bits for COLD_BITS-bucket fp prefixes.
    # Lockless reads/writes safe (bits only ever set, never cleared).
    cold_bitmap         ::Vector{UInt64}   # length COLD_WORDS = 2^COLD_BITS / 64

    # Partial fingerprint log — chronological COLD_BITS-bit bucket indices.
    # Written under bday_lock.  Circular beyond PARTIAL_FP_LOG_CAP entries.
    partial_fp_log      ::Vector{UInt32}

    # Cold-filter stats: entries dropped at flush time (never observed → can
    # never produce a birthday collision → SSD waste to spill).
    n_cold_dropped      ::Int

    # Pre-allocated scratch buffer for disk find pread calls.
    # Access safe because _lsm_disk_find is always called under file_lock.
    read_buf            ::Vector{UInt8}

    # Top-K multiplicity reservoir — tracks the K keys with highest emission
    # count (store + close combined).  Updated under bday_lock.
    topk                ::TopKMultiplicity
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
        flush_num    ::Int  = 1,
        flush_denom  ::Int  = 4,
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

    mkpath(dirname(spill_path))
    spill_io = open(spill_path, "w+")

    LP1ConjLSM{V}(
        hot_keys, hot_vals, hot_counts, hot_caps, hot_masks, hot_thresh,
        shard_locks,
        RunMeta[], ReentrantLock(), spill_path, spill_io,
        nothing,   # spill_read_io opened lazily on first flush
        0,         # spill_size
        BloomFilter(bloom_cap),
        BloomFilter(64),           # global_bloom placeholder — caller replaces
        Any[],                     # peers — caller populates
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
        UInt32[],                    # partial_fp_log
        0,                           # n_cold_dropped
        zeros(UInt8, RECORD_BYTES),  # read_buf — pre-allocated scratch
        TopKMultiplicity()           # topk
    )
end

function LP1ConjLSM(
        ell           ::Integer;
        amortized     ::Bool   = true,
        spill_path    ::String = joinpath(homedir(), "crypto", "tmp", "lp1_conj_shards"),
        max_hot_ram_mb::Int    = 4096,
        flush_num     ::Int    = 3,
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
        bloom_cap   = min(cap, 4_000_000)
    )
end

# ---------------------------------------------------------------------------
#  Read-IO helper — open (or keep open) the read-side fd after each flush.
#  Caller must hold file_lock.
# ---------------------------------------------------------------------------
function _lsm_open_read_io!(sc::LP1ConjLSM)
    sc.spill_size == 0 && return
    flush(sc.spill_io)
    if sc.spill_read_io === nothing
        sc.spill_read_io = _open_direct(sc.spill_path)
    end
    nothing
end

# Thin wrappers that route to the free functions in lp1_conj_lsm_disk.jl,
# passing sc's fields directly so the disk module stays LP1ConjLSM-agnostic.
@inline function _sc_pread_record!(sc::LP1ConjLSM, buf::Vector{UInt8}, off::Int)
    _pread_record!(sc.spill_read_io::Cint, buf, off)
end

@inline function _sc_fadvise_dontneed!(sc::LP1ConjLSM)
    sc.spill_read_io === nothing && return
    _fadvise_dontneed!(sc.spill_read_io::Cint)
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
#  Flush one shard to the spill file.
#  Caller must hold BOTH sc.shard_locks[si] AND sc.file_lock.
# ---------------------------------------------------------------------------
function _lsm_flush_shard!(sc::LP1ConjLSM{V}, si::Int) where V
    n = sc.hot_counts[si]
    n == 0 && return

    # Cold-filter: drop entries whose coarse fp bucket was never observed.
    # Warmup: require at least 4 × 2^COLD_BITS emissions before filtering.
    cold_filter_warmup = (1 << COLD_BITS) * 4
    use_cold_filter = sc.bday_emissions >= cold_filter_warmup
    cb = sc.cold_bitmap   # lockless snapshot reference

    fps  = Vector{UInt64}(undef, n)
    u0s  = Vector{UInt32}(undef, n)
    u1s  = Vector{UInt32}(undef, n)
    v0s  = Vector{UInt32}(undef, n)
    v1s  = Vector{UInt32}(undef, n)
    i0s  = Vector{UInt16}(undef, n)
    als  = Vector{UInt64}(undef, n)
    bes  = Vector{UInt64}(undef, n)

    idx    = 0
    n_cold = 0
    keys   = sc.hot_keys[si]
    vals   = sc.hot_vals[si]
    @inbounds for slot in 1:sc.hot_caps[si]
        k = keys[slot]
        k == CONJ_KEY_EMPTY && continue
        fp = _lsm_fp(k)
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

    # Reset hot shard before I/O so the shard is available for new insertions.
    fill!(sc.hot_keys[si], CONJ_KEY_EMPTY)
    sc.hot_counts[si] = 0
    sc.n_cold_dropped += n_cold

    idx == 0 && return

    # Sort by fingerprint, then write sorted run to spill file.
    order = sortperm(view(fps, 1:idx))

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

    # Update Bloom filters.
    for i in 1:idx
        fp_i = fps[order[i]]
        set_bloom!(sc.bloom, fp_i)
        set_bloom!(sc.global_bloom, fp_i)
    end

    # Register run.
    min_fp = fps[order[1]]
    max_fp = fps[order[idx]]
    push!(sc.runs, RunMeta(length(sc.runs)+1, byte_offset, idx, min_fp, max_fp))
    sc.n_disk_live += idx

    _lsm_open_read_io!(sc)
    _sc_fadvise_dontneed!(sc)

    # Compact if fan-out is large.
    # _lsm_compact! acquires file_lock itself; release it here first.
    if length(sc.runs) >= 16
        unlock(sc.file_lock)
        _lsm_compact!(sc)
        lock(sc.file_lock)
    end

    nothing
end

# ---------------------------------------------------------------------------
#  Compact all runs into a single sorted run via k-way merge.
#
#  LOCKING CONTRACT: caller must NOT hold file_lock.  This function
#  acquires file_lock briefly for the snapshot (phase 1) and commit (phase 3),
#  and releases it for the I/O-heavy merge body (phase 2).
# ---------------------------------------------------------------------------
function _lsm_compact!(sc::LP1ConjLSM)
    length(sc.runs) <= 1 && return
    sc.n_disk_live == 0  && return
    sc.spill_read_io === nothing && return

    # ── Phase 1: snapshot run list ────────────────────────────────────────────
    lock(sc.file_lock)
    nruns_snap   = length(sc.runs)
    runs_snap    = sc.runs[1:nruns_snap]
    read_fd_snap = sc.spill_read_io::Cint
    unlock(sc.file_lock)

    # ── Phase 2: I/O-heavy merge (no locks held) ─────────────────────────────
    cursors = Vector{Int}(undef, nruns_snap)
    for ri in 1:nruns_snap
        rm  = runs_snap[ri]
        pos = 1
        while pos <= rm.len && _run_is_dead(rm, pos)
            pos += 1
        end
        cursors[ri] = pos
    end

    local_pread! = function(buf::Vector{UInt8}, off::Int)
        n = ccall(:pread, Cssize_t, (Cint, Ptr{UInt8}, Csize_t, Int64),
                  read_fd_snap, buf, RECORD_BYTES, off)
        if n != RECORD_BYTES
            err_msg = Base.Libc.strerror()
            error("_lsm_compact! local_pread: short read ($n) at offset $off: $err_msg")
        end
        nothing
    end

    heap = Tuple{UInt64,Int,Int}[]
    sizehint!(heap, nruns_snap)
    rec_buf_seed = zeros(UInt8, RECORD_BYTES)
    for ri in 1:nruns_snap
        rm  = runs_snap[ri]
        pos = cursors[ri]
        pos > rm.len && continue
        local_pread!(rec_buf_seed, _rec_base(rm, pos))
        fp = _buf_fp(rec_buf_seed)
        _compact_heap_push!(heap, (fp, ri, pos))
    end

    tmp_path  = sc.spill_path * ".compact"
    tmp_io    = open(tmp_path, "w+")
    wbuf      = Vector{UInt8}(undef, COMPACT_WRITE_BUF_BYTES)
    wbuf_pos  = 0

    actual   = 0
    first_fp = UInt64(0)
    last_fp  = UInt64(0)

    rec_buf_merge = zeros(UInt8, RECORD_BYTES)
    while !isempty(heap)
        fp, ri, pos = _compact_heap_pop!(heap)
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
            _compact_heap_push!(heap, (fp2, ri, pos))
        end
    end

    wbuf_pos > 0 && write(tmp_io, view(wbuf, 1:wbuf_pos))
    flush(tmp_io)
    close(tmp_io)

    # ── Phase 3: reacquire file_lock and atomically commit ───────────────────
    lock(sc.file_lock)

    # Copy any runs appended during phase 2 into the temp file.
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
        old_tombs        = rm.tombs
        sc.runs[i]       = RunMeta(i, rm.byte_offset, rm.len, rm.min_fp, rm.max_fp)
        sc.runs[i].tombs = old_tombs
    end

    if sc.spill_read_io !== nothing
        ccall(:close, Cint, (Cint,), sc.spill_read_io::Cint)
        sc.spill_read_io = nothing
    end
    sc.spill_read_io = _open_direct(sc.spill_path)
    _sc_fadvise_dontneed!(sc)
    unlock(sc.file_lock)
    nothing
end

# ---------------------------------------------------------------------------
#  Disk find/delete wrappers — route through sc's fields
# ---------------------------------------------------------------------------
function _sc_disk_find(sc::LP1ConjLSM,
                        key::CanonicalLP1Key,
                        fp_target::UInt64)::Tuple{Bool,Int,Int,UInt16,UInt64,UInt64}
    sc.spill_read_io === nothing &&
        return (false, 0, 0, UInt16(0), UInt64(0), UInt64(0))
    _lsm_disk_find(sc.runs, sc.spill_read_io::Cint, sc.read_buf, key, fp_target)
end

function _sc_disk_delete!(sc::LP1ConjLSM, ri::Int, pos::Int)
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
            found, _, _, _, _, _ = _sc_disk_find(sc, key, fp)
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
            found, _, _, i0_v, al_v, be_v = _sc_disk_find(sc, key, fp)
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
            found, ri, pos, i0_v, al_v, be_v = _sc_disk_find(sc, key, fp)
            found && _sc_disk_delete!(sc, ri, pos)
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
            found, ri, pos, i0_v, al_v, be_v = _sc_disk_find(sc, key, fp)
            found && _sc_disk_delete!(sc, ri, pos)
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
                _lsm_flush_shard!(sc, si)
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
#  conj_insert_or_pop! — atomic check+act, no TOCTOU race.
#
#  Returns (prev_val, is_same_col):
#    (nothing, false)  -- genuine miss; key was inserted.  Rényi updated.
#    (v,       false)  -- genuine cross-col collision.  Rényi updated.
#    (nothing, true)   -- same-col hit: stored entry kept, current discarded.
#                         Rényi NOT updated (not an independent sample).
# ---------------------------------------------------------------------------
function conj_insert_or_pop!(sc::LP1ConjLSM{V}, si::Int,
                              key::CanonicalLP1Key, val::V
                             )::Tuple{Union{V,Nothing}, Bool} where V

    fp    = _lsm_fp(key)
    now_t = time_ns() * 1e-9
    i0_cur = Int(val.i0)

    # 1. Fast Path: own hot table, shard lock only.
    lock(sc.shard_locks[si])
    try
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            v = @inbounds sc.hot_vals[si][slot]
            if Int(v.i0) == i0_cur
                return (nothing, true)
            end
            _lsm_hot_delete!(sc, si, slot)
            _lsm_record_sample!(sc, fp, now_t, key)
            _bday_record_collision!(sc, now_t)
            return (v, false)
        end
    finally
        unlock(sc.shard_locks[si])
    end

    # 2. Own disk runs.
    if !isempty(sc.runs) && bloom_maybe_has(sc.bloom, fp)
        lock(sc.file_lock)
        try
            lock(sc.shard_locks[si])
            try
                # TOCTOU double-check.
                slot = _lsm_hot_find(sc, si, key)
                if slot != 0
                    v = @inbounds sc.hot_vals[si][slot]
                    if Int(v.i0) == i0_cur
                        return (nothing, true)
                    end
                    _lsm_hot_delete!(sc, si, slot)
                    _lsm_record_sample!(sc, fp, now_t, key)
                    _bday_record_collision!(sc, now_t)
                    return (v, false)
                end

                found, ri, pos, i0_v, al_v, be_v = _sc_disk_find(sc, key, fp)
                if found
                    if Int(i0_v) == i0_cur
                        _sc_disk_delete!(sc, ri, pos)
                        _lsm_hot_insert!(sc, si, key, _conj_make_val(V, i0_v, al_v, be_v))
                        return (nothing, true)
                    end
                    _sc_disk_delete!(sc, ri, pos)
                    result_v = _conj_make_val(V, i0_v, al_v, be_v)
                    _lsm_record_sample!(sc, fp, now_t, key)
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

    # 3. Cross-peer probe.
    #    Guard: only probe after first collision (avoids serialising all threads
    #    on empty peer disks at walk start) and when global bloom says fp exists.
    if bloom_maybe_has(sc.global_bloom, fp)
        for peer in sc.peers
            peer === sc && continue
            peer_lsm = peer::LP1ConjLSM{V}

            bloom_maybe_has(peer_lsm.bloom, fp) || continue

            # Check peer hot table first.
            if trylock(peer_lsm.shard_locks[si])
                try
                    pslot = _lsm_hot_find(peer_lsm, si, key)
                    if pslot != 0
                        pv = @inbounds peer_lsm.hot_vals[si][pslot]
                        if Int(pv.i0) == i0_cur
                            return (nothing, true)
                        end
                        _lsm_hot_delete!(peer_lsm, si, pslot)
                        _lsm_record_sample!(sc, fp, now_t, key)
                        _bday_record_collision!(sc, now_t)
                        return (pv, false)
                    end
                finally
                    unlock(peer_lsm.shard_locks[si])
                end
            end

            # Check peer disk via trylock — skip peer if busy flushing.
            if !isempty(peer_lsm.runs)
                if trylock(peer_lsm.file_lock)
                    try
                        if trylock(peer_lsm.shard_locks[si])
                            try
                                found, ri, pos, i0_v, al_v, be_v =
                                    _lsm_disk_find(peer_lsm.runs,
                                                   peer_lsm.spill_read_io::Cint,
                                                   peer_lsm.read_buf,
                                                   key, fp)
                                if found
                                    if Int(i0_v) == i0_cur
                                        _run_set_dead!(peer_lsm.runs[ri], pos)
                                        peer_lsm.n_disk_live -= 1
                                        lock(peer_lsm.shard_locks[si]) do
                                            _lsm_hot_insert!(peer_lsm, si, key,
                                                             _conj_make_val(V, i0_v, al_v, be_v))
                                        end
                                        return (nothing, true)
                                    end
                                    _run_set_dead!(peer_lsm.runs[ri], pos)
                                    peer_lsm.n_disk_live -= 1
                                    _lsm_record_sample!(sc, fp, now_t, key)
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

    # 4. Not found — insert into own LSM, unless at cap.
    lock(sc.file_lock)
    try
        lock(sc.shard_locks[si])
        try
            # Final TOCTOU check before insertion.
            slot = _lsm_hot_find(sc, si, key)
            if slot != 0
                v = @inbounds sc.hot_vals[si][slot]
                if Int(v.i0) == i0_cur
                    return (nothing, true)
                end
                _lsm_hot_delete!(sc, si, slot)
                _lsm_record_sample!(sc, fp, now_t, key)
                _bday_record_collision!(sc, now_t)
                return (v, false)
            end

            # Cap enforcement.
            if sc.n_disk_live + sum(sc.hot_counts) >= sc.max_entries
                sc.n_cold_dropped += 1
                return (nothing, false)
            end

            if sc.hot_counts[si] >= sc.hot_thresh[si]
                _lsm_flush_shard!(sc, si)
            end
            _lsm_hot_insert!(sc, si, key, val)
            _lsm_record_sample!(sc, fp, now_t, key)
            return (nothing, false)
        finally
            unlock(sc.shard_locks[si])
        end
    finally
        unlock(sc.file_lock)
    end
end

# ---------------------------------------------------------------------------
#  Lifecycle
# ---------------------------------------------------------------------------

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
        ccall(:close, Cint, (Cint,), sc.spill_read_io::Cint)
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
#  Snapshot / streaming helpers
# ---------------------------------------------------------------------------

function lsm_to_dict(sc::LP1ConjLSM{V})::Dict{CanonicalLP1Key, V} where V
    d = Dict{CanonicalLP1Key, V}()
    sizehint!(d, conj_total_entries(sc) + 16)

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

    lock(sc.file_lock)
    if sc.spill_read_io !== nothing
        buf = zeros(UInt8, RECORD_BYTES)
        for rm in sc.runs
            for pos in 1:rm.len
                _run_is_dead(rm, pos) && continue
                _pread_record!(sc.spill_read_io::Cint, buf, _rec_base(rm, pos))
                ku0  = _buf_u32(buf, OFF_U0)
                ku1  = _buf_u32(buf, OFF_U1)
                kv0  = _buf_u32(buf, OFF_V0)
                kv1  = _buf_u32(buf, OFF_V1)
                ck   = UInt128(ku0) | (UInt128(ku1) << 32) |
                       (UInt128(kv0) << 64) | (UInt128(kv1) << 96)
                haskey(d, ck) || (d[ck] = _conj_make_val(V, _buf_i0(buf), _buf_al(buf), _buf_be(buf)))
            end
        end
    end
    unlock(sc.file_lock)

    d
end

conj_to_dict(sc::LP1ConjLSM{V}) where V = lsm_to_dict(sc)

# Stream one LSM's entries into a caller-supplied Dict, then close the LSM.
# Avoids a full intermediate snapshot Dict by freeing shard arrays as we go.
function lsm_stream_into_dict!(d::Dict{CanonicalLP1Key, V},
                                sc::LP1ConjLSM{V}) where V
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
        sc.hot_keys[si]   = CanonicalLP1Key[]
        sc.hot_vals[si]   = V[]
        sc.hot_counts[si] = 0
        sc.hot_caps[si]   = 0
        unlock(sc.shard_locks[si])
    end
    GC.gc(false)

    lock(sc.file_lock)
    if sc.spill_read_io !== nothing
        buf = zeros(UInt8, RECORD_BYTES)
        for rm in sc.runs
            for pos in 1:rm.len
                _run_is_dead(rm, pos) && continue
                _pread_record!(sc.spill_read_io::Cint, buf, _rec_base(rm, pos))
                ku0 = _buf_u32(buf, OFF_U0)
                ku1 = _buf_u32(buf, OFF_U1)
                kv0 = _buf_u32(buf, OFF_V0)
                kv1 = _buf_u32(buf, OFF_V1)
                ck  = UInt128(ku0) | (UInt128(ku1) << 32) |
                      (UInt128(kv0) << 64) | (UInt128(kv1) << 96)
                haskey(d, ck) || (d[ck] = _conj_make_val(V, _buf_i0(buf), _buf_al(buf), _buf_be(buf)))
            end
        end
    end
    unlock(sc.file_lock)

    lock(sc.file_lock)
    if sc.spill_io !== nothing
        close(sc.spill_io)
        sc.spill_io = nothing
    end
    if sc.spill_read_io !== nothing
        ccall(:close, Cint, (Cint,), sc.spill_read_io::Cint)
        sc.spill_read_io = nothing
    end
    unlock(sc.file_lock)

    nothing
end

# Build a merged snapshot Dict from an array of per-thread LSMs with minimal
# peak RAM (streams one LSM at a time, frees each immediately).
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
        GC.gc(false)
    end

    if verbose
        @printf("  [lsm_snapshot] done: %d entries in %.3fs\n", length(d), time() - t0)
        flush(stdout)
    end
    d
end

# ---------------------------------------------------------------------------
#  Hot-table management utilities
# ---------------------------------------------------------------------------

function conj_roundtrip_ok(sc::LP1ConjLSM{V}, si::Int,
                            key::CanonicalLP1Key, val::V)::Bool where V
    conj_insert!(sc, si, key, val)
    return conj_haskey(sc, si, key)
end

# Compute recommended hot-table size from birthday statistics.
# Returns (recommended_total, recommended_per_shard, reason).
function lsm_recommended_hot_cap(sc::LP1ConjLSM;
                                  safety_factor::Int = 8
                                 )::Tuple{Int, Int, String}
    lock(sc.bday_lock)
    m      = sc.bday_first_coll_m
    unlock(sc.bday_lock)

    current_total = sc.n_shards * sc.hot_caps[1]

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

# Shrink (or grow) every shard's hot table in-place.
# Returns true if any shard was actually resized.
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

        if new_slot_count >= old_slot_count
            unlock(sc.shard_locks[si])
            continue
        end

        if sc.hot_counts[si] > new_thresh
            _lsm_flush_shard!(sc, si)
        end

        old_keys  = sc.hot_keys[si]
        old_vals  = sc.hot_vals[si]

        new_keys  = fill(CONJ_KEY_EMPTY, new_slot_count)
        new_vals  = Vector{V}(undef, new_slot_count)
        new_count = 0

        @inbounds for slot in 1:old_slot_count
            k = old_keys[slot]
            k == CONJ_KEY_EMPTY && continue
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

# Convenience wrapper: query recommended size and apply if beneficial.
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
