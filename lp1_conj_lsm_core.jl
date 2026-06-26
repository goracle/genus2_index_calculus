# =============================================================================
#  lp1_conj_lsm_core.jl — LP1ConjLSM struct, hot-shard layer, public API
#
#  Depends on: lp1_conj_lsm_constants.jl, lp1_conj_lsm_bloom.jl,
#              lp1_conj_lsm_topk.jl, lp1_conj_lsm_disk.jl,
#              lp1_conj_lsm_renyi.jl  (for _lsm_record_sample! et al.)
# =============================================================================
#
# ---------------------------------------------------------------------------
#  NOTE: LP1ConjVal and LP1ConjValFull are defined in trial3_config.jl and
#  carry anchor_indices::NTuple{K_MAX,UInt16} (K_MAX set in trial3_config.jl)
#  instead of a separate i0::UInt16.  The on-disk record stores all K_MAX
#  anchor slots contiguously starting at OFF_I0 (see constants).
#  The hot_rows side-channel and conj_row_store have been eliminated entirely.
# ---------------------------------------------------------------------------

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

    # (hot_rows removed — anchor FB indices are now packed in LP1ConjVal.anchor_indices
    #  and reconstructed at close time via _unpack_anchor_row(); no side-channel needed.)

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
    n_shards      ::Int
    max_entries   ::Int
    n_disk_live   ::Int
    amortized     ::Bool

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
    # ams_Z[(g-1)*AMS_WIDTH + j] = Σ σ_{g,j}(key) ∈ ℤ, where
    #   σ_{g,j}(key) = MSB( lo(key)*AMS_SALTS[idx] + hi(key)*AMS_SALTS_HI[idx] )
    # with idx = (g-1)*AMS_WIDTH + j.  Updated under bday_lock.
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
        flush_denom   ::Int    = 4,
        anchor_tuple_size::Int = 1   # kept for call-site compat; no longer used
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
        amortized         = amortized,
        flush_num         = flush_num,
        flush_denom       = flush_denom,
        bloom_cap         = min(cap, 4_000_000)
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
    fp   = _lsm_fp(key)
    slot = Int(fp & mask) + 1
    @inbounds while true
        if keys[slot] == CONJ_KEY_EMPTY
            keys[slot] = key
            vals[slot] = val
            sc.hot_counts[si] += 1
            # Sampled global-bloom write: advertise this key to peer threads
            # before the shard is flushed to disk.  1-in-8 sample rate keeps
            # the global bloom from saturating faster than the disk-flush path
            # would while still providing coverage for high-frequency keys.
            # Uses the fingerprint directly — no RNG, no extra state.
            if (fp & GLOBAL_BLOOM_HOT_SAMPLE_MASK) == 0
                set_bloom!(sc.global_bloom, fp)
            end
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
        dead_key = keys[slot]
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
    ais  = Vector{NTuple{K_MAX,UInt16}}(undef, n)
    stps = Vector{UInt32}(undef, n)
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
        ais[idx] = v.anchor_indices
        stps[idx] = v.store_step
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
                       ais[oi], stps[oi], als[oi], bes[oi])
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
                        fp_target::UInt64)::Tuple{Bool,Int,Int,NTuple{K_MAX,UInt16},UInt32,UInt64,UInt64}
    sc.spill_read_io === nothing &&
        return (false, 0, 0, ntuple(_ -> ANCHOR_IDX_NONE, K_MAX), UInt32(0), UInt64(0), UInt64(0))
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
            found, _, _, _, _, _, _ = _sc_disk_find(sc, key, fp)
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
            found, _, _, ai_v, step_v, al_v, be_v = _sc_disk_find(sc, key, fp)
            found || throw(KeyError(key))
            return _conj_make_val(V, _unpack_anchor_row(ai_v), step_v, al_v, be_v)
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
            found, ri, pos, ai_v, step_v, al_v, be_v = _sc_disk_find(sc, key, fp)
            found && _sc_disk_delete!(sc, ri, pos)
            found || throw(KeyError(key))
            return _conj_make_val(V, _unpack_anchor_row(ai_v), step_v, al_v, be_v)
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
            found, ri, pos, ai_v, step_v, al_v, be_v = _sc_disk_find(sc, key, fp)
            found && _sc_disk_delete!(sc, ri, pos)
            found || return nothing
            return _conj_make_val(V, _unpack_anchor_row(ai_v), step_v, al_v, be_v)
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
#  Returns (prev_val, is_same_col, prev_row):
#    (nothing, false, nothing)   -- genuine miss; key was inserted.
#    (v,       false, row)       -- genuine collision (hot or disk); row is
#                                   reconstructed from v.anchor_indices —
#                                   always valid, never nothing.
#    (nothing, true,  nothing)   -- same-col hit: stored entry kept, current discarded.
#
#  The fb_row parameter is accepted for call-site compatibility but is no longer
#  used — the anchor indices are packed into the val struct and reconstructed at
#  close time via _unpack_anchor_row(v.anchor_indices).
#
#  Same-partial detection uses only neg_al + neg_be.
# ---------------------------------------------------------------------------
function conj_insert_or_pop!(sc::LP1ConjLSM{V}, si::Int,
                              key::CanonicalLP1Key, val::V,
                              fb_row::Dict{Int,Int}   # kept for compat; not used
                             )::Tuple{Union{V,Nothing}, Bool, Union{Dict{Int,Int},Nothing}} where V

    fp    = _lsm_fp(key)
    now_t = time_ns() * 1e-9

    # 1. Fast Path: own hot table, shard lock only.
    lock(sc.shard_locks[si])
    try
        slot = _lsm_hot_find(sc, si, key)
        if slot != 0
            v = @inbounds sc.hot_vals[si][slot]
            if Int(v.neg_al) == Int(val.neg_al) &&
               _conj_prev_be(v) == _conj_prev_be(val)
                return (nothing, true, nothing)
            end
            prev_row = _unpack_anchor_row(v.anchor_indices)
            _lsm_hot_delete!(sc, si, slot)
            _lsm_record_sample!(sc, fp, now_t, key)
            _bday_record_collision!(sc, now_t)
            return (v, false, prev_row)
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
                    if Int(v.neg_al) == Int(val.neg_al) &&
                       _conj_prev_be(v) == _conj_prev_be(val)
                        return (nothing, true, nothing)
                    end
                    prev_row = _unpack_anchor_row(v.anchor_indices)
                    _lsm_hot_delete!(sc, si, slot)
                    _lsm_record_sample!(sc, fp, now_t, key)
                    _bday_record_collision!(sc, now_t)
                    return (v, false, prev_row)
                end

                found, ri, pos, ai_v, step_v, al_v, be_v = _sc_disk_find(sc, key, fp)
                if found
                    if al_v == UInt64(val.neg_al) &&
                       be_v == UInt64(_conj_prev_be(val))
                        # Same-partial by scalars: re-insert to hot with anchor_indices
                        # recovered from disk so future closes work.
                        _sc_disk_delete!(sc, ri, pos)
                        disk_val = _conj_make_val(V, _unpack_anchor_row(ai_v), step_v, al_v, be_v)
                        _lsm_hot_insert!(sc, si, key, disk_val)
                        return (nothing, true, nothing)
                    end
                    _sc_disk_delete!(sc, ri, pos)
                    result_v = _conj_make_val(V, _unpack_anchor_row(ai_v), step_v, al_v, be_v)
                    _lsm_record_sample!(sc, fp, now_t, key)
                    _bday_record_collision!(sc, now_t)
                    return (result_v, false, _unpack_anchor_row(ai_v))
                end
            finally
                unlock(sc.shard_locks[si])
            end
        finally
            unlock(sc.file_lock)
        end
    end

    # 3. Cross-peer probe.
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
                        if Int(pv.neg_al) == Int(val.neg_al) &&
                           _conj_prev_be(pv) == _conj_prev_be(val)
                            return (nothing, true, nothing)
                        end
                        prev_row = _unpack_anchor_row(pv.anchor_indices)
                        _lsm_hot_delete!(peer_lsm, si, pslot)
                        _lsm_record_sample!(sc, fp, now_t, key)
                        _bday_record_collision!(sc, now_t)
                        return (pv, false, prev_row)
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
                                found, ri, pos, ai_v, step_v, al_v, be_v =
                                    _lsm_disk_find(peer_lsm.runs,
                                                   peer_lsm.spill_read_io::Cint,
                                                   peer_lsm.read_buf,
                                                   key, fp)
                                if found
                                    if al_v == UInt64(val.neg_al) &&
                                       be_v == UInt64(_conj_prev_be(val))
                                        _run_set_dead!(peer_lsm.runs[ri], pos)
                                        peer_lsm.n_disk_live -= 1
                                        disk_val = _conj_make_val(V, _unpack_anchor_row(ai_v), step_v, al_v, be_v)
                                        _lsm_hot_insert!(peer_lsm, si, key, disk_val)
                                        return (nothing, true, nothing)
                                    end
                                    _run_set_dead!(peer_lsm.runs[ri], pos)
                                    peer_lsm.n_disk_live -= 1
                                    _lsm_record_sample!(sc, fp, now_t, key)
                                    _bday_record_collision!(sc, now_t)
                                    result_v = _conj_make_val(V, _unpack_anchor_row(ai_v), step_v, al_v, be_v)
                                    return (result_v, false, _unpack_anchor_row(ai_v))
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
                if Int(v.neg_al) == Int(val.neg_al) &&
                   _conj_prev_be(v) == _conj_prev_be(val)
                    return (nothing, true, nothing)
                end
                prev_row = _unpack_anchor_row(v.anchor_indices)
                _lsm_hot_delete!(sc, si, slot)
                _lsm_record_sample!(sc, fp, now_t, key)
                _bday_record_collision!(sc, now_t)
                return (v, false, prev_row)
            end

            # Cap enforcement.
            if sc.n_disk_live + sum(sc.hot_counts) >= sc.max_entries
                sc.n_cold_dropped += 1
                return (nothing, false, nothing)
            end

            if sc.hot_counts[si] >= sc.hot_thresh[si]
                _lsm_flush_shard!(sc, si)
            end
            _lsm_hot_insert!(sc, si, key, val)
            _lsm_record_sample!(sc, fp, now_t, key)
            return (nothing, false, nothing)
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
                haskey(d, ck) || (d[ck] = _conj_make_val(V, _unpack_anchor_row(_buf_anchor_indices(buf)), _buf_step(buf), _buf_al(buf), _buf_be(buf)))
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
                haskey(d, ck) || (d[ck] = _conj_make_val(V, _unpack_anchor_row(_buf_anchor_indices(buf)), _buf_step(buf), _buf_al(buf), _buf_be(buf)))
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

# ---------------------------------------------------------------------------
#  _lsm_disk_delete! — tombstone a live record in a flushed run.
#  Caller holds file_lock.
# ---------------------------------------------------------------------------
function _lsm_disk_delete!(sc::LP1ConjLSM, ri::Int, pos::Int)
    _run_set_dead!(sc.runs[ri], pos)
    sc.n_disk_live -= 1
    nothing
end


# ---------------------------------------------------------------------------
#  lsm_mem_report — heap / spill memory breakdown
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
#  lsm_flush_stats — flush efficiency and spill accounting
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

# ---------------------------------------------------------------------------
#  lsm_multiplicity_report — D17 top-K key multiplicity diagnostics
# ---------------------------------------------------------------------------
function lsm_multiplicity_report(peers::Vector{<:LP1ConjLSM},
                                  p::Integer;
                                  io::IO = stdout)

    @printf(io, "\n══ D17 — LP1-conj store multiplicity analysis (top-%d keys) ════════\n", TOPK_K)

    # --- Merge top-K heaps across all peers ---
    # Build a global count Dict by iterating all peers' heaps.
    global_counts = Dict{CanonicalLP1Key, Int}()
    total_keys_seen = 0
    total_N = Int64(0)

    for peer in peers
        lock(peer.bday_lock)
        try
            total_N += peer.bday_emissions
            total_keys_seen += peer.topk.total_keys_seen
            for (cnt, k) in peer.topk.heap
                global_counts[k] = get(global_counts, k, 0) + cnt
            end
        finally
            unlock(peer.bday_lock)
        end
    end

    if isempty(global_counts)
        @printf(io, "  (no entries in top-K reservoir — need more walk emissions)\n")
        @printf(io, "══ End D17 ═══════════════════════════════════════════════════════════\n")
        return
    end

    # Sort by count descending
    sorted = sort(collect(global_counts), by=x -> -x[2])
    n_show = min(length(sorted), TOPK_K)

    pf   = Float64(p)
    logp = log(pf)

    @printf(io, "  Total emissions N          : %d\n", total_N)
    @printf(io, "  Distinct keys tracked      : %d  (across %d peers, top-%d each)\n",
            length(global_counts), length(peers), TOPK_K)
    @printf(io, "  Total distinct keys seen   : %d  (approximate; new keys with count≤min not tracked)\n",
            total_keys_seen)
    @printf(io, "\n")

    # --- Zipf / Gini on tracked keys ---
    counts_sorted = [c for (_, c) in sorted]
    c_max    = counts_sorted[1]
    c_median = counts_sorted[max(1, length(counts_sorted) ÷ 2)]
    c_mean   = total_N > 0 ? Float64(total_N) / max(1, total_keys_seen) : 0.0
    total_c  = sum(counts_sorted)
    gini_num = 0.0
    n_c = length(counts_sorted)
    for i in 1:n_c, j in 1:n_c
        gini_num += abs(counts_sorted[i] - counts_sorted[j])
    end
    gini = n_c > 1 ? gini_num / (2.0 * n_c * total_c) : 0.0

    cum = 0
    top1_mass = counts_sorted[1] / Float64(total_c)
    top10_mass = sum(counts_sorted[1:min(10,n_c)]) / Float64(total_c)

    @printf(io, "  Multiplicity summary (tracked keys only):\n")
    @printf(io, "    max count            : %d\n", c_max)
    @printf(io, "    median count         : %d\n", c_median)
    @printf(io, "    mean count (global)  : %.2f  (= N/total_distinct_seen)\n", c_mean)
    @printf(io, "    Gini (tracked)       : %.4f\n", gini)
    @printf(io, "    top-1  mass          : %.4f%%\n", 100.0 * top1_mass)
    @printf(io, "    top-10 mass          : %.4f%%\n", 100.0 * top10_mass)
    @printf(io, "\n")

    # --- F₂ and α₂ implied by tracked top-K alone ---
    # Each tracked key has count c_i; their contribution to F₂ is Σ c_i².
    # If these dominate, F₂_observed ≈ Σ_{top-K} c_i².
    f2_topk = Float64(sum(c^2 for c in counts_sorted))
    s2_topk = total_N > 0 ? Float64(total_N)^2 / f2_topk : 0.0
    a2_topk = s2_topk > 0.0 ? log(s2_topk) / (2.0 * logp) : 0.0
    @printf(io, "  F₂ from top-K keys alone   : %.5g\n", f2_topk)
    @printf(io, "  S₂ from top-K keys alone   : %.5g  (α₂ = %.4f)\n", s2_topk, a2_topk)
    @printf(io, "  (if α₂_topk ≈ global α₂, top-K keys explain the full collision entropy)\n")
    @printf(io, "\n")

    # --- Decode and report top keys ---
    # CanonicalLP1Key packing: u0(32)|u1(32)|v0(32)|v1(32) from low to high bits.
    function decode_key(k::CanonicalLP1Key)
        u0 = Int(UInt32(k & 0xffffffff))
        u1 = Int(UInt32((k >> 32)  & 0xffffffff))
        v0 = Int(UInt32((k >> 64)  & 0xffffffff))
        v1 = Int(UInt32((k >> 96)  & 0xffffffff))
        (u0, u1, v0, v1)
    end

    # Modular helpers (p is in scope from outer)
    pi = Int(p)
    function modsq(a::Int)::Int; mod(a * a, pi); end
    function modmul(a::Int, b::Int)::Int; mod(a * b, pi); end
    function modsub(a::Int, b::Int)::Int; mod(a - b, pi); end
    # Legendre symbol via Euler criterion: a^((p-1)/2) mod p
    function legendre(a::Int)::Int
        a = mod(a, pi); a == 0 && return 0
        r = powermod(a, (pi - 1) ÷ 2, pi)
        r == 1 ? 1 : -1
    end

    @printf(io, "  Top-%d high-multiplicity keys (Mumford u,v coordinates):\n", min(n_show, 50))
    @printf(io, "  %6s  %8s  %10s  %10s  %10s  %10s  %6s  %6s  %s\n",
            "rank", "count", "u0", "u1", "v0", "v1", "disc_u", "disc_v", "notes")
    @printf(io, "  %s\n", "-"^95)

    disc_u_vals = Int[]
    disc_v_vals = Int[]
    leg_u_vals  = Int[]
    leg_v_vals  = Int[]
    u1_vals     = Int[]
    v1_vals     = Int[]

    for rank in 1:min(n_show, 50)
        key, cnt = sorted[rank]
        u0, u1, v0, v1 = decode_key(key)

        # discriminants (as elements of F_p, reduced to [0,p))
        disc_u = modsub(modsq(u1), modmul(4, u0))   # u1²-4u0 mod p
        disc_v = modsub(modsq(v1), modmul(4, v0))   # v1²-4v0 mod p
        leg_u  = legendre(disc_u)
        leg_v  = legendre(disc_v)

        push!(disc_u_vals, disc_u); push!(disc_v_vals, disc_v)
        push!(leg_u_vals, leg_u);   push!(leg_v_vals, leg_v)
        push!(u1_vals, u1); push!(v1_vals, v1)

        leg_u_s = leg_u ==  1 ? "QR" : leg_u == -1 ? "NR" : "0"
        leg_v_s = leg_v ==  1 ? "QR" : leg_v == -1 ? "NR" : "0"

        notes = String[]
        leg_u == 1  && push!(notes, "u-splits")
        leg_v == -1 && push!(notes, "v-non-split✓")
        leg_v == 1  && push!(notes, "v-SPLIT!")
        disc_u == 0 && push!(notes, "u-repeated-root")
        disc_v == 0 && push!(notes, "v-repeated-root")

        @printf(io, "  %6d  %8d  %10d  %10d  %10d  %10d  %6s  %6s  %s\n",
                rank, cnt, u0, u1, v0, v1, leg_u_s, leg_v_s,
                isempty(notes) ? "" : join(notes, ", "))
    end

    @printf(io, "\n")

    # --- Geometric summary across top keys ---
    n_top = length(leg_v_vals)
    n_v_nr  = count(==(-1), leg_v_vals)
    n_v_qr  = count(==(1),  leg_v_vals)
    n_u_qr  = count(==(1),  leg_u_vals)
    n_u_nr  = count(==(-1), leg_u_vals)

    @printf(io, "  Geometric summary (top-%d keys):\n", n_top)
    @printf(io, "    disc(v) = NR (conjugate, expected) : %d / %d  (%.1f%%)\n",
            n_v_nr, n_top, 100.0 * n_v_nr / n_top)
    @printf(io, "    disc(v) = QR (accidentally split!) : %d / %d  (%.1f%%)\n",
            n_v_qr, n_top, 100.0 * n_v_qr / n_top)
    @printf(io, "    disc(u) = QR (u-poly splits in F_p): %d / %d  (%.1f%%)\n",
            n_u_qr, n_top, 100.0 * n_u_qr / n_top)
    @printf(io, "    disc(u) = NR (u-poly non-split)    : %d / %d  (%.1f%%)\n",
            n_u_nr, n_top, 100.0 * n_u_nr / n_top)

    # u1 clustering: does u1 concentrate?
    u1_counts = Dict{Int,Int}()
    for v in u1_vals; u1_counts[v] = get(u1_counts, v, 0) + 1; end
    top_u1 = sort(collect(u1_counts), by=x -> -x[2])
    u1_top1_frac = isempty(top_u1) ? 0.0 : top_u1[1][2] / Float64(n_top)

    @printf(io, "\n    u1 (x-sum) clustering:\n")
    @printf(io, "      distinct u1 values among top-%d keys : %d\n", n_top, length(u1_counts))
    @printf(io, "      top-1 u1 value appears               : %d / %d  (%.1f%%)\n",
            isempty(top_u1) ? 0 : top_u1[1][2], n_top, 100.0 * u1_top1_frac)
    if u1_top1_frac > 0.3
        @printf(io, "      ↑ CLUSTERING: many top keys share u1=%d\n",
                isempty(top_u1) ? 0 : top_u1[1][1])
        @printf(io, "         → x₁+x₂ ≡ -%d (mod %d) for most high-mult keys\n",
                isempty(top_u1) ? 0 : top_u1[1][1], pi)
        @printf(io, "         → these keys lie on the hyperplane x₁+x₂ = const in Kummer space\n")
    else
        @printf(io, "      u1 values are spread — no common x-sum constraint\n")
    end

    # v1 clustering
    v1_counts = Dict{Int,Int}()
    for v in v1_vals; v1_counts[v] = get(v1_counts, v, 0) + 1; end
    top_v1 = sort(collect(v1_counts), by=x -> -x[2])
    v1_top1_frac = isempty(top_v1) ? 0.0 : top_v1[1][2] / Float64(n_top)

    @printf(io, "\n    v1 clustering:\n")
    @printf(io, "      distinct v1 values among top-%d keys : %d\n", n_top, length(v1_counts))
    @printf(io, "      top-1 v1 value appears               : %d / %d  (%.1f%%)\n",
            isempty(top_v1) ? 0 : top_v1[1][2], n_top, 100.0 * v1_top1_frac)
    if v1_top1_frac > 0.3
        @printf(io, "      ↑ CLUSTERING: many top keys share v1=%d\n",
                isempty(top_v1) ? 0 : top_v1[1][1])
    else
        @printf(io, "      v1 values are spread\n")
    end

    # disc_u distribution mod small primes
    @printf(io, "\n    disc(u) mod small primes (structure probe):\n")
    for q in (2, 3, 5, 7, 11, 13)
        res_counts = Dict{Int,Int}()
        for dv in disc_u_vals
            r = mod(dv, q); res_counts[r] = get(res_counts, r, 0) + 1
        end
        fracs = sort([(r, c / Float64(n_top)) for (r,c) in res_counts], by=x->-x[2])
        top_r, top_f = fracs[1]
        exp_f = 1.0 / q
        note = top_f > 3.0 * exp_f ? " ← CONCENTRATED ($(round(Int, top_f / exp_f))× expected)" : ""
        @printf(io, "      mod %2d: top residue=%d  freq=%.3f  (uniform=%.3f)%s\n",
                q, top_r, top_f, exp_f, note)
    end

    # High-multiplicity model: if top-K hold fraction f of F₂, estimate n_hot
    @printf(io, "\n    High-multiplicity model:\n")
    if total_N > 0 && c_max > 1
        # Estimate: n_hot keys each with count c_max → F₂_model = n_hot * c_max²
        # n_hot such that n_hot * c_max² = F₂_topk  → n_hot = F₂_topk / c_max²
        n_hot_est = f2_topk / Float64(c_max)^2
        mass_hot  = n_hot_est * c_max / Float64(total_N)
        kappa_est = n_hot_est > 0.0 ? log(n_hot_est) / logp : 0.0
        @printf(io, "      Effective n_hot (c ~ c_max = %d)  : %.2f  (κ = log_p(n_hot) = %.4f)\n",
                c_max, n_hot_est, kappa_est)
        @printf(io, "      Mass fraction from hot keys        : %.4f%%\n", 100.0 * mass_hot)
        @printf(io, "      S₂ model (n_hot × c_max²)         : %.5g  vs observed S₂ above\n",
                Float64(total_N)^2 / (n_hot_est * Float64(c_max)^2))
        if kappa_est > 0.0
            @printf(io, "      Interpretation: ~p^%.4f keys dominate F₂\n", kappa_est)
            if kappa_est < 0.3
                @printf(io, "        → sub-polynomial count: walk is attracted to O(1) Jacobian elements\n")
            elseif kappa_est < 0.7
                @printf(io, "        → small algebraic family: these keys may lie on a low-dim subvariety\n")
            else
                @printf(io, "        → broad fat tail: no sharp algebraic confinement of hot keys\n")
            end
        end
    end

    @printf(io, "\n══ End D17 ═══════════════════════════════════════════════════════════\n")
    flush(io)
    nothing
end
