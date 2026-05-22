# =============================================================================
#  lp1_conj_lsm.jl  —  Staged RAM+SSD LP1-conj index (LSM-tree style)
#
#  Drop-in replacement for ShardedLP1Conj that caps RAM usage at O(buffer size)
#  rather than O(total entries) by spilling sorted runs to HDF5 on SSD.
#
#  Design
#  ──────
#  Hot path (RAM):
#    • A small sharded open-addressing table (LP1ConjLSM.hot) holds the most
#      recently inserted entries.  Same ConjShard{V} primitives as before.
#    • When any shard's live count crosses its flush threshold, a background
#      task sorts it by fingerprint and writes a sorted "run" to HDF5.
#
#  Cold path (SSD):
#    • Each flushed run is a columnar HDF5 group containing flat UInt64 arrays:
#        run_NNNN/fp   :: UInt64   — sort key (fingerprint of packed Mumford key)
#        run_NNNN/u0   :: UInt64
#        run_NNNN/u1   :: UInt64
#        run_NNNN/v0   :: UInt64
#        run_NNNN/v1   :: UInt64
#        run_NNNN/i0   :: UInt16
#        run_NNNN/al   :: UInt64
#        run_NNNN/be   :: UInt64   (0 in amortized mode)
#    • An in-RAM RunIndex stores (min_fp, max_fp, length) per run for cheap
#      dispatch: a probe whose fingerprint lies outside [min,max] skips the run
#      entirely with no disk IO.
#
#  Lookup protocol
#  ───────────────
#    1. Compute fingerprint fp of the incoming CanonicalLP1Key.
#    2. Probe hot shard (RAM).
#    3. For each disk run whose [min_fp, max_fp] brackets fp:
#         a. Binary-search run/fp array for fp.
#         b. Linear-scan the (typically empty or 1-element) match range.
#         c. For each candidate, verify full key equality.
#         d. On match: read payload (i0, al, be) and mark slot as tombstoned.
#    4. Return found/not-found.
#
#  Insert protocol
#  ───────────────
#    1. Probe hot shard first; if already present, close and delete.
#    2. If hot shard full (at flush threshold): flush shard to disk, then insert.
#    3. Otherwise: insert into hot shard.
#
#  Concurrency
#  ───────────
#    • Per-shard ReentrantLocks guard hot table mutations (unchanged from before).
#    • HDF5 file access is serialised via a single global file_lock.
#    • Disk reads during lookup hold only the file_lock, not the shard lock —
#      avoiding cross-lock ordering deadlocks.
#    • Run metadata (RunIndex vector) is protected by file_lock.
#
#  Compatibility
#  ─────────────
#    ShardedLP1ConjLSM exports the same public API as ShardedLP1Conj:
#      conj_shard_idx(key)           — routes CanonicalLP1Key by low bits
#      canonical_lp1_conj_key(...)   — replaces conj_key32
#      conj_total_entries(sc)        — includes hot + estimated disk entries
#      conj_haskey(sc, si, key)      — hot + cold probe
#      conj_getval(sc, si, key)      — hot + cold fetch (does NOT delete)
#      conj_pop!(sc, si, key)        — hot + cold fetch-and-delete
#      conj_insert!(sc, si, key, val)— hot insert with flush-on-full
#    plus:
#      lsm_flush_all!(sc)            — force-flush all dirty hot shards
#      lsm_close!(sc)                — flush + close HDF5 file
#
#  Dependencies
#  ────────────
#    HDF5.jl  (add with:  import Pkg; Pkg.add("HDF5"))
# =============================================================================

using HDF5

# ---------------------------------------------------------------------------
#  Canonical key type  (defined in trial3_config.jl; referenced here)
# ---------------------------------------------------------------------------
# CanonicalLP1Key = UInt128, defined in trial3_config.jl.
# Single UInt128 packing: lo32=u0, bits32-63=u1, bits64-95=v0, hi32=v1.

# ---------------------------------------------------------------------------
#  Fingerprint
#
#  Same multiply-constants as _conj_hash64 in trial3_config.jl but exported
#  under a distinct name so this file is self-contained.
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
#  RunMeta — in-RAM metadata for one flushed run on SSD
# ---------------------------------------------------------------------------
struct RunMeta
    id     ::Int      # run index (for dataset name "run_NNNN")
    min_fp ::UInt64
    max_fp ::UInt64
    len    ::Int      # number of records
    # tombstoned slots: bit-packed; stored as a Vector{UInt64} of length
    # cld(len, 64).  We allocate it lazily on first delete from this run.
    # Protected by file_lock.
    tombs  ::Vector{UInt64}
end

function RunMeta(id::Int, min_fp::UInt64, max_fp::UInt64, len::Int)
    RunMeta(id, min_fp, max_fp, len, UInt64[])
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
        # zero newly appended words
        for i in length(rm.tombs):-1:1
            rm.tombs[i] == 0 && break
            rm.tombs[i] = 0
        end
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
    # Hot RAM table — same structure as ShardedLP1Conj
    hot_keys    ::Vector{Vector{CanonicalLP1Key}}    # [shard][slot]
    hot_vals    ::Vector{Vector{V}}                  # [shard][slot]
    hot_counts  ::Vector{Int}                        # live entries per shard
    hot_caps    ::Vector{Int}                        # slot count per shard (pow2)
    hot_masks   ::Vector{UInt}                       # slot_count - 1
    hot_thresh  ::Vector{Int}                        # flush when count >= thresh
    shard_locks ::Vector{ReentrantLock}

    # Disk metadata
    runs        ::Vector{RunMeta}       # one entry per flushed run
    file_lock   ::ReentrantLock
    hdf_path    ::String
    hdf_fid     ::Union{HDF5.File, Nothing}

    # Bookkeeping
    n_shards    ::Int
    max_entries ::Int   # total cap (informational)
    n_disk_live ::Int   # estimated live (non-tombstoned) records on disk
    amortized   ::Bool  # if true, be == 0 always → store/retrieve 0
end

# ---------------------------------------------------------------------------
#  Construction
# ---------------------------------------------------------------------------
function LP1ConjLSM{V}(
        n_shards    ::Int,
        cap_per_shard::Int,       # hot-shard cap (entries, not slots)
        max_entries ::Int,
        hdf_path    ::String;
        amortized   ::Bool = true,
        load_num    ::Int  = 4,
        load_denom  ::Int  = 5
    ) where V

    function make_shard(cap_entries::Int)
        slot_count = max(16, nextpow(2, cld(cap_entries * load_denom, load_num)))
        keys = fill(CONJ_KEY_EMPTY, slot_count)
        vals = Vector{V}(undef, slot_count)
        thresh = cld(slot_count * load_num, load_denom)   # 80% load
        (keys, vals, slot_count, UInt(slot_count - 1), thresh)
    end

    hot_keys   = Vector{Vector{CanonicalLP1Key}}(undef, n_shards)
    hot_vals   = Vector{Vector{V}}(undef, n_shards)
    hot_counts = zeros(Int, n_shards)
    hot_caps   = zeros(Int, n_shards)
    hot_masks  = zeros(UInt, n_shards)
    hot_thresh = zeros(Int, n_shards)
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

    # Open (or create) HDF5 file — always truncate so run_NNNN names start from 1
    # and never collide with groups left behind by a prior crashed run.
    fid = h5open(hdf_path, "w")

    LP1ConjLSM{V}(
        hot_keys, hot_vals, hot_counts, hot_caps, hot_masks, hot_thresh,
        shard_locks,
        RunMeta[], ReentrantLock(), hdf_path, fid,
        n_shards, max_entries, 0,
        amortized
    )
end

# Convenience constructor mirroring ShardedLP1Conj(ell; amortized=...)
# Uses same LP1_CONJ_CAP_MULTIPLIER / N_CONJ_SHARDS constants.
# hot_shard_entries controls how many entries each shard buffers before flush.
function LP1ConjLSM(
        ell          ::Integer;
        amortized    ::Bool = true,
        hdf_path     ::String = "/tmp/lp1_conj_lsm.h5",
        hot_shard_entries::Int = 50_000   # ~50 K entries per shard hot
    )
    cap = min(LP1_CONJ_CAP_MULTIPLIER * Int(min(ell, p)), LP1_CONJ_CAP_MAX)
    V   = amortized ? LP1ConjVal : LP1ConjValFull
    LP1ConjLSM{V}(
        N_CONJ_SHARDS,
        hot_shard_entries,
        cap,
        hdf_path;
        amortized = amortized
    )
end

# ---------------------------------------------------------------------------
#  Low-level hot-shard primitives (mirror ConjShard API)
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
#  Flush one shard to disk
#
#  Collects all live entries from hot_keys[si]/hot_vals[si], sorts by
#  fingerprint, writes columnar HDF5 arrays under a new run group, updates
#  RunMeta, resets hot shard.
#
#  Caller must hold BOTH sc.shard_locks[si] AND sc.file_lock.
# ---------------------------------------------------------------------------
function _lsm_flush_shard!(sc::LP1ConjLSM{V}, si::Int) where V
    n = sc.hot_counts[si]
    n == 0 && return   # nothing to flush

    # Collect live entries
    fps  = Vector{UInt64}(undef, n)
    u0s  = Vector{UInt64}(undef, n)
    u1s  = Vector{UInt64}(undef, n)
    v0s  = Vector{UInt64}(undef, n)
    v1s  = Vector{UInt64}(undef, n)
    i0s  = Vector{UInt16}(undef, n)
    als  = Vector{UInt64}(undef, n)
    bes  = Vector{UInt64}(undef, n)

    idx = 0
    keys = sc.hot_keys[si]
    vals = sc.hot_vals[si]
    @inbounds for slot in 1:sc.hot_caps[si]
        k = keys[slot]
        k == CONJ_KEY_EMPTY && continue
        idx += 1
        fps[idx] = _lsm_fp(k)
        u0s[idx] = UInt64(k & 0x00000000ffffffff)
        u1s[idx] = UInt64((k >> 32)  & 0x00000000ffffffff)
        v0s[idx] = UInt64((k >> 64)  & 0x00000000ffffffff)
        v1s[idx] = UInt64((k >> 96)  & 0x00000000ffffffff)
        v = vals[slot]
        i0s[idx] = v.i0
        als[idx] = v.neg_al
        bes[idx] = sc.amortized ? UInt64(0) : UInt64(_conj_prev_be(v))
    end
    # idx should equal n; guard defensively
    if idx != n
        throw(AssertionError("_lsm_flush_shard!: collected $idx entries but count=$n"))
    end

    # Sort by fingerprint
    order = sortperm(fps)
    fps  = fps[order]
    u0s  = u0s[order]
    u1s  = u1s[order]
    v0s  = v0s[order]
    v1s  = v1s[order]
    i0s  = i0s[order]
    als  = als[order]
    bes  = bes[order]

    # Write to HDF5
    run_id   = length(sc.runs) + 1
    grp_name = @sprintf("run_%04d", run_id)
    sc.hdf_fid === nothing && throw(ErrorException("_lsm_flush_shard!: HDF5 file is closed"))
    g = create_group(sc.hdf_fid, grp_name)
    g["fp"] = fps
    g["u0"] = u0s
    g["u1"] = u1s
    g["v0"] = v0s
    g["v1"] = v1s
    g["i0"] = i0s
    g["al"] = als
    g["be"] = bes
    close(g)
    flush(sc.hdf_fid)

    # Register run metadata
    push!(sc.runs, RunMeta(run_id, fps[1], fps[end], n))
    sc.n_disk_live += n

    # Reset hot shard
    fill!(sc.hot_keys[si], CONJ_KEY_EMPTY)
    sc.hot_counts[si] = 0

    nothing
end

# ---------------------------------------------------------------------------
#  Cold (disk) lookup
#
#  Returns (found::Bool, run_idx::Int, pos_in_run::Int, V-payload fields)
#  Caller must hold sc.file_lock.
# ---------------------------------------------------------------------------
function _lsm_disk_find(sc::LP1ConjLSM{V},
                         key::CanonicalLP1Key)::Tuple{Bool,Int,Int,UInt16,UInt64,UInt64} where V
    fp_target = _lsm_fp(key)
    ku0 = UInt64(key & 0x00000000ffffffff)
    ku1 = UInt64((key >> 32)  & 0x00000000ffffffff)
    kv0 = UInt64((key >> 64)  & 0x00000000ffffffff)
    kv1 = UInt64((key >> 96)  & 0x00000000ffffffff)

    sc.hdf_fid === nothing && throw(ErrorException("_lsm_disk_find: HDF5 file is closed"))

    for (ri, rm) in enumerate(sc.runs)
        # Cheap range filter
        (fp_target < rm.min_fp || fp_target > rm.max_fp) && continue

        grp_name = @sprintf("run_%04d", rm.id)
        g = sc.hdf_fid[grp_name]

        fps_arr = read(g, "fp")   # Vector{UInt64}

        # Binary search for left boundary
        lo = searchsortedfirst(fps_arr, fp_target)
        lo > rm.len && (close(g); continue)

        # Scan matching fingerprints
        pos = lo
        while pos <= rm.len && fps_arr[pos] == fp_target
            if _run_is_dead(rm, pos)
                pos += 1; continue
            end
            # Verify exact key
            u0arr = read(g, "u0"); u1arr = read(g, "u1")
            v0arr = read(g, "v0"); v1arr = read(g, "v1")
            if u0arr[pos] == ku0 && u1arr[pos] == ku1 &&
               v0arr[pos] == kv0 && v1arr[pos] == kv1
                i0arr = read(g, "i0")
                alarr = read(g, "al")
                bearr = read(g, "be")
                i0_v  = i0arr[pos]
                al_v  = alarr[pos]
                be_v  = bearr[pos]
                close(g)
                return (true, ri, pos, i0_v, al_v, be_v)
            end
            pos += 1
        end
        close(g)
    end
    return (false, 0, 0, UInt16(0), UInt64(0), UInt64(0))
end

# Mark a disk record as tombstoned.  Caller must hold sc.file_lock.
function _lsm_disk_delete!(sc::LP1ConjLSM, ri::Int, pos::Int)
    rm = sc.runs[ri]
    _run_set_dead!(rm, pos)
    sc.n_disk_live -= 1
    nothing
end

# ---------------------------------------------------------------------------
#  Public API  (mirrors ShardedLP1Conj)
# ---------------------------------------------------------------------------

# Total live entries (hot + estimated disk)
function conj_total_entries(sc::LP1ConjLSM)::Int
    hot = sum(sc.hot_counts)
    hot + sc.n_disk_live
end

# Probe: hot then cold.  Acquires shard lock + file_lock.
function conj_haskey(sc::LP1ConjLSM, si::Int, key::CanonicalLP1Key)::Bool
    hot_found = lock(sc.shard_locks[si]) do
        _lsm_hot_find(sc, si, key) != 0
    end
    hot_found && return true
    found, _, _, _, _, _ = lock(sc.file_lock) do
        _lsm_disk_find(sc, key)
    end
    return found
end

# Fetch without delete.  Hot path: returns value directly.
# Cold path: reconstructs V from stored fields.
function conj_getval(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    # Hot
    slot = lock(sc.shard_locks[si]) do
        _lsm_hot_find(sc, si, key)
    end
    if slot != 0
        return @inbounds sc.hot_vals[si][slot]
    end
    # Cold
    found, _, _, i0_v, al_v, be_v = lock(sc.file_lock) do
        _lsm_disk_find(sc, key)
    end
    found || throw(KeyError(key))
    return _conj_make_val(V, i0_v, al_v, be_v)
end

# Fetch-and-delete.  Hot: backward-shift delete.  Cold: tombstone.
function conj_pop!(sc::LP1ConjLSM{V}, si::Int, key::CanonicalLP1Key)::V where V
    # Hot
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
    # Cold — need file_lock
    found, ri, pos, i0_v, al_v, be_v = lock(sc.file_lock) do
        res = _lsm_disk_find(sc, key)
        if res[1]
            _lsm_disk_delete!(sc, res[2], res[3])
        end
        res
    end
    found || throw(KeyError(key))
    return _conj_make_val(V, i0_v, al_v, be_v)
end

# Like conj_pop! but returns nothing on TOCTOU miss (haskey=true but entry vanished)
# rather than throwing.  Used by handle_1lp_conj! to distinguish races from bugs.
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
    found, ri, pos, i0_v, al_v, be_v = lock(sc.file_lock) do
        res = _lsm_disk_find(sc, key)
        if res[1]
            _lsm_disk_delete!(sc, res[2], res[3])
        end
        res
    end
    found || return nothing
    return _conj_make_val(V, i0_v, al_v, be_v)
end

# Immediate round-trip check: insert key/val, then verify haskey returns true.
# Returns true if the entry is findable immediately after insert.
# Inserts unconditionally (for diagnostic purposes) regardless of whether key exists.
# Caller must ensure this is only called when key is NOT already present.
function conj_roundtrip_ok(sc::LP1ConjLSM{V}, si::Int,
                            key::CanonicalLP1Key, val::V)::Bool where V
    conj_insert!(sc, si, key, val)
    return conj_haskey(sc, si, key)
end

# Insert key→val.  If hot shard is full (at flush threshold), flush to disk
# first, then insert.  Returns true if stored, false if dropped (only when
# flush itself fails — shouldn't happen under normal conditions).
function conj_insert!(sc::LP1ConjLSM{V}, si::Int,
                       key::CanonicalLP1Key, val::V)::Bool where V
    needs_flush = lock(sc.shard_locks[si]) do
        if sc.hot_counts[si] >= sc.hot_thresh[si]
            true   # signal: need flush path
        else
            _lsm_hot_insert!(sc, si, key, val)
            false  # inserted; done
        end
    end
    needs_flush || return true

    # Full path: acquire both locks in order (file_lock outer, shard_lock inner)
    lock(sc.file_lock) do
        lock(sc.shard_locks[si]) do
            # Re-check after re-acquiring: another thread may have flushed.
            if sc.hot_counts[si] >= sc.hot_thresh[si]
                _lsm_flush_shard!(sc, si)
            end
            _lsm_hot_insert!(sc, si, key, val)
        end
    end
    return true
end

# Force-flush all non-empty hot shards.
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

# Flush + close HDF5 file.  After this call the object is inert.
function lsm_close!(sc::LP1ConjLSM)
    lsm_flush_all!(sc)
    lock(sc.file_lock) do
        if sc.hdf_fid !== nothing
            close(sc.hdf_fid)
            sc.hdf_fid = nothing
        end
    end
    nothing
end

# ---------------------------------------------------------------------------
#  Sharding helpers — identical to the ShardedLP1Conj versions so call sites
#  in phase2/phase3 need no changes.
# ---------------------------------------------------------------------------
# (conj_shard_idx(::CanonicalLP1Key) and canonical_lp1_conj_key are defined
#  in trial3_config.jl; LP1ConjLSM reuses them.  No re-definition needed here.)

# ---------------------------------------------------------------------------
#  Val-type helpers — same _conj_make_val / _conj_prev_be from config
# ---------------------------------------------------------------------------
# Already defined in trial3_config.jl.  LP1ConjLSM uses them transparently.

# ---------------------------------------------------------------------------
#  Diagnostic / info
# ---------------------------------------------------------------------------
function lsm_info(sc::LP1ConjLSM; io::IO = stdout)
    hot_total = sum(sc.hot_counts)
    @printf(io, "LP1ConjLSM: %d hot entries | %d disk-live entries | %d runs\n",
            hot_total, sc.n_disk_live, length(sc.runs))
    @printf(io, "  HDF5 path: %s\n", sc.hdf_path)
    @printf(io, "  Hot shards: %d  (thresh %d/shard)\n",
            sc.n_shards, sc.hot_thresh[1])
    if !isempty(sc.runs)
        total_disk = sum(rm.len for rm in sc.runs)
        tombed     = total_disk - sc.n_disk_live
        @printf(io, "  Disk records: %d total, %d tombstoned (%.1f%%)\n",
                total_disk, tombed, 100.0 * tombed / max(1, total_disk))
    end
    nothing
end
