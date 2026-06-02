# =============================================================================
#  lp1_conj_lsm_disk.jl — disk/spill-file layer for LP1ConjLSM
#
#  Covers:
#    • RunMeta — in-RAM metadata for one flushed sorted run + tombstone helpers
#    • Record encode/decode helpers (_write_record!, _buf_*, _mmap_*, _rec_*)
#    • Raw I/O syscall wrappers (_open_direct, _pread_record!, _fadvise_dontneed!)
#    • _lsm_disk_find  — binary-search lookup across all runs
#    • _lsm_disk_delete! — tombstone a found record
#    • k-way merge heap helpers used by _lsm_compact! (defined in core)
# =============================================================================

# ---------------------------------------------------------------------------
#  RunMeta — in-RAM metadata for one flushed sorted run
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
#  Raw I/O syscall wrappers
#
#  We do NOT use O_DIRECT because RECORD_BYTES=48 is not sector-aligned;
#  that would trigger EINVAL on every pread.  Instead we call
#  posix_fadvise(DONTNEED) after each flush/compact to keep the page cache
#  from eating all RAM.
# ---------------------------------------------------------------------------
function _open_direct(path::String)::Cint
    fd = ccall(:open, Cint, (Cstring, Cint), path, Cint(0))
    fd < 0 && error("_open_direct: cannot open $(path): $(Base.Libc.strerror())")
    fd
end

# POSIX_FADV_DONTNEED = 4 on Linux x86-64.
@inline function _fadvise_dontneed!(fd::Cint)
    fd < 0 && return
    ccall(:posix_fadvise, Cint, (Cint, Int64, Int64, Cint),
          fd, Int64(0), Int64(0), Cint(4))
    nothing
end

@inline function _pread_record!(fd::Cint, buf::Vector{UInt8}, off::Int)
    n = ccall(:pread, Cssize_t, (Cint, Ptr{UInt8}, Csize_t, Int64),
              fd, buf, RECORD_BYTES, off)
    if n != RECORD_BYTES
        err_msg = Base.Libc.strerror()
        error("_pread_record!: short read ($n) at offset $off. OS Error: $err_msg")
    end
    nothing
end

# ---------------------------------------------------------------------------
#  Buffer field accessors (0-based byte offsets from buffer start)
# ---------------------------------------------------------------------------
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

# ---------------------------------------------------------------------------
#  mmap-style field accessors (same layout; used in the compaction read path)
# ---------------------------------------------------------------------------
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

# ---------------------------------------------------------------------------
#  Run-relative helpers
# ---------------------------------------------------------------------------
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
    # pad (6 bytes)
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
#  Cold (disk) lookup
#
#  Returns (found, run_idx, pos_in_run, i0_v, al_v, be_v).
#  Caller must hold sc.file_lock.  `read_fd` and `buf` are the LSM's
#  spill_read_io and read_buf fields passed in directly so this function
#  remains free of LP1ConjLSM-type references (defined later in core).
# ---------------------------------------------------------------------------
function _lsm_disk_find(runs::Vector{RunMeta},
                         read_fd::Cint,
                         buf::Vector{UInt8},
                         key::CanonicalLP1Key,
                         fp_target::UInt64
                        )::Tuple{Bool,Int,Int,UInt16,UInt64,UInt64}
    read_fd < 0 && return (false, 0, 0, UInt16(0), UInt64(0), UInt64(0))
    ku0 = UInt32(key & 0x00000000ffffffff)
    ku1 = UInt32((key >> 32)  & 0x00000000ffffffff)
    kv0 = UInt32((key >> 64)  & 0x00000000ffffffff)
    kv1 = UInt32((key >> 96)  & 0x00000000ffffffff)

    for (ri, rm) in enumerate(runs)
        (fp_target < rm.min_fp || fp_target > rm.max_fp) && continue

        # Binary search on fp via pread.
        lo = 1; hi = rm.len
        while lo < hi
            mid = (lo + hi) >>> 1
            _pread_record!(read_fd, buf, _rec_base(rm, mid))
            if _buf_fp(buf) < fp_target
                lo = mid + 1
            else
                hi = mid
            end
        end
        lo > rm.len && continue
        _pread_record!(read_fd, buf, _rec_base(rm, lo))
        _buf_fp(buf) != fp_target && continue

        # Scan all records sharing this fingerprint.
        pos = lo
        while pos <= rm.len
            _pread_record!(read_fd, buf, _rec_base(rm, pos))
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

# ---------------------------------------------------------------------------
#  k-way merge min-heap helpers (used by _lsm_compact! in core)
# ---------------------------------------------------------------------------
@inline function _compact_heap_less(a::Tuple{UInt64,Int,Int}, b::Tuple{UInt64,Int,Int})
    a[1] < b[1] || (a[1] == b[1] && a[2] < b[2])
end

function _compact_heap_push!(h::Vector{Tuple{UInt64,Int,Int}}, x::Tuple{UInt64,Int,Int})
    push!(h, x)
    i = length(h)
    @inbounds while i > 1
        p = i >> 1
        if _compact_heap_less(h[i], h[p])
            h[i], h[p] = h[p], h[i]
            i = p
        else
            break
        end
    end
    nothing
end

function _compact_heap_pop!(h::Vector{Tuple{UInt64,Int,Int}})::Tuple{UInt64,Int,Int}
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
        l <= n && _compact_heap_less(h[l], h[smallest]) && (smallest = l)
        r <= n && _compact_heap_less(h[r], h[smallest]) && (smallest = r)
        smallest == i && break
        h[i], h[smallest] = h[smallest], h[i]
        i = smallest
    end
    top
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
