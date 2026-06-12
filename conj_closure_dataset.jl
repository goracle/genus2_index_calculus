# =============================================================================
#  conj_closure_dataset.jl  —  LP1-conj closure dataset writer
#
#  Records one 64-byte entry per LP1-conj closure.  The resulting flat binary
#  file plus a companion JSON schema can be loaded directly into numpy/PyTorch:
#
#    import numpy as np
#    dt = np.dtype([
#        ('c0',         np.int32), ('c1',         np.int32),
#        ('v0',         np.int32), ('v1',         np.int32),
#        ('i0',         np.int32), ('neg_al',      np.int32),
#        ('neg_be',     np.int32), ('raw_steps',   np.int32),
#        ('prev_col',   np.int32), ('prev_al',     np.int32),
#        ('prev_be',    np.int32), ('store_step',  np.int32),
#        ('combined_al',np.int32), ('combined_be', np.int32),
#        ('step_gap',   np.int32),
#        ('al_cur',     np.int32), ('px_anchor',   np.int32),
#        ('py_anchor',  np.int32), ('a_raw',       np.int32),
#        ('a_bucket',   np.int32), ('tid',         np.int32),
#        ('_pad',       np.int32),   # reserved, always 0
#    ])
#    data = np.fromfile("conj_closures.bin", dtype=dt)
#    # data.shape == (N,); access e.g. data['combined_al']
#
#  Field semantics
#  ───────────────
#  The LP1-conj protocol:
#    Two walk positions (stored & incoming) independently reach the same LP
#    key — a degree-2 Mumford point over F_p² identified by its 4 Mumford
#    coordinates.  Closure emits the weight-2 FB relation:
#
#      fb[i0] − fb[prev_col] = combined_al·G + combined_be·T  (mod ell)
#
#  LP key (Mumford coordinates of the shared non-split residual):
#    c0, c1, v0, v1  — Int32; see canonical_lp1_conj_key in trial3_config.jl
#
#  Incoming partial (the walk step that triggered the closure):
#    i0         — FB column index of this step's P0 anchor
#    neg_al     — (−α) mod ell  at this step
#    neg_be     — (−β) mod ell  at this step
#    raw_steps  — step counter of the arriving thread at closure time
#
#  Stored partial (the previously stored waiting entry):
#    prev_col   — FB column index when the stored entry was created
#    prev_al    — neg_al stored in the waiting entry
#    prev_be    — neg_be stored in the waiting entry
#    store_step — raw_steps value when the stored entry was inserted
#
#  Derived scalar outputs:
#    combined_al — mod(neg_al − prev_al, ell)   (coefficient of G in relation)
#    combined_be — mod(neg_be − prev_be, ell)   (coefficient of T in relation)
#    step_gap    — raw_steps − store_step        (birthday gap; clamped to Int32)
#
#  Walk context at the moment of closure (incoming thread):
#    al_cur      — raw α cursor value (before mod ell)
#    px_anchor   — x-coordinate of P0
#    py_anchor   — y-coordinate of P0
#    a_raw       — a parameter from build_phi_mumford (the φ linear coefficient)
#    a_bucket    — a_raw bucketed into [1, n_split_hist_buckets]
#
#  Bookkeeping:
#    tid         — Julia thread id of the arriving thread
#    _pad        — reserved / always 0
#
#  Each record is exactly CONJ_RECORD_BYTES = 88 bytes (22 × Int32).
#  The file begins with a 16-byte magic + version header so a reader can
#  sanity-check endianness and layout:
#
#    bytes 0..7   : magic = 0x434F4E4A434C4F53  ("CONJCLOS" in ASCII)
#    bytes 8..11  : version = Int32(1)
#    bytes 12..15 : record_bytes = Int32(CONJ_RECORD_BYTES)
#    bytes 16..   : packed Int32[22] records, one per closure
#
#  Thread safety: all writes go through a single ReentrantLock; this is
#  fine because dataset writes are rare compared to walk steps.
# =============================================================================

const CONJ_MAGIC        = 0x434F4E4A434C4F53  # "CONJCLOS"
const CONJ_VERSION      = Int32(1)
const CONJ_N_FIELDS     = 22
const CONJ_RECORD_BYTES = CONJ_N_FIELDS * sizeof(Int32)   # 88 bytes

# Field names in order — kept here as the single source of truth.
const CONJ_FIELD_NAMES = [
    "c0", "c1", "v0", "v1",            # LP key (Mumford coords)
    "i0", "neg_al", "neg_be", "raw_steps",        # incoming partial
    "prev_col", "prev_al", "prev_be", "store_step", # stored partial
    "combined_al", "combined_be", "step_gap",     # derived relation
    "al_cur", "px_anchor", "py_anchor", "a_raw", "a_bucket", # walk context
    "tid",                                         # bookkeeping
    "_pad",                                        # reserved
]

mutable struct ConjClosureDataset
    path    ::String
    io      ::IOStream
    lock    ::ReentrantLock
    n_records::Threads.Atomic{Int}
end

"""
    open_conj_dataset(path) -> ConjClosureDataset

Open (or create) the binary dataset file at `path` and write the 16-byte
header.  Call `close_conj_dataset` when the walk finishes.
"""
function open_conj_dataset(path::String)::ConjClosureDataset
    io = open(path, "w")
    # Write header: magic (UInt64 LE), version (Int32), record_bytes (Int32)
    write(io, UInt64(CONJ_MAGIC))
    write(io, CONJ_VERSION)
    write(io, Int32(CONJ_RECORD_BYTES))
    flush(io)
    ds = ConjClosureDataset(path, io, ReentrantLock(), Threads.Atomic{Int}(0))
    # Write companion schema JSON immediately so the file is always usable
    # even if the Julia process is killed mid-run.
    _write_conj_schema(path)
    return ds
end

function close_conj_dataset(ds::ConjClosureDataset)
    lock(ds.lock) do
        flush(ds.io)
        close(ds.io)
    end
    @printf("[ConjDataset] closed %s  (%d records, %.2f MB)\n",
            ds.path, ds.n_records[], ds.n_records[] * CONJ_RECORD_BYTES / 1024^2)
end

"""
    record_conj_closure!(ds, lp_key, i0, neg_al, neg_be, raw_steps,
                         prev_col, prev_al, prev_be, store_step,
                         combined_al, combined_be, ell,
                         al_cur, px_anchor, py_anchor, a_raw, a_bucket)

Append one closure record to the dataset.  Safe to call from any thread.
All integer arguments are plain Julia Ints; values are truncated to Int32
before writing (any value larger than typemax(Int32) is clamped to
typemax(Int32) so the record is never silently corrupted).
"""
@inline function record_conj_closure!(
        ds          ::ConjClosureDataset,
        lp_key      ::NTuple{4,Int},   # (c0, c1, v0, v1)
        i0          ::Int,
        neg_al      ::Int,
        neg_be      ::Int,
        raw_steps   ::Int,
        prev_col    ::Int,
        prev_al     ::Int,
        prev_be     ::Int,
        store_step  ::Int,
        combined_al ::Int,
        combined_be ::Int,
        al_cur      ::Int,
        px_anchor   ::Int,
        py_anchor   ::Int,
        a_raw       ::Int,
        a_bucket    ::Int)

    step_gap = raw_steps - store_step

    # Pack all 22 fields into a stack-allocated buffer.
    buf = (
        Int32(lp_key[1]),      # c0
        Int32(lp_key[2]),      # c1
        Int32(lp_key[3]),      # v0
        Int32(lp_key[4]),      # v1
        Int32(i0),             # i0
        Int32(neg_al),         # neg_al
        Int32(neg_be),         # neg_be
        Int32(clamp(raw_steps,  0, typemax(Int32))),  # raw_steps
        Int32(prev_col),       # prev_col
        Int32(prev_al),        # prev_al
        Int32(prev_be),        # prev_be
        Int32(clamp(store_step, 0, typemax(Int32))),  # store_step
        Int32(combined_al),    # combined_al
        Int32(combined_be),    # combined_be
        Int32(clamp(step_gap,   0, typemax(Int32))),  # step_gap
        Int32(al_cur),         # al_cur
        Int32(px_anchor),      # px_anchor
        Int32(py_anchor),      # py_anchor
        Int32(a_raw),          # a_raw
        Int32(a_bucket),       # a_bucket
        Int32(Threads.threadid()), # tid
        Int32(0),              # _pad
    )

    lock(ds.lock) do
        for x in buf
            write(ds.io, x)
        end
    end
    Threads.atomic_add!(ds.n_records, 1)
    return nothing
end

# ---------------------------------------------------------------------------
#  Companion JSON schema — written alongside the .bin file.
#  Lets Python code reconstruct the numpy dtype without hardcoding it.
# ---------------------------------------------------------------------------
function _write_conj_schema(bin_path::String)
    schema_path = splitext(bin_path)[1] * "_schema.json"
    open(schema_path, "w") do io
        println(io, "{")
        println(io, "  \"magic\": \"CONJCLOS\",")
        println(io, "  \"version\": 1,")
        println(io, "  \"header_bytes\": 16,")
        println(io, "  \"record_bytes\": ", CONJ_RECORD_BYTES, ",")
        println(io, "  \"dtype\": \"int32\",")
        println(io, "  \"endian\": \"little\",")
        println(io, "  \"n_fields\": ", CONJ_N_FIELDS, ",")
        println(io, "  \"fields\": [")
        for (k, name) in enumerate(CONJ_FIELD_NAMES)
            comma = k < length(CONJ_FIELD_NAMES) ? "," : ""
            println(io, "    {\"name\": \"", name, "\", \"dtype\": \"int32\", \"offset\": ", (k-1)*4, "}", comma)
        end
        println(io, "  ],")
        println(io, "  \"field_notes\": {")
        println(io, "    \"c0-v1\":        \"Mumford coords of the shared non-split LP residual\",")
        println(io, "    \"i0\":           \"FB column index of the incoming (closing) anchor\",")
        println(io, "    \"neg_al\":       \"(-alpha) mod ell at the incoming step\",")
        println(io, "    \"neg_be\":       \"(-beta)  mod ell at the incoming step\",")
        println(io, "    \"raw_steps\":    \"step counter of the arriving thread at closure\",")
        println(io, "    \"prev_col\":     \"FB column index of the stored (waiting) anchor\",")
        println(io, "    \"prev_al\":      \"neg_al stored in the waiting entry\",")
        println(io, "    \"prev_be\":      \"neg_be stored in the waiting entry\",")
        println(io, "    \"store_step\":   \"step counter when the waiting entry was inserted\",")
        println(io, "    \"combined_al\":  \"mod(neg_al - prev_al, ell) = coefficient of G in emitted relation\",")
        println(io, "    \"combined_be\":  \"mod(neg_be - prev_be, ell) = coefficient of T in emitted relation\",")
        println(io, "    \"step_gap\":     \"raw_steps - store_step (birthday gap)\",")
        println(io, "    \"al_cur\":       \"raw alpha cursor value (before mod ell) at the incoming step\",")
        println(io, "    \"px_anchor\":    \"x-coordinate of P0 (the incoming anchor point)\",")
        println(io, "    \"py_anchor\":    \"y-coordinate of P0 (the incoming anchor point)\",")
        println(io, "    \"a_raw\":        \"phi a-parameter (Int(a) from build_phi_mumford)\",")
        println(io, "    \"a_bucket\":     \"a_raw bucketed into [1, n_split_hist_buckets]\",")
        println(io, "    \"tid\":          \"Julia thread id of the arriving (closing) thread\",")
        println(io, "    \"_pad\":         \"reserved, always 0\"")
        println(io, "  }")
        println(io, "}")
    end
end
