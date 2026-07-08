# =============================================================================
#  alloc_test_harness.jl
#
#  Standalone @btime/@allocated harness for LP1ConjLSM and LP1ConjDeepDiag.
#  Run from the directory containing TrialConfig.jl, PhiBiasTypes.jl, and the
#  lp1/ package tree (LP1ConjLSM/, LP1ConjDeepDiag/), e.g.:
#
#      julia> include("alloc_test_harness.jl")
#
#  Adjust the `include(...)` paths below if your layout differs.
# =============================================================================

using BenchmarkTools
using Random

# ---------------------------------------------------------------------------
# 1. Load dependency chain in order: TrialConfig -> LP1ConjLSM -> LP1ConjDeepDiag
#    (PhiBiasTypes has no internal deps, load it any time before DeepDiag.)
#
#    TrialConfig/, PhiBiasTypes/, LP1ConjLSM/, LP1ConjDeepDiag/ are real
#    packages (Project.toml + src/) in this repo, so include() the src/
#    entry file directly rather than `using` them as installed packages —
#    avoids any Pkg.develop / LOAD_PATH setup.
# ---------------------------------------------------------------------------
#include("TrialConfig/src/TrialConfig.jl")
#include("PhiBiasTypes/src/PhiBiasTypes.jl")
#include("LP1ConjLSM/src/LP1ConjLSM.jl")
#include("LP1ConjDeepDiag/src/LP1ConjDeepDiag.jl")
#include(".")
pushfirst!(LOAD_PATH, @__DIR__)

using TrialConfig
using PhiBiasTypes
using LP1ConjLSM
using LP1ConjDeepDiag

# ---------------------------------------------------------------------------
# 2. Curve context — both TrialConfig and LP1ConjLSM keep their own global
#    F_POLY/p/ell, so set both. canonical_lp1_conj_key reduces mod TrialConfig.p.
# ---------------------------------------------------------------------------
const F_POLY_TEST = [1, 2, 3, 4, 5, 1]
const P_TEST      = 1_000_003
const ELL_TEST     = 11

TrialConfig.set_curve_context!(F_POLY_TEST, P_TEST, ELL_TEST)
LP1ConjLSM.set_curve_context!(F_POLY_TEST, P_TEST, ELL_TEST)

# ---------------------------------------------------------------------------
# 3. Stand up an LP1ConjLSMStore{LP1ConjVal} (amortized mode).
#    Store must use N_CONJ_SHARDS (64) shards -- see note below -- with modest
#    per-shard caps, spilling to a tmp dir.
# ---------------------------------------------------------------------------
spill_dir = mktempdir()
spill_path = joinpath(spill_dir, "lp1_conj_shards_test")

# IMPORTANT: conj_shard_idx (in TrialConfig/trial3_config.jl) always returns a
# value in [1, N_CONJ_SHARDS] via `key & (N_CONJ_SHARDS-1) + 1` — it is NOT
# parameterized by the store's own n_shards. The store's n_shards must equal
# N_CONJ_SHARDS or conj_shard_idx can return an index out of bounds for
# sc.shard_locks/hot_* (as it did here once we exercised enough distinct keys).
# The original 8-shard harness store only worked by coincidence for the single
# fixed test key, since key_test & 63 happened to also be <= 8.
lsm_store = LP1ConjLSMStore{LP1ConjVal}(
    N_CONJ_SHARDS,   # n_shards -- MUST match conj_shard_idx's fixed modulus
    1024,       # cap_per_shard (hot RAM)
    100_000,    # max_entries
    spill_path;
    amortized = true,
)
# Solo mode: point global_bloom at its own bloom, no peers.
lsm_store.global_bloom = lsm_store.bloom

# Build a representative key/val pair.
u0_t, u1_t, v0_t, v1_t = 7, 8, 9, 10
key_test = canonical_lp1_conj_key(u0_t, u1_t, v0_t, v1_t)
si_test  = conj_shard_idx(key_test)

fb_row_test = Dict(3 => 1, 5 => 2)   # dummy anchor multiplicities, sums to K_MAX-compatible <=6
val_test = _conj_make_val(LP1ConjVal, fb_row_test, UInt32(42), UInt64(123), UInt64(0))

println("== LP1ConjLSMStore (LP1ConjVal) ==")
println("key=$(key_test)  shard=$(si_test)")

@btime conj_insert!($lsm_store, $si_test, $key_test, $val_test)

# haskey/getval need a key that's actually present — reinsert fresh each @btime
# run is unnecessary since insert is idempotent-ish here (hot table just
# overwrites/upserts on repeat key), so this is safe to call repeatedly.
@btime conj_haskey($lsm_store, $si_test, $key_test)
@btime conj_getval($lsm_store, $si_test, $key_test)

println("@allocated conj_insert!  = ", @allocated conj_insert!(lsm_store, si_test, key_test, val_test))
println("@allocated conj_haskey   = ", @allocated conj_haskey(lsm_store, si_test, key_test))
println("@allocated conj_getval   = ", @allocated conj_getval(lsm_store, si_test, key_test))

# ---------------------------------------------------------------------------
# 4. Bloom filter (already confirmed zero-alloc, included here for completeness)
# ---------------------------------------------------------------------------
println()
println("== BloomFilter ==")
bf_test = BloomFilter(100_000)
fp_test = UInt64(0x123456789abcdef0)
@btime set_bloom!($bf_test, $fp_test)
@btime bloom_maybe_has($bf_test, $fp_test)

# ---------------------------------------------------------------------------
# 5. ConjDeepStat — deep diagnostic record functions.
#    These take only plain Int/Bool/UInt128 args, no TrialConfig/PhiBiasTypes
#    types directly, so this section is otherwise decoupled from the LSM store.
# ---------------------------------------------------------------------------
println()
println("== ConjDeepStat record functions ==")
deep_stat = ConjDeepStat()

lp_key_test  = UInt128(key_test)
raw_step_t   = 1000
alpha_cur_t  = 5
px_t         = 12
a_val_t      = 99
py_t         = 34

@btime record_conj_deep_miss!($deep_stat, $lp_key_test, $raw_step_t,
                               $alpha_cur_t, $px_t, $a_val_t, $py_t)

@btime record_conj_deep_step!($deep_stat, $lp_key_test, 3, $raw_step_t,
                               true, $alpha_cur_t, $px_t, 900, 0)

println("@allocated record_conj_deep_miss! = ",
        @allocated record_conj_deep_miss!(deep_stat, lp_key_test, raw_step_t,
                                           alpha_cur_t, px_t, a_val_t, py_t))
println("@allocated record_conj_deep_step! = ",
        @allocated record_conj_deep_step!(deep_stat, lp_key_test, 3, raw_step_t,
                                           true, alpha_cur_t, px_t, 900, 0))

# ---------------------------------------------------------------------------
# 6. conj_pop! / conj_pop_safe
#    Both need a key that's actually present, and both remove it — so each
#    @btime sample must reinsert first. @btime's setup=/evals= let us do that
#    without polluting the timed region.
# ---------------------------------------------------------------------------
println()
println("== conj_pop! / conj_pop_safe ==")

@btime conj_pop!($lsm_store, $si_test, $key_test) setup=(
    conj_insert!($lsm_store, $si_test, $key_test, $val_test)
) evals=1

@btime conj_pop_safe($lsm_store, $si_test, $key_test) setup=(
    conj_insert!($lsm_store, $si_test, $key_test, $val_test)
) evals=1

# reinsert so later sections have a live key again
conj_insert!(lsm_store, si_test, key_test, val_test)

println("@allocated conj_pop! (after reinsert) = ",
        (conj_insert!(lsm_store, si_test, key_test, val_test);
         @allocated conj_pop!(lsm_store, si_test, key_test)))
conj_insert!(lsm_store, si_test, key_test, val_test)  # leave present for section 7

# ---------------------------------------------------------------------------
# 7. conj_insert_or_pop! — exercise both the same-col-hit branch and the
#    genuine miss/insert branch. fb_row is accepted but unused (see comment
#    at the call site in lp1_conj_lsm_core.jl), so any Dict{Int,Int} works.
# ---------------------------------------------------------------------------
println()
println("== conj_insert_or_pop! ==")

# --- ADD THESE THREE LINES HERE ---
global si_new  = 0
global key_new = UInt128(0)
global val_new = val_test 
# ----------------------------------

fb_row_iop = Dict(3 => 1, 5 => 2)

# -- (a) same-col-hit branch: val_test's own (neg_al, neg_be) already present
#    in the store from section 3/6 above, so calling with the identical val
#    hits "same-partial" and returns (nothing, true, nothing) without any
#    hot-table mutation — cheapest branch, exercised repeatedly is safe.
@btime conj_insert_or_pop!($lsm_store, $si_test, $key_test, $val_test, $fb_row_iop)

let (prev, same_col, prev_row) = conj_insert_or_pop!(lsm_store, si_test, key_test, val_test, fb_row_iop)
    println("  same-col branch sanity: same_col=", same_col,
            "  prev=", prev, "  prev_row=", prev_row)
end

println("@allocated conj_insert_or_pop! (same-col) = ",
        @allocated conj_insert_or_pop!(lsm_store, si_test, key_test, val_test, fb_row_iop))

# -- (b) genuine miss/insert branch: needs a *fresh* key each call, since a
#    repeat on the same key after insertion becomes a same-col or collision
#    hit instead. Use setup= to mint a new (u0,u1,v0,v1)/key/val per sample.
miss_ctr = Ref(0)
const _MISS_ROW = Dict(2 => 1)  # hoisted out of setup= -- must not be part of the timed/counted allocation

# -- (b) genuine miss/insert branch: needs a *fresh* key each call, since a
#    repeat on the same key after insertion becomes a same-col or collision
#    hit instead. Use setup= to mint a new (u0,u1,v0,v1)/key/val per sample.
miss_ctr = Ref(0)
const _MISS_ROW = Dict(2 => 1)  # hoisted out of setup= -- must not be part of the timed/counted allocation

@btime conj_insert_or_pop!($lsm_store, si_new, key_new, val_new, $fb_row_iop) setup=(
    begin
        miss_ctr[] += 1
        n = miss_ctr[]
        global key_new = canonical_lp1_conj_key(100 + n, 200 + n, 300 + n, 400 + n)
        global si_new  = conj_shard_idx(key_new)
        global val_new = _conj_make_val(LP1ConjVal, _MISS_ROW, UInt32(n), UInt64(n), UInt64(n + 1))
    end
) evals=1

let n = (miss_ctr[] += 1)
    global key_new = canonical_lp1_conj_key(100 + n, 200 + n, 300 + n, 400 + n)
    global si_new  = conj_shard_idx(key_new)
    global val_new = _conj_make_val(LP1ConjVal, _MISS_ROW, UInt32(n), UInt64(n), UInt64(n + 1))
    println("@allocated conj_insert_or_pop! (miss/insert) = ",
            @allocated conj_insert_or_pop!(lsm_store, si_new, key_new, val_new, fb_row_iop))
end

# Diagnostic 2: confirm whether si_new/key_new/val_new being untyped globals
# (reassigned each setup= run) is the source of @btime's 3-alloc figure.
# Paste this in right after the existing section 7 miss/insert block.

# (a) What are the runtime types right now?
println("typeof(si_new)  = ", si_new  isa Any ? typeof(si_new)  : "undef")
println("typeof(key_new) = ", key_new isa Any ? typeof(key_new) : "undef")
println("typeof(val_new) = ", val_new isa Any ? typeof(val_new) : "undef")

# (b) Check if these are declared as concrete-typed globals or just ::Any
println("isconst(si_new)  binding? -- check with @which/methods below")

# (c) The real test: benchmark the *identical* call, but force si_new/key_new/val_new
# to be looked up through a function barrier instead of as bare globals in the
# @btime top-level expression. If this drops to 0 allocations while the original
# section-7b @btime still shows 3, that confirms global type-instability as the cause.
function _call_iop(store, si, key, val, fb_row)
    conj_insert_or_pop!(store, si, key, val, fb_row)
end

@btime _call_iop($lsm_store, si_new, key_new, val_new, $fb_row_iop) setup=(
    begin
        miss_ctr[] += 1
        n = miss_ctr[]
        global key_new = canonical_lp1_conj_key(100 + n, 200 + n, 300 + n, 400 + n)
        global si_new  = conj_shard_idx(key_new)
        global val_new = _conj_make_val(LP1ConjVal, _MISS_ROW, UInt32(n), UInt64(n), UInt64(n + 1))
    end
) evals=1



function _alloc_probe(store, si, key, val, fb_row)
    @allocated conj_insert_or_pop!(store, si, key, val, fb_row)
end

let n = (miss_ctr[] += 1)
    key_new = canonical_lp1_conj_key(100 + n, 200 + n, 300 + n, 400 + n)
    si_new  = conj_shard_idx(key_new)
    val_new = _conj_make_val(LP1ConjVal, _MISS_ROW, UInt32(n), UInt64(n), UInt64(n + 1))
    println("@allocated (function-barrier) conj_insert_or_pop! (miss/insert) = ",
            _alloc_probe(lsm_store, si_new, key_new, val_new, fb_row_iop))
end


# Diagnostic 3: get the raw @benchmark Trial object instead of @btime's summary,
# and inspect allocs per-sample directly, to see if the 3-alloc/80-byte figure
# is uniform across samples or a one-off (e.g. compilation-triggered).
# Paste in after the existing diagnostics.

trial = @benchmark conj_insert_or_pop!($lsm_store, si_new, key_new, val_new, $fb_row_iop) setup=(
    begin
        miss_ctr[] += 1
        n = miss_ctr[]
        key_new = canonical_lp1_conj_key(100 + n, 200 + n, 300 + n, 400 + n)
        si_new  = conj_shard_idx(key_new)
        val_new = _conj_make_val(LP1ConjVal, _MISS_ROW, UInt32(n), UInt64(n), UInt64(n + 1))
    end
) evals=1 samples=20

println("n samples run: ", length(trial.times))
println("allocs per sample (trial.memory is TOTAL across all samples): ", trial.memory)
println("allocs count field (total, not per-sample): ", trial.allocs)
println("per-sample memory if uniform: ", trial.memory / length(trial.times), " bytes")
println("per-sample allocs if uniform: ", trial.allocs / length(trial.times))
println()
println("Raw trial summary:")
show(stdout, MIME("text/plain"), trial)
println()


# Diagnostic 4: run conj_insert_or_pop! N times directly (no BenchmarkTools),
# each with a fresh key, timing and @allocated'ing EVERY call individually,
# to see whether allocation correlates with the slow-call tail seen in
# diagnostic 3's bimodal histogram (163ns cluster vs 4.4us tail).
# If some calls show >0 alloc and those are exactly the slow ones, that
# points at LSM flush/compact triggering both the latency spike and the
# allocation together -- not a benchmarking artifact at all, but a real,
# occasionally-triggered code path worth knowing about.

println()
println("== Per-call alloc/timing correlation (conj_insert_or_pop! miss/insert) ==")
for i in 1:30
    n = (miss_ctr[] += 1)
    key_i = canonical_lp1_conj_key(100 + n, 200 + n, 300 + n, 400 + n)
    si_i  = conj_shard_idx(key_i)
    val_i = _conj_make_val(LP1ConjVal, _MISS_ROW, UInt32(n), UInt64(n), UInt64(n + 1))
    t0 = time_ns()
    a  = @allocated conj_insert_or_pop!(lsm_store, si_i, key_i, val_i, fb_row_iop)
    t1 = time_ns()
    println("  call ", i, ": alloc=", a, " bytes  time=", (t1 - t0), " ns", a > 0 ? "  <-- ALLOCATED" : "")
end


# ---------------------------------------------------------------------------
# 8. Multithreaded shard-lock contention smoke test.
#
#    Threads.nthreads() reflects however Julia was launched (JULIA_NUM_THREADS
#    / -t). With 1 thread this just runs serially and is uninteresting but
#    harmless. Each thread hammers conj_insert! with keys it alone owns (no
#    cross-thread key collisions, so this isolates lock overhead itself from
#    same-col/collision logic) across a fixed spread of shards so both
#    same-shard and different-shard contention get exercised.
# ---------------------------------------------------------------------------
# conj_insert! wraps its entire body (including any triggered
# _lsm_flush_shard!/_lsm_compact! disk I/O) in lock(sc.file_lock) -- a single
# GLOBAL lock shared across all shards/threads, not a per-shard lock. With
# nthreads()==1 that's harmless (no contention, degenerates to serial). With
# nthreads()>1 every thread genuinely serializes on that one lock for the
# duration of each insert, so wall-clock cost scales with nthreads instead of
# being amortized by them -- this is a real bug in the library, not a harness
# artifact (see conj_insert_or_pop! next door, which already fixed this
# pattern for itself but conj_insert! still has it). Cap the workload hard so
# the smoke test can finish in bounded time regardless of thread count rather
# than silently running for minutes; this is deliberately small enough to
# still exercise both same-shard and cross-shard contention without being a
# real throughput benchmark.
const N_PER_THREAD = Threads.nthreads() > 1 ? 100 : 2_000

println()
println("== Multithreaded contention smoke test (nthreads=", Threads.nthreads(), ") ==")
println("  N_PER_THREAD=", N_PER_THREAD, (Threads.nthreads() > 1 ? " (capped: conj_insert! serializes on a global file_lock)" : ""))

function _mt_contention_test!(store::LP1ConjLSMStore{V}, base_offset::Int) where V
    tid = Threads.threadid()
    for i in 1:N_PER_THREAD
        u0 = base_offset + tid * 100_000 + i
        u1 = u0 + 1; v0 = u0 + 2; v1 = u0 + 3
        k  = canonical_lp1_conj_key(u0, u1, v0, v1)
        si = conj_shard_idx(k)
        v  = _conj_make_val(V, Dict(2 => 1), UInt32(i), UInt64(i), UInt64(i + 1))
        conj_insert!(store, si, k, v)
    end
    return nothing
end

elapsed = @elapsed Threads.@threads for _ in 1:max(Threads.nthreads(), 1)
    _mt_contention_test!(lsm_store, 1_000_000)
end
println("  ", Threads.nthreads(), " thread(s) x ", N_PER_THREAD,
        " inserts each in ", round(elapsed, digits=4), "s")
if Threads.nthreads() > 1 && elapsed > 5.0
    println("  WARNING: capped run still took >5s -- this is consistent with conj_insert!'s",
            " global sc.file_lock serializing every insert (see comment above N_PER_THREAD);",
            " not expected to be a harness issue.")
end

alloc_mt = @allocated begin
    Threads.@threads for _ in 1:max(Threads.nthreads(), 1)
        _mt_contention_test!(lsm_store, 2_000_000)
    end
end
println("  @allocated total across all threads = ", alloc_mt,
        "  (", round(alloc_mt / (Threads.nthreads() * N_PER_THREAD), digits=1),
        " bytes/insert avg — includes Task/closure overhead from @threads itself,")
println("   not just conj_insert!, so compare relatively across runs rather than",
        " against the single-thread @allocated figure above)")

# ---------------------------------------------------------------------------
# 9. Cleanup
# ---------------------------------------------------------------------------
lsm_close!(lsm_store)
rm(spill_dir; recursive = true, force = true)

println()
println("Done.")
