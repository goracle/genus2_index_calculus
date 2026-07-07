# =============================================================================
#  trial3_phase2.jl  --  Phase-2 walk worker and LP-closure helpers.
#
#  The phase-2 walk is the core of the index calculus: multiple threads run
#  independent Markov walks over the Jacobian, each step producing a φ-function
#  whose zero set intersects three curve points {P0, R, S}.  Depending on how
#  many of those points are in the factor base, each step falls into one of
#  four cases:
#
#    0-LP: all three in FB → emit full relation immediately.
#    1-LP: exactly one outside FB → store (or close against stored entry).
#    2-LP: exactly two outside FB → insert edge into LP2 spanning-tree graph.
#    3-LP: all three outside FB → discard.
#
#  The conjugate/extension case (φ residual is a non-split degree-2 point
#  over F_p²) is treated as a 1-LP or 2-LP step depending on whether P0 is
#  in the FB; the LP key is the full 4-tuple Mumford representation rather
#  than an affine coordinate pair.
#
#  Threading model:
#    - Shared state: shared_lp1 (affine 1-LP table), shared_lp2 (affine 2-LP
#      graph), shared_lp1_conj (sharded conj 1-LP table), shared_lp2_conj,
#      shared_lp_doubled (odd-cycle residuals), rel_counter (atomic).
#    - Per-thread: alpha_vec, beta_vec, rel_rows, all counters, scratch dicts.
#    - Locking: shared_lp1_lock guards shared_lp1 and shared_lp_doubled (they
#      are always updated together to prevent tearing).  shared_lp2_lock guards
#      shared_lp2.  shared_lp1_conj uses per-shard locks (N_CONJ_SHARDS = 64).
# =============================================================================

using Random
using StaticArrays: MVector
using TrialConfig
using PhiBiasTypes
using LP1ConjLSM
using LP1ConjDeepDiag

# ---------------------------------------------------------------------------
#  ShardedLP1Affine — sharded affine 1-LP table with per-shard locks.
#
#  Replaces the single Dict + single ReentrantLock for shared_lp1 and
#  shared_lp_doubled with N_LP1_SHARDS independent shard pairs, each
#  guarded by its own lock.  The shard index is determined by the lower
#  bits of the affine X-coordinate, which is highly uniform over F_p.
#
#  With N_LP1_SHARDS = 64 and 32 walk threads, contention per shard drops
#  by ~64x vs the single-lock design, virtually eliminating the spinlock
#  storm observed at thread counts above ~8.
#
#  INTERFACE:
#    lp1a_shard_idx(pt)           -> Int  (shard for point pt)
#    lp1a_lock!(s, si, f)         -> call f() under shard si's lock
#    lp1a_get(s, pt)              -> entry or nothing
#    lp1a_pop!(s, pt)             -> entry or nothing (removes)
#    lp1a_set!(s, pt, val)        -> store
#    lp1a_delete!(s, pt)          -> remove
#    lp1a_length(s)               -> total entries across all shards
#    lp1a_length_doubled(s)       -> total doubled entries
#    doubled_get(s, pt)           -> entry or nothing
#    doubled_pop!(s, pt)          -> entry or nothing (removes)
#    doubled_set!(s, pt, val)     -> store
#    doubled_delete!(s, pt)       -> remove
# ---------------------------------------------------------------------------
const N_LP1_SHARDS = 64   # power of 2 — enables bitmask shard selection

struct ShardedLP1Affine
    lp1_shards     ::Vector{Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}}}
    doubled_shards ::Vector{Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}}}
    locks          ::Vector{ReentrantLock}

    function ShardedLP1Affine()
        new(
            [Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}}() for _ in 1:N_LP1_SHARDS],
            [Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}}()      for _ in 1:N_LP1_SHARDS],
            [ReentrantLock() for _ in 1:N_LP1_SHARDS],
        )
    end
end

@inline function lp1a_shard_idx(pt::NTuple{2,Int})::Int
    # Lower 6 bits of the x-coordinate — uniformly distributed over F_p.
    (pt[1] & (N_LP1_SHARDS - 1)) + 1
end

@inline function lp1a_lock!(f::F, s::ShardedLP1Affine, si::Int) where F
    lock(s.locks[si]) do; f(); end
end

@inline function lp1a_get(s::ShardedLP1Affine, pt::NTuple{2,Int})
    si = lp1a_shard_idx(pt)
    get(s.lp1_shards[si], pt, nothing)
end

@inline function lp1a_pop!(s::ShardedLP1Affine, pt::NTuple{2,Int})
    si = lp1a_shard_idx(pt)
    pop!(s.lp1_shards[si], pt, nothing)
end

@inline function lp1a_set!(s::ShardedLP1Affine, pt::NTuple{2,Int}, val)
    si = lp1a_shard_idx(pt)
    s.lp1_shards[si][pt] = val
end

@inline function lp1a_delete!(s::ShardedLP1Affine, pt::NTuple{2,Int})
    si = lp1a_shard_idx(pt)
    delete!(s.lp1_shards[si], pt)
end

@inline function lp1a_haskey(s::ShardedLP1Affine, pt::NTuple{2,Int})::Bool
    si = lp1a_shard_idx(pt)
    haskey(s.lp1_shards[si], pt)
end

@inline function lp1a_length(s::ShardedLP1Affine)::Int
    sum(length(sh) for sh in s.lp1_shards)
end

@inline function doubled_get(s::ShardedLP1Affine, pt::NTuple{2,Int})
    si = lp1a_shard_idx(pt)
    get(s.doubled_shards[si], pt, nothing)
end

@inline function doubled_pop!(s::ShardedLP1Affine, pt::NTuple{2,Int})
    si = lp1a_shard_idx(pt)
    pop!(s.doubled_shards[si], pt, nothing)
end

@inline function doubled_set!(s::ShardedLP1Affine, pt::NTuple{2,Int}, val)
    si = lp1a_shard_idx(pt)
    s.doubled_shards[si][pt] = val
end

@inline function doubled_delete!(s::ShardedLP1Affine, pt::NTuple{2,Int})
    si = lp1a_shard_idx(pt)
    delete!(s.doubled_shards[si], pt)
end

@inline function doubled_haskey(s::ShardedLP1Affine, pt::NTuple{2,Int})::Bool
    si = lp1a_shard_idx(pt)
    haskey(s.doubled_shards[si], pt)
end

@inline function lp1a_length_doubled(s::ShardedLP1Affine)::Int
    sum(length(sh) for sh in s.doubled_shards)
end


# ---------------------------------------------------------------------------
#  try_lp1_doubled_cross_close!
#
#  Called under shared_lp1_lock.  Checks whether BOTH a standard 1-LP entry
#  and a "doubled" entry exist for the same point `pt`, and if so combines
#  them into a pure FB relation.
#
#  Invariants of the two stored entries:
#    shared_lp1[pt]      :  atom(pt) + row_1 = neg_al_1·G + neg_be_1·T
#    shared_lp_doubled[pt]:  2·atom(pt) + row_d = al_d·G + be_d·T
#
#  Taking 2×(lp1 entry) − (doubled entry) eliminates atom(pt):
#    (2·row_1 − row_d) = (2·neg_al_1 − al_d)·G + (2·neg_be_1 − be_d)·T
#
#  The doubled entry arises when an LP2 odd-cycle's root is an affine LP
#  point whose degree-2 coefficient has cancelled — the odd-cycle contributes
#  2·atom(root) to the divisor sum, so it pairs naturally with the standard
#  1-LP entry for that root.
#
#  Returns true if a relation was emitted.
# ---------------------------------------------------------------------------
# Shard-level inner implementation — called while ALREADY holding shard lock si.
# Takes the shard Dicts directly to avoid re-hashing the point.
@inline function _try_lp1_doubled_cross_close_inner!(
        pt             ::NTuple{2,Int},
        lp1_shard      ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        doubled_shard  ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        ell            ::BigInt,
        alpha_vec      ::Vector{BigInt},
        beta_vec       ::Vector{BigInt},
        rel_rows       ::Vector{Dict{Int,Int}},
        rank_growth    ::Vector{Tuple{Int,Int}},
        raw_steps      ::Int,
        rel_counter    ::Threads.Atomic{Int},
        ort            ::OnlineRankTracker,
        G              ::Div2,
        T              ::Div2,
        fb             ::Vector{NTuple{2,Int}})::Bool

    haskey(lp1_shard, pt)     || return false
    haskey(doubled_shard, pt) || return false

    row_1, neg_al_1, neg_be_1, _ = lp1_shard[pt]
    row_d, al_d,     be_d        = doubled_shard[pt]

    # Combine: result = 2*row_1 - row_d
    combined = copy(row_1)
    for (j, v) in combined; combined[j] = 2*v; end
    for (j, v) in row_d
        nv = get(combined, j, 0) - v
        nv == 0 ? delete!(combined, j) : (combined[j] = nv)
    end
    c_al = mod(2*neg_al_1 - al_d, Int(ell))
    c_be = mod(2*neg_be_1 - be_d, Int(ell))

    delete!(lp1_shard,     pt)
    delete!(doubled_shard, pt)

    (isempty(combined) || (c_al == 0 && c_be == 0)) && return false

    push!(alpha_vec, c_al); push!(beta_vec, c_be); push!(rel_rows, copy(combined))
    ort_add_row!(ort, combined)
    length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
        push!(rank_growth, (raw_steps, length(rel_rows)))
    Threads.atomic_add!(rel_counter, 1)
    return true
end

# ShardedLP1Affine overload — acquires the per-shard lock internally.
function try_lp1_doubled_cross_close!(
        pt             ::NTuple{2,Int},
        shared_lp1     ::ShardedLP1Affine,
        ell            ::BigInt,
        alpha_vec      ::Vector{BigInt},
        beta_vec       ::Vector{BigInt},
        rel_rows       ::Vector{Dict{Int,Int}},
        rank_growth    ::Vector{Tuple{Int,Int}},
        raw_steps      ::Int,
        rel_counter    ::Threads.Atomic{Int},
        ort            ::OnlineRankTracker,
        G              ::Div2,
        T              ::Div2,
        fb             ::Vector{NTuple{2,Int}})::Bool

    si = lp1a_shard_idx(pt)
    result = false
    lock(shared_lp1.locks[si]) do
        result = _try_lp1_doubled_cross_close_inner!(
            pt, shared_lp1.lp1_shards[si], shared_lp1.doubled_shards[si],
            ell, alpha_vec, beta_vec, rel_rows, rank_growth, raw_steps,
            rel_counter, ort, G, T, fb)
    end
    return result
end

# Legacy Dict overload — kept for callers that manage their own lock externally.
function try_lp1_doubled_cross_close!(
        pt             ::NTuple{2,Int},
        shared_lp1     ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        shared_lp_doubled::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        ell            ::BigInt,
        alpha_vec      ::Vector{BigInt},
        beta_vec       ::Vector{BigInt},
        rel_rows       ::Vector{Dict{Int,Int}},
        rank_growth    ::Vector{Tuple{Int,Int}},
        raw_steps      ::Int,
        rel_counter    ::Threads.Atomic{Int},
        ort            ::OnlineRankTracker,
        G              ::Div2,
        T              ::Div2,
    combined_scratch::ThreadScratchpad{<:Any},
        fb             ::Vector{NTuple{2,Int}})::Bool

    haskey(shared_lp1,      pt) || return false
    haskey(shared_lp_doubled, pt) || return false

    row_1, neg_al_1, neg_be_1, _ = shared_lp1[pt]
    row_d, al_d,     be_d        = shared_lp_doubled[pt]

    # Combine: result = 2·row_1 − row_d
    combined = copy(row_1)
    for (j, v) in combined; combined[j] = 2*v; end
    for (j, v) in row_d
        nv = get(combined, j, 0) - v
        nv == 0 ? delete!(combined, j) : (combined[j] = nv)
    end
    c_al = mod(2*neg_al_1 - al_d, Int(ell))
    c_be = mod(2*neg_be_1 - be_d, Int(ell))

    if ASSERT_RELATIONS
        D_sum = JacID
        for (idx, v) in combined
            D_fb = mumford1(fb[idx][1], fb[idx][2])
            D_v  = jac_mul_raw(D_fb, abs(v))
            D_sum = v > 0 ? jac_add(D_sum, D_v) : jac_sub(D_sum, D_v)
        end
        RHS    = jac_add(jac_mul(G, c_al, ell), jac_mul(T, c_be, ell))
        ok_pos = jac_isid(jac_sub(D_sum, RHS))
        ok_neg = jac_isid(jac_add(D_sum, RHS))
        if !(ok_pos || ok_neg)
            @printf("\n[!!!] LP-DOUBLED DIVISOR FAIL at pt=%s\n", pt)
            @printf("  Relation Check: Failed (Residual is NOT Identity)\n")
            @printf("  Divisor Sum (LHS): %s\n", string(D_sum))
            @printf("  Target (RHS):      %s\n", string(RHS))
            @printf("  Residual (LHS-RHS):%s\n", string(jac_sub(D_sum, RHS)))
            @printf("  Coefficients: al=%s, be=%s, weight=%d\n", string(c_al), string(c_be), length(combined))
            @printf("  row_1 (%d terms): %s\n", length(row_1), string(row_1))
            @printf("  row_d (%d terms): %s\n", length(row_d), string(row_d))
            fatal_assert(false, "try_lp1_doubled_cross_close!: principal divisor check failed")
        end
    end

    # Clean up both entries.
    delete!(shared_lp1,       pt)
    delete!(shared_lp_doubled, pt)

    (isempty(combined) || (c_al == 0 && c_be == 0)) && return false

    push!(alpha_vec, c_al); push!(beta_vec, c_be); push!(rel_rows, copy(combined))
    ort_add_row!(ort, combined)
    length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
        push!(rank_growth, (raw_steps, length(rel_rows)))
    Threads.atomic_add!(rel_counter, 1)
    return true
end

# ---------------------------------------------------------------------------
#  report_worker_progress — periodic per-thread status line
# ---------------------------------------------------------------------------
function report_worker_progress(tid, elapsed, s::WorkerStats, rel_counter, rel_target,
                                shared_lp1_conj::Union{ShardedLP1Conj{<:Any}, LP1ConjLSMStore{<:Any}})
    lp1_total = s.hits_lp1 + s.hits_lp1_conj
    @printf("[thread %2d | t=%6.1fs] raw=%d valid=%d 0lp=%d  1lp_aff(step=%d emit=%d) 1lp_conj(step=%d emit=%d)  2lp_seen=%d 2lp_emit=%d skip=%d  rels_local=%d  global=%d/%d\n",
            tid, elapsed, s.raw_steps, s.hits_total, s.hits_0lp,
            s.hits_lp1,      s.hits_1lp_emit,
            s.hits_lp1_conj, s.hits_1lp_conj_emit,
            s.hits_lp2seen, s.hits_lp2emit, s.hits_skip,
            s.rel_local, rel_counter[], rel_target)
    @printf("           rates: phi_val=%.3f%%  full=%.3f%%  1lp_aff=%.3f%%  1lp_conj=%.3f%%  2lp_seen=%.3f%%  2lp_emit=%.3f%%  skip=%.3f%%\n",
            100.0 * s.hits_total       / max(1, s.raw_steps),
            100.0 * s.hits_full        / max(1, s.hits_total),
            100.0 * s.hits_lp1         / max(1, s.hits_total),
            100.0 * s.hits_lp1_conj    / max(1, s.hits_total),
            100.0 * s.hits_lp2seen     / max(1, s.hits_total),
            100.0 * s.hits_lp2emit     / max(1, s.hits_total),
            100.0 * s.hits_skip        / max(1, s.hits_total))
    # phi_val above is hits_total/raw_steps and includes phase2_alpha_first_seen!
    # gate rejections (Bloom filter, monotonically fills over the run).
    # phi_build below is hits_total/phi_attempts — only counts steps that
    # actually reached build_phi_mumford!/step_phi_k!, i.e. the TRUE
    # phi-construction success rate. If phi_val declines over a run but
    # phi_build stays flat, the decline is the alpha-dedup gate, not phi
    # construction or jac_add. If phi_build itself declines, that points to
    # real corruption (see jac_add invariant-check counter in trial1).
    @printf("           phi_build (gates-cleared only) = %.3f%%  |  attempts=%d  |  gate-rejected=%d (%.3f%% of raw)\n",
            100.0 * s.hits_total / max(1, s.phi_attempts),
            s.phi_attempts,
            s.raw_steps - s.phi_attempts,
            100.0 * (s.raw_steps - s.phi_attempts) / max(1, s.raw_steps))
    @printf("           1lp_conj closure rate: %.3f%%  |  1lp_aff closure rate: %.3f%%  |  conj_cap_drops=%d\n",
            100.0 * s.hits_1lp_conj_emit / max(1, s.hits_lp1_conj),
            100.0 * s.hits_1lp_emit      / max(1, s.hits_lp1),
            s.evictions_conj)
    let total_conj_close = s.hits_1lp_conj_emit + s.hits_1lp_conj_trivial_same_col +
                            s.hits_1lp_conj_trivial_zero_dal + s.hits_1lp_conj_trivial_dup +
                            s.hits_1lp_conj_row_missing
        @printf("           1lp_conj trivial breakdown: same_col=%d (%.1f%%)  zero_dal=%d (%.1f%%)  dup=%d (%.1f%%)  row_missing=%d (%.1f%%)  useful=%d (%.1f%%) of %d closes\n",
                s.hits_1lp_conj_trivial_same_col,
                100.0 * s.hits_1lp_conj_trivial_same_col / max(1, total_conj_close),
                s.hits_1lp_conj_trivial_zero_dal,
                100.0 * s.hits_1lp_conj_trivial_zero_dal / max(1, total_conj_close),
                s.hits_1lp_conj_trivial_dup,
                100.0 * s.hits_1lp_conj_trivial_dup / max(1, total_conj_close),
                s.hits_1lp_conj_row_missing,
                100.0 * s.hits_1lp_conj_row_missing / max(1, total_conj_close),
                s.hits_1lp_conj_emit,
                100.0 * s.hits_1lp_conj_emit / max(1, total_conj_close),
                total_conj_close)
        if s.hits_1lp_conj_trivial_same_col > 0
            @printf("             same_col sub-breakdown: attractor_exact(Δα=0)=%d (%.1f%%)  birthday_filtered(Δα≠0)=%d (%.1f%%) of same_col probed=%d\n",
                    s.hits_1lp_conj_attractor_exact,
                    100.0 * s.hits_1lp_conj_attractor_exact   / max(1, s.hits_1lp_conj_attractor_exact + s.hits_1lp_conj_attractor_birthday),
                    s.hits_1lp_conj_attractor_birthday,
                    100.0 * s.hits_1lp_conj_attractor_birthday / max(1, s.hits_1lp_conj_attractor_exact + s.hits_1lp_conj_attractor_birthday),
                    s.hits_1lp_conj_attractor_exact + s.hits_1lp_conj_attractor_birthday)
        end
    end
    @printf("           smoothness histogram (0-LP, 1-LP, 2-LP, 3-LP): %d %d %d %d\n",
            s.smooth_hist[1], s.smooth_hist[2], s.smooth_hist[3], s.smooth_hist[4])
    # Print conj table occupancy once (from thread 2 only) to avoid redundant summation.
    # (Thread 1 is the coordinator and never enters the worker report path.)
    if tid == 2
        conj_total = conj_total_entries(shared_lp1_conj)
        @printf("           conj_table: %d entries (hot+disk)\n", conj_total)

        # Full LSM diagnostics — only when the conj store is an LP1ConjLSM.
        if shared_lp1_conj isa LP1ConjLSMStore
            # Emission rate for birthday estimator: LP1-conj closures per second.
            r_conj = s.hits_1lp_conj_emit / max(1.0, elapsed)
            lsm_flush_stats(shared_lp1_conj)
            lsm_mem_report(shared_lp1_conj;
                           label  = "thread $tid (LSM)",
                           peers  = false)
            lsm_bday_report(shared_lp1_conj, p, r_conj)
        end
    end
    # PHI-TIMING: series/gauss/residual split for step_phi_k! — see
    # trial3_phi_general.jl's PhiTimingStats. No-op unless PHI_TIMING_ENABLED[]
    # was flipped on (set it once before spawning workers, e.g. right after
    # init_scratch_caches!/scratch_by_k setup, and call init_phi_timing!()
    # with the run's actual thread count). Printed once (tid==2) same as the
    # conj-table occupancy line above, since this is a cross-thread aggregate,
    # not per-thread — the underlying PHI_TIMING vector already sums every
    # thread's slot in print_phi_timing_report.
    tid == 2 && PHI_TIMING_ENABLED[] && print_phi_timing_report(label = "t=$(round(elapsed, digits=1))s")
    # SYMBOLIC-REPORT: unlike PHI-TIMING above, run_symbolic_report! is NOT
    # called from here — it needs F_POLY_ASC and p, which are the
    # including driver's globals, not visible inside this file. Samples
    # accumulate in the background via record_symbolic_sample! (see the
    # hook at s.hits_total += 1 below); call
    # run_symbolic_report!(F_POLY_ASC, p) from the driver whenever you want
    # the report (e.g. after the walk finishes, or periodically from the
    # same place that calls this function, which does have F_POLY in scope).
    flush(stdout)
end

# ---------------------------------------------------------------------------
#  Helpers for the three LP cases inside phase2_worker.
#
#  These handle the shared-table bookkeeping so the main loop body stays
#  readable.  All of them run on the calling thread (no spawning).
#  Arguments that would need to be closed over from the outer scope are
#  passed explicitly so Julia's inference can see them.
# ---------------------------------------------------------------------------

# conj_insert_or_pop! for ShardedLP1Conj: same atomic semantics as the LSM
# version.  Returns (val, is_same_partial, prev_row) matching the LSM signature
# so handle_1lp_conj! can treat both backends uniformly.  prev_row is
# reconstructed from v.anchor_indices — never nothing for a real collision.
#
# Same-partial: (neg_al, neg_be) match the stored entry — genuine repeat,
# leave stored entry in place and discard the new arrival.
# Any other collision is a valid closure.
@inline function TrialConfig.conj_insert_or_pop!(sc::ShardedLP1Conj{V}, si::Int,
                                                   key::CanonicalLP1Key, val::V,
                                                   fb_row::Dict{Int,Int}) where V
    lock(sc.locks[si]) do
        sh   = sc.shards[si]
        slot = _conj_find(sh, key)
        if slot != 0
            v = @inbounds sh.vals[slot]
            if Int(v.neg_al) == Int(val.neg_al) &&
               _conj_prev_be(v) == _conj_prev_be(val)
                # Exact same partial (same α, same β): leave in place, discard.
                return (nothing, true, nothing)
            end
            # Different partial: valid closure.  Reconstruct row from anchor_indices.
            prev_row = _unpack_anchor_row(v.anchor_indices)
            _conj_delete_slot!(sh, slot)
            (v, false, prev_row)
        elseif sh.count < sh.max_entries
            _conj_insert!(sh, key, val)
            (nothing, false, nothing)
        else
            # At cap: drop silently.
            (nothing, false, nothing)
        end
    end
end

# --- 0-LP: all three atoms are in the factor base → emit immediately. ---
@inline function emit_0lp!(fb_row     ::Dict{Int,Int},
                           neg_al         ::Int,
                           neg_be         ::Int,
                           fb         ::Vector{NTuple{2,Int}},
                           G          ::Div2,
                           T          ::Div2,
                           alpha_vec  ::Vector{BigInt},
                           beta_vec   ::Vector{BigInt},
                           rel_rows   ::Vector{Dict{Int,Int}},
                           rel_counter::Threads.Atomic{Int},
                           ort        ::OnlineRankTracker,
                           s          ::WorkerStats,
                           rank_growth::Vector{Tuple{Int,Int}})
    if ASSERT_RELATIONS
        fatal_assert(
            check_relation_principal(fb_row, neg_al, neg_be, "α", fb, G, T; tag="0LP-EMIT"),
            "0LP-EMIT")
    end
    row_copy = copy(fb_row)
    push!(alpha_vec, neg_al); push!(beta_vec, neg_be); push!(rel_rows, row_copy)
    ort_add_row!(ort, row_copy)
    length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
        push!(rank_growth, (s.raw_steps, length(rel_rows)))
    s.hits_full += 1; s.hits_0lp += 1; s.rel_local += 1
    Threads.atomic_add!(rel_counter, 1)
end

# --- 1-LP (affine): one atom is not in the FB. ---
#
# Protocol:
#   1. Record diagnostics in lp_col.
#   2. Lock shared_lp1.
#   3a. If the LP is already stored: subtract rows and emit a full relation.
#   3b. If not stored: store this entry; then check for a doubled cross-close.
#   4. Unlock.
#   5. Return the next walk anchor.
#
# The next anchor after a closure is a random FB point (the walk has "used up"
# the current LP chain).  After a mere store it falls back to the non-LP atom
# with the highest FB membership (R > S > P0, in that priority).
@inline function handle_1lp_affine!(
        lp_pt          ::NTuple{2,Int},
        fb_row         ::Dict{Int,Int},
        al             ::Int,
        be             ::Int,
        neg_al         ::Int,
        neg_be         ::Int,
        ell            ::BigInt,
        fb             ::Vector{NTuple{2,Int}},
        nF_cur         ::Int,
        G              ::Div2,
        T              ::Div2,
        alpha_vec      ::Vector{BigInt},
        beta_vec       ::Vector{BigInt},
        rel_rows       ::Vector{Dict{Int,Int}},
        rel_counter    ::Threads.Atomic{Int},
        ort            ::OnlineRankTracker,
        s              ::WorkerStats,
        shared_lp1     ::ShardedLP1Affine,       # sharded — per-shard locking below
        shared_lp1_lock::Nothing,                 # unused sentinel (sharding handles locking)
        shared_lp_doubled::Nothing,               # unused sentinel (inside ShardedLP1Affine)
        lp_col         ::LPResidualCollector,
        rank_growth    ::Vector{Tuple{Int,Int}},
        combined_scratch::ThreadScratchpad{<:Any},
        iR             ::Int,
        iS             ::Int,
        R              ::NTuple{2,Int},
        S              ::NTuple{2,Int},
        P0             ::NTuple{2,Int},
        next_anchor_ref::Ref{Function};
        # --- diagnostic-only context, passed through to check_lp1_stored on
        #     failure so the bookkeeping cross-check has what it needs ---
        k_cur          ::Int = -1,
        anchors_diag   ::Union{Vector{NTuple{2,Int}}, Nothing} = nothing,
        i0_diag        ::Int = -1)::NTuple{2,Int}

    record_lp1!(lp_col, lp_pt, Int(al), Int(be), s.raw_steps)

    si = lp1a_shard_idx(lp_pt)
    closed = false
    lock(shared_lp1.locks[si])
    try
        prev_lp1 = pop!(shared_lp1.lp1_shards[si], lp_pt, nothing)
        if prev_lp1 !== nothing
            # --- Close against stored entry ---
            prev_row, prev_al, prev_be, prev_step = prev_lp1
            combined    = sparse_copy!(combined_scratch, fb_row)
            lp2_subtract_rows(combined, prev_row)
            ellI_loc    = Int(ell)
            combined_al = mod(neg_al - prev_al, ellI_loc)
            combined_be = mod(neg_be - prev_be, ellI_loc)
            record_closure!(lp_col, s.raw_steps, prev_step)

            if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                if ASSERT_RELATIONS
                    fatal_assert(
                        check_relation_principal(combined, combined_al, combined_be,
                                                 "α", fb, G, T; tag="1LP-CLOSE"),
                        "1LP-CLOSE")
                end
                row_copy = copy(combined)
                push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
                push!(rel_rows, row_copy)
                ort_add_row!(ort, row_copy)
                length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                    push!(rank_growth, (s.raw_steps, length(rel_rows)))
                s.hits_full += 1; s.hits_1lp_emit += 1; s.rel_local += 1
                Threads.atomic_add!(rel_counter, 1)
                closed = true
            end
        else
            # --- Store this entry ---
            if ASSERT_RELATIONS
                fatal_assert(
                    check_lp1_stored(lp_pt, fb_row, neg_al, neg_be, fb, G, T;
                                      tag="1LP-STORE", k_cur=k_cur, anchors=anchors_diag,
                                      i0=i0_diag, iR=iR, iS=iS, R=R, S=S, P0=P0),
                    "1LP-STORE")
            end
            # Skip (do not store) if the table is full.  Evicting a random
            # existing entry is counter-productive: it destroys an unmatched
            # entry before it can close, causes correlated re-generation of the
            # same keys, and produces duplicate relations.  A full table of
            # stable unmatched entries is strictly better — closures drain it
            # naturally.
            if lp1a_length(shared_lp1) >= MAX_LP1_ENTRIES
                # drop silently; doubled cross-close check is skipped too
            else
                shared_lp1.lp1_shards[si][lp_pt] = (copy(fb_row), neg_al, neg_be, s.raw_steps)
                # Check whether the complementary doubled entry already exists (same shard, same lock).
                if _try_lp1_doubled_cross_close_inner!(
                        lp_pt, shared_lp1.lp1_shards[si], shared_lp1.doubled_shards[si],
                        ell, alpha_vec, beta_vec, rel_rows, rank_growth, s.raw_steps,
                        rel_counter, ort, G, T, fb)
                    s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1; closed = true
                end
            end
        end
    finally
        unlock(shared_lp1.locks[si])
    end

    # Next anchor: advance the structured cursor (breaks attractor feedback).
    return next_anchor_ref[]()
end

# --- 1-LP conjugate: P0 is in FB; RS is a non-split Mumford pair. ---
#
# The LP key is the 4-tuple (c0, c1, v0, v1) of the Mumford u/v polynomials
# of the degree-2 residual.  We route to the correct shard, then either close
# against a stored entry (producing a relation between two FB columns with
# coefficients ±1) or store for future closure.
# --- 1-LP conjugate: P0 is in FB; RS is a non-split Mumford pair. ---
#
# The LP key is the 4-tuple (c0, c1, v0, v1) of the Mumford u/v polynomials
# of the degree-2 residual.  We route to the correct shard, then either close
# against a stored entry (producing a relation between two FB columns with
# coefficients ±1) or store for future closure.
# --- 1-LP conjugate: P0 is in FB; RS is a non-split Mumford pair. ---
#
# The LP key is the 4-tuple (c0, c1, v0, v1) of the Mumford u/v polynomials
# of the degree-2 residual.  We route to the correct shard, then either close
# against a stored entry (producing a relation between two FB columns with
# coefficients ±1) or store for future closure.
@inline function handle_1lp_conj!(
        lp_key          ::CanonicalLP1Key,
        i0              ::Int,
        fb_row          ::Dict{Int,Int},
        neg_al          ::Int,
        neg_be          ::Int,
        ell             ::BigInt,
        fb              ::Vector{NTuple{2,Int}},
        nF_cur          ::Int,
        G               ::Div2,
        T               ::Div2,
        alpha_vec       ::Vector{BigInt},
        beta_vec        ::Vector{BigInt},
        rel_rows        ::Vector{Dict{Int,Int}},
        rel_counter     ::Threads.Atomic{Int},
        ort             ::OnlineRankTracker,
        s               ::WorkerStats,
        shared_lp1_conj ::Union{ShardedLP1Conj{V}, LP1ConjLSMStore{V}},
        rank_growth     ::Vector{Tuple{Int,Int}},
        combined_scratch::ThreadScratchpad{<:Any},
        P0              ::NTuple{2,Int},
        phi_bias_stat   ::PhiBiasStat,
        next_anchor_ref ::Ref{Function},
        a_bucket        ::Int,
        deep_stat       ::ConjDeepStat,
        al_cur          ::Int = -1,
        px_anchor       ::Int = -1,
        a_raw           ::Int = -1,
        py_anchor       ::Int = -1,
        post_conj_stride::Int = 0,
        anchor_alpha_seen::Union{Dict{Tuple{Int,CanonicalLP1Key},Int}, Nothing} = nothing,
        anchor_alpha_cap::Int = 200_000,
        emitted_conj_rels::Union{Set{NTuple{4,Int}}, Nothing} = nothing,
        conj_dataset    ::Union{ConjClosureDataset, Nothing} = nothing,
        step_phase      ::Int = -1)::NTuple{2,Int} where V

    si = conj_shard_idx(lp_key)

    # Use atomic insert-or-pop to close the haskey/insert TOCTOU race.
    val = _conj_make_val(V, copy(fb_row), UInt32(s.raw_steps), UInt64(neg_al), UInt64(neg_be))
    prev, is_same_partial, _ = conj_insert_or_pop!(shared_lp1_conj, si, lp_key, val, fb_row)

    if is_same_partial
        s.hits_1lp_conj_trivial_same_col += 1
        if anchor_alpha_seen !== nothing
            akey = (i0, lp_key)
            if haskey(anchor_alpha_seen, akey)
                last_al = anchor_alpha_seen[akey]
                if last_al == neg_al
                    s.hits_1lp_conj_attractor_exact += 1
                else
                    s.hits_1lp_conj_attractor_birthday += 1
                end
            end
            if length(anchor_alpha_seen) < anchor_alpha_cap
                anchor_alpha_seen[akey] = neg_al
            end
        end
        record_conj_deep_miss!(deep_stat, lp_key, s.raw_steps, al_cur, px_anchor, a_raw, py_anchor)
        return next_anchor_ref[]()
    end

    if prev !== nothing
        # --- Close against shared global entry ---
        v = prev

        # Reconstruct the stored entry's FB row from anchor_indices packed in the val.
        # Works for both hot and disk hits — no side-channel or row store needed.
        prev_fb_row = _unpack_anchor_row(v.anchor_indices)
        # prev_col: representative single anchor index from the stored row
        # (used by diagnostics that expect a single Int; minimum key is stable)
        prev_col = isempty(prev_fb_row) ? 0 : minimum(keys(prev_fb_row))

        prev_al  = Int(v.neg_al)
        prev_be  = _conj_prev_be(v)

        if neg_al == 0 || prev_al == 0
            throw(ErrorException("CRITICAL PANIC: alpha accumulation hit zero boundary at tid=$(Threads.threadid())"))
        end

        # Unification: Use the stable affine tracking orientation to fix the sign flips
        combined_al = mod(neg_al - prev_al, Int(ell))
        combined_be = mod(neg_be - prev_be, Int(ell))

        if combined_al == 0 && combined_be == 0
            s.hits_1lp_conj_trivial_zero_dal += 1
            return next_anchor_ref[]()
        end

        # Construct the true sparse combined relation row
        cs = combined_scratch.combined_scratch
        sparse_copy!(cs, fb_row)
        lp2_subtract_rows(cs, prev_fb_row)

        # An empty combined row means the two closures carried identical FB support —
        # the anchor contributions cancelled exactly.  This is not a usable relation
        # (it would assert 0 = Δα·G with Δα≠0, contradicting ord(G)=ell).  Drop it.
        if isempty(cs)
            s.hits_1lp_conj_trivial_zero_dal += 1
            return next_anchor_ref[]()
        end

        if ASSERT_RELATIONS
            ok = check_relation_principal(cs, combined_al, combined_be, "α", fb, G, T; tag="RS-CONJ-CLOSE")
            if !ok
                D_sum = JacID
                for (idx, val_coeff) in cs
                    D_fb = mumford1(fb[idx][1], fb[idx][2])
                    D_sum = val_coeff > 0 ? jac_add(D_sum, jac_mul_raw(D_fb, abs(val_coeff))) : jac_sub(D_sum, jac_mul_raw(D_fb, abs(val_coeff)))
                end
                RHS = jac_add(jac_mul(G, combined_al, ell), jac_mul(T, combined_be, ell))
                
                @printf("\n============================================================\n")
                @printf("[!!!] HARD STOP: RS-CONJ-CLOSE CRITICAL MISMATCH\n")
                @printf("============================================================\n")
                @printf("  lp_key=%s\n", string(lp_key))
                @printf("  neg_al=%s, prev_al=%s -> combined_al=%s\n", string(neg_al), string(prev_al), string(combined_al))
                @printf("  Is Inverse Sign Match? %s\n", string(jac_isid(jac_add(D_sum, RHS))))
                @printf("  fb_row (current):     %s\n", string(sort(collect(fb_row))))
                @printf("  prev_fb_row (stored): %s\n", string(sort(collect(prev_fb_row))))
                @printf("  cs (combined):        %s\n", string(sort(collect(cs))))
                @printf("  row_w=%d  source=%s\n", sum(abs(v) for v in values(cs)),
                        "anchor_indices")
                @printf("  lp_key=%s\n", string(lp_key))
                @printf("============================================================\n\n")
                Base.flush(stdout)
                ccall(:exit, Cvoid, (Cint,), 1)
            end
        end


        # Bank the validated relation row
        push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
        push!(rel_rows, copy(cs))
        ort_add_row!(ort, cs)
        
        if length(rank_growth) < MAX_RANK_GROWTH_SAMPLES
            push!(rank_growth, (s.raw_steps, length(rel_rows)))
        end

        s.hits_full += 1; s.hits_1lp_conj_emit += 1; s.rel_local += 1
        Threads.atomic_add!(rel_counter, 1)

        # Unpack limbs for diagnostic logging
        lp_key_bits = UInt128(lp_key)
        u0_limb = Int(lp_key_bits % UInt32)
        u1_limb = Int((lp_key_bits >> 32) % UInt32)
        v0_limb = Int((lp_key_bits >> 64) % UInt32)
        v1_limb = Int((lp_key_bits >> 96) % UInt32)

        if conj_dataset !== nothing
            record_conj_closure!(conj_dataset,
                (u0_limb, u1_limb, v0_limb, v1_limb),
                i0, neg_al, neg_be, s.raw_steps,
                prev_col, prev_al, prev_be, Int(v.store_step),
                px_anchor, py_anchor, 
                combined_al, combined_be,
                al_cur, px_anchor, py_anchor, a_raw, a_bucket)
        end

        record_lp1_conj_hit!(phi_bias_stat, s.raw_steps, lp_key, a_bucket)
        record_conj_deep_step!(deep_stat, lp_key, a_bucket, s.raw_steps, true, al_cur, px_anchor,
                               Int(v.store_step), i0)
        record_d25_closure!(deep_stat, al_cur, px_anchor, Int(v.neg_al),
                            s.raw_steps - Int(v.store_step), Int(ell))
        
        record_d37_closure!(deep_stat, px_anchor, u0_limb, al_cur, s.raw_steps)
        record_d39_closure!(deep_stat, neg_al, px_anchor, combined_al, step_phase)
        record_d16_emission!(deep_stat, lp_key, s.raw_steps, i0)
        record_d20_emission!(deep_stat)
        record_d19_closure!(deep_stat, i0, prev_col, combined_al, combined_be)
        
        if prev_col >= 1
            record_d35_closure!(deep_stat, combined_al, combined_be,
                                fb[i0][1], fb[i0][2], fb[prev_col][1], fb[prev_col][2])
            record_d30_closure!(deep_stat, fb[i0][1], fb[prev_col][1])
        end
        
        record_d36_closure!(deep_stat, i0, prev_col)
        record_d22_d23_d24_emission!(deep_stat, s.raw_steps, _deep_bucket(lp_key), a_bucket)
        
        for _ in 1:post_conj_stride
            next_anchor_ref[]()
        end
        return next_anchor_ref[]()
    end

    # --- STORE BRANCH ---
    # The val already carries anchor_indices packed by _conj_make_val above;
    # no separate row store entry is needed.

    return next_anchor_ref[]()
end


# --- 2-LP conjugate: P0 is not in FB; RS is a non-split Mumford pair. ---
#
# Insert an edge (P0, lp_key) into the extension-field LP2 graph.  The graph
# mixes affine-point nodes (NTuple{2,Int}) and Mumford-pair nodes (NTuple{4,Int}).
# An even cycle in this mixed graph yields a pure FB relation; an odd cycle
# produces a doubled residual that may cross-close with a stored 1-LP entry.

# --- 2-LP affine: exactly two atoms are outside the FB. ---
#
# Protocol:
#   1. Identify lp2_a and lp2_b (the two non-FB atoms).
#   2. Record diagnostics.
#   3. Insert edge into the affine LP2 spanning-tree graph (under lp2_lock).
#   4. If an even cycle is found, emit the full relation.
#      If an odd cycle is found, attempt a doubled cross-close.
#   5. Under lp1_lock, attempt a cross-close: if one of the two LP atoms
#      already has a stored 1-LP entry, combine the new fb_row with that
#      stored row to produce an effective 1-LP entry for the other LP atom.
#      If the other LP atom also has a stored entry, that gives a full relation.
#
# Note on lp2_a / lp2_b assignment:
#   n_lp == 2 means exactly two of (i0, iR, iS) are zero.
#   Case table (zero means "not in FB"):
#     i0==0, iR==0, iS!=0 → a=P0, b=R
#     i0==0, iS==0, iR!=0 → a=P0, b=S
#     iR==0, iS==0, i0!=0 → a=R,  b=S
# ---------------------------------------------------------------------------
@inline function handle_2lp_affine!(
        i0             ::Int,
        iR             ::Int,
        iS             ::Int,
        R              ::NTuple{2,Int},
        S              ::NTuple{2,Int},
        P0             ::NTuple{2,Int},
        fb_row_scratch ::Dict{Int,Int},
        neg_al         ::Int,
        neg_be         ::Int,
        ell            ::Integer,
        fb             ::Vector{NTuple{2,Int}},
        nF_cur         ::Int,
        G              ::Div2,
        T              ::Div2,
        alpha_vec      ::Vector{BigInt},
        beta_vec       ::Vector{BigInt},
        rel_rows       ::Vector{Dict{Int,Int}},
        rel_counter    ::Threads.Atomic{Int},
        ort            ::OnlineRankTracker,
        s              ::WorkerStats,
        shared_lp1     ::ShardedLP1Affine,
        shared_lp1_lock::Nothing,                 # unused — sharding handles locking
        shared_lp2     ::LP2Graph,
        shared_lp2_lock::ReentrantLock,
        shared_lp_doubled::Nothing,               # unused — inside ShardedLP1Affine
        lp_col         ::LPResidualCollector,
        max_lp2_nodes  ::Int,
        rank_growth    ::Vector{Tuple{Int,Int}},
        combined_scratch::ThreadScratchpad{<:Any},
        next_anchor_ref::Ref{Function})::NTuple{2,Int}

    s.hits_lp2seen += 1

    # Identify the two non-FB atoms.
    lp2_a, lp2_b = if i0 == 0 && iR == 0; P0, R
                   elseif i0 == 0 && iS == 0; P0, S
                   else; R, S   # iR==0 && iS==0
                   end

    record_lp2!(lp_col, lp2_a, lp2_b, s.raw_steps)

    # --- LP2 graph insertion ---
    if lp2_graph_node_count(shared_lp2) >= max_lp2_nodes
        s.hits_lp2_cap += 1
        # Fall through to the cross-close check below even when capped.
    else
        emitted_rel = nothing
        lock(shared_lp2_lock)
        try
            if lp2_graph_node_count(shared_lp2) < max_lp2_nodes
                emitted_rel = lp2_insert_edge!(shared_lp2, lp2_a, lp2_b,
                                               fb_row_scratch, neg_al, neg_be, ell)
            else
                s.hits_lp2_cap += 1
            end
        finally
            unlock(shared_lp2_lock)
        end

        if emitted_rel !== nothing && emitted_rel.type === :even_cycle
            push!(alpha_vec, emitted_rel.alpha); push!(beta_vec, emitted_rel.beta)
            push!(rel_rows, emitted_rel.row)
            ort_add_row!(ort, emitted_rel.row)
            length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                push!(rank_growth, (s.raw_steps, length(rel_rows)))
            s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
            Threads.atomic_add!(rel_counter, 1)

            if ASSERT_RELATIONS
                let row = emitted_rel.row, α = emitted_rel.alpha, β = emitted_rel.beta
                    D_sum = JacID
                    for (idx, v) in row
                        pt   = fb[idx]
                        D_fb = mumford1(pt[1], pt[2])
                        Dv   = jac_mul_raw(D_fb, abs(v))
                        D_sum = v > 0 ? jac_add(D_sum, Dv) : jac_sub(D_sum, Dv)
                    end
                    RHS = jac_add(jac_mul(G, α, ell), jac_mul(T, β, ell))
                    if !(jac_isid(jac_sub(D_sum, RHS)) || jac_isid(jac_add(D_sum, RHS)))
                        @printf("[LP2-DIAG tid=%d] FAIL  alpha=%s beta=%s  row_weight=%d  root_signs=(%d,%d)  depths=(%d,%d)\n",
                                Threads.threadid(), string(α), string(β), length(row),
                                emitted_rel.root_signs[1], emitted_rel.root_signs[2],
                                emitted_rel.depths[1], emitted_rel.depths[2])
                        @printf("  lp2_a=%s  lp2_b=%s  i0=%d iR=%d iS=%d\n",
                                string(lp2_a), string(lp2_b), i0, iR, iS)
                        @printf("  row = %s\n", string(row))
                        lock(shared_lp2_lock)
                        try; clear_lp2_graph!(shared_lp2); finally; unlock(shared_lp2_lock); end
                        error("Relation validation failed during 2-LP even cycle closure.")
                    end
                end
            end
            return next_anchor_ref[]()

        elseif emitted_rel !== nothing && emitted_rel.type === :odd_cycle
            s.hits_lp2_odd += 1
            si_root = lp1a_shard_idx(root)
            lock(shared_lp1.locks[si_root])
            try
                root = emitted_rel.root
                prev_doubled = doubled_pop!(shared_lp1, root)
                if prev_doubled !== nothing
                    prev_row, prev_al, prev_be = prev_doubled
                    combined    = sparse_copy!(combined_scratch, emitted_rel.row)
                    for (j, v) in prev_row
                        nv = get(combined, j, 0) - v
                        nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                    end
                    combined_al = mod(emitted_rel.alpha - prev_al, ell)
                    combined_be = mod(emitted_rel.beta  - prev_be, ell)
                    if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                        push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
                        push!(rel_rows, copy(combined))
                        ort_add_row!(ort, combined)
                        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                            push!(rank_growth, (s.raw_steps, length(rel_rows)))
                        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        Threads.atomic_add!(rel_counter, 1)
                    end
                else
                    if lp1a_length_doubled(shared_lp1) <= MAX_LP1_DOUBLED_ENTRIES
                        doubled_set!(shared_lp1, root, (emitted_rel.row, Int(emitted_rel.alpha), Int(emitted_rel.beta)))
                        if _try_lp1_doubled_cross_close_inner!(
                                root, shared_lp1.lp1_shards[si_root], shared_lp1.doubled_shards[si_root],
                                ell, alpha_vec, beta_vec, rel_rows, rank_growth, s.raw_steps,
                                rel_counter, ort, G, T, fb)
                            s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        end
                    end
                end
            finally
                unlock(shared_lp1.locks[lp1a_shard_idx(root)])
            end
        end
    end   # end LP2 graph insertion block

    # --- Cross-close with existing 1-LP entries ---
    # Acquire shard locks for both LP atoms (in canonical order to prevent deadlock).
    si_a = lp1a_shard_idx(lp2_a); si_b = lp1a_shard_idx(lp2_b)
    si_lo, si_hi = minmax(si_a, si_b)
    lock(shared_lp1.locks[si_lo])
    si_lo != si_hi && lock(shared_lp1.locks[si_hi])
    try
        for (lp_known, lp_other) in ((lp2_a, lp2_b), (lp2_b, lp2_a))
            si_known = lp1a_shard_idx(lp_known)
            if haskey(shared_lp1.lp1_shards[si_known], lp_known)
                r_known, na_known, nb_known, _step_known = shared_lp1.lp1_shards[si_known][lp_known]
                new_row    = copy(fb_row_scratch)
                for (j, v) in r_known
                    nv = get(new_row, j, 0) - v
                    nv == 0 ? delete!(new_row, j) : (new_row[j] = nv)
                end
                ellI_loc   = Int(ell)
                new_neg_al = mod(neg_al - na_known, ellI_loc)
                new_neg_be = mod(neg_be - nb_known, ellI_loc)

                s.hits_lp2_cross += 1

                si_other = lp1a_shard_idx(lp_other)
                prev_other = pop!(shared_lp1.lp1_shards[si_other], lp_other, nothing)
                if prev_other !== nothing
                    prev_row, prev_al, prev_be, prev_step = prev_other
                    combined    = copy(new_row)
                    lp2_subtract_rows(combined, prev_row)
                    combined_al = mod(new_neg_al - prev_al, ellI_loc)
                    combined_be = mod(new_neg_be - prev_be, ellI_loc)
                    record_closure!(lp_col, s.raw_steps, prev_step)
                    if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                        if ASSERT_RELATIONS
                            fatal_assert(
                                check_relation_principal(combined, combined_al, combined_be,
                                                         "α", fb, G, T; tag="2LP-CROSS-CLOSE"),
                                "2LP-CROSS-CLOSE")
                        end
                        push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
                        push!(rel_rows, combined)
                        ort_add_row!(ort, combined)
                        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                            push!(rank_growth, (s.raw_steps, length(rel_rows)))
                        s.hits_full += 1; s.hits_1lp_emit += 1; s.rel_local += 1
                        Threads.atomic_add!(rel_counter, 1)
                    end
                else
                    if ASSERT_RELATIONS
                        ok = check_lp1_stored(lp_other, new_row, new_neg_al, new_neg_be,
                                              fb, G, T; tag="2LP-CROSS-STORE")
                        if !ok
                            @printf("[2LP-CROSS-STORE DIAG tid=%d] lp_known=%s  lp_other=%s\n",
                                    Threads.threadid(), string(lp_known), string(lp_other))
                            @printf("[2LP-CROSS-STORE DIAG]  r_known=%s  na=%d  nb=%d\n",
                                    string(r_known), na_known, nb_known)
                            @printf("[2LP-CROSS-STORE DIAG]  fb_row=%s  new_row=%s  neg_al=%d neg_be=%d\n",
                                    string(fb_row_scratch), string(new_row), neg_al, neg_be)
                        end
                        fatal_assert(ok, "2-LP cross-store: derived 1-LP row inconsistent")
                    end
                    if lp1a_length(shared_lp1) >= MAX_LP1_ENTRIES
                        # drop — no eviction (see handle_1lp_affine! reasoning)
                    else
                        shared_lp1.lp1_shards[si_other][lp_other] = (new_row, new_neg_al, new_neg_be, s.raw_steps)
                        if _try_lp1_doubled_cross_close_inner!(
                                lp_other, shared_lp1.lp1_shards[si_other], shared_lp1.doubled_shards[si_other],
                                ell, alpha_vec, beta_vec, rel_rows, rank_growth, s.raw_steps,
                                rel_counter, ort, G, T, fb)
                            s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        end
                    end
                end
            end  # if haskey(shared_lp1, lp_known)
            break   # only act on the first match
        end
    finally
        si_lo != si_hi && unlock(shared_lp1.locks[si_hi])
        unlock(shared_lp1.locks[si_lo])
    end

    if i0 != 0;  return P0
    elseif iR != 0; return R
    elseif iS != 0; return S
    else; return next_anchor_ref[]()
    end
end

# ---------------------------------------------------------------------------
#  phase2_worker
#
#  One independent walk thread.  Runs until rel_counter reaches rel_target
#  or raw_steps reaches step_cap, then returns all locally collected
#  relations and per-thread counters.
#
#  Read-only shared inputs (no locking needed):
#    fb, pt2idx  — frozen factor base from phase 1
#    step_D, step_a, step_b — precomputed walk steps
#    rel_target, step_cap, enable_lp2_conj, max_lp2_nodes, max_lp2_conj_nodes
#
#  Write-shared (locking required):
#    shared_lp1 + shared_lp_doubled → shared_lp1_lock
#    shared_lp2                     → shared_lp2_lock
#    shared_lp1_conj                → per-shard locks inside ShardedLP1Conj
#    shared_lp2_conj                → shared_lp2_conj_lock
#    rel_counter                    → atomic increment only
#
#  Per-thread (no locking):
#    alpha_vec, beta_vec, rel_rows, all WorkerStats fields, scratch dicts
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  Global alpha no-repeat filter — EXACT one-bit-per-alpha bitset, with a
#  properly-sized Bloom fallback for pathologically large ellI.
#
#  HISTORY / WHY THIS CHANGED:
#  This used to be a fixed 128 MB / 3-hash Bloom filter, sized under the
#  assumption of ~150M total walk steps against ell≈4.88e9 (FP rate ~1e-8
#  per query at that scale). Real runs now do orders of magnitude more raw
#  steps (billions per thread, tens of billions aggregate, over many hours).
#  Bloom bits are set-only — never cleared — so the filter saturates well
#  before the walk finishes: once total insertions approach the bit count,
#  per-query false-positive rate climbs toward 100%. Past that point the
#  gate isn't "skip a duplicate" anymore, it's "reject alphas that were
#  never actually seen" — which is exactly the runaway gate-rejected%
#  (97%+, still climbing) seen in long runs, and it hits hardest right when
#  a run is closing in on rel_target and needs the last few genuinely novel
#  alphas most.
#
#  FIX: ellI is known exactly before any worker starts and is bounded (order
#  1e9-1e10 for problems we actually run), so default to an EXACT
#  one-bit-per-alpha array — zero false positives, ever, independent of run
#  length or step count. Cost: ellI/8 bytes (~610 MB @ ellI≈4.88e9 — 8x
#  cheaper than the original Vector{UInt8}-per-alpha approach, and unlike
#  the Bloom filter, correctness doesn't decay as the run gets longer). Only
#  falls back to a Bloom filter — sized from the ACTUAL run's ellI/step_cap,
#  not a fixed constant — if the exact bitset would exceed a memory budget.
#
#  The gate is still lockless: bits are only ever set, never cleared, so
#  racy concurrent writes are benign (two threads both believe they're
#  "first" for the same alpha and both process it once).
#
#  Resetting between runs: call phase2_alpha_gate_reset!(gate) before each
#  walk phase that must start with a clean gate (e.g. the amortized
#  pre-run in trial3_fixed.jl).
# ---------------------------------------------------------------------------
const ALPHA_EXACT_MAX_BYTES = 2_000_000_000   # 2 GB ceiling before falling back to Bloom

struct AlphaGate
    words ::Vector{UInt64}
    exact ::Bool   # true: words indexed directly by alpha, no hashing, no FPs
    nbits ::Int    # ellI for exact mode; Bloom bit count otherwise
    nhash ::Int    # unused when exact=true
end

# Construct once per run (or per amortized sub-run), BEFORE spawning workers,
# and share the single instance across all threads — mirrors how
# PHASE2_ALPHA_BLOOM used to be a single shared global.
#
# `step_cap_total` is passed through to the Bloom fallback ONLY as a coarse
# upper bound on n_expected — it is NOT a reliable estimate of how many
# alphas will actually be inserted. step_cap is a pessimistic safety-valve
# ("never run forever"), derived as rel_target / prob_per_step; when the
# factor base is small relative to p (e.g. an amortized β=0 precompute pass
# with FB≈50 against p≈4e7), prob_per_step is tiny and step_cap balloons to
# absurd values (tens of billions) that the walk will never actually reach.
# Sizing Bloom memory directly off that number tries to allocate hundreds of
# GB and OOMs before the walk even starts — this bit us in practice.
#
# So: for the Bloom fallback, memory is capped to `bloom_max_bytes` FIRST
# (hard ceiling, independent of step_cap_total), and we report whatever
# false-positive rate that budget actually buys given n_expected, rather
# than solving for a fixed target_fp and letting the allocation size run
# away. This can never OOM regardless of how large ellI or step_cap get —
# worst case is a high (but bounded, logged) false-positive rate, which is
# the same "performance hint, not correctness gate" tradeoff the original
# Bloom filter always had, now just made explicit instead of silently
# assumed to be negligible.
function phase2_alpha_gate_init!(ellI::Int, step_cap_total::Int;
                                  target_fp::Float64 = 1e-6,
                                  bloom_max_bytes::Int = ALPHA_EXACT_MAX_BYTES)::AlphaGate
    exact_bytes = cld(ellI, 8)
    if exact_bytes <= ALPHA_EXACT_MAX_BYTES
        gate = AlphaGate(zeros(UInt64, cld(ellI, 64)), true, ellI, 0)
        @printf("[alpha-gate] exact bitset: ellI=%d (%.1f MB), zero false positives\n",
                ellI, exact_bytes / 1e6)
        return gate
    end

    # n_expected is a rough ceiling, not a forecast: step_cap_total can be a
    # wild overestimate (see note above), so it only ever pushes m_bits DOWN
    # relative to what we'd want (bloom_max_bytes still wins if smaller) —
    # it never pushes the allocation up past the memory budget.
    n_expected     = min(ellI, step_cap_total)
    m_bits_wanted  = ceil(Int, -n_expected * log(target_fp) / (log(2)^2))
    m_bits_budget  = bloom_max_bytes * 8
    m_bits         = min(m_bits_wanted, m_bits_budget)
    memory_bound   = m_bits == m_bits_budget && m_bits_wanted > m_bits_budget

    # Optimal-k formula (m/n)·ln2 only makes sense when m/n is reasonably
    # large; when we're memory-bound and m << n_expected, more hashes just
    # means more chances to collide with an already-set bit, so clamp hard.
    k_hash = clamp(round(Int, (m_bits / max(1, n_expected)) * log(2)), 1, 30)

    achieved_fp = (1.0 - exp(-k_hash * n_expected / max(1.0, m_bits)))^k_hash

    if memory_bound
        @printf("[alpha-gate] ellI=%d too large for exact bitset (%.1f GB); Bloom is MEMORY-BOUND at %.1f MB budget (wanted %.1f MB for target_fp=%.1e off n_expected=%d, which is a loose step_cap-derived ceiling, not a real forecast)\n",
                ellI, exact_bytes / 1e9, bloom_max_bytes / 1e6, m_bits_wanted / 8 / 1e6, target_fp, n_expected)
        @printf("[alpha-gate]   k=%d hashes, achieved_fp≈%.3e AT n_expected — actual fp will be far lower if the walk finishes in far fewer than %d steps (likely, since step_cap is a pessimistic ceiling)\n",
                k_hash, achieved_fp, n_expected)
    else
        @printf("[alpha-gate] ellI=%d too large for exact bitset (%.1f GB); sized Bloom: %.1f MB, k=%d hashes, target_fp=%.1e, n_expected=%d\n",
                ellI, exact_bytes / 1e9, m_bits / 8 / 1e6, k_hash, target_fp, n_expected)
    end
    return AlphaGate(zeros(UInt64, cld(m_bits, 64)), false, m_bits, k_hash)
end

function phase2_alpha_gate_reset!(gate::AlphaGate)
    fill!(gate.words, UInt64(0))
    nothing
end

@inline function phase2_alpha_first_seen!(gate::AlphaGate, alpha::Int)::Bool
    if gate.exact
        # Direct index — no hashing, no collisions, no false positives ever.
        @inbounds begin
            w = alpha >> 6; r = alpha & 63
            bit = UInt64(1) << r
            (gate.words[w+1] & bit) != 0 && return false
            gate.words[w+1] |= bit
        end
        return true
    end

    # Bloom fallback path (only reached when ellI exceeds ALPHA_EXACT_MAX_BYTES
    # in bit-per-alpha terms). Double hashing (Kirsch-Mitzenmacher) over
    # gate.nhash slots derived at construction time from the real run size,
    # instead of a hardcoded 3-hash / 128 MB constant.
    h    = UInt64(alpha) * 0x9e3779b97f4a7c15
    step = UInt64(alpha) * 0x6c62272e07bb0142
    already = true
    @inbounds for j in 0:gate.nhash-1
        b = Int((h + j*step) % UInt64(gate.nbits))
        w = b >> 6; r = b & 63
        if (gate.words[w+1] >> r) & UInt64(1) == 0
            already = false
            break
        end
    end
    already && return false
    @inbounds for j in 0:gate.nhash-1
        b = Int((h + j*step) % UInt64(gate.nbits))
        w = b >> 6; r = b & 63
        gate.words[w+1] |= UInt64(1) << r
    end
    return true
end


# Top-level struct for the importance-sampling reservoir (must be at module scope).
function phase2_worker(G               ::Div2,
                       T               ::Div2,
                       fb              ::Vector{NTuple{2,Int}},
                       ell             ::BigInt,  # <--- Add this here
                       pt2idx          ::Dict{NTuple{2,Int},Int},
                       step_D          ::Vector{Div2},
                       step_a          ::Vector{BigInt},
                       step_b          ::Vector{BigInt},
                       rel_counter     ::Threads.Atomic{Int},
                       rel_target      ::Int,
                       step_cap        ::Int,
                       shared_lp1      ::ShardedLP1Affine,   # sharded; lock-per-shard
                       shared_lp1_lock ::Nothing,            # unused sentinel
                       shared_lp2      ::LP2Graph,
                       shared_lp2_lock ::ReentrantLock,
                       shared_lp_doubled::Nothing,           # unused sentinel; inside ShardedLP1Affine
                       shared_lp1_conj ::Union{ShardedLP1Conj{<:Any}, LP1ConjLSMStore{<:Any}},
                       shared_lp2_conj ::LP2ConjGraph,
                       shared_lp2_conj_lock::ReentrantLock,
                       enable_lp2      ::Bool,
                       enable_lp2_conj ::Bool,
                       max_lp2_nodes   ::Int,
                       max_lp2_conj_nodes::Int,
                       lp_col          ::LPResidualCollector,
                       ort             ::OnlineRankTracker,
                       phi_bias_stat   ::PhiBiasStat,
                       deep_stat       ::ConjDeepStat,
                       n_workers       ::Int = Threads.nthreads();
                       verbose         ::Bool = true,
                       beta_zero       ::Bool = false,
                       amortized_precompute::Bool = false,
                       enable_lp1_aff  ::Bool = true,
                       post_conj_stride::Int  = 0,
                       anchor_tuple_size::Int = 1,
                       carry_in_deep_stat::Union{ConjDeepStat,Nothing} = nothing,
                       conj_dataset      ::Union{ConjClosureDataset,Nothing} = nothing,
                       d38_stat          ::Union{D38Stat,Nothing} = nothing,
                       # Shared alpha no-repeat gate (see phase2_alpha_gate_init!
                       # above). Must be constructed ONCE before spawning workers
                       # and passed the same instance to every thread — it is the
                       # replacement for the old module-level PHASE2_ALPHA_BLOOM
                       # global. Kept `nothing`-defaultable only so any stray old
                       # call site fails loudly instead of silently reusing a
                       # stale global; a real run must always pass one in.
                       alpha_gate        ::Union{AlphaGate,Nothing} = nothing,
                       anchor_tuple_weight_decay::Float64 = 2.0,
                       # Anchor-sweep base-tuple collector (see
                       # trial3_anchor_sweep_diag.jl). nothing = disabled (default,
                       # zero cost: the capture call site below is a single nothing
                       # check). When set, every thread races to fill it with real
                       # (cur_anchors, u0,u1,v0,v1) states pulled from its own live
                       # walk the moment k_cur == anchor_tuple_size — no synthetic
                       # base tuples, exactly what the diagnostic's docstring asks
                       # for. Same instance must be shared across all threads.
                       sweep_collector   ::Union{SweepCollector,Nothing} = nothing,
                       # F_p arithmetic backend — StandardArith(p) (default) is
                       # bit-identical to the old hardcoded fpmul/fpinv path.
                       # Pass MontgomeryArith(p) to switch the k>=2 general-φ hot
                       # path (build_phi_general!, fp_gauss!, the x^i mod u(x)
                       # cache) over to REDC multiplication. Must be the SAME
                       # instance used to build scratch_by_k's small_inv table
                       # below — see init_scratch_caches! in
                       # trial3_phi_general.jl and the KNOWN LIMITATION note in
                       # trial3_fp_backend.jl. Caller should have already run
                       # validate_backend(backend) once before spawning workers.
                       backend           ::FpArith = StandardArith(p))

    nF_cur   = length(fb)
    N_STEPS  = length(step_D)
    tid      = Threads.threadid()
    t_start  = time()

    ellI = Int(ell)
    alpha_gate === nothing && error("phase2_worker: alpha_gate must be constructed once " *
        "via phase2_alpha_gate_init!(ellI, step_cap_total) and passed in by the caller " *
        "before spawning workers — see trial3_fixed.jl.")
    step_a_i = Vector{Int}(undef, length(step_a))
    step_b_i = Vector{Int}(undef, length(step_b))
    @inbounds for i in eachindex(step_a)
        step_a_i[i] = Int(step_a[i])
        step_b_i[i] = Int(step_b[i])
    end

    # ==========================================================================
    #  Anchor tuple cursor — the TUPLE SPACE is sliced across threads, not the
    #  factor base.  Each thread owns an exclusive contiguous chunk of the
    #  GLOBAL lexicographic index space of k-multisets drawn from the FULL
    #  factor base fb[1..nF_cur] — independently for every tuple length
    #  k = 1..K_ceil.
    #
    #  WHY THE CHANGE: the old scheme partitioned fb[] itself into contiguous
    #  FB-index slices [anchor_start, anchor_end] and only ever formed
    #  k-tuples out of entries drawn from a single thread's own slice. That
    #  is exactly right for k=1 (a 1-tuple IS a single FB index, so slicing
    #  the FB and slicing the tuple space are the same partition), but for
    #  k>=2 it is far too restrictive: the true k-tuple space is every
    #  non-decreasing k-multiset over the WHOLE factor base — size
    #  C(nF_cur+k-1, k) — while FB-slicing only let a thread draw entries
    #  from within its own ~nF_cur/n_workers-sized slice, a subspace of size
    #  C(slice_size+k-1, k). With n_workers=32 that subspace shrinks by
    #  roughly 32^(k-1) relative to the true tuple space, so almost the
    #  entire k>=2 combinatorial space was never visited by any thread.
    #
    #  NEW SCHEME: for each k, compute Nk = multichoose(nF_cur, k) =
    #  C(nF_cur+k-1, k) — the exact count of non-decreasing k-tuples over the
    #  full FB — partition [0, Nk-1] into n_workers balanced contiguous
    #  chunks using the SAME floor(Nk/n_workers)-or-+1 balancing as before,
    #  and give thread `tid` its chunk [start_idx_k, end_idx_k]. The chunk's
    #  starting tuple is obtained once, at setup, by UNRANKING start_idx_k
    #  (standard combinatorial unranking of multisets — see
    #  `_unrank_multicombination` below). From there the same odometer
    #  advance as before (`_advance_tuple_cursor!`) walks forward in lex
    #  order, except the carry bound is now the GLOBAL nF_cur (an entry may
    #  be any FB index, not just one inside a slice), and instead of relying
    #  on hitting a slice boundary to wrap, we count steps taken and wrap
    #  back to this thread's own start tuple once its chunk has been fully
    #  cycled — so threads never re-enter each other's assigned ranges.
    #
    #  For k=1, Nk == nF_cur exactly and this reduces to precisely the old
    #  FB-slicing scheme (start_idx_1 + 1 == old anchor_start, chunk_size_1
    #  == old slice_size), so k=1 behaviour — including the i0-exclusivity
    #  guarantee across threads that same-partial collision detection relies
    #  on — is unchanged.
    # ==========================================================================
    nt_    = n_workers
    K_ceil = anchor_tuple_size   # effective ceiling; K_ceil <= K_MAX (CLI-validated)

    # multichoose(n, k) = C(n+k-1, k): count of non-decreasing k-tuples
    # (multisets of size k) drawable from n distinct values. BigInt
    # throughout — Nk grows combinatorially in k and can exceed Int64 for
    # realistic (nF_cur, K_ceil) once K_ceil gets past ~4-5.
    @inline function _multichoose_big(n::Integer, k::Integer)::BigInt
        k == 0 && return BigInt(1)
        n <= 0  && return BigInt(0)
        return binomial(BigInt(n) + BigInt(k) - 1, BigInt(k))
    end

    # Unrank position `rank` (0-indexed, BigInt) in the lex order of
    # non-decreasing k-tuples with entries in [1,n] — the SAME order
    # produced by _advance_tuple_cursor! below (first coordinate
    # slowest-changing, last coordinate fastest-changing). Standard greedy
    # unranking: at each position, walk candidate values upward, skipping
    # past however many completions each candidate value would cover.
    @inline function _unrank_multicombination(rank::BigInt, n::Int, k::Int)::Vector{Int}
        result = Vector{Int}(undef, k)
        lo  = 1
        rem = rank
        for i in 1:k
            v = lo
            while true
                cnt = _multichoose_big(n - v + 1, k - i)
                if rem < cnt
                    result[i] = v
                    lo = v
                    break
                else
                    rem -= cnt
                    v += 1
                end
            end
        end
        return result
    end

    # Per-thread balanced chunk of the global tuple-index space, one entry
    # per tuple length k = 1..K_ceil, computed once at thread setup.
    chunk_size_k  = Vector{Int}(undef, K_ceil)      # capped at typemax(Int)
    start_tuple_k = Vector{Vector{Int}}(undef, K_ceil)

    idle = false
    for k in 1:K_ceil
        Nk         = _multichoose_big(nF_cur, k)
        base_chunk = Nk ÷ nt_
        r_k        = Nk % nt_
        start_idx  = BigInt(tid - 1) * base_chunk + min(BigInt(tid - 1), r_k)
        end_idx    = start_idx + base_chunk - 1 + (tid <= r_k ? 1 : 0)

        if start_idx >= Nk
            # This thread has no tuples of length k specifically. THIS ALONE
            # DOES NOT MEAN THE THREAD IS IDLE — see the bug this replaced,
            # below.
            chunk_size_k[k]  = 0
            start_tuple_k[k] = fill(1, k)   # placeholder; only read if chunk_size_k[k]>0 elsewhere by mistake
            continue
        end

        chunk_big       = end_idx - start_idx + 1
        chunk_size_k[k] = chunk_big > typemax(Int) ? typemax(Int) : Int(chunk_big)
        start_tuple_k[k] = _unrank_multicombination(start_idx, nF_cur, k)
    end

    # BUGFIX (the actual root cause of threads sitting IDLE with
    # nF_cur=25 < n_workers=32 despite K_ceil=6 giving those same threads
    # tens of thousands of valid k=2..6 tuples apiece — see conversation,
    # confirmed by hand-computing chunk_size_k for tid=26..32 with
    # nF_cur=25, n_workers=32: chunk_size_k[1]==0 but chunk_size_k[2..6]
    # are all in the thousands-to-tens-of-thousands range, definitely
    # nonzero):
    #
    # The OLD code set `idle = true` the moment k==1 hit start_idx>=Nk,
    # then unconditionally returned empty results for the WHOLE thread —
    # discarding its perfectly valid, already-computed k=2..K_ceil chunks.
    # The comment justifying that ("Since Nk is non-decreasing in k, this
    # can only happen at k=1") is true as far as it goes — Nk=multichoose
    # (nF_cur,k) does grow with k, so start_idx>=Nk can indeed only trip at
    # k=1 — but the CONCLUSION drawn from it was wrong: "only happens at
    # k=1" was read as "therefore the thread has no tuples at all," when
    # it actually only means "no LENGTH-1 tuples." For any K_ceil>=2 this
    # is precisely the case where the tuple-space-slicing refactor (see
    # the big comment above this loop) was supposed to give excess threads
    # real work via k>=2 — the early return was silently throwing that
    # away and falling back to exactly the "still only slicing by FB"
    # behaviour the refactor was meant to fix.
    #
    # CORRECT CONDITION: a thread is only genuinely idle if EVERY k in
    # 1:K_ceil has an empty chunk — i.e. n_workers exceeds the ENTIRE
    # k=1..K_ceil tuple space combined, not just the k=1 slice. Since Nk is
    # strictly increasing in k (for nF_cur>=1), this reduces to checking
    # k==K_ceil alone (the largest, hence most populous, tuple space) —
    # but checking all(iszero, chunk_size_k) directly is just as cheap and
    # doesn't rely on that monotonicity argument holding in some future
    # edit (e.g. if _multichoose_big's formula or nF_cur's role in it ever
    # changes).
    idle = all(iszero, chunk_size_k)

    if idle
        # This thread has no FB elements to walk at all (n_workers > nF_cur).
        # Return empty results immediately rather than wrapping with mod1
        # (which aliases i0 ranges and produces spurious same_col=100% on
        # the wrapped threads).
        verbose && @printf("[thread %2d | IDLE | no tuple-space slice (nF_cur=%d < n_workers=%d)]\n",
                           tid, nF_cur, nt_)
        return (rel_rows      = Dict{Int,Int}[],
                alpha_vec     = BigInt[],
                beta_vec      = BigInt[],
                phi_attempts  = 0,
                hits_total    = 0,
                hits_full     = 0,
                hits_0lp      = 0,
                hits_lp1      = 0,
                hits_1lp_emit = 0,
                hits_lp1_conj      = 0,
                hits_1lp_conj_emit = 0,
                hits_1lp_conj_trivial_same_col  = 0,
                hits_1lp_conj_trivial_zero_dal  = 0,
                hits_1lp_conj_trivial_dup       = 0,
                hits_1lp_conj_row_missing       = 0,
                hits_1lp_conj_attractor_exact   = 0,
                hits_1lp_conj_attractor_birthday= 0,
                hits_lp2seen  = 0,
                hits_lp2emit  = 0,
                hits_lp2_cross= 0,
                hits_lp2_odd  = 0,
                hits_lp2_cap  = 0,
                hits_skip     = 0,
                evictions_conj= 0,
                sample_rels   = Dict{Int,Int}[],
                total_steps   = 0,
                smooth_hist   = zeros(Int, 4),
                rank_growth   = Tuple{Int,Int}[],
                lp_col        = Int[],
                phi_bias_stat = phi_bias_stat,
                basin_hot_anchors  = Int[],
                basin_steers_fired = 0,
                basin_steers_hit   = 0,
                lp1_conj_mean_gap_steps = 0.0,
                deep_stat = deep_stat,
                d38_stat = d38_stat)
    end

    verbose && tid == 1 && K_ceil >= 2 && @printf(
        "[thread %2d | tuple-space slicing: nF_cur=%d, K_ceil=%d, chunk sizes per k = %s]\n",
        tid, nF_cur, K_ceil, string(chunk_size_k))

    # tuple_cursors[k] holds the CURRENT length-k tuple (as FB indices,
    # non-decreasing) for this thread's walk over its length-k chunk.
    # Seeded to this thread's own start tuple for each k.
    tuple_cursors = [copy(start_tuple_k[k]) for k in 1:K_ceil]

    # Steps taken so far within the current cycle of this thread's chunk,
    # per k — used to wrap back to start_tuple_k[k] once the whole chunk has
    # been walked, instead of relying on the odometer hitting a slice
    # boundary (there is no boundary now: entries range over the full
    # [1, nF_cur], not a per-thread slice).
    step_in_chunk_k = zeros(Int, K_ceil)

    # cur_anchors is sized to the hard compile-time ceiling K_MAX so it can
    # hold any length up to K_MAX, but only the first k_cur_ref[] slots are
    # meaningful after any given next_anchor_tuple() call — every caller must
    # iterate `1:k_cur_ref[]`, never the whole vector, once k_cur_ref[] < K_MAX.
    # Use MVector so the ntuple() shim at step_phi_k!'s boundary sees a
    # StaticArray: escape analysis can prove all bounds and lifetimes
    # statically, enabling stack allocation of the NTuple.
    cur_anchors  = MVector{K_MAX, NTuple{2,Int}}(ntuple(_ -> (0,0), Val(K_MAX)))

    # Tracks the tuple length k produced by the most recent next_anchor_tuple()
    # call. Wrapped in a Ref (not a plain local) so it can be mutated from
    # inside the closures below without Julia boxing the outer binding —
    # mirrors the existing next_anchor_ref convention just below. Starts at 0
    # so the very first call yields k=1 (round-robin's natural starting point).
    k_cur_ref = Ref{Int}(0)

    # ==========================================================================
    #  Weighted round-robin over tuple length k = 1..K_ceil.
    #
    #  Previously this was a *flat* round-robin (k=1,2,...,K_ceil,1,2,...):
    #  every length got exactly 1/K_ceil of all next_anchor_tuple() calls,
    #  regardless of how the k-tuple space (and its closure yield) scales
    #  with k. At K_ceil=6 that means 1/6 of all wall-clock walk effort goes
    #  into 6-anchor tuples, whose combinatorial space is astronomically
    #  larger than k=1's and whose closure probability is correspondingly far
    #  lower — i.e. the walk can burn most of a run chasing rare fat
    #  relations before the cheap small-k ones are anywhere near exhausted.
    #
    #  Fix: bias the schedule toward small k with a SMOOTH weighted
    #  round-robin (the scheme nginx uses for weighted load balancing): each
    #  length k carries a static weight w_k; each call picks whichever k has
    #  accumulated the most "credit" (credit[i] += w_i every call), then
    #  debits the winner by the total weight. This reproduces the ratio
    #  w_k / sum(w) over the long run WITHOUT clustering — it interleaves
    #  k=1's and k=6's rather than doing a block of one length before moving
    #  to the next — and degenerates exactly to the old flat round-robin when
    #  all weights are equal (anchor_tuple_weight_decay = 1.0).
    #
    #  Default weight_k = anchor_tuple_weight_decay^(K_ceil - k): geometric
    #  decay, so k=1 is `decay^(K_ceil-1)` times as frequent as k=K_ceil.
    #  decay=2.0, K_ceil=6 -> weights [32,16,8,4,2,1] for k=1..6 (k=1 is 32x
    #  as frequent as k=6). Raise anchor_tuple_weight_decay to push harder
    #  toward small k; set to 1.0 to recover the old flat behaviour exactly.
    # ==========================================================================
    # BUGFIX (companion to the idle-thread fix above): zero the weight of
    # any k whose chunk_size_k[k]==0 for THIS thread, so the SWRR schedule
    # below can never select it.
    #
    # Without this, _next_k() was a pure function of (K_ceil,
    # anchor_tuple_weight_decay) with no knowledge of this thread's actual
    # per-k chunk sizes. For any excess thread (n_workers > Nk at k=1, the
    # exact case the idle-fix above addresses) that still has empty chunks
    # at some OTHER k too — e.g. nF_cur small enough that even k=2 is
    # exhausted before all threads get a slice, while k>=3 still has
    # room — _next_k() would keep periodically selecting that empty k
    # anyway. tuple_cursors[k] for an empty chunk is permanently pinned to
    # the unadvanced placeholder start_tuple_k[k] = fill(1, k), so every
    # such selection either:
    #   (a) silently re-returns the identical placeholder tuple forever,
    #       wasting that k's whole weight share on a single duplicate
    #       relation-check instead of real work other k's could have used,
    #       or
    #   (b) if that placeholder tuple happens to be structurally poisoned
    #       (e.g. fb[1] is a repeated Weierstrass point), hard-errors the
    #       thread almost immediately: chunk_size_k[k]==0 means
    #       _advance_tuple_cursor!(k)'s step-count guard
    #       (step_in_chunk_k[k] >= chunk_size_k[k], i.e. 0 >= 0) fires on
    #       the very first advance and just copies start_tuple_k[k] onto
    #       itself, so the `rejects > chunk_size_k[k]` bound in
    #       next_anchor_tuple() (i.e. rejects > 0) trips on the second
    #       attempt and raises — a thread crash caused entirely by
    #       scheduling a k this thread was never assigned any real tuples
    #       for, not by an actual poisoned tuple in its assigned chunks.
    #
    # Excluding empty-chunk k's from the weight vector up front avoids both:
    # this thread's SWRR credit is redistributed over only the k's it
    # genuinely has tuples for, in the same relative proportions
    # (anchor_tuple_weight_decay^(K_ceil-k)) as before.
    k_weight     = [chunk_size_k[k] == 0 ? 0.0 : anchor_tuple_weight_decay^(K_ceil - k) for k in 1:K_ceil]
    k_weight_tot = sum(k_weight)
    k_cur_weight = zeros(Float64, K_ceil)   # SWRR running credit, one per k

    @inline function _next_k()::Int
        K_ceil == 1 && return 1
        @inbounds for i in 1:K_ceil
            k_cur_weight[i] += k_weight[i]
        end
        # Seed `best` with the first k this thread actually has tuples for,
        # not unconditionally k=1: if chunk_size_k[1]==0 (the common excess-
        # thread case the whole idle-fix is about), k=1 is excluded and must
        # never be the starting candidate the loop below compares against.
        # idle=all(iszero,chunk_size_k) was already checked earlier and this
        # function is only reachable when that was false, so at least one
        # k_weight[i]>0.0 is guaranteed to exist.
        best = findfirst(>(0.0), k_weight)::Int
        @inbounds for i in (best + 1):K_ceil
            # Skip k's with zero weight (this thread has no tuples of that
            # length) even if floating-point noise ever let their credit
            # creep above another k's — chunk_size_k[i]==0 is the ground
            # truth, k_weight[i]==0.0 encodes it exactly, so this branch
            # should never matter in practice, but checking the weight
            # directly (not just comparing credit) costs nothing and
            # removes that possibility entirely.
            (k_weight[i] > 0.0) && k_cur_weight[i] > k_cur_weight[best] && (best = i)
        end
        @inbounds k_cur_weight[best] -= k_weight_tot
        return best
    end

    # Defensive check: if K_ceil >= 2 and the ENTIRE factor base is
    # Weierstrass points (py == 0), every possible k-tuple with k>=2 that
    # repeats any single FB index is structurally poisoned, and — since
    # every thread's tuples are now drawn from the full FB, not a
    # per-thread slice — this is a GLOBAL property of fb[] rather than
    # something that can differ thread-to-thread as it could under the old
    # per-slice scheme. Checked once against the whole factor base.
    if K_ceil >= 2
        n_weierstrass_total = count(i -> fb[i][2] == 0, 1:nF_cur)
        if n_weierstrass_total == nF_cur
            error("Thread $tid: the entire factor base ($nF_cur points) is " *
                  "Weierstrass; no valid k-tuple with k>=2 exists. Reduce " *
                  "--anchor-tuple-size, or increase factor base size / mix " *
                  "in non-Weierstrass points.")
        end
    end

    # Structural validity check: true iff the first `k` entries of `tup`
    # are compatible with what build_phi_general! can actually construct:
    #   - a Weierstrass point (py == 0) must not repeat at all (branch_series!
    #     divides by Fy = 2*py, which is 0 at a Weierstrass point regardless
    #     of multiplicity — even a single such anchor already relies on
    #     that division inside compute_branch_series!'s m=1 path... actually
    #     m=1 never calls branch_series!'s divide-by-Fy branch (see its
    #     early `if m==1` return), so a lone Weierstrass anchor is fine; a
    #     REPEATED one would need m=2, which does hit that division, hence
    #     the special-case rejection here).
    #   - any other point may repeat AT MOST twice (single tangency, m=2,
    #     implemented via fill_f_tay!/branch_series!'s m=2 path in
    #     build_phi_general!'s anchor loop). A point occurring 3+ times
    #     would need m=3 (double tangency / higher jet), which fill_f_tay!
    #     does not populate (it only fills f_tay[2] = F_x(px); a
    #     hypothetical f_tay[3] = F_xx(px) is not computed anywhere) — see
    #     build_phi_general!'s own occ_count assert, which this mirrors so
    #     a bad tuple is rejected here, before it ever reaches the
    #     φ-builder, rather than assert-failing deep inside it.
    @inline function _anchor_tuple_valid(tup, k::Int)::Bool
        @inbounds for i in 1:k
            cnt = 0
            for j in 1:k
                if tup[j] == tup[i]
                    cnt += 1
                end
            end
            tup[i][2] == 0 && cnt >= 2 && return false   # Weierstrass: no repeats at all
            cnt >= 3 && return false                      # anyone: at most double (m=2)
        end
        return true
    end

    @inline function _advance_tuple_cursor!(k::Int)
        # Advance the length-k cursor by one step in the GLOBAL lex order
        # (entries range over the full [1, nF_cur], not a per-thread FB
        # slice): increment last position, carry right-to-left, bounded by
        # nF_cur. Once this thread has taken chunk_size_k[k] steps — i.e. it
        # has cycled all the way through its own assigned chunk of the
        # tuple-index space — wrap back to this thread's own start tuple
        # (start_tuple_k[k]), NOT to global index 1, so threads never
        # re-enter each other's assigned ranges.
        step_in_chunk_k[k] += 1
        tc = tuple_cursors[k]
        if step_in_chunk_k[k] >= chunk_size_k[k]
            step_in_chunk_k[k] = 0
            copyto!(tc, start_tuple_k[k])
            return
        end
        @inbounds begin
            pos = k
            while pos >= 1
                if tc[pos] < nF_cur
                    tc[pos] += 1
                    # Reset all positions to the right to the new value (non-decreasing)
                    for j in pos+1:k
                        tc[j] = tc[pos]
                    end
                    break
                end
                pos -= 1
            end
            if pos == 0
                # Should be unreachable while step_in_chunk_k[k] < chunk_size_k[k]
                # (the step-count wrap above always intercepts before the
                # odometer would need to carry past the last global tuple) —
                # kept as a defensive guard against off-by-one drift, wrapping
                # to this thread's own start tuple rather than corrupting state.
                copyto!(tc, start_tuple_k[k])
                step_in_chunk_k[k] = 0
            end
        end
    end

    @inline function next_anchor_tuple()
        # Weighted round-robin the tuple length itself (see _next_k above):
        # small k is visited more often than large k by anchor_tuple_weight_decay.
        # With decay=1.0 this is exactly the old flat 1->2->...->K_ceil->1->...
        # cycle.
        k = _next_k()
        k_cur_ref[] = k
        tc = tuple_cursors[k]

        # Snapshot this length's current cursor into cur_anchors[1:k]
        # (preserves original semantics: the first time length k comes up, it
        # returns that length's seed tuple unadvanced).
        @inbounds for i in 1:k
            cur_anchors[i] = fb[tc[i]]
        end

        # Structurally reject poisoned tuples (a Weierstrass point repeated
        # >= 2 times) by advancing past them here, instead of returning them
        # to the caller and relying on a `continue` that never re-advances
        # the cursor. Bounded by this thread's own chunk_size_k[k] so a
        # chunk that is entirely poisoned raises loudly instead of spinning
        # forever.
        rejects = 0
        while !_anchor_tuple_valid(cur_anchors, k)
            _advance_tuple_cursor!(k)
            @inbounds for i in 1:k
                cur_anchors[i] = fb[tc[i]]
            end
            rejects += 1
            if rejects > chunk_size_k[k]
                error("Thread $tid: every tuple in this thread's length-$k chunk " *
                      "($(chunk_size_k[k]) tuples) is structurally poisoned " *
                      "(repeated Weierstrass point). Reduce --anchor-tuple-size " *
                      "or increase factor base size.")
            end
        end

        _advance_tuple_cursor!(k)
        return cur_anchors
    end

    # Compatibility shim: next_anchor() returns just the first element of the
    # tuple (used for single-anchor diagnostics, px_anchor fields, etc.).
    @inline function next_anchor()
        t = next_anchor_tuple()
        return t[1]
    end
    next_anchor_ref = Ref{Function}(next_anchor)

    # ==========================================================================
    #  Alpha/beta cursor offsets — distinct per-thread seeds, plus a shared
    #  no-repeat gate that makes the expensive LP bookkeeping global-unique.
    #
    #  The per-thread seeds still keep the deterministic walk phases decorrelated,
    #  but uniqueness across the whole run is enforced by phase2_alpha_first_seen!
    #  right after each alpha update.  That lets us avoid doing any further work
    #  for a residue once some thread has already consumed it.
    #
    #  The walk still advances deterministically, but we no longer rely on the
    #  thread-local seed alone for uniqueness.  Instead, a shared alpha bitmap
    #  marks each residue the first time any thread reaches it; later visits are
    #  skipped before the expensive φ / LP machinery runs.
    #
    #  The per-thread slice below is still useful as a cheap way to decorrelate
    #  the first few residues each worker sees, but global uniqueness is now
    #  enforced by phase2_alpha_first_seen!.
    #
    #  Partition [1, ell-1] (ell-1 values) into n_workers contiguous chunks
    #  using the same balanced-partition scheme as the anchor cursor above,
    #  and give thread `tid` the start of its chunk as the additive offset.
    #  Requires n_workers <= ell-1 ("threads << ell"); if violated, raise
    #  rather than silently letting two threads share an offset.
    # ==========================================================================
    ellm1 = ellI - 1
    nt_ > ellm1 && throw(ArgumentError(
        "phase2_worker: n_workers=$nt_ exceeds ell-1=$ellm1 — cannot give " *
        "every thread a distinct alpha/beta cursor offset (threads << ell required)"))
    base_chunk_ab = ellm1 ÷ nt_
    r_ab          = ellm1 % nt_
    ab_offset     = (tid - 1) * base_chunk_ab + min(tid - 1, r_ab)   # in [0, ellm1-1]

    alpha_cursor     = 1 + ab_offset                      # in [1, ell-1], distinct per thread
    beta_cursor_init = beta_zero ? 0 : (1 + ab_offset)    # same offset reused for beta:
                                                           # alpha alone already guarantees
                                                           # (alpha,beta) disjointness above

    # ==========================================================================
    #  Golden-ratio (R2 low-discrepancy) drift — added to alpha_cur/beta_cur
    #  (and the matching D_cur term) every step, on top of the deterministic
    #  step table.
    #
    #  WHY: a zero_dal closure fires when combined_al==combined_be==0, i.e.
    #  the CURRENT (alpha_cur,beta_cur) equals the (alpha_cur,beta_cur) that
    #  was in force when the colliding lp_key was first STORED.  Without a
    #  drift term, alpha_cur(n)/beta_cur(n) are entirely determined by the
    #  fixed step table cycling with period N_STEPS: if the table's net
    #  per-lap drift (sum(step_a_i), sum(step_b_i)) happens to be ≡ 0
    #  (mod ell), alpha_cur/beta_cur are THEMSELVES periodic with period
    #  N_STEPS (or a divisor) — so ANY two closures whose step indices land
    #  on the same table phase (n ≡ m mod N_STEPS) automatically get
    #  combined_al == combined_be == 0, a structural ~1/N_STEPS-ish collision
    #  rate independent of how "interesting" the (fb_row, prev_fb_row) pair is.
    #  That's the likely source of the high zero_dal fractions you're seeing
    #  (and why it'd vary thread-to-thread: each thread's closures land at
    #  different absolute step counts, hence different table-phase mixes).
    #
    #  FIX: add a fixed nonzero per-step increment (Δ_a,Δ_b) to alpha_cur/
    #  beta_cur, taken from the 2D R2 low-discrepancy sequence — the proper
    #  2D generalisation of "golden ratio striding" (plastic number
    #  g≈1.3247179572447460..., α1=1/g≈0.7548776662, α2=1/g²≈0.5698402910;
    #  these two are far better mutually-decorrelated than φ and φ² would be).
    #  Since ell is prime, any nonzero Δ generates all of (Z/ellZ,+), so
    #  alpha_cur(n) = mod(alpha_cursor_0 + n*Δ_a + Cum_a^table(n), ell) is now
    #  dominated by the n*Δ_a term, which is injective for n=1..ell-1.  Two
    #  closures n≠m now satisfy alpha_cur(n)==alpha_cur(m) only if
    #  (n-m)*Δ_a ≡ (table-part difference) — a single residue class of (n-m)
    #  per possible table difference, i.e. collisions drop from ~1/N_STEPS to
    #  ~O(N_STEPS)/ell.  Requiring BOTH combined_al==0 AND combined_be==0
    #  (independent Δ_a,Δ_b) pushes zero_dal down to ~O(N_STEPS²)/ell².
    #
    #  D_cur is kept consistent (D_cur == alpha_cur*G + beta_cur*T, mod ell in
    #  the Jacobian) by adding the matching DRIFT_D = Δ_a*G + Δ_b*T every step,
    #  exactly the way step_D[si] already tracks (step_a_i[si],step_b_i[si]).
    #  In beta_zero mode, Δ_b=0 and DRIFT_D carries no T-component, so
    #  beta_cur stays identically 0 as before.
    # ==========================================================================
    # Reversed-alpha experiment: phase-2 alpha cursor decrements instead of
    # incrementing, and the golden-ratio drift runs in the same reversed direction.
    # Together with sequential-alpha phase 1 (which bakes in a low-index↔low-alpha
    # correlation into the FB), this puts the two sweeps in opposite orientations,
    # so the (fb_index, alpha) coupling from phase 1 fights the phase-2 traversal
    # rather than aligning with it.  Goal: observe D39c cross-term sign flip and
    # assess whether sweep-coupling accounts for the apparent key autocorrelation.
    #
    # DELTA_A is negated so the drift also decrements; DRIFT_D is recomputed to
    # match (D_cur must stay consistent with alpha_cur*G + beta_cur*T mod ell).
    # DELTA_B and beta are left forward — only alpha orientation is under test.
    DELTA_A = -Int(div(BigInt(ellI) * BigInt(754877666246692760), BigInt(10)^18))  # -(ell * 1/g)
    DELTA_B = beta_zero ? 0 :
               Int(div(BigInt(ellI) * BigInt(569840290998053265), BigInt(10)^18)) # ell * 1/g^2
    (DELTA_A == 0 || (!beta_zero && DELTA_B == 0)) && throw(ArgumentError(
        "phase2_worker: ell=$ellI too small for a nonzero golden-ratio drift " *
        "(DELTA_A=$DELTA_A, DELTA_B=$DELTA_B) — increase ell or disable the drift"))
    # DRIFT_D carries the negated DELTA_A: jac_mul with a negative scalar mod ell
    # is jac_mul(G, ell + DELTA_A, ell) since DELTA_A < 0 here.
    DRIFT_D = beta_zero ? jac_mul(G, BigInt(mod(DELTA_A, ellI)), ell) :
                          jac_add(jac_mul(G, BigInt(mod(DELTA_A, ellI)), ell),
                                  jac_mul(T, BigInt(DELTA_B), ell))

    @inline function next_alpha_beta()::Tuple{Int,Int}
        a = alpha_cursor
        b = beta_zero ? 0 : beta_cursor_init
        # Decrement: alpha sweeps downward, wrapping from 1 back to ell-1.
        alpha_cursor -= 1
        if alpha_cursor < 1
            alpha_cursor = ellI - 1
        end
        if !beta_zero
            beta_cursor_init += 1
            if beta_cursor_init > ellI - 1
                beta_cursor_init = 1
            end
        end
        return a::Int, b::Int
    end

    # --- Walk state ---
    # For k_cur_ref[] == 1: cur_pt is the sole anchor (classic behaviour).
    # For k_cur_ref[] >  1: cur_anchors[1:k_cur_ref[]] holds the full k-tuple;
    #                 cur_pt = cur_anchors[1] is used for diagnostics, pt2idx
    #                 lookups, and the handle_* LP helpers (which remain
    #                 single-anchor). k_cur_ref[] itself varies step-to-step
    #                 now that tuple length round-robins over 1..K_ceil.
    next_anchor_tuple()
    cur_pt = cur_anchors[1]      # initial cur_pt from the seeded tuple
    # D29 artifact filter: tracks whether cur_pt's MOST RECENT assignment came
    # from a genuine LP resolution (handle_1lp_affine!/handle_1lp_conj!/
    # handle_2lp_affine! storing or closing) vs a bare next_anchor() round-robin
    # advance. Read at next iteration's record_d29_step! call (it describes P0,
    # i.e. last step's cur_pt), then overwritten by this step's own assignment.
    # Initial value is false: the seed cur_pt came from next_anchor() above.
    cur_pt_from_lp = false
    alpha_cur::Int, beta_cur::Int = next_alpha_beta()
    D_cur     = beta_zero ? jac_mul(G, BigInt(alpha_cur), ell) :
                            jac_add(jac_mul(G, BigInt(alpha_cur), ell), jac_mul(T, BigInt(beta_cur), ell))

    # --- Per-thread relation accumulation ---
    hint = max(64, cld(rel_target, Threads.nthreads()) + 32)
    alpha_vec = sizehint!(BigInt[], hint)
    beta_vec  = sizehint!(BigInt[], hint)
    rel_rows  = sizehint!(Vector{Dict{Int,Int}}(), hint)

    # --- Counters (collected in WorkerStats at the end) ---
    s = WorkerStats()

    # --- Scratch dicts (reused every step to avoid per-step allocation) ---
    fb_row_scratch   = sizehint!(Dict{Int,Int}(), 4)
    # anchor_tuple_size (K_ceil) is now the round-robin CEILING, not a single
    # fixed tuple length — the walk visits every length k = 1..K_ceil in
    # rotation, and each length needs its OWN ThreadScratchpad{k}, since
    # ThreadScratchpad{K} bakes K into every field size (A_mat is
    # (K+2)x(K+2), seen_counts has K slots, etc.). We build one instance per
    # length up front (each still allocated once per thread, exactly as the
    # old single ThreadScratchpad{K_MAX} was) and hold them in a
    # heterogeneous tuple so every element keeps its own concrete type —
    # no abstract-type boxing, no dynamic dispatch inside the hot loop.
    # k=1 never actually reaches into this tuple (see the K==1 fast path in
    # the main loop below, which calls the closed-form build_phi_mumford
    # instead), but we still build slot 1 so scratch_by_k stays uniformly
    # 1-indexed by k; the extra allocation is negligible and happens once.
    # init_scratch_caches! returns a NEW, fully-typed ThreadScratchpad with
    # concrete FpT/RxT/BufT type params instead of Nothing placeholders,
    # eliminating dynamic dispatch on every Oscar dereference in
    # find_roots_and_points_inplace!.
    # IMPORTANT — representation-consistency invariant (see KNOWN LIMITATION
    # in trial3_fp_backend.jl): F_POLY_DESC is a module-level global filled
    # once by init_phi_general_caches!(max_k, backend) and is combined inside
    # branch_series! with backend-form px/py via fpmul_b. `backend` here must
    # be the SAME instance (or at least the same kind + same p) as the one
    # passed to init_phi_general_caches! by the driver before any worker was
    # spawned — a mismatch silently mixes representations and is not
    # reliably caught by phi_residual_general!'s remainder check. The driver
    # should construct `backend` once, call
    # init_phi_general_caches!(K_MAX, backend) and validate_backend(backend)
    # before spawning threads, then pass that same `backend` into every
    # phase2_worker(...; backend=backend) call.
    scratch_by_k = ntuple(k -> init_scratch_caches!(ThreadScratchpad{k}(), p, backend), Val(K_ceil))
    # Kept for the handful of call sites (handle_1lp_conj!, sparse_copy!,
    # etc.) that only ever touch the K-independent `.combined_scratch` Dict
    # field and accept ThreadScratchpad{<:Any} — any one instance will do,
    # so we default to the k=1 slot. The main loop below always passes the
    # step's OWN active scratch (returned by step_phi_dispatch!) wherever the
    # callee's behaviour actually depends on K.
    combined_scratch = scratch_by_k[1]

    # Initialize a fast, thread-local RNG for step selection.
    # Xoshiro has a 2^256 period and is seeded randomly per thread,
    # so threads take fully independent paths through the step table.
    rng = Random.Xoshiro()

    # --- Conj relation dedup filter ---
    # Tracks (lo_idx, hi_idx, combined_al, combined_be) of every conj relation
    # already emitted by this thread.  Prevents the repeated-closure pathology
    # where the same deterministic step-table delta regenerates the same key pair
    # with the same alpha difference, producing an identical weight-2 row.
    # Key is canonical: (lo_row_hash, hi_row_hash, combined_al, combined_be)
    # so equivalent relation pairs from the same anchor pair are deduplicated.
    emitted_conj_rels = Set{NTuple{4,Int}}()

    # --- Attractor detection: for same-col trivial conj closes, check whether
    #     Δα = 0 too (same walk path revisit) vs Δα ≠ 0 (different path, but
    #     same anchor+key — still a birthday, just filtered).
    #     Key = (i0, lp_key); value = last neg_al seen.
    #     Only populated when a same-col close is first detected; capped to
    #     avoid OOM on pathological walks.
    conj_anchor_alpha_seen = Dict{Tuple{Int,CanonicalLP1Key}, Int}()
    CONJ_ANCHOR_ALPHA_CAP  = 200_000   # entries; ~6.4 MB at 32 bytes/entry

    # --- Diagnostics ---
    sample_phase2_rels = Vector{Tuple{Div2,Int,Int,NTuple{2,Int},NTuple{2,Int},NTuple{2,Int}}}()
    rank_growth  = Tuple{Int,Int}[]
    t_last_report = time()
    report_interval_secs = 30.0

    # Desynchronize the step cursor to break rigid formation
    # (step_cursor is no longer used; PRNG below handles divergence)
    step_cursor = mod((tid - 1) * cld(N_STEPS, n_workers), N_STEPS) + 1
    # ==========================================================================
    #  Main walk loop
    # ==========================================================================
    # WILLY-NILLY ASSERT SUPPORT: stall canary. "one valid phi then nothing
    # for millions of steps" is exactly the symptom that a plain counter
    # dump can't diagnose (it just confirms the stall after the fact) — this
    # converts it into an immediate, loud failure the moment it happens,
    # instead of a multi-minute silent run the human has to notice and Ctrl-C.
    steps_since_hit = 0
    last_hit_k      = 0
    STALL_ASSERT_STEPS = 500_000

    while rel_counter[] < rel_target && s.raw_steps < step_cap && (amortized_precompute || ort_b1(ort) == 0)
        s.raw_steps += 1
        steps_since_hit += 1
        if steps_since_hit >= STALL_ASSERT_STEPS
            # Pull this thread's own phi-failure-reason counters (always
            # tracked now — see phi_timing_stats()'s lazy-init fallback in
            # trial3_phi_general.jl — independent of --phi-timing) so the
            # assert message names WHICH continue site inside
            # step_phi_dispatch!/build_phi_general!/phi_residual_general!/
            # phase2_worker's own post-processing is eating every attempt,
            # instead of just reporting that one exists.
            pts = phi_timing_stats()
            accounted = pts.n_fail_build + pts.n_fail_residual +
                        pts.n_drop_residual_deg_not_2_no_split + s.hits_total
            unaccounted = s.phi_attempts - accounted
            msg = "phase2_worker tid=$tid: $steps_since_hit raw steps since last phi hit (limit $STALL_ASSERT_STEPS) — " *
                  "raw_steps=$(s.raw_steps) phi_attempts=$(s.phi_attempts) hits_total=$(s.hits_total) hits_skip=$(s.hits_skip) " *
                  "k_cur=$(k_cur_ref[]) last_hit_k=$last_hit_k.  " *
                  "phi_fail_build=$(pts.n_fail_build) (gauss_singular=$(pts.n_fail_build_gauss_singular))  " *
                  "phi_fail_residual=$(pts.n_fail_residual) (anchor_remainder=$(pts.n_fail_resid_anchor_remainder), " *
                  "u_remainder=$(pts.n_fail_resid_u_remainder), degenerate=$(pts.n_fail_resid_degenerate))  " *
                  "post_success_drop_deg_not_2=$(pts.n_drop_residual_deg_not_2_no_split).  " *
                  "unaccounted=$unaccounted (phi_attempts - all_tracked_failures - hits_total; should be 0 for " *
                  "k_cur>=2 steps — k_cur==1's build_phi_mumford/phi_residual_mumford failures are NOT split into " *
                  "these buckets, only lumped into n_fail_build/n_fail_residual, since that fast-path function " *
                  "isn't in a file available for editing here)."
            # Raise unconditionally rather than only on the round-number
            # threshold: an unaccounted gap means there is a 5th silent
            # continue site this instrumentation pass didn't find (or a
            # cross-thread PHI_TIMING[] aliasing bug), and per Claire's
            # standing preference this must fail loudly, not degrade into
            # "well the buckets mostly add up."
            @assert unaccounted == 0 "$msg  ← ACCOUNTING GAP: a phi-attempt was silently dropped somewhere this instrumentation doesn't yet cover."
            @assert steps_since_hit < STALL_ASSERT_STEPS msg
        end

        # --- Periodic progress report (moved to top of loop) ---
        # Every other gate/skip below this point uses `continue`, which would
        # bypass a reporter placed later in the loop body. Keeping this check
        # first guarantees visibility into the walk even when a thread is
        # dropping the overwhelming majority of its steps (bloom-filter hits,
        # degenerate tuples, gate misses, etc.) — that situation is exactly
        # when seeing live progress matters most for diagnosing a stall.
        if verbose
            now_t = time()
            if (now_t - t_last_report) >= report_interval_secs
                report_worker_progress(tid, now_t - t_start, s, rel_counter, rel_target,
                                       shared_lp1_conj)
                t_last_report = now_t
            end
        end

        # --- PRNG step selection ---
        # Replace the previous hash(D_cur.u[1])-based selection, which caused
        # the walk to degenerate into a closed attractor cycle (D_{n+1} = f(D_n)
        # is a pure function → Birthday Paradox guarantees a short cycle).
        # Xoshiro period is 2^256; each thread is independently seeded, so
        # threads take divergent paths with no lockstep duplicates.
        si = rand(rng, 1:N_STEPS)
        D_cur     = jac_add(jac_add(D_cur, step_D[si]), DRIFT_D)
        alpha_cur = mod(alpha_cur + step_a_i[si] + DELTA_A, ellI)::Int
        beta_cur  = (beta_zero ? 0 : mod(beta_cur + step_b_i[si] + DELTA_B, ellI))::Int

        # Early no-repeat gate: once a residue has been consumed by any thread,
        # skip the rest of the expensive gate/φ/LP work for that alpha.
        phase2_alpha_first_seen!(alpha_gate, alpha_cur) || continue

        # --- Gate 1: D must be a degree-2 divisor (generic Jacobian element) ---
        fp3_deg(D_cur.u) != 2 && continue

        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]
        px, py = cur_pt   # cur_pt is set by the previous iteration's branch-end

        # k_cur: the tuple length that seeded cur_anchors this step (set by
        # the most recent next_anchor_tuple() call, either the initial seed
        # above the loop or the previous iteration's branch-end advance).
        # Only cur_anchors[1:k_cur] are meaningful — every loop over the
        # active anchor tuple below is bounded by k_cur, never the whole
        # (K_MAX-sized) cur_anchors vector.
        k_cur = k_cur_ref[]

        # --- Gate 2: all anchor points must not be in the support of D ---
        # (build_phi_general also checks each anchor; we do a fast pre-check here.)
        let _skip = false
            for _i in 1:k_cur
                _anc = cur_anchors[_i]
                _apx = _anc[1]
                _upx = fp(fp(_apx*_apx) + fp(u1*_apx) + u0)
                if _upx == 0; _skip = true; break; end
            end
            _skip && continue
        end

        # This step has cleared gate 1 (D degree-2) and gate 2 (no anchor in
        # supp(D)) and is about to actually attempt a phi build below.
        # hits_total/phi_attempts is the TRUE phi-construction success rate,
        # uncontaminated by phase2_alpha_first_seen! rejections upstream
        # (those are counted in raw_steps but never reach this line).
        s.phi_attempts += 1

        # --- Build φ and recover residual (k-aware) ---
        local res_R::NTuple{2,Int}, res_S::NTuple{2,Int}, RS_mumford::NTuple{4,Int}
        local a::Int  # φ leading x²-coefficient (used by D38 and phi_bias_stat)

        if k_cur == 1
            # Fast path: closed-form single-anchor φ
            PHI_TIMING_ENABLED[] && (phi_timing_stats().n_calls += 1)
            _pt_k1_series_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
            phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
            if PHI_TIMING_ENABLED[]
                phi_timing_stats().ns_series += time_ns() - _pt_k1_series_t0
            end
            if phi_c === nothing
                # build_phi_mumford's internal failure modes are opaque from
                # here (it's defined outside these three files, so we can't
                # instrument its own return sites) — but we CAN at least
                # count "k==1 build step failed" at this call site so a
                # future stall assert can tell k==1-vs-k>=2 apart instead of
                # only ever reporting the k>=2 general-path breakdown.
                # Deliberately NOT touching `s` (hits_skip etc.) here: `s`'s
                # mutable struct is defined in a file we don't have, and
                # guessing at unseen field names/types would be worse than
                # this separate, self-contained counter.
                pts_k1 = phi_timing_stats()
                pts_k1.n_fail_build += 1
                # No finer-grained bucket exists for k==1 (unlike gauss_singular
                # for the k>=2 path) since build_phi_mumford's internals aren't
                # visible here; if this dominates a future stall, the fix is to
                # add matching n_fail_* counters at build_phi_mumford's own
                # return sites, analogous to build_phi_general!'s gauss_singular one.
                continue
            end
            a, b_phi, c_phi, _ = phi_c

            # D38 — φ a-coefficient sequential autocorrelation.
            d38_stat !== nothing && record_d38_step!(d38_stat, Int(a))

            _pt_k1_resid_t0 = PHI_TIMING_ENABLED[] ? time_ns() : UInt64(0)
            res_R, res_S, RS_mumford = phi_residual_mumford(a, b_phi, c_phi, px, u0, u1)
            if PHI_TIMING_ENABLED[]
                phi_timing_stats().ns_residual += time_ns() - _pt_k1_resid_t0
            end
            if RS_mumford === SENTINEL_MUMFORD
                # division failed — same opacity caveat as above applies to
                # phi_residual_mumford's internal failure sites.
                pts_k1 = phi_timing_stats()
                pts_k1.n_fail_residual += 1
                continue
            end
        else
            # General k-anchor path via the zero-allocation step_phi_k!,
            # dispatched to the ThreadScratchpad{k_cur} instance out of
            # scratch_by_k (see step_phi_dispatch! in trial3_phi_general.jl).
            step_success, res_R, res_S, RS_mumford, a = step_phi_dispatch!(scratch_by_k, k_cur, cur_anchors, u0, u1, v0, v1; backend=backend)
            !step_success && continue

            # Restored guard (was dropped when the manual extraction block in
            # phase2_worker got replaced by step_phi_dispatch!/extract_step_results):
            # a residual that is neither degree-2 (RS_mumford real) NOR split
            # (res_R/res_S real) carries no usable information — it must be
            # discarded here exactly like the k_cur==1 branch above does via
            # its `RS_mumford === SENTINEL_MUMFORD` check. Without this guard,
            # RS_mumford stays as SENTINEL_MUMFORD = (-1,-1,-1,-1) and falls
            # through to canonical_lp1_conj_key(RS_mumford) below as if it were
            # a real Mumford key — a fabricated key (mod p wrap of -1 in each
            # coordinate) that can collide with genuine LP1-conj entries from
            # unrelated steps, producing false closures that fail the
            # RS-CONJ-CLOSE relation-integrity assertion downstream.
            if RS_mumford === SENTINEL_MUMFORD && res_R === SENTINEL_PT
                pts_drop = phi_timing_stats()
                pts_drop.n_drop_residual_deg_not_2_no_split += 1
                continue
            end

            # Anchor-sweep capture: grab this real, live-walk (anchors,u0,u1,v0,v1)
            # state as a base tuple for the independence experiment, iff a
            # collector is armed AND this step's tuple length matches the
            # collector's fixed K (base_tuples must share one K — see
            # trial3_anchor_sweep_diag.jl's run_anchor_sweep_experiment). No-op
            # (single field check, no lock) once disabled or already full.
            sweep_collector !== nothing &&
                try_capture!(sweep_collector, cur_anchors, k_cur, u0, u1, v0, v1)

            
            if d38_stat !== nothing 
                record_d38_step!(d38_stat, Int(a))
            end
        end

        s.hits_total += 1
        steps_since_hit = 0
        last_hit_k      = k_cur

        # SYMBOLIC-REPORT sampling: cheap, gated hook (see trial3_phi_general.jl's
        # "SYMBOLIC RESIDUAL REPORT" section) that copies this step's
        # (cur_anchors[1:k_cur], u0,u1,v0,v1) into a bounded per-thread buffer
        # for later, off-hot-path analysis via run_symbolic_report! (treats
        # the LAST anchor, cur_anchors[k_cur], as the one to make symbolic).
        # No-op unless SYMBOLIC_REPORT_ENABLED[] is set — same cost discipline
        # as PHI_TIMING_ENABLED[] elsewhere in this loop (one Ref{Bool} check).
        record_symbolic_sample!(cur_anchors, k_cur, u0, u1, v0, v1)

        # SYMBOLIC2-REPORT sampling: same cost discipline, one level up (see
        # trial3_phi_general.jl's "SYMBOLIC2 RESIDUAL REPORT" section) --
        # copies this step's (cur_anchors[1:k_cur], u0,u1,v0,v1) into a
        # bounded per-thread buffer, treating the LAST TWO anchors
        # (cur_anchors[k_cur-1], cur_anchors[k_cur]) as the ones to make
        # symbolic. No-op unless SYMBOLIC_REPORT_ENABLED[] is set, and a
        # further no-op below k_cur=2 (need two anchors to leave two
        # symbolic) -- gated by the SAME flag as record_symbolic_sample!
        # above, deliberately not a second independent toggle.
        record_symbolic_sample2!(cur_anchors, k_cur, u0, u1, v0, v1)

        al     = alpha_cur
        be     = beta_cur
        neg_al = mod(ellI - al, ellI)
        neg_be = mod(ellI - be, ellI)
        # BigInt conversion deferred to emit/store sites — avoids 4 heap allocs
        # on every valid step including 3-LP discards.
        P0     = cur_pt
        i0     = get(pt2idx, P0, 0)

        # D29 — wide-lag burst-memory trackers: log (alpha_cur, px) once per
        # valid step, before the LP1/LP2 branch, regardless of outcome. See
        # lp1_conj_deep_diag_core.jl's D29 constants-block docstring.
        # from_lp describes P0 = cur_pt as set at the END of the PREVIOUS
        # step (i.e. read before this step's own branch reassigns cur_pt).
        record_d29_step!(deep_stat, al, P0[1], cur_pt_from_lp)

        rs_split   = res_R !== SENTINEL_PT
        R          = res_R   # NTuple{2,Int} always; SENTINEL_PT if conjugate
        S          = res_S   # NTuple{2,Int} always; SENTINEL_PT if conjugate

        # Structural precondition: step_phi_k!/build_phi_mumford are supposed
        # to divide out the FULL anchor multiplicity (including tangencies,
        # via the multiplicity-aware vanishing-condition code) before handing
        # back the residual roots. If a residual root still equals one of the
        # k_cur anchors, that mass was double-counted — the row-building loop
        # below adds +1 for the anchor AND +1 for iR/iS at the same fb index,
        # silently fabricating an extra factor of atom(P0) in the banked
        # relation. This is the earliest point all of {P0,R,S,cur_anchors}
        # are known and is O(k_cur); left on unconditionally since it is
        # index/multiplicity bookkeeping, not floating Jacobian arithmetic.
        if rs_split
            for _i in 1:k_cur
                _anc = cur_anchors[_i]
                if R == _anc || S == _anc
                    @printf("\n[FATAL residual_anchor_collision tid=%d] φ-residual root coincides with anchor _i=%d: anc=%s  R=%s  S=%s  k_cur=%d  anchors=%s  (u0=%d u1=%d v0=%d v1=%d)\n",
                            Threads.threadid(), _i, string(_anc), string(R), string(S), k_cur,
                            string(ntuple(_j -> cur_anchors[_j], k_cur)), u0, u1, v0, v1)
                    Base.flush(stdout)
                    ccall(:exit, Cvoid, (Cint,), 1)
                end
            end
        end

        # --- φ a-parameter bias diagnostics ---
        # RS_mumford = (c0_rs, c1_rs, v0_rs, v1_rs); we use indices 1 and 2.
        # For split steps we do a cheap pt2idx lookup so the a=0 FB-smooth
        # counter is accurate.  These lookups are redundant with the ones in
        # BRANCH B below, but they cost one Dict lookup each and keep the
        # diagnostic self-contained.  For non-split steps iR/iS are not
        # meaningful; we pass false and the a=0_fb counter will not fire.
        let c0_rs = RS_mumford[1], c1_rs = RS_mumford[2]
            if rs_split
                _iR_d = get(pt2idx, R, 0)
                _iS_d = get(pt2idx, S, 0)
                record_phi_step!(phi_bias_stat, a, c1_rs, c0_rs,
                                 true, _iR_d != 0, _iS_d != 0,
                                 (u0, u1, v0, v1), p)
            else
                record_phi_step!(phi_bias_stat, a, c1_rs, c0_rs,
                                 false, false, false,
                                 (u0, u1, v0, v1), p)
            end
        end

        # ==========================================================================
        #  BRANCH A: conjugate residual (RS is a degree-2 Mumford pair over F_p²)
        # ==========================================================================
        if !rs_split
            lp_key32 = canonical_lp1_conj_key(RS_mumford::NTuple{4,Int})
            # For LP1-conj ALL anchors in the k-tuple must be in the FB.
            # If any anchor is off-FB the step has ≥2 large primes (RS pair + the
            # off-FB anchor) and belongs in the 2-LP-conj path, not here.
            all_anchors_in_fb = all(get(pt2idx, cur_anchors[_i], 0) != 0 for _i in 1:k_cur)
            if i0 != 0 && all_anchors_in_fb
                s.hits_lp1_conj += 1
                # Build the FB row for the anchor k-tuple.  No residual points
                # are added — the RS pair is off-FB by construction in this branch.
                empty!(fb_row_scratch)
                for _i in 1:k_cur
                    idx = get(pt2idx, cur_anchors[_i], 0)
                    fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
                end
                let _nb_a2 = length(phi_bias_stat.split_hist)
                    _a_bucket = clamp(1 + (Int(a) * _nb_a2) ÷ p, 1, _nb_a2)
                    n_emit_before = deep_stat.n_emissions
                    d34_stores_before = deep_stat.d12_n_stores_seen
                    cur_pt = handle_1lp_conj!(lp_key32, i0, fb_row_scratch, neg_al, neg_be, ell,
                                               fb, nF_cur, G, T,
                                               alpha_vec, beta_vec, rel_rows, rel_counter,
                                               ort, s, shared_lp1_conj, rank_growth,
                                               combined_scratch,
                                               P0, phi_bias_stat, next_anchor_ref,
                                               _a_bucket, deep_stat, al, P0[1], Int(a), P0[2],
                                               post_conj_stride,
                                               conj_anchor_alpha_seen, CONJ_ANCHOR_ALPHA_CAP,
                                               emitted_conj_rels, conj_dataset,
                                               si)
                    # D29: handle_1lp_conj! returns next_anchor_ref[]() on every
                    # path (miss, same-partial, AND emission/closure — see its
                    # source, every `return` is next_anchor_ref[]()). It never
                    # returns the LP point itself, so this is always cursor-derived.
                    cur_pt_from_lp = false
                    # D9: record 1LP-conj opcode; is_emission = true iff handle produced an emission
                    record_conj_deep_opcode!(deep_stat, OPCODE_1LP_CONJ,
                                             deep_stat.n_emissions > n_emit_before)
                    record_d20_step!(deep_stat, OPCODE_1LP_CONJ)
                    record_d22_d23_d24_step!(deep_stat)
                    record_d34_step!(deep_stat, P0[1], p,
                        deep_stat.d12_n_stores_seen > d34_stores_before ?
                        D34_OUTCOME_STORE : D34_OUTCOME_OTHER)
                end
            elseif enable_lp2_conj
                cur_pt = handle_2lp_conj!(P0, RS_mumford::NTuple{4,Int}, neg_al, neg_be, ell,
                                           fb, nF_cur, G, T,
                                           alpha_vec, beta_vec, rel_rows, rel_counter,
                                           ort, s, shared_lp1, nothing,
                                           nothing,
                                           shared_lp2_conj, shared_lp2_conj_lock,
                                           max_lp2_conj_nodes, rank_growth,
                                           combined_scratch, next_anchor_ref)
                # D29: handle_2lp_conj! returns next_anchor_ref[]() on every path
                # (cap, no-edge, even_cycle, odd_cycle both sub-branches) — never
                # the LP point itself. Always cursor-derived.
                cur_pt_from_lp = false
                # 2-LP-conj: the returned anchor may or may not be LP-derived;
                # conservatively mark as LP for Seq 3 since P0 came from a conj step.
                phi_bias_stat._prev_anchor_was_lp = true
                record_conj_deep_opcode!(deep_stat, OPCODE_2LP_CONJ, false)
                record_d20_step!(deep_stat, OPCODE_2LP_CONJ)
                record_d22_d23_d24_step!(deep_stat)
                record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_OTHER)
            else
                cur_pt = next_anchor()
                cur_pt_from_lp = false  # D29: next_anchor() round-robin advance, not LP-derived
                record_random_anchor!(phi_bias_stat)
                record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
                record_d20_step!(deep_stat, OPCODE_SKIP)
                record_d22_d23_d24_step!(deep_stat)
                record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_OTHER)
            end
            continue
        end

        # ==========================================================================
        #  BRANCH B: split residual (R, S are both F_p-rational)
        # ==========================================================================
        iR = get(pt2idx, R, 0)
        iS = get(pt2idx, S, 0)
        n_lp = (i0 == 0 ? 1 : 0) + (iR == 0 ? 1 : 0) + (iS == 0 ? 1 : 0)
        s.smooth_hist[n_lp + 1] += 1

        if n_lp == 0
            # ------------------------------------------------------------------
            #  0-LP: P0, R, S all in FB → full relation
            # ------------------------------------------------------------------
            empty!(fb_row_scratch)
            # Add ALL anchors from the k-tuple (bounded by k_cur, not the
            # K_MAX-sized cur_anchors buffer)
            for _i in 1:k_cur
                idx = get(pt2idx, cur_anchors[_i], 0)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end
            # Add the residual points
            for idx in (iR, iS)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end

            emit_0lp!(fb_row_scratch, neg_al, neg_be, fb, G, T,
                      alpha_vec, beta_vec, rel_rows, rel_counter, ort, s, rank_growth)
            if length(sample_phase2_rels) < 10
                push!(sample_phase2_rels, (D_cur, neg_al, neg_be,
                                           P0, R, S))
            end
            # IDEA 4: 0-LP is a full relation but NOT a LP1-conj event.
            cur_pt = next_anchor()
            cur_pt_from_lp = false  # D29: next_anchor() round-robin advance, not LP-derived
            record_random_anchor!(phi_bias_stat)
            record_conj_deep_opcode!(deep_stat, OPCODE_0LP, false)
            record_d20_step!(deep_stat, OPCODE_0LP)
            record_d22_d23_d24_step!(deep_stat)
            record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_0LP)

        elseif n_lp == 1
            # ------------------------------------------------------------------
            #  1-LP affine: exactly one of P0, R, S is not in FB
            # ------------------------------------------------------------------
            if !enable_lp1_aff
                s.hits_skip += 1
                cur_pt = next_anchor()
                cur_pt_from_lp = false  # D29: next_anchor() round-robin advance, not LP-derived
                record_random_anchor!(phi_bias_stat)
                record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
                record_d20_step!(deep_stat, OPCODE_SKIP)
                record_d22_d23_d24_step!(deep_stat)
                record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_OTHER)
            else
            s.hits_lp1 += 1

            lp_pt = i0 == 0 ? P0 : iR == 0 ? R : S

            # Cheap structural check on the n_lp==1 invariant this whole
            # branch assumes, BEFORE any Jacobian arithmetic or locking.
            # This is index bookkeeping (i0/iR/iS vs pt2idx), not group-law
            # correctness, so it's O(1) and safe to leave on unconditionally
            # rather than gating behind ASSERT_RELATIONS — it's what should
            # have caught a mis-tupled anchor/residual set at the source,
            # instead of surfacing 70 lines later as a Jacobian-identity
            # mismatch (or, worse, silently banking a bad relation when
            # ASSERT_RELATIONS is off).
            let n_missing = (i0 == 0 ? 1 : 0) + (iR == 0 ? 1 : 0) + (iS == 0 ? 1 : 0)
                if n_missing != 1
                    @printf("\n[FATAL n_lp_invariant tid=%d] n_lp==1 branch entered with n_missing=%d (i0=%d iR=%d iS=%d)  P0=%s R=%s S=%s k_cur=%d\n",
                            Threads.threadid(), n_missing, i0, iR, iS,
                            string(P0), string(R), string(S), k_cur)
                    Base.flush(stdout)
                    ccall(:exit, Cvoid, (Cint,), 1)
                end
                if get(pt2idx, lp_pt, 0) != 0
                    @printf("\n[FATAL n_lp_invariant tid=%d] lp_pt=%s selected as the missing atom but IS present in pt2idx (idx=%d) — i0=%d iR=%d iS=%d\n",
                            Threads.threadid(), string(lp_pt), pt2idx[lp_pt], i0, iR, iS)
                    Base.flush(stdout)
                    ccall(:exit, Cvoid, (Cint,), 1)
                end
            end

            empty!(fb_row_scratch)
            # Add ALL anchors from the k-tuple (bounded by k_cur, not the
            # K_MAX-sized cur_anchors buffer)
            for _i in 1:k_cur
                idx = get(pt2idx, cur_anchors[_i], 0)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end
            # Add the residual points
            for idx in (iR, iS)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end

            cur_pt = handle_1lp_affine!(lp_pt, fb_row_scratch, al, be, neg_al, neg_be,
                                         ell, fb, nF_cur, G, T,
                                         alpha_vec, beta_vec, rel_rows, rel_counter, ort, s,
                                         shared_lp1, nothing, nothing,
                                         lp_col, rank_growth, combined_scratch,
                                         iR, iS, R, S, P0, next_anchor_ref;
                                         k_cur=k_cur,
                                         anchors_diag=[cur_anchors[_i] for _i in 1:k_cur],
                                         i0_diag=i0)
            # NOTE (D29 audit): handle_1lp_affine! in fact returns
            # next_anchor_ref[]() unconditionally on every path (store, close,
            # drop-when-full) — see its source, the only `return` is at the
            # bottom of the function after the lock block. It does NOT return
            # the LP point. The comment below (_prev_anchor_was_lp = true) is a
            # pre-existing, separate Seq-3 diagnostic convention that treats this
            # site as "conservatively LP" regardless; left as-is here since that's
            # out of scope for the D29 fix. For D29 specifically we use the true
            # provenance, which is always cursor-derived at this site.
            cur_pt_from_lp = false
            # 1-LP affine: handle_1lp_affine! returns the LP point as the next
            # anchor when it stores/conjugates, otherwise a structured cursor step.
            # We mark LP-derived here since the LP point is the structurally
            # interesting anchor; handle_1lp_affine! emitting structured is less
            # frequent and folding it in is conservative.
            phi_bias_stat._prev_anchor_was_lp = true
            record_conj_deep_opcode!(deep_stat, OPCODE_1LP_AFF, false)
            record_d28_aff_step!(deep_stat, OPCODE_1LP_AFF, lp_pt[1], lp_pt[2], al)
            record_d22_d23_d24_step!(deep_stat)
            record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_OTHER)
            end  # enable_lp1_aff

        elseif n_lp == 2
            # ------------------------------------------------------------------
            #  2-LP affine: exactly two of P0, R, S are not in FB
            # ------------------------------------------------------------------
            if !enable_lp2
                s.hits_skip += 1
                cur_pt = next_anchor()
                cur_pt_from_lp = false  # D29: next_anchor() round-robin advance, not LP-derived
                record_random_anchor!(phi_bias_stat)
                record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
                record_d20_step!(deep_stat, OPCODE_SKIP)
                record_d22_d23_d24_step!(deep_stat)
                record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_OTHER)
            else
                empty!(fb_row_scratch)
                # Add ALL anchors from the k-tuple (bounded by k_cur, not the
                # K_MAX-sized cur_anchors buffer)
                for _i in 1:k_cur
                    idx = get(pt2idx, cur_anchors[_i], 0)
                    idx == 0 && continue
                    fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
                end
                # Add the residual points
                for idx in (iR, iS)
                    idx == 0 && continue
                    fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
                end

                cur_pt = handle_2lp_affine!(i0, iR, iS,
                                             R, S, P0,
                                             fb_row_scratch, neg_al, neg_be,
                                             ell, fb, nF_cur, G, T,
                                             alpha_vec, beta_vec, rel_rows, rel_counter, ort, s,
                                             shared_lp1, nothing,
                                             shared_lp2, shared_lp2_lock,
                                             nothing,
                                             lp_col, max_lp2_nodes, rank_growth,
                                             combined_scratch, next_anchor_ref)
                # D29: handle_2lp_affine! is the ONLY handle_*! that can return
                # a real (non-cursor) point — it returns whichever of P0/R/S is
                # in the FB (i0!=0 → P0, elseif iR!=0 → R, elseif iS!=0 → S),
                # falling back to next_anchor_ref[]() only when none of the three
                # are in the FB. Mirror that exact dispatch here using i0/iR/iS,
                # which are already computed above for this branch.
                cur_pt_from_lp = (i0 != 0) || (iR != 0) || (iS != 0)
                record_conj_deep_opcode!(deep_stat, OPCODE_2LP_AFF, false)
                record_d20_step!(deep_stat, OPCODE_2LP_AFF)
                record_d22_d23_d24_step!(deep_stat)
                record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_OTHER)
            end

        else
            # ------------------------------------------------------------------
            #  3-LP: discard step, advance structured cursor
            # ------------------------------------------------------------------
            s.hits_skip += 1
            # at the hits_total site above; no separate increment needed here.
            cur_pt = next_anchor()
            cur_pt_from_lp = false  # D29: next_anchor() round-robin advance, not LP-derived
            record_random_anchor!(phi_bias_stat)
            record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
            record_d20_step!(deep_stat, OPCODE_SKIP)
            record_d22_d23_d24_step!(deep_stat)
            record_d34_step!(deep_stat, P0[1], p, D34_OUTCOME_OTHER)
        end
    end   # end main walk loop

    # ==========================================================================
    #  Final report
    # ==========================================================================
    elapsed_total = time() - t_start
    if verbose
        exit_reason = (!amortized_precompute && ort_b1(ort) > 0) ? "b₁>0 (kernel found)" :
                      rel_counter[] >= rel_target ? "rel_target reached" :
                                                    "step_cap reached"
        @printf("[thread %2d | DONE | t=%.1fs | exit: %s] raw=%d valid=%d 0lp=%d  1lp_aff(step=%d emit=%d) 1lp_conj(step=%d emit=%d)  2lp_seen=%d 2lp_emit=%d 2lp_cross=%d 2lp_odd=%d 2lp_cap=%d skip=%d  conj_evict=%d  rels_local=%d\n",
                tid, elapsed_total, exit_reason, s.raw_steps, s.hits_total, s.hits_0lp,
                s.hits_lp1,      s.hits_1lp_emit,
                s.hits_lp1_conj, s.hits_1lp_conj_emit,
                s.hits_lp2seen, s.hits_lp2emit, s.hits_lp2_cross, s.hits_lp2_odd,
                s.hits_lp2_cap, s.hits_skip, s.evictions_conj, length(rel_rows))
        @printf("           phi-valid rate: %.4f%%  |  full-rel/valid: %.4f%%  |  steps/full: %.1f\n",
                100.0 * s.hits_total / max(1, s.raw_steps),
                100.0 * s.hits_full  / max(1, s.hits_total),
                s.raw_steps / max(1, s.hits_full))
        # See report_worker_progress for the phi_val vs phi_build distinction.
        # phi_build isolates the actual build_phi_mumford!/step_phi_k! success
        # rate from phase2_alpha_first_seen! gate rejections.
        @printf("           phi-build rate (gates-cleared only): %.4f%%  |  attempts=%d  |  gate-rejected=%d (%.4f%% of raw)\n",
                100.0 * s.hits_total / max(1, s.phi_attempts),
                s.phi_attempts,
                s.raw_steps - s.phi_attempts,
                100.0 * (s.raw_steps - s.phi_attempts) / max(1, s.raw_steps))
        @printf("           smoothness (0-LP 1-LP 2-LP 3-LP): %d %d %d %d\n",
                s.smooth_hist[1], s.smooth_hist[2], s.smooth_hist[3], s.smooth_hist[4])
        let total_conj_close = s.hits_1lp_conj_emit + s.hits_1lp_conj_trivial_same_col +
                                s.hits_1lp_conj_trivial_zero_dal + s.hits_1lp_conj_trivial_dup +
                                s.hits_1lp_conj_row_missing
            @printf("           1lp_conj trivial breakdown: same_col=%d (%.1f%%)  zero_dal=%d (%.1f%%)  dup=%d (%.1f%%)  row_missing=%d (%.1f%%)  useful=%d (%.1f%%) of %d closes\n",
                    s.hits_1lp_conj_trivial_same_col,
                    100.0 * s.hits_1lp_conj_trivial_same_col / max(1, total_conj_close),
                    s.hits_1lp_conj_trivial_zero_dal,
                    100.0 * s.hits_1lp_conj_trivial_zero_dal / max(1, total_conj_close),
                    s.hits_1lp_conj_trivial_dup,
                    100.0 * s.hits_1lp_conj_trivial_dup / max(1, total_conj_close),
                    s.hits_1lp_conj_row_missing,
                    100.0 * s.hits_1lp_conj_row_missing / max(1, total_conj_close),
                    s.hits_1lp_conj_emit,
                    100.0 * s.hits_1lp_conj_emit / max(1, total_conj_close),
                    total_conj_close)
            if s.hits_1lp_conj_trivial_same_col > 0
                @printf("             same_col sub-breakdown: attractor_exact(Δα=0)=%d (%.1f%%)  birthday_filtered(Δα≠0)=%d (%.1f%%) of same_col probed=%d\n",
                        s.hits_1lp_conj_attractor_exact,
                        100.0 * s.hits_1lp_conj_attractor_exact   / max(1, s.hits_1lp_conj_attractor_exact + s.hits_1lp_conj_attractor_birthday),
                        s.hits_1lp_conj_attractor_birthday,
                        100.0 * s.hits_1lp_conj_attractor_birthday / max(1, s.hits_1lp_conj_attractor_exact + s.hits_1lp_conj_attractor_birthday),
                        s.hits_1lp_conj_attractor_exact + s.hits_1lp_conj_attractor_birthday)
            end
        end
        if length(rank_growth) >= 2
            gaps = [rank_growth[i][1] - rank_growth[i-1][1]
                    for i in 2:min(10, length(rank_growth))]
            @printf("           first-emission raw step gaps (up to 10): %s\n",
                    join(string.(gaps), " "))
        end
        # Basin steer diagnostic report
        flush(stdout)
    end

    # Flush any open D22/D25 burst window so the last burst is counted even if it
    # never reached the inter-burst gap threshold before the walk ended.
    flush_d22_open_burst!(deep_stat)

    # If a carry-in ConjDeepStat was provided (e.g. from a prior precompute walk
    # on this thread), merge its D16 histograms into our own so the report covers
    # all emissions across both walks.  Other fields (ring buffer, opcode log, etc.)
    # are not merged — they are walk-phase-specific.
    if carry_in_deep_stat !== nothing
        cin = carry_in_deep_stat
        for (k, v) in cin.d16_preburst_hist
            deep_stat.d16_preburst_hist[k] = get(deep_stat.d16_preburst_hist, k, 0) + v
        end
        for (k, v) in cin.d16_baseline_hist
            deep_stat.d16_baseline_hist[k] = get(deep_stat.d16_baseline_hist, k, 0) + v
        end
        deep_stat.d16_n_preburst += cin.d16_n_preburst
        deep_stat.d16_n_baseline += cin.d16_n_baseline
    end

    return (rel_rows      = rel_rows,
            alpha_vec     = alpha_vec,
            beta_vec      = beta_vec,
            phi_attempts  = s.phi_attempts,
            hits_total    = s.hits_total,
            hits_full     = s.hits_full,
            hits_0lp      = s.hits_0lp,
            hits_lp1      = s.hits_lp1,
            hits_1lp_emit = s.hits_1lp_emit,
            hits_lp1_conj      = s.hits_lp1_conj,
            hits_1lp_conj_emit = s.hits_1lp_conj_emit,
            hits_1lp_conj_trivial_same_col  = s.hits_1lp_conj_trivial_same_col,
            hits_1lp_conj_trivial_zero_dal  = s.hits_1lp_conj_trivial_zero_dal,
            hits_1lp_conj_trivial_dup       = s.hits_1lp_conj_trivial_dup,
            hits_1lp_conj_row_missing       = s.hits_1lp_conj_row_missing,
            hits_1lp_conj_attractor_exact   = s.hits_1lp_conj_attractor_exact,
            hits_1lp_conj_attractor_birthday= s.hits_1lp_conj_attractor_birthday,
            hits_lp2seen  = s.hits_lp2seen,
            hits_lp2emit  = s.hits_lp2emit,
            hits_lp2_cross= s.hits_lp2_cross,
            hits_lp2_odd  = s.hits_lp2_odd,
            hits_lp2_cap  = s.hits_lp2_cap,
            hits_skip     = s.hits_skip,
            evictions_conj= s.evictions_conj,
            sample_rels   = sample_phase2_rels,
            total_steps   = s.raw_steps,
            smooth_hist   = s.smooth_hist,
            rank_growth   = rank_growth,
            lp_col        = lp_col,
            phi_bias_stat = phi_bias_stat,
            basin_hot_anchors = Int[],
            basin_steers_fired = 0,
            basin_steers_hit   = 0,
            lp1_conj_mean_gap_steps = begin
                arrivals = phi_bias_stat.lp1_conj_arrivals
                n = length(arrivals)
                if n < 2
                    0.0
                else
                    arr = sort(copy(arrivals))
                    gap_sum = 0.0
                    @inbounds for i in 2:n
                        gap_sum += arr[i] - arr[i-1]
                    end
                    gap_sum / (n - 1)
                end
            end,
            deep_stat = deep_stat,
            d38_stat = d38_stat)
end


### from gemini:
@inline function handle_2lp_conj!(
        P0                ::NTuple{2,Int},
        lp_key            ::NTuple{4,Int},
        neg_al         ::Int,
        neg_be         ::Int,
        ell            ::BigInt,
        fb                ::Vector{NTuple{2,Int}},
        nF_cur            ::Int,
        G                 ::Div2,
        T                 ::Div2,
        alpha_vec         ::Vector{BigInt},
        beta_vec          ::Vector{BigInt},
        rel_rows          ::Vector{Dict{Int,Int}},
        rel_counter       ::Threads.Atomic{Int},
        ort               ::OnlineRankTracker,
        s                 ::WorkerStats,
        shared_lp1        ::ShardedLP1Affine,
        shared_lp1_lock   ::Nothing,           # unused sentinel
        shared_lp_doubled ::Nothing,           # unused sentinel; inside ShardedLP1Affine
        shared_lp2_conj   ::LP2ConjGraph,
        shared_lp2_conj_lock::ReentrantLock,
        max_lp2_conj_nodes::Int,
        rank_growth       ::Vector{Tuple{Int,Int}},
        combined_scratch  ::ThreadScratchpad{<:Any},
        next_anchor_ref   ::Ref{Function})::NTuple{2,Int}

    s.hits_lp2seen += 1

    emitted_conj = nothing
    if lp2_graph_node_count(shared_lp2_conj) >= max_lp2_conj_nodes
        s.hits_lp2_cap += 1
    else
        lock(shared_lp2_conj_lock)
        try
            if lp2_graph_node_count(shared_lp2_conj) < max_lp2_conj_nodes
                emitted_conj = lp2c_insert_edge!(shared_lp2_conj, P0, lp_key,
                                                 Dict{Int,Int}(), neg_al, neg_be, Int(ell))
            else
                s.hits_lp2_cap += 1
            end
        finally
            unlock(shared_lp2_conj_lock)
        end
    end

    emitted_conj === nothing && return next_anchor_ref[]()

    if emitted_conj.type === :even_cycle
        # Even cycle → full FB relation directly.
        push!(alpha_vec, emitted_conj.alpha); push!(beta_vec, emitted_conj.beta)
        push!(rel_rows, emitted_conj.row)
        ort_add_row!(ort, emitted_conj.row)
        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
            push!(rank_growth, (s.raw_steps, length(rel_rows)))
        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
        Threads.atomic_add!(rel_counter, 1)
        if ASSERT_RELATIONS
            @assert check_relation_principal(emitted_conj.row, emitted_conj.alpha,
                                             emitted_conj.beta, "α", fb, G, T; tag="QLP-CONJ-CYCLE")
        end
        return next_anchor_ref[]()

    elseif emitted_conj.type === :odd_cycle
        # Odd cycle → the root contributes 2·atom(root) to the divisor sum.
        s.hits_lp2_odd += 1
        root_key = emitted_conj.root
        if root_key isa NTuple{2,Int}
            root_affine = root_key::NTuple{2,Int}
            si_root2 = lp1a_shard_idx(root_affine)
            lock(shared_lp1.locks[si_root2])
            try
                prev_doubled2 = doubled_pop!(shared_lp1, root_affine)
                if prev_doubled2 !== nothing
                    # A previous odd cycle already stored 2·atom(root).
                    # Combine: subtract the two doubled rows.
                    prev_row, prev_al, prev_be = prev_doubled2
                    combined    = copy(emitted_conj.row)
                    for (j, v) in prev_row
                        nv = get(combined, j, 0) - v
                        nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                    end
                    combined_al = mod(emitted_conj.alpha - prev_al, ell)
                    combined_be = mod(emitted_conj.beta  - prev_be, ell)
                    if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                        push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
                        push!(rel_rows, combined)
                        ort_add_row!(ort, combined)
                        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                            push!(rank_growth, (s.raw_steps, length(rel_rows)))
                        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        Threads.atomic_add!(rel_counter, 1)
                    end
                else
                    # Park: store 2·atom(root) for a future 1-LP entry to consume.
                    if lp1a_length_doubled(shared_lp1) <= MAX_LP1_DOUBLED_ENTRIES
                        doubled_set!(shared_lp1, root_affine, (emitted_conj.row, Int(emitted_conj.alpha), Int(emitted_conj.beta)))
                        if _try_lp1_doubled_cross_close_inner!(
                                root_affine, shared_lp1.lp1_shards[si_root2], shared_lp1.doubled_shards[si_root2],
                                ell, alpha_vec, beta_vec, rel_rows, rank_growth, s.raw_steps,
                                rel_counter, ort, G, T, fb)
                            s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        end
                    end
                end  # else (haskey branch)
            finally
                unlock(shared_lp1.locks[si_root2])
            end
        end
        return next_anchor_ref[]()
    end

    return next_anchor_ref[]()
end
