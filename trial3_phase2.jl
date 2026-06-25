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
    combined_scratch::ThreadScratchpad,     # Updated type signature to match the caller #combined_scratch  ::Dict{Int,Int},
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
            @assert false "try_lp1_doubled_cross_close!: principal divisor check failed"
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
                                shared_lp1_conj::Union{ShardedLP1Conj{<:Any}, LP1ConjLSM{<:Any}})
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
    @printf("           1lp_conj closure rate: %.3f%%  |  1lp_aff closure rate: %.3f%%  |  conj_cap_drops=%d\n",
            100.0 * s.hits_1lp_conj_emit / max(1, s.hits_lp1_conj),
            100.0 * s.hits_1lp_emit      / max(1, s.hits_lp1),
            s.evictions_conj)
    let total_conj_close = s.hits_1lp_conj_emit + s.hits_1lp_conj_trivial_same_col +
                            s.hits_1lp_conj_trivial_zero_dal + s.hits_1lp_conj_trivial_dup
        @printf("           1lp_conj trivial breakdown: same_col=%d (%.1f%%)  zero_dal=%d (%.1f%%)  dup=%d (%.1f%%)  useful=%d (%.1f%%) of %d closes\n",
                s.hits_1lp_conj_trivial_same_col,
                100.0 * s.hits_1lp_conj_trivial_same_col / max(1, total_conj_close),
                s.hits_1lp_conj_trivial_zero_dal,
                100.0 * s.hits_1lp_conj_trivial_zero_dal / max(1, total_conj_close),
                s.hits_1lp_conj_trivial_dup,
                100.0 * s.hits_1lp_conj_trivial_dup / max(1, total_conj_close),
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
        if shared_lp1_conj isa LP1ConjLSM
            # Emission rate for birthday estimator: LP1-conj closures per second.
            r_conj = s.hits_1lp_conj_emit / max(1.0, elapsed)
            lsm_flush_stats(shared_lp1_conj)
            lsm_mem_report(shared_lp1_conj;
                           label  = "thread $tid (LSM)",
                           peers  = false)
            lsm_bday_report(shared_lp1_conj, p, r_conj)
        end
    end
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
# version.  Returns (val, is_same_partial) matching the LSM signature so
# handle_1lp_conj! can treat both backends uniformly.
#
# Same-partial: all three of (i0, neg_al, neg_be) match the stored entry —
# this is a genuine repeat of the same walk partial and carries no new
# information.  Leave the stored entry in place and discard the new arrival
# so it survives for a future cross-col visitor.
# Any other collision (i0 differs, or same i0 but different α/β) is a valid
# closure: different walk positions hit the same residual key.
@inline function conj_insert_or_pop!(sc::ShardedLP1Conj{V}, si::Int,
                                      key::CanonicalLP1Key, val::V
                                     )::Tuple{Union{V,Nothing}, Bool} where V
    lock(sc.locks[si]) do
        sh   = sc.shards[si]
        slot = _conj_find(sh, key)
        if slot != 0
            v = @inbounds sh.vals[slot]
            if Int(v.i0) == Int(val.i0) &&
               Int(v.neg_al) == Int(val.neg_al) &&
               _conj_prev_be(v) == _conj_prev_be(val)
                # Exact same partial (same anchor col, same α, same β): leave in place, discard.
                return (nothing, true)
            end
            # Different partial: valid closure regardless of whether i0 matches.
            _conj_delete_slot!(sh, slot)
            (v, false)
        elseif sh.count < sh.max_entries
            _conj_insert!(sh, key, val)
            (nothing, false)
        else
            # At cap: drop silently.
            (nothing, false)
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
        @assert check_relation_principal(fb_row, neg_al, neg_be, "α", fb, G, T; tag="0LP-EMIT")
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
        shared_lp1     ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        shared_lp1_lock::ReentrantLock,
        shared_lp_doubled::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        lp_col         ::LPResidualCollector,
        rank_growth    ::Vector{Tuple{Int,Int}},
        combined_scratch::ThreadScratchpad,     # Updated type signature to match the caller #combined_scratch  ::Dict{Int,Int},
        iR             ::Int,
        iS             ::Int,
        R              ::NTuple{2,Int},
        S              ::NTuple{2,Int},
        P0             ::NTuple{2,Int},
        next_anchor_ref::Ref{Function})::NTuple{2,Int}

    record_lp1!(lp_col, lp_pt, Int(al), Int(be), s.raw_steps)

    closed = false
    lock(shared_lp1_lock)
    try
        if haskey(shared_lp1, lp_pt)
            # --- Close against stored entry ---
            prev_row, prev_al, prev_be, prev_step = shared_lp1[lp_pt]
            combined    = sparse_copy!(combined_scratch, fb_row)
            lp2_subtract_rows(combined, prev_row)
            ellI_loc    = Int(ell)
            combined_al = mod(neg_al - prev_al, ellI_loc)
            combined_be = mod(neg_be - prev_be, ellI_loc)
            delete!(shared_lp1, lp_pt)
            record_closure!(lp_col, s.raw_steps, prev_step)

            if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                if ASSERT_RELATIONS
                    @assert check_relation_principal(combined, combined_al, combined_be,
                                                     "α", fb, G, T; tag="1LP-CLOSE")
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
                @assert check_lp1_stored(lp_pt, fb_row, neg_al, neg_be, fb, G, T; tag="1LP-STORE")
            end
            # Skip (do not store) if the table is full.  Evicting a random
            # existing entry is counter-productive: it destroys an unmatched
            # entry before it can close, causes correlated re-generation of the
            # same keys, and produces duplicate relations.  A full table of
            # stable unmatched entries is strictly better — closures drain it
            # naturally.
            if length(shared_lp1) >= MAX_LP1_ENTRIES
                # drop silently; doubled cross-close check is skipped too
            else
                shared_lp1[lp_pt] = (copy(fb_row), neg_al, neg_be, s.raw_steps)
                # Check whether the complementary doubled entry already exists.
                if try_lp1_doubled_cross_close!(lp_pt, shared_lp1, shared_lp_doubled,
                                                ell, alpha_vec, beta_vec, rel_rows,
                                                rank_growth, s.raw_steps, rel_counter, ort,
                                                G, T, combined_scratch, fb)
                    s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1; closed = true
                end
            end
        end
    finally
        unlock(shared_lp1_lock)
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
@inline function handle_1lp_conj!(
        lp_key          ::CanonicalLP1Key,
        i0              ::Int,
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
        shared_lp1_conj ::Union{ShardedLP1Conj{V}, LP1ConjLSM{V}},
        rank_growth     ::Vector{Tuple{Int,Int}},
        combined_scratch::ThreadScratchpad, 
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
    val = _conj_make_val(V, UInt16(i0), UInt32(s.raw_steps), UInt64(neg_al), UInt64(neg_be))
    prev, is_same_partial = conj_insert_or_pop!(shared_lp1_conj, si, lp_key, val)

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

    if prev === nothing
        record_conj_deep_miss!(deep_stat, lp_key, s.raw_steps, al_cur, px_anchor, a_raw, py_anchor)
    end

    if prev !== nothing
        # --- Close against stored entry ---
        v        = prev
        prev_col = Int(v.i0)
        prev_al  = Int(v.neg_al)
        prev_be  = _conj_prev_be(v)

        if neg_al == 0
            throw(ErrorException("handle_1lp_conj!: neg_al==0 (alpha==ell) at tid=$(Threads.threadid())"))
        end
        if prev_al == 0
            throw(ErrorException("handle_1lp_conj!: stored prev_al==0 (alpha==ell) at tid=$(Threads.threadid())"))
        end

        combined_al = mod(neg_al - prev_al, Int(ell))
        combined_be = mod(neg_be - prev_be, Int(ell))

        if i0 == prev_col
            throw(ErrorException(
                "handle_1lp_conj!: i0==prev_col=$i0 reached close path — same-partial leak " *
                "(lp_key=$lp_key neg_al=$neg_al prev_al=$prev_al)"
            ))
        end

        if combined_al == 0 && combined_be == 0
            s.hits_1lp_conj_trivial_zero_dal += 1
            return next_anchor_ref[]()
        end

        if emitted_conj_rels !== nothing
            lo_idx   = min(i0, prev_col)
            hi_idx   = max(i0, prev_col)
            canon_al = i0 <= prev_col ? combined_al : mod(Int(ell) - combined_al, Int(ell))
            canon_be = i0 <= prev_col ? combined_be : mod(Int(ell) - combined_be, Int(ell))
            rel_key  = (lo_idx, hi_idx, canon_al, canon_be)
            if rel_key in emitted_conj_rels
                s.hits_1lp_conj_trivial_dup += 1
                return next_anchor_ref[]()
            end
            push!(emitted_conj_rels, rel_key)
        end

        empty!(combined_scratch)
        combined_scratch[i0]       = 1
        combined_scratch[prev_col] = -1

        if ASSERT_RELATIONS
            ok = check_relation_principal(combined_scratch, combined_al, combined_be,
                                          "α", fb, G, T; tag="RS-CONJ-CLOSE")
            if !ok
                @printf("[RS-CONJ-CLOSE DIAG tid=%d] i0=%d prev_col=%d\n",
                        Threads.threadid(), i0, prev_col)
                @printf("[RS-CONJ-CLOSE DIAG]  neg_al=%s neg_be=%s prev_al=%s prev_be=%s\n",
                        string(neg_al), string(neg_be), string(prev_al), string(prev_be))
                @printf("[RS-CONJ-CLOSE DIAG]  lp_key=(c0=%d,c1=%d,v0=%d,v1=%d) i0=%d\n",
                        lp_key..., i0)
                throw(ErrorException("Conjugate-pair 1-LP closure failed principal divisor check"))
            end
        end

        push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
        push!(rel_rows, copy(combined_scratch))
        ort_add_row!(ort, combined_scratch)
        
        if length(rank_growth) < MAX_RANK_GROWTH_SAMPLES
            push!(rank_growth, (s.raw_steps, length(rel_rows)))
        end

        s.hits_full += 1; s.hits_1lp_conj_emit += 1; s.rel_local += 1
        Threads.atomic_add!(rel_counter, 1)

        # Unpack lp_key limbs manually via bit shifts to prevent scalar-iteration overflow
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
                px_anchor, py_anchor, # FIX: Pass valid current anchor state instead of corrupted fb reads
                combined_al, combined_be,
                al_cur, px_anchor, py_anchor, a_raw, a_bucket)
        end

        record_lp1_conj_hit!(phi_bias_stat, s.raw_steps, lp_key, a_bucket)
        record_conj_deep_step!(deep_stat, lp_key, a_bucket, s.raw_steps, true, al_cur, px_anchor,
                               Int(v.store_step), i0)
        record_d25_closure!(deep_stat, al_cur, px_anchor, Int(v.neg_al),
                            s.raw_steps - Int(v.store_step), Int(ell))
        
        # FIX: For general walks, replace direct fb[prev_col] reads with the unpacked Mumford u0 component 
        record_d37_closure!(deep_stat, px_anchor, u0_limb, al_cur, s.raw_steps)
        record_d39_closure!(deep_stat, neg_al, px_anchor, combined_al, step_phase)
        record_d16_emission!(deep_stat, lp_key, s.raw_steps, i0)
        record_d20_emission!(deep_stat)
        record_d19_closure!(deep_stat, i0, prev_col, combined_al, combined_be)
        
        # FIX: Spatial ACF diagnostics use the extracted Mumford coefficients directly
        record_d35_closure!(deep_stat, combined_al, combined_be,
                            u0_limb, u1_limb, u0_limb, u1_limb)
        record_d30_closure!(deep_stat, u0_limb, u0_limb)
        
        record_d36_closure!(deep_stat, i0, prev_col)
        record_d22_d23_d24_emission!(deep_stat, s.raw_steps, _deep_bucket(lp_key), a_bucket)
        
        for _ in 1:post_conj_stride
            next_anchor_ref[]()
        end
        return next_anchor_ref[]()
    end

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
        shared_lp1     ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        shared_lp1_lock::ReentrantLock,
        shared_lp2     ::LP2Graph,
        shared_lp2_lock::ReentrantLock,
        shared_lp_doubled::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        lp_col         ::LPResidualCollector,
        max_lp2_nodes  ::Int,
        rank_growth    ::Vector{Tuple{Int,Int}},
        combined_scratch::ThreadScratchpad,     # Updated type signature to match the caller #combined_scratch  ::Dict{Int,Int},
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
            lock(shared_lp1_lock)
            try
                root = emitted_rel.root
                if haskey(shared_lp_doubled, root)
                    prev_row, prev_al, prev_be = shared_lp_doubled[root]
                    combined    = sparse_copy!(combined_scratch, emitted_rel.row)
                    for (j, v) in prev_row
                        nv = get(combined, j, 0) - v
                        nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                    end
                    combined_al = mod(emitted_rel.alpha - prev_al, ell)
                    combined_be = mod(emitted_rel.beta  - prev_be, ell)
                    delete!(shared_lp_doubled, root)
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
                    shared_lp_doubled[root] = (emitted_rel.row, Int(emitted_rel.alpha), Int(emitted_rel.beta))
                    if length(shared_lp_doubled) > MAX_LP1_DOUBLED_ENTRIES
                        for evict_key in keys(shared_lp_doubled)
                            delete!(shared_lp_doubled, evict_key); break
                        end
                    end
                    if try_lp1_doubled_cross_close!(root, shared_lp1, shared_lp_doubled,
                                                    ell, alpha_vec, beta_vec, rel_rows,
                                                    rank_growth, s.raw_steps, rel_counter,
                                                    ort, G, T, combined_scratch, fb)
                        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                    end
                end
            finally
                unlock(shared_lp1_lock)
            end
        end
    end   # end LP2 graph insertion block

    # --- Cross-close with existing 1-LP entries ---
    lock(shared_lp1_lock)
    try
        for (lp_known, lp_other) in ((lp2_a, lp2_b), (lp2_b, lp2_a))
            haskey(shared_lp1, lp_known) || continue

            r_known, na_known, nb_known, _step_known = shared_lp1[lp_known]
            new_row    = copy(fb_row_scratch)
            for (j, v) in r_known
                nv = get(new_row, j, 0) - v
                nv == 0 ? delete!(new_row, j) : (new_row[j] = nv)
            end
            ellI_loc   = Int(ell)
            new_neg_al = mod(neg_al - na_known, ellI_loc)
            new_neg_be = mod(neg_be - nb_known, ellI_loc)

            s.hits_lp2_cross += 1

            if haskey(shared_lp1, lp_other)
                prev_row, prev_al, prev_be, prev_step = shared_lp1[lp_other]
                combined    = copy(new_row)
                lp2_subtract_rows(combined, prev_row)
                combined_al = mod(new_neg_al - prev_al, ellI_loc)
                combined_be = mod(new_neg_be - prev_be, ellI_loc)
                delete!(shared_lp1, lp_other)
                record_closure!(lp_col, s.raw_steps, prev_step)
                if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                    if ASSERT_RELATIONS
                        @assert check_relation_principal(combined, combined_al, combined_be,
                                                         "α", fb, G, T; tag="2LP-CROSS-CLOSE")
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
                    @assert ok "2-LP cross-store: derived 1-LP row inconsistent"
                end
                if length(shared_lp1) >= MAX_LP1_ENTRIES
                    for evict_key in keys(shared_lp1)
                        delete!(shared_lp1, evict_key); break
                    end
                end
                shared_lp1[lp_other] = (new_row, new_neg_al, new_neg_be, s.raw_steps)
                if try_lp1_doubled_cross_close!(lp_other, shared_lp1, shared_lp_doubled,
                                                ell, alpha_vec, beta_vec, rel_rows,
                                                rank_growth, s.raw_steps, rel_counter,
                                                ort, G, T, combined_scratch, fb)
                    s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                end
            end
            break   # only act on the first match
        end
    finally
        unlock(shared_lp1_lock)
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
#  Global alpha no-repeat filter — fixed-size Bloom filter (128 MB).
#
#  Previously this was a Vector{UInt8} of length ell+1, which cost ~4.88 GB
#  for ell≈4.88e9.  Replaced with a fixed 128 MB Bloom filter (3 hashes,
#  ~1.07 billion bits).
#
#  At 128 MB and 150M walk steps out of ell≈4.88e9 possible alphas, the
#  false-positive rate per query is negligible (~10⁻⁸ with 3 independent
#  hashes), meaning a negligible fraction of alphas get silently skipped a
#  second time by a spurious "already seen" report.  This is a correctness
#  non-issue: the gate is a performance hint, not a correctness gate — a
#  false positive just means two threads both skip the same alpha once, losing
#  at most one LP event.
#
#  The filter is lockless: bits are only ever set, never cleared, so racy
#  concurrent writes produce benign spurious false positives at worst (two
#  threads both believe they are "first" for the same alpha and both process
#  it once — identical to the behaviour before the gate existed).
#
#  Resetting between runs: call phase2_alpha_bloom_reset!() before each walk.
# ---------------------------------------------------------------------------
const ALPHA_BLOOM_MB    = 128
const ALPHA_BLOOM_BITS  = ALPHA_BLOOM_MB * 1024 * 1024 * 8   # 1,073,741,824 bits
const ALPHA_BLOOM_WORDS = ALPHA_BLOOM_BITS ÷ 64               # 16,777,216 UInt64 words
const PHASE2_ALPHA_BLOOM = zeros(UInt64, ALPHA_BLOOM_WORDS)   # 128 MB, allocated once

function phase2_alpha_bloom_reset!()
    fill!(PHASE2_ALPHA_BLOOM, UInt64(0))
    nothing
end

@inline function phase2_alpha_first_seen!(alpha::Int, ellI::Int)::Bool
    # Three independent hashes of alpha into [1, ALPHA_BLOOM_BITS].
    # Multiplicative hashing with distinct coprime constants (same scheme as
    # BloomFilter in lp1_conj_lsm_bloom.jl for consistency).
    h1 = UInt64(alpha) * 0x9e3779b97f4a7c15
    h2 = UInt64(alpha) * 0x6c62272e07bb0142
    h3 = h1 ⊻ (h2 >> 17)
    b1 = Int(h1 % UInt64(ALPHA_BLOOM_BITS)) + 1
    b2 = Int(h2 % UInt64(ALPHA_BLOOM_BITS)) + 1
    b3 = Int(h3 % UInt64(ALPHA_BLOOM_BITS)) + 1
    words = PHASE2_ALPHA_BLOOM
    @inbounds begin
        w1, r1 = divrem(b1 - 1, 64)
        w2, r2 = divrem(b2 - 1, 64)
        w3, r3 = divrem(b3 - 1, 64)
        # Check: if all three bits already set, report "seen".
        already = ((words[w1+1] >> r1) & UInt64(1)) != 0 &&
                  ((words[w2+1] >> r2) & UInt64(1)) != 0 &&
                  ((words[w3+1] >> r3) & UInt64(1)) != 0
        already && return false
        # Set all three bits (racy writes are safe: bits only go 0→1).
        words[w1+1] |= UInt64(1) << r1
        words[w2+1] |= UInt64(1) << r2
        words[w3+1] |= UInt64(1) << r3
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
                       shared_lp1      ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
                       shared_lp1_lock ::ReentrantLock,
                       shared_lp2      ::LP2Graph,
                       shared_lp2_lock ::ReentrantLock,
                       shared_lp_doubled::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
                       shared_lp1_conj ::Union{ShardedLP1Conj{<:Any}, LP1ConjLSM{<:Any}},
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
                       d38_stat          ::Union{D38Stat,Nothing} = nothing)

    nF_cur   = length(fb)
    N_STEPS  = length(step_D)
    tid      = Threads.threadid()
    t_start  = time()

    ellI = Int(ell)
    step_a_i = Vector{Int}(undef, length(step_a))
    step_b_i = Vector{Int}(undef, length(step_b))
    @inbounds for i in eachindex(step_a)
        step_a_i[i] = Int(step_a[i])
        step_b_i[i] = Int(step_b[i])
    end

    # ==========================================================================
    #  Anchor cursor — contiguous per-thread slice of the factor base.
    #
    #  Each thread owns an exclusive chunk [anchor_start, anchor_end] of fb[].
    #  This ensures no two threads ever share an i0 value, making the
    #  (lp_key, i0, neg_al, neg_be) partial triple globally unique by
    #  construction — threads cannot produce same-partial collisions with each
    #  other, only within their own walk (which alpha/beta cycling can cause).
    # ==========================================================================
    # Balanced partition: every thread gets either ⌊nF_cur/n_workers⌋ or
    # ⌊nF_cur/n_workers⌋+1 FB elements.  The first `r` threads each get one
    # extra element so that all nF_cur elements are covered with no thread idle
    # (as long as n_workers ≤ nF_cur).  This replaces the old cld-based fixed
    # chunk, which left up to (n_workers-1) trailing threads with empty ranges
    # whenever nF_cur % n_workers != 0.
    #
    # n_workers is passed in from the coordinator rather than sampled here to
    # avoid the Julia quirk where Threads.nthreads() can return a different value
    # inside a @spawn'd task than from the main thread (e.g. 32 vs 33 when the
    # main thread is tid=1 and workers are tid=2..33), which causes the last
    # worker's anchor_start to exceed nF_cur and fire a spurious IDLE.
    nt_            = n_workers
    base_chunk_    = nF_cur ÷ nt_           # minimum slice width
    r_             = nF_cur % nt_            # first `r_` threads get one extra
    anchor_start   = (tid - 1) * base_chunk_ + min(tid - 1, r_) + 1
    anchor_end     = anchor_start + base_chunk_ - 1 + (tid <= r_ ? 1 : 0)
    # Guard: excess threads (nthreads > nF_cur) still get an empty range and
    # immediately idle, which is correct and preserves i0 exclusivity.
    if anchor_start > nF_cur
        # This thread has no FB elements to walk.  Return empty results immediately
        # rather than wrapping with mod1 (which aliases i0 ranges and produces
        # spurious same_col=100% on the wrapped threads).
        verbose && @printf("[thread %2d | IDLE | no FB slice (nF_cur=%d < chunk start %d)]\n",
                           tid, nF_cur, anchor_start)
        return (rel_rows      = Dict{Int,Int}[],
                alpha_vec     = BigInt[],
                beta_vec      = BigInt[],
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
    anchor_cursor = anchor_start

    # ==========================================================================
    #  Anchor tuple cursor — round-robin over all multiset k-tuples drawn from
    #  this thread's FB slice, in lexicographic index order.
    #
    #  For anchor_tuple_size == 1 (classic): identical to the old behaviour —
    #  we just cycle through fb[anchor_start..anchor_end] one point at a time.
    #
    #  For anchor_tuple_size == K > 1: we enumerate all K-element multiset
    #  selections from {anchor_start..anchor_end} (i.e. combinations with
    #  repetition, ordered by lex index).  A K-tuple with a repeated element
    #  requests a tangency (order-2 vanishing) at that point; `build_phi_general`
    #  handles the derivative row automatically.
    #
    #  State: a length-K index vector `tuple_cursor[1..K]` where each entry is
    #  an FB index in [anchor_start, anchor_end], non-decreasing.  Advancing
    #  increments the last position and carries like a restricted odometer.
    #
    #  Total tuple count = C(slice_size + K - 1, K)  (stars-and-bars).
    #  For K=1 this is exactly slice_size, recovering the old cycle.
    # ==========================================================================
    slice_size   = anchor_end - anchor_start + 1
    K_anc        = anchor_tuple_size

    # Initialise tuple cursor to (anchor_start, anchor_start, ...) — the
    # lexicographically smallest K-tuple.
    tuple_cursor = fill(anchor_start, K_anc)

    # Advance tuple_cursor by one step and return the current tuple as a
    # Vector{NTuple{2,Int}}.  Thread-local, no allocation on the fast path
    # (we reuse `cur_anchors`).
    cur_anchors  = Vector{NTuple{2,Int}}(undef, K_anc)

    @inline function next_anchor_tuple()
        # Snapshot current cursor into cur_anchors
        @inbounds for i in 1:K_anc
            cur_anchors[i] = fb[tuple_cursor[i]]
        end
        # Advance: increment last position, carry right-to-left.
        # Each position tc[i] ∈ [anchor_start, anchor_end], and must satisfy
        # tc[i] >= tc[i-1] (non-decreasing).  The carry bound for position i
        # is anchor_end (it can go up to anchor_end regardless of position).
        @inbounds begin
            pos = K_anc
            while pos >= 1
                if tuple_cursor[pos] < anchor_end
                    tuple_cursor[pos] += 1
                    # Reset all positions to the right to the new value (non-decreasing)
                    for j in pos+1:K_anc
                        tuple_cursor[j] = tuple_cursor[pos]
                    end
                    break
                end
                pos -= 1
            end
            if pos == 0
                # Wrap: reset to all-anchor_start
                fill!(tuple_cursor, anchor_start)
            end
        end
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
    #  rate independent of how "interesting" the (i0,prev_col) pair is.
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

    @inline function next_alpha_beta()
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
        return a, b
    end

    # --- Walk state ---
    # For K_anc == 1: cur_pt is the sole anchor (classic behaviour).
    # For K_anc >  1: cur_anchors holds the full K-tuple; cur_pt = cur_anchors[1]
    #                 is used for diagnostics, pt2idx lookups, and the handle_*
    #                 LP helpers (which remain single-anchor).
    _init_anchors = next_anchor_tuple()
    cur_pt        = _init_anchors[1]
    cur_anchors   = copy(_init_anchors)   # mutable working copy for multi-anchor steps
    # D29 artifact filter: tracks whether cur_pt's MOST RECENT assignment came
    # from a genuine LP resolution (handle_1lp_affine!/handle_1lp_conj!/
    # handle_2lp_affine! storing or closing) vs a bare next_anchor() round-robin
    # advance. Read at next iteration's record_d29_step! call (it describes P0,
    # i.e. last step's cur_pt), then overwritten by this step's own assignment.
    # Initial value is false: the seed cur_pt came from next_anchor() above.
    cur_pt_from_lp = false
    alpha_cur, beta_cur = next_alpha_beta()
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
    combined_scratch = ThreadScratchpad()

    # Initialize a fast, thread-local RNG for step selection.
    # Xoshiro has a 2^256 period and is seeded randomly per thread,
    # so threads take fully independent paths through the step table.
    rng = Random.Xoshiro()

    # --- Conj relation dedup filter ---
    # Tracks (lo_idx, hi_idx, combined_al, combined_be) of every conj relation
    # already emitted by this thread.  Prevents the repeated-closure pathology
    # where the same deterministic step-table delta regenerates the same key pair
    # with the same alpha difference, producing an identical weight-2 row.
    # Key is canonical: lo=min(i0,prev_col) so fb[i]-fb[j] and fb[j]-fb[i]
    # (which differ only by sign on the row and negation of combined_al) are
    # treated as the same relation.
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
    while rel_counter[] < rel_target && s.raw_steps < step_cap && (amortized_precompute || ort_b1(ort) == 0)
        s.raw_steps += 1

        # --- PRNG step selection ---
        # Replace the previous hash(D_cur.u[1])-based selection, which caused
        # the walk to degenerate into a closed attractor cycle (D_{n+1} = f(D_n)
        # is a pure function → Birthday Paradox guarantees a short cycle).
        # Xoshiro period is 2^256; each thread is independently seeded, so
        # threads take divergent paths with no lockstep duplicates.
        si = rand(rng, 1:N_STEPS)
        D_cur     = jac_add(jac_add(D_cur, step_D[si]), DRIFT_D)
        alpha_cur = mod(alpha_cur + step_a_i[si] + DELTA_A, ellI)
        beta_cur  = beta_zero ? 0 : mod(beta_cur + step_b_i[si] + DELTA_B, ellI)

        # Early no-repeat gate: once a residue has been consumed by any thread,
        # skip the rest of the expensive gate/φ/LP work for that alpha.
        phase2_alpha_first_seen!(alpha_cur, ellI) || continue

        # --- Gate 1: D must be a degree-2 divisor (generic Jacobian element) ---
        fp3_deg(D_cur.u) != 2 && continue

        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]
        px, py = cur_pt   # cur_pt is set by the previous iteration's branch-end

        # --- Gate 2: all anchor points must not be in the support of D ---
        # (build_phi_general also checks each anchor; we do a fast pre-check here.)
        let _skip = false
            for _anc in cur_anchors
                _apx = _anc[1]
                _upx = fp(fp(_apx*_apx) + fp(u1*_apx) + u0)
                if _upx == 0; _skip = true; break; end
            end
            _skip && continue
        end

        # --- Build φ and recover residual (K-aware) ---
        local res_R::NTuple{2,Int}, res_S::NTuple{2,Int}, RS_mumford::NTuple{4,Int}
        local a::Int  # φ leading x²-coefficient (used by D38 and phi_bias_stat)

        if K_anc == 1
            # Fast path: closed-form single-anchor φ
            phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
            phi_c === nothing && continue
            a, b_phi, c_phi, _ = phi_c

            # D38 — φ a-coefficient sequential autocorrelation.
            d38_stat !== nothing && record_d38_step!(d38_stat, Int(a))

            res_R, res_S, RS_mumford = phi_residual_mumford(a, b_phi, c_phi, px, u0, u1)
            RS_mumford === SENTINEL_MUMFORD && continue   # division failed
        else
            # General K-anchor path via the zero-allocation step_phi_k!.
            # Pass `combined_scratch` (or your thread-local scratch variable) downstream.
            step_success = step_phi_k!(combined_scratch, cur_anchors, u0, u1, v0, v1)
            !step_success && continue

            # Extract references directly from our pre-allocated thread-local scratch buffers
            # instead of unpacking an allocated tuple.
            k_len      = length(cur_anchors)
            nb_k       = k_len + 3
            roots_k    = combined_scratch.roots_out
            n_roots    = combined_scratch.roots_count[1]  # Track active logical count via a primitive field
            
            # Extract up to 2 residual affine points as res_R, res_S.
            if n_roots >= 2
                @inbounds res_R = roots_k[1]
                @inbounds res_S = roots_k[2]
            elseif n_roots == 1
                @inbounds res_R = roots_k[1]
                res_S = SENTINEL_PT
            else
                res_R = SENTINEL_PT
                res_S = SENTINEL_PT
            end

            # Build RS_mumford from u_RS / v_RS for the conjugate branch.
            # u_RS length is determined via scratch integer flags rather than allocating length(u_RS_k).
            u_rs_len = combined_scratch.u_RS_len[1]
            v_rs_len = combined_scratch.v_RS_len[1]

            if u_rs_len == 3   # degree 2 — standard conjugate pair
                @inbounds u0_rs = combined_scratch.u_RS[1]
                @inbounds u1_rs = combined_scratch.u_RS[2]
                @inbounds v0_rs = (v_rs_len == 0) ? 0 : combined_scratch.v_RS[1]
                @inbounds v1_rs = (v_rs_len >= 2) ? combined_scratch.v_RS[2] : 0
                RS_mumford = (u0_rs, u1_rs, v0_rs, v1_rs)
            else
                # Residual degree ≠ 2: no conjugate LP key available.
                # If we have split points use them; otherwise skip the step.
                RS_mumford = SENTINEL_MUMFORD
                if res_R == SENTINEL_PT && res_S == SENTINEL_PT
                    continue
                end
            end

            # Approximate a as the leading pure-x² coefficient for D38/diagnostics.
            # In the general basis, find the coeff of the x² monomial (pole order 4).
            basis_k = rr_basis_cached(nb_k)::Vector{NTuple{2, Int}}
            a = 0
            for _ki in 1:nb_k
                @inbounds basis_elem = basis_k[_ki]
                if basis_elem[1] == 2 && basis_elem[2] == 0
                    @inbounds a = combined_scratch.coeffs_out[_ki]
                    break
                end
            end
            
            if d38_stat !== nothing 
                record_d38_step!(d38_stat, Int(a))
            end
        end

        s.hits_total += 1

        # --- Periodic progress report ---
        if verbose
            now_t = time()
            if (now_t - t_last_report) >= report_interval_secs
                s.raw_steps = s.raw_steps   # flush to struct (it's already there)
                report_worker_progress(tid, now_t - t_start, s, rel_counter, rel_target,
                                       shared_lp1_conj)
                t_last_report = now_t
            end
        end

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
            if i0 != 0
                s.hits_lp1_conj += 1
                let _nb_a2 = length(phi_bias_stat.split_hist)
                    _a_bucket = clamp(1 + (Int(a) * _nb_a2) ÷ p, 1, _nb_a2)
                    n_emit_before = deep_stat.n_emissions
                    d34_stores_before = deep_stat.d12_n_stores_seen
                    cur_pt = handle_1lp_conj!(lp_key32, i0, neg_al, neg_be, ell,
                                               fb, nF_cur, G, T,
                                               alpha_vec, beta_vec, rel_rows, rel_counter,
                                               ort, s, shared_lp1_conj, rank_growth,
                                               combined_scratch, P0, phi_bias_stat, next_anchor_ref,
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
                                           ort, s, shared_lp1, shared_lp1_lock,
                                           shared_lp_doubled,
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
            # Add ALL anchors from the K-tuple
            for anc in cur_anchors
                idx = get(pt2idx, anc, 0)
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
            empty!(fb_row_scratch)
            # Add ALL anchors from the K-tuple
            for anc in cur_anchors
                idx = get(pt2idx, anc, 0)
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
                                         shared_lp1, shared_lp1_lock, shared_lp_doubled,
                                         lp_col, rank_growth, combined_scratch,
                                         iR, iS, R, S, P0, next_anchor_ref)
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
                # Add ALL anchors from the K-tuple
                for anc in cur_anchors
                    idx = get(pt2idx, anc, 0)
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
                                             shared_lp1, shared_lp1_lock,
                                             shared_lp2, shared_lp2_lock,
                                             shared_lp_doubled,
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
        @printf("           smoothness (0-LP 1-LP 2-LP 3-LP): %d %d %d %d\n",
                s.smooth_hist[1], s.smooth_hist[2], s.smooth_hist[3], s.smooth_hist[4])
        let total_conj_close = s.hits_1lp_conj_emit + s.hits_1lp_conj_trivial_same_col +
                                s.hits_1lp_conj_trivial_zero_dal + s.hits_1lp_conj_trivial_dup
            @printf("           1lp_conj trivial breakdown: same_col=%d (%.1f%%)  zero_dal=%d (%.1f%%)  dup=%d (%.1f%%)  useful=%d (%.1f%%) of %d closes\n",
                    s.hits_1lp_conj_trivial_same_col,
                    100.0 * s.hits_1lp_conj_trivial_same_col / max(1, total_conj_close),
                    s.hits_1lp_conj_trivial_zero_dal,
                    100.0 * s.hits_1lp_conj_trivial_zero_dal / max(1, total_conj_close),
                    s.hits_1lp_conj_trivial_dup,
                    100.0 * s.hits_1lp_conj_trivial_dup / max(1, total_conj_close),
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
        shared_lp1        ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        shared_lp1_lock   ::ReentrantLock,
        shared_lp_doubled ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        shared_lp2_conj   ::LP2ConjGraph,
        shared_lp2_conj_lock::ReentrantLock,
        max_lp2_conj_nodes::Int,
        rank_growth       ::Vector{Tuple{Int,Int}},
    combined_scratch::ThreadScratchpad,     # Updated type signature to match the caller #combined_scratch  ::Dict{Int,Int},
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
            lock(shared_lp1_lock)
            try
                if haskey(shared_lp_doubled, root_affine)
                    # A previous odd cycle already stored 2·atom(root).
                    # Combine: subtract the two doubled rows.
                    prev_row, prev_al, prev_be = shared_lp_doubled[root_affine]
                    combined    = copy(emitted_conj.row)
                    for (j, v) in prev_row
                        nv = get(combined, j, 0) - v
                        nv == 0 ? delete!(combined, j) : (combined[j] = nv)
                    end
                    combined_al = mod(emitted_conj.alpha - prev_al, ell)
                    combined_be = mod(emitted_conj.beta  - prev_be, ell)
                    delete!(shared_lp_doubled, root_affine)
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
                    # Skip if full rather than evicting — same reasoning as lp1/lp1_conj.
                    if length(shared_lp_doubled) <= MAX_LP1_DOUBLED_ENTRIES
                        shared_lp_doubled[root_affine] = (emitted_conj.row, Int(emitted_conj.alpha), Int(emitted_conj.beta))
                        if try_lp1_doubled_cross_close!(root_affine, shared_lp1, shared_lp_doubled,
                                                        ell, alpha_vec, beta_vec, rel_rows,
                                                        rank_growth, s.raw_steps, rel_counter,
                                                        ort, G, T, combined_scratch, fb)
                            s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        end
                    end
                end  # else (haskey branch)
            finally
                unlock(shared_lp1_lock)
            end
        end
        return next_anchor_ref[]()
    end

    return next_anchor_ref[]()
end
