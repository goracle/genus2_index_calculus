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
        combined_scratch::Dict{Int,Int},
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
    let total_conj_close = s.hits_1lp_conj_emit + s.hits_1lp_conj_trivial_same_col + s.hits_1lp_conj_trivial_zero_dal
        @printf("           1lp_conj trivial breakdown: same_col=%d (%.1f%%)  zero_dal=%d (%.1f%%)  useful=%d (%.1f%%) of %d closes\n",
                s.hits_1lp_conj_trivial_same_col,
                100.0 * s.hits_1lp_conj_trivial_same_col / max(1, total_conj_close),
                s.hits_1lp_conj_trivial_zero_dal,
                100.0 * s.hits_1lp_conj_trivial_zero_dal / max(1, total_conj_close),
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
        combined_scratch::Dict{Int,Int},
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
        combined_scratch::Dict{Int,Int},
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
        anchor_alpha_cap::Int = 200_000)::NTuple{2,Int} where V

    si = conj_shard_idx(lp_key)

    # Use atomic insert-or-pop to close the haskey/insert TOCTOU race.
    # Returns (prev_or_nothing, is_same_partial).  Same-partial hits (i0 matches
    # stored entry) leave the stored entry in place and return (nothing, true) so
    # it survives for a genuine cross-col visitor.  Rényi accounting is skipped
    # for same-partial hits in the LSM backend so alpha_2 stays clean.
    val = _conj_make_val(V, UInt16(i0), UInt64(neg_al), UInt64(neg_be))
    prev, is_same_partial = conj_insert_or_pop!(shared_lp1_conj, si, lp_key, val)

    if is_same_partial
        # Same-partial: stored entry was preserved; this step is a no-op.
        # Update diagnostic counter and attractor probe, then treat as miss.
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
        # Genuine miss: key was freshly stored.
        record_conj_deep_miss!(deep_stat, lp_key, s.raw_steps, al_cur, px_anchor, a_raw, py_anchor)
    end

    if prev !== nothing
        # --- Close against stored entry ---
        v        = prev
        prev_col = Int(v.i0)
        prev_al  = Int(v.neg_al)
        prev_be  = _conj_prev_be(v)
        # Sanity: neg_al==0 would mean alpha==ell, which is outside the cursor
        # range [1, ell-1].  Assert here so a cursor bug surfaces immediately.
        @assert neg_al != 0 "handle_1lp_conj!: neg_al==0 (alpha==ell) at tid=$(Threads.threadid())"
        @assert prev_al != 0 "handle_1lp_conj!: stored prev_al==0 (alpha==ell) at tid=$(Threads.threadid())"

        combined_al = mod(neg_al - prev_al, Int(ell))
        combined_be = mod(neg_be - prev_be, Int(ell))

        if i0 == prev_col
            # Same anchor column reached the close path — means the same-partial
            # guard passed a non-exact-duplicate through (neg_al or neg_be differed).
            # combined_al==0 && combined_be==0 is impossible here because neg_al!=prev_al
            # or neg_be!=prev_be (otherwise same-partial would have blocked it).
            # This is a zero-weight row with nonzero scalars: alpha·a + beta·b = 0 style.
            # With true FB slicing per thread this should not occur cross-thread;
            # within a thread it means the walk revisited the same lp_key from the
            # same anchor with different α/β — treat as instant DLP solve if
            # combined_al==0, combined_be==0 is impossible; otherwise it's a
            # degenerate relation we must not emit.  Assert to catch if it fires.
            @assert false "handle_1lp_conj!: i0==prev_col=$i0 reached close path — same-partial leak (lp_key=$lp_key neg_al=$neg_al prev_al=$prev_al)"
        end

        # i0 != prev_col guaranteed from here.
        if combined_al == 0 && combined_be == 0
            # combined_al==combined_be==0 with i0!=prev_col means fb[i0]=fb[prev_col]
            # in the Jacobian: a pure FB-only relation with no G/T involvement.
            # Emitting it pollutes the kernel with a zero-scalar direction that
            # carries no information about log_G(T).  Drop it.
            s.hits_1lp_conj_trivial_zero_dal += 1
            return next_anchor_ref[]()
        end
        # i0 != prev_col, combined_al or combined_be nonzero: standard relation.
        # atom(fb[i0]) - atom(fb[prev_col]) = combined_al·G + combined_be·T
        # Reuse combined_scratch (weight-2 row; cleared and refilled here).

        # Dedup check: the deterministic step table can regenerate the same lp_key
        # with the same alpha delta repeatedly, producing identical weight-2 rows.
        # Root cause: after key K is closed between threads A(i0) and B(prev_col),
        # both threads advance their alpha cursors by the same cumulative step-table
        # increments before regenerating K, so combined_al = al_A - al_B is
        # constant across all closures of the same pair.  We catch this with a
        # per-thread set keyed on the canonical (lo,hi,al,be) form of the relation.
        lo_idx  = min(i0, prev_col)
        hi_idx  = max(i0, prev_col)
        # Canonicalize scalar: if i0 > prev_col the stored row sign is flipped;
        # negate so (lo→hi) and (hi→lo) variants hash to the same key.
        canon_al = i0 <= prev_col ? combined_al : mod(Int(ell) - combined_al, Int(ell))
        canon_be = i0 <= prev_col ? combined_be : mod(Int(ell) - combined_be, Int(ell))
        rel_key  = (lo_idx, hi_idx, canon_al, canon_be)
        if rel_key in emitted_conj_rels
            # Duplicate: drop silently; do not increment rel_counter.
            s.hits_1lp_conj_trivial_zero_dal += 1   # repurposed as dup-dropped counter
            return next_anchor_ref[]()
        end
        push!(emitted_conj_rels, rel_key)

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
            end
            @assert ok "Conjugate-pair 1-LP closure failed principal divisor check"
        end
        push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
        push!(rel_rows, copy(combined_scratch))
        ort_add_row!(ort, combined_scratch)
        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
            push!(rank_growth, (s.raw_steps, length(rel_rows)))
        s.hits_full += 1; s.hits_1lp_conj_emit += 1; s.rel_local += 1
        Threads.atomic_add!(rel_counter, 1)
        # Record arrival only on actual emission, not on every conj hit.
        # Pass lp_key so the CIR fingerprint analysis can correlate
        # temporally-close hits with shared algebraic structure.
        record_lp1_conj_hit!(phi_bias_stat, s.raw_steps, lp_key, a_bucket)
        record_conj_deep_step!(deep_stat, lp_key, a_bucket, s.raw_steps, true, al_cur, px_anchor)
        record_d16_emission!(deep_stat, lp_key, s.raw_steps, i0)
        record_d19_closure!(deep_stat, i0, prev_col, combined_al, combined_be)
        for _ in 1:post_conj_stride; next_anchor_ref[](); end
        return next_anchor_ref[]()
    end
    # Miss (inserted): advance structured anchor cursor (no stride).
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
        combined_scratch::Dict{Int,Int},
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
                       deep_stat       ::ConjDeepStat;
                       verbose         ::Bool = true,
                       beta_zero       ::Bool = false,
                       amortized_precompute::Bool = false,
                       enable_lp1_aff  ::Bool = true,
                       post_conj_stride::Int  = 0,
                       carry_in_deep_stat::Union{ConjDeepStat,Nothing} = nothing)

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
    chunk_size   = cld(nF_cur, Threads.nthreads())
    anchor_start = (tid - 1) * chunk_size + 1
    anchor_end   = min(tid * chunk_size, nF_cur)
    # Guard against over-allocation when nthreads > nF_cur.
    if anchor_start > nF_cur
        anchor_start = mod1(tid, nF_cur)
        anchor_end   = anchor_start
    end
    anchor_cursor = anchor_start

    @inline function next_anchor()
        pt = fb[anchor_cursor]
        anchor_cursor = anchor_cursor < anchor_end ? anchor_cursor + 1 : anchor_start
        return pt
    end
    next_anchor_ref = Ref{Function}(next_anchor)

    # ==========================================================================
    #  Alpha/beta cursors — simple sequential 1,2,3,... iteration.
    # ==========================================================================
    # Each call to next_alpha_beta() just increments alpha by 1 (mod ell-1,
    # staying in [1, ell-1]) and beta by 1 (mod ell).  No golden-ratio stride,
    # no per-thread offsets — purely deterministic sequential enumeration so we
    # can observe what happens as alpha and the factor base advance one by one.
    alpha_cursor     = 1
    beta_cursor_init = beta_zero ? 0 : 1

    @inline function next_alpha_beta()
        a = alpha_cursor
        b = beta_zero ? 0 : beta_cursor_init
        alpha_cursor = mod(alpha_cursor, ellI - 1) + 1          # cycles 1..ell-1
        if !beta_zero
            beta_cursor_init = mod(beta_cursor_init, ellI - 1) + 1  # cycles 1..ell-1
        end
        return a, b
    end

    # --- Walk state ---
    cur_pt    = next_anchor()
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
    combined_scratch = sizehint!(Dict{Int,Int}(), 8)

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

    # Sequential step cursor — iterates 1,2,3,...,N_STEPS,1,2,... deterministically.
    step_cursor = 1

    # ==========================================================================
    #  Main walk loop
    # ==========================================================================
    while rel_counter[] < rel_target && s.raw_steps < step_cap && (amortized_precompute || ort_b1(ort) == 0)
        s.raw_steps += 1

        # --- Sequential step selection ---
        si          = step_cursor
        step_cursor = mod(step_cursor, N_STEPS) + 1
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a_i[si], ellI)
        beta_cur  = beta_zero ? 0 : mod(beta_cur + step_b_i[si], ellI)

        # --- Gate 1: D must be a degree-2 divisor (generic Jacobian element) ---
        fp3_deg(D_cur.u) != 2 && continue

        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]
        px, py = cur_pt

        # --- Gate 2: P0 must not be in the support of D ---
        upx = fp(fp(px*px) + fp(u1*px) + u0)
        upx == 0 && continue

        # --- Build φ and recover residual ---
        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a, b, c, _ = phi_c

        res_R, res_S, RS_mumford = phi_residual_mumford(a, b, c, px, u0, u1)
        RS_mumford === SENTINEL_MUMFORD && continue   # division failed

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
                    cur_pt = handle_1lp_conj!(lp_key32, i0, neg_al, neg_be, ell,
                                               fb, nF_cur, G, T,
                                               alpha_vec, beta_vec, rel_rows, rel_counter,
                                               ort, s, shared_lp1_conj, rank_growth,
                                               combined_scratch, P0, phi_bias_stat, next_anchor_ref,
                                               _a_bucket, deep_stat, al, P0[1], Int(a), P0[2],
                                               post_conj_stride,
                                               conj_anchor_alpha_seen, CONJ_ANCHOR_ALPHA_CAP)
                    # D9: record 1LP-conj opcode; is_emission = true iff handle produced an emission
                    record_conj_deep_opcode!(deep_stat, OPCODE_1LP_CONJ,
                                             deep_stat.n_emissions > n_emit_before)
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
                # 2-LP-conj: the returned anchor may or may not be LP-derived;
                # conservatively mark as LP for Seq 3 since P0 came from a conj step.
                phi_bias_stat._prev_anchor_was_lp = true
                record_conj_deep_opcode!(deep_stat, OPCODE_2LP_CONJ, false)
            else
                cur_pt = next_anchor()
                record_random_anchor!(phi_bias_stat)
                record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
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
            for idx in (i0, iR, iS)
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
            record_random_anchor!(phi_bias_stat)
            record_conj_deep_opcode!(deep_stat, OPCODE_0LP, false)

        elseif n_lp == 1
            # ------------------------------------------------------------------
            #  1-LP affine: exactly one of P0, R, S is not in FB
            # ------------------------------------------------------------------
            if !enable_lp1_aff
                s.hits_skip += 1
                cur_pt = next_anchor()
                record_random_anchor!(phi_bias_stat)
                record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
            else
            s.hits_lp1 += 1
            lp_pt = i0 == 0 ? P0 : iR == 0 ? R : S

            empty!(fb_row_scratch)
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end

            cur_pt = handle_1lp_affine!(lp_pt, fb_row_scratch, al, be, neg_al, neg_be,
                                         ell, fb, nF_cur, G, T,
                                         alpha_vec, beta_vec, rel_rows, rel_counter, ort, s,
                                         shared_lp1, shared_lp1_lock, shared_lp_doubled,
                                         lp_col, rank_growth, combined_scratch,
                                         iR, iS, R, S, P0, next_anchor_ref)
            # 1-LP affine: handle_1lp_affine! returns the LP point as the next
            # anchor when it stores/conjugates, otherwise a structured cursor step.
            # We mark LP-derived here since the LP point is the structurally
            # interesting anchor; handle_1lp_affine! emitting structured is less
            # frequent and folding it in is conservative.
            phi_bias_stat._prev_anchor_was_lp = true
            record_conj_deep_opcode!(deep_stat, OPCODE_1LP_AFF, false)
            end  # enable_lp1_aff

        elseif n_lp == 2
            # ------------------------------------------------------------------
            #  2-LP affine: exactly two of P0, R, S are not in FB
            # ------------------------------------------------------------------
            if !enable_lp2
                s.hits_skip += 1
                cur_pt = next_anchor()
                record_random_anchor!(phi_bias_stat)
                record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
            else
                empty!(fb_row_scratch)
                for idx in (i0, iR, iS)
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
                record_conj_deep_opcode!(deep_stat, OPCODE_2LP_AFF, false)
            end

        else
            # ------------------------------------------------------------------
            #  3-LP: discard step, advance structured cursor
            # ------------------------------------------------------------------
            s.hits_skip += 1
            # at the hits_total site above; no separate increment needed here.
            cur_pt = next_anchor()
            record_random_anchor!(phi_bias_stat)
            record_conj_deep_opcode!(deep_stat, OPCODE_SKIP, false)
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
        let total_conj_close = s.hits_1lp_conj_emit + s.hits_1lp_conj_trivial_same_col + s.hits_1lp_conj_trivial_zero_dal
            @printf("           1lp_conj trivial breakdown: same_col=%d (%.1f%%)  zero_dal=%d (%.1f%%)  useful=%d (%.1f%%) of %d closes\n",
                    s.hits_1lp_conj_trivial_same_col,
                    100.0 * s.hits_1lp_conj_trivial_same_col / max(1, total_conj_close),
                    s.hits_1lp_conj_trivial_zero_dal,
                    100.0 * s.hits_1lp_conj_trivial_zero_dal / max(1, total_conj_close),
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
            deep_stat = deep_stat)
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
        combined_scratch  ::Dict{Int,Int},
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
