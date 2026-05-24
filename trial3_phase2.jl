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
    @printf("           smoothness histogram (0-LP, 1-LP, 2-LP, 3-LP): %d %d %d %d\n",
            s.smooth_hist[1], s.smooth_hist[2], s.smooth_hist[3], s.smooth_hist[4])
    # Print conj table occupancy once (from thread 2 only) to avoid redundant summation.
    # (Thread 1 is the coordinator and never enters the worker report path.)
    if tid == 2
        conj_total = conj_total_entries(shared_lp1_conj)
        @printf("           conj_table: %d entries (hot+disk)\n", conj_total)
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
# version.  Under the shard lock: if key present, pop and return value; else
# insert and return nothing.
@inline function conj_insert_or_pop!(sc::ShardedLP1Conj{V}, si::Int,
                                      key::CanonicalLP1Key, val::V)::Union{V,Nothing} where V
    lock(sc.locks[si]) do
        sh   = sc.shards[si]
        slot = _conj_find(sh, key)
        if slot != 0
            v = @inbounds sh.vals[slot]
            _conj_delete_slot!(sh, slot)
            v
        elseif sh.count < sh.max_entries
            _conj_insert!(sh, key, val)
            nothing
        else
            # At cap: drop silently (same behaviour as old conj_insert! cap-drop).
            nothing
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
        next_anchor_ref ::Ref{Function})::NTuple{2,Int} where V

    si = conj_shard_idx(lp_key)

    # Use atomic insert-or-pop to close the haskey/insert TOCTOU race.
    # Two threads that both miss conj_haskey and both insert end up with
    # duplicate entries; each later closes against its own entry and gets
    # combined_al=0 — a useless discard.  conj_insert_or_pop! collapses the
    # check+act into one shard-lock critical section, eliminating the race.
    val = _conj_make_val(V, UInt16(i0), UInt64(neg_al), UInt64(neg_be))
    prev = conj_insert_or_pop!(shared_lp1_conj, si, lp_key, val)

    if prev !== nothing
        # --- Close against stored entry ---
        v        = prev
        prev_col = Int(v.i0)
        prev_al  = Int(v.neg_al)
        prev_be  = _conj_prev_be(v)
        combined_al = mod(neg_al - prev_al, Int(ell))
        combined_be = mod(neg_be - prev_be, Int(ell))

        if !(combined_al == 0 && combined_be == 0) && i0 != prev_col
            # Relation: atom(fb[i0]) - atom(fb[prev_col]) = combined_al·G + combined_be·T
            # Reuse combined_scratch to avoid per-closure Dict allocation (weight-2 rows
            # are always exactly 2 entries; scratch is cleared and refilled here).
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
            record_lp1_conj_hit!(phi_bias_stat, s.raw_steps, lp_key)
            return next_anchor_ref[]()
        end
        # combined_al==0 or i0==prev_col: useless close, fall through to structured jump
    end
    # Miss (inserted) or useless close: advance structured anchor cursor.
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
mutable struct HotAnchorEntry
    fb_idx       ::Int
    score        ::Float64   # EMA( hit_rate / global_rate )
    hits         ::Int       # total LP1-conj hits near this anchor
    steps_nearby ::Int       # steps taken near this anchor
    last_seen    ::Int       # s.hits_total when last updated
    # Conditional post-anchor yield curve:
    # yield_windows[k] = (hits_within_horizon_k, total_observations_k) across all
    # anchor visits.  We track 4 horizons: 500, 1000, 2000, 4000 steps.
    yield_obs    ::NTuple{4,Int}   # denominator: how many times we had ≥k steps post-hit
    yield_hits   ::NTuple{4,Int}   # numerator:   how many times ≥1 LP event occurred within k
    # Running half-life estimate (steps until yield drops to 50% of peak rate).
    # Initialised to 0 (unknown).  Updated lazily when enough observations exist.
    halflife_est ::Int
end

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
                       phi_bias_stat   ::PhiBiasStat;
                       verbose         ::Bool = true,
                       beta_zero       ::Bool = false,
                       amortized_precompute::Bool = false,
                       enable_lp1_aff  ::Bool = true)

    nF_cur   = length(fb)
    N_STEPS  = length(step_D)
    tid      = Threads.threadid()
    t_start  = time()

    # Use Int locally in the hot loop; convert back to BigInt only when a
    # relation is emitted or stored.
    ellI = Int(ell)
    step_a_i = Vector{Int}(undef, length(step_a))
    step_b_i = Vector{Int}(undef, length(step_b))
    @inbounds for i in eachindex(step_a)
        step_a_i[i] = Int(step_a[i])
        step_b_i[i] = Int(step_b[i])
    end

    # ==========================================================================
    #  α-residue step buckets  (algebraic inertia)
    #
    #  Partition the step table by (step_a_i[i] mod ALPHA_MOD) into ALPHA_MOD
    #  buckets.  When the walk is inside a hot geometric basin (basin_dry_streak
    #  == 0), we bias step selection toward the bucket that keeps alpha_cur in
    #  the same residue class — creating algebraic coherence alongside the
    #  existing geometric inertia.  Outside a basin we use uniform selection.
    #
    #  ALPHA_MOD is now scaled as round(Int, log2(p)) rather than fixed at 8.
    #  Motivation (GPT diagnosis): with fixed ALPHA_MOD the transition partition
    #  stays "small" as p grows, giving giant coherent basins.  A log(p)-scaled
    #  partition grows the entropy of the transition slowly with the ambient
    #  geometry, preventing single basins from dominating.  For p≈16411,
    #  log2(16411)≈14, so ALPHA_MOD≈14 — only modestly larger than 8 and well
    #  below the collapse threshold of 16 observed empirically.
    #
    #  Safety clamp: ALPHA_MOD is clamped to [4, N_STEPS÷8] so every bucket
    #  gets at least ~8 entries from the 256-step table, preventing the
    #  over-constrained attractor collapse seen with ALPHA_MOD=16.
    # ==========================================================================
    ALPHA_MOD    = clamp(round(Int, log2(max(2, ellI))), 4, N_STEPS ÷ 8)
    alpha_buckets = [Int[] for _ in 0:ALPHA_MOD-1]
    for i in 1:N_STEPS
        r = mod(step_a_i[i], ALPHA_MOD)
        push!(alpha_buckets[r + 1], i)   # +1 for 1-based indexing
    end
    # Fallback to full table if any bucket is empty.
    alpha_buckets_safe = [isempty(b) ? collect(1:N_STEPS) : b for b in alpha_buckets]

    # ==========================================================================
    #  uv-hash step buckets  (nonlinear diversity mixing)
    #
    #  GPT diagnosis: routing logic that depends on only a few bits of the
    #  divisor state causes neighboring states to follow nearly identical
    #  trajectories, creating long coherent excursions that inflate ACF.
    #  Solution: build a second partition that hashes both u AND v coefficients
    #  of the *step* divisors (not just alpha), so step selection depends on
    #  more state dimensions and avalanches faster.
    #
    #  uv_buckets[r+1] contains step indices i where:
    #    hash(step_D[i].u[1], step_D[i].u[2], step_D[i].v[1], step_D[i].v[2])
    #    mod UV_MOD == r
    #  This is built from step_a_i and step_b_i (which encode the exponents and
    #  therefore implicitly the Mumford data) via a cheap nonlinear mix.
    #
    #  UV_MOD = ALPHA_MOD (same partition size).  In-basin we pick the uv-bucket
    #  that matches a nonlinear mix of the current Mumford state; outside a basin
    #  we use uniform selection.  This only fires when basin_dry_streak == 0,
    #  so it does not interact with the cold-path decorrelation.
    # ==========================================================================
    UV_MOD = ALPHA_MOD
    uv_buckets = [Int[] for _ in 0:UV_MOD-1]
    for i in 1:N_STEPS
        # Nonlinear mix of (step_a, step_b) using xor-shift — cheap, avalanches well.
        ha = step_a_i[i]
        hb = step_b_i[i]
        h  = xor(ha, hb << 7) + xor(hb, ha >> 3)
        r  = mod(h, UV_MOD)
        r  = r < 0 ? r + UV_MOD : r    # Julia mod can return negative for negative h
        push!(uv_buckets[r + 1], i)
    end
    uv_buckets_safe = [isempty(b) ? collect(1:N_STEPS) : b for b in uv_buckets]

    # ==========================================================================
    #  Structured walk cursors
    #
    #  Instead of fully random anchor and alpha restarts, each thread maintains
    #  a deterministic cursor through (anchor, alpha) space.  This gives uniform
    #  coverage across the factor base and the discrete-log exponent range,
    #  preventing the i.i.d. birthday clustering that causes some FB regions to
    #  be visited ≫ their fair share while others are starved.
    #
    #  Design:
    #    anchor_cursor — cycles through fb[1..nF_cur] in steps of anchor_stride.
    #      anchor_stride is a per-thread coprime-to-nF_cur offset so that no two
    #      threads walk the same subsequence.
    #
    #    alpha_cursor  — advances by alpha_stride (mod ellI) on every restart.
    #      alpha_stride is chosen as a large prime-like increment so consecutive
    #      restarts explore distinct exponent regions.  It is also per-thread
    #      offset to spread threads across the range.
    #
    #  Threads are offset by tid so their cursors start in different positions
    #  and stride differently — they cover complementary slices of the space
    #  rather than each independently sampling the full space at random.
    #
    #  The step-D loop (which advances D_cur algebraically each raw step) is
    #  unchanged: it still picks a random precomputed step.  Only the *restart*
    #  anchor and the *initial* alpha/beta are made structured.
    # ==========================================================================

    # Coprime anchor stride per thread: use the (tid-1)-th prime > 1 as the step,
    # taken mod nF_cur; if nF_cur is small just use tid offset directly.
    _small_primes = (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71)
    anchor_stride = nF_cur > 1 ?
        mod(_small_primes[min(tid, length(_small_primes))], nF_cur - 1) + 1 :
        1
    # Ensure stride is coprime to nF_cur via gcd reduction; fallback to 1.
    function _gcd(a, b)
        b == 0 && throw(ArgumentError("_gcd: divisor b is zero (a=$a)"))
        while b != 0; a, b = b, a % b; end
        a
    end
    if nF_cur > 1
        start_stride = anchor_stride
        while _gcd(anchor_stride, nF_cur) != 1
            anchor_stride = mod(anchor_stride, nF_cur) + 1
            anchor_stride == start_stride && throw(ErrorException(
                "phase2_worker tid=$tid: no anchor_stride coprime to nF_cur=$nF_cur found (full cycle)"))
        end
    end
    anchor_cursor = mod((tid - 1) * anchor_stride, max(1, nF_cur)) + 1

    # Alpha stride: large fractional step through [1, ellI-1], per-thread offset.
    # We use ⌊ellI * φ⁻¹⌋ (golden-ratio increment) shifted by tid — this gives
    # a low-discrepancy sequence over the exponent range.
    phi_inv_frac = 0.6180339887498949   # 1/φ = (√5−1)/2
    alpha_stride = max(1, round(Int, ellI * phi_inv_frac))
    alpha_stride = mod(alpha_stride + (tid - 1) * max(1, ellI ÷ 64), ellI - 1) + 1

    # Beta stride: similar golden-ratio step, shifted by a different prime multiple.
    beta_stride = max(1, round(Int, ellI * 0.7548776662))  # 1 - 1/φ² ≈ 0.7548
    beta_stride = mod(beta_stride + (tid - 1) * max(1, ellI ÷ 97), ellI)

    # Initial cursor positions: spread threads across the space.
    alpha_cursor = mod((tid - 1) * alpha_stride, max(1, ellI - 1)) + 1
    beta_cursor_init = beta_zero ? 0 :
                       mod((tid - 1) * beta_stride, ellI)

    # Helper: advance anchor cursor and return the next fb point.
    # Called on every restart (after closure, 0-LP, 3-LP, miss).
    @inline function next_anchor()
        pt = fb[anchor_cursor]
        anchor_cursor = mod(anchor_cursor - 1 + anchor_stride, nF_cur) + 1
        return pt
    end

    # Ref wrapper so out-of-scope handler functions can call next_anchor.
    next_anchor_ref = Ref{Function}(next_anchor)

    # Helper: advance alpha/beta cursors and return (alpha, beta).
    # Called on every restart to keep the (D, anchor) pairing varied.
    @inline function next_alpha_beta()
        a = alpha_cursor
        b = beta_zero ? 0 : beta_cursor_init
        alpha_cursor = mod(alpha_cursor - 1 + alpha_stride, ellI - 1) + 1
        if !beta_zero
            beta_cursor_init = mod(beta_cursor_init + beta_stride, ellI)
        end
        return a, b
    end

    # ==========================================================================
    #  IDEA 2: Controlled inertia / correlated diffusion
    #
    #  Instead of always restarting to a fresh cursor position after each
    #  closure or 3-LP discard, we maintain a "direction" variable that
    #  persists across restarts with probability (1-ε).  When the direction
    #  persists, we stay near the same anchor region, creating long coherent
    #  excursions through Jacobian state-space (sub-Brownian diffusion).
    #  When we flip, we jump to a fresh structured cursor position.
    #
    #  This directly targets the Allan-slope and ACF-persistence diagnostics:
    #  a walk with inertia will accumulate long hot/cold epochs in the LP-conj
    #  hit-density, which is exactly the empirically observed structure we want
    #  to exploit.
    #
    #  ε = INERTIA_FLIP_PROB controls the mixing/recurrence tradeoff:
    #    ε → 0 : maximum persistence (nearly periodic orbit)
    #    ε → 1 : standard cursor walk (no inertia)
    #  At ε=0.05 the walk was over-coherent (Rényi-2 burst dominance 566×, phase-3 430k avg
    #  steps vs 376k). Raising to ε=0.15 restores cold-path exploration while keeping
    #  hot-epoch coherence (inertia persists ~7 steps on average before a flip).
    # ==========================================================================
    INERTIA_FLIP_PROB = 0.15   # flip to new direction with 15% probability

    # Direction state: offset added to anchor_cursor on each "next" call when
    # inertia is active.  Same parity as anchor_stride so it stays coprime.
    inertia_dir   = anchor_stride       # start aligned with the cursor stride
    inertia_alpha_dir = alpha_stride    # companion alpha perturbation

    @inline function next_anchor_inertia()
        nF_cur <= 0 && throw(ErrorException(
            "next_anchor_inertia tid=$tid: empty factor base (nF_cur=$nF_cur)"))
        pt = fb[anchor_cursor]
        # With probability INERTIA_FLIP_PROB, flip direction to a new one.
        if rand() < INERTIA_FLIP_PROB
            # Pick a new direction from the small-primes list, shifted by tid
            # so threads diverge when they flip simultaneously.
            new_dir = _small_primes[mod(anchor_cursor + tid, length(_small_primes)) + 1]
            if nF_cur > 1
                start_dir = new_dir
                while _gcd(new_dir, nF_cur) != 1
                    new_dir = mod(new_dir, nF_cur) + 1
                    new_dir == start_dir && throw(ErrorException(
                        "next_anchor_inertia tid=$tid: no direction coprime to nF_cur=$nF_cur (full cycle)"))
                end
            end
            inertia_dir = new_dir
        end
        anchor_cursor = mod(anchor_cursor - 1 + inertia_dir, nF_cur) + 1
        return pt
    end

    # ==========================================================================
    #  IDEA 1: Affine recurrence anchor schedule
    #
    #  Replace the linear cursor with an affine map i_{t+1} = a*i_t + b mod nF,
    #  where (a, b) are chosen to give a single long orbit (i.e. a is a
    #  primitive root mod nF, or at least has full orbit length).  This gives
    #  more structured revisitation patterns than a linear stride, which can
    #  concentrate the walk near productive geometric configurations.
    #
    #  We use a = anchor_stride (already coprime to nF) as the multiplicative
    #  factor and b = 1 + tid as the additive offset.  The orbit length is
    #  lcm(ord(a, nF_cur), nF_cur / gcd(b, nF_cur)), which for generic
    #  coprime (a, nF) equals nF — so we get full coverage with a different
    #  traversal order than the linear cursor.
    # ==========================================================================
    affine_a = anchor_stride                     # multiplicative factor
    affine_b = mod(1 + tid, max(1, nF_cur))      # additive offset
    affine_cursor = mod((tid - 1) * anchor_stride, max(1, nF_cur)) + 1

    @inline function next_anchor_affine()
        pt = fb[affine_cursor]
        affine_cursor = mod(affine_a * affine_cursor + affine_b - 1, nF_cur) + 1
        return pt
    end

    # ==========================================================================
    #  IDEA 4 (enhanced): LP-basin memory with weighted anchor scoring
    #
    #  When the walk produces a LP1-conj hit, we record both the current anchor
    #  index AND a hit count for that anchor.  `basin_steer_anchor` now picks the
    #  highest-hit-count entry rather than the most recent one, so we steer toward
    #  the algebraically hottest remembered anchor, not just the newest one.
    #
    #  BASIN_BUF_SIZE=32: doubled from 16 so we remember more candidates across
    #  the observed ~2800-step inter-arrival mean.
    #
    #  BASIN_TRIGGER tuning: set to ~1.5x observed inter-arrival mean (2826) ->
    #  ~4500 steps.  The previous value of 2000 fired before the expected next
    #  hit, wasting steers; 4500 fires well into the next expected hot window.
    #
    #  basin_hot_depth: within a hot epoch (basin_dry_streak == 0 after a hit),
    #  we track how many consecutive LP-conj hits we have seen (retained for
    #  diagnostics; no longer gates any step-selection tier).
    # ==========================================================================
    BASIN_BUF_SIZE  = 32    # remember last 32 LP-conj hit anchor indices
    BASIN_TRIGGER   = 4500  # steer back after this many non-LP-conj steps

    basin_buf         = zeros(Int, BASIN_BUF_SIZE)   # circular buffer: anchor indices
    basin_hit_counts  = zeros(Int, BASIN_BUF_SIZE)   # parallel: hit count for each slot
    basin_buf_head    = 1
    basin_buf_count   = 0
    basin_dry_streak  = 0
    basin_hot_depth   = 0   # consecutive LP1-conj hits since last dry period

    # Diagnostics: count how many times basin steering actually fired, and how
    # many LP1-conj hits followed within BASIN_TRIGGER steps of a steer.
    basin_steers_fired    = 0
    basin_steers_hit      = 0
    basin_steer_countdown = 0   # steps remaining in the post-steer observation window

    # ── Burst exploitation ────────────────────────────────────────────────────
    # When a LP1-conj hit fires, D_cur is geometrically hot.  Save it and probe
    # it with fresh independent offsets for burst_budget steps before resuming
    # the normal walk.  D_cur keeps accumulating so resumption is seamless.
    # Budget ≈ mean_gap/3 estimated from running inter-arrival; fall back to 2000.
    _burst_arrivals_sum = 0   # sum of inter-arrival gaps observed so far
    _burst_arrivals_n   = 0   # count
    _burst_last_hit_step = 0  # s.hits_total at last LP1-conj hit
    _burst_budget_default = 2000
    burst_budget        = 0
    burst_active        = false
    hot_D_b2            = G       # dummy init; overwritten before burst_active is ever true
    hot_alpha_b2        = 0
    hot_beta_b2         = 0
    n_burst_steps_b2       = 0   # raw burst iterations (pre-gate)
    n_burst_valid_steps_b2 = 0   # burst iterations that passed all gates (same units as hits_total)
    n_burst_hits_b2        = 0

    @inline function record_basin_hit!(anchor_idx::Int)
        # Search for this anchor_idx in the buffer; if found, increment its count.
        # Otherwise insert into the next slot (LRU eviction of oldest entry).
        found_slot = 0
        for k in 1:basin_buf_count
            slot = mod(basin_buf_head - 1 - k + BASIN_BUF_SIZE, BASIN_BUF_SIZE) + 1
            if basin_buf[slot] == anchor_idx
                found_slot = slot
                break
            end
        end
        if found_slot != 0
            basin_hit_counts[found_slot] += 1
        else
            basin_buf[basin_buf_head]        = anchor_idx
            basin_hit_counts[basin_buf_head] = 1
            basin_buf_head  = mod(basin_buf_head, BASIN_BUF_SIZE) + 1
            basin_buf_count = min(basin_buf_count + 1, BASIN_BUF_SIZE)
        end
        basin_dry_streak = 0
        basin_hot_depth += 1
        # If a steer was pending observation, credit it.
        if basin_steer_countdown > 0
            basin_steers_hit      += 1
            basin_steer_countdown  = 0
        end
        # Arm burst: save current hot divisor and set budget.
        # Update running inter-arrival estimate for adaptive budgeting.
        if _burst_last_hit_step > 0
            gap = s.hits_total - _burst_last_hit_step
            _burst_arrivals_sum += gap
            _burst_arrivals_n   += 1
            mean_gap = _burst_arrivals_sum / _burst_arrivals_n
            _burst_budget_default = max(500, round(Int, mean_gap / 3))
        end
        _burst_last_hit_step = s.hits_total
        hot_D_b2     = D_cur
        hot_alpha_b2 = alpha_cur
        hot_beta_b2  = beta_cur
        burst_budget = _burst_budget_default
        burst_active = true
    end

    # Return the anchor index of the highest-hit-count slot, or 0 if basin
    # is inactive / dry streak has not reached trigger.
    @inline function basin_steer_anchor()::Int
        basin_buf_count == 0 && return 0
        basin_dry_streak < BASIN_TRIGGER && return 0
        # Find the slot with the highest hit count.
        best_slot  = 0
        best_count = 0
        for k in 1:basin_buf_count
            slot = mod(basin_buf_head - 1 - k + BASIN_BUF_SIZE, BASIN_BUF_SIZE) + 1
            if basin_buf[slot] != 0 && basin_hit_counts[slot] > best_count
                best_count = basin_hit_counts[slot]
                best_slot  = slot
            end
        end
        best_slot == 0 && return 0
        base_idx = basin_buf[best_slot]
        jitter   = rand(-2:2)
        return mod(base_idx - 1 + jitter, nF_cur) + 1
    end

    # Unified next_anchor that combines inertia + basin steering.
    # Priority: basin steer (when dry streak is long) > inertia > affine.
    @inline function next_anchor_structured()
        # Basin steering: jump to a hot region if we have been cold too long.
        steered = basin_steer_anchor()
        if steered != 0
            anchor_cursor         = steered
            basin_dry_streak      = 0
            basin_hot_depth       = 0    # reset hot depth after a forced steer
            basin_steers_fired   += 1
            basin_steer_countdown = BASIN_TRIGGER   # observe next BASIN_TRIGGER steps for a hit
        end
        # Fall through to inertia walk from (possibly updated) cursor.
        return next_anchor_inertia()
    end

    # Override next_anchor_ref to use the structured version.
    next_anchor_ref[] = next_anchor_structured

    # ==========================================================================
    #  Importance-sampling layer  (controlled perturbation, NOT hard steering)
    #
    #  Architecture follows the "soft biased sampler" design:
    #    • HotAnchor reservoir: scored regions with EMA hit-rate over global base.
    #    • ε-greedy restart: with prob ε_EXPL pick uniform seed; else pick from
    #      the reservoir proportional to score.  ε starts at ε_EXPL_INIT and
    #      is held constant until ESS drops, then backed off.
    #    • Step-type softmax: each precomputed step index carries a smoothed
    #      reward score; in-basin steps are sampled via softmax(β_STEP * score).
    #    • Online diagnostics: ESS, rank-growth-per-relation, entropy drift.
    #
    #  Crucially: this layer sits *on top of* the existing basin/inertia
    #  machinery.  It fires only at restarts (after closure / 0-LP / 3-LP)
    #  and does NOT replace the basin_steer_anchor path — both run.
    # ==========================================================================

    # ── HotAnchor record ──────────────────────────────────────────────────────
    # Each entry tracks a FB-index region with an EMA of LP1-conj hit rate
    # normalised by the global base rate.
    # (struct HotAnchorEntry defined at top level, before phase2_worker)

    # Reservoir: fixed capacity; evict lowest-score entry when full.
    IS_RESERVOIR_CAP = 128
    is_reservoir     = HotAnchorEntry[]
    is_reservoir_idx = Dict{Int,Int}()   # fb_idx → position in is_reservoir

    # Global LP1-conj hit rate estimate (EMA): updated on every valid step.
    is_global_rate_ema = 0.0
    is_global_ema_α    = 0.02   # EMA smoothing; slow enough to be stable

    # ε-greedy exploration fraction.
    ε_EXPL_INIT  = 0.35   # start with 35% exploration
    ε_EXPL_MIN   = 0.10   # never go below 10%
    ε_cur        = ε_EXPL_INIT

    # Step-type softmax scoring.
    # step_scores[i] = smoothed reward for step index i (initialised flat).
    step_scores  = fill(0.0, N_STEPS)
    step_β       = 0.05   # softmax inverse-temperature; low = nearly uniform

    # ESS tracking: we track a simple running estimate of effective sample size
    # from the restart weight distribution.  If ESS falls below ESS_FLOOR ×
    # (number of restarts), we increase ε to restore exploration diversity.
    is_restart_weights = Float64[]   # unnormalised weight of each restart
    is_ess_check_every = 200         # check ESS every N restarts
    is_restart_count   = 0
    ESS_FLOOR          = 0.20        # trigger back-off when ESS < 20% of restarts

    # Entropy drift counters: track reservoir score entropy and ESS.
    is_ess_last        = 0.0
    is_entropy_last    = 0.0

    # ── Helpers ───────────────────────────────────────────────────────────────

    @inline function is_score_ema(old_score::Float64, new_obs::Float64)::Float64
        α = 0.1   # per-anchor EMA smoothing
        α * new_obs + (1 - α) * old_score
    end

    # Add or update a hot-anchor entry after an LP1-conj hit at fb_idx.
    @inline function is_record_hit!(fb_idx::Int, steps_since_last::Int)
        # Score = log(1 + hits_so_far) * clamp(hit_rate / base_rate, 0, MAX_LIFT)
        # Using log(1+hits) gives diminishing returns per hit so one lucky early
        # hit can't permanently dominate.  Clamping the rate ratio at MAX_LIFT
        # prevents a single very-short inter-arrival gap from inflating the score
        # by 6 orders of magnitude (the original bug: obs = 1/1 / 1e-9 = 1e9).
        MAX_LIFT  = 20.0   # cap rate ratio at 20× global baseline
        hit_rate  = steps_since_last > 0 ? 1.0 / steps_since_last : 0.0
        base_rate = max(1e-6, is_global_rate_ema)
        lift      = clamp(hit_rate / base_rate, 0.0, MAX_LIFT)

        if haskey(is_reservoir_idx, fb_idx)
            i = is_reservoir_idx[fb_idx]
            e = is_reservoir[i]
            new_hits   = e.hits + 1
            # Score blends lift (recency) with log-hits (accumulation) AND
            # measured yield (if available).  Yield-adjusted score rewards anchors
            # that have demonstrated real future productivity, not just past hits.
            yield_bonus = if e.yield_obs[1] >= 2
                # Use the shortest horizon (500 steps) as the primary signal.
                # P(hit within 500 | this anchor) / global_rate * 500
                empirical_yield = e.yield_hits[1] / max(1, e.yield_obs[1])
                global_yield    = max(1e-6, is_global_rate_ema) * 500
                min(3.0, empirical_yield / global_yield)
            else
                1.0
            end
            e.score        = log1p(Float64(new_hits)) * yield_bonus *
                             (0.3 * lift + 0.7 * e.score / max(1.0, log1p(Float64(e.hits)) * max(1.0, e.halflife_est > 0 ? yield_bonus : 1.0)))
            e.hits         = new_hits
            e.steps_nearby += steps_since_last
            e.last_seen    = s.hits_total
        else
            init_score = log1p(1.0) * lift
            if length(is_reservoir) >= IS_RESERVOIR_CAP
                # Prefer evicting anchors with zero yield observations; only
                # fall back to global minimum if all entries have yield data.
                unyielded = filter(i -> is_reservoir[i].yield_obs[1] == 0, eachindex(is_reservoir))
                min_i = if !isempty(unyielded)
                    unyielded[argmin(is_reservoir[i].score for i in unyielded)]
                else
                    argmin(e.score for e in is_reservoir)
                end
                old_idx = is_reservoir[min_i].fb_idx
                delete!(is_reservoir_idx, old_idx)
                is_reservoir[min_i] = HotAnchorEntry(fb_idx, init_score, 1,
                                                      steps_since_last, s.hits_total,
                                                      (0,0,0,0), (0,0,0,0), 0)
                is_reservoir_idx[fb_idx] = min_i
            else
                push!(is_reservoir, HotAnchorEntry(fb_idx, init_score, 1,
                                                    steps_since_last, s.hits_total,
                                                    (0,0,0,0), (0,0,0,0), 0))
                is_reservoir_idx[fb_idx] = length(is_reservoir)
            end
        end
    end

    # Sample a restart anchor: ε-greedy over reservoir.
    # Returns a fb index (1-based).
    @inline function is_sample_restart()::Int
        is_restart_count += 1
        if isempty(is_reservoir) || rand() < ε_cur
            # Pure exploration: uniform random FB point.
            idx = rand(1:nF_cur)
            push!(is_restart_weights, ε_cur)
            return idx
        end
        # Exploitation: sample proportional to exp(score).
        # Numerically stable softmax over reservoir scores.
        scores = [e.score for e in is_reservoir]
        max_s  = maximum(scores)
        probs  = [exp(s - max_s) for s in scores]
        Z      = sum(probs)
        r      = rand() * Z
        cumsum = 0.0
        chosen = 1
        for i in eachindex(probs)
            cumsum += probs[i]
            if cumsum >= r
                chosen = i
                break
            end
        end
        w = probs[chosen] / Z
        push!(is_restart_weights, w)
        # Return with small jitter to sample basin neighbourhood, not exact orbit.
        base = is_reservoir[chosen].fb_idx
        jitter = rand(-3:3)
        return mod(base - 1 + jitter, nF_cur) + 1
    end

    # Update step reward: called after any full-relation emission to credit
    # the step that produced it.  si_last must be tracked in the walk loop.
    @inline function is_reward_step!(si::Int, reward::Float64)
        step_scores[si] = (1 - step_β) * step_scores[si] + step_β * reward
    end

    # Sample a step index via softmax when in-basin.
    @inline function is_step_sample_softmax()::Int
        max_s  = maximum(step_scores)
        probs  = [exp(step_β * (step_scores[i] - max_s)) for i in 1:N_STEPS]
        Z      = sum(probs)
        r      = rand() * Z
        cumsum = 0.0
        for i in 1:N_STEPS
            cumsum += probs[i]
            cumsum >= r && return i
        end
        return N_STEPS
    end

    # ESS check: if ESS collapses below floor, back off ε toward ε_EXPL_INIT.
    @inline function is_check_ess!()
        isempty(is_restart_weights) && return
        sw  = sum(is_restart_weights)
        sw2 = sum(w^2 for w in is_restart_weights)
        ess = sw2 > 0 ? (sw^2 / sw2) / length(is_restart_weights) : 1.0
        is_ess_last = ess
        if ess < ESS_FLOOR
            # Walk is over-concentrating; increase exploration.
            ε_cur = min(ε_EXPL_INIT, ε_cur * 1.5)
        else
            # Healthy diversity; slowly decay toward minimum.
            ε_cur = max(ε_EXPL_MIN, ε_cur * 0.98)
        end
        # Rotate the window: keep last is_ess_check_every weights.
        if length(is_restart_weights) > is_ess_check_every * 2
            deleteat!(is_restart_weights, 1:is_ess_check_every)
        end
    end

    # Entropy of reservoir scores (log-sum-exp based).
    @inline function is_reservoir_entropy()::Float64
        isempty(is_reservoir) && return 0.0
        scores = [e.score for e in is_reservoir]
        max_s  = maximum(scores)
        probs  = [exp(s - max_s) for s in scores]
        Z      = sum(probs)
        -sum((w / Z) * log(w / Z + 1e-300) for w in probs)
    end

    # Steps since the last LP1-conj hit (used to feed is_record_hit! per-anchor).
    is_steps_since_last_hit = 0

    # Last step index used (to credit rewards to the right step).
    is_last_si = 1

    # ── Post-hit yield observation windows ───────────────────────────────────
    # After each LP1-conj hit at anchor fb_idx, we open 4 observation windows of
    # widths [500, 1000, 2000, 4000] steps.  If another LP1-conj hit fires within
    # the window, we credit it as a yield observation.  This builds the empirical
    # conditional yield curve P(hit within k | anchor fb_idx).
    #
    # is_yield_windows: circular buffer of (fb_idx, remaining_steps[4]) for all
    # currently open windows.  Max concurrent open windows = MAX_YIELD_WINDOWS.
    # When a new hit opens windows we push; when remaining_steps all hit 0 we close.
    YIELD_HORIZONS     = (1000, 2000, 4000, 8000)
    MAX_YIELD_WINDOWS  = 32   # doubled from 16; more concurrent observations
    # Each entry: (fb_idx, remaining[4], hit_fired[4])
    # remaining[k] counts down from YIELD_HORIZONS[k]; hit_fired[k] = 1 if any hit
    # fired in that window (saturating at 1, not counting multiplicity).
    _yw_idx   = zeros(Int,    MAX_YIELD_WINDOWS)   # fb_idx for each slot
    _yw_rem   = zeros(Int,    MAX_YIELD_WINDOWS, 4)  # remaining steps per horizon
    _yw_hit   = zeros(Bool,   MAX_YIELD_WINDOWS, 4)  # hit fired in window?
    _yw_used  = zeros(Bool,   MAX_YIELD_WINDOWS)   # slot in use?
    _yw_head  = 1   # next slot to allocate (round-robin)

    # Open 4 yield windows for a given anchor.
    @inline function open_yield_windows!(fb_idx::Int)
        slot = _yw_head
        # Find an unused slot (fallback: overwrite oldest = _yw_head).
        for k in 1:MAX_YIELD_WINDOWS
            s2 = mod(_yw_head - 1 + k - 1, MAX_YIELD_WINDOWS) + 1
            if !_yw_used[s2]; slot = s2; break; end
        end
        _yw_idx[slot] = fb_idx
        for k in 1:4; _yw_rem[slot, k] = YIELD_HORIZONS[k]; _yw_hit[slot, k] = false; end
        _yw_used[slot] = true
        _yw_head = mod(_yw_head, MAX_YIELD_WINDOWS) + 1
    end

    # Tick all open windows by 1 step.  Called every valid phi step.
    # When a window closes (remaining → 0) we record the observation.
    @inline function tick_yield_windows!()
        @inbounds for slot in 1:MAX_YIELD_WINDOWS
            _yw_used[slot] || continue
            all_done = true
            for k in 1:4
                _yw_rem[slot, k] > 0 || continue
                _yw_rem[slot, k] -= 1
                all_done = false
                if _yw_rem[slot, k] == 0
                    # Window k just closed: record observation in reservoir.
                    fbi = _yw_idx[slot]
                    if haskey(is_reservoir_idx, fbi)
                        ei = is_reservoir_idx[fbi]
                        e  = is_reservoir[ei]
                        fired = _yw_hit[slot, k] ? 1 : 0
                        # Update NTuple fields by rebuilding them.
                        obs = e.yield_obs
                        hit = e.yield_hits
                        e.yield_obs  = ntuple(j -> j == k ? obs[j] + 1 : obs[j], Val(4))
                        e.yield_hits = ntuple(j -> j == k ? hit[j] + fired : hit[j], Val(4))
                        # Update halflife estimate when enough observations exist.
                        # Use whichever closed horizon has the most signal: prefer
                        # k=2 (2000 steps, closest to μ) once it has ≥2 obs, else k=1.
                        if e.yield_obs[k] >= 2
                            horizon_steps = YIELD_HORIZONS[k]
                            y_k = e.yield_hits[k] / max(1, e.yield_obs[k])
                            if y_k > 0.01 && y_k < 0.99
                                tau = round(Int, -Float64(horizon_steps) / log(1.0 - y_k))
                                # Only update if this horizon gives a tighter (lower) estimate
                                # or we had no estimate yet.
                                if e.halflife_est <= 0 || tau < e.halflife_est * 2
                                    e.halflife_est = clamp(tau, 100, 20000)
                                end
                            end
                        end
                    end
                end
            end
            if all_done || all(_yw_rem[slot, k] == 0 for k in 1:4)
                _yw_used[slot] = false
            end
        end
    end

    # Credit a hit to all currently open yield windows.
    @inline function credit_yield_hit!(fb_idx::Int)
        @inbounds for slot in 1:MAX_YIELD_WINDOWS
            _yw_used[slot] || continue
            for k in 1:4
                _yw_rem[slot, k] > 0 || continue
                _yw_hit[slot, k] = true
            end
        end
    end

    # Exploitation suppression: when the walk is near an anchor with a measured
    # short halflife (< IS_SUPPRESS_THRESHOLD steps), suppress IS random restarts
    # so we don't destroy locality just when it's productive.
    IS_SUPPRESS_THRESHOLD = 2000  # suppress if halflife < this (raised to match μ~1400-1800)
    is_suppress_restarts  = false
    is_suppress_countdown = 0

    @inline function maybe_suppress_restarts!(fb_idx::Int)
        haskey(is_reservoir_idx, fb_idx) || return
        e = is_reservoir[is_reservoir_idx[fb_idx]]
        e.halflife_est > 0 && e.halflife_est < IS_SUPPRESS_THRESHOLD || return
        # Suppress for 3× halflife; extend non-destructively if already suppressed.
        is_suppress_restarts  = true
        is_suppress_countdown = max(is_suppress_countdown, 3 * e.halflife_est)
    end

    # ── Override next_anchor_structured to inject IS restart ─────────────────
    # We wrap the existing next_anchor_structured with an IS restart with
    # probability IS_RESTART_PROB, so the IS layer fires rarely and never
    # dominates over the basin/inertia path.
    IS_RESTART_PROB = 0.20   # 20% of restarts go through IS sampler (up from 12%)

    _orig_next_anchor_structured = next_anchor_ref[]
    next_anchor_ref[] = function ()
        # Periodic ESS check (every is_ess_check_every restarts).
        if is_restart_count > 0 && is_restart_count % is_ess_check_every == 0
            is_check_ess!()
        end
        # Only fire IS restart if not suppressed and reservoir has candidates.
        if !is_suppress_restarts && !isempty(is_reservoir) && rand() < IS_RESTART_PROB
            new_idx = is_sample_restart()
            anchor_cursor = new_idx
        end
        return _orig_next_anchor_structured()
    end

    # --- Walk state (structured init) ---
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

    # --- Diagnostics ---
    sample_phase2_rels = Vector{Tuple{Div2,Int,Int,NTuple{2,Int},NTuple{2,Int},NTuple{2,Int}}}()
    rank_growth  = Tuple{Int,Int}[]
    t_last_report = time()
    report_interval_secs = 30.0

    lp2_node_cache     = 0
    lp2_check_interval = 256
    lp2_check_countdown = 0

    # ==========================================================================
    #  Main walk loop
    # ==========================================================================
    while rel_counter[] < rel_target && s.raw_steps < step_cap && (amortized_precompute || ort_b1(ort) == 0)
        s.raw_steps += 1

        # --- Take a step biased toward the current α-residue class when in-basin ---
        #
        # Two-tier step selection:
        #   Tier 1 (in-basin): alternate between two diversification modes:
        #     Even raw_steps → pick from alpha_buckets_safe for α-residue coherence.
        #     Odd  raw_steps → pick from uv_buckets_safe for nonlinear uv-hash mixing.
        #     This alternation keeps algebraic coherence while increasing the effective
        #     routing entropy, preventing single-basin trapping diagnosed by GPT.
        #   Tier 2 (cold, basin_dry_streak>0): uniform step selection.
        si = if basin_dry_streak == 0 && basin_buf_count > 0
            if (s.raw_steps & 1) == 0
                # Even step: α-residue bucket coherence
                cur_r  = mod(alpha_cur, ALPHA_MOD) + 1   # 1-based
                bucket = alpha_buckets_safe[cur_r]
                bucket[rand(1:length(bucket))]
            else
                # Odd step: uv-hash bucket for nonlinear diversity
                ha     = alpha_cur
                hb     = beta_cur
                h      = xor(ha, hb << 7) + xor(hb, ha >> 3)
                cur_r  = mod(h, UV_MOD) + 1
                cur_r  = clamp(cur_r, 1, UV_MOD)
                bucket = uv_buckets_safe[cur_r]
                bucket[rand(1:length(bucket))]
            end
        else
            rand(1:N_STEPS)
        end
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a_i[si], ellI)
        beta_cur  = beta_zero ? 0 : mod(beta_cur + step_b_i[si], ellI)
        is_last_si = si   # IS: remember which step index we used

        # Burst mode: probe hot_D with a fresh independent step.
        # All three of (D_eff, alpha_eff, beta_eff) use the same si_burst so
        # the divisor and scalar tracking stay consistent.
        D_eff     = D_cur
        alpha_eff = alpha_cur
        beta_eff  = beta_cur
        this_step_was_burst = burst_active
        if burst_active
            si_burst  = rand(1:N_STEPS)
            D_eff     = jac_add(hot_D_b2, step_D[si_burst])
            alpha_eff = mod(hot_alpha_b2 + step_a_i[si_burst], ellI)
            beta_eff  = beta_zero ? 0 : mod(hot_beta_b2 + step_b_i[si_burst], ellI)
            n_burst_steps_b2 += 1
            burst_budget -= 1
            burst_active  = burst_budget > 0
        end

        # --- Gate 1: D_eff must be a degree-2 divisor (generic Jacobian element) ---
        fp3_deg(D_eff.u) != 2 && continue

        u0 = D_eff.u[1]; u1 = D_eff.u[2]
        v0 = D_eff.v[1]; v1 = D_eff.v[2]
        px, py = cur_pt

        # --- Gate 2: P0 must not be in the support of D_eff ---
        upx = fp(fp(px*px) + fp(u1*px) + u0)
        upx == 0 && continue

        # --- Build φ and recover residual ---
        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a, b, c, _ = phi_c

        res_R, res_S, RS_mumford = phi_residual_mumford(a, b, c, px, u0, u1)
        RS_mumford === SENTINEL_MUMFORD && continue   # division failed

        s.hits_total += 1
        this_step_was_burst && (n_burst_valid_steps_b2 += 1)
        # Basin dry streak: advance on every valid step; reset inside record_basin_hit!
        # on LP1-conj hits.  Counting all valid steps (not just 3-LP) gives a more
        # accurate picture of how long we have been away from LP1-conj events.
        basin_dry_streak += 1
        # Steer observation countdown: tick down on every valid step.
        basin_steer_countdown > 0 && (basin_steer_countdown -= 1)
        # IS: advance per-step counters.
        is_steps_since_last_hit += 1
        # IS: tick all open yield-observation windows.
        tick_yield_windows!()
        # IS: tick down restart suppression counter.
        if is_suppress_restarts
            is_suppress_countdown -= 1
            if is_suppress_countdown <= 0; is_suppress_restarts = false; end
        end

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

        al     = alpha_eff
        be     = beta_eff
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
                let p0_basin_idx = get(pt2idx, P0, 0)
                    # basin_hit / IS updates gated on emission (after handle call)
                    # so basin_dry_streak reflects actual productive-step drought.
                    emit_before = s.hits_1lp_conj_emit
                    cur_pt = handle_1lp_conj!(lp_key32, i0, neg_al, neg_be, ell,
                                               fb, nF_cur, G, T,
                                               alpha_vec, beta_vec, rel_rows, rel_counter,
                                               ort, s, shared_lp1_conj, rank_growth,
                                               combined_scratch, P0, phi_bias_stat, next_anchor_ref)
                    if s.hits_1lp_conj_emit > emit_before
                        # An actual closure fired — credit basin + IS + burst.
                        record_basin_hit!(p0_basin_idx != 0 ? p0_basin_idx : anchor_cursor)
                        let _fbi = p0_basin_idx != 0 ? p0_basin_idx : anchor_cursor
                            is_record_hit!(_fbi, is_steps_since_last_hit)
                            is_global_rate_ema = (1 - is_global_ema_α) * is_global_rate_ema +
                                                 is_global_ema_α * (1.0 / max(1, is_steps_since_last_hit))
                            is_steps_since_last_hit = 0
                            is_reward_step!(is_last_si, 1.0)
                            # Credit any open yield windows (this hit falls within their horizon).
                            credit_yield_hit!(_fbi)
                            # Open new yield windows for this anchor.
                            open_yield_windows!(_fbi)
                            # Suppress IS restarts if this anchor has measured short halflife.
                            maybe_suppress_restarts!(_fbi)
                        end
                        burst_active && (n_burst_hits_b2 += 1)
                    end
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
            else
                cur_pt = next_anchor()
                record_random_anchor!(phi_bias_stat)
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
            # basin_dry_streak is now incremented globally at hits_total and reset
            # only inside record_basin_hit! on LP1-conj hits; do not touch it here.
            cur_pt = next_anchor()
            record_random_anchor!(phi_bias_stat)

        elseif n_lp == 1
            # ------------------------------------------------------------------
            #  1-LP affine: exactly one of P0, R, S is not in FB
            # ------------------------------------------------------------------
            if !enable_lp1_aff
                s.hits_skip += 1
                cur_pt = next_anchor()
                record_random_anchor!(phi_bias_stat)
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
            end  # enable_lp1_aff

        elseif n_lp == 2
            # ------------------------------------------------------------------
            #  2-LP affine: exactly two of P0, R, S are not in FB
            # ------------------------------------------------------------------
            if !enable_lp2
                s.hits_skip += 1
                cur_pt = next_anchor()
                record_random_anchor!(phi_bias_stat)
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
            end

        else
            # ------------------------------------------------------------------
            #  3-LP: discard step, advance structured cursor
            # ------------------------------------------------------------------
            s.hits_skip += 1
            # basin_dry_streak is now incremented globally on every valid step
            # at the hits_total site above; no separate increment needed here.
            cur_pt = next_anchor()
            record_random_anchor!(phi_bias_stat)
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
        if length(rank_growth) >= 2
            gaps = [rank_growth[i][1] - rank_growth[i-1][1]
                    for i in 2:min(10, length(rank_growth))]
            @printf("           first-emission raw step gaps (up to 10): %s\n",
                    join(string.(gaps), " "))
        end
        # Basin steer diagnostic report
        steer_hit_rate = basin_steers_fired > 0 ?
            100.0 * basin_steers_hit / basin_steers_fired : 0.0
        @printf("           basin_steers: fired=%d  credited_hits=%d  hit_rate=%.1f%%  buf_count=%d\n",
                basin_steers_fired, basin_steers_hit, steer_hit_rate, basin_buf_count)
        # Burst-exploitation efficiency: among all LP1-conj emissions, how many
        # occurred within BASIN_TRIGGER steps of a basin steer?  This separates
        # "steer actually helped" from "would have hit anyway via natural walk."
        # basin_steers_hit counts credited hits; compare to total emissions.
        lp1c_total = s.hits_1lp_conj_emit
        exploit_efficiency = lp1c_total > 0 ?
            100.0 * basin_steers_hit / lp1c_total : 0.0
        @printf("           burst-exploit: credited_hits=%d / total_lp1c_emit=%d = %.1f%% of emissions came within steer window\n",
                basin_steers_hit, lp1c_total, exploit_efficiency)
        burst_hit_rate = n_burst_valid_steps_b2 > 0 ? Float64(n_burst_hits_b2) / Float64(n_burst_valid_steps_b2) : 0.0
        cold_steps_b2  = s.hits_total - n_burst_valid_steps_b2
        cold_hits_b2   = s.hits_1lp_conj_emit - n_burst_hits_b2
        cold_rate_b2   = cold_steps_b2 > 0 ? Float64(cold_hits_b2) / Float64(cold_steps_b2) : 0.0
        @printf("           burst: budget=%d  burst_steps=%d  burst_valid=%d  burst_hits=%d  burst_rate=%.4f  cold_rate=%.4f  lift=%.2f\n",
                _burst_budget_default, n_burst_steps_b2, n_burst_valid_steps_b2, n_burst_hits_b2, burst_hit_rate, cold_rate_b2,
                cold_rate_b2 > 0 ? burst_hit_rate / cold_rate_b2 : 0.0)
        @printf("           ALPHA_MOD=%d (log2(ell)=%.1f)  UV_MOD=%d  INERTIA_FLIP=%.2f  BASIN_TRIGGER=%d\n",
                ALPHA_MOD, log2(max(2,ellI)), UV_MOD, INERTIA_FLIP_PROB, BASIN_TRIGGER)
        # IS diagnostics
        is_check_ess!()   # final ESS snapshot
        @printf("           IS: reservoir=%d/%d  ε_cur=%.3f  ESS=%.3f  entropy=%.3f  restarts=%d\n",
                length(is_reservoir), IS_RESERVOIR_CAP, ε_cur, is_ess_last,
                is_reservoir_entropy(), is_restart_count)
        if !isempty(is_reservoir)
            sorted_anchors = sort(is_reservoir, by=e->e.score, rev=true)
            top_is = min(3, length(sorted_anchors))
            @printf("           IS top-%d anchors (score, hits, fb_idx): %s\n",
                    top_is,
                    join(["($(round(e.score,digits=2)),$(e.hits),$(e.fb_idx))"
                          for e in sorted_anchors[1:top_is]], "  "))
            # Yield-curve report: for anchors with ≥2 yield observations, print the curve.
            yield_anchors = filter(e -> e.yield_obs[1] >= 2, sorted_anchors)
            if !isempty(yield_anchors)
                @printf("           IS yield curves (fb_idx: P(hit|500) P(hit|1000) P(hit|2000) P(hit|4000)  halflife):\n")
                for e in yield_anchors[1:min(4, length(yield_anchors))]
                    y = ntuple(k -> e.yield_obs[k] > 0 ? round(e.yield_hits[k] / e.yield_obs[k], digits=3) : 0.0, 4)
                    hl = e.halflife_est > 0 ? string(e.halflife_est) : "?"
                    @printf("             fb[%3d]: %.3f  %.3f  %.3f  %.3f  hl=%s\n",
                            e.fb_idx, y[1], y[2], y[3], y[4], hl)
                end
            else
                @printf("           IS yield curves: (not yet accumulated — need ≥2 obs per anchor)\n")
            end
        end
        if basin_buf_count > 0
            # Report top-3 hot anchors by hit count for spatial diagnostics.
            anchor_pairs = [(basin_hit_counts[mod(basin_buf_head - 1 - k + BASIN_BUF_SIZE, BASIN_BUF_SIZE) + 1],
                             basin_buf[mod(basin_buf_head - 1 - k + BASIN_BUF_SIZE, BASIN_BUF_SIZE) + 1])
                            for k in 1:basin_buf_count]
            sort!(anchor_pairs, rev=true)
            top_n = min(3, length(anchor_pairs))
            @printf("           top-%d hot anchors (hits, fb_idx): %s\n",
                    top_n, join(["($c,$i)" for (c,i) in anchor_pairs[1:top_n]], "  "))
        end
        flush(stdout)
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
            # IDEA 4 (enhanced): export hot-basin anchors with hit counts so
            # phase3 can warm-start near the algebraically hottest FB regions.
            # basin_hot_anchors is a Vector of (hit_count, fb_idx) pairs sorted
            # by hit_count descending.
            basin_hot_anchors = let
                pairs = [(basin_hit_counts[mod(basin_buf_head - 1 - k + BASIN_BUF_SIZE, BASIN_BUF_SIZE) + 1],
                          basin_buf[mod(basin_buf_head - 1 - k + BASIN_BUF_SIZE, BASIN_BUF_SIZE) + 1])
                         for k in 1:basin_buf_count if basin_buf[mod(basin_buf_head - 1 - k + BASIN_BUF_SIZE, BASIN_BUF_SIZE) + 1] != 0]
                sort!(pairs, rev=true)
                [p[2] for p in pairs]   # return just the fb indices, sorted by hotness
            end,
            basin_steers_fired = basin_steers_fired,
            basin_steers_hit   = basin_steers_hit,
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
            end)
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
