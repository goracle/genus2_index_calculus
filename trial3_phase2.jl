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
        ell            ::Int,
        alpha_vec      ::Vector{Int},
        beta_vec       ::Vector{Int},
        rel_rows       ::Vector{Dict{Int,Int}},
        rank_growth    ::Vector{Tuple{Int,Int}},
        raw_steps      ::Int,
        rel_counter    ::Threads.Atomic{Int},
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
    c_al = mod(2*neg_al_1 - al_d, ell)
    c_be = mod(2*neg_be_1 - be_d, ell)

    if ASSERT_RELATIONS
        D_sum = JacID
        for (idx, v) in combined
            D_fb = mumford1(fb[idx][1], fb[idx][2])
            D_v  = jac_mul_raw(D_fb, abs(v))
            D_sum = v > 0 ? jac_add(D_sum, D_v) : jac_sub(D_sum, D_v)
        end
        RHS    = jac_add(jac_mul(G, c_al), jac_mul(T, c_be))
        ok_pos = jac_isid(jac_sub(D_sum, RHS))
        ok_neg = jac_isid(jac_add(D_sum, RHS))
        if !(ok_pos || ok_neg)
            @printf("\n[!!!] LP-DOUBLED DIVISOR FAIL at pt=%s\n", pt)
            @printf("  Relation Check: Failed (Residual is NOT Identity)\n")
            @printf("  Divisor Sum (LHS): %s\n", string(D_sum))
            @printf("  Target (RHS):      %s\n", string(RHS))
            @printf("  Residual (LHS-RHS):%s\n", string(jac_sub(D_sum, RHS)))
            @printf("  Coefficients: al=%d, be=%d, weight=%d\n", c_al, c_be, length(combined))
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
    length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
        push!(rank_growth, (raw_steps, length(rel_rows)))
    Threads.atomic_add!(rel_counter, 1)
    return true
end

# ---------------------------------------------------------------------------
#  report_worker_progress — periodic per-thread status line
# ---------------------------------------------------------------------------
function report_worker_progress(tid, elapsed, s::WorkerStats, rel_counter, rel_target)
    @printf("[thread %2d | t=%6.1fs] raw=%d valid=%d 0lp=%d 1lp_emit=%d 1lp_step=%d 2lp_seen=%d 2lp_emit=%d skip=%d  rels_local=%d  global=%d/%d\n",
            tid, elapsed, s.raw_steps, s.hits_total, s.hits_0lp, s.hits_1lp_emit,
            s.hits_lp1, s.hits_lp2seen, s.hits_lp2emit, s.hits_skip,
            s.rel_local, rel_counter[], rel_target)
    @printf("           rates: phi_val=%.3f%%  full=%.3f%%  1lp=%.3f%%  2lp_seen=%.3f%%  2lp_emit=%.3f%%  skip=%.3f%%\n",
            100.0 * s.hits_total  / max(1, s.raw_steps),
            100.0 * s.hits_full   / max(1, s.hits_total),
            100.0 * s.hits_lp1    / max(1, s.hits_total),
            100.0 * s.hits_lp2seen/ max(1, s.hits_total),
            100.0 * s.hits_lp2emit/ max(1, s.hits_total),
            100.0 * s.hits_skip   / max(1, s.hits_total))
    @printf("           smoothness histogram (0-LP, 1-LP, 2-LP, 3-LP): %d %d %d %d\n",
            s.smooth_hist[1], s.smooth_hist[2], s.smooth_hist[3], s.smooth_hist[4])
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

# --- 0-LP: all three atoms are in the factor base → emit immediately. ---
@inline function emit_0lp!(fb_row     ::Dict{Int,Int},
                           neg_al     ::Int,
                           neg_be     ::Int,
                           fb         ::Vector{NTuple{2,Int}},
                           G          ::Div2,
                           T          ::Div2,
                           alpha_vec  ::Vector{Int},
                           beta_vec   ::Vector{Int},
                           rel_rows   ::Vector{Dict{Int,Int}},
                           rel_counter::Threads.Atomic{Int},
                           s          ::WorkerStats,
                           rank_growth::Vector{Tuple{Int,Int}})
    if ASSERT_RELATIONS
        @assert check_relation_principal(fb_row, neg_al, neg_be, "α", fb, G, T; tag="0LP-EMIT")
    end
    push!(alpha_vec, neg_al); push!(beta_vec, neg_be); push!(rel_rows, copy(fb_row))
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
        ell            ::Int,
        fb             ::Vector{NTuple{2,Int}},
        nF_cur         ::Int,
        G              ::Div2,
        T              ::Div2,
        alpha_vec      ::Vector{Int},
        beta_vec       ::Vector{Int},
        rel_rows       ::Vector{Dict{Int,Int}},
        rel_counter    ::Threads.Atomic{Int},
        s              ::WorkerStats,
        shared_lp1     ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        shared_lp1_lock::ReentrantLock,
        shared_lp_doubled::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        lp_col         ::LPResidualCollector,
        rank_growth    ::Vector{Tuple{Int,Int}},
        combined_scratch::Dict{Int,Int},
        iR             ::Int,
        iS             ::Int,
        R              ::Union{NTuple{2,Int},Nothing},
        S              ::Union{NTuple{2,Int},Nothing},
        P0             ::NTuple{2,Int})::NTuple{2,Int}

    record_lp1!(lp_col, lp_pt, al, be, s.raw_steps)

    closed = false
    lock(shared_lp1_lock)
    try
        if haskey(shared_lp1, lp_pt)
            # --- Close against stored entry ---
            prev_row, prev_al, prev_be, prev_step = shared_lp1[lp_pt]
            combined    = sparse_copy!(combined_scratch, fb_row)
            lp2_subtract_rows(combined, prev_row)
            combined_al = mod(neg_al - prev_al, ell)
            combined_be = mod(neg_be - prev_be, ell)
            delete!(shared_lp1, lp_pt)
            record_closure!(lp_col, s.raw_steps, prev_step)

            if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                if ASSERT_RELATIONS
                    @assert check_relation_principal(combined, combined_al, combined_be,
                                                     "α", fb, G, T; tag="1LP-CLOSE")
                end
                push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
                push!(rel_rows, copy(combined))
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
            # Evict one entry if the table is full (single-entry FIFO — avoids
            # evicting the entry we just inserted).
            if length(shared_lp1) >= MAX_LP1_ENTRIES
                for evict_key in keys(shared_lp1)
                    delete!(shared_lp1, evict_key); break
                end
            end
            shared_lp1[lp_pt] = (copy(fb_row), neg_al, neg_be, s.raw_steps)

            # Check whether the complementary doubled entry already exists.
            if try_lp1_doubled_cross_close!(lp_pt, shared_lp1, shared_lp_doubled,
                                            ell, alpha_vec, beta_vec, rel_rows,
                                            rank_growth, s.raw_steps, rel_counter,
                                            G, T, combined_scratch, fb)
                s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1; closed = true
            end
        end
    finally
        unlock(shared_lp1_lock)
    end

    # Next anchor: random FB point after closure; best non-LP atom otherwise.
    if closed;  return fb[rand(1:nF_cur)]
    elseif iR != 0; return R::NTuple{2,Int}
    elseif iS != 0; return S::NTuple{2,Int}
    else;           return P0
    end
end

# --- 1-LP conjugate: P0 is in FB; RS is a non-split Mumford pair. ---
#
# The LP key is the 4-tuple (c0, c1, v0, v1) of the Mumford u/v polynomials
# of the degree-2 residual.  We route to the correct shard, then either close
# against a stored entry (producing a relation between two FB columns with
# coefficients ±1) or store for future closure.
@inline function handle_1lp_conj!(
        lp_key         ::NTuple{4,Int},
        i0             ::Int,
        neg_al         ::Int,
        neg_be         ::Int,
        ell            ::Int,
        fb             ::Vector{NTuple{2,Int}},
        nF_cur         ::Int,
        G              ::Div2,
        T              ::Div2,
        alpha_vec      ::Vector{Int},
        beta_vec       ::Vector{Int},
        rel_rows       ::Vector{Dict{Int,Int}},
        rel_counter    ::Threads.Atomic{Int},
        s              ::WorkerStats,
        shared_lp1_conj::ShardedLP1Conj,
        rank_growth    ::Vector{Tuple{Int,Int}},
        P0             ::NTuple{2,Int})::NTuple{2,Int}

    si        = conj_shard_idx(lp_key)
    conj_dict = shared_lp1_conj.shards[si]
    conj_lock = shared_lp1_conj.locks[si]

    lock(conj_lock)
    try
        if haskey(conj_dict, lp_key)
            prev_col, prev_al, prev_be, _ = conj_dict[lp_key]
            combined_al = mod(neg_al - prev_al, ell)
            combined_be = mod(neg_be - prev_be, ell)
            delete!(conj_dict, lp_key)

            if !(combined_al == 0 && combined_be == 0) && i0 != prev_col
                # Relation: atom(fb[i0]) - atom(fb[prev_col]) = combined_al·G + combined_be·T
                combined = Dict{Int,Int}(i0 => 1, prev_col => -1)
                if ASSERT_RELATIONS
                    ok = check_relation_principal(combined, combined_al, combined_be,
                                                  "α", fb, G, T; tag="RS-CONJ-CLOSE")
                    if !ok
                        @printf("[RS-CONJ-CLOSE DIAG tid=%d] i0=%d prev_col=%d\n",
                                Threads.threadid(), i0, prev_col)
                        @printf("[RS-CONJ-CLOSE DIAG]  neg_al=%d neg_be=%d prev_al=%d prev_be=%d\n",
                                neg_al, neg_be, prev_al, prev_be)
                        @printf("[RS-CONJ-CLOSE DIAG]  lp_key=(c0=%d,c1=%d,v0=%d,v1=%d) i0=%d\n",
                                lp_key..., i0)
                    end
                    @assert ok "Conjugate-pair 1-LP closure failed principal divisor check"
                end
                push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
                push!(rel_rows, combined)
                length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                    push!(rank_growth, (s.raw_steps, length(rel_rows)))
                s.hits_full += 1; s.hits_1lp_emit += 1; s.rel_local += 1
                Threads.atomic_add!(rel_counter, 1)
                return fb[rand(1:nF_cur)]
            end
        else
            # Store: shard is capped per shard to MAX_LP1_CONJ_ENTRIES ÷ N_CONJ_SHARDS.
            if length(conj_dict) >= MAX_LP1_CONJ_ENTRIES ÷ N_CONJ_SHARDS
                empty!(conj_dict)   # evict entire shard — closures are too rare to cherry-pick
            end
            conj_dict[lp_key] = (i0, neg_al, neg_be, s.raw_steps)
        end
    finally
        unlock(conj_lock)
    end
    return P0
end

# --- 2-LP conjugate: P0 is not in FB; RS is a non-split Mumford pair. ---
#
# Insert an edge (P0, lp_key) into the extension-field LP2 graph.  The graph
# mixes affine-point nodes (NTuple{2,Int}) and Mumford-pair nodes (NTuple{4,Int}).
# An even cycle in this mixed graph yields a pure FB relation; an odd cycle
# produces a doubled residual that may cross-close with a stored 1-LP entry.
@inline function handle_2lp_conj!(
        P0                ::NTuple{2,Int},
        lp_key            ::NTuple{4,Int},
        neg_al            ::Int,
        neg_be            ::Int,
        ell               ::Int,
        fb                ::Vector{NTuple{2,Int}},
        nF_cur            ::Int,
        G                 ::Div2,
        T                 ::Div2,
        alpha_vec         ::Vector{Int},
        beta_vec          ::Vector{Int},
        rel_rows          ::Vector{Dict{Int,Int}},
        rel_counter       ::Threads.Atomic{Int},
        s                 ::WorkerStats,
        shared_lp1        ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        shared_lp1_lock   ::ReentrantLock,
        shared_lp_doubled ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        shared_lp2_conj   ::LP2ConjGraph,
        shared_lp2_conj_lock::ReentrantLock,
        max_lp2_conj_nodes::Int,
        rank_growth       ::Vector{Tuple{Int,Int}},
        combined_scratch  ::Dict{Int,Int})::NTuple{2,Int}

    s.hits_lp2seen += 1

    emitted_conj = nothing
    if lp2_graph_node_count(shared_lp2_conj) >= max_lp2_conj_nodes
        s.hits_lp2_cap += 1
    else
        lock(shared_lp2_conj_lock)
        try
            if lp2_graph_node_count(shared_lp2_conj) < max_lp2_conj_nodes
                emitted_conj = lp2c_insert_edge!(shared_lp2_conj, P0, lp_key,
                                                  Dict{Int,Int}(), neg_al, neg_be, ell)
            else
                s.hits_lp2_cap += 1
            end
        finally
            unlock(shared_lp2_conj_lock)
        end
    end

    emitted_conj === nothing && return fb[rand(1:nF_cur)]

    if emitted_conj.type === :even_cycle
        # Even cycle → full FB relation directly.
        push!(alpha_vec, emitted_conj.alpha); push!(beta_vec, emitted_conj.beta)
        push!(rel_rows, emitted_conj.row)
        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
            push!(rank_growth, (s.raw_steps, length(rel_rows)))
        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
        Threads.atomic_add!(rel_counter, 1)
        if ASSERT_RELATIONS
            @assert check_relation_principal(emitted_conj.row, emitted_conj.alpha,
                                             emitted_conj.beta, "α", fb, G, T; tag="QLP-CONJ-CYCLE")
        end
        return fb[rand(1:nF_cur)]

    elseif emitted_conj.type === :odd_cycle
        # Odd cycle → the root contributes 2·atom(root) to the divisor sum.
        # If the root is an affine point, try to pair with a stored 1-LP entry
        # (try_lp1_doubled_cross_close!), or park in shared_lp_doubled for
        # a future 1-LP closure to consume.
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
                        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                            push!(rank_growth, (s.raw_steps, length(rel_rows)))
                        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        Threads.atomic_add!(rel_counter, 1)
                    end
                else
                    # Park: store 2·atom(root) for a future 1-LP entry to consume.
                    shared_lp_doubled[root_affine] = (emitted_conj.row, emitted_conj.alpha, emitted_conj.beta)
                    if try_lp1_doubled_cross_close!(root_affine, shared_lp1, shared_lp_doubled,
                                                    ell, alpha_vec, beta_vec, rel_rows,
                                                    rank_growth, s.raw_steps, rel_counter,
                                                    G, T, combined_scratch, fb)
                        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                    end
                end
            finally
                unlock(shared_lp1_lock)
            end
        end
        return fb[rand(1:nF_cur)]
    end

    return fb[rand(1:nF_cur)]
end

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
        ell            ::Int,
        fb             ::Vector{NTuple{2,Int}},
        nF_cur         ::Int,
        G              ::Div2,
        T              ::Div2,
        alpha_vec      ::Vector{Int},
        beta_vec       ::Vector{Int},
        rel_rows       ::Vector{Dict{Int,Int}},
        rel_counter    ::Threads.Atomic{Int},
        s              ::WorkerStats,
        shared_lp1     ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
        shared_lp1_lock::ReentrantLock,
        shared_lp2     ::LP2Graph,
        shared_lp2_lock::ReentrantLock,
        shared_lp_doubled::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
        lp_col         ::LPResidualCollector,
        max_lp2_nodes  ::Int,
        rank_growth    ::Vector{Tuple{Int,Int}},
        combined_scratch::Dict{Int,Int})::NTuple{2,Int}

    s.hits_lp2seen += 1

    # Identify the two non-FB atoms.
    lp2_a, lp2_b = if i0 == 0 && iR == 0;  P0, R
                   elseif i0 == 0 && iS == 0;  P0, S
                   else;                        R, S   # iR==0 && iS==0
                   end

    record_lp2!(lp_col, lp2_a, lp2_b, s.raw_steps)

    # fb_row_scratch is already populated by the caller (the n_lp == 2 branch
    # in phase2_worker builds it before dispatching here).

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
                    RHS = jac_add(jac_mul(G, α), jac_mul(T, β))
                    if !(jac_isid(jac_sub(D_sum, RHS)) || jac_isid(jac_add(D_sum, RHS)))
                        @printf("[LP2-DIAG tid=%d] FAIL  alpha=%d beta=%d  row_weight=%d  root_signs=(%d,%d)  depths=(%d,%d)\n",
                                Threads.threadid(), α, β, length(row),
                                emitted_rel.root_signs[1], emitted_rel.root_signs[2],
                                emitted_rel.depths[1], emitted_rel.depths[2])
                        @printf("  lp2_a=%s  lp2_b=%s  i0=%d iR=%d iS=%d\n",
                                string(lp2_a), string(lp2_b), i0, iR, iS)
                        @printf("  row = %s\n", string(row))
                        lock(shared_lp2_lock)
                        try; clear_lp2_graph!(shared_lp2); finally; unlock(shared_lp2_lock); end
                    end
                end
            end
            return fb[rand(1:nF_cur)]

        elseif emitted_rel !== nothing && emitted_rel.type === :odd_cycle
            # Odd cycle from LP2 graph: the root contributes 2·atom(root) to the
            # divisor sum.  Attempt the same doubled cross-close as in the conj case.
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
                        length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                            push!(rank_growth, (s.raw_steps, length(rel_rows)))
                        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                        Threads.atomic_add!(rel_counter, 1)
                    end
                else
                    shared_lp_doubled[root] = (emitted_rel.row, emitted_rel.alpha, emitted_rel.beta)
                    if try_lp1_doubled_cross_close!(root, shared_lp1, shared_lp_doubled,
                                                    ell, alpha_vec, beta_vec, rel_rows,
                                                    rank_growth, s.raw_steps, rel_counter,
                                                    G, T, combined_scratch, fb)
                        s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                    end
                end
            finally
                unlock(shared_lp1_lock)
            end
        end
    end   # end LP2 graph insertion block

    # --- Cross-close with existing 1-LP entries ---
    #
    # A 2-LP step can be resolved without the LP2 graph if one of the two LP
    # atoms (lp2_a or lp2_b) already has a stored 1-LP entry.  Combining the
    # fb_row of this step with the stored row eliminates that atom, leaving a
    # 1-LP entry for the other atom.  If the other atom is also stored, we get
    # a full relation immediately.
    #
    # We check (lp2_a, lp2_b) and (lp2_b, lp2_a) in order; only the first
    # match is acted on (to avoid double-counting).
    lock(shared_lp1_lock)
    try
        for (lp_known, lp_other) in ((lp2_a, lp2_b), (lp2_b, lp2_a))
            haskey(shared_lp1, lp_known) || continue

            r_known, na_known, nb_known, _step_known = shared_lp1[lp_known]
            # Derived 1-LP entry for lp_other:
            #   atom(lp_other) + (fb_row - r_known) = (neg_al - na_known)·G + (neg_be - nb_known)·T
            new_row    = copy(fb_row_scratch)
            for (j, v) in r_known
                nv = get(new_row, j, 0) - v
                nv == 0 ? delete!(new_row, j) : (new_row[j] = nv)
            end
            new_neg_al = mod(neg_al - na_known, ell)
            new_neg_be = mod(neg_be - nb_known, ell)

            s.hits_lp2_cross += 1

            if haskey(shared_lp1, lp_other)
                # lp_other is also stored → full relation.
                prev_row, prev_al, prev_be, prev_step = shared_lp1[lp_other]
                combined    = copy(new_row)
                lp2_subtract_rows(combined, prev_row)
                combined_al = mod(new_neg_al - prev_al, ell)
                combined_be = mod(new_neg_be - prev_be, ell)
                delete!(shared_lp1, lp_other)
                record_closure!(lp_col, s.raw_steps, prev_step)
                if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                    if ASSERT_RELATIONS
                        @assert check_relation_principal(combined, combined_al, combined_be,
                                                         "α", fb, G, T; tag="2LP-CROSS-CLOSE")
                    end
                    push!(alpha_vec, combined_al); push!(beta_vec, combined_be)
                    push!(rel_rows, combined)
                    length(rank_growth) < MAX_RANK_GROWTH_SAMPLES &&
                        push!(rank_growth, (s.raw_steps, length(rel_rows)))
                    s.hits_full += 1; s.hits_1lp_emit += 1; s.rel_local += 1
                    Threads.atomic_add!(rel_counter, 1)
                end
            else
                # Store derived 1-LP entry for lp_other.
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
                                                G, T, combined_scratch, fb)
                    s.hits_full += 1; s.hits_lp2emit += 1; s.rel_local += 1
                end
            end
            break   # only act on the first match
        end
    finally
        unlock(shared_lp1_lock)
    end

    # Next anchor: prefer a non-LP atom if available.
    if i0 != 0;  return P0
    elseif iR != 0; return R
    elseif iS != 0; return S
    else;           return fb[rand(1:nF_cur)]
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
function phase2_worker(G               ::Div2,
                       T               ::Div2,
                       fb              ::Vector{NTuple{2,Int}},
                       pt2idx          ::Dict{NTuple{2,Int},Int},
                       step_D          ::Vector{Div2},
                       step_a          ::Vector{Int},
                       step_b          ::Vector{Int},
                       rel_counter     ::Threads.Atomic{Int},
                       rel_target      ::Int,
                       step_cap        ::Int,
                       shared_lp1      ::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
                       shared_lp1_lock ::ReentrantLock,
                       shared_lp2      ::LP2Graph,
                       shared_lp2_lock ::ReentrantLock,
                       shared_lp_doubled::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
                       shared_lp1_conj ::ShardedLP1Conj,
                       shared_lp2_conj ::LP2ConjGraph,
                       shared_lp2_conj_lock::ReentrantLock,
                       enable_lp2_conj ::Bool,
                       max_lp2_nodes   ::Int,
                       max_lp2_conj_nodes::Int,
                       lp_col          ::LPResidualCollector;
                       verbose         ::Bool = true)

    nF_cur   = length(fb)
    N_STEPS  = length(step_D)
    tid      = Threads.threadid()
    t_start  = time()

    # --- Walk state ---
    cur_pt    = fb[rand(1:nF_cur)]
    alpha_cur = rand(1:ell-1)
    beta_cur  = rand(0:ell-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur), jac_mul(T, beta_cur))

    # --- Per-thread relation accumulation ---
    hint = max(64, cld(rel_target, Threads.nthreads()) + 32)
    alpha_vec = sizehint!(Int[], hint)
    beta_vec  = sizehint!(Int[], hint)
    rel_rows  = sizehint!(Vector{Dict{Int,Int}}(), hint)

    # --- Counters (collected in WorkerStats at the end) ---
    s = WorkerStats()

    # --- Scratch dicts (reused every step to avoid per-step allocation) ---
    fb_row_scratch   = sizehint!(Dict{Int,Int}(), 4)
    combined_scratch = sizehint!(Dict{Int,Int}(), 8)

    # --- Diagnostics ---
    sample_rels  = Vector{Tuple{Div2,Dict{Int,Int},Int,Int,NTuple{2,Int},NTuple{2,Int},NTuple{2,Int}}}()
    rank_growth  = Tuple{Int,Int}[]
    t_last_report = time()
    report_interval_secs = 30.0

    # LP2 node-count cache: checking length(shared_lp2.nodes) under the lock
    # every step is expensive.  We cache the count and only refresh it when
    # we actually need to insert an edge (or every CHECK_INTERVAL steps).
    lp2_node_cache     = 0
    lp2_check_interval = 256
    lp2_check_countdown = 0

    # ==========================================================================
    #  Main walk loop
    # ==========================================================================
    while rel_counter[] < rel_target && s.raw_steps < step_cap
        s.raw_steps += 1

        # --- Take a random precomputed step ---
        si        = rand(1:N_STEPS)
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a[si], ell)
        beta_cur  = mod(beta_cur  + step_b[si], ell)

        # --- Gate 1: D_cur must be a degree-2 divisor (generic Jacobian element) ---
        fp3_deg(D_cur.u) != 2 && continue

        u0 = D_cur.u[1]; u1 = D_cur.u[2]
        v0 = D_cur.v[1]; v1 = D_cur.v[2]
        px, py = cur_pt

        # --- Gate 2: P0 must not be in the support of D_cur ---
        upx = fp(fp(px*px) + fp(u1*px) + u0)
        upx == 0 && continue

        # --- Build φ and recover residual ---
        phi_c = build_phi_mumford(px, py, u0, u1, v0, v1)
        phi_c === nothing && continue
        a, b, c, _ = phi_c

        res = phi_residual_mumford(a, b, c, px, u0, u1)
        res === nothing && continue

        s.hits_total += 1

        # --- Periodic progress report ---
        if verbose
            now_t = time()
            if (now_t - t_last_report) >= report_interval_secs
                s.raw_steps = s.raw_steps   # flush to struct (it's already there)
                report_worker_progress(tid, now_t - t_start, s, rel_counter, rel_target)
                t_last_report = now_t
            end
        end

        al     = alpha_cur
        be     = beta_cur
        neg_al = mod(ell - al, ell)
        neg_be = mod(ell - be, ell)
        P0     = cur_pt
        i0     = get(pt2idx, P0, 0)

        rs_split   = res[1] !== nothing
        R          = rs_split ? res[1]::NTuple{2,Int}   : nothing
        S          = rs_split ? res[2]::NTuple{2,Int}   : nothing
        RS_mumford = rs_split ? nothing : res[3]::NTuple{4,Int}

        # ==========================================================================
        #  BRANCH A: conjugate residual (RS is a degree-2 Mumford pair over F_p²)
        # ==========================================================================
        if !rs_split
            lp_key = RS_mumford::NTuple{4,Int}
            if i0 != 0
                # P0 ∈ FB, RS ∉ F_p → 1-LP conjugate
                s.hits_lp1 += 1
                cur_pt = handle_1lp_conj!(lp_key, i0, neg_al, neg_be, ell,
                                           fb, nF_cur, G, T,
                                           alpha_vec, beta_vec, rel_rows, rel_counter,
                                           s, shared_lp1_conj, rank_growth, P0)
            elseif enable_lp2_conj
                # P0 ∉ FB, RS ∉ F_p → 2-LP conjugate (both "atoms" are non-affine)
                cur_pt = handle_2lp_conj!(P0, lp_key, neg_al, neg_be, ell,
                                           fb, nF_cur, G, T,
                                           alpha_vec, beta_vec, rel_rows, rel_counter,
                                           s, shared_lp1, shared_lp1_lock,
                                           shared_lp_doubled,
                                           shared_lp2_conj, shared_lp2_conj_lock,
                                           max_lp2_conj_nodes, rank_growth,
                                           combined_scratch)
            else
                cur_pt = fb[rand(1:nF_cur)]
            end
            continue
        end

        # ==========================================================================
        #  BRANCH B: split residual (R, S are both F_p-rational)
        # ==========================================================================
        iR = get(pt2idx, R::NTuple{2,Int}, 0)
        iS = get(pt2idx, S::NTuple{2,Int}, 0)
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
                      alpha_vec, beta_vec, rel_rows, rel_counter, s, rank_growth)
            if length(sample_rels) < 10
                push!(sample_rels, (D_cur, copy(fb_row_scratch), neg_al, neg_be,
                                    P0, R::NTuple{2,Int}, S::NTuple{2,Int}))
            end
            cur_pt = fb[rand(1:nF_cur)]

        elseif n_lp == 1
            # ------------------------------------------------------------------
            #  1-LP affine: exactly one of P0, R, S is not in FB
            # ------------------------------------------------------------------
            s.hits_lp1 += 1
            lp_pt = i0 == 0 ? P0 : iR == 0 ? R::NTuple{2,Int} : S::NTuple{2,Int}

            empty!(fb_row_scratch)
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end

            cur_pt = handle_1lp_affine!(lp_pt, fb_row_scratch, al, be, neg_al, neg_be,
                                         ell, fb, nF_cur, G, T,
                                         alpha_vec, beta_vec, rel_rows, rel_counter, s,
                                         shared_lp1, shared_lp1_lock, shared_lp_doubled,
                                         lp_col, rank_growth, combined_scratch,
                                         iR, iS, R, S, P0)

        elseif n_lp == 2
            # ------------------------------------------------------------------
            #  2-LP affine: exactly two of P0, R, S are not in FB
            # ------------------------------------------------------------------
            empty!(fb_row_scratch)
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end

            cur_pt = handle_2lp_affine!(i0, iR, iS,
                                         R::NTuple{2,Int}, S::NTuple{2,Int}, P0,
                                         fb_row_scratch, neg_al, neg_be,
                                         ell, fb, nF_cur, G, T,
                                         alpha_vec, beta_vec, rel_rows, rel_counter, s,
                                         shared_lp1, shared_lp1_lock,
                                         shared_lp2, shared_lp2_lock,
                                         shared_lp_doubled,
                                         lp_col, max_lp2_nodes, rank_growth,
                                         combined_scratch)

        else
            # ------------------------------------------------------------------
            #  3-LP: discard step, jump to a random FB point
            # ------------------------------------------------------------------
            s.hits_skip += 1
            cur_pt = fb[rand(1:nF_cur)]
        end
    end   # end main walk loop

    # ==========================================================================
    #  Final report
    # ==========================================================================
    elapsed_total = time() - t_start
    if verbose
        @printf("[thread %2d | DONE | t=%.1fs] raw=%d valid=%d 0lp=%d 1lp_emit=%d 1lp_step=%d 2lp_seen=%d 2lp_emit=%d 2lp_cross=%d 2lp_odd=%d 2lp_cap=%d skip=%d  rels_local=%d\n",
                tid, elapsed_total, s.raw_steps, s.hits_total, s.hits_0lp, s.hits_1lp_emit,
                s.hits_lp1, s.hits_lp2seen, s.hits_lp2emit, s.hits_lp2_cross, s.hits_lp2_odd,
                s.hits_lp2_cap, s.hits_skip, length(rel_rows))
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
            hits_lp2seen  = s.hits_lp2seen,
            hits_lp2emit  = s.hits_lp2emit,
            hits_lp2_cross= s.hits_lp2_cross,
            hits_lp2_odd  = s.hits_lp2_odd,
            hits_lp2_cap  = s.hits_lp2_cap,
            hits_skip     = s.hits_skip,
            sample_rels   = sample_rels,
            total_steps   = s.raw_steps,
            smooth_hist   = s.smooth_hist,
            rank_growth   = rank_growth,
            lp_col        = lp_col)
end
