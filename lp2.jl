# =============================================================================
#  lp2.jl  --  2-Large-Prime graph structures and helpers
#
#  Included by trial3_fixed.jl.  Requires: ell (global), fp/fpinv (from trial1),
#  Div2/jac_* types, and the sparse_add!/lp2_subtract_rows helpers.
#
#  KEY CHANGE vs. previous version:
#    LP2Node now stores a SmallRow (not a single edge_col/edge_val pair) for the
#    edge-to-parent label.  This enables cross-tree merges: when both L and R are
#    already in the graph but in *different* spanning trees, we walk both paths to
#    their respective roots, compose the two SmallRows plus the new edge into a
#    single composite SmallRow, and attach rR as a depth-1 child of rL.  The
#    composite row records the full path contribution in one hop so subsequent
#    lp2_path_to_root walks remain allocation-free and depth-bounded.
#
#    Previously cross-tree merges were silently discarded, which meant that at
#    large p the graph accumulated tens of thousands of disconnected depth-1/2
#    stubs and almost never formed a cycle.  This produced zero 2-LP emissions and
#    a large null-space dimension (~1000) in the relation matrix.
# =============================================================================

function lp2_subtract_rows(dst::Dict{Int,Int}, src::Dict{Int,Int})
    for (j, v) in src
        nv = get(dst, j, 0) - v
        nv == 0 ? delete!(dst, j) : (dst[j] = nv)
    end
    return dst
end

# ── Stack-allocated sparse row ────────────────────────────────────────────────
#
# SmallRow: fixed-capacity inline sparse row, allocation-free.
#
# Capacity notes:
#   - A single incoming edge has at most 1 nonzero (one FB point per 2-LP step).
#   - A path of depth D accumulates at most D nonzeros after cancellations.
#   - A cross-tree merge composes two depth-≤MAX_LP2_DEPTH paths plus 1 edge,
#     so the composite row has at most 2*MAX_LP2_DEPTH + 1 = 13 nonzeros before
#     cancellation.  We use capacity 16 (next power of 2 above 13).
#   - At cycle-emit time the combined row from two depth-≤MAX_LP2_DEPTH paths
#     has at most 2*MAX_LP2_DEPTH + 1 nonzeros, same bound.
#
# SMALL_ROW_CAP = 16 covers all cases.

const SMALL_ROW_CAP = 16

struct SmallRow
    cols::NTuple{SMALL_ROW_CAP, Int}
    vals::NTuple{SMALL_ROW_CAP, Int}
    len ::Int
end

SmallRow() = SmallRow(ntuple(_->0, SMALL_ROW_CAP), ntuple(_->0, SMALL_ROW_CAP), 0)

@inline function smallrow_add(r::SmallRow, col::Int, sv::Int)::SmallRow
    sv == 0 && return r
    cols = r.cols; vals = r.vals; len = r.len
    for i in 1:len
        if cols[i] == col
            nv = vals[i] + sv
            if nv == 0
                # Remove entry i by swapping with last.
                new_cols = Base.setindex(Base.setindex(cols, cols[len], i), 0, len)
                new_vals = Base.setindex(Base.setindex(vals, vals[len], i), 0, len)
                return SmallRow(new_cols, new_vals, len - 1)
            else
                return SmallRow(Base.setindex(cols, col, i),
                                Base.setindex(vals, nv,  i), len)
            end
        end
    end
    # New entry.
    if len >= SMALL_ROW_CAP
        # Capacity overflow — should not happen given the depth bounds above.
        # Silently drop rather than corrupt; the resulting composite may be
        # heavier than intended but won't be wrong (missing FB entries make the
        # emitted relation fail the principal-divisor assert, which surfaces it).
        return r
    end
    return SmallRow(Base.setindex(cols, col,  len+1),
                    Base.setindex(vals, sv,   len+1), len + 1)
end

# Add a single (col, val) entry scaled by sign into a SmallRow.
@inline function smallrow_add_entry(r::SmallRow, col::Int, val::Int, sign::Int)::SmallRow
    col == 0 && return r   # sentinel: no FB contribution
    smallrow_add(r, col, sign * val)
end

# Merge all entries of src (scaled by sign) into dst.  Allocation-free.
@inline function smallrow_merge(dst::SmallRow, src::SmallRow, sign::Int)::SmallRow
    r = dst
    for i in 1:src.len
        r = smallrow_add(r, src.cols[i], sign * src.vals[i])
    end
    return r
end

# Add a single Dict entry into a SmallRow (used when absorbing fb_row at edges).
@inline function smallrow_add_dict_entry(r::SmallRow, col::Int, val::Int)::SmallRow
    smallrow_add(r, col, val)
end

# Spill SmallRow into a Dict{Int,Int} (only at cycle-emit time — rare).
function smallrow_to_dict(r::SmallRow)::Dict{Int,Int}
    d = Dict{Int,Int}()
    sizehint!(d, r.len)
    for i in 1:r.len
        d[r.cols[i]] = r.vals[i]
    end
    return d
end

# Subtract a SmallRow from a Dict{Int,Int} (rare: only at cycle-emit time).
function smallrow_subtract_into_dict!(dst::Dict{Int,Int}, r::SmallRow)
    for i in 1:r.len
        col = r.cols[i]; v = r.vals[i]
        nv = get(dst, col, 0) - v
        nv == 0 ? delete!(dst, col) : (dst[col] = nv)
    end
end

# Add a SmallRow into a Dict{Int,Int}.
function smallrow_add_into_dict!(dst::Dict{Int,Int}, r::SmallRow)
    for i in 1:r.len
        col = r.cols[i]; v = r.vals[i]
        nv = get(dst, col, 0) + v
        nv == 0 ? delete!(dst, col) : (dst[col] = nv)
    end
end

# ---------------------------------------------------------------------------
#  LP2Graph — shared 2-large-prime graph for cycle-based relation emission
#
#  Invariant: each LP node v stores
#    parent[v]      — the parent node key (nothing for roots)
#    depth[v]       — distance from v to its root
#    edge_row[v]    — SmallRow for the FB contribution of the edge v→parent(v)
#    edge_alpha[v]  — alpha coefficient of the edge v→parent(v)
#    edge_beta[v]   — beta  coefficient of the edge v→parent(v)
#
#  Each edge (L, R, fb_row, alpha, beta) in the original 2-LP graph encodes:
#
#      atom(L) + atom(R) + fb_row  ==  alpha*G + beta*T         ... (*)
#
#  When traversing child→parent along edge v, the contribution to a path sum is:
#    +edge_row[v], +edge_alpha[v], +edge_beta[v]
#  When traversing parent→child (i.e., against the stored direction), the sign flips.
#  lp2_path_to_root alternates signs as it walks, starting with sign=+1 at the
#  first node and flipping at each step.
#
#  Cross-tree merge:
#    When edge (L, R) arrives and both L (in tree T_L rooted at rL) and R (in tree
#    T_R rooted at rR) already exist but rL ≠ rR, we merge the trees by walking
#    both paths to their roots, composing the path rows into a single SmallRow, and
#    storing rR as a depth-1 child of rL with the composite edge.  This collapses
#    the two trees into one; future edges may then form a cycle.
#
#    Composite edge label for rR→rL:
#      The path from rR through R → L through rL expresses:
#        path_R (from rR to R) + new_edge (L,R) + path_L (from L to rL)
#      Combined row  = pathR.row  +  fb_row  +  pathL.row    (all with appropriate signs)
#      Combined alpha = pathR.alpha + alpha - pathL.alpha
#      Combined beta  = pathR.beta  + beta  - pathL.beta
#      (signs derived from the alternating-sign convention in lp2_path_to_root;
#       see inline derivation in lp2_insert_edge!)
#
#  Thread safety:
#    Shared across all walker threads behind a single ReentrantLock.
#    Lock held only during graph mutation — O(depth) work, bounded by MAX_LP2_DEPTH.
# ---------------------------------------------------------------------------

const MAX_LP2_DEPTH       = 6    # max spanning-tree depth; prevents row blowup
const MAX_LP2_ROW_WEIGHT  = 24   # max nonzeros in an emitted 2-LP relation

# Hard cap on total nodes.  When reached the graph is cleared entirely.
# At ~200 bytes per node (SmallRow inlined, no Dict per node), 250_000 nodes ≈ 50 MB.
const MAX_LP2_NODES = 50_000

struct LP2Node
    parent    ::Union{NTuple{2,Int}, Nothing}   # nothing = root
    depth     ::Int
    # Edge to parent: SmallRow encodes all FB contributions along this edge.
    # For direct insertions this has at most 1 entry; for cross-tree composite
    # edges it may have up to 2*MAX_LP2_DEPTH+1 entries (bounded by SMALL_ROW_CAP).
    edge_row  ::SmallRow
    edge_alpha::Int
    edge_beta ::Int
end

mutable struct LP2Graph
    nodes             ::Dict{NTuple{2,Int}, LP2Node}
    n_edges_inserted  ::Int
    n_cycles_found    ::Int
    n_emitted         ::Int
    n_depth_pruned    ::Int
    n_weight_pruned   ::Int
    n_parity_pruned   ::Int
    n_odd_stored      ::Int
    n_merges          ::Int   # successful cross-tree merges
    n_clears          ::Int
end

function LP2Graph()
    LP2Graph(
        Dict{NTuple{2,Int}, LP2Node}(),
        0, 0, 0, 0, 0, 0, 0, 0, 0
    )
end

# Walk from pt to its root.  Returns root key or nothing if pt not in tree.
#
# After cross-tree merges, grafted subtree nodes retain stale depth fields; their
# actual depth to the new root can exceed MAX_LP2_DEPTH.  We use a generous step
# budget so valid (acyclic) merged trees always terminate, and return nothing
# (rather than throwing) if the budget is exceeded.
const _LP2_ROOT_STEP_LIMIT = MAX_LP2_DEPTH * MAX_LP2_DEPTH + MAX_LP2_DEPTH + 4

function lp2_tree_root(g::LP2Graph, pt::NTuple{2,Int})
    cur   = pt
    steps = 0
    while true
        node = get(g.nodes, cur, nothing)
        node === nothing && return nothing
        node.parent === nothing && return cur
        steps += 1
        if steps > _LP2_ROOT_STEP_LIMIT
            # Stale depths or true cycle — delete the stuck node and bail.
            delete!(g.nodes, cur)
            return nothing
        end
        cur = node.parent
    end
end

# Walk from start to root, accumulating SmallRow and alpha/beta with alternating signs.
# sign_node starts at +1 for the first edge (start→parent(start)) and flips each hop.
# Returns (row, alpha, beta, root_sign, depth) or nothing if depth exceeded.
function lp2_path_to_root(g::LP2Graph, start::NTuple{2,Int}, ell::Int)
    row       = SmallRow()
    alpha     = 0
    beta      = 0
    sign_node = 1
    cur       = start
    depth     = 0
    while true
        node = get(g.nodes, cur, nothing)
        if node === nothing || node.parent === nothing
            break
        end

        depth += 1
        if depth > MAX_LP2_DEPTH
            return nothing
        end

        row   = smallrow_merge(row, node.edge_row, sign_node)
        alpha = mod(alpha + sign_node * node.edge_alpha, ell)
        beta  = mod(beta  + sign_node * node.edge_beta,  ell)

        sign_node = -sign_node
        cur = node.parent
    end
    return (row=row, alpha=alpha, beta=beta, root_sign=-sign_node, depth=depth)
end


# ---------------------------------------------------------------------------
#  lp2_insert_edge!
#
#  Try to insert edge (L, R) with label (fb_row, alpha, beta).
#
#  fb_row has at most 1 entry (one FB point per 2-LP step).  We convert it to a
#  SmallRow for node storage, avoiding per-node Dict allocation.
#
#  Cases:
#   (a) Neither L nor R in graph → create fresh two-node tree (R=root, L→R).
#   (b) L not in graph, R exists → attach L as new leaf of R's tree.
#   (c) R not in graph, L exists → attach R as new leaf of L's tree.
#   (d) Both in same tree → cycle detected; emit or prune.
#   (e) Both in different trees → cross-tree merge (previously discarded, now fixed).
#
#  Returns an emitted relation namedtuple or nothing.
# ---------------------------------------------------------------------------
function lp2_insert_edge!(g::LP2Graph,
                          L::NTuple{2,Int}, R::NTuple{2,Int},
                          fb_row::Dict{Int,Int},
                          alpha::Int, beta::Int,
                          ell::Int)

    g.n_edges_inserted += 1
    L == R && return nothing

    # Convert fb_row to a SmallRow (at most 1 entry).
    edge_sr = SmallRow()
    for (j, v) in fb_row
        edge_sr = smallrow_add(edge_sr, j, v)
        break   # at most one entry
    end

    rL = lp2_tree_root(g, L)
    rR = lp2_tree_root(g, R)

    # ── Case (d): same-tree cycle ────────────────────────────────────────────
    if rL !== nothing && rR !== nothing && rL == rR
        g.n_cycles_found += 1

        pathL = lp2_path_to_root(g, L, ell)
        pathR = lp2_path_to_root(g, R, ell)

        if pathL === nothing || pathR === nothing
            g.n_depth_pruned += 1
            return nothing
        end

        if pathL.root_sign == pathR.root_sign
            # Odd cycle.
            g.n_parity_pruned += 1
            g.n_odd_stored    += 1
            s = pathL.root_sign

            odd_row = Dict{Int,Int}()
            smallrow_subtract_into_dict!(odd_row, pathL.row)
            smallrow_subtract_into_dict!(odd_row, pathR.row)
            smallrow_add_into_dict!(odd_row, edge_sr)
            if s == -1
                for k in keys(odd_row); odd_row[k] = -odd_row[k]; end
            end

            odd_alpha = mod(s * (pathL.alpha + pathR.alpha - alpha), ell)
            odd_beta  = mod(s * (pathL.beta  + pathR.beta  - beta),  ell)

            if length(odd_row) > MAX_LP2_ROW_WEIGHT
                g.n_weight_pruned += 1
                return nothing
            end
            return (type=:odd_cycle, root=rL,
                    row=odd_row, alpha=odd_alpha, beta=odd_beta,
                    debug=(L=L, R=R, rL=rL, rR=rR,
                           sL=pathL.root_sign, sR=pathR.root_sign,
                           depth_L=pathL.depth, depth_R=pathR.depth,
                           edge_row=smallrow_to_dict(edge_sr),
                           pathL=pathL, pathR=pathR))
        end

        # Even cycle.
        combined = Dict{Int,Int}()
        smallrow_add_into_dict!(combined, edge_sr)
        smallrow_subtract_into_dict!(combined, pathL.row)
        smallrow_subtract_into_dict!(combined, pathR.row)

        if length(combined) > MAX_LP2_ROW_WEIGHT
            g.n_weight_pruned += 1
            return nothing
        end

        # Swap the subtraction order (around lines 155-156)
        combined_alpha = mod(pathL.alpha + pathR.alpha - alpha, ell)
        combined_beta  = mod(pathL.beta  + pathR.beta  - beta,  ell)

        if isempty(combined) || (combined_alpha == 0 && combined_beta == 0)
            return nothing
        end

        g.n_emitted += 1
        lp2_prune_component!(g, rL)

        return (type=:even_cycle,
                row=combined,
                alpha=combined_alpha,
                beta=combined_beta,
                root_signs=(pathL.root_sign, pathR.root_sign),
                depths=(pathL.depth, pathR.depth),
                debug=(L=L, R=R, rL=rL, rR=rR,
                       sL=sL, sR=sR,
                       depth_L=node_L.depth, depth_R=node_R.depth,
                       edge_row=smallrow_to_dict(edge_sr),
                       pathL=pathL, pathR=pathR))
    end

    # ── Node cap: evict before inserting new nodes ───────────────────────────
    if length(g.nodes) >= MAX_LP2_NODES
        empty!(g.nodes)
        g.n_clears += 1
        # Re-read roots after clear — both are now nothing.
        rL = nothing
        rR = nothing
    end

    node_L = get(g.nodes, L, nothing)
    node_R = get(g.nodes, R, nothing)

    # ── Case (a): both new ───────────────────────────────────────────────────
    if node_L === nothing && node_R === nothing
        # depth check: the L node will be at depth 1
        if 1 > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end
        g.nodes[R] = LP2Node(nothing, 0, SmallRow(), 0, 0)
        g.nodes[L] = LP2Node(R, 1, edge_sr, alpha, beta)

    # ── Case (b): L new, R exists ────────────────────────────────────────────
    elseif node_L === nothing
        new_depth = node_R.depth + 1
        if new_depth > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end
        g.nodes[L] = LP2Node(R, new_depth, edge_sr, alpha, beta)

    # ── Case (c): R new, L exists ────────────────────────────────────────────
    elseif node_R === nothing
        new_depth = node_L.depth + 1
        if new_depth > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end
        g.nodes[R] = LP2Node(L, new_depth, edge_sr, alpha, beta)

    # ── Case (e): both exist in DIFFERENT trees — cross-tree merge ───────────
    #
    #  We attach rR as a depth-1 child of rL, using a composite SmallRow that
    #  encodes the full path rR → R → L → rL.
    #
    #  Derivation of composite label:
    #    Let pathR = lp2_path_to_root(R):
    #      walks rR ← ... ← R  (backwards from R; root_sign tells parity)
    #      encodes: (contribution from R's side)
    #    Let pathL = lp2_path_to_root(L):
    #      walks rL ← ... ← L
    #
    #    The stored edge on a node v contributes +edge_row * sign when walking
    #    child→parent (sign starts +1 at first edge, flips each hop).
    #
    #    Path from rR side: pathR accumulates with sign_node starting at +1 at R,
    #      so it represents the sum of edge contributions R→...→rR with alternating
    #      signs starting +.  The "root_sign" at the end is the sign that would have
    #      been applied to rR's (nonexistent) edge; it encodes the parity of depth_R.
    #
    #    Path from L side: pathL accumulates similarly from L toward rL.
    #
    #    The new edge (L, R) contributes fb_row with a sign determined by its
    #    position in the combined path.  In the combined path rR→R→L→rL the
    #    L-side path is traversed in the *reverse* direction (rL←L), so the sign
    #    for the new edge and the L-side path must be reconciled.
    #
    #    Concretely, the composite edge on rR→rL should satisfy:
    #      For any future path walk that reaches rR and takes this one edge to rL,
    #      the contribution is exactly:
    #        sign * composite_row, sign * composite_alpha, sign * composite_beta
    #      where sign is the sign_node at rR during that future walk.
    #
    #    Working out the algebra (treating pathL.root_sign and pathR.root_sign as
    #    the "exit signs" from their respective sides):
    #
    #      The path from R to rR contributes pathR (with sign +1 at R's first edge).
    #      The new edge (R,L) contributes fb_row; in the rR→rL direction the new
    #        edge is traversed with sign = pathR.root_sign (the sign after walking
    #        the full R-side path up to rR, which is the sign that would apply to
    #        the "next" step beyond rR, i.e., the step from rR to the new edge).
    #      The path from L to rL is traversed in reverse (rL→L direction), so each
    #        edge's sign is negated relative to the forward (L→rL) walk.  The entry
    #        sign for the L-side reversal is pathR.root_sign * pathL.root_sign
    #        (accumulated parity from rR side times the parity needed to reverse rL side).
    #
    #    composite_row   = pathR.row
    #                    + pathR.root_sign * fb_row
    #                    + pathR.root_sign * pathL.root_sign * pathL.row   (negated: subtract)
    #    composite_alpha = pathR.alpha
    #                    + pathR.root_sign * alpha
    #                    - pathR.root_sign * pathL.root_sign * pathL.alpha
    #    composite_beta  = pathR.beta
    #                    + pathR.root_sign * beta
    #                    - pathR.root_sign * pathL.root_sign * pathL.beta
    #
    #    (mod ell throughout)
    #
    #  After storing rR→rL with this composite edge, lp2_path_to_root from rR will
    #  traverse exactly one hop to rL, contributing the composite row with sign +1,
    #  which correctly reconstructs the full combined path.
    else
        # rL != rR, both non-nothing (otherwise we'd have hit case b or c after the clear).
        pathL = lp2_path_to_root(g, L, ell)
        pathR = lp2_path_to_root(g, R, ell)

        if pathL === nothing || pathR === nothing
            g.n_depth_pruned += 1
            return nothing
        end

        # Depth of composite edge: rR becomes depth-1 child of rL.
        # Future paths from rR to rL will be depth 1, so any node that previously
        # had rR as an ancestor and had depth d now has depth ≤ d - depth_R + 1.
        # We only need to check that the composite node itself fits at depth 1, which
        # is trivially true (1 ≤ MAX_LP2_DEPTH).  But nodes below rR in the R-tree
        # keep their old depths; we do NOT re-root or rebalance them.  Those nodes
        # may have depth up to MAX_LP2_DEPTH already, and their depth field is now
        # stale (their actual depth to the new root is depth_to_rR + 1).
        # We handle this conservatively: only merge if both sides are shallow enough
        # that the composite node cannot create a path longer than MAX_LP2_DEPTH
        # through an existing R-tree node.
        depth_R_actual = node_R.depth   # depth of R in R's tree (= depth from R to rR)
        depth_L_actual = node_L.depth   # depth of L in L's tree

        # Worst-case future path depth through the merged tree:
        #   A node at depth d_R in R's original tree is now at depth d_R + 1 from rL
        #   (one hop rR→rL plus d_R hops to rR).  From an arbitrary node at depth
        #   d_R in R's tree, a path to the new root (rL) has length d_R + 1.
        #   We require d_R + 1 ≤ MAX_LP2_DEPTH for any node in R's tree.
        #   The deepest R-tree node could be at depth MAX_LP2_DEPTH already, giving
        #   MAX_LP2_DEPTH + 1 — one too many.  So we require the tallest R-tree node
        #   to be at depth ≤ MAX_LP2_DEPTH - 1.  We conservatively bound this by
        #   depth_R_actual (depth of R itself) since we don't track subtree height.
        if depth_R_actual + 1 > MAX_LP2_DEPTH || depth_L_actual + 1 > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end

        sR = pathR.root_sign
        sL = pathL.root_sign

        # Cross-tree merge: valid for both (sR,sL) = (+1,+1) and (-1,-1).
        #
        # Full derivation:
        #
        #   Path equations (from lp2_path_to_root):
        #     atom(L) + sL*atom(rL) = pathL.alpha*G + pathL.beta*T - pathL.row   ... (1)
        #     atom(R) + sR*atom(rR) = pathR.alpha*G + pathR.beta*T - pathR.row   ... (2)
        #   New edge:
        #     atom(L) + atom(R) + fb_row = alpha*G + beta*T                      ... (3)
        #
        #   Goal: atom(rR) + atom(rL) + comp_row = comp_alpha*G + comp_beta*T
        #
        #   Multiply (1) by sL, multiply (2) by sR, subtract (3) scaled as needed:
        #
        #   Case sL = sR = +1:
        #     (1)+(2)-(3): atom(rL) + atom(rR) + fb_row - pathL.row - pathR.row
        #                    = (pathL.alpha + pathR.alpha - alpha)*G + ...
        #     => comp_row   = fb_row - pathL.row - pathR.row
        #        comp_alpha = pathL.alpha + pathR.alpha - alpha
        #
        #   Case sL = sR = -1:
        #     Multiply (1) by -1, (2) by -1, add (3):
        #     atom(rL) + atom(rR) + fb_row - pathL.row - pathR.row
        #                    = (-pathL.alpha - pathR.alpha + alpha)*G + ...
        #     => comp_row   = fb_row - pathL.row - pathR.row   (same!)
        #        comp_alpha = alpha - pathL.alpha - pathR.alpha = sR*(pathL.alpha + pathR.alpha - alpha)
        #
        #   In both cases comp_row = edge_sr - pathL.row - pathR.row (sign-independent!).
        #   comp_alpha = sR * (pathL.alpha + pathR.alpha - alpha)  (correctly handles both signs).
        #
        #   Case sL != sR (mixed parity):
        #     atom(L)*(1+sL) + atom(R)*(1+sR) terms do NOT cancel regardless of combination.
        #     e.g. sR=+1, sL=-1: adding (1)+sL*(2)-(3) leaves atom(L)*(1+sL)=0, atom(R)*(1+sR)=2*atom(R) — stuck.
        #     => Mixed-parity merges cannot be expressed as the standard edge invariant.  Reject.
        if sR * sL != 1
            g.n_depth_pruned += 1
            return nothing
        end

        # Composite edge (rR → rL).
        # comp_row = edge_sr - pathR.row - pathL.row  (sign-independent; see derivation above).
        # comp_alpha/beta scale by sR to handle both parity cases uniformly.
        comp_row = smallrow_merge(SmallRow(), edge_sr,    1)
        comp_row = smallrow_merge(comp_row,   pathR.row, -1)
        comp_row = smallrow_merge(comp_row,   pathL.row, -1)

        comp_alpha = mod(sR * (pathR.alpha + pathL.alpha - alpha), ell)
        comp_beta  = mod(sR * (pathR.beta  + pathL.beta  - beta),  ell)

        if comp_row.len > MAX_LP2_ROW_WEIGHT
            g.n_weight_pruned += 1
            return nothing
        end

        # Attach rR as depth-1 child of rL with the composite edge.
        g.nodes[rR] = LP2Node(rL, 1, comp_row, comp_alpha, comp_beta)
        g.n_merges += 1
    end

    return nothing
end


# ---------------------------------------------------------------------------
#  lp2_prune_component!
#
#  Delete all nodes in the spanning tree rooted at `root`.
#  Called after an even-cycle emission to reclaim the whole component.
#
#  Implementation: build a reverse-adjacency (parent → children) map in one
#  pass over g.nodes, then BFS/DFS from `root`.  This is O(N) in the number
#  of nodes in the graph, not O(N·depth) like a per-node root-walk would be.
#
#  This correctly handles the full component including nodes in subtrees that
#  were merged in via cross-tree edges (fixing the orphan-node leak in the
#  old lp2_prune_path! approach, which only deleted nodes on the two paths
#  to root but left the rest of the tree dangling).
# ---------------------------------------------------------------------------
function lp2_prune_component!(g::LP2Graph, root::NTuple{2,Int})
    root ∈ keys(g.nodes) || return

    # Build children map (parent → [child, ...]) for the whole graph.
    # We only need to include nodes that are actually in the same component,
    # but since we don't track that we scan all nodes.  One O(N) pass.
    children = Dict{NTuple{2,Int}, Vector{NTuple{2,Int}}}()
    for (pt, node) in g.nodes
        node.parent === nothing && continue
        par = node.parent
        if !haskey(children, par)
            children[par] = NTuple{2,Int}[]
        end
        push!(children[par], pt)
    end

    # BFS from root, deleting every reachable node.
    queue = NTuple{2,Int}[root]
    while !isempty(queue)
        cur = pop!(queue)
        haskey(g.nodes, cur) || continue
        delete!(g.nodes, cur)
        kids = get(children, cur, nothing)
        kids === nothing && continue
        for child in kids
            push!(queue, child)
        end
    end
end

# ---------------------------------------------------------------------------
#  lp2_prune_path! — compatibility alias
#
#  The old implementation deleted only the two paths to root (leaving orphan
#  subtrees).  We now delegate to lp2_prune_component! which correctly
#  removes the entire tree.  The `start` argument is walked to its root first.
# ---------------------------------------------------------------------------
function lp2_prune_path!(g::LP2Graph, start::NTuple{2,Int})
    root = lp2_tree_root(g, start)
    root === nothing && return
    lp2_prune_component!(g, root)
end

# ---------------------------------------------------------------------------
#  lp2_graph_node_count — helper used by the walker to check cap
# ---------------------------------------------------------------------------
function lp2_graph_node_count(g::LP2Graph)::Int
    return length(g.nodes)
end
