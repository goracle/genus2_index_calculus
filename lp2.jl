# =============================================================================
#  lp2.jl  --  2-Large-Prime graph structures and helpers
#
#  Included by trial3_fixed.jl.  Requires: ell (global), fp/fpinv (from trial1),
#  Div2/jac_* types, and the sparse_add!/lp2_subtract_rows helpers.
# =============================================================================

# ---------------------------------------------------------------------------
#  2-LP graph helpers
#
#  We treat a 2-LP relation as an edge between the two large-prime points.
#  When two edges meet at a shared endpoint, subtracting them eliminates the
#  shared LP and yields a new edge between the other endpoints.  Repeating this
#  is a sparse graph walk; when the endpoints coincide, the LPs cancel and we
#  emit a pure factor-base relation.
# ---------------------------------------------------------------------------

function lp2_subtract_rows(dst::Dict{Int,Int}, src::Dict{Int,Int})
    for (j, v) in src
        nv = get(dst, j, 0) - v
        nv == 0 ? delete!(dst, j) : (dst[j] = nv)
    end
    return dst
end

# ── Stack-allocated sparse row for LP2 edge storage ──────────────────────────
#
# Each 2-LP walk step has exactly one FB point among {P0,R,S}, so each edge
# stored in LP2Node has at most 1 nonzero entry.  Encoding it as two plain Ints
# (edge_col=0 means empty) eliminates the per-node Dict{Int,Int} entirely.
#
# SmallRow: fixed-capacity inline sparse row for path accumulation.
# MAX_LP2_DEPTH=6 edges × 1 entry each = at most 6 nonzeros after cancellation.
# Capacity 8 (next power of 2) with a length field; all ops allocation-free.

const SMALL_ROW_CAP = 8

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
                # Remove: swap with last entry
                new_cols = Base.setindex(Base.setindex(cols, cols[len], i), 0, len)
                new_vals = Base.setindex(Base.setindex(vals, vals[len], i), 0, len)
                return SmallRow(new_cols, new_vals, len - 1)
            else
                return SmallRow(Base.setindex(cols, col, i), Base.setindex(vals, nv, i), len)
            end
        end
    end
    # New entry — silently drop if at cap (shouldn't happen at depth≤6 with 1 entry/edge)
    len >= SMALL_ROW_CAP && return r
    return SmallRow(Base.setindex(cols, col, len+1), Base.setindex(vals, sv, len+1), len + 1)
end

# Merge a single (col, val) edge entry into a SmallRow with given sign.
@inline function smallrow_add_edge(r::SmallRow, edge_col::Int, edge_val::Int, sign::Int)::SmallRow
    edge_col == 0 && return r   # empty edge (root node)
    smallrow_add(r, edge_col, sign * edge_val)
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

# ---------------------------------------------------------------------------
#  LP2Graph — shared 2-large-prime graph for cycle-based relation emission
#
#  Each 2-LP walk step yields a pair of off-factor-base points (L, R) and
#  a factor-base row expressing:
#
#      atom(L) + atom(R) + fb_row  =  -alpha*G - beta*T      ... (*)
#
#  We model this as a weighted graph where nodes are LP points and each
#  such step inserts an edge (L, R) labelled with (fb_row, alpha, beta).
#
#  A cycle in this graph means we can subtract two edge labels to eliminate
#  the shared LP node and produce a pure factor-base relation.  We detect
#  cycles online via union-find: when we try to insert edge (L,R) and L,R
#  are already in the same component, we have a cycle.  We then walk the
#  stored spanning-tree path from L to their common root and from R to that
#  root, cancelling LP nodes along the way, to recover the FB relation.
#
#  Spanning tree storage:
#    Each LP node v stores parent[v], edge_to_parent[v] = (fb_row, alpha, beta).
#    The edge direction is always child→parent, so "subtracting" means we negate
#    when traversing parent→child.
#
#  Row-weight bound:
#    Each path-combination can double the row weight at each step.  We cap the
#    total combined row weight at MAX_LP2_ROW_WEIGHT; if exceeded we discard
#    rather than emit a bloated row.
#
#  Thread safety:
#    The struct is shared across all walker threads behind a single ReentrantLock.
#    Lock is held only during graph mutation and cycle checks — O(depth) work,
#    bounded by MAX_LP2_DEPTH.
# ---------------------------------------------------------------------------

const MAX_LP2_DEPTH       = 6    # max spanning-tree depth; prevents row blowup
const MAX_LP2_ROW_WEIGHT  = 24   # max nonzeros in an emitted 2-LP relation
# Hard cap on total nodes in the LP2Graph.  When reached, the graph is cleared
# entirely.  This is a blunt instrument but correct: a cleared graph loses
# pending edges but not correctness.  Without this, a walk where the LP bound
# is large relative to p accumulates millions of nodes and OOMs.
# At ~500 bytes per node (Dict overhead + edge_row), 50_000 nodes ≈ 25 MB per graph.
# Two graphs (affine + conj) × this cap = ~50 MB total for LP2 state.
const MAX_LP2_NODES = 50_000

mutable struct LP2Node
    parent   ::Union{NTuple{2,Int}, Nothing}   # nothing = this node is a root
    depth    ::Int
    # Edge to parent: at most 1 FB entry per 2-LP step (one of P0/R/S is in FB).
    # Stored as plain Ints; edge_col==0 means no FB contribution (root node).
    edge_col  ::Int
    edge_val  ::Int
    edge_alpha::Int
    edge_beta ::Int
end

mutable struct LP2Graph
    nodes    ::Dict{NTuple{2,Int}, LP2Node}
    n_edges_inserted ::Int
    n_cycles_found   ::Int
    n_emitted        ::Int
    n_depth_pruned   ::Int
    n_weight_pruned  ::Int
    n_parity_pruned  ::Int
    n_odd_stored     ::Int   # odd cycles passed to caller for doubled-atom storage
    n_clears         ::Int   # number of times graph was fully cleared due to node cap
end

function LP2Graph()
    LP2Graph(
        Dict{NTuple{2,Int}, LP2Node}(),
        0, 0, 0, 0, 0, 0, 0, 0
    )
end

# Walk the spanning tree from `pt` to find its root (node with parent===nothing).
# Returns the root key, or nothing if pt is not in the tree.
#
# Allocation-free: we bound the walk by MAX_LP2_DEPTH+1 steps using the stored
# depth field.  No Set is needed because the tree invariant (maintained by
# lp2_insert_edge!) guarantees no parent-pointer cycles; we error if the depth
# bound is exceeded so bugs surface immediately.
function lp2_tree_root(g::LP2Graph, pt::NTuple{2,Int})
    cur = pt
    steps = 0
    while true
        node = get(g.nodes, cur, nothing)
        node === nothing && return nothing   # pt not in tree at all
        node.parent === nothing && return cur
        steps += 1
        if steps > MAX_LP2_DEPTH + 1
            @printf("[LP2-CYCLE] Root walk exceeded depth bound from %s (steps=%d)\n",
                    string(pt), steps)
            flush(stdout)
            error("lp2_tree_root: depth bound exceeded — possible parent-pointer cycle")
        end
        cur = node.parent
    end
end

# Walk the spanning tree from `start` up to the root, accumulating the
# combined fb_row (with alternating signs) and alpha/beta.
# Returns (row::SmallRow, alpha, beta, root_sign, depth) or nothing if depth exceeded.
# Allocation-free: SmallRow is a stack-allocated immutable tuple struct.
function lp2_path_to_root(g::LP2Graph, start::NTuple{2,Int}, ell::Int)
    row   = SmallRow()
    alpha = 0
    beta  = 0
    sign_node = 1
    cur   = start
    depth = 0
    while true
        node = get(g.nodes, cur, nothing)
        if node === nothing || node.parent === nothing
            break
        end

        depth += 1
        if depth > MAX_LP2_DEPTH
            return nothing
        end

        row   = smallrow_add_edge(row, node.edge_col, node.edge_val, sign_node)
        alpha = mod(alpha + sign_node * node.edge_alpha, ell)
        beta  = mod(beta  + sign_node * node.edge_beta,  ell)

        sign_node = -sign_node
        cur = node.parent
    end
    return (row=row, alpha=alpha, beta=beta, root_sign=sign_node, depth=depth)
end


# Try to insert edge (L, R) with label (fb_row, alpha, beta).
# fb_row has at most 1 entry (one FB point per 2-LP step); we extract it for
# inline storage in LP2Node (edge_col/edge_val), avoiding per-node Dict alloc.
# Returns the emitted relation namedtuple or nothing.
function lp2_insert_edge!(g::LP2Graph,
                          L::NTuple{2,Int}, R::NTuple{2,Int},
                          fb_row::Dict{Int,Int},
                          alpha::Int, beta::Int,
                          ell::Int)

    g.n_edges_inserted += 1
    L == R && return nothing

    # Extract the single FB entry (if any) for inline node storage.
    edge_col = 0; edge_val = 0
    for (j, v) in fb_row; edge_col = j; edge_val = v; break; end

    rL = lp2_tree_root(g, L)
    rR = lp2_tree_root(g, R)

    if rL !== nothing && rR !== nothing && rL == rR
        g.n_cycles_found += 1

        pathL = lp2_path_to_root(g, L, ell)
        pathR = lp2_path_to_root(g, R, ell)

        if pathL === nothing || pathR === nothing
            g.n_depth_pruned += 1
            return nothing
        end

        if pathL.root_sign == pathR.root_sign
            # Odd cycle — spill SmallRows to Dict (rare path)
            g.n_parity_pruned += 1
            g.n_odd_stored    += 1
            s = pathL.root_sign

            odd_row = Dict{Int,Int}()
            smallrow_subtract_into_dict!(odd_row, pathL.row)
            smallrow_subtract_into_dict!(odd_row, pathR.row)
            for (j, v) in fb_row
                nv = get(odd_row, j, 0) + v
                nv == 0 ? delete!(odd_row, j) : (odd_row[j] = nv)
            end
            if s == -1; for k in keys(odd_row); odd_row[k] = -odd_row[k]; end; end

            odd_alpha = mod(s * (pathL.alpha + pathR.alpha - alpha), ell)
            odd_beta  = mod(s * (pathL.beta  + pathR.beta  - beta),  ell)

            if length(odd_row) > MAX_LP2_ROW_WEIGHT
                g.n_weight_pruned += 1
                return nothing
            end
            return (type=:odd_cycle, root=rL,
                    row=odd_row, alpha=odd_alpha, beta=odd_beta)
        end

        # Even cycle — spill SmallRows to Dict (rare path)
        combined = copy(fb_row)
        smallrow_subtract_into_dict!(combined, pathL.row)
        smallrow_subtract_into_dict!(combined, pathR.row)

        if length(combined) > MAX_LP2_ROW_WEIGHT
            g.n_weight_pruned += 1
            return nothing
        end

        combined_alpha = mod(pathL.alpha + pathR.alpha - alpha, ell)
        combined_beta  = mod(pathL.beta  + pathR.beta  - beta,  ell)

        if isempty(combined) || (combined_alpha == 0 && combined_beta == 0)
            return nothing
        end

        g.n_emitted += 1
        lp2_prune_path!(g, L)
        lp2_prune_path!(g, R)

        return (type=:even_cycle,
                row=combined,
                alpha=combined_alpha,
                beta=combined_beta,
                root_signs=(pathL.root_sign, pathR.root_sign),
                depths=(pathL.depth, pathR.depth))

    else
        if length(g.nodes) >= MAX_LP2_NODES
            empty!(g.nodes)
            g.n_clears += 1
        end

        node_L = get(g.nodes, L, nothing)
        node_R = get(g.nodes, R, nothing)

        if node_L === nothing && node_R === nothing
            1 > MAX_LP2_DEPTH && (g.n_depth_pruned += 1; return nothing)
            g.nodes[R] = LP2Node(nothing, 0, 0, 0, 0, 0)
            g.nodes[L] = LP2Node(R, 1, edge_col, edge_val, alpha, beta)

        elseif node_L === nothing
            new_depth = node_R.depth + 1
            new_depth > MAX_LP2_DEPTH && (g.n_depth_pruned += 1; return nothing)
            g.nodes[L] = LP2Node(R, new_depth, edge_col, edge_val, alpha, beta)

        elseif node_R === nothing
            new_depth = node_L.depth + 1
            new_depth > MAX_LP2_DEPTH && (g.n_depth_pruned += 1; return nothing)
            g.nodes[R] = LP2Node(L, new_depth, edge_col, edge_val, alpha, beta)

        # else: both in different trees — cross-tree merge unsound, discard.
        end

        return nothing
    end
end

# Delete all nodes on the path from `start` up to and including the root.
# Called after an even-cycle emission to prevent unbounded graph growth:
# once a component has produced a relation, all stored edges in that component
# are stale and the memory can be reclaimed.
# Allocation-free: bounded by MAX_LP2_DEPTH+1 steps.
function lp2_prune_path!(g::LP2Graph, start::NTuple{2,Int})
    cur = start
    steps = 0
    while true
        node = get(g.nodes, cur, nothing)
        node === nothing && break
        next = node.parent   # capture before delete
        delete!(g.nodes, cur)
        node.parent === nothing && break   # was the root; done
        steps += 1
        steps > MAX_LP2_DEPTH + 1 && break
        cur = next
    end
end
