# =============================================================================
#  lp2_conj.jl  --  Extension-field large-prime graph
#
#  Included by trial3_fixed.jl after lp2.jl.  Requires ell (global), fp/fpinv,
#  Div2/jac_* from trial1, and lp2_subtract_rows from lp2.jl.
#
#  PURPOSE
#  -------
#  When the phi residual R,S form a conjugate pair over Fp² (rs_split==false),
#  the walk step produces:
#
#      atom(P0) + QLP(RS) + fb_row  =  neg_al·G + neg_be·T        ... (*)
#
#  where QLP(RS) = [R]+[S]-2[∞] is a genuine degree-2 Jacobian element,
#  irreducible over Fp, whose Mumford key is (c0,c1,v0,v1)::NTuple{4,Int}.
#
#  Previously this was handled as:
#    P0 ∈ FB  →  1-LP stored in shared_lp1_conj   (already works, unchanged)
#    P0 ∉ FB  →  DISCARDED (two unknowns, no graph)
#
#  This file adds a proper 2-LP graph whose nodes are typed
#
#      LPKey = Union{NTuple{2,Int},   # ordinary affine Fp point
#                    NTuple{4,Int}}   # Mumford QLP token (c0,c1,v0,v1)
#
#  so that the P0-off-FB / RS-conjugate case can contribute relations via
#  cycle detection, exactly like ordinary 2-LP pairs.
#
#  INVARIANT (same as lp2.jl, generalised)
#  ----------------------------------------
#  Each edge (L, R, fb_row, alpha, beta) asserts:
#
#      atom(L) + atom(R) + fb_row  =  -alpha·G - beta·T
#
#  where atom(X) is [X]-[∞] for an affine point or [R]+[S]-2[∞] for a QLP.
#  Arithmetic on atom(QLP) is exact: when two edges sharing the same QLP key
#  are subtracted, the QLP atom cancels and the result is a pure FB relation
#  (or a smaller LP relation if only one of the other endpoints is on FB).
#
#  RELATION TO SHARED_LP1_CONJ
#  ----------------------------
#  shared_lp1_conj handles the case where only one unknown is a QLP (P0 on FB).
#  LP2ConjGraph handles the case where BOTH unknowns appear — either as two
#  affine LPs, one affine LP + one QLP, or (theoretically) two QLPs.
#  In practice the dominant new case is (affine P0) × (QLP RS).
#  The two tables are entirely separate; no key type collisions are possible.
#
#  ROW-WEIGHT AND DEPTH CAPS
#  --------------------------
#  Same as lp2.jl: MAX_LP2_DEPTH and MAX_LP2_ROW_WEIGHT.  The QLP graph uses
#  the same constants; they're imported from the main file.
# =============================================================================

# ---------------------------------------------------------------------------
#  Node-key type alias
# ---------------------------------------------------------------------------
const LPKey = Union{NTuple{2,Int}, NTuple{4,Int}}

# Node cap for LP2ConjGraph — same rationale as MAX_LP2_NODES in lp2.jl.
const MAX_LP2C_NODES = 50_000

# ---------------------------------------------------------------------------
#  LP2ConjNode — one vertex in the mixed LP2 spanning tree
# ---------------------------------------------------------------------------
mutable struct LP2ConjNode
    parent    ::Union{LPKey, Nothing}   # nothing → this node is a root
    depth     ::Int
    edge_row  ::Dict{Int,Int}           # fb contribution on edge to parent
    edge_alpha::Int
    edge_beta ::Int
end

# ---------------------------------------------------------------------------
#  LP2ConjGraph — shared mixed LP2 graph (one per index_calculus_walk run)
# ---------------------------------------------------------------------------
mutable struct LP2ConjGraph
    nodes             ::Dict{LPKey, LP2ConjNode}
    n_edges_inserted  ::Int
    n_cycles_found    ::Int
    n_emitted         ::Int
    n_depth_pruned    ::Int
    n_weight_pruned   ::Int
    n_parity_pruned   ::Int
    n_odd_stored      ::Int
    n_clears          ::Int
end

function LP2ConjGraph()
    LP2ConjGraph(Dict{LPKey, LP2ConjNode}(), 0, 0, 0, 0, 0, 0, 0, 0)
end

# ---------------------------------------------------------------------------
#  Internal helpers (mirrors lp2.jl exactly, generalised key type)
# ---------------------------------------------------------------------------

function lp2c_tree_root(g::LP2ConjGraph, pt::LPKey)::Union{LPKey,Nothing}
    cur = pt
    steps = 0
    while true
        node = get(g.nodes, cur, nothing)
        node === nothing && return nothing
        node.parent === nothing && return cur
        steps += 1
        if steps > MAX_LP2_DEPTH + 1
            @printf("[LP2C-CYCLE] Root walk exceeded depth bound from %s (steps=%d)\n",
                    string(cur), steps)
            flush(stdout)
            error("lp2c_tree_root: depth bound exceeded — possible parent-pointer cycle")
        end
        cur = node.parent::LPKey
    end
end

function lp2c_path_to_root(g::LP2ConjGraph, start::LPKey, ell::Int)
    row   = Dict{Int,Int}()
    alpha = 0
    beta  = 0
    sign_node = 1
    cur   = start
    depth = 0
    while true
        node = get(g.nodes, cur, nothing)
        (node === nothing || node.parent === nothing) && break
        depth += 1
        if depth > MAX_LP2_DEPTH
            return nothing
        end
        for (j, v) in node.edge_row
            nv = get(row, j, 0) + sign_node * v
            nv == 0 ? delete!(row, j) : (row[j] = nv)
        end
        alpha     = mod(alpha + sign_node * node.edge_alpha, ell)
        beta      = mod(beta  + sign_node * node.edge_beta,  ell)
        sign_node = -sign_node
        cur       = node.parent::LPKey
    end
    return (row=row, alpha=alpha, beta=beta, root_sign=sign_node, depth=depth)
end

# Delete all nodes on the path from `start` up to and including the root.
# Called after an even-cycle emission to reclaim memory from completed components.
# Allocation-free: bounded by MAX_LP2_DEPTH+1 steps.
function lp2c_prune_path!(g::LP2ConjGraph, start::LPKey)
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
        cur = next::LPKey
    end
end

# ---------------------------------------------------------------------------
#  lp2c_insert_edge!
#
#  Identical contract to lp2_insert_edge! but accepts LPKey node identifiers.
#  Returns one of:
#    nothing                                  — tree insertion, no cycle
#    (type=:even_cycle, row, alpha, beta, …)  — emittable pure-FB relation
#    (type=:odd_cycle,  root, row, alpha, beta) — 2·atom(root) + row relation
# ---------------------------------------------------------------------------
function lp2c_insert_edge!(g::LP2ConjGraph,
                            L::LPKey, R::LPKey,
                            fb_row::Dict{Int,Int},
                            alpha::Int, beta::Int,
                            ell::Int)

    g.n_edges_inserted += 1

    # Degenerate self-loop.
    L == R && return nothing

    rL = lp2c_tree_root(g, L)
    rR = lp2c_tree_root(g, R)

    if rL !== nothing && rR !== nothing && rL == rR
        # ── Cycle detected ──────────────────────────────────────────────
        g.n_cycles_found += 1

        pathL = lp2c_path_to_root(g, L, ell)
        pathR = lp2c_path_to_root(g, R, ell)

        if pathL === nothing || pathR === nothing
            g.n_depth_pruned += 1
            return nothing
        end

        if pathL.root_sign == pathR.root_sign
            # Odd cycle: 2·atom(root) + odd_row = odd_alpha·G + odd_beta·T
            g.n_parity_pruned += 1
            g.n_odd_stored    += 1
            s = pathL.root_sign

            odd_row = Dict{Int,Int}()
            for (j, v) in pathL.row
                nv = get(odd_row, j, 0) - s * v
                nv == 0 ? delete!(odd_row, j) : (odd_row[j] = nv)
            end
            for (j, v) in pathR.row
                nv = get(odd_row, j, 0) - s * v
                nv == 0 ? delete!(odd_row, j) : (odd_row[j] = nv)
            end
            for (j, v) in fb_row
                nv = get(odd_row, j, 0) + s * v
                nv == 0 ? delete!(odd_row, j) : (odd_row[j] = nv)
            end
            odd_alpha = mod(s * (pathL.alpha + pathR.alpha - alpha), ell)
            odd_beta  = mod(s * (pathL.beta  + pathR.beta  - beta),  ell)

            if length(odd_row) > MAX_LP2_ROW_WEIGHT
                g.n_weight_pruned += 1
                return nothing
            end

            return (type=:odd_cycle, root=rL,
                    row=odd_row, alpha=odd_alpha, beta=odd_beta)
        end

        # Even cycle: LPs cancel, pure FB relation.
        combined = copy(fb_row)
        for (j, v) in pathL.row
            nv = get(combined, j, 0) - v
            nv == 0 ? delete!(combined, j) : (combined[j] = nv)
        end
        for (j, v) in pathR.row
            nv = get(combined, j, 0) - v
            nv == 0 ? delete!(combined, j) : (combined[j] = nv)
        end

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

        # Prune both paths to reclaim memory from the completed component.
        lp2c_prune_path!(g, L)
        lp2c_prune_path!(g, R)

        return (type=:even_cycle,
                row=combined,
                alpha=combined_alpha,
                beta=combined_beta,
                root_signs=(pathL.root_sign, pathR.root_sign),
                depths=(pathL.depth, pathR.depth))

    else
        # ── Tree insertion / merge ───────────────────────────────────────
        # Hard node cap: clear the graph if it has grown without producing cycles.
        if length(g.nodes) >= MAX_LP2C_NODES
            empty!(g.nodes)
            g.n_clears += 1
        end

        node_L = get(g.nodes, L, nothing)
        node_R = get(g.nodes, R, nothing)

        if node_L === nothing && node_R === nothing
            1 > MAX_LP2_DEPTH && (g.n_depth_pruned += 1; return nothing)
            g.nodes[R] = LP2ConjNode(nothing, 0, Dict{Int,Int}(), 0, 0)
            g.nodes[L] = LP2ConjNode(R, 1, copy(fb_row), alpha, beta)

        elseif node_L === nothing
            new_depth = node_R.depth + 1
            new_depth > MAX_LP2_DEPTH && (g.n_depth_pruned += 1; return nothing)
            g.nodes[L] = LP2ConjNode(R, new_depth, copy(fb_row), alpha, beta)

        elseif node_R === nothing
            new_depth = node_L.depth + 1
            new_depth > MAX_LP2_DEPTH && (g.n_depth_pruned += 1; return nothing)
            g.nodes[R] = LP2ConjNode(L, new_depth, copy(fb_row), alpha, beta)

        else
            # Both in different existing trees — cross-tree merge is unsound
            # with the alternating-sign convention (same reason as lp2.jl).
            # Discard silently.
        end

        return nothing
    end
end
