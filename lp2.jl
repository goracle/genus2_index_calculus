# =============================================================================
#  lp2.jl  --  2-Large-Prime graph structures and helpers
#
#  Included by trial3_fixed.jl.  Requires: ell (global), fp/fpinv (from trial1),
#  Div2/jac_* types, and the sparse_add!/lp2_subtract_rows helpers below.
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
struct LP2Edge
    left::NTuple{2,Int}
    right::NTuple{2,Int}
    row::Dict{Int,Int}
    alpha::Int
    beta::Int
    function LP2Edge(a::NTuple{2,Int}, b::NTuple{2,Int},
                     row::Dict{Int,Int}, alpha::Int, beta::Int)
        a <= b ? new(a, b, row, alpha, beta) : new(b, a, row, alpha, beta)
    end
end

@inline lp2_other(e::LP2Edge, pt::NTuple{2,Int})::Union{NTuple{2,Int},Nothing} =
    e.left == pt ? e.right : (e.right == pt ? e.left : nothing)

function lp2_subtract_rows(dst::Dict{Int,Int}, src::Dict{Int,Int})
    for (j, v) in src
        nv = get(dst, j, 0) - v
        nv == 0 ? delete!(dst, j) : (dst[j] = nv)
    end
    return dst
end

function lp2_attach!(edges::Vector{LP2Edge},
                     live::Vector{Bool},
                     incidence::Dict{NTuple{2,Int}, Vector{Int}},
                     left::NTuple{2,Int},
                     right::NTuple{2,Int},
                     row::Dict{Int,Int},
                     alpha::Int,
                     beta::Int,
                     rel_rows::Vector{Dict{Int,Int}},
                     alpha_vec::Vector{Int},
                     beta_vec::Vector{Int},
                     rel_counter::Threads.Atomic{Int})::Int
    cur_left  = left
    cur_right = right
    cur_row   = copy(row)
    cur_alpha = alpha
    cur_beta  = beta

    # One bounded fold only: if the new edge touches an existing live edge,
    # cancel that shared LP once. This closes local triangles without letting
    # the graph walk recurse or chase long cyclic components.
    hit_eid = 0
    hit_pt  = cur_left

    if haskey(incidence, cur_left)
        vec = incidence[cur_left]
        while !isempty(vec) && !live[vec[end]]
            pop!(vec)
        end
        if !isempty(vec)
            hit_eid = vec[end]
            hit_pt  = cur_left
        end
    end

    if hit_eid == 0 && haskey(incidence, cur_right)
        vec = incidence[cur_right]
        while !isempty(vec) && !live[vec[end]]
            pop!(vec)
        end
        if !isempty(vec)
            hit_eid = vec[end]
            hit_pt  = cur_right
        end
    end

    if hit_eid == 0
        e = LP2Edge(cur_left, cur_right, copy(cur_row), cur_alpha, cur_beta)
        push!(edges, e)
        push!(live, true)
        eid = length(edges)
        push!(get!(incidence, e.left, Int[]), eid)
        push!(get!(incidence, e.right, Int[]), eid)
        return 0
    end

    old = edges[hit_eid]
    old_other = lp2_other(old, hit_pt)
    old_other === nothing && (live[hit_eid] = false; return 0)

    live[hit_eid] = false
    cur_row   = lp2_subtract_rows(copy(cur_row), old.row)
    cur_alpha = mod(cur_alpha - old.alpha, ell)
    cur_beta  = mod(cur_beta  - old.beta, ell)

    cur_other = hit_pt == cur_left ? cur_right : cur_left

    if old_other == cur_other
        if !isempty(cur_row) && !(cur_alpha == 0 && cur_beta == 0)
            push!(alpha_vec, cur_alpha)
            push!(beta_vec,  cur_beta)
            push!(rel_rows,  cur_row)
            Threads.atomic_add!(rel_counter, 1)
        end
        return 1
    end

    # Store the folded edge and stop. The next closure attempt happens only
    # when a fresh relation later hits one of its endpoints.
    e = LP2Edge(old_other, cur_other, cur_row, cur_alpha, cur_beta)
    push!(edges, e)
    push!(live, true)
    eid = length(edges)
    push!(get!(incidence, e.left, Int[]), eid)
    push!(get!(incidence, e.right, Int[]), eid)
    return 0
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

mutable struct LP2Node
    parent   ::Union{NTuple{2,Int}, Nothing}   # nothing = this node is a root
    depth    ::Int
    # edge to parent: fb_row contribution when traversing child→parent
    edge_row  ::Dict{Int,Int}
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
end

function LP2Graph()
    LP2Graph(
        Dict{NTuple{2,Int}, LP2Node}(),
        0, 0, 0, 0, 0, 0
    )
end

# Walk the spanning tree from `pt` to find its root (node with parent===nothing).
# Returns the root key, or nothing if pt is not in the tree.
function lp2_tree_root(g::LP2Graph, pt::NTuple{2,Int})
    cur = pt
    visited = Set{NTuple{2,Int}}()
    while true
        node = get(g.nodes, cur, nothing)
        node === nothing && return nothing   # pt not in tree at all
        node.parent === nothing && return cur
        next = node.parent
        if next in visited
            # Parent-pointer cycle detected — dump the cycle and abort.
            @printf("[LP2-CYCLE] Detected parent-pointer cycle starting from %s!\n", string(pt))
            @printf("[LP2-CYCLE] Cycle node: %s -> parent %s (already visited)\n", string(cur), string(next))
            @printf("[LP2-CYCLE] Full walk from start:\n")
            walk_cur = pt
            walk_depth = 0
            while walk_depth < 2 * length(g.nodes) + 5
                walk_node = get(g.nodes, walk_cur, nothing)
                if walk_node === nothing
                    @printf("[LP2-CYCLE]   [%d] %s -> (not in graph)\n", walk_depth, string(walk_cur))
                    break
                end
                @printf("[LP2-CYCLE]   [%d] %s -> parent=%s  depth_field=%d\n",
                        walk_depth, string(walk_cur),
                        walk_node.parent === nothing ? "ROOT" : string(walk_node.parent),
                        walk_node.depth)
                walk_node.parent === nothing && break
                walk_cur = walk_node.parent
                walk_depth += 1
                if walk_depth > 2 * length(g.nodes) + 4
                    @printf("[LP2-CYCLE]   ... (truncated)\n")
                end
            end
            @printf("[LP2-CYCLE] Graph has %d nodes total\n", length(g.nodes))
            flush(stdout)
            error("lp2_tree_root: parent-pointer cycle detected — see LP2-CYCLE diagnostics above")
        end
        push!(visited, cur)
        cur = next
    end
end

# Walk the spanning tree from `start` up to the root, accumulating the
# combined fb_row (with signs) and alpha/beta into (row, a, b).
# Returns (row, alpha, beta, depth_reached) or nothing if depth exceeded.
function lp2_path_to_root(g::LP2Graph, start::NTuple{2,Int}, ell::Int)
    row   = Dict{Int,Int}()
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

        for (j, v) in node.edge_row
            nv = get(row, j, 0) + sign_node * v   # +sign_node (consistent with alpha/beta)
            nv == 0 ? delete!(row, j) : (row[j] = nv)
        end
        alpha = mod(alpha + sign_node * node.edge_alpha, ell)
        beta  = mod(beta  + sign_node * node.edge_beta,  ell)

        sign_node = -sign_node
        cur = node.parent
    end
    return (row=row, alpha=alpha, beta=beta, root_sign=sign_node, depth=depth)
end


# Try to insert edge (L, R) with label (fb_row, alpha, beta).
# If L and R are already connected → cycle → emit a relation.
# Otherwise insert L or R as a new child in the spanning tree.
# Returns the emitted (row, alpha, beta) or nothing.
function lp2_insert_edge!(g::LP2Graph,
                          L::NTuple{2,Int}, R::NTuple{2,Int},
                          fb_row::Dict{Int,Int},
                          alpha::Int, beta::Int,
                          ell::Int)

    g.n_edges_inserted += 1

    rL = lp2_tree_root(g, L)
    rR = lp2_tree_root(g, R)

    # Cycle: both nodes already in the same spanning tree
    if rL !== nothing && rR !== nothing && rL == rR
        g.n_cycles_found += 1

        pathL = lp2_path_to_root(g, L, ell)
        pathR = lp2_path_to_root(g, R, ell)

        if pathL === nothing || pathR === nothing
            g.n_depth_pruned += 1
            return nothing
        end

        # Reject odd cycles (roots fail to cancel)
        if pathL.root_sign == pathR.root_sign
            g.n_parity_pruned += 1
            if g.n_parity_pruned <= 8
                @printf("[LP2-PARITY tid=%d] odd cycle rejected at cycle-detect: L=%s R=%s root_signs=(%d,%d) depths=(%d,%d)\n",
                        Threads.threadid(), string(L), string(R),
                        pathL.root_sign, pathR.root_sign, pathL.depth, pathR.depth)
            end
            return nothing
        end

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
        return (row=combined,
                alpha=combined_alpha,
                beta=combined_beta,
                root_signs=(pathL.root_sign, pathR.root_sign),
                depths=(pathL.depth, pathR.depth))

    else
        # Tree-merge: attach whichever endpoint is not yet in a tree.
        # IMPORTANT: when both L and R are already in *different* trees, we must
        # attach the ROOT of one tree to the ROOT of the other.  Attaching a
        # non-root node would overwrite its existing parent pointer and create a
        # cycle in the parent-pointer graph, causing lp2_tree_root to loop forever.
        node_L = get(g.nodes, L, nothing)
        node_R = get(g.nodes, R, nothing)

        if node_L === nothing && node_R === nothing
            # Neither in tree yet: make R a root, attach L as child.
            if 1 > MAX_LP2_DEPTH
                g.n_depth_pruned += 1
                return nothing
            end
            g.nodes[R] = LP2Node(nothing, 0, Dict{Int,Int}(), 0, 0)
            g.nodes[L] = LP2Node(R, 1, copy(fb_row), alpha, beta)

        elseif node_L === nothing
            # L is new; attach it directly as child of R.
            new_depth = node_R.depth + 1
            if new_depth > MAX_LP2_DEPTH
                g.n_depth_pruned += 1
                return nothing
            end
            g.nodes[L] = LP2Node(R, new_depth, copy(fb_row), alpha, beta)

        elseif node_R === nothing
            # R is new; attach it directly as child of L.
            new_depth = node_L.depth + 1
            if new_depth > MAX_LP2_DEPTH
                g.n_depth_pruned += 1
                return nothing
            end
            g.nodes[R] = LP2Node(L, new_depth, copy(fb_row), alpha, beta)

        else
            # Both L and R are in different trees (rL != rR guaranteed here).
            # We must attach rL to rR (or vice-versa) — never a non-root node.
            # Compute paths L->rL and R->rR to derive the edge label for rL->rR.
            pathL = lp2_path_to_root(g, L, ell)
            pathR = lp2_path_to_root(g, R, ell)

            if pathL === nothing || pathR === nothing
                g.n_depth_pruned += 1
                return nothing
            end

            # Same parity roots are incompatible in this tree model:
            # the stored alternating-sign path convention would make the
            # root-to-root edge land in the wrong sign class.
            if pathL.root_sign == pathR.root_sign
                g.n_parity_pruned += 1
                if g.n_parity_pruned <= 8
                    @printf("[LP2-PARITY tid=%d] tree-merge rejected: L=%s R=%s rL=%s rR=%s root_signs=(%d,%d) depths=(%d,%d)\n",
                            Threads.threadid(), string(L), string(R), string(rL), string(rR),
                            pathL.root_sign, pathR.root_sign, pathL.depth, pathR.depth)
                end
                return nothing
            end

            # Depth bound: merged tree height is pathL.depth + 1 + pathR.depth
            new_root_depth = pathL.depth + 1 + pathR.depth
            if new_root_depth > MAX_LP2_DEPTH
                g.n_depth_pruned += 1
                return nothing
            end

            # Compute the edge label for the new rL->rR link.
            # Same arithmetic as the cycle-emit case, but stored instead of emitted.
            edge_row = copy(fb_row)
            for (j, v) in pathL.row
                nv = get(edge_row, j, 0) - v
                nv == 0 ? delete!(edge_row, j) : (edge_row[j] = nv)
            end
            for (j, v) in pathR.row
                nv = get(edge_row, j, 0) - v
                nv == 0 ? delete!(edge_row, j) : (edge_row[j] = nv)
            end
            edge_alpha = mod(alpha - pathL.alpha - pathR.alpha, ell)
            edge_beta  = mod(beta  - pathL.beta  - pathR.beta,  ell)

            # Attach the shallower-rooted tree under the deeper one.
            if pathL.depth <= pathR.depth
                # attach rL as child of rR
                g.nodes[rL] = LP2Node(rR, pathR.depth + 1,
                                      edge_row, edge_alpha, edge_beta)
            else
                # attach rR as child of rL; negate edge label (direction flipped)
                neg_edge_row = Dict{Int,Int}()
                for (j, v) in edge_row
                    neg_edge_row[j] = -v
                end
                neg_edge_alpha = mod(ell - edge_alpha, ell)
                neg_edge_beta  = mod(ell - edge_beta,  ell)
                g.nodes[rR] = LP2Node(rL, pathL.depth + 1,
                                      neg_edge_row, neg_edge_alpha, neg_edge_beta)
            end
        end

        # Integrity check: verify no cycle was just introduced for the two nodes we touched.
        # This is O(depth) and cheap; remove once the bug is confirmed fixed.
        for check_pt in (L, R)
            visited_check = Set{NTuple{2,Int}}()
            walk = check_pt
            steps = 0
            while true
                n = get(g.nodes, walk, nothing)
                n === nothing && break
                n.parent === nothing && break
                if n.parent in visited_check
                    @printf("[LP2-POSTCYCLE tid=%d] Cycle introduced by last insert! node=%s parent=%s\n",
                            Threads.threadid(), string(walk), string(n.parent))
                    @printf("[LP2-POSTCYCLE] L=%s R=%s rL=%s rR=%s\n",
                            string(L), string(R), string(rL), string(rR))
                    flush(stdout)
                    error("lp2_insert_edge!: cycle introduced — see LP2-POSTCYCLE diagnostics")
                end
                push!(visited_check, walk)
                walk = n.parent
                steps += 1
                steps > length(g.nodes) + 5 && break
            end
        end

        return nothing
    end
end
