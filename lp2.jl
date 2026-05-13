# =============================================================================
#  lp2.jl  --  2-Large-Prime graph structures and helpers
#
#  Included by trial3_fixed.jl. Requires: ell (global), fp/fpinv (from trial1),
#  Div2/jac_* types, and the sparse_add!/lp2_subtract_rows helpers.
#
#  KEY CHANGE vs. previous version:
#    LP2Node now stores a SmallRow (not a single edge_col/edge_val pair) for the
#    edge-to-parent label. This enables cross-tree merges: when both L and R are
#    already in the graph but in *different* spanning trees, we walk both paths to
#    their respective roots, compose the two SmallRows plus the new edge into a
#    single composite SmallRow, and attach rR as a depth-1 child of rL. The
#    composite row records the full path contribution in one hop so subsequent
#    lp2_path_to_root walks remain allocation-free and depth-bounded.
#
#    Previously cross-tree merges were silently discarded, which meant that at
#    large p the graph accumulated tens of thousands of disconnected depth-1/2
#    stubs and almost never formed a cycle. This produced zero 2-LP emissions and
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
#   - A cross-tree merge composes two depth-≤MAX_LP2_DEPTH paths plus 1 edge.
#   - Because composite edges can themselves contain multiple nonzeros, we MUST 
#     provide a capacity strictly larger than MAX_LP2_ROW_WEIGHT (64) so that 
#     large rows are properly evaluated and pruned by the weight limits rather 
#     than silently truncating and mathematically corrupting the graph.
#
# SMALL_ROW_CAP = 128 safely covers all cases below the pruning threshold.

const SMALL_ROW_CAP = 128

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
        # Capacity overflow — return r unmodified. If this happens, the length
        # caps at SMALL_ROW_CAP. We set the cap high enough (128) that it should
        # be pruned by MAX_LP2_ROW_WEIGHT (64) before it ever overflows.
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

# Merge all entries of src (scaled by sign) into dst. Allocation-free.
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
#  Hard principal-divisor checks for LP2 emission paths.
#  These are mandatory: any failure is a hard abort.
# ---------------------------------------------------------------------------

const LP2_PRINCIPAL_CHECK_CTX = Ref{Any}(nothing)

function set_lp2_principal_check_context!(fb::Vector{NTuple{2,Int}},
                                          G::Div2,
                                          T::Div2)
    LP2_PRINCIPAL_CHECK_CTX[] = (fb = fb, G = G, T = T)
    return nothing
end

function clear_lp2_principal_check_context!()
    LP2_PRINCIPAL_CHECK_CTX[] = nothing
    return nothing
end

@inline function _lp2_principal_ctx()
    ctx = LP2_PRINCIPAL_CHECK_CTX[]
    ctx === nothing && error("LP2 principal-divisor check context not set")
    return ctx
end

function lp2_assert_even_cycle_principal!(
    row::Dict{Int,Int}, alpha::Int, beta::Int;
    tag::String = ""
)
    ctx = _lp2_principal_ctx()
    fb = ctx.fb
    G  = ctx.G
    T  = ctx.T

    lhs = JacID
    for (idx, v) in row
        pt = fb[idx]
        Dp = mumford1(pt[1], pt[2])
        Dv = jac_mul_raw(Dp, abs(v))
        lhs = v > 0 ? jac_add(lhs, Dv) : jac_sub(lhs, Dv)
    end

    rhs = jac_add(jac_mul(G, alpha), jac_mul(T, beta))

    if lhs != rhs
        rhs_neg = jac_neg(rhs)
        if lhs == rhs_neg
            @printf("[LP2 PRINCIPAL %s] SIGN-FLIP on even cycle: alpha=%d beta=%d row_w=%d\n",
                    tag, alpha, beta, length(row))
        else
            @printf("[LP2 PRINCIPAL %s] FAIL on even cycle: alpha=%d beta=%d row_w=%d\n",
                    tag, alpha, beta, length(row))
        end
        @printf("  lhs = %s\n", string(lhs))
        @printf("  rhs = %s\n", string(rhs))
        @printf("  row = %s\n", string(row))
        @assert false "LP2 even-cycle principal divisor check failed"
    end

    return true
end

function lp2_assert_odd_cycle_principal!(
    root::NTuple{2,Int}, row::Dict{Int,Int}, alpha::Int, beta::Int;
    tag::String = ""
)
    ctx = _lp2_principal_ctx()
    fb = ctx.fb
    G  = ctx.G
    T  = ctx.T

    root_atom = mumford1(root[1], root[2])
    lhs = jac_add(root_atom, root_atom)
    for (idx, v) in row
        pt = fb[idx]
        Dp = mumford1(pt[1], pt[2])
        Dv = jac_mul_raw(Dp, abs(v))
        lhs = v > 0 ? jac_add(lhs, Dv) : jac_sub(lhs, Dv)
    end

    rhs = jac_add(jac_mul(G, alpha), jac_mul(T, beta))

    if lhs != rhs
        rhs_neg = jac_neg(rhs)
        if lhs == rhs_neg
            @printf("[LP2 PRINCIPAL %s] SIGN-FLIP on odd cycle: root=%s alpha=%d beta=%d row_w=%d\n",
                    tag, string(root), alpha, beta, length(row))
        else
            @printf("[LP2 PRINCIPAL %s] FAIL on odd cycle: root=%s alpha=%d beta=%d row_w=%d\n",
                    tag, string(root), alpha, beta, length(row))
        end
        @printf("  lhs = %s\n", string(lhs))
        @printf("  rhs = %s\n", string(rhs))
        @printf("  row = %s\n", string(row))
        @assert false "LP2 odd-cycle principal divisor check failed"
    end

    return true
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
#    storing rR as a depth-1 child of rL with the composite edge. This collapses
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
const MAX_LP2_ROW_WEIGHT  = 64   # max nonzeros in an emitted 2-LP relation

# Hard cap on total nodes. When reached the graph is cleared entirely.
# At ~200 bytes per node (SmallRow inlined, no Dict per node), 250_000 nodes ≈ 50 MB.
const MAX_LP2_NODES = 50_000

struct LP2Node
    parent    ::Union{NTuple{2,Int}, Nothing}   # nothing = root
    # Edge to parent: SmallRow encodes all FB contributions along this edge.
    # For direct insertions this has at most 1 entry; for cross-tree composite
    # edges it may have many entries (bounded by SMALL_ROW_CAP).
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

# Walk from pt to its root. Returns root key or nothing if pt not in tree.
#
# After cross-tree merges, grafted subtree nodes retain stale depth fields; their
# actual depth to the new root can exceed MAX_LP2_DEPTH. We use a generous step
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
            return nothing   # don't delete — that orphans children
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
        # Missing node: dangling parent pointer from a deleted node.
        # This is corruption — return nothing so the caller discards cleanly.
        if node === nothing
            return nothing
        end
        node.parent === nothing && break   # reached root cleanly

        depth += 1
        if depth > _LP2_ROOT_STEP_LIMIT    # same budget as lp2_tree_root
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

function lp2_actual_depth(g::LP2Graph, x)
    d = 0
    seen = Set{typeof(x)}()
    cur = x

    while true
        cur in seen && error("cycle in LP2 parent pointers at $cur")
        push!(seen, cur)

        node = get(g.nodes, cur, nothing)
        node === nothing && return d
        node.parent === nothing && return d

        d += 1
        cur = node.parent
    end
end

# ---------------------------------------------------------------------------
#  lp2_insert_edge!
#
#  Try to insert edge (L, R) with label (fb_row, alpha, beta).
#
#  fb_row has at most 1 entry (one FB point per 2-LP step). We convert it to a
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
        break
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

        signL = pathL.root_sign
        signR = pathR.root_sign

        # ── Odd cycle ───────────────────────────────────────────────────────
        if signL == signR
            # signL == signR means the roots add up to ±2*atom(root).
            g.n_parity_pruned += 1
            g.n_odd_stored    += 1

            # Base cycle row before root-sign normalization:
            odd_row = Dict{Int,Int}()
            smallrow_add_into_dict!(odd_row, pathL.row)
            smallrow_add_into_dict!(odd_row, pathR.row)
            smallrow_subtract_into_dict!(odd_row, edge_sr)

            # Extract the proper positive coefficients for the RHS
            odd_alpha = mod(pathL.alpha + pathR.alpha - alpha, ell)
            odd_beta  = mod(pathL.beta  + pathR.beta  - beta,  ell)

            # Normalize to +2*atom(root) so the stored invariant is always
            #   2*atom(root) + row = alpha*G + beta*T.
            if signL == -1
                for k in keys(odd_row)
                    odd_row[k] = -odd_row[k]
                end
                odd_alpha = mod(-odd_alpha, ell)
                odd_beta  = mod(-odd_beta,  ell)
            end

            if length(odd_row) > MAX_LP2_ROW_WEIGHT
                g.n_weight_pruned += 1
                return nothing
            end

            lp2_assert_odd_cycle_principal!(rL, odd_row, odd_alpha, odd_beta;
                                             tag = "lp2_insert_edge!/odd_cycle")

            return (
                type  = :odd_cycle,
                root  = rL,
                row   = odd_row,
                alpha = odd_alpha,
                beta  = odd_beta,
                debug = (
                    L = L, R = R, rL = rL, rR = rR,
                    signL = signL, signR = signR,
                    depthL = pathL.depth, depthR = pathR.depth,
                    edge_row = smallrow_to_dict(edge_sr),
                    pathL_alpha = pathL.alpha, pathL_beta  = pathL.beta,
                    pathR_alpha = pathR.alpha, pathR_beta  = pathR.beta,
                    pathL_row = smallrow_to_dict(pathL.row),
                    pathR_row = smallrow_to_dict(pathR.row),
                )
            )
        end

        # ── Even cycle ──────────────────────────────────────────────────────
        # Here the root terms cancel directly (signL != signR):
        combined = Dict{Int,Int}()
        smallrow_add_into_dict!(combined, pathL.row)
        smallrow_add_into_dict!(combined, pathR.row)
        smallrow_subtract_into_dict!(combined, edge_sr)

        if length(combined) > MAX_LP2_ROW_WEIGHT
            g.n_weight_pruned += 1
            return nothing
        end

        combined_alpha = mod(pathL.alpha + pathR.alpha - alpha, ell)
        combined_beta  = mod(pathL.beta  + pathR.beta  - beta,  ell)

        if isempty(combined) || (combined_alpha == 0 && combined_beta == 0)
            return nothing
        end

        lp2_assert_even_cycle_principal!(combined, combined_alpha, combined_beta;
                                         tag = "lp2_insert_edge!/even_cycle")

        g.n_emitted += 1

        debug_payload = (
            L = L, R = R, rL = rL, rR = rR,
            signL = signL, signR = signR,
            path_depthL = pathL.depth, path_depthR = pathR.depth,
            edge_row = smallrow_to_dict(edge_sr),
            combined = copy(combined),
            combined_alpha = combined_alpha, combined_beta  = combined_beta,
            pathL_alpha = pathL.alpha, pathL_beta  = pathL.beta,
            pathR_alpha = pathR.alpha, pathR_beta  = pathR.beta,
            pathL_row = smallrow_to_dict(pathL.row), pathR_row = smallrow_to_dict(pathR.row),
        )

        lp2_prune_component!(g, rL)

        return (
            type  = :even_cycle,
            row   = combined,
            alpha = combined_alpha,
            beta  = combined_beta,
            root_signs = (signL, signR),
            depths = (pathL.depth, pathR.depth),
            debug = debug_payload,
        )
    end

    # ── Node cap: evict before inserting new nodes ───────────────────────────
    if length(g.nodes) >= MAX_LP2_NODES
        empty!(g.nodes)
        g.n_clears += 1
        rL = nothing
        rR = nothing
    end

    node_L = get(g.nodes, L, nothing)
    node_R = get(g.nodes, R, nothing)

    # ── Case (a): both new ───────────────────────────────────────────────────
    if node_L === nothing && node_R === nothing
        if 1 > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end
        g.nodes[R] = LP2Node(nothing, SmallRow(), 0, 0)
        g.nodes[L] = LP2Node(R, edge_sr, alpha, beta)
        return nothing
    end

    # ── Case (b): L new, R exists ────────────────────────────────────────────
    if node_L === nothing
        new_depth = lp2_actual_depth(g, R)
        if new_depth > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end
        g.nodes[L] = LP2Node(R, edge_sr, alpha, beta)
        return nothing
    end

    # ── Case (c): R new, L exists ────────────────────────────────────────────
    if node_R === nothing
        new_depth = lp2_actual_depth(g, L)
        if new_depth > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end
        g.nodes[R] = LP2Node(L, edge_sr, alpha, beta)
        return nothing
    end

    # ── Case (e): both exist in DIFFERENT trees — cross-tree merge ───────────
    pathL = lp2_path_to_root(g, L, ell)
    pathR = lp2_path_to_root(g, R, ell)

    if pathL === nothing || pathR === nothing
        g.n_depth_pruned += 1
        return nothing
    end

    # Determine merge direction (smaller depth merges into larger depth)
    depthL = lp2_actual_depth(g, L)
    depthR = lp2_actual_depth(g, R)
    
    if depthL <= depthR
        src_root, dst_root   = rL, rR
        src_path, dst_path   = pathL, pathR
        src_sign, dst_sign   = pathL.root_sign, pathR.root_sign
    else
        src_root, dst_root   = rR, rL
        src_path, dst_path   = pathR, pathL
        src_sign, dst_sign   = pathR.root_sign, pathL.root_sign
    end

    # We can ONLY merge if the roots share the same parity/sign in the bipartite graph.
    # Connecting mismatched signs breaks the alternating path assumptions entirely.
    if src_sign != dst_sign
        return nothing
    end

    sig = src_sign

    # Compute composite edge representing the jump from src_root directly to dst_root
    comp_row = smallrow_merge(SmallRow(), edge_sr, -sig)
    comp_row = smallrow_merge(comp_row, src_path.row, sig)
    comp_row = smallrow_merge(comp_row, dst_path.row, sig)

    comp_alpha = mod(sig * (src_path.alpha + dst_path.alpha - alpha), ell)
    comp_beta  = mod(sig * (src_path.beta  + dst_path.beta  - beta),  ell)

    if comp_row.len > MAX_LP2_ROW_WEIGHT
        g.n_weight_pruned += 1
        return nothing
    end

    if dst_path.depth + 1 > MAX_LP2_DEPTH
        g.n_depth_pruned += 1
        return nothing
    end

    # Mutate the graph and attach
    g.nodes[src_root] = LP2Node(
        dst_root,
        comp_row,
        comp_alpha,
        comp_beta
    )

    g.n_merges += 1
    return nothing
end

# ---------------------------------------------------------------------------
#  lp2_prune_component!
#
#  Delete all nodes in the spanning tree rooted at `root`.
#  Called after an even-cycle emission to reclaim the whole component.
#
#  Implementation: build a reverse-adjacency (parent → children) map in one
#  pass over g.nodes, then BFS/DFS from `root`. This is O(N) in the number
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
    # but since we don't track that we scan all nodes. One O(N) pass.
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
#  subtrees). We now delegate to lp2_prune_component! which correctly
#  removes the entire tree. The `start` argument is walked to its root first.
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
