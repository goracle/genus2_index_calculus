# =============================================================================
#  trial3_tree.jl  --  Walk guidance, LP stage tree, and sparse-row helpers.
#
#  WalkGuidance: lightweight online statistics used to steer the anchor point
#    selection toward under-represented factor-base columns.
#
#  LPStageTree: a Diem-style staged tree of 1-LP partial relations.  Each
#    vertex L in the tree stores an expansion
#      atom(L) + row[L] = -alpha[L]·G - beta[L]·T
#    where row[L] is a factor-base-only sparse vector.  Vertices are admitted
#    up to MAX_TREE_DEPTH to prevent exponential row-weight growth.
#
#  Sparse row helpers (sparse_add!, sparse_copy!) and LP2 graph wrappers
#  (lp2_graph_node_count, clear_lp2_graph!) complete the utilities needed
#  by phase2_worker without importing the LP2 internals.
# =============================================================================

# ---------------------------------------------------------------------------
#  WalkGuidance — online column-degree statistics for anchor selection
# ---------------------------------------------------------------------------
mutable struct WalkGuidance
    col_degree  ::Dict{Int,Int}   # accumulated use-count per FB column index
    recent_cols ::Vector{Int}     # sliding window of recently used columns
    recent_limit::Int
end

function WalkGuidance(; recent_limit::Int = 64)
    WalkGuidance(Dict{Int,Int}(), Int[], recent_limit)
end

# Register the columns touched by a new relation.
function update_guidance!(G::WalkGuidance, row::Dict{Int,Int})
    for (col, v) in row
        v == 0 && continue
        G.col_degree[col] = get(G.col_degree, col, 0) + 1
        push!(G.recent_cols, col)
    end
    if length(G.recent_cols) > G.recent_limit
        deleteat!(G.recent_cols, 1:length(G.recent_cols) - G.recent_limit)
    end
    return nothing
end

# ---------------------------------------------------------------------------
#  Sparse row arithmetic helpers
#
#  sparse_add!: dst += sign * src  (zero entries are deleted from dst)
#  sparse_copy!: dst = src  (reuses dst's allocation, clears first)
# ---------------------------------------------------------------------------
function sparse_add!(dst::Dict{Int,Int}, src::Dict{Int,Int}; sign::Int = 1)
    for (k, v) in src
        nv = get(dst, k, 0) + sign * v
        nv == 0 ? delete!(dst, k) : (dst[k] = nv)
    end
    return dst
end

# Fast path for raw dictionaries
function sparse_copy!(dst::Dict{Int64, Int64}, src::Dict{Int64, Int64})
    empty!(dst)
    sizehint!(dst, length(src))
    for (k, v) in src
        dst[k] = v
    end
    return dst
end

# Passthrough to handle a ThreadScratchpad wrapper automatically
function sparse_copy!(scratch::ThreadScratchpad, src::Dict{Int64, Int64})
    # Replace .combined_scratch with the exact name of the Dict field in your struct
    return sparse_copy!(scratch.combined_scratch, src)
end

# ---------------------------------------------------------------------------
#  LP2 graph introspection helpers
#
#  These wrap lp2.jl's internal layout so phase2_worker does not need to
#  know whether the graph uses a `nodes` or `vertices` field.
# ---------------------------------------------------------------------------
function lp2_graph_node_count(g)::Int
    for nm in propertynames(g)
        if nm === :nodes || nm === :vertices
            obj = getproperty(g, nm)
            return (obj isa AbstractDict || obj isa AbstractVector) ? length(obj) : 0
        end
    end
    return typemax(Int)
end

function clear_lp2_graph!(g)
    for nm in propertynames(g)
        if nm === :nodes || nm === :vertices
            obj = getproperty(g, nm)
            (obj isa AbstractDict || obj isa AbstractVector) && empty!(obj)
            return nothing
        end
    end
    return nothing
end

# ---------------------------------------------------------------------------
#  LPStageTree — depth-bounded Diem-style 1-LP partial-relation tree
#
#  Each node stores:
#    parent : NTuple{2,Int} | Nothing  (parent LP point, or root if nothing)
#    depth  : Int                       (distance from root)
#    row    : Dict{Int,Int}             (FB-only sparse vector, owned by node)
#    alpha  : Int                       (scalar coefficient for G)
#    beta   : Int                       (scalar coefficient for T)
#
#  Invariant at node L:
#    atom(L) + row[L] = -alpha[L]·G - beta[L]·T   (in Jac)
#
#  The stage mechanism doubles the depth limit each time the tree reaches
#  its current stage_limit, up to max_vertices.  This mirrors Diem's
#  staged attachment policy and prevents the tree from becoming a star graph
#  (which would create very heavy rows).
# ---------------------------------------------------------------------------

mutable struct TreeVertex
    parent ::Union{Nothing, NTuple{2,Int}}
    depth  ::Int
    row    ::Dict{Int,Int}
    alpha  ::Int
    beta   ::Int
end

mutable struct LPStageTree
    vertices    ::Dict{NTuple{2,Int}, TreeVertex}
    stage       ::Int
    stage_limit ::Int
    max_vertices::Int
end

function LPStageTree(; stage_limit::Int, max_vertices::Int)
    LPStageTree(Dict{NTuple{2,Int}, TreeVertex}(), 1, stage_limit, max_vertices)
end

# Advance the stage when the tree fills its current stage_limit.
function tree_maybe_advance_stage!(tree::LPStageTree)
    if length(tree.vertices) >= tree.stage_limit && tree.stage_limit < tree.max_vertices
        tree.stage += 1
        tree.stage_limit = min(tree.max_vertices,
                               max(tree.stage_limit * 2, tree.stage_limit + 1))
    end
    return nothing
end

function tree_depth(tree::LPStageTree, pt::NTuple{2,Int})::Int
    haskey(tree.vertices, pt) ? tree.vertices[pt].depth : 0
end

function tree_row(tree::LPStageTree, pt::NTuple{2,Int})::Dict{Int,Int}
    haskey(tree.vertices, pt) || error("tree_row called on non-tree vertex")
    copy(tree.vertices[pt].row)
end

function tree_ab(tree::LPStageTree, pt::NTuple{2,Int})::Tuple{Int,Int}
    haskey(tree.vertices, pt) || error("tree_ab called on non-tree vertex")
    v = tree.vertices[pt]
    (v.alpha, v.beta)
end

# Depth > 2 causes exponential row-weight blowup — hard limit.
const MAX_TREE_DEPTH = 2

# Add a vertex to the tree.  Returns false if pt is already present or
# if the parent's depth exceeds MAX_TREE_DEPTH - 1.
function tree_add_vertex!(tree::LPStageTree, pt::NTuple{2,Int},
                          parent::Union{Nothing, NTuple{2,Int}},
                          row::Dict{Int,Int}, alpha::Int, beta::Int)::Bool
    haskey(tree.vertices, pt) && return false

    pdep = parent === nothing ? 0 : tree.vertices[parent].depth
    pdep + 1 > MAX_TREE_DEPTH && return false   # enforce sparsity cap

    tree.vertices[pt] = TreeVertex(parent, pdep + 1, copy(row), alpha, beta)
    tree_maybe_advance_stage!(tree)
    return true
end

# ---------------------------------------------------------------------------
#  point_contrib — classify a point as FB, tree, or large-prime
# ---------------------------------------------------------------------------
function point_contrib(pt    ::NTuple{2,Int},
                       pt2idx::Dict{NTuple{2,Int},Int},
                       tree  ::LPStageTree)
    if haskey(tree.vertices, pt)
        v = tree.vertices[pt]
        return (:tree, copy(v.row), v.alpha, v.beta)
    end
    idx = get(pt2idx, pt, 0)
    idx != 0 && return (:fb, Dict{Int,Int}(idx => 1), 0, 0)
    return (:lp, Dict{Int,Int}(), 0, 0)
end

# ---------------------------------------------------------------------------
#  Anchor and parent selection (guidance-steered)
# ---------------------------------------------------------------------------

# Choose the best tree vertex to use as parent for a new attachment.
# Prefers lower depth and lower column-degree saturation.
function choose_tree_parent(others ::Vector{NTuple{2,Int}},
                            pt2idx ::Dict{NTuple{2,Int},Int},
                            tree   ::LPStageTree,
                            guidance::WalkGuidance)::Union{Nothing, NTuple{2,Int}}
    cands = [pt for pt in others
             if haskey(tree.vertices, pt) && tree_depth(tree, pt) < tree.stage]
    isempty(cands) && return nothing

    best_pt = cands[1]; best_sc = Inf
    for pt in cands
        idx   = get(pt2idx, pt, 0)
        depth = tree_depth(tree, pt)
        deg   = idx == 0 ? 0 : get(guidance.col_degree, idx, 0)
        rec   = idx == 0 ? 0 : count(==(idx), guidance.recent_cols)
        sc    = 8.0*depth + 2.0*deg + 0.5*rec + 0.001*rand()
        if sc < best_sc; best_sc = sc; best_pt = pt; end
    end
    return best_pt
end

# Choose the next walk anchor from a set of candidate points.
function choose_next_anchor(cands   ::Vector{NTuple{2,Int}},
                            pt2idx  ::Dict{NTuple{2,Int},Int},
                            guidance::WalkGuidance,
                            tree    ::LPStageTree;
                            current ::Union{Nothing,NTuple{2,Int}} = nothing)
    isempty(cands) && error("choose_next_anchor called with no candidates")

    best_pt = cands[1]; best_sc = Inf
    for pt in cands
        idx   = get(pt2idx, pt, 0)
        deg   = idx == 0 ? 0 : get(guidance.col_degree, idx, 0)
        rec   = idx == 0 ? 0 : count(==(idx), guidance.recent_cols)
        depth = tree_depth(tree, pt)
        sc    = 8.0*depth + 2.0*deg + 0.5*rec
        current !== nothing && pt == current && (sc += 1.0)
        sc += 1e-6 * rand()
        if sc < best_sc; best_sc = sc; best_pt = pt; end
    end
    return best_pt
end

# ---------------------------------------------------------------------------
#  combined_relation_from_points — aggregate point_contrib across a relation
# ---------------------------------------------------------------------------
function combined_relation_from_points(points ::Vector{NTuple{2,Int}},
                                       pt2idx ::Dict{NTuple{2,Int},Int},
                                       tree   ::LPStageTree)
    row = Dict{Int,Int}()
    a = 0; b = 0; lp_count = 0; lp_pt = nothing
    for pt in points
        typ, r, aa, bb = point_contrib(pt, pt2idx, tree)
        if typ == :lp
            lp_count += 1; lp_pt = pt
        else
            sparse_add!(row, r); a = mod(a+aa, ell); b = mod(b+bb, ell)
        end
    end
    return lp_count, lp_pt, row, a, b
end
