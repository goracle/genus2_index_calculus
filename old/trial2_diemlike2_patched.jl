#!/usr/bin/env julia
# =============================================================================
#  trial2.jl  --  Index calculus via Markov-walk / phi-function relations
#
#  Same curve/field/subgroup as trial1.jl.  Instead of the Gaudry-Harley
#  random-pair strategy we use the Diem plane-model variant:
#
#  Walk step  (current point P0 = (px, py)):
#    1. Pick random (alpha, beta), form D = alpha*G + beta*T  (degree-2 Mumford).
#       Extract the two affine support points Q1=(x1,y1), Q2=(x2,y2) of D.
#    2. Build phi = a*x^2 + b*x + c + d*y  vanishing at P0, Q1, Q2.
#       (4 coefficients, 1 overall scale => 3 free parameters, 3 conditions
#        => unique phi up to scale.)
#    3. div(phi) on C has degree 5 (C is a plane quintic):
#         div(phi) = [P0] + [Q1] + [Q2] + [R] + [S] - 5*[inf]
#       Recover R, S by forming N(x) = (a*x^2+b*x+c)^2 - d^2*f(x) (degree 5),
#       then dividing out the three known roots px, x1, x2.
#    4. Principal-divisor relation in Cl^0:
#         atom(P0) + atom(R) + atom(S) = -(alpha*G + beta*T)
#       where atom(P) = [P] - [inf].
#       When P0, R, S are all in the factor base F, record this relation.
#    5. Set P_next = R;  add P0, R, S to F during the build phase.
#
#  Phase 1: walk until |F| >= fb_target.
#  Phase 2: continue walk, recording relations whenever P0,R,S in F.
#           Stop after |F|+20 relations; left-kernel => k.
# =============================================================================

include("trial1_autoell_p10.jl")   # all Fp/poly/Jacobian/curve utilities
using LinearAlgebra

# ---------------------------------------------------------------------------
#  phi construction
#
#  phi(x,y) = a*x^2 + b*x + c + d*y
#
#  Vanishing conditions (mod p):
#    a*px^2 + b*px + c + d*py = 0
#    a*x1^2 + b*x1 + c + d*y1 = 0
#    a*x2^2 + b*x2 + c + d*y2 = 0
#
#  Fix d=1 and solve the 3x3 system in (a,b,c).  If singular, fix a=1 and
#  solve for (b,c,d).  Returns (a,b,c,d) or nothing.
# ---------------------------------------------------------------------------
function build_phi(px::Int, py::Int,
                   x1::Int, y1::Int,
                   x2::Int, y2::Int)::Union{NTuple{4,Int}, Nothing}

    M = [fp(px*px)  px  1  py;
         fp(x1*x1)  x1  1  y1;
         fp(x2*x2)  x2  1  y2]

    # 3x3 Gaussian elimination over Fp.  A is 3x3, rhs is length-3.
    function solve3(A::Matrix{Int}, rhs::Vector{Int})::Union{Vector{Int}, Nothing}
        Aug = hcat(mod.(A, p), mod.(rhs, p))
        for col in 1:3
            piv = findfirst(r -> Aug[r, col] != 0, col:3)
            piv === nothing && return nothing
            piv += col - 1
            Aug[[col, piv], :] = Aug[[piv, col], :]
            inv_lc = powermod(Int(Aug[col, col]), p - 2, p)
            Aug[col, :] = mod.(Aug[col, :] .* inv_lc, p)
            for r in 1:3
                r == col && continue
                f = Aug[r, col]
                f == 0 && continue
                Aug[r, :] = mod.(Aug[r, :] .- f .* Aug[col, :], p)
            end
        end
        Aug[:, 4]
    end

    # Try d = 1: solve M[:,1:3] * [a,b,c]' = -M[:,4]
    rhs1 = [fp(-py), fp(-y1), fp(-y2)]
    sol1 = solve3(M[:, 1:3], rhs1)
    if sol1 !== nothing
        a, b, c = sol1
        return (fp(a), fp(b), fp(c), 1)
    end

    # Fallback: a = 1, solve M[:,2:4] * [b,c,d]' = -M[:,1]
    rhs2 = [fp(-fp(px*px)), fp(-fp(x1*x1)), fp(-fp(x2*x2))]
    sol2 = solve3(M[:, 2:4], rhs2)
    sol2 === nothing && return nothing
    b2, c2, d2 = sol2
    return (1, fp(b2), fp(c2), fp(d2))
end

# ---------------------------------------------------------------------------
#  Residual intersection points R, S
#
#  phi(x,y) = 0 on C: substitute y = -(a*x^2+b*x+c)/d into y^2=f(x):
#    N(x) = (a*x^2+b*x+c)^2 - d^2*f(x)   (degree 5, leading coeff -d^2)
#
#  Three roots px, x1, x2 are known.  Divide them out -> degree-2 residual.
#  Returns vector of (x,y) pairs with correct y-sign (length 0, 1, or 2).
# ---------------------------------------------------------------------------
function phi_residual_points(a::Int, b::Int, c::Int, d::Int,
                              px::Int, x1::Int, x2::Int)::Vector{NTuple{2,Int}}
    d == 0 && return NTuple{2,Int}[]

    # N(x) = (a*x^2+b*x+c)^2 - d^2*f(x)
    apoly = Int[c, b, a]                    # ascending-coeff representation
    sq    = pmul(apoly, apoly)              # degree 4
    fd2   = pscale(F_POLY, fp(d * d))      # d^2*f(x), degree 5 (len 6)
    nlen  = max(length(sq), length(fd2))
    N     = ptrim(mod.(
                vcat(sq,  zeros(Int, nlen - length(sq))) .-
                vcat(fd2, zeros(Int, nlen - length(fd2))),
                p))

    # Divide out a known root r => divide by (x - r) = [-r, 1]
    function divide_out(poly::Vector{Int}, r::Int)::Union{Vector{Int}, Nothing}
        q, rem = pdivrem(poly, Int[fp(-r), 1])
        pzero(rem) ? q : nothing
    end

    q = divide_out(N,  px);  q === nothing && return NTuple{2,Int}[]
    q = divide_out(q,  x1);  q === nothing && return NTuple{2,Int}[]
    q = divide_out(q,  x2);  q === nothing && return NTuple{2,Int}[]
    q = ptrim(q)

    # Given x-coordinate, find correct y using phi(x,y) = 0
    function y_for_x(xr::Int)::Union{NTuple{2,Int}, Nothing}
        yr = sqrt_fp(eval_f(xr));  yr === nothing && return nothing
        base = fp(a * fp(xr * xr) + b * xr + c)
        fp(base + d * yr) == 0 && return (xr, yr)
        fp(base - d * yr) == 0 && return (xr, fp(-yr))
        return nothing
    end

    pts = NTuple{2,Int}[]
    dq  = pdeg(q)

    if dq == 1
        xr = fp(-q[1] * fpinv(q[2]))
        pt = y_for_x(xr);  pt !== nothing && push!(pts, pt)

    elseif dq == 2
        q_monic = pscale(q, fpinv(q[end]))   # normalise to monic for u2_roots
        rs = u2_roots(q_monic);  rs === nothing && return NTuple{2,Int}[]
        for xr in rs
            pt = y_for_x(xr);  pt !== nothing && push!(pts, pt)
        end
    end

    pts
end




# ---------------------------------------------------------------------------
#  Matrix diagnostics for LA speedups
#
#  We inspect the final sparse relation matrix in three ways:
#    1. Row/column sparsity statistics.
#    2. Column co-occurrence components (possible block decomposition).
#    3. Leaf-stripping / peeling core (possible sparse elimination savings).
# ---------------------------------------------------------------------------
function analyze_relation_matrix(rel_rows::Vector{Dict{Int,Int}}, nF::Int; verbose::Bool=true)
    nrel = length(rel_rows)
    nrel == 0 && return nothing

    # Row supports and column degrees.
    supports    = Vector{Vector{Int}}(undef, nrel)
    col_to_rows = [Int[] for _ in 1:nF]
    coldeg      = zeros(Int, nF)
    row_hist    = Dict{Int,Int}()
    total_nz    = 0

    for i in 1:nrel
        cols = Int[]
        for (j, v) in rel_rows[i]
            v == 0 && continue
            1 <= j <= nF || continue
            push!(cols, j)
        end
        sort!(cols)
        supports[i] = cols
        w = length(cols)
        row_hist[w] = get(row_hist, w, 0) + 1
        total_nz += w
        for j in cols
            coldeg[j] += 1
            push!(col_to_rows[j], i)
        end
    end

    # Basic stats.
    deg_sorted = sort(copy(coldeg))
    zero_cols  = count(==(0), coldeg)
    deg1_cols   = count(==(1), coldeg)
    deg2_cols   = count(==(2), coldeg)
    avg_w       = total_nz / nrel
    density     = total_nz / (nrel * nF)

    # Connected components of the column co-occurrence graph.
    parent = collect(1:nF)
    rank   = zeros(Int, nF)

    function findroot(x::Int)::Int
        y = x
        while parent[y] != y
            y = parent[y]
        end
        while parent[x] != x
            px = parent[x]
            parent[x] = y
            x = px
        end
        return y
    end

    function unite(a::Int, b::Int)
        ra = findroot(a)
        rb = findroot(b)
        ra == rb && return
        if rank[ra] < rank[rb]
            parent[ra] = rb
        elseif rank[ra] > rank[rb]
            parent[rb] = ra
        else
            parent[rb] = ra
            rank[ra] += 1
        end
    end

    for cols in supports
        length(cols) <= 1 && continue
        c1 = cols[1]
        for k in 2:length(cols)
            unite(c1, cols[k])
        end
    end

    comp_sizes = Dict{Int,Int}()
    for j in 1:nF
        r = findroot(j)
        comp_sizes[r] = get(comp_sizes, r, 0) + 1
    end
    comps = sort(collect(values(comp_sizes)), rev=true)
    ncomp = length(comps)
    largest_comp = isempty(comps) ? 0 : comps[1]
    singleton_comps = count(==(1), comps)

    # Peeling / leaf stripping on the incidence hypergraph.
    active_col = trues(nF)
    active_row = trues(nrel)
    deg        = copy(coldeg)
    q          = Int[]

    for j in 1:nF
        deg[j] <= 1 && push!(q, j)
    end

    while !isempty(q)
        j = pop!(q)
        active_col[j] || continue
        deg[j] > 1 && continue
        active_col[j] = false

        for ri in col_to_rows[j]
            active_row[ri] || continue
            active_row[ri] = false
            for k in supports[ri]
                k == j && continue
                active_col[k] || continue
                deg[k] -= 1
                deg[k] <= 1 && push!(q, k)
            end
        end
    end

    core_cols = count(identity, active_col)
    core_rows = count(identity, active_row)

    if verbose
        println("Matrix diagnostics for LA:")
        @printf("  rows = %d, cols = %d, nonzeros = %d, avg row weight = %.3f, density = %.4g
",
                nrel, nF, total_nz, avg_w, density)

        row_keys = sort(collect(keys(row_hist)))
        row_descs = String[]
        for k in row_keys
            push!(row_descs, string(k, ":", row_hist[k]))
        end
        println("  row-weight histogram: ", join(row_descs, ", "))

        @printf("  column degrees: zero=%d, deg1=%d, deg2=%d, min=%d, median=%d, max=%d
",
                zero_cols, deg1_cols, deg2_cols,
                isempty(deg_sorted) ? 0 : deg_sorted[1],
                isempty(deg_sorted) ? 0 : deg_sorted[(length(deg_sorted)+1) ÷ 2],
                isempty(deg_sorted) ? 0 : deg_sorted[end])

        @printf("  component graph: %d components, largest=%d, singletons=%d
",
                ncomp, largest_comp, singleton_comps)

        @printf("  peel/core estimate: core cols = %d, core rows = %d, peeled cols = %d
",
                core_cols, core_rows, nF - core_cols)

        if largest_comp < nF
            @printf("  note: matrix is block-disconnected enough to split off subproblems
")
        end
        if core_cols < nF
            @printf("  note: leaf-stripping removes %d/%d columns before any dense solve
",
                    nF - core_cols, nF)
        end
    end

    return (
        supports = supports,
        row_hist = row_hist,
        coldeg = coldeg,
        components = comps,
        core_cols = core_cols,
        core_rows = core_rows,
        density = density,
        total_nz = total_nz,
    )
end


# ---------------------------------------------------------------------------
#  Spectral gap diagnostics for the column co-occurrence graph
#
#  For a given prefix of relations, build the weighted graph on factor-base
#  columns where each relation contributes a clique on its support. Then
#  compute the second-largest eigenvalue of the normalized adjacency matrix
#  B = D^{-1/2} W D^{-1/2}. The spectral gap is 1 - λ2(B).
#
#  For connected non-bipartite graphs, a larger gap generally means better
#  expansion / mixing, which is the regime where sparse iterative LA tends to
#  behave well.
# ---------------------------------------------------------------------------
function spectral_gap_report(rel_rows::Vector{Dict{Int,Int}}, nF::Int;
                             prefixes::Vector{Int}=Int[],
                             verbose::Bool=true)
    nrel = length(rel_rows)
    nrel == 0 && return nothing

    prefixes = isempty(prefixes) ? unique(sort(Int[
        min(nrel, max(50, nrel ÷ 8)),
        min(nrel, max(100, nrel ÷ 4)),
        min(nrel, max(200, nrel ÷ 2)),
        nrel
    ])) : unique(sort(filter(x -> 1 <= x <= nrel, prefixes)))

    function gap_for_prefix(m::Int)
        # Weighted adjacency matrix for the first m rows.
        W = zeros(Float64, nF, nF)
        for i in 1:m
            cols = Int[]
            for (j, v) in rel_rows[i]
                v == 0 && continue
                1 <= j <= nF || continue
                push!(cols, j)
            end
            length(cols) <= 1 && continue
            w = 1.0 / (length(cols) - 1)
            for a in 1:length(cols)-1, b in a+1:length(cols)
                i1 = cols[a]; i2 = cols[b]
                W[i1, i2] += w
                W[i2, i1] += w
            end
        end

        deg = vec(sum(W, dims=2))
        nz = findall(>(0.0), deg)
        if length(nz) <= 1
            return (m=m, gap=NaN, lambda2=NaN, lambda1=NaN, comp_size=length(nz))
        end

        idx = nz
        Ws = W[idx, idx]
        ds = deg[idx]
        invsqrt = Diagonal(1.0 ./ sqrt.(ds))
        B = invsqrt * Ws * invsqrt
        vals = sort(real.(eigvals(Symmetric(B))), rev=true)
        λ1 = vals[1]
        λ2 = length(vals) >= 2 ? vals[2] : NaN
        gap = 1.0 - λ2
        return (m=m, gap=gap, lambda2=λ2, lambda1=λ1, comp_size=length(idx))
    end

    stats = map(gap_for_prefix, prefixes)
    if verbose
        println("Spectral gap diagnostics (normalized adjacency of column graph):")
        for s in stats
            if isnan(s.gap)
                @printf("  rows=%d: insufficient support to estimate gap\n", s.m)
            else
                @printf("  rows=%d: active cols=%d, lambda1=%.6f, lambda2=%.6f, gap=%.6f\n",
                        s.m, s.comp_size, s.lambda1, s.lambda2, s.gap)
            end
        end
        if length(stats) >= 2 && !isnan(stats[end].gap) && !isnan(stats[1].gap)
            @printf("  gap change: %.6f -> %.6f\n", stats[1].gap, stats[end].gap)
        end
    end
    return stats
end





# ---------------------------------------------------------------------------
#  Diem-like staged large-prime tree
#
#  We keep the factor base fixed first, and then grow a staged tree of large
#  primes.  The tree is built with a depth-aware attachment policy so that new
#  LPs attach mostly to the previous frontier, mirroring Diem's staged tree of
#  large prime relations.
#
#  Each tree vertex L stores an expansion
#
#      atom(L) + row[L] = -alpha[L]*G - beta[L]*T
#
#  where row[L] is a factor-base-only sparse row.
# ---------------------------------------------------------------------------


mutable struct WalkGuidance
    col_degree::Dict{Int,Int}   # support degree per factor-base column
    recent_cols::Vector{Int}    # recently used columns (sliding window)
    recent_limit::Int
end

function WalkGuidance(; recent_limit::Int = 64)
    return WalkGuidance(Dict{Int,Int}(), Int[], recent_limit)
end

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

function sparse_add!(dst::Dict{Int,Int}, src::Dict{Int,Int}; sign::Int = 1)
    for (k, v) in src
        nv = get(dst, k, 0) + sign * v
        if nv == 0
            delete!(dst, k)
        else
            dst[k] = nv
        end
    end
    return dst
end

#### gemini edits:

mutable struct TreeVertex
    parent::Union{Nothing, NTuple{2,Int}}
    depth::Int
    row::Dict{Int,Int}
    alpha::Int
    beta::Int
end

mutable struct LPStageTree
    vertices::Dict{NTuple{2,Int}, TreeVertex}
    stage::Int
    stage_limit::Int
    max_vertices::Int
end

function LPStageTree(; stage_limit::Int, max_vertices::Int)
    return LPStageTree(Dict{NTuple{2,Int}, TreeVertex}(), 1,
                       stage_limit, max_vertices)
end

function tree_maybe_advance_stage!(tree::LPStageTree)
    if length(tree.vertices) >= tree.stage_limit && tree.stage_limit < tree.max_vertices
        tree.stage += 1
        tree.stage_limit = min(tree.max_vertices, max(tree.stage_limit * 2, tree.stage_limit + 1))
    end
    return nothing
end


function tree_depth(tree::LPStageTree, pt::NTuple{2,Int})::Int
    haskey(tree.vertices, pt) ? tree.vertices[pt].depth : 0
end

function tree_row(tree::LPStageTree, pt::NTuple{2,Int})::Dict{Int,Int}
    haskey(tree.vertices, pt) || error("tree_row called on non-tree vertex")
    return copy(tree.vertices[pt].row)
end

function tree_ab(tree::LPStageTree, pt::NTuple{2,Int})::Tuple{Int,Int}
    haskey(tree.vertices, pt) || error("tree_ab called on non-tree vertex")
    v = tree.vertices[pt]
    return (v.alpha, v.beta)
end

const MAX_TREE_DEPTH = 2   # depth > 2 causes exponential row-weight blowup

function tree_add_vertex!(tree::LPStageTree, pt::NTuple{2,Int},
                          parent::Union{Nothing, NTuple{2,Int}},
                          row::Dict{Int,Int}, alpha::Int, beta::Int)
    haskey(tree.vertices, pt) && return false

    pdep = parent === nothing ? 0 : tree.vertices[parent].depth
    pdep + 1 > MAX_TREE_DEPTH && return false   # enforce sparsity cap

    tree.vertices[pt] = TreeVertex(parent, pdep + 1, copy(row), alpha, beta)
    tree_maybe_advance_stage!(tree)
    return true
end

function point_contrib(pt::NTuple{2,Int},
                       pt2idx::Dict{NTuple{2,Int},Int},
                       tree::LPStageTree)
    if haskey(tree.vertices, pt)
        v = tree.vertices[pt]
        return (:tree, copy(v.row), v.alpha, v.beta)
    end
    idx = get(pt2idx, pt, 0)
    if idx != 0
        return (:fb, Dict{Int,Int}(idx => 1), 0, 0)
    end
    return (:lp, Dict{Int,Int}(), 0, 0)
end

function choose_tree_parent(others::Vector{NTuple{2,Int}},
                            pt2idx::Dict{NTuple{2,Int},Int},
                            tree::LPStageTree,
                            guidance::WalkGuidance)::Union{Nothing, NTuple{2,Int}}
    cands = NTuple{2,Int}[]
    for pt in others
        if haskey(tree.vertices, pt) && tree_depth(tree, pt) < tree.stage
            push!(cands, pt)
        end
    end
    isempty(cands) && return nothing

    best_pt = cands[1]
    best_sc = Inf
    for pt in cands
        idx = get(pt2idx, pt, 0)
        depth = tree_depth(tree, pt)
        deg   = idx == 0 ? 0 : get(guidance.col_degree, idx, 0)
        rec   = idx == 0 ? 0 : count(==(idx), guidance.recent_cols)

        sc = 8.0 * depth + 2.0 * deg + 0.5 * rec + 0.001 * rand()
        if sc < best_sc
            best_sc = sc
            best_pt = pt
        end
    end
    return best_pt
end

function choose_next_anchor(cands::Vector{NTuple{2,Int}},
                            pt2idx::Dict{NTuple{2,Int},Int},
                            guidance::WalkGuidance,
                            tree::LPStageTree;
                            current::Union{Nothing,NTuple{2,Int}}=nothing)
    isempty(cands) && error("choose_next_anchor called with no candidates")

    best_pt = cands[1]
    best_sc = Inf
    for pt in cands
        idx = get(pt2idx, pt, 0)
        deg = idx == 0 ? 0 : get(guidance.col_degree, idx, 0)
        rec = idx == 0 ? 0 : count(==(idx), guidance.recent_cols)
        depth = tree_depth(tree, pt)

        sc = 8.0 * depth + 2.0 * deg + 0.5 * rec
        if current !== nothing && pt == current
            sc += 1.0
        end
        sc += 1e-6 * rand()

        if sc < best_sc
            best_sc = sc
            best_pt = pt
        end
    end
    return best_pt
end

function combined_relation_from_points(points::Vector{NTuple{2,Int}},
                                       pt2idx::Dict{NTuple{2,Int},Int},
                                       tree::LPStageTree)
    row = Dict{Int,Int}()
    a = 0
    b = 0
    lp_count = 0
    lp_pt = nothing
    for pt in points
        typ, r, aa, bb = point_contrib(pt, pt2idx, tree)
        if typ == :lp
            lp_count += 1
            lp_pt = pt
        else
            sparse_add!(row, r)
            a = mod(a + aa, ell)
            b = mod(b + bb, ell)
        end
    end
    return lp_count, lp_pt, row, a, b
end

# ---------------------------------------------------------------------------
#  left_kernel_all: return ALL left null vectors of R over GF(ell).
#
#  Same augmented row-reduction as left_kernel in trial1.jl, but we
#  collect every row whose R-part is all-zero, not just the first.
#  This lets the solver try each null vector in turn and pick the first
#  one with nonzero beta-sum, avoiding spurious beta=0 failures without
#  requiring a full walk restart.
# ---------------------------------------------------------------------------
function left_kernel_all(R::Matrix{Int})::Vector{Vector{Int}}
    m, n  = size(R)
    aug   = hcat(Matrix{Int}(I, m, m), mod.(R, ell))
    prow  = 1

    for col in m+1:m+n
        piv = findfirst(r -> aug[r, col] != 0, prow:m)
        piv === nothing && continue
        piv += prow - 1
        aug[[prow, piv], :] = aug[[piv, prow], :]
        s = powermod(aug[prow, col], ell - 2, ell)
        aug[prow, :] = mod.(aug[prow, :] .* s, ell)
        for r in 1:m
            r == prow && continue
            f = aug[r, col];  f == 0 && continue
            aug[r, :] = mod.(aug[r, :] .- f .* aug[prow, :], ell)
        end
        prow += 1;  prow > m && break
    end

    result = Vector{Int}[]
    for row in 1:m
        all(aug[row, m+1:end] .== 0) || continue
        γ = aug[row, 1:m]
        any(!=(0), γ) && push!(result, γ)
    end
    result
end

function index_calculus_walk(G::Div2, T::Div2;
                             fb_size::Int         = 650,
                             walk_steps::Int      = 500_000,
                             verbose::Bool        = true,
                             analyze_matrix::Bool = true,
                             solve::Bool          = true,
                             guided::Bool         = true)

    all_pts = curve_points()
    t0      = time()

    # ------------------------------------------------------------------
    # Running Jacobian state
    # ------------------------------------------------------------------
    cur_pt    = all_pts[rand(1:length(all_pts))]
    alpha_cur = rand(1:ell-1)
    beta_cur  = rand(0:ell-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur), jac_mul(T, beta_cur))

    # ------------------------------------------------------------------
    # Factor base (built dynamically in Phase 1)
    # ------------------------------------------------------------------
    fb        = NTuple{2,Int}[]
    pt2idx    = Dict{NTuple{2,Int},Int}()
    fb_frozen = false
    guidance  = WalkGuidance(recent_limit=64)

    # ------------------------------------------------------------------
    # Staged large-prime tree, only used after the FB is frozen.
    # ------------------------------------------------------------------
    tree_limit   = max(128, fb_size ÷ 2)
    tree_max     = max(2 * fb_size, fb_size + max(100, fb_size ÷ 2))
    tree         = LPStageTree(stage_limit=tree_limit, max_vertices=tree_max)

    # ------------------------------------------------------------------
    # Relation storage
    # ------------------------------------------------------------------
    alpha_vec   = Int[]
    beta_vec    = Int[]
    rel_rows    = Vector{Dict{Int,Int}}()

    # Partial rows keyed by a large prime not yet in the tree.
    lp_table = Dict{NTuple{2,Int}, Tuple{Int,Int,Dict{Int,Int}}}()

    # ------------------------------------------------------------------
    # Counters
    # ------------------------------------------------------------------
    hits_total = 0
    hits_full  = 0
    hits_lp    = 0
    hits_lp2   = 0
    hits_tree  = 0

    # ------------------------------------------------------------------
    # Precompute random walk steps to break deterministic +G degeneracy.
    # Without this, tree path substitutions yield delta_beta=0 relations
    # which span a beta-blind subspace, forcing sum(gamma*beta) = 0.
    # ------------------------------------------------------------------
    # 256 steps ensures wide beta coverage; both a,b strictly nonzero so every
    # step carries T-information and no step is a pure-G translation.
    N_STEPS = 256
    step_D = Vector{Div2}(undef, N_STEPS)
    step_a = zeros(Int, N_STEPS)
    step_b = zeros(Int, N_STEPS)
    for i in 1:N_STEPS
        a = rand(1:ell-1)
        b = rand(1:ell-1)   # strictly 1..ell-1, never 0
        step_D[i] = jac_add(jac_mul(G, a), jac_mul(T, b))
        step_a[i] = a
        step_b[i] = b
    end

    verbose && @printf("Walking %d steps...\n", walk_steps)

    for step in 1:walk_steps

        # Advance D with a random step from the precomputed table
        si        = rand(1:N_STEPS)
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a[si], ell)
        beta_cur  = mod(beta_cur  + step_b[si], ell)

        # D must be degree-2 and split over Fp
        pdeg(D_cur.u) != 2 && continue
        rs_D = u2_roots(D_cur.u)
        rs_D === nothing && continue
        x1, x2 = rs_D

        px, py = cur_pt
        (px == x1 || px == x2 || x1 == x2) && continue

        y1 = peval(D_cur.v, x1)
        y2 = peval(D_cur.v, x2)
        eval_f(x1) == fp(y1 * y1) || continue
        eval_f(x2) == fp(y2 * y2) || continue

        phi_c = build_phi(px, py, x1, y1, x2, y2)
        phi_c === nothing && continue
        a, b, c, d = phi_c

        res = phi_residual_points(a, b, c, d, px, x1, x2)
        length(res) < 2 && continue
        R, S = res[1], res[2]

        eval_f(R[1]) == fp(R[2] * R[2]) || continue
        eval_f(S[1]) == fp(S[2] * S[2]) || continue

        hits_total += 1

        al = alpha_cur
        be = beta_cur
        P0 = cur_pt
        neg_al = mod(ell - al, ell)
        neg_be = mod(ell - be, ell)

        # ------------------------------------------------------------------
        # Phase 1: fill the factor base only.
        # ------------------------------------------------------------------
        if !fb_frozen
            for pt in (P0, R, S)
                if !haskey(pt2idx, pt)
                    push!(fb, pt)
                    pt2idx[pt] = length(fb)
                end
            end

            row = Dict{Int,Int}()
            for idx in (pt2idx[P0], pt2idx[R], pt2idx[S])
                row[idx] = get(row, idx, 0) + 1
            end
            push!(alpha_vec, neg_al)
            push!(beta_vec, neg_be)
            push!(rel_rows, row)
            update_guidance!(guidance, row)
            hits_full += 1

            cur_pt = choose_next_anchor([P0, R, S], pt2idx, guidance, tree; current=P0)
            if length(fb) >= fb_size
                fb_frozen = true
                cur_pt = choose_next_anchor(fb, pt2idx, guidance, tree; current=nothing)
                verbose && @printf("  FB full (%d atoms) after %d valid steps, %d rels\n",
                                   length(fb), hits_total, hits_full)
            end
            continue
        end

        # ------------------------------------------------------------------
        # Phase 2: staged LP tree and LP collision handling.
        # ------------------------------------------------------------------
        pts = [P0, R, S]
        lp_count, lp_pt, sum_row_others, sum_a_others, sum_b_others = combined_relation_from_points(pts, pt2idx, tree)

        if lp_count == 0
            push!(alpha_vec, mod(neg_al - sum_a_others, ell))
            push!(beta_vec,  mod(neg_be - sum_b_others, ell))
            push!(rel_rows, sum_row_others)
            update_guidance!(guidance, sum_row_others)
            hits_full += 1
            cur_pt = choose_next_anchor(pts, pt2idx, guidance, tree; current=P0)

        elseif lp_count == 1
            lp = lp_pt

            lp_row = Dict{Int,Int}()
            sparse_add!(lp_row, sum_row_others; sign = -1)
            lp_a = mod(neg_al - sum_a_others, ell)
            lp_b = mod(neg_be - sum_b_others, ell)

            if haskey(tree.vertices, lp)
                v = tree.vertices[lp]
                row = copy(sum_row_others)
                sparse_add!(row, v.row)
                push!(alpha_vec, mod(neg_al - sum_a_others - v.alpha, ell))
                push!(beta_vec,  mod(neg_be - sum_b_others - v.beta, ell))
                push!(rel_rows, row)
                update_guidance!(guidance, row)
                hits_tree += 1
                cur_pt = lp
                continue
            end

            if length(tree.vertices) < tree.max_vertices
                others = NTuple{2,Int}[]
                for pt in pts
                    pt == lp && continue
                    push!(others, pt)
                end
                parent = choose_tree_parent(others, pt2idx, tree, guidance)

                added = tree_add_vertex!(tree, lp, parent, lp_row, lp_a, lp_b)
                if added
                    hits_tree += 1
                    cur_pt = lp
                end

                if length(tree.vertices) >= tree.max_vertices && tree.stage_limit < tree.max_vertices
                    verbose && @printf("  tree expanding... vertices=%d\n", length(tree.vertices))
                end
            else
                hits_lp += 1
                if haskey(lp_table, lp)
                    (al2, be2, row2) = lp_table[lp]
                    combined = copy(row2)
                    sparse_add!(combined, lp_row, sign = -1)
                    filter!(kv -> kv[2] != 0, combined)
                    if !isempty(combined)
                        push!(alpha_vec, mod(lp_a - al2, ell))
                        push!(beta_vec,  mod(lp_b - be2, ell))
                        push!(rel_rows, combined)
                        update_guidance!(guidance, combined)
                        hits_lp2 += 1
                    end
                    delete!(lp_table, lp)
                else
                    lp_table[lp] = (lp_a, lp_b, lp_row)
                end
                cur_pt = choose_next_anchor(pts, pt2idx, guidance, tree; current=P0)
            end

        else
            continue
        end
    end

    nF   = length(fb)
    nrel = length(alpha_vec)

    verbose && @printf(
        "Walk done: %d valid steps / %d total  (%.1fs)\n",
        hits_total, walk_steps, time()-t0)
    verbose && @printf(
        "FB: %d atoms | tree verts: %d | full rels: %d | tree rows: %d | LP partials seen: %d | LP pairs: %d\n",
        nF, length(tree.vertices), hits_full, hits_tree, hits_lp, hits_lp2)
    verbose && @printf("Total relations: %d  (need >= %d)\n", nrel, nF + 1)

    # ------------------------------------------------------------------
    # Dense relation matrix
    # ------------------------------------------------------------------
    Rmat = zeros(Int, nrel, nF)
    for i in 1:nrel, (j, v) in rel_rows[i]
        1 <= j <= nF || continue
        Rmat[i, j] = mod(Rmat[i, j] + v, ell)
    end

    analyze_matrix && analyze_relation_matrix(rel_rows, nF; verbose=verbose)
    analyze_matrix && spectral_gap_report(rel_rows, nF; verbose=verbose)

    if nrel < nF + 1
        msg = "Too few relations ($nrel) for FB size $nF. Increase walk_steps or decrease fb_size."
        verbose && println("  shortfall: ", msg, solve ? "  (retrying)" : "  (diagnostics only; skipping solve)")
        return nothing
    end

    if verbose && !isempty(tree.vertices)
        depths = [v.depth for v in values(tree.vertices)]
        @printf("Tree summary: stage=%d, next_limit=%d, max_depth=%d, avg_depth=%.2f\n",
                tree.stage, tree.stage_limit, maximum(depths), sum(depths)/length(depths))
    end

    !solve && return nothing

    # ------------------------------------------------------------------
    # Structured Gaussian Elimination (SGE): leaf-stripping
    #
    # We iteratively remove degree-1 columns (FB elements that appear in
    # only one relation). Each such column j with unique row i lets us
    # express FB element j in terms of the other elements in row i, then
    # substitute and delete both.  This reduces the system before the
    # expensive O(N^3) dense solve.
    #
    # We track a substitution stack so we can reconstruct the full gamma
    # vector after solving the reduced system.
    # ------------------------------------------------------------------
    verbose && println("SGE (leaf-stripping) on $(nrel)x$(nF) matrix...")

    # Work on copies; row_active[i]=true means row i is still in system.
    # We store the reduced system as explicit dense rows after stripping.
    row_alpha  = copy(alpha_vec)          # length nrel
    row_beta   = copy(beta_vec)
    Rwork      = [copy(Rmat[i, :]) for i in 1:nrel]   # Vector of row vectors
    row_active = trues(nrel)
    col_active = trues(nF)

    # col_degree[j] = number of active rows in which col j is nonzero
    col_degree = zeros(Int, nF)
    col_to_rows = [Int[] for _ in 1:nF]
    for i in 1:nrel, j in 1:nF
        Rwork[i][j] == 0 && continue
        col_degree[j] += 1
        push!(col_to_rows[j], i)
    end

    # substitution_stack: each entry is (elim_row_idx, elim_col_idx)
    # meaning: row elim_row_idx was used to eliminate col elim_col_idx.
    # We replay this in reverse to lift gamma from the reduced system.
    # subst_stack records eliminated (row, col) pairs for future back-substitution
    # if we ever need the full gamma vector. For now we solve in the reduced system.
    subst_stack = Tuple{Int,Int}[]

    peeled = 0
    changed = true
    while changed
        changed = false
        for j in 1:nF
            col_active[j] || continue
            col_degree[j] == 1 || continue

            # Find the unique active row containing j
            pivot_row = 0
            for ri in col_to_rows[j]
                row_active[ri] || continue
                Rwork[ri][j] == 0 && continue
                pivot_row = ri
                break
            end
            pivot_row == 0 && continue

            # Scale pivot row so coefficient of j is 1
            piv_val = Rwork[pivot_row][j]
            inv_piv = powermod(piv_val, ell - 2, ell)
            for jj in 1:nF
                Rwork[pivot_row][jj] = mod(Rwork[pivot_row][jj] * inv_piv, ell)
            end
            row_alpha[pivot_row] = mod(row_alpha[pivot_row] * inv_piv, ell)
            row_beta[pivot_row]  = mod(row_beta[pivot_row]  * inv_piv, ell)

            # Eliminate j from all other active rows; update col_degree incrementally
            for ri in col_to_rows[j]
                ri == pivot_row && continue
                row_active[ri] || continue
                Rwork[ri][j] == 0 && continue
                f = Rwork[ri][j]
                for jj in 1:nF
                    old_nz = Rwork[ri][jj] != 0
                    Rwork[ri][jj] = mod(Rwork[ri][jj] - f * Rwork[pivot_row][jj], ell)
                    new_nz = Rwork[ri][jj] != 0
                    if old_nz && !new_nz && col_active[jj]
                        col_degree[jj] -= 1
                    elseif !old_nz && new_nz && col_active[jj]
                        col_degree[jj] += 1
                        push!(col_to_rows[jj], ri)
                    end
                end
                row_alpha[ri] = mod(row_alpha[ri] - f * row_alpha[pivot_row], ell)
                row_beta[ri]  = mod(row_beta[ri]  - f * row_beta[pivot_row],  ell)
            end

            # Deactivate pivot row and column j; decrement degrees for pivot row's nonzeros
            for jj in 1:nF
                jj == j && continue
                col_active[jj] || continue
                Rwork[pivot_row][jj] == 0 && continue
                col_degree[jj] -= 1
            end

            push!(subst_stack, (pivot_row, j))
            row_active[pivot_row] = false
            col_active[j]         = false
            col_degree[j]         = 0
            peeled += 1
            changed = true
            break  # restart outer loop after one peel
        end
    end

    active_rows = findall(row_active)
    active_cols = findall(col_active)
    nr2 = length(active_rows)
    nc2 = length(active_cols)
    verbose && @printf("SGE peeled %d columns; reduced to %dx%d (was %dx%d)\n",
                       peeled, nr2, nc2, nrel, nF)

    if nr2 < nc2 + 1
        verbose && println("  SGE left insufficient relations; will retry.")
        return nothing
    end

    # Build reduced dense matrix
    Rred = zeros(Int, nr2, nc2)
    for (ii, ri) in enumerate(active_rows), (jj, j) in enumerate(active_cols)
        Rred[ii, jj] = Rwork[ri][j]
    end
    alpha_red = [row_alpha[ri] for ri in active_rows]
    beta_red  = [row_beta[ri]  for ri in active_rows]

    # ------------------------------------------------------------------
    # Solve: try every null vector in the left kernel of the reduced
    # matrix, testing each for nonzero beta sum. This avoids the need
    # to retry the entire walk when only the kernel pick is unlucky.
    # ------------------------------------------------------------------
    verbose && println("Left-kernel search over GF($ell) on reduced $(nr2)x$(nc2) matrix...")

    k_found = nothing
    null_vecs = left_kernel_all(Rred)
    verbose && @printf("  Found %d null vector(s) to try\n", length(null_vecs))

    for gamma in null_vecs
        Sa = mod(sum(Int128(gamma[i]) * alpha_red[i] for i in 1:nr2), ell)
        Sb = mod(sum(Int128(gamma[i]) * beta_red[i]  for i in 1:nr2), ell)
        Sb == 0 && continue

        k_cand = mod(-Int(Sa) * powermod(Int(Sb), ell - 2, ell), ell)
        if jac_mul(G, k_cand) == T
            k_found = k_cand
            break
        end
    end

    if k_found !== nothing
        verbose && println("  ✓  k = $k_found   (k*G == T)")
    else
        verbose && println("  No usable kernel vector found; will retry with fresh walk.")
    end
    k_found
end





function main2()
    println("="^62)
    println("  trial2: Markov-walk phi-relation index calculus")
    println("  y^2 = x^5+3x^3+2x^2+5x+4  /F_$p,  ell=$ell")
    println("="^62, "\n")

    pts = curve_points()

    println("Finding G of order ell...")
    G = find_ell_generator(pts)
    @printf("G.u = %s\nG.v = %s\n", G.u, G.v)
    @assert jac_isid(jac_mul_raw(G, ell))  "G does not have order ell"
    println("Confirmed: ell*G = identity\n")

    k_true = rand(2:ell-1)
    T      = jac_mul(G, k_true)
    @printf("Secret k = %d\n\n", k_true)

    # Optional quick sweep: keep the walk cheap, but inspect how the matrix
    # and its spectral gap behave as the factor base size changes.
    sweep_fb_sizes = [450, 550, 650]
    for fb in sweep_fb_sizes
        println("--- diagnostic sweep for fb_size=$fb ---")
        _ = index_calculus_walk(G, T; fb_size=fb, walk_steps=200_000,
                                verbose=true, analyze_matrix=true, solve=false, guided=true)
        println()
    end

    # Main run
    k_rec = nothing
    max_restarts = 5
    for attempt in 1:max_restarts
        if attempt > 1
            println("Retrying the full walk with fresh randomness... (attempt $attempt/$max_restarts)")
        end
        k_rec = index_calculus_walk(G, T; fb_size=650, walk_steps=500_000,
                                    verbose=true, analyze_matrix=true, solve=true, guided=true)
        k_rec !== nothing && break
    end

    println()
    if k_rec !== nothing
        @printf("Recovered k = %-8d  true k = %-8d  match = %s\n",
                k_rec, k_true, k_rec == k_true)
    else
        println("DLP not recovered.")
    end
end

main2()
