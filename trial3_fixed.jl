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

#include("trial1.jl")   # all Fp/poly/Jacobian/curve utilities
include("trial1_autoell_p10.jl")   # all Fp/poly/Jacobian/curve utilities
using LinearAlgebra
using Base.Threads
using Nemo
using Dates

include("lp_residual_stats.jl")   # LP residual diagnostics (occupancy, entropy, autocorr, clustering)

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

    # Vanishing conditions give the 3×4 augmented system.
    # We unroll Gaussian elimination entirely into scalars to avoid
    # allocating any matrix, vector, or slice.
    #
    # Rows:  [x²  x  1  y | rhs]
    #   r0:  [px² px 1 py | rhs0]
    #   r1:  [x1² x1 1 y1 | rhs1]
    #   r2:  [x2² x2 1 y2 | rhs2]

    # ── Try d=1: solve for (a,b,c) from the 3×3 left block ──────────────────
    # augmented columns: A = [x² x 1], rhs = -y
    @inline function solve3x3(a00,a01,a02, a10,a11,a12, a20,a21,a22,
                               r0, r1, r2)::Union{NTuple{3,Int},Nothing}
        # Column 0 pivot
        if a00 != 0
            inv0 = fpinv(a00)
            # eliminate row1 col0
            f10 = fp(a10 * inv0)
            a10 = 0; a11 = fp(a11 - f10*a01); a12 = fp(a12 - f10*a02); r1 = fp(r1 - f10*r0)
            # eliminate row2 col0
            f20 = fp(a20 * inv0)
            a20 = 0; a21 = fp(a21 - f20*a01); a22 = fp(a22 - f20*a02); r2 = fp(r2 - f20*r0)
            # back-eliminate into row0 later; focus on col1 next
            if a11 != 0
                inv1 = fpinv(a11)
                f21 = fp(a21 * inv1)
                a21 = 0; a22 = fp(a22 - f21*a12); r2 = fp(r2 - f21*r1)
                a22 == 0 && return nothing
                inv2 = fpinv(a22)
                # back-sub col2
                x2v = fp(r2 * inv2)
                x1v = fp((r1 - a12*x2v) * inv1)
                x0v = fp((r0 - a01*x1v - a02*x2v) * inv0)
                return (x0v, x1v, x2v)
            elseif a21 != 0
                # swap rows 1 and 2
                a11,a21 = a21,a11; a12,a22 = a22,a12; r1,r2 = r2,r1
                inv1 = fpinv(a11)
                f21 = fp(a21 * inv1)  # a21 is now 0, but we already swapped
                a22 = fp(a22 - f21*a12); r2 = fp(r2 - f21*r1)
                a22 == 0 && return nothing
                inv2 = fpinv(a22)
                x2v = fp(r2 * inv2)
                x1v = fp((r1 - a12*x2v) * inv1)
                x0v = fp((r0 - a01*x1v - a02*x2v) * inv0)
                return (x0v, x1v, x2v)
            else
                return nothing  # col1 all-zero after col0 elimination
            end
        elseif a10 != 0
            # swap rows 0 and 1 then redo
            return solve3x3(a10,a11,a12, a00,a01,a02, a20,a21,a22, r1,r0,r2)
        elseif a20 != 0
            return solve3x3(a20,a21,a22, a10,a11,a12, a00,a01,a02, r2,r1,r0)
        else
            return nothing  # col0 all-zero
        end
    end

    px2 = fp(px*px); x12 = fp(x1*x1); x22 = fp(x2*x2)

    # Try d=1: solve [x² x 1]*[a,b,c]' = -y
    sol = solve3x3(px2,px,1, x12,x1,1, x22,x2,1,
                   fp(-py), fp(-y1), fp(-y2))
    if sol !== nothing
        a,b,c = sol
        return (fp(a), fp(b), fp(c), 1)
    end

    # Fallback a=1: solve [x 1 y]*[b,c,d]' = -x²
    sol = solve3x3(px,1,py, x1,1,y1, x2,1,y2,
                   fp(-px2), fp(-x12), fp(-x22))
    sol === nothing && return nothing
    b2,c2,d2 = sol
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
                              px::Int, x1::Int, x2::Int)::NTuple{2, Union{NTuple{2,Int},Nothing}}
    # Returns exactly two slots; caller checks for nothing entries.
    _nothing2 = (nothing, nothing)
    d == 0 && return _nothing2

    # N(x) = (a*x²+b*x+c)² - d²*f(x)  — degree 5, fixed 6-element buffer.
    # Compute coefficients of (a*x²+b*x+c)² directly:
    #   coeff of x^k in apoly² where apoly = [c,b,a]
    d2 = fp(d * d)
    # apoly² coefficients (degree 0..4):
    N0 = fp(c*c)
    N1 = fp(2*b*c)
    N2 = fp(b*b + 2*a*c)
    N3 = fp(2*a*b)
    N4 = fp(a*a)
    # subtract d²*f(x); F_POLY = [f0,f1,f2,f3,0,1] (len 6, degree 5)
    N = (fp(N0 - d2*F_POLY[1]),
         fp(N1 - d2*F_POLY[2]),
         fp(N2 - d2*F_POLY[3]),
         fp(N3 - d2*F_POLY[4]),
         fp(N4 - d2*F_POLY[5]),
         fp(   - d2*F_POLY[6]))   # = -d² (leading)

    # Synthetic division of a degree-5 poly (6 coeffs, ascending) by (x - r).
    # Returns the degree-4 quotient as a 5-tuple, or nothing if remainder != 0.
    @inline function syndiv5(n0,n1,n2,n3,n4,n5, r::Int)
        # Descending Horner for poly div by (x-r): process from high to low.
        q4 = n5
        q3 = fp(n4 + q4*r)
        q2 = fp(n3 + q3*r)
        q1 = fp(n2 + q2*r)
        q0 = fp(n1 + q1*r)
        rem = fp(n0 + q0*r)
        rem != 0 && return nothing
        (q0, q1, q2, q3, q4)
    end

    @inline function syndiv4(n0,n1,n2,n3,n4, r::Int)
        q3 = n4
        q2 = fp(n3 + q3*r)
        q1 = fp(n2 + q2*r)
        q0 = fp(n1 + q1*r)
        rem = fp(n0 + q0*r)
        rem != 0 && return nothing
        (q0, q1, q2, q3)
    end

    @inline function syndiv3(n0,n1,n2,n3, r::Int)
        q2 = n3
        q1 = fp(n2 + q2*r)
        q0 = fp(n1 + q1*r)
        rem = fp(n0 + q0*r)
        rem != 0 && return nothing
        (q0, q1, q2)
    end

    q5 = syndiv5(N[1],N[2],N[3],N[4],N[5],N[6], px)
    q5 === nothing && return _nothing2
    q4 = syndiv4(q5[1],q5[2],q5[3],q5[4],q5[5], x1)
    q4 === nothing && return _nothing2
    q3 = syndiv3(q4[1],q4[2],q4[3],q4[4], x2)
    q3 === nothing && return _nothing2

    # q3 is the degree-2 residual (q3[1], q3[2], q3[3]) = [r0, r1, r2] ascending.
    r0, r1, r2 = q3

    # Given x-coordinate, find correct y using phi(x,y) = 0.
    @inline function y_for_x(xr::Int)::Union{NTuple{2,Int},Nothing}
        yr = sqrt_fp(eval_f(xr));  yr === nothing && return nothing
        base = fp(a * fp(xr * xr) + b * xr + c)
        fp(base + d * yr) == 0 && return (xr, yr)
        fp(base - d * yr) == 0 && return (xr, fp(-yr))
        return nothing
    end

    dq = (r2 != 0) ? 2 : (r1 != 0 ? 1 : 0)

    if dq == 1
        # linear: r1*x + r0 = 0  =>  x = -r0 / r1
        xr = fp(-r0 * fpinv(r1))
        return (y_for_x(xr), nothing)
    elseif dq == 2
        # quadratic: r2*x² + r1*x + r0 = 0
        # normalise to monic then use u2_roots
        inv_r2 = fpinv(r2)
        u_monic = Int[fp(r0*inv_r2), fp(r1*inv_r2), 1]
        rs = u2_roots(u_monic)
        rs === nothing && return _nothing2
        return (y_for_x(rs[1]), y_for_x(rs[2]))
    else
        return _nothing2
    end
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
        @printf("  rows = %d, cols = %d, nonzeros = %d, avg row weight = %.3f, density = %.4g\n",
                nrel, nF, total_nz, avg_w, density)

        row_keys = sort(collect(keys(row_hist)))
        row_descs = String[]
        for k in row_keys
            push!(row_descs, string(k, ":", row_hist[k]))
        end
        println("  row-weight histogram: ", join(row_descs, ", "))

        @printf("  column degrees: zero=%d, deg1=%d, deg2=%d, min=%d, median=%d, max=%d\n",
                zero_cols, deg1_cols, deg2_cols,
                isempty(deg_sorted) ? 0 : deg_sorted[1],
                isempty(deg_sorted) ? 0 : deg_sorted[(length(deg_sorted)+1) ÷ 2],
                isempty(deg_sorted) ? 0 : deg_sorted[end])

        @printf("  component graph: %d components, largest=%d, singletons=%d\n",
                ncomp, largest_comp, singleton_comps)

        @printf("  peel/core estimate: core cols = %d, core rows = %d, peeled cols = %d\n",
                core_cols, core_rows, nF - core_cols)

        if largest_comp < nF
            @printf("  note: matrix is block-disconnected enough to split off subproblems\n")
        end
        if core_cols < nF
            @printf("  note: leaf-stripping removes %d/%d columns before any dense solve\n",
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
#  Asymptotic diagnostics
#
#  This report is aimed at scaling questions rather than one-off correctness:
#    - how many nonzeros accumulate as the relation count grows,
#    - how quickly leaf-stripping shrinks the core,
#    - and whether the spectral gap settles into a stable regime.
#
#  The prefixes are chosen on a roughly geometric grid so you can compare
#  early, mid, and late behavior without drowning in per-row noise.
# ---------------------------------------------------------------------------
function asymptotic_report(rel_rows::Vector{Dict{Int,Int}}, nF::Int;
                           prefixes::Vector{Int}=Int[],
                           hits_total::Int=0,
                           walk_steps::Int=0,
                           hits_full::Int=0,
                           hits_tree::Int=0,
                           hits_lp::Int=0,
                           hits_lp2::Int=0,
                           verbose::Bool=true)
    nrel = length(rel_rows)
    nrel == 0 && return nothing

    prefixes = isempty(prefixes) ? unique(sort(Int[
        min(nrel, max(50, nrel ÷ 16)),
        min(nrel, max(100, nrel ÷ 8)),
        min(nrel, max(200, nrel ÷ 4)),
        min(nrel, max(400, nrel ÷ 2)),
        nrel
    ])) : unique(sort(filter(x -> 1 <= x <= nrel, prefixes)))

    # Build supports once; the prefix statistics reuse them.
    supports = Vector{Vector{Int}}(undef, nrel)
    for i in 1:nrel
        cols = Int[]
        for (j, v) in rel_rows[i]
            v == 0 && continue
            1 <= j <= nF || continue
            push!(cols, j)
        end
        sort!(cols)
        supports[i] = cols
    end

    function prefix_core_stats(m::Int)
        coldeg = zeros(Int, nF)
        col_to_rows = [Int[] for _ in 1:nF]
        total_nz = 0
        row_hist = Dict{Int,Int}()

        for i in 1:m
            cols = supports[i]
            w = length(cols)
            row_hist[w] = get(row_hist, w, 0) + 1
            total_nz += w
            for j in cols
                coldeg[j] += 1
                push!(col_to_rows[j], i)
            end
        end

        active_col = trues(nF)
        active_row = trues(m)
        deg = copy(coldeg)
        q = Int[]

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
        avg_w = total_nz / m
        density = total_nz / (m * nF)
        zero_cols = count(==(0), coldeg)
        deg1_cols = count(==(1), coldeg)
        deg2_cols = count(==(2), coldeg)
        return (
            m = m,
            total_nz = total_nz,
            avg_w = avg_w,
            density = density,
            row_hist = row_hist,
            zero_cols = zero_cols,
            deg1_cols = deg1_cols,
            deg2_cols = deg2_cols,
            core_cols = core_cols,
            core_rows = core_rows,
            peeled_cols = nF - core_cols,
            core_frac = core_cols / nF,
            peel_frac = (nF - core_cols) / nF,
        )
    end

    prefix_stats = map(prefix_core_stats, prefixes)
    gap_stats = spectral_gap_report(rel_rows, nF; prefixes=prefixes, verbose=false)
    gap_by_m = Dict(s.m => s for s in gap_stats)

    function loglog_slope(xs::Vector{Float64}, ys::Vector{Float64})
        pts = [(x, y) for (x, y) in zip(xs, ys) if x > 0 && y > 0 && isfinite(x) && isfinite(y)]
        length(pts) < 2 && return NaN
        lx = [log(p[1]) for p in pts]
        ly = [log(p[2]) for p in pts]
        mx = sum(lx) / length(lx)
        my = sum(ly) / length(ly)
        num = sum((lx[i] - mx) * (ly[i] - my) for i in eachindex(lx))
        den = sum((lx[i] - mx)^2 for i in eachindex(lx))
        den == 0 && return NaN
        return num / den
    end

    if verbose
        println("Asymptotic diagnostics (prefix growth across the matrix):")
        @printf("  walk yield: %d valid steps / %d total = %.4f\n",
                hits_total, walk_steps, walk_steps == 0 ? 0.0 : hits_total / walk_steps)
        if hits_total > 0
            @printf("  relation mix: full=%d, tree=%d, LP-partials=%d, LP-pairs=%d\n",
                    hits_full, hits_tree, hits_lp, hits_lp2)
            @printf("  normalized relation rates: full/valid=%.4f, tree/valid=%.4f, LP-pairs/valid=%.4f\n",
                    hits_full / hits_total, hits_tree / hits_total, hits_lp2 / hits_total)
        end

        for s in prefix_stats
            g = get(gap_by_m, s.m, nothing)
            if g === nothing || isnan(g.gap)
                @printf("  rows=%d: nz=%d, avg_w=%.2f, core=%d/%d (%.3f), peel=%d, gap=n/a\n",
                        s.m, s.total_nz, s.avg_w, s.core_cols, nF, s.core_frac, s.peeled_cols)
            else
                @printf("  rows=%d: nz=%d, avg_w=%.2f, core=%d/%d (%.3f), peel=%d, gap=%.6f\n",
                        s.m, s.total_nz, s.avg_w, s.core_cols, nF, s.core_frac, s.peeled_cols, g.gap)
            end
        end

        ms  = Float64[s.m for s in prefix_stats]
        nzs = Float64[s.total_nz for s in prefix_stats]
        ccs = Float64[s.core_cols for s in prefix_stats]
        crs = Float64[s.core_rows for s in prefix_stats]
        ps  = Float64[s.peel_frac for s in prefix_stats]
        avs = Float64[s.avg_w for s in prefix_stats]

        @printf("  log-log fit total_nz ~ rows^a: a=%.4f\n", loglog_slope(ms, nzs))
        @printf("  log-log fit avg row weight ~ rows^a: a=%.4f\n", loglog_slope(ms, avs))
        @printf("  log-log fit core cols ~ rows^a: a=%.4f\n", loglog_slope(ms, ccs))
        @printf("  log-log fit core rows ~ rows^a: a=%.4f\n", loglog_slope(ms, crs))
        @printf("  log-log fit peel fraction ~ rows^a: a=%.4f\n", loglog_slope(ms, ps))
    end

    return (prefix_stats = prefix_stats, gap_stats = gap_stats)
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

#  left_kernel_all: return ALL left null vectors of R over GF(ell).
#
#  Takes rel_rows sparse format directly to avoid materializing a dense matrix.
#  Uses Nemo.jl (FLINT backend) for the dense finite-field kernel computation.
#  Falls back to pure-Julia elimination if Nemo is unavailable.
# ---------------------------------------------------------------------------
function left_kernel_all(rel_rows::Vector{Dict{Int,Int}}, nF::Int, ell::Int)::Vector{Vector{Int}}
    m = length(rel_rows)
    n = nF

    # ── Nemo / FLINT fast path ──────────────────────────────────────────────
    # Build the matrix TRANSPOSED (n×m) so nullspace() gives left kernel directly
    # without materializing a second dense matrix via transpose().
    # Use raw Int entries in a flat Vector{Int} — Nemo.matrix(F, nrows, ncols, vec)
    # accepts Int directly and converts inside FLINT, avoiding m*n boxed GF objects.
    try
        F = Nemo.GF(ell)
        # entries[j + (i-1)*n] = R[i,j] stored as plain Int (column-major for transposed matrix)
        # We want the TRANSPOSED matrix: rows=n, cols=m, entry[j,i] = R[i,j]
        # Flat vector in row-major order for the transposed matrix: row j, col i → R[i,j]
        entries = zeros(Int, n * m)
        for i in 1:m
            for (j, v) in rel_rows[i]
                1 <= j <= n || continue
                # transposed matrix: row j, col i, row-major index = (j-1)*m + i
                entries[(j-1)*m + i] = mod(v, ell)
            end
        end
        # Build n×m matrix (the transpose of the original m×n relation matrix)
        Rnemo_t = Nemo.matrix(F, n, m, entries)
        entries = nothing   # allow GC before nullspace
        GC.gc()
        nu, K = nullspace(Rnemo_t)
        Rnemo_t = nothing
        GC.gc()
        result = Vector{Int}[]
        for col in 1:nu
            γ = [Int(lift(ZZ, K[row, col])) for row in 1:m]
            any(!=(0), γ) && push!(result, γ)
        end
        return result
    catch e
        @warn "Nemo nullspace failed ($e); falling back to pure-Julia elimination."
    end

    # ── Pure-Julia fallback ─────────────────────────────────────────────────
    # Build dense matrix only in fallback path (small matrices only).
    R = zeros(Int, m, n)
    for i in 1:m, (j, v) in rel_rows[i]
        1 <= j <= n || continue
        R[i, j] = mod(R[i, j] + v, ell)
    end

    aug  = hcat(Matrix{Int}(I, m, m), R)
    prow = 1
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


# ---------------------------------------------------------------------------
#  phase2_worker: one independent phase-2 walk thread.
#
#  Takes the frozen factor base and precomputed step table (read-only, safe to
#  share across threads).  Runs until the shared atomic counter `rel_counter`
#  reaches `rel_target`, then returns its collected relations and counters.
#  Each thread has its own lp_table, so no synchronisation is needed during
#  the walk — only the atomic increment on emit.
# ---------------------------------------------------------------------------

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
end

function LP2Graph()
    LP2Graph(
        Dict{NTuple{2,Int}, LP2Node}(),
        0, 0, 0, 0, 0
    )
end

# Walk the spanning tree from `pt` to find its root (node with parent===nothing).
# Returns the root key, or nothing if pt is not in the tree.
function lp2_tree_root(g::LP2Graph, pt::NTuple{2,Int})
    cur = pt
    while true
        node = get(g.nodes, cur, nothing)
        node === nothing && return nothing   # pt not in tree at all
        node.parent === nothing && return cur
        cur = node.parent
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
            g.n_depth_pruned += 1
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
        return (row=combined, alpha=combined_alpha, beta=combined_beta)

    else
        # Tree-merge: attach whichever endpoint is not yet in a tree (or is shallower)
        node_L = get(g.nodes, L, nothing)
        node_R = get(g.nodes, R, nothing)
        depth_L = node_L === nothing ? 0 : node_L.depth
        depth_R = node_R === nothing ? 0 : node_R.depth

        attach_child  = nothing
        attach_parent = nothing
        new_depth     = 0

        if node_L === nothing && node_R !== nothing
            attach_child  = L
            attach_parent = R
            new_depth     = depth_R + 1
        elseif node_R === nothing && node_L !== nothing
            attach_child  = R
            attach_parent = L
            new_depth     = depth_L + 1
        elseif node_L === nothing && node_R === nothing
            # Neither in tree yet: make R a root, attach L as child
            g.nodes[R] = LP2Node(nothing, 0, Dict{Int,Int}(), 0, 0)
            attach_child  = L
            attach_parent = R
            new_depth     = 1
        else
            # Both in separate trees: attach the shallower-rooted one
            if depth_L <= depth_R
                attach_child  = L
                attach_parent = R
                new_depth     = depth_R + 1
            else
                attach_child  = R
                attach_parent = L
                new_depth     = depth_L + 1
            end
        end

        if new_depth > MAX_LP2_DEPTH
            g.n_depth_pruned += 1
            return nothing
        end

        g.nodes[attach_child] = LP2Node(attach_parent, new_depth,
                                        copy(fb_row), alpha, beta)
        return nothing
    end
end



function phase2_worker(G::Div2, T::Div2,
                       fb::Vector{NTuple{2,Int}},
                       pt2idx::Dict{NTuple{2,Int},Int},
                       step_D::Vector{Div2},
                       step_a::Vector{Int},
                       step_b::Vector{Int},
                       rel_counter::Threads.Atomic{Int},
                       rel_target::Int,
                       shared_lp1::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}},
                       shared_lp1_lock::ReentrantLock,
                       shared_lp2::LP2Graph,
                       shared_lp2_lock::ReentrantLock,
                       # per-thread LP residual collector (write-only from this thread)
                       lp_col::LPResidualCollector;
                       verbose::Bool = true)

    nF_cur   = length(fb)
    N_STEPS  = length(step_D)
    tid      = Threads.threadid()
    t_worker_start = time()

    # Per-thread mutable state
    cur_pt    = fb[rand(1:nF_cur)]
    alpha_cur = rand(1:ell-1)
    beta_cur  = rand(0:ell-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur), jac_mul(T, beta_cur))

    alpha_vec = Int[]
    beta_vec  = Int[]
    rel_rows  = Vector{Dict{Int,Int}}()
    
    hint = max(64, cld(rel_target, Threads.nthreads()) + 32)
    sizehint!(alpha_vec, hint)
    sizehint!(beta_vec,  hint)
    sizehint!(rel_rows,  hint)

    hits_total    = 0
    hits_full     = 0
    hits_0lp      = 0
    hits_lp1      = 0
    hits_1lp_emit = 0
    hits_lp2seen  = 0
    hits_lp2emit  = 0
    hits_skip     = 0
    raw_steps     = 0

    smooth_hist  = zeros(Int, 4) 

    t_last_report = time()
    report_interval_secs = 30.0

    fb_row_scratch = Dict{Int,Int}()
    sizehint!(fb_row_scratch, 4)

    sample_rels = Vector{Tuple{Div2,Dict{Int,Int},Int,Int,NTuple{2,Int},NTuple{2,Int},NTuple{2,Int}}}()
    rank_growth = Tuple{Int,Int}[]

    while rel_counter[] < rel_target
        raw_steps += 1
        si        = rand(1:N_STEPS)
        D_cur     = jac_add(D_cur, step_D[si])
        alpha_cur = mod(alpha_cur + step_a[si], ell)
        beta_cur  = mod(beta_cur  + step_b[si], ell)

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
        (res[1] === nothing || res[2] === nothing) && continue
        R = res[1]::NTuple{2,Int}
        S = res[2]::NTuple{2,Int}

        eval_f(R[1]) == fp(R[2] * R[2]) || continue
        eval_f(S[1]) == fp(S[2] * S[2]) || continue

        hits_total += 1

        now_t = time()
        if verbose && (now_t - t_last_report) >= report_interval_secs
            elapsed = now_t - t_worker_start
            rel_local = length(rel_rows)
            @printf("[thread %2d | t=%6.1fs] raw=%d valid=%d 0lp=%d 1lp_emit=%d 1lp_step=%d 2lp_seen=%d 2lp_emit=%d skip=%d  rels_local=%d  global=%d/%d\n",
                    tid, elapsed, raw_steps, hits_total, hits_0lp, hits_1lp_emit,
                    hits_lp1, hits_lp2seen, hits_lp2emit, hits_skip,
                    rel_local, rel_counter[], rel_target)
            @printf("           rates: phi_val=%.3f%%  full=%.3f%%  1lp=%.3f%%  2lp_seen=%.3f%%  2lp_emit=%.3f%%  skip=%.3f%%\n",
                    100.0 * hits_total / raw_steps,
                    100.0 * hits_full  / max(1, hits_total),
                    100.0 * hits_lp1   / max(1, hits_total),
                    100.0 * hits_lp2seen / max(1, hits_total),
                    100.0 * hits_lp2emit / max(1, hits_total),
                    100.0 * hits_skip  / max(1, hits_total))
            @printf("           smoothness histogram (0-LP, 1-LP, 2-LP, 3-LP): %d %d %d %d\n",
                    smooth_hist[1], smooth_hist[2], smooth_hist[3], smooth_hist[4])
            flush(stdout)
            t_last_report = now_t
        end

        al     = alpha_cur
        be     = beta_cur
        P0     = cur_pt
        neg_al = mod(ell - al, ell)
        neg_be = mod(ell - be, ell)

        i0 = get(pt2idx, P0, 0)
        iR = get(pt2idx, R,  0)
        iS = get(pt2idx, S,  0)
        n_lp = (i0 == 0 ? 1 : 0) + (iR == 0 ? 1 : 0) + (iS == 0 ? 1 : 0)
        smooth_hist[n_lp + 1] += 1

        if n_lp == 0
            empty!(fb_row_scratch)
            for idx in (i0, iR, iS)
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end
            fb_row = copy(fb_row_scratch)
            push!(alpha_vec, neg_al)
            push!(beta_vec,  neg_be)
            push!(rel_rows,  fb_row)
            push!(rank_growth, (raw_steps, length(rel_rows)))
            if length(sample_rels) < 10
                push!(sample_rels, (D_cur, copy(fb_row), neg_al, neg_be, P0, R, S))
            end
            hits_full += 1
            hits_0lp += 1
            Threads.atomic_add!(rel_counter, 1)
            cur_pt = fb[rand(1:nF_cur)]

        elseif n_lp == 1
            hits_lp1 += 1
            lp_pt = iR == 0 ? R : S
            empty!(fb_row_scratch)
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end

            # ── LP residual recording ────────────────────────────────────
            record_lp1!(lp_col, lp_pt, al, be, raw_steps)
            # ─────────────────────────────────────────────────────────────

            closed = false
            lock(shared_lp1_lock)
            try
                if haskey(shared_lp1, lp_pt)
                    prev_row, prev_al, prev_be, prev_step = shared_lp1[lp_pt]
                    combined    = copy(fb_row_scratch)
                    lp2_subtract_rows(combined, prev_row)
                    combined_al = mod(neg_al - prev_al, ell)
                    combined_be = mod(neg_be - prev_be, ell)
                    delete!(shared_lp1, lp_pt)
                    closed = true
                    # ── record closure gap ───────────────────────────────
                    record_closure!(lp_col, raw_steps, prev_step)
                    
                    if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                        push!(alpha_vec, combined_al)
                        push!(beta_vec,  combined_be)
                        push!(rel_rows,  combined)
                        push!(rank_growth, (raw_steps, length(rel_rows)))
                        hits_full += 1
                        hits_1lp_emit += 1
                        Threads.atomic_add!(rel_counter, 1)
                    end
                else
                    shared_lp1[lp_pt] = (copy(fb_row_scratch), neg_al, neg_be, raw_steps)
                end
            finally
                unlock(shared_lp1_lock)
            end

            if closed
                cur_pt = fb[rand(1:nF_cur)]
            elseif iR != 0
                cur_pt = R
            elseif iS != 0
                cur_pt = S
            else
                cur_pt = P0
            end

        elseif n_lp == 2
            hits_lp2seen += 1

            # Identify the two LP points.  Exactly two of {P0,R,S} are off-FB.
            lp2_a = i0 == 0 ? P0 : (iR == 0 ? R : S)
            lp2_b = if i0 == 0 && iR == 0
                        R
                    elseif i0 == 0 && iS == 0
                        S
                    else
                        S   # iR==0, iS==0
                    end

            # ── LP residual recording ────────────────────────────────────
            record_lp2!(lp_col, lp2_a, lp2_b, raw_steps)

            # Build the FB-only part of this 2-LP edge.
            # Relation: atom(lp2_a) + atom(lp2_b) + fb_part = -neg_al*G - neg_be*T
            # where fb_part covers the one FB point among {P0,R,S}.
            empty!(fb_row_scratch)
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row_scratch[idx] = get(fb_row_scratch, idx, 0) + 1
            end

            # Attempt edge insertion / cycle detection under the LP2 lock.
            # We pass al/be (not neg_al/neg_be): the edge invariant is
            #   atom(L) + atom(R) + fb_row = -al·G - be·T
            # so alpha/beta stored on edges are the raw walk values.
            emitted_rel = nothing
            lock(shared_lp2_lock)
            try
                emitted_rel = lp2_insert_edge!(
                    shared_lp2,
                    lp2_a, lp2_b,
                    fb_row_scratch,
                    al, be,
                    ell)
            finally
                unlock(shared_lp2_lock)
            end

            if emitted_rel !== nothing
                # emitted_rel.alpha/beta satisfy:
                #   combined_fb_row = emitted_rel.alpha·G + emitted_rel.beta·T
                # Kernel solve expects: fb_row = alpha_vec·G + beta_vec·T
                # so push them directly without negating.
                push!(alpha_vec, emitted_rel.alpha)
                push!(beta_vec,  emitted_rel.beta)
                push!(rel_rows,  emitted_rel.row)
                push!(rank_growth, (raw_steps, length(rel_rows)))
                hits_full    += 1
                hits_lp2emit += 1
                Threads.atomic_add!(rel_counter, 1)

                # --- PRINCIPAL DIVISOR DIAGNOSTIC ---
                let
                    # Compute D_fb = Σ row[j] · atom(fb[j])
                    D_fb_sum = JacID
                    for (idx, v) in emitted_rel.row
                        pt = fb[idx]
                        D_fb = mumford1(pt[1], pt[2])
                        absv = abs(v)
                        Dv = jac_mul_raw(D_fb, absv)
                        D_fb_sum = v > 0 ? jac_add(D_fb_sum, Dv) : jac_sub(D_fb_sum, Dv)
                    end
                    D_G = jac_mul(G, emitted_rel.alpha)
                    D_T = jac_mul(T, emitted_rel.beta)
                    RHS = jac_add(D_G, D_T)

                    ok_pos = jac_isid(jac_sub(D_fb_sum, RHS))   # D_fb == +alpha*G + beta*T
                    ok_neg = jac_isid(jac_add(D_fb_sum, RHS))   # D_fb == -alpha*G - beta*T

                    if !ok_pos
                        @printf("[LP2-DIAG tid=%d] FAIL  ok_pos=%s ok_neg=%s  alpha=%d beta=%d  row_weight=%d\n",
                                Threads.threadid(), ok_pos, ok_neg,
                                emitted_rel.alpha, emitted_rel.beta, length(emitted_rel.row))
                        @assert false "LP2 emitted relation is not principal! (see diagnostic above)"
                    end
                end
                # ------------------------------------

                cur_pt = fb[rand(1:nF_cur)]
            else
                # No emission; advance anchor to the one FB point if available.
                if i0 != 0
                    cur_pt = P0
                elseif iR != 0
                    cur_pt = R
                elseif iS != 0
                    cur_pt = S
                else
                    cur_pt = fb[rand(1:nF_cur)]
                end
            end

        else
            hits_skip += 1
            cur_pt = fb[rand(1:nF_cur)]
        end
    end

    elapsed_total = time() - t_worker_start
    if verbose
        @printf("[thread %2d | DONE | t=%.1fs] raw=%d valid=%d 0lp=%d 1lp_emit=%d 1lp_step=%d 2lp_seen=%d 2lp_emit=%d skip=%d  rels_local=%d\n",
                tid, elapsed_total, raw_steps, hits_total, hits_0lp, hits_1lp_emit,
                hits_lp1, hits_lp2seen, hits_lp2emit, hits_skip, length(rel_rows))
        @printf("           phi-valid rate: %.4f%%  |  full-rel/valid: %.4f%%  |  steps/full: %.1f\n",
                100.0 * hits_total / max(1, raw_steps),
                100.0 * hits_full / max(1, hits_total),
                raw_steps / max(1, hits_full))
        @printf("           smoothness (0-LP 1-LP 2-LP 3-LP): %d %d %d %d\n",
                smooth_hist[1], smooth_hist[2], smooth_hist[3], smooth_hist[4])
        if length(rank_growth) >= 2
            gaps = [rank_growth[i][1] - rank_growth[i-1][1] for i in 2:min(10, length(rank_growth))]
            @printf("           first-emission raw step gaps (up to 10): %s\n",
                    join(string.(gaps), " "))
        end
        flush(stdout)
    end

    return (rel_rows=rel_rows, alpha_vec=alpha_vec, beta_vec=beta_vec,
            hits_total=hits_total, hits_full=hits_full, hits_0lp=hits_0lp,
            hits_lp1=hits_lp1, hits_1lp_emit=hits_1lp_emit, hits_lp2seen=hits_lp2seen,
            hits_lp2emit=hits_lp2emit, hits_skip=hits_skip,
            sample_rels=sample_rels,
            total_steps=raw_steps,
            smooth_hist=smooth_hist,
            rank_growth=rank_growth,
            lp_col=lp_col)
end

function index_calculus_walk(G::Div2, T::Div2;
                             fb_size::Int         = 650,
                             verbose::Bool        = true,
                             analyze_matrix::Bool = true,
                             asymptotic::Bool     = true,
                             solve::Bool          = true,
                             guided::Bool         = true)

    t_walk_start = time()

    all_pts = curve_points()
    n_all   = length(all_pts)
    n_all < 2 && error("Not enough rational points on the curve")

    nF = min(fb_size, n_all)
    fb = all_pts[1:nF]
    pt2idx = Dict{NTuple{2,Int},Int}(pt => i for (i, pt) in enumerate(fb))

    if verbose
        println()
        @printf("── Factor base ─────────────────────────────────────────────────────\n")
        @printf("  FB size:          %d / %d total rational points\n", nF, n_all)
        @printf("  curve coverage:   %.4f%%  (FB/total)\n", 100.0 * nF / n_all)
        @printf("  smoothness bound: B = %d  (p^(1/2) = %.1f)\n", nF, p^(1/2))
        @printf("  x-range of FB:    [%d, %d]\n",
                minimum(pt[1] for pt in fb), maximum(pt[1] for pt in fb))
        p_smooth_one = nF / n_all
        p_smooth_both = p_smooth_one^2
        @printf("  expected full-rel prob per valid step: ~%.2e  (FB/total)^2\n",
                p_smooth_both)
        @printf("  expected full-rel prob incl. LP: ~%.2e  (1-LP pairs)\n",
                2 * p_smooth_one * (1 - p_smooth_one))
        flush(stdout)
    end

    t_step_build = time()
    N_STEPS = 256
    step_D = Vector{Div2}(undef, N_STEPS)
    step_a = zeros(Int, N_STEPS)
    step_b = zeros(Int, N_STEPS)
    for i in 1:N_STEPS
        a = rand(1:ell-1)
        b = rand(1:ell-1)
        step_D[i] = jac_add(jac_mul(G, a), jac_mul(T, b))
        step_a[i] = a
        step_b[i] = b
    end
    t_step_done = time() - t_step_build

    target_excess = max(20, nF ÷ 10)
    rel_target = nF + 1 + target_excess
    rel_counter = Threads.Atomic{Int}(0)

    shared_lp1       = Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int, Int}}()
    shared_lp1_lock  = ReentrantLock()
    shared_lp2       = LP2Graph()
    shared_lp2_lock  = ReentrantLock()

    if verbose
        println()
        @printf("── Walk setup ──────────────────────────────────────────────────────\n")
        @printf("  N_STEPS (precomputed):  %d\n", N_STEPS)
        @printf("  step table build time:  %.3fs\n", t_step_done)
        @printf("  rel_target:             %d  (nF + 1 + %d excess)\n",
                rel_target, target_excess)
        @printf("  threads:                %d\n", Threads.nthreads())
        @printf("  launching walkers at:   %s\n", string(Dates.now()))
        flush(stdout)
    end

    t_phase2_start = time()
    tasks = Vector{Task}(undef, Threads.nthreads())
    # One collector per thread: no locking needed during walk, merged after.
    thread_collectors = [LPResidualCollector() for _ in 1:Threads.nthreads()]
    for tid in 1:Threads.nthreads()
        tasks[tid] = Threads.@spawn phase2_worker(
            G, T, fb, pt2idx,
            step_D, step_a, step_b,
            rel_counter, rel_target,
            shared_lp1, shared_lp1_lock,
            shared_lp2, shared_lp2_lock,
            thread_collectors[tid]; verbose=verbose)
    end
    results = [fetch(t) for t in tasks]
    t_phase2_done = time() - t_phase2_start

    alpha_vec = Int[]
    beta_vec  = Int[]
    rel_rows  = Vector{Dict{Int,Int}}()
    
    hits_total    = 0
    hits_full     = 0
    hits_0lp      = 0
    hits_lp1      = 0
    hits_1lp_emit = 0
    hits_lp2seen  = 0
    hits_lp2emit  = 0
    hits_skip     = 0
    all_samples   = similar(results[1].sample_rels, 0)

    thread_hits   = Int[]
    thread_full   = Int[]
    thread_lp1    = Int[]
    thread_steps  = Int[]

    for r in results
        append!(alpha_vec, r.alpha_vec)
        append!(beta_vec,  r.beta_vec)
        append!(rel_rows,  r.rel_rows)
        hits_total    += r.hits_total
        hits_full     += r.hits_full
        hits_0lp      += r.hits_0lp
        hits_lp1      += r.hits_lp1
        hits_1lp_emit += r.hits_1lp_emit
        hits_lp2seen  += r.hits_lp2seen
        hits_lp2emit  += r.hits_lp2emit
        hits_skip     += r.hits_skip
        append!(all_samples, r.sample_rels)
        push!(thread_hits,  r.hits_total)
        push!(thread_full,  r.hits_full)
        push!(thread_lp1,   r.hits_lp1)
        push!(thread_steps, r.total_steps)
    end

    nrel = length(rel_rows)

    if verbose
        println()
        @printf("── Walk results ────────────────────────────────────────────────────\n")
        @printf("  phase-2 wall time:     %.3fs\n", t_phase2_done)
        @printf("  total raw steps:       %d  (across all threads)\n",
                sum(thread_steps))
        @printf("  valid phi steps:       %d\n", hits_total)
        @printf("  phi validity rate:     %.4f%%\n",
                100.0 * hits_total / max(1, sum(thread_steps)))
        println()
        @printf("  smoothness breakdown:\n")
        @printf("    0-LP (pure FB):      %d  (%.2f%% of valid steps)\n",
                hits_0lp, 100.0 * hits_0lp / max(1, hits_total))
        @printf("    1-LP steps:          %d  (%.2f%%)\n",
                hits_lp1, 100.0 * hits_lp1 / max(1, hits_total))
        @printf("    1-LP closures emit:  %d  (%.2f%%)\n",
                hits_1lp_emit, 100.0 * hits_1lp_emit / max(1, hits_total))
        @printf("    2-LP seen:           %d  (%.2f%%)\n",
                hits_lp2seen, 100.0 * hits_lp2seen / max(1, hits_total))
        @printf("    2-LP closures emit:  %d  (%.2f%%)\n",
                hits_lp2emit, 100.0 * hits_lp2emit / max(1, hits_total))
        @printf("    3-LP skips:          %d  (%.2f%%)\n",
                hits_skip, 100.0 * hits_skip / max(1, hits_total))
        println()
        @printf("  2-LP graph stats:\n")
        @printf("    edges inserted:      %d\n",  shared_lp2.n_edges_inserted)
        @printf("    cycles found:        %d\n",  shared_lp2.n_cycles_found)
        @printf("    relations emitted:   %d\n",  shared_lp2.n_emitted)
        @printf("    depth-pruned:        %d\n",  shared_lp2.n_depth_pruned)
        @printf("    weight-pruned:       %d\n",  shared_lp2.n_weight_pruned)
        @printf("    LP nodes in graph:   %d\n",  length(shared_lp2.nodes))
        cycle_rate = shared_lp2.n_cycles_found / max(1, shared_lp2.n_edges_inserted)
        emit_rate  = shared_lp2.n_emitted      / max(1, shared_lp2.n_cycles_found)
        @printf("    cycle/edge rate:     %.4f\n", cycle_rate)
        @printf("    emit/cycle rate:     %.4f  (pruning loss)\n", emit_rate)
        println()
        @printf("  total relations collected:   %d\n", nrel)
        @printf("  FB size (nF):                %d\n", nF)
        @printf("  relation surplus:            %+d\n", nrel - (nF + 1))
        @printf("  relation yield rate:         %.4e rels/sec\n",
                nrel / max(1e-9, t_phase2_done))
        @printf("  full-rel yield rate:         %.4e rels/sec\n",
                hits_full / max(1e-9, t_phase2_done))
        @printf("  steps per full relation:     %.1f\n",
                sum(thread_steps) / max(1, hits_full))
        @printf("  1-LP table size (residual):  %d entries\n", length(shared_lp1))
        @printf("  1-LP pair rate:              %.4f  (LP-closures / LP-steps)\n",
                hits_1lp_emit / max(1, hits_lp1))
        println()
        @printf("  per-thread breakdown:\n")
        for tid in 1:length(thread_hits)
            @printf("    thread %d: steps=%d  valid=%d  full=%d  1-LP=%d\n",
                    tid, thread_steps[tid], thread_hits[tid],
                    thread_full[tid], thread_lp1[tid])
        end
        flush(stdout)
    end

    analyze_matrix && analyze_relation_matrix(rel_rows, nF; verbose=verbose)
    analyze_matrix && spectral_gap_report(rel_rows, nF; verbose=verbose)
    asymptotic && asymptotic_report(rel_rows, nF;
                                    hits_total=hits_total,
                                    walk_steps=sum(thread_steps),
                                    hits_full=hits_0lp,
                                    hits_tree=0,
                                    hits_lp=hits_lp1,
                                    hits_lp2=hits_1lp_emit,
                                    verbose=verbose)

    # ── LP residual statistics (ChatGPT analysis) ────────────────────────────
    if verbose
        merged_col = merge_collectors(thread_collectors)
        lp_residual_report(merged_col; p_field=p, verbose=true)
    end
    # ─────────────────────────────────────────────────────────────────────────

    if nrel < nF + 1
        verbose && println("  shortfall: too few relations; skipping solve")
        return nothing
    end

    !solve && return nothing

    empty!(shared_lp1)
    empty!(shared_lp2.nodes)
    empty!(all_samples)
    GC.gc()

    if verbose
        println()
        @printf("── Pre-solve diagnostics ───────────────────────────────────────────\n")
        @printf("  nrel=%d, nF=%d, kernel dim to follow...\n", nrel, nF)
        @printf("  alpha_vec range: [%d, %d]\n", extrema(alpha_vec)...)
        @printf("  beta_vec range:  [%d, %d]\n", extrema(beta_vec)...)
        weights = [length(rel_rows[i]) for i in 1:nrel]
        @printf("  row weight: min=%d, max=%d, mean=%.2f, median=%d\n",
                minimum(weights), maximum(weights),
                sum(weights)/nrel,
                sort(weights)[(length(weights)+1)÷2])
        n_zero_row = count(isempty, rel_rows)
        n_zero_ab  = count(i -> alpha_vec[i]==0 && beta_vec[i]==0, 1:nrel)
        @printf("  zero rows: %d,  zero-alpha-and-beta: %d\n", n_zero_row, n_zero_ab)

        all_rg = vcat([r.rank_growth for r in results]...)
        if !isempty(all_rg)
            total_raw = sum(r.total_steps for r in results)
            @printf("  rank growth: %d emissions logged across threads\n", length(all_rg))
            @printf("  total raw steps (all threads): %d\n", total_raw)
            @printf("  raw steps per full emission (global): %.1f\n",
                    total_raw / max(1, hits_full))
        end

        agg_hist = zeros(Int, 4)
        for r in results
            agg_hist .+= r.smooth_hist
        end
        @printf("  global smoothness histogram (0-LP 1-LP 2-LP 3-LP): %d %d %d %d\n",
                agg_hist[1], agg_hist[2], agg_hist[3], agg_hist[4])
        total_smooth = sum(agg_hist)
        if total_smooth > 0
            @printf("  smoothness fractions: 0-LP=%.3f  1-LP=%.3f  2-LP=%.3f  3-LP=%.3f\n",
                    agg_hist[1]/total_smooth, agg_hist[2]/total_smooth,
                    agg_hist[3]/total_smooth, agg_hist[4]/total_smooth)
        end

        @printf("  spot-checking %d full relations:\n", min(5, length(all_samples)))
        n_ok = 0; n_bad = 0
        for (D_stored, fb_row, neg_al, neg_be, P0, R, S) in all_samples[1:min(5,end)]
            lhs = jac_add(jac_mul(G, neg_al), jac_mul(T, neg_be))
            neg_D = jac_neg(D_stored)
            step_ok = (lhs == neg_D)
            @printf("    neg_al=%d neg_be=%d  neg_al*G+neg_be*T == -D_cur: %s\n",
                    neg_al, neg_be, step_ok)
            step_ok ? (n_ok += 1) : (n_bad += 1)
        end
        @printf("  spot-check: %d ok, %d BAD\n", n_ok, n_bad)
        @printf("  ell*G == id: %s,  ell = %d\n",
                jac_isid(jac_mul_raw(G, ell)), ell)
        flush(stdout)
    end

    verbose && @printf("\n── Kernel solve ────────────────────────────────────────────────────\n")
    verbose && @printf("  Left-kernel search over GF(%d)...\n", ell)
    t_solve_start = time()
    kernels = left_kernel_all(rel_rows, nF, ell)
    t_solve_done = time() - t_solve_start
    isempty(kernels) && error("Kernel not found — collect more relations")

    verbose && @printf("  kernel solve time: %.3fs\n", t_solve_done)
    verbose && @printf("  kernel dimension:  %d\n", length(kernels))

    n_tried = 0
    for γ in kernels
        Sa = mod(sum(Int128(γ[i]) * alpha_vec[i] for i in 1:nrel), ell)
        Sb = mod(sum(Int128(γ[i]) * beta_vec[i]  for i in 1:nrel), ell)
        Sb == 0 && continue
        k_cand = mod(-Int(Sa) * powermod(Int(Sb), ell - 2, ell), ell)
        n_tried += 1
        if verbose && n_tried <= 5
            @printf("  kernel vec %d: Sa=%d Sb=%d k_cand=%d  match=%s\n",
                    n_tried, Sa, Sb, k_cand, jac_mul(G, k_cand) == T)
        end
        if jac_mul(G, k_cand) == T
            verbose && @printf("  ✓  k = %d   (k*G == T)  [kernel vec %d of %d]\n",
                               k_cand, n_tried, length(kernels))
            verbose && @printf("  total walk+solve time: %.3fs\n", time() - t_walk_start)
            return k_cand
        end
    end

    verbose && @printf("  tried %d kernel vectors, none matched\n", n_tried)
    verbose && println("  No usable kernel vector found; will retry with fresh walk.")
    return nothing
end



function largest_prime_factor(n::Int)
    d = 2
    best = 1
    while d*d ≤ n
        while n % d == 0
            best = d
            n ÷= d
        end
        d += 1
    end
    return max(best, n)
end

# order_via_cycle removed: Floyd's cycle detection with a 1e7 cap can never find
# element orders for #Jac ≈ p² ≈ 2.7e10.  Use jac_order_bsgs (O(√#Jac)) instead.




function main2()
    t_main_start = time()
    println("="^70)
    println("  trial2: Markov-walk phi-relation index calculus")
    println("  y^2 = x^5+3x^3+2x^2+5x+4  /F_$p,  ell=<auto>")
    println("  threads = $(Threads.nthreads())  |  start: $(Dates.now())")
    println("="^70, "\n")

    # 1. Get the list of points and print curve stats
    t_pts = time()
    pts = curve_points()
    t_pts_done = time() - t_pts
    if length(pts) < 2
        error("No affine points found on curve.")
    end
    @printf("Curve enumeration: %d affine rational points in %.3fs\n", length(pts), t_pts_done)
    @printf("  expected ~p = %d points (density check: %.4f)\n",
            p, length(pts) / Float64(p))
    println()

    # ── subgroup bootstrap via Pollard rho ────────────────────────────────
    println("── Generator search (Pollard rho) ──────────────────────────────────")
    t_ell = time()
    G, ell_found = fast_find_ell_generator()
    t_ell_done = time() - t_ell
    global ell = ell_found

    @printf("  bootstrap total time = %.3fs\n", t_ell_done)
    @printf("  G.u = %s\n  G.v = %s\n", G.u, G.v)
    @printf("  ell = %d  (%.1f bits)\n", ell, log2(ell))
    @printf("  ell/p ratio = %.6f\n", ell / p)

    # Verification
    @assert jac_isid(jac_mul_raw(G, ell))  "G does not have order ell"
    println("  Confirmed: ell*G = identity")
    println()

    k_true = rand(2:ell-1)
    T      = jac_mul(G, k_true)
    @printf("Secret k = %d  (%.1f bits)\n\n", k_true, log2(k_true + 1))

    # Scale FB size as p^(1/2) — the standard smoothness bound for genus-2
    # index calculus.  At p≈100k: ~2154; p≈164k: ~3024; p≈1M: ~10000.
    fb_auto = clamp(round(Int, p^(1/2)), 200, 20000)
    @printf("Auto FB size: %d  (= ceil(p^(1/2)) clamped to [200,20000])\n", fb_auto)
    @printf("  target relations: %d + excess\n", fb_auto + 1)
    @printf("  expected smoothness prob per step: ~(fb_auto/p)^2 ~ %.2e\n",
            (fb_auto / p)^2)
    println()

    # Main run
    println("── Index calculus walk ─────────────────────────────────────────────")
    t_walk = time()
    k_rec = index_calculus_walk(G, T;
                                fb_size=fb_auto,
                                verbose=true, analyze_matrix=true, asymptotic=true,
                                solve=true, guided=true)
    t_walk_done = time() - t_walk

    println()
    println("── Final results ───────────────────────────────────────────────────")
    @printf("  walk+solve wall time: %.3fs\n", t_walk_done)
    @printf("  total wall time:      %.3fs\n", time() - t_main_start)
    if k_rec !== nothing
        @printf("  Recovered k = %-10d  true k = %-10d  match = %s\n",
                k_rec, k_true, k_rec == k_true)
    else
        println("  DLP not recovered.")
    end
    println("="^70)
end



# ---------------------------------------------------------------------------
#  fast_find_ell_generator — BSGS-based, O(√#Jac) = O(p) jac_add calls.
#
#  Strategy:
#    1. Pick two random affine rational points, build a random degree-2 divisor.
#    2. Find its exact order via jac_order_bsgs (baby-giant, O(√#Jac) ≈ O(p)).
#    3. Extract the largest prime factor ell_cand of that order.
#    4. Multiply D by the cofactor to get a generator of order exactly ell_cand.
#    5. Verify ell_cand * G = id, then return.
#
#  Why not order_via_cycle?
#    Floyd's cycle detection needs O(λ) iterations where λ is the element order.
#    For a random element of the genus-2 Jacobian, λ ≈ #Jac ≈ p² ≈ 2.7e10
#    (for p = 164147), which vastly exceeds any practical cap.  BSGS finds the
#    order in O(√#Jac) ≈ 165 000 jac_add calls — a few seconds, not forever.
# ---------------------------------------------------------------------------
function fast_find_ell_generator(::Div2 = JacID; trials::Int = 200)

    println("Finding G of large prime order (Pollard rho, parallel)...")

    t_start = time()

    pts = curve_points()
    n   = length(pts)

    n < 2 && error("Not enough rational points on the curve")

    nthreads = Threads.nthreads()
    trials_per_thread = max(1, cld(trials, nthreads))

    result_ch = Channel{Tuple{Div2, Int, NamedTuple}}(1)

    done = Threads.Atomic{Bool}(false)

    # hard cap for rho
    rho_max = 64 * p + 10_000

    for tid in 1:nthreads

        Threads.@spawn begin

            n_id_skips     = 0
            n_tiny_ell     = 0
            n_id_cofac     = 0
            n_bad_verify   = 0
            n_ord_calls    = 0
            total_ord_time = 0.0

            for attempt in 1:trials_per_thread

                done[] && break

                P = pts[rand(1:n)]
                Q = pts[rand(1:n)]

                D = mumford_from_pts(P, Q)

                if jac_isid(D)
                    n_id_skips += 1
                    continue
                end

                t_ord = time()

                ord = try
                    jac_order_pollard_rho(D; max_iter = rho_max, abort_flag = done)
                catch e
                    e isa InterruptException && break
                    rethrow(e)
                end

                total_ord_time += time() - t_ord
                n_ord_calls += 1

                ord <= 1 && continue

                ell_cand = largest_prime_factor(ord)

                if ell_cand < max(isqrt(p), 3)
                    n_tiny_ell += 1
                    continue
                end

                cofactor = ord ÷ ell_cand

                cofactor == 0 && continue

                G = jac_mul_raw(D, cofactor)

                if jac_isid(G)
                    n_id_cofac += 1
                    continue
                end

                if !jac_isid(jac_mul_raw(G, ell_cand))
                    n_bad_verify += 1
                    continue
                end

                old = Threads.atomic_cas!(done, false, true)

                if !old

                    GC.safepoint()   # nudge Julia scheduler; stuck threads re-check done[] sooner

                    stats = (
                        thread         = tid,
                        attempt        = attempt,
                        ord            = ord,
                        ell_cand       = ell_cand,
                        cofactor       = cofactor,
                        n_ord_calls    = n_ord_calls,
                        total_ord_time = total_ord_time,
                        n_id_skips     = n_id_skips,
                        n_tiny_ell     = n_tiny_ell,
                        n_id_cofac     = n_id_cofac,
                        n_bad_verify   = n_bad_verify,
                    )

                    # nonblocking because channel size = 1
                    put!(result_ch, (G, ell_cand, stats))
                end

                break
            end
        end
    end

    # separate waiter task
    waiter = Threads.@spawn take!(result_ch)

    timeout_s = 60.0 + 120.0 * (p / 164147)

    t0 = time()

    while !istaskdone(waiter)

        if (time() - t0) > timeout_s

            done[] = true
            GC.safepoint()

            error("fast_find_ell_generator: timeout after $(timeout_s)s")
        end

        sleep(0.05)
    end

    done[] = true
    GC.safepoint()

    G, ell_cand, s = fetch(waiter)

    total_elapsed = time() - t_start

    @printf(
        "  thread %d, attempt %d: ord(D) = %d, ell = %d, cofactor h = %d\n",
        s.thread,
        s.attempt,
        s.ord,
        s.ell_cand,
        s.cofactor
    )

    @printf(
        "  order calls (winner thread): %d, avg rho time: %.4fs, total rho time: %.4fs\n",
        s.n_ord_calls,
        s.total_ord_time / max(1, s.n_ord_calls),
        s.total_ord_time
    )

    @printf(
        "  skips (winner) — id_divisor: %d, tiny_ell: %d, id_after_cofac: %d, bad_verify: %d\n",
        s.n_id_skips,
        s.n_tiny_ell,
        s.n_id_cofac,
        s.n_bad_verify
    )

    @printf(
        "  generator search total wall time: %.3fs (%d threads)\n",
        total_elapsed,
        nthreads
    )

    flush(stdout)

    return G, ell_cand
end


main2()
