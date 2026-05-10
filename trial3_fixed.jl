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
    # Build the Nemo matrix directly from sparse rel_rows — never touch a dense Julia array.
    try
        F = Nemo.GF(ell)
        # Nemo.matrix from a flat vector of elements, row-major.
        entries = Vector{elem_type(F)}(undef, m * n)
        for i in 1:m
            base = (i-1)*n
            for j in 1:n
                entries[base+j] = F(0)
            end
            for (j, v) in rel_rows[i]
                1 <= j <= n || continue
                entries[base+j] = F(mod(v, ell))
            end
        end
        Rnemo = Nemo.matrix(F, m, n, entries)
        nu, K = nullspace(transpose(Rnemo))
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

function phase2_worker(G::Div2, T::Div2,
                       fb::Vector{NTuple{2,Int}},
                       pt2idx::Dict{NTuple{2,Int},Int},
                       step_D::Vector{Div2},
                       step_a::Vector{Int},
                       step_b::Vector{Int},
                       rel_counter::Threads.Atomic{Int},
                       rel_target::Int,
                       shared_lp1::Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}},
                       shared_lp1_lock::ReentrantLock;
                       verbose::Bool = true)

    nF_cur   = length(fb)
    N_STEPS  = length(step_D)

    # Per-thread mutable state
    cur_pt    = fb[rand(1:nF_cur)]
    alpha_cur = rand(1:ell-1)
    beta_cur  = rand(0:ell-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur), jac_mul(T, beta_cur))

    alpha_vec = Int[]
    beta_vec  = Int[]
    rel_rows  = Vector{Dict{Int,Int}}()

    hits_total   = 0
    hits_full    = 0
    hits_lp1     = 0
    hits_lp2seen = 0
    hits_lp2emit = 0
    hits_skip    = 0
    step         = 0


    # Sample full relations for algebraic spot-checking.
    sample_rels = Vector{Tuple{Div2,Dict{Int,Int},Int,Int,NTuple{2,Int},NTuple{2,Int},NTuple{2,Int}}}()
    # 2-LP graph: sparse edge walk (per-thread; no lock needed).
    lp2_edges    = LP2Edge[]
    lp2_live     = Bool[]
    lp2_incidence = Dict{NTuple{2,Int}, Vector{Int}}()

    while rel_counter[] < rel_target
        # (rel_counter check at top of loop is the only exit condition)

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
        step += 1

        if verbose && step % 100_000 == 0
            @printf("[thread %d] steps=%d  hits=%d  rels=%d/%d\n",
                    Threads.threadid(), step, hits_total, rel_counter[], rel_target)
            flush(stdout)
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

        if n_lp == 0
            fb_row = Dict{Int,Int}()
            for idx in (i0, iR, iS)
                fb_row[idx] = get(fb_row, idx, 0) + 1
            end
            push!(alpha_vec, neg_al)
            push!(beta_vec,  neg_be)
            push!(rel_rows,  fb_row)
            # Stash first few full relations with their divisor for spot-checking
            if length(sample_rels) < 10
                push!(sample_rels, (D_cur, copy(fb_row), neg_al, neg_be, P0, R, S))
            end
            hits_full += 1
            Threads.atomic_add!(rel_counter, 1)
            cur_pt = fb[rand(1:nF_cur)]

        elseif n_lp == 1
            hits_lp1 += 1
            lp_pt = i0 == 0 ? P0 : (iR == 0 ? R : S)
            fb_row = Dict{Int,Int}()
            for idx in (i0, iR, iS)
                idx == 0 && continue
                fb_row[idx] = get(fb_row, idx, 0) + 1
            end

            lock(shared_lp1_lock)
            if haskey(shared_lp1, lp_pt)
                prev_row, prev_al, prev_be = shared_lp1[lp_pt]
                combined = copy(fb_row)
                lp2_subtract_rows(combined, prev_row)
                combined_al = mod(neg_al - prev_al, ell)
                combined_be = mod(neg_be - prev_be, ell)
                delete!(shared_lp1, lp_pt)
                unlock(shared_lp1_lock)
                if !isempty(combined) && !(combined_al == 0 && combined_be == 0)
                    push!(alpha_vec, combined_al)
                    push!(beta_vec,  combined_be)
                    push!(rel_rows,  combined)
                    hits_full += 1
                    Threads.atomic_add!(rel_counter, 1)
                end
            else
                shared_lp1[lp_pt] = (fb_row, neg_al, neg_be)
                unlock(shared_lp1_lock)
            end

            # Re-anchor to a known FB point without allocating a temp vector.
            if i0 != 0
                cur_pt = P0
            elseif iR != 0
                cur_pt = R
            elseif iS != 0
                cur_pt = S
            else
                cur_pt = fb[rand(1:nF_cur)]
            end

        elseif n_lp == 2
            hits_lp2seen += 1
            fb_row = Dict{Int,Int}()
            lp_pts = NTuple{2,Int}[]
            for (idx, pt) in ((i0, P0), (iR, R), (iS, S))
                if idx == 0
                    push!(lp_pts, pt)
                else
                    fb_row[idx] = get(fb_row, idx, 0) + 1
                end
            end
            if length(lp_pts) != 2
                hits_skip += 1
                cur_pt = fb[rand(1:nF_cur)]
                continue
            end

            # Feed the 2-LP graph for bookkeeping/counting only.
            # Emission disabled: synthetic rows from graph closure carry
            # sign/involution errors that poison the kernel.  Store edges
            # and count closures but do not push rows into rel_rows.
            _dummy_rows  = Vector{Dict{Int,Int}}()
            _dummy_alpha = Int[]
            _dummy_beta  = Int[]
            _dummy_ctr   = Threads.Atomic{Int}(0)
            emitted = lp2_attach!(lp2_edges, lp2_live, lp2_incidence,
                                  lp_pts[1], lp_pts[2], fb_row, neg_al, neg_be,
                                  _dummy_rows, _dummy_alpha, _dummy_beta,
                                  _dummy_ctr)
            hits_lp2emit += emitted
            # hits_full NOT incremented; rows intentionally not added to matrix

            # Re-anchor on the known FB point if there is one; otherwise reseed.
            if i0 != 0
                cur_pt = P0
            elseif iR != 0
                cur_pt = R
            elseif iS != 0
                cur_pt = S
            else
                cur_pt = fb[rand(1:nF_cur)]
            end

        else
            hits_skip += 1
            cur_pt = fb[rand(1:nF_cur)]
        end
    end

    return (rel_rows=rel_rows, alpha_vec=alpha_vec, beta_vec=beta_vec,
            hits_total=hits_total, hits_full=hits_full,
            hits_lp1=hits_lp1, hits_lp2seen=hits_lp2seen,
            hits_lp2emit=hits_lp2emit, hits_skip=hits_skip,
            sample_rels=sample_rels)
end



function index_calculus_walk(G::Div2, T::Div2;
                             fb_size::Int         = 650,
                             verbose::Bool        = true,
                             analyze_matrix::Bool = true,
                             asymptotic::Bool     = true,
                             solve::Bool          = true,
                             guided::Bool         = true)

    all_pts = curve_points()
    n_all   = length(all_pts)
    n_all < 2 && error("Not enough rational points on the curve")

    # Use the first fb_size rational points as a fixed factor base.
    nF = min(fb_size, n_all)
    fb = all_pts[1:nF]
    pt2idx = Dict{NTuple{2,Int},Int}(pt => i for (i, pt) in enumerate(fb))

    verbose && @printf("Factor base: %d / %d rational points\n", nF, n_all)

    # Precompute random walk steps.
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

    target_excess = max(20, nF ÷ 10)
    rel_target = nF + 1 + target_excess
    rel_counter = Threads.Atomic{Int}(0)

    # Shared 1-LP table across all threads — the single biggest closure multiplier.
    # A ReentrantLock guards it; contention is low because each insert/lookup is O(1).
    shared_lp1       = Dict{NTuple{2,Int}, Tuple{Dict{Int,Int}, Int, Int}}()
    shared_lp1_lock  = ReentrantLock()

    verbose && @printf("Phase 2: launching %d walker thread(s), target=%d live rels...\n",
                       Threads.nthreads(), rel_target)

    tasks = Vector{Task}(undef, Threads.nthreads())
    for tid in 1:Threads.nthreads()
        tasks[tid] = Threads.@spawn phase2_worker(
            G, T, fb, pt2idx,
            step_D, step_a, step_b,
            rel_counter, rel_target,
            shared_lp1, shared_lp1_lock; verbose=verbose)
    end
    results = [fetch(t) for t in tasks]

    alpha_vec = Int[]
    beta_vec  = Int[]
    rel_rows  = Vector{Dict{Int,Int}}()
    hits_total = 0
    hits_full  = 0
    hits_lp1   = 0
    hits_lp2seen = 0
    hits_lp2emit = 0
    hits_skip  = 0
    all_samples = similar(results[1].sample_rels, 0)

    for r in results
        append!(alpha_vec, r.alpha_vec)
        append!(beta_vec,  r.beta_vec)
        append!(rel_rows,  r.rel_rows)
        hits_total   += r.hits_total
        hits_full    += r.hits_full
        hits_lp1     += r.hits_lp1
        hits_lp2seen += r.hits_lp2seen
        hits_lp2emit += r.hits_lp2emit
        hits_skip    += r.hits_skip
        append!(all_samples, r.sample_rels)
    end

    nrel = length(rel_rows)
    verbose && @printf("Walk done: %d valid steps\n", hits_total)
    verbose && @printf(
        "FB: %d atoms | full rels: %d | 1-LP steps: %d | 2-LP seen: %d | 2-LP closures: %d | skips: %d\n",
        nF, hits_full, hits_lp1, hits_lp2seen, hits_lp2emit, hits_skip)
    verbose && @printf("Total relations: %d  (need >= %d)\n", nrel, nF + 1)

    analyze_matrix && analyze_relation_matrix(rel_rows, nF; verbose=verbose)
    analyze_matrix && spectral_gap_report(rel_rows, nF; verbose=verbose)
    asymptotic && asymptotic_report(rel_rows, nF;
                                    hits_total=hits_total,
                                    walk_steps=hits_total,
                                    hits_full=hits_full,
                                    hits_tree=0,
                                    hits_lp=hits_lp1,
                                    hits_lp2=hits_lp2emit,
                                    verbose=verbose)

    if nrel < nF + 1
        verbose && println("  shortfall: too few relations; skipping solve")
        return nothing
    end

    !solve && return nothing


    # ── Diagnostics before solve ──────────────────────────────────────────────
    if verbose
        println("  [diag] nrel=$(nrel), nF=$(nF), kernel dim to follow...")
        println("  [diag] alpha_vec range: $(extrema(alpha_vec))")
        println("  [diag] beta_vec range:  $(extrema(beta_vec))")
        weights = [length(rel_rows[i]) for i in 1:nrel]
        println("  [diag] row weight: min=$(minimum(weights)), max=$(maximum(weights)), mean=$(round(sum(weights)/nrel, digits=2))")
        n_zero_row = count(isempty, rel_rows)
        n_zero_ab  = count(i -> alpha_vec[i]==0 && beta_vec[i]==0, 1:nrel)
        println("  [diag] zero rows=$(n_zero_row), zero-alpha-and-beta=$(n_zero_ab)")

        # Algebraic spot-check: for each sampled full relation,
        # verify neg_al*G + neg_be*T == D_cur (the step divisor).
        # The phi relation gives atom(P0)+atom(R)+atom(S) = -D_cur,
        # and we store neg_al=-alpha, neg_be=-beta, so neg_al*G+neg_be*T == D_cur.
        println("  [diag] spot-checking $(min(5,length(all_samples))) full relations:")
        n_ok = 0; n_bad = 0
        for (D_stored, fb_row, neg_al, neg_be, P0, R, S) in all_samples[1:min(5,end)]
            # neg_al = ell - alpha, neg_be = ell - beta, D_stored = alpha*G + beta*T
            # so neg_al*G + neg_be*T = -D_stored.  Check that.
            lhs = jac_add(jac_mul(G, neg_al), jac_mul(T, neg_be))
            neg_D = jac_neg(D_stored)
            step_ok = (lhs == neg_D)
            @printf("    neg_al=%d neg_be=%d  neg_al*G+neg_be*T == -D_cur: %s\n",
                    neg_al, neg_be, step_ok)
            step_ok ? (n_ok += 1) : (n_bad += 1)
        end
        println("  [diag] spot-check: $(n_ok) ok, $(n_bad) BAD")
        println("  [diag] ell*G == id: $(jac_isid(jac_mul_raw(G, ell)))")
        println("  [diag] ell = $(ell)")
    end

    verbose && println("Left-kernel search over GF($ell)...")
    kernels = left_kernel_all(rel_rows, nF, ell)
    isempty(kernels) && error("Kernel not found — collect more relations")

    verbose && @printf("  kernel dimension = %d\n", length(kernels))

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
            verbose && println("  ✓  k = $k_cand   (k*G == T)")
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
    println("="^62)
    println("  trial2: Markov-walk phi-relation index calculus")
    println("  y^2 = x^5+3x^3+2x^2+5x+4  /F_$p,  ell=$ell")
    println("="^62, "\n")

    # 1. Get the list of points
    pts = curve_points()
    if length(pts) < 2
        error("No affine points found on curve.")
    end

    # ── fast subgroup bootstrap via BSGS ─────────────────────────────────
    t_ell = time()
    G, ell_found = fast_find_ell_generator()
    
    global ell = ell_found
    @printf("  bootstrap time = %.2fs\n", time()-t_ell)
    @printf("G.u = %s\nG.v = %s\n", G.u, G.v)
    
    # Verification
    @assert jac_isid(jac_mul_raw(G, ell))  "G does not have order ell"
    println("Confirmed: ell*G = identity\n")

    k_true = rand(2:ell-1)
    T      = jac_mul(G, k_true)
    @printf("Secret k = %d\n\n", k_true)

    # Scale FB size as p^(2/3) — the standard smoothness bound for genus-2
    # index calculus.  At p≈100k: ~2154; p≈164k: ~3024; p≈1M: ~10000.
    fb_auto  = clamp(round(Int, p^(2/3)), 200, 20000)

    # Main run
    k_rec = index_calculus_walk(G, T;
                                fb_size=fb_auto,
                                verbose=true, analyze_matrix=false, asymptotic=false,
                                solve=true, guided=true)

    println()
    if k_rec !== nothing
        @printf("Recovered k = %-8d  true k = %-8d  match = %s\n",
                k_rec, k_true, k_rec == k_true)
    else
        println("DLP not recovered.")
    end
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
    println("Finding G of large prime order (BSGS)...")
    pts = curve_points()
    n   = length(pts)
    n < 2 && error("Not enough rational points on the curve")

    for attempt in 1:trials
        # Random degree-2 divisor from two independently chosen rational points.
        P = pts[rand(1:n)]
        Q = pts[rand(1:n)]
        D = mumford_from_pts(P, Q)
        jac_isid(D) && continue

        # Exact element order via baby-giant.  For p = 164147 this stores
        # ≈ 165 000 Div2 entries and does ≈ 330 000 jac_add calls.
        ord = jac_order_bsgs(D)
        ord <= 1 && continue

        # Extract the largest prime factor without Oscar (trial division).
        ell_cand = largest_prime_factor(ord)
        ell_cand < 1000 && continue          # skip if subgroup is tiny

        cofactor = ord ÷ ell_cand
        cofactor == 0 && continue

        G = jac_mul_raw(D, cofactor)
        jac_isid(G) && continue              # unlucky draw; try again

        # Sanity: ell_cand · G must be the identity.
        jac_isid(jac_mul_raw(G, ell_cand)) || continue

        @printf("  attempt %d: ord(D) = %d,  ell = %d\n", attempt, ord, ell_cand)
        return G, ell_cand
    end

    error("fast_find_ell_generator: no large-prime-order element found in $trials attempts")
end




main2()
