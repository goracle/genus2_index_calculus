#!/usr/bin/env julia
#
# hc_path_estimate.jl
#
# BKK (Bernstein-Kushnirenko-Khovanskii) path-count estimate for a planned
# HomotopyContinuation.jl run on the U/V matching system, using the same
# Newton-polytope machinery already in newton_polytope.jl.
#
# IMPORTANT -- this does NOT assume the 4x4 system decomposes into two
# independent 2x2 blocks (x1,x2) and (x3,x4). That decomposition has not
# been confirmed. This script computes the estimate under BOTH scenarios so
# the block-structure question can be settled by inspection of the actual
# equations rather than assumed away.
#
# Why only the 2-variable case gets an exact closed form here:
#   For two polytopes P, Q in the PLANE, the mixed volume has the
#   inclusion-exclusion closed form
#       MV(P,Q) = Vol(P+Q) - Vol(P) - Vol(Q)
#   which needs only volume() and minkowski_sum(), both already implemented
#   in newton_polytope.jl via Oscar/Polymake. This is what
#   two_variable_mixed_volume below computes -- no new convex-geometry code,
#   just composition of what's already there.
#
#   For n>2 variables there is no such two-term closed form; genuine mixed
#   volume in n dimensions needs either the full multivariate
#   inclusion-exclusion over subsets of the polytopes (2^n - 1 terms, each a
#   volume of a Minkowski sum) or a dedicated mixed-volume/BKK routine.
#   Polymake does not expose the latter through what's wrapped here, so the
#   4-variable "undecomposed" estimate below uses the general
#   inclusion-exclusion formula directly (n=4 means 15 Minkowski sums, not
#   too costly for 4 polytopes) rather than approximating it.
#
# Usage:
#   julia hc_path_estimate.jl <U_alpha.native> <V_alpha.native> \
#                              <U_alphaprime.native> <V_alphaprime.native>
#
# If the native files aren't available yet (U/V still being recomputed),
# run with --box to use the stated degree-box assumption instead of reading
# any file: full cube, degree 64 in U's two variables, degree 96 in V's two
# variables, treating "<32 terms missing out of tens of millions" as an
# exact full box for polytope-vertex purposes (missing interior lattice
# points don't move the hull unless they're missing from the box's own
# vertices/facets -- worth double-checking that assumption once real data
# is available, since near-vertex gaps *would* change the answer).

include(joinpath(@__DIR__, "newton_polytope.jl"))

using Combinatorics: combinations

# ---------------------------------------------------------------------------
# Exact 2-variable mixed volume, reusing existing volume()/minkowski_sum()
# ---------------------------------------------------------------------------

"""
    two_variable_mixed_volume(P::NewtonPolytope, Q::NewtonPolytope) -> Int

Mixed volume of two polytopes in the plane (ambient_dim == 2), via the
closed-form MV(P,Q) = Vol(P+Q) - Vol(P) - Vol(Q). Raises if either polytope
is not 2-dimensional ambient.
"""
function two_variable_mixed_volume(P::NewtonPolytope, Q::NewtonPolytope)
    ambient_dimension(P) == 2 && ambient_dimension(Q) == 2 ||
        error("two_variable_mixed_volume: expected both polytopes to have " *
              "ambient_dim=2, got $(ambient_dimension(P)) and $(ambient_dimension(Q)) " *
              "-- use inclusion_exclusion_mixed_volume for n>2")

    vP = normalized_volume_of(P)
    vQ = normalized_volume_of(Q)
    sum_pq = minkowski_sum(P, Q)
    vsum = normalized_volume_of(sum_pq)

    # normalized_volume_of returns n! * (Euclidean volume) by polymake
    # convention (matches how newton_polytope.jl already reports it) -- the
    # inclusion-exclusion identity is linear in whichever convention is used
    # consistently, so no rescaling is needed here as long as all three
    # volumes come from the same function.
    mv = vsum - vP - vQ
    mv >= 0 ||
        error("two_variable_mixed_volume: computed negative mixed volume " *
              "($mv) -- likely a normalized-volume convention mismatch " *
              "between Vol(P+Q), Vol(P), Vol(Q); check normalized_volume_of's " *
              "scaling before trusting this result")
    return mv
end

# ---------------------------------------------------------------------------
# General n-variable mixed volume via inclusion-exclusion (exact, not an
# approximation -- just more Minkowski sums as n grows)
# ---------------------------------------------------------------------------

"""
    inclusion_exclusion_mixed_volume(polys::Vector{NewtonPolytope}) -> Rational

Exact mixed volume MV(P_1,...,P_n) of n polytopes in R^n via
    MV(P_1,...,P_n) = (1/n!) * sum_{S subseteq {1..n}, S nonempty}
                           (-1)^(n-|S|) * Vol(sum_{i in S} P_i)
Requires n! Minkowski sums to evaluate (2^n - 1 subset sums, each reusing
minkowski_sum/normalized_volume_of already in newton_polytope.jl). Raises if
any polytope's ambient dimension doesn't match n = length(polys).
"""
function inclusion_exclusion_mixed_volume(polys::Vector{NewtonPolytope})
    n = length(polys)
    n >= 1 || error("inclusion_exclusion_mixed_volume: need at least 1 polytope")
    for (i, P) in enumerate(polys)
        ambient_dimension(P) == n ||
            error("inclusion_exclusion_mixed_volume: polytope $i has " *
                  "ambient_dim=$(ambient_dimension(P)), expected $n to match " *
                  "the number of polytopes (mixed volume of n polytopes is " *
                  "only defined in R^n)")
    end

    total = 0 // 1
    idxs = collect(1:n)
    for k in 1:n
        for S in combinations(idxs, k)
            summed = polys[S[1]]
            for j in S[2:end]
                summed = minkowski_sum(summed, polys[j])
            end
            vol_S = normalized_volume_of(summed)
            sign = (-1)^(n - k)
            total += sign * vol_S
        end
    end
    mv = total // factorial(n)
    mv >= 0 ||
        error("inclusion_exclusion_mixed_volume: computed negative mixed " *
              "volume ($mv) -- check normalized_volume_of's scaling " *
              "convention before trusting this result")
    return mv
end

# ---------------------------------------------------------------------------
# Box-polytope construction (for the --box fallback, no file needed)
# ---------------------------------------------------------------------------

"""
    full_box_polytope(degrees::Vector{Int}) -> NewtonPolytope

Newton polytope of a dense polynomial whose Newton polytope is the full
axis-aligned box [0,degrees[1]] x ... x [0,degrees[n]] -- i.e. every
exponent tuple with 0 <= e_i <= degrees[i] present. This is the "<32 terms
missing out of tens of millions" assumption: treated as an exact full box.
Only the box's 2^n VERTICES actually matter for convex hull / volume
purposes, so this is cheap regardless of how many terms the real polynomial
has.
"""
function full_box_polytope(degrees::Vector{Int})
    n = length(degrees)
    supp = Vector{Vector{Int}}()
    for corner in Iterators.product((0:1 for _ in 1:n)...)
        push!(supp, [c == 1 ? degrees[i] : 0 for (i, c) in enumerate(corner)])
    end
    return newton_polytope(supp, n)
end

# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

function main()
    use_box = "--box" in ARGS

    if use_box
        println("Using stated box-degree assumption (no files read):")
        println("  U_alpha, U_alphaprime : full box, degree 64 in each of 2 vars")
        println("  V_alpha, V_alphaprime : full box, degree 96 in each of 2 vars")
        println("  (<32 missing terms out of tens of millions treated as exact box)")
        println()

        # 2-variable (block-decomposed) scenario: x1,x2 only for the alpha
        # side, x3,x4 only for the alpha' side.
        U_block = full_box_polytope([64, 64])
        V_block = full_box_polytope([96, 96])
        mv_block = two_variable_mixed_volume(U_block, V_block)

        println("=" ^ 70)
        println("SCENARIO A: system decomposes into two independent 2x2 blocks")
        println("  {U_alpha=0, V_alpha=0} in (x1,x2), {U_alphaprime=0, V_alphaprime=0} in (x3,x4)")
        println("=" ^ 70)
        println("  Mixed volume per block (BKK path bound): ", mv_block)
        println("  Two independent blocks -> paths run as 2 separate small systems")
        println("  Total path-tracking work (sum, not product): ", 2 * mv_block)
        println()

        # 4-variable (undecomposed) scenario: build each equation's polytope
        # embedded in the full 4-dim ambient space (degree 0 in the
        # variables it doesn't involve), then take the genuine 4-way mixed
        # volume via inclusion-exclusion.
        embed(degrees_nonzero::Vector{Int}, which_vars::Vector{Int}, n::Int) = begin
            supp = Vector{Vector{Int}}()
            for corner in Iterators.product((0:1 for _ in 1:length(which_vars))...)
                e = zeros(Int, n)
                for (k, v) in enumerate(which_vars)
                    e[v] = corner[k] == 1 ? degrees_nonzero[k] : 0
                end
                push!(supp, e)
            end
            newton_polytope(supp, n)
        end

        U_alpha_4d      = embed([64, 64], [1, 2], 4)
        V_alpha_4d      = embed([96, 96], [1, 2], 4)
        U_alphaprime_4d = embed([64, 64], [3, 4], 4)
        V_alphaprime_4d = embed([96, 96], [3, 4], 4)

        println("=" ^ 70)
        println("SCENARIO B: undecomposed 4x4 system (all four equations in x1..x4)")
        println("  (equations here still only involve 2 of the 4 variables each --")
        println("   only the AMBIENT dimension is 4; this is what an exact 4-way")
        println("   mixed volume gives if you do NOT exploit the block structure)")
        println("=" ^ 70)
        mv_full = inclusion_exclusion_mixed_volume(
            [U_alpha_4d, V_alpha_4d, U_alphaprime_4d, V_alphaprime_4d])
        println("  Mixed volume (BKK path bound), full 4-variable system: ", mv_full)
        println()

        println("=" ^ 70)
        println("Interpretation")
        println("=" ^ 70)
        println("  If the block structure is real: ~", 2 * mv_block, " paths total,")
        println("  tracked as two independent small homotopies.")
        println("  If solved as one undecomposed system without exploiting the")
        println("  block structure: ", mv_full, " paths -- ")
        println("  same equations, much worse bound, purely from not splitting.")
        println("  CONFIRM the block structure against the actual U/V equations")
        println("  before trusting either number as the real cost.")
        return
    end

    length(ARGS) == 4 ||
        error("hc_path_estimate.jl: expected 4 native support file paths " *
              "(U_alpha, V_alpha, U_alphaprime, V_alphaprime), or --box to " *
              "use the stated degree-box assumption instead. Got $(length(ARGS)) args.")

    println("Reading real support files -- this determines ground truth for")
    println("whether the equations are actually confined to 2 variables each")
    println("(i.e. whether the block-decomposition scenario is real) rather")
    println("than assumed.")
    println()

    paths = ARGS
    names = ["U_alpha", "V_alpha", "U_alphaprime", "V_alphaprime"]
    supports = Dict{String, Tuple{Vector{Vector{Int}}, Int}}()
    for (name, path) in zip(names, paths)
        println("Loading $name from $path ...")
        (supp, adim) = load_native_support(path)
        supports[name] = (supp, adim)

        # Check which variables actually appear (nonzero exponent anywhere)
        active_vars = Set{Int}()
        for e in supp
            for (i, ei) in enumerate(e)
                ei != 0 && push!(active_vars, i)
            end
        end
        println("  ambient_dim=$adim, n_terms=$(length(supp)), active variables (1-indexed): ",
                sort(collect(active_vars)))
    end
    println()

    println("Compare the 'active variables' lines above by hand:")
    println("  if U_alpha/V_alpha only ever show variables {1,2} and")
    println("  U_alphaprime/V_alphaprime only ever show {3,4}, the block")
    println("  decomposition (Scenario A above) is confirmed for real data --")
    println("  rerun with those two pairs through two_variable_mixed_volume")
    println("  directly for the exact path count.")
end

main()
