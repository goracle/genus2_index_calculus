#!/usr/bin/env julia
#
# newton_polytope.jl
#
# Newton polytope analysis toolkit for multivariate cryptanalysis.
#
# Purpose
# -------
# Given a multivariate polynomial (coefficients over any field/ring --
# coefficients themselves are irrelevant, only the monomial support matters),
# this module builds the Newton polytope of its exponent vectors and exposes
# dilation, lattice-point counting, and Ehrhart-polynomial functionality.
# The intended use is estimating the growth of Jochemsz-May multivariate
# Coppersmith lattices *without ever expanding polynomial powers* -- lattice
# dimension/volume growth under f^k is read off from k*Newton(f) instead.
#
# All convex-geometric work (convex hull, dimension, f-vector, volume,
# lattice-point counting, Ehrhart polynomial, Minkowski sum) is delegated to
# Oscar.jl's polymake-backed `Polyhedron` / `Polymake.polytope` machinery --
# no custom computational geometry is implemented here.
#
# Convention (matches elim2.jl): every failure mode raises an exception with
# a descriptive message (function name + what was expected + what was found).
# There are no silent fallbacks and no default-value swallowing of errors.

using Oscar

# ---------------------------------------------------------------------------
# 1. Support extraction
# ---------------------------------------------------------------------------

"""
    support(poly) -> Vector{Vector{Int}}

Return the exponent vectors of every monomial in `poly`, as plain
`Vector{Int}`s (constant term, if present, has the zero vector).

`poly` must be an Oscar/AbstractAlgebra multivariate polynomial
(`MPolyRingElem`). Delegates to Oscar's own `exponents` iterator rather than
re-deriving monomial exponents by hand.

Raises `ArgumentError` if `poly` is not a multivariate polynomial, or
`ErrorException` if `poly` has no terms (the zero polynomial has an
undefined Newton polytope).
"""
function support(poly)
    poly isa MPolyRingElem ||
        throw(ArgumentError("support: expected an Oscar/AbstractAlgebra " *
                             "multivariate polynomial (MPolyRingElem), got $(typeof(poly))"))

    exps = Vector{Vector{Int}}()
    for e in Oscar.exponents(poly)
        push!(exps, Int.(e))
    end

    isempty(exps) &&
        error("support: polynomial has zero terms (is it the zero polynomial?) " *
              "-- the Newton polytope of the zero polynomial is undefined")

    return exps
end

# ---------------------------------------------------------------------------
# 1b. Support from a native binary file (bypasses Oscar.load entirely)
# ---------------------------------------------------------------------------
#
# For polynomials too large to round-trip through Oscar.save/load (JSON
# deserialization builds a full parsed-DOM-plus-object-graph representation
# that OOMs well before any Newton-polytope-specific code runs), convert
# the .oscar/.mrdi file once with convert_to_native.jl, then load the
# resulting flat binary file with `load_native_support` below instead of
# ever calling `support(poly)` on a loaded polynomial.
#
# Matches convert_to_native.jl's "NEWTPOL1" v1 format exactly:
#   magic       :: UInt64
#   ambient_dim :: Int64
#   n_terms     :: Int64
#   exps        :: Int32, ambient_dim * n_terms values, row-major
#
# convert_to_native.jl can also write a "NEWTPOL2" v2 format (same header
# plus a UInt64 prime and a trailing UInt64-per-term coefficient block) when
# a prime modulus was given at conversion time -- that's for the numerical
# evaluation-interpolation approach, which needs actual coefficient values,
# not just monomial support. `load_native_support` below only ever reads the
# exponent block and works unchanged against either file (v2's extra prime
# field and trailing coefficient block are simply never read, since v2's
# header is byte-identical to v1's up through the exponent block, just with
# a different magic and one extra UInt64 -- the prime -- immediately after
# n_terms). `load_native_support_with_coeffs` is the v2-aware counterpart
# that also returns coefficients and the prime.

const NATIVE_SUPPORT_MAGIC = UInt64(0x4E455754504F4C31)     # "NEWTPOL1", must match convert_to_native.jl
const NATIVE_SUPPORT_MAGIC_V2 = UInt64(0x4E455754504F4C32)  # "NEWTPOL2", must match convert_to_native.jl
const NATIVE_SUPPORT_EXP_TYPE = Int32
const NATIVE_SUPPORT_COEFF_TYPE = UInt64

"""
    load_native_support(path) -> (support::Vector{Vector{Int}}, ambient_dim::Int)

Bulk-read a flat native binary exponent file (as produced by
`convert_to_native.jl`) and return the support as a `Vector{Vector{Int}}`,
ready to pass to `newton_polytope(supp, ambient_dim)` / `NewtonAnalyzer(supp,
ambient_dim)`. This never touches Oscar's JSON serialization machinery.

Raises an exception if the file's magic header doesn't match (wrong format
or corrupt file) or if the recorded array length is inconsistent with the
header's term count / ambient dimension.
"""
function load_native_support(path::String)
    isfile(path) ||
        error("load_native_support: no such file: $path")

    fsize_mb = filesize(path) / 1024 / 1024
    println("  load_native_support: reading ", path, " (", round(fsize_mb, digits=1), " MB on disk)...")
    flush(stdout)

    (ambient_dim, n_terms, flat) = open(path, "r") do io
        magic = read(io, UInt64)
        magic == NATIVE_SUPPORT_MAGIC || magic == NATIVE_SUPPORT_MAGIC_V2 ||
            error("load_native_support: $path does not have the expected " *
                  "NEWTPOL1/NEWTPOL2 native-format header (got magic=$(magic), " *
                  "expected $(NATIVE_SUPPORT_MAGIC) or $(NATIVE_SUPPORT_MAGIC_V2)) " *
                  "-- this is not a file produced by convert_to_native.jl, or it " *
                  "is corrupt")
        is_v2 = magic == NATIVE_SUPPORT_MAGIC_V2
        adim = read(io, Int64)
        adim > 0 ||
            error("load_native_support: $path has ambient_dim=$adim in its " *
                  "header, expected a positive integer")
        nt = read(io, Int64)
        nt > 0 ||
            error("load_native_support: $path has n_terms=$nt in its header, " *
                  "expected a positive integer")
        # v2 has one extra UInt64 (the prime) between n_terms and the
        # exponent block -- skip past it, since this function only wants the
        # support (use load_native_support_with_coeffs for the coefficients).
        is_v2 && read(io, UInt64)
        flat_exps = Vector{NATIVE_SUPPORT_EXP_TYPE}(undef, adim * nt)
        read!(io, flat_exps)
        # v2 also has a trailing coefficient block after the exponent block,
        # but since this is the last thing read from the file and we never
        # read it, it's simply left unread -- no need to skip past it.
        (adim, nt, flat_exps)
    end

    length(flat) == ambient_dim * n_terms ||
        error("load_native_support: corrupt file $path -- flat exponent array " *
              "has length $(length(flat)), expected ambient_dim*n_terms = " *
              "$ambient_dim*$n_terms = $(ambient_dim * n_terms)")

    supp = Vector{Vector{Int}}(undef, n_terms)
    @inbounds for i in 1:n_terms
        base = (i - 1) * ambient_dim
        supp[i] = Int[flat[base + j] for j in 1:ambient_dim]
    end

    println("  load_native_support: loaded ", n_terms, " terms, ambient_dim=", ambient_dim)
    return (supp, ambient_dim)
end

"""
    load_native_support_with_coeffs(path) ->
        (support::Vector{Vector{Int}}, coeffs::Vector{UInt64}, ambient_dim::Int, prime::UInt64)

Bulk-read a "NEWTPOL2" v2 native binary file (as produced by
`convert_to_native.jl` when given a prime modulus) and return both the
support and the coefficients (as canonical residues mod `prime`, in the
same term order), ready for numerical evaluation/interpolation.

Raises if `path` is a v1 ("NEWTPOL1") file -- those were never written with
coefficients, so there is nothing here to return; use `load_native_support`
for that case instead.
"""
function load_native_support_with_coeffs(path::String)
    isfile(path) ||
        error("load_native_support_with_coeffs: no such file: $path")

    fsize_mb = filesize(path) / 1024 / 1024
    println("  load_native_support_with_coeffs: reading ", path, " (",
            round(fsize_mb, digits=1), " MB on disk)...")
    flush(stdout)

    (ambient_dim, n_terms, prime, flat_exps, flat_coeffs) = open(path, "r") do io
        magic = read(io, UInt64)
        magic == NATIVE_SUPPORT_MAGIC_V2 ||
            error("load_native_support_with_coeffs: $path does not have the " *
                  "expected NEWTPOL2 native-format header (got magic=$(magic), " *
                  "expected $(NATIVE_SUPPORT_MAGIC_V2)) -- this converter only " *
                  "wrote coefficients for files converted with a prime given " *
                  "on the command line; if this is a NEWTPOL1 (v1, magic=" *
                  "$(NATIVE_SUPPORT_MAGIC)) file, re-run convert_to_native.jl " *
                  "with a prime argument to get coefficients, or use " *
                  "load_native_support if you only need the support")
        adim = read(io, Int64)
        adim > 0 ||
            error("load_native_support_with_coeffs: $path has ambient_dim=$adim " *
                  "in its header, expected a positive integer")
        nt = read(io, Int64)
        nt > 0 ||
            error("load_native_support_with_coeffs: $path has n_terms=$nt in " *
                  "its header, expected a positive integer")
        p = read(io, UInt64)
        p > 1 ||
            error("load_native_support_with_coeffs: $path has prime=$p in its " *
                  "header, expected a modulus > 1")
        flat_exps = Vector{NATIVE_SUPPORT_EXP_TYPE}(undef, adim * nt)
        read!(io, flat_exps)
        flat_coeffs = Vector{NATIVE_SUPPORT_COEFF_TYPE}(undef, nt)
        read!(io, flat_coeffs)
        (adim, nt, p, flat_exps, flat_coeffs)
    end

    length(flat_exps) == ambient_dim * n_terms ||
        error("load_native_support_with_coeffs: corrupt file $path -- flat " *
              "exponent array has length $(length(flat_exps)), expected " *
              "ambient_dim*n_terms = $ambient_dim*$n_terms = $(ambient_dim * n_terms)")
    length(flat_coeffs) == n_terms ||
        error("load_native_support_with_coeffs: corrupt file $path -- " *
              "coefficient array has length $(length(flat_coeffs)), expected " *
              "n_terms = $n_terms")

    supp = Vector{Vector{Int}}(undef, n_terms)
    @inbounds for i in 1:n_terms
        base = (i - 1) * ambient_dim
        supp[i] = Int[flat_exps[base + j] for j in 1:ambient_dim]
    end

    println("  load_native_support_with_coeffs: loaded ", n_terms,
            " terms, ambient_dim=", ambient_dim, ", prime=", prime)
    return (supp, flat_coeffs, ambient_dim, prime)
end

# ---------------------------------------------------------------------------
# 2. Newton polytope construction
# ---------------------------------------------------------------------------

"""
    NewtonPolytope

Wraps an Oscar `Polyhedron` together with the ambient dimension and the
exponent-vector support it was built from, so downstream functions don't
need to re-derive them.

Fields:
- `polyhedron :: Polyhedron`   -- the Oscar/Polymake convex hull object
- `ambient_dim :: Int`         -- number of variables in the source ring
- `support :: Vector{Vector{Int}}` -- exponent vectors used to build the hull
"""
struct NewtonPolytope
    polyhedron::Oscar.Polyhedron
    ambient_dim::Int
    support::Vector{Vector{Int}}
end

"""
    newton_polytope(poly) -> NewtonPolytope
    newton_polytope(supp::Vector{Vector{Int}}, ambient_dim::Int) -> NewtonPolytope

Construct the Newton polytope (convex hull of the monomial support) of a
polynomial, or directly from a precomputed list of exponent vectors.

Convex hull computation is delegated entirely to Oscar's `convex_hull`,
which is backed by polymake -- no manual hull algorithm is implemented here.

Raises an exception if the support is empty, or if the exponent vectors are
not all of the same length (inconsistent ambient dimension).
"""
function newton_polytope(poly)
    supp = support(poly)
    return newton_polytope(supp, nvars(parent(poly)))
end

function newton_polytope(supp::Vector{Vector{Int}}, ambient_dim::Int;
                          prefilter::Bool=false)
    isempty(supp) &&
        error("newton_polytope: empty support -- cannot construct a Newton " *
              "polytope with no monomials")

    for (i, v) in enumerate(supp)
        length(v) == ambient_dim ||
            throw(ArgumentError("newton_polytope: exponent vector at index $i has " *
                                 "length $(length(v)), expected ambient_dim=$ambient_dim " *
                                 "-- all monomials must live in the same polynomial ring"))
    end

    hull_input = supp
    if prefilter
        hull_input = prefilter_extreme_candidates(supp, ambient_dim)
    end
    n = length(hull_input)

    # Build the points matrix as ONE preallocated Matrix{Int} filled in
    # place, rather than `reduce(vcat, [permutedims(v) for v in supp])`,
    # which for n in the tens-of-millions allocates n temporary 1xd
    # matrices (each its own small heap object) and then repeatedly
    # reallocates/copies a growing matrix on every vcat step -- the exact
    # "many small heap objects" pattern flagged elsewhere in this project
    # (see elim2.jl's save_shard_native comments) as a major, avoidable
    # memory/time cost independent of the final data size.
    println("  newton_polytope: building ", n, "x", ambient_dim,
            " points matrix (single preallocated array, no per-row allocation)",
            prefilter ? " [prefiltered from $(length(supp))]" : "", "...")
    flush(stdout)
    M = Matrix{Int}(undef, n, ambient_dim)
    @inbounds for i in 1:n
        v = hull_input[i]
        for j in 1:ambient_dim
            M[i, j] = v[j]
        end
    end

    n > 200_000 &&
        @warn "newton_polytope: constructing an exact convex hull from $n input " *
              "points. polymake's hull algorithm is not designed to scale to " *
              "tens of millions of points -- if this hangs or OOMs, pass " *
              "prefilter=true to reduce the candidate set first (see " *
              "prefilter_extreme_candidates in this file for exactness caveats)."

    P = try
        convex_hull(M)
    catch e
        error("newton_polytope: Oscar.convex_hull failed on $n points " *
              "in dimension $ambient_dim -- underlying error: $e")
    end

    return NewtonPolytope(P, ambient_dim, supp)
end

# ---------------------------------------------------------------------------
# Pre-filtering for huge support sets
# ---------------------------------------------------------------------------
#
# For a degree-D polynomial in `ambient_dim` variables, the number of
# SUPPORT monomials can be enormous (tens of millions here), but the number
# of VERTICES of the Newton polytope is typically minuscule by comparison --
# only points that are extreme in some direction can be vertices. Handing
# polymake the full multi-million-point set is both a memory problem and an
# algorithmic-scaling problem (exact hull algorithms are not designed for
# this many input points); the fix is to shrink the candidate set FIRST,
# using a method that is provably safe (never discards an actual vertex),
# before calling convex_hull at all.
#
# Method: linear-functional extremization. For a convex hull, a point p is
# NOT a vertex only if it can be written as a convex combination of other
# points -- equivalently, p is a vertex if and only if there EXISTS some
# linear functional c such that p uniquely maximizes c . x over the point
# set. So: pick a battery of directions c (all +-1 combinations of unit
# axis vectors covers all "corner-ish" directions relevant to a polytope
# whose points already lie in the non-negative orthant, as monomial
# exponent vectors always do) and keep the argmax (and argmin, for
# completeness / lower faces) of each. This is a single O(n * ambient_dim)
# pass per direction -- linear in the huge n, not combinatorial -- and is
# exact in the sense that every TRUE vertex is guaranteed to maximize (or
# minimize) at least one such functional for a full-dimensional generic
# polytope; for degenerate/non-generic cases this is a conservative
# over-approximation (keeps candidates that turn out non-extreme, which
# convex_hull then correctly discards) rather than ever silently dropping a
# real vertex. If Oscar/polymake's own convex_hull still discards points
# not on the hull -- which it does, by definition -- feeding it this
# filtered candidate set produces the SAME polytope as feeding it the full
# support, just far faster.
#
# NOTE ON EXACTNESS: this uses the 2^ambient_dim signed-axis directions
# (all-positive picks the coordinatewise max point, etc.) plus each single
# axis direction and its negation. For ambient_dim=4 that's 16 + 8 = 24
# directions, i.e. at most 48 candidate points (some directions will tie on
# the same point). This is NOT guaranteed to capture every vertex of an
# arbitrary high-dimensional polytope in general position -- only vertices
# that are extreme along one of these specific directions are guaranteed to
# survive. Use `prefilter_extreme_candidates` as a fast first pass when you
# expect the answer to still be correct (e.g. verified via the spot-check
# pattern below), NOT as a mathematically complete substitute for a real
# hull algorithm. If you need a guarantee of capturing every vertex, either
# run convex_hull on the full support (accepting the memory/time cost) or
# add more directions (e.g. random rational directions) and re-check
# stability of the resulting vertex set as more directions are added.
"""
    prefilter_extreme_candidates(supp::Vector{Vector{Int}}, ambient_dim::Int) -> Vector{Vector{Int}}

Reduce a (possibly huge) support set to a much smaller candidate set that is
guaranteed to contain every point extremal along an axis-aligned or
all-signed-axis-combination direction. See the module-level comment above
this function for exactness caveats -- this is a fast heuristic pre-filter,
not a certified-complete vertex enumeration.

Raises `ArgumentError` for an empty support.
"""
function prefilter_extreme_candidates(supp::Vector{Vector{Int}}, ambient_dim::Int)
    isempty(supp) &&
        throw(ArgumentError("prefilter_extreme_candidates: empty support"))

    n = length(supp)
    println("  prefilter_extreme_candidates: scanning ", n, " points across ",
             "signed-axis-combination directions...")
    flush(stdout)

    candidates = Set{Vector{Int}}()

    # Single-axis directions: e_j and -e_j for each coordinate j.
    for j in 1:ambient_dim
        best_max_val = typemin(Int)
        best_max_pt = supp[1]
        best_min_val = typemax(Int)
        best_min_pt = supp[1]
        @inbounds for v in supp
            val = v[j]
            if val > best_max_val
                best_max_val = val
                best_max_pt = v
            end
            if val < best_min_val
                best_min_val = val
                best_min_pt = v
            end
        end
        push!(candidates, best_max_pt)
        push!(candidates, best_min_pt)
    end

    # All-signed-axis-combination directions: c in {-1,+1}^ambient_dim,
    # maximize c . x. There are 2^ambient_dim of these; for ambient_dim=4
    # that's 16, fine, but this function raises rather than silently
    # exploding for large ambient_dim.
    ambient_dim > 20 &&
        error("prefilter_extreme_candidates: ambient_dim=$ambient_dim would " *
              "require 2^$ambient_dim signed-direction passes -- this function " *
              "is only intended for the small ambient_dim (4) this project " *
              "actually uses; extend it deliberately (e.g. random-direction " *
              "sampling) rather than let it silently blow up for higher dim")

    for mask in 0:(2^ambient_dim - 1)
        signs = [((mask >> (j - 1)) & 1 == 1) ? 1 : -1 for j in 1:ambient_dim]
        best_val = typemin(Int)
        best_pt = supp[1]
        @inbounds for v in supp
            val = 0
            for j in 1:ambient_dim
                val += signs[j] * v[j]
            end
            if val > best_val
                best_val = val
                best_pt = v
            end
        end
        push!(candidates, best_pt)
    end

    result = collect(candidates)
    println("  prefilter_extreme_candidates: reduced ", n, " points to ",
             length(result), " candidates")
    return result
end

# ---------------------------------------------------------------------------
# Basic polytope accessors
# ---------------------------------------------------------------------------

"""
    ambient_dimension(A::NewtonPolytope) -> Int

Dimension of the ambient space (= number of ring variables), as opposed to
the polytope's own (possibly lower) dimension -- see `polytope_dimension`.
"""
ambient_dimension(A::NewtonPolytope) = A.ambient_dim

"""
    polytope_dimension(A::NewtonPolytope) -> Int

Dimension of the Newton polytope itself. Can be strictly less than
`ambient_dimension(A)` if the support is not full-dimensional (e.g. a
polynomial missing some variable, or one lying in an affine subspace).
Delegates to Oscar's `dim`.
"""
function polytope_dimension(A::NewtonPolytope)
    try
        return dim(A.polyhedron)
    catch e
        error("polytope_dimension: Oscar.dim failed on the underlying " *
              "polyhedron -- underlying error: $e")
    end
end

"""
    vertices_of(A::NewtonPolytope) -> Vector{Vector{QQFieldElem}}

Vertices of the Newton polytope (a subset of the original support -- convex
hull may discard non-extreme monomials). Delegates to Oscar's `vertices`.
"""
function vertices_of(A::NewtonPolytope)
    try
        return [Vector(v) for v in vertices(A.polyhedron)]
    catch e
        error("vertices_of: Oscar.vertices failed on the underlying " *
              "polyhedron -- underlying error: $e")
    end
end

"""
    f_vector_of(A::NewtonPolytope) -> Vector{Int}

The f-vector (number of faces of each dimension, 0-faces=vertices through
top-dimensional faces) of the Newton polytope, if polymake can compute it.
Delegates to Oscar's `f_vector`.

Raises an exception (rather than returning a placeholder) if polymake
cannot compute it for this polytope.
"""
function f_vector_of(A::NewtonPolytope)
    try
        return Int.(f_vector(A.polyhedron))
    catch e
        error("f_vector_of: Oscar.f_vector failed on the underlying " *
              "polyhedron -- underlying error: $e")
    end
end

"""
    normalized_volume_of(A::NewtonPolytope) -> QQFieldElem

Normalized (polymake convention: lattice-normalized, i.e. `dim! * volume`)
volume of the Newton polytope. Delegates to Oscar's `normalized_volume`.

Raises an exception if the polytope is not full-dimensional in its own
affine hull in a way that makes normalized volume ill-posed for the current
Oscar/Polymake version, rather than silently returning zero.
"""
function normalized_volume_of(A::NewtonPolytope)
    try
        return normalized_volume(A.polyhedron)
    catch e
        error("normalized_volume_of: Oscar.normalized_volume failed on the " *
              "underlying polyhedron (polytope_dimension=$(polytope_dimension(A)), " *
              "ambient_dimension=$(A.ambient_dim)) -- underlying error: $e")
    end
end

# ---------------------------------------------------------------------------
# 3. Dilation
# ---------------------------------------------------------------------------

"""
    dilate(A::NewtonPolytope, k::Integer) -> NewtonPolytope

Construct kP for the Newton polytope P = A.polyhedron, using Oscar's
polytope scaling (`k * P`), which is a pure polytope operation -- this never
touches or expands the original polynomial's powers.

Valid for k = 1,...,6 as specified; larger k is not rejected outright (the
underlying polymake scaling has no such limit) but a k outside 1:6 emits no
special handling beyond the general validity checks below, since the task
only requires small-k support.

Raises `ArgumentError` for non-positive k.
"""
function dilate(A::NewtonPolytope, k::Integer)
    k >= 1 ||
        throw(ArgumentError("dilate: dilation factor k must be a positive integer, got k=$k"))

    Pk = try
        k * A.polyhedron
    catch e
        error("dilate: Oscar polytope scaling (k * polyhedron) failed for k=$k " *
              "-- underlying error: $e")
    end

    # The dilated support (k * original exponent vectors) -- kept for
    # bookkeeping/printing; the *vertices* of kP are recomputed by polymake
    # from Pk itself, this is just a convenient parallel record.
    dilated_supp = [k .* v for v in A.support]

    return NewtonPolytope(Pk, A.ambient_dim, dilated_supp)
end

# ---------------------------------------------------------------------------
# 4. Lattice-point counting
# ---------------------------------------------------------------------------

"""
    lattice_points_of(A::NewtonPolytope; method::Symbol=:ehrhart) -> Int

Total number of integer lattice points contained in the Newton polytope
(inclusive of the boundary), i.e. L_P(1) where L_P is the Ehrhart
polynomial.

`method`:
  - `:ehrhart` (default) -- evaluate the Ehrhart polynomial at k=1. This is
    a closed-form polynomial evaluation, NOT an enumeration -- for a
    polytope with a large normalized volume (as is expected here, given the
    support has tens of millions of points), polymake's brute-force
    `lattice_points` enumerator materializes every point as an explicit
    object and predictably runs out of memory (confirmed: `std::bad_alloc`
    in polymake's `LATTICE_POINTS_GENERATORS` rule at this project's actual
    polytope scale). The Ehrhart polynomial gives the exact same integer
    without ever constructing the point list.
  - `:enumerate` -- the old brute-force path via Oscar's `lattice_points`.
    Only use this for small polytopes (say, normalized volume well under
    10^6) where you actually want the point list itself, not just the
    count. Raises the underlying polymake error rather than silently
    falling back to `:ehrhart` -- an OOM here should surface as an OOM to
    fix (use `:ehrhart` or `:enumerate` deliberately), not something this
    function hides from you.
"""
function lattice_points_of(A::NewtonPolytope; method::Symbol=:ehrhart)
    if method == :ehrhart
        L = ehrhart_polynomial_of(A)
        return Int(evaluate(L, 1))
    elseif method == :enumerate
        pts = try
            lattice_points(A.polyhedron)
        catch e
            error("lattice_points_of: Oscar.lattice_points (brute enumeration) " *
                  "failed on the underlying polyhedron -- if the polytope has a " *
                  "large normalized volume this is an expected OOM/resource " *
                  "failure, not a bug; use method=:ehrhart instead (the default) " *
                  "for an exact count without enumerating points. Underlying " *
                  "error: $e")
        end
        return length(pts)
    else
        throw(ArgumentError("lattice_points_of: unknown method=$method, " *
                             "expected :ehrhart or :enumerate"))
    end
end

"""
    lattice_points_of(A::NewtonPolytope, k::Integer; method::Symbol=:ehrhart) -> Int

Number of lattice points in kP.

`method=:ehrhart` (default) evaluates the Ehrhart polynomial at k directly
-- this is the whole point of having computed it, and is dramatically
cheaper than `method=:enumerate`, which dilates the polytope via `dilate`
and then brute-force enumerates (only recommended for small k / small
volume, same caveats as the k=1 case above).
"""
function lattice_points_of(A::NewtonPolytope, k::Integer; method::Symbol=:ehrhart)
    if method == :ehrhart
        L = ehrhart_polynomial_of(A)
        return Int(evaluate(L, k))
    elseif method == :enumerate
        return lattice_points_of(dilate(A, k); method=:enumerate)
    else
        throw(ArgumentError("lattice_points_of: unknown method=$method, " *
                             "expected :ehrhart or :enumerate"))
    end
end

# ---------------------------------------------------------------------------
# 5. Ehrhart polynomial
# ---------------------------------------------------------------------------

"""
    ehrhart_polynomial_of(A::NewtonPolytope)

Compute the Ehrhart polynomial L_P(k) of the Newton polytope, whose value at
a positive integer k equals the number of lattice points in kP. Delegates
to Oscar's `ehrhart_polynomial`.

This is preferred over repeated `lattice_points_of(A, k)` calls for
understanding growth, since it gives the closed-form growth law directly
(leading coefficient = normalized volume / dim!).

Raises an exception if Oscar/Polymake cannot compute the Ehrhart polynomial
for this polytope (e.g. it requires the polytope to be a lattice polytope --
non-integral vertices will fail here rather than silently rounding).
"""
function ehrhart_polynomial_of(A::NewtonPolytope)
    try
        return ehrhart_polynomial(A.polyhedron)
    catch e
        error("ehrhart_polynomial_of: Oscar.ehrhart_polynomial failed on the " *
              "underlying polyhedron -- this requires a lattice polytope; " *
              "underlying error: $e")
    end
end

# ---------------------------------------------------------------------------
# 6. Minkowski sums
# ---------------------------------------------------------------------------

"""
    minkowski_sum(P::NewtonPolytope, Q::NewtonPolytope) -> NewtonPolytope

Minkowski sum P + Q, delegated to Oscar's `minkowski_sum` (polytope
operation, never touches polynomial coefficients or expands powers).

Raises `ArgumentError` if P and Q have different ambient dimensions --
Minkowski sum is only defined for polytopes living in the same space.
"""
function minkowski_sum(P::NewtonPolytope, Q::NewtonPolytope)
    P.ambient_dim == Q.ambient_dim ||
        throw(ArgumentError("minkowski_sum: ambient dimension mismatch " *
                             "($(P.ambient_dim) vs $(Q.ambient_dim)) -- both " *
                             "polytopes must live in the same space"))

    S = try
        Oscar.minkowski_sum(P.polyhedron, Q.polyhedron)
    catch e
        error("minkowski_sum: Oscar.minkowski_sum failed -- underlying error: $e")
    end

    # Support of a Minkowski sum is (up to convex hull) the pairwise sums;
    # record it for bookkeeping consistency with the `dilate` convention.
    combined_supp = vec([p .+ q for p in P.support, q in Q.support])

    return NewtonPolytope(S, P.ambient_dim, combined_supp)
end

# `dilate` via repeated Minkowski sums is available as an explicit
# alternative implementation for verification/testing purposes -- the
# primary `dilate` above uses direct polytope scaling (k * P), which is the
# standard and more efficient route and is what NewtonAnalyzer uses.
"""
    dilate_by_minkowski(A::NewtonPolytope, k::Integer) -> NewtonPolytope

Alternative implementation of `dilate` via k-fold repeated Minkowski
summation (P + P + ... + P), rather than direct scalar polytope scaling.
Mathematically equivalent to `dilate(A, k)` for convex P (Newton polytopes
are always convex by construction) -- provided mainly so the two routes can
be cross-checked against each other.

Raises `ArgumentError` for non-positive k.
"""
function dilate_by_minkowski(A::NewtonPolytope, k::Integer)
    k >= 1 ||
        throw(ArgumentError("dilate_by_minkowski: dilation factor k must be " *
                             "a positive integer, got k=$k"))

    result = A
    for _ in 2:k
        result = minkowski_sum(result, A)
    end
    return result
end

# ---------------------------------------------------------------------------
# 7. Growth report
# ---------------------------------------------------------------------------

"""
    print_vertices(A::NewtonPolytope)

Print every vertex of the Newton polytope, one per line, sorted
lexicographically for readability. Also runs `detect_box_structure` and
prints its verdict, since with only a handful of vertices (as is the case
for the resultants this project works with) the natural next question is
whether the polytope is exactly an axis-aligned box (or a translate of
one), and if so, what the side lengths are.
"""
function print_vertices(A::NewtonPolytope)
    verts = vertices_of(A)
    sorted_verts = sort(verts)

    println("Vertices (", length(sorted_verts), " total, sorted lexicographically):")
    for v in sorted_verts
        coords = join(string.(v), ", ")
        println("  (", coords, ")")
    end
    println()

    verdict = detect_box_structure(A)
    println("Box structure check:")
    if verdict.is_box
        println("  MATCH: exact axis-aligned box.")
        println("  origin (min corner): (", join(string.(verdict.origin), ", "), ")")
        println("  side lengths:        (", join(string.(verdict.side_lengths), ", "), ")")
    else
        println("  NOT an axis-aligned box: ", verdict.reason)
    end
    println()

    return nothing
end

"""
    detect_box_structure(A::NewtonPolytope)

Check whether the Newton polytope's vertex set is exactly the vertex set of
an axis-aligned box, i.e. `{origin[j] or origin[j]+side_lengths[j] : j in
1:d}` for every one of the `2^d` sign combinations, with no missing and no
extra vertices.

Returns a NamedTuple `(is_box, origin, side_lengths, reason)`. `origin` and
`side_lengths` are only meaningful when `is_box == true`; `reason` is only
meaningful when `is_box == false`.

This is a direct combinatorial check (not a heuristic): it computes the
coordinatewise min/max across the actual vertex set, generates the
resulting box's expected 2^d corner set, and verifies it against the actual
vertex set exactly (same count, same points, no more no less). It does NOT
check for the more general "affine image of a box under a unimodular
integer matrix" (parallelotope) case GPT raised as the fallback
possibility -- that requires solving for a transform matrix and is left as
a manual follow-up if this exact-box check comes back false.
"""
function detect_box_structure(A::NewtonPolytope)
    verts_raw = vertices_of(A)
    d = A.ambient_dim

    n_expected = 2^d
    length(verts_raw) == n_expected ||
        return (is_box=false, origin=nothing, side_lengths=nothing,
                reason="vertex count is $(length(verts_raw)), expected 2^$d=$n_expected " *
                       "for an axis-aligned box in $d dimensions")

    # Oscar/Polymake vertices are QQFieldElem by type (rational), even when
    # the actual values are integers -- monomial exponent vectors are
    # always integral, so coerce explicitly here rather than propagating
    # QQFieldElem into plain-Int range/Set machinery downstream (which
    # errors opaquely, as happened before this fix). A genuinely
    # non-integral vertex coordinate would mean the "box" claim is wrong in
    # a more fundamental way than a type nuisance, so this raises rather
    # than silently rounding.
    verts = Vector{Vector{Int}}(undef, length(verts_raw))
    for (i, v) in enumerate(verts_raw)
        coords = Vector{Int}(undef, d)
        for j in 1:d
            isinteger(v[j]) ||
                error("detect_box_structure: vertex $i has non-integral coordinate " *
                      "$(v[j]) in dimension $j -- exponent-vector Newton polytopes " *
                      "should always have integer vertices; this indicates either a " *
                      "bug upstream or a genuinely surprising non-lattice vertex " *
                      "that needs manual investigation, not silent rounding")
            coords[j] = Int(v[j])
        end
        verts[i] = coords
    end

    origin = [minimum(v[j] for v in verts) for j in 1:d]
    top = [maximum(v[j] for v in verts) for j in 1:d]
    side_lengths = top .- origin

    any(side_lengths .== 0) &&
        return (is_box=false, origin=nothing, side_lengths=nothing,
                reason="coordinatewise range is zero in at least one direction " *
                       "(side_lengths=$side_lengths) -- polytope is not full-" *
                       "dimensional as a box in $d dimensions")

    expected_corners = Set{Vector{Int}}()
    for mask in 0:(n_expected - 1)
        corner = [((mask >> (j - 1)) & 1 == 1) ? top[j] : origin[j] for j in 1:d]
        push!(expected_corners, corner)
    end

    actual_corners = Set(verts)

    if expected_corners == actual_corners
        return (is_box=true, origin=origin, side_lengths=side_lengths, reason="")
    else
        missing = setdiff(expected_corners, actual_corners)
        extra = setdiff(actual_corners, expected_corners)
        return (is_box=false, origin=nothing, side_lengths=nothing,
                reason="vertex set does not match the expected $n_expected box " *
                       "corners exactly -- $(length(missing)) expected corner(s) " *
                       "absent, $(length(extra)) unexpected vertex/vertices present " *
                       "(so it may still be a parallelotope: an affine/unimodular " *
                       "image of a box, which this check does not detect)")
    end
end

# ---------------------------------------------------------------------------
# Missing lattice points (box case only)
# ---------------------------------------------------------------------------
#
# Once `detect_box_structure` confirms the Newton polytope is exactly an
# axis-aligned box [origin[1],origin[1]+L1] x ... x [origin[d],origin[d]+Ld],
# the full set of lattice points in that box is just the Cartesian product
# of d integer ranges -- no polymake, no convex hull, no Ehrhart machinery
# needed. This is a plain nested-loop enumeration with total point count
# equal to the box's exact lattice-point count (e.g. 65^4 ~ 17.85M for a
# [0,64]^4 box), held as a Set for O(1) membership testing against the
# actual support -- both scales comfortably in memory (this is a set of
# small tuples, not a set of heap-heavy Julia objects with per-term
# metadata, unlike the failure modes seen earlier in this project).
"""
    missing_lattice_points(A::NewtonPolytope) -> Vector{Vector{Int}}

Requires the polytope to be an exact axis-aligned box (verified via
`detect_box_structure` -- raises if it is not). Returns every lattice point
inside `[origin[1], origin[1]+L1] x ... x [origin[d], origin[d]+Ld]` that is
NOT present in `A.support`, sorted lexicographically.

This is a direct enumerate-and-diff, not a heuristic: it is exact by
construction given that the box hypothesis holds. If `A` is not a box, use
`detect_box_structure(A)` to see why before calling this.
"""
function missing_lattice_points(A::NewtonPolytope)
    verdict = detect_box_structure(A)
    verdict.is_box ||
        error("missing_lattice_points: the Newton polytope is not an exact " *
              "axis-aligned box (detect_box_structure reported: " *
              "$(verdict.reason)) -- this function only applies to the " *
              "confirmed-box case; a general polytope needs a different " *
              "(non-box) lattice enumeration, e.g. dilate(A,1) + brute " *
              "lattice_points_of(..., method=:enumerate) if memory allows")

    origin = verdict.origin
    side_lengths = verdict.side_lengths
    d = A.ambient_dim

    ranges = [origin[j]:(origin[j] + side_lengths[j]) for j in 1:d]
    total_box_points = prod(length.(ranges))
    println("  missing_lattice_points: enumerating ", total_box_points,
             " box lattice points across ranges ", ranges, "...")
    flush(stdout)

    present = Set(A.support)
    missing = Vector{Vector{Int}}()

    # Nested nested loop for arbitrary d via CartesianIndices, so this isn't
    # hardcoded to d=4 even though that's what this project currently uses.
    dims = length.(ranges)
    for ci in CartesianIndices(Tuple(dims))
        pt = [ranges[j][ci[j]] for j in 1:d]
        if !(pt in present)
            push!(missing, pt)
        end
    end

    sort!(missing)
    println("  missing_lattice_points: ", length(missing), " missing out of ",
             total_box_points, " (", round(100 * length(missing) / total_box_points, sigdigits=3), "% missing)")

    return missing
end

"""
    print_missing_lattice_points(A)

Convenience wrapper: computes `missing_lattice_points(A)` and prints each
missing point, one per line. Works on either `NewtonPolytope` or
`NewtonAnalyzer`.
"""
function print_missing_lattice_points(A)
    missing = missing_lattice_points(A)
    println("Missing lattice points (", length(missing), " total):")
    for pt in missing
        println("  (", join(string.(pt), ", "), ")")
    end
    return missing
end

# ---------------------------------------------------------------------------
# 7. Growth report
# ---------------------------------------------------------------------------

"""
    summary(A::NewtonPolytope; max_k::Integer=6)

Print a human-readable growth report: ambient/polytope dimension, support
size, vertex coordinates (with a box-structure check), normalized volume,
Ehrhart polynomial (if computable), and lattice-point counts (with growth
ratios) for k = 1,...,max_k.

Growth ratios are printed as floating point for readability but are derived
from exact lattice-point counts.
"""
function summary(A::NewtonPolytope; max_k::Integer=6)
    max_k >= 1 ||
        throw(ArgumentError("summary: max_k must be a positive integer, got max_k=$max_k"))

    println("Ambient dimension: ", A.ambient_dim)
    println("Polytope dimension: ", polytope_dimension(A))
    println()
    println("Number of support monomials: ", length(A.support))
    println()

    print_vertices(A)

    try
        println("Normalized volume: ", normalized_volume_of(A))
    catch e
        println("Normalized volume: <unavailable -- ", e, ">")
    end
    println()

    ehrhart_str = try
        string(ehrhart_polynomial_of(A))
    catch e
        "<unavailable -- $e>"
    end
    println("Ehrhart polynomial:")
    println("  ", ehrhart_str)
    println()

    counts = Int[]
    for k in 1:max_k
        n = lattice_points_of(A, k)
        push!(counts, n)
        println("k = $k")
        println("  lattice points = $n")
    end
    println()

    println("Growth ratios:")
    for i in 2:length(counts)
        prev, cur = counts[i-1], counts[i]
        ratio = prev == 0 ? "undefined (division by zero at k=$(i-1))" : string(round(cur / prev, digits=4))
        println("  k=$(i-1) -> k=$i : $ratio")
    end

    return nothing
end

# ---------------------------------------------------------------------------
# 8. Clean API: NewtonAnalyzer
# ---------------------------------------------------------------------------

"""
    NewtonAnalyzer

Thin, ergonomic wrapper around `NewtonPolytope` matching the requested API
shape (`summary(A)`, `vertices(A)`, `volume(A)`, `ehrhart(A)`,
`lattice_points(A,k)`, `dilate(A,k)`, `plot(A)`).

Construct with either a polynomial or a raw (support, ambient_dim) pair:

    A = NewtonAnalyzer(poly)
    A = NewtonAnalyzer(supp, ambient_dim)
    A = NewtonAnalyzer(supp, ambient_dim; prefilter=true)  # for huge supports
"""
struct NewtonAnalyzer
    np::NewtonPolytope
end

NewtonAnalyzer(poly) = NewtonAnalyzer(newton_polytope(poly))
NewtonAnalyzer(supp::Vector{Vector{Int}}, ambient_dim::Int; prefilter::Bool=false) =
    NewtonAnalyzer(newton_polytope(supp, ambient_dim; prefilter=prefilter))

"""
    NewtonAnalyzer(native_path::String; prefilter::Bool=false) -> NewtonAnalyzer

Construct directly from a flat native binary exponent file produced by
`convert_to_native.jl` (see `load_native_support`). This is the entry point
for polynomials too large to load through `Oscar.load`.

Pass `prefilter=true` when the support is too large (tens of millions of
points) for polymake's exact convex hull to handle directly -- see
`prefilter_extreme_candidates` for what this trades away.
"""
function NewtonAnalyzer(native_path::String; prefilter::Bool=false)
    (supp, ambient_dim) = load_native_support(native_path)
    return NewtonAnalyzer(supp, ambient_dim; prefilter=prefilter)
end

# Method extensions on top of the already-imported Oscar generics
# (`vertices`, `dim`, `Base.summary`, etc. all live in Base/Oscar's
# namespace already, so these are added as new methods rather than
# redefinitions of unrelated functions).

"""
    summary(A::NewtonAnalyzer; max_k::Integer=6)

See `summary(::NewtonPolytope)`.
"""
summary(A::NewtonAnalyzer; max_k::Integer=6) = summary(A.np; max_k=max_k)

"""
    vertices(A::NewtonAnalyzer)

Vertices of the underlying Newton polytope. See `vertices_of`.
"""
Oscar.vertices(A::NewtonAnalyzer) = vertices_of(A.np)

"""
    print_vertices(A::NewtonAnalyzer)

Print vertex coordinates and run the box-structure check. See
`print_vertices(::NewtonPolytope)`.
"""
print_vertices(A::NewtonAnalyzer) = print_vertices(A.np)

"""
    detect_box_structure(A::NewtonAnalyzer)

See `detect_box_structure(::NewtonPolytope)`.
"""
detect_box_structure(A::NewtonAnalyzer) = detect_box_structure(A.np)

"""
    missing_lattice_points(A::NewtonAnalyzer) -> Vector{Vector{Int}}

See `missing_lattice_points(::NewtonPolytope)`.
"""
missing_lattice_points(A::NewtonAnalyzer) = missing_lattice_points(A.np)

"""
    volume(A::NewtonAnalyzer)

Normalized volume of the underlying Newton polytope. See `normalized_volume_of`.
"""
Oscar.volume(A::NewtonAnalyzer) = normalized_volume_of(A.np)

"""
    ehrhart(A::NewtonAnalyzer)

Ehrhart polynomial of the underlying Newton polytope. See `ehrhart_polynomial_of`.
"""
ehrhart(A::NewtonAnalyzer) = ehrhart_polynomial_of(A.np)

"""
    lattice_points(A::NewtonAnalyzer, k::Integer)

Number of lattice points in the k-th dilate of the underlying Newton polytope.
"""
Oscar.lattice_points(A::NewtonAnalyzer, k::Integer) = lattice_points_of(A.np, k)

"""
    lattice_points(A::NewtonAnalyzer)

Number of lattice points in the underlying Newton polytope (k=1).
"""
Oscar.lattice_points(A::NewtonAnalyzer) = lattice_points_of(A.np)

"""
    dilate(A::NewtonAnalyzer, k::Integer) -> NewtonAnalyzer

k-th dilate of the underlying Newton polytope, wrapped back into a
NewtonAnalyzer so it chains: `dilate(A, 3) |> summary`.
"""
dilate(A::NewtonAnalyzer, k::Integer) = NewtonAnalyzer(dilate(A.np, k))

"""
    plot(A::NewtonAnalyzer)

Optional visualization hook. Only meaningful for ambient dimension 2 or 3
(higher-dimensional Newton polytopes, the expected case here at total
degree ~256 in 4 variables, cannot be plotted directly).

Raises an exception rather than silently no-op'ing when plotting isn't
possible, per the "raise exceptions on unsupported operations" requirement.
Delegates to Polymake's `visual` when dimension permits; Polymake's
visualization requires an interactive/jupyter backend and is not guaranteed
to render in all environments -- this function surfaces that failure rather
than swallowing it.
"""
function plot(A::NewtonAnalyzer)
    d = ambient_dimension(A.np)
    d in (2, 3) ||
        error("plot: NewtonAnalyzer plotting only supports ambient dimension " *
              "2 or 3, got ambient_dim=$d -- for the 4-variable, degree~256 " *
              "polytopes this project actually uses, plotting is not " *
              "available; use summary(A) / f_vector_of(A.np) for a " *
              "non-visual characterization instead")

    try
        return Oscar.visualize(A.np.polyhedron)
    catch e
        error("plot: Oscar.visualize failed on the underlying polyhedron -- " *
              "this typically requires an interactive/Jupyter Polymake " *
              "backend that may not be available in this environment; " *
              "underlying error: $e")
    end
end

# ---------------------------------------------------------------------------
# Exports
# ---------------------------------------------------------------------------

export support, newton_polytope, NewtonPolytope, NewtonAnalyzer,
       ambient_dimension, polytope_dimension, vertices_of, f_vector_of,
       normalized_volume_of, dilate, dilate_by_minkowski, lattice_points_of,
       ehrhart_polynomial_of, minkowski_sum, summary, ehrhart, plot,
       print_vertices, detect_box_structure, missing_lattice_points,
       print_missing_lattice_points
