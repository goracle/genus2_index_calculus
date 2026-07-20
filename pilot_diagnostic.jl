#!/usr/bin/env julia
#
# pilot_diagnostic.jl
#
# This was pilot_elimination_bench.jl. It is now a DIAGNOSTIC tool, not a
# benchmark: both lex Groebner and grevlex+FGLM were hanging on real
# specialized samples, and before spending time optimizing Groebner
# computations, the goal is to characterize the specialized bivariate
# systems g0(x2,x3), g1(x2,x3) themselves -- degree, sparsity,
# squarefreeness, common factors, Newton polygon shape, and ideal-theoretic
# invariants that are cheap to get -- to find out whether these systems are
# genuinely close to the worst-case Bezout bound, or whether there is
# hidden algebraic structure (a common factor, a non-generic Newton
# polygon, degeneracy in one variable, etc.) that a generic Groebner
# algorithm is failing to exploit.
#
# The only EXPENSIVE, potentially-hanging computations left are in section
# 8 (timed elimination with a hard timeout), and those now run each
# strategy in a separate killable subprocess -- see the big comment above
# run_with_timeout() for why that's necessary and why a Task/Timer-based
# timeout would NOT actually work here.
#
# Usage:
#   julia pilot_diagnostic.jl <U0.native> <U1.native> <prime> [n_samples] [seed] [timeout_secs]
#
#   U0.native, U1.native : NEWTPOL2 v2 native files (with coefficients),
#                           as produced by convert_to_native.jl <input> <output> <ambient_dim> <prime>
#   prime                : the F_p modulus -- must match what the native
#                           files were converted with (checked against the
#                           file's own stored prime; mismatch is an error)
#   n_samples             : number of random (x1,x4) specialization points
#                           to run diagnostics on (default 10)
#   seed                  : RNG seed for reproducible sample points (default 0)
#   timeout_secs          : per-strategy hard timeout in section 8, in
#                           seconds (default 30)
#
# Variable convention (matches interpolate_elimination.jl and the decision
# to eliminate (x2,x3), leaving F(x1,x4)): ambient_dim=4, exponent order in
# the native file is (x1,x2,x3,x4), i.e. index 1..4 = x1,x2,x3,x4. We fix
# x1=alpha, x4=beta and eliminate x2 (keeping x3), matching the request's
# R_{alpha,beta}(x3) = Res_{x2}(U0(alpha,x2,x3,beta), U1(alpha,x2,x3,beta)).
#
# Memory note: this script reconstructs U0 and U1 as actual Oscar
# multivariate polynomial ring elements over F_p (via the coefficients now
# stored in the v2 native format) ONCE at startup, and reuses those two
# polynomial objects for every specialization -- it substitutes numeric
# values for x1,x4 via evaluate/specialization, never re-parsing the
# native files per sample. With U0 and U1 both loaded simultaneously this
# is exactly the "only the U files fit in memory together" case Claire
# already identified -- V0/V1 are NOT touched by this script at all.

using Oscar

using Random
include(joinpath(@__DIR__, "newton_polytope.jl"))  # for load_native_support_with_coeffs

# ---------------------------------------------------------------------------
# Reconstruct an Oscar polynomial from a v2 native file's (support, coeffs)
# ---------------------------------------------------------------------------

# Builds an actual MPolyRingElem over F_p from the flat (support, coeffs)
# arrays returned by load_native_support_with_coeffs, using
# MPolyBuildCtx-based construction (per this project's established
# convention -- see memory: "MPolyBuildCtx-based ring remapping to replace
# failing evaluate() calls") rather than any term-by-term `+=`, which would
# be catastrophically slow and allocation-heavy for tens of millions of
# terms.
function reconstruct_polynomial(R, supp::Vector{Vector{Int}}, coeffs::Vector{UInt64}, Fp)
    length(supp) == length(coeffs) ||
        error("reconstruct_polynomial: support has $(length(supp)) terms, " *
              "coeffs has $(length(coeffs)) -- length mismatch")
    n = length(supp)
    ctx = MPolyBuildCtx(R)
    println("    reconstructing polynomial from ", n, " terms...")
    flush(stdout)
    t0 = time()
    @inbounds for i in 1:n
        push_term!(ctx, Fp(coeffs[i]), supp[i])
        if i % 5_000_000 == 0
            println("      ", i, "/", n, " terms rebuilt (", round(time() - t0, digits=1), "s)")
            flush(stdout)
        end
    end
    f = finish(ctx)
    println("    done in ", round(time() - t0, digits=1), "s")
    flush(stdout)
    return f
end

# Loads a v2 native file and returns the reconstructed polynomial over F_p,
# checking that the file's stored prime matches the prime given on the
# command line (a mismatch here would silently produce a wrong polynomial,
# so this is checked rather than assumed).
function load_polynomial(path::String, R, Fp, expected_prime::UInt64)
    (supp, coeffs, ambient_dim, file_prime) = load_native_support_with_coeffs(path)
    ambient_dim == 4 ||
        error("load_polynomial: $path has ambient_dim=$ambient_dim, expected 4 " *
              "(x1,x2,x3,x4) -- this pilot script is hard-coded for the 4-variable case")
    file_prime == expected_prime ||
        error("load_polynomial: $path was converted with prime=$file_prime, but " *
              "$expected_prime was given on the command line -- these must match " *
              "or the reconstructed polynomial's coefficients would be silently wrong")
    return reconstruct_polynomial(R, supp, coeffs, Fp)
end

# ---------------------------------------------------------------------------
# Specialization: substitute x1=alpha, x4=beta into a 4-variable polynomial,
# yielding a bivariate polynomial in (x2,x3) over the SAME field.
# ---------------------------------------------------------------------------

# Rebuilds the specialized polynomial term-by-term into a fresh bivariate
# ring S = Fp[x2,x3], rather than using Oscar's generic `evaluate` (which,
# per this project's established pattern -- see memory: "MPolyBuildCtx-based
# ring remapping to replace failing evaluate() calls" -- has been unreliable
# for this kind of partial substitution at this project's scale). This is
# still an O(n_terms) pass but with cheap scalar Fp arithmetic per term
# (two Fp exponentiations to compute alpha^e1 * beta^e4), not a symbolic
# operation.
function specialize(f, R4, S2, alpha, beta)
    ctx = MPolyBuildCtx(S2)
    # Accumulate into a Dict keyed by (e2,e3) first, since specializing
    # collapses many original 4-variable terms onto the same (x2,x3)
    # monomial (every distinct (e1,e4) pair with the same (e2,e3) merges) --
    # pushing directly into an MPolyBuildCtx requires monomials in sorted
    # order, which we don't have after collapsing, so accumulate then emit.
    acc = Dict{Tuple{Int,Int}, elem_type(base_ring(R4))}()
    for (exps, c) in zip(AbstractAlgebra.exponent_vectors(f), AbstractAlgebra.coefficients(f))
        e1, e2, e3, e4 = exps
        scale = alpha^e1 * beta^e4
        key = (e2, e3)
        term = c * scale
        if haskey(acc, key)
            acc[key] += term
        else
            acc[key] = term
        end
    end
    for (key, c) in acc
        iszero(c) && continue
        push_term!(ctx, c, [key[1], key[2]])
    end
    return finish(ctx)
end

# ---------------------------------------------------------------------------
# Diagnostics -- sections 1-7. All of these are meant to be cheap (no
# Groebner basis, no full resultant) and are run in-process with no
# timeout. Each diagnostic function is defensive: if the specific Oscar/
# AbstractAlgebra API it wants isn't available in this version, it catches
# the error and reports "not available" for that one line rather than
# taking down the whole diagnostic pass.
# ---------------------------------------------------------------------------

# Small helper: run `f()`, returning (value, nothing) on success or
# (nothing, "unavailable: <msg>") on any exception. Used throughout this
# section so one missing/renamed Oscar function doesn't abort the others.
function try_diag(f)
    try
        return (f(), nothing)
    catch e
        return (nothing, "unavailable: $(sprint(showerror, e))")
    end
end

# --- 1. Degree information -------------------------------------------------

function diag_degrees(g, varname::String, vars)
    println("    degree($varname, x2) = ", degree(g, vars[1]))
    println("    degree($varname, x3) = ", degree(g, vars[2]))
    println("    total_degree($varname) = ", total_degree(g))
end

# --- 2. Sparsity -------------------------------------------------------------

# Bounding box of exponents actually occurring, whether every (e2,e3) pair
# inside that box occurs (i.e. the support is a "full rectangle"), and if
# not, how many / which are missing (only the count + a few examples are
# printed if there are many, to avoid dumping thousands of pairs).
function diag_sparsity(g, varname::String)
    n_monomials = length(g)
    exps = collect(AbstractAlgebra.exponent_vectors(g))
    if isempty(exps)
        println("    $varname is the zero polynomial -- no sparsity data")
        return
    end
    e2s = [e[1] for e in exps]
    e3s = [e[2] for e in exps]
    lo2, hi2 = extrema(e2s)
    lo3, hi3 = extrema(e3s)
    box_size = (hi2 - lo2 + 1) * (hi3 - lo3 + 1)
    present = Set{Tuple{Int,Int}}((e[1], e[2]) for e in exps)
    n_missing = box_size - length(present)
    is_full_rectangle = n_missing == 0

    println("    $varname: ", n_monomials, " monomials")
    println("      exponent bounding box: x2 in [$lo2,$hi2], x3 in [$lo3,$hi3] ",
             "(box holds $box_size lattice points)")
    println("      full rectangle (every pair in box occurs)? ", is_full_rectangle)
    if !is_full_rectangle
        missing_pairs = Tuple{Int,Int}[]
        for e2 in lo2:hi2, e3 in lo3:hi3
            (e2, e3) in present || push!(missing_pairs, (e2, e3))
            length(missing_pairs) >= 12 && break
        end
        println("      missing from box: ", n_missing, " pairs",
                 n_missing > 0 ? " (first few: $missing_pairs" * (n_missing > 12 ? ", ..." : "") * ")" : "")
    end
end

# --- 3. Squarefreeness ------------------------------------------------------

# gcd(g, dg/dx2, dg/dx3) == 1 (a unit) iff g is squarefree. Computed as two
# pairwise gcds rather than a 3-argument gcd since AbstractAlgebra's gcd is
# binary.
function diag_squarefree(g, varname::String, vars)
    val, err = try_diag() do
        dg2 = derivative(g, vars[1])
        dg3 = derivative(g, vars[2])
        h = gcd(g, dg2)
        h = gcd(h, dg3)
        is_unit(h)
    end
    if err !== nothing
        println("    $varname squarefree? ", err)
    else
        println("    $varname squarefree? ", val)
    end
end

# --- 4. Common factor test --------------------------------------------------

# THIS IS THE MOST IMPORTANT CHEAP CHECK: if g0 and g1 share a nonconstant
# common factor, that factor is a spurious component of every fiber and
# would explain inflated Groebner/resultant cost independent of any
# algorithmic issue -- it needs to be caught (and ideally divided out)
# before any elimination is attempted.
function diag_common_factor(g0, g1)
    val, err = try_diag() do
        gcd(g0, g1)
    end
    if err !== nothing
        println("    gcd(g0,g1): ", err)
        return
    end
    h = val
    println("    gcd(g0,g1): degree=", iszero(h) ? "undefined (one input is zero)" : total_degree(h),
             ", monomials=", length(h), ", constant? ", is_unit(h))
    if !is_unit(h) && !iszero(h)
        println("    *** NONTRIVIAL COMMON FACTOR DETECTED -- g0 and g1 share a ",
                 "component at this specialization point. This alone can explain ",
                 "elimination blowup; consider dividing it out before eliminating, ",
                 "or treat this sample point as non-generic. ***")
    end
end

# --- 5. Resultant metadata only --------------------------------------------

# Does NOT compute the resultant. Reports what's knowable about the
# Sylvester matrix / expected resultant degree from degrees alone:
#   - Sylvester matrix for eliminating x2 from g0,g1 (viewed as univariate
#     in x2 over Fp[x3]) has dimension (d0+d1) x (d0+d1), where
#     d_i = degree(g_i, x2).
#   - The resultant, as a polynomial in x3, has degree bounded by the
#     classical bound deg_x3(Res) <= d0*e1 + d1*e0 where e_i = degree(g_i, x3)
#     (each row of the Sylvester matrix contributes at most one factor's
#     x3-degree; this is the standard resultant degree bound, not a Groebner
#     computation).
# If Oscar exposes anything more specific (e.g. a way to query the
# Sylvester matrix without forming the resultant), this is the place it
# would be added; as of the Oscar version this project uses, there is no
# public API for that, so this function only reports the bound above.
function diag_resultant_metadata(g0, g1, vars)
    x2s, x3s = vars
    d0x2, d1x2 = degree(g0, x2s), degree(g1, x2s)
    d0x3, d1x3 = degree(g0, x3s), degree(g1, x3s)
    syl_dim = d0x2 + d1x2
    # classical bound: deg_x3(Res_x2(g0,g1)) <= d0x2*d1x3 + d1x2*d0x3
    deg_bound = d0x2 * d1x3 + d1x2 * d0x3
    println("    degree(g0,x2)=", d0x2, ", degree(g1,x2)=", d1x2)
    println("    Sylvester matrix dimension (eliminating x2): ", syl_dim, " x ", syl_dim,
             " (", syl_dim^2, " entries if fully dense)")
    println("    classical bound on deg_x3(resultant): d0x2*d1x3 + d1x2*d0x3 = ",
             d0x2, "*", d1x3, " + ", d1x2, "*", d0x3, " = ", deg_bound)
    println("    Oscar has no public API (as far as this script can tell) to inspect ",
             "the Sylvester matrix or a resultant degree estimate without either ",
             "constructing the matrix or computing the resultant outright -- the ",
             "bound above is a hand-computed classical estimate, not something Oscar reports.")
end

# --- 6. Newton polygons -----------------------------------------------------

# 2D Newton polytope of a bivariate polynomial: convex hull of its
# exponent vectors (e2,e3). Oscar's newton_polytope() (via Polymake)
# returns a Polyhedron; vertices, normalized_volume, and lattice_points are
# all exact/combinatorial and cheap relative to any Groebner computation.
function diag_newton_polygon(g, varname::String)
    val, err = try_diag() do
        NP = Oscar.newton_polytope(g)
        verts = vertices(NP)
        nv = normalized_volume(NP)
        lp = lattice_points(NP)
        (NP, verts, nv, lp)
    end
    if err !== nothing
        println("    $varname Newton polygon: ", err)
        return
    end
    (NP, verts, nv, lp) = val
    n_verts = length(verts)
    n_lattice = length(lp)
    println("    $varname Newton polygon:")
    println("      vertices (", n_verts, "): ", verts)
    println("      normalized area: ", nv)
    println("      lattice points: ", n_lattice)
    # A complete rectangle has exactly 4 vertices and its normalized area
    # equals 2 * (width * height) (normalized volume convention: unit
    # triangle = 1, so a w x h axis-aligned rectangle has normalized area
    # 2wh). Only checked when we have exactly the rectangle vertex count;
    # otherwise it's straightforwardly not a rectangle.
    is_rect = n_verts == 4
    println("      complete rectangle? ", is_rect,
             is_rect ? "" : " (has $n_verts vertices, not 4)")
end

# --- 7. Projection / ideal diagnostics -------------------------------------

# Per the request: skip anything that requires a Groebner basis under the
# hood. In Oscar, `dim(I)` for an MPolyIdeal and `degree(I)` are BOTH
# implemented via a Groebner basis internally (there is no GB-free way to
# get either in general), so both are skipped here rather than silently
# running a hidden expensive computation inside what's supposed to be the
# cheap diagnostic phase. Hilbert polynomial/series likewise require a GB.
# The only thing reported here is a structural remark, not a computed
# invariant.
function diag_projection(g0, g1)
    println("    dimension / degree of <g0,g1> / Hilbert polynomial: SKIPPED -- ",
             "Oscar computes all of these via a Groebner basis internally, so ",
             "computing them here would just be the same hang moved earlier. ",
             "See section 8 for the actual timed Groebner/resultant attempts.")
end

# ---------------------------------------------------------------------------
# Section 8: timed elimination with a HARD timeout.
# ---------------------------------------------------------------------------
#
# IMPORTANT -- why this runs each strategy in a subprocess instead of a
# Julia Task + Timer:
#
# groebner_basis() and resultant() are blocking calls into Singular's C
# library. A Julia `Task` only yields at specific points (I/O, GC safepoints,
# explicit `yield()`); a tight C computation inside Singular does not hit
# those points, so an `@async` task running it cannot be preempted, and a
# `Timer` firing after N seconds cannot actually stop it -- the task just
# keeps running in the background even after the "timeout" branch gives up
# and moves on. That's not a hard timeout, it's a fake one: the hang is
# still there, just hidden, and now there may be TWO Groebner computations
# racing (the "timed out" one and the next sample's) inside a library that
# was never designed for that.
#
# The only way to get a REAL, killable timeout around this kind of call is
# an OS-level process boundary: spawn a separate `julia` subprocess to do
# just the one elimination call, wait up to `timeout_secs`, and `kill -9`
# it if it hasn't finished. That's what this section does:
#
#   1. Serialize g0, g1 (as flat exponent/coefficient arrays, prime, and
#      which strategy to run) to a small temp file.
#   2. Spawn `julia <this same file> --worker <tmpfile> <strategy>` as a
#      subprocess.
#   3. Poll process_running(proc) with a deadline; if the deadline passes,
#      kill(proc, SIGKILL) and report TIMEOUT.
#   4. Otherwise read the worker's result back from a second temp file.
#
# This does mean each timed strategy pays Oscar/Singular startup cost
# again per subprocess call (a few seconds) -- an acceptable price for an
# honest timeout given the goal here is diagnosis, not throughput.

using Serialization

const WORKER_FLAG = "--diagnostic-worker"

# Serializes just enough to reconstruct g0, g1 in a fresh Oscar session:
# the prime and each polynomial's (exponent_vectors, coefficients as UInt).
#
# NOTE on coeff_to_u64: `data(c)` (used elsewhere in the codebase's native
# I/O, going by convention) is not guaranteed to be the right accessor for
# an FqFieldElem across all Oscar/Nemo versions -- it can also be
# `lift(ZZ, c)` or a direct `Int(c)` conversion depending on version. This
# uses `Int(c)` first (works for prime fields in recent Nemo) and falls
# back to `lift(ZZ, c)` if that errors. If BOTH fail on your Oscar version,
# this is the one spot in the file to fix by hand -- nothing else in the
# script depends on which accessor wins.
function coeff_to_u64(c)
    try
        return UInt64(Int(c))
    catch
        return UInt64(lift(ZZ, c))
    end
end

function serialize_pair_for_worker(path, g0, g1, prime::UInt64)
    supp0 = collect(AbstractAlgebra.exponent_vectors(g0))
    coef0 = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g0)]
    supp1 = collect(AbstractAlgebra.exponent_vectors(g1))
    coef1 = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g1)]
    open(path, "w") do io
        serialize(io, (prime, supp0, coef0, supp1, coef1))
    end
end

# Worker-side entry point: reconstructs g0,g1 from the temp file, runs the
# ONE requested strategy, writes (status, elapsed, deg, info) to the result
# file. status is one of :ok, :error. This branch only runs when this
# script is invoked as `julia pilot_diagnostic.jl --diagnostic-worker
# <infile> <outfile> <strategy>` (see dispatch at the bottom of the file).
function run_worker(infile::String, outfile::String, strategy::String)
    (prime, supp0, coef0, supp1, coef1) = open(deserialize, infile)
    Fp = GF(prime)
    S2, (x2s, x3s) = polynomial_ring(Fp, [:x2, :x3])

    function rebuild(supp, coef)
        ctx = MPolyBuildCtx(S2)
        for (e, c) in zip(supp, coef)
            push_term!(ctx, Fp(c), e)
        end
        return finish(ctx)
    end
    g0 = rebuild(supp0, coef0)
    g1 = rebuild(supp1, coef1)

    result = try
        if strategy == "lex"
            t0 = time()
            I = ideal(S2, [g0, g1])
            G = groebner_basis(I; ordering=lex(S2))
            elapsed = time() - t0
            univ = [g for g in G if !isnothing(g) && degree(g, x2s) == 0]
            deg = isempty(univ) ? -1 : maximum(total_degree(g) for g in univ)
            (:ok, elapsed, deg, "lex basis size=$(length(G)), univariate-in-x3 generators=$(length(univ))")
        elseif strategy == "grevlex"
            t0 = time()
            I = ideal(S2, [g0, g1])
            G = groebner_basis(I; ordering=degrevlex(S2))
            elapsed = time() - t0
            (:ok, elapsed, -1, "grevlex basis size=$(length(G)) (no elimination -- grevlex " *
                               "basis alone doesn't give a univariate generator)")
        elseif strategy == "resultant"
            # resultant() for FpMPolyRingElem/FqMPolyRingElem wants the
            # eliminated variable as an Int INDEX into gens(parent(g0)),
            # not the variable element itself -- see the MethodError from
            # the original pilot run:
            #   resultant(::FpMPolyRingElem, ::FpMPolyRingElem, ::Int64)
            # x2s is gens(S2)[1], so its index is 1.
            x2_idx = findfirst(==(x2s), gens(parent(g0)))
            x2_idx === nothing && error("run_worker: could not find x2s in gens(parent(g0))")
            t0 = time()
            R_x3 = resultant(g0, g1, x2_idx)
            elapsed = time() - t0
            deg = iszero(R_x3) ? -1 : total_degree(R_x3)
            info = iszero(R_x3) ? "resultant is IDENTICALLY ZERO (common factor in x2)" :
                                  "resultant degree in x3 = $deg"
            (:ok, elapsed, deg, info)
        elseif strategy == "numerical_resultant"
            # Double Specialization (Numerical Resultant) strategy.
            #
            # Rationale: g0, g1 are dense bivariate degree-64 polynomials,
            # so both a symbolic resultant and a lex Groebner basis suffer
            # catastrophic expression swell (see "resultant"/"lex" above,
            # which time out or blow up). Instead of ever forming R(x3) =
            # Res_x2(g0,g1) as a symbolic polynomial, this strategy treats
            # it as a black-box function: for each scalar test point
            # gamma in Fp, specialize x3=gamma, form the CONCRETE Sylvester
            # matrix (entries are scalars in Fp, not polynomials) for the
            # two resulting univariate-in-x2 polynomials, and take its
            # determinant mod p. det(Syl(g0(x2,gamma), g1(x2,gamma))) =
            # R(gamma), so this recovers point-values of the resultant at
            # O(D^3) cost per point instead of ever building R symbolically.
            #
            # IMPORTANT SCOPE NOTE: this branch, as specified, reports
            # whether R(x3) is identically zero across the sampled points
            # and how long the scalar evaluations take -- it does NOT
            # interpolate the D_bound+1 (gamma, R(gamma)) pairs back into
            # the resultant polynomial itself. Interpolation (e.g. Lagrange
            # interpolation over Fp, or a structured evaluation/interp
            # scheme) is the natural next step if the actual resultant
            # polynomial or its exact degree is wanted -- it is NOT
            # implemented here since it wasn't part of the requested
            # sub-tasks, and doing it carelessly on 8193 points would
            # reintroduce real cost. If R turns out nonzero at points, this
            # strategy confirms that and times the evaluation, nothing more.
            d0x2, d1x2 = degree(g0, x2s), degree(g1, x2s)
            d0x3, d1x3 = degree(g0, x3s), degree(g1, x3s)
            d_bound = d0x2 * d1x3 + d1x2 * d0x3
            syl_dim = d0x2 + d1x2  # 64+64 = 128 for the systems seen so far

            n_points = d_bound + 1
            t0 = time()

            # Univariate polynomial ring over Fp, used to hold
            # g_i(x2, gamma) as an actual univariate poly so its
            # coefficients can be read off directly for the Sylvester
            # matrix rows, rather than hand-rolling coefficient extraction
            # against S2's bivariate representation.
            Ux, xvar = polynomial_ring(Fp, "x")

            # Builds the (d0+d1) x (d0+d1) Sylvester matrix over Fp for two
            # univariate polynomials a (degree da) and b (degree db) in x2,
            # via the standard shifted-row construction.
            function sylvester_matrix_fp(a, da::Int, b, db::Int)
                n = da + db
                M = zero_matrix(Fp, n, n)
                ca = [coeff(a, k) for k in 0:da]  # ca[1] = coeff of x^0, ..., ca[da+1] = leading
                cb = [coeff(b, k) for k in 0:db]
                # Row i (1..db): shifted copy of a's coefficients (highest
                # degree first), offset by (i-1).
                for i in 1:db
                    for k in 0:da
                        M[i, i + (da - k)] = ca[k + 1]
                    end
                end
                # Row db+i (1..da): shifted copy of b's coefficients.
                for i in 1:da
                    for k in 0:db
                        M[db + i, i + (db - k)] = cb[k + 1]
                    end
                end
                return M
            end

            zero_count = 0
            nonzero_count = 0
            first_nonzero = nothing
            eval_errors = 0
            first_error = nothing

            # Explicit, version-independent specialization of a bivariate
            # g (in x2,x3) at x3=gamma into a univariate polynomial in x2
            # over Fp: walk g's terms, accumulate coeff * gamma^e3 into
            # the x2^e2 slot of a dense coefficient vector, then build the
            # univariate poly from that vector. Deliberately avoids
            # relying on any particular evaluate()/specialize() method
            # signature across Oscar/AbstractAlgebra versions -- see the
            # note above this branch for why.
            function specialize_x3_to_univariate(g, deg_x2::Int, gamma)
                coeffs_by_e2 = [Fp(0) for _ in 0:deg_x2]
                for (exps, c) in zip(AbstractAlgebra.exponent_vectors(g), AbstractAlgebra.coefficients(g))
                    e2, e3 = exps[1], exps[2]
                    coeffs_by_e2[e2 + 1] += c * gamma^e3
                end
                return Ux(coeffs_by_e2)
            end

            for i in 0:(n_points - 1)
                gamma = Fp(i)
                try
                    # 1. Evaluate g0, g1 at x3=gamma, yielding univariate
                    #    polys in x2 over Fp.
                    g0_at = specialize_x3_to_univariate(g0, d0x2, gamma)
                    g1_at = specialize_x3_to_univariate(g1, d1x2, gamma)

                    # 2. Construct the concrete syl_dim x syl_dim Sylvester
                    #    matrix over Fp.
                    M = sylvester_matrix_fp(g0_at, d0x2, g1_at, d1x2)
                    size(M, 1) == syl_dim || error("Sylvester matrix dimension mismatch: " *
                                                    "got $(size(M,1)), expected $syl_dim")

                    # 3. Scalar determinant mod p.
                    dval = det(M)

                    if iszero(dval)
                        zero_count += 1
                    else
                        nonzero_count += 1
                        if first_nonzero === nothing
                            first_nonzero = (i, gamma)
                        end
                    end
                catch e
                    # Per the project's error-handling convention: catch
                    # cleanly here, but do NOT swallow the error silently
                    # -- record it and re-raise (via the outer `try` around
                    # the whole strategy dispatch) so it is reported
                    # through the worker's (:error, ...) result rather than
                    # being counted as an ordinary zero/nonzero point,
                    # which would misrepresent the diagnostic.
                    eval_errors += 1
                    if first_error === nothing
                        first_error = sprint(showerror, e)
                    end
                    error("numerical_resultant: evaluation failed at sample point " *
                          "index=$i, gamma=$gamma: $(sprint(showerror, e))")
                end
            end
            elapsed = time() - t0

            if nonzero_count == 0
                info = "ALL $n_points sampled determinants are IDENTICALLY ZERO -- " *
                       "potential structural base-field component (R(x3) may vanish " *
                       "identically, or g0/g1 share a factor not caught by the earlier " *
                       "gcd check at this specialization); see section 4 (common factor " *
                       "test) for this sample point"
                (:ok, elapsed, -1, info)
            else
                fn_str = first_nonzero === nothing ? "n/a" :
                         "index=$(first_nonzero[1]), gamma=$(first_nonzero[2])"
                info = "numerical Sylvester evaluation succeeded: $n_points points sampled " *
                       "($syl_dim x $syl_dim scalar determinants over Fp), " *
                       "nonzero=$nonzero_count, zero=$zero_count, first nonzero at $fn_str " *
                       "-- NOTE: this confirms R(x3) is not identically zero and times the " *
                       "scalar evaluation; it does NOT interpolate these point-values back " *
                       "into the resultant polynomial or its degree (see comment above this " *
                       "branch for why interpolation is a separate follow-up step)"
                (:ok, elapsed, -1, info)
            end
        elseif strategy == "grevlex_analysis"
            # Per the pilot diagnostic finding: grevlex Groebner bases are
            # cheap (~2.4s) while lex times out. This strategy stays in
            # grevlex the whole time and extracts everything possible about
            # the quotient algebra Fp[x2,x3]/<g0,g1> WITHOUT ever changing
            # monomial order:
            #   - leading monomials / initial ideal of the grevlex basis
            #   - standard monomials (a basis for the quotient algebra) and
            #     their count = dim_Fp(quotient) = degree of the ideal
            #     (valid because the ideal is 0-dimensional here: g0,g1 have
            #     no common factor per section 4, and two generic-looking
            #     curves of degree 128 meeting properly in the plane give a
            #     finite fiber)
            #   - Hilbert series/polynomial, if Oscar exposes it off this GB
            #   - FGLM to lex, but ONLY if the quotient dimension is modest
            #     (<= fglm_cutoff), since FGLM cost scales with (at least)
            #     quotient dimension and is exactly the expensive step this
            #     diagnostic is trying to avoid running blind.
            fglm_cutoff = 20000  # generous but bounded; see note above
            t0 = time()
            I = ideal(S2, [g0, g1])
            G = groebner_basis(I; ordering=degrevlex(S2))
            gb_elapsed = time() - t0

            lms = [leading_monomial(g; ordering=degrevlex(S2)) for g in G]
            lm_exps = [collect(AbstractAlgebra.exponent_vectors(m))[1] for m in lms]

            # Per-generator report: total degree, leading monomial exponent,
            # number of terms for each element of the grevlex basis -- to
            # look for a staircase / other visible pattern in the 128
            # generators, per the request.
            gen_reports = String[]
            for (idx, g) in enumerate(G)
                (ge2, ge3) = lm_exps[idx]
                push!(gen_reports,
                      "#$idx: deg=$(total_degree(g)), LM=(x2^$ge2*x3^$ge3), terms=$(length(g))")
            end

            # Standard monomials: monomials NOT divisible by any leading
            # monomial of the initial ideal. Since degree(g0,x2)=degree(g1,x2)
            # =degree(*,x3)=64 for the systems seen so far, bound the search
            # box generously (2x the max total degree seen in any basis
            # element) and bail out past fglm_cutoff rather than enumerate
            # unboundedly.
            max_deg_bound = maximum(total_degree(g) for g in G; init=0)
            search_bound = max(2 * max_deg_bound, 2 * max(total_degree(g0), total_degree(g1)))

            function divides_some_lm(e2, e3)
                for (a, b) in lm_exps
                    if e2 >= a && e3 >= b
                        return true
                    end
                end
                return false
            end

            standard_monomials = Tuple{Int,Int}[]
            box_exceeded = false
            for e2 in 0:search_bound
                for e3 in 0:search_bound
                    if !divides_some_lm(e2, e3)
                        push!(standard_monomials, (e2, e3))
                        if length(standard_monomials) > fglm_cutoff
                            box_exceeded = true
                            break
                        end
                    end
                end
                box_exceeded && break
            end

            quotient_dim = box_exceeded ? -1 : length(standard_monomials)

            hilbert_val, hilbert_err = try_diag() do
                hilbert_series(I)
            end

            elapsed = time() - t0

            info_parts = String[]
            push!(info_parts, "grevlex basis size=$(length(G)) (computed in $(round(gb_elapsed, digits=3))s)")
            push!(info_parts, "leading monomial exponents (x2,x3)=$(lm_exps)")
            push!(info_parts, "per-generator report: " * join(gen_reports, "; "))
            if box_exceeded
                push!(info_parts, "quotient dimension: EXCEEDED search cutoff ($fglm_cutoff within box up to degree $search_bound) -- too large to enumerate here")
            else
                push!(info_parts, "quotient dimension (= degree of ideal, assuming 0-dimensional) = $quotient_dim")
            end
            if hilbert_err === nothing
                push!(info_parts, "hilbert_series available: $(hilbert_val)")
            else
                push!(info_parts, "hilbert_series: $hilbert_err")
            end

            ran_fglm = false
            fglm_info = ""
            if !box_exceeded && quotient_dim > 0 && quotient_dim <= fglm_cutoff
                fglm_t0 = time()
                fglm_result, fglm_err = try_diag() do
                    fglm(I; start_ordering=degrevlex(S2), destination_ordering=lex(S2))
                end
                fglm_elapsed = time() - fglm_t0
                if fglm_err === nothing
                    ran_fglm = true
                    univ = [g for g in fglm_result if !isnothing(g) && degree(g, x2s) == 0]
                    fglm_deg = isempty(univ) ? -1 : maximum(total_degree(g) for g in univ)
                    fglm_info = "FGLM attempted (dim=$quotient_dim <= cutoff=$fglm_cutoff): " *
                                "succeeded in $(round(fglm_elapsed, digits=3))s, " *
                                "lex basis size=$(length(fglm_result)), " *
                                "univariate-in-x3 generators=$(length(univ)), " *
                                "fiber_degree=$fglm_deg"
                else
                    fglm_info = "FGLM attempted (dim=$quotient_dim <= cutoff=$fglm_cutoff) but failed: $fglm_err"
                end
            else
                reason = box_exceeded ? "quotient dimension exceeded search cutoff" :
                         quotient_dim <= 0 ? "quotient dimension is degenerate ($quotient_dim)" :
                         "quotient dimension $quotient_dim exceeds fglm_cutoff=$fglm_cutoff"
                fglm_info = "FGLM SKIPPED: $reason"
            end
            push!(info_parts, fglm_info)

            deg_report = box_exceeded ? -1 : quotient_dim
            (:ok, elapsed, deg_report, join(info_parts, " | "))
        else
            error("run_worker: unknown strategy $strategy")
        end
    catch e
        (:error, NaN, -1, sprint(showerror, e))
    end

    open(outfile, "w") do io
        serialize(io, result)
    end
end

# Driver-side: spawns the worker subprocess for one strategy, enforces the
# hard wall-clock timeout, and returns (elapsed, deg, info) where elapsed
# is NaN and info == "TIMEOUT" if the deadline was hit.
function run_with_timeout(g0, g1, prime::UInt64, strategy::String, timeout_secs::Real, script_path::String)
    tmpdir = mktempdir()
    infile = joinpath(tmpdir, "in.jls")
    outfile = joinpath(tmpdir, "out.jls")
    serialize_pair_for_worker(infile, g0, g1, prime)

    cmd = `julia --startup-file=no $script_path $WORKER_FLAG $infile $outfile $strategy`
    proc = run(pipeline(cmd; stdout=devnull, stderr=devnull); wait=false)

    deadline = time() + timeout_secs
    while process_running(proc) && time() < deadline
        sleep(0.2)
    end

    if process_running(proc)
        # Hard kill -- SIGKILL, not SIGTERM, since Singular/GC internals
        # may not respond to a polite signal in the middle of a C loop.
        try
            kill(proc, Base.SIGKILL)
        catch
        end
        # Reap the process so it doesn't linger as a zombie.
        try
            wait(proc)
        catch
        end
        rm(tmpdir; recursive=true, force=true)
        return (NaN, -1, "TIMEOUT (exceeded $(timeout_secs)s, subprocess killed)")
    end

    if !isfile(outfile)
        rm(tmpdir; recursive=true, force=true)
        return (NaN, -1, "worker exited without producing a result (crashed or was killed externally)")
    end

    (status, elapsed, deg, info) = open(deserialize, outfile)
    rm(tmpdir; recursive=true, force=true)
    if status == :error
        return (NaN, -1, "ERROR: $info")
    end
    return (elapsed, deg, info)
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()
    length(ARGS) >= 3 ||
        error("pilot_diagnostic.jl: usage: julia pilot_diagnostic.jl " *
              "<U0.native> <U1.native> <prime> [n_samples] [seed] [timeout_secs]")

    u0_path = ARGS[1]
    u1_path = ARGS[2]
    prime = parse(UInt64, ARGS[3])
    n_samples = length(ARGS) >= 4 ? parse(Int, ARGS[4]) : 10
    seed = length(ARGS) >= 5 ? parse(Int, ARGS[5]) : 0
    timeout_secs = length(ARGS) >= 6 ? parse(Float64, ARGS[6]) : 30.0

    isfile(u0_path) || error("pilot_diagnostic.jl: no such file: $u0_path")
    isfile(u1_path) || error("pilot_diagnostic.jl: no such file: $u1_path")

    script_path = abspath(@__FILE__)

    println("=" ^ 70)
    println("Pilot diagnostic (specialized system characterization)")
    println("=" ^ 70)
    println("U0 file:      ", u0_path)
    println("U1 file:      ", u1_path)
    println("prime:        ", prime)
    println("samples:      ", n_samples, " (seed=", seed, ")")
    println("timeout:      ", timeout_secs, "s per strategy in section 8")
    println()

    Fp = GF(prime)
    R4, (x1, x2, x3, x4) = polynomial_ring(Fp, [:x1, :x2, :x3, :x4])
    S2, (y2, y3) = polynomial_ring(Fp, [:x2, :x3])

    println("Loading and reconstructing U0...")
    U0 = load_polynomial(u0_path, R4, Fp, prime)
    println("Loading and reconstructing U1...")
    U1 = load_polynomial(u1_path, R4, Fp, prime)
    println()

    # Reproducible sample points: a simple LCG-free approach using Julia's
    # Random with an explicit seed, avoiding alpha=0 or beta=0 (those are
    # more likely to hit non-generic special fibers, e.g. coordinate
    # hyperplanes intersecting the variety's boundary strata).
    rng = Random.MersenneTwister(seed)
    samples = Tuple{elem_type(Fp), elem_type(Fp)}[]
    while length(samples) < n_samples
        a = Fp(rand(rng, 1:(prime - 1)))
        b = Fp(rand(rng, 1:(prime - 1)))
        push!(samples, (a, b))
    end

    # NOTE on strategy selection (updated after the first pilot run): lex
    # Groebner timed out on every sample at 30s while grevlex finished in
    # ~2.4s, so lex is dropped from the default rotation for now -- it was
    # burning the whole timeout budget for zero information. grevlex_analysis
    # is the new focus: it stays in grevlex the entire time (cheap, per the
    # pilot run) and extracts leading monomials, standard monomials, quotient
    # dimension (= degree of the ideal), and Hilbert series without ever
    # attempting a monomial-order conversion, then only attempts FGLM if the
    # quotient dimension turns out to be modest. Plain "grevlex" (just the
    # basis, no analysis) is kept too since it's nearly free once
    # grevlex_analysis is already being timed, and resultant_x2 is kept with
    # its fixed API call (variable index instead of variable element) as an
    # independent cross-check on the same fiber degree.
    timed_strategies = [
        ("grevlex_analysis",    "grevlex_analysis"),
        ("numerical_resultant", "numerical_resultant"),
        ("resultant_x2",        "resultant"),
    ]
    timed_results = Dict(name => Vector{Tuple{Float64,Int,String}}() for (name, _) in timed_strategies)

    for (i, (a, b)) in enumerate(samples)
        println("=" ^ 70)
        println("Sample ", i, "/", n_samples, ": x1=", a, ", x4=", b)
        println("=" ^ 70)
        flush(stdout)

        println("  specializing U0, U1 at this point...")
        t0 = time()
        g0 = specialize(U0, R4, S2, a, b)
        g1 = specialize(U1, R4, S2, a, b)
        println("  specialized in ", round(time() - t0, digits=2), "s ",
                 "(g0 has ", length(g0), " terms, g1 has ", length(g1), " terms)")
        flush(stdout)
        vars = (y2, y3)

        println()
        println("  --- 1. Degree information ---")
        diag_degrees(g0, "g0", vars)
        diag_degrees(g1, "g1", vars)
        flush(stdout)

        println()
        println("  --- 2. Sparsity ---")
        diag_sparsity(g0, "g0")
        diag_sparsity(g1, "g1")
        flush(stdout)

        println()
        println("  --- 3. Squarefreeness ---")
        diag_squarefree(g0, "g0", vars)
        diag_squarefree(g1, "g1", vars)
        flush(stdout)

        println()
        println("  --- 4. Common factor test (gcd(g0,g1)) ---")
        diag_common_factor(g0, g1)
        flush(stdout)

        println()
        println("  --- 5. Resultant metadata only (no resultant computed here) ---")
        diag_resultant_metadata(g0, g1, vars)
        flush(stdout)

        println()
        println("  --- 6. Newton polygons ---")
        diag_newton_polygon(g0, "g0")
        diag_newton_polygon(g1, "g1")
        flush(stdout)

        println()
        println("  --- 7. Projection / ideal diagnostics ---")
        diag_projection(g0, g1)
        flush(stdout)

        println()
        println("  --- 8. Timed elimination (hard timeout=", timeout_secs, "s, subprocess-isolated) ---")
        for (name, strategy) in timed_strategies
            print("    [", name, "] running in subprocess... ")
            flush(stdout)
            (elapsed, deg, info) = run_with_timeout(g0, g1, prime, strategy, timeout_secs, script_path)
            if info == "TIMEOUT" || startswith(info, "TIMEOUT")
                println("TIMEOUT")
            elseif startswith(info, "ERROR")
                println("FAILED")
            else
                println("done in ", round(elapsed, digits=3), "s, fiber_degree=", deg)
            end
            println("        ", info)
            push!(timed_results[name], (elapsed, deg, info))
            flush(stdout)
        end
        println()
    end

    println("=" ^ 70)
    println("Summary (section 8 timed strategies only -- sections 1-7 are")
    println("per-sample diagnostics, see above)")
    println("=" ^ 70)
    for (name, _) in timed_strategies
        rows = timed_results[name]
        times = [r[1] for r in rows if !isnan(r[1])]
        degs = [r[2] for r in rows if r[2] >= 0]
        n_timeout = count(r -> occursin("TIMEOUT", r[3]), rows)
        n_error = count(r -> startswith(r[3], "ERROR"), rows)
        println(name, ":")
        println("  completed: ", length(times), "/", n_samples,
                 "   timed out: ", n_timeout, "/", n_samples,
                 "   errored: ", n_error, "/", n_samples)
        if !isempty(times)
            println("  time (completed only): min=", round(minimum(times), digits=3), "s  ",
                     "median=", round(sort(times)[cld(length(times), 2)], digits=3), "s  ",
                     "max=", round(maximum(times), digits=3), "s")
        end
        if !isempty(degs)
            if all(==(degs[1]), degs)
                println("  fiber degree: CONSISTENT at ", degs[1], " across completed samples")
            else
                println("  fiber degree: INCONSISTENT across samples: ", degs)
            end
        end
        println()
    end

    println("This is a diagnostic pass, not an optimization pass. Use sections 1-7")
    println("(especially #4, the common-factor test) to look for structural reasons")
    println("elimination might be harder than a generic system of these degrees,")
    println("before concluding the systems are simply at/near the Bezout bound.")
end

# ---------------------------------------------------------------------------
# Entry point dispatch: this file is either run normally (main()) or, when
# invoked with the WORKER_FLAG by run_with_timeout() above, as a one-shot
# subprocess worker that runs a single elimination strategy and exits.
# ---------------------------------------------------------------------------

if length(ARGS) >= 1 && ARGS[1] == WORKER_FLAG
    # ARGS = ["--diagnostic-worker", infile, outfile, strategy]
    run_worker(ARGS[2], ARGS[3], ARGS[4])
else
    main()
end
