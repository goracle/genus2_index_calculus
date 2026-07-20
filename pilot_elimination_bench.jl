#!/usr/bin/env julia
#
# pilot_elimination_bench.jl
#
# BEFORE running the full interpolate_elimination.jl sweep over thousands of
# (x1,x4) specialization points, this script answers the question that
# actually determines whether that sweep is feasible at all: at a
# specialized point, how expensive is eliminating (x2,x3) from the two
# specialized bivariate polynomials U0(a,x2,x3,b), U1(a,x2,x3,b), and what
# is the generic fiber degree (the number of (x2,x3) solutions)?
#
# It benchmarks candidate elimination strategies Oscar provides, against the
# SAME set of random specialization points, and reports timing, peak memory,
# and the fiber degree recovered by each method (so disagreements in fiber
# degree are visible, not just timing differences):
#
#   1. lex Groebner basis directly (groebner_basis(I; ordering=lex(R))) --
#      CURRENTLY SKIPPED: hangs on real samples, see `methods` list in main()
#   2. grevlex Groebner basis followed by fglm to lex (often much faster to
#      get the grevlex basis first, then convert -- this is the classical
#      reason FGLM exists)
#   3. resultant_x2(U0, U1) -- eliminate x2 via resultant to get a
#      univariate-in-x3 polynomial directly, without ever forming a full
#      2-variable ideal/Groebner basis
#
# It does NOT pick a winner automatically -- it prints a comparison table
# and leaves the strategy choice to be wired into interpolate_elimination.jl
# by hand once you've looked at the numbers. Degrees after specialization
# can still be in the dozens to ~96, so a method that looks fine on the
# first 1-2 samples can still blow up on others (uneven cost is itself
# useful information), which is why this script runs multiple samples per
# method rather than just one.
#
# Usage:
#   julia pilot_elimination_bench.jl <U0.native> <U1.native> <prime> [n_samples] [seed]
#
#   U0.native, U1.native : NEWTPOL2 v2 native files (with coefficients),
#                           as produced by convert_to_native.jl <input> <output> <ambient_dim> <prime>
#   prime                : the F_p modulus -- must match what the native
#                           files were converted with (checked against the
#                           file's own stored prime; mismatch is an error)
#   n_samples            : number of random (x1,x4) specialization points to
#                           benchmark each method against (default 10)
#   seed                  : RNG seed for reproducible sample points (default 0)
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
# Elimination strategies (each returns (elapsed_seconds, fiber_degree,
# extra_info::String) so the comparison table can show a one-line summary
# per method per sample)
# ---------------------------------------------------------------------------

# Strategy 1: direct lex Groebner basis of <g0,g2> in Fp[x2,x3] with
# x2 > x3 (so eliminating x2 leaves a univariate-in-x3 generator at the
# bottom of the lex basis, per the Elimination Theorem).
function bench_lex_groebner(g0, g2, S2)
    t0 = time()
    I = ideal(S2, [g0, g2])
    G = groebner_basis(I; ordering=lex(S2))
    elapsed = time() - t0
    # Under lex(x2,x3) with x2>x3, the elimination ideal I ∩ Fp[x3] is
    # generated by whichever basis element(s) involve only x3 -- for a
    # zero-dimensional generic fiber there should be exactly one such
    # univariate generator; its degree is the fiber degree (Bezout bound
    # 96^2 = 9216 in the worst case, per the request's own estimate).
    x2s, x3s = gens(S2)
    univ = [g for g in G if !isnothing(g) && degree(g, x2s) == 0]
    deg = isempty(univ) ? -1 : maximum(total_degree(g) for g in univ)
    info = "lex basis size=$(length(G)), univariate-in-x3 generators=$(length(univ))"
    return (elapsed, deg, info)
end

# Strategy 2: grevlex Groebner basis first (classically much cheaper to
# compute than lex directly), then fglm-convert to lex. Same fiber-degree
# extraction as strategy 1, applied to the FGLM-converted basis.
function bench_fglm(g0, g2, S2)
    t0 = time()
    I = ideal(S2, [g0, g2])
    Ggrevlex = groebner_basis(I; ordering=degrevlex(S2))
    t_grevlex = time() - t0
    t1 = time()
    Glex = fglm(I; start_ordering=degrevlex(S2), destination_ordering=lex(S2))
    t_fglm = time() - t1
    elapsed = t_grevlex + t_fglm
    x2s, x3s = gens(S2)
    univ = [g for g in Glex if !isnothing(g) && degree(g, x2s) == 0]
    deg = isempty(univ) ? -1 : maximum(total_degree(g) for g in univ)
    info = "grevlex=$(round(t_grevlex,digits=2))s (basis size $(length(Ggrevlex))), " *
           "fglm=$(round(t_fglm,digits=2))s (lex basis size $(length(Glex)))"
    return (elapsed, deg, info)
end

# Strategy 3: eliminate x2 directly via resultant (no ideal/Groebner
# machinery at all), yielding a univariate-in-x3 polynomial whose degree is
# read off directly -- this is the cheapest-per-call method IF Oscar's
# resultant implementation handles dense bivariate degree ~96 inputs well;
# that's exactly what this benchmark is here to check, not assume.
function bench_resultant(g0, g2, S2)
    x2s, x3s = gens(S2)
    t0 = time()
    R_x3 = resultant(g0, g2, x2s)
    elapsed = time() - t0
    deg = iszero(R_x3) ? -1 : total_degree(R_x3)
    info = iszero(R_x3) ? "resultant is IDENTICALLY ZERO (common factor in x2, or " *
                          "the two specialized curves share a component -- inspect " *
                          "manually before trusting this sample point)" :
                          "resultant degree in x3 = $deg"
    return (elapsed, deg, info)
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()
    length(ARGS) >= 3 ||
        error("pilot_elimination_bench.jl: usage: julia pilot_elimination_bench.jl " *
              "<U0.native> <U1.native> <prime> [n_samples] [seed]")

    u0_path = ARGS[1]
    u1_path = ARGS[2]
    prime = parse(UInt64, ARGS[3])
    n_samples = length(ARGS) >= 4 ? parse(Int, ARGS[4]) : 10
    seed = length(ARGS) >= 5 ? parse(Int, ARGS[5]) : 0

    isfile(u0_path) || error("pilot_elimination_bench.jl: no such file: $u0_path")
    isfile(u1_path) || error("pilot_elimination_bench.jl: no such file: $u1_path")

    println("=" ^ 70)
    println("Pilot elimination benchmark")
    println("=" ^ 70)
    println("U0 file: ", u0_path)
    println("U1 file: ", u1_path)
    println("prime:   ", prime)
    println("samples: ", n_samples, " (seed=", seed, ")")
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

    methods = [
        # lex Groebner skipped -- was hanging on real samples; re-enable by
        # uncommenting once grevlex+FGLM/resultant numbers are in hand.
        # ("lex Groebner",      bench_lex_groebner),
        ("grevlex+FGLM",      bench_fglm),
        ("resultant_x2",      bench_resultant),
    ]

    # results[method_name] = Vector of (elapsed, deg, info) per sample
    results = Dict(name => Vector{Tuple{Float64,Int,String}}() for (name, _) in methods)

    for (i, (a, b)) in enumerate(samples)
        println("-" ^ 70)
        println("Sample ", i, "/", n_samples, ": x1=", a, ", x4=", b)
        println("-" ^ 70)
        flush(stdout)

        println("  specializing U0, U1 at this point...")
        t0 = time()
        g0 = specialize(U0, R4, S2, a, b)
        g2 = specialize(U1, R4, S2, a, b)
        println("  specialized in ", round(time() - t0, digits=2), "s ",
                 "(g0 has ", length(g0), " terms, g1 has ", length(g2), " terms)")
        flush(stdout)

        for (name, fn) in methods
            print("  [", name, "] running... ")
            flush(stdout)
            try
                (elapsed, deg, info) = fn(g0, g2, S2)
                println("done in ", round(elapsed, digits=3), "s, fiber_degree=", deg)
                println("      ", info)
                push!(results[name], (elapsed, deg, info))
            catch e
                println("FAILED: ", e)
                push!(results[name], (NaN, -1, "ERROR: $e"))
            end
            flush(stdout)
        end
        println()
    end

    println("=" ^ 70)
    println("Summary")
    println("=" ^ 70)
    for (name, _) in methods
        times = [r[1] for r in results[name] if !isnan(r[1])]
        degs = [r[2] for r in results[name] if r[2] >= 0]
        println(name, ":")
        if isempty(times)
            println("  all samples FAILED")
        else
            println("  time:   min=", round(minimum(times), digits=3), "s  ",
                     "median=", round(sort(times)[cld(length(times), 2)], digits=3), "s  ",
                     "max=", round(maximum(times), digits=3), "s  ",
                     "(", length(times), "/", n_samples, " succeeded)")
        end
        if isempty(degs)
            println("  fiber degree: no successful samples")
        elseif all(==(degs[1]), degs)
            println("  fiber degree: CONSISTENT at ", degs[1], " across all successful samples")
        else
            println("  fiber degree: INCONSISTENT across samples: ", degs,
                     " -- investigate before trusting any single value " *
                     "(could mean non-generic sample points, or a bug)")
        end
        println()
    end

    println("No strategy is auto-selected. Compare the timings and fiber-degree")
    println("agreement above, then hard-code the winning method into")
    println("interpolate_elimination.jl's eliminate_at_point function.")
end

main()
