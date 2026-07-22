#!/usr/bin/env julia
#
# streaming_ideal_dimension.jl
#
# Estimates dim(I) for I = <U0,U1,V0,V1> in Fp[x1,x2,x3,x4], under the
# constraint that AT MOST ONE of the four native files (U0.native, U1.native,
# V0.native, V1.native) is ever fully materialized in memory at once --
# because only one full V equation fits in memory at once (17.8M terms,
# ~13GB, per convert_to_native.jl / pilot_diagnostic.jl's own header
# comments). This rules out ANY approach that needs two or more of the four
# generators as live in-memory MPolyRingElem objects simultaneously in 4
# variables, which is exactly what a direct groebner_basis/dimension call on
# ideal(R4, [U0,U1,V0,V1]) would require -- so that direct call is not
# attempted here at all, not even behind a timeout.
#
# ---------------------------------------------------------------------------
# What "dim(I)" means here, and why this script computes a PROXY, not the
# certified answer
# ---------------------------------------------------------------------------
#
# Assuming (as pilot_diagnostic.jl's own diagnostics assume, see e.g.
# summarize_effective_fiber_degree, diag_resultant_metadata's Bezout-style
# bound) that V(I) is zero-dimensional as a variety -- i.e. U0,U1,V0,V1 have
# only finitely many common solutions in 4 variables, which is the generic
# expectation for 4 equations in 4 unknowns -- then "dim(I)" in the sense
# that actually matters for this project is the COLENGTH
#
#     dim(I) := dim_{Fp} Fp[x1,x2,x3,x4] / I
#
# i.e. the degree of the zero-dimensional scheme V(I), counted with
# multiplicity. That is the quantity a Groebner-basis + standard-monomial
# count would give you if it didn't hang/OOM. If instead V(I) turns out to
# be positive-dimensional (this script's diagnostics below will show this as
# an ever-growing / non-stabilizing per-sample count -- see the
# CONSISTENT/INCONSISTENT summary at the end, same convention as
# pilot_diagnostic.jl), the whole streaming-fiber-count strategy stops being
# a colength estimator and just becomes a "here's a lower bound and evidence
# of the wrong assumption" tool -- flagged explicitly in the final summary
# rather than silently reported as if it were exact.
#
# THIS SCRIPT NEVER CLAIMS TO CERTIFY dim(I) EXACTLY. What it computes,
# honestly:
#
#   1. A genuinely STREAMED, exact reduction: at each of several random
#      sample points (x1,x2) = (alpha,beta), it specializes U0,U1,V0,V1 one
#      at a time (only one polynomial's exponent/coefficient arrays alive at
#      any moment -- see stream_specialize_one_at_a_time below) into a
#      SMALL bivariate system in Fp[x3,x4]. This step is exact: no
#      approximation, no numerical error, just substitution.
#
#   2. An EXACT bivariate colength computation on that small system via a
#      grevlex Groebner basis of <u0,u1,v0,v1> in Fp[x3,x4] (reusing/
#      extending pilot_diagnostic.jl's grevlex_analysis strategy from a
#      2-generator ideal to this script's 4-generator one) -- standard
#      monomials counted by leading-monomial staircase, exactly as
#      run_worker's "grevlex_analysis" strategy already does for a pair.
#      This step is ALSO exact, given that the bivariate GB computation
#      itself terminates (it can still hang/OOM on a genuinely hard
#      bivariate instance -- guarded by the same subprocess+timeout
#      discipline pilot_diagnostic.jl uses for exactly that reason).
#
#   3. What is NOT exact / NOT certified: whether "the generic (x1,x2)-fiber
#      colength, repeated across independent samples until it stabilizes"
#      actually equals dim(I) itself. This is standard commutative-algebra
#      folklore (a flat family's fiber dimension is generically constant,
#      and for a zero-dimensional-in-the-fiber-variables ideal the total
#      colength is captured by a SINGLE generic fiber when the projection
#      x1,x2 -> point is finite/proper over a dense open set) but is NOT
#      re-derived or proven here for this specific I -- it is a hypothesis
#      this script tests empirically (do independent random samples agree?)
#      rather than a theorem this script invokes. Section 4 below states
#      this explicitly every time it reports a number.
#
# ---------------------------------------------------------------------------
# Streaming discipline (the actual point of this file)
# ---------------------------------------------------------------------------
#
# At every sample point, the four native files are processed ONE AT A TIME:
# open file, stream+specialize+collapse it into a small (x3,x4)-bivariate
# polynomial, close the file, move on. The specialized bivariate polynomial
# for a fully-collapsed generator (thousands of terms at most, since it is
# indexed only by (e3,e4) pairs which are bounded by V's own box degree in
# x3,x4 -- see diag_newton_polygon's box-size numbers in pilot_diagnostic.jl
# runs) is retained (it is tiny), but the SOURCE file's 17.8M-term
# exponent/coefficient arrays are never held in memory beyond the current
# chunk (chunk_terms below, same default as pilot_diagnostic.jl's
# stream_specialize_native_to_poly). So peak memory across the whole script
# is: O(1) chunks of raw file bytes + O(1) small specialized bivariate
# polynomials (four of them, all small, all in Fp[x3,x4]) + whatever a
# bivariate Groebner basis over Fp[x3,x4] needs -- never anything close to
# "all of V0 and V1 as MPolyRingElem objects in 4 variables at once".
#
# This is exactly stream_specialize_native_to_poly from pilot_diagnostic.jl,
# copied here (not included/reused via `include`, to keep this script
# self-contained and independently auditable against the "never hold two
# native files' term arrays live at once" requirement) under a new name
# (stream_specialize_one_at_a_time) with one change: pilot_diagnostic.jl's
# version hard-codes ambient_dim==4 and specializes x1,x2 fixed / keeps
# x3,x4 -- this script keeps that same convention (matches
# interpolate_elimination.jl's elimination-order decision, per
# pilot_diagnostic.jl's own header comment) but the mapping is made an
# explicit parameter (fixed_idx, keep_idx) rather than hard-coded positions,
# so this script does not silently assume the pilot script's docstring
# (which says "fix x1,x4, eliminate x2" -- text that does NOT match that
# script's own code, which fixes x1,x2 and keeps x3,x4) -- see the CAVEAT
# note right below main()'s argument parsing, this discrepancy is called
# out explicitly rather than silently resolved one way or the other.
#
# ---------------------------------------------------------------------------
# Usage
# ---------------------------------------------------------------------------
#   julia streaming_ideal_dimension.jl <U0.native> <U1.native> <V0.native> \
#         <V1.native> <prime> [n_samples] [seed] [timeout_secs] [chunk_terms]
#
#   U0/U1/V0/V1.native : NEWTPOL2 v2 native files (WITH coefficients), same
#                        convention as pilot_diagnostic.jl.
#   prime              : Fp modulus, must match every file's stored prime.
#   n_samples          : number of independent random (x1,x2) sample points
#                        to test for colength stabilization (default 8).
#   seed               : RNG seed (default 0).
#   timeout_secs       : hard timeout, in seconds, for the per-sample
#                        bivariate Groebner computation, run in a killable
#                        subprocess exactly like pilot_diagnostic.jl's
#                        run_with_timeout (default 60).
#   chunk_terms        : streaming chunk size in terms, same meaning as
#                        pilot_diagnostic.jl's stream_specialize_native_to_poly
#                        (default 1_000_000).

using Oscar
using Random
using Serialization

include(joinpath(@__DIR__, "newton_polytope.jl"))  # for NATIVE_SUPPORT_MAGIC_V2 etc., and coeff/modarith reuse

# ---------------------------------------------------------------------------
# CAVEAT (read before trusting this script's variable convention):
#
# pilot_diagnostic.jl's own header comment (lines ~60-65 of that file) says
# the convention is "fix x1=alpha, x4=beta, eliminate x2, keep x3" -- but
# stream_specialize_native_to_poly's ACTUAL CODE in that same file specializes
# x1 and x2 (exponent slots 1 and 2) and keeps x3,x4 (slots 3 and 4). This is
# a genuine doc/code mismatch in the uploaded pilot_diagnostic.jl, not
# something this script resolves by guessing which one is "right" -- this
# script FOLLOWS THE CODE (fix x1,x2; keep x3,x4), because the code is what
# actually ran and produced whatever downstream results already exist, and
# flags this explicitly here rather than silently picking a side. If the
# intended convention was actually "fix x1,x4; keep x2,x3", swap
# FIXED_SLOTS/KEPT_SLOTS below (and double check every other script that
# consumes these outputs is using the same convention) before trusting
# results run through this file.
# ---------------------------------------------------------------------------
const FIXED_SLOTS = (1, 2)   # x1, x2 -- specialized to random field elements
const KEPT_SLOTS   = (3, 4)  # x3, x4 -- survive as the bivariate ring's variables

# ---------------------------------------------------------------------------
# Raw modular arithmetic (identical to pilot_diagnostic.jl's helpers;
# duplicated rather than `include`d from that file so this script has no
# dependency on pilot_diagnostic.jl's own state/side effects at load time --
# it only needs newton_polytope.jl's native-file format constants).
# ---------------------------------------------------------------------------

@inline function modmul(a::UInt64, b::UInt64, p::UInt64)
    return UInt64((UInt128(a) * UInt128(b)) % UInt128(p))
end

@inline function modadd(a::UInt64, b::UInt64, p::UInt64)
    s = a + b
    return s >= p ? s - p : s
end

function modpow(base::UInt64, exp::Integer, p::UInt64)
    result = UInt64(1) % p
    b = base % p
    e = exp
    while e > 0
        if isodd(e)
            result = modmul(result, b, p)
        end
        b = modmul(b, b, p)
        e >>= 1
    end
    return result
end

function coeff_to_u64(c)
    try
        return UInt64(Int(c))
    catch
        return UInt64(lift(ZZ, c))
    end
end

# ---------------------------------------------------------------------------
# Streaming specialization: fix FIXED_SLOTS at (alpha,beta), keep KEPT_SLOTS
# as the bivariate result's two variables. ONE file open at a time -- this
# function is called four times per sample point (once each for U0, U1, V0,
# V1), sequentially, and nothing from a previous call survives except the
# small MPolyRingElem it returned.
#
# Peak memory for a single call: O(chunk_terms) raw exponent/coefficient
# bytes (the read buffers below), plus a Dict{Tuple{Int,Int},UInt64}
# accumulator whose size is bounded by the number of DISTINCT (e3,e4) pairs
# actually appearing in the file -- which, for the box-shaped supports this
# project's Newton-polytope diagnostics already characterize (see
# diag_newton_polygon / detect_box_structure in pilot_diagnostic.jl and
# newton_polytope.jl respectively), is bounded by (deg_x3+1)*(deg_x4+1), NOT
# by the 17.8M raw term count -- this is the entire reason streaming
# specialization collapses a huge file into a small polynomial rather than
# just being a slower way to load the same amount of data.
function stream_specialize_one_at_a_time(path::String, expected_prime::UInt64,
                                          alpha, beta, S2;
                                          chunk_terms::Int = 1_000_000)
    isfile(path) ||
        error("stream_specialize_one_at_a_time: no such file: $path")

    fsize_mb = filesize(path) / 1024 / 1024
    println("      streaming ", path, " (", round(fsize_mb, digits=1), " MB on disk)...")
    flush(stdout)
    t0 = time()

    p = expected_prime
    alpha_r = coeff_to_u64(alpha) % p
    beta_r  = coeff_to_u64(beta)  % p

    fixed1_idx, fixed2_idx = FIXED_SLOTS
    kept1_idx, kept2_idx   = KEPT_SLOTS

    acc = Dict{Tuple{Int,Int}, UInt64}()

    exp_io   = open(path, "r")
    coeff_io = open(path, "r")

    try
        magic = read(exp_io, UInt64)
        magic == NATIVE_SUPPORT_MAGIC_V2 ||
            error("stream_specialize_one_at_a_time: $path does not have the " *
                  "expected NEWTPOL2 header (got $(magic)) -- this script " *
                  "requires v2 files WITH coefficients, produced by " *
                  "convert_to_native.jl <in> <out> <ambient_dim> <prime>")

        ambient_dim = read(exp_io, Int64)
        ambient_dim == 4 ||
            error("stream_specialize_one_at_a_time: expected ambient_dim=4 " *
                  "(x1,x2,x3,x4), got $ambient_dim in $path")

        n_terms = read(exp_io, Int64)
        n_terms > 0 ||
            error("stream_specialize_one_at_a_time: invalid n_terms=$n_terms in $path")

        file_prime = read(exp_io, UInt64)
        file_prime == expected_prime ||
            error("stream_specialize_one_at_a_time: $path has prime=$file_prime " *
                  "in its header, expected $expected_prime")

        read(coeff_io, UInt64); read(coeff_io, Int64)
        read(coeff_io, Int64);  read(coeff_io, UInt64)

        exp_offset = position(exp_io)
        coeff_offset = exp_offset + ambient_dim * n_terms * sizeof(NATIVE_SUPPORT_EXP_TYPE)
        seek(coeff_io, coeff_offset)

        alpha_pow_cache = Dict{Int,UInt64}(0 => UInt64(1))
        beta_pow_cache  = Dict{Int,UInt64}(0 => UInt64(1))

        function cached_pow(cache::Dict{Int,UInt64}, base::UInt64, e::Int)
            get!(cache, e) do
                modpow(base, e, p)
            end
        end

        exp_buf   = Vector{NATIVE_SUPPORT_EXP_TYPE}(undef, ambient_dim * chunk_terms)
        coeff_buf = Vector{NATIVE_SUPPORT_COEFF_TYPE}(undef, chunk_terms)

        terms_done = 0

        while terms_done < n_terms
            this_chunk = min(chunk_terms, n_terms - terms_done)

            read!(exp_io, @view(exp_buf[1:ambient_dim*this_chunk]))
            read!(coeff_io, @view(coeff_buf[1:this_chunk]))

            @inbounds for i in 1:this_chunk
                base = (i - 1) * ambient_dim

                e_fixed1 = Int(exp_buf[base + fixed1_idx])
                e_fixed2 = Int(exp_buf[base + fixed2_idx])
                e_kept1  = Int(exp_buf[base + kept1_idx])
                e_kept2  = Int(exp_buf[base + kept2_idx])

                c = UInt64(coeff_buf[i]) % p

                a_pow = cached_pow(alpha_pow_cache, alpha_r, e_fixed1)
                b_pow = cached_pow(beta_pow_cache,  beta_r,  e_fixed2)

                scale = modmul(a_pow, b_pow, p)
                term  = modmul(c, scale, p)

                key = (e_kept1, e_kept2)
                acc[key] = haskey(acc, key) ? modadd(acc[key], term, p) : term
            end

            terms_done += this_chunk

            if terms_done % 5_000_000 == 0 || terms_done == n_terms
                println("        ", terms_done, "/", n_terms, " terms streamed (",
                        round(time() - t0, digits=1), "s)")
                flush(stdout)
            end
        end
    finally
        close(exp_io)
        close(coeff_io)
    end

    ctx = MPolyBuildCtx(S2)
    Fp = base_ring(S2)

    for ((k1, k2), c_u) in acc
        iszero(c_u) && continue
        push_term!(ctx, Fp(c_u), [k1, k2])
    end

    poly = finish(ctx)

    println("      done in ", round(time() - t0, digits=1), "s (",
            length(poly), " terms after collapsing) -- source file's term ",
            "arrays now released")
    flush(stdout)

    return poly
end

# ---------------------------------------------------------------------------
# Bivariate colength of <u0,u1,v0,v1> in Fp[x3,x4], via a grevlex Groebner
# basis and leading-monomial staircase count -- the 4-generator
# generalization of run_worker's "grevlex_analysis" strategy in
# pilot_diagnostic.jl (that one only ever built ideal(S2, [g0,g1]) for a
# SINGLE pair; this builds ideal(S2, [u0,u1,v0,v1]), all four collapsed
# generators at once, which is fine memory-wise because by this point all
# four are small bivariate polynomials, not 4-variable 17.8M-term ones).
#
# Runs standalone (own main(), dispatched via a worker flag) so it can be
# invoked in a killable subprocess with a hard timeout, exactly like
# pilot_diagnostic.jl's run_worker/run_with_timeout -- a bivariate grevlex
# Groebner basis for a 4-generator near-zero-dimensional ideal is not
# guaranteed to be fast, and pilot_diagnostic.jl's own history (this file's
# stated purpose: lex/FGLM were hanging) is reason enough not to trust an
# in-process call without a kill switch.
const WORKER_FLAG = "--dimension-worker"

function serialize_bivariate_system(path, prime::UInt64, u0, u1, v0, v1)
    data = Any[prime]
    for g in (u0, u1, v0, v1)
        supp = collect(AbstractAlgebra.exponent_vectors(g))
        coef = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g)]
        push!(data, supp)
        push!(data, coef)
    end
    open(path, "w") do io
        serialize(io, Tuple(data))
    end
end

# Computes the colength (standard monomial count) of <u0,u1,v0,v1> in
# Fp[x3,x4] via grevlex GB + staircase counting. Returns
# (:ok, elapsed, colength, info) or (:error, NaN, -1, message) or
# (:unbounded, elapsed, -1, message) if the ideal is NOT zero-dimensional
# (staircase search exceeds a generous cutoff without terminating) --
# reported distinctly from an outright error, since "not zero-dimensional"
# is itself the important finding this script is designed to surface (see
# the big header comment on what dim(I) means).
function bivariate_colength(u0, u1, v0, v1, prime::UInt64; staircase_cutoff::Int = 200_000)
    Fp = GF(prime)
    S2, (x3s, x4s) = polynomial_ring(Fp, [:x3, :x4])

    function rebuild(supp, coef)
        ctx = MPolyBuildCtx(S2)
        for (e, c) in zip(supp, coef)
            push_term!(ctx, Fp(c), e)
        end
        finish(ctx)
    end

    t0 = time()
    I = ideal(S2, [u0, u1, v0, v1])
    G = groebner_basis(I; ordering=degrevlex(S2))
    gb_elapsed = time() - t0

    lms = [leading_monomial(g; ordering=degrevlex(S2)) for g in G]
    lm_exps = [collect(AbstractAlgebra.exponent_vectors(m))[1] for m in lms]

    max_deg_bound = maximum(total_degree(g) for g in G; init=0)
    max_input_deg = maximum(total_degree(g) for g in (u0, u1, v0, v1))
    search_bound = max(2 * max_deg_bound, 2 * max_input_deg, 4)

    function divides_some_lm(e3, e4)
        for (a, b) in lm_exps
            if e3 >= a && e4 >= b
                return true
            end
        end
        return false
    end

    standard_monomials = Tuple{Int,Int}[]
    box_exceeded = false
    for e3 in 0:search_bound
        for e4 in 0:search_bound
            if !divides_some_lm(e3, e4)
                push!(standard_monomials, (e3, e4))
                if length(standard_monomials) > staircase_cutoff
                    box_exceeded = true
                    break
                end
            end
        end
        box_exceeded && break
    end

    elapsed = time() - t0

    if box_exceeded
        return (:unbounded, elapsed, -1,
                "grevlex basis size=$(length(G)) (computed in $(round(gb_elapsed,digits=3))s), " *
                "standard-monomial staircase exceeded cutoff=$staircase_cutoff within " *
                "search bound $search_bound -- ideal is likely NOT zero-dimensional at " *
                "this sample point (or the true colength genuinely exceeds the cutoff; " *
                "raise staircase_cutoff to tell the two apart)")
    end

    colength = length(standard_monomials)
    return (:ok, elapsed, colength,
            "grevlex basis size=$(length(G)) (computed in $(round(gb_elapsed,digits=3))s), " *
            "colength (standard monomials)=$colength, search_bound=$search_bound")
end

function run_worker(infile::String, outfile::String, staircase_cutoff::Int)
    data = open(deserialize, infile)
    prime = data[1]

    Fp = GF(prime)
    S2, _ = polynomial_ring(Fp, [:x3, :x4])
    function rebuild(supp, coef)
        ctx = MPolyBuildCtx(S2)
        for (e, c) in zip(supp, coef)
            push_term!(ctx, Fp(c), e)
        end
        finish(ctx)
    end

    polys = MPolyRingElem[]
    for i in 2:2:length(data)
        push!(polys, rebuild(data[i], data[i+1]))
    end
    u0, u1, v0, v1 = polys

    result = try
        bivariate_colength(u0, u1, v0, v1, prime; staircase_cutoff=staircase_cutoff)
    catch e
        (:error, NaN, -1, sprint(showerror, e))
    end

    open(outfile, "w") do io
        serialize(io, result)
    end
end

function run_with_timeout(prime, u0, u1, v0, v1, timeout_secs::Real, script_path::String,
                          staircase_cutoff::Int)
    tmpdir = mktempdir()
    infile = joinpath(tmpdir, "in.jls")
    outfile = joinpath(tmpdir, "out.jls")

    try
        serialize_bivariate_system(infile, prime, u0, u1, v0, v1)

        cmd = `julia --startup-file=no $script_path $WORKER_FLAG $infile $outfile $staircase_cutoff`
        proc = run(pipeline(cmd; stdout=devnull, stderr=devnull); wait=false)

        deadline = time() + timeout_secs
        while process_running(proc) && time() < deadline
            sleep(0.2)
        end

        if process_running(proc)
            try; kill(proc, Base.SIGKILL); catch; end
            try; wait(proc); catch; end
            return (:timeout, NaN, -1, "TIMEOUT (exceeded $(timeout_secs)s, subprocess killed)")
        end

        if !isfile(outfile)
            return (:error, NaN, -1, "worker exited without producing a result (crashed or killed externally)")
        end

        return open(deserialize, outfile)
    finally
        rm(tmpdir; recursive=true, force=true)
    end
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()
    length(ARGS) >= 5 ||
        error("streaming_ideal_dimension.jl: usage: julia streaming_ideal_dimension.jl " *
              "<U0.native> <U1.native> <V0.native> <V1.native> <prime> " *
              "[n_samples] [seed] [timeout_secs] [chunk_terms]")

    u0_path = ARGS[1]
    u1_path = ARGS[2]
    v0_path = ARGS[3]
    v1_path = ARGS[4]
    prime = parse(UInt64, ARGS[5])
    n_samples   = length(ARGS) >= 6 ? parse(Int, ARGS[6])     : 8
    seed        = length(ARGS) >= 7 ? parse(Int, ARGS[7])     : 0
    timeout_secs = length(ARGS) >= 8 ? parse(Float64, ARGS[8]) : 60.0
    chunk_terms = length(ARGS) >= 9 ? parse(Int, ARGS[9])     : 1_000_000

    for path in (u0_path, u1_path, v0_path, v1_path)
        isfile(path) || error("streaming_ideal_dimension.jl: no such file: $path")
    end

    script_path = abspath(@__FILE__)

    println("=" ^ 70)
    println("Streaming dim(I) estimator for I = <U0,U1,V0,V1> in Fp[x1,x2,x3,x4]")
    println("=" ^ 70)
    println("U0 file:     ", u0_path)
    println("U1 file:     ", u1_path)
    println("V0 file:     ", v0_path)
    println("V1 file:     ", v1_path)
    println("prime:       ", prime)
    println("samples:     ", n_samples, " (seed=", seed, ")")
    println("timeout:     ", timeout_secs, "s per sample's bivariate GB (subprocess)")
    println("chunk_terms: ", chunk_terms)
    println()
    println("CONVENTION IN USE: fixing slots ", FIXED_SLOTS, " (x1,x2), keeping slots ",
            KEPT_SLOTS, " (x3,x4) -- see the CAVEAT comment above main() if this needs to change.")
    println()
    println("At most one native file's exponent/coefficient arrays are ever held in ")
    println("memory at once -- see stream_specialize_one_at_a_time's docstring.")
    println()

    Fp = GF(prime)
    S2, _ = polynomial_ring(Fp, [:x3, :x4])

    rng = Random.MersenneTwister(seed)
    samples = Tuple{elem_type(Fp), elem_type(Fp)}[]
    while length(samples) < n_samples
        a = Fp(rand(rng, 1:(prime - 1)))
        b = Fp(rand(rng, 1:(prime - 1)))
        push!(samples, (a, b))
    end

    colengths = Int[]
    statuses  = Symbol[]

    for (i, (a, b)) in enumerate(samples)
        println("=" ^ 70)
        println("Sample ", i, "/", n_samples, ": (x1,x2) = (", a, ",", b, ")")
        println("=" ^ 70)
        flush(stdout)

        println("  streaming+specializing U0, U1, V0, V1 ONE AT A TIME...")
        t0 = time()
        u0 = stream_specialize_one_at_a_time(u0_path, prime, a, b, S2; chunk_terms=chunk_terms)
        u1 = stream_specialize_one_at_a_time(u1_path, prime, a, b, S2; chunk_terms=chunk_terms)
        v0 = stream_specialize_one_at_a_time(v0_path, prime, a, b, S2; chunk_terms=chunk_terms)
        v1 = stream_specialize_one_at_a_time(v1_path, prime, a, b, S2; chunk_terms=chunk_terms)
        println("  all four specialized in ", round(time() - t0, digits=2), "s ",
                "(U0=", length(u0), ", U1=", length(u1), ", V0=", length(v0),
                ", V1=", length(v1), " terms)")
        flush(stdout)

        println("  computing bivariate colength of <U0,U1,V0,V1> in Fp[x3,x4] ",
                "(subprocess, timeout=", timeout_secs, "s)...")
        flush(stdout)
        status, elapsed, colength, info = run_with_timeout(
            prime, u0, u1, v0, v1, timeout_secs, script_path, 200_000
        )

        push!(statuses, status)
        if status == :ok
            push!(colengths, colength)
            println("    OK in ", round(elapsed, digits=3), "s: colength=", colength)
        elseif status == :timeout
            println("    TIMEOUT: ", info)
        elseif status == :unbounded
            println("    NOT ZERO-DIMENSIONAL (or cutoff too small): ", info)
        else
            println("    ERROR: ", info)
        end
        println("        ", info)
        println()
    end

    println("=" ^ 70)
    println("Summary")
    println("=" ^ 70)
    n_ok = count(==(:ok), statuses)
    n_timeout = count(==(:timeout), statuses)
    n_unbounded = count(==(:unbounded), statuses)
    n_error = count(==(:error), statuses)
    println("completed: ", n_ok, "/", n_samples,
            "   timed out: ", n_timeout, "/", n_samples,
            "   not-zero-dim/cutoff: ", n_unbounded, "/", n_samples,
            "   errored: ", n_error, "/", n_samples)
    println()

    if n_unbounded > 0
        println("WARNING: at least one sample point's bivariate colength search did not ")
        println("terminate within its cutoff. Per this script's own stated assumptions ")
        println("(see the header comment on what dim(I) means), this is a signal that ")
        println("either V(I) is NOT zero-dimensional, or the true colength exceeds the ")
        println("cutoff used here -- re-run with a larger staircase_cutoff (edit the ")
        println("200_000 literal above, or expose it as a CLI argument) to tell these ")
        println("apart before trusting any number below.")
        println()
    end

    if isempty(colengths)
        println("No sample produced a colength (all timed out / errored / unbounded) -- ")
        println("dim(I) could not be estimated from this run. See per-sample notes above.")
    elseif all(==(colengths[1]), colengths)
        println("dim(I) estimate: CONSISTENT at ", colengths[1],
                " across ", length(colengths), " completed sample(s)")
        println()
        println("Per the header comment's caveat: this is the colength of the generic ")
        println("(x1,x2)-fiber, repeated identically across independent random samples. ")
        println("That stabilization is evidence for -- not a proof of -- dim(I) = ",
                colengths[1], ". A single unlucky/non-generic sample point could in ")
        println("principle agree by coincidence; more independent samples (raise ")
        println("n_samples) strengthen this evidence further.")
    else
        println("dim(I) estimate: INCONSISTENT across samples: ", colengths)
        println()
        println("This is the important finding, not a bug to work around: either some ")
        println("sample points were non-generic (unlucky (x1,x2) choice landing on a ")
        println("special fiber -- try more samples / a different seed to see if a ")
        println("majority value emerges), or V(I) genuinely is not equidimensional/not ")
        println("zero-dimensional as assumed. Do not average or otherwise combine these ")
        println("numbers into a single answer without resolving which case this is.")
    end
end

# ---------------------------------------------------------------------------
# Entry point dispatch (worker subprocess vs normal invocation), same
# pattern as pilot_diagnostic.jl's own dispatch at the bottom of that file.
# ---------------------------------------------------------------------------

if length(ARGS) >= 1 && ARGS[1] == WORKER_FLAG
    length(ARGS) >= 4 ||
        error("streaming_ideal_dimension.jl: worker mode expects " *
              "$WORKER_FLAG <infile> <outfile> <staircase_cutoff>")
    run_worker(ARGS[2], ARGS[3], parse(Int, ARGS[4]))
else
    main()
end
