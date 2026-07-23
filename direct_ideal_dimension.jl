#!/usr/bin/env julia
#
# direct_ideal_dimension.jl
#
# Computes dim(I) for I = <U0,U1> in Fp[x1,x2,x3,x4] DIRECTLY -- no
# specialization, no sampling, no bivariate proxy. This is the actual
# Krull dimension of Fp[x1,x2,x3,x4]/I (via a Groebner basis computed once,
# in the full 4-variable ring), plus -- if that dimension comes out
# positive, i.e. V(I) is NOT a finite point set -- the degree of V(I) as a
# projective/affine variety, read off the same Groebner basis's Hilbert
# series, since that is cheap to obtain once the GB itself is in hand and a
# bare dimension number is not by itself very informative for a
# positive-dimensional variety.
#
# ---------------------------------------------------------------------------
# Why this is different from pair_ideal_dimension.jl / streaming_ideal_dimension.jl
# ---------------------------------------------------------------------------
#
# Both of those scripts compute a PROXY: fix (x1,x2) at a random point,
# collapse the generators to a small bivariate system in (x3,x4), and count
# standard monomials there. That proxy is only meaningful as "dim(I)" in the
# colength sense if V(I) is zero-dimensional to begin with -- and for
# <U0,U1> (2 generators in 4 ambient variables) that is NOT the generic
# case; V(<U0,U1>) is generically a surface (dimension 2), not a finite set
# of points.
#
# This script does not specialize anything and does not assume
# zero-dimensionality one way or the other. It builds ideal(R4, [U0,U1]) in
# the FULL ring R4 = Fp[x1,x2,x3,x4] and asks Oscar directly for:
#
#   1. dim(I) -- the Krull dimension of R4/I. For 2 generators that form a
#      regular sequence (the expected generic case, absent some special
#      coincidence making U0,U1 share a non-trivial common factor or having
#      the pair fail to be a system of parameters), Krull's principal ideal
#      theorem gives dim(R4/I) = 4 - 2 = 2 automatically, but this script
#      does not assume that either -- it reads the actual number back from
#      the Groebner basis via Oscar's dim(I).
#
#   2. IF dim(I) > 0 (the expected case): the DEGREE of the variety V(I),
#      read off the leading behavior of the Hilbert series / Hilbert
#      polynomial of R4/I with respect to the same Groebner basis (this is
#      "free" once the GB is computed -- Oscar's hilbert_series /
#      degree(I) reuse the GB rather than requiring separate work). Degree
#      here means the usual scheme-theoretic degree of a projective variety
#      of dimension d: the positive integer D such that the Hilbert
#      polynomial has leading term D/d! * t^d. This generalizes "colength"
#      to the positive-dimensional case in the sense that both are read off
#      the same Hilbert data; colength IS the degree when dim(I) = 0.
#
#   3. IF dim(I) == 0: also report the colength (Oscar's vector_space_dim /
#      equivalently degree(I) in the zero-dimensional case coincide), for
#      direct comparability with what pair_ideal_dimension.jl's per-sample
#      colength numbers were estimating.
#
# ---------------------------------------------------------------------------
# Cost and honesty
# ---------------------------------------------------------------------------
#
# THIS IS THE EXPENSIVE, NON-STREAMED COMPUTATION the earlier scripts were
# explicitly built to avoid for the 4-generator <U0,U1,V0,V1> case (V0/V1's
# 88.5M-term files are far too large to hold as live 4-variable
# MPolyRingElem objects). It is attempted here ONLY for <U0,U1>, whose two
# generators are small enough to hold resident (408.6 MB / 17.85M raw terms
# each, per the logs from the earlier scripts) -- but "small enough to
# load" is not the same as "cheap to compute a 4-variable Groebner basis
# from". A degrevlex GB of two dense-ish quartic-ambient-dimension
# polynomials with millions of terms each is a serious computation with no
# principled runtime estimate in advance; there is no guarantee it finishes
# in any particular amount of time, and no sampling/streaming trick can
# shortcut it, because dim(I) and degree(I) are properties of the WHOLE
# ideal, not of any single fiber.
#
# This script does not silently hang forever: it runs the GB + dimension +
# Hilbert-data computation in a killable subprocess with a hard timeout,
# same discipline as the earlier scripts' run_with_timeout, so a
# non-terminating run is reported as :timeout rather than leaving you
# unsure whether the process is stuck or just slow.
#
# No number reported here is a proxy or an estimate -- if the computation
# completes, dim(I) and degree(I) (or colength, in the zero-dimensional
# case) are exact, certified values, not samples. The only uncertainty is
# whether the computation finishes within the timeout at all.
#
# ---------------------------------------------------------------------------
# Usage
# ---------------------------------------------------------------------------
#   julia direct_ideal_dimension.jl <U0.native> <U1.native> <prime> [timeout_secs]
#
#   U0/U1.native  : NEWTPOL2 v2 native files (WITH coefficients), same
#                   convention as streaming_ideal_dimension.jl /
#                   pair_ideal_dimension.jl / pilot_diagnostic.jl.
#   prime         : Fp modulus, must match every file's stored prime.
#   timeout_secs  : hard timeout, in seconds, for the GB + dimension +
#                   Hilbert-data computation, run in a killable subprocess
#                   (default 7200 = 2 hours -- longer than
#                   pair_ideal_dimension.jl's 1800s default for the
#                   bivariate case, because a 4-variable GB on inputs this
#                   size is a much larger computation than a 2-variable one
#                   and there is no data yet on how long it actually takes;
#                   raise this further and rerun if it times out -- that
#                   alone does not mean anything is wrong, only that this
#                   starting guess wasn't enough).

using Oscar
using Serialization

include(joinpath(@__DIR__, "newton_polytope.jl"))  # for NATIVE_SUPPORT_MAGIC_V2 etc., and coeff/modarith reuse

# ---------------------------------------------------------------------------
# Native-file loading, reused verbatim from pair_ideal_dimension.jl /
# streaming_ideal_dimension.jl -- loads U0/U1's raw exponent/coefficient
# arrays and builds them DIRECTLY as elements of the full 4-variable ring
# Fp[x1,x2,x3,x4] (no specialization -- this is the one place this script's
# loading path differs from the earlier ones, which built RawNative structs
# and specialized per-sample into a 2-variable ring; here there is only one
# ring, R4, and generators are built once, directly in it).
# ---------------------------------------------------------------------------

function load_native_as_poly(path::String, expected_prime::UInt64, R4)
    isfile(path) ||
        error("load_native_as_poly: no such file: $path")

    fsize_mb = filesize(path) / 1024 / 1024
    println("  loading ", path, " (", round(fsize_mb, digits=1),
            " MB on disk) directly into Fp[x1,x2,x3,x4]...")
    flush(stdout)
    t0 = time()

    io = open(path, "r")
    local ambient_dim, n_terms
    try
        magic = read(io, UInt64)
        magic == NATIVE_SUPPORT_MAGIC_V2 ||
            error("load_native_as_poly: $path does not have the expected NEWTPOL2 " *
                  "header (got $(magic)) -- requires v2 files WITH coefficients, " *
                  "produced by convert_to_native.jl <in> <out> <ambient_dim> <prime>")

        ambient_dim = read(io, Int64)
        ambient_dim == 4 ||
            error("load_native_as_poly: expected ambient_dim=4 (x1,x2,x3,x4), " *
                  "got $ambient_dim in $path")

        n_terms = read(io, Int64)
        n_terms > 0 ||
            error("load_native_as_poly: invalid n_terms=$n_terms in $path")

        file_prime = read(io, UInt64)
        file_prime == expected_prime ||
            error("load_native_as_poly: $path has prime=$file_prime in its header, " *
                  "expected $expected_prime")

        exps = Vector{NATIVE_SUPPORT_EXP_TYPE}(undef, ambient_dim * n_terms)
        read!(io, exps)

        coeff_offset = position(io)
        expected_coeff_offset = 8 + 8 + 8 + 8 + ambient_dim * n_terms * sizeof(NATIVE_SUPPORT_EXP_TYPE)
        coeff_offset == expected_coeff_offset ||
            error("load_native_as_poly: unexpected coeff block offset in $path " *
                  "(got $coeff_offset, expected $expected_coeff_offset) -- " *
                  "native file layout assumption violated, refusing to guess")

        coeffs = Vector{NATIVE_SUPPORT_COEFF_TYPE}(undef, n_terms)
        read!(io, coeffs)

        Fp = base_ring(R4)
        ctx = MPolyBuildCtx(R4)
        p = expected_prime
        @inbounds for i in 1:n_terms
            base = (i - 1) * ambient_dim
            e1 = Int(exps[base + 1])
            e2 = Int(exps[base + 2])
            e3 = Int(exps[base + 3])
            e4 = Int(exps[base + 4])
            c = UInt64(coeffs[i]) % p
            iszero(c) && continue
            push_term!(ctx, Fp(c), [e1, e2, e3, e4])
        end
        poly = finish(ctx)

        println("    done in ", round(time() - t0, digits=1), "s (",
                n_terms, " raw terms -> ", length(poly), " terms in R4)")
        flush(stdout)

        return poly
    finally
        close(io)
    end
end

# ---------------------------------------------------------------------------
# Serialization helpers for the worker subprocess -- pass U0/U1's support +
# coefficients (not the built polynomial object, which doesn't survive
# process boundaries) plus the prime, exactly as the earlier scripts did for
# their bivariate systems.
# ---------------------------------------------------------------------------

function coeff_to_u64(c)
    try
        return UInt64(Int(c))
    catch
        return UInt64(lift(ZZ, c))
    end
end

function serialize_system(path, prime::UInt64, u0, u1)
    data = Any[prime]
    for g in (u0, u1)
        supp = collect(AbstractAlgebra.exponent_vectors(g))
        coef = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g)]
        push!(data, supp)
        push!(data, coef)
    end
    open(path, "w") do io
        serialize(io, Tuple(data))
    end
end

const WORKER_FLAG = "--dimension-worker"

# Computes dim(I) and, depending on that dimension, degree(I) or colength,
# for I = <u0,u1> in the full ring Fp[x1,x2,x3,x4]. Returns
# (:ok, elapsed, dim, extra_kind, extra_value, info) where extra_kind is
# :degree (dim > 0) or :colength (dim == 0), or (:error, NaN, -1, :none,
# -1, message) on failure.
function ideal_dimension_and_degree(u0, u1, prime::UInt64)
    Fp = GF(prime)
    R4, (x1s, x2s, x3s, x4s) = polynomial_ring(Fp, [:x1, :x2, :x3, :x4])

    t0 = time()
    println("  [worker] building ideal(R4, [U0,U1]) and starting Groebner basis...")
    flush(stdout)
    I = ideal(R4, [u0, u1])
    G = groebner_basis(I; ordering=degrevlex(R4))
    gb_elapsed = time() - t0
    println("  [worker] GB done in ", round(gb_elapsed, digits=3),
            "s, basis size=", length(G), " -- computing dim(I)...")
    flush(stdout)

    d = dim(I)
    dim_elapsed = time() - t0
    println("  [worker] dim(I) = ", d, " (", round(dim_elapsed - gb_elapsed, digits=3),
            "s after GB) -- computing degree/colength...")
    flush(stdout)

    if d == 0
        colength = vector_space_dimension(quo(R4, I)[1])
        elapsed = time() - t0
        return (:ok, elapsed, d, :colength, colength,
                "grevlex basis size=$(length(G)) (GB in $(round(gb_elapsed,digits=3))s), " *
                "dim(I)=0, colength (=vector space dim of R4/I)=$colength")
    else
        D = degree(I)
        elapsed = time() - t0
        return (:ok, elapsed, d, :degree, D,
                "grevlex basis size=$(length(G)) (GB in $(round(gb_elapsed,digits=3))s), " *
                "dim(I)=$d (V(I) is positive-dimensional), degree(I)=$D " *
                "(leading Hilbert-polynomial coefficient x $(factorial(d)), " *
                "i.e. the usual scheme-theoretic degree of the dimension-$d variety V(I))")
    end
end

function run_worker(infile::String, outfile::String)
    data = open(deserialize, infile)
    prime = data[1]

    Fp = GF(prime)
    R4, _ = polynomial_ring(Fp, [:x1, :x2, :x3, :x4])
    function rebuild(supp, coef)
        ctx = MPolyBuildCtx(R4)
        for (e, c) in zip(supp, coef)
            push_term!(ctx, Fp(c), e)
        end
        finish(ctx)
    end

    polys = MPolyRingElem[]
    for i in 2:2:length(data)
        push!(polys, rebuild(data[i], data[i+1]))
    end
    u0, u1 = polys

    result = try
        ideal_dimension_and_degree(u0, u1, prime)
    catch e
        (:error, NaN, -1, :none, -1, sprint(showerror, e))
    end

    open(outfile, "w") do io
        serialize(io, result)
    end
end

function run_with_timeout(prime, u0, u1, timeout_secs::Real, script_path::String)
    tmpdir = mktempdir()
    infile = joinpath(tmpdir, "in.jls")
    outfile = joinpath(tmpdir, "out.jls")

    try
        serialize_system(infile, prime, u0, u1)

        cmd = `julia --startup-file=no $script_path $WORKER_FLAG $infile $outfile`
        proc = run(pipeline(cmd; stdout=devnull, stderr=devnull); wait=false)

        deadline = time() + timeout_secs
        while process_running(proc) && time() < deadline
            sleep(0.5)
        end

        if process_running(proc)
            try; kill(proc, Base.SIGKILL); catch; end
            try; wait(proc); catch; end
            return (:timeout, NaN, -1, :none, -1, "TIMEOUT (exceeded $(timeout_secs)s, subprocess killed)")
        end

        if !isfile(outfile)
            return (:error, NaN, -1, :none, -1, "worker exited without producing a result (crashed or killed externally)")
        end

        try
            return open(deserialize, outfile)
        catch e
            error("run_with_timeout: worker process exited (not killed by our timeout) " *
                  "and left a result file at $outfile, but it failed to deserialize " *
                  "-- the file is corrupt or truncated. This is NOT reported as an " *
                  "ordinary (:error, ...) status because a bad result file is a " *
                  "different failure mode from a worker exception (run_worker's own " *
                  "try/catch already reports those cleanly) and silently downgrading " *
                  "it would hide a serialization/IO bug rather than surface it. " *
                  "Underlying error: $(sprint(showerror, e))")
        end
    finally
        rm(tmpdir; recursive=true, force=true)
    end
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()
    length(ARGS) >= 3 ||
        error("direct_ideal_dimension.jl: usage: julia direct_ideal_dimension.jl " *
              "<U0.native> <U1.native> <prime> [timeout_secs]")

    u0_path = ARGS[1]
    u1_path = ARGS[2]
    prime = parse(UInt64, ARGS[3])
    timeout_secs = length(ARGS) >= 4 ? parse(Float64, ARGS[4]) : 7200.0

    for path in (u0_path, u1_path)
        isfile(path) || error("direct_ideal_dimension.jl: no such file: $path")
    end

    script_path = abspath(@__FILE__)

    println("=" ^ 70)
    println("Direct dim(I) + degree(I) for I = <U0,U1> in Fp[x1,x2,x3,x4]")
    println("(no specialization -- full 4-variable Groebner basis)")
    println("=" ^ 70)
    println("U0 file:     ", u0_path)
    println("U1 file:     ", u1_path)
    println("prime:       ", prime)
    println("timeout:     ", timeout_secs, "s for the GB + dim + degree computation (subprocess)")
    println()
    println("This computes dim(I) and degree(I) EXACTLY (or colength, if dim(I)=0) -- ")
    println("not an estimate. No sampling, no bivariate proxy. See the header comment ")
    println("for cost caveats: this is a full 4-variable Groebner basis on two ")
    println("million-plus-term generators, with no advance runtime guarantee.")
    println()

    Fp = GF(prime)
    R4, _ = polynomial_ring(Fp, [:x1, :x2, :x3, :x4])

    println("Loading U0/U1 directly into Fp[x1,x2,x3,x4]...")
    flush(stdout)
    u0 = load_native_as_poly(u0_path, prime, R4)
    u1 = load_native_as_poly(u1_path, prime, R4)
    println()

    println("Computing dim(I) and degree/colength (subprocess, timeout=", timeout_secs, "s)...")
    flush(stdout)
    status, elapsed, d, extra_kind, extra_value, info = run_with_timeout(
        prime, u0, u1, timeout_secs, script_path
    )

    println()
    println("=" ^ 70)
    println("Result")
    println("=" ^ 70)
    if status == :ok
        println("dim(I) = ", d, "   (Krull dimension of Fp[x1,x2,x3,x4]/<U0,U1>)")
        if extra_kind == :colength
            println("colength (dim(I)=0 case) = ", extra_value)
        else
            println("degree(I) = ", extra_value,
                    "   (V(I) is positive-dimensional; this is the scheme-theoretic ",
                    "degree of that dimension-", d, " variety)")
        end
        println()
        println("Completed in ", round(elapsed, digits=3), "s. ", info)
        println()
        println("This is an EXACT, certified result (given the Groebner-basis computation ")
        println("terminated correctly) -- not a sample-based estimate.")
    elseif status == :timeout
        println("TIMEOUT: the GB + dimension computation did not finish within ",
                timeout_secs, "s.")
        println("This says nothing about dim(I) itself -- only that this computation is ")
        println("more expensive than the timeout budget. Rerun with a larger ")
        println("timeout_secs argument.")
    elseif status == :error
        println("ERROR: ", info)
    else
        println("UNEXPECTED STATUS: ", status, " -- ", info)
    end
end

# ---------------------------------------------------------------------------
# Entry point dispatch (worker subprocess vs normal invocation), same
# pattern as pair_ideal_dimension.jl / streaming_ideal_dimension.jl.
# ---------------------------------------------------------------------------

if length(ARGS) >= 1 && ARGS[1] == WORKER_FLAG
    length(ARGS) >= 3 ||
        error("direct_ideal_dimension.jl: worker mode expects " *
              "$WORKER_FLAG <infile> <outfile>")
    run_worker(ARGS[2], ARGS[3])
else
    main()
end
