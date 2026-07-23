#!/usr/bin/env julia
#
# pair_ideal_dimension.jl
#
# Estimates dim(I) for I = <U0,U1> in Fp[x1,x2,x3,x4].
#
# This is the 2-generator analogue of streaming_ideal_dimension.jl (which
# computes the same kind of estimate for the 4-generator ideal
# <U0,U1,V0,V1>). It is derived from that script and keeps the same file
# format, CLI conventions, and honesty caveats, but is simplified in one
# important way:
#
#   <U0,U1> only involves the two SMALL native files (408.6 MB each, 17.85M
#   raw terms each, per streaming_ideal_dimension.jl's own header comments
#   and the U0/U1 numbers logged in err.txt from that script's run). Both
#   fit comfortably in memory at once -- U0+U1 together is ~820MB, nowhere
#   near the "only one V-sized file fits" constraint that forced V0/V1 onto
#   a one-at-a-time disk-streaming path in streaming_ideal_dimension.jl.
#   There is therefore no V-style streaming code in this script at all: both
#   U0 and U1 are loaded once (raw_load_native, reused verbatim from
#   streaming_ideal_dimension.jl) and specialized per-sample from resident
#   memory (specialize_from_raw, also reused verbatim). No file is ever
#   re-opened after its one initial load.
#
# ---------------------------------------------------------------------------
# What "dim(I)" means here, and why this script computes a PROXY, not the
# certified answer
# ---------------------------------------------------------------------------
#
# Exactly the same caveat as streaming_ideal_dimension.jl, restated for the
# 2-generator case:
#
# IF V(I) for I = <U0,U1> is zero-dimensional as a variety in x1,x2,x3,x4
# (this is a MUCH stronger assumption for 2 equations in 4 unknowns than it
# was for streaming_ideal_dimension.jl's 4-equations-in-4-unknowns case --
# generically, 2 equations in 4 unknowns cut out a SURFACE, i.e. a
# 2-dimensional variety, not a finite set of points. This script does not
# assume away that possibility; it is exactly what the per-sample
# stabilization check below is designed to expose, see the INCONSISTENT /
# ever-growing-count branch in the summary), THEN "dim(I)" in the sense that
# matters here is the COLENGTH
#
#     dim(I) := dim_{Fp} Fp[x1,x2,x3,x4] / I
#
# i.e. the degree of the zero-dimensional scheme V(I), counted with
# multiplicity.
#
# If instead V(<U0,U1>) is positive-dimensional -- which, again, is the
# GENERIC expectation for 2 equations in 4 unknowns, not a corner case --
# then fixing only (x1,x2) and computing a bivariate colength in the
# remaining (x3,x4) does NOT collapse to a finite set: the "bivariate
# colength" computed at a sample (alpha,beta) is instead counting the
# (finite, generically) intersection of a curve V(<U0,U1>) with the
# hyperplane slice {x1=alpha, x2=beta} -- which is itself a perfectly
# well-defined and useful number (the DEGREE of the residual curve/surface
# in the eliminated variables, at a generic slice) but is NOT dim(I) in the
# colength-of-the-whole-ideal sense above. This script computes exactly the
# same per-sample bivariate colength that streaming_ideal_dimension.jl
# computes for the 4-generator case, applied here to only <u0,u1>, and
# states in its final summary -- explicitly, every time -- that consistency
# across samples is evidence the SLICE behaves uniformly, not a proof that
# V(<U0,U1>) is zero-dimensional or that this number equals
# dim_{Fp} Fp[x1,x2,x3,x4]/<U0,U1>. If V(<U0,U1>) is positive-dimensional in
# a way that also varies with the (x1,x2) slice (e.g. a ruled/non-flat
# family), the per-sample counts will simply disagree, and this script
# reports that as INCONSISTENT exactly like streaming_ideal_dimension.jl
# does -- it does not attempt to distinguish "genuinely inconsistent" from
# "positive-dimensional but flat" beyond that same stabilization check.
#
# THIS SCRIPT NEVER CLAIMS TO CERTIFY dim(I) EXACTLY, for the same three
# reasons streaming_ideal_dimension.jl gives (streamed specialization is
# exact; the bivariate GB + staircase count is exact given termination;
# whether the generic-fiber colength equals the whole ideal's colength is
# an empirically-tested hypothesis, not a theorem invoked here) -- restated
# below at the point where the summary is printed.
#
# ---------------------------------------------------------------------------
# Usage
# ---------------------------------------------------------------------------
#   julia pair_ideal_dimension.jl <U0.native> <U1.native> <prime> \
#         [n_samples] [seed] [timeout_secs]
#
#   U0/U1.native : NEWTPOL2 v2 native files (WITH coefficients), same
#                  convention as streaming_ideal_dimension.jl /
#                  pilot_diagnostic.jl.
#   prime        : Fp modulus, must match every file's stored prime.
#   n_samples    : number of independent random (x1,x2) sample points to
#                  test for colength stabilization (default 8).
#   seed         : RNG seed (default 0).
#   timeout_secs : hard timeout, in seconds, for the per-sample bivariate
#                  Groebner computation, run in a killable subprocess
#                  exactly like streaming_ideal_dimension.jl's
#                  run_with_timeout (default 1800 = 30 min -- same default
#                  and same rationale as that script: a degrevlex GB of a
#                  system this dense in 2 variables is routinely a
#                  multi-minute-to-hour computation).
#
# NOTE: there is no chunk_terms argument here (unlike
# streaming_ideal_dimension.jl), because there is no disk-streaming path in
# this script to chunk -- both native files are read once, in full, via
# raw_load_native.

using Oscar
using Random
using Serialization

include(joinpath(@__DIR__, "newton_polytope.jl"))  # for NATIVE_SUPPORT_MAGIC_V2 etc., and coeff/modarith reuse

# ---------------------------------------------------------------------------
# CAVEAT (same discrepancy noted in streaming_ideal_dimension.jl, carried
# over unchanged since it applies equally to U0/U1 here):
#
# pilot_diagnostic.jl's own header comment says "fix x1=alpha, x4=beta,
# eliminate x2, keep x3" -- but stream_specialize_native_to_poly's ACTUAL
# CODE in that file specializes x1 and x2 (exponent slots 1 and 2) and keeps
# x3,x4 (slots 3 and 4). This script follows the code (fix x1,x2; keep
# x3,x4), matching streaming_ideal_dimension.jl's own choice, not the
# docstring. If the intended convention was actually "fix x1,x4; keep
# x2,x3", swap FIXED_SLOTS/KEPT_SLOTS below -- and make sure this matches
# whatever convention streaming_ideal_dimension.jl is using in the same run,
# since U0/U1 files are shared inputs to both scripts.
# ---------------------------------------------------------------------------
const FIXED_SLOTS = (1, 2)   # x1, x2 -- specialized to random field elements
const KEPT_SLOTS   = (3, 4)  # x3, x4 -- survive as the bivariate ring's variables

# ---------------------------------------------------------------------------
# Raw modular arithmetic (identical to streaming_ideal_dimension.jl's
# helpers; duplicated rather than `include`d from that file so this script
# has no dependency on that file's own state/side effects at load time -- it
# only needs newton_polytope.jl's native-file format constants).
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
# Load-once-keep-resident path, for BOTH U0 and U1.
#
# Unlike streaming_ideal_dimension.jl (where this path was only safe for
# U0/U1 and V0/V1 had to stay on a disk-streaming path to respect the
# one-V-at-a-time memory constraint), this script has no such constraint:
# there are only two generators here, both U-sized (408.6 MB / 17.85M raw
# terms each per streaming_ideal_dimension.jl's own numbers), so BOTH are
# loaded once and kept resident for the whole run. Only the O(1) cheap
# modular-arithmetic specialization step (the @inbounds loop in
# specialize_from_raw below) repeats per sample -- neither file's 408.6MB
# disk read does.
struct RawNative
    ambient_dim::Int
    n_terms::Int
    exps::Vector{NATIVE_SUPPORT_EXP_TYPE}    # ambient_dim * n_terms, flat
    coeffs::Vector{NATIVE_SUPPORT_COEFF_TYPE} # n_terms
end

function raw_load_native(path::String, expected_prime::UInt64)
    isfile(path) ||
        error("raw_load_native: no such file: $path")

    fsize_mb = filesize(path) / 1024 / 1024
    println("      loading (once, resident for whole run) ", path,
            " (", round(fsize_mb, digits=1), " MB on disk)...")
    flush(stdout)
    t0 = time()

    io = open(path, "r")
    local ambient_dim, n_terms
    try
        magic = read(io, UInt64)
        magic == NATIVE_SUPPORT_MAGIC_V2 ||
            error("raw_load_native: $path does not have the expected NEWTPOL2 " *
                  "header (got $(magic)) -- requires v2 files WITH coefficients, " *
                  "produced by convert_to_native.jl <in> <out> <ambient_dim> <prime>")

        ambient_dim = read(io, Int64)
        ambient_dim == 4 ||
            error("raw_load_native: expected ambient_dim=4 (x1,x2,x3,x4), " *
                  "got $ambient_dim in $path")

        n_terms = read(io, Int64)
        n_terms > 0 ||
            error("raw_load_native: invalid n_terms=$n_terms in $path")

        file_prime = read(io, UInt64)
        file_prime == expected_prime ||
            error("raw_load_native: $path has prime=$file_prime in its header, " *
                  "expected $expected_prime")

        exps = Vector{NATIVE_SUPPORT_EXP_TYPE}(undef, ambient_dim * n_terms)
        read!(io, exps)

        coeff_offset = position(io)
        expected_coeff_offset = 8 + 8 + 8 + 8 + ambient_dim * n_terms * sizeof(NATIVE_SUPPORT_EXP_TYPE)
        coeff_offset == expected_coeff_offset ||
            error("raw_load_native: unexpected coeff block offset in $path " *
                  "(got $coeff_offset, expected $expected_coeff_offset) -- " *
                  "native file layout assumption violated, refusing to guess")

        coeffs = Vector{NATIVE_SUPPORT_COEFF_TYPE}(undef, n_terms)
        read!(io, coeffs)

        println("      done in ", round(time() - t0, digits=1), "s (",
                n_terms, " raw terms resident in memory, kept for whole run)")
        flush(stdout)

        return RawNative(ambient_dim, n_terms, exps, coeffs)
    finally
        close(io)
    end
end

function specialize_from_raw(raw::RawNative, expected_prime::UInt64, alpha, beta, S2)
    p = expected_prime
    alpha_r = coeff_to_u64(alpha) % p
    beta_r  = coeff_to_u64(beta)  % p

    fixed1_idx, fixed2_idx = FIXED_SLOTS
    kept1_idx, kept2_idx   = KEPT_SLOTS
    ambient_dim = raw.ambient_dim
    n_terms = raw.n_terms

    acc = Dict{Tuple{Int,Int}, UInt64}()

    alpha_pow_cache = Dict{Int,UInt64}(0 => UInt64(1))
    beta_pow_cache  = Dict{Int,UInt64}(0 => UInt64(1))

    function cached_pow(cache::Dict{Int,UInt64}, base::UInt64, e::Int)
        get!(cache, e) do
            modpow(base, e, p)
        end
    end

    @inbounds for i in 1:n_terms
        base = (i - 1) * ambient_dim

        e_fixed1 = Int(raw.exps[base + fixed1_idx])
        e_fixed2 = Int(raw.exps[base + fixed2_idx])
        e_kept1  = Int(raw.exps[base + kept1_idx])
        e_kept2  = Int(raw.exps[base + kept2_idx])

        c = UInt64(raw.coeffs[i]) % p

        a_pow = cached_pow(alpha_pow_cache, alpha_r, e_fixed1)
        b_pow = cached_pow(beta_pow_cache,  beta_r,  e_fixed2)

        scale = modmul(a_pow, b_pow, p)
        term  = modmul(c, scale, p)

        key = (e_kept1, e_kept2)
        acc[key] = haskey(acc, key) ? modadd(acc[key], term, p) : term
    end

    ctx = MPolyBuildCtx(S2)
    Fp = base_ring(S2)
    for ((k1, k2), c_u) in acc
        iszero(c_u) && continue
        push_term!(ctx, Fp(c_u), [k1, k2])
    end
    return finish(ctx)
end

# ---------------------------------------------------------------------------
# Bivariate colength of <u0,u1> in Fp[x3,x4], via a grevlex Groebner basis
# and leading-monomial staircase count -- same strategy as
# streaming_ideal_dimension.jl's bivariate_colength, restricted to the
# 2-generator case.
#
# Runs standalone (own main(), dispatched via a worker flag) so it can be
# invoked in a killable subprocess with a hard timeout, exactly like
# streaming_ideal_dimension.jl's own worker/timeout discipline.
# ---------------------------------------------------------------------------
const WORKER_FLAG = "--dimension-worker"

function serialize_bivariate_system(path, prime::UInt64, u0, u1)
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

# Computes the colength (standard monomial count) of <u0,u1> in Fp[x3,x4]
# via grevlex GB + staircase counting. Returns
# (:ok, elapsed, colength, info) or (:error, NaN, -1, message) or
# (:unbounded, elapsed, -1, message) if the ideal is NOT zero-dimensional
# (staircase search exceeds a generous cutoff without terminating) --
# reported distinctly from an outright error, since "not zero-dimensional"
# is itself the important finding this script is designed to surface, and
# is the GENERIC expectation here (2 generators in 4 ambient variables), not
# a surprise -- see the big header comment on what dim(I) means for <U0,U1>.
function bivariate_colength(u0, u1, prime::UInt64; staircase_cutoff::Int = 200_000)
    Fp = GF(prime)
    S2, (x3s, x4s) = polynomial_ring(Fp, [:x3, :x4])

    t0 = time()
    println("      [worker] building ideal and starting degrevlex GB...")
    flush(stdout)
    I = ideal(S2, [u0, u1])
    G = groebner_basis(I; ordering=degrevlex(S2))
    gb_elapsed = time() - t0
    println("      [worker] GB done in ", round(gb_elapsed, digits=3),
            "s, basis size=", length(G), " -- starting staircase count...")
    flush(stdout)

    lms = [leading_monomial(g; ordering=degrevlex(S2)) for g in G]
    lm_exps = [collect(AbstractAlgebra.exponent_vectors(m))[1] for m in lms]

    max_deg_bound = maximum(total_degree(g) for g in G; init=0)
    max_input_deg = maximum(total_degree(g) for g in (u0, u1))
    search_bound = max(2 * max_deg_bound, 2 * max_input_deg, 4)

    # Efficient staircase count: identical algorithm to
    # streaming_ideal_dimension.jl's bivariate_colength -- O(search_bound *
    # |G|) via a running minimum over generators sorted by their first
    # exponent, rather than an O(search_bound^2 * |G|) brute-force scan.
    sorted_by_a = sort(lm_exps; by = first)

    standard_monomials = Tuple{Int,Int}[]
    box_exceeded = false
    gi = 1
    min_b_so_far = typemax(Int)
    for e3 in 0:search_bound
        while gi <= length(sorted_by_a) && sorted_by_a[gi][1] <= e3
            min_b_so_far = min(min_b_so_far, sorted_by_a[gi][2])
            gi += 1
        end
        if min_b_so_far == typemax(Int)
            box_exceeded = true
            break
        end
        n_here = min_b_so_far
        if length(standard_monomials) + n_here > staircase_cutoff
            box_exceeded = true
            break
        end
        for e4 in 0:(min_b_so_far - 1)
            push!(standard_monomials, (e3, e4))
        end
    end

    elapsed = time() - t0

    if box_exceeded
        return (:unbounded, elapsed, -1,
                "grevlex basis size=$(length(G)) (computed in $(round(gb_elapsed,digits=3))s), " *
                "standard-monomial staircase exceeded cutoff=$staircase_cutoff within " *
                "search bound $search_bound -- ideal is likely NOT zero-dimensional at " *
                "this sample point (which, for <U0,U1> alone -- 2 generators in 4 " *
                "ambient variables -- is the GENERIC expectation, not a surprise; " *
                "raise staircase_cutoff if you want to distinguish 'positive-dimensional' " *
                "from 'zero-dimensional but colength exceeds the cutoff')")
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
    u0, u1 = polys

    result = try
        bivariate_colength(u0, u1, prime; staircase_cutoff=staircase_cutoff)
    catch e
        (:error, NaN, -1, sprint(showerror, e))
    end

    open(outfile, "w") do io
        serialize(io, result)
    end
end

function run_with_timeout(prime, u0, u1, timeout_secs::Real, script_path::String,
                          staircase_cutoff::Int)
    tmpdir = mktempdir()
    infile = joinpath(tmpdir, "in.jls")
    outfile = joinpath(tmpdir, "out.jls")

    try
        serialize_bivariate_system(infile, prime, u0, u1)

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

        try
            return open(deserialize, outfile)
        catch e
            error("run_with_timeout: worker process exited (not killed by our timeout) " *
                  "and left a result file at $outfile, but it failed to deserialize " *
                  "-- the file is corrupt or truncated. This is NOT reported as an " *
                  "ordinary (:error, ...) status because a bad result file is a " *
                  "different failure mode from a worker exception (run_worker's own " *
                  "try/catch already reports those cleanly) and silently downgrading " *
                  "it to a per-sample :error would hide a serialization/IO bug rather " *
                  "than surface it. Underlying error: $(sprint(showerror, e))")
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
        error("pair_ideal_dimension.jl: usage: julia pair_ideal_dimension.jl " *
              "<U0.native> <U1.native> <prime> " *
              "[n_samples] [seed] [timeout_secs]")

    u0_path = ARGS[1]
    u1_path = ARGS[2]
    prime = parse(UInt64, ARGS[3])
    n_samples    = length(ARGS) >= 4 ? parse(Int, ARGS[4])     : 8
    seed         = length(ARGS) >= 5 ? parse(Int, ARGS[5])     : 0
    timeout_secs = length(ARGS) >= 6 ? parse(Float64, ARGS[6]) : 1800.0

    for path in (u0_path, u1_path)
        isfile(path) || error("pair_ideal_dimension.jl: no such file: $path")
    end

    script_path = abspath(@__FILE__)

    println("=" ^ 70)
    println("Streaming dim(I) estimator for I = <U0,U1> in Fp[x1,x2,x3,x4]")
    println("=" ^ 70)
    println("U0 file:     ", u0_path)
    println("U1 file:     ", u1_path)
    println("prime:       ", prime)
    println("samples:     ", n_samples, " (seed=", seed, ")")
    println("timeout:     ", timeout_secs, "s per sample's bivariate GB (subprocess)")
    println()
    println("CONVENTION IN USE: fixing slots ", FIXED_SLOTS, " (x1,x2), keeping slots ",
            KEPT_SLOTS, " (x3,x4) -- see the CAVEAT comment above main() if this needs to change.")
    println()
    println("Memory discipline: U0 and U1 (408.6 MB each) are BOTH loaded once ")
    println("and kept resident for the whole run -- unlike streaming_ideal_dimension.jl's ")
    println("V0/V1, no re-streaming from disk is needed here (see the header comment ")
    println("for why this ideal doesn't need the one-file-at-a-time discipline).")
    println()
    println("REMINDER: <U0,U1> is 2 generators in 4 ambient variables -- generically a ")
    println("2-dimensional variety (a surface), NOT zero-dimensional. Consistent ")
    println("per-sample colengths below are evidence the (x1,x2)-slice behaves ")
    println("uniformly; they are NOT by themselves proof that V(<U0,U1>) is ")
    println("zero-dimensional or that this number is dim_{Fp} Fp[x1,x2,x3,x4]/<U0,U1>. ")
    println("See the header comment for the full caveat.")
    println()

    Fp = GF(prime)
    S2, _ = polynomial_ring(Fp, [:x3, :x4])

    println("Loading U0/U1 ONCE (both kept resident for the whole run).")
    flush(stdout)
    u0_raw = raw_load_native(u0_path, prime)
    u1_raw = raw_load_native(u1_path, prime)
    println()

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

        println("  specializing U0,U1 from resident memory (no disk I/O)...")
        t0 = time()
        u0 = specialize_from_raw(u0_raw, prime, a, b, S2)
        u1 = specialize_from_raw(u1_raw, prime, a, b, S2)
        println("  both specialized in ", round(time() - t0, digits=2), "s ",
                "(U0=", length(u0), ", U1=", length(u1), " terms)")
        flush(stdout)

        println("  computing bivariate colength of <U0,U1> in Fp[x3,x4] ",
                "(subprocess, timeout=", timeout_secs, "s)...")
        flush(stdout)
        status, elapsed, colength, info = run_with_timeout(
            prime, u0, u1, timeout_secs, script_path, 200_000
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
        println("terminate within its cutoff. For <U0,U1> alone (2 generators, 4 ambient ")
        println("variables) this is the GENERIC expectation, not a surprise -- V(<U0,U1>) ")
        println("is very likely positive-dimensional, so a slice at fixed (x1,x2) need not ")
        println("be finite either. Re-run with a larger staircase_cutoff (edit the 200_000 ")
        println("literal above, or expose it as a CLI argument) if you want to tell ")
        println("'genuinely infinite at this slice' apart from 'finite but exceeds cutoff'.")
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
        println("(x1,x2)-slice through V(<U0,U1>), repeated identically across independent ")
        println("random samples. That stabilization is evidence the slice behaves ")
        println("uniformly -- it is NOT a proof that V(<U0,U1>) is zero-dimensional, and it ")
        println("is NOT by itself dim_{Fp} Fp[x1,x2,x3,x4]/<U0,U1> unless V(<U0,U1>) really ")
        println("is zero-dimensional (an assumption this script does not verify ")
        println("independently -- see the header comment). A single unlucky/non-generic ")
        println("sample point could in principle agree by coincidence; more independent ")
        println("samples (raise n_samples) strengthen this evidence further.")
    else
        println("dim(I) estimate: INCONSISTENT across samples: ", colengths)
        println()
        println("This is the important finding, not a bug to work around: either some ")
        println("sample points were non-generic (unlucky (x1,x2) choice landing on a ")
        println("special fiber -- try more samples / a different seed to see if a ")
        println("majority value emerges), or V(<U0,U1>) genuinely is not equidimensional/ ")
        println("not zero-dimensional as a (x1,x2)-family (again, the GENERIC expectation ")
        println("for 2 generators in 4 variables). Do not average or otherwise combine ")
        println("these numbers into a single answer without resolving which case this is.")
    end
end

# ---------------------------------------------------------------------------
# Entry point dispatch (worker subprocess vs normal invocation), same
# pattern as streaming_ideal_dimension.jl's own dispatch at the bottom of
# that file.
# ---------------------------------------------------------------------------

if length(ARGS) >= 1 && ARGS[1] == WORKER_FLAG
    length(ARGS) >= 4 ||
        error("pair_ideal_dimension.jl: worker mode expects " *
              "$WORKER_FLAG <infile> <outfile> <staircase_cutoff>")
    run_worker(ARGS[2], ARGS[3], parse(Int, ARGS[4]))
else
    main()
end
