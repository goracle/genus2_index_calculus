#!/usr/bin/env julia
#
# pilot_diagnostic.jl
#
# This was pilot_elimination_bench.jl. It is now a DIAGNOSTIC tool, not a
# benchmark: both lex Groebner and grevlex+FGLM were hanging on real
# specialized samples, and before spending time optimizing Groebner
# computations, the goal is to characterize the specialized bivariate
# systems themselves -- degree, sparsity, squarefreeness, common factors,
# Newton polygon shape, and ideal-theoretic invariants that are cheap to
# get -- to find out whether these systems are genuinely close to the
# worst-case Bezout bound, or whether there is hidden algebraic structure
# (a common factor, a non-generic Newton polygon, degeneracy in one
# variable, etc.) that a generic Groebner algorithm is failing to exploit.
#
# U and V are treated completely symmetrically: both pairs are streamed
# and specialized term-by-term straight off disk (see
# stream_specialize_native_to_poly) at each sample point, and both then go
# through the exact same sections 1-8 diagnostics. There is no
# numerical_resultant strategy any more -- that was a premature U+V
# cross-pair Sylvester check written before V's own per-pair diagnostics
# (grevlex_analysis, resultant_x2, common-factor test, etc.) had ever
# actually been looked at.
#
# The only EXPENSIVE, potentially-hanging computations left are in section
# 8 (timed elimination with a hard timeout), and those now run each
# strategy in a separate killable subprocess -- see the big comment above
# run_with_timeout() for why that's necessary and why a Task/Timer-based
# timeout would NOT actually work here.
#
# Usage:
#   julia pilot_diagnostic.jl <U0.native> <U1.native> <V0.native> <V1.native> <prime> [n_samples] [seed] [timeout_secs]
#
#   U0.native, U1.native,
#   V0.native, V1.native : NEWTPOL2 v2 native files (with coefficients),
#                           as produced by convert_to_native.jl <input> <output> <ambient_dim> <prime>.
#                           None of these four files is ever bulk-loaded
#                           into memory as a whole (neither as raw flat
#                           arrays nor as an Oscar MPolyRingElem): each is
#                           streamed and specialized term-by-term straight
#                           off disk, once per (alpha,beta) sample, via
#                           stream_specialize_native_to_poly -- read a
#                           chunk of terms, fold alpha^e1*beta^e4*coeff
#                           into a small accumulator keyed by (e2,e3), move
#                           to the next chunk. Only the much smaller
#                           resulting specialized bivariate polynomial
#                           (thousands of terms, not 17.8M) is ever fully
#                           materialized.
#   prime                 : the F_p modulus -- must match what the native
#                           files were converted with (checked against the
#                           file's own stored prime; mismatch is an error)
#   n_samples             : number of random (x1,x4) specialization points
#                           to run diagnostics on (default 10)
#   seed                  : RNG seed for reproducible sample points (default 0)
#   timeout_secs          : per-strategy hard timeout in section 8, in
#                           seconds (default 30), applied to both
#                           grevlex_analysis and resultant_x2, for both the
#                           U pair and the V pair
#
# Variable convention (matches interpolate_elimination.jl and the decision
# to eliminate (x2,x3), leaving F(x1,x4)): ambient_dim=4, exponent order in
# the native file is (x1,x2,x3,x4), i.e. index 1..4 = x1,x2,x3,x4. We fix
# x1=alpha, x4=beta and eliminate x2 (keeping x3), matching the request's
# R_{alpha,beta}(x3) = Res_{x2}(U0(alpha,x2,x3,beta), U1(alpha,x2,x3,beta))
# -- and, symmetrically, Res_{x2}(V0(alpha,x2,x3,beta), V1(alpha,x2,x3,beta)).

using Oscar

using Random
include(joinpath(@__DIR__, "newton_polytope.jl"))  # for load_native_support_with_coeffs

# ---------------------------------------------------------------------------
# Raw modular arithmetic helpers (no ring objects, no Oscar/Nemo types) --
# used by stream_specialize_native_to_poly's hot per-term loop (for both
# U0/U1 and V0/V1 alike), where the whole point is to avoid the overhead of
# symbolic polynomial ring elements while folding 17.8M terms into a
# specialized polynomial.
# ---------------------------------------------------------------------------

# a*b mod p for a,b,p < 2^64: promote to UInt128 for the multiply so this
# can never overflow (p in this project is on the order of 2.4e6, so a*b
# alone would already fit in UInt64, but this stays correct even if p grows
# up to just under 2^64).
@inline function modmul(a::UInt64, b::UInt64, p::UInt64)
    return UInt64((UInt128(a) * UInt128(b)) % UInt128(p))
end

@inline function modadd(a::UInt64, b::UInt64, p::UInt64)
    s = a + b
    return s >= p ? s - p : s
end

@inline function modsub(a::UInt64, b::UInt64, p::UInt64)
    return a >= b ? a - b : a + p - b
end

# Fast modular exponentiation (square-and-multiply), used to compute
# alpha^e1 and beta^e4 in stream_specialize_native_to_poly's per-term loop.
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

# Modular inverse via Fermat's little theorem (p is prime for every use in
# this project): a^(p-2) mod p.
@inline function modinv(a::UInt64, p::UInt64)
    iszero(a) && error("modinv: cannot invert 0 mod $p")
    return modpow(a, p - 2, p)
end

# ---------------------------------------------------------------------------
# True streaming specialization of a NEWTPOL2 native file at x1=alpha,
# x4=beta, straight off disk into an actual Oscar bivariate polynomial over
# Fp[x2,x3]. This is the ONLY specialization path in this file -- used
# identically for U0/U1 and V0/V1, so both pairs are fed through the exact
# same sections 1-8 diagnostics. This NEVER holds the file's full
# support/coeffs arrays in memory (unlike load_native_support_with_coeffs,
# which bulk-reads everything with a single `read!` into full-length
# arrays): it reads the NEWTPOL2 header
# directly, then streams the exponent block and coefficient block in
# fixed-size chunks, computing alpha^e1 * beta^e4 * coeff mod p and
# accumulating into a Dict{(e2,e3), UInt64} as each chunk is read -- only
# the final MPolyBuildCtx construction touches Oscar ring objects, and only
# for the (much smaller) collapsed term count, not the full 17.8M-term
# stream.
#
# Matches the NEWTPOL2 binary layout exactly, per newton_polytope.jl's
# documented format:
#   magic       :: UInt64            (must be NATIVE_SUPPORT_MAGIC_V2)
#   ambient_dim :: Int64              (must be 4: x1,x2,x3,x4)
#   n_terms     :: Int64
#   prime       :: UInt64             (checked against expected_prime)
#   exps        :: Int32, ambient_dim * n_terms values, row-major
#   coeffs      :: UInt64, n_terms values
function stream_specialize_native_to_poly(path::String, expected_prime::UInt64,
                                          alpha, beta, S2;
                                          chunk_terms::Int = 1_000_000)
    isfile(path) ||
        error("stream_specialize_native_to_poly: no such file: $path")

    fsize_mb = filesize(path) / 1024 / 1024
    println("    stream_specialize_native_to_poly: streaming ", path,
            " (", round(fsize_mb, digits=1), " MB on disk)...")
    flush(stdout)
    t0 = time()

    p = expected_prime
    alpha_r = coeff_to_u64(alpha) % p
    beta_r  = coeff_to_u64(beta)  % p

    acc = Dict{Tuple{Int,Int}, UInt64}()

    exp_io   = open(path, "r")
    coeff_io = open(path, "r")

    try
        magic = read(exp_io, UInt64)
        magic == NATIVE_SUPPORT_MAGIC_V2 ||
            error("stream_specialize_native_to_poly: $path does not have the expected NEWTPOL2 header")

        ambient_dim = read(exp_io, Int64)
        ambient_dim == 4 ||
            error("stream_specialize_native_to_poly: expected ambient_dim=4, got $ambient_dim")

        n_terms = read(exp_io, Int64)
        n_terms > 0 ||
            error("stream_specialize_native_to_poly: invalid n_terms=$n_terms")

        file_prime = read(exp_io, UInt64)
        file_prime == expected_prime ||
            error("stream_specialize_native_to_poly: file prime=$file_prime, expected $expected_prime")

        # Mirror the header reads on the second handle.
        read(coeff_io, UInt64)
        read(coeff_io, Int64)
        read(coeff_io, Int64)
        read(coeff_io, UInt64)

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

                e1 = Int(exp_buf[base + 1])
                e2 = Int(exp_buf[base + 2])
                e3 = Int(exp_buf[base + 3])
                e4 = Int(exp_buf[base + 4])

                c = UInt64(coeff_buf[i]) % p

                # Specialize x1 = alpha and x2 = beta.
                a_pow = cached_pow(alpha_pow_cache, alpha_r, e1)
                b_pow = cached_pow(beta_pow_cache,  beta_r,  e2)

                scale = modmul(a_pow, b_pow, p)
                term  = modmul(c, scale, p)

                # Keep x3, x4.
                key = (e3, e4)
                acc[key] = haskey(acc, key) ? modadd(acc[key], term, p) : term
            end

            terms_done += this_chunk

            if terms_done % 5_000_000 == 0 || terms_done == n_terms
                println("      ", terms_done, "/", n_terms,
                        " terms streamed+specialized (",
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

    for ((e3, e4), c_u) in acc
        iszero(c_u) && continue
        push_term!(ctx, Fp(c_u), [e3, e4])
    end

    poly = finish(ctx)

    println("    stream_specialize_native_to_poly: done in ",
            round(time() - t0, digits=1), "s (",
            length(poly), " terms after collapsing)")
    flush(stdout)

    return poly
end

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
#
# NOTE: the only specialization path left in this file is
# stream_specialize_native_to_poly (above), which loads and specializes
# term-by-term straight off disk -- read a chunk, fold it into the
# accumulator, move to the next chunk -- so the full (support, coeffs)
# arrays for a file never exist in memory at once, for EITHER U or V. An
# earlier version of this file had a separate load_raw_polynomial +
# specialize() two-step (bulk-read the whole file into flat arrays, then
# process those arrays) used only for U; that bulk-load step is exactly
# what's being avoided now that V is treated identically to U, so both
# functions were removed rather than kept as a second, unused code path.
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

# --- [U] 6. Newton polygons ---
function diag_newton_polygon(g, varname::String)
    val, err = try_diag() do
        # 1. Extract the raw support matrix
        supp = support(g)
        
        # 2. Use the prefiltered NewtonPolytope wrapper to prevent OOM/hanging
        NP = newton_polytope(supp, 2; prefilter=true)
        
        # 3. Pull metrics using the custom wrappers
        verts = vertices_of(NP)
        nv = normalized_volume_of(NP)
        
        # 4. Count via Ehrhart polynomial evaluation rather than brute enumeration
        lp_count = lattice_points_of(NP; method=:ehrhart)
        
        (NP, verts, nv, lp_count)
    end
    if err !== nothing
        println("    $varname Newton polygon: ", err)
        return
    end
    (NP, verts, nv, lp_count) = val
    n_verts = length(verts)
    
    println("    $varname Newton polygon:")
    println("      vertices (", n_verts, "): ", verts)
    println("      normalized area: ", nv)
    println("      lattice points: ", lp_count)
    
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

function serialize_system_for_worker(path, polys::Vector, prime::UInt64)
    data = Any[prime]

    for g in polys
        supp = collect(AbstractAlgebra.exponent_vectors(g))
        coef = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g)]
        push!(data, supp)
        push!(data, coef)
    end

    open(path, "w") do io
        serialize(io, Tuple(data))
    end
end

# Worker-side entry point: reconstructs g0,g1 from the temp file, runs the
# ONE requested strategy, writes (status, elapsed, deg, info) to the result
# file. status is one of :ok, :error. This branch only runs when this
# script is invoked as `julia pilot_diagnostic.jl --diagnostic-worker
# <infile> <outfile> <strategy>` (see dispatch at the bottom of the file).
# Works on whichever (g0,g1) pair it's handed -- the driver calls this once
# per (U-pair, V-pair) x sample, so this function has no notion of "U" or
# "V" at all, just "a bivariate pair".



# Driver-side: spawns the worker subprocess for one strategy, enforces the
# hard wall-clock timeout, and returns (elapsed, deg, info) where elapsed
# is NaN and info == "TIMEOUT" if the deadline was hit.
function run_with_timeout(polys::AbstractVector,
                          prime::UInt64,
                          strategy::String,
                          timeout_secs::Real,
                          script_path::String)

    tmpdir = mktempdir()
    infile = joinpath(tmpdir, "in.jls")
    outfile = joinpath(tmpdir, "out.jls")

    try
        serialize_system_for_worker(infile, polys, prime)

        cmd = `julia --startup-file=no $script_path $WORKER_FLAG $infile $outfile $strategy`
        proc = run(pipeline(cmd; stdout=devnull, stderr=devnull); wait=false)

        deadline = time() + timeout_secs
        while process_running(proc) && time() < deadline
            sleep(0.2)
        end

        if process_running(proc)
            try
                kill(proc, Base.SIGKILL)
            catch
            end
            try
                wait(proc)
            catch
            end
            return (NaN, -1, "TIMEOUT (exceeded $(timeout_secs)s, subprocess killed)")
        end

        if !isfile(outfile)
            return (NaN, -1,
                    "worker exited without producing a result (crashed or killed externally)")
        end

        status, elapsed, deg, info = open(deserialize, outfile)
        if status == :error
            return (NaN, -1, "ERROR: $info")
        end

        return (elapsed, deg, info)

    finally
        rm(tmpdir; recursive=true, force=true)
    end
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
# Entry point dispatch: this file is either run normally (main()) or, when
# invoked with the WORKER_FLAG by run_with_timeout() above, as a one-shot
# subprocess worker that runs a single elimination strategy and exits.
# ---------------------------------------------------------------------------



# ---------------------------------------------------------------------------

# Small helper: run `f()`, returning (value, nothing) on success or

# (nothing, "unavailable: <msg>") on any exception. Used throughout this

# section so one missing/renamed Oscar function doesn't abort the others.

# ---------------------------------------------------------------------------

function try_diag(f)
    try
        return (f(), nothing)
    catch e
        return (nothing, "unavailable: $(sprint(showerror, e))")
    end
end

# --- 1. Degree information -------------------------------------------------

function diag_degrees(g, varname::String, vars)
    println("    degree($varname, x3) = ", degree(g, vars[1]))
    println("    degree($varname, x4) = ", degree(g, vars[2]))
    println("    total_degree($varname) = ", total_degree(g))
end

# --- 2. Sparsity ------------------------------------------------------------

function diag_sparsity(g, varname::String)
    n_monomials = length(g)
    exps = collect(AbstractAlgebra.exponent_vectors(g))
    if isempty(exps)
        println("    $varname is the zero polynomial -- no sparsity data")
        return
    end


    e3s = [e[1] for e in exps]
    e4s = [e[2] for e in exps]
    lo3, hi3 = extrema(e3s)
    lo4, hi4 = extrema(e4s)
    box_size = (hi3 - lo3 + 1) * (hi4 - lo4 + 1)
    present = Set{Tuple{Int,Int}}((e[1], e[2]) for e in exps)
    n_missing = box_size - length(present)
    is_full_rectangle = n_missing == 0

    println("    $varname: ", n_monomials, " monomials")
    println("      exponent bounding box: x3 in [$lo3,$hi3], x4 in [$lo4,$hi4] ",
            "(box holds $box_size lattice points)")
    println("      full rectangle (every pair in box occurs)? ", is_full_rectangle)
    if !is_full_rectangle
        missing_pairs = Tuple{Int,Int}[]
        for e3 in lo3:hi3, e4 in lo4:hi4
            (e3, e4) in present || push!(missing_pairs, (e3, e4))
            length(missing_pairs) >= 12 && break
        end
        println("      missing from box: ", n_missing, " pairs",
                n_missing > 0 ? " (first few: $missing_pairs" *
                    (n_missing > 12 ? ", ..." : "") * ")" : "")
    end


end

# --- 3. Squarefreeness ------------------------------------------------------

function diag_squarefree(g, varname::String, vars)
    val, err = try_diag() do
        dg3 = derivative(g, vars[1])
        dg4 = derivative(g, vars[2])
        h = gcd(g, dg3)
        h = gcd(h, dg4)
        is_unit(h)
    end
    if err !== nothing
        println("    $varname squarefree? ", err)
    else
        println("    $varname squarefree? ", val)
    end
end

# --- 4. Common factor test --------------------------------------------------

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

function diag_resultant_metadata(g0, g1, vars)
    x3s, x4s = vars
    d0x3, d1x3 = degree(g0, x3s), degree(g1, x3s)
    d0x4, d1x4 = degree(g0, x4s), degree(g1, x4s)
    syl_dim = d0x3 + d1x3
    deg_bound = d0x3 * d1x4 + d1x3 * d0x4


    println("    degree(g0,x3)=", d0x3, ", degree(g1,x3)=", d1x3)
    println("    Sylvester matrix dimension (eliminating x3): ", syl_dim, " x ", syl_dim,
            " (", syl_dim^2, " entries if fully dense)")
    println("    classical bound on deg_x4(resultant): d0x3*d1x4 + d1x3*d0x4 = ",
            d0x3, "*", d1x4, " + ", d1x3, "*", d0x4, " = ", deg_bound)
    println("    Oscar has no public API (as far as this script can tell) to inspect ",
            "the Sylvester matrix or a resultant degree estimate without either ",
            "constructing the matrix or computing the resultant outright -- the ",
            "bound above is a hand-computed classical estimate, not something Oscar reports.")


end

# --- 6. Newton polygons -----------------------------------------------------

function diag_newton_polygon(g, varname::String)
    val, err = try_diag() do
        supp = support(g)
        NP = newton_polytope(supp, 2; prefilter=true)
        verts = vertices_of(NP)
        nv = normalized_volume_of(NP)
        lp_count = lattice_points_of(NP; method=:ehrhart)
        (NP, verts, nv, lp_count)
    end


    if err !== nothing
        println("    $varname Newton polygon: ", err)
        return
    end

    (NP, verts, nv, lp_count) = val
    n_verts = length(verts)

    println("    $varname Newton polygon:")
    println("      vertices (", n_verts, "): ", verts)
    println("      normalized area: ", nv)
    println("      lattice points: ", lp_count)

    is_rect = n_verts == 4
    println("      complete rectangle? ", is_rect,
            is_rect ? "" : " (has $n_verts vertices, not 4)")


end

# --- 7. Projection / ideal diagnostics -------------------------------------

function diag_projection(g0, g1)
    println("    dimension / degree of <g0,g1> / Hilbert polynomial: SKIPPED -- ",
            "Oscar computes all of these via a Groebner basis internally, so ",
            "computing them here would just be the same hang moved earlier. ",
            "See section 8 for the actual timed Groebner attempts.")
end

# ---------------------------------------------------------------------------

# Section 8: timed elimination with a HARD timeout.

# ---------------------------------------------------------------------------

using Serialization

const WORKER_FLAG = "--diagnostic-worker"

function coeff_to_u64(c)
    try
        return UInt64(Int(c))
    catch
        return UInt64(lift(ZZ, c))
    end
end

function serialize_system_for_worker(path, polys::AbstractVector, prime::UInt64)
    data = Any[prime]


    for g in polys
        supp = collect(AbstractAlgebra.exponent_vectors(g))
        coef = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g)]
        push!(data, supp)
        push!(data, coef)
    end

    open(path, "w") do io
        serialize(io, Tuple(data))
    end


end

function run_worker(infile::String, outfile::String, strategy::String)
    data = open(deserialize, infile)


    prime = data[1]
    Fp = GF(prime)
    S2, (x3s, x4s) = polynomial_ring(Fp, [:x3, :x4])

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

    result = try
        if strategy == "lex"
            t0 = time()
            I = ideal(S2, polys)
            G = groebner_basis(I; ordering=lex(S2))
            elapsed = time() - t0

            univ = [g for g in G if degree(g, x3s) == 0]
            deg = isempty(univ) ? -1 : maximum(total_degree(g) for g in univ)

            (:ok,
             elapsed,
             deg,
             "lex basis size=$(length(G)), generators=$(length(polys)), univariate-in-x4 generators=$(length(univ))")

        elseif strategy == "grevlex_analysis"
            fglm_cutoff = 20000

            t0 = time()
            I = ideal(S2, polys)
            G = groebner_basis(I; ordering=degrevlex(S2))
            gb_elapsed = time() - t0

            lms = [leading_monomial(g; ordering=degrevlex(S2)) for g in G]
            lm_exps = [collect(AbstractAlgebra.exponent_vectors(m))[1] for m in lms]

            gen_reports = String[]
            for (idx, g) in enumerate(G)
                (ge3, ge4) = lm_exps[idx]
                push!(gen_reports,
                      "#$idx: deg=$(total_degree(g)), LM=(x3^$ge3*x4^$ge4), terms=$(length(g))")
            end

            max_deg_bound = maximum(total_degree(g) for g in G; init=0)
            max_input_deg = maximum(total_degree(g) for g in polys)
            search_bound = max(2 * max_deg_bound, 2 * max_input_deg)

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
            push!(info_parts,
                  "grevlex basis size=$(length(G)) (computed in $(round(gb_elapsed,digits=3))s)")
            push!(info_parts,
                  "input generators=$(length(polys))")
            push!(info_parts,
                  "leading monomial exponents=$(lm_exps)")
            push!(info_parts,
                  "per-generator report: " * join(gen_reports, "; "))

            if box_exceeded
                push!(info_parts, "quotient dimension exceeded cutoff")
            else
                push!(info_parts, "quotient dimension=$quotient_dim")
            end

            if hilbert_err === nothing
                push!(info_parts, "hilbert_series=$hilbert_val")
            else
                push!(info_parts, "hilbert_series: $hilbert_err")
            end

            if !box_exceeded &&
                quotient_dim > 0 &&
                quotient_dim <= fglm_cutoff

                fglm_t0 = time()

                fglm_result, fglm_err = try_diag() do
                    fglm(I;
                         start_ordering=degrevlex(S2),
                         destination_ordering=lex(S2))
                end

                fglm_elapsed = time() - fglm_t0

                if fglm_err === nothing
                    univ = [g for g in fglm_result if degree(g, x3s) == 0]
                    fglm_deg = isempty(univ) ? -1 :
                        maximum(total_degree(g) for g in univ)

                    push!(info_parts,
                          "FGLM succeeded in $(round(fglm_elapsed,digits=3))s, " *
                              "lex basis size=$(length(fglm_result)), " *
                              "fiber_degree=$fglm_deg")
                else
                    push!(info_parts, "FGLM failed: $fglm_err")
                end
            else
                push!(info_parts, "FGLM skipped")
            end

            deg_report = box_exceeded ? -1 : quotient_dim

            (:ok,
             elapsed,
             deg_report,
             join(info_parts, " | "))

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

function run_with_timeout(polys::AbstractVector,
                          prime::UInt64,
                          strategy::String,
                          timeout_secs::Real,
                          script_path::String)

    tmpdir = mktempdir()
    infile = joinpath(tmpdir, "in.jls")
    outfile = joinpath(tmpdir, "out.jls")

    try
        serialize_system_for_worker(infile, polys, prime)

        cmd = `julia --startup-file=no $script_path $WORKER_FLAG $infile $outfile $strategy`
        proc = run(pipeline(cmd; stdout=devnull, stderr=devnull); wait=false)

        deadline = time() + timeout_secs
        while process_running(proc) && time() < deadline
            sleep(0.2)
        end

        if process_running(proc)
            try
                kill(proc, Base.SIGKILL)
            catch
            end
            try
                wait(proc)
            catch
            end
            return (NaN, -1, "TIMEOUT (exceeded $(timeout_secs)s, subprocess killed)")
        end

        if !isfile(outfile)
            return (NaN, -1,
                    "worker exited without producing a result (crashed or killed externally)")
        end

        status, elapsed, deg, info = open(deserialize, outfile)
        if status == :error
            return (NaN, -1, "ERROR: $info")
        end

        return (elapsed, deg, info)
    finally
        rm(tmpdir; recursive=true, force=true)
    end

end

# ---------------------------------------------------------------------------

# Main

# ---------------------------------------------------------------------------

function main()
    length(ARGS) >= 5 ||
        error("pilot_diagnostic.jl: usage: julia pilot_diagnostic.jl " *
        "<U0.native> <U1.native> <V0.native> <V1.native> <prime> " *
        "[n_samples] [seed] [timeout_secs]")

    u0_path = ARGS[1]
    u1_path = ARGS[2]
    v0_path = ARGS[3]
    v1_path = ARGS[4]
    prime = parse(UInt64, ARGS[5])
    n_samples = length(ARGS) >= 6 ? parse(Int, ARGS[6]) : 10
    seed = length(ARGS) >= 7 ? parse(Int, ARGS[7]) : 0
    timeout_secs = length(ARGS) >= 8 ? parse(Float64, ARGS[8]) : 30.0

    isfile(u0_path) || error("pilot_diagnostic.jl: no such file: $u0_path")
    isfile(u1_path) || error("pilot_diagnostic.jl: no such file: $u1_path")
    isfile(v0_path) || error("pilot_diagnostic.jl: no such file: $v0_path")
    isfile(v1_path) || error("pilot_diagnostic.jl: no such file: $v1_path")

    script_path = abspath(@__FILE__)

    println("=" ^ 70)
    println("Pilot diagnostic (specialized system characterization)")
    println("=" ^ 70)
    println("U0 file:      ", u0_path)
    println("U1 file:      ", u1_path)
    println("V0 file:      ", v0_path)
    println("V1 file:      ", v1_path)
    println("prime:        ", prime)
    println("samples:      ", n_samples, " (seed=", seed, ")")
    println("timeout:      ", timeout_secs, "s per strategy in section 8")
    println()

    Fp = GF(prime)
    S2, (y3, y4) = polynomial_ring(Fp, [:x3, :x4])
    vars = (y3, y4)

    rng = Random.MersenneTwister(seed)
    samples = Tuple{elem_type(Fp), elem_type(Fp)}[]
    while length(samples) < n_samples
        a = Fp(rand(rng, 1:(prime - 1)))
        b = Fp(rand(rng, 1:(prime - 1)))
        push!(samples, (a, b))
    end

    timed_strategies = [
        ("grevlex_analysis", "grevlex_analysis"),
        ("lex",              "lex"),
    ]

    timed_results = Dict(name => Vector{Tuple{Float64,Int,String}}()
                         for (name, _) in timed_strategies)

    for (i, (a, b)) in enumerate(samples)
        println("=" ^ 70)
        println("Sample ", i, "/", n_samples, ": x1=", a, ", x2=", b)
        println("=" ^ 70)
        flush(stdout)

        println("  streaming+specializing U0, U1, V0, V1 at this point...")
        t0 = time()
        u0 = stream_specialize_native_to_poly(u0_path, prime, a, b, S2)
        u1 = stream_specialize_native_to_poly(u1_path, prime, a, b, S2)
        v0 = stream_specialize_native_to_poly(v0_path, prime, a, b, S2)
        v1 = stream_specialize_native_to_poly(v1_path, prime, a, b, S2)
        println("  specialized in ", round(time() - t0, digits=2), "s ",
                "(U0 has ", length(u0), " terms, U1 has ", length(u1),
                ", V0 has ", length(v0), ", V1 has ", length(v1), ")")
        flush(stdout)

        bundle = [u0, u1, v0, v1]

        pair_data = Dict(
            "U" => (u0, u1),
            "V" => (v0, v1),
        )

        for label in ("U", "V")
            g0, g1 = pair_data[label]

            println()
            println("  --- [", label, "] 1. Degree information ---")
            diag_degrees(g0, "$(label)0", vars)
            diag_degrees(g1, "$(label)1", vars)
            flush(stdout)

            println()
            println("  --- [", label, "] 2. Sparsity ---")
            diag_sparsity(g0, "$(label)0")
            diag_sparsity(g1, "$(label)1")
            flush(stdout)

            println()
            println("  --- [", label, "] 3. Squarefreeness ---")
            diag_squarefree(g0, "$(label)0", vars)
            diag_squarefree(g1, "$(label)1", vars)
            flush(stdout)

            println()
            println("  --- [", label, "] 4. Common factor test (gcd) ---")
            diag_common_factor(g0, g1)
            flush(stdout)

            println()
            println("  --- [", label, "] 5. Resultant metadata only (no resultant computed here) ---")
            diag_resultant_metadata(g0, g1, vars)
            flush(stdout)

            println()
            println("  --- [", label, "] 6. Newton polygons ---")
            diag_newton_polygon(g0, "$(label)0")
            diag_newton_polygon(g1, "$(label)1")
            flush(stdout)

            println()
            println("  --- [", label, "] 7. Projection / ideal diagnostics ---")
            diag_projection(g0, g1)
            flush(stdout)
        end

        println()
        println("  --- [FULL SYSTEM] 8. Timed elimination on <U0,U1,V0,V1> ---")
        for (name, strategy) in timed_strategies
            print("    [", name, "] running in subprocess... ")
            flush(stdout)

            elapsed, deg, info = run_with_timeout(
                bundle, prime, strategy, timeout_secs, script_path
            )

            if startswith(info, "TIMEOUT")
                println("TIMEOUT")
            elseif startswith(info, "ERROR")
                println("FAILED")
            else
                println("done in ", round(elapsed, digits=3), "s, degree=", deg)
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

# Entry point dispatch

# ---------------------------------------------------------------------------

if length(ARGS) >= 1 && ARGS[1] == WORKER_FLAG
    run_worker(ARGS[2], ARGS[3], ARGS[4])
else
    main()
end






















