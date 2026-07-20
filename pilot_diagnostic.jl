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
# Section 8 (NEW): resultant-then-gcd effective fiber degree estimator.
#
# This replaces the timed Groebner/FGLM section as the PRIMARY effective-
# degree estimator. It deliberately does NOT use groebner_basis, fglm,
# hilbert_series, or a lex ordering conversion anywhere -- those are exactly
# the calls that were timing out. Instead, for a bivariate pair (g0,g1) in
# Fp[x3,x4], it:
#
#   1. Eliminates x3 via a single resultant call, giving R(x4) =
#      Res_{x3}(g0,g1) -- a UNIVARIATE polynomial in x4 (see resultant_x3).
#   2. Factors R(x4) over Fp and keeps only the linear factors, each of
#      which gives one candidate value b with R(b) = 0 (see
#      candidate_roots_from_resultant).
#   3. For each candidate b, specializes g0(x3,b) and g1(x3,b) down to
#      univariate polynomials in x3 and takes their gcd h_b(x3) (see
#      specialize_and_gcd) -- any common root of g0(x3,b) and g1(x3,b) must
#      be a root of h_b, so h_b's degree (and, if it splits completely over
#      Fp, its root count) is the candidate-point count at that b.
#
# This is a genuine algorithmic trade relative to Groebner elimination, not
# just a faster path to the same number: a resultant only detects points
# where the two curves actually meet (finitely many x3-roots existing at
# that x4), and factoring only recovers Fp-RATIONAL roots of R, not roots
# in an extension field. So the candidate/point counts reported here are a
# computable, exact proxy for the Fp-RATIONAL part of the fiber -- not a
# certified count of the full fiber over the algebraic closure the way a
# Groebner+FGLM computation would give. That tradeoff (exact but partial,
# vs. complete but hanging) is the whole point: it is what stays cheap.
# ---------------------------------------------------------------------------

# Rebuilds a bivariate Fp[x3,x4] element as a univariate polynomial in ONE
# of the two variables, over a base ring that is Fp[the other variable] --
# e.g. rebuild_univariate_over_polyring(g, x3s, x4s, T, y) turns g(x3,x4)
# into an element of T = (Fp[x4])[x3], i.e. a polynomial in x3 whose
# coefficients are elements of Fp[x4].
#
# This exists because the classical resultant-of-two-univariate-polynomials
# is only defined once g0/g1 are viewed as univariate in x3 over the base
# ring Fp[x4] -- Oscar's `resultant` on two elements of the same bivariate
# MPolyRing does not itself do that reinterpretation. Doing the
# reinterpretation with a naive term-by-term Oscar `evaluate` call in a
# loop would be exactly the kind of slow generic evaluation this task asked
# to avoid, so instead this walks the (already materialized, small)
# exponent/coefficient arrays once and accumulates directly into plain
# Dicts before building the ring elements.
#
# elim_var and keep_var are the actual ring generators (elements of
# parent(g)) -- used only to identify which exponent slot is which; T is
# the target univariate-over-Fp[keep_var] ring and y is T's generator.
function rebuild_univariate_over_polyring(g, elim_var, keep_var, T, y)
    Fp = base_ring(parent(g))
    Tbase = base_ring(T)                 # Fp[keep_var]
    keep_gen = gen(Tbase)

    # elim_idx / keep_idx: which exponent-vector slot (1 or 2) belongs to
    # elim_var and which to keep_var, determined once from the ring's own
    # generator list rather than assumed, since callers use this helper
    # with the elim/keep roles swapped (x3 eliminated vs x4 kept, or the
    # reverse in specialize_and_gcd's sibling logic).
    gens_list = gens(parent(g))
    elim_idx = findfirst(==(elim_var), gens_list)
    keep_idx = findfirst(==(keep_var), gens_list)
    (elim_idx === nothing || keep_idx === nothing) &&
        error("rebuild_univariate_over_polyring: could not locate elim_var/keep_var " *
              "among parent(g)'s generators -- ring generator mismatch")

    # Accumulate coefficients of x_elim^d (d = 0..deg_elim) as elements of
    # Fp[keep_var]: a Dict{Int,Dict{Int,elem_type(Fp)}} mapping elim-exponent
    # to a partially-built Fp[keep_var] polynomial, represented as its own
    # Dict of keep-exponent => Fp coefficient, then converted once at the end.
    by_elim_deg = Dict{Int, Dict{Int, elem_type(Fp)}}()

    for (e, c) in zip(AbstractAlgebra.exponent_vectors(g), AbstractAlgebra.coefficients(g))
        d_elim = e[elim_idx]
        d_keep = e[keep_idx]
        inner = get!(by_elim_deg, d_elim) do
            Dict{Int, elem_type(Fp)}()
        end
        inner[d_keep] = haskey(inner, d_keep) ? inner[d_keep] + c : c
    end

    result = zero(T)
    for (d_elim, inner) in by_elim_deg
        # Build the Fp[keep_var] coefficient polynomial directly via + and
        # keep_gen^d_keep -- exact, no generic evaluate() call.
        coeff_poly = zero(Tbase)
        for (d_keep, c) in inner
            is_zero(c) && continue
            coeff_poly += c * keep_gen^d_keep
        end
        is_zero(coeff_poly) && continue
        result += coeff_poly * y^d_elim
    end

    return result
end

# Computes R(x4) = resultant_{x3}(g0, g1) as an element of Fp[x4] (a plain
# univariate polynomial, NOT wrapped in the Fp[x4][x3] ring), by first
# rebuilding g0,g1 as elements of T = (Fp[x4])[x3] via
# rebuild_univariate_over_polyring and then calling the univariate
# `resultant`. Falls back cleanly (returns (nothing, nothing, msg)) if
# either the ring construction or the resultant call itself fails or is
# unavailable in this Oscar version, per the task's requirement to report
# unavailability rather than silently switching strategy.
function resultant_x3(g0, g1, vars)
    x3s, x4s = vars
    Fp = base_ring(parent(g0))

    val, err = try_diag() do
        Tbase, _ = polynomial_ring(Fp, :x4)   # Fp[x4], fresh generator
        T, y = polynomial_ring(Tbase, :x3)    # (Fp[x4])[x3]

        h0 = rebuild_univariate_over_polyring(g0, x3s, x4s, T, y)
        h1 = rebuild_univariate_over_polyring(g1, x3s, x4s, T, y)

        R_raw = resultant(h0, h1)   # element of Fp[x4] (T's base ring) --
                                     # or, when the resultant happens to be
                                     # constant, sometimes a bare Fp scalar
                                     # (FqFieldElem) instead of a degree-0
                                     # Tbase element; coerce explicitly below
                                     # rather than relying on that ever being
                                     # a Tbase-typed value on the nose.
        R_wrapped = Tbase(R_raw)
        (R_wrapped, Tbase)
    end

    if err !== nothing
        return (nothing, nothing, "resultant_x3: unavailable or failed: $err")
    end

    (R_wrapped, Tbase) = val
    return (R_wrapped, Tbase, nothing)
end

# Finds all Fp-RATIONAL roots of a univariate polynomial R (over Fp, i.e.
# an element of some Fp[t] ring) WITHOUT calling factor().
#
# Why this exists rather than just calling factor(R) and keeping the
# degree-1 factors: on this project's Fp = GF(prime) field type,
# factor(R) for large-degree R can hit an internal Nemo bug (a bare
# FqFieldElem getting passed through Base.convert instead of the proper
# FqPolyRingElem constructor, deep inside factor()'s root-extraction code)
# and crash outright rather than returning a result -- see the
# resultant_x3 comment above R_wrapped = Tbase(R_raw) for the same failure
# mode hit one level up. Rather than working around a bug inside a black-box
# library call, this sidesteps factor() entirely for the "just get me the
# Fp-rational roots" case, using the standard exact identity:
#
#   the product of ALL distinct linear factors (x - r) of R, over r in Fp
#   that are roots of R, equals gcd(R(x), x^p - x)
#
# (x^p - x factors as the product of (x-r) over every r in Fp, by Fermat's
# little theorem -- x^p = x for every element of Fp). So:
#
#   1. g = gcd(R, x^p - x)  -- squarefree, degree = number of distinct
#      Fp-rational roots of R.
#   2. g's own degree is small in every case this fast path actually calls
#      this helper on (it only runs after a resultant/gcd step has already
#      cut things down), so its roots are extracted via gcd-based
#      Cantor-Zassenhaus-style splitting rather than by evaluating at every
#      element of Fp (p can be ~10^6-10^7 here, too slow to trial-evaluate
#      per candidate root).
#
# Computing x^p - x itself would need a degree-p exponentiation, exactly as
# expensive as what's being avoided -- but x^p MOD R (not x^p - x directly)
# is cheap via square-and-multiply: O(log p) polynomial multiplications,
# each reduced mod R so degree never exceeds ~2*deg(R). This is the
# standard "distinct-degree factorization, stage 1" building block.
function rational_roots_via_frobenius_gcd(R, p::UInt64)
    Ux = parent(R)
    x = gen(Ux)
    Fp_field = base_ring(Ux)

    deg_R = degree(R)
    deg_R <= 0 && return elem_type(Fp_field)[]  # nothing to do; caller checks constant/zero separately

    # Compute x^p mod R via square-and-multiply, reducing mod R after every
    # multiplication so intermediate degree never exceeds ~2*deg(R).
    xp_mod_R = powermod(x, p, R)

    g = gcd(xp_mod_R - x, R)
    deg_g = iszero(g) ? -1 : degree(g)
    deg_g <= 0 && return elem_type(Fp_field)[]

    # g is now squarefree of (typically small) degree deg_g, with every
    # root being Fp-rational. Peel off roots one at a time via gcd with a
    # random linear shift (Cantor-Zassenhaus-style splitting), which stays
    # correct (not just probabilistically fast) because g is guaranteed
    # fully split over Fp already -- each gcd(g, (x+s)^((p-1)/2) - 1) is
    # exact, not a Monte Carlo guess about g's factorization type.
    roots = elem_type(Fp_field)[]
    remaining = g

    attempts_since_progress = 0
    while degree(remaining) >= 1
        if degree(remaining) == 1
            c1 = coeff(remaining, 1)
            c0 = coeff(remaining, 0)
            push!(roots, -c0 * inv(c1))
            remaining = one(Ux)
            break
        end

        s = Fp_field(rand(0:(p - 1)))
        shifted = remaining(x + s)   # remaining(x + s)
        half_pow = powermod(shifted, div(p - 1, 2), remaining)
        split_candidate = gcd(half_pow - one(Ux), remaining)

        if degree(split_candidate) >= 1 && degree(split_candidate) < degree(remaining)
            factor1 = split_candidate
            factor2 = divexact(remaining, split_candidate)
            # Extract linear roots from whichever side has degree 1,
            # recurse (via the same loop) on whatever's left by just
            # continuing to split the smaller nontrivial piece.
            for part in (factor1, factor2)
                d = degree(part)
                if d == 1
                    c1 = coeff(part, 1)
                    c0 = coeff(part, 0)
                    push!(roots, -c0 * inv(c1))
                elseif d >= 2
                    append!(roots, rational_roots_via_frobenius_gcd_split(part, p))
                end
            end
            remaining = one(Ux)
            break
        else
            attempts_since_progress += 1
            attempts_since_progress > 200 &&
                error("rational_roots_via_frobenius_gcd: splitting stalled after 200 " *
                      "attempts on a degree-$(degree(remaining)) squarefree-and-fully-split " *
                      "factor -- unexpected for a prime field of this size")
        end
    end

    return roots
end

# Helper used by the recursive-split branch above: identical splitting
# logic, factored out so rational_roots_via_frobenius_gcd's main loop
# doesn't need to recurse into itself with different argument shapes.
# Returns plain Fp scalars, same as rational_roots_via_frobenius_gcd.
function rational_roots_via_frobenius_gcd_split(remaining, p::UInt64)
    Ux = parent(remaining)
    x = gen(Ux)
    Fp_field = base_ring(Ux)
    roots = elem_type(Fp_field)[]

    stack = [remaining]
    attempts_since_progress = 0
    while !isempty(stack)
        cur = pop!(stack)
        d = degree(cur)
        if d <= 0
            continue
        elseif d == 1
            c1 = coeff(cur, 1)
            c0 = coeff(cur, 0)
            push!(roots, -c0 * inv(c1))
            continue
        end

        s = Fp_field(rand(0:(p - 1)))
        shifted = cur(x + s)
        half_pow = powermod(shifted, div(p - 1, 2), cur)
        split_candidate = gcd(half_pow - one(Ux), cur)

        if degree(split_candidate) >= 1 && degree(split_candidate) < d
            attempts_since_progress = 0
            push!(stack, split_candidate)
            push!(stack, divexact(cur, split_candidate))
        else
            attempts_since_progress += 1
            attempts_since_progress > 200 &&
                error("rational_roots_via_frobenius_gcd_split: splitting stalled after " *
                      "200 attempts on a degree-$d factor")
            push!(stack, cur)
        end
    end

    return roots
end

# Factors R(x4) over Fp and returns the list of Fp-rational roots coming
# from R's LINEAR factors only (a degree>=2 irreducible factor over Fp
# contributes roots only in an extension field, which this fast path does
# not chase -- see the module docstring above on why that is an accepted
# tradeoff here). Returns (roots, nothing) on success or (nothing, msg) if
# R is zero, or (empty_vector, nothing) if R is a nonzero constant, or
# (nothing, msg) if root-finding itself is unavailable/fails.
#
# NOTE: this deliberately does NOT call factor(R) -- see
# rational_roots_via_frobenius_gcd's docstring for why (a Nemo bug on this
# project's Fp = GF(prime) field type crashes factor() on large-degree
# polynomials). gcd/powermod-based root finding sidesteps that entirely
# and is also, incidentally, cheaper: it never attempts to find the
# irreducible factorization of the non-Fp-rational part of R at all.
function candidate_roots_from_resultant(R, Tbase)
    if R === nothing
        return (nothing, "candidate_roots_from_resultant: no resultant available")
    end
    if iszero(R)
        return (nothing, "candidate_roots_from_resultant: resultant is identically zero " *
                "(g0,g1 have infinitely many common x3-roots as x4 varies, or share a " *
                "common factor -- see the common-factor diagnostic in section 4)")
    end
    if is_constant(R)
        return (elem_type(base_ring(Tbase))[], nothing)  # no roots -- R is a nonzero constant
    end

    val, err = try_diag() do
        Fp = base_ring(Tbase)
        p = UInt64(characteristic(Fp))
        rational_roots_via_frobenius_gcd(R, p)
    end

    if err !== nothing
        return (nothing, "candidate_roots_from_resultant: root-finding failed: $err")
    end
    return (val, nothing)
end

# Specializes x4 = b into g0 and g1 (both elements of Fp[x3,x4]), producing
# two univariate polynomials in x3 (over Fp), and returns their gcd h_b
# together with its degree and (if h_b splits completely over Fp) its
# roots. Uses the same exponent/coefficient-array-walk strategy as
# rebuild_univariate_over_polyring rather than a generic evaluate() call,
# since this runs once per candidate root and needs to stay cheap.
function specialize_and_gcd(g0, g1, vars, b)
    x3s, x4s = vars
    Fp = base_ring(parent(g0))

    val, err = try_diag() do
        Ux3, x3u = polynomial_ring(Fp, :x3)

        function specialize_to_x3(g)
            gens_list = gens(parent(g))
            idx3 = findfirst(==(x3s), gens_list)
            idx4 = findfirst(==(x4s), gens_list)
            (idx3 === nothing || idx4 === nothing) &&
                error("specialize_and_gcd: could not locate x3/x4 generators")

            acc = Dict{Int, elem_type(Fp)}()
            for (e, c) in zip(AbstractAlgebra.exponent_vectors(g), AbstractAlgebra.coefficients(g))
                d3 = e[idx3]
                d4 = e[idx4]
                term = c * b^d4
                acc[d3] = haskey(acc, d3) ? acc[d3] + term : term
            end

            p = zero(Ux3)
            for (d3, c) in acc
                is_zero(c) && continue
                p += c * x3u^d3
            end
            return p
        end

        p0 = specialize_to_x3(g0)
        p1 = specialize_to_x3(g1)

        if iszero(p0) || iszero(p1)
            return (p0, p1, nothing, -1, nothing, false)
        end

        h = gcd(p0, p1)
        deg_h = iszero(h) ? -1 : degree(h)

        splits_completely = false
        roots_h = nothing
        if deg_h >= 1
            rval, rerr = try_diag() do
                p = UInt64(characteristic(Fp))
                rs = rational_roots_via_frobenius_gcd(h, p)
                (rs, length(rs) == deg_h)
            end
            if rerr === nothing
                roots_h, splits_completely = rval
            end
        end

        (p0, p1, h, deg_h, roots_h, splits_completely)
    end

    if err !== nothing
        return (nothing, "specialize_and_gcd: failed at x4=$b: $err")
    end
    return (val, nothing)
end

# Orchestrates steps 1-3 of the resultant-then-gcd strategy for one pair
# (g0,g1), reporting the diagnostics requested in the task: degree of the
# resultant in x4, number of Fp-rational roots, per-root gcd degree /
# splitting behaviour, and the total candidate (x3,x4) point count found.
# Never raises on a failed resultant/factorization -- reports the failure
# in the returned NamedTuple's `notes` field and continues with whatever
# partial information is available, per the "no silent fallback" /
# "report cleanly and continue" requirements.
function solve_pair_via_resultant(g0, g1, vars, label::String)
    notes = String[]
    R, Tbase, err = resultant_x3(g0, g1, vars)

    if err !== nothing
        push!(notes, err)
        return (label=label, resultant_degree=-1, n_roots=0,
                candidates=Tuple{Any,Any}[], per_root=NamedTuple[], notes=notes)
    end

    resultant_degree = iszero(R) ? -1 : (is_constant(R) ? 0 : degree(R))

    roots, rerr = candidate_roots_from_resultant(R, Tbase)
    if rerr !== nothing
        push!(notes, rerr)
        return (label=label, resultant_degree=resultant_degree, n_roots=0,
                candidates=Tuple{Any,Any}[], per_root=NamedTuple[], notes=notes)
    end

    per_root = NamedTuple[]
    candidates = Tuple{Any,Any}[]

    for b in roots
        sg, serr = specialize_and_gcd(g0, g1, vars, b)
        if serr !== nothing
            push!(notes, serr)
            push!(per_root, (x4=b, gcd_degree=-1, splits_completely=false,
                              n_points=0, note=serr))
            continue
        end

        (p0, p1, h, deg_h, roots_h, splits_completely) = sg

        if deg_h <= 0
            push!(per_root, (x4=b, gcd_degree=deg_h, splits_completely=false,
                              n_points=0, note=nothing))
            continue
        end

        if splits_completely && roots_h !== nothing
            n_points = length(roots_h)
            for a in roots_h
                push!(candidates, (a, b))
            end
        else
            # gcd is nonconstant but does not split completely over Fp (or
            # factoring it failed) -- its degree is recorded above as the
            # best proxy for the number of common roots (with multiplicity,
            # over the algebraic closure), but no Fp-rational points are
            # fabricated for it here.
            n_points = 0
        end

        push!(per_root, (x4=b, gcd_degree=deg_h, splits_completely=splits_completely,
                          n_points=n_points, note=nothing))
    end

    return (label=label, resultant_degree=resultant_degree, n_roots=length(roots),
            candidates=candidates, per_root=per_root, notes=notes)
end

# Small formatting helper for solve_pair_via_resultant's return value,
# kept separate from summarize_effective_fiber_degree so the per-pair
# report layout is easy to change without touching the U/V orchestration.
function print_pair_summary(r)
    if r.resultant_degree < 0
        println("      degree_x4(resultant) = (resultant unavailable or identically zero)")
    else
        println("      degree_x4(resultant) = ", r.resultant_degree)
    end
    println("      Fp-rational roots of resultant: ", r.n_roots)

    for pr in r.per_root
        if pr.note !== nothing
            println("        x4=", pr.x4, ": ", pr.note)
        else
            splits_str = pr.gcd_degree <= 0 ? "n/a" : string(pr.splits_completely)
            println("        x4=", pr.x4,
                    ": gcd_degree(x3)=", pr.gcd_degree,
                    ", splits completely over Fp? ", splits_str,
                    ", Fp-rational points here=", pr.n_points)
        end
    end

    println("      total candidate (x3,x4) points over Fp: ", length(r.candidates))

    if !isempty(r.notes)
        println("      notes:")
        for n in r.notes
            println("        - ", n)
        end
    end
end

# Reports the diagnostics for both U and V (and, if U produced any
# candidate points, a cross-pair consistency count: how many of U's
# candidate (x3,x4) points also satisfy V0=V1=0 there -- the "combined
# four-polynomial consistency check" from the task). Returns the effective
# fiber degree estimates (U, V, and the combined count) to fold into the
# run-level summary. This is what section 8 now calls as the PRIMARY
# effective-degree estimator, in place of the timed Groebner/FGLM
# strategies below (which are still run, but only as a secondary
# cross-check -- see the note above the old Section 8 block).
function summarize_effective_fiber_degree(u0, u1, v0, v1, vars)
    println("    [U] resultant-then-gcd (eliminating x3, over Fp[x4]):")
    u_result = solve_pair_via_resultant(u0, u1, vars, "U")
    print_pair_summary(u_result)

    println()
    println("    [V] resultant-then-gcd (eliminating x3, over Fp[x4]):")
    v_result = solve_pair_via_resultant(v0, v1, vars, "V")
    print_pair_summary(v_result)

    combined_n = -1
    if isempty(u_result.candidates)
        combined_n = 0
        println()
        println("    [U+V] combined four-polynomial consistency check: skipped ",
                "(no U-candidate points to check against V)")
    else
        println()
        println("    [U+V] combined four-polynomial consistency check:")
        combined_points = Tuple{Any,Any}[]
        for (a, b) in u_result.candidates
            ok, cerr = try_diag() do
                iszero(evaluate(v0, [a, b])) && iszero(evaluate(v1, [a, b]))
            end
            if cerr !== nothing
                println("      point (", a, ",", b, "): could not check against V (", cerr, ")")
                continue
            end
            if ok
                push!(combined_points, (a, b))
            end
        end
        combined_n = length(combined_points)
        println("      ", length(u_result.candidates),
                " U-candidate point(s) checked against V0,V1; ",
                combined_n, " also satisfy V0=V1=0")
    end

    println()
    println("    Effective fiber degree estimate (Fp-rational candidate points): ",
            "U=", length(u_result.candidates),
            ", V=", length(v_result.candidates),
            ", U∩V=", combined_n)

    return (U=u_result, V=v_result, combined_n=combined_n)
end

# ---------------------------------------------------------------------------

# Section 8 (OLD): timed Groebner/FGLM elimination with a HARD timeout.
# No longer the primary estimator (see summarize_effective_fiber_degree
# above) -- kept as an optional secondary cross-check, still run per
# sample and reported in its own summary block, but the resultant-then-gcd
# path above is what main() now leads with.

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

    # U/V/combined effective-fiber-degree counts from the resultant-then-gcd
    # estimator, one entry per sample -- used for the CONSISTENT/INCONSISTENT
    # style summary at the end, same as the old timed-strategy degrees.
    resultant_fiber_degrees = (U=Int[], V=Int[], combined=Int[])

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
        println("  --- [FULL SYSTEM] 8a. Effective fiber degree via resultant-then-gcd ---")
        println("  (PRIMARY estimator -- no Groebner basis, FGLM, Hilbert series, or lex")
        println("   conversion is used anywhere in this section)")
        fiber_result = summarize_effective_fiber_degree(u0, u1, v0, v1, vars)
        push!(resultant_fiber_degrees.U, length(fiber_result.U.candidates))
        push!(resultant_fiber_degrees.V, length(fiber_result.V.candidates))
        push!(resultant_fiber_degrees.combined, max(fiber_result.combined_n, 0))
        flush(stdout)

        println()
        println("  --- [FULL SYSTEM] 8b. (secondary cross-check) Timed elimination on <U0,U1,V0,V1> ---")
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
    println("Summary (section 8 only -- sections 1-7 are per-sample diagnostics,")
    println("see above)")
    println("=" ^ 70)

    println("resultant_then_gcd (PRIMARY estimator, section 8a):")
    for (key, degs) in pairs(resultant_fiber_degrees)
        if isempty(degs)
            println("  ", key, ": no samples")
        elseif all(==(degs[1]), degs)
            println("  ", key, ": CONSISTENT at ", degs[1],
                    " Fp-rational candidate point(s) across ", length(degs), " sample(s)")
        else
            println("  ", key, ": INCONSISTENT across samples: ", degs)
        end
    end
    println()

    println("timed Groebner/FGLM (secondary cross-check, section 8b):")
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






















