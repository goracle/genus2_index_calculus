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
#   julia pilot_diagnostic.jl <U0.native> <U1.native> <V0.native> <V1.native> <prime> [n_samples] [seed] [timeout_secs] [numerical_resultant_timeout_secs]
#
#   U0.native, U1.native : NEWTPOL2 v2 native files (with coefficients),
#                           as produced by convert_to_native.jl <input> <output> <ambient_dim> <prime>.
#                           These are loaded up front as raw (support,
#                           coeffs) arrays only (see load_raw_polynomial) --
#                           NOT reconstructed as Oscar MPolyRingElem objects,
#                           since specialize() (below) works directly off
#                           the raw arrays. See the comment on
#                           load_raw_polynomial for why.
#   V0.native, V1.native : NEWTPOL2 v2 native files for the second equation
#                           pair. Unlike U0/U1, these are NEVER fully loaded
#                           into an Oscar ring object -- they're only used by
#                           the numerical_resultant strategy, which streams
#                           and specializes them term-by-term straight off
#                           disk into a dense raw array, once per (alpha,
#                           beta) sample (see stream_specialize_native_to_dense).
#   prime                : the F_p modulus -- must match what the native
#                           files were converted with (checked against the
#                           file's own stored prime; mismatch is an error)
#   n_samples             : number of random (x1,x4) specialization points
#                           to run diagnostics on (default 10)
#   seed                  : RNG seed for reproducible sample points (default 0)
#   timeout_secs          : per-strategy hard timeout in section 8 for
#                           grevlex_analysis and resultant_x2, in seconds
#                           (default 30) -- does NOT apply to
#                           numerical_resultant, see next arg
#   numerical_resultant_timeout_secs : separate, much larger timeout just for
#                           numerical_resultant (default 1200 = 20 minutes).
#                           Its gamma-loop cost is driven by the larger of
#                           the U-pair and V-pair Sylvester dimensions; at
#                           V's individual degree 96 that's a 192x192
#                           determinant at each of ~18433 sample points,
#                           which is minutes per sample, not seconds -- so
#                           it needs its own budget rather than sharing
#                           section 8's general timeout_secs.
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
# Raw modular arithmetic helpers (no ring objects, no Oscar/Nemo types) --
# used exclusively by the numerical_resultant strategy's hot paths (the
# streaming V-file specializer and the Horner/Sylvester/determinant inner
# loop), where the whole point is to avoid the overhead of symbolic
# polynomial ring elements.
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
# alpha^e1 and beta^e4 (and, in the Horner loop, gamma^k implicitly via
# repeated multiplication rather than modpow -- see the loop itself).
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
# Fp[x2,x3] -- the same output shape specialize() produces for U0/U1, so
# V0/V1 can be fed through the exact same sections 1-7 diagnostics. This
# NEVER holds the file's full support/coeffs arrays in memory (unlike
# load_native_support_with_coeffs, which bulk-reads everything with a
# single `read!` into full-length arrays): it reads the NEWTPOL2 header
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
    isfile(path) || error("stream_specialize_native_to_poly: no such file: $path")

    fsize_mb = filesize(path) / 1024 / 1024
    println("    stream_specialize_native_to_poly: streaming ", path,
            " (", round(fsize_mb, digits=1), " MB on disk)...")
    flush(stdout)
    t0 = time()

    p = expected_prime
    alpha_r = coeff_to_u64(alpha) % p
    beta_r = coeff_to_u64(beta) % p

    io = open(path, "r")
    local ambient_dim, n_terms, file_prime
    acc = Dict{Tuple{Int,Int}, UInt64}()
    try
        magic = read(io, UInt64)
        magic == NATIVE_SUPPORT_MAGIC_V2 ||
            error("stream_specialize_native_to_poly: $path does not have the " *
                  "expected NEWTPOL2 header (got magic=$(magic), expected " *
                  "$(NATIVE_SUPPORT_MAGIC_V2)) -- streaming specialization " *
                  "requires coefficients, so this must be a v2 file")
        ambient_dim = read(io, Int64)
        ambient_dim == 4 ||
            error("stream_specialize_native_to_poly: $path has ambient_dim=" *
                  "$ambient_dim, expected 4 (x1,x2,x3,x4)")
        n_terms = read(io, Int64)
        n_terms > 0 ||
            error("stream_specialize_native_to_poly: $path has n_terms=$n_terms " *
                  "in its header, expected a positive integer")
        file_prime = read(io, UInt64)
        file_prime == expected_prime ||
            error("stream_specialize_native_to_poly: $path was converted with " *
                  "prime=$file_prime, but $expected_prime was expected -- these " *
                  "must match or the specialized coefficients would be silently wrong")

        # Precompute alpha^e1 mod p and beta^e4 mod p on demand via a small
        # memoizing cache -- e1,e4 range only up to whatever individual
        # degree x1,x4 have in the source polynomial (small, tens at most,
        # nowhere near the 17.8M term count), so a Dict cache here is cheap
        # and avoids a fresh modpow call per term for repeated exponents.
        alpha_pow_cache = Dict{Int,UInt64}(0 => UInt64(1) % p)
        beta_pow_cache = Dict{Int,UInt64}(0 => UInt64(1) % p)
        function cached_pow(cache::Dict{Int,UInt64}, base::UInt64, e::Int)
            v = get(cache, e, nothing)
            v !== nothing && return v
            val = modpow(base, e, p)
            cache[e] = val
            return val
        end

        exp_buf = Vector{Int32}(undef, chunk_terms * ambient_dim)
        coeff_buf = Vector{UInt64}(undef, chunk_terms)

        terms_done = 0
        while terms_done < n_terms
            this_chunk = min(chunk_terms, n_terms - terms_done)
            exp_view = @view exp_buf[1:(this_chunk * ambient_dim)]
            read!(io, exp_view)
            coeff_view = @view coeff_buf[1:this_chunk]
            read!(io, coeff_view)

            @inbounds for i in 1:this_chunk
                base = (i - 1) * ambient_dim
                e1 = Int(exp_view[base + 1])
                e2 = Int(exp_view[base + 2])
                e3 = Int(exp_view[base + 3])
                e4 = Int(exp_view[base + 4])
                c = coeff_view[i] % p

                a_pow = cached_pow(alpha_pow_cache, alpha_r, e1)
                b_pow = cached_pow(beta_pow_cache, beta_r, e4)
                scale = modmul(a_pow, b_pow, p)
                term = modmul(c, scale, p)

                key = (e2, e3)
                acc[key] = haskey(acc, key) ? modadd(acc[key], term, p) : term
            end

            terms_done += this_chunk
            if terms_done % 5_000_000 == 0 || terms_done == n_terms
                println("      ", terms_done, "/", n_terms,
                        " terms streamed+specialized (", round(time() - t0, digits=1), "s)")
                flush(stdout)
            end
        end
    finally
        close(io)
    end

    ctx = MPolyBuildCtx(S2)
    Fp = base_ring(S2)
    for (key, c_u) in acc
        iszero(c_u) && continue
        push_term!(ctx, Fp(c_u), [key[1], key[2]])
    end
    poly = finish(ctx)
    println("    stream_specialize_native_to_poly: done in ",
            round(time() - t0, digits=1), "s (", length(poly), " terms after collapsing)")
    flush(stdout)
    return poly
end
                e1 = Int(exp_view[base + 1])
                e2 = Int(exp_view[base + 2])
                e3 = Int(exp_view[base + 3])
                e4 = Int(exp_view[base + 4])
                c = coeff_view[i] % p

                a_pow = cached_pow(alpha_pow_cache, alpha_r, e1, p)
                b_pow = cached_pow(beta_pow_cache, beta_r, e4, p)
                scale = modmul(a_pow, b_pow, p)
                term = modmul(c, scale, p)

                acc[e2 + 1, e3 + 1] = modadd(acc[e2 + 1, e3 + 1], term, p)
            end

            terms_done += this_chunk
            if terms_done % 5_000_000 == 0 || terms_done == n_terms
                println("      pass 2/2: ", terms_done, "/", n_terms,
                        " terms streamed+specialized (", round(time() - t0, digits=1), "s)")
                flush(stdout)
            end
        end

        println("    stream_specialize_native_to_dense: done in ",
                round(time() - t0, digits=1), "s")
        flush(stdout)
        return acc
    finally
        close(io)
    end
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

# Loads a v2 native file's RAW (support, coeffs) arrays only -- no
# MPolyBuildCtx reconstruction into an Oscar MPolyRingElem. Used for
# U0/U1: specialize() (below) was rewritten to work directly off these
# flat arrays rather than an Oscar polynomial object, since iterating an
# already-built MPolyRingElem's term stream via
# AbstractAlgebra.exponent_vectors/coefficients at 17.8M terms is what
# caused the apparent hang on Sample 1 -- that iterator protocol isn't
# guaranteed O(1) per step, and at this term count a non-constant-time
# iterate() turns an intended O(n) specialize() pass into something far
# worse. Skipping the Oscar reconstruction entirely for U0/U1 also saves
# the ~5s MPolyBuildCtx build step and the memory of holding a giant
# Oscar polynomial object that, per the earlier code audit, was never
# actually used for anything except being handed straight to specialize().
function load_raw_polynomial(path::String, expected_prime::UInt64)
    (supp, coeffs, ambient_dim, file_prime) = load_native_support_with_coeffs(path)
    ambient_dim == 4 ||
        error("load_raw_polynomial: $path has ambient_dim=$ambient_dim, expected 4 " *
              "(x1,x2,x3,x4) -- this pilot script is hard-coded for the 4-variable case")
    file_prime == expected_prime ||
        error("load_raw_polynomial: $path was converted with prime=$file_prime, but " *
              "$expected_prime was given on the command line -- these must match " *
              "or the specialized coefficients would be silently wrong")
    return (supp, coeffs)
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
#
# IMPORTANT: this now takes the RAW (supp, coeffs) arrays from
# load_raw_polynomial directly, NOT an Oscar polynomial object -- see the
# comment on load_raw_polynomial for why iterating an already-built
# MPolyRingElem's term stream at 17.8M terms was the actual hang.
function specialize(supp::Vector{Vector{Int}}, coeffs::Vector{UInt64}, S2, alpha, beta, prime::UInt64)
    p = prime
    alpha_u = coeff_to_u64(alpha) % p  # only 2 calls total (alpha, beta) -- try/catch cost is irrelevant here
    beta_u = coeff_to_u64(beta) % p

    n = length(supp)
    length(coeffs) == n ||
        error("specialize: support has $n terms, coeffs has $(length(coeffs)) -- length mismatch")

    # Memoizing power caches -- e1,e4 range only up to the individual
    # degree of f in x1,x4 (small), so this avoids a fresh modpow per term
    # for repeated exponents, same pattern as
    # stream_specialize_native_to_dense.
    alpha_pow_cache = Dict{Int,UInt64}(0 => UInt64(1) % p)
    beta_pow_cache = Dict{Int,UInt64}(0 => UInt64(1) % p)
    function cached_pow(cache::Dict{Int,UInt64}, base::UInt64, e::Int)
        v = get(cache, e, nothing)
        v !== nothing && return v
        val = modpow(base, e, p)
        cache[e] = val
        return val
    end

    # Accumulate into a raw UInt64 (mod p) dict keyed by (e2,e3). This
    # iterates the RAW arrays returned by load_raw_polynomial -- plain
    # Vector indexing, guaranteed O(1) per step -- rather than
    # AbstractAlgebra.exponent_vectors(f)/coefficients(f) on an already-
    # built Oscar MPolyRingElem, which is what actually caused the
    # apparent hang on Sample 1: that iterator protocol isn't guaranteed
    # O(1) per step, and at 17.8M terms a non-constant iterate() turns an
    # intended O(n) pass into something far worse. No FqFieldElem ring
    # arithmetic anywhere in this loop either (each ^ and * on a ring
    # element allocates; across 17.8M terms x 2 polys x 10 samples that
    # raw allocation volume was also contributing to the driver process's
    # earlier OOM crash). Only the final nonzero terms get converted back
    # to Fp at the end, in `finish`.
    acc = Dict{Tuple{Int,Int}, UInt64}()
    @inbounds for i in 1:n
        e1, e2, e3, e4 = supp[i]
        a_pow = cached_pow(alpha_pow_cache, alpha_u, e1)
        b_pow = cached_pow(beta_pow_cache, beta_u, e4)
        scale = modmul(a_pow, b_pow, p)
        c_u = coeffs[i] % p
        term = modmul(c_u, scale, p)
        key = (e2, e3)
        acc[key] = haskey(acc, key) ? modadd(acc[key], term, p) : term
    end

    ctx = MPolyBuildCtx(S2)
    Fp = base_ring(S2)
    for (key, c_u) in acc
        iszero(c_u) && continue
        push_term!(ctx, Fp(c_u), [key[1], key[2]])
    end
    return finish(ctx)
end

# ---------------------------------------------------------------------------
# Dense raw-array machinery for the numerical_resultant strategy: given a
# bivariate polynomial as a dense (dx2+1) x (dx3+1) UInt64 coefficient
# matrix (indices [e2+1, e3+1], mod p), reduce it to a univariate
# coefficient vector at x3=gamma via Horner's method, build a concrete
# Sylvester matrix from two such vectors, and compute its determinant via
# in-place modular Gaussian elimination -- all on raw UInt64 arrays, no
# Oscar/Nemo ring objects anywhere in these functions.
# ---------------------------------------------------------------------------

# Horner-reduce a dense bivariate coefficient matrix M (indices
# [e2+1, e3+1], row e2 holds the x3-coefficients of the x2^e2 term) at
# x3=gamma, returning a length-(size(M,1)) vector where entry e2+1 is the
# coefficient of x2^e2 in M(x2, gamma). For each row (fixed e2), this is
# exactly univariate Horner evaluation of that row's polynomial-in-x3 at
# gamma: c[dx3]*gamma^dx3 + ... + c[0] evaluated as
# (((c[dx3])*gamma + c[dx3-1])*gamma + ...)*gamma + c[0].
function horner_reduce_x3(M::Matrix{UInt64}, gamma::UInt64, p::UInt64)
    dx2p1, dx3p1 = size(M)
    out = Vector{UInt64}(undef, dx2p1)
    @inbounds for e2 in 1:dx2p1
        acc = UInt64(0)
        for e3 in dx3p1:-1:1
            acc = modadd(modmul(acc, gamma, p), M[e2, e3], p)
        end
        out[e2] = acc
    end
    return out
end

# Builds the (da+db) x (db) ... standard (da+db) x (da+db) Sylvester matrix
# over raw Fp (as a Matrix{UInt64}) for two univariate polynomials given as
# coefficient vectors a (length da+1, a[k+1] = coeff of x^k) and b (length
# db+1), via the classical shifted-row construction -- same layout as the
# earlier symbolic sylvester_matrix_fp, just over raw UInt64 instead of Fp
# ring elements.
function sylvester_matrix_raw(a::Vector{UInt64}, da::Int, b::Vector{UInt64}, db::Int, p::UInt64)
    n = da + db
    M = zeros(UInt64, n, n)
    @inbounds for i in 1:db
        for k in 0:da
            M[i, i + (da - k)] = a[k + 1]
        end
    end
    @inbounds for i in 1:da
        for k in 0:db
            M[db + i, i + (db - k)] = b[k + 1]
        end
    end
    return M
end

# In-place modular determinant via Gaussian elimination with partial
# pivoting (search for any nonzero pivot in the column -- "partial" here
# meaning "first nonzero found", since over a finite field there is no
# magnitude to compare, only zero/nonzero) over raw UInt64 mod p. Destroys
# M (operates in place on a copy the caller provides). Returns the
# determinant as a UInt64 residue mod p, or UInt64(0) if M is singular.
#
# This is the "low-overhead, concrete row-reduction determinant check"
# requested in place of a generic library det() call on a symbolic-ring
# matrix, since library det() on Fp-typed AbstractAlgebra matrices carries
# ring-element dispatch overhead per arithmetic operation that a raw
# UInt64 loop avoids.
function det_mod_p!(M::Matrix{UInt64}, p::UInt64)
    n = size(M, 1)
    n == size(M, 2) || error("det_mod_p!: matrix is not square ($(size(M)))")
    det_val = UInt64(1) % p
    @inbounds for col in 1:n
        # Find a nonzero pivot in this column at or below row `col`.
        pivot_row = 0
        for row in col:n
            if !iszero(M[row, col])
                pivot_row = row
                break
            end
        end
        if pivot_row == 0
            return UInt64(0)  # singular
        end
        if pivot_row != col
            # Swap rows; each swap flips the sign of the determinant.
            for k in 1:n
                M[pivot_row, k], M[col, k] = M[col, k], M[pivot_row, k]
            end
            det_val = modsub(p, det_val, p)  # negate: det_val = p - det_val, i.e. -det_val mod p
            iszero(det_val) && (det_val = UInt64(0))  # guard the p-0 edge case
        end
        pivot = M[col, col]
        det_val = modmul(det_val, pivot, p)
        inv_pivot = modinv(pivot, p)
        for row in (col + 1):n
            factor = modmul(M[row, col], inv_pivot, p)
            iszero(factor) && continue
            for k in col:n
                M[row, k] = modsub(M[row, k], modmul(factor, M[col, k], p), p)
            end
        end
    end
    return det_val
end

# Converts an already-specialized bivariate Oscar polynomial g (in x2,x3
# over Fp, as produced by the existing `specialize` function) into a dense
# (deg_x2+1) x (deg_x3+1) raw UInt64 matrix, indices [e2+1, e3+1]. This is
# a one-time O(n_terms) extraction per polynomial per outer sample (n_terms
# here is at most a few thousand -- g0/g1 have 4225 terms per the pilot
# run -- not the 17.8M-term scale of the original U/V files), used so the
# numerical_resultant strategy's hot gamma-loop never touches ring objects.
function oscar_poly_to_dense(g, deg_x2::Int, deg_x3::Int, p::UInt64)
    M = zeros(UInt64, deg_x2 + 1, deg_x3 + 1)
    for (exps, c) in zip(AbstractAlgebra.exponent_vectors(g), AbstractAlgebra.coefficients(g))
        e2, e3 = exps[1], exps[2]
        M[e2 + 1, e3 + 1] = coeff_to_u64(c) % p
    end
    return M
end



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

function serialize_pair_for_worker(path, g0, g1, prime::UInt64;
                                    v0_path::Union{String,Nothing}=nothing,
                                    v1_path::Union{String,Nothing}=nothing,
                                    alpha_raw::Union{UInt64,Nothing}=nothing,
                                    beta_raw::Union{UInt64,Nothing}=nothing)
    supp0 = collect(AbstractAlgebra.exponent_vectors(g0))
    coef0 = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g0)]
    supp1 = collect(AbstractAlgebra.exponent_vectors(g1))
    coef1 = UInt64[coeff_to_u64(c) for c in AbstractAlgebra.coefficients(g1)]
    open(path, "w") do io
        serialize(io, (prime, supp0, coef0, supp1, coef1, v0_path, v1_path, alpha_raw, beta_raw))
    end
end

# Worker-side entry point: reconstructs g0,g1 from the temp file, runs the
# ONE requested strategy, writes (status, elapsed, deg, info) to the result
# file. status is one of :ok, :error. This branch only runs when this
# script is invoked as `julia pilot_diagnostic.jl --diagnostic-worker
# <infile> <outfile> <strategy>` (see dispatch at the bottom of the file).
function run_worker(infile::String, outfile::String, strategy::String)
    (prime, supp0, coef0, supp1, coef1, v0_path, v1_path, alpha_raw, beta_raw) = open(deserialize, infile)
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
            # Double Specialization (Numerical Resultant) strategy -- dense
            # raw-array rewrite, now covering all four equations (U0,U1,
            # V0,V1), not just U0,U1.
            #
            # Background / why all four equations: U0=U1 and V0=V1 are the
            # two independent constraints (Mumford u(x) match, Mumford v(x)
            # match) that cut the 4-variable ambient space (x1,x2,x3,x4)
            # down to a 2-dimensional variety. This worker already receives
            # U0,U1 pre-specialized at x1=alpha,x4=beta (as g0,g1, bivariate
            # in x2,x3) from the driver. Since x1,x4 are already fixed, what
            # remains at THIS (alpha,beta) sample is a slice of that 2D
            # variety -- generically a FINITE set of (x2,x3) points, not a
            # curve. Using only U0,U1 (as the original numerical_resultant
            # did) computes Res_x2(U0,U1) = R_U(x3), which is generically a
            # nonzero degree-~8192 curve in x3 -- that's expected, since it
            # ignores the V constraints entirely. The actual finite solution
            # set requires BOTH pairs: it's exactly the common roots (in x3)
            # of R_U(x3) = Res_x2(U0,U1) and R_V(x3) = Res_x2(V0,V1).
            #
            # V0,V1 are NOT already loaded (unlike U0,U1) -- both U files
            # together already use the available RAM, and there isn't room
            # to also hold a full V file's term arrays, let alone two. So
            # V0 and V1 are each streamed straight from disk via
            # stream_specialize_native_to_dense (term-by-term, accumulating
            # directly into a dense mod-p array, never materializing the
            # full support/coeffs arrays or any Oscar ring object), once
            # per OUTER (alpha,beta) sample -- i.e. once per call to this
            # worker, not once per inner gamma point. The inner gamma-loop
            # below only ever touches the four resulting dense arrays.
            #
            # Per-step outline (dense-array / raw-arithmetic only, no
            # symbolic ring objects anywhere in the gamma-loop):
            #   1. Convert g0,g1 (already-specialized Oscar polys) into
            #      dense (deg+1)x(deg+1) raw UInt64 (mod p) coefficient
            #      matrices -- 65x65 for U0/U1 (individual degree 64).
            #   2. Stream-load and specialize V0, V1 directly into their
            #      own dense raw matrices (fresh disk read each worker
            #      call, per Claire's memory-budget constraint -- U's fit
            #      comfortably and are left alone, V's don't and are
            #      reloaded+respecialized every time). V0/V1 have
            #      individual degree 96 (97x97), NOT the same as U's 64 --
            #      the U-side and V-side dense arrays, Horner vectors, and
            #      Sylvester matrices are all sized independently off each
            #      pair's own actual degree (see d0x2/d1x2/d0x3/d1x3 for U
            #      and d0x2_v/d1x2_v/d0x3_v/d1x3_v for V below), never
            #      assumed equal.
            #   3. For each gamma in [0, Dbound]: Horner-reduce all four
            #      dense matrices at x3=gamma into univariate coefficient
            #      vectors, build TWO concrete Sylvester matrices sized off
            #      each pair's own degree sum (128x128 for U0,U1; 192x192
            #      for V0,V1, given individual degree 64 and 96
            #      respectively), and compute both determinants via
            #      in-place modular Gaussian elimination -- giving
            #      point-values R_U(gamma), R_V(gamma). Dbound is likewise
            #      pair-specific: 8192 for U (64*64+64*64), 18432 for V
            #      (96*96+96*96) -- the sweep below samples enough points
            #      to cover the LARGER of the two, so it's driven by V's
            #      18432 bound, not U's 8192.
            #   4. After the sweep: gamma values where BOTH R_U and R_V
            #      vanish are candidate x3 solutions of the full 4-equation
            #      system. For each such gamma, recover x2 via gcd of the
            #      univariate specializations U0(x2,gamma), U1(x2,gamma)
            #      (computed once more, off the hot loop, via Oscar's
            #      symbolic gcd on the reconstructed univariate polys --
            #      this only runs for the rare common-root candidates, not
            #      all 8193 points, so the earlier "no ring objects in the
            #      loop" constraint doesn't apply here). If no common root
            #      exists at all, the sample is reported INCONSISTENT (the
            #      slice of the 2D variety at this (alpha,beta) is empty).
            info_parts = String[]
            t0 = time()

            v0_path === nothing && error("numerical_resultant: v0_path was not provided -- " *
                                          "the driver must pass V0's native file path for this strategy")
            v1_path === nothing && error("numerical_resultant: v1_path was not provided -- " *
                                          "the driver must pass V1's native file path for this strategy")
            alpha_raw === nothing && error("numerical_resultant: alpha_raw was not provided")
            beta_raw === nothing && error("numerical_resultant: beta_raw was not provided")

            d0x2, d1x2 = degree(g0, x2s), degree(g1, x2s)
            d0x3, d1x3 = degree(g0, x3s), degree(g1, x3s)
            d_bound_u = d0x2 * d1x3 + d1x2 * d0x3
            syl_dim_u = d0x2 + d1x2

            # 1. Dense-array conversion of the already-specialized U0,U1.
            g0_dense = oscar_poly_to_dense(g0, d0x2, d0x3, prime)
            g1_dense = oscar_poly_to_dense(g1, d1x2, d1x3, prime)

            # 2. Stream-load and specialize V0, V1 fresh from disk, this
            #    call only -- see the long comment above for why this is
            #    NOT cached/reused across gamma points or across worker
            #    invocations.
            println("    numerical_resultant: streaming V0 and V1 for this sample (alpha=",
                    alpha_raw, ", beta=", beta_raw, ")...")
            flush(stdout)
            h0_dense = stream_specialize_native_to_dense(v0_path, prime, alpha_raw, beta_raw)
            h1_dense = stream_specialize_native_to_dense(v1_path, prime, alpha_raw, beta_raw)

            # Individual x2/x3 degrees of the specialized V polys, read off
            # the dense arrays' actual nonzero extent (rather than assumed
            # equal to U's 64/64, in case V's structure differs).
            function dense_degree_x2(M::Matrix{UInt64})
                for e2 in size(M,1):-1:1
                    any(!iszero, @view M[e2, :]) && return e2 - 1
                end
                return -1  # zero polynomial
            end
            function dense_degree_x3(M::Matrix{UInt64})
                for e3 in size(M,2):-1:1
                    any(!iszero, @view M[:, e3]) && return e3 - 1
                end
                return -1
            end
            d0x2_v = dense_degree_x2(h0_dense)
            d1x2_v = dense_degree_x2(h1_dense)
            d0x3_v = dense_degree_x3(h0_dense)
            d1x3_v = dense_degree_x3(h1_dense)
            (d0x2_v < 0 || d1x2_v < 0) &&
                error("numerical_resultant: a specialized V polynomial is identically zero " *
                      "at this sample point (d0x2_v=$d0x2_v, d1x2_v=$d1x2_v) -- cannot form " *
                      "a Sylvester matrix from a zero polynomial")
            d_bound_v = d0x2_v * d1x3_v + d1x2_v * d0x3_v
            syl_dim_v = d0x2_v + d1x2_v

            # The two resultants R_U(x3), R_V(x3) have (in general) DIFFERENT
            # degree bounds, so sample enough points to cover the larger of
            # the two -- using the same sample points for both sweeps (so
            # "common root at gamma" is a direct comparison, not requiring
            # separate interpolation grids).
            d_bound = max(d_bound_u, d_bound_v)
            n_points = d_bound + 1

            push!(info_parts, "Dbound_U=$d_bound_u (syl_dim=$syl_dim_u), " *
                               "Dbound_V=$d_bound_v (syl_dim=$syl_dim_v), sampling $n_points points")

            ru_zero_gammas = Int[]
            rv_zero_gammas = Int[]
            common_root_gammas = Int[]

            for i in 0:(n_points - 1)
                gamma = UInt64(i) % prime
                try
                    ru_val = UInt64(0)
                    rv_val = UInt64(0)

                    # R_U(gamma): only defined/needed while i is within the
                    # U-pair's own sample range; reuse the same gamma value
                    # otherwise (Res is a polynomial, well-defined at any
                    # scalar, so evaluating past d_bound_u is still valid,
                    # just samples more points than strictly required for
                    # U alone -- harmless, just extra work already paid for
                    # by needing n_points for V).
                    a_u = horner_reduce_x3(g0_dense, gamma, prime)
                    b_u = horner_reduce_x3(g1_dense, gamma, prime)
                    Mu = sylvester_matrix_raw(a_u, d0x2, b_u, d1x2, prime)
                    ru_val = det_mod_p!(Mu, prime)

                    a_v = horner_reduce_x3(h0_dense, gamma, prime)
                    b_v = horner_reduce_x3(h1_dense, gamma, prime)
                    Mv = sylvester_matrix_raw(a_v, d0x2_v, b_v, d1x2_v, prime)
                    rv_val = det_mod_p!(Mv, prime)

                    ru_is_zero = iszero(ru_val)
                    rv_is_zero = iszero(rv_val)
                    ru_is_zero && push!(ru_zero_gammas, i)
                    rv_is_zero && push!(rv_zero_gammas, i)
                    (ru_is_zero && rv_is_zero) && push!(common_root_gammas, i)
                catch e
                    # Per the project's error-handling convention: catch
                    # cleanly, do not swallow -- re-raise with a
                    # descriptive message so it is reported through the
                    # worker's (:error, ...) result rather than silently
                    # miscounted.
                    error("numerical_resultant: evaluation failed at sample point " *
                          "index=$i, gamma=$gamma: $(sprint(showerror, e))")
                end
            end

            push!(info_parts, "R_U zero at $(length(ru_zero_gammas))/$n_points sampled points, " *
                               "R_V zero at $(length(rv_zero_gammas))/$n_points sampled points")

            deg_report = -1
            if isempty(common_root_gammas)
                push!(info_parts, "NO COMMON ROOTS FOUND -- the system (U0=U1=V0=V1=0) is " *
                                   "INCONSISTENT at this (alpha,beta) sample; the slice of the " *
                                   "2D variety at this point is empty over the $n_points sampled " *
                                   "x3 values (note: this is a sampled check, not an exhaustive " *
                                   "one if n_points < p -- see Dbound above for the sample count " *
                                   "actually used)")
            else
                # For each common-root gamma, recover x2 via gcd of the
                # univariate specializations of U0,U1 at that x3 value --
                # this DOES use Oscar ring objects, but only for the (small,
                # generically very few) common-root candidates, not for all
                # n_points sampled gammas, so it stays cheap.
                solutions = Tuple{Int,Any}[]
                for gi in common_root_gammas
                    gamma_fp = Fp(gi)
                    Ux, _ = polynomial_ring(Fp, "x")
                    a_u = horner_reduce_x3(g0_dense, UInt64(gi) % prime, prime)
                    b_u = horner_reduce_x3(g1_dense, UInt64(gi) % prime, prime)
                    pu = Ux([Fp(c) for c in a_u])
                    qu = Ux([Fp(c) for c in b_u])
                    g_gcd, gcd_err = try_diag() do
                        gcd(pu, qu)
                    end
                    if gcd_err === nothing && !is_unit(g_gcd) && !iszero(g_gcd)
                        push!(solutions, (gi, "x2 root(s) of gcd, degree=$(degree(g_gcd))"))
                    else
                        push!(solutions, (gi, "gcd step " * (gcd_err === nothing ? "gave unit/zero (no shared x2 root found numerically)" : gcd_err)))
                    end
                end
                push!(info_parts, "COMMON ROOTS FOUND at $(length(common_root_gammas)) sampled " *
                                   "gamma value(s): " *
                                   join(["x3=$gi ($desc)" for (gi, desc) in solutions], "; "))
                deg_report = length(common_root_gammas)
            end

            elapsed = time() - t0
            (:ok, elapsed, deg_report, join(info_parts, " | "))
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
function run_with_timeout(g0, g1, prime::UInt64, strategy::String, timeout_secs::Real, script_path::String;
                           v0_path::Union{String,Nothing}=nothing,
                           v1_path::Union{String,Nothing}=nothing,
                           alpha_raw::Union{UInt64,Nothing}=nothing,
                           beta_raw::Union{UInt64,Nothing}=nothing)
    tmpdir = mktempdir()
    infile = joinpath(tmpdir, "in.jls")
    outfile = joinpath(tmpdir, "out.jls")
    serialize_pair_for_worker(infile, g0, g1, prime;
                               v0_path=v0_path, v1_path=v1_path,
                               alpha_raw=alpha_raw, beta_raw=beta_raw)

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
    length(ARGS) >= 5 ||
        error("pilot_diagnostic.jl: usage: julia pilot_diagnostic.jl " *
              "<U0.native> <U1.native> <V0.native> <V1.native> <prime> " *
              "[n_samples] [seed] [timeout_secs] [numerical_resultant_timeout_secs]")

    u0_path = ARGS[1]
    u1_path = ARGS[2]
    v0_path = ARGS[3]
    v1_path = ARGS[4]
    prime = parse(UInt64, ARGS[5])
    n_samples = length(ARGS) >= 6 ? parse(Int, ARGS[6]) : 10
    seed = length(ARGS) >= 7 ? parse(Int, ARGS[7]) : 0
    timeout_secs = length(ARGS) >= 8 ? parse(Float64, ARGS[8]) : 30.0
    # numerical_resultant's gamma-loop cost is driven by the LARGER of the
    # U-pair and V-pair degree sums -- with V at individual degree 96 (vs
    # U's 64), its Sylvester determinants are 192x192 (vs 128x128) and the
    # sweep needs ~18433 sample points (vs U alone's 8193), which is on the
    # order of minutes per sample, not seconds. It gets its own, much
    # larger default timeout rather than sharing section 8's general 30s
    # budget (which is sized for the cheap grevlex-based strategies).
    numerical_resultant_timeout_secs = length(ARGS) >= 9 ? parse(Float64, ARGS[9]) : 1200.0

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
    println("timeout:      ", timeout_secs, "s per strategy in section 8 " *
                              "(numerical_resultant uses its own ", numerical_resultant_timeout_secs, "s)")
    println()

    Fp = GF(prime)
    S2, (y2, y3) = polynomial_ring(Fp, [:x2, :x3])

    println("Loading U0 (raw arrays, no Oscar reconstruction)...")
    (supp0, coeffs0) = load_raw_polynomial(u0_path, prime)
    println("Loading U1 (raw arrays, no Oscar reconstruction)...")
    (supp1, coeffs1) = load_raw_polynomial(u1_path, prime)
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
        g0 = specialize(supp0, coeffs0, S2, a, b, prime)
        g1 = specialize(supp1, coeffs1, S2, a, b, prime)
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
        println("  --- 8. Timed elimination (hard timeout=", timeout_secs, "s for grevlex/resultant, ",
                 numerical_resultant_timeout_secs, "s for numerical_resultant, subprocess-isolated) ---")
        for (name, strategy) in timed_strategies
            print("    [", name, "] running in subprocess... ")
            flush(stdout)
            # Only numerical_resultant needs V-file paths and raw alpha/beta
            # (to stream-specialize V0,V1 on the worker side); other
            # strategies work purely off the already-specialized g0,g1 and
            # shouldn't pay for passing this extra data through. It also
            # gets its own, much larger timeout -- see the definition of
            # numerical_resultant_timeout_secs above for why.
            if strategy == "numerical_resultant"
                (elapsed, deg, info) = run_with_timeout(g0, g1, prime, strategy, numerical_resultant_timeout_secs, script_path;
                                                         v0_path=v0_path, v1_path=v1_path,
                                                         alpha_raw=coeff_to_u64(a), beta_raw=coeff_to_u64(b))
            else
                (elapsed, deg, info) = run_with_timeout(g0, g1, prime, strategy, timeout_secs, script_path)
            end
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
