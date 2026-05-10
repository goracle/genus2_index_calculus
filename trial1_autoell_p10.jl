#!/usr/bin/env julia
# =============================================================================
#  genus2_dlp.jl  —  Basic index calculus (Gaudry-Harley) for genus-2 Jacobian
#
#  Curve:   C : y² = x⁵ + 3x³ + 2x² + 5x + 4   over  F_p,   p = 164147 (≈ 10× larger)
#  Target:  cyclic subgroup  ⟨G⟩ ⊆ Jac(C/Fp)  of prime order  ell computed automatically
#  Problem: given G, T = k·G, recover k
#
#  Algorithm outline (Gaudry-Harley):
#   1. Factor base F = first `fb_size` rational affine points of C
#   2. Relation collection: pick random (α,β), compute D = α·G + β·T;
#      if D's Mumford u-poly splits over Fp with both roots in F, record
#      the linear congruence  α + β·k ≡ Σ rj·dlog(Fj)  (mod ell)
#   3. Left-kernel: find γ with γᵀ·R = 0 (mod ell); recover k = -(Σγα)/(Σγβ)
#
#  To swap in your own relation-generation strategy, replace the block
#  between the RELATION GENERATION markers in index_calculus() below.
# =============================================================================

using LinearAlgebra, Printf, Primes, Oscar

# ─────────────────────────── Global parameters ────────────────────────────────
# Accept an optional command-line argument: the prime (or near-prime) to use.
# We find the next prime >= the supplied value, mirroring Sage's next_prime().
function _next_prime(n::Int)::Int
    n < 2 && return 2
    candidate = n % 2 == 0 ? n + 1 : n
    while !isprime(candidate)
        candidate += 2
    end
    return candidate
end

const p = let
    if !isempty(ARGS)
        raw = tryparse(Int, ARGS[1])
        raw === nothing && error("Command-line argument must be an integer, got: $(ARGS[1])")
        np = _next_prime(raw)
        np != raw && println("next_prime($raw) = $np  →  using p = $np")
        np
    else
        164147   # default
    end
end
ell = 0  # computed automatically at runtime
# f(x) = x^5 + 3x^3 + 2x^2 + 5x + 4;  F_POLY[i] = coeff of x^(i-1)
const F_POLY = Int[4, 5, 2, 3, 0, 1]

# ─────────────────────────── Fp arithmetic ────────────────────────────────────
@inline fp(x::Integer)    = mod(x, p)
@inline fpinv(x::Integer) = powermod(fp(x), p - 2, p)

# Square root in Fp via Tonelli-Shanks (works for any odd prime p).
function sqrt_fp(a::Int)
    a = fp(a);  a == 0 && return 0
    # Quick Euler criterion: a^((p-1)/2) must be 1
    powermod(a, (p - 1) >> 1, p) == 1 || return nothing
    if p % 4 == 3
        r = powermod(a, (p + 1) >> 2, p)
        return fp(r * r) == a ? r : nothing
    end
    # Tonelli-Shanks for p ≡ 1 (mod 4)
    Q, S = p - 1, 0
    while Q % 2 == 0; Q >>= 1; S += 1; end
    # Find a quadratic non-residue z
    z = 2
    while powermod(z, (p - 1) >> 1, p) != p - 1; z += 1; end
    M2 = S
    c = powermod(z, Q, p)
    t = powermod(a, Q, p)
    r = powermod(a, (Q + 1) >> 1, p)
    while true
        t == 1 && return r
        i, tmp = 1, fp(t * t)
        while tmp != 1; tmp = fp(tmp * tmp); i += 1; end
        b = powermod(c, 1 << (M2 - i - 1), p)
        M2 = i
        c = fp(b * b)
        t = fp(t * c)
        r = fp(r * b)
    end
end

# ─────────────────────── Polynomial ring Fp[x] ────────────────────────────────
# Representation: Vector{Int} with poly[i] = coeff of x^(i-1); always trimmed.
#
# Allocation discipline: every function that returns a fresh Vector allocates
# exactly one output vector and nothing else.  In particular:
#   - ptrim!  mutates in place (resize!); ptrim returns a new trimmed copy.
#   - padd/psub/pmul each allocate exactly one output vector.
#   - pneg/pscale avoid broadcast temporaries by using a manual loop.
#   - pdivrem trims the remainder in-place via resize! rather than re-slicing.
#   - pgcd_ext is the main Cantor hot path; its alloc count per call is O(deg).

# Trim trailing zeros in-place; returns the same vector.
function ptrim!(a::Vector{Int})
    n = length(a)
    while n > 1 && a[n] == 0; n -= 1; end
    n < length(a) && resize!(a, n)
    a
end

# Allocating trim (used when a new vector is needed).
function ptrim(a::Vector{Int})
    n = length(a)
    while n > 1 && a[n] == 0; n -= 1; end
    n == length(a) ? copy(a) : a[1:n]
end

# Degree without allocating a trimmed copy.
function pdeg(a::Vector{Int})
    n = length(a)
    while n > 1 && a[n] == 0; n -= 1; end
    n - 1
end

pzero(a::Vector{Int}) = (length(a) == 1 && a[1] == 0)

function padd(a::Vector{Int}, b::Vector{Int})
    la, lb = length(a), length(b)
    c = Vector{Int}(undef, max(la, lb))
    if la >= lb
        @inbounds for i in 1:lb;  c[i] = fp(a[i] + b[i]); end
        @inbounds for i in lb+1:la; c[i] = fp(a[i]); end
    else
        @inbounds for i in 1:la;  c[i] = fp(a[i] + b[i]); end
        @inbounds for i in la+1:lb; c[i] = fp(b[i]); end
    end
    ptrim!(c)
end

function psub(a::Vector{Int}, b::Vector{Int})
    la, lb = length(a), length(b)
    c = Vector{Int}(undef, max(la, lb))
    if la >= lb
        @inbounds for i in 1:lb;  c[i] = fp(a[i] - b[i]); end
        @inbounds for i in lb+1:la; c[i] = fp(a[i]); end
    else
        @inbounds for i in 1:la;  c[i] = fp(a[i] - b[i]); end
        @inbounds for i in la+1:lb; c[i] = fp(-b[i]); end
    end
    ptrim!(c)
end

function pmul(a::Vector{Int}, b::Vector{Int})
    la, lb = length(a), length(b)
    c = zeros(Int, la + lb - 1)
    @inbounds for i in 1:la, j in 1:lb
        c[i+j-1] = fp(c[i+j-1] + a[i] * b[j])
    end
    ptrim!(c)
end

function pneg(a::Vector{Int})
    c = Vector{Int}(undef, length(a))
    @inbounds for i in eachindex(a); c[i] = fp(-a[i]); end
    ptrim!(c)
end

function pscale(a::Vector{Int}, s::Int)
    s = fp(s)
    c = Vector{Int}(undef, length(a))
    @inbounds for i in eachindex(a); c[i] = fp(a[i] * s); end
    ptrim!(c)
end

# In-place: scale a by s, trim, return a.  No allocation.
function pscale!(a::Vector{Int}, s::Int)
    s = fp(s)
    @inbounds for i in eachindex(a); a[i] = fp(a[i] * s); end
    ptrim!(a)
end

# In-place: negate a, trim, return a.  No allocation.
function pneg!(a::Vector{Int})
    @inbounds for i in eachindex(a); a[i] = fp(-a[i]); end
    ptrim!(a)
end

# Compute F_POLY - V*V into a pre-allocated buffer dst (resized as needed).
# Returns the degree-5 result in dst.  One allocation avoided vs psub(F_POLY, pmul(V,V)).
function f_minus_vsq!(dst::Vector{Int}, V::Vector{Int})
    lv = length(V)
    # V*V has degree 2*(lv-1), so length lv+lv-1; F_POLY has length 6.
    lout = max(6, 2 * lv - 1)
    resize!(dst, lout)
    fill!(dst, 0)
    # Add F_POLY
    @inbounds for i in 1:6; dst[i] = fp(dst[i] + F_POLY[i]); end
    # Subtract V^2
    @inbounds for i in 1:lv, j in 1:lv
        dst[i+j-1] = fp(dst[i+j-1] - V[i] * V[j])
    end
    ptrim!(dst)
end

function peval(poly::Vector{Int}, x::Int)
    x = fp(x); r = 0
    for i in length(poly):-1:1; r = fp(r * x + poly[i]); end
    r
end

function pdivrem(a::Vector{Int}, b::Vector{Int})
    # Work on trimmed mutable copies
    a = ptrim(copy(a))
    b = ptrim(copy(b))

    if pzero(b)
        error("Division by zero polynomial")
    end

    db = pdeg(b)
    lb = b[end]

    # Leading coefficient of divisor must be invertible mod p
    if lb == 0
        error("Invalid divisor: leading coefficient is zero")
    end
    lc_inv = fpinv(lb)

    # Quotient size: max degree difference + 1, but at least 1
    q = zeros(Int, max(1, length(a) - length(b) + 1))

    while !pzero(a) && pdeg(a) >= db
        da = pdeg(a)
        d  = da - db

        # Leading term cancellation coefficient
        c = fp(a[end] * lc_inv)
        q[d + 1] = c

        # Subtract c * x^d * b from a
        @inbounds for i in eachindex(b)
            a[i + d] = fp(a[i + d] - c * b[i])
        end

        # Hard-kill the top coefficient we just canceled
        a[end] = 0

        # CRITICAL FIX:
        # actually shrink the vector every iteration.
        # Your old code only moved `da` logically, but left stale
        # high-degree zeros sitting around, which can cause repeated
        # reprocessing / effective infinite loops depending on pdeg().
        while length(a) > 1 && a[end] == 0
            pop!(a)
        end
    end

    # Final trim for quotient
    while length(q) > 1 && q[end] == 0
        pop!(q)
    end

    return q, a
end


pmod(a, b) = pdivrem(a, b)[2]

# Extended GCD: returns (g, s, t) with g monic, g = s·a + t·b
function pgcd_ext(a0::Vector{Int}, b0::Vector{Int})
    r0, r1 = ptrim(a0), ptrim(b0)
    s0, s1 = Int[1], Int[0]
    t0, t1 = Int[0], Int[1]
    while !pzero(r1)
        q, r2 = pdivrem(r0, r1)
        r0, r1 = r1, r2
        s0, s1 = s1, psub(s0, pmul(q, s1))
        t0, t1 = t1, psub(t0, pmul(q, t1))
    end
    sc = fpinv(r0[end])
    pscale(r0, sc), pscale(s0, sc), pscale(t0, sc)
end

# ──────────────────────── Genus-2 Jacobian (Cantor) ───────────────────────────
# A reduced divisor D = Div2(u, v) satisfies:
#   u monic deg ≤ 2,  deg v < deg u,  u | v² - f.
# Identity element: u = [1], v = [0].

struct Div2
    u::Vector{Int}
    v::Vector{Int}
end

Base.:(==)(A::Div2, B::Div2) = (A.u == B.u) && (A.v == B.v)

# Without this, Dict{Div2,Int} hashes by pointer (mutable Vector fields),
# so baby-giant collisions in jac_order_bsgs never fire.  Julia's built-in
# hash(::Vector{Int}, h) does content hashing, so this is correct and O(deg).
function Base.hash(D::Div2, h::UInt)
    h = hash(D.u, h)
    h = hash(D.v, h)
    h
end

const JacID = Div2(Int[1], Int[0])
jac_isid(D::Div2) = pdeg(D.u) == 0

function jac_add(D1::Div2, D2::Div2)::Div2
    jac_isid(D1) && return D2
    jac_isid(D2) && return D1

    u1, v1, u2, v2 = D1.u, D1.v, D2.u, D2.v

    # ── Composition ───────────────────────────────────────────────────────────
    d1, e1, e2 = pgcd_ext(u1, u2)

    if pdeg(d1) == 0                            # gcd(u1,u2) = 1  (generic path)
        U = pmul(u1, u2)
        V = pmod(padd(pmul(pmul(e1, u1), v2),
                      pmul(pmul(e2, u2), v1)), U)
    else                                        # degenerate: shared root(s)
        d, c1, c2 = pgcd_ext(d1, padd(v1, v2))
        s1 = pmul(c1, e1);  s2 = pmul(c1, e2)
        U, _  = pdivrem(pmul(u1, u2), pmul(d, d))   # exact
        Vn    = padd(padd(pmul(pmul(s1, u1), v2), pmul(pmul(s2, u2), v1)),
                     pmul(c2, padd(pmul(v1, v2), F_POLY)))
        Vd, _ = pdivrem(Vn, d)                       # exact
        V     = pmod(Vd, U)
    end

    U = pscale(U, fpinv(U[end]))                # make monic

    # ── Reduction: while deg(U) > g = 2 ──────────────────────────────────────
    # Reuse a single buffer for f - V² across reduction steps.
    _tmp = Vector{Int}(undef, 6)
    while pdeg(U) > 2
        f_minus_vsq!(_tmp, V)                   # _tmp = F_POLY - V²  (no alloc)
        U2, _ = pdivrem(_tmp, U)                # exact: U | V²-f
        pscale!(U2, fpinv(U2[end]))             # make monic in-place
        pneg!(V)                                # V = -V in-place
        V = pmod(V, U2)                         # one alloc (pmod result)
        U = U2
    end

    Div2(ptrim(U), ptrim(V))
end

jac_neg(D::Div2)             = Div2(D.u, pmod(pneg(D.v), D.u))
jac_sub(D1::Div2, D2::Div2) = jac_add(D1, jac_neg(D2))

# Raw scalar multiplication — no modular reduction of the scalar
function jac_mul_raw(D::Div2, n::Integer)::Div2
    n = Int(n);  n == 0 && return JacID
    R = JacID;  Q = D
    while n > 0
        isodd(n) && (R = jac_add(R, Q))
        Q = jac_add(Q, Q);  n >>= 1
    end
    R
end

# Scalar multiplication in the ell-order subgroup (reduces n mod ell)
jac_mul(D::Div2, n::Integer) = jac_mul_raw(D, mod(n, ell))

# ──────────────────────── Order / subgroup selection ─────────────────────────
# Find the exact order of a Jacobian element by BSGS, using the Hasse-Weil bound
# (#Jac ≲ (sqrt(p)+1)^4) as a safe search radius.  This is enough here because
# p is still modest, so a table of O(p) Jacobian elements is practical.
function jac_order_bsgs(D::Div2; verbose::Bool=false)::Int
    # Safe upper bound for the group order.
    B = (isqrt(p) + 1)^4
    m = isqrt(B) + 1

    baby = Dict{Div2,Int}()
    cur  = JacID
    for j in 0:m-1
        haskey(baby, cur) || (baby[cur] = j)
        cur = jac_add(cur, D)
    end

    step = cur            # m·D
    giant = step
    best  = 0

    # Search for a collision i·m·D = j·D, i>=1, 0<=j<m.
    for i in 1:m
        if haskey(baby, giant)
            j = baby[giant]
            cand = i*m - j
            if cand > 0 && (best == 0 || cand < best)
                best = cand
            end
        end
        giant = jac_add(giant, step)
    end

    best == 0 && error("jac_order_bsgs failed to find a multiple within the Hasse-Weil bound")

    # Reduce the candidate down to the exact order.
    function factor_int(n::Int)::Dict{Int,Int}
        fac = Dict{Int,Int}()
        x = n
        while x % 2 == 0
            fac[2] = get(fac, 2, 0) + 1
            x ÷= 2
        end
        d = 3
        while d*d <= x
            while x % d == 0
                fac[d] = get(fac, d, 0) + 1
                x ÷= d
            end
            d += 2
        end
        x > 1 && (fac[x] = get(fac, x, 0) + 1)
        fac
    end

    n = best
    fac = factor_int(n)
    for q in sort!(collect(keys(fac)))
        while n % q == 0 && jac_isid(jac_mul_raw(D, div(n, q)))
            n ÷= q
        end
    end

    verbose && @printf("  element order = %d (found from BSGS candidate %d)\n", n, best)
    return n
end

# ---------------------------------------------------------------------------
#  Pollard rho for Jacobian element order computation.
#
#  We want ord(D) given that ord(D) | N (the Hasse-Weil bound).
#  Strategy: run Pollard rho on the cyclic group ⟨D⟩ of order N to find
#  a collision  aD = bD  ⟹  (a-b)D = 0  ⟹  ord(D) | (a-b).
#  Then divide out prime factors to get the exact order, just as in BSGS.
#
#  The walk is the standard Floyd-cycle / distinguished-point variant on
#  the product group Z_N × ⟨D⟩.  We use 3-way splitting:
#    S0: add D    (xD = (a+1)D,  a += 1)
#    S1: double   (2xD,          a *= 2)
#    S2: add D    (xD = (a+1)D,  a += 1)  [asymmetric split avoids period-2]
#  Classification is by hash of the Mumford u-poly's first coefficient.
#
#  Distinguished-point criterion: low-order bits of u[1] all zero.
#  This avoids the O(√N) table of BSGS while keeping expected work O(√N).
#
#  Returns the exact element order, or falls back to jac_order_bsgs on failure.
# ---------------------------------------------------------------------------
function jac_order_pollard_rho(
    D::Div2;
    N::Int = 0,
    max_iter::Int = 0,
    dp_mask::Int = 1023,
    verbose::Bool = false,
    abort_flag::Union{Threads.Atomic{Bool}, Nothing} = nothing
)::Int

    if N == 0
        N = (isqrt(p) + 1)^4
    end

    if max_iter == 0
        max_iter = 64 * p + 10_000
    end

    # ------------------------------------------------------------------
    # Cancellation helper — throws InterruptException if abort_flag is set.
    # Callers catch this and treat it as a clean early exit.
    # ------------------------------------------------------------------
    @inline function maybe_abort()
        abort_flag !== nothing && abort_flag[] && throw(InterruptException())
    end

    # ------------------------------------------------------------------
    # Precompute small multiples of D (constant throughout the walk).
    # These are used in rho_step; computing them on every step via
    # jac_mul_raw hit 50% of steps and was the primary rho bottleneck.
    # ------------------------------------------------------------------
    D_neg = jac_neg(D)
    D2    = jac_add(D, D)
    D3    = jac_add(D2, D)
    D5    = jac_add(D3, D2)
    D7    = jac_add(D5, D2)

    # ------------------------------------------------------------------
    # Random walk update
    # ------------------------------------------------------------------

    @inline function rho_step(X::Div2, a::Int)

        maybe_abort()

        s = Int(X.u[1]) & 7   # cheap 3-bit classify; was mod(hash(...), 8)

        if s == 0
            return jac_add(X, D),    mod(a + 1, N)
        elseif s == 1
            return jac_add(X, X),    mod(2a, N)
        elseif s == 2
            return jac_add(jac_add(X, X), D), mod(2a + 1, N)
        elseif s == 3
            return jac_add(X, D3),   mod(a + 3, N)
        elseif s == 4
            return jac_add(X, D5),   mod(a + 5, N)
        elseif s == 5
            return jac_add(jac_add(X, X), D3), mod(2a + 3, N)
        elseif s == 6
            return jac_add(X, D_neg), mod(a - 1, N)
        else
            return jac_add(X, D7),   mod(a + 7, N)
        end
    end

    # ------------------------------------------------------------------
    # Distinguished points
    # ------------------------------------------------------------------

    dp_table = Dict{UInt64, Int}()

    @inline function dp_hash(X::Div2)::UInt64

        u0 = length(X.u) >= 1 ? UInt64(X.u[1]) : 0
        u1 = length(X.u) >= 2 ? UInt64(X.u[2]) : 0
        v0 = length(X.v) >= 1 ? UInt64(X.v[1]) : 0
        v1 = length(X.v) >= 2 ? UInt64(X.v[2]) : 0

        return xor(
            u0,
            xor(
                u1 << 13,
                xor(v0 << 27, v1 << 41)
            )
        )
    end

    X  = D
    a  = 1

    dp_found = 0

    for iter in 1:max_iter

        maybe_abort()

        # --------------------------------------------------------------
        # Distinguished point collision detection
        # --------------------------------------------------------------

        h = dp_hash(X)

        if (h & UInt64(dp_mask)) == 0

            if haskey(dp_table, h)

                a_prev = dp_table[h]

                diff = mod(a - a_prev, N)

                if diff != 0

                    return _reduce_to_order(D, diff, N)
                end

            else

                dp_table[h] = a
                dp_found += 1
            end
        end

        X, a = rho_step(X, a)
    end

    verbose && @printf(
        "  [pollard_rho] max_iter=%d reached after %d distinguished points\n",
        max_iter,
        dp_found
    )

    # fallback
    return jac_order_bsgs(D; verbose = verbose)
end



# Helper: given that n = candidate is a multiple of ord(D), reduce to exact order.
function _reduce_to_order(D::Div2, candidate::Int, N::Int)::Int
    n = candidate
    function factor_int_small(x::Int)::Dict{Int,Int}
        fac = Dict{Int,Int}()
        d = 2
        while d * d <= x
            while x % d == 0
                fac[d] = get(fac, d, 0) + 1
                x ÷= d
            end
            d += 1
        end
        x > 1 && (fac[x] = get(fac, x, 0) + 1)
        fac
    end
    fac = factor_int_small(n)
    for q in sort!(collect(keys(fac)))
        while n % q == 0 && jac_isid(jac_mul_raw(D, n ÷ q))
            n ÷= q
        end
    end
    n
end


# Find a random generator of prime order ell by first determining the exact
# order of a random element, then taking its largest prime divisor.
function largest_prime_factor(n::Int)
    n <= 1 && return 0
    fac = Oscar.factor(ZZ(n))   # factor over ZZ; returns Fac{ZZRingElem}
    return maximum(Int(q) for (q, _) in fac)
end


# ──────────────────────── Jacobian order via Frobenius point-counting ────────
# For a genus-2 curve C/Fp, the characteristic polynomial of Frobenius is
#
#   χ(T) = T^4 - s1·T^3 + s2·T^2 - p·s1·T + p^2
#
# where  s1 = N1 - (p+1)  and  s2 = (s1^2 - (N2 - (p^2+1))) / 2,
# with N1 = #C(Fp), N2 = #C(Fp^2)  (affine + point at infinity).
#
# Then  #Jac(C/Fp) = χ(1) = 1 - s1 + s2 - p·s1 + p^2.
#
# N1 is free (caller may pass the pre-enumerated affine count via `n1`).
# N2 requires one O(p) pass over Fp^2 = Fp[sqrt(g)] for a non-residue g,
# using the norm criterion: f(a+b√g) is a square in Fp^2 iff its Fp-norm
# u²-g·v² is a nonzero square in Fp  (Lidl-Niederreiter, standard fact).
function jacobian_order_frobenius(; n1::Union{Int,Nothing}=nothing)::Int
    # Find a quadratic non-residue g in F_p
    g = 2
    while powermod(g, (p - 1) ÷ 2, p) != p - 1
        g += 1
    end

    ####################################################################
    # N1 = #C(F_p)
    ####################################################################
    if n1 === nothing
        n1_local = 1  # point at infinity

        @inbounds for x in 0:p-1
            fx = eval_f(x)

            if fx == 0
                n1_local += 1
            elseif powermod(fx, (p - 1) ÷ 2, p) == 1
                n1_local += 2
            end
        end
    else
        # caller passed affine count
        n1_local = n1 + 1
    end

    ####################################################################
    # N2 = #C(F_{p^2})
    #
    # Outer loop over b is embarrassingly parallel: each b-row is
    # independent.  Use per-thread accumulators to avoid atomic contention.
    ####################################################################
    # Precompute constants once
    g_mod = fp(g)

    nthreads = Threads.nthreads()
    n2_partial = zeros(Int, nthreads)

    Threads.@threads :static for tid in 1:nthreads
        chunk = cld(p - 1, nthreads)
        b_lo  = (tid - 1) * chunk + 1
        b_hi  = min(tid * chunk, p - 1)
        local_n2 = 0

        for b in b_lo:b_hi
            bg   = fp(b * g_mod)
            b2g  = fp(b * bg)
            i1   = b
            i2_c = fp(2 * b)

            for a in 0:p-1
                r1 = a
                r2 = fp(a * a + b2g)
                i2 = fp(a * i2_c)
                r3 = fp(r2 * r1 + g_mod * i2 * i1)
                i3 = fp(r2 * i1 + i2 * r1)
                r5 = fp(r3 * r2 + g_mod * i3 * i2)
                i5 = fp(r3 * i2 + i3 * r2)
                fu = fp(r5 + 3r3 + 2r2 + 5r1 + 4)
                fv = fp(i5 + 3i3 + 2i2 + 5i1)

                if fu == 0 && fv == 0
                    local_n2 += 2
                    continue
                end
                norm_f = fp(fu * fu - g_mod * fp(fv * fv))
                if norm_f != 0 && powermod(norm_f, (p - 1) ÷ 2, p) == 1
                    local_n2 += 4
                end
            end
        end
        n2_partial[tid] = local_n2
    end

    n2 = Int(n1_local) + sum(n2_partial) + 1   # +1 for point at infinity over F_{p²}

    ####################################################################
    # Recover Jacobian order from N1, N2
    ####################################################################
    s1 = n1_local - (p + 1)
    s2 = (s1^2 - (n2 - (p^2 + 1))) ÷ 2

    return 1 - s1 + s2 - p * s1 + p^2
end



function find_ell_generator(pts::Vector{Tuple{Int,Int}})
    println("Finding G of large prime order...")

    while true
        D = random_jacobian_divisor(pts)

        ord = jacobian_order_bsgs(D)

        if ord <= 1
            continue
        end

        ell = largest_prime_factor(ord)

        if ell <= 3
            continue
        end

        h = ord ÷ ell
        h == 0 && continue

        G = jacobian_scalar_mul(h, D)

        if is_identity(G)
            continue
        end

        # verify exact order ell
        if is_identity(jacobian_scalar_mul(ell, G))
            println("  ord(D) = $ord")
            println("  ell    = $ell")
            println("  h      = $h")
            return G, ell
        end
    end
end


# ──────────────────────── Curve utilities ─────────────────────────────────────
eval_f(x::Int) = peval(F_POLY, fp(x))

# All affine rational points (x, y) on C, ordered by x.
# Threaded: each thread scans a contiguous x-range; results are merged in order.
function curve_points()
    nthreads = Threads.nthreads()
    # Pre-allocate per-thread buffers.  Upper bound: 2 points per x.
    chunk_size = cld(p, nthreads)
    buffers = [NTuple{2,Int}[] for _ in 1:nthreads]
    for buf in buffers
        sizehint!(buf, 2 * chunk_size)
    end

    Threads.@threads :static for tid in 1:nthreads
        x_lo = (tid - 1) * chunk_size
        x_hi = min(tid * chunk_size - 1, p - 1)
        buf  = buffers[tid]
        for x in x_lo:x_hi
            y = sqrt_fp(eval_f(x));  y === nothing && continue
            push!(buf, (x, y))
            y != 0 && push!(buf, (x, fp(-y)))
        end
    end

    # Merge in thread order so the result is sorted by x (matching old behaviour).
    total = sum(length(b) for b in buffers)
    pts = NTuple{2,Int}[]
    sizehint!(pts, total)
    for buf in buffers
        append!(pts, buf)
    end
    pts
end

mumford1(x0::Int, y0::Int) = Div2(Int[fp(-x0), 1], Int[fp(y0)])

function mumford2(x1::Int, y1::Int, x2::Int, y2::Int)::Div2
    u  = Int[fp(x1 * x2), fp(-(x1 + x2)), 1]
    sl = fp((y2 - y1) * fpinv(x2 - x1))
    Div2(u, ptrim(Int[fp(y1 - sl * x1), sl]))
end

function mumford_from_pts(P::NTuple{2,Int}, Q::NTuple{2,Int})::Div2
    x1, y1 = P;  x2, y2 = Q
    x1 == x2 && y2 == fp(-y1) && return JacID          # Q = -P
    x1 == x2 && return jac_add(mumford1(x1, y1), mumford1(x2, y2))  # tangent
    mumford2(x1, y1, x2, y2)
end

# ──────────────────────── Smoothness test ─────────────────────────────────────
# For a degree-2 monic Mumford u-poly, find both Fp-roots or return nothing.
function u2_roots(u::Vector{Int})
    length(u) != 3 && return nothing          # must be degree 2 (u[3]=1)
    c0, c1 = u[1], u[2]                       # u(x) = x² + c1·x + c0
    disc   = fp(c1^2 - 4c0)
    sq     = sqrt_fp(disc)
    sq === nothing && return nothing
    inv2   = fpinv(2)
    (fp((-c1 + sq) * inv2), fp((-c1 - sq) * inv2))
end

# ──────────────────────── Key generation ──────────────────────────────────────
# Find a Div2 of order exactly ell.
#
# Since we now know #Jac exactly from jacobian_order_frobenius, the cofactor
# is exact: cofactor = #Jac / ell.  For a random D, G = cofactor·D is either
# the identity (unlucky draw; try again) or has order dividing ell; since ell
# is prime and G ≠ id, G has order exactly ell.  No scan needed.
# ──────────────────────── Linear algebra over GF(ell) ─────────────────────────
# Find a nonzero γ with  γᵀ R ≡ 0 (mod ell),  or return nothing.
#
# Method: augment [I_m | R] (m × m+n), row-reduce the R columns.
# Any row whose R-part is all-zero is a left null vector; read γ from I-part.
function left_kernel(R::Matrix{Int})
    m, n  = size(R)
    aug   = hcat(Matrix{Int}(I, m, m), mod.(R, ell))
    prow  = 1

    for col in m+1:m+n
        # find pivot in current column, at or below pivot row
        piv = findfirst(r -> aug[r, col] != 0, prow:m)
        piv === nothing && continue
        piv += prow - 1

        # swap and normalize pivot row
        aug[[prow, piv], :] = aug[[piv, prow], :]
        s = powermod(aug[prow, col], ell - 2, ell)
        aug[prow, :] = mod.(aug[prow, :] .* s, ell)

        # eliminate this column in all other rows
        for r in 1:m
            r == prow && continue
            f = aug[r, col];  f == 0 && continue
            aug[r, :] = mod.(aug[r, :] .- f .* aug[prow, :], ell)
        end

        prow += 1;  prow > m && break
    end

    # Return the first row whose R-part is all zero (= a left null vector)
    for row in 1:m
        all(aug[row, m+1:end] .== 0) || continue
        γ = aug[row, 1:m]
        any(!=(0), γ) && return γ
    end
    nothing
end

# ────────────────────────── Index calculus ────────────────────────────────────
"""
    index_calculus(G, T; fb_size=650, verbose=true) → k or nothing

Solve k·G = T in the ell-order subgroup of Jac(C/Fp).

`fb_size`: number of rational points to use as factor base.
           Default ≈ p^(1/2) is the smoothness bound used here.

To plug in a different relation-generation mechanism, replace the block
between the RELATION GENERATION markers below.  The contract for each
candidate:
  - compute some Div2 D that equals α·G + β·T in the Jacobian
  - record (α, β) and the factor-base decomposition of D
"""
function index_calculus(G::Div2, T::Div2;
                        fb_size::Int  = 650,
                        verbose::Bool = true)

    # ── Build factor base ─────────────────────────────────────────────────────
    all_pts = curve_points()
    fb      = all_pts[1:min(fb_size, length(all_pts))]
    nF      = length(fb)
    pt2idx  = Dict(pt => i for (i, pt) in enumerate(fb))
    verbose && @printf("Factor base: %d / %d rational points\n", nF, length(all_pts))

    # ── Relation collection ───────────────────────────────────────────────────
    needed = nF + 20
    αvec   = zeros(Int, needed)
    βvec   = zeros(Int, needed)
    Rmat   = zeros(Int, needed, nF)
    nrel   = 0;  tries = 0;  t0 = time()

    while nrel < needed

        # ── RELATION GENERATION (replace this block for custom strategy) ──────
        α = rand(1:ell-1)
        β = rand(0:ell-1)
        D = jac_add(jac_mul(G, α), jac_mul(T, β))
        # ─────────────────────────────────────────────────────────────────────

        tries += 1

        # Smoothness test: u must be degree 2 and split over Fp
        pdeg(D.u) != 2 && continue
        rs = u2_roots(D.u)
        rs === nothing && continue

        # Both roots must correspond to factor-base points
        x1, x2 = rs
        pt1 = (x1, peval(D.v, x1))
        pt2 = (x2, peval(D.v, x2))
        haskey(pt2idx, pt1) && haskey(pt2idx, pt2) || continue

        # Record relation:  α·G + β·T = pt1 + pt2  in Jacobian
        nrel += 1
        αvec[nrel], βvec[nrel] = α, β
        Rmat[nrel, pt2idx[pt1]] += 1
        Rmat[nrel, pt2idx[pt2]] += 1

        if verbose && nrel % max(1, needed ÷ 10) == 0
            @printf("  [%d/%d]  %d tries  hit=%.3f%%  %.1fs\n",
                    nrel, needed, tries, 100.0*nrel/tries, time()-t0)
        end
    end
    verbose && @printf("Collection done: %d rels in %d tries (%.1fs)\n",
                       nrel, tries, time()-t0)

    # ── Left kernel over GF(ell) ──────────────────────────────────────────────
    verbose && println("Left-kernel search over GF($ell)...")
    γ = left_kernel(Rmat[1:nrel, :])
    γ === nothing && error("Kernel not found — collect more relations")

    # k = -(Σ γᵢαᵢ) / (Σ γᵢβᵢ)  mod ell
    # Use Int128 to avoid overflow before taking mod
    Σα = mod(sum(Int128(γ[i]) * αvec[i] for i in 1:nrel), ell)
    Σβ = mod(sum(Int128(γ[i]) * βvec[i] for i in 1:nrel), ell)
    Σβ == 0 && error("β-coefficient = 0 in kernel vector; collect more relations and retry")

    k = mod(-Σα * powermod(Int(Σβ), ell - 2, ell), ell)

    # ── Verify ───────────────────────────────────────────────────────────────
    ok = jac_mul(G, k) == T
    if verbose
        ok ? println("  ✓  k = $k   (k·G == T)") : println("  ✗  k = $k   FAILED")
    end
    ok ? k : nothing
end

# ─────────────────────────────── Sanity checks ────────────────────────────────
function run_sanity_checks(pts)
    println("Running sanity checks...")

    # 1. Arithmetic: commutativity and associativity on small examples
    P = mumford_from_pts(pts[1], pts[2])
    Q = mumford_from_pts(pts[3], pts[4])
    @assert jac_add(P, Q) == jac_add(Q, P)              "Commutativity"
    @assert jac_add(jac_add(P, Q), P) == jac_add(P, jac_add(Q, P)) "Associativity"

    # 2. Identity and negation
    @assert jac_add(P, JacID) == P                       "Identity"
    @assert jac_add(P, jac_neg(P)) == JacID              "Negation"

    # 3. Scalar multiplication consistency
    D3 = jac_mul_raw(P, 3)
    @assert D3 == jac_add(jac_add(P, P), P)             "3·P via add"
    @assert jac_mul_raw(P, 0) == JacID                   "0·P = id"

    println("  All checks passed.")
end

# ───────────────────────────────── Demo ───────────────────────────────────────
function main()
    println("="^62)
    println("  Genus-2 index calculus   y²=x⁵+3x³+2x²+5x+4  /F_$p")
    println("  ell = (auto-computed below)")
    println("="^62, "\n")

    pts = curve_points()
    @printf("Rational affine points on C: %d\n\n", length(pts))

    run_sanity_checks(pts)
    println()

    println("Finding G and computing ell automatically...")
    G, ell_found, ordG = find_ell_generator(pts)
    global ell = ell_found
    @printf("G.u = %s\nG.v = %s\n", G.u, G.v)
    @printf("ord(G) = %d\nell = %d\n\n", ordG, ell)

    # Verify order of G
    @assert jac_isid(jac_mul_raw(G, ell))   "G does not have order ell!"
    @assert !jac_isid(G)                     "G is identity!"
    println("Confirmed: ell·G = identity\n")

    # Key pair
    k = rand(2:ell-1)
    T = jac_mul(G, k)
    @printf("Secret k = %d\nT.u = %s\nT.v = %s\n\n", k, T.u, T.v)

    println("Running index calculus (fb_size=650)...")
    recovered = index_calculus(G, T; fb_size=650, verbose=true)

    println()
    if recovered !== nothing
        @printf("Recovered k = %-8d  true k = %-8d  match = %s\n",
                recovered, k, recovered == k)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
