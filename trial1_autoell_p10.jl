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
using StaticArrays

# ─────────────────────────── Global parameters ────────────────────────────────
# Accept an optional command-line argument: the prime (or near-prime) to use.
# We find the next prime >= the supplied value, mirroring Sage's next_prime().
function _next_prime(n::Integer)::Int
    n < 2 && return 2
    candidate = Int(n % 2 == 0 ? n + 1 : n)
    while !isprime(candidate)
        candidate += 2
    end
    return candidate
end

# p is a type-annotated global (not const) so that main2 can reassign it when
# --min-ell-bits causes a prime search.  The Int annotation preserves the same
# type-specialisation that const would give, keeping fp/fpmul/fpinv fast.
global p::Int = let
    if !isempty(ARGS)
        raw = tryparse(Int128, ARGS[1])
        raw === nothing && error("Command-line argument must be an integer, got: $(ARGS[1])")
        np = _next_prime(raw)
        np != Int(raw) && println("next_prime($raw) = $np  →  using p = $np")
        np
    else
        164147   # default
    end
end
ell = 0  # computed automatically at runtime
# f(x) = x^5 + 3x^3 + 2x^2 + 5x + 4;  F_POLY[i] = coeff of x^(i-1)
#const F_POLY = Int[4, 5, 2, 3, 0, 1] # the OG
const F_POLY = Int[2, 1, 0, 0, 0, 1] # y^2 = x^5 + x + 2

# ─────────────────────────── Fp arithmetic ────────────────────────────────────
@inline fp(x::Integer)    = mod(x, p)
# fpmul: multiplication in F_p safe for any p < 2^62 (uses 128-bit intermediate)
@inline fpmul(a::Integer, b::Integer) = Int(mod(widemul(Int64(a), Int64(b)), p))
# Multiplicative inverse in F_p
@inline function fpinv(a::Integer)
    aa = mod(Int(a), p)
    aa == 0 && throw(DomainError(a, "attempted inversion of zero modulo p"))
    return Int(invmod(aa, p))
end

function pdivrem(a::Vector{Int}, b::Vector{Int})
    # Work on mutable copies, normalize coefficients first, then trim again.
    # Trimming before normalization is not enough because a trailing coefficient
    # can be nonzero as an integer but become 0 mod p.
    a = copy(a)
    b = copy(b)

    @inbounds for i in eachindex(a)
        a[i] = fp(a[i])
    end
    @inbounds for i in eachindex(b)
        b[i] = fp(b[i])
    end

    a = ptrim!(a)
    b = ptrim!(b)

    if pzero(b)
        error("Division by zero polynomial")
    end

    db = pdeg(b)
    lb = b[end]  # now guaranteed reduced and trimmed

    if lb == 0
        error("Invalid divisor: leading coefficient is zero mod $p")
    end

    lc_inv = fpinv(lb)

    # Quotient size: degree(a) - degree(b) + 1, but at least 1
    q = zeros(Int, max(1, length(a) - length(b) + 1))

    while !pzero(a) && pdeg(a) >= db
        da = pdeg(a)
        d  = da - db

        # Leading-term cancellation coefficient
        c = fpmul(a[end], lc_inv)
        q[d + 1] = c

        # Subtract c * x^d * b from a
        @inbounds for i in eachindex(b)
            a[i + d] = fp(a[i + d] - fpmul(c, b[i]))
        end

        # Force the highest coefficient to zero, then physically shrink
        a[end] = 0
        while length(a) > 1 && a[end] == 0
            pop!(a)
        end
    end

    # Trim quotient
    while length(q) > 1 && q[end] == 0
        pop!(q)
    end

    # Ensure remainder is in canonical trimmed form
    return q, ptrim(a)
end




# Square root in Fp via Tonelli-Shanks (works for any odd prime p).
function sqrt_fp(a::Int)
    a = fp(a);  a == 0 && return 0
    # Quick Euler criterion: a^((p-1)/2) must be 1
    powermod(a, (p - 1) >> 1, p) == 1 || return nothing
    if p % 4 == 3
        r = powermod(a, (p + 1) >> 2, p)
        return fpmul(r, r) == a ? r : nothing
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
        i, tmp = 1, fpmul(t, t)
        while tmp != 1; tmp = fpmul(tmp, tmp); i += 1; end
        # Use powermod(c, 2^(M2-i-1), p) to avoid shift overflow
        b = powermod(c, Int128(1) << (M2 - i - 1), p)
        M2 = i
        c = fpmul(b, b)
        t = fpmul(t, c)
        r = fpmul(r, b)
    end
end

# =============================================================================
#  Polynomial ring Fp[x]  —  two layers:
#
#  HOT PATH (stack-allocated, zero heap):
#    Fp3 = SVector{3,Int}  represents degree ≤ 2:  c0 + c1·x + c2·x²
#    Fp2 = SVector{2,Int}  represents degree ≤ 1:  c0 + c1·x
#    All arithmetic on Fp3/Fp2 is fully inlined and allocation-free.
#
#  COLD PATH (heap Vector{Int}, variable degree):
#    Used by pgcd_ext, pdivrem, jac_order_bsgs, mumford2, etc.
#    Untouched from the original implementation.
#
#  Div2 is now an immutable struct holding (u::Fp3, v::Fp2), making it a
#  40-byte stack value.  jac_add on the hot path never touches the heap.
# =============================================================================

const Fp3 = SVector{3,Int}   # degree-≤-2 poly: [c0, c1, c2]
const Fp2 = SVector{2,Int}   # degree-≤-1 poly: [c0, c1]

# Degree of an Fp3 (ignoring trailing zeros)
@inline fp3_deg(u::Fp3) = u[3] != 0 ? 2 : (u[2] != 0 ? 1 : 0)
@inline fp2_deg(v::Fp2) = v[2] != 0 ? 1 : 0

@inline fp3_iszero(u::Fp3) = u[1] == 0 && u[2] == 0 && u[3] == 0
@inline fp2_iszero(v::Fp2) = v[1] == 0 && v[2] == 0

# Evaluate an Fp3/Fp2 at a point
@inline fp3_eval(u::Fp3, x::Int) = fp(u[1] + fpmul(x, fp(u[2] + fpmul(x, u[3]))))
@inline fp2_eval(v::Fp2, x::Int) = fp(v[1] + fpmul(x, v[2]))

# Convert to/from heap Vector{Int} for cold-path interop.
# to_vec trims trailing zeros.
@inline function fp3_to_vec(u::Fp3)::Vector{Int}
    u[3] != 0 && return Int[u[1], u[2], u[3]]
    u[2] != 0 && return Int[u[1], u[2]]
    return Int[u[1]]
end
@inline function fp2_to_vec(v::Fp2)::Vector{Int}
    v[2] != 0 && return Int[v[1], v[2]]
    return Int[v[1]]
end
@inline function vec_to_fp3(a::Vector{Int})::Fp3
    la = length(a)
    Fp3(la >= 1 ? fp(a[1]) : 0,
        la >= 2 ? fp(a[2]) : 0,
        la >= 3 ? fp(a[3]) : 0)
end
@inline function vec_to_fp2(a::Vector{Int})::Fp2
    la = length(a)
    Fp2(la >= 1 ? fp(a[1]) : 0,
        la >= 2 ? fp(a[2]) : 0)
end

# ── Hot-path arithmetic on Fp3/Fp2 ──────────────────────────────────────────
# All functions are @inline and allocation-free.

# Fp3 + Fp3 → Fp3
@inline fp3_add(a::Fp3, b::Fp3) = Fp3(fp(a[1]+b[1]), fp(a[2]+b[2]), fp(a[3]+b[3]))
# Fp3 - Fp3 → Fp3
@inline fp3_sub(a::Fp3, b::Fp3) = Fp3(fp(a[1]-b[1]), fp(a[2]-b[2]), fp(a[3]-b[3]))
# Fp2 + Fp2 → Fp2
@inline fp2_add(a::Fp2, b::Fp2) = Fp2(fp(a[1]+b[1]), fp(a[2]+b[2]))
# Fp2 - Fp2 → Fp2
@inline fp2_sub(a::Fp2, b::Fp2) = Fp2(fp(a[1]-b[1]), fp(a[2]-b[2]))
# -Fp2 → Fp2
@inline fp2_neg(v::Fp2)         = Fp2(fp(-v[1]), fp(-v[2]))
# scalar * Fp3 → Fp3
@inline fp3_scale(a::Fp3, s::Int) = Fp3(fpmul(a[1],s), fpmul(a[2],s), fpmul(a[3],s))
# scalar * Fp2 → Fp2
@inline fp2_scale(v::Fp2, s::Int) = Fp2(fpmul(v[1],s), fpmul(v[2],s))

# Fp2 * Fp2 → Fp3  (degree ≤ 2)
@inline function fp2_mul(a::Fp2, b::Fp2)::Fp3
    Fp3(fpmul(a[1],b[1]),
        fp(fpmul(a[1],b[2]) + fpmul(a[2],b[1])),
        fpmul(a[2],b[2]))
end

# Fp3 mod Fp3-monic-deg2: compute a mod u where u is monic degree 2.
# Reduces degree-2 term: x² ≡ -u[2]·x - u[1]  (since u = x²+u[2]·x+u[1])
# Input a has degree ≤ 2; output has degree ≤ 1 → Fp2.
@inline function fp3_mod_u2(a::Fp3, u::Fp3)::Fp2
    # u is monic degree 2: u[3]=1, u = x²+u[2]x+u[1]
    # a = a[3]x² + a[2]x + a[1]
    # subtract a[3]·u: a[3]·(x²+u[2]x+u[1]) from a
    # result: (a[2] - a[3]*u[2])x + (a[1] - a[3]*u[1])
    c = a[3]
    Fp2(fp(a[1] - fpmul(c, u[1])),
        fp(a[2] - fpmul(c, u[2])))
end

# Fp2 mod Fp3-monic-deg2 → Fp2  (already degree ≤ 1, no-op)
@inline fp2_mod_u2(v::Fp2, ::Fp3)::Fp2 = v

# ── Cantor jac_add: fully inlined, zero allocation ──────────────────────────
#
# For genus-2 Jacobians the generic Cantor composition+reduction has a
# known closed form when gcd(u1,u2)=1 (the overwhelmingly common case).
# We special-case the full generic path inline.
#
# Notation:  u1,u2 are monic degree-2 Fp3;  v1,v2 are degree≤1 Fp2.
# The degenerate path (gcd≠1) falls through to the Vector-based implementation.
#
# Returns a new Div2 from stack-only arithmetic.

# ── Old heap-based poly utilities (cold path only) ───────────────────────────

@inline function ptrim!(a::Vector{Int})
    n = length(a)
    @inbounds while n > 1 && a[n] == 0; n -= 1; end
    n < length(a) && resize!(a, n)
    a
end

@inline function ptrim(a::Vector{Int})
    n = length(a)
    @inbounds while n > 1 && a[n] == 0; n -= 1; end
    n == length(a) ? copy(a) : a[1:n]
end

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
        @inbounds for i in 1:lb;    c[i] = fp(a[i] + b[i]); end
        @inbounds for i in lb+1:la; c[i] = fp(a[i]); end
    else
        @inbounds for i in 1:la;    c[i] = fp(a[i] + b[i]); end
        @inbounds for i in la+1:lb; c[i] = fp(b[i]); end
    end
    ptrim!(c)
end

function psub(a::Vector{Int}, b::Vector{Int})
    la, lb = length(a), length(b)
    c = Vector{Int}(undef, max(la, lb))
    if la >= lb
        @inbounds for i in 1:lb;    c[i] = fp(a[i] - b[i]); end
        @inbounds for i in lb+1:la; c[i] = fp(a[i]); end
    else
        @inbounds for i in 1:la;    c[i] = fp(a[i] - b[i]); end
        @inbounds for i in la+1:lb; c[i] = fp(-b[i]); end
    end
    ptrim!(c)
end

function pmul(a::Vector{Int}, b::Vector{Int})
    la, lb = length(a), length(b)
    c = zeros(Int, la + lb - 1)
    @inbounds for i in 1:la, j in 1:lb
        c[i+j-1] = fp(c[i+j-1] + fpmul(a[i], b[j]))
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
    @inbounds for i in eachindex(a); c[i] = fpmul(a[i], s); end
    ptrim!(c)
end

function pscale!(a::Vector{Int}, s::Int)
    s = fp(s)
    @inbounds for i in eachindex(a); a[i] = fpmul(a[i], s); end
    ptrim!(a)
end

function pneg!(a::Vector{Int})
    @inbounds for i in eachindex(a); a[i] = fp(-a[i]); end
    ptrim!(a)
end

function f_minus_vsq!(dst::Vector{Int}, V::Vector{Int})
    lv = length(V)
    lout = max(6, 2 * lv - 1)
    resize!(dst, lout)
    fill!(dst, 0)
    @inbounds for i in 1:6; dst[i] = fp(dst[i] + F_POLY[i]); end
    @inbounds for i in 1:lv, j in 1:lv
        dst[i+j-1] = fp(dst[i+j-1] - fpmul(V[i], V[j]))
    end
    ptrim!(dst)
end

function peval(poly::Vector{Int}, x::Int)
    x = fp(x); r = 0
    for i in length(poly):-1:1; r = fp(fpmul(r, x) + poly[i]); end
    r
end

pmod(a, b) = pdivrem(a, b)[2]

function pgcd_ext(a0::Vector{Int}, b0::Vector{Int})
    r0 = copy(ptrim(a0))
    r1 = copy(ptrim(b0))
    s0, s1 = Int[1], Int[0]
    t0, t1 = Int[0], Int[1]
    while !pzero(r1)
        q, r2 = pdivrem(r0, r1)
        r0, r1 = r1, r2
        s0, s1 = s1, psub(s0, pmul(q, s1))
        t0, t1 = t1, psub(t0, pmul(q, t1))
    end
    pzero(r0) && throw(ArgumentError("pgcd_ext: gcd collapsed to zero polynomial"))
    sc = fpinv(r0[end])
    pscale(r0, sc), pscale(s0, sc), pscale(t0, sc)
end

# ──────────────────────── Genus-2 Jacobian (Cantor) ───────────────────────────
# Div2 is now a fully stack-allocated value type.
# u::Fp3 = SVector{3,Int}: coefficients of the monic u-poly (degree ≤ 2).
# v::Fp2 = SVector{2,Int}: coefficients of the v-poly (degree ≤ 1).
# Identity: u = [1,0,0] (degree 0), v = [0,0].

struct Div2
    u::Fp3
    v::Fp2
end

Base.:(==)(A::Div2, B::Div2) = (A.u == B.u) && (A.v == B.v)

function Base.hash(D::Div2, h::UInt)
    h = hash(D.u, h)
    h = hash(D.v, h)
    h
end

const JacID = Div2(Fp3(1,0,0), Fp2(0,0))
@inline jac_isid(D::Div2) = D.u[2] == 0 && D.u[3] == 0   # degree 0

# ─────────────────────────── jac_add invariant diagnostics ────────────────────
#  jac_add's hot-path synthetic division of g(x)=f(x)-V_raw(x)² by U(x)=u1·u2
#  (below) only computes the quotient coefficients qq0,qq1,qq2 and assumes the
#  remainder is exactly zero, which is guaranteed by the Cantor identity *only
#  when D1 and D2 are both genuine, valid genus-2 divisors*.  If that ever
#  fails to hold (an edge case slipping past the D==0/qq2==0 degenerate
#  checks, or a caller passing in an already-corrupted Div2), the old code
#  silently returned whatever qq0/qq1 happened to be — a Div2 that looks
#  valid (right degree, right types) but does not actually satisfy the curve
#  relation, and which would then corrupt every subsequent jac_add call built
#  on top of it for the rest of the walk.
#
#  This counter is incremented whenever the (now-checked) remainder is
#  nonzero, so a run can be inspected after the fact for whether silent
#  invariant violations are occurring and, if so, whether their rate climbs
#  over the course of a walk (i.e. it "gets worse" — the signature we're
#  chasing in the round-off/phi-validity investigation).
const JAC_ADD_INVARIANT_VIOLATIONS = Threads.Atomic{Int}(0)

"""
    jac_add_invariant_violations() -> Int

Number of times jac_add's fast Cantor-reduction path detected a nonzero
remainder (Cantor invariant violated) and fell back to the slow,
general-purpose `_jac_add_degenerate` path instead of returning a
potentially-corrupted result. Should be 0 for a healthy run; a nonzero and/or
climbing count points at genuine divisor corruption rather than at the
alpha-dedup gate (see trial3_phase2.jl's phi_attempts counter for the
gate-side half of this comparison).
"""
jac_add_invariant_violations() = JAC_ADD_INVARIANT_VIOLATIONS[]

jac_add_invariant_violations_reset!() = (JAC_ADD_INVARIANT_VIOLATIONS[] = 0; nothing)

# ── Generic (degenerate) Cantor via heap polys — called only when gcd(u1,u2)≠1
function _jac_add_degenerate(D1::Div2, D2::Div2)::Div2
    u1 = fp3_to_vec(D1.u); v1 = fp2_to_vec(D1.v)
    u2 = fp3_to_vec(D2.u); v2 = fp2_to_vec(D2.v)
    d1, e1, e2 = pgcd_ext(u1, u2)
    d, c1v, c2v = pgcd_ext(d1, padd(v1, v2))
    s1v = pmul(c1v, e1); s2v = pmul(c1v, e2)
    U, _  = pdivrem(pmul(u1, u2), pmul(d, d))
    Vn    = padd(padd(pmul(pmul(s1v, u1), v2), pmul(pmul(s2v, u2), v1)),
                 pmul(c2v, padd(pmul(v1, v2), F_POLY)))
    Vd, _ = pdivrem(Vn, d)
    V     = pmod(Vd, U)
    U[end] == 0 && throw(ArgumentError("jac_add degenerate: zero leading coeff"))
    U = pscale(U, fpinv(U[end]))
    _tmp = Vector{Int}(undef, 6)
    while pdeg(U) > 2
        f_minus_vsq!(_tmp, V)
        U2, _ = pdivrem(_tmp, U)
        U2[end] == 0 && throw(ArgumentError("jac_add reduction: zero leading coeff"))
        pscale!(U2, fpinv(U2[end]))
        pneg!(V)
        V = pmod(V, U2)
        U = U2
    end
    Div2(vec_to_fp3(U), vec_to_fp2(V))
end

# ── Hot-path Cantor: generic case gcd(u1,u2)=1, both degree-2, inline.
#
# Explicit Cantor formulas for genus 2 with deg(u1)=deg(u2)=2, gcd=1.
# See Lange "Formulae for Arithmetic on Genus 2 Hyperelliptic Curves" or
# direct derivation from Cantor's algorithm.
#
# u_i = x² + a_i·x + b_i  (monic, stored as Fp3(b,a,1))
# v_i = c_i + d_i·x       (stored as Fp2(c,d))
#
# Step 1 (composition): U = u1·u2, find V mod U.
# We need s,t with s·u1 + t·u2 = 1 (since gcd=1).
# By extended Euclidean on degree-2 polys, s and t are degree ≤ 1.
#
# For monic degree-2 coprime u1,u2:
#   gcd_ext gives s,t degree ≤ 1 with s·u1 + t·u2 = 1.
#   V = (s·u1·v2 + t·u2·v1) mod U    (degree ≤ 3 before reduction, ≤ 3 after mod)
#
# Step 2 (reduction): U has degree 4; reduce once to get degree 2.
#   U' = (f - V²) / U   (degree 5 - 4 = 1... wait, need one more step)
# Actually for genus 2 composition of two degree-2 elements gives degree-4 U,
# which reduces in exactly two steps to degree 2.
# We implement this directly with fixed-size arithmetic.
#
# For the s,t computation with degree-2 coprime u1,u2:
#   Write u1 = x²+a1·x+b1, u2 = x²+a2·x+b2.
#   u1 - u2 = (a1-a2)·x + (b1-b2).
#   If a1≠a2: gcd(u1,u2) divides u1-u2 which is degree 1, so gcd=1 iff a1≠a2 or b1≠b2.
#   s = 1/(a1-a2) (scalar), but we need the full extended gcd for the general case.
#   We fall back to the heap version for the extended gcd since it's degree ≤ 2,
#   and the vectors are tiny (length 3). The key win is that AFTER the gcd,
#   all arithmetic stays in Fp3/Fp2 without further heap allocation.

function jac_add(D1::Div2, D2::Div2)::Div2
    jac_isid(D1) && return D2
    jac_isid(D2) && return D1

    u1 = D1.u; v1 = D1.v
    u2 = D2.u; v2 = D2.v

    # Degree check: if either u is degree < 2, use heap path.
    (u1[3] == 0 || u2[3] == 0) && return _jac_add_degenerate(D1, D2)

    # ── Inline stack-allocated extended GCD of two monic degree-2 polys ──────
    #
    # u1 = x² + a1·x + b1  (u1 = Fp3(b1, a1, 1))
    # u2 = x² + a2·x + b2  (u2 = Fp3(b2, a2, 1))
    #
    # We need e1, e2 (degree ≤ 1) with e1·u1 + e2·u2 = 1  (when gcd=1).
    #
    # u1 - u2 = δa·x + δb  where δa = a1-a2, δb = b1-b2.
    #
    # Case A: δa ≠ 0  (generic — the common case).
    #   Let L = δa·x + δb  (degree 1).
    #   gcd(u1, u2) = gcd(u1, L).
    #   We need s (degree ≤ 1) with s·L ≡ 1 (mod u1):
    #     (s0 + s1·x)(δb + δa·x) ≡ 1 (mod x²+a1·x+b1)
    #   Expand: δb·s0 + (δa·s0+δb·s1)·x + δa·s1·x²
    #   Reduce x² ≡ -a1·x - b1:
    #     const: δb·s0 - δa·s1·b1
    #     x:     δa·s0 + δb·s1 - δa·s1·a1
    #   Set = [1, 0]:
    #     δb·s0 - δa·b1·s1 = 1
    #     δa·s0 + (δb - δa·a1)·s1 = 0
    #   From the second: s0 = -(δb - δa·a1)·s1 / δa = (δa·a1 - δb)·s1 / δa
    #   Let γ = δa·a1 - δb  (= a2·δa since δa=a1-a2, δb=b1-b2:
    #     γ = δa·a1 - δb = (a1-a2)·a1 - (b1-b2) = a1²-a1·a2-b1+b2)
    #   s0 = γ·s1/δa.  Sub into first:
    #     δb·γ·s1/δa - δa·b1·s1 = 1
    #     s1·(δb·γ - δa²·b1)/δa = 1
    #     s1 = δa / (δb·γ - δa²·b1)
    #   Denominator: D = δb·γ - δa²·b1
    #               = (b1-b2)(a1²-a1·a2-b1+b2) - (a1-a2)²·b1
    #   If D = 0, gcd(u1,u2) > 1 → degenerate path.
    #   Otherwise:
    #     s1 = δa · inv(D)
    #     s0 = γ · s1 / δa = γ · inv(D)    (γ/δa · δa·inv(D) = γ·inv(D))
    #   So  s = inv(D)·(γ + δa·x)  is the Bezout coeff for L on the u1 side.
    #   Now e1·u1 + e2·u2 = 1 with e2 = s (works mod u2 as well by symmetry):
    #     Actually: s·L = 1 mod u1, and L = u1 - u2, so s·(u1-u2) = 1 mod u1
    #     → -s·u2 ≡ 1 mod u1  → e2 = -s (as a polynomial Bezout coeff for u1+u2=1 form).
    #     More carefully: e1·u1 + e2·u2 = 1
    #     We have s·L = s·(u1-u2) = s·u1 - s·u2 ≡ 1 mod u1 (means s·u1 - s·u2 = 1 + k·u1 for some k)
    #     Rearranging: (s-k)·u1 + (-s)·u2 = 1  → e1 = s-k (degree doesn't matter for Cantor),
    #     e2 = -s.  For the Cantor formula we only need e1 mod u1 and e2 mod u2:
    #     e2 mod u2 = (-s) mod u2.  Since deg(s)=1 < deg(u2)=2, e2 = -s directly.
    #     e1: we need e1 mod u1.  s·L = 1 mod u1 means s·u1 - s·u2 - 1 = 0 mod u1
    #     → s·u1 ≡ 1 + s·u2 mod u1 → not helpful.  But for Cantor we compute
    #     V_num = e1·u1·v2 + e2·u2·v1 = (e1·u1)·v2 + (e2·u2)·v1.
    #     e1·u1 mod U = e1·u1 mod (u1·u2): using e1·u1 + e2·u2 = 1 we get
    #     e1·u1 = 1 - e2·u2, so e1·u1·v2 = v2 - e2·u2·v2, and
    #     V_num = v2 - e2·u2·v2 + e2·u2·v1 = v2 + e2·u2·(v1-v2).
    #     This is the key identity that avoids needing e1 explicitly!
    #
    # Case B: δa = 0, δb ≠ 0  (u1 and u2 share leading coefficient, differ in const).
    #   L = δb (nonzero scalar). gcd(u1, u2) = gcd(u1, δb) = 1.
    #   s = inv(δb) (scalar), e2 = -inv(δb), and same V_num identity applies.
    #   In this sub-case: γ = δa·a1 - δb = -δb, D = δb·(-δb) - 0 = -δb².
    #   inv(D) = inv(-δb²) = -inv(δb)².  s1 = δa·inv(D) = 0.  s0 = γ·inv(D) = -δb·(-inv(δb²)) = inv(δb). ✓
    #   So Case B falls out of the same formula with δa=0: s = (γ·inv(D), 0·inv(D)) = (inv(δb), 0). ✓
    #
    # Summary of unified formula (no branches beyond D=0 check):
    #   δa = a1 - a2,  δb = b1 - b2
    #   γ  = δa·a1 - δb
    #   D  = δb·γ - δa²·b1      (if 0: degenerate)
    #   invD = fpinv(D)
    #   e2  = Fp2(-γ·invD, -δa·invD)   (= -s, degree ≤ 1)
    #   V_num (mod U) = v2 + e2·u2·(v1-v2) — computed below without storing e1.

    a1 = u1[2]; b1 = u1[1]
    a2 = u2[2]; b2 = u2[1]
    δa = fp(a1 - a2)
    δb = fp(b1 - b2)
    γ  = fp(fpmul(δa, a1) - δb)
    D  = fp(fpmul(δb, γ) - fpmul(fpmul(δa, δa), b1))

    if D == 0
        return _jac_add_degenerate(D1, D2)
    end

    invD = fpinv(D)
    # e2 = -s = Fp2(-γ·invD, -δa·invD)
    e2 = Fp2(fp(-fpmul(γ, invD)), fp(-fpmul(δa, invD)))

    # ── Compute V_num = v2 + e2·u2·(v1-v2) mod U  (degree ≤ 3 after reduction) ──
    #
    # Identity: e1·u1 + e2·u2 = 1  →  e1·u1·v2 + e2·u2·v1
    #         = v2·(1 - e2·u2) + e2·u2·v1 = v2 + e2·u2·(v1-v2).
    # This avoids computing e1 entirely and saves ~8 multiplications.
    #
    # dv = v1 - v2  (Fp2, degree ≤ 1)
    # e2·u2: Fp2·Fp3 → degree ≤ 3  (4 scalar coefficients)
    # e2·u2·dv: degree ≤ 4  (5 coefficients)
    # V_num = v2 + e2·u2·dv: add v2 into the degree-0 and degree-1 terms.
    # Then reduce mod U = u1·u2 (degree 4, monic) by subtracting the degree-4 term.

    dv0 = fp(v1[1] - v2[1])
    dv1 = fp(v1[2] - v2[2])

    # e2·u2: Fp2(e2[1],e2[2]) * Fp3(b2,a2,1) → 4 coeffs
    e2u2_0 = fpmul(e2[1],u2[1])
    e2u2_1 = fp(fpmul(e2[1],u2[2]) + fpmul(e2[2],u2[1]))
    e2u2_2 = fp(fpmul(e2[1],u2[3]) + fpmul(e2[2],u2[2]))
    e2u2_3 = fpmul(e2[2],u2[3])

    # (e2·u2)·dv: degree ≤ 4, then add v2 into coeffs 0 and 1.
    vn0 = fp(v2[1] + fpmul(e2u2_0,dv0))
    vn1 = fp(v2[2] + fpmul(e2u2_0,dv1) + fpmul(e2u2_1,dv0))
    vn2 = fp(        fpmul(e2u2_1,dv1)  + fpmul(e2u2_2,dv0))
    vn3 = fp(        fpmul(e2u2_2,dv1)  + fpmul(e2u2_3,dv0))
    vn4 = fp(        fpmul(e2u2_3,dv1))

    # U = u1·u2, degree 4, monic.
    ub0 = fpmul(u1[1],u2[1])
    ub1 = fp(fpmul(u1[1],u2[2]) + fpmul(u1[2],u2[1]))
    ub2 = fp(u1[1] + fpmul(u1[2],u2[2]) + u2[1])
    ub3 = fp(u1[2] + u2[2])
    # ub4 = 1 (monic)

    # Reduce Vn (degree ≤ 4) mod U by eliminating the degree-4 term.
    c4 = vn4
    r0 = fp(vn0 - fpmul(c4,ub0))
    r1 = fp(vn1 - fpmul(c4,ub1))
    r2 = fp(vn2 - fpmul(c4,ub2))
    r3 = fp(vn3 - fpmul(c4,ub3))
    # V_raw = r3·x³ + r2·x² + r1·x + r0  (degree ≤ 3)

    # ── Cantor reduction: deg(U)=4 → deg(U1)=2 ─────────────────────────────
    # U1 = (f - V_raw²) / U  where f = curve polynomial (degree 5).
    # deg(V_raw) ≤ 3 → deg(V_raw²) ≤ 6; deg(f-V_raw²) ≤ 6; quotient degree ≤ 2. ✓
    # V1 = -(V_raw mod U1).

    # V_raw² coefficients (degree ≤ 6 from V of degree 3):
    vsq0 = fpmul(r0,r0)
    vsq1 = fp(2*fpmul(r0,r1))
    vsq2 = fp(2*fpmul(r0,r2) + fpmul(r1,r1))
    vsq3 = fp(2*fpmul(r0,r3) + 2*fpmul(r1,r2))
    vsq4 = fp(2*fpmul(r1,r3) + fpmul(r2,r2))
    vsq5 = fp(2*fpmul(r2,r3))
    vsq6 = fpmul(r3,r3)

    # f - V²
    g0 = fp(F_POLY[1] - vsq0)
    g1 = fp(F_POLY[2] - vsq1)
    g2 = fp(F_POLY[3] - vsq2)
    g3 = fp(F_POLY[4] - vsq3)
    g4 = fp(           - vsq4)   # F_POLY[5]=0
    g5 = fp(1          - vsq5)   # F_POLY[6]=1 (leading x⁵ coeff)
    g6 = fp(           - vsq6)   # degree-6 term (from V²)

    # Synthetic division of g (degree ≤ 6) by U (degree 4, monic).
    qq2 = g6
    rr5 = fp(g5 - fpmul(qq2,ub3))
    rr4 = fp(g4 - fpmul(qq2,ub2))
    rr3 = fp(g3 - fpmul(qq2,ub1))
    rr2 = fp(g2 - fpmul(qq2,ub0))

    qq1 = rr5
    rr4b = fp(rr4 - fpmul(qq1,ub3))
    rr3b = fp(rr3 - fpmul(qq1,ub2))
    rr2b = fp(rr2 - fpmul(qq1,ub1))
    rr1  = fp(g1  - fpmul(qq1,ub0))

    qq0 = rr4b

    # ── Invariant check: the remainder of g(x) ÷ U(x) must be exactly zero.
    #
    #  Previously this was assumed ("Remainder rr3c..rr0 not needed — zero
    #  when Cantor invariant holds") and never actually computed. That is a
    #  true mathematical identity for genuine curve divisors, but it silently
    #  trusted every input — including a D1/D2 that had *already* drifted off
    #  the curve due to some earlier, unrelated corruption. This finishes the
    #  division and checks the remainder explicitly; a nonzero remainder means
    #  D1/D2 did not actually satisfy the Cantor invariant, and the fast-path
    #  qq0/qq1/qq2 above cannot be trusted. Route to the general (heap) path
    #  instead of returning a bogus-but-valid-looking Div2 that would then
    #  poison every jac_add call downstream for the rest of the walk.
    rem3 = fp(rr3b - fpmul(qq0,ub3))
    rem2 = fp(rr2b - fpmul(qq0,ub2))
    rem1 = fp(rr1  - fpmul(qq0,ub1))
    rem0 = fp(g0   - fpmul(qq0,ub0))
    if rem3 != 0 || rem2 != 0 || rem1 != 0 || rem0 != 0
        Threads.atomic_add!(JAC_ADD_INVARIANT_VIOLATIONS, 1)
        return _jac_add_degenerate(D1, D2)
    end

    # U1 = quotient [qq0, qq1, qq2], make monic:
    if qq2 == 0
        return _jac_add_degenerate(D1, D2)
    end
    inv_u1lc = fpinv(qq2)
    U1_0 = fpmul(qq0, inv_u1lc)
    U1_1 = fpmul(qq1, inv_u1lc)
    U1 = Fp3(U1_0, U1_1, 1)

    # V1 = -V_raw mod U1.
    # Reduce mod U1 (monic degree 2):
    s2 = fp(r2 - fpmul(r3,U1_1))
    s1_ = fp(r1 - fpmul(r3,U1_0))
    # Now degree ≤ 2: reduce x²:
    t1 = fp(s1_ - fpmul(s2,U1_1))
    t0 = fp(r0  - fpmul(s2,U1_0))
    # V1 = -(V_raw mod U1) = -t0 - t1·x
    V1 = Fp2(fp(-t0), fp(-t1))

    return Div2(U1, V1)
end

@inline function jac_neg(D::Div2)::Div2
    jac_isid(D) && return D
    u = D.u; v = D.v
    # -v mod u: v has degree ≤ 1, u has degree 2.
    # -v is just fp2_neg(v) since deg(-v) < deg(u) always.
    Div2(u, fp2_neg(v))
end

jac_sub(D1::Div2, D2::Div2) = jac_add(D1, jac_neg(D2))

function jac_mul_raw(D::Div2, n::Integer)::Div2
    n = Int(n)
    n == 0 && return JacID
    R = JacID
    Q = D
    while n > 0
        isodd(n) && (R = jac_add(R, Q))
        n > 1    && (Q = jac_add(Q, Q))
        n >>= 1
    end
    return R
end

@inline function jac_mul(D::Div2, n::Integer, ell::Integer)
    jac_mul_raw(D, mod(n, ell))
end

# ──────────────────────── Order / subgroup selection ─────────────────────────
# Find the exact order of a Jacobian element by BSGS, using the Hasse-Weil bound
# (#Jac ≲ (sqrt(p)+1)^4) as a safe search radius.  This is enough here because
# p is still modest, so a table of O(p) Jacobian elements is practical.
function jac_order_bsgs(D::Div2; verbose::Bool=false)::Int
    # Safe upper bound for the group order.
    # (isqrt(p)+1)^4 overflows Int64 for p > 2^15; use Int128.
    B = Int(min(Int128(isqrt(p) + 1)^4, typemax(Int)))
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
        N = Int(min(Int128(isqrt(p) + 1)^4, typemax(Int)))
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
        u0 = UInt64(X.u[1])
        u1 = UInt64(X.u[2])
        v0 = UInt64(X.v[1])
        v1 = UInt64(X.v[2])

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
            bg   = fpmul(b, g_mod)
            b2g  = fpmul(b, bg)
            i1   = b
            i2_c = fp(2 * b)

            for a in 0:p-1
                r1 = a
                r2 = fp(fpmul(a, a) + b2g)
                i2 = fpmul(a, i2_c)
                r3 = fp(fpmul(r2, r1) + fpmul(g_mod, fpmul(i2, i1)))
                i3 = fp(fpmul(r2, i1) + fpmul(i2, r1))
                r5 = fp(fpmul(r3, r2) + fpmul(g_mod, fpmul(i3, i2)))
                i5 = fp(fpmul(r3, i2) + fpmul(i3, r2))
                fu = fp(r5 + 3*r3 + 2*r2 + 5*r1 + 4)
                fv = fp(i5 + 3*i3 + 2*i2 + 5*i1)

                if fu == 0 && fv == 0
                    local_n2 += 2
                    continue
                end
                norm_f = fp(fpmul(fu, fu) - fpmul(g_mod, fpmul(fv, fv)))
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
    # Use Int128 arithmetic — s1 ~ O(p^{1/2}), p^2 overflows Int64 for p > 2^31
    s1_128 = Int128(s1)
    p_128  = Int128(p)
    s2 = Int((s1_128^2 - (Int128(n2) - (p_128^2 + 1))) ÷ 2)

    return Int(1 - s1_128 + s2 - p_128 * s1_128 + p_128^2)
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

# Collect only the first `cap` affine rational points on C.
# This is the only path needed for bootstrap / factor-base construction.
function factor_base_points(cap::Int)
    cap <= 0 && return NTuple{2,Int}[]
    fb = NTuple{2,Int}[]
    sizehint!(fb, cap)

    for x in 0:p-1
        y = sqrt_fp(eval_f(x));  y === nothing && continue
        push!(fb, (x, y))
        length(fb) >= cap && return fb
        y != 0 && push!(fb, (x, fp(-y)))
        length(fb) >= cap && return fb
    end

    fb
end

# All affine rational points (x, y) on C, ordered by x.
# Threaded: each thread scans a contiguous x-range; results are merged in order.
# NOTE: This materializes the full curve and is kept only for debugging.
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

# Lightweight alternative to curve_points() that stops after collecting n points.
# Used for generator search (which only needs a handful of random points) and
# avoids storing the full O(p) array (~1.4 GB at p=21M).
function sample_curve_points(n::Int = 100)::Vector{NTuple{2,Int}}
    pts = NTuple{2,Int}[]
    sizehint!(pts, n)
    for x in 0:p-1
        y = sqrt_fp(eval_f(x))
        y === nothing && continue
        push!(pts, (x, y))
        length(pts) >= n && break
    end
    pts
end

mumford1(x0::Int, y0::Int) = Div2(Fp3(fp(-x0), 1, 0), Fp2(fp(y0), 0))

function mumford2(x1::Int, y1::Int, x2::Int, y2::Int)::Div2
    x1 == x2 && throw(ArgumentError(
        "mumford2: x1 == x2 ($x1); use mumford_from_pts for the tangent/negation cases"))
    u  = Int[fpmul(x1, x2), fp(-(x1 + x2)), 1]
    sl = fpmul(fp(y2 - y1), fpinv(x2 - x1))
    Div2(vec_to_fp3(u), vec_to_fp2(ptrim(Int[fp(y1 - fpmul(sl, x1)), sl])))
end

function mumford_from_pts(P::NTuple{2,Int}, Q::NTuple{2,Int})::Div2
    x1, y1 = P;  x2, y2 = Q
    x1 == x2 && y2 == fp(-y1) && return JacID          # Q = -P
    x1 == x2 && return jac_add(mumford1(x1, y1), mumford1(x2, y2))  # tangent
    mumford2(x1, y1, x2, y2)
end

# ──────────────────────── Smoothness test ─────────────────────────────────────
# For a degree-2 monic Mumford u-poly, find both Fp-roots or return nothing.
function u2_roots(u::Fp3)
    fp3_deg(u) != 2 && return nothing          # must be degree 2 (u[3]=1)
    c0, c1 = u[1], u[2]                       # u(x) = x² + c1·x + c0
    disc   = fp(fpmul(c1, c1) - 4*c0)
    sq     = sqrt_fp(disc)
    sq === nothing && return nothing
    inv2   = fpinv(2)
    (fpmul(fp(-c1 + sq), inv2), fpmul(fp(-c1 - sq), inv2))
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
    m, n = size(R)
    aug  = hcat(Matrix{Int}(I, m, m), mod.(R, ell))
    prow = 1
    lastcol = m + n

    for col in m+1:lastcol
        # find pivot in current column, at or below pivot row
        piv = 0
        @inbounds for r in prow:m
            if aug[r, col] != 0
                piv = r
                break
            end
        end
        piv == 0 && continue

        # swap and normalize pivot row
        if piv != prow
            @inbounds for c in 1:lastcol
                aug[prow, c], aug[piv, c] = aug[piv, c], aug[prow, c]
            end
        end
        s = powermod(aug[prow, col], ell - 2, ell)
        @inbounds for c in 1:lastcol
            aug[prow, c] = mod(Int128(aug[prow, c]) * s, ell)
        end

        # eliminate this column in all other rows
        @inbounds for r in 1:m
            r == prow && continue
            f = aug[r, col]
            f == 0 && continue
            for c in 1:lastcol
                aug[r, c] = mod(Int128(aug[r, c]) - Int128(f) * aug[prow, c], ell)
            end
        end

        prow += 1
        prow > m && break
    end

    # Return the first row whose R-part is all zero (= a left null vector)
    @inbounds for row in 1:m
        all_zero = true
        for c in m+1:lastcol
            if aug[row, c] != 0
                all_zero = false
                break
            end
        end
        all_zero || continue

        γ = Vector{Int}(undef, m)
        for c in 1:m
            γ[c] = aug[row, c]
        end
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
    fb      = factor_base_points(fb_size)
    nF      = length(fb)
    pt2idx  = Dict(pt => i for (i, pt) in enumerate(fb))
    verbose && @printf("Factor base: %d rational points (cap=%d)\n", nF, fb_size)

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
        D = jac_add(jac_mul(G, α, ell), jac_mul(T, β, ell))
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

    k = mod(fpmul(Int(-Σα), powermod(Int(Σβ), ell - 2, ell)), ell)

    # ── Verify ───────────────────────────────────────────────────────────────
    ok = jac_mul(G, k, ell) == T
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

    pts = factor_base_points(10_000)
    @printf("Bootstrap/sample affine points on C: %d (capped)\n\n", length(pts))
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
    T = jac_mul(G, k, ell)
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
