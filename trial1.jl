#!/usr/bin/env julia
# =============================================================================
#  genus2_dlp.jl  —  Basic index calculus (Gaudry-Harley) for genus-2 Jacobian
#
#  Curve:   C : y² = x⁵ + 3x³ + 2x² + 5x + 4   over  F_p,   p = 16411
#  Target:  cyclic subgroup  ⟨G⟩ ⊆ Jac(C/Fp)  of prime order  ell = 25373
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

using LinearAlgebra, Printf

# ─────────────────────────── Global parameters ────────────────────────────────
const p      = 16411
const ell    = 25373
# f(x) = x^5 + 3x^3 + 2x^2 + 5x + 4;  F_POLY[i] = coeff of x^(i-1)
const F_POLY = Int[4, 5, 2, 3, 0, 1]

# ─────────────────────────── Fp arithmetic ────────────────────────────────────
@inline fp(x::Integer)    = mod(x, p)
@inline fpinv(x::Integer) = powermod(fp(x), p - 2, p)

# Square root in Fp; valid since p = 16411 ≡ 3 (mod 4)
function sqrt_fp(a::Int)
    a = fp(a);  a == 0 && return 0
    r = powermod(a, (p + 1) >> 2, p)
    fp(r * r) == a ? r : nothing
end

# ─────────────────────── Polynomial ring Fp[x] ────────────────────────────────
# Representation: Vector{Int} with poly[i] = coeff of x^(i-1); always trimmed.

ptrim(a::Vector{Int}) = (n = length(a); while n > 1 && a[n] == 0; n -= 1; end; a[1:n])
pdeg(a::Vector{Int})  = length(ptrim(a)) - 1
pzero(a::Vector{Int}) = (length(a) == 1 && a[1] == 0)

function padd(a::Vector{Int}, b::Vector{Int})
    c = zeros(Int, max(length(a), length(b)))
    for i in eachindex(a); c[i] = fp(a[i]); end
    for i in eachindex(b); c[i] = fp(c[i] + b[i]); end
    ptrim(c)
end

function psub(a::Vector{Int}, b::Vector{Int})
    c = zeros(Int, max(length(a), length(b)))
    for i in eachindex(a); c[i] = fp(a[i]); end
    for i in eachindex(b); c[i] = fp(c[i] - b[i]); end
    ptrim(c)
end

function pmul(a::Vector{Int}, b::Vector{Int})
    c = zeros(Int, length(a) + length(b) - 1)
    @inbounds for i in eachindex(a), j in eachindex(b)
        c[i+j-1] = fp(c[i+j-1] + a[i] * b[j])
    end
    ptrim(c)
end

pneg(a::Vector{Int})           = ptrim(fp.(-a))
pscale(a::Vector{Int}, s::Int) = ptrim(fp.(a .* fp(s)))

function peval(poly::Vector{Int}, x::Int)
    x = fp(x); r = 0
    for i in length(poly):-1:1; r = fp(r * x + poly[i]); end
    r
end

function pdivrem(a::Vector{Int}, b::Vector{Int})
    a  = copy(ptrim(a));  b = ptrim(b)
    lc = fpinv(b[end]);   db = pdeg(b)
    q  = zeros(Int, max(1, length(a) - length(b) + 1))
    while !pzero(a) && pdeg(a) >= db
        d = pdeg(a) - db;  c = fp(a[end] * lc)
        q[d+1] = c
        for i in eachindex(b); a[i+d] = fp(a[i+d] - c * b[i]); end
        a = ptrim(a)
    end
    ptrim(q), a
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
    while pdeg(U) > 2
        U2, _ = pdivrem(psub(F_POLY, pmul(V, V)), U)   # exact: U | V²-f
        U2    = pscale(U2, fpinv(U2[end]))
        V     = pmod(pneg(V), U2)
        U     = U2
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

# ──────────────────────── Curve utilities ─────────────────────────────────────
eval_f(x::Int) = peval(F_POLY, fp(x))

# All affine rational points (x, y) on C, ordered by x
function curve_points()
    pts = NTuple{2,Int}[]
    for x in 0:p-1
        y = sqrt_fp(eval_f(x));  y === nothing && continue
        push!(pts, (x, y))
        y != 0 && push!(pts, (x, fp(-y)))
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
# Find a Div2 of order exactly ell by scanning cofactors in the Hasse-Weil range.
#
# Hasse-Weil for g=2:  #Jac ∈ [(√p-1)^4, (√p+1)^4]
# cofactor = #Jac / ell ∈ [(√p-1)^4/ell, (√p+1)^4/ell]  (range ≈ 1400 values)
#
# For any random D, ell*(c*D) = 0 iff cofactor | c (since order(D) | #Jac = ell*cofactor).
# We scan c values; the unique c ≈ #Jac/ell in range will satisfy this and give
# G = c*D as a non-identity element of order ell.
function find_ell_generator(pts::Vector{NTuple{2,Int}})
    sqp = isqrt(p)
    lo  = max(1, (sqp - 2)^4 ÷ ell - 10)
    hi  =         (sqp + 2)^4 ÷ ell + 10
    @printf("  Cofactor scan range: [%d, %d]  (%d candidates)\n", lo, hi, hi - lo + 1)

    n = length(pts)
    for attempt in 1:300
        D = mumford_from_pts(pts[rand(1:n)], pts[rand(1:n)])
        jac_isid(D) && continue
        for c in lo:hi
            G = jac_mul_raw(D, c)        # must use raw mul; c < ell here
            jac_isid(G) && continue
            jac_isid(jac_mul_raw(G, ell)) && return G
        end
    end
    error("find_ell_generator failed — verify ell | #Jac for this curve/p")
end

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
           Default ≈ p^(2/3) is the asymptotically optimal choice.

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
    println("  ell = $ell")
    println("="^62, "\n")

    pts = curve_points()
    @printf("Rational affine points on C: %d\n\n", length(pts))

    run_sanity_checks(pts)
    println()

    println("Finding G of order ell (cofactor scan)...")
    G = find_ell_generator(pts)
    @printf("G.u = %s\nG.v = %s\n\n", G.u, G.v)

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
