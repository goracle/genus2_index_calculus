# =============================================================================
#  trial3_phi_symbolic.jl  --  Symbolic (last-anchor-free) phi construction.
#
#  COMPANION TO: trial3_phi_general.jl (build_phi_general! / phi_residual_general!)
#
#  WHAT THIS IS
#  ------------
#  trial3_phi_general.jl solves, for K concrete anchor points, the (K+2)x(K+2)
#  linear system for phi's coefficients, then divides N(x) = E(x)^2 - f(x)Y(x)^2
#  by the known factors (each anchor's (x-px_i), and u(x)) to get the residual
#  pair (u_RS, v_RS) -- all over F_p, all concrete numbers.
#
#  This module does the SAME construction, for general K, but with:
#     anchors 1..K-1  : fixed, concrete F_p points (px_i, py_i), as usual
#     anchor  K       : SYMBOLIC. Its x-coordinate is an indeterminate t,
#                       and its y-coordinate w is tied to the curve equation
#                       w^2 = f(t) -- i.e. we work in the coordinate ring
#                       F_p(t)[w]/(w^2 - f(t)), and every element normalizes
#                       to a(t) + b(t)*w with a,b in F_p(t). Any power of w
#                       >= 2 that arises gets reduced immediately via
#                       w^2 = f(t) (per Claire's instruction). We never take
#                       w = sqrt(f(t)) as a *rational* function of t -- the
#                       symbolic anchor genuinely lives in the degree-2
#                       extension, exactly like any other affine point on
#                       the curve.
#
#  The output is u_RS(x; t) and v_RS(x; t): the coefficients of the residual
#  Mumford divisor, each as a genuine element of Ft2 = F_p(t)[w]/(w^2-f(t))
#  -- i.e. each coefficient is a pair (a(t), b(t)) with a,b in F_p(t), NOT
#  a plain RFun -- see WHY THE OUTPUT DOES NOT COLLAPSE TO F_p(t) below.
#
#  WHY THE OUTPUT DOES NOT COLLAPSE TO F_p(t): Ft2 all the way through
#  ----------------------------------------------------------------------
#  An earlier version of this module asserted that N(x) = E(x)^2 - f(x)*Y(x)^2
#  must have b(t) == 0 in every coefficient, on the theory that
#  N(x) = phi(x,y)*phi(x,-y) is invariant under the hyperelliptic involution
#  y -> -y, and that this involution acts on the symbolic anchor's
#  y-coordinate as w -> -w. That assertion was WRONG and fired on every
#  input; the fix (per Claire, 2026-07-05) was to drop it and carry
#  u_RS, v_RS as genuine Ft2 objects.
#
#  The error was conflating two different involutions:
#
#    (1) w -> -w, i.e. sigma: F_p(t)[w]/(w^2-f(t)) -> itself, fixing F_p(t).
#        This is the Galois/Frobenius-type automorphism of the FIELD the
#        symbolic anchor's y-coordinate lives in -- it changes WHICH curve
#        point (t,w) vs (t,-w) got anchored, i.e. moves to a different,
#        generically unrelated divisor with its own (E,Y). Verified
#        numerically (p=10007, K=1): applying sigma to every input of the
#        linear system sends each phi-coefficient's (a,b) -> (a,-b) exactly
#        (real Galois conjugation, working as designed) -- but N(x) formed
#        from the sigma-twisted (E,Y) is NOT the sigma-image of the
#        original N(x): the a-parts of N(x) do agree either way (that part
#        of the identity is fine), but the b-parts are different nonzero
#        elements of F_p(t) in each case, not related to each other by
#        negation or anything else. So sigma-invariance of N(x) is simply
#        false, and asserting b(t)==0 from it was asserting a false thing.
#
#    (2) y -> -y in the DEFINITION N(x) := phi(x,y)*phi(x,-y). Here y is
#        the free curve-coordinate variable that Y(x)*y multiplies against
#        -- NOT the anchor's w. This is the involution that actually makes
#        N(x) = E(x)^2 - f(x)*Y(x)^2 a polynomial in x alone, and it holds
#        unconditionally by construction (E(x)^2 - f(x)Y(x)^2 is manifestly
#        the "y -> -y norm" regardless of what E, Y are) -- no assertion
#        needed for this part; it was never in question.
#
#  What (1) and (2) do NOT combine to give is: "N(x)'s coefficients, as
#  elements of F_p(t)[w]/(w^2-f(t)) built from an anchor at (t,w), are
#  themselves fixed by w -> -w." They aren't, because E(x), Y(x) depend on
#  w only through which point was anchored (via (1)), and N(x) doesn't
#  undo that dependence -- it only guarantees polynomiality in x (via (2)),
#  which is a property of the OTHER variable. A symbolic anchor (t,w) is a
#  point of the curve over F_p(t), not over F_p(t) itself (w satisfies a
#  degree-2 relation over F_p(t) that is irreducible, deg f = 5 odd), so
#  there is no general reason for objects built from it -- u_RS, v_RS
#  included -- to descend to F_p(t). They are honest Ft2 elements.
#
#  The concrete-evaluation entry point (symbolic_residual_concrete, see
#  USAGE below) is where a REAL branch gets chosen: plugging in a specific
#  curve point (t0, y0) with y0^2 = f(t0) and combining a(t0) + b(t0)*y0
#  lands back in plain F_p automatically (real + real*real = real), and
#  matches trial3_phi_general.jl's build_phi_general!/phi_residual_general!
#  run directly with (t0,y0) as the K-th concrete anchor -- this has been
#  checked to agree numerically for K=1,2,3. That's the only place a
#  "collapse" ever legitimately happens; it does not happen at the Ft2
#  level, and this module no longer claims that it does.
#
#  SCOPE / LIMITATIONS
#  --------------------
#    - Anchors are assumed pairwise DISTINCT, m=1 each (no tangency). The
#      concrete build_phi_general! supports m=2 tangency via a Taylor
#      branch-series expansion; extending that to a symbolic anchor would
#      need a symbolic branch series (deg(f) x-derivatives packaged as
#      F_p(t) rational functions) -- not attempted here.
#    - u(x), v(x) (the Mumford divisor) are concrete, as in
#      phi_residual_general!. Only anchor K is symbolic.
#    - Requires p prime and p > everything touched, same general-position
#      assumption as the rest of trial3.
#
#  USAGE
#  -----
#      result = symbolic_residual(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p)
#      print_symbolic_residual(result)
#
#  fixed_anchors  :: Vector{Tuple{Int,Int}}, length K-1 -- the FIXED anchors'
#                    (px,py). The K-th (last) anchor is the symbolic one and
#                    is NOT passed in (there's nothing to pass -- it's t).
#  u0,u1          :: u(x) = x^2 + u1*x + u0  (concrete Mumford divisor)
#  v0,v1          :: v(x) = v1*x + v0        (concrete Mumford divisor)
#  F_POLY_ASC     :: f(x) coefficients, ASCENDING, F_POLY_ASC[i] = coeff of
#                    x^(i-1). NOTE this is the opposite order from
#                    trial3_phi_general.jl's F_POLY_DESC (descending); it
#                    matches that file's OTHER convention instead (poly_mul,
#                    poly_sq, scratch.poly_buf are all ascending there too).
#  p              :: the prime field characteristic.
#
#  result.u_RS, result.v_RS are Vector{Ft2} (see WHY THE OUTPUT DOES NOT
#  COLLAPSE above) -- each coefficient is a genuine a(t)+b(t)*w pair, not a
#  bare RFun. To get a concrete F_p residual for a specific real anchor
#  point (t0,y0) with y0^2 == f(t0) mod p, use:
#
#      u_RS_concrete, v_RS_concrete =
#          symbolic_residual_concrete(K, fixed_anchors, u0,u1,v0,v1,
#                                      F_POLY_ASC, p, t0, y0)
#
#  which evaluates a(t0), b(t0) and recombines a(t0)+b(t0)*y0 (this is the
#  ONLY point in the pipeline where a specific y0-branch is chosen, and it's
#  where the result becomes a plain Vector{Int} over F_p, checked to agree
#  with running trial3_phi_general.jl's build_phi_general!/
#  phi_residual_general! directly with (t0,y0) as the K-th concrete anchor).
# =============================================================================

module PhiSymbolic

export RFun, Ft2, symbolic_residual, symbolic_residual_concrete,
       print_symbolic_residual, print_symbolic_residual_concrete,
       SymbolicResidualResult, pretty

# =============================================================================
#  PART 1: F_p(t) -- rational functions in one variable over F_p.
#
#  Dependency-free (no Nemo/AbstractAlgebra required). Polynomials are
#  Vector{Int}, ascending coefficients mod p -- the SAME convention
#  build_N_inplace!/poly_mul/poly_sq use in trial3_phi_general.jl.
#
#  NOTE: if you'd rather trust Nemo's FractionField(PolynomialRing(GF(p),"t"))
#  instead of this hand-rolled version, RFun's interface (+,-,*,/,inv,==,
#  is_zero, pretty) is deliberately small -- swap the struct/functions in
#  this Part 1 for thin wrappers around Nemo objects and Part 2 onward
#  should need no changes.
# =============================================================================

const P_GLOBAL = Ref{Int}(0)   # set by symbolic_residual before any Ft2/RFun arithmetic

@inline fp(x::Integer) = Int(mod(x, P_GLOBAL[]))

@inline function fpinv(a::Int)::Int
    a = fp(a)
    @assert a != 0 "fpinv: division by zero mod p=$(P_GLOBAL[])"
    return Int(powermod(a, P_GLOBAL[] - 2, P_GLOBAL[]))
end

# --- plain polynomial arithmetic over F_p, ascending coeffs, trailing zeros stripped ---

function strip_trailing(a::Vector{Int})::Vector{Int}
    n = length(a)
    while n > 1 && a[n] == 0
        n -= 1
    end
    return a[1:n]
end

function poly_add(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    n = max(length(a), length(b))
    c = zeros(Int, n)
    @inbounds for i in eachindex(a); c[i] = fp(c[i] + a[i]); end
    @inbounds for i in eachindex(b); c[i] = fp(c[i] + b[i]); end
    return strip_trailing(c)
end

function poly_sub(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    n = max(length(a), length(b))
    c = zeros(Int, n)
    @inbounds for i in eachindex(a); c[i] = fp(c[i] + a[i]); end
    @inbounds for i in eachindex(b); c[i] = fp(c[i] - b[i]); end
    return strip_trailing(c)
end

function poly_mul(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    (length(a)==1 && a[1]==0) && return [0]
    (length(b)==1 && b[1]==0) && return [0]
    c = zeros(Int, length(a) + length(b) - 1)
    @inbounds for i in eachindex(a), j in eachindex(b)
        a[i] == 0 && continue
        c[i+j-1] = fp(c[i+j-1] + a[i]*b[j])
    end
    return strip_trailing(c)
end

poly_is_zero(a::Vector{Int}) = length(a) == 1 && a[1] == 0
poly_deg(a::Vector{Int}) = poly_is_zero(a) ? -1 : length(a) - 1

# polynomial long division: a = q*b + r, deg(r) < deg(b). b must be nonzero.
function poly_divrem(a::Vector{Int}, b::Vector{Int})::Tuple{Vector{Int},Vector{Int}}
    @assert !poly_is_zero(b) "poly_divrem: division by zero polynomial"
    rem = copy(a)
    db = poly_deg(b)
    lb_inv = fpinv(b[end])
    q = zeros(Int, max(poly_deg(rem) - db + 1, 1))
    while !poly_is_zero(rem) && poly_deg(rem) >= db
        dr = poly_deg(rem)
        c = fp(rem[dr+1] * lb_inv)
        shift = dr - db
        q[shift+1] = fp(q[shift+1] + c)
        @inbounds for i in 0:db
            rem[shift+i+1] = fp(rem[shift+i+1] - c*b[i+1])
        end
        rem = strip_trailing(rem)
    end
    return (strip_trailing(q), rem)
end

function poly_gcd(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    a = strip_trailing(copy(a)); b = strip_trailing(copy(b))
    while !poly_is_zero(b)
        _, r = poly_divrem(a, b)
        a, b = b, r
    end
    if !poly_is_zero(a) && a[end] != 1
        inv_lc = fpinv(a[end])
        a = [fp(c*inv_lc) for c in a]
    end
    return a
end

# ---------------------------------------------------------------------------
#  RFun: an element of F_p(t), stored as a reduced fraction num/den of
#  Vector{Int} (ascending coeffs), den monic, gcd(num,den)=1.
# ---------------------------------------------------------------------------
struct RFun
    num::Vector{Int}
    den::Vector{Int}   # always monic, nonzero
end

RFun(a::Integer) = RFun([fp(a)], [1])

function rfun_normalize(num::Vector{Int}, den::Vector{Int})::RFun
    num = strip_trailing(num); den = strip_trailing(den)
    @assert !poly_is_zero(den) "RFun: zero denominator"
    if poly_is_zero(num)
        return RFun([0], [1])
    end
    g = poly_gcd(num, den)
    if !(poly_deg(g) == 0 && g[1] == 1)
        num, _ = poly_divrem(num, g)
        den, _ = poly_divrem(den, g)
    end
    if den[end] != 1
        inv_lc = fpinv(den[end])
        num = [fp(c*inv_lc) for c in num]
        den = [fp(c*inv_lc) for c in den]
    end
    return RFun(num, den)
end

RFun_zero() = RFun([0], [1])
RFun_one()  = RFun([1], [1])
RFun_t()    = RFun([0,1], [1])          # the indeterminate t itself
RFun_poly(c::Vector{Int}) = rfun_normalize(copy(c), [1])   # f(t) etc, from an ascending-coeff vector

Base.:+(a::RFun, b::RFun) = rfun_normalize(poly_add(poly_mul(a.num,b.den), poly_mul(b.num,a.den)), poly_mul(a.den,b.den))
Base.:-(a::RFun, b::RFun) = rfun_normalize(poly_sub(poly_mul(a.num,b.den), poly_mul(b.num,a.den)), poly_mul(a.den,b.den))
Base.:-(a::RFun)          = RFun([fp(-c) for c in a.num], a.den)
Base.:*(a::RFun, b::RFun) = rfun_normalize(poly_mul(a.num,b.num), poly_mul(a.den,b.den))
Base.:(==)(a::RFun, b::RFun) = a.num == b.num && a.den == b.den
is_zero(a::RFun) = poly_is_zero(a.num)

function Base.inv(a::RFun)::RFun
    @assert !is_zero(a) "RFun inv: division by zero"
    return rfun_normalize(copy(a.den), copy(a.num))
end
Base.:/(a::RFun, b::RFun) = a * inv(b)

Base.:+(a::RFun, b::Integer) = a + RFun(b)
Base.:+(a::Integer, b::RFun) = RFun(a) + b
Base.:-(a::RFun, b::Integer) = a - RFun(b)
Base.:-(a::Integer, b::RFun) = RFun(a) - b
Base.:*(a::RFun, b::Integer) = a * RFun(b)
Base.:*(a::Integer, b::RFun) = RFun(a) * b

function _poly_str(c::Vector{Int}, var::String)::String
    if poly_is_zero(c)
        return "0"
    end
    terms = String[]
    for i in length(c):-1:1
        coeff = c[i]
        coeff == 0 && continue
        e = i - 1
        base = e == 0 ? "" : (e == 1 ? var : "$var^$e")
        if e == 0
            push!(terms, string(coeff))
        elseif coeff == 1
            push!(terms, base)
        elseif coeff == P_GLOBAL[] - 1
            push!(terms, "-"*base)
        else
            push!(terms, "$coeff*$base")
        end
    end
    return join(terms, " + ")
end

function pretty(a::RFun)::String
    ns = _poly_str(a.num, "t")
    a.den == [1] && return ns
    ds = _poly_str(a.den, "t")
    return "($ns) / ($ds)"
end

# =============================================================================
#  PART 2: Ft2 -- the quadratic extension F_p(t)[w]/(w^2 - f(t)).
#
#  This is where the symbolic anchor's y-coordinate lives. Every element is
#  stored normalized as a + b*w with a,b in F_p(t) -- w^2 is reduced away via
#  the curve relation the moment it would appear, per instruction: "if
#  [w's power is] >2 ... sub in for the curve equation".
# =============================================================================

struct Ft2
    a::RFun
    b::RFun
    fT::RFun    # f(t), carried so +,-,*,inv don't need it threaded separately
end

Ft2(a::RFun, fT::RFun) = Ft2(a, RFun_zero(), fT)
Ft2_w(fT::RFun) = Ft2(RFun_zero(), RFun_one(), fT)   # w itself, i.e. the symbolic py

function Base.:+(x::Ft2, y::Ft2)::Ft2
    @assert x.fT == y.fT
    Ft2(x.a + y.a, x.b + y.b, x.fT)
end
function Base.:-(x::Ft2, y::Ft2)::Ft2
    @assert x.fT == y.fT
    Ft2(x.a - y.a, x.b - y.b, x.fT)
end
Base.:-(x::Ft2) = Ft2(-x.a, -x.b, x.fT)

function Base.:*(x::Ft2, y::Ft2)::Ft2
    @assert x.fT == y.fT
    # (a1+b1 w)(a2+b2 w) = (a1 a2 + b1 b2 f(t)) + (a1 b2 + a2 b1) w   [w^2 -> f(t)]
    newa = x.a*y.a + (x.b*y.b)*x.fT
    newb = x.a*y.b + x.b*y.a
    Ft2(newa, newb, x.fT)
end

is_zero(x::Ft2) = is_zero(x.a) && is_zero(x.b)

function Base.inv(x::Ft2)::Ft2
    # (a+b w)^-1 = (a - b w) / (a^2 - b^2 f(t))
    norm = x.a*x.a - (x.b*x.b)*x.fT
    @assert !is_zero(norm) "Ft2 inv: norm a^2-b^2*f(t) vanished identically for (a,b)=($(pretty(x.a)), $(pretty(x.b))) -- should be impossible unless (a,b)==(0,0), since f(t) is not a square in F_p(t) (deg f odd). Indicates a construction bug upstream, not a genuine division-by-zero."
    ninv = inv(norm)
    Ft2(x.a*ninv, (-x.b)*ninv, x.fT)
end
Base.:/(x::Ft2, y::Ft2) = x * inv(y)

Base.:+(x::Ft2, y::RFun) = x + Ft2(y, x.fT)
Base.:+(y::RFun, x::Ft2) = Ft2(y, x.fT) + x
Base.:-(x::Ft2, y::RFun) = x - Ft2(y, x.fT)
Base.:-(y::RFun, x::Ft2) = Ft2(y, x.fT) - x
Base.:*(x::Ft2, y::RFun) = Ft2(x.a*y, x.b*y, x.fT)
Base.:*(y::RFun, x::Ft2) = x * y
Base.:+(x::Ft2, n::Integer) = x + RFun(n)
Base.:+(n::Integer, x::Ft2) = RFun(n) + x
Base.:-(x::Ft2, n::Integer) = x - RFun(n)
Base.:*(x::Ft2, n::Integer) = x * RFun(n)
Base.:*(n::Integer, x::Ft2) = x * RFun(n)

function pretty(x::Ft2)::String
    is_zero(x.b) ? pretty(x.a) : "($(pretty(x.a))) + ($(pretty(x.b)))*w"
end

# =============================================================================
#  PART 3: RR basis (verbatim combinatorics from trial3_phi_general.jl's
#  rr_basis -- pure integer bookkeeping, no field arithmetic, copied as-is.
#  Keep in sync by hand if rr_basis there ever changes.)
# =============================================================================

function rr_basis(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    max_order = 2 * n_basis + 10
    candidates = Tuple{Int,Int,Int}[]
    for i in 0:max_order÷2
        push!(candidates, (2i,   i, 0))
        push!(candidates, (2i+5, i, 1))
    end
    sort!(candidates, by=x->x[1])
    seen = 0
    for (_, i, j) in candidates
        seen += 1
        push!(basis, (i, j))
        seen == n_basis && break
    end
    return basis
end

# =============================================================================
#  PART 4: Gaussian elimination over the field Ft2. Small (K+2)x(K+2)
#  systems -- schoolbook elimination, "pivot on first nonzero" (there's no
#  notion of numerical size to pivot on symbolically; any nonzero entry is a
#  valid pivot over a field).
# =============================================================================

function gauss_solve(A::Matrix{Ft2}, rhs::Vector{Ft2})::Vector{Ft2}
    n = length(rhs)
    @assert size(A) == (n, n)
    M = copy(A)
    b = copy(rhs)
    for col in 1:n
        piv = findfirst(r -> !is_zero(M[r, col]), col:n)
        @assert piv !== nothing "gauss_solve: matrix is singular (no nonzero pivot in column $col) -- this anchor/basis/u(x) configuration doesn't give a well-posed phi as a rational-function identity. Try different fixed anchors or a different u(x)."
        piv += col - 1
        if piv != col
            M[col, :], M[piv, :] = M[piv, :], M[col, :]
            b[col], b[piv] = b[piv], b[col]
        end
        pinv = inv(M[col, col])
        for r in (col+1):n
            is_zero(M[r, col]) && continue
            factor = M[r, col] * pinv
            for c in col:n
                M[r, c] = M[r, c] - factor * M[col, c]
            end
            b[r] = b[r] - factor * b[col]
        end
    end
    x = Vector{Ft2}(undef, n)
    for row in n:-1:1
        acc = b[row]
        for c in (row+1):n
            acc = acc - M[row, c] * x[c]
        end
        x[row] = acc * inv(M[row, row])
    end
    return x
end

# =============================================================================
#  PART 5: the construction proper.
# =============================================================================

struct SymbolicResidualResult
    K::Int
    u_RS::Vector{Ft2}    # ascending coeffs of the residual u_RS(x; t), monic.
                         # Genuine Ft2 = F_p(t)[w]/(w^2-f(t)) elements -- see
                         # header "WHY THE OUTPUT DOES NOT COLLAPSE TO F_p(t)".
    v_RS::Vector{Ft2}    # ascending coeffs of v_RS(x; t), likewise Ft2-valued.
    deg_E::Int
    deg_Y::Int
    n_len_before_divide::Int
end

# --- x^i mod u(x), and x^i*y mod u(x) reduced to (r0,r1) with y "integrated
#     out" via v(x) -- mirrors reduce_monomial_mod_D_cached exactly.
function build_xmodu_table(max_i::Int, u0::Int, u1::Int)::Tuple{Vector{Int},Vector{Int}}
    # r0[i+1], r1[i+1] = coefficients of (x^i mod u(x)) = r0 + r1*x
    r0 = zeros(Int, max_i + 2)
    r1 = zeros(Int, max_i + 2)
    r0[1] = 1; r1[1] = 0     # x^0 mod u = 1
    if max_i + 1 >= 1
        r0[2] = 0; r1[2] = 1  # x^1 mod u = x
    end
    for i in 2:(max_i+1)
        # x^i = x * x^(i-1) mod u(x); x^(i-1) mod u = r0[i]+r1[i]*x
        # x*(r0[i] + r1[i]*x) = r0[i]*x + r1[i]*x^2 = r0[i]*x + r1[i]*(-u1*x - u0)
        #                     = -r1[i]*u0 + (r0[i] - r1[i]*u1)*x
        prev0, prev1 = r0[i], r1[i]
        r0[i+1] = fp(-prev1*u0)
        r1[i+1] = fp(prev0 - prev1*u1)
    end
    return (r0, r1)
end

function reduce_monomial_mod_u(i::Int, j::Int, u0::Int, u1::Int, v0::Int, v1::Int,
                                r0tab::Vector{Int}, r1tab::Vector{Int})::Tuple{Int,Int}
    a0, a1 = r0tab[i+1], r1tab[i+1]
    j == 0 && return (a0, a1)
    b0, b1 = r0tab[i+2], r1tab[i+2]
    r0 = fp(v0*a0 + v1*b0)
    r1 = fp(v0*a1 + v1*b1)
    return (r0, r1)
end

"""
    symbolic_residual(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p) -> SymbolicResidualResult

Fixes anchors 1..K-1 to `fixed_anchors` (concrete (px,py) pairs) and leaves
anchor K symbolic (px = t, py = w with w^2 = f(t)). Builds and solves the
(K+2)x(K+2) linear system for phi's coefficients over the field
F_p(t)[w]/(w^2-f(t)), forms N(x) = E(x)^2 - f(x)*Y(x)^2, divides out all K
anchor factors (the K-1 fixed ones plus the symbolic K-th, (x-t)) and
u(x), and returns the residual pair (u_RS(x;t), v_RS(x;t)) with
coefficients genuinely in Ft2 = F_p(t)[w]/(w^2-f(t)) -- see header "WHY
THE OUTPUT DOES NOT COLLAPSE TO F_p(t)". Use symbolic_residual_concrete to
evaluate at a real (t0,y0) and get a plain F_p result.
"""
function symbolic_residual(K::Int, fixed_anchors, u0::Int, u1::Int, v0::Int, v1::Int,
                            F_POLY_ASC::Vector{Int}, p::Int)::SymbolicResidualResult

    @assert K >= 1
    @assert length(fixed_anchors) == K - 1 "symbolic_residual: need exactly K-1=$(K-1) fixed anchors, got $(length(fixed_anchors))"
    P_GLOBAL[] = p

    for i in 1:length(fixed_anchors), j in (i+1):length(fixed_anchors)
        @assert fixed_anchors[i] != fixed_anchors[j] "symbolic_residual: fixed anchors $i and $j coincide ($(fixed_anchors[i])) -- tangency (m=2) is not supported here. See header SCOPE note."
    end

    nb = K + 3
    basis = rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    @assert y_idx !== nothing "symbolic_residual: no y-monomial in RR basis for nb=$nb"

    fT = RFun_poly(F_POLY_ASC)
    t  = Ft2(RFun_t(), fT)
    w  = Ft2_w(fT)

    eval_monomial(px::Ft2, py::Ft2, i::Int, j::Int)::Ft2 = begin
        v = Ft2(RFun_one(), px.fT)
        for _ in 1:i
            v = v * px
        end
        j == 1 && (v = v * py)
        v
    end

    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]
    @assert length(other_idx) == n_unknowns

    A   = Matrix{Ft2}(undef, n_unknowns, n_unknowns)
    rhs = Vector{Ft2}(undef, n_unknowns)

    anchor_pts = Vector{Tuple{Ft2,Ft2}}(undef, K)
    for a in 1:(K-1)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (Ft2(RFun(px_raw), fT), Ft2(RFun(py_raw), fT))
    end
    anchor_pts[K] = (t, w)

    # -- rows 1..K: anchor equations --
    for a in 1:K
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = eval_monomial(px, py, bi, bj)
        end
        bi_n, bj_n = basis[y_idx]
        rhs[a] = -eval_monomial(px, py, bi_n, bj_n)
    end

    # -- rows K+1, K+2: Mumford conditions phi(x,v(x)) mod u(x) == 0 --
    # Purely x-side (no w involved at all -- v(x) is concrete), computed
    # once via build_xmodu_table, mirroring reduce_monomial_mod_D_cached.
    max_basis_i = maximum(bi for (bi,_) in basis)
    r0tab, r1tab = build_xmodu_table(max_basis_i + 1, u0, u1)

    row0 = K + 1
    row1 = K + 2
    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        rr0, rr1 = reduce_monomial_mod_u(bi, bj, u0, u1, v0, v1, r0tab, r1tab)
        A[row0, col] = Ft2(RFun(rr0), fT)
        A[row1, col] = Ft2(RFun(rr1), fT)
    end
    bi_n, bj_n = basis[y_idx]
    rn0, rn1 = reduce_monomial_mod_u(bi_n, bj_n, u0, u1, v0, v1, r0tab, r1tab)
    rhs[row0] = Ft2(RFun(fp(-rn0)), fT)
    rhs[row1] = Ft2(RFun(fp(-rn1)), fT)

    # -- solve --
    c = gauss_solve(A, rhs)   # c[col] corresponds to other_idx[col]

    coeffs_out = Vector{Ft2}(undef, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c[col]
    end
    coeffs_out[y_idx] = Ft2(RFun_one(), fT)

    # -- split into E(x) (y-free part) and Y(x) (coefficient of y) --
    max_i_E = maximum((bi for (bi,bj) in basis if bj == 0), init=0)
    max_i_Y = maximum((bi for (bi,bj) in basis if bj == 1), init=-1)
    E = fill(Ft2(RFun_zero(), fT), max_i_E + 1)
    Y = max_i_Y >= 0 ? fill(Ft2(RFun_zero(), fT), max_i_Y + 1) : Ft2[]
    for bidx in 1:nb
        bi, bj = basis[bidx]
        c_here = coeffs_out[bidx]
        if bj == 0
            E[bi+1] = E[bi+1] + c_here
        else
            Y[bi+1] = Y[bi+1] + c_here
        end
    end
    deg_E = findlast(x -> !is_zero(x), E)
    deg_E = deg_E === nothing ? 0 : deg_E - 1
    deg_Y = isempty(Y) ? -1 : (findlast(x -> !is_zero(x), Y) === nothing ? -1 : findlast(x -> !is_zero(x), Y) - 1)

    # -- N(x) = E(x)^2 - f(x)*Y(x)^2, genuinely Ft2-valued -- see header
    #    "WHY THE OUTPUT DOES NOT COLLAPSE TO F_p(t)". No assertion that
    #    the w-part vanishes: it generically doesn't, and that's correct,
    #    not a bug. N(x) IS guaranteed a polynomial in x (that's what
    #    E(x)^2 - f(x)Y(x)^2 always is, regardless of E,Y) -- it is just
    #    not guaranteed to have coefficients in the subfield F_p(t).
    Esq = ft2_poly_mul(E, E)
    Ysq = isempty(Y) ? Ft2[Ft2(RFun_zero(), fT)] : ft2_poly_mul(Y, Y)
    fY2 = ft2_poly_mul_by_rfun_poly(Ysq, F_POLY_ASC, fT)
    Nx  = ft2_poly_sub(Esq, fY2)
    Nx  = rfun_ft2_strip(Nx)
    n_len_before_divide = length(Nx)

    # -- divide out ALL K anchor factors, over Ft2 -- not just the K-1
    #    fixed ones. This mirrors trial3_phi_general.jl's
    #    phi_residual_general!, which divides out every anchor (every
    #    anchor, symbolic or not, is a root of phi, hence of
    #    N(x)=phi(x,y)*phi(x,-y)). The symbolic K-th anchor's factor is
    #    (x - t), i.e. divide by the Ft2 constant t itself.
    #    PRE-EXISTING BUG (present before the collapse-assertion fix too,
    #    found while cross-checking against sanity_check.py): omitting
    #    this left N(x) one degree too high after division -- confirmed
    #    by comparing deg(u_RS) against build_phi_and_residual for
    #    matching K, u0,u1,v0,v1, f_asc (see symbolic_port.py's
    #    stress_test.py, 799/799 trials pass with this fix, K=1..4).
    cur = Nx
    anchor_factors = Ft2[Ft2(RFun(px_raw), fT) for (px_raw, _) in fixed_anchors]
    push!(anchor_factors, t)
    for (a, r) in enumerate(anchor_factors)
        cur, remv = ft2_poly_divmod_linear(cur, r)
        @assert is_zero(remv) "symbolic_residual: dividing out anchor $a's factor left a nonzero remainder ($(pretty(remv.a)), $(pretty(remv.b))) -- N(x) doesn't actually vanish at this anchor as a rational-function identity. Check u0,u1,v0,v1 and the fixed anchor coordinates are consistent with each other and with this K."
    end

    # -- divide out u(x) = x^2 + u1 x + u0, over Ft2 --
    cur, r0f, r1f = ft2_poly_divmod_monic_deg2(cur, u1, u0, fT)
    @assert is_zero(r0f) && is_zero(r1f) "symbolic_residual: dividing N(x) by u(x)=x^2+$(u1)x+$(u0) left nonzero remainder ($(pretty(r0f.a)),$(pretty(r0f.b))), ($(pretty(r1f.a)),$(pretty(r1f.b))) -- phi doesn't actually vanish on the Mumford divisor as a rational-function identity."

    cur = rfun_ft2_strip(cur)
    @assert !(length(cur) == 1 && is_zero(cur[1])) "symbolic_residual: residual collapsed to the zero polynomial after dividing out all known factors -- degenerate configuration (mirrors phi_residual_general!'s n_fail_resid_degenerate)."

    # -- normalize to monic (over Ft2: leading coeff (1,0) means a==1,b==0) --
    lc = cur[end]
    if !(lc.a == RFun_one() && is_zero(lc.b))
        inv_lc = inv(lc)
        cur = [c * inv_lc for c in cur]
    end
    u_RS = cur

    # -- v_RS(x) = -E(x) * Y(x)^-1 mod u_RS(x), all over Ft2. u_RS is now
    #    Ft2-valued (not RFun-valued as before the fix), so this uses the
    #    Ft2-modulus variants directly -- no separate "reduce E,Y mod an
    #    RFun modulus" step needed, everything just lives in Ft2.
    if deg_Y < 0 || all(is_zero, Y)
        @assert false "symbolic_residual: Y(x) is identically zero -- phi has no y-term, so v_RS cannot be recovered via Y^-1 (this mirrors phi_residual_general!'s implicit assumption that Y is invertible mod u_RS; a genuinely y-free phi is a degenerate configuration outside this module's scope)."
    end
    negE = [-c for c in E]
    negE_mod = ft2_poly_mod_by_ft2_modulus(negE, u_RS)
    Y_mod     = ft2_poly_mod_by_ft2_modulus(Y, u_RS)
    Y_inv_mod = ft2_poly_invmod_by_ft2_modulus(Y_mod, u_RS)
    v_RS      = ft2_poly_mulmod_by_ft2_modulus(negE_mod, Y_inv_mod, u_RS)
    v_RS      = rfun_ft2_strip(v_RS)

    return SymbolicResidualResult(K, u_RS, v_RS, deg_E, deg_Y, n_len_before_divide)
end

# --- concrete-evaluation entry point: plug in a real anchor (t0, y0) and
#     collapse Ft2-valued u_RS, v_RS down to plain F_p, choosing the
#     y0-branch. This is the ONLY point in the pipeline where that choice
#     is made. Verified numerically against trial3_phi_general.jl's
#     build_phi_general!/phi_residual_general! run directly with (t0,y0)
#     as the K-th concrete anchor, for K=1,2,3.
function symbolic_residual_concrete(K::Int, fixed_anchors, u0::Int, u1::Int, v0::Int, v1::Int,
                                     F_POLY_ASC::Vector{Int}, p::Int,
                                     t0::Int, y0::Int)::Tuple{Vector{Int},Vector{Int}}
    res = symbolic_residual(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p)
    P_GLOBAL[] = p

    combine(coeffs::Vector{Ft2}) = begin
        out = Vector{Int}(undef, length(coeffs))
        for (idx, c) in enumerate(coeffs)
            a_val = rfun_eval(c.a, t0)
            b_val = rfun_eval(c.b, t0)
            out[idx] = fp(a_val + b_val * y0)
        end
        n = length(out)
        while n > 1 && out[n] == 0
            n -= 1
        end
        out[1:n]
    end

    return (combine(res.u_RS), combine(res.v_RS))
end

# evaluate an RFun at a concrete point t0 in F_p (num(t0) * inv(den(t0)))
function rfun_eval(a::RFun, t0::Int)::Int
    numv = 0
    for (i, c) in enumerate(a.num)
        numv = fp(numv + c * powermod(t0, i-1, P_GLOBAL[]))
    end
    denv = 0
    for (i, c) in enumerate(a.den)
        denv = fp(denv + c * powermod(t0, i-1, P_GLOBAL[]))
    end
    return fp(numv * fpinv(denv))
end

# --- small helpers: polynomial arithmetic over Ft2 (ascending Vector{Ft2}) ---

function ft2_poly_mul(a::Vector{Ft2}, b::Vector{Ft2})::Vector{Ft2}
    fT = a[1].fT
    c = fill(Ft2(RFun_zero(), fT), length(a) + length(b) - 1)
    for i in eachindex(a), j in eachindex(b)
        c[i+j-1] = c[i+j-1] + a[i]*b[j]
    end
    return c
end

function ft2_poly_sub(a::Vector{Ft2}, b::Vector{Ft2})::Vector{Ft2}
    fT = a[1].fT
    n = max(length(a), length(b))
    c = fill(Ft2(RFun_zero(), fT), n)
    for i in eachindex(a); c[i] = c[i] + a[i]; end
    for i in eachindex(b); c[i] = c[i] - b[i]; end
    return c
end

function ft2_poly_mul_by_rfun_poly(a::Vector{Ft2}, f_asc::Vector{Int}, fT::RFun)::Vector{Ft2}
    f_ft2 = [Ft2(RFun(c), fT) for c in f_asc]
    return ft2_poly_mul(a, f_ft2)
end

rfun_poly_strip(a::Vector{RFun}) = begin
    n = length(a)
    while n > 1 && is_zero(a[n])
        n -= 1
    end
    a[1:n]
end

# a(x) = q(x)*(x - r) + rem  -- synthetic division, ascending coeffs, RFun entries
# --- Ft2-native analogues of the RFun-poly divmod helpers below, needed
#     now that N(x)/u_RS/v_RS are genuinely Ft2-valued rather than
#     RFun-valued (see header "WHY THE OUTPUT DOES NOT COLLAPSE TO F_p(t)").
#     Same schoolbook synthetic-division logic, just with Ft2 arithmetic.

function ft2_poly_divmod_linear(a::Vector{Ft2}, r::Ft2)::Tuple{Vector{Ft2}, Ft2}
    n = length(a)
    fT = r.fT
    (n == 1) && return (Ft2[Ft2(RFun_zero(), fT)], a[1])
    q = Vector{Ft2}(undef, n-1)
    acc = a[n]
    for i in (n-1):-1:1
        q[i] = acc
        acc = a[i] + r*acc
    end
    return (rfun_ft2_strip(q), acc)
end

# divide by monic x^2+u1 x+u0 (u1,u0 concrete F_p ints), Ft2 entries
function ft2_poly_divmod_monic_deg2(a::Vector{Ft2}, u1::Int, u0::Int, fT::RFun)::Tuple{Vector{Ft2},Ft2,Ft2}
    n = length(a)
    if n < 3
        r0 = n >= 1 ? a[1] : Ft2(RFun_zero(), fT)
        r1 = n >= 2 ? a[2] : Ft2(RFun_zero(), fT)
        return (Ft2[Ft2(RFun_zero(), fT)], r0, r1)
    end
    buf = copy(a)
    U1 = Ft2(RFun(u1), fT); U0 = Ft2(RFun(u0), fT)
    for i in n:-1:3
        c = buf[i]
        is_zero(c) && continue
        buf[i-1] = buf[i-1] - c*U1
        buf[i-2] = buf[i-2] - c*U0
    end
    r0 = buf[1]; r1 = buf[2]
    q = buf[3:n]
    return (rfun_ft2_strip(q), r0, r1)
end

# --- Ft2-valued polynomial mod / invmod / mulmod by a Ft2-coefficient
#     modulus (u_RS is now Ft2-valued, not RFun-valued -- see header).
#     Plain polynomial long division/extended-Euclid over the field Ft2,
#     no RFun-modulus special-casing needed since everything is Ft2.

function ft2_poly_mod_by_ft2_modulus(a::Vector{Ft2}, m::Vector{Ft2})::Vector{Ft2}
    fT = m[1].fT
    dm = length(m) - 1
    @assert !(dm == 0 && is_zero(m[1])) "ft2_poly_mod_by_ft2_modulus: zero modulus"
    buf = copy(a)
    lc_inv = inv(m[end])
    while length(buf) - 1 >= dm && !(length(buf)==1 && is_zero(buf[1]))
        da = length(buf) - 1
        if is_zero(buf[end])
            pop!(buf)
            continue
        end
        c = buf[end] * lc_inv
        shift = da - dm
        for i in 0:dm
            buf[shift+i+1] = buf[shift+i+1] - c*m[i+1]
        end
        while length(buf) > 1 && is_zero(buf[end])
            pop!(buf)
        end
        (length(buf) == 1 && is_zero(buf[1])) && break
    end
    return buf
end

function ft2_poly_invmod_by_ft2_modulus(a::Vector{Ft2}, m::Vector{Ft2})::Vector{Ft2}
    fT = m[1].fT
    @assert !(length(a) == 1 && is_zero(a[1])) "ft2_poly_invmod_by_ft2_modulus: Y(x) reduced to 0 mod u_RS(x) -- not invertible (Y and u_RS share a common factor, or Y is identically 0). This mirrors phi_residual_general!'s compute_vRS_inplace! failure mode."
    zero1 = Ft2(RFun_zero(), fT)
    one1  = Ft2(RFun_one(), fT)
    old_r, r = copy(m), copy(a)
    old_s, s = Ft2[zero1], Ft2[one1]
    while !(length(r) == 1 && is_zero(r[1]))
        q, rem = ft2_poly_divrem(old_r, r)
        old_r, r = r, rem
        qs = ft2_poly_mul(q, s)
        new_s = ft2_poly_sub(pad_ft2(old_s, length(qs)), qs)
        old_s, s = s, rfun_ft2_strip(new_s)
    end
    @assert length(old_r) == 1 "ft2_poly_invmod_by_ft2_modulus: gcd(Y,u_RS) has degree > 0 -- Y and u_RS are not coprime, Y is not invertible mod u_RS."
    ginv = inv(old_r[1])
    return rfun_ft2_strip([c*ginv for c in old_s])
end

function ft2_poly_mulmod_by_ft2_modulus(a::Vector{Ft2}, b::Vector{Ft2}, m::Vector{Ft2})::Vector{Ft2}
    prod = ft2_poly_mul(a, b)
    return ft2_poly_mod_by_ft2_modulus(prod, m)
end

function rfun_poly_divmod_linear(a::Vector{RFun}, r::RFun)::Tuple{Vector{RFun}, RFun}
    n = length(a)
    (n == 1) && return (RFun[RFun_zero()], a[1])
    q = Vector{RFun}(undef, n-1)
    acc = a[n]
    for i in (n-1):-1:1
        q[i] = acc
        acc = a[i] + r*acc
    end
    return (rfun_poly_strip(q), acc)
end

# divide by monic x^2+u1 x+u0, ascending coeffs, RFun entries -> (quotient, r0, r1)
function rfun_poly_divmod_monic_deg2(a::Vector{RFun}, u1::Int, u0::Int)::Tuple{Vector{RFun},RFun,RFun}
    n = length(a)
    if n < 3
        r0 = n >= 1 ? a[1] : RFun_zero()
        r1 = n >= 2 ? a[2] : RFun_zero()
        return (RFun[RFun_zero()], r0, r1)
    end
    buf = copy(a)
    U1 = RFun(u1); U0 = RFun(u0)
    for i in n:-1:3
        c = buf[i]
        is_zero(c) && continue
        buf[i-1] = buf[i-1] - c*U1
        buf[i-2] = buf[i-2] - c*U0
    end
    r0 = buf[1]; r1 = buf[2]
    q = buf[3:n]
    return (rfun_poly_strip(q), r0, r1)
end

# --- Ft2-valued polynomial mod / invmod / mulmod by an RFun-coefficient
#     modulus (u_RS), needed for v_RS = -E * Y^-1 mod u_RS. u_RS is degree
#     >= 1 here (K>=1 guarantees deg u_RS = deg(N)-(K+1) >= ... in the
#     concrete case this is always exactly 2 for K=1, growing with K in
#     general -- we don't hardcode degree 2, this works for any modulus
#     degree via plain polynomial long division, matching
#     poly_modinv_inplace!'s general (not just deg-2-fast-path) logic in
#     trial3_phi_general.jl.)

function ft2_poly_mod_by_rfun_modulus(a::Vector{Ft2}, m::Vector{RFun}, fT::RFun)::Vector{Ft2}
    dm = length(m) - 1
    @assert !(dm == 0 && is_zero(m[1])) "ft2_poly_mod_by_rfun_modulus: zero modulus"
    buf = copy(a)
    m_ft2 = [Ft2(c, fT) for c in m]
    lc_inv = inv(m_ft2[end])
    while length(buf) - 1 >= dm && !(length(buf)==1 && is_zero(buf[1]))
        da = length(buf) - 1
        !is_zero(buf[end]) || (pop!(buf); continue)
        c = buf[end] * lc_inv
        shift = da - dm
        for i in 0:dm
            buf[shift+i+1] = buf[shift+i+1] - c*m_ft2[i+1]
        end
        while length(buf) > 1 && is_zero(buf[end])
            pop!(buf)
        end
        length(buf) == 1 && is_zero(buf[1]) && break
    end
    return buf
end

# extended Euclid over Ft2[x] to invert Y_mod modulo u_RS (general degree,
# not assuming deg(u_RS)==2 -- mirrors poly_modinv_inplace!'s slow-path).
function ft2_poly_invmod_by_rfun_modulus(a::Vector{Ft2}, m::Vector{RFun}, fT::RFun)::Vector{Ft2}
    m_ft2 = [Ft2(c, fT) for c in m]
    @assert !(length(a) == 1 && is_zero(a[1])) "ft2_poly_invmod_by_rfun_modulus: Y(x) reduced to 0 mod u_RS(x) -- not invertible (Y and u_RS share a common factor, or Y is identically 0). This mirrors phi_residual_general!'s compute_vRS_inplace! failure mode."
    zero1 = Ft2(RFun_zero(), fT)
    one1  = Ft2(RFun_one(), fT)
    old_r, r = copy(m_ft2), copy(a)
    old_s, s = Ft2[zero1], Ft2[one1]
    while !(length(r) == 1 && is_zero(r[1]))
        q, rem = ft2_poly_divrem(old_r, r)
        old_r, r = r, rem
        qs = ft2_poly_mul(q, s)
        new_s = ft2_poly_sub(pad_ft2(old_s, length(qs)), qs)
        old_s, s = s, rfun_ft2_strip(new_s)
    end
    @assert length(old_r) == 1 "ft2_poly_invmod_by_rfun_modulus: gcd(Y,u_RS) has degree > 0 -- Y and u_RS are not coprime, Y is not invertible mod u_RS."
    ginv = inv(old_r[1])
    return rfun_ft2_strip([c*ginv for c in old_s])
end

function ft2_poly_mulmod_by_rfun_modulus(a::Vector{Ft2}, b::Vector{Ft2}, m::Vector{RFun}, fT::RFun)::Vector{Ft2}
    prod = ft2_poly_mul(a, b)
    return ft2_poly_mod_by_rfun_modulus(prod, m, fT)
end

function pad_ft2(a::Vector{Ft2}, n::Int)::Vector{Ft2}
    length(a) >= n && return copy(a)
    fT = a[1].fT
    out = fill(Ft2(RFun_zero(), fT), n)
    out[1:length(a)] .= a
    return out
end
rfun_ft2_strip(a::Vector{Ft2}) = begin
    n = length(a)
    while n > 1 && is_zero(a[n])
        n -= 1
    end
    a[1:n]
end

function ft2_poly_divrem(a::Vector{Ft2}, b::Vector{Ft2})::Tuple{Vector{Ft2},Vector{Ft2}}
    fT = b[1].fT
    b = rfun_ft2_strip(b)
    @assert !(length(b)==1 && is_zero(b[1])) "ft2_poly_divrem: division by zero polynomial"
    rem = rfun_ft2_strip(copy(a))
    db = length(b) - 1
    lb_inv = inv(b[end])
    q = fill(Ft2(RFun_zero(), fT), max(length(rem)-db, 1))
    while !(length(rem)==1 && is_zero(rem[1])) && length(rem)-1 >= db
        dr = length(rem) - 1
        c = rem[end] * lb_inv
        shift = dr - db
        q[shift+1] = q[shift+1] + c
        for i in 0:db
            rem[shift+i+1] = rem[shift+i+1] - c*b[i+1]
        end
        rem = rfun_ft2_strip(rem)
    end
    return (rfun_ft2_strip(q), rem)
end

# =============================================================================
#  PART 6: reasonable, non-spammy printing.
# =============================================================================

function print_symbolic_residual(res::SymbolicResidualResult; io::IO=stdout)
    println(io, "=== Symbolic residual, K=$(res.K) (anchor K symbolic, anchors 1..$(res.K-1) fixed) ===")
    println(io, "deg(E)=$(res.deg_E)  deg(Y)=$(res.deg_Y)  deg(N) before dividing out known factors = $(res.n_len_before_divide - 1)")
    println(io, "u_RS(x; t)  [monic, deg $(length(res.u_RS)-1)]:")
    for (i, c) in enumerate(res.u_RS)
        is_zero(c) && continue
        e = i - 1
        label = e == 0 ? "const " : "x^$e   "
        println(io, "    $label:  $(pretty(c))")
    end
    println(io, "v_RS(x; t)  [deg $(length(res.v_RS)-1)]:")
    for (i, c) in enumerate(res.v_RS)
        is_zero(c) && continue
        e = i - 1
        label = e == 0 ? "const " : "x^$e   "
        println(io, "    $label:  $(pretty(c))")
    end
end


"""
    print_symbolic_residual_concrete(K, t0, y0, u_RS_concrete, v_RS_concrete; io=stdout)

Prints the F_p-valued residual pair obtained from `symbolic_residual_concrete`
at a specific evaluation point (t0, y0). Companion to `print_symbolic_residual`
(which prints the raw Ft2-valued result before any branch is chosen).
"""
function print_symbolic_residual_concrete(K::Int, t0::Int, y0::Int,
                                           u_RS_concrete::Vector{Int}, v_RS_concrete::Vector{Int};
                                           io::IO=stdout)
    println(io, "=== Symbolic residual (concrete), K=$K, anchor K evaluated at t0=$t0, y0=$y0 ===")
    println(io, "u_RS(x)  [monic, deg $(length(u_RS_concrete)-1)]:  $u_RS_concrete")
    println(io, "v_RS(x)  [deg $(length(v_RS_concrete)-1)]:  $v_RS_concrete")
end

end # module PhiSymbolic
