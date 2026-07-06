# =============================================================================
#  trial3_phi_symbolic2.jl  --  Symbolic (last-TWO-anchors-free) phi construction.
#
#  COMPANION TO: trial3_phi_general.jl (build_phi_general! / phi_residual_general!)
#  GENERALIZES:  trial3_phi_symbolic.jl (ONE symbolic anchor, over
#                Ft2 = F_p(t)[w]/(w^2-f(t)))
#
#  WHAT THIS IS
#  ------------
#  trial3_phi_symbolic.jl fixes anchors 1..K-1 concrete and leaves anchor K
#  symbolic (t,w). This module fixes anchors 1..K-2 concrete and leaves the
#  LAST TWO anchors symbolic:
#     anchor K-1 : (t1, w1),  w1^2 = f(t1)
#     anchor K   : (t2, w2),  w2^2 = f(t2)
#  t1, t2 are independent indeterminates. Every coefficient of phi, E, Y, N,
#  u_RS, v_RS now lives in
#
#       Ft4 := F_p(t1,t2)[w1,w2] / (w1^2 - f(t1),  w2^2 - f(t2))
#
#  an 8-dimensional... no -- a DEGREE-4 extension of F_p(t1,t2) (basis
#  {1, w1, w2, w1*w2}), built here as an ITERATED TOWER rather than a single
#  flat 4-component struct:
#
#       Level1 = QuadExt{RFun2}       -- adjoins w1 over F_p(t1,t2)
#       Level2 = QuadExt{Level1}      -- adjoins w2 over Level1
#
#  QuadExt{B} is a small generic "B[w]/(w^2-disc)" ring, written ONCE with
#  +,-,*,inv defined purely in terms of B's own +,-,*,inv,is_zero. It is used
#  TWICE (B=RFun2, then B=Level1), so none of the Ft2-style arithmetic in
#  trial3_phi_symbolic.jl had to be copy-pasted and re-derived by hand for a
#  4-dimensional case -- it falls out of composing the 2-dimensional case
#  with itself. Level2 elements print as a + b*w1 + c*w2 + d*w1*w2 with
#  a,b,c,d in F_p(t1,t2) (see `pretty`).
#
#  Every polynomial-in-x helper below (divmod by a linear factor, divmod by
#  the monic quadratic u(x), mod/invmod/mulmod by a Level2-valued modulus,
#  Gaussian elimination for the (K+2)x(K+2) system) is likewise written ONCE,
#  generically over a type parameter T, and instantiated with T=Level2 --
#  mirroring the corresponding Ft2-specific functions in
#  trial3_phi_symbolic.jl but without re-deriving each one for a new type.
#
#  SCOPE / LIMITATIONS (same spirit as trial3_phi_symbolic.jl's header, plus
#  one new item):
#    - Anchors are pairwise DISTINCT, m=1 each (no tangency), same as the
#      one-symbolic-anchor module. This applies to the two symbolic anchors
#      too: t1 and t2 are treated as formally distinct indeterminates, and
#      any concrete evaluation (t1_0,t2_0) you plug in must satisfy t1_0 !=
#      t2_0 mod p -- symbolic_residual2_concrete asserts this.
#    - u(x), v(x) (the Mumford divisor) are concrete, exactly as before.
#    - RFun2 (elements of F_p(t1,t2)) is stored as num/den where num is an
#      expanded BiPoly but den is a FACTORED multiset of BiPoly factors
#      (Dict{BiPoly,Int} => exponent). This is NOT a real bivariate GCD/
#      factorization engine (F_p[t1,t2] is a UFD, not Euclidean -- an actual
#      factoring routine would go via resultants or Groebner bases). Instead:
#      the denominator alphabet in this module's actual use (gauss_solve2 on
#      a Level2-valued system) is small and mostly RECURRING -- pivot
#      denominators, f(t1), f(t2), (t1-t2)-type factors get reused verbatim
#      over and over rather than being genuinely new polynomials each time.
#      Representing den as factor=>exponent and merging by structural
#      equality (BiPoly's own ==, which Dict already gives for free) turns
#      the dominant cost -- repeatedly multiplying the SAME growing
#      denominator into itself across an elimination column -- from
#      "convolve two huge Dicts" into "increment an integer". Numerators are
#      still expanded (they don't blow up nearly as fast in this module's
#      use, and keeping them expanded keeps bipoly_add/bipoly_eval trivial).
#      This is not a substitute for a real bivariate GCD (no cancellation is
#      attempted between num and den), but it removes the specific
#      catastrophic-blowup mode that made gauss_solve2 hang on sample 1: see
#      RFun2's +,-,*,inv below.
#    - Requires p prime and p > everything touched, same general-position
#      assumption as the rest of trial3.
#    - NOT YET RUN: Julia was not available in the environment this was
#      written in, so this has NOT been executed or cross-checked against
#      build_phi_general!/phi_residual_general! the way
#      trial3_phi_symbolic.jl was (see that file's header: "checked to
#      agree numerically for K=1,2,3"). Please run the equivalent
#      cross-check here (symbolic_residual2_concrete(K, fixed_anchors, ...,
#      t1_0,y1_0,t2_0,y2_0) vs. build_phi_general!/phi_residual_general! run
#      directly with (t1_0,y1_0) and (t2_0,y2_0) as the last two concrete
#      anchors) before trusting this for real work.
#
#  USAGE
#  -----
#      result = symbolic_residual2(K, fixed_anchors, u0,u1,v0,v1, F_POLY_ASC, p)
#      print_symbolic_residual2(result)
#
#  fixed_anchors :: Vector{Tuple{Int,Int}}, length K-2 -- the FIXED anchors'
#                   (px,py). Anchors K-1 and K are symbolic and are NOT
#                   passed in.
#  u0,u1,v0,v1,F_POLY_ASC,p :: same conventions as trial3_phi_symbolic.jl.
#
#  result.u_RS, result.v_RS :: Vector{Level2}, i.e. genuine
#  F_p(t1,t2)[w1,w2]/(w1^2-f(t1),w2^2-f(t2)) elements (never assumed to
#  collapse to anything smaller -- see trial3_phi_symbolic.jl's "WHY THE
#  OUTPUT DOES NOT COLLAPSE" discussion; the same reasoning applies here
#  once more, now for two independent symbolic anchors instead of one).
#
#  To get a concrete F_p residual for specific real anchor points (t1_0,y1_0)
#  and (t2_0,y2_0) with y1_0^2==f(t1_0), y2_0^2==f(t2_0) mod p, use:
#
#      u_RS_c, v_RS_c = symbolic_residual2_concrete(K, fixed_anchors,
#                           u0,u1,v0,v1, F_POLY_ASC, p, t1_0,y1_0,t2_0,y2_0)
# =============================================================================

module PhiSymbolic2

export RFun2, symbolic_residual2, symbolic_residual2_concrete,
       print_symbolic_residual2, print_symbolic_residual2_concrete,
       SymbolicResidualResult2, pretty

const P_GLOBAL2 = Ref{Int}(0)   # set by symbolic_residual2 before any arithmetic

@inline fp2(x::Integer) = Int(mod(x, P_GLOBAL2[]))

@inline function fpinv2(a::Int)::Int
    a = fp2(a)
    @assert a != 0 "fpinv2: division by zero mod p=$(P_GLOBAL2[])"
    return Int(powermod(a, P_GLOBAL2[] - 2, P_GLOBAL2[]))
end

# =============================================================================
#  PART 1: BiPoly -- sparse bivariate polynomials over F_p in (t1,t2).
#  Dict{(i,j) => coeff}, coeff always in [1,p-1] (zero entries pruned so
#  bipoly_is_zero is a cheap isempty check).
# =============================================================================

const BiPoly = Dict{Tuple{Int,Int},Int}

bipoly_zero()::BiPoly = BiPoly()
bipoly_is_zero(a::BiPoly)::Bool = isempty(a)

function bipoly_from_int(n::Integer)::BiPoly
    v = fp2(n)
    v == 0 ? bipoly_zero() : BiPoly((0,0) => v)
end
bipoly_t1()::BiPoly = BiPoly((1,0) => 1)
bipoly_t2()::BiPoly = BiPoly((0,1) => 1)

"""
    bipoly_from_univariate(coeffs_asc, var)

Lifts a univariate ascending-coefficient polynomial (e.g. F_POLY_ASC, f(x)'s
coefficients) into a bivariate polynomial purely in variable `var`
(1 => t1, 2 => t2), i.e. f(t1) or f(t2) as an element of F_p[t1,t2].
"""
function bipoly_from_univariate(coeffs_asc::Vector{Int}, var::Int)::BiPoly
    @assert var == 1 || var == 2 "bipoly_from_univariate: var must be 1 or 2, got $var"
    out = BiPoly()
    for (idx, c) in enumerate(coeffs_asc)
        cv = fp2(c)
        cv == 0 && continue
        e = idx - 1
        key = var == 1 ? (e, 0) : (0, e)
        out[key] = fp2(get(out, key, 0) + cv)
    end
    return out
end

function bipoly_add(a::BiPoly, b::BiPoly)::BiPoly
    out = copy(a)
    for (k, v) in b
        nv = fp2(get(out, k, 0) + v)
        if nv == 0
            delete!(out, k)
        else
            out[k] = nv
        end
    end
    return out
end

bipoly_neg(a::BiPoly)::BiPoly = BiPoly(k => fp2(-v) for (k, v) in a)
bipoly_sub(a::BiPoly, b::BiPoly)::BiPoly = bipoly_add(a, bipoly_neg(b))

function bipoly_mul(a::BiPoly, b::BiPoly)::BiPoly
    (bipoly_is_zero(a) || bipoly_is_zero(b)) && return bipoly_zero()
    out = BiPoly()
    for (ka, va) in a, (kb, vb) in b
        k = (ka[1] + kb[1], ka[2] + kb[2])
        nv = fp2(get(out, k, 0) + va * vb)
        if nv == 0
            delete!(out, k)
        else
            out[k] = nv
        end
    end
    return out
end

function bipoly_eval(a::BiPoly, t1_0::Int, t2_0::Int)::Int
    acc = 0
    for ((i, j), c) in a
        acc = fp2(acc + c * powermod(t1_0, i, P_GLOBAL2[]) * powermod(t2_0, j, P_GLOBAL2[]))
    end
    return acc
end

# =============================================================================
#  PART 2: RFun2 -- elements of F_p(t1,t2). num is an expanded BiPoly; den is
#  a FACTORED multiset of BiPoly factors (Dict{BiPoly,Int} => exponent, never
#  containing the constant-1 polynomial as a key, exponents always > 0 --
#  DenFactors() / empty Dict means den == 1). See header "SCOPE /
#  LIMITATIONS" for the rationale. Every operation below is exact; only the
#  REPRESENTATION of the denominator changed relative to a naive "den::BiPoly"
#  version, not the field semantics.
# =============================================================================

const DenFactors = Dict{BiPoly,Int}

denfactors_one()::DenFactors = DenFactors()
denfactors_is_one(d::DenFactors)::Bool = isempty(d)

# Merge two factor multisets (used by RFun2 * and RFun2 +/- for the
# denominator side): O(number of distinct factors), not O(their expanded
# degree) -- this is the whole point of the representation. Structural
# equality/hashing on BiPoly (a Dict) is what makes "same factor recurring
# across many elimination steps" collapse into an exponent bump instead of a
# fresh convolution.
function _denfactors_mul(d1::DenFactors, d2::DenFactors)::DenFactors
    out = copy(d1)
    for (f, e) in d2
        out[f] = get(out, f, 0) + e
    end
    return out
end

# Expand a factor multiset back into a single BiPoly. Only called where an
# expanded denominator is genuinely needed: mixed-denominator +/- (see
# below), bipoly_eval at the very end (symbolic_residual2_concrete, once per
# result coefficient), and pretty(). Never called on the a.den==b.den fast
# path of +/-, nor by * or by the DenFactors side of inv -- that's the fix.
function _denfactors_expand(d::DenFactors)::BiPoly
    out = bipoly_from_int(1)
    for (f, e) in d
        for _ in 1:e
            out = bipoly_mul(out, f)
        end
    end
    return out
end

function _denfactors_eval(d::DenFactors, t1_0::Int, t2_0::Int)::Int
    acc = 1
    for (f, e) in d
        acc = fp2(acc * powermod(bipoly_eval(f, t1_0, t2_0), e, P_GLOBAL2[]))
    end
    return acc
end

struct RFun2
    num::BiPoly
    den::DenFactors
end

# Build an RFun2 from an expanded BiPoly denominator. Used only at the
# leaves (constants, t1, t2, f(t1), f(t2)) and inside inv (where the OLD
# numerator, already expanded, becomes the new denominator) -- i.e. bounded,
# not called from inside the +,-,* hot path. A denominator that is just the
# constant 1 gets the empty DenFactors(); anything else becomes a single
# factor with exponent 1. No attempt is made to split a composite
# denominator into smaller pieces (no bivariate factorization is
# implemented), so repeated inv/* on an already-composite value will
# accumulate that composite as one opaque factor -- still correct, and still
# far cheaper than re-expanding it every arithmetic step.
function _rfun2_from_expanded(num::BiPoly, den_expanded::BiPoly)::RFun2
    @assert !bipoly_is_zero(den_expanded) "RFun2: zero denominator encountered -- construction bug upstream."
    if length(den_expanded) == 1 && haskey(den_expanded, (0,0)) && den_expanded[(0,0)] == 1
        return RFun2(num, denfactors_one())
    end
    return RFun2(num, DenFactors(den_expanded => 1))
end

RFun2(n::Integer) = RFun2(bipoly_from_int(n), denfactors_one())
RFun2_zero() = RFun2(bipoly_zero(), denfactors_one())
RFun2_one()  = RFun2(bipoly_from_int(1), denfactors_one())
RFun2_t1()   = RFun2(bipoly_t1(), denfactors_one())
RFun2_t2()   = RFun2(bipoly_t2(), denfactors_one())
RFun2_poly1(coeffs_asc::Vector{Int}) = RFun2(bipoly_from_univariate(coeffs_asc, 1), denfactors_one())
RFun2_poly2(coeffs_asc::Vector{Int}) = RFun2(bipoly_from_univariate(coeffs_asc, 2), denfactors_one())

is_zero(a::RFun2) = bipoly_is_zero(a.num)

@inline function _rfun2_check(a::RFun2)
    # Placeholder check point (mirrors the old "den nonzero" assertion). A
    # DenFactors multiset built exclusively through denfactors_one(),
    # _denfactors_mul, and _rfun2_from_expanded can't represent a zero
    # denominator (factors are only ever inserted from already-nonzero
    # BiPolys), so there is nothing further to assert here; kept as a named
    # no-op in case a future caller starts constructing DenFactors by hand.
    nothing
end

# a/da + b/db = (a*db + b*da) / (da*db). FAST PATH: when da==db (extremely
# common inside gauss_solve2 -- many terms being combined trace back to the
# same pivot's denominator), skip expansion entirely: numerator is a plain
# BiPoly add, denominator is unchanged. SLOW PATH (different denominators):
# the numerator side genuinely needs both denominators expanded (no way
# around that -- it's mixing coefficients from both fractions), but the
# denominator side is still just a DenFactors merge, never re-expanded on
# its own account.
function Base.:+(a::RFun2, b::RFun2)::RFun2
    _rfun2_check(a); _rfun2_check(b)
    if a.den == b.den
        return RFun2(bipoly_add(a.num, b.num), a.den)
    end
    da = _denfactors_expand(a.den)
    db = _denfactors_expand(b.den)
    RFun2(bipoly_add(bipoly_mul(a.num, db), bipoly_mul(b.num, da)), _denfactors_mul(a.den, b.den))
end
function Base.:-(a::RFun2, b::RFun2)::RFun2
    _rfun2_check(a); _rfun2_check(b)
    if a.den == b.den
        return RFun2(bipoly_sub(a.num, b.num), a.den)
    end
    da = _denfactors_expand(a.den)
    db = _denfactors_expand(b.den)
    RFun2(bipoly_sub(bipoly_mul(a.num, db), bipoly_mul(b.num, da)), _denfactors_mul(a.den, b.den))
end
Base.:-(a::RFun2) = RFun2(bipoly_neg(a.num), a.den)

# a*b: numerator is a plain BiPoly multiply (unavoidable -- two genuinely
# different polynomials with no structure in common to exploit here).
# Denominator is a DenFactors merge -- O(1) when a.den==b.den (e.g. squaring
# something in QuadExt's x.b*y.b), never an expansion.
Base.:*(a::RFun2, b::RFun2) = RFun2(bipoly_mul(a.num, b.num), _denfactors_mul(a.den, b.den))

# inv swaps num and den. The old denominator must be expanded here to become
# the new numerator -- but that expansion happens once, at the moment a
# reciprocal is actually requested, not once per +/- on every step leading
# up to it (which was the actual source of the blowup: gauss_solve2 calls
# inv once per pivot, not once per arithmetic op).
function Base.inv(a::RFun2)::RFun2
    @assert !is_zero(a) "RFun2 inv: division by zero"
    return _rfun2_from_expanded(a.num, _denfactors_expand(a.den))
end
Base.:/(a::RFun2, b::RFun2) = a * inv(b)

Base.:+(a::RFun2, n::Integer) = a + RFun2(n)
Base.:+(n::Integer, a::RFun2) = RFun2(n) + a
Base.:-(a::RFun2, n::Integer) = a - RFun2(n)
Base.:-(n::Integer, a::RFun2) = RFun2(n) - a
Base.:*(a::RFun2, n::Integer) = a * RFun2(n)
Base.:*(n::Integer, a::RFun2) = RFun2(n) * a

function pretty(a::RFun2)::String
    _pp(bp::BiPoly) = begin
        bipoly_is_zero(bp) && return "0"
        terms = String[]
        for (i, j) in sort(collect(keys(bp)); by = k -> (k[1] + k[2], k[1]))
            c = bp[(i, j)]
            m = i == 0 && j == 0 ? "1" : (i == 0 ? "t2^$j" : (j == 0 ? "t1^$i" : "t1^$i*t2^$j"))
            push!(terms, i == 0 && j == 0 ? "$c" : (c == 1 ? m : "$c*$m"))
        end
        join(terms, " + ")
    end
    ns = _pp(a.num)
    denfactors_is_one(a.den) && return ns
    # Present the factorization as a product of parenthesized factors raised
    # to their exponents, instead of silently re-expanding into one giant
    # bivariate denominator -- cheaper, and arguably more legible.
    dparts = String[]
    for (f, e) in sort(collect(a.den); by = fk -> string(sort(collect(fk[1]))))
        fs = _pp(f)
        push!(dparts, e == 1 ? "($fs)" : "($fs)^$e")
    end
    ds = join(dparts, "*")
    return "($ns) / ($ds)"
end


# =============================================================================
#  PART 3: QuadExt{B} -- generic quadratic ring extension B[w]/(w^2-disc),
#  for any base ring type B implementing +,-,*,is_zero,inv (inv MUST raise
#  on division by zero, per Claire's always-raise-exceptions convention --
#  RFun2's inv above does, and QuadExt{B}'s inv below does too, so the
#  property is preserved at every level of the tower).
#
#  Used TWICE, stacked (not as one flat 4-tuple struct): once with B=RFun2
#  (adjoining w1, disc=f(t1)) to get Level1, and again with B=Level1
#  (adjoining w2, disc=f(t2) lifted into Level1) to get Level2. All of the
#  +,-,*,inv logic is written ONCE here and does double duty at both levels,
#  instead of trial3_phi_symbolic.jl's Ft2 arithmetic being re-derived by
#  hand for a 4-dimensional case.
# =============================================================================

struct QuadExt{B}
    a::B
    b::B
    disc::B    # the "d" with w^2 = d
end

is_zero(x::QuadExt) = is_zero(x.a) && is_zero(x.b)

Base.:+(x::QuadExt{B}, y::QuadExt{B}) where {B} = QuadExt{B}(x.a + y.a, x.b + y.b, x.disc)
Base.:-(x::QuadExt{B}, y::QuadExt{B}) where {B} = QuadExt{B}(x.a - y.a, x.b - y.b, x.disc)
Base.:-(x::QuadExt{B}) where {B} = QuadExt{B}(-x.a, -x.b, x.disc)

function Base.:*(x::QuadExt{B}, y::QuadExt{B})::QuadExt{B} where {B}
    # (a1+b1 w)(a2+b2 w) = (a1 a2 + b1 b2 disc) + (a1 b2 + a2 b1) w   [w^2 -> disc]
    newa = x.a * y.a + (x.b * y.b) * x.disc
    newb = x.a * y.b + x.b * y.a
    QuadExt{B}(newa, newb, x.disc)
end

function Base.inv(x::QuadExt{B})::QuadExt{B} where {B}
    # (a+b w)^-1 = (a - b w) / (a^2 - b^2 disc)
    norm = x.a * x.a - (x.b * x.b) * x.disc
    @assert !is_zero(norm) "QuadExt inv: norm a^2-b^2*disc vanished identically -- should be impossible unless (a,b)==(0,0), since disc is not a square in the base field by construction (deg f odd). Indicates a construction bug upstream, not a genuine division by zero."
    ninv = inv(norm)
    QuadExt{B}(x.a * ninv, (-x.b) * ninv, x.disc)
end
Base.:/(x::QuadExt{B}, y::QuadExt{B}) where {B} = x * inv(y)

Base.:+(x::QuadExt{B}, n::Integer) where {B} = QuadExt{B}(x.a + n, x.b, x.disc)
Base.:+(n::Integer, x::QuadExt{B}) where {B} = x + n
Base.:-(x::QuadExt{B}, n::Integer) where {B} = QuadExt{B}(x.a - n, x.b, x.disc)
Base.:*(x::QuadExt{B}, n::Integer) where {B} = QuadExt{B}(x.a * n, x.b * n, x.disc)
Base.:*(n::Integer, x::QuadExt{B}) where {B} = x * n

const Level1 = QuadExt{RFun2}
const Level2 = QuadExt{Level1}

function pretty(x::Level1)::String
    is_zero(x.b) ? pretty(x.a) : "($(pretty(x.a))) + ($(pretty(x.b)))*w1"
end
function pretty(x::Level2)::String
    is_zero(x.b) ? pretty(x.a) : "($(pretty(x.a))) + ($(pretty(x.b)))*w2"
end

# =============================================================================
#  PART 4: RR basis -- verbatim combinatorics from trial3_phi_general.jl's
#  rr_basis / trial3_phi_symbolic.jl's rr_basis. Pure integer bookkeeping, no
#  field arithmetic. Keep in sync by hand if rr_basis ever changes upstream.
# =============================================================================

function rr_basis2(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    max_order = 2 * n_basis + 10
    candidates = Tuple{Int,Int,Int}[]
    for i in 0:max_order÷2
        push!(candidates, (2i, i, 0))
        push!(candidates, (2i+5, i, 1))
    end
    sort!(candidates, by = x -> x[1])
    seen = 0
    for (_, i, j) in candidates
        seen += 1
        push!(basis, (i, j))
        seen == n_basis && break
    end
    return basis
end

# x^i mod u(x), and x^i*y mod u(x) reduced to (r0,r1) -- verbatim from
# trial3_phi_symbolic.jl's build_xmodu_table / reduce_monomial_mod_u (pure
# Int arithmetic, no field-tower involvement -- u(x),v(x) are concrete).

function build_xmodu_table2(max_i::Int, u0::Int, u1::Int)::Tuple{Vector{Int},Vector{Int}}
    r0 = zeros(Int, max_i + 2)
    r1 = zeros(Int, max_i + 2)
    r0[1] = 1; r1[1] = 0
    if max_i + 1 >= 1
        r0[2] = 0; r1[2] = 1
    end
    for i in 2:(max_i+1)
        prev0, prev1 = r0[i], r1[i]
        r0[i+1] = fp2(-prev1*u0)
        r1[i+1] = fp2(prev0 - prev1*u1)
    end
    return (r0, r1)
end

function reduce_monomial_mod_u2(i::Int, j::Int, u0::Int, u1::Int, v0::Int, v1::Int,
                                 r0tab::Vector{Int}, r1tab::Vector{Int})::Tuple{Int,Int}
    a0, a1 = r0tab[i+1], r1tab[i+1]
    j == 0 && return (a0, a1)
    b0, b1 = r0tab[i+2], r1tab[i+2]
    r0 = fp2(v0*a0 + v1*b0)
    r1 = fp2(v0*a1 + v1*b1)
    return (r0, r1)
end

# =============================================================================
#  PART 5: generic polynomial-in-x helpers over any ring type T supporting
#  is_zero, +,-,*,inv (inv raising on zero). Written once, used with T=Level2
#  throughout this module -- mirrors the Ft2-specific poly helpers in
#  trial3_phi_symbolic.jl (ft2_poly_mul, ft2_poly_divmod_linear, etc.)
#  without re-deriving each one by hand for the new coefficient type.
# =============================================================================

function _strip_trailing(a::Vector{T}) where {T}
    n = length(a)
    while n > 1 && is_zero(a[n])
        n -= 1
    end
    return a[1:n]
end

function _poly_mul(a::Vector{T}, b::Vector{T}, zero_val::T) where {T}
    c = fill(zero_val, length(a) + length(b) - 1)
    for i in eachindex(a), j in eachindex(b)
        c[i+j-1] = c[i+j-1] + a[i]*b[j]
    end
    return c
end

function _poly_sub(a::Vector{T}, b::Vector{T}, zero_val::T) where {T}
    n = max(length(a), length(b))
    c = fill(zero_val, n)
    for i in eachindex(a); c[i] = c[i] + a[i]; end
    for i in eachindex(b); c[i] = c[i] - b[i]; end
    return c
end

# synthetic division: a = q*(x-r) + rem
function _poly_divmod_linear(a::Vector{T}, r::T, zero_val::T) where {T}
    n = length(a)
    (n == 1) && return (T[zero_val], a[1])
    q = Vector{T}(undef, n-1)
    acc = a[n]
    for i in (n-1):-1:1
        q[i] = acc
        acc = a[i] + r*acc
    end
    return (_strip_trailing(q), acc)
end

# divide by monic x^2 + U1*x + U0, U1/U0 already lifted to type T
function _poly_divmod_monic_deg2(a::Vector{T}, U1::T, U0::T, zero_val::T) where {T}
    n = length(a)
    if n < 3
        r0 = n >= 1 ? a[1] : zero_val
        r1 = n >= 2 ? a[2] : zero_val
        return (T[zero_val], r0, r1)
    end
    buf = copy(a)
    for i in n:-1:3
        c = buf[i]
        is_zero(c) && continue
        buf[i-1] = buf[i-1] - c*U1
        buf[i-2] = buf[i-2] - c*U0
    end
    r0 = buf[1]; r1 = buf[2]
    q = buf[3:n]
    return (_strip_trailing(q), r0, r1)
end

function _poly_mod_by_modulus(a::Vector{T}, m::Vector{T}, zero_val::T) where {T}
    dm = length(m) - 1
    @assert !(dm == 0 && is_zero(m[1])) "_poly_mod_by_modulus: zero modulus"
    buf = copy(a)
    lc_inv = inv(m[end])
    while length(buf) - 1 >= dm && !(length(buf) == 1 && is_zero(buf[1]))
        da = length(buf) - 1
        if is_zero(buf[end])
            pop!(buf); continue
        end
        c = buf[end]*lc_inv
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

function _poly_divrem(a::Vector{T}, b::Vector{T}, zero_val::T) where {T}
    b = _strip_trailing(copy(b))
    @assert !(length(b) == 1 && is_zero(b[1])) "_poly_divrem: division by zero polynomial"
    rem = _strip_trailing(copy(a))
    db = length(b) - 1
    lb_inv = inv(b[end])
    q = fill(zero_val, max(length(rem) - db, 1))
    while !(length(rem) == 1 && is_zero(rem[1])) && length(rem) - 1 >= db
        dr = length(rem) - 1
        c = rem[end]*lb_inv
        shift = dr - db
        q[shift+1] = q[shift+1] + c
        for i in 0:db
            rem[shift+i+1] = rem[shift+i+1] - c*b[i+1]
        end
        rem = _strip_trailing(rem)
    end
    return (_strip_trailing(q), rem)
end

function _pad(a::Vector{T}, n::Int, zero_val::T) where {T}
    length(a) >= n && return copy(a)
    out = fill(zero_val, n)
    out[1:length(a)] .= a
    return out
end

# extended Euclid, generic over T -- inverts `a` modulo `m`.
function _poly_invmod_by_modulus(a::Vector{T}, m::Vector{T}, zero_val::T, one_val::T) where {T}
    @assert !(length(a) == 1 && is_zero(a[1])) "_poly_invmod_by_modulus: input reduced to 0 mod modulus -- not invertible (shares a common factor with the modulus, or is identically 0)."
    old_r, r = copy(m), copy(a)
    old_s, s = T[zero_val], T[one_val]
    while !(length(r) == 1 && is_zero(r[1]))
        q, rem = _poly_divrem(old_r, r, zero_val)
        old_r, r = r, rem
        qs = _poly_mul(q, s, zero_val)
        new_s = _poly_sub(_pad(old_s, length(qs), zero_val), qs, zero_val)
        old_s, s = s, _strip_trailing(new_s)
    end
    @assert length(old_r) == 1 "_poly_invmod_by_modulus: gcd has degree > 0 -- inputs are not coprime, not invertible."
    ginv = inv(old_r[1])
    return _strip_trailing([c*ginv for c in old_s])
end

function _poly_mulmod_by_modulus(a::Vector{T}, b::Vector{T}, m::Vector{T}, zero_val::T) where {T}
    prod = _poly_mul(a, b, zero_val)
    return _poly_mod_by_modulus(prod, m, zero_val)
end

# =============================================================================
#  PART 6: Gaussian elimination, generic over T -- (K+2)x(K+2) system,
#  "pivot on first nonzero" (no notion of numerical size over a field).
#  Mirrors trial3_phi_symbolic.jl's gauss_solve exactly, parametrized.
# =============================================================================

function gauss_solve2(A::Matrix{T}, rhs::Vector{T}) where {T}
    n = length(rhs)
    @assert size(A) == (n, n)
    M = copy(A)
    b = copy(rhs)
    for col in 1:n
        piv = findfirst(r -> !is_zero(M[r, col]), col:n)
        @assert piv !== nothing "gauss_solve2: matrix is singular (no nonzero pivot in column $col) -- this anchor/basis/u(x) configuration doesn't give a well-posed phi as a rational-function identity in (t1,t2). Try different fixed anchors or a different u(x)."
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
    x = Vector{T}(undef, n)
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
#  PART 7: the construction proper.
# =============================================================================

struct SymbolicResidualResult2
    K::Int
    u_RS::Vector{Level2}   # ascending coeffs of residual u_RS(x; t1,t2), monic.
    v_RS::Vector{Level2}   # ascending coeffs of residual v_RS(x; t1,t2).
    deg_E::Int
    deg_Y::Int
    n_len_before_divide::Int
end

"""
    symbolic_residual2(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p) -> SymbolicResidualResult2

Fixes anchors 1..K-2 to `fixed_anchors` (concrete (px,py) pairs) and leaves
anchors K-1, K symbolic: (t1,w1) with w1^2=f(t1), and (t2,w2) with
w2^2=f(t2), t1/t2 independent indeterminates. Builds and solves the
(K+2)x(K+2) linear system for phi's coefficients over
Level2 = QuadExt{QuadExt{RFun2}} (see header), forms
N(x) = E(x)^2 - f(x)*Y(x)^2, divides out all K anchor factors (the K-2 fixed
ones plus (x-t1) and (x-t2)) and u(x), and returns the residual pair
(u_RS(x;t1,t2), v_RS(x;t1,t2)) with coefficients genuinely in Level2.

Use symbolic_residual2_concrete to evaluate at real (t1_0,y1_0),(t2_0,y2_0)
and get a plain F_p result.
"""
function symbolic_residual2(K::Int, fixed_anchors, u0::Int, u1::Int, v0::Int, v1::Int,
                             F_POLY_ASC::Vector{Int}, p::Int)::SymbolicResidualResult2

    @assert K >= 2 "symbolic_residual2: need K>=2 (the last two anchors are symbolic)"
    @assert length(fixed_anchors) == K - 2 "symbolic_residual2: need exactly K-2=$(K-2) fixed anchors, got $(length(fixed_anchors))"
    P_GLOBAL2[] = p

    for i in 1:length(fixed_anchors), j in (i+1):length(fixed_anchors)
        @assert fixed_anchors[i] != fixed_anchors[j] "symbolic_residual2: fixed anchors $i and $j coincide ($(fixed_anchors[i])) -- tangency (m=2) is not supported here. See header SCOPE note."
    end

    nb = K + 3
    basis = rr_basis2(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    @assert y_idx !== nothing "symbolic_residual2: no y-monomial in RR basis for nb=$nb"

    # --- build the Level1/Level2 tower's fixed data (discriminants, 0/1) ---
    f1_disc    = RFun2_poly1(F_POLY_ASC)                          # f(t1) in F_p(t1,t2)
    zero_L1    = QuadExt{RFun2}(RFun2_zero(), RFun2_zero(), f1_disc)
    one_L1     = QuadExt{RFun2}(RFun2_one(),  RFun2_zero(), f1_disc)
    f2_disc_L1 = QuadExt{RFun2}(RFun2_poly2(F_POLY_ASC), RFun2_zero(), f1_disc)  # f(t2), lifted into Level1
    zero_L2    = QuadExt{Level1}(zero_L1, zero_L1, f2_disc_L1)
    one_L2     = QuadExt{Level1}(one_L1,  zero_L1, f2_disc_L1)

    lift_int_L1(n::Integer)::Level1 = QuadExt{RFun2}(RFun2(n), RFun2_zero(), f1_disc)
    lift_int_L2(n::Integer)::Level2 = QuadExt{Level1}(lift_int_L1(n), zero_L1, f2_disc_L1)

    t1_L2 = QuadExt{Level1}(QuadExt{RFun2}(RFun2_t1(), RFun2_zero(), f1_disc), zero_L1, f2_disc_L1)
    w1_L2 = QuadExt{Level1}(QuadExt{RFun2}(RFun2_zero(), RFun2_one(), f1_disc), zero_L1, f2_disc_L1)
    t2_L2 = QuadExt{Level1}(QuadExt{RFun2}(RFun2_t2(), RFun2_zero(), f1_disc), zero_L1, f2_disc_L1)
    w2_L2 = QuadExt{Level1}(zero_L1, one_L1, f2_disc_L1)

    eval_monomial2(px::Level2, py::Level2, i::Int, j::Int)::Level2 = begin
        v = one_L2
        for _ in 1:i
            v = v * px
        end
        j == 1 && (v = v * py)
        v
    end

    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]
    @assert length(other_idx) == n_unknowns

    A   = Matrix{Level2}(undef, n_unknowns, n_unknowns)
    rhs = Vector{Level2}(undef, n_unknowns)

    anchor_pts = Vector{Tuple{Level2,Level2}}(undef, K)
    for a in 1:(K-2)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (lift_int_L2(px_raw), lift_int_L2(py_raw))
    end
    anchor_pts[K-1] = (t1_L2, w1_L2)
    anchor_pts[K]   = (t2_L2, w2_L2)

    # -- rows 1..K: anchor equations --
    for a in 1:K
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = eval_monomial2(px, py, bi, bj)
        end
        bi_n, bj_n = basis[y_idx]
        rhs[a] = -eval_monomial2(px, py, bi_n, bj_n)
    end

    # -- rows K+1, K+2: Mumford conditions phi(x,v(x)) mod u(x) == 0 --
    # Purely x-side/concrete, computed once via build_xmodu_table2, then
    # lifted into Level2 as constants.
    max_basis_i = maximum(bi for (bi,_) in basis)
    r0tab, r1tab = build_xmodu_table2(max_basis_i + 1, u0, u1)

    row0 = K + 1
    row1 = K + 2
    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        rr0, rr1 = reduce_monomial_mod_u2(bi, bj, u0, u1, v0, v1, r0tab, r1tab)
        A[row0, col] = lift_int_L2(rr0)
        A[row1, col] = lift_int_L2(rr1)
    end
    bi_n, bj_n = basis[y_idx]
    rn0, rn1 = reduce_monomial_mod_u2(bi_n, bj_n, u0, u1, v0, v1, r0tab, r1tab)
    rhs[row0] = lift_int_L2(fp2(-rn0))
    rhs[row1] = lift_int_L2(fp2(-rn1))

    # -- solve --
    c = gauss_solve2(A, rhs)   # c[col] corresponds to other_idx[col]

    coeffs_out = Vector{Level2}(undef, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c[col]
    end
    coeffs_out[y_idx] = one_L2

    # -- split into E(x) (y-free part) and Y(x) (coefficient of y) --
    max_i_E = maximum((bi for (bi,bj) in basis if bj == 0), init=0)
    max_i_Y = maximum((bi for (bi,bj) in basis if bj == 1), init=-1)
    E = fill(zero_L2, max_i_E + 1)
    Y = max_i_Y >= 0 ? fill(zero_L2, max_i_Y + 1) : Level2[]
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

    # -- N(x) = E(x)^2 - f(x)*Y(x)^2, genuinely Level2-valued. No assertion
    #    that this collapses to anything smaller (see
    #    trial3_phi_symbolic.jl's "WHY THE OUTPUT DOES NOT COLLAPSE"
    #    discussion; identical reasoning applies here for two symbolic
    #    anchors instead of one -- N(x) is guaranteed a polynomial in x, not
    #    guaranteed to live in any proper subring of Level2).
    Esq = _poly_mul(E, E, zero_L2)
    Ysq = isempty(Y) ? Level2[zero_L2] : _poly_mul(Y, Y, zero_L2)
    F_asc_L2 = [lift_int_L2(c) for c in F_POLY_ASC]
    fY2 = _poly_mul(Ysq, F_asc_L2, zero_L2)
    Nx  = _poly_sub(Esq, fY2, zero_L2)
    Nx  = _strip_trailing(Nx)
    n_len_before_divide = length(Nx)

    # -- divide out ALL K anchor factors (K-2 fixed, plus (x-t1),(x-t2)) --
    cur = Nx
    anchor_factors = Level2[lift_int_L2(px_raw) for (px_raw, _) in fixed_anchors]
    push!(anchor_factors, t1_L2)
    push!(anchor_factors, t2_L2)
    for (a, r) in enumerate(anchor_factors)
        cur, remv = _poly_divmod_linear(cur, r, zero_L2)
        @assert is_zero(remv) "symbolic_residual2: dividing out anchor $a's factor left a nonzero remainder -- N(x) doesn't actually vanish at this anchor as a rational-function identity in (t1,t2). Check u0,u1,v0,v1 and the fixed anchor coordinates are consistent with each other and with this K."
    end

    # -- divide out u(x) = x^2 + u1 x + u0 --
    U1_L2 = lift_int_L2(u1); U0_L2 = lift_int_L2(u0)
    cur, r0f, r1f = _poly_divmod_monic_deg2(cur, U1_L2, U0_L2, zero_L2)
    @assert is_zero(r0f) && is_zero(r1f) "symbolic_residual2: dividing N(x) by u(x)=x^2+$(u1)x+$(u0) left nonzero remainder -- phi doesn't actually vanish on the Mumford divisor as a rational-function identity."

    cur = _strip_trailing(cur)
    @assert !(length(cur) == 1 && is_zero(cur[1])) "symbolic_residual2: residual collapsed to the zero polynomial after dividing out all known factors -- degenerate configuration (mirrors phi_residual_general!'s n_fail_resid_degenerate)."

    # -- normalize to monic --
    lc = cur[end]
    if !is_zero(lc - one_L2)
        inv_lc = inv(lc)
        cur = [c * inv_lc for c in cur]
    end
    u_RS = cur

    # -- v_RS(x) = -E(x) * Y(x)^-1 mod u_RS(x), all over Level2 --
    if deg_Y < 0 || all(is_zero, Y)
        @assert false "symbolic_residual2: Y(x) is identically zero -- phi has no y-term, so v_RS cannot be recovered via Y^-1 (mirrors phi_residual_general!'s implicit assumption that Y is invertible mod u_RS; a genuinely y-free phi is a degenerate configuration outside this module's scope)."
    end
    negE = [-c for c in E]
    negE_mod  = _poly_mod_by_modulus(negE, u_RS, zero_L2)
    Y_mod     = _poly_mod_by_modulus(Y, u_RS, zero_L2)
    Y_inv_mod = _poly_invmod_by_modulus(Y_mod, u_RS, zero_L2, one_L2)
    v_RS      = _poly_mulmod_by_modulus(negE_mod, Y_inv_mod, u_RS, zero_L2)
    v_RS      = _strip_trailing(v_RS)

    return SymbolicResidualResult2(K, u_RS, v_RS, deg_E, deg_Y, n_len_before_divide)
end

"""
    symbolic_residual2_concrete(K, fixed_anchors, u0,u1,v0,v1, F_POLY_ASC, p,
                                 t1_0, y1_0, t2_0, y2_0) -> (Vector{Int}, Vector{Int})

Plugs in real curve points (t1_0,y1_0) and (t2_0,y2_0) for the two symbolic
anchors and collapses the Level2-valued u_RS, v_RS down to plain F_p. This is
the ONLY point in the pipeline where the y-branches are chosen. Should agree
with running trial3_phi_general.jl's build_phi_general!/phi_residual_general!
directly with (t1_0,y1_0) and (t2_0,y2_0) as the last two concrete anchors --
NOT YET CHECKED numerically in this environment (see header), please verify
before trusting this for real work.
"""
function symbolic_residual2_concrete(K::Int, fixed_anchors, u0::Int, u1::Int, v0::Int, v1::Int,
                                      F_POLY_ASC::Vector{Int}, p::Int,
                                      t1_0::Int, y1_0::Int, t2_0::Int, y2_0::Int)::Tuple{Vector{Int},Vector{Int}}
    P_GLOBAL2[] = p

    @assert fp2(t1_0) != fp2(t2_0) "symbolic_residual2_concrete: t1_0 == t2_0 mod p -- the two symbolic anchors would coincide at this evaluation point, which is outside this module's scope (see SCOPE: anchors pairwise distinct)."
    f_t1_0 = fp2(sum(c * powermod(t1_0, i-1, p) for (i, c) in enumerate(F_POLY_ASC)))
    @assert fp2(y1_0^2) == f_t1_0 "symbolic_residual2_concrete: y1_0^2 != f(t1_0) mod p -- (t1_0,y1_0) is not a point on the curve."
    f_t2_0 = fp2(sum(c * powermod(t2_0, i-1, p) for (i, c) in enumerate(F_POLY_ASC)))
    @assert fp2(y2_0^2) == f_t2_0 "symbolic_residual2_concrete: y2_0^2 != f(t2_0) mod p -- (t2_0,y2_0) is not a point on the curve."

    res = symbolic_residual2(K, fixed_anchors, u0, u1, v0, v1, F_POLY_ASC, p)
    P_GLOBAL2[] = p   # symbolic_residual2 also sets this; re-assert post-call for clarity

    eval_rfun2(x::RFun2)::Int = begin
        numv = bipoly_eval(x.num, t1_0, t2_0)
        denv = _denfactors_eval(x.den, t1_0, t2_0)
        fp2(numv * fpinv2(denv))
    end
    eval_L1(x::Level1)::Int = fp2(eval_rfun2(x.a) + eval_rfun2(x.b) * y1_0)
    eval_L2(x::Level2)::Int = fp2(eval_L1(x.a) + eval_L1(x.b) * y2_0)

    combine(coeffs::Vector{Level2}) = begin
        out = [eval_L2(c) for c in coeffs]
        n = length(out)
        while n > 1 && out[n] == 0
            n -= 1
        end
        out[1:n]
    end

    return (combine(res.u_RS), combine(res.v_RS))
end

# =============================================================================
#  PART 8: reasonable, non-spammy printing.
# =============================================================================

function print_symbolic_residual2(res::SymbolicResidualResult2; io::IO=stdout)
    println(io, "=== Symbolic residual (2 symbolic anchors), K=$(res.K) (anchors K-1,K symbolic; anchors 1..$(res.K-2) fixed) ===")
    println(io, "deg(E)=$(res.deg_E)  deg(Y)=$(res.deg_Y)  deg(N) before dividing out known factors = $(res.n_len_before_divide - 1)")
    println(io, "u_RS(x; t1,t2)  [monic, deg $(length(res.u_RS)-1)]:")
    for (i, c) in enumerate(res.u_RS)
        is_zero(c) && continue
        e = i - 1
        label = e == 0 ? "const " : "x^$e   "
        println(io, "    $label:  $(pretty(c))")
    end
    println(io, "v_RS(x; t1,t2)  [deg $(length(res.v_RS)-1)]:")
    for (i, c) in enumerate(res.v_RS)
        is_zero(c) && continue
        e = i - 1
        label = e == 0 ? "const " : "x^$e   "
        println(io, "    $label:  $(pretty(c))")
    end
end

"""
    print_symbolic_residual2_concrete(K, t1_0,y1_0,t2_0,y2_0, u_RS_concrete, v_RS_concrete; io=stdout)

Prints the F_p-valued residual pair from `symbolic_residual2_concrete`.
"""
function print_symbolic_residual2_concrete(K::Int, t1_0::Int, y1_0::Int, t2_0::Int, y2_0::Int,
                                            u_RS_concrete::Vector{Int}, v_RS_concrete::Vector{Int};
                                            io::IO=stdout)
    println(io, "=== Symbolic residual (concrete), K=$K, anchors K-1,K evaluated at (t1_0,y1_0)=($t1_0,$y1_0), (t2_0,y2_0)=($t2_0,$y2_0) ===")
    println(io, "u_RS(x)  [monic, deg $(length(u_RS_concrete)-1)]:  $u_RS_concrete")
    println(io, "v_RS(x)  [deg $(length(v_RS_concrete)-1)]:  $v_RS_concrete")
end

end # module PhiSymbolic2
