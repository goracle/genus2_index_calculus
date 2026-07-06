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
