#!/usr/bin/env julia

using Oscar

################################################################################
#
#  Match symbolic residual divisors from two partial relations.
#
#  Unknowns:
#
#      (t1,w1)  on the curve
#      (t2,w2)  on the curve
#
#  We seek
#
#      u₁(x) = u₂(x)
#
#  and later verify
#
#      v₁(x) = v₂(x)
#
################################################################################

const p = 2371157

F = GF(p)

################################################################################
# Lex ordering:
#
#     w1 > w2 > t2 > t1
#
# so eliminating w1,w2 leaves equations in t1,t2.
################################################################################

R,(w1,w2,t2,t1) = polynomial_ring(
    F,
    ["w1","w2","t2","t1"]
)
################################################################################
# Curve
################################################################################

curve1 = w1^2 - (t1^5 + t1 + 2)
curve2 = w2^2 - (t2^5 + t2 + 2)

################################################################################
# Sample 1
################################################################################

D1 =
    t1^4 +
    1869462*t1^3 +
    1408746*t1^2 +
    381595*t1 +
    1827639

u1x0 =
    (76373*t1 + 1618225)*w1 +
    (
        463294*t1^4 +
        1979687*t1^3 +
        2039297*t1^2 +
        1766020*t1 +
        1466684
    )

u1x1 =
    (1178440*t1 + 76373)*w1 +
    (
        934731*t1^4 +
        444430*t1^3 +
        9875*t1^2 +
        875375*t1 +
        2041555
    )

Dv1 =
    t1^6 +
    433036*t1^5 +
    465199*t1^4 +
    992136*t1^3 +
    2332305*t1^2 +
    554329*t1 +
    1131637

v1x0 =
    (773065*t1^3 +
     1247291*t1^2 +
     2145997*t1 +
     476917)*w1 +
    (
        1147392*t1^6 +
        433228*t1^5 +
        1812819*t1^4 +
        2250585*t1^3 +
        1416169*t1^2 +
        624698*t1 +
        2306090
    )

v1x1 =
    (519886*t1^3 +
     504619*t1^2 +
     758402*t1 +
     13640)*w1 +
    (
        1781937*t1^6 +
        304248*t1^5 +
        1349490*t1^4 +
        56951*t1^3 +
        1916786*t1^2 +
        208447*t1 +
        176607
    )

################################################################################
# Sample 2
################################################################################

D2 =
    t2^4 +
    1773894*t2^3 +
    1467*t2^2 +
    2220726*t2 +
    1449522

u2x0 =
    (76820*t2 + 1538127)*w2 +
    (
        1889274*t2^4 +
        1720450*t2^3 +
        1810757*t2^2 +
        331956*t2 +
        712643
    )

u2x1 =
    (1039068*t2 + 76820)*w2 +
    (
        886947*t2^4 +
        442158*t2^3 +
        801138*t2^2 +
        1482032*t2 +
        1152246
    )

Dv2 =
    t2^6 +
    289684*t2^5 +
    1450050*t2^4 +
    1456351*t2^3 +
    1812180*t2^2 +
    2251389*t2 +
    161448

v2x0 =
    (500276*t2^3 +
     1901238*t2^2 +
     644639*t2 +
     1530220)*w2 +
    (
        2332747*t2^6 +
        2126826*t2^5 +
        1925741*t2^4 +
        2296926*t2^3 +
        1706749*t2^2 +
        438582*t2 +
        1647282
    )

v2x1 =
    (1488308*t2^3 +
     280825*t2^2 +
     143870*t2 +
     535109)*w2 +
    (
        1851623*t2^6 +
        904489*t2^5 +
        1077359*t2^4 +
        1072976*t2^3 +
        2218875*t2^2 +
        947498*t2 +
        1259148
    )

################################################################################
# Equality equations
################################################################################

function coeff_equal(num1,den1,num2,den2)
    return num1*den2 - num2*den1
end

Fu0 = coeff_equal(u1x0,D1,u2x0,D2)
Fu1 = coeff_equal(u1x1,D1,u2x1,D2)

Fv0 = coeff_equal(v1x0,Dv1,v2x0,Dv2)
Fv1 = coeff_equal(v1x1,Dv1,v2x1,Dv2)

################################################################################
# Build ideals
################################################################################

#
# U-only system.
#
Iu = ideal(R,[
    Fu0,
    Fu1,
    curve1,
    curve2
])

#
# Full Mumford system.
#
# This is the one I actually trust mathematically.
#
Iuv = ideal(R,[
    Fu0,
    Fu1,
    Fv0,
    Fv1,
    curve1,
    curve2
])

println()
println("Constructed symbolic systems.")
println("U equations:   ", ngens(Iu))
println("UV equations:  ", ngens(Iuv))
println("dim(Iu)  = ", dim(Iu))
println("dim(Iuv) = ", dim(Iuv))
println()



################################################################################
#
# Gröbner basis
#
################################################################################

println()
println("===========================================================")
println("Computing Groebner basis for U-system")
println("===========================================================")
println()

GBu = groebner_basis(Iu)

println("Basis has ", length(GBu), " elements.")
println()

for (i,g) in enumerate(GBu)

    println("--------------------------------------------------")
    println("g",i)
    println("--------------------------------------------------")
    println("variables = ", vars(g))
    println("degree    = ", total_degree(g))
    println("terms     = ", length(terms(g)))
    println()
    println(g)
    println()

end

################################################################################
#
# Repeat for the full Mumford system.
#
################################################################################

println()
println("===========================================================")
println("Computing Groebner basis for UV-system")
println("===========================================================")
println()

GBuv = groebner_basis(Iuv)

println("Basis has ", length(GBuv), " elements.")
println()

for (i,g) in enumerate(GBuv)

    println("--------------------------------------------------")
    println("g",i)
    println("--------------------------------------------------")
    println("variables = ", vars(g))
    println("degree    = ", total_degree(g))
    println("terms     = ", length(terms(g)))
    println()
    println(g)
    println()

end

################################################################################
#
# Look for elimination polynomials.
#
################################################################################

function uses_only_t(g)

    for v in vars(g)

        if v == w1 || v == w2
            return false
        end

    end

    return true

end

println()
println("===========================================================")
println("Polynomials involving only (t1,t2)")
println("===========================================================")
println()

pure = typeof(GBu[1])[]

for g in GBu

    if uses_only_t(g)

        push!(pure,g)

        println("--------------------------------")
        println("degree = ", total_degree(g))
        println("terms  = ", length(terms(g)))
        println(g)
        println()

    end

end

println()
println("Found ",length(pure)," elimination candidates.")
println()

################################################################################
#
# If we got at least two, inspect them.
#
################################################################################

if length(pure) >= 2

    println("First candidate:")
    println(pure[1])
    println()

    println("Second candidate:")
    println(pure[2])
    println()

end


################################################################################
#
# If the UV ideal is zero-dimensional, convert to lex.
#
################################################################################

for (i,f) in enumerate(gens(Iuv))
    println("eq $i: ", vars(f))
end

println("All variables:")
println(symbols(R))

for x in gens(R)
    J = ideal(vcat(gens(Iuv), [x]))
    println(x, " -> ", dim(J))
end

println(dim(ideal(curve1,curve2)))
println(dim(Iu))
println(dim(Iuv))



println()
println("===========================================================")
println("Eliminating w1, w2 directly from 1D system")
println("===========================================================")
println()

# Eliminates w1 and w2, leaving an ideal generated by polynomials in t1, t2
It = eliminate(Iuv, [w1, w2])

println("Found ", length(gens(It)), " elimination polynomials in (t1, t2).")
for (i, g) in enumerate(gens(It))
    println("\nCandidate $i (Degree $(total_degree(g))):")
    println(g)
end
################################################################################
#
# Look for a univariate polynomial.
#
################################################################################

function is_univariate_t1(f)

    for v in vars(f)

        if v != t1
            return false
        end

    end

    return true

end

function is_univariate_t1(f)

    for v in vars(f)

        if v != t1
            return false
        end

    end

    return true

end

println()
println("===========================================================")
println("Intersecting with Factor Base Candidates")
println("===========================================================")
println()

cand1 = gens(It)[1]
fb_size = round(Int, 3*sqrt(p))

using Random
Random.seed!(42)
fb_t_pool = shuffle(collect(0:p-1))[1:fb_size]

println("Generated a factor base pool of ", length(fb_t_pool), " t-coordinates.")

# 1. Define the true univariate ring over F
S, y = polynomial_ring(F, "y")

found_match = false

for alpha in fb_t_pool
    # Evaluate at t1 = alpha, leaving a polynomial conceptually only in t2
    f_multivariate = evaluate(cand1, [t1], [F(alpha)])
    
    # 2. Manually reconstruct it in the univariate ring S
    f_univariate = zero(S)
    for term in terms(f_multivariate)
        c = leading_coefficient(term)
        # exponent_vector returns an array of exponents for [w1, w2, t2, t1]
        # t2 is at index 3 in your ring R
        exp_t2 = exponent_vector(term, 1)[3] 
        f_univariate += c * y^exp_t2
    end
    
# 3. roots() returns a Vector{FqFieldElem}
    rt_vector = roots(f_univariate)
    
    if !isempty(rt_vector)
        for beta in rt_vector
            # Lift from the finite field to the integer ring ZZ, then cast to Int64
            beta_int = Int(lift(ZZ, beta))
            
            if beta_int in fb_t_pool
                println("Found a factor base match!")
                println("  t1 = ", alpha)
                println("  t2 = ", beta_int)
                global found_match = true
            end
        end
    end
end

if !found_match
    println("No mutual factor base matches found in this random sample.")
end

################################################################################
#
# Optional numerical solving.
#
################################################################################

println()
println("===========================================================")
println("Normal forms")
println("===========================================================")
println()

for g in Glex

    println("--------------------------------")
    println("leading monomial = ",leading_monomial(g))
    println(g)
    println()

end

################################################################################
#
# Verification helper.
#
################################################################################

function verify_candidate(t1v,w1v,t2v,w2v)

    vals = Dict(
        t1 => F(t1v),
        w1 => F(w1v),
        t2 => F(t2v),
        w2 => F(w2v),
    )

    println()

    println("Fu0 = ",evaluate(Fu0,vals))
    println("Fu1 = ",evaluate(Fu1,vals))
    println("Fv0 = ",evaluate(Fv0,vals))
    println("Fv1 = ",evaluate(Fv1,vals))
    println("C1  = ",evaluate(curve1,vals))
    println("C2  = ",evaluate(curve2,vals))

    println()

    ok =
        iszero(evaluate(Fu0,vals)) &&
        iszero(evaluate(Fu1,vals)) &&
        iszero(evaluate(Fv0,vals)) &&
        iszero(evaluate(Fv1,vals)) &&
        iszero(evaluate(curve1,vals)) &&
        iszero(evaluate(curve2,vals))

    println("Verified = ",ok)

    return ok

end

