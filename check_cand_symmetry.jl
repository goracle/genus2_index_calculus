#!/usr/bin/env julia
#
# Follow-up diagnostic: Fu0..Fv1 are NOT swap-symmetric as a 4-variable
# system (confirmed). But the *eliminated* polynomials cand1, cand2 --
# the degree-9 and degree-10 polys in (t1,t2) that come out of
# `eliminate(Iuv, [w1,w2])` -- are a different object. Elimination can
# produce a symmetric result even from an asymmetric ideal, e.g. if the
# variety being projected onto is itself symmetric. Check that directly.
#
# This tells us whether the observed mirrored factor-base hits are:
#   (a) a genuine symmetry of cand1 in (t1,t2) -- in which case a (s,q)
#       rewrite of JUST the eliminated polynomial (not the full ideal)
#       is the right move, or
#   (b) purely an artifact of scanning one shared factor-base pool for
#       both the t1-role and the t2-role -- in which case the fix is in
#       the search loop, not in the algebra at all.

using Oscar

const p = 2371157
F = GF(p)

R, (w1, w2, t2, t1) = polynomial_ring(F, ["w1", "w2", "t2", "t1"])
swap_map = hom(R, R, [w2, w1, t1, t2])
swap(f) = swap_map(f)

curve1 = w1^2 - (t1^5 + t1 + 2)
curve2 = w2^2 - (t2^5 + t2 + 2)

D1 = t1^4 + 1869462*t1^3 + 1408746*t1^2 + 381595*t1 + 1827639
u1x0 = (76373*t1 + 1618225)*w1 + (463294*t1^4 + 1979687*t1^3 + 2039297*t1^2 + 1766020*t1 + 1466684)
u1x1 = (1178440*t1 + 76373)*w1 + (934731*t1^4 + 444430*t1^3 + 9875*t1^2 + 875375*t1 + 2041555)

Dv1 = t1^6 + 433036*t1^5 + 465199*t1^4 + 992136*t1^3 + 2332305*t1^2 + 554329*t1 + 1131637
v1x0 = (773065*t1^3 + 1247291*t1^2 + 2145997*t1 + 476917)*w1 +
       (1147392*t1^6 + 433228*t1^5 + 1812819*t1^4 + 2250585*t1^3 + 1416169*t1^2 + 624698*t1 + 2306090)
v1x1 = (519886*t1^3 + 504619*t1^2 + 758402*t1 + 13640)*w1 +
       (1781937*t1^6 + 304248*t1^5 + 1349490*t1^4 + 56951*t1^3 + 1916786*t1^2 + 208447*t1 + 176607)

D2 = t2^4 + 1773894*t2^3 + 1467*t2^2 + 2220726*t2 + 1449522
u2x0 = (76820*t2 + 1538127)*w2 + (1889274*t2^4 + 1720450*t2^3 + 1810757*t2^2 + 331956*t2 + 712643)
u2x1 = (1039068*t2 + 76820)*w2 + (886947*t2^4 + 442158*t2^3 + 801138*t2^2 + 1482032*t2 + 1152246)

Dv2 = t2^6 + 289684*t2^5 + 1450050*t2^4 + 1456351*t2^3 + 1812180*t2^2 + 2251389*t2 + 161448
v2x0 = (500276*t2^3 + 1901238*t2^2 + 644639*t2 + 1530220)*w2 +
       (2332747*t2^6 + 2126826*t2^5 + 1925741*t2^4 + 2296926*t2^3 + 1706749*t2^2 + 438582*t2 + 1647282)
v2x1 = (1488308*t2^3 + 280825*t2^2 + 143870*t2 + 535109)*w2 +
       (1851623*t2^6 + 904489*t2^5 + 1077359*t2^4 + 1072976*t2^3 + 2218875*t2^2 + 947498*t2 + 1259148)

function coeff_equal(num1, den1, num2, den2)
    return num1*den2 - num2*den1
end

Fu0 = coeff_equal(u1x0, D1, u2x0, D2)
Fu1 = coeff_equal(u1x1, D1, u2x1, D2)
Fv0 = coeff_equal(v1x0, Dv1, v2x0, Dv2)
Fv1 = coeff_equal(v1x1, Dv1, v2x1, Dv2)

Iuv = ideal(R, [Fu0, Fu1, Fv0, Fv1, curve1, curve2])

println("Eliminating w1, w2 ...")
It = eliminate(Iuv, [w1, w2])
gs = gens(It)
println("Got ", length(gs), " elimination polynomials.")
println()

for (i, g) in enumerate(gs)
    gs_swapped = swap(g)
    diff_sym  = g - gs_swapped
    diff_anti = g + gs_swapped
    rel = if iszero(diff_sym)
        "SYMMETRIC (swap(cand) == cand)"
    elseif iszero(diff_anti)
        "ANTISYMMETRIC (swap(cand) == -cand)"
    else
        # check proportional (swap(g) == c*g for scalar c), which still
        # implies the same root set / same vanishing locus
        "NEITHER exactly -- checking scalar multiple / shared roots next"
    end
    println("cand$i (degree $(total_degree(g))): ", rel)
end
println()

# Regardless of exact polynomial identity, the thing that actually matters
# for the search is the ROOT SET: does (a,b) a root of cand1 imply (b,a)
# also a root of cand1 (or of cand2, or of the combined ideal It)? Check
# this directly and numerically for the reported hits, since that's what
# actually explains -- or fails to explain -- the mirrored output.

reported_pairs = [
    (1069899, 169735),
    (1667551, 1943240),
    (2353730, 1257061),
    (681089, 558545),
    (2178473, 1432318),
]

println("Checking root-set symmetry on the actual reported hits:")
for (a, b) in reported_pairs
    vals_ab = Dict(t1 => F(a), t2 => F(b))
    vals_ba = Dict(t1 => F(b), t2 => F(a))
    for (i, g) in enumerate(gs)
        v_ab = evaluate(g, collect(keys(vals_ab)), collect(values(vals_ab)))
        v_ba = evaluate(g, collect(keys(vals_ba)), collect(values(vals_ba)))
        println("  (t1,t2)=($a,$b): cand$i = ", v_ab, "   |   swapped ($b,$a): cand$i = ", v_ba)
    end
end
