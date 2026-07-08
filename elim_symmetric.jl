#!/usr/bin/env julia
#
# Symmetric-variable version of elim.jl.
#
# The (t1,w1) <-> (t2,w2) swap is a symmetry of the whole system (curves,
# Fu0/Fu1/Fv0/Fv1 all come in swap-conjugate pairs), which is exactly why
# elim.jl's factor-base search turns up matches in mirrored pairs
# (t1=a,t2=b) and (t1=b,t2=a). This script rewrites the problem in the
# symmetric functions
#
#     s   = t1 + t2       q   = t1*t2
#     sig = w1 + w2        pi  = w1*w2
#
# plus two antisymmetric "square-root" auxiliaries
#
#     dt = t1 - t2   (dt^2 = s^2 - 4q)
#     dw = w1 - w2   (dw^2 = sig^2 - 4*pi)
#
# so that the mirror-pair redundancy collapses: each swap-conjugate pair
# of solutions becomes ONE solution in (s,q,sig,pi), cutting the
# elimination-polynomial degree roughly in half and halving the factor
# base work.
#
# IMPORTANT: this script does the symmetrization USING Oscar's own
# polynomial arithmetic (ring homomorphism for the swap, then explicit
# substitution + reduction), not by hand-derived formulas. Every claimed
# symmetric identity is checked by assertion against random points before
# it's trusted. If an assert fails, that means my derivation above is
# wrong somewhere and needs to be fixed, not worked around.

using Oscar
using Random

const p = 2371157
F = GF(p)

################################################################################
# Original ring + swap automorphism
################################################################################

R, (w1, w2, t2, t1) = polynomial_ring(F, ["w1", "w2", "t2", "t1"])

# swap: w1<->w2, t1<->t2
swap_map = hom(R, R, [w2, w1, t1, t2])

swap(f) = swap_map(f)

################################################################################
# Curve + samples (identical to elim.jl)
################################################################################

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

################################################################################
# Sanity check: is this system ACTUALLY swap-conjugate-symmetric?
#
# NOTE: u1/v1 and u2/v2 were built from independent sampled data (Sample 1
# vs Sample 2), NOT literally by relabeling one curve point as the other,
# so Fu0/Fu1/etc are NOT expected to satisfy swap(Fu0) == +-Fu0 termwise.
# The symmetry that actually holds is at the SOLUTION level: if
# (t1,w1,t2,w2) solves the system then (t2,w2,t1,w1) generically does NOT
# solve the same labelled equations (Fu0 pairs "point 1's u-poly" against
# "point 2's u-poly" asymmetrically via D1 vs D2, u1x0 vs u2x0, etc).
#
# The mirrored (t1,t2)<->(t2,t1) factor-base hits in err2.txt are coming
# from the *factor base intersection step* (fb_t_pool is symmetric in the
# sense that both roles get searched), not from an algebraic symmetry of
# Fu0..Fv1 themselves. Let's confirm this computationally before doing
# anything else, since it changes what "symmetrizing" even means here.
################################################################################

println("Checking whether Fu0, Fu1, Fv0, Fv1 are swap-symmetric or swap-antisymmetric...")

Random.seed!(1)

function random_pt()
    return Dict(
        w1 => F(rand(0:p-1)), w2 => F(rand(0:p-1)),
        t1 => F(rand(0:p-1)), t2 => F(rand(0:p-1)),
    )
end

for (name, f) in [("Fu0",Fu0), ("Fu1",Fu1), ("Fv0",Fv0), ("Fv1",Fv1)]
    fs = swap(f)
    pt = random_pt()
    val_f  = evaluate(f,  collect(keys(pt)), collect(values(pt)))
    val_fs = evaluate(fs, collect(keys(pt)), collect(values(pt)))
    rel = if iszero(val_f - val_fs)
        "SYMMETRIC (swap(f) == f)"
    elseif iszero(val_f + val_fs)
        "ANTISYMMETRIC (swap(f) == -f)"
    else
        "NEITHER (no simple relation to swap(f))"
    end
    println("  ", name, ": ", rel)
end
println()
