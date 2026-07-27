
println("===========================================================")
println("DEGREE-IN-W DIAGNOSTIC")
println("===========================================================")
println()

w_all = [wa1, wa2, wb1, wb2]
w_names = ["wa1", "wa2", "wb1", "wb2"]

function report_wdeg(label, g)
    degs = [degree(g, w) for w in w_all]
    println("  $label: total_degree=", total_degree(g),
            "  degree-in-(wa1,wa2,wb1,wb2)=", degs)
    return degs
end

println("--- Sample 1 per-coefficient num/den: degree in wa1, wa2 (should be <=1 each) ---")
for (i, (n, d)) in enumerate(zip(u1_num, u1_den))
    report_wdeg("u1_num[$i]", n)
    report_wdeg("u1_den[$i]", d)
end
for (i, (n, d)) in enumerate(zip(v1_num, v1_den))
    report_wdeg("v1_num[$i]", n)
    report_wdeg("v1_den[$i]", d)
end
println()

println("--- Sample 2 per-coefficient num/den: degree in wb1, wb2 (should be <=1 each) ---")
for (i, (n, d)) in enumerate(zip(u2_num, u2_den))
    report_wdeg("u2_num[$i]", n)
    report_wdeg("u2_den[$i]", d)
end
for (i, (n, d)) in enumerate(zip(v2_num, v2_den))
    report_wdeg("v2_num[$i]", n)
    report_wdeg("v2_den[$i]", d)
end
println()

println("--- Fu/Fv (post cross-multiplication): degree in each of wa1,wa2,wb1,wb2 ---")
all_ok = true
for (i, g) in enumerate(Fu)
    degs = report_wdeg("Fu$(i-1)", g)
    if any(d -> d > 1, degs)
        global all_ok = false
        println("    *** Fu$(i-1) EXCEEDS degree 1 in at least one w-variable ***")
    end
end
for (i, g) in enumerate(Fv)
    degs = report_wdeg("Fv$(i-1)", g)
    if any(d -> d > 1, degs)
        global all_ok = false
        println("    *** Fv$(i-1) EXCEEDS degree 1 in at least one w-variable ***")
    end
end
println()

if all_ok
    println("RESULT: every Fu/Fv generator is degree <=1 in EACH of wa1,wa2,wb1,wb2.")
    println("This is the exact precondition needed for iterated norm elimination")
    println("(each generator can be split as A + B*w_i with A,B free of w_i, and")
    println("the norm A^2 - B^2*f(t_i) eliminates w_i exactly, no reduction needed).")
else
    println("RESULT: at least one Fu/Fv generator exceeds degree 1 in some w-variable.")
    println("This means _tower_to_ring's recursion produced a w_i^2 (or higher) term")
    println("that was NEVER reduced using w_i^2 = f(t_i) before being stored as a")
    println("free-ring element. Norm elimination as originally proposed does NOT")
    println("apply directly to Fu/Fv as currently constructed -- the polynomials")
    println("must first be reduced modulo (wa1^2-f(a1), wa2^2-f(a2), wb1^2-f(b1),")
    println("wb2^2-f(b2)) to bring them back to degree <=1 in each w before a norm")
    println("step can be taken. See the reduction helper below.")
end
println()

################################################################################
# If degrees DO exceed 1: reduce each Fu/Fv generator modulo the four curve
# relations (w_i^2 - f(t_i)) to bring it back to affine-in-each-w form, then
# recheck degrees. This directly tests whether the higher-degree terms were
# "fake" (removable by the algebraic relation the ring doesn't know about)
# or genuinely irreducible content.
################################################################################

function reduce_mod_w_squares(g, w_list, f_list)
    # w_list[i]^2 -> f_list[i]  (f_list[i] is the univariate poly a_i^5+a_i+2
    # etc., already expressed in R). Repeatedly replace w_i^2 with f_list[i]
    # using exponent reduction on each variable independently: any monomial
    # w_i^k for k>=2 reduces via k -> k-2 replacing w_i^2 by f_list[i], i.e.
    # w_i^k = f_list[i]^(k div 2) * w_i^(k mod 2).
    R_local = parent(g)
    result = zero(R_local)
    for (mono, coeff_) in zip(monomials(g), coefficients(g))
        new_mono_coeff = coeff_
        new_mono = mono
        for (w, f) in zip(w_list, f_list)
            e = degree(new_mono, w)
            if e >= 2
                k = div(e, 2)
                r = e - 2*k
                # divide out w^e, multiply back w^r, multiply coeff by f^k
                new_mono = divexact(new_mono, w^e) * (r == 0 ? one(R_local) : w^r)
                new_mono_coeff = new_mono_coeff * f^k
            end
        end
        result += new_mono_coeff * new_mono
    end
    return result
end

if !all_ok
    println("--- Reducing Fu/Fv modulo (w_i^2 - f(t_i)) and rechecking degrees ---")
    f_list = [a1^5 + a1 + 2, a2^5 + a2 + 2, b1^5 + b1 + 2, b2^5 + b2 + 2]

    Fu_reduced_test = [reduce_mod_w_squares(g, w_all, f_list) for g in Fu]
    Fv_reduced_test = [reduce_mod_w_squares(g, w_all, f_list) for g in Fv]

    println("After reduction:")
    all_ok_after = true
    for (i, g) in enumerate(Fu_reduced_test)
        degs = report_wdeg("Fu$(i-1)_reduced", g)
        if any(d -> d > 1, degs); global all_ok_after = false; end
    end
    for (i, g) in enumerate(Fv_reduced_test)
        degs = report_wdeg("Fv$(i-1)_reduced", g)
        if any(d -> d > 1, degs); global all_ok_after = false; end
    end
    println()
    if all_ok_after
        println("RESULT: after reducing mod the curve relations, all generators ARE")
        println("degree <=1 in each w. Norm elimination applies to the REDUCED")
        println("generators (Fu_reduced_test / Fv_reduced_test), not the raw Fu/Fv.")
    else
        println("RESULT: even after reduction mod curve relations, some generator")
        println("still exceeds degree 1 in some w-variable. This means the excess")
        println("degree is NOT an artifact of unreduced w^2 terms -- it is genuine")
        println("polynomial content that norm elimination (a rank-2 construction)")
        println("cannot remove in one step. In that case, the obstruction is real:")
        println("iterated norms would need to be taken multiple times (norm of a")
        println("norm) or the degree pattern needs to be inspected term-by-term")
        println("to see whether SOME but not all w's are safely affine.")
    end
end

################################################################################
# ALTERNATIVE: decoupled construction via target variables.
#
# coeff_equal(num1,den1,num2,den2) = num1*den2 - num2*den1 forces BOTH
# samples' variables (a1,a2,wa1,wa2,b1,b2,wb1,wb2 -- 8 variables total)
# into a single generator, cross-multiplied together. That's the direct
# cause of the degree-32/48, tens-of-thousands-of-terms blowup: each
# cross-multiplied generator already mixes everything before
# groebner_basis/F4 gets a chance to work with anything smaller.
#
# Decoupling introduces one target variable per matched coefficient
# (U0,U1 for u_RS's x^0,x^1 coefficients; V0,V1 for v_RS's) and replaces
# each single 8-variable degree-32/48 equation with TWO equations, each
# touching only ONE sample's variables (5 variables: that sample's
# a/b-pair, its w-pair, and the shared target variable) at whatever
# degree that sample's own num/den carry individually (checked above in
# the per-sample size diagnostics -- confirm those are actually smaller
# before trusting this is a win, rather than assuming it).
#
# This does NOT change the underlying variety: U_i is just forced to
# equal both samples' i-th coefficient (in lowest terms), which is
# exactly what Fu/Fv's cross-multiplication was already asserting -- it
# only changes how that assertion is phrased algebraically, trading one
# dense 8-variable equation for two sparser 5-variable ones plus an
# extra variable to eliminate later (along with the w's).
#
# NOTE: unlike the "w-linearity/norm" idea some outside analysis
# suggested, this does not depend on any assumption about the degree of
# these polynomials in the w variables, so there's no risk of silently
# dropping terms -- it's a straightforward, always-valid algebraic
# substitution (introduce a variable, equate it to both sides).
################################################################################

R_dec, dec_gens = polynomial_ring(
    F,
    vcat(["wa1", "wa2", "wb1", "wb2", "a2", "a1", "b2", "b1"],
         ["U$i" for i in 0:(N_U_MATCH-1)],
         ["V$i" for i in 0:(length(v1_num)-1)])
)
wa1_d, wa2_d, wb1_d, wb2_d, a2_d, a1_d, b2_d, b1_d = dec_gens[1:8]
U_vars = dec_gens[9:(8+N_U_MATCH)]
V_vars = dec_gens[(9+N_U_MATCH):(8+N_U_MATCH+length(v1_num))]

curve_a1_d = wa1_d^2 - (a1_d^5 + a1_d + 2)
curve_a2_d = wa2_d^2 - (a2_d^5 + a2_d + 2)
curve_b1_d = wb1_d^2 - (b1_d^5 + b1_d + 2)
curve_b2_d = wb2_d^2 - (b2_d^5 + b2_d + 2)

# Re-map each sample's num/den (currently elements of R, built from
# t_gens_1=[a1,a2]/w_gens_1=[wa1,wa2] and t_gens_2=[b1,b2]/w_gens_2=
# [wb1,wb2]) into R_dec. Since R and R_dec share the same variable
# NAMES for wa1,wa2,wb1,wb2,a2,a1,b2,b1 (just with U0,U1,V0,V1 appended),
# this is a straightforward generator-for-generator substitution.
old_to_new = Dict(
    wa1 => wa1_d, wa2 => wa2_d, wb1 => wb1_d, wb2 => wb2_d,
    a2 => a2_d, a1 => a1_d, b2 => b2_d, b1 => b1_d,
)
remap(f) = evaluate(f, [old_to_new[g] for g in gens(R)])

u1_num_d = [remap(f) for f in u1_num]
u1_den_d = [remap(f) for f in u1_den]
u2_num_d = [remap(f) for f in u2_num]
u2_den_d = [remap(f) for f in u2_den]
v1_num_d = [remap(f) for f in v1_num]
v1_den_d = [remap(f) for f in v1_den]
v2_num_d = [remap(f) for f in v2_num]
v2_den_d = [remap(f) for f in v2_den]

# U_i * den == num, for each sample separately, for each matched
# coefficient i. (V_i likewise for v_RS.) This is what "num/den == U_i"
# means algebraically -- same content as coeff_equal, just not
# cross-multiplied against the other sample directly.
Fu_decoupled = Any[]
for (i, Uvar) in enumerate(U_vars)
    push!(Fu_decoupled, u1_num_d[i] - Uvar * u1_den_d[i])
    push!(Fu_decoupled, u2_num_d[i] - Uvar * u2_den_d[i])
end

Fv_decoupled = Any[]
for (i, Vvar) in enumerate(V_vars)
    push!(Fv_decoupled, v1_num_d[i] - Vvar * v1_den_d[i])
    push!(Fv_decoupled, v2_num_d[i] - Vvar * v2_den_d[i])
end

println("Decoupled construction (target variables U0,U1,V0,V1):")
for (i, g) in enumerate(Fu_decoupled)
    println("  Fu_decoupled[$i]: degree=", total_degree(g), "  terms=", length(terms(g)))
end
for (i, g) in enumerate(Fv_decoupled)
    println("  Fv_decoupled[$i]: degree=", total_degree(g), "  terms=", length(terms(g)))
end
println()

Iu_decoupled = ideal(R_dec, vcat(Fu_decoupled, [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]))
Iuv_decoupled = ideal(R_dec, vcat(Fu_decoupled, Fv_decoupled,
                                  [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]))

block_ordering_dec = degrevlex(dec_gens[1:4]) * degrevlex(dec_gens[5:end])





################################################################################
# norm_eliminate.jl
#
# Insert immediately after the DEGREE-IN-W DIAGNOSTIC block confirms
# all Fu/Fv are degree <=1 in each of wa1,wa2,wb1,wb2 (confirmed by your
# run). This replaces the entire Groebner-basis + eliminate() pipeline
# for Fu/Fv with four sequential exact norm (resultant) computations.
#
# split_linear(g, w) : g = P + Q*w  (P,Q free of w), EXACT, since g is
# degree <=1 in w by the diagnostic above -- no approximation, no
# reduction needed.
#
# norm_eliminate(g, w, f) : returns P^2 - Q^2*f, i.e. Res_w(g, w^2-f).
# This vanishes exactly when g vanishes AND w^2=f holds (either root),
# so V(norm_eliminate(g,w,f)) restricted to the curve w^2=f equals the
# projection of V(g, w^2-f) onto the w-free variables. Standard
# elimination-via-norm for a quadratic extension -- exact, not lossy,
# PROVIDED g is degree <=1 in w (confirmed above).
################################################################################

function split_linear(g, w)
    # g has degree <=1 in w (confirmed by diagnostic). Extract P (w^0
    # coefficient) and Q (w^1 coefficient) as elements not involving w.
    P = evaluate(g, [w], [zero(parent(g))])   # g with w set to 0 -> P
    Q = divexact(g - P, w)                    # (g - P)/w -> Q, exact since g-P is divisible by w
    return P, Q
end

function norm_eliminate(g, w, f)
    P, Q = split_linear(g, w)
    return P^2 - Q^2 * f
end

################################################################################
# layer_degree_check.jl
#
# Goal: measure polynomial size/degree AT EACH TOWER LAYER, before
# _tower_to_ring finishes flattening to the fully-reduced (num,den) pair.
# This tests GPT's specific claim: that taking the norm INSIDE the
# recursion (at level 1, before the final _base_frac_to_ring substitution
# into t1) gives smaller polynomials than taking it after full
# flattening (which is what norm_eliminate.jl did, and which exploded).
#
# Insert this in place of the existing tower_to_ring wrapper call, i.e.
# instrument _tower_to_ring itself to print degree/terms at each level,
# for one representative coefficient (res1.u_RS_coeffs[1]) rather than
# all of them, to keep this fast and readable.
################################################################################

# Instrumented copy of _tower_to_ring that prints size at each level
# instead of silently recursing. Uses the same logic as elim2.jl's
# _tower_to_ring (lines 209-227) verbatim, just with diagnostics added.
function _tower_to_ring_instrumented(val, level::Int, t_gens::Vector, w_gens::Vector, path::String="root")
    if level == 0
        n, d = _base_frac_to_ring(val, t_gens)
        println("  [level 0, $path] AFTER base_frac_to_ring (t-substitution): ",
                "num: degree=", total_degree(n), " terms=", length(terms(n)),
                "  den: degree=", total_degree(d), " terms=", length(terms(d)))
        return (n, d)
    end

    val_poly = data(val)
    c0 = coeff(val_poly, 0)
    c1 = coeff(val_poly, 1)

    n0, d0 = _tower_to_ring_instrumented(c0, level - 1, t_gens, w_gens, path * ".c0")
    n1, d1 = _tower_to_ring_instrumented(c1, level - 1, t_gens, w_gens, path * ".c1")

    wv = w_gens[level]
    num = n0 * d1 + n1 * d0 * wv
    den = d0 * d1
    num, den = _reduce_frac(num, den)

    println("  [level $level, $path] AFTER combining with w_gens[$level]: ",
            "num: degree=", total_degree(num), " terms=", length(terms(num)),
            "  den: degree=", total_degree(den), " terms=", length(terms(den)))

    return (num, den)
end

println("===========================================================")
println("PER-LAYER DEGREE TRACE (sample 1, u_RS_coeffs[1] only)")
println("===========================================================")
println()
n_test, d_test = _tower_to_ring_instrumented(res1.u_RS_coeffs[1], 2, t_gens_1, w_gens_1)
println()
println("Final (should match u1_num[1]/u1_den[1] from the main script): ",
        "num degree=", total_degree(n_test), " den degree=", total_degree(d_test))
println()

################################################################################
# Now test: take the norm at LEVEL 1 (i.e. eliminate wa2, the innermost/
# outermost w depending on convention -- here level=2 is outermost per
# the wrapper's level=c=2 call, level=1 is the c0/c1 split w.r.t. w_gens[1]
# = wa1) BEFORE doing the final t-substitution, vs. the current approach
# of flattening all the way to (num,den) in R and THEN norm-eliminating.
#
# Concretely: at level 1, val is c0(t1) + c1(t1)*w1, i.e. an element of
# K1 = R_t[w1]/(w1^2-f(t1)) -- but c0, c1 here are still elements of the
# RATIONAL FUNCTION FIELD R_t (fractions of polys in t1,t2), not yet
# substituted into the ring R. Taking the norm HERE means:
#
#   norm = c0^2 - c1^2 * f(t1)
#
# computed as a rational-function-field operation (numerator/denominator
# arithmetic in Fp(t1,t2)), THEN substituting t_gens at the very end --
# i.e. norm-then-substitute, instead of substitute-then-norm.
################################################################################

println("===========================================================")
println("Testing norm-BEFORE-substitution vs norm-AFTER-substitution")
println("===========================================================")
println()

# Get the level-1 c0, c1 split directly (one layer of recursion by hand,
# mirroring _tower_to_ring's own level==2 branch).
val2 = res1.u_RS_coeffs[1]
val2_poly = data(val2)
c0_at_lvl1 = coeff(val2_poly, 0)   # element of K1 (contains t1, w1)
c1_at_lvl1 = coeff(val2_poly, 1)   # element of K1 (contains t1, w1)

# c0_at_lvl1, c1_at_lvl1 are themselves elements of K1 = R_t[w1]/(w1^2-f(t1)),
# so split AGAIN to get down to R_t (rational function field) coefficients:
c0_poly = data(c0_at_lvl1)
c00 = coeff(c0_poly, 0)   # in R_t
c01 = coeff(c0_poly, 1)   # in R_t

c1_poly = data(c1_at_lvl1)
c10 = coeff(c1_poly, 0)   # in R_t
c11 = coeff(c1_poly, 1)   # in R_t

println("Level-1 rational-function-field pieces (before any ring substitution):")
for (label, v) in [("c00", c00), ("c01", c01), ("c10", c10), ("c11", c11)]
    num_deg = total_degree(numerator(v))
    den_deg = total_degree(denominator(v))
    println("  $label: numerator degree=$num_deg  denominator degree=$den_deg")
end
println()
println("(If these are small -- e.g. single-digit degree in t1,t2 -- then taking")
println("norms at THIS level, while everything is still a rational function of")
println("just t1,t2 with no w's substituted in yet, is much cheaper than doing")
println("it after _tower_to_ring has fully flattened to degree-16/24 polys in R.")
println("Compare these numbers to u1_num[1]'s degree=16 to see the ratio.)")

if false # dis too slow lmao, gets done with the first one but blows up
    println("===========================================================")
    println("NORM/RESULTANT ELIMINATION (no Groebner basis)")
    println("===========================================================")
    println()

    f_a1 = a1^5 + a1 + 2
    f_a2 = a2^5 + a2 + 2
    f_b1 = b1^5 + b1 + 2
    f_b2 = b2^5 + b2 + 2

    # Eliminate wa1, wa2, wb1, wb2 in sequence from each of Fu0, Fu1, Fv0, Fv1.
    # Order chosen to match elim2.jl's own elimination order (wb2, wb1, wa2, wa1)
    # for comparability, though for norm elimination the order is a free choice
    # (each step is an exact algebraic operation, not a search) and shouldn't
    # matter mathematically -- only for intermediate-expression-size bookkeeping.
    function eliminate_all_w(g)
        g = norm_eliminate(g, wb2, f_b2)
        println("    after eliminating wb2: total_degree=", total_degree(g), " terms=", length(terms(g)))
        g = norm_eliminate(g, wb1, f_b1)
        println("    after eliminating wb1: total_degree=", total_degree(g), " terms=", length(terms(g)))
        g = norm_eliminate(g, wa2, f_a2)
        println("    after eliminating wa2: total_degree=", total_degree(g), " terms=", length(terms(g)))
        g = norm_eliminate(g, wa1, f_a1)
        println("    after eliminating wa1: total_degree=", total_degree(g), " terms=", length(terms(g)))
        return g
    end

    println("--- Eliminating Fu0 ---")
    Ru0 = eliminate_all_w(Fu[1])
    println("--- Eliminating Fu1 ---")
    Ru1 = eliminate_all_w(Fu[2])
    println("--- Eliminating Fv0 ---")
    Rv0 = eliminate_all_w(Fv[1])
    println("--- Eliminating Fv1 ---")
    Rv1 = eliminate_all_w(Fv[2])

    println()
    println("Final relation polynomials in (a1,a2,b1,b2) only -- NO Groebner basis used:")
    for (label, g) in [("Ru0", Ru0), ("Ru1", Ru1), ("Rv0", Rv0), ("Rv1", Rv1)]
        println("  $label: total_degree=", total_degree(g), " terms=", length(terms(g)),
                "  vars=", vars(g))
    end
    println()

    # Sanity: confirm none of these are identically zero (that would mean
    # either a real algebraic degeneracy, or a bug in split_linear/norm_eliminate).
    for (label, g) in [("Ru0", Ru0), ("Ru1", Ru1), ("Rv0", Rv0), ("Rv1", Rv1)]
        if iszero(g)
            println("  *** WARNING: $label is IDENTICALLY ZERO after norm elimination ***")
        end
    end

    println()
    println("If nonzero, gcd(Ru0,Ru1,Rv0,Rv1) (in F[a1,a2,b1,b2]) is your candidate")
    println("relation-ideal generating set WITHOUT ever calling groebner_basis.")
    println("Compute pairwise gcds next -- cheap compared to everything above.")
end







