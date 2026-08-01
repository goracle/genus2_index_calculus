using Serialization
using Oscar

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names
p = 2371157   # NOTE: pulled from hensel_verification.jls's stored `p` in the
              # last inspection -- confirm this still matches your current p
              # before trusting output; do not assume it's unchanged.

# Only these four determine d1-factor-base membership. wa1,wa2,wb1,wb2 and
# U0,U1,V0,V1 are allowed to live in an extension field and are NOT checked.
d1_var_names = [:a1, :a2, :b1, :b2]
d1_idx = [findfirst(==(v), gen_names) for v in d1_var_names]
any(isnothing, d1_idx) &&
    error("Could not find one of ", d1_var_names, " in gen_names=", gen_names,
          " -- variable order assumption is wrong, fix d1_var_names or check ",
          "witness_points.jls's actual gen_names before proceeding.")

const HEURISTIC_RADIUS = 1e-6  # SAME caveat as before: this must reflect
                                # HC.jl's actual achieved precision at these
                                # points, not an assumed value. Complex
                                # points here (not just real ones) still need
                                # an honest error radius for guess() to be
                                # trustworthy -- an enclosure that's too
                                # tight silently produces a wrong minimal
                                # polynomial, not a "no result" failure.
const MAXDEG = 12
const MAXBITS = 40

CC = ArbComplexField(128)
Qb = algebraic_closure(QQ)
Fp, _ = finite_field(p)  # NOTE: for degree-1 factor checking; extension
                          # fields would need Fp2/Fp3/... constructed
                          # separately if you later want to classify THOSE
                          # too, which this script does not attempt.

"""
    reduces_to_Fp(z::ComplexF64, p) -> (ok::Bool, root_mod_p::Union{Int,Nothing}, minpoly_or_nothing)

Attempt to identify z (real or complex) as an algebraic number via Nemo's
guess(), then factor its minimal polynomial mod p. Returns ok=true with the
matching root in F_p iff the minimal polynomial has a degree-1 factor mod p
-- i.e. iff z's algebraic value genuinely reduces to F_p at this prime, not
merely "z looks numerically close to some integer."

Raises (does not silently return ok=false) if guess() itself errors in an
unexpected way, so a guess() API problem doesn't get misreported as "this
point isn't in the factor base."
"""
function reduces_to_Fp(z::ComplexF64, p::Int)
    enclosure = CC(real(z), imag(z)) + CC("+/- $(HEURISTIC_RADIUS)", "+/- $(HEURISTIC_RADIUS)")
    local alg
    try
        alg = guess(Qb, enclosure, MAXDEG; maxbits = MAXBITS)
    catch e
        if occursin("No suitable algebraic number found", sprint(showerror, e))
            return (false, nothing, nothing)  # genuinely not found at this deg/bits -- not an error
        end
        rethrow(e)  # anything else is unexpected; surface it, don't swallow it
    end
    Qx, x = polynomial_ring(QQ, "x")
    mp = minpoly(Qx, alg)

    # Reduce mp's (rational, but should be integral after clearing
    # denominators for an algebraic integer -- if not, that's itself worth
    # knowing, not silently coercing) coefficients mod p and factor.
    Zx, xz = polynomial_ring(Fp, "x")
    coeffs_zz = Int.(numerator.(collect(coefficients(mp))))
    denoms = Int.(denominator.(collect(coefficients(mp))))
    all(==(1), denoms) ||
        error("minpoly ", mp, " has non-integer coefficients after guess() ",
              "-- z was not identified as an algebraic INTEGER. Reducing a ",
              "non-monic/non-integral minimal polynomial mod p needs more ",
              "care than this script does; inspect by hand.")
    mp_modp = Zx(coeffs_zz)

    fac = factor(mp_modp)
    for (factor_poly, _mult) in fac
        if degree(factor_poly) == 1
            # factor_poly = x - r (up to leading coeff); extract r
            r = -coeff(factor_poly, 0) // leading_coefficient(factor_poly)
            return (true, Int(lift(ZZ, Fp(r))), mp)
        end
    end
    return (false, nothing, mp)
end

println("Checking which witness points have a1,a2,b1,b2 all reducing to F_$p")
println("(the d1 factor-base condition). wa1,wa2,wb1,wb2,U0,U1,V0,V1 are NOT")
println("checked and may legitimately live in an extension field.")
println()

n_check = min(20, length(pts))  # small sample first -- guess() is not free,
                                  # confirm this works before running all 2457
d1_candidates = Int[]
for i in 1:n_check
    pt = pts[i]
    all_ok = true
    roots = Dict{Symbol,Int}()
    for (name, idx) in zip(d1_var_names, d1_idx)
        ok, root, mp = reduces_to_Fp(pt[idx], p)
        if !ok
            all_ok = false
            break
        end
        roots[name] = root
    end
    if all_ok
        push!(d1_candidates, i)
        println("point $i: d1 CANDIDATE -- ", roots)
    end
end
println()
println("$(length(d1_candidates)) / $n_check checked points have all of ",
        d1_var_names, " reducing to F_$p.")
println("If this is 0/$n_check, either none of the first $n_check points are")
println("d1 (plausible -- d1 is typically a small fraction of all witness")
println("points), or HEURISTIC_RADIUS/MAXDEG/MAXBITS need adjustment. Do not")
println("conclude \"the fix doesn't work\" from a single small sample without")
println("checking which of those it is.")
