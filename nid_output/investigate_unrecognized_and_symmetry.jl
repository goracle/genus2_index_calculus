using Serialization
using Oscar

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names
p = 2371157
d1_points = deserialize("d1_candidate_indices.jls")

x_var_names = [:a1, :a2, :b1, :b2]
x_idx = Dict(v => findfirst(==(v), gen_names) for v in x_var_names)

println("=" ^ 70)
println("PART 1: identify the 3 repeated unrecognized values via guess()")
println("=" ^ 70)

# The 3 representative values seen repeatedly in the unrecognized list.
# Pulled directly from the prior run's output, not re-derived here -- if a
# future run's unrecognized list looks different, these need updating by
# hand, this isn't computed dynamically from the classification step.
reps = ComplexF64[
    -0.7547515219522206 - 8.378903833553049e-5im,
    -0.7550769481713409 + 0.00018914653021348204im,
    0.8772862180016957 + 0.7448168350857688im,
]

CC = AcbField(128)
Qb = algebraic_closure(QQ)
Qx, x = polynomial_ring(QQ, "x")

for (i, z) in enumerate(reps)
    println("--- unrecognized value $i: $z ---")
    # First: is this just the known cubic's root, computed less accurately?
    # Compare directly against the cubic's real roots (computed exactly via
    # Nemo, not from HC.jl) at a much LOOSER tolerance than the classifier
    # used, before assuming this is a genuinely new algebraic value.
    Qx0, x0 = polynomial_ring(QQ, "x")
    cubic_roots_check = roots(CC, x0^3 - x0^2 + 1)
    best_dist = minimum(abs(z - ComplexF64(r)) for r in cubic_roots_check)
    println("  distance to nearest known cubic root: ", best_dist)
    if best_dist < 1e-3
        println("  -> LIKELY the known cubic root, computed at lower accuracy",
                " (consistent with a degraded/failed homotopy path at this",
                " witness point, not a new algebraic value). Re-solving or",
                " re-tracking this specific point would confirm.")
        println()
        continue
    end

    enclosure = CC(real(z), imag(z)) + CC("+/- 1e-4", "+/- 1e-4")
    found = false
    for (md, mb) in [(4, 20), (8, 40), (16, 60), (24, 100)]
        try
            alg = guess(Qb, enclosure, md, mb)
            mp = minpoly(Qx, alg)
            println("  found at maxdeg=$md, maxbits=$mb: degree ", Nemo.degree(mp),
                    ", minpoly: ", mp)
            # Check its behavior mod p too, while we're here.
            Fp, _ = finite_field(p)
            Fpx, xp = polynomial_ring(Fp, "x")
            coeffs_zz = Int.(numerator.(collect(coefficients(mp))))
            denoms = Int.(denominator.(collect(coefficients(mp))))
            if all(==(1), denoms)
                mp_modp = Fpx(coeffs_zz)
                println("  mod p factorization: ", factor(mp_modp))
            else
                println("  minpoly has non-integer coefficients, skipping mod-p check")
            end
            found = true
            break
        catch e
            occursin("No suitable algebraic number found", sprint(showerror, e)) && continue
            println("  unexpected error: ", sprint(showerror, e))
            break
        end
    end
    found || println("  NOT FOUND even at maxdeg=24/maxbits=100 -- may need a ",
                      "tighter enclosure (closer to HC.jl's real achieved ",
                      "precision) or a genuinely higher degree/coefficient size.")
    println()
end

println("=" ^ 70)
println("PART 2: cross-tab the 299 d1 candidates against a1/a2, b1/b2 swap symmetry")
println("=" ^ 70)
println("(swap symmetry a1<->a2, b1<->b2 was confirmed structurally earlier in")
println("this project -- checking whether the 299 d1 points respect it, and")
println("whether a1==a2 / b1==b2 exactly for any of them, which would mean")
println("fewer than 299 distinct factor-base elements once symmetry-duplicates")
println("are collapsed.)")
println()

const EQ_TOL = 1e-4
n_a_equal = 0
n_b_equal = 0
n_both_equal = 0
n_neither_equal = 0
for i in d1_points
    pt = pts[i]
    a1z, a2z = pt[x_idx[:a1]], pt[x_idx[:a2]]
    b1z, b2z = pt[x_idx[:b1]], pt[x_idx[:b2]]
    a_eq = abs(a1z - a2z) < EQ_TOL
    b_eq = abs(b1z - b2z) < EQ_TOL
    global n_a_equal += a_eq
    global n_b_equal += b_eq
    global n_both_equal += (a_eq && b_eq)
    global n_neither_equal += (!a_eq && !b_eq)
end

println("Of ", length(d1_points), " d1 candidate points:")
println("  a1 == a2 (within tol): ", n_a_equal)
println("  b1 == b2 (within tol): ", n_b_equal)
println("  both equal: ", n_both_equal)
println("  neither equal (a1!=a2 AND b1!=b2): ", n_neither_equal)
println()
println("If n_both_equal is a large fraction of 299, many 'points' likely")
println("represent the SAME underlying factor-base element counted multiple")
println("times via the swap symmetry (e.g. (a1,a2)=(r,r) is a fixed point of")
println("the a1<->a2 swap, not two distinct symmetric images of each other).")
println("If n_neither_equal dominates instead, the 299 points are more likely")
println("genuinely paired-up under the swap (a1,a2) and (a2,a1) both present")
println("as separate witness points for the same underlying unordered pair --")
println("in which case the TRUE distinct factor-base count could be closer to")
println("299/2 (or 299/4 counting the b-side too), not 299 itself.")
println()
println("Either way: do not treat 299 as the final factor-base size without")
println("resolving which of these two pictures applies -- that's a real open")
println("question this cross-tab surfaces, not one it answers by itself.")
