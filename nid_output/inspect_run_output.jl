using Serialization

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names

println("Checking why reduce_mod_p fails for every point.")
println("gen_names order: ", gen_names)
println()

# Same logic as reduce_mod_p, but reporting magnitudes instead of just
# pass/fail, so we can see WHICH check is failing and by how much.
tol = 1e-6
n_checked = min(5, length(pts))  # just the first few points is enough to see the pattern
for i in 1:n_checked
    pt = pts[i]
    println("--- point $i ---")
    for (j, z) in enumerate(pt)
        im_mag = abs(imag(z))
        r = real(z)
        n = round(Int, r)
        frac_mag = abs(r - n)
        flag_im = im_mag > tol ? " <-- FAILS imag check" : ""
        flag_frac = frac_mag > tol ? " <-- FAILS frac check" : ""
        println("  ", gen_names[j], " = ", z,
                "   |im|=", im_mag, flag_im,
                "   |frac|=", frac_mag, flag_frac)
    end
    println()
end

println("=" ^ 70)
println("If |im| is small (~1e-8 to 1e-10, typical HC.jl numerical noise) but")
println("|frac| is NOT small -- e.g. values are near a non-trivial rational")
println("or near a non-integer algebraic number -- that confirms the real bug:")
println("reduce_mod_p assumes witness coordinates are near-INTEGERS, but wa1,")
println("wa2,wb1,wb2 (square-root eliminated via A^2-B^2*f(t)) and the U/V")
println("target variables have no reason to BE integers even though the")
println("SYSTEM's coefficients were lifted to Z. That's a design assumption")
println("bug in reduce_mod_p, not a problem with the witness points.")
println()
println("If instead |im| itself is large (not just above tol, but not-small,")
println("like O(1) or bigger), that's a different and more serious problem --")
println("it would mean these witness points aren't well-approximated by real")
println("algebraic numbers at all, which would call the witness points")
println("themselves into question, not just this reduction step.")
