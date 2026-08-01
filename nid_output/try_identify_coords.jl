using Serialization

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names

# ---------------------------------------------------------------------------
# Cheap, first-pass experiment: don't try to be clever about WHICH algebraic
# numbers appear -- just check whether each coordinate's real part matches
# k/n for small integers k,n (rationals), or matches a handful of common
# quadratic irrationals, within tolerance. This won't fix the pipeline by
# itself; it's a fast way to see how much of the data a simple approach
# would explain before investing in real integer-relation detection (PSLQ)
# or going back through the symbolic/Oscar-side construction.
# ---------------------------------------------------------------------------

const TOL = 1e-5

function try_identify(z::ComplexF64)
    im_ok = abs(imag(z)) < 1e-4
    r = real(z)

    # small rationals k/n, n up to 12
    for n in 1:12, k in -12*n:12*n
        if abs(r - k/n) < TOL
            return im_ok ? "$k/$n (real)" : "$k/$n (real part; |im|=$(round(imag(z), digits=6)))"
        end
    end

    # common quadratic irrationals and their negatives/halves
    candidates = Dict(
        "sqrt(2)"    => sqrt(2), "sqrt(3)"    => sqrt(3), "sqrt(5)"    => sqrt(5),
        "sqrt(2)/2"  => sqrt(2)/2, "sqrt(3)/2" => sqrt(3)/2,
        "(1+sqrt(5))/2" => (1+sqrt(5))/2, "(1-sqrt(5))/2" => (1-sqrt(5))/2,
    )
    for (name, val) in candidates
        for sign in (1, -1)
            if abs(r - sign*val) < TOL
                return "$(sign<0 ? "-" : "")$name (real part)"
            end
        end
    end

    return nothing
end

println("Attempting to identify each coordinate against a small fixed basis")
println("(rationals k/n up to n=12, plus common quadratic irrationals).")
println("This is a first pass, not a real integer-relation search -- if most")
println("coordinates come back `nothing`, that tells us this basis is too")
println("small / wrong, not that PSLQ is needed yet.")
println()

n_check = min(20, length(pts))
identified = 0
total = 0
for i in 1:n_check
    pt = pts[i]
    for (j, z) in enumerate(pt)
        global total += 1
        id = try_identify(z)
        if id !== nothing
            global identified += 1
            println("point $i, ", gen_names[j], " = ", z, "  ~=  ", id)
        end
    end
end
println()
println("Identified $identified / $total coordinates (first $n_check points) ",
        "against this small basis.")
println("If this fraction is high, extending the basis (more radicals, higher")
println("n) is probably enough. If it's low, we likely need real integer-")
println("relation detection (e.g. a PSLQ implementation) or to go back through")
println("the symbolic/Oscar construction instead of pattern-matching floats.")
