using Serialization
using Oscar   # brings in Nemo's QQBar / real_field / guess

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names

# ---------------------------------------------------------------------------
# guess(QQBar, x, maxdeg) needs an ENCLOSURE (a value + explicit error
# radius), not a bare Float64 -- per Nemo's own docs, a bare float without a
# radius can at best "guess" the binary float itself, which is useless here.
# We don't have a rigorous a priori error bound on HC.jl's output, so this
# uses a heuristic radius based on typical HC.jl endgame precision. That
# heuristic is a real weak point -- see the warning printed below -- and
# should be checked against your own understanding of the tracker's actual
# achieved precision before trusting any resulting minimal polynomial as
# more than "plausible."
# ---------------------------------------------------------------------------

const HEURISTIC_RADIUS = 1e-6   # ADJUST: should reflect HC.jl's actual achieved precision, not a guess
const MAXDEG = 12                # search degree; raise if nothing is found and you suspect higher degree
const MAXBITS = 40               # coefficient bit-size ceiling; raise together with MAXDEG if needed

RR = ArbField(128)
Qb = algebraic_closure(QQ)

function try_guess_minpoly(z::ComplexF64)
    r = real(z)
    im_mag = abs(imag(z))
    if im_mag > 1e-4
        return (:not_real, nothing, im_mag)
    end
    x_enclosure = RR(r) + RR("+/- $(HEURISTIC_RADIUS)")
    try
        alg = guess(Qb, x_enclosure, MAXDEG; maxbits = MAXBITS)
        Qx, _ = polynomial_ring(QQ, "x")
        mp = minpoly(Qx, alg)
        return (:found, mp, im_mag)
    catch e
        return (:not_found, nothing, im_mag)
    end
end

println("Running Nemo's guess() against a sample of witness coordinates.")
println("HEURISTIC_RADIUS = ", HEURISTIC_RADIUS, " -- if this is smaller than")
println("HC.jl's actual achieved precision, guess() may return a WRONG minimal")
println("polynomial with false confidence (an enclosure that's too tight for")
println("the true error is worse than one that's honestly too loose). Cross-")
println("check a few hits against the raw log's per-point residual/precision")
println("info if HC.jl reports one, before trusting these results.")
println()

n_check = min(10, length(pts))
found_count = 0
total_count = 0
for i in 1:n_check
    pt = pts[i]
    for (j, z) in enumerate(pt)
        global total_count += 1
        status, mp, im_mag = try_guess_minpoly(z)
        if status == :found
            global found_count += 1
            println("point $i, ", gen_names[j], " = ", z)
            println("  minimal polynomial (degree ", Nemo.degree(mp), "): ", mp)
        elseif status == :not_real
            println("point $i, ", gen_names[j], ": |im|=", im_mag, " too large to treat as real, skipped")
        end
    end
end
println()
println("Found minimal polynomials for $found_count / $total_count coordinates checked.")
println("Points/coords with no output above either genuinely need higher MAXDEG/MAXBITS,")
println("or HEURISTIC_RADIUS is wrong for this data -- both are real unknowns, not defaults")
println("to trust blindly.")
