using Serialization
using Oscar

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names

x_var_names = [:a1, :a2, :b1, :b2]
x_idx = [findfirst(==(v), gen_names) for v in x_var_names]
any(isnothing, x_idx) &&
    error("Could not find one of ", x_var_names, " in gen_names=", gen_names,
          " -- fix x_var_names or check witness_points.jls's actual gen_names.")

const HEURISTIC_RADIUS = 1e-6  # SAME open caveat as before: this must
                                # reflect HC.jl's actual achieved precision
                                # at these points. Not yet verified against
                                # a real per-point accuracy figure. Treat
                                # degrees found below as provisional until
                                # that's checked -- a too-tight radius can
                                # make guess() report a WRONG (often lower
                                # apparent) degree with false confidence.
const MAXDEG = 16   # ceiling on degree searched; if everything comes back
                    # "not found", this is the first thing to raise
const MAXBITS = 60  # coefficient bit-size ceiling; raise alongside MAXDEG

CC = AcbField(128)  # Nemo's arbitrary-precision complex ball field --
                     # correct name per Nemo (ArbComplexField doesn't exist
                     # in this version; confirmed by the prior run's error)
Qb = algebraic_closure(QQ)
Qx, x = polynomial_ring(QQ, "x")

"""
Returns (degree::Union{Int,Nothing}, minpoly::Union{PolyElem,Nothing}).
`degree === nothing` means guess() found nothing at this MAXDEG/MAXBITS --
NOT that the true degree is unbounded; raise the search parameters and
retry rather than treating this as "no algebraic structure."
"""
function identify_degree(z::ComplexF64)
    enclosure = CC(real(z), imag(z)) + CC("+/- $(HEURISTIC_RADIUS)", "+/- $(HEURISTIC_RADIUS)")
    # Nemo's own docs recommend escalating maxdeg/maxbits across repeated
    # calls rather than one fixed-size attempt, since a single guess() call
    # only searches up to the given ceiling and a miss doesn't mean "no
    # algebraic structure," just "not found at this size." Try a small set
    # of increasing (maxdeg, maxbits) pairs before giving up.
    for (md, mb) in [(4, 20), (8, 40), (MAXDEG, MAXBITS)]
        local alg
        try
            alg = guess(Qb, enclosure, md, mb)
        catch e
            occursin("No suitable algebraic number found", sprint(showerror, e)) && continue
            rethrow(e)  # an unexpected guess() failure should surface, not be swallowed
        end
        mp = minpoly(Qx, alg)
        return (Nemo.degree(mp), mp)
    end
    return (nothing, nothing)
end

println("Identifying the exact degree over Q of a1,a2,b1,b2 at each witness point.")
println("HEURISTIC_RADIUS=$HEURISTIC_RADIUS, MAXDEG=$MAXDEG, MAXBITS=$MAXBITS")
println("(all provisional -- see comments in this file before trusting results at scale)")
println()

n_check = min(15, length(pts))
degree_counts = Dict{Union{Int,Nothing}, Int}()
for i in 1:n_check
    pt = pts[i]
    println("--- point $i ---")
    for (name, idx) in zip(x_var_names, x_idx)
        deg, mp = identify_degree(pt[idx])
        degree_counts[deg] = get(degree_counts, deg, 0) + 1
        if deg === nothing
            println("  ", name, " = ", pt[idx], "  -> NOT FOUND at MAXDEG=$MAXDEG/MAXBITS=$MAXBITS")
        else
            println("  ", name, " = ", pt[idx], "  -> degree $deg, minpoly: ", mp)
        end
    end
end
println()
println("=" ^ 70)
println("Degree histogram across ", n_check, " point(s) x 4 coords = ",
        4*n_check, " checks:")
for (deg, count) in sort(collect(degree_counts); by = p -> something(p[1], -1))
    println("  degree ", something(deg, "NOT FOUND"), ": ", count)
end
println()
println("If one degree dominates (e.g. mostly degree 4 or 8), that's a strong")
println("signal for the actual extension structure -- e.g. degree 4 across")
println("a1,a2,b1,b2 would be consistent with the norm-elimination stacking")
println("(genus-2 curve is degree 2 in y over x already, plus whatever degree")
println("the a1/a2/b1/b2 themselves pick up from being norms/symmetric")
println("functions of Mumford coordinates upstream). A mixed histogram, or a")
println("large NOT FOUND count, means MAXDEG/MAXBITS/HEURISTIC_RADIUS need")
println("adjustment before this is trustworthy.")
