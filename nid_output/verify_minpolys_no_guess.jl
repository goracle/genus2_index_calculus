using Serialization
using Oscar
using HomotopyContinuation

# ---------------------------------------------------------------------------
# WHY THIS EXISTS: guess_minpolys.jl found x^3-x^2+1 and x^2+x+1 via Nemo's
# guess(), which searches for ANY algebraic number of low degree/small
# coefficients inside a heuristic radius (HEURISTIC_RADIUS=1e-6) -- per
# Nemo's own docs, guess() with too-loose a radius can return a plausible
# but WRONG small polynomial (their own example: a bare-float 0.1 with no
# radius returns a nonsense degree-1 fit, but 0.1 with an honest small
# radius returns the "nice" x - 1/10). guess() cannot by itself distinguish
# "this really is the root" from "the radius was wide enough to catch a
# nearby simple algebraic number by accident."
#
# certify_degraded_points.jl certified 30 witness points as genuine roots
# of the ORIGINAL 12-variable system F -- that is a real proof, but it says
# nothing about whether a1/a2/b1/b2 satisfy these SPECIFIC two low-degree
# polynomials. That's a different claim guess() made, not one certify()
# checked.
#
# THIS SCRIPT closes that gap directly, without guess() or any heuristic
# radius: it re-derives the two polynomials' roots exactly and symbolically
# (via Nemo's roots(), 128-bit complex ball arithmetic), then checks the
# actual residual distance from EVERY witness point's a1/a2/b1/b2
# coordinates to those exact roots -- both a tight-tolerance re-match
# (1e-10, vs the 5e-4 classify_and_reduce_d1.jl used) and a full residual
# histogram, so a false-positive-by-loose-radius would show up as a
# cluster of borderline distances rather than a clean gap.
# ---------------------------------------------------------------------------

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names

x_var_names = [:a1, :a2, :b1, :b2]
x_idx = Dict(v => findfirst(==(v), gen_names) for v in x_var_names)

CC = AcbField(128)
Qx, x = polynomial_ring(QQ, "x")
omega_roots_C = roots(CC, x^2 + x + 1)
cubic_roots_C = roots(CC, x^3 - x^2 + 1)
all_known_roots = vcat([ComplexF64(r) for r in omega_roots_C],
                        [ComplexF64(r) for r in cubic_roots_C])

println("Exact roots (Nemo roots(), 128-bit, no heuristic radius):")
println("  x^2+x+1 roots: ", [ComplexF64(r) for r in omega_roots_C])
println("  x^3-x^2+1 roots: ", [ComplexF64(r) for r in cubic_roots_C])
println()

# ---------------------------------------------------------------------------
# For every a1/a2/b1/b2 coordinate across ALL 2457 witness points, compute
# the distance to its nearest known root. No radius, no search -- just the
# actual number.
# ---------------------------------------------------------------------------

all_dists = Float64[]
for pt in pts
    for name in x_var_names
        z = pt[x_idx[name]]
        dmin = minimum(abs(z - r) for r in all_known_roots)
        push!(all_dists, dmin)
    end
end

println("Distance-to-nearest-known-root, across all ", length(all_dists),
        " (a1,a2,b1,b2) coordinate instances (", length(pts), " points x 4):")
println()

# Histogram in log-spaced buckets -- a genuine match should cluster near
# float64 precision (~1e-13 to 1e-6 depending on solve/eval precision); an
# accidental guess()-radius fit would instead show a broad or bimodal
# spread with mass sitting close to the old MATCH_TOL boundary (5e-4).
buckets = [1e-13, 1e-10, 1e-8, 1e-6, 1e-4, 5e-4, 1e-2, 1e-1, Inf]
labels = ["<1e-13", "1e-13..1e-10", "1e-10..1e-8", "1e-8..1e-6",
          "1e-6..1e-4", "1e-4..5e-4", "5e-4..1e-2", "1e-2..1e-1", ">1e-1"]
counts = zeros(Int, length(labels))
for d in all_dists
    for (k, b) in enumerate(buckets)
        if d < b
            counts[k] += 1
            break
        end
    end
end
for (lbl, c) in zip(labels, counts)
    println("  ", lbl, ": ", c)
end
println()

n_far = count(d -> d > 5e-4, all_dists)
n_total = length(all_dists)
println(n_far, " / ", n_total, " coordinate instances are farther than",
        " 5e-4 from BOTH known roots (these are the 'mixed'/non-d1/d2",
        " points -- not evidence against the hypothesis, just points",
        " that aren't pure d1 or d2 type).")
println()

# ---------------------------------------------------------------------------
# The decisive check: restrict to coordinates ALREADY classified as
# cubic_type or omega_type (i.e. within the old 5e-4 tolerance), and look
# at the tight end of their distance distribution specifically. If these
# are genuine roots limited only by solve/eval precision, essentially all
# of them should sit well under 1e-5 -- not spread uniformly up to 5e-4.
# ---------------------------------------------------------------------------

close_dists = filter(d -> d < 5e-4, all_dists)
println("Of the ", length(close_dists), " coordinate instances within the",
        " old 5e-4 tolerance:")
println("  fraction under 1e-5: ",
        round(100 * count(d -> d < 1e-5, close_dists) / length(close_dists), digits=1), "%")
println("  fraction under 1e-6: ",
        round(100 * count(d -> d < 1e-6, close_dists) / length(close_dists), digits=1), "%")
println("  max distance in this group: ", maximum(close_dists))
println("  median distance in this group: ", sort(close_dists)[length(close_dists) ÷ 2])
println()
println("INTERPRETATION: if the vast majority sit under 1e-6 with only a",
        " handful of outliers up near 1e-4 (the already-identified",
        " degraded-precision points from certify_degraded_points.jl), that",
        " is a clean, guess()-independent confirmation that a1/a2/b1/b2",
        " genuinely satisfy these two polynomials -- not a radius",
        " artifact. A spread that's roughly UNIFORM across the whole",
        " 1e-6..5e-4 range, with no sharp concentration near float",
        " precision, would instead be the signature of an accidental fit",
        " and should NOT be trusted.")
