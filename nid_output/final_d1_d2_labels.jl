using Serialization
using Oscar

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names
p = 2371157

x_var_names = [:a1, :a2, :b1, :b2]
x_idx = Dict(v => findfirst(==(v), gen_names) for v in x_var_names)

Fp, _ = finite_field(p)
Fpx, xp = polynomial_ring(Fp, "x")
f_omega = xp^2 + xp + 1
f_cubic = xp^3 - xp^2 + 1

cubic_roots_Fp = [-coeff(g, 0) for (g, _) in factor(f_cubic) if degree(g) == 1]

# x^2+x+1 does NOT split over F_p at this p (p mod 3 = 2, confirmed earlier
# this session) -- its roots live in F_{p^2} = F_p[y]/(y^2+y+1), not F_p.
# Build that extension and find its roots there (same construction
# output_d1_d2.jl used originally), rather than indexing into an
# always-empty F_p root list.
Fp2, y2 = finite_field(f_omega, "y2")
Fp2x, xp2 = polynomial_ring(Fp2, "x")
f_omega_Fp2 = xp2^2 + xp2 + 1
omega_roots_Fp2 = [-coeff(g, 0) for (g, _) in factor(f_omega_Fp2) if degree(g) == 1]

CC = AcbField(128)
Qx, x = polynomial_ring(QQ, "x")
omega_roots_C = roots(CC, x^2 + x + 1)
cubic_roots_C = roots(CC, x^3 - x^2 + 1)

const MATCH_TOL = 5e-4  # confirmed safe: certify_degraded_points.jl showed the
                         # 30 previously-borderline points all certify as
                         # genuine roots within 2e-8 to 1.6e-5 of these known
                         # roots -- no ambiguity left at this tolerance.

# classify a coordinate against BOTH known polynomials; returns
# (:omega_type, root_index) | (:cubic_type, root_index) | (:unrecognized, nothing)
function classify_coordinate(z::ComplexF64)
    for (i, r) in enumerate(omega_roots_C)
        abs(z - ComplexF64(r)) < MATCH_TOL && return (:omega_type, i)
    end
    for (i, r) in enumerate(cubic_roots_C)
        abs(z - ComplexF64(r)) < MATCH_TOL && return (:cubic_type, i)
    end
    return (:unrecognized, nothing)
end

# ---------------------------------------------------------------------------
# Classify every witness point's (a1,a2,b1,b2) as pure d1 (all 4 cubic_type),
# pure d2 (all 4 omega_type), or mixed/unrecognized (neither, dropped).
# ---------------------------------------------------------------------------

d1_labels = Dict{Int, NTuple{4,Int}}()  # point index -> (a1,a2,b1,b2) as cubic-root indices
d2_labels = Dict{Int, NTuple{4,Int}}()  # point index -> (a1,a2,b1,b2) as omega-root indices
n_unrecognized = 0

for (i, pt) in enumerate(pts)
    kinds = Symbol[]
    idxs = Int[]
    for name in x_var_names
        kind, ridx = classify_coordinate(pt[x_idx[name]])
        push!(kinds, kind)
        push!(idxs, something(ridx, 0))
    end
    if all(==(:cubic_type), kinds)
        d1_labels[i] = (idxs[1], idxs[2], idxs[3], idxs[4])
    elseif all(==(:omega_type), kinds)
        d2_labels[i] = (idxs[1], idxs[2], idxs[3], idxs[4])
    elseif any(==(:unrecognized), kinds)
        global n_unrecognized += 1
    end
    # mixed (some cubic, some omega, none unrecognized) is neither d1 nor d2;
    # not counted as an error, just not part of either factor-base bucket.
end

println("d1 (pure cubic_type) witness points: ", length(d1_labels))
println("d2 (pure omega_type) witness points: ", length(d2_labels))
println("points with an unrecognized coordinate: ", n_unrecognized)
println()

# ---------------------------------------------------------------------------
# Quotient by the FULL confirmed symmetry group: independent a1<->a2 and
# b1<->b2 swaps (order 4: id, swap_a, swap_b, both) -- both confirmed
# separately in 01_elim2_main.jl's run_symmetry_checks, and re-confirmed in
# this session's certify_degraded_points.jl run ("CONFIRMED: full
# a1<->a2/b1<->b2 swap symmetry holds"). This is the correct group; the
# earlier reclassify_and_verify_pairing.jl only tested the combined-swap
# element and undercounted the quotient (156 instead of the true 36 for d1).
# ---------------------------------------------------------------------------

function label_orbit(t::NTuple{4,Int})
    a1, a2, b1, b2 = t
    return Set([(a1, a2, b1, b2), (a2, a1, b1, b2),
                (a1, a2, b2, b1), (a2, a1, b2, b1)])
end

function distinct_labels_mod_symmetry(labels::Dict{Int, NTuple{4,Int}})
    canon = Set{NTuple{4,Int}}()
    for t in values(labels)
        push!(canon, minimum(label_orbit(t)))
    end
    return canon
end

d1_distinct = distinct_labels_mod_symmetry(d1_labels)
d2_distinct = distinct_labels_mod_symmetry(d2_labels)

println("=" ^ 70)
println("FINAL: distinct d1 and d2 values, mod symmetry")
println("=" ^ 70)
println()
println("d1: ", length(d1_distinct), " distinct value(s) (raw witness points: ",
        length(d1_labels), ")")
for t in sort(collect(d1_distinct))
    a1, a2, b1, b2 = t
    vals = (cubic_roots_Fp[a1], cubic_roots_Fp[a2], cubic_roots_Fp[b1], cubic_roots_Fp[b2])
    println("  (a1,a2,b1,b2) = ", vals, "   [root indices: ", t, "]")
end
println()
println("d2: ", length(d2_distinct), " distinct value(s) (raw witness points: ",
        length(d2_labels), ")")
for t in sort(collect(d2_distinct))
    a1, a2, b1, b2 = t
    vals = (omega_roots_Fp2[a1], omega_roots_Fp2[a2], omega_roots_Fp2[b1], omega_roots_Fp2[b2])
    println("  (a1,a2,b1,b2) = ", vals, "   [root indices: ", t, "]")
end

serialize("d1_d2_final.jls", (
    d1_distinct = d1_distinct,
    d2_distinct = d2_distinct,
    d1_labels_by_point = d1_labels,
    d2_labels_by_point = d2_labels,
    cubic_roots_Fp = cubic_roots_Fp,
    omega_roots_Fp2 = omega_roots_Fp2,
))
println()
println("Saved to d1_d2_final.jls.")
