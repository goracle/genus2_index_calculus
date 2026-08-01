using Serialization
using Oscar

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names
p = 2371157

x_var_names = [:a1, :a2, :b1, :b2]
x_idx = Dict(v => findfirst(==(v), gen_names) for v in x_var_names)

Fp, Fp_gen = finite_field(p)

# Build F_p^2 explicitly as F_p[y]/(y^2+y+1) -- the same polynomial whose
# roots (omega, omega^2) are the d2 values, so F_p2's generator IS one of
# those roots by construction, not an arbitrary extension representation.
Fpx_for_ext, y_for_ext = polynomial_ring(Fp, "y")
omega_defining_poly = y_for_ext^2 + y_for_ext + 1
Fp2, y2 = finite_field(omega_defining_poly, "y2")
omega_val_Fp2 = y2            # generator IS a root of y^2+y+1 by construction
omega2_val_Fp2 = -1 - y2      # the other root: omega + omega^2 = -1 (sum of roots = -coeff)
omega_roots_Fp2 = [omega_val_Fp2, omega2_val_Fp2]

Fpx, xp = polynomial_ring(Fp, "x")
f_cubic = xp^3 - xp^2 + 1
fac_cubic = factor(f_cubic)
cubic_roots_Fp = [Int(lift(ZZ, -coeff(g, 0))) for (g, _) in fac_cubic if degree(g) == 1]

CC = AcbField(128)
Qx, x = polynomial_ring(QQ, "x")
omega_roots_C = roots(CC, x^2 + x + 1)      # complex approximations, for matching
cubic_roots_C = roots(CC, x^3 - x^2 + 1)

const MATCH_TOL = 5e-4  # confirmed sufficient in the prior investigation --
                          # captures degraded-accuracy points without merging
                          # genuinely distinct roots (cubic's 3 real roots
                          # and omega's 2 roots are all well-separated at
                          # this tolerance; re-check if p or the curve changes)

# Nearest-root match, not just "within tolerance of *a* root" -- returns the
# CLOSEST root and its distance, so we can flag anything alarmingly far from
# every known root instead of silently bucketing it into whichever happens
# to be checked first.
function nearest_root(z::ComplexF64, roots_list)
    dists = [abs(z - ComplexF64(r)) for r in roots_list]
    i = argmin(dists)
    return (i, dists[i])
end

function classify_coordinate(z::ComplexF64)
    i_o, d_o = nearest_root(z, omega_roots_C)
    i_c, d_c = nearest_root(z, cubic_roots_C)
    if d_o < MATCH_TOL && d_o <= d_c
        return (:omega_type, i_o, d_o)
    elseif d_c < MATCH_TOL
        return (:cubic_type, i_c, d_c)
    else
        return (:unrecognized, nothing, min(d_o, d_c))
    end
end

println("Classifying all ", length(pts), " witness points' a1,a2,b1,b2 into")
println("d1 (F_p, cubic-type) and d2 (F_p^2, omega-type) buckets.")
println("MATCH_TOL=$MATCH_TOL")
println()

d1_points = Int[]   # all 4 coords cubic-type
d2_points = Int[]   # all 4 coords omega-type
mixed_points = Int[]  # some cubic, some omega -- neither pure d1 nor d2
unrecognized_points = Tuple{Int,Symbol,ComplexF64,Float64}[]

for (i, pt) in enumerate(pts)
    kinds = Symbol[]
    ok = true
    for name in x_var_names
        z = pt[x_idx[name]]
        kind, _, dist = classify_coordinate(z)
        if kind == :unrecognized
            push!(unrecognized_points, (i, name, z, dist))
            ok = false
        end
        push!(kinds, kind)
    end
    ok || continue
    if all(==(:cubic_type), kinds)
        push!(d1_points, i)
    elseif all(==(:omega_type), kinds)
        push!(d2_points, i)
    else
        push!(mixed_points, i)
    end
end

println("d1 (pure F_p) points: ", length(d1_points))
println("d2 (pure F_p^2) points: ", length(d2_points))
println("mixed (some F_p, some F_p^2 coords -- neither pure d1 nor d2): ",
        length(mixed_points))
println("unrecognized coordinate instances: ", length(unrecognized_points))
if !isempty(unrecognized_points)
    println("  (should be 0 based on the prior run at this tolerance -- if not,")
    println("  something changed; inspect before trusting counts below)")
    for (i, name, z, dist) in first(unrecognized_points, min(5, length(unrecognized_points)))
        println("    point $i, $name=$z, nearest-root distance=$dist")
    end
end
println()

# ---------------------------------------------------------------------------
# Deduplicate via the confirmed swap symmetry: (a1,a2,b1,b2) and
# (a2,a1,b2,b1) are the same underlying factor-base pair. Keep one
# representative per pair (canonicalize by requiring a1's index <= a2's
# index in the root list, arbitrary but consistent).
# ---------------------------------------------------------------------------
const PAIR_TOL = 5e-4

function dedupe_by_swap(indices, pts, x_idx)
    kept = Int[]
    used = falses(length(indices))
    for (ii, i) in enumerate(indices)
        used[ii] && continue
        push!(kept, i)
        used[ii] = true
        pt_i = pts[i]
        a1i, a2i = pt_i[x_idx[:a1]], pt_i[x_idx[:a2]]
        b1i, b2i = pt_i[x_idx[:b1]], pt_i[x_idx[:b2]]
        for (jj, j) in enumerate(indices)
            used[jj] && continue
            pt_j = pts[j]
            if abs(pt_j[x_idx[:a1]] - a2i) < PAIR_TOL && abs(pt_j[x_idx[:a2]] - a1i) < PAIR_TOL &&
               abs(pt_j[x_idx[:b1]] - b2i) < PAIR_TOL && abs(pt_j[x_idx[:b2]] - b1i) < PAIR_TOL
                used[jj] = true  # mark partner as consumed, don't add separately
            end
        end
    end
    return kept
end

d1_dedup = dedupe_by_swap(d1_points, pts, x_idx)
d2_dedup = dedupe_by_swap(d2_points, pts, x_idx)

println("After swap-symmetry dedup: d1 = ", length(d1_dedup), " distinct, ",
        "d2 = ", length(d2_dedup), " distinct.")
println("(d1 should match the previously-confirmed 156; if it doesn't, ",
        "something about this run's data differs from the prior investigation.)")
println()

# ---------------------------------------------------------------------------
# Output actual values, not just indices. For d1: exact F_p integer values
# (matched against the exact root list computed via factor(), not re-derived
# from the noisy complex value). For d2: exact F_p2 elements (as
# coefficients over the F_p2 basis {1, omega}).
# ---------------------------------------------------------------------------

d1_values = NamedTuple[]
for i in d1_dedup
    pt = pts[i]
    row = (point_index = i,
           a1 = cubic_roots_Fp[nearest_root(pt[x_idx[:a1]], cubic_roots_C)[1]],
           a2 = cubic_roots_Fp[nearest_root(pt[x_idx[:a2]], cubic_roots_C)[1]],
           b1 = cubic_roots_Fp[nearest_root(pt[x_idx[:b1]], cubic_roots_C)[1]],
           b2 = cubic_roots_Fp[nearest_root(pt[x_idx[:b2]], cubic_roots_C)[1]])
    push!(d1_values, row)
end

d2_values = NamedTuple[]
for i in d2_dedup
    pt = pts[i]
    row = (point_index = i,
           a1 = omega_roots_Fp2[nearest_root(pt[x_idx[:a1]], omega_roots_C)[1]],
           a2 = omega_roots_Fp2[nearest_root(pt[x_idx[:a2]], omega_roots_C)[1]],
           b1 = omega_roots_Fp2[nearest_root(pt[x_idx[:b1]], omega_roots_C)[1]],
           b2 = omega_roots_Fp2[nearest_root(pt[x_idx[:b2]], omega_roots_C)[1]])
    push!(d2_values, row)
end

println("First 5 d1 values (F_p): ")
for row in first(d1_values, min(5, length(d1_values)))
    println("  point $(row.point_index): a1=$(row.a1) a2=$(row.a2) b1=$(row.b1) b2=$(row.b2)")
end
println()
println("First 5 d2 values (F_p^2, as elements of F_p[y]/(y^2+y+1)): ")
for row in first(d2_values, min(5, length(d2_values)))
    println("  point $(row.point_index): a1=$(row.a1) a2=$(row.a2) b1=$(row.b1) b2=$(row.b2)")
end
println()

serialize("d1_values.jls", d1_values)
serialize("d2_values.jls", d2_values)
println("Saved ", length(d1_values), " d1 value(s) to d1_values.jls")
println("Saved ", length(d2_values), " d2 value(s) to d2_values.jls")

# Also write plain-text CSVs, matching the pattern used for witness_points.csv
open("d1_values.csv", "w") do io
    println(io, "point_index,a1,a2,b1,b2")
    for row in d1_values
        println(io, row.point_index, ",", row.a1, ",", row.a2, ",", row.b1, ",", row.b2)
    end
end
open("d2_values.csv", "w") do io
    println(io, "point_index,a1,a2,b1,b2")
    for row in d2_values
        println(io, row.point_index, ",", row.a1, ",", row.a2, ",", row.b1, ",", row.b2)
    end
end
println("Also wrote d1_values.csv and d2_values.csv (plain text).")
