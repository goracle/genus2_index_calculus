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

CC = AcbField(128)
Qx, x = polynomial_ring(QQ, "x")
omega_roots_C = roots(CC, x^2 + x + 1)
cubic_roots_C = roots(CC, x^3 - x^2 + 1)

# ---------------------------------------------------------------------------
# PART 1: reclassify with a looser tolerance (5e-4, vs the original 1e-4)
# to correctly capture the 44 previously-"unrecognized" coordinates, which
# were confirmed last run to be the cubic root at 1.5e-4-2.7e-4 distance --
# genuinely outside the old tolerance, genuinely inside this one.
# ---------------------------------------------------------------------------
const MATCH_TOL = 5e-4

function classify_coordinate(z::ComplexF64)
    for (i, r) in enumerate(omega_roots_C)
        abs(z - ComplexF64(r)) < MATCH_TOL && return (:omega_type, i)
    end
    for (i, r) in enumerate(cubic_roots_C)
        abs(z - ComplexF64(r)) < MATCH_TOL && return (:cubic_type, i)
    end
    return (:unrecognized, nothing)
end

println("=" ^ 70)
println("PART 1: reclassify with MATCH_TOL=$MATCH_TOL (was 1e-4)")
println("=" ^ 70)

n_omega = n_cubic = n_unrecognized = 0
d1_points = Int[]
unrecognized_examples = Tuple{Int,Symbol,ComplexF64}[]

for (i, pt) in enumerate(pts)
    all_cubic = true
    for name in x_var_names
        z = pt[x_idx[name]]
        kind, _ = classify_coordinate(z)
        if kind == :omega_type
            global n_omega += 1
            all_cubic = false
        elseif kind == :cubic_type
            global n_cubic += 1
        else
            global n_unrecognized += 1
            all_cubic = false
            push!(unrecognized_examples, (i, name, z))
        end
    end
    all_cubic && push!(d1_points, i)
end

println("omega_type: ", n_omega, "   cubic_type: ", n_cubic,
        "   unrecognized: ", n_unrecognized)
println("d1 candidates (all 4 cubic-type): ", length(d1_points), " / ", length(pts),
        "  (was 299 at the old 1e-4 tolerance)")
if !isempty(unrecognized_examples)
    println("Still-unrecognized examples (should be much shorter than 44 now,")
    println("if it isn't, MATCH_TOL may need to go even looser, or these are")
    println("genuinely a third value after all):")
    for (i, name, z) in first(unrecognized_examples, min(10, length(unrecognized_examples)))
        println("  point $i, $name = $z")
    end
end
println()

serialize("d1_candidate_indices_v2.jls", d1_points)
println("Saved ", length(d1_points), " candidate index(es) to d1_candidate_indices_v2.jls")
println()

# ---------------------------------------------------------------------------
# PART 2: verify the swap-pairing hypothesis directly. For each d1 point i
# with (a1,a2,b1,b2) NOT self-symmetric, search the rest of d1_points for a
# genuine partner j whose (a1,a2,b1,b2) equals i's under the a1<->a2, b1<->b2
# swap. This either confirms real pairing (supporting a true count near
# len(d1_points)/2) or shows most points are unpaired (meaning the earlier
# "127 neither-equal" reading was misleading, and the true count is closer
# to len(d1_points) after all).
# ---------------------------------------------------------------------------
println("=" ^ 70)
println("PART 2: verify swap-pairing directly (not just plausible bucket sizes)")
println("=" ^ 70)
println("NOTE: this is an O(n^2) search over d1_points (", length(d1_points),
        " points here). Fine at a few hundred; if PART 1's reclassification",
        " pushed this into the thousands, this loop will be slow -- consider",
        " sorting by a1's real part first and only comparing nearby entries",
        " if that happens, rather than waiting it out.")
println()

const PAIR_TOL = 5e-4

function swapped_match(pt_i, pt_j)
    a1i, a2i = pt_i[x_idx[:a1]], pt_i[x_idx[:a2]]
    b1i, b2i = pt_i[x_idx[:b1]], pt_i[x_idx[:b2]]
    a1j, a2j = pt_j[x_idx[:a1]], pt_j[x_idx[:a2]]
    b1j, b2j = pt_j[x_idx[:b1]], pt_j[x_idx[:b2]]
    # j is i's swap-partner if j's (a1,a2) = i's (a2,a1), same for b
    abs(a1j - a2i) < PAIR_TOL && abs(a2j - a1i) < PAIR_TOL &&
    abs(b1j - b2i) < PAIR_TOL && abs(b2j - b1i) < PAIR_TOL
end

paired = falses(length(d1_points))
partner_of = Dict{Int,Int}()
for (ii, i) in enumerate(d1_points), (jj, j) in enumerate(d1_points)
    ii == jj && continue
    haskey(partner_of, i) && continue  # already matched
    if swapped_match(pts[i], pts[j])
        paired[ii] = true
        partner_of[i] = j
    end
end

n_paired_points = count(paired)
n_unpaired_points = length(d1_points) - n_paired_points
println("Of ", length(d1_points), " d1 candidates: ", n_paired_points,
        " have a confirmed swap-partner elsewhere in the set, ",
        n_unpaired_points, " do not.")
println()
if n_paired_points > 0
    n_pairs = n_paired_points ÷ 2
    println("If pairing is symmetric (i's partner is j, j's partner is i), that's ",
            n_pairs, " genuine pairs -> ", n_pairs,
            " distinct factor-base elements from the paired points, plus ",
            n_unpaired_points, " unpaired (self-symmetric or genuinely singleton) points.")
    println("Estimated TRUE distinct count: ", n_pairs + n_unpaired_points,
            " (vs. ", length(d1_points), " raw d1 candidate points)")
else
    println("No confirmed pairs found -- the earlier 'neither equal' reading",
            " did NOT indicate real swap-pairing after all. Do not assume",
            " len(d1_points)/2 as the true count; ", length(d1_points),
            " may be closer to correct, or something else explains the",
            " a1!=a2/b1!=b2 pattern.")
end
