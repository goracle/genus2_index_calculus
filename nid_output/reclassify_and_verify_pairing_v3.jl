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
println("PART 1: classify at MATCH_TOL=$MATCH_TOL (same as v2)")
println("=" ^ 70)

d1_points = Int[]
labels = Dict{Int, NTuple{4,Int}}()   # point index -> (a1,a2,b1,b2) as cubic-root indices

for (i, pt) in enumerate(pts)
    all_cubic = true
    idxs = Int[]
    for name in x_var_names
        z = pt[x_idx[name]]
        kind, ridx = classify_coordinate(z)
        if kind == :cubic_type
            push!(idxs, ridx)
        else
            all_cubic = false
        end
    end
    if all_cubic
        push!(d1_points, i)
        labels[i] = (idxs[1], idxs[2], idxs[3], idxs[4])
    end
end

println("d1 candidates (all 4 cubic-type): ", length(d1_points), " / ", length(pts))
println()

# ---------------------------------------------------------------------------
# PART 2: quotient by the FULL confirmed symmetry group.
#
# BUG FIX vs v2 (reclassify_and_verify_pairing.jl): that script's
# `swapped_match` only tested the SIMULTANEOUS swap (a1<->a2 AND b1<->b2
# together) as a single check. But 01_elim2_main.jl's own
# `run_symmetry_checks` confirms a1<->a2 (with wa1<->wa2) and b1<->b2 (with
# wb1<->wb2) are each INDEPENDENTLY confirmed symmetries of u_RS/v_RS -- two
# separate order-2 generators, i.e. a group of order 4:
#   {id, swap_a, swap_b, swap_a ∘ swap_b}
# v2 only ever tested the "swap_a ∘ swap_b" element and treated a
# non-match there as "unpaired", which undercounts the true quotient
# whenever a point's real partner is related by ONLY swap_a or ONLY
# swap_b (very common -- e.g. a1==a2 already, so only the b-swap does
# anything). This version enumerates the full 4-element orbit of each
# label and canonicalizes on the lexicographically-min representative,
# which is correct regardless of which subset of swaps actually moves a
# given tuple (fixed points collapse to orbit size 1, not 4).
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("PART 2: quotient by full order-4 symmetry group (id, swap_a, swap_b, both)")
println("=" ^ 70)

function label_orbit(t::NTuple{4,Int})
    a1, a2, b1, b2 = t
    return Set([
        (a1, a2, b1, b2),
        (a2, a1, b1, b2),
        (a1, a2, b2, b1),
        (a2, a1, b2, b1),
    ])
end

canon = Dict{NTuple{4,Int}, Vector{Int}}()
for (i, t) in labels
    rep = minimum(label_orbit(t))
    push!(get!(canon, rep, Int[]), i)
end

println("Distinct label-orbits under the full group: ", length(canon),
        " (vs. ", length(d1_points), " raw d1 points, and the v2 script's ",
        "flawed count from only testing the combined swap)")
println()

orbit_sizes = sort([length(v) for v in values(canon)])
println("Orbit size distribution (how many witness points share each label-orbit): ")
size_counts = Dict{Int,Int}()
for s in orbit_sizes
    size_counts[s] = get(size_counts, s, 0) + 1
end
for s in sort(collect(keys(size_counts)))
    println("  size $s: $(size_counts[s]) orbit(s)")
end
println()

# ---------------------------------------------------------------------------
# PART 3: within each label-orbit, count the TRUE number of distinct
# underlying (wa1,wa2,wb1,wb2,U0,U1,V0,V1) solutions, up to the same
# swap symmetry (since wa1<->wa2 rides along with a1<->a2, same for b).
# This is a genuinely different number from the label-orbit count in
# PART 2 -- multiple distinct full solutions can and do share one
# (a1,a2,b1,b2) label (confirmed: this is real fiber structure, not
# redundancy, per earlier inspection of one size-16 orbit collapsing to
# 8 truly distinct full points under the b-swap alone).
# ---------------------------------------------------------------------------

println("=" ^ 70)
println("PART 3: distinct FULL solutions per label-orbit (fiber size)")
println("=" ^ 70)

other_names = [:wa1, :wa2, :wb1, :wb2, :U0, :U1, :V0, :V1]
other_idx = Dict(v => findfirst(==(v), gen_names) for v in other_names)

const ROUND_DIGITS = 3  # coarse enough to not split genuinely-equal solve outputs,
                         # fine enough not to conflate distinct ones (values here differ
                         # at the 1e-1 to 1e0 scale typically; adjust if that's wrong)

function round_c(z::ComplexF64)
    return (round(real(z), digits=ROUND_DIGITS), round(imag(z), digits=ROUND_DIGITS))
end

function full_key_up_to_swap(pt)
    wa1, wa2 = round_c(pt[other_idx[:wa1]]), round_c(pt[other_idx[:wa2]])
    wb1, wb2 = round_c(pt[other_idx[:wb1]]), round_c(pt[other_idx[:wb2]])
    U0, U1 = round_c(pt[other_idx[:U0]]), round_c(pt[other_idx[:U1]])
    V0, V1 = round_c(pt[other_idx[:V0]]), round_c(pt[other_idx[:V1]])
    wa_frozen = Set([(wa1, wa2), (wa2, wa1)])
    wb_frozen = Set([(wb1, wb2), (wb2, wb1)])
    return (wa_frozen, wb_frozen, U0, U1, V0, V1)
end

total_full_distinct = 0
for (rep, members) in canon
    keys = Set(full_key_up_to_swap(pts[i]) for i in members)
    global total_full_distinct += length(keys)
end

println("Sum over all label-orbits of (distinct full solutions per orbit): ",
        total_full_distinct)
println("This is the true count of distinct points in the variety (up to the",
        " confirmed symmetry group), as opposed to:")
println("  - ", length(d1_points), " raw d1-classified witness points (no dedup)")
println("  - ", length(canon), " distinct (a1,a2,b1,b2) base labels (dedup on labels only)")
println()
println("NOTE: if total_full_distinct is well below length(d1_points) but",
        " clearly above length(canon), that confirms the fiber-over-base",
        " picture: each base label genuinely has multiple full preimages,",
        " and those preimages (not the raw witness count) are what should",
        " be treated as the factor-base element count for downstream",
        " index-calculus matching. If it equals length(d1_points), the",
        " symmetry group as coded here isn't actually collapsing anything",
        " for this data and that itself would be worth re-checking.")

serialize("d1_label_orbits_v3.jls", canon)
println()
println("Saved label-orbit -> witness-point-index map to d1_label_orbits_v3.jls")
