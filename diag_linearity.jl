#!/usr/bin/env julia
#
# diag_linearity.jl
#
# Purpose: settle the question raised by the supervisor AI, for ONE sample,
# with no Groebner basis call anywhere in this file.
#
# For sample 1 (K=2, c=2), we:
#
#   1. Build the graph equation(s) U*den - num = 0 for u_RS and v_RS,
#      exactly as elim2.jl does, but stop BEFORE cross-sample matching.
#   2. Collect each equation's coefficients on the monomial basis
#      {1, wa1, wa2, wa1*wa2} of F[wa1,wa2] over the coefficient ring
#      F[a1,a2,U0,...] (resp. V0,... for the v-equations). The number of
#      U/V variables is sized dynamically from the actual number of
#      u_RS/v_RS coefficients (see stage-2 ring construction below), not
#      assumed fixed at 2.
#   3. Report whether the wa1*wa2 coefficient is identically zero.
#        - If YES for all equations: the per-sample system is a genuine
#          affine-linear system in (wa1,wa2) over F[a1,a2,U,V], and we
#          build the coefficient matrix M and vector b so that
#          M * (wa1,wa2)^T + b = 0, ready for minor-based elimination
#          (NOT substitution -- see note below).
#        - If NO: the system is bilinear, and we report the max degree
#          of the wa1*wa2 coefficients so we know the size of the object
#          we'd be dealing with instead.
#   4. If the linear case holds, build the augmented matrix [M | b] and
#      report the SIZE of its 3x3 minors (we do NOT expand them by
#      default -- that determinant computation is exactly the "next"
#      expensive step, and we want its cost measured, not silently paid,
#      before committing to it). Pass EXPAND_MINORS=true to also expand
#      and report term counts/degrees of the actual minors.
#
# This deliberately avoids substitution (wa1 = -b/A) as the elimination
# method, per the supervisor's correction: that step is only valid where
# A is a unit, and silently discards the case A=0 (loses components).
# Minors of the augmented matrix detect the FULL consistency locus,
# including where individual coefficients vanish.

using Oscar

const EXPAND_MINORS = get(ENV, "EXPAND_MINORS", "false") == "true"

################################################################################
# Locate the symbolic engine. Adjust this path if your checkout differs --
# the uploaded file sits directly next to this script, not under
# phi_general/src/, so we point at it directly.
################################################################################

const HERE = @__DIR__
const PHI_GENERAL_SRC = joinpath(HERE, "phi_general", "src")
const SYMBOLIC_ENGINE = joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl")

if !isfile(SYMBOLIC_ENGINE)
    error("diag_linearity.jl: can't find trial3_phi_symbolic_unified.jl at $SYMBOLIC_ENGINE. " *
          "Edit SYMBOLIC_ENGINE to point at your checkout.")
end

include(SYMBOLIC_ENGINE)
using .PhiSymbolic

################################################################################
# Curve / field constants -- same as elim2.jl
################################################################################

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs

F = GF(p)

################################################################################
# Sample 1 only (K=2, c=2) -- same data as elim2.jl's sample 1.
################################################################################

const K1, c1 = 2, 2
const fixed1 = Tuple{Int,Int}[]
const u0_1, u1_1, v0_1, v1_1 = 468873, 956582, 2168176, 2288437

println("Calling PhiSymbolic.symbolic_residual for sample 1 (K=$K1, c=$c1)...")
res1 = PhiSymbolic.symbolic_residual(K1, c1, fixed1, u0_1, u1_1, v0_1, v1_1, F_POLY_ASC, p)

if isempty(res1.u_RS_coeffs) || isempty(res1.v_RS_coeffs)
    error("sample 1: construction failed or degenerate -- no u_RS/v_RS")
end

println("sample 1: deg(u_RS)=$(length(res1.u_RS_coeffs)-1)  deg(v_RS)=$(length(res1.v_RS_coeffs)-1)")

################################################################################
# Target ring, stage 1: F[wa1,wa2,a1,a2] only.
#
# We can't fix the number of U/V variables yet -- that depends on
# length(u_RS_coeffs)/length(v_RS_coeffs), which varies per sample
# (PhiSymbolic's own comment: "deg(u_RS) is typically small, often 2",
# i.e. 3 coefficients is a normal outcome, not a guaranteed 2). So we
# flatten into a small ring first, count real coefficients, then build
# the final ring (stage 2, below) sized correctly and remap into it.
################################################################################

R0, (wa1_0, wa2_0, a1_0, a2_0) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2"])

################################################################################
# Tower -> plain-ring substitution (same machinery as elim2.jl).
################################################################################

function _reduce_frac(num, den)
    iszero(num) && return (num, one(den))
    g = gcd(num, den)
    if !isone(g)
        num = divexact(num, g)
        den = divexact(den, g)
    end
    return (num, den)
end

function _base_frac_to_ring(val, t_gens::Vector)
    num = numerator(val)
    den = denominator(val)
    num_R = evaluate(num, t_gens)
    den_R = evaluate(den, t_gens)
    return _reduce_frac(num_R, den_R)
end

# Walk the c=2 tower: val = c0(t1,w1) + c1(t1,w1)*w2, each c_i = d0(t1) + d1(t1)*w1.
# Returns (num, den) in R for the fully-flattened element, substituting
# w_gens = [wa1,wa2], t_gens = [a1,a2].
function _tower_to_ring(val, w_gens::Vector, t_gens::Vector)
    # layer 2: val is degree<=1 in w2 over K1
    d = data(val)  # polynomial in w2 over K1, or a K1 element directly
    coeffs2 = collect(coefficients(d))
    # coeffs2 can have 0, 1, or 2 entries: 0 means d is the zero
    # polynomial entirely (val==0), 1 means no w2 term (c1=0), 2 means
    # both c0 and c1 present. Pull the ring's own zero element as a
    # fallback rather than indexing blindly.
    K1ring = base_ring(parent(d))
    c0 = length(coeffs2) >= 1 ? coeffs2[1] : zero(K1ring)
    c1 = length(coeffs2) >= 2 ? coeffs2[2] : zero(K1ring)

    function layer1_to_ring(val1)
        d1 = data(val1)
        coeffs1 = collect(coefficients(d1))
        Rt = base_ring(parent(d1))
        e0 = length(coeffs1) >= 1 ? coeffs1[1] : zero(Rt)
        e1 = length(coeffs1) >= 2 ? coeffs1[2] : zero(Rt)
        n0, dn0 = _base_frac_to_ring(e0, t_gens)
        n1, dn1 = _base_frac_to_ring(e1, t_gens)
        # e0 + e1*w1  ->  (n0*dn1 + n1*dn0*w1) / (dn0*dn1), then reduce
        num = n0 * dn1 + n1 * dn0 * w_gens[1]
        den = dn0 * dn1
        return _reduce_frac(num, den)
    end

    n_c0, d_c0 = layer1_to_ring(c0)
    n_c1, d_c1 = layer1_to_ring(c1)

    # c0 + c1*w2 -> (n_c0*d_c1 + n_c1*d_c0*w2) / (d_c0*d_c1), reduce
    num = n_c0 * d_c1 + n_c1 * d_c0 * w_gens[2]
    den = d_c0 * d_c1
    return _reduce_frac(num, den)
end

w_gens = [wa1_0, wa2_0]
t_gens = [a1_0, a2_0]

println("Flattening u_RS coefficients into R0...")
u_flat_0 = [_tower_to_ring(c, w_gens, t_gens) for c in res1.u_RS_coeffs]

println("Flattening v_RS coefficients into R0...")
v_flat_0 = [_tower_to_ring(c, w_gens, t_gens) for c in res1.v_RS_coeffs]

################################################################################
# Target ring, stage 2: F[wa1,wa2,a1,a2,U0,...,U(n_u-1),V0,...,V(n_v-1)],
# sized off the REAL coefficient counts (n_u, n_v) instead of an assumed
# fixed 2. U_i/V_i are the decoupling target variables from elim2.jl's
# Iu_decoupled / Iuv_decoupled route: instead of matching sample 1 against
# sample 2 directly, we match sample 1 against an UNKNOWN target that
# sample 2 will separately be matched against. This script only builds
# sample 1's half. (Mirrors elim2.jl's own dynamic sizing at
# dec_gens[9:(8+N_U_MATCH)] -- that file never hardcoded the count either;
# this diagnostic script just hadn't caught up to it.)
################################################################################

n_u = length(u_flat_0)
n_v = length(v_flat_0)
println("n_u = $n_u, n_v = $n_v (sizing U/V variable lists accordingly)")

U_names = ["U$(i)" for i in 0:(n_u-1)]
V_names = ["V$(i)" for i in 0:(n_v-1)]

R, gens_R = polynomial_ring(F, vcat(["wa1", "wa2", "a1", "a2"], U_names, V_names))
wa1, wa2, a1, a2 = gens_R[1], gens_R[2], gens_R[3], gens_R[4]
U_vars = gens_R[5:(4+n_u)]
V_vars = gens_R[(5+n_u):(4+n_u+n_v)]

curve_a1 = wa1^2 - (a1^5 + a1 + 2)
curve_a2 = wa2^2 - (a2^5 + a2 + 2)

# Remap (num,den) pairs from R0 into R via the shared variable names
# (R0's wa1,wa2,a1,a2 map positionally onto R's first four generators).
_r0_to_r = [wa1, wa2, a1, a2]
u_flat = [(evaluate(num, _r0_to_r), evaluate(den, _r0_to_r)) for (num, den) in u_flat_0]
v_flat = [(evaluate(num, _r0_to_r), evaluate(den, _r0_to_r)) for (num, den) in v_flat_0]

################################################################################
# Build graph equations: U_i * den_i - num_i = 0 for each u_RS coefficient,
# and V_i * den_i - num_i = 0 for each v_RS coefficient. U_vars/V_vars are
# now sized to match u_flat/v_flat exactly (stage-2 ring above), so no
# fixed-length assumption is baked in here anymore.
################################################################################

@assert length(U_vars) == length(u_flat)
@assert length(V_vars) == length(v_flat)

graph_eqs = Any[]
eq_labels = String[]

for (i, (num, den)) in enumerate(u_flat)
    eq = U_vars[i] * den - num
    push!(graph_eqs, eq)
    push!(eq_labels, "Gu$(i-1)")
end
for (i, (num, den)) in enumerate(v_flat)
    eq = V_vars[i] * den - num
    push!(graph_eqs, eq)
    push!(eq_labels, "Gv$(i-1)")
end

println()
println("===========================================================")
println("Graph equations built (per-sample, no cross-sample matching)")
println("===========================================================")
for (label, eq) in zip(eq_labels, graph_eqs)
    println("$label: degree=$(total_degree(eq))  terms=$(length(terms(eq)))")
end
println()

################################################################################
# THE ACTUAL EXPERIMENT.
#
# For each graph equation, collect coefficients on the monomial basis
# {1, wa1, wa2, wa1*wa2} of F[wa1,wa2], with coefficients living in
# F[a1,a2,U0,...,V0,...] (a1,a2 and whichever U/V vars appear).
#
# We do this by hand (not via a generic multivariate coefficient() call)
# so the classification is unambiguous: walk every term of the expanded
# polynomial, look at its (wa1,wa2)-exponent pair, and bucket accordingly.
################################################################################

function classify_by_w_monomials(eq, wa1, wa2)
    buckets = Dict{Tuple{Int,Int}, Any}(
        (0,0) => zero(eq), (1,0) => zero(eq), (0,1) => zero(eq), (1,1) => zero(eq),
    )
    other_degree = Ref(0)  # tracks any wa1/wa2 exponent > 1, which would
                             # mean the equation ISN'T even bilinear
    for t in terms(eq)
        e_wa1 = degree(t, wa1)
        e_wa2 = degree(t, wa2)
        if e_wa1 > 1 || e_wa2 > 1
            other_degree[] = max(other_degree[], max(e_wa1, e_wa2))
            key = (min(e_wa1,2), min(e_wa2,2))  # bucket overflow separately below
            buckets[(99,99)] = get(buckets, (99,99), zero(eq)) + t
            continue
        end
        buckets[(e_wa1, e_wa2)] += t
    end
    return buckets, other_degree[]
end

println("===========================================================")
println("Classifying each equation's terms by (wa1,wa2)-monomial")
println("===========================================================")
println()

println("===========================================================")
println("Sanity check: is den already free of wa1,wa2? (confirmed true")
println("in the elim2.jl run for u1/v1 dens -- verifying here too)")
println("===========================================================")
for (i, (num, den)) in enumerate(u_flat)
    d1, d2 = degree(den, wa1), degree(den, wa2)
    println("  u1 den[$i]: degree-in-(wa1,wa2) = ($d1, $d2)")
end
for (i, (num, den)) in enumerate(v_flat)
    d1, d2 = degree(den, wa1), degree(den, wa2)
    println("  v1 den[$i]: degree-in-(wa1,wa2) = ($d1, $d2)")
end
println("If all zero: graph equation U*den-num is affine-linear in (wa1,wa2)")
println("IFF num itself has no wa1*wa2 cross term -- that's what the")
println("classification below actually isolates.")
println()

any_higher_degree = false
any_bilinear_term = false

coeff_matrix_rows = Any[]   # each row: [coeff(wa1), coeff(wa2)] for M*w + b = 0
coeff_vector_b = Any[]      # each row: coeff(1)  (the b_i)
bilinear_terms = Any[]      # coeff(wa1*wa2) per equation, for inspection

for (label, eq) in zip(eq_labels, graph_eqs)
    buckets, max_extra_deg = classify_by_w_monomials(eq, wa1, wa2)

    c00 = buckets[(0,0)]
    c10 = buckets[(1,0)]
    c01 = buckets[(0,1)]
    c11 = buckets[(1,1)]
    overflow = get(buckets, (99,99), zero(eq))

    println("--- $label ---")
    println("  coeff(1)         : degree=$(iszero(c00) ? -1 : total_degree(c00))  terms=$(length(terms(c00)))")
    println("  coeff(wa1)       : degree=$(iszero(c10) ? -1 : total_degree(c10))  terms=$(length(terms(c10)))")
    println("  coeff(wa2)       : degree=$(iszero(c01) ? -1 : total_degree(c01))  terms=$(length(terms(c01)))")
    println("  coeff(wa1*wa2)   : degree=$(iszero(c11) ? -1 : total_degree(c11))  terms=$(length(terms(c11)))")
    if !iszero(overflow)
        println("  ** WARNING: terms with wa1 or wa2 exponent > 1 found (degree up to $max_extra_deg).")
        println("     This equation is NOT even bilinear in (wa1,wa2) -- classification below is incomplete for it.")
        global any_higher_degree = true
    end
    if !iszero(c11)
        println("  ** wa1*wa2 term is NONZERO for $label -- this equation is genuinely bilinear, not linear.")
        global any_bilinear_term = true
    else
        println("  wa1*wa2 term is ZERO for $label -- consistent with affine-linear in (wa1,wa2).")
    end
    println()

    push!(coeff_matrix_rows, [c10, c01])
    push!(coeff_vector_b, c00)
    push!(bilinear_terms, c11)
end

println("===========================================================")
println("VERDICT")
println("===========================================================")
if any_higher_degree
    println("At least one equation has wa1 or wa2 exponent > 1.")
    println("=> Neither the linear nor the simple bilinear model applies cleanly.")
    println("   Re-examine _tower_to_ring / the tower depth assumption before proceeding.")
elseif any_bilinear_term
    println("At least one wa1*wa2 coefficient is nonzero.")
    println("=> Per-sample system is BILINEAR in (wa1,wa2), not linear.")
    println("   Next step: treat as a bilinear system -- e.g. eliminate via the")
    println("   2x2 minors of the coefficient matrix in the bilinear monomial")
    println("   basis {1,wa1,wa2,wa1wa2}, NOT via substitution.")
else
    println("ALL wa1*wa2 coefficients are zero.")
    println("=> Per-sample system is genuinely AFFINE-LINEAR in (wa1,wa2)")
    println("   over F[a1,a2,U0,...,V0,...] ($n_u U-vars, $n_v V-vars).")
    println("   => Proceed to matrix/minor construction below.")
end
println()

################################################################################
# If linear (or even if not -- we still report matrix shape for inspection),
# build the coefficient matrix M (n_eqs x 2) and vector b (n_eqs x 1) such
# that graph_eqs[i] == M[i,1]*wa1 + M[i,2]*wa2 + b[i].
#
# Consistency of M*w = -b (as a system with MORE equations than unknowns --
# we have 4 equations, 2 unknowns wa1,wa2) is governed by the 3x3 minors of
# the augmented matrix [M | b] (4 choose 3 = 4 minors of a 3x4... actually
# for a 4x2 M and 4x1 b, augmented is 4x3; rank <= 2 required for
# consistency, so ALL 3x3 minors of [M|b] must vanish). We do NOT eliminate
# by substitution: we report the minors themselves as elimination
# candidates, exactly the object the supervisor described.
################################################################################

n_eqs = length(coeff_matrix_rows)
println("Coefficient matrix M is $(n_eqs) x 2 (equations x {wa1,wa2}).")
println("Augmented matrix [M | b] is $(n_eqs) x 3.")
println("Consistency (rank <= 2) requires all 3x3 minors of [M|b] to vanish.")
println("Number of 3x3 minors from a $(n_eqs)x3 matrix: C($(n_eqs),3) = $(binomial(n_eqs,3))")
println()

# Assemble as an actual matrix over R for minor extraction.
M_aug = Array{typeof(graph_eqs[1])}(undef, n_eqs, 3)
for i in 1:n_eqs
    M_aug[i,1] = coeff_matrix_rows[i][1]  # coeff(wa1)
    M_aug[i,2] = coeff_matrix_rows[i][2]  # coeff(wa2)
    M_aug[i,3] = coeff_vector_b[i]        # coeff(1), i.e. b_i (note sign: eq = A*wa1+B*wa2+b = 0)
end

function minor_3x3(Mrows::Vector{Int})
    # 3x3 determinant of M_aug[Mrows, :], by cofactor expansion (small,
    # exact, no need for generic det() machinery on a 3x3).
    a,b,c = M_aug[Mrows[1],1], M_aug[Mrows[1],2], M_aug[Mrows[1],3]
    d,e,f = M_aug[Mrows[2],1], M_aug[Mrows[2],2], M_aug[Mrows[2],3]
    g,h,i = M_aug[Mrows[3],1], M_aug[Mrows[3],2], M_aug[Mrows[3],3]
    return a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)
end

function combinations3(n::Int)
    combos = Vector{Int}[]
    for i in 1:n-2, j in i+1:n-1, k in j+1:n
        push!(combos, [i,j,k])
    end
    return combos
end

row_combos = combinations3(n_eqs)

println("Reporting SIZE of each candidate minor's inputs before expanding")
println("(expansion of a 3x3 determinant of degree-~17-25 polys is itself")
println(" a nontrivial multiplication -- measure before committing).")
println()
for combo in row_combos
    degs = [total_degree(M_aug[r,c]) for r in combo, c in 1:3]
    println("  minor(rows=$combo): input entry degrees = ", vec(degs))
end
println()

if EXPAND_MINORS
    println("EXPAND_MINORS=true -- expanding minors (this may be slow/large):")
    for combo in row_combos
        m = minor_3x3(combo)
        println("  minor(rows=$combo): degree=$(iszero(m) ? -1 : total_degree(m))  terms=$(length(terms(m)))")
    end
else
    println("Skipping minor expansion (set EXPAND_MINORS=true to run it).")
    println("This is the next real cost center to measure -- do it as its own")
    println("timed step, not folded into a Groebner call.")
end

println()
println("Done.")
