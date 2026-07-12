#!/usr/bin/env julia
#
# reorder_test.jl
#
# Tests the reordering idea from chat: instead of
#
#   (existing pipeline)
#     1. tower_to_ring: flatten each sample's U_0 into (num,den) over a
#        PLAIN polynomial ring (wa1,wa2,a1,a2) / (wb1,wb2,b1,b2)
#     2. eliminate w's per sample -> g1(a1,a2,U0), g2(b1,b2,U0)  [deg 36,34]
#     3. resultant/eliminate over U0 -> relation in (a1,a2,b1,b2)  [deg ~230+, OOM risk]
#
# this script tries:
#
#   (reordered pipeline)
#     1. build sample 1 and sample 2's U_0 as elements of a SHARED tower
#        field with base rational_function_field(Fp, [a1,a2,b1,b2])
#        (4 base vars, 4 w-layers -- one per anchor across BOTH samples)
#     2. compute U_0 - U_0' as ONE subtraction in that shared field --
#        Oscar's rational_function_field arithmetic reduces
#        numerator/denominator by gcd automatically at every step, so any
#        cancellation between sample 1's and sample 2's denominators is
#        caught HERE, symbolically, before anything is forced into a
#        dense plain-ring representation
#     3. ONLY THEN flatten the (still possibly reduced) tower fraction
#        into a plain ring and eliminate the w's
#
# The question this answers: does step 2's shared-field subtraction
# produce something smaller than Fu0's degree-32/~30k-term
# cross-multiplication, i.e. does symbolic reduction inside the tower
# catch cancellation the manual _tower_to_ring/coeff_equal pipeline misses?
#
# This is a NEW, separate script -- it does not modify elim2.jl or
# trial3_phi_symbolic_unified.jl. It re-derives U_0 from scratch for a
# custom 4-variable tower by copying (not calling) symbolic_residual's
# linear-system construction, since symbolic_residual itself always
# builds a tower sized to ONE sample's own c, not a shared cross-sample
# tower -- see chat for why this can't just call symbolic_residual twice
# and combine the results afterward.
#
# Usage: julia -t 1 reorder_test.jl
# (single-threaded on purpose -- this is a diagnostic, not a production
# run, and threading bugs are not worth debugging for a one-shot test)

using Oscar

const HERE = @__DIR__
const CANDIDATE_PATHS = [
    joinpath(HERE, "trial3_phi_symbolic_unified.jl"),
    joinpath(HERE, "phi_general", "src", "trial3_phi_symbolic_unified.jl"),
    joinpath(HERE, "phi_general", "phi_general", "src", "trial3_phi_symbolic_unified.jl"),
]
const ENGINE_PATH = let idx = findfirst(isfile, CANDIDATE_PATHS)
    idx === nothing && error("reorder_test.jl: trial3_phi_symbolic_unified.jl not found in any of: $CANDIDATE_PATHS")
    CANDIDATE_PATHS[idx]
end
include(ENGINE_PATH)
using .PhiSymbolic: rr_basis, build_xmodu_table, reduce_monomial_mod_u

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2
F = GF(p)

################################################################################
# Sample data -- same as elim2.jl.
################################################################################

const K1, c1 = 2, 2
const fixed1 = Tuple{Int,Int}[]
const u0_1, u1_1, v0_1, v1_1 = 468873, 956582, 2168176, 2288437

const K2, c2 = 3, 2
const fixed2 = [(196, 793353)]
const u0_2, u1_2, v0_2, v1_2 = 2112189, 375309, 801778, 2048138

################################################################################
# Build ONE shared tower with base field Fp(a1,a2,b1,b2) and 4 w-layers:
# w_a1 -> a1, w_a2 -> a2, w_b1 -> b1, w_b2 -> b2 (in that construction
# order). This mirrors symbolic_residual's own tower-building loop
# (trial3_phi_symbolic_unified.jl lines 240-266) but with 4 base
# variables shared across what were previously two independent towers.
################################################################################

println("Building shared 4-variable tower field Fp(a1,a2,b1,b2)[wa1,wa2,wb1,wb2]/(...)")
flush(stdout)

function build_shared_tower(F, F_POLY_ASC)
    R_t, (a1, a2, b1, b2) = rational_function_field(F, ["a1", "a2", "b1", "b2"])

    t_vars = Any[a1, a2, b1, b2]
    w_names = ["wa1", "wa2", "wb1", "wb2"]
    K_curr = R_t
    w_vars = Any[]

    for i in 1:4
        f_ti = sum(K_curr(F(coeff)) * K_curr(t_vars[i])^(j - 1) for (j, coeff) in enumerate(F_POLY_ASC))
        R_wi, wi_var = polynomial_ring(K_curr, w_names[i])
        K_curr, _ = residue_ring(R_wi, wi_var^2 - f_ti)
        push!(w_vars, gen(K_curr))
        t_vars = [K_curr(tv) for tv in t_vars]
        for j in 1:(i - 1)
            w_vars[j] = K_curr(w_vars[j])
        end
    end

    return K_curr, t_vars, w_vars
end

K_shared, t_vars, w_vars = build_shared_tower(F, F_POLY_ASC)
a1_k, a2_k, b1_k, b2_k = t_vars
wa1_k, wa2_k, wb1_k, wb2_k = w_vars

println("Shared tower built. K_shared = ", K_shared)
println()

################################################################################
# Solve sample 1's linear system DIRECTLY inside K_shared (using only the
# a1,a2/wa1,wa2 slots -- b1,b2/wb1,wb2 simply never appear in sample 1's
# construction, so this is exact, not an approximation).
#
# This is a copy of symbolic_residual's steps 3-8 (trial3_phi_symbolic_unified.jl
# lines 268-397), generalized to solve INSIDE an already-built shared
# tower instead of building its own tower first. Kept as a local function
# so it can be called once per sample with different anchor variables.
################################################################################

function solve_u0_in_shared_tower(Kshared, anchor_t_1, anchor_w_1, anchor_t_2, anchor_w_2,
                                   K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}},
                                   u0::Int, u1::Int, v0::Int, v1::Int, p::Int)
    Kx, X = polynomial_ring(Kshared, "X")

    nb = K + 3
    basis = rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0, 1), basis)
    y_idx === nothing && error("solve_u0_in_shared_tower: rr_basis missing (0,1) entry")

    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]

    A = zero_matrix(Kshared, n_unknowns, n_unknowns)
    rhs = zero_matrix(Kshared, n_unknowns, 1)

    anchor_pts = Vector{Tuple{elem_type(Kshared),elem_type(Kshared)}}(undef, K)
    for a in 1:(K - c)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (Kshared(px_raw), Kshared(py_raw))
    end
    # c is always 2 for both our samples -- wire the two symbolic anchors
    # to the two shared-tower generators passed in explicitly (avoids any
    # ordering ambiguity about which anchor is "first").
    c == 2 || error("solve_u0_in_shared_tower: this script assumes c=2, got c=$c")
    anchor_pts[K - c + 1] = (anchor_t_1, anchor_w_1)
    anchor_pts[K - c + 2] = (anchor_t_2, anchor_w_2)

    for a in 1:K
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = (px^bi) * (bj == 1 ? py : Kshared(1))
        end
        bi_n, bj_n = basis[y_idx]
        rhs[a, 1] = -((px^bi_n) * (bj_n == 1 ? py : Kshared(1)))
    end

    max_basis_i = maximum(bi for (bi, _) in basis)
    r0tab, r1tab = build_xmodu_table(max_basis_i + 1, u0, u1, p)
    row0, row1 = K + 1, K + 2

    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        rr0, rr1 = reduce_monomial_mod_u(bi, bj, u0, u1, v0, v1, r0tab, r1tab, p)
        A[row0, col] = Kshared(rr0)
        A[row1, col] = Kshared(rr1)
    end

    bi_n, bj_n = basis[y_idx]
    rn0, rn1 = reduce_monomial_mod_u(bi_n, bj_n, u0, u1, v0, v1, r0tab, r1tab, p)
    rhs[row0, 1] = Kshared(mod(-rn0, p))
    rhs[row1, 1] = Kshared(mod(-rn1, p))

    c_sol = solve(A, rhs; side=:right)

    coeffs_out = Vector{elem_type(Kshared)}(undef, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c_sol[col, 1]
    end
    coeffs_out[y_idx] = Kshared(1)

    E_poly = Kx(0)
    Y_poly = Kx(0)
    for bidx in 1:nb
        bi, bj = basis[bidx]
        c_here = coeffs_out[bidx]
        if bj == 0
            E_poly += c_here * X^bi
        else
            Y_poly += c_here * X^bi
        end
    end

    f_poly_Kx = sum(Kshared(coeff) * X^(i - 1) for (i, coeff) in enumerate(F_POLY_ASC))
    Nx = E_poly^2 - f_poly_Kx * Y_poly^2

    cur = Nx
    for (px_raw, _) in fixed_anchors
        cur = divexact(cur, X - Kshared(px_raw))
    end
    cur = divexact(cur, X - anchor_t_1)
    cur = divexact(cur, X - anchor_t_2)

    u_poly_Kx = X^2 + Kshared(u1) * X + Kshared(u0)
    cur = divexact(cur, u_poly_Kx)
    iszero(cur) && error("solve_u0_in_shared_tower: u_RS division produced zero -- degenerate sample")

    u_RS = cur * inv(leading_coefficient(cur))
    # Return U0 = the constant coefficient of the monic quadratic u_RS(x) = x^2+U1*x+U0
    return coeff(u_RS, 0)
end

println("Solving sample 1's U0 inside the shared tower (anchors -> a1,a2/wa1,wa2)...")
flush(stdout)
t0 = time()
U0_sample1 = solve_u0_in_shared_tower(K_shared, a1_k, wa1_k, a2_k, wa2_k,
                                       K1, c1, fixed1, u0_1, u1_1, v0_1, v1_1, p)
println("  done in ", round(time() - t0, digits=3), "s")

println("Solving sample 2's U0 inside the shared tower (anchors -> b1,b2/wb1,wb2)...")
flush(stdout)
t0 = time()
U0_sample2 = solve_u0_in_shared_tower(K_shared, b1_k, wb1_k, b2_k, wb2_k,
                                       K2, c2, fixed2, u0_2, u1_2, v0_2, v1_2, p)
println("  done in ", round(time() - t0, digits=3), "s")
println()

################################################################################
# THE KEY STEP: subtract inside the shared field, before any plain-ring
# flattening. Oscar's tower/field arithmetic reduces at every operation,
# so this exercises whatever built-in cancellation the field structure
# offers -- something the manual _tower_to_ring + coeff_equal pipeline
# in elim2.jl never gets a chance to do, since it flattens to a plain
# ring (no automatic gcd on every +,-,*) before cross-multiplying.
################################################################################

println("Computing U0_sample1 - U0_sample2 as ONE shared-field subtraction...")
flush(stdout)
t0 = time()
diff = U0_sample1 - U0_sample2
println("  done in ", round(time() - t0, digits=3), "s")
println()

################################################################################
# Now flatten the result (a single tower element, level=4 above the base
# field) into a plain polynomial ring, and report its size -- this is the
# number to compare against Fu0's degree=32 / terms=29889 from the
# existing pipeline's log.
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

function _tower_to_ring(val, level::Int, t_gens::Vector, w_gens::Vector)
    if level == 0
        return _base_frac_to_ring(val, t_gens)
    end
    val_poly = data(val)
    c0 = coeff(val_poly, 0)
    c1 = coeff(val_poly, 1)
    n0, d0 = _tower_to_ring(c0, level - 1, t_gens, w_gens)
    n1, d1 = _tower_to_ring(c1, level - 1, t_gens, w_gens)
    wv = w_gens[level]
    num = n0 * d1 + n1 * d0 * wv
    den = d0 * d1
    return _reduce_frac(num, den)
end

Rplain, (wa1_p, wa2_p, wb1_p, wb2_p, a1_p, a2_p, b1_p, b2_p) = polynomial_ring(
    F, ["wa1", "wa2", "wb1", "wb2", "a1", "a2", "b1", "b2"]
)

println("Flattening (U0_sample1 - U0_sample2) into the plain ring...")
flush(stdout)
t0 = time()
num_final, den_final = _tower_to_ring(diff, 4, [a1_p, a2_p, b1_p, b2_p], [wa1_p, wa2_p, wb1_p, wb2_p])
println("  done in ", round(time() - t0, digits=3), "s")
println()

println("="^70)
println("RESULT: reordered (shared-tower-subtraction-first) construction")
println("="^70)
println("  numerator:   degree=", total_degree(num_final), "  terms=", length(terms(num_final)))
println("  denominator: degree=", total_degree(den_final), "  terms=", length(terms(den_final)))
println()
println("Compare to the EXISTING pipeline's Fu0 (flatten-then-cross-multiply):")
println("  Fu0: degree=32  terms=29889   (from err2.txt)")
println()
if total_degree(num_final) < 32 || length(terms(num_final)) < 29889
    println("REORDERING WINS on this metric -- shared-field subtraction found")
    println("cancellation the flatten-then-cross-multiply pipeline missed.")
    println("Worth rebuilding the full U0/U1/V0/V1 pipeline this way.")
elseif total_degree(num_final) == 32 && length(terms(num_final)) == 29889
    println("IDENTICAL to Fu0 -- as expected if this is just Fu0's own")
    println("numerator, reconstructed via a different route with no extra")
    println("cancellation available. Reordering does not help here; the")
    println("resultant-on-w-eliminated-samples route (PART H/I/J, already")
    println("proven to work per-sample) remains the best lever.")
else
    println("LARGER than Fu0 -- reordering made things worse here. Do not")
    println("pursue this route further without understanding why.")
end
