#!/usr/bin/env julia
#
# sign_dependence_test.jl
#
# Question: does U0 (equivalently U1) depend on the SIGN of w_a1 -- i.e.
# on which of the two curve points (a1, +w_a1) / (a1, -w_a1) was actually
# picked as the factor base element -- or only on the x-coordinate a1
# itself?
#
# This matters directly for the meet-in-the-middle table design (see
# chat): if U0 only depends on a1,a2 (equivalently on s1=a1+a2, s2=a1*a2,
# GIVEN the already-confirmed a1<->a2 swap symmetry), the O(B^2)
# precomputed table can be built purely from x-coordinate pairs. If it
# depends on the actual sign choice too, the table must be indexed by
# the actual factor-base POINT pairs (still O(B^2) many, since each
# x-coordinate has a definite, fixed sign once you're restricted to
# points that are actually in the factor base -- no combinatorial
# blowup, just a reminder that x-coordinate alone isn't enough
# information).
#
# Method: reuse the shared-tower construction from reorder_test.jl,
# solve for U0 with (a1, +wa1_k) as the first anchor, then solve AGAIN
# with (a1, -wa1_k) -- same a1, same a2, same wa2 -- and diff the two
# U0 values symbolically. If the difference is identically zero, sign
# doesn't matter. If nonzero, it does.
#
# This is a NEW, separate script -- does not modify elim2.jl,
# reorder_test.jl, or trial3_phi_symbolic_unified.jl.
#
# Usage: julia -t 1 sign_dependence_test.jl

using Oscar

const HERE = @__DIR__
const CANDIDATE_PATHS = [
    joinpath(HERE, "trial3_phi_symbolic_unified.jl"),
    joinpath(HERE, "phi_general", "src", "trial3_phi_symbolic_unified.jl"),
    joinpath(HERE, "phi_general", "phi_general", "src", "trial3_phi_symbolic_unified.jl"),
]
const ENGINE_PATH = let idx = findfirst(isfile, CANDIDATE_PATHS)
    idx === nothing && error("sign_dependence_test.jl: trial3_phi_symbolic_unified.jl not found in any of: $CANDIDATE_PATHS")
    CANDIDATE_PATHS[idx]
end
include(ENGINE_PATH)
using .PhiSymbolic: rr_basis, build_xmodu_table, reduce_monomial_mod_u

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2
F = GF(p)

# Only need ONE sample's worth of anchors here -- this question is about
# a single sample's internal structure (does its own U0 depend on the
# sign of its own w's), not about matching two samples against each
# other. Reuse sample 1's data from elim2.jl/reorder_test.jl.
const K1, c1 = 2, 2
const fixed1 = Tuple{Int,Int}[]
const u0_1, u1_1, v0_1, v1_1 = 468873, 956582, 2168176, 2288437

################################################################################
# Build a 2-variable tower (just a1,a2/wa1,wa2 -- no need for the b's
# here, this is a single-sample question). Function-scoped, same reason
# as reorder_test.jl's build_shared_tower: top-level `for` loops in
# Julia scripts have soft-scope rules that make reassigning loop-carried
# state ambiguous.
################################################################################

function build_tower_2var(F, F_POLY_ASC)
    R_t, (a1, a2) = rational_function_field(F, ["a1", "a2"])
    t_vars = Any[a1, a2]
    w_names = ["wa1", "wa2"]
    K_curr = R_t
    w_vars = Any[]
    for i in 1:2
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

println("Building 2-variable tower Fp(a1,a2)[wa1,wa2]/(...)")
flush(stdout)
K2v, t_vars, w_vars = build_tower_2var(F, F_POLY_ASC)
a1_k, a2_k = t_vars
wa1_k, wa2_k = w_vars
println("Tower built.")
println()

################################################################################
# Same linear-system solve as reorder_test.jl's solve_u0_in_shared_tower,
# but also returning U1 (the x^1 coefficient of u_RS), since we want to
# check both, not just U0.
################################################################################

function solve_u0_u1(Kshared, anchor_t_1, anchor_w_1, anchor_t_2, anchor_w_2,
                      K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}},
                      u0::Int, u1::Int, v0::Int, v1::Int, p::Int)
    Kx, X = polynomial_ring(Kshared, "X")

    nb = K + 3
    basis = rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0, 1), basis)
    y_idx === nothing && error("solve_u0_u1: rr_basis missing (0,1) entry")

    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]

    A = zero_matrix(Kshared, n_unknowns, n_unknowns)
    rhs = zero_matrix(Kshared, n_unknowns, 1)

    anchor_pts = Vector{Tuple{elem_type(Kshared),elem_type(Kshared)}}(undef, K)
    for a in 1:(K - c)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (Kshared(px_raw), Kshared(py_raw))
    end
    c == 2 || error("solve_u0_u1: this script assumes c=2, got c=$c")
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
    iszero(cur) && error("solve_u0_u1: u_RS division produced zero -- degenerate sample")

    u_RS = cur * inv(leading_coefficient(cur))
    U0 = coeff(u_RS, 0)
    U1 = coeff(u_RS, 1)
    return U0, U1
end

################################################################################
# Solve with +wa1_k, then again with -wa1_k. Same a1, a2, wa2 both times
# -- only the sign of the FIRST anchor's w flips. If U0/U1 are
# invariant, the table can be indexed by (a1,a2) alone (or s1,s2, given
# the already-confirmed a1<->a2 swap symmetry). If not, it needs the
# actual point pair.
################################################################################

println("Solving with anchor 1 = (a1, +wa1)...")
flush(stdout)
t0 = time()
U0_plus, U1_plus = solve_u0_u1(K2v, a1_k, wa1_k, a2_k, wa2_k,
                                K1, c1, fixed1, u0_1, u1_1, v0_1, v1_1, p)
println("  done in ", round(time() - t0, digits=3), "s")

println("Solving with anchor 1 = (a1, -wa1)...")
flush(stdout)
t0 = time()
U0_minus, U1_minus = solve_u0_u1(K2v, a1_k, -wa1_k, a2_k, wa2_k,
                                  K1, c1, fixed1, u0_1, u1_1, v0_1, v1_1, p)
println("  done in ", round(time() - t0, digits=3), "s")
println()

println("Comparing U0(+wa1) vs U0(-wa1)...")
flush(stdout)
diff_U0 = U0_plus - U0_minus
println("Comparing U1(+wa1) vs U1(-wa1)...")
diff_U1 = U1_plus - U1_minus
println()

println("="^70)
println("RESULT")
println("="^70)
println("U0 sign-invariant (U0_plus == U0_minus)?  ", iszero(diff_U0))
println("U1 sign-invariant (U1_plus == U1_minus)?  ", iszero(diff_U1))
println()
if iszero(diff_U0) && iszero(diff_U1)
    println("U0, U1 depend ONLY on the x-coordinates a1,a2 -- NOT on which")
    println("point (which sign of w) was chosen. Combined with the earlier")
    println("a1<->a2 swap symmetry, the meet-in-the-middle table can be built")
    println("over (s1,s2) = (a1+a2, a1*a2) alone: O(B^2) distinct x-coordinate")
    println("pairs, no need to track sign/point identity separately.")
else
    println("U0 and/or U1 DEPEND on the sign of wa1 -- i.e. on which actual")
    println("curve point was chosen, not just its x-coordinate. The")
    println("meet-in-the-middle table must be indexed by the actual")
    println("factor-base POINT pairs (still O(B^2) many total, since each")
    println("factor-base x-coordinate has one fixed, definite sign -- this")
    println("does not reintroduce a factor of B, it just means x-coordinate")
    println("alone is not a sufficient table key).")
end
