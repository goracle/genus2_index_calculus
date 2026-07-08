#!/usr/bin/env julia
#
# diag_structure.jl -- test the hypothesis that the huge Fu/Fv denominators
# are structurally explained by det(A), the determinant of the (K+2)x(K+2)
# linear system symbolic_residual solves internally (see "4. Solve the
# matrix system directly over K_final" in trial3_phi_symbolic_unified.jl).
#
# By Cramer's rule, every entry of c_sol (hence every coefficient of
# E_poly and Y_poly) has denominator det(A). Both E_poly and Y_poly then
# SHARE that one scalar denominator -- meaning N(x)=E^2-f*Y^2 carries
# det(A)^2, and after exact division by (x-fixed)*(x-t1)*(x-t2)*u_poly
# and monic-normalization, u_RS/v_RS's denominators should still be
# expressible in terms of det(A) (to some power) rather than being
# independently-derived degree-16+ polynomials.
#
# If this holds, det(A) -- or a low-degree combination of det(A) for
# sample 1 and sample 2 -- should account for most of the degree-128
# blowup in Fu/Fv, and factor(Fu0) should show det(A)-related pieces
# with high multiplicity.

using Oscar

const PHI_GENERAL_SRC = joinpath(@__DIR__, "phi_general", "src")
include(joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl"))
using .PhiSymbolic

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]
F = GF(p)

# Rebuild the exact same linear system symbolic_residual builds internally,
# for a given (K,c,fixed_anchors,u0,u1,v0,v1), and return det(A) mapped
# into a plain 2-variable polynomial ring F[t1,t2] (valid whenever c==2
# and the tower's w-linear entries don't survive into the determinant --
# checked explicitly below, not assumed).
function build_A_and_det(K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}},
                          u0::Int, u1::Int, v0::Int, v1::Int)
    Fp = GF(p)
    R_t, t_vars = rational_function_field(Fp, ["t$i" for i in 1:c])

    K_curr = R_t
    w_vars = Any[]
    for i in 1:c
        f_ti = sum(K_curr(Fp(coeff)) * K_curr(t_vars[i])^(j-1) for (j, coeff) in enumerate(F_POLY_ASC))
        R_wi, wi_var = polynomial_ring(K_curr, "w$i")
        K_curr, _ = residue_ring(R_wi, wi_var^2 - f_ti)
        push!(w_vars, gen(K_curr))
        t_vars = [K_curr(tv) for tv in t_vars]
        for j in 1:(i-1)
            w_vars[j] = K_curr(w_vars[j])
        end
    end
    K_final = K_curr

    nb = K + 3
    basis = PhiSymbolic.rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]

    A = zero_matrix(K_final, n_unknowns, n_unknowns)

    anchor_pts = Vector{Tuple{elem_type(K_final), elem_type(K_final)}}(undef, K)
    for a in 1:(K-c)
        px_raw, py_raw = fixed_anchors[a]
        anchor_pts[a] = (K_final(px_raw), K_final(py_raw))
    end
    for i in 1:c
        anchor_pts[K-c+i] = (t_vars[i], w_vars[i])
    end

    for a in 1:K
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = (px^bi) * (bj == 1 ? py : K_final(1))
        end
    end

    max_basis_i = maximum(bi for (bi,_) in basis)
    r0tab, r1tab = PhiSymbolic.build_xmodu_table(max_basis_i + 1, u0, u1, p)
    row0, row1 = K + 1, K + 2
    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        rr0, rr1 = PhiSymbolic.reduce_monomial_mod_u(bi, bj, u0, u1, v0, v1, r0tab, r1tab, p)
        A[row0, col] = K_final(rr0)
        A[row1, col] = K_final(rr1)
    end

    detA = det(A)
    println("  det(A) computed over K_final.")

    # Full decomposition: det(A) as an element of K_final = (R_t[w1]/(w1^2-f1))[w2]/(w2^2-f2)
    # should have the shape p00 + p10*w1 + p01*w2 + p11*w1*w2 for RATIONAL
    # FUNCTIONS p00,p10,p01,p11 in (t1,t2) -- since each row of A contributes
    # at most one factor of w1 (from the w1-anchor row) and at most one
    # factor of w2 (from the w2-anchor row), by the Leibniz determinant
    # expansion. Extract all four pieces explicitly and confirm nothing
    # beyond degree-1-in-each survives.
    detA_poly = data(detA)          # degree <=1 in w2, coefficients in K1 = R_t[w1]/(w1^2-f1)
    d0 = coeff(detA_poly, 0)        # p00 + p10*w1   (an element of K1)
    d1 = coeff(detA_poly, 1)        # p01 + p11*w1   (an element of K1)

    d0_poly = data(d0)              # degree <=1 in w1, coefficients rational functions in t1,t2
    p00 = coeff(d0_poly, 0)
    p10 = coeff(d0_poly, 1)

    d1_poly = data(d1)
    p01 = coeff(d1_poly, 0)
    p11 = coeff(d1_poly, 1)

    println("  det(A) = p00 + p10*w1 + p01*w2 + p11*w1*w2")
    println("    p00 = ", iszero(p00) ? "0" : "nonzero, num deg=$(total_degree(numerator(p00))) den deg=$(total_degree(denominator(p00)))")
    println("    p10 = ", iszero(p10) ? "0" : "nonzero, num deg=$(total_degree(numerator(p10))) den deg=$(total_degree(denominator(p10)))")
    println("    p01 = ", iszero(p01) ? "0" : "nonzero, num deg=$(total_degree(numerator(p01))) den deg=$(total_degree(denominator(p01)))")
    println("    p11 = ", iszero(p11) ? "0" : "nonzero, num deg=$(total_degree(numerator(p11))) den deg=$(total_degree(denominator(p11)))")

    has_w2_term = !iszero(coeff(detA_poly, 1))
    println("  det(A) has a nonzero w$(c) coefficient? ", has_w2_term,
            has_w2_term ? "  <-- HYPOTHESIS PARTIALLY WRONG: det(A) has p01/p11 terms, not purely in t1,t2" :
                          "  <-- consistent with det(A) purely in t1,t2 (p01=p11=0)")

    return detA, K_final, t_vars, w_vars, (p00, p10, p01, p11)
end

println("=== Sample 1 (K=2, c=2) ===")
detA1, K_final1, tv1, wv1, pieces1 = build_A_and_det(2, 2, Tuple{Int,Int}[], 468873, 956582, 2168176, 2288437)

println()
println("=== Sample 2 (K=3, c=2) ===")
detA2, K_final2, tv2, wv2, pieces2 = build_A_and_det(3, 2, [(196, 793353)], 2112189, 375309, 801778, 2048138)

println()
println("Done. det(A) for each sample decomposes as p00 + p10*w1 + p01*w2 +")
println("p11*w1*w2 (Leibniz expansion: each row contributes at most one")
println("factor of w1, at most one of w2). Whether p01/p11 vanish (sample 1,")
println("0 fixed anchors) or not (sample 2, 1 fixed anchor) is a computed")
println("fact, not a general law -- but the SHAPE (at most 4 rational-")
println("function pieces in t1,t2) holds regardless. u_RS/v_RS denominators")
println("should reduce to products/powers of {p00,p10,p01,p11} (and the")
println("analogous pieces from computing 1/det(A) in the tower, which uses")
println("the norm p00^2 - p10^2*f(t1) - p01^2*f(t2) + p11^2*f(t1)*f(t2) +")
println("cross terms via w1*w2=w1*w2 directly -- i.e. inverting a tower")
println("element of this shape is itself a small, structured computation,")
println("not something that needs det(A) treated as an opaque black box).")
