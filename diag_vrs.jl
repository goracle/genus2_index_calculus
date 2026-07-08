#!/usr/bin/env julia
#
# diag_vrs.jl -- trace WHY v_RS (and hence Fv0/Fv1) comes out structurally
# bigger than u_RS (Fu0/Fu1): degree 48 vs 32 in the last full elim2.jl
# run. u_RS comes from a plain divexact chain (deterministic, denominator
# growth bounded by det(A) alone, per diag_norm.jl). v_RS additionally
# requires gcdx(Y_poly, u_RS) to compute Y_inv_mod -- an extended
# Euclidean algorithm over the tower field, which for two polynomials
# with rational-function coefficients typically introduces ITS OWN
# resultant-like denominator on top of whatever Y_poly/u_RS already carry.
# This script isolates that step directly.

using Oscar

const PHI_GENERAL_SRC = joinpath(@__DIR__, "phi_general", "src")
include(joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl"))
using .PhiSymbolic

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]
F = GF(p)

# Reproduce symbolic_residual's internals up through Y_poly/u_RS, but keep
# every intermediate object instead of just returning coefficients.
function trace_sample(K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}},
                       u0::Int, u1::Int, v0::Int, v1::Int, label::String)
    println("=== $label (K=$K, c=$c) ===")

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
    Kx, X = polynomial_ring(K_final, "X")

    nb = K + 3
    basis = PhiSymbolic.rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    n_unknowns = K + 2
    other_idx = [idx for idx in 1:nb if idx != y_idx]

    A = zero_matrix(K_final, n_unknowns, n_unknowns)
    rhs = zero_matrix(K_final, n_unknowns, 1)
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
        bi_n, bj_n = basis[y_idx]
        rhs[a, 1] = -((px^bi_n) * (bj_n == 1 ? py : K_final(1)))
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
    bi_n, bj_n = basis[y_idx]
    rn0, rn1 = PhiSymbolic.reduce_monomial_mod_u(bi_n, bj_n, u0, u1, v0, v1, r0tab, r1tab, p)
    rhs[row0, 1] = K_final(mod(-rn0, p))
    rhs[row1, 1] = K_final(mod(-rn1, p))

    c_sol = solve(A, rhs; side = :right)
    coeffs_out = Vector{elem_type(K_final)}(undef, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c_sol[col, 1]
    end
    coeffs_out[y_idx] = K_final(1)

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

    println("  deg(E_poly)=", degree(E_poly), "  deg(Y_poly)=", degree(Y_poly))

    f_poly_Kx = sum(K_final(coeff) * X^(i-1) for (i, coeff) in enumerate(F_POLY_ASC))
    Nx = E_poly^2 - f_poly_Kx * Y_poly^2

    cur = Nx
    for (px_raw, _) in fixed_anchors
        cur = divexact(cur, X - K_final(px_raw))
    end
    for i in 1:c
        cur = divexact(cur, X - t_vars[i])
    end
    u_poly_Kx = X^2 + K_final(u1)*X + K_final(u0)
    cur = divexact(cur, u_poly_Kx)
    u_RS = cur * inv(leading_coefficient(cur))

    println("  deg(u_RS)=", degree(u_RS))

    # Now the v_RS step -- this is what we're isolating.
    println("  Computing gcdx(Y_poly, u_RS)...")
    g, Y_inv_mod, other = gcdx(Y_poly, u_RS)
    println("  gcd degree = ", degree(g))
    println("  Y_inv_mod degree (as poly in X) = ", degree(Y_inv_mod))

    # Y_inv_mod's coefficients are tower elements -- decompose the x^0
    # coefficient (representative) the same way we decomposed det(A), to
    # see its denominator size directly.
    yi_c0 = coeff(Y_inv_mod, 0)
    yi_poly = data(yi_c0)
    d0 = coeff(yi_poly, 0)
    d1 = c == 2 ? coeff(yi_poly, 1) : K_final(0)
    if c == 2
        d0_poly = data(d0)
        p00 = coeff(d0_poly, 0)
        p10 = coeff(d0_poly, 1)
        d1_poly = data(d1)
        p01 = coeff(d1_poly, 0)
        p11 = coeff(d1_poly, 1)
        println("  Y_inv_mod's x^0 coeff denominator degrees:")
        for (nm, pp) in [("p00",p00),("p10",p10),("p01",p01),("p11",p11)]
            if !iszero(pp)
                dd = denominator(pp)
                println("    $nm: num deg=", total_degree(numerator(pp)), "  den deg=", total_degree(dd))
            end
        end
    end

    v_RS = mod(-E_poly * Y_inv_mod, u_RS)
    println("  deg(v_RS)=", degree(v_RS))
    println()

    return (E_poly, Y_poly, u_RS, Y_inv_mod, v_RS)
end

trace_sample(2, 2, Tuple{Int,Int}[], 468873, 956582, 2168176, 2288437, "Sample 1")
trace_sample(3, 2, [(196, 793353)], 2112189, 375309, 801778, 2048138, "Sample 2")

println("If Y_inv_mod's denominator (p00/p10/p01/p11 degrees above) is")
println("noticeably bigger than det(A)'s own degrees from diag_structure.jl")
println("(5,4,4,0 for sample 1/2's det(A) pieces), that confirms gcdx is")
println("introducing genuine extra denominator growth on top of det(A) --")
println("i.e. v_RS structurally needs MORE denominator than u_RS does, which")
println("would explain Fv0/Fv1 (degree 48) being bigger than Fu0/Fu1")
println("(degree 32) as real content, not something further reducible by")
println("the same gcd trick already applied in elim2.jl's _tower_to_ring.")
