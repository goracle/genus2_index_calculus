#!/usr/bin/env julia
#
# diag_norm.jl -- compute norm(det(A)) = det(A) * (its full tower conjugate)
# directly, for both samples, via the two-step conjugate-rationalization
# implied by det(A) = p00 + p10*w1 + p01*w2 + p11*w1*w2:
#
#   step 1 (kill w2):  (p00+p10*w1+p01*w2+p11*w1*w2) * (p00+p10*w1-p01*w2-p11*w1*w2)
#                     = (p00+p10*w1)^2 - (p01+p11*w1)^2 * f(t2)
#                     =: q0 + q1*w1      (still has w1, but no more w2)
#
#   step 2 (kill w1):  (q0+q1*w1) * (q0-q1*w1) = q0^2 - q1^2*f(t1)
#                     =: N(t1,t2)        a PLAIN polynomial in t1,t2
#
# N(t1,t2) is the true "denominator seed": 1/det(A) = conjugate(det(A)) /
# N(t1,t2) in the tower, so N(t1,t2) is (up to sign/units) the actual
# scalar denominator that should appear in u_RS/v_RS -- and it should be
# MUCH smaller than the degree-128 Fu0/Fu1 we got from raw coeff_equal
# cross-multiplication, since that path never rationalized first.

using Oscar

const PHI_GENERAL_SRC = joinpath(@__DIR__, "phi_general", "src")
include(joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl"))
using .PhiSymbolic

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]
F = GF(p)

function build_tower(c::Int)
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
    return K_curr, t_vars, w_vars
end

function build_A(K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}},
                  u0::Int, u1::Int, v0::Int, v1::Int, K_final, t_vars, w_vars)
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
    return A
end

# Decompose a K_final (c=2 tower) element into its 4 rational-function pieces.
function decompose4(val)
    val_poly = data(val)
    d0 = coeff(val_poly, 0)
    d1 = coeff(val_poly, 1)
    d0_poly = data(d0)
    d1_poly = data(d1)
    p00 = coeff(d0_poly, 0)
    p10 = coeff(d0_poly, 1)
    p01 = coeff(d1_poly, 0)
    p11 = coeff(d1_poly, 1)
    return p00, p10, p01, p11
end

function compute_norm(K::Int, c::Int, fixed_anchors::Vector{Tuple{Int,Int}},
                       u0::Int, u1::Int, v0::Int, v1::Int, label::String)
    println("=== $label (K=$K, c=$c) ===")
    K_final, t_vars, w_vars = build_tower(c)
    A = build_A(K, c, fixed_anchors, u0, u1, v0, v1, K_final, t_vars, w_vars)
    detA = det(A)

    p00, p10, p01, p11 = decompose4(detA)
    println("  p00,p10,p01,p11 nonzero? ", .!iszero.((p00,p10,p01,p11)))

    # These pieces are elements of the RATIONAL FUNCTION FIELD in (t1,t2)
    # (before any tower promotion), so we can get honest (num,den) pairs
    # for each directly via numerator()/denominator().
    Rbase = parent(numerator(p00))   # the plain poly ring F[t1,t2] underneath
    t1sym, t2sym = gens(Rbase)

    # f(t1), f(t2) as plain polynomials in Rbase
    f_t1 = sum(F(coeff) * t1sym^(j-1) for (j, coeff) in enumerate(F_POLY_ASC))
    f_t2 = sum(F(coeff) * t2sym^(j-1) for (j, coeff) in enumerate(F_POLY_ASC))

    # Work entirely with numerators (all four p's had den deg=0 per the
    # earlier probe, i.e. they're already plain polynomials -- but handle
    # the general case just in case that's sample-specific).
    P00 = iszero(p00) ? Rbase(0) : (isone(denominator(p00)) ? numerator(p00) : error("p00 has nontrivial denominator -- generalize this script"))
    P10 = iszero(p10) ? Rbase(0) : (isone(denominator(p10)) ? numerator(p10) : error("p10 has nontrivial denominator -- generalize this script"))
    P01 = iszero(p01) ? Rbase(0) : (isone(denominator(p01)) ? numerator(p01) : error("p01 has nontrivial denominator -- generalize this script"))
    P11 = iszero(p11) ? Rbase(0) : (isone(denominator(p11)) ? numerator(p11) : error("p11 has nontrivial denominator -- generalize this script"))

    println("  degrees: P00=", total_degree(P00), " P10=", iszero(P10) ? -1 : total_degree(P10),
            " P01=", iszero(P01) ? -1 : total_degree(P01), " P11=", iszero(P11) ? -1 : total_degree(P11))

    # step 1: kill w2.  q0 + q1*w1 = (P00+P10*w1)^2 - (P01+P11*w1)^2 * f(t2)
    # expand (P00+P10*w1)^2 = P00^2 + 2*P00*P10*w1 + P10^2*w1^2, and w1^2 = f(t1)
    # so (P00+P10*w1)^2 = (P00^2 + P10^2*f(t1)) + (2*P00*P10)*w1
    A2_0 = P00^2 + P10^2 * f_t1
    A2_1 = 2*P00*P10

    B2_0 = P01^2 + P11^2 * f_t1
    B2_1 = 2*P01*P11

    q0 = A2_0 - B2_0 * f_t2
    q1 = A2_1 - B2_1 * f_t2

    println("  after step1 (kill w2): q0 deg=", iszero(q0) ? -1 : total_degree(q0),
            "  q1 deg=", iszero(q1) ? -1 : total_degree(q1))

    # step 2: kill w1.  N = q0^2 - q1^2 * f(t1)
    N = q0^2 - q1^2 * f_t1

    println("  N(t1,t2) = norm(det(A)):  degree=", iszero(N) ? -1 : total_degree(N),
            "  terms=", iszero(N) ? 0 : length(terms(N)))

    return N
end

N1 = compute_norm(2, 2, Tuple{Int,Int}[], 468873, 956582, 2168176, 2288437, "Sample 1")
println()
N2 = compute_norm(3, 2, [(196, 793353)], 2112189, 375309, 801778, 2048138, "Sample 2")

println()
println("If N1/N2 are much smaller than degree 128 (they should be -- norm")
println("of a degree ~5 quantity through two squarings tops out around")
println("degree 20-40, not 128), that confirms the raw coeff_equal cross-")
println("multiplication path is generating a LOT of spurious bulk that a")
println("rationalize-first approach avoids. Next: factor N1, N2 directly")
println("(small polys) and compare against the factor() results we'd get")
println("from the current elim2.jl on Fu0, to see how much of the degree-128")
println("blowup that factoring pass was fighting through unnecessarily.")

println()
println("factor(N1):")
println(factor(N1))
println()
println("factor(N2):")
println(factor(N2))
