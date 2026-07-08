#!/usr/bin/env julia
#
# diag_k3.jl -- pinpoint why symbolic_residual(K=3, c=2, ...) returns
# degenerate for the sample-2 parameters. This is a copy of
# symbolic_residual's body with a println at every early-return so we can
# see exactly which guard fires, instead of guessing.

using Oscar

const PHI_GENERAL_SRC = joinpath(@__DIR__, "phi_general", "src")
include(joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl"))
using .PhiSymbolic

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]

# sample 2 params
K = 3
c = 2
fixed_anchors = Tuple{Int,Int}[]
u0, u1, v0, v1 = 1974853, 360394, 1287699, 528456

println("K=$K c=$c fixed_anchors=$fixed_anchors")
println("K < c ? ", K < c)
println("length(fixed_anchors) != K - c ? ", length(fixed_anchors) != K - c, "  (K-c=$(K-c))")

if K < c || length(fixed_anchors) != K - c
    error("would degenerate at guard 1 (K<c or wrong fixed_anchors length)")
end

Fp = GF(p)
R_t, t_vars = rational_function_field(Fp, ["t$i" for i in 1:c])

K_curr = R_t
w_vars = Any[]

for i in 1:c
    global K_curr
    f_ti = sum(K_curr(Fp(coeff)) * K_curr(t_vars[i])^(j-1) for (j, coeff) in enumerate(F_POLY_ASC))
    R_wi, wi_var = polynomial_ring(K_curr, "w$i")
    K_curr, _ = residue_ring(R_wi, wi_var^2 - f_ti)
    push!(w_vars, gen(K_curr))
    global t_vars = [K_curr(tv) for tv in t_vars]
    for j in 1:(i-1)
        w_vars[j] = K_curr(w_vars[j])
    end
end

K_final = K_curr
Kx, X = polynomial_ring(K_final, "X")

nb = K + 3
basis = PhiSymbolic.rr_basis(nb)
y_idx = findfirst(bi -> bi == (0,1), basis)
println("y_idx = ", y_idx, "  (nothing means guard 2 fires)")
if y_idx === nothing
    error("would degenerate at guard 2 (no (0,1) in rr_basis)")
end

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

println("Attempting solve(A, rhs)...")
local c_sol
try
    global c_sol = solve(A, rhs; side = :right)
    println("solve() SUCCEEDED")
catch e
    println("solve() FAILED (this is guard 3 -- the degenerate cause): ", e)
    error("stopping here, guard 3 fired")
end

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
    global E_poly, Y_poly
    if bj == 0
        E_poly += c_here * X^bi
    else
        Y_poly += c_here * X^bi
    end
end

deg_E = iszero(E_poly) ? -1 : degree(E_poly)
deg_Y = iszero(Y_poly) ? -1 : degree(Y_poly)
println("deg_E = $deg_E, deg_Y = $deg_Y")

f_poly_Kx = sum(K_final(coeff) * X^(i-1) for (i, coeff) in enumerate(F_POLY_ASC))
Nx = E_poly^2 - f_poly_Kx * Y_poly^2
n_len_before_divide = iszero(Nx) ? 0 : degree(Nx) + 1
println("n_len_before_divide = $n_len_before_divide  (deg(N) = $(n_len_before_divide - 1))")

cur = Nx
for (px_raw, _) in fixed_anchors
    global cur
    cur = divexact(cur, X - K_final(px_raw))
end
for i in 1:c
    global cur
    cur = divexact(cur, X - t_vars[i])
end

u_poly_Kx = X^2 + K_final(u1)*X + K_final(u0)
cur = divexact(cur, u_poly_Kx)

println("iszero(cur) after all division? ", iszero(cur), "  <-- guard 4 if true")
if iszero(cur)
    error("would degenerate at guard 4 (cur==0 after division by (x-anchors)*u_poly)")
end

u_RS = cur * inv(leading_coefficient(cur))
println("u_RS degree = ", degree(u_RS))

println("iszero(Y_poly)? ", iszero(Y_poly), "  <-- guard 5 if true")
if iszero(Y_poly)
    error("would degenerate at guard 5 (Y_poly==0, can't compute v_RS)")
end

_, Y_inv_mod, _ = gcdx(Y_poly, u_RS)
v_RS = mod(-E_poly * Y_inv_mod, u_RS)

println()
println("SUCCESS -- no guard fired. u_RS/v_RS should have been non-empty.")
println("u_RS coeffs: ", collect(coefficients(u_RS)))
println("v_RS coeffs: ", collect(coefficients(v_RS)))
