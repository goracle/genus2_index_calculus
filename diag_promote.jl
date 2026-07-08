#!/usr/bin/env julia
#
# diag_promote.jl -- isolate exactly how a fixed anchor's concrete
# (px_raw, py_raw) gets promoted into K_final, and whether that promotion
# is genuinely responsible for det(A) picking up w2-dependence in the
# K=3,c=2 sample -- or whether something more subtle is going on (e.g.
# w2-dependence showing up in det(A) for reasons unrelated to the fixed
# anchor's y-value promotion itself, such as row/column structure).

using Oscar

const PHI_GENERAL_SRC = joinpath(@__DIR__, "phi_general", "src")
include(joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl"))
using .PhiSymbolic

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]
F = GF(p)

c = 2
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

K_final, t_vars, w_vars = build_tower(c)

println("K_final = ", K_final)
println()

# The fixed anchor from sample 2: (196, 793353)
px_raw, py_raw = 196, 793353

px_final = K_final(px_raw)
py_final = K_final(py_raw)

println("px_final = K_final(196)  = ", px_final)
println("py_final = K_final(793353) = ", py_final)
println()

px_poly = data(px_final)
py_poly = data(py_final)

println("data(px_final) = ", px_poly, "   coeff(.,1) [w2-part] = ", coeff(px_poly, 1))
println("data(py_final) = ", py_poly, "   coeff(.,1) [w2-part] = ", coeff(py_poly, 1))
println()

println("Sanity: is py_final actually just the constant Fp(793353), or does")
println("K_final(::Int) somehow route through the tower nontrivially?")
println("iszero(coeff(py_poly,1))? ", iszero(coeff(py_poly, 1)))
println()

# Now check px^bi * py -- a typical matrix entry -- for a couple of small
# (bi,bj) values, to see whether the PRODUCT introduces w2-dependence
# even if py_final itself doesn't.
basis_test = PhiSymbolic.rr_basis(5)
println("A few basis (bi,bj) pairs: ", basis_test)
for (bi, bj) in basis_test[1:min(5,end)]
    entry = (px_final^bi) * (bj == 1 ? py_final : K_final(1))
    entry_poly = data(entry)
    println("  (bi=$bi,bj=$bj): entry = ", entry, "   w2-coeff = ", coeff(entry_poly, 1))
end
