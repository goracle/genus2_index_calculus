# jacobian_ell.jl
#
# Compute ell = largest prime factor of #J(C)(F_p) for
#   C : y^2 = x^5 + 3x^3 + 2x^2 + 5x + 4  over  F_p,  p = 1_000_003
#
# Strategy
# --------
# OSCAR (as of 2026) has elliptic-curve order counting (Hecke) but no
# built-in Jacobian order computation for genus-2 curves.  The standard
# tool for this is Sage's `HyperellipticCurve.frobenius_polynomial()`,
# which uses Kedlaya's p-adic algorithm (hypellfrob) and runs fast even
# for p ~ 10^6.
#
# This script shells out to Sage for the Frobenius polynomial chi(t), then
# uses OSCAR/Nemo for exact integer factorisation of N = chi(1) = #J(F_p).
#
# Requirements: Julia with Oscar.jl, and `sage` on PATH.

using Oscar

const p = ZZ(1_000_003)

# ---------------------------------------------------------------------------
# 1. Compute #J(F_p) via Sage (Kedlaya/hypellfrob)
# ---------------------------------------------------------------------------

sage_script = """
p = $(p)
F = GF(p)
R.<x> = F[]
f = x^5 + 3*x^3 + 2*x^2 + 5*x + 4
H = HyperellipticCurve(f)
chi = H.frobenius_polynomial()   # degree-4 Weil polynomial in ZZ[t]
N = ZZ(chi(1))                   # = #J(F_p)
print(int(N))
"""

println("─── Step 1: Computing Frobenius polynomial via Sage ───")
result = try
    readchomp(`sage -c $sage_script`)
catch e
    error("Failed to call Sage. Make sure `sage` is on your PATH.\n$e")
end

N = ZZ(parse(BigInt, strip(result)))
println("#J(F_p) = $N")
println()

# ---------------------------------------------------------------------------
# 2. Factorise N using OSCAR/Nemo (uses FLINT internally)
# ---------------------------------------------------------------------------

println("─── Step 2: Factoring #J(F_p) via Oscar/FLINT ───")
fac = factor(N)
println("Factorisation: $fac")
println()

# ---------------------------------------------------------------------------
# 3. Extract ell = largest prime factor
# ---------------------------------------------------------------------------

prime_factors = [q for (q, _) in fac]
ell = maximum(prime_factors)
cofactor = div(N, ell)
ell_bits = ndigits(BigInt(ell); base=2)

println("─── Result ───")
println("p         = $p")
println("#J        = $N")
println("ell       = $ell  ($ell_bits bits)")
println("cofactor  = $cofactor  (= #J / ell)")
println()
println("The Jacobian has a subgroup of prime order ell.")
suitable = BigInt(ell) > BigInt(2)^128 && BigInt(cofactor) <= 4
println("Suitable for HEC cryptography (ell > 2^128, cofactor <= 4): $suitable")
