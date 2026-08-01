# Quick check: does x^2+x+1 and x^3-x^2+1 factor mod p=2371157?
using Oscar
p = 2371157
Fp, _ = finite_field(p)
Fpx, x = polynomial_ring(Fp, "x")
f2 = x^2 + x + 1
f3 = x^3 - x^2 + 1
println("p mod 3 = ", p % 3, "  (x^2+x+1 splits in F_p iff p ≡ 1 mod 3)")
println("factor(x^2+x+1) mod p: ", factor(f2))
println("factor(x^3-x^2+1) mod p: ", factor(f3))
