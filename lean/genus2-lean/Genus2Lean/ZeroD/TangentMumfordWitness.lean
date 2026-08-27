import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.LCanonicalElementary

/-! # The `f+` witness for `ROADMAP-principal-witness-assembly.md`'s
`C + 2•[δ₀]` construction

Per that roadmap's latest status update: `f+ := y - b_+(x)`, where `b_+`
is the UNIQUE degree-≤3 polynomial satisfying FOUR linear conditions —
`b_+` agrees with `Ra1.Y`/`Ra2.Y` at `Ra1.X`/`Ra2.X` (two ordinary
evaluation conditions, exactly `mumfordB`'s own two-point interpolation
idiom, `LCanonicalElementary.lean`), PLUS a full TANGENCY pair of
conditions at `δ₀`: `b_+` agrees with `δ₀.Y` at `δ₀.X` (value) AND
`b_+`'s derivative at `δ₀.X` matches the curve's own implicit branch
derivative there (`AlphaReduce.lean`'s `branchDeriv4` formula,
`f'(δ₀.X)/(2·δ₀.Y)`, generalized here to a bare `k`-field/`H.f` version).

**Corrected condition count (this pass): 4, not 3** — an earlier draft of
this file mistakenly used only the derivative condition at `δ₀`,
dropping the value condition, giving a 3-condition/degree-≤2 `b_+`. That
was wrong (order-2 vanishing needs BOTH value and derivative to vanish,
matching `AlphaReduce.lean`'s own `P1=P2` tangent-row precedent, which
has TWO rows — evaluation AND derivative — for its single tangent
point). With 4 conditions, `b_+` has degree ≤3, and
`ordInf(y-b_+) = -max(2·3,5) = -6` — matching the companion `f-`'s
Cantor-addition pole order (`ROADMAP-principal-witness-assembly.md`'s
own hand-derivation), both landing at `-6` with a shared degree-2
residual divisor `R`.

This gives `y - b_+(x)` vanishing SIMPLY at `Ra1, Ra2` and to order
(at least) `2` at `δ₀` — exactly `C + 2•[δ₀]` — plus a residual degree-2
divisor `R` (`6 = 2+2+deg R ⟹ deg R = 2`), which is the `R` the
roadmap's construction needs, matched against `f-`'s own residual.

**Status: skeleton only, unit-existence/uniqueness of the 4×4 linear
solve and all divisor-level `ordAt` facts still to be proved (`sorry`
throughout) — this pass scopes the DEFINITION and the linear-algebra
setup, matching this project's "smaller named sorries, easiest first"
convention. Not yet build-tested (no live Lean toolchain in this
environment) — Claire's REPL to confirm.** -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-- **The branch derivative, generalized off `AlphaReduce.lean`'s
`F p`/`curvePoly`-specific `branchDeriv4`.** Same formula, `f'(px)/(2·py)`
— the implicit-function-theorem derivative of `y` along `y² = H.f(x)` at
a point with `py ≠ 0` (nondegeneracy required at the call site, not
baked into the definition itself, matching `branchDeriv4`'s own
convention). -/
noncomputable def branchDeriv (H : HyperellipticPolynomial k) (px py : k) : k :=
  (derivative H.f).eval px / (2 * py)

/-- **The 4×4 tangent-interpolation matrix for `b_+`.** Unknowns are
`b_+`'s four coefficients `(b0,b1,b2,b3)` (`b_+ = C b0 + C b1·X + C b2·X²
+ C b3·X³`). Row 0: evaluation at `Ra1.X` (`1, x, x², x³`). Row 1:
evaluation at `Ra2.X`, same shape. Row 2: evaluation at `δ₀.X`, same
shape (the value condition this file's earlier draft mistakenly
omitted). Row 3: the DERIVATIVE row at `δ₀.X`, `(0, 1, 2x, 3x²)` —
coefficients of `d/dx (b0+b1x+b2x²+b3x³) = b1+2b2x+3b3x²`, mirroring
`AlphaReduce.lean`'s `tangentRowEntryX4` pattern one degree higher. -/
def tangentInterpMatrix (Ra1X Ra2X delta0X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, Ra1X,   Ra1X ^ 2,   Ra1X ^ 3;
     1, Ra2X,   Ra2X ^ 2,   Ra2X ^ 3;
     1, delta0X, delta0X ^ 2, delta0X ^ 3;
     0, 1,      2 * delta0X, 3 * delta0X ^ 2]

/-- **The RHS vector for `b_+`'s 4×4 solve.** Rows 0–2: the target
`y`-values `Ra1.Y`, `Ra2.Y`, `δ₀.Y`. Row 3: the target derivative value,
`branchDeriv H δ₀.X δ₀.Y`. -/
def tangentInterpRHS (Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k) : Fin 4 → k :=
  ![Ra1Y, Ra2Y, delta0Y, branchDerivAtDelta0]

/-- **Nondegeneracy of the 4×4 tangent-interpolation system.** This
"confluent Vandermonde" matrix (three ordinary evaluation rows plus one
derivative row collapsed onto one of the three nodes) is invertible iff
`Ra1.X`, `Ra2.X`, `δ₀.X` are PAIRWISE DISTINCT — the standard Hermite/
confluent-Vandermonde nondegeneracy condition (a repeated NODE, not a
repeated ROW, is what would make it singular; the derivative row at an
already-distinct `δ₀.X` is exactly the non-degenerate confluent case).
**Not yet proved** — needs either a direct determinant computation
(expected closed form: `(Ra1X - Ra2X)·(Ra1X - delta0X)²·(Ra2X -
delta0X)²`, the confluent-Vandermonde determinant formula with `δ₀`'s
node doubled, UNCONFIRMED, to be checked by direct `Matrix.det_fin_four`
expansion or a Mathlib confluent-Vandermonde lemma if one exists — not
searched yet) or a Mathlib `Matrix.det_vandermonde`-adjacent lemma for
the confluent case (unlikely to exist off-the-shelf; more likely this
needs a direct expansion). This is the first genuinely new piece of
algebra this file needs, and the one most likely to need either a
ChatGPT consultation (if the closed form isn't found quickly) or a
direct `Matrix.det_fin_four`/`ring`-level computation. -/
theorem tangentInterpMatrix_det_ne_zero (Ra1X Ra2X delta0X : k)
    (h1 : Ra1X ≠ Ra2X) (h2 : Ra1X ≠ delta0X) (h3 : Ra2X ≠ delta0X) :
    (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0 := by
  sorry

/-- **`b_+`'s coefficients, via Cramer's rule.** `bPlusCoeff i` gives the
`i`-th coefficient of the unique degree-≤3 `b_+` solving the four
conditions above. Matches this project's existing `cramerSolution`/
`cramerSolution4` naming and `Matrix.cramer`-based construction pattern,
one size (4×4 instead of 6×6) down from the K=4 file's own machinery. -/
noncomputable def bPlusCoeff (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (i : Fin 4) : k :=
  (tangentInterpMatrix Ra1X Ra2X delta0X).det⁻¹ *
    (Matrix.cramer (tangentInterpMatrix Ra1X Ra2X delta0X)
      (tangentInterpRHS Ra1Y Ra2Y delta0Y branchDerivAtDelta0) i)

/-- **`b_+` itself, as a polynomial.** `∑_{i<4} C (bPlusCoeff i) * X^i` —
degree ≤ 3 by construction (four explicit coefficients, no higher-degree
terms possible). -/
noncomputable def bPlus (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k) :
    Polynomial k :=
  Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 0) +
  Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 1) * X +
  Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 2) * X ^ 2 +
  Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 3) * X ^ 3

/-- **`b_+`'s degree bound: `≤ 3`.** Immediate from its four-term shape —
same style as `mumfordB_natDegree_le`, two degrees up (`max 0 (max 1
(max 2 3)) = 3` via `natDegree_add_le` iterated three times). -/
theorem bPlus_natDegree_le (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).natDegree ≤ 3 := by
  sorry

/-- **`ordInfOfPair` of the `f+` numerator is exactly `-6`.** With `A :=
-bPlus ...` and `B := 1`: `ordInfOfPair A B = -(max (2·deg A) (2·deg B+5))`.
`deg B = deg (1:k[X]) = 0`, so the second term is `5`. `deg A ≤ 3` (via
`bPlus_natDegree_le` + `natDegree_neg`), so `2·deg A ≤ 6 > 5` this time —
**the max is now pinned at `6`, not `5`** (the key difference from
`mumfordB_ordInfOfPair`'s `-5` conclusion: there `2·deg ≤ 2 < 5`; here
`2·deg ≤ 6`, and generically `= 6` once `bPlus_natDegree_le` is sharpened
to an equality — degree exactly `3`, not just `≤3`, needed for this
theorem's `-6` to be exact rather than merely `≥ -6`; not yet checked
whether the 4×4 solve's leading coefficient `bPlusCoeff ... 3` is
generically nonzero, a genuinely separate fact from the det-nonzero
fact above). -/
theorem bPlus_ordInfOfPair (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k) :
    ordInfOfPair (-bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0) (1 : k[X]) = -6 := by
  sorry

/-- **`b_+` evaluates to `Ra1.Y` at `Ra1.X`.** Row 0 of the linear
system. -/
theorem bPlus_eval_Ra1 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).eval Ra1X = Ra1Y := by
  sorry

/-- **`b_+` evaluates to `Ra2.Y` at `Ra2.X`.** Row 1. -/
theorem bPlus_eval_Ra2 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).eval Ra2X = Ra2Y := by
  sorry

/-- **`b_+` evaluates to `δ₀.Y` at `δ₀.X`.** Row 2 — now genuinely
present, unlike the earlier flawed draft. -/
theorem bPlus_eval_delta0 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).eval delta0X = delta0Y := by
  sorry

/-- **`b_+`'s derivative at `δ₀.X` matches the branch derivative.**
Row 3 — the tangency condition proper. -/
theorem bPlus_deriv_eval_delta0 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (derivative (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0)).eval delta0X =
      branchDerivAtDelta0 := by
  sorry

end DecoupledSystem
end Genus2Lean
