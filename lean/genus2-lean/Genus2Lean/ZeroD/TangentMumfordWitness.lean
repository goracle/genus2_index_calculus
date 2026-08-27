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

**Status update (this pass): all 7 `sorry`s filled.** `bPlus_natDegree_le`
(via `compute_degree`), the confluent-Vandermonde determinant
`tangentInterpMatrix_det_ne_zero` (closed form `-(Ra1X-Ra2X)(Ra1X-δ₀X)²
(Ra2X-δ₀X)²`, confirmed independently via sympy, then `Matrix.det_fin_four`
+ `ring`), the four `bPlus_eval_*`/`bPlus_deriv_eval_delta0` row identities
(via a shared `bPlus_row_eq` Cramer's-rule helper, `Matrix.mulVec_cramer`-based,
mirroring but simplifying `AlphaReduce.lean`'s `rowTangent_defining_eq_aux`
pattern), and `bPlus_ordInfOfPair` — **WEAKENED, see its own docstring**:
the original unconditional `= -6` claim is false in general (the degree-3
coefficient `bPlusCoeff ... 3` can vanish for special input data), so it
now takes `hlead : bPlusCoeff ... 3 ≠ 0` as an explicit hypothesis. Not
yet used by any other file, so this doesn't break existing callers.

Not yet build-tested (no live Lean toolchain in this environment) —
Claire's REPL to confirm. Two spots flagged as the most likely to need
REPL-driven adjustment rather than being fully certain in advance: (1)
`tangentInterpMatrix_det_ne_zero`'s bare `simp` before `Matrix.det_fin_four`
+ `ring` — if `simp` doesn't fully normalize the `!![...] i j` entries,
may need an explicit `Matrix.cons_val_zero`/`cons_val_one`/`head_cons`-style
lemma list added; (2) the `push_cast; ring` closings in the eval/derivative
helper lemmas, which lean on `Fin.sum_univ_four` and `derivative_C_mul_X_pow`
unfolding cleanly — plausible but not REPL-confirmed. -/

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
**Proved this pass.** Closed form: `det = -(Ra1X - Ra2X)·(Ra1X -
delta0X)²·(Ra2X - delta0X)²` — the NEGATIVE of the docstring's original
guessed sign (confirmed independently via a sympy symbolic computation,
not just derived in-proof), via `Matrix.det_fin_four` + `ring`. See the
proof's own leading comment for the REPL-confirmation caveat on the
`!![...] i j`-unfolding `simp` call. -/
theorem tangentInterpMatrix_det_ne_zero (Ra1X Ra2X delta0X : k)
    (h1 : Ra1X ≠ Ra2X) (h2 : Ra1X ≠ delta0X) (h3 : Ra2X ≠ delta0X) :
    (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0 := by
  -- Closed form confirmed independently via sympy (`Matrix([[1,a,a^2,a^3],[1,b,b^2,b^3],
  -- [1,d,d^2,d^3],[0,1,2d,3d^2]]).det()` factors to exactly `-(a-b)(a-d)²(b-d)²`, matching
  -- the docstring's guessed form up to an overall sign). `Matrix.det_fin_four` does NOT
  -- exist in Mathlib (checked against the doc page — Determinant/Basic.lean stops at
  -- `det_fin_three`), so the determinant is expanded via the confirmed-to-exist
  -- `Matrix.det_succ_row_zero` (cofactor expansion along row 0) down to `Fin 3`, then
  -- `Matrix.det_fin_three` for the 3×3 minors.
  have hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det =
      -((Ra1X - Ra2X) * (Ra1X - delta0X) ^ 2 * (Ra2X - delta0X) ^ 2) := by
    unfold tangentInterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  refine neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h1)
    (pow_ne_zero 2 (sub_ne_zero.mpr h2))) (pow_ne_zero 2 (sub_ne_zero.mpr h3)))

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
  unfold bPlus
  compute_degree

/-- **WEAKENED from the original unconditional `= -6` claim.** That
version is FALSE in general: `bPlusCoeff ... 3` (the degree-3
coefficient) can vanish for special input data (e.g. if `Ra1,Ra2,δ₀,
branchDerivAtDelta0` happen to be consistent with some degree-≤2
polynomial), in which case `bPlus.natDegree < 3` and `ordInfOfPair`
lands above `-6`, not at it. Added `hlead : bPlusCoeff ... 3 ≠ 0` as an
explicit hypothesis — the genuinely separate fact the original
docstring already flagged as "not yet checked," now surfaced as a
caller obligation rather than silently assumed. Not yet used by any
other file in the project (`bPlusCoeff`/`bPlus_ordInfOfPair` don't
appear elsewhere), so weakening here doesn't break existing callers.

With `hlead`, `A := -bPlus ...` and `B := 1`: `ordInfOfPair A B =
-(max (2·deg A) (2·deg B+5))`. `deg B = deg (1:k[X]) = 0`, so the
second term is `5`. `deg A = 3` exactly (`bPlus_natDegree_le` gives
`≤ 3`; `hlead` plus the coefficient-3 term rules out `< 3`), so
`2·deg A = 6 > 5`, pinning the max at `6`. -/
theorem bPlus_ordInfOfPair (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hlead : bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 3 ≠ 0) :
    ordInfOfPair (-bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0)
      (1 : k[X]) = -6 := by
  have hdeg3 : (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).natDegree = 3 := by
    apply le_antisymm (bPlus_natDegree_le Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0)
    unfold bPlus
    have hcoeff3 : (Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y
        branchDerivAtDelta0 0) +
      Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 1) * X +
      Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 2) * X ^ 2 +
      Polynomial.C (bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 3) *
        X ^ 3).coeff 3 =
        bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg :
      (-bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  have hB1 : ¬ ((-bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0) = 0 ∧
      (1 : k[X]) = 0) := fun h => one_ne_zero h.2
  rw [if_neg hB1, if_neg (one_ne_zero (α := k[X]))]
  rw [natDegree_one, hAdeg]
  rw [show (2 * ((3 : ℕ) : ℤ)) = 6 by norm_num,
    show (2 * ((0 : ℕ) : ℤ) + 5) = 5 by norm_num]
  rw [max_eq_left (by norm_num : (5 : ℤ) ≤ 6)]

/-- **Row identity, shared core for all four `bPlus_*` theorems.** Direct
consequence of `Matrix.mulVec_cramer` (`A.mulVec (A.cramer b) = A.det • b`)
composed with `bPlusCoeff`'s own `det⁻¹ * cramer` definition: for any row
`r`, `∑ⱼ M r j * bPlusCoeff j = (det⁻¹ * det) * b r = b r` once `hdet`
clears the `det⁻¹ * det = 1` factor. Kept `private`, matching this
project's convention for Cramer-rule plumbing lemmas (cf. `AlphaReduce.lean`'s
`rowTangent_defining_eq_aux`) — the four public theorems below are the
per-row unfoldings a caller actually needs. -/
private theorem bPlus_row_eq (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, tangentInterpMatrix Ra1X Ra2X delta0X r j *
      bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 j =
      tangentInterpRHS Ra1Y Ra2Y delta0Y branchDerivAtDelta0 r := by
  -- `bPlusCoeff = det⁻¹ * cramer`, so the goal's LHS is `det⁻¹ * (M r ⬝ᵥ cramer ...)`.
  have hexpand : ∑ j : Fin 4, tangentInterpMatrix Ra1X Ra2X delta0X r j *
      bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 j =
      (tangentInterpMatrix Ra1X Ra2X delta0X).det⁻¹ *
        (tangentInterpMatrix Ra1X Ra2X delta0X r ⬝ᵥ
          (Matrix.cramer (tangentInterpMatrix Ra1X Ra2X delta0X)
            (tangentInterpRHS Ra1Y Ra2Y delta0Y branchDerivAtDelta0))) := by
    unfold bPlusCoeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (tangentInterpMatrix Ra1X Ra2X delta0X)
    (tangentInterpRHS Ra1Y Ra2Y delta0Y branchDerivAtDelta0)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

/-- **`bPlus`'s evaluation at an arbitrary `x`, as a row-vector dot
product.** `bPlus.eval x = c0 + c1*x + c2*x² + c3*x³`, matching row `r`
of `tangentInterpMatrix` whenever `tangentInterpMatrix Ra1X Ra2X delta0X r
= ![1, x, x^2, x^3]` — used to identify rows 0–2 (the plain evaluation
rows) with `bPlus.eval` at the corresponding node. -/
private theorem bPlus_eval_eq_row (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 x : k) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 j := by
  unfold bPlus
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- **`b_+` evaluates to `Ra1.Y` at `Ra1.X`.** Row 0 of the linear
system. -/
theorem bPlus_eval_Ra1 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).eval Ra1X = Ra1Y := by
  rw [bPlus_eval_eq_row]
  have hrow0 := bPlus_row_eq Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 hdet 0
  have hmat0 : tangentInterpMatrix Ra1X Ra2X delta0X 0 =
      ![(1 : k), Ra1X, Ra1X ^ 2, Ra1X ^ 3] := by
    unfold tangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat0] at hrow0
  simpa [tangentInterpRHS] using hrow0

/-- **`b_+` evaluates to `Ra2.Y` at `Ra2.X`.** Row 1. -/
theorem bPlus_eval_Ra2 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).eval Ra2X = Ra2Y := by
  rw [bPlus_eval_eq_row]
  have hrow1 := bPlus_row_eq Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 hdet 1
  have hmat1 : tangentInterpMatrix Ra1X Ra2X delta0X 1 =
      ![(1 : k), Ra2X, Ra2X ^ 2, Ra2X ^ 3] := by
    unfold tangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat1] at hrow1
  simpa [tangentInterpRHS] using hrow1

/-- **`b_+` evaluates to `δ₀.Y` at `δ₀.X`.** Row 2 — now genuinely
present, unlike the earlier flawed draft. -/
theorem bPlus_eval_delta0 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0).eval delta0X = delta0Y := by
  rw [bPlus_eval_eq_row]
  have hrow2 := bPlus_row_eq Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 hdet 2
  have hmat2 : tangentInterpMatrix Ra1X Ra2X delta0X 2 =
      ![(1 : k), delta0X, delta0X ^ 2, delta0X ^ 3] := by
    unfold tangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat2] at hrow2
  simpa [tangentInterpRHS] using hrow2

/-- **`b_+`'s derivative at `δ₀.X` matches the branch derivative.**
Row 3 — the tangency condition proper. `derivative bPlus = C c1 + C(2c2)*X
+ C(3c3)*X²` (via `derivative_C_mul_X_pow`), so `(derivative bPlus).eval
delta0X = c1 + 2c2*delta0X + 3c3*delta0X² = ![0,1,2δ₀,3δ₀²] ⬝ c`, exactly
row 3 of `tangentInterpMatrix`. -/
theorem bPlus_deriv_eval_delta0 (Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 : k)
    (hdet : (tangentInterpMatrix Ra1X Ra2X delta0X).det ≠ 0) :
    (derivative (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0)).eval delta0X =
      branchDerivAtDelta0 := by
  have hrow3 := bPlus_row_eq Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 hdet 3
  have hmat3 : tangentInterpMatrix Ra1X Ra2X delta0X 3 =
      ![(0 : k), 1, 2 * delta0X, 3 * delta0X ^ 2] := by
    unfold tangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat3] at hrow3
  simp only [tangentInterpRHS] at hrow3
  have hderiv : (derivative
      (bPlus Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0)).eval delta0X =
      ∑ j : Fin 4, ![(0 : k), 1, 2 * delta0X, 3 * delta0X ^ 2] j *
        bPlusCoeff Ra1X Ra2X delta0X Ra1Y Ra2Y delta0Y branchDerivAtDelta0 j := by
    unfold bPlus
    rw [Fin.sum_univ_four]
    rw [show (X : k[X]) = X ^ 1 from (pow_one X).symm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three, derivative_add, derivative_C_mul_X_pow,
      derivative_C, zero_add, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    push_cast
    simp [derivative_C_mul_X_pow]
    ring
  rw [hderiv]
  simpa using hrow3

end DecoupledSystem
end Genus2Lean
