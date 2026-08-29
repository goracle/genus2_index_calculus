import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.TangentMumfordWitness
import Genus2Lean.ZeroD.CAWitnessCrossTangent

/-! # `bCA`'s CROSS-pair tangent case, part 2: the confluent interpolation
matrix for `Ra1 = ι(sa.P1)`

Per `ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3, the
honest-tangency sub-case identified by `CAWitnessCrossTangent.lean`'s
`eq_iota_of_X_eq_of_ne` (the "same point" sub-case is excluded there by
the caller's existing `Ra1 ≠ sa.P1` convention, not handled here).

**Row layout, DIFFERENT from cases 1/2 — the doubled node is
NON-ADJACENT.** `caInterpMatrix`'s original rows are `[Ra1, Ra2, P1,
P2]` (rows 0,1,2,3). Here `Ra1.X = sa.P1.X =: x` collapses ROWS 0 AND
2 onto the same node (not 0-1 or 2-3 as in cases 1/2), leaving rows 1
(`Ra2X`) and 3 (`P2X`) ordinary. Verified independently via sympy
before writing this file (not assumed from the roadmap's own already-
sympy-checked claim): with row 0 = evaluation at `x`, row 1 =
evaluation at `Ra2X`, row 2 = DERIVATIVE at `x` (replacing `P1`'s old
evaluation row), row 3 = evaluation at `P2X`, the determinant is
`-(x-P2X)^2 * (P2X-Ra2X) * (x-Ra2X)^2` — matches the roadmap's
`-(x-P2X)²(P2X-Ra2X)(x-Ra2X)²` exactly. Nondegeneracy is three
pairwise-distinctness facts (`x ≠ Ra2X`, `x ≠ P2X`, `Ra2X ≠ P2X`), not
five — the same node-count reduction cases 1/2 already exhibited.

**RHS sign convention.** Row 0 (`Ra1`'s old slot) sits on the
UNFLIPPED (`C`) side of `caInterpRHS`, wanting `Ra1.Y`. Row 2 (`P1`'s
old slot) sits on the FLIPPED (`ι(A)`) side, so both its value contribution
and its derivative contribution carry a minus sign — but since `Ra1 =
ι(sa.P1)` means the SAME node now supplies both rows' data, row 2's
"value" is folded into row 0 (`Ra1.Y = -sa.P1.Y` is exactly the
`ι`-identification, not a separate row), and what remains at row 2 is
purely the DERIVATIVE contribution, flipped: `-vDerivAtP1` where
`vDerivAtP1 := (derivative v).eval sa.P1.X` (target Mumford pair's own
line, mirroring `CAWitnessTangentTarget.lean`'s `vDerivAtP`
convention). Stated as a caller-supplied hypothesis (`hP1Deriv`,
unflipped natural form `2 * P1Y * vDerivAtP1 = (derivative H.f).eval
P1X`, same convention as `hPDeriv`/`hRaDeriv` elsewhere), with the flip
applied only at the RHS-row level, matching both existing tangent
files' established pattern.

**Status: drafted this pass, not yet REPL-confirmed beyond the
determinant** (no live Lean toolchain in this environment for the rest
of the file) — the determinant closed form IS independently verified
(see above), unlike cases 1/2's own docstrings which flagged theirs as
unverified guesses. Everything past the determinant follows the same
`det⁻¹ * cramer` / row-identity idiom already proven twice in this
codebase (`CAWitnessTangent.lean`, `CAWitnessTangentTarget.lean`), so
risk here is mechanical (index bookkeeping), not new mathematics. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The 4×4 confluent interpolation matrix for `bCA`'s cross-pair
tangent case (`Ra1.X = sa.P1.X`).** Row 0: evaluation at the doubled
node `RaX` (`= sa.P1.X`). Row 1: evaluation at `Ra2X`. Row 2:
DERIVATIVE at the doubled node (replacing `P1`'s old row — the
confluent row). Row 3: evaluation at `P2X`. Determinant independently
sympy-verified in the module docstring above. -/
def caCrossInterpMatrix (RaX Ra2X P2X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, RaX,  RaX ^ 2,  RaX ^ 3;
     1, Ra2X, Ra2X ^ 2, Ra2X ^ 3;
     0, 1,    2 * RaX,  3 * RaX ^ 2;
     1, P2X,  P2X ^ 2,  P2X ^ 3]

/-- **The RHS for `bCA`'s cross-pair tangent-case 4×4 solve.** Row 0:
`RaY` (`= Ra1.Y`, unflipped anchor value — also equals `-sa.P1.Y` by
the `ι`-identification, but this row is stated in `Ra1`'s own
unflipped terms, matching row 0's role in `caInterpRHS`). Row 1:
`Ra2Y`, unflipped. Row 2: `-vDerivAtP1`, the FLIPPED target-side
derivative (see module docstring). Row 3: `-P2Y`, the ordinary
`ι`-flipped target value, same convention as `caInterpRHS`'s row 3. -/
def caCrossInterpRHS (RaY Ra2Y vDerivAtP1 P2Y : k) : Fin 4 → k :=
  ![RaY, Ra2Y, -vDerivAtP1, -P2Y]

/-- **Nondegeneracy: invertible iff `RaX, Ra2X, P2X` are pairwise
distinct.** Three hypotheses, not five or six — the doubled node
collapses `Ra1X ≠ P1X`'s slot entirely (it's now the SAME point), and
the two remaining ordinary nodes only need to differ from the doubled
node and from each other. -/
theorem caCrossInterpMatrix_det_ne_zero (RaX Ra2X P2X : k)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X) :
    (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0 := by
  have hdet : (caCrossInterpMatrix RaX Ra2X P2X).det =
      -(RaX - P2X) ^ 2 * (P2X - Ra2X) * (RaX - Ra2X) ^ 2 := by
    unfold caCrossInterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr
    (pow_ne_zero 2 (sub_ne_zero.mpr h2))) (sub_ne_zero.mpr (Ne.symm h3)))
    (pow_ne_zero 2 (sub_ne_zero.mpr h1))

/-- **`bCA`'s cross-tangent-case coefficients, via Cramer's rule.**
Same `det⁻¹ * cramer` idiom as `caCoeff`/`caTangentCoeff`. -/
noncomputable def caCrossCoeff (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (i : Fin 4) : k :=
  (caCrossInterpMatrix RaX Ra2X P2X).det⁻¹ *
    (Matrix.cramer (caCrossInterpMatrix RaX Ra2X P2X)
      (caCrossInterpRHS RaY Ra2Y vDerivAtP1 P2Y) i)

/-- **`bCA`'s cross-tangent-case witness polynomial.** `∑_{i<4} C
(caCrossCoeff i) * X^i`, degree ≤ 3, same four-term shape as the other
`bCA` variants. -/
noncomputable def bCACross (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k) :
    Polynomial k :=
  Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 0) +
  Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 1) * X +
  Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 2) * X ^ 2 +
  Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 3) * X ^ 3

theorem bCACross_natDegree_le (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k) :
    (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).natDegree ≤ 3 := by
  unfold bCACross
  compute_degree

/-- **Row identity, shared core.** Same `Matrix.mulVec_cramer` argument
as every other `bCA` variant in this project. -/
private theorem bCACross_row_eq (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, caCrossInterpMatrix RaX Ra2X P2X r j *
      caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y j =
      caCrossInterpRHS RaY Ra2Y vDerivAtP1 P2Y r := by
  have hexpand : ∑ j : Fin 4, caCrossInterpMatrix RaX Ra2X P2X r j *
      caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y j =
      (caCrossInterpMatrix RaX Ra2X P2X).det⁻¹ *
        (caCrossInterpMatrix RaX Ra2X P2X r ⬝ᵥ
          (Matrix.cramer (caCrossInterpMatrix RaX Ra2X P2X)
            (caCrossInterpRHS RaY Ra2Y vDerivAtP1 P2Y))) := by
    unfold caCrossCoeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (caCrossInterpMatrix RaX Ra2X P2X)
    (caCrossInterpRHS RaY Ra2Y vDerivAtP1 P2Y)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

private theorem bCACross_eval_eq_row (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y x : k) :
    (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y j := by
  unfold bCACross
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- **`bCACross` evaluates to `RaY` at `RaX`.** Row 0. -/
theorem bCACross_eval_Ra (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0) :
    (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval RaX = RaY := by
  rw [bCACross_eval_eq_row]
  have hrow := bCACross_row_eq RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet 0
  have hmat : caCrossInterpMatrix RaX Ra2X P2X 0 = ![(1 : k), RaX, RaX ^ 2, RaX ^ 3] := by
    unfold caCrossInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCrossInterpRHS] using hrow

/-- **`bCACross` evaluates to `Ra2Y` at `Ra2X`.** Row 1. -/
theorem bCACross_eval_Ra2 (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0) :
    (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval Ra2X = Ra2Y := by
  rw [bCACross_eval_eq_row]
  have hrow := bCACross_row_eq RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet 1
  have hmat : caCrossInterpMatrix RaX Ra2X P2X 1 = ![(1 : k), Ra2X, Ra2X ^ 2, Ra2X ^ 3] := by
    unfold caCrossInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCrossInterpRHS] using hrow

/-- **`bCACross`'s derivative at `RaX` equals `-vDerivAtP1`.** Row 2 —
the confluent/tangency condition, `ι`-flipped since this row descends
from `P1`'s old (flipped) slot. -/
theorem bCACross_deriv_eval_Ra (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0) :
    (derivative (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y)).eval RaX =
      -vDerivAtP1 := by
  have hrow := bCACross_row_eq RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet 2
  have hmat : caCrossInterpMatrix RaX Ra2X P2X 2 = ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] := by
    unfold caCrossInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simp only [caCrossInterpRHS] at hrow
  have hderiv : (derivative (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y)).eval RaX =
      ∑ j : Fin 4, ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] j *
        caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y j := by
    unfold bCACross
    rw [Fin.sum_univ_four]
    rw [show (X : k[X]) = X ^ 1 from (pow_one X).symm]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.cons_val_three, derivative_add, derivative_C_mul_X_pow,
      derivative_C, zero_add, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    push_cast
    simp [derivative_C_mul_X_pow]
    ring
  rw [hderiv]
  simpa using hrow

/-- **`bCACross` at `P2.X` equals `-P2.Y`.** Row 3 — the ordinary `ι`
substitution, same convention as `bCA_eval_P2`. -/
theorem bCACross_eval_P2 (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0) :
    (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P2X = -P2Y := by
  rw [bCACross_eval_eq_row]
  have hrow := bCACross_row_eq RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet 3
  have hmat : caCrossInterpMatrix RaX Ra2X P2X 3 = ![(1 : k), P2X, P2X ^ 2, P2X ^ 3] := by
    unfold caCrossInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCrossInterpRHS] using hrow

end DecoupledSystem
end Genus2Lean
