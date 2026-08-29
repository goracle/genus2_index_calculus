import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.TangentMumfordWitness
import Genus2Lean.ZeroD.CAWitnessCrossTangent

/-! # `bCA`'s CROSS-pair tangent case, variant 2: `Ra1 = ι(sa.P2)`

Second of the three remaining symmetric cross-pair variants (per
`ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3's closing
note: "the other 3 cross-pair variants by symmetry ... each needs the
same treatment, matrix shape differs only in which row pair is
doubled"). Confirmed via independent sympy check before writing any
Lean, same discipline as `CAWitnessCrossTangent2.lean`: this is
genuinely a different matrix from that file's (`Ra1 = ι(sa.P1)`), not
a copy — the doubled row pair here is positions 0 and 3 (`Ra1`'s and
`P2`'s original slots), not 0 and 2.

**Row layout.** `caInterpMatrix`'s original rows `[Ra1, Ra2, P1, P2]`
(0,1,2,3). Here `Ra1.X = sa.P2.X =: x` collapses rows 0 and 3. Row 0:
evaluation at `x`. Row 1: evaluation at `Ra2X` (ordinary, survives).
Row 2: evaluation at `P1X` (ordinary, survives). Row 3: DERIVATIVE at
`x` (replacing `P2`'s old row). Sympy-verified determinant:
`-(x-Ra2X)^2 * (Ra2X-P1X) * (x-P1X)^2`.

**RHS signs.** Row 0 unflipped (`Ra1`'s slot, `C`-side). Row 1
unflipped (`Ra2`, `C`-side). Row 2 FLIPPED (`P1`, `ι(A)`-side,
`-P1Y`). Row 3 FLIPPED (derivative, since it descends from `P2`'s old
`ι(A)`-side slot: `-vDerivAtP2`).

Combines what took `CAWitnessCrossTangent2.lean`/`CAWitnessCrossTangent3.lean`
two files to build into one file here, since the shape is now
established and three more separate checkpoint files per variant
would be pure duplication — matrix/coeffs/bCA/rows/dvd/uCANew
together. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The 4×4 confluent interpolation matrix, variant 2.** Row 0:
evaluation at doubled node `RaX` (`= sa.P2.X`). Row 1: evaluation at
`Ra2X`. Row 2: evaluation at `P1X`. Row 3: DERIVATIVE at `RaX`. -/
def caCross2InterpMatrix (RaX Ra2X P1X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, RaX,  RaX ^ 2,  RaX ^ 3;
     1, Ra2X, Ra2X ^ 2, Ra2X ^ 3;
     1, P1X,  P1X ^ 2,  P1X ^ 3;
     0, 1,    2 * RaX,  3 * RaX ^ 2]

/-- **RHS, variant 2.** Row 0: `RaY` (`= Ra1.Y`, unflipped). Row 1:
`Ra2Y`, unflipped. Row 2: `-P1Y`, ordinary `ι`-flip. Row 3:
`-vDerivAtP2`, the flipped target-side derivative. -/
def caCross2InterpRHS (RaY Ra2Y P1Y vDerivAtP2 : k) : Fin 4 → k :=
  ![RaY, Ra2Y, -P1Y, -vDerivAtP2]

/-- **Nondegeneracy: invertible iff `RaX, Ra2X, P1X` pairwise
distinct.** Sympy-verified closed form. -/
theorem caCross2InterpMatrix_det_ne_zero (RaX Ra2X P1X : k)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X) :
    (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0 := by
  have hdet : (caCross2InterpMatrix RaX Ra2X P1X).det =
      -(RaX - Ra2X) ^ 2 * (Ra2X - P1X) * (RaX - P1X) ^ 2 := by
    unfold caCross2InterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr
    (pow_ne_zero 2 (sub_ne_zero.mpr h1))) (sub_ne_zero.mpr h3))
    (pow_ne_zero 2 (sub_ne_zero.mpr h2))

noncomputable def caCross2Coeff (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (i : Fin 4) : k :=
  (caCross2InterpMatrix RaX Ra2X P1X).det⁻¹ *
    (Matrix.cramer (caCross2InterpMatrix RaX Ra2X P1X)
      (caCross2InterpRHS RaY Ra2Y P1Y vDerivAtP2) i)

noncomputable def bCACross2 (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k) :
    Polynomial k :=
  Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 0) +
  Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 1) * X +
  Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 2) * X ^ 2 +
  Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 3) * X ^ 3

theorem bCACross2_natDegree_le (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k) :
    (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).natDegree ≤ 3 := by
  unfold bCACross2
  compute_degree

private theorem bCACross2_row_eq (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, caCross2InterpMatrix RaX Ra2X P1X r j *
      caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 j =
      caCross2InterpRHS RaY Ra2Y P1Y vDerivAtP2 r := by
  have hexpand : ∑ j : Fin 4, caCross2InterpMatrix RaX Ra2X P1X r j *
      caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 j =
      (caCross2InterpMatrix RaX Ra2X P1X).det⁻¹ *
        (caCross2InterpMatrix RaX Ra2X P1X r ⬝ᵥ
          (Matrix.cramer (caCross2InterpMatrix RaX Ra2X P1X)
            (caCross2InterpRHS RaY Ra2Y P1Y vDerivAtP2))) := by
    unfold caCross2Coeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (caCross2InterpMatrix RaX Ra2X P1X)
    (caCross2InterpRHS RaY Ra2Y P1Y vDerivAtP2)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

private theorem bCACross2_eval_eq_row (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 x : k) :
    (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 j := by
  unfold bCACross2
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem bCACross2_eval_Ra (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0) :
    (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval RaX = RaY := by
  rw [bCACross2_eval_eq_row]
  have hrow := bCACross2_row_eq RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet 0
  have hmat : caCross2InterpMatrix RaX Ra2X P1X 0 = ![(1 : k), RaX, RaX ^ 2, RaX ^ 3] := by
    unfold caCross2InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross2InterpRHS] using hrow

theorem bCACross2_eval_Ra2 (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0) :
    (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval Ra2X = Ra2Y := by
  rw [bCACross2_eval_eq_row]
  have hrow := bCACross2_row_eq RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet 1
  have hmat : caCross2InterpMatrix RaX Ra2X P1X 1 = ![(1 : k), Ra2X, Ra2X ^ 2, Ra2X ^ 3] := by
    unfold caCross2InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross2InterpRHS] using hrow

theorem bCACross2_eval_P1 (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0) :
    (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P1X = -P1Y := by
  rw [bCACross2_eval_eq_row]
  have hrow := bCACross2_row_eq RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet 2
  have hmat : caCross2InterpMatrix RaX Ra2X P1X 2 = ![(1 : k), P1X, P1X ^ 2, P1X ^ 3] := by
    unfold caCross2InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross2InterpRHS] using hrow

/-- **Row 3, the confluent/tangency row: derivative at `RaX` equals
`-vDerivAtP2`.** -/
theorem bCACross2_deriv_eval_Ra (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0) :
    (derivative (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2)).eval RaX =
      -vDerivAtP2 := by
  have hrow := bCACross2_row_eq RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet 3
  have hmat : caCross2InterpMatrix RaX Ra2X P1X 3 = ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] := by
    unfold caCross2InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simp only [caCross2InterpRHS] at hrow
  have hderiv : (derivative (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2)).eval RaX =
      ∑ j : Fin 4, ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] j *
        caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 j := by
    unfold bCACross2
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

theorem pairNormBCACross2_eval_Ra2_eq_zero (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) :
    (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2).eval Ra2X = 0 := by
  rw [eval_sub, eval_pow, bCACross2_eval_Ra2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet,
    hRa2_curve, sub_self]

theorem pairNormBCACross2_eval_P1_eq_zero (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2).eval P1X = 0 := by
  rw [eval_sub, eval_pow, bCACross2_eval_P1 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet,
    neg_sq, hP1_curve, sub_self]

theorem dvd_pairNormBCACross2_Ra2 (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) :
    (X - C Ra2X) ∣ (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross2_eval_Ra2_eq_zero H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet hRa2_curve

theorem dvd_pairNormBCACross2_P1 (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (X - C P1X) ∣ (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross2_eval_P1_eq_zero H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet hP1_curve

/-- **`(X-RaX)² ∣ H.f - bCACross2²`.** Same sign-convention caveat as
`CAWitnessCrossTangent3.lean`'s `dvd_sq_pairNormBCACross_Ra`: `hP2Deriv`
is stated ALREADY flipped (`2*RaY*(-vDerivAtP2) = f'.eval RaX`) to
match what `bCACross2_deriv_eval_Ra` actually proves, not in the
"natural unflipped" form `hRaDeriv`/`hPDeriv` use — checked
algebraically against that lemma's conclusion before writing this
hypothesis shape, not copied from the other files by pattern-matching. -/
theorem dvd_sq_pairNormBCACross2_Ra (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 ∣ (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) := by
  have h0 : (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2).eval RaX = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow,
      bCACross2_eval_Ra RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet, hRa_curve]
    ring
  have h1 : (derivative
      (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2)).eval RaX = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sq, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      bCACross2_eval_Ra RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet,
      bCACross2_deriv_eval_Ra RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet,
      ← hP2Deriv]
    ring
  exact sq_dvd_of_eval_derivative_eq_zero' hne h0 h1

theorem dvd_pairNormBCACross2_full (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 * (X - C Ra2X) * (X - C P1X) ∣
      (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) := by
  have hd1 := dvd_sq_pairNormBCACross2_Ra H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet
    hRa_curve hP2Deriv hne
  have hd2 := dvd_pairNormBCACross2_Ra2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet hRa2_curve
  have hd3 := dvd_pairNormBCACross2_P1 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet hP1_curve
  have hc1Ra2 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C Ra2X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1)).pow_left
  have hc1P1 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C P1X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2)).pow_left
  have hcRa2P1 : IsCoprime (X - C Ra2X : k[X]) (X - C P1X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h3)
  have hd12 : (X - C RaX) ^ 2 * (X - C Ra2X) ∣
      (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) :=
    hc1Ra2.mul_dvd hd1 hd2
  have hc12P1 : IsCoprime ((X - C RaX : k[X]) ^ 2 * (X - C Ra2X)) (X - C P1X) :=
    hc1P1.mul_left hcRa2P1
  exact hc12P1.mul_dvd hd12 hd3

/-! ## `uCANewCross2` -/

noncomputable def denomPolyCACross2 (RaX Ra2X P1X : k) : Polynomial k :=
  (X - C RaX) ^ 2 * (X - C Ra2X) * (X - C P1X)

theorem denomPolyCACross2_monic (RaX Ra2X P1X : k) :
    (denomPolyCACross2 RaX Ra2X P1X).Monic := by
  unfold denomPolyCACross2
  exact (((Polynomial.monic_X_sub_C RaX).pow 2).mul (Polynomial.monic_X_sub_C Ra2X)).mul
    (Polynomial.monic_X_sub_C P1X)

theorem denomPolyCACross2_natDegree (RaX Ra2X P1X : k) :
    (denomPolyCACross2 RaX Ra2X P1X).natDegree = 4 := by
  unfold denomPolyCACross2
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX))
        (Polynomial.X_sub_C_ne_zero Ra2X))
      (Polynomial.X_sub_C_ne_zero P1X),
    Polynomial.natDegree_mul (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX))
      (Polynomial.X_sub_C_ne_zero Ra2X),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

noncomputable def uCANewCross2 (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k) : Polynomial k :=
  (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) /ₘ
    denomPolyCACross2 RaX Ra2X P1X

theorem pairNormBCACross2_eq_denomPolyCACross2_mul_uCANewCross2
    (H : HyperellipticPolynomial k)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0) :
    H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 =
      denomPolyCACross2 RaX Ra2X P1X *
        uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 := by
  have hdvd := dvd_pairNormBCACross2_full H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet
    h1 h2 h3 hRa_curve hRa2_curve hP1_curve hP2Deriv hne
  have hmod : (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) %ₘ
      denomPolyCACross2 RaX Ra2X P1X = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyCACross2_monic RaX Ra2X P1X)).mpr
      (by
        change (X - C RaX) ^ 2 * (X - C Ra2X) * (X - C P1X) ∣
          (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2)
    (q := denomPolyCACross2 RaX Ra2X P1X)
  rw [hmod, zero_add] at hadd
  unfold uCANewCross2
  exact hadd.symm

end DecoupledSystem
end Genus2Lean
