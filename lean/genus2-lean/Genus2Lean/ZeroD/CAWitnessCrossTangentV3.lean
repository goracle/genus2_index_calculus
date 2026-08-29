import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.TangentMumfordWitness
import Genus2Lean.ZeroD.CAWitnessCrossTangent

/-! # `bCA`'s CROSS-pair tangent case, variant 3: `Ra2 = ι(sa.P1)`

Third of the three remaining symmetric cross-pair variants (per
`ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3's closing
note: "the other 3 cross-pair variants by symmetry ... each needs the
same treatment, matrix shape differs only in which row pair is
doubled"). Confirmed via independent sympy check before writing any
Lean, same discipline as `CAWitnessCrossTangent2.lean`/
`CAWitnessCrossTangentV2.lean`.

**Row layout.** `caInterpMatrix`'s original rows `[Ra1, Ra2, P1, P2]`
(0,1,2,3). Here `Ra2.X = sa.P1.X =: x` collapses rows 1 and 2 — the
SAME adjacent-pair shape as `CAWitnessCrossTangent2.lean`'s
`Ra1 = ι(sa.P1)` (rows 0/2, non-adjacent) is NOT the analogy here;
this is closer in row-position shape to cases 1/2's adjacent doubling,
just shifted down by one row. Row 0: evaluation at `Ra1X` (ordinary,
survives). Row 1: evaluation at `x` (representing `Ra2`, encountered
first). Row 2: DERIVATIVE at `x` (replacing `P1`'s old row — the
confluent row). Row 3: evaluation at `P2X` (ordinary, survives).

**Sympy-verified determinant**:
`det = (x - P2X)^2 * (P2X - Ra1X) * (x - Ra1X)^2`
— note NO leading minus sign, unlike variants 1/2
(`CAWitnessCrossTangent2.lean`'s `-(x-P2X)^2*(P2X-Ra2X)*(x-Ra2X)^2`,
`CAWitnessCrossTangentV2.lean`'s `-(RaX-Ra2X)^2*(Ra2X-P1X)*(RaX-P1X)^2`).
Checked directly, not assumed by pattern-matching the other two files'
sign — cofactor expansion along row 2 (the all-but-one-zero row here,
`[0,1,2x,3x²]`) picks up a different sign than expansion along row 0
or row 3, since row 2 sits in an even vs. odd position relative to the
other two variants' confluent row. Verify independently again if this
file is ever refactored to expand along a different row.

**RHS signs.** Row 0 (`Ra1`, `C`-side) unflipped: `Ra1Y`. Row 1
(`Ra2`'s slot, `C`-side) unflipped: `Ra2Y` (`= x`'s value, since
`Ra2 = ι(sa.P1)` supplies the `C`-side data at this node — `Ra2` is an
anchor point, always unflipped, regardless of which target point it
coincides with). Row 2 (derivative, descending from `P1`'s old
`ι(A)`-side slot) FLIPPED: `-vDerivAtP1`. Row 3 (`P2`, `ι(A)`-side)
FLIPPED: `-P2Y`.

Combines matrix/coeffs/bCA/rows/dvd/uCANew into one file, following
`CAWitnessCrossTangentV2.lean`'s precedent (established once the shape
was clear enough that separate checkpoint files per variant would be
pure duplication). -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The 4×4 confluent interpolation matrix, variant 3.** Row 0:
evaluation at `Ra1X`. Row 1: evaluation at doubled node `RaX`
(`= Ra2X = sa.P1.X`). Row 2: DERIVATIVE at `RaX`. Row 3: evaluation at
`P2X`. -/
def caCross3InterpMatrix (Ra1X RaX P2X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, Ra1X, Ra1X ^ 2, Ra1X ^ 3;
     1, RaX,  RaX ^ 2,  RaX ^ 3;
     0, 1,    2 * RaX,  3 * RaX ^ 2;
     1, P2X,  P2X ^ 2,  P2X ^ 3]

/-- **RHS, variant 3.** Row 0: `Ra1Y`, unflipped. Row 1: `RaY`
(`= Ra2.Y`), unflipped. Row 2: `-vDerivAtP1`, the flipped target-side
derivative. Row 3: `-P2Y`, ordinary `ι`-flip. -/
def caCross3InterpRHS (Ra1Y RaY vDerivAtP1 P2Y : k) : Fin 4 → k :=
  ![Ra1Y, RaY, -vDerivAtP1, -P2Y]

/-- **Nondegeneracy: invertible iff `Ra1X, RaX, P2X` pairwise
distinct.** Sympy-verified closed form; NO leading minus sign, unlike
variants 1/2 — see module docstring. -/
theorem caCross3InterpMatrix_det_ne_zero (Ra1X RaX P2X : k)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X) :
    (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0 := by
  have hdet : (caCross3InterpMatrix Ra1X RaX P2X).det =
      (RaX - P2X) ^ 2 * (P2X - Ra1X) * (RaX - Ra1X) ^ 2 := by
    unfold caCross3InterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  refine mul_ne_zero (mul_ne_zero
    (pow_ne_zero 2 (sub_ne_zero.mpr h3)) (sub_ne_zero.mpr (Ne.symm h2)))
    (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h1)))

noncomputable def caCross3Coeff (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (i : Fin 4) : k :=
  (caCross3InterpMatrix Ra1X RaX P2X).det⁻¹ *
    (Matrix.cramer (caCross3InterpMatrix Ra1X RaX P2X)
      (caCross3InterpRHS Ra1Y RaY vDerivAtP1 P2Y) i)

noncomputable def bCACross3 (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k) :
    Polynomial k :=
  Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 0) +
  Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 1) * X +
  Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 2) * X ^ 2 +
  Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 3) * X ^ 3

theorem bCACross3_natDegree_le (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k) :
    (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).natDegree ≤ 3 := by
  unfold bCACross3
  compute_degree

private theorem bCACross3_row_eq (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, caCross3InterpMatrix Ra1X RaX P2X r j *
      caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y j =
      caCross3InterpRHS Ra1Y RaY vDerivAtP1 P2Y r := by
  have hexpand : ∑ j : Fin 4, caCross3InterpMatrix Ra1X RaX P2X r j *
      caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y j =
      (caCross3InterpMatrix Ra1X RaX P2X).det⁻¹ *
        (caCross3InterpMatrix Ra1X RaX P2X r ⬝ᵥ
          (Matrix.cramer (caCross3InterpMatrix Ra1X RaX P2X)
            (caCross3InterpRHS Ra1Y RaY vDerivAtP1 P2Y))) := by
    unfold caCross3Coeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (caCross3InterpMatrix Ra1X RaX P2X)
    (caCross3InterpRHS Ra1Y RaY vDerivAtP1 P2Y)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

private theorem bCACross3_eval_eq_row (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y x : k) :
    (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y j := by
  unfold bCACross3
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem bCACross3_eval_Ra1 (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0) :
    (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval Ra1X = Ra1Y := by
  rw [bCACross3_eval_eq_row]
  have hrow := bCACross3_row_eq Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet 0
  have hmat : caCross3InterpMatrix Ra1X RaX P2X 0 = ![(1 : k), Ra1X, Ra1X ^ 2, Ra1X ^ 3] := by
    unfold caCross3InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross3InterpRHS] using hrow

theorem bCACross3_eval_Ra (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0) :
    (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval RaX = RaY := by
  rw [bCACross3_eval_eq_row]
  have hrow := bCACross3_row_eq Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet 1
  have hmat : caCross3InterpMatrix Ra1X RaX P2X 1 = ![(1 : k), RaX, RaX ^ 2, RaX ^ 3] := by
    unfold caCross3InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross3InterpRHS] using hrow

theorem bCACross3_eval_P2 (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0) :
    (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P2X = -P2Y := by
  rw [bCACross3_eval_eq_row]
  have hrow := bCACross3_row_eq Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet 3
  have hmat : caCross3InterpMatrix Ra1X RaX P2X 3 = ![(1 : k), P2X, P2X ^ 2, P2X ^ 3] := by
    unfold caCross3InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross3InterpRHS] using hrow

/-- **Row 2, the confluent/tangency row: derivative at `RaX` equals
`-vDerivAtP1`.** -/
theorem bCACross3_deriv_eval_Ra (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0) :
    (derivative (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y)).eval RaX =
      -vDerivAtP1 := by
  have hrow := bCACross3_row_eq Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet 2
  have hmat : caCross3InterpMatrix Ra1X RaX P2X 2 = ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] := by
    unfold caCross3InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simp only [caCross3InterpRHS] at hrow
  have hderiv : (derivative (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y)).eval RaX =
      ∑ j : Fin 4, ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] j *
        caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y j := by
    unfold bCACross3
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

theorem pairNormBCACross3_eval_Ra1_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) :
    (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2).eval Ra1X = 0 := by
  rw [eval_sub, eval_pow, bCACross3_eval_Ra1 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet,
    hRa1_curve, sub_self]

theorem pairNormBCACross3_eval_P2_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2).eval P2X = 0 := by
  rw [eval_sub, eval_pow, bCACross3_eval_P2 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet,
    neg_sq, hP2_curve, sub_self]

theorem dvd_pairNormBCACross3_Ra1 (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) :
    (X - C Ra1X) ∣ (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross3_eval_Ra1_eq_zero H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet hRa1_curve

theorem dvd_pairNormBCACross3_P2 (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (X - C P2X) ∣ (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross3_eval_P2_eq_zero H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet hP2_curve

/-- **`(X-RaX)² ∣ H.f - bCACross3²`.** `hP1Deriv` is stated ALREADY
FLIPPED (`2*RaY*(-vDerivAtP1) = f'.eval RaX`) to match what
`bCACross3_deriv_eval_Ra` actually proves — checked algebraically
against that lemma's conclusion, same discipline as
`CAWitnessCrossTangentV2.lean`'s `dvd_sq_pairNormBCACross2_Ra`, not
copied by pattern-matching. -/
theorem dvd_sq_pairNormBCACross3_Ra (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 ∣ (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) := by
  have h0 : (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2).eval RaX = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow,
      bCACross3_eval_Ra Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet, hRa_curve]
    ring
  have h1 : (derivative
      (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2)).eval RaX = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sq, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      bCACross3_eval_Ra Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet,
      bCACross3_deriv_eval_Ra Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet,
      ← hP1Deriv]
    ring
  exact sq_dvd_of_eval_derivative_eq_zero' hne h0 h1

theorem dvd_pairNormBCACross3_full (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0) :
    (X - C Ra1X) * (X - C RaX) ^ 2 * (X - C P2X) ∣
      (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) := by
  have hd1 := dvd_pairNormBCACross3_Ra1 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet hRa1_curve
  have hd2 := dvd_sq_pairNormBCACross3_Ra H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet
    hRa_curve hP1Deriv hne
  have hd3 := dvd_pairNormBCACross3_P2 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet hP2_curve
  have hc1Ra : IsCoprime (X - C Ra1X : k[X]) ((X - C RaX) ^ 2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1)).pow_right
  have hc1P2 : IsCoprime (X - C Ra1X : k[X]) (X - C P2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2)
  have hcRaP2 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C P2X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h3)).pow_left
  have hd12 : (X - C Ra1X) * (X - C RaX) ^ 2 ∣
      (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) :=
    hc1Ra.mul_dvd hd1 hd2
  have hc12P2 : IsCoprime ((X - C Ra1X : k[X]) * (X - C RaX) ^ 2) (X - C P2X) :=
    hc1P2.mul_left hcRaP2
  exact hc12P2.mul_dvd hd12 hd3

/-! ## `uCANewCross3` -/

noncomputable def denomPolyCACross3 (Ra1X RaX P2X : k) : Polynomial k :=
  (X - C Ra1X) * (X - C RaX) ^ 2 * (X - C P2X)

theorem denomPolyCACross3_monic (Ra1X RaX P2X : k) :
    (denomPolyCACross3 Ra1X RaX P2X).Monic := by
  unfold denomPolyCACross3
  exact ((Polynomial.monic_X_sub_C Ra1X).mul ((Polynomial.monic_X_sub_C RaX).pow 2)).mul
    (Polynomial.monic_X_sub_C P2X)

theorem denomPolyCACross3_natDegree (Ra1X RaX P2X : k) :
    (denomPolyCACross3 Ra1X RaX P2X).natDegree = 4 := by
  unfold denomPolyCACross3
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero Ra1X)
        (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX)))
      (Polynomial.X_sub_C_ne_zero P2X),
    Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero Ra1X)
      (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX)),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

noncomputable def uCANewCross3 (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k) : Polynomial k :=
  (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) /ₘ
    denomPolyCACross3 Ra1X RaX P2X

theorem pairNormBCACross3_eq_denomPolyCACross3_mul_uCANewCross3
    (H : HyperellipticPolynomial k)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0) :
    H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 =
      denomPolyCACross3 Ra1X RaX P2X *
        uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y := by
  have hdvd := dvd_pairNormBCACross3_full H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet
    h1 h2 h3 hRa1_curve hRa_curve hP2_curve hP1Deriv hne
  have hmod : (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) %ₘ
      denomPolyCACross3 Ra1X RaX P2X = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyCACross3_monic Ra1X RaX P2X)).mpr
      (by
        change (X - C Ra1X) * (X - C RaX) ^ 2 * (X - C P2X) ∣
          (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2)
    (q := denomPolyCACross3 Ra1X RaX P2X)
  rw [hmod, zero_add] at hadd
  unfold uCANewCross3
  exact hadd.symm

end DecoupledSystem
end Genus2Lean
