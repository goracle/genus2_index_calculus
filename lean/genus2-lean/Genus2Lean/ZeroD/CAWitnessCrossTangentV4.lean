import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.TangentMumfordWitness
import Genus2Lean.ZeroD.CAWitnessCrossTangent

/-! # `bCA`'s CROSS-pair tangent case, variant 4: `Ra2 = ι(sa.P2)`

Fourth and last of the four symmetric cross-pair variants (per
`ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3's closing
note: "the other 3 cross-pair variants by symmetry ... each needs the
same treatment, matrix shape differs only in which row pair is
doubled"). Confirmed via independent sympy check before writing any
Lean, same discipline as the other three variants.

**Row layout.** `caInterpMatrix`'s original rows `[Ra1, Ra2, P1, P2]`
(0,1,2,3). Here `Ra2.X = sa.P2.X =: x` collapses rows 1 and 3 — NON-
ADJACENT, the same row-position shape as `CAWitnessCrossTangent2.lean`'s
`Ra1 = ι(sa.P1)` (rows 0/2), just shifted down one row (rows 1/3
instead of 0/2), NOT the adjacent shape of `CAWitnessCrossTangentV3.lean`
(rows 1/2). Row 0: evaluation at `Ra1X` (ordinary, survives). Row 1:
evaluation at `x` (representing `Ra2`, encountered first). Row 2:
evaluation at `P1X` (ordinary, survives). Row 3: DERIVATIVE at `x`
(replacing `P2`'s old row — the confluent row).

**Sympy-verified determinant**:
`det = -(x - P1X)^2 * (P1X - Ra1X) * (x - Ra1X)^2`
— HAS the leading minus sign, matching variants 1/2
(`CAWitnessCrossTangent2.lean`'s `-(RaX-P2X)^2*(P2X-Ra2X)*(RaX-Ra2X)^2`,
`CAWitnessCrossTangentV2.lean`'s `-(RaX-Ra2X)^2*(Ra2X-P1X)*(RaX-P1X)^2`)
but UNLIKE variant 3 (`CAWitnessCrossTangentV3.lean`, no leading minus).
Checked directly via independent sympy computation before writing this
file — do not assume the sign from row-adjacency alone; variant 3's
own docstring already flagged that its sign broke the naive pattern,
and this computation confirms the sign genuinely depends on which
specific rows collide, not just adjacent-vs-non-adjacent.

**RHS signs.** Row 0 (`Ra1`, `C`-side) unflipped: `Ra1Y`. Row 1
(`Ra2`'s slot, `C`-side) unflipped: `RaY` (`= Ra2.Y` — `Ra2` is an
anchor point, always unflipped, regardless of which target point it
coincides with). Row 2 (`P1`, `ι(A)`-side) FLIPPED: `-P1Y`. Row 3
(derivative, descending from `P2`'s old `ι(A)`-side slot) FLIPPED:
`-vDerivAtP2`.

Combines matrix/coeffs/bCA/rows/dvd/uCANew into one file, following
`CAWitnessCrossTangentV2.lean`/`CAWitnessCrossTangentV3.lean`'s
precedent. With this file, all four symmetric cross-pair variants
exist (`Ra1=ι(sa.P1)`: `CAWitnessCrossTangent2.lean`/`CAWitnessCrossTangent3.lean`;
`Ra1=ι(sa.P2)`: `CAWitnessCrossTangentV2.lean`; `Ra2=ι(sa.P1)`:
`CAWitnessCrossTangentV3.lean`; `Ra2=ι(sa.P2)`: this file) — none are
yet wired into `AlphaLocusDegreeUniform.lean`'s top-level theorem;
that wiring remains the next task. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The 4×4 confluent interpolation matrix, variant 4.** Row 0:
evaluation at `Ra1X`. Row 1: evaluation at doubled node `RaX`
(`= Ra2X = sa.P2.X`). Row 2: evaluation at `P1X`. Row 3: DERIVATIVE at
`RaX`. -/
def caCross4InterpMatrix (Ra1X RaX P1X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, Ra1X, Ra1X ^ 2, Ra1X ^ 3;
     1, RaX,  RaX ^ 2,  RaX ^ 3;
     1, P1X,  P1X ^ 2,  P1X ^ 3;
     0, 1,    2 * RaX,  3 * RaX ^ 2]

/-- **RHS, variant 4.** Row 0: `Ra1Y`, unflipped. Row 1: `RaY`
(`= Ra2.Y`), unflipped. Row 2: `-P1Y`, ordinary `ι`-flip. Row 3:
`-vDerivAtP2`, the flipped target-side derivative. -/
def caCross4InterpRHS (Ra1Y RaY P1Y vDerivAtP2 : k) : Fin 4 → k :=
  ![Ra1Y, RaY, -P1Y, -vDerivAtP2]

/-- **Nondegeneracy: invertible iff `Ra1X, RaX, P1X` pairwise
distinct.** Sympy-verified closed form; HAS a leading minus sign,
matching variants 1/2, unlike variant 3 — see module docstring. -/
theorem caCross4InterpMatrix_det_ne_zero (Ra1X RaX P1X : k)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P1X) (h3 : RaX ≠ P1X) :
    (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0 := by
  have hdet : (caCross4InterpMatrix Ra1X RaX P1X).det =
      -(RaX - P1X) ^ 2 * (P1X - Ra1X) * (RaX - Ra1X) ^ 2 := by
    unfold caCross4InterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr
    (pow_ne_zero 2 (sub_ne_zero.mpr h3))) (sub_ne_zero.mpr (Ne.symm h2)))
    (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h1)))

noncomputable def caCross4Coeff (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (i : Fin 4) : k :=
  (caCross4InterpMatrix Ra1X RaX P1X).det⁻¹ *
    (Matrix.cramer (caCross4InterpMatrix Ra1X RaX P1X)
      (caCross4InterpRHS Ra1Y RaY P1Y vDerivAtP2) i)

noncomputable def bCACross4 (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k) :
    Polynomial k :=
  Polynomial.C (caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 0) +
  Polynomial.C (caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 1) * X +
  Polynomial.C (caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 2) * X ^ 2 +
  Polynomial.C (caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 3) * X ^ 3

theorem bCACross4_natDegree_le (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k) :
    (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).natDegree ≤ 3 := by
  unfold bCACross4
  compute_degree

private theorem bCACross4_row_eq (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, caCross4InterpMatrix Ra1X RaX P1X r j *
      caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 j =
      caCross4InterpRHS Ra1Y RaY P1Y vDerivAtP2 r := by
  have hexpand : ∑ j : Fin 4, caCross4InterpMatrix Ra1X RaX P1X r j *
      caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 j =
      (caCross4InterpMatrix Ra1X RaX P1X).det⁻¹ *
        (caCross4InterpMatrix Ra1X RaX P1X r ⬝ᵥ
          (Matrix.cramer (caCross4InterpMatrix Ra1X RaX P1X)
            (caCross4InterpRHS Ra1Y RaY P1Y vDerivAtP2))) := by
    unfold caCross4Coeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (caCross4InterpMatrix Ra1X RaX P1X)
    (caCross4InterpRHS Ra1Y RaY P1Y vDerivAtP2)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

private theorem bCACross4_eval_eq_row (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 x : k) :
    (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 j := by
  unfold bCACross4
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem bCACross4_eval_Ra1 (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0) :
    (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval Ra1X = Ra1Y := by
  rw [bCACross4_eval_eq_row]
  have hrow := bCACross4_row_eq Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet 0
  have hmat : caCross4InterpMatrix Ra1X RaX P1X 0 = ![(1 : k), Ra1X, Ra1X ^ 2, Ra1X ^ 3] := by
    unfold caCross4InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross4InterpRHS] using hrow

theorem bCACross4_eval_Ra (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0) :
    (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval RaX = RaY := by
  rw [bCACross4_eval_eq_row]
  have hrow := bCACross4_row_eq Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet 1
  have hmat : caCross4InterpMatrix Ra1X RaX P1X 1 = ![(1 : k), RaX, RaX ^ 2, RaX ^ 3] := by
    unfold caCross4InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross4InterpRHS] using hrow

theorem bCACross4_eval_P1 (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0) :
    (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2).eval P1X = -P1Y := by
  rw [bCACross4_eval_eq_row]
  have hrow := bCACross4_row_eq Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet 2
  have hmat : caCross4InterpMatrix Ra1X RaX P1X 2 = ![(1 : k), P1X, P1X ^ 2, P1X ^ 3] := by
    unfold caCross4InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caCross4InterpRHS] using hrow

/-- **Row 3, the confluent/tangency row: derivative at `RaX` equals
`-vDerivAtP2`.** -/
theorem bCACross4_deriv_eval_Ra (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0) :
    (derivative (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2)).eval RaX =
      -vDerivAtP2 := by
  have hrow := bCACross4_row_eq Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet 3
  have hmat : caCross4InterpMatrix Ra1X RaX P1X 3 = ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] := by
    unfold caCross4InterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simp only [caCross4InterpRHS] at hrow
  have hderiv : (derivative (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2)).eval RaX =
      ∑ j : Fin 4, ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] j *
        caCross4Coeff Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 j := by
    unfold bCACross4
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

theorem pairNormBCACross4_eval_Ra1_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) :
    (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2).eval Ra1X = 0 := by
  rw [eval_sub, eval_pow, bCACross4_eval_Ra1 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet,
    hRa1_curve, sub_self]

theorem pairNormBCACross4_eval_P1_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2).eval P1X = 0 := by
  rw [eval_sub, eval_pow, bCACross4_eval_P1 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet,
    neg_sq, hP1_curve, sub_self]

theorem dvd_pairNormBCACross4_Ra1 (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) :
    (X - C Ra1X) ∣ (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross4_eval_Ra1_eq_zero H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet hRa1_curve

theorem dvd_pairNormBCACross4_P1 (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (X - C P1X) ∣ (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross4_eval_P1_eq_zero H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet hP1_curve

/-- **`(X-RaX)² ∣ H.f - bCACross4²`.** `hP2Deriv` is stated ALREADY
FLIPPED (`2*RaY*(-vDerivAtP2) = f'.eval RaX`) to match what
`bCACross4_deriv_eval_Ra` actually proves — checked algebraically
against that lemma's conclusion, same discipline as the other three
variants' analogous lemmas, not copied by pattern-matching. -/
theorem dvd_sq_pairNormBCACross4_Ra (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 ∣ (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2) := by
  have h0 : (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2).eval RaX = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow,
      bCACross4_eval_Ra Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet, hRa_curve]
    ring
  have h1 : (derivative
      (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2)).eval RaX = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sq, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      bCACross4_eval_Ra Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet,
      bCACross4_deriv_eval_Ra Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet,
      ← hP2Deriv]
    ring
  exact sq_dvd_of_eval_derivative_eq_zero' hne h0 h1

theorem dvd_pairNormBCACross4_full (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P1X) (h3 : RaX ≠ P1X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2 ≠ 0) :
    (X - C Ra1X) * (X - C RaX) ^ 2 * (X - C P1X) ∣
      (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2) := by
  have hd1 := dvd_pairNormBCACross4_Ra1 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet hRa1_curve
  have hd2 := dvd_sq_pairNormBCACross4_Ra H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet
    hRa_curve hP2Deriv hne
  have hd3 := dvd_pairNormBCACross4_P1 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet hP1_curve
  have hc1Ra : IsCoprime (X - C Ra1X : k[X]) ((X - C RaX) ^ 2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1)).pow_right
  have hc1P1 : IsCoprime (X - C Ra1X : k[X]) (X - C P1X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2)
  have hcRaP1 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C P1X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h3)).pow_left
  have hd12 : (X - C Ra1X) * (X - C RaX) ^ 2 ∣
      (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2) :=
    hc1Ra.mul_dvd hd1 hd2
  have hc12P1 : IsCoprime ((X - C Ra1X : k[X]) * (X - C RaX) ^ 2) (X - C P1X) :=
    hc1P1.mul_left hcRaP1
  exact hc12P1.mul_dvd hd12 hd3

/-! ## `uCANewCross4` -/

noncomputable def denomPolyCACross4 (Ra1X RaX P1X : k) : Polynomial k :=
  (X - C Ra1X) * (X - C RaX) ^ 2 * (X - C P1X)

theorem denomPolyCACross4_monic (Ra1X RaX P1X : k) :
    (denomPolyCACross4 Ra1X RaX P1X).Monic := by
  unfold denomPolyCACross4
  exact ((Polynomial.monic_X_sub_C Ra1X).mul ((Polynomial.monic_X_sub_C RaX).pow 2)).mul
    (Polynomial.monic_X_sub_C P1X)

theorem denomPolyCACross4_natDegree (Ra1X RaX P1X : k) :
    (denomPolyCACross4 Ra1X RaX P1X).natDegree = 4 := by
  unfold denomPolyCACross4
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero Ra1X)
        (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX)))
      (Polynomial.X_sub_C_ne_zero P1X),
    Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero Ra1X)
      (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX)),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

noncomputable def uCANewCross4 (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k) : Polynomial k :=
  (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2) /ₘ
    denomPolyCACross4 Ra1X RaX P1X

theorem pairNormBCACross4_eq_denomPolyCACross4_mul_uCANewCross4
    (H : HyperellipticPolynomial k)
    (Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 : k)
    (hdet : (caCross4InterpMatrix Ra1X RaX P1X).det ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P1X) (h3 : RaX ≠ P1X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2 ≠ 0) :
    H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2 =
      denomPolyCACross4 Ra1X RaX P1X *
        uCANewCross4 H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 := by
  have hdvd := dvd_pairNormBCACross4_full H Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2 hdet
    h1 h2 h3 hRa1_curve hRa_curve hP1_curve hP2Deriv hne
  have hmod : (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2) %ₘ
      denomPolyCACross4 Ra1X RaX P1X = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyCACross4_monic Ra1X RaX P1X)).mpr
      (by
        change (X - C Ra1X) * (X - C RaX) ^ 2 * (X - C P1X) ∣
          (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (H.f - (bCACross4 Ra1X RaX P1X Ra1Y RaY P1Y vDerivAtP2) ^ 2)
    (q := denomPolyCACross4 Ra1X RaX P1X)
  rw [hmod, zero_add] at hadd
  unfold uCANewCross4
  exact hadd.symm

end DecoupledSystem
end Genus2Lean
