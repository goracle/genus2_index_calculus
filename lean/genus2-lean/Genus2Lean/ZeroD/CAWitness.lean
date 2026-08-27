import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.LCanonicalElementary

/-! # The single `C - A` witness (replaces the `f+`/`f-` two-witness plan)

**Claire's correction, this pass: stop building two independent
interpolations and hoping their residuals coincide — that can never
work by construction (nothing forces two unrelated 4-point Vandermonde
solves to land on the same residual quadratic).** The right move,
already implicit in how every other Mumford/Cantor object in this
codebase is built (`uRS4`, `uANew`, `uMinusNew` are all "whatever's left
over," never separately chosen): build ONE function `f := y - b(x)`
that interpolates `C - A` directly (i.e. `C + ι(A)`, `ι` the
hyperelliptic involution `(x,y) ↦ (x,-y)`, `AffinePoints.lean`'s
`Point.iota`), and let its residual quadratic BE `T`, by definition of
what Cantor reduction computes. There is no second witness and no
residual-matching question left to ask — `T` falls out of this single
construction the same way `uRS4`'s residual falls out of the K=4
interpolation, not as a separately-proved coincidence.

`f := y - b(x)`, `b` the unique degree-≤3 polynomial solving the plain
4×4 Vandermonde system:

    b(Ra1.X) = Ra1.Y
    b(Ra2.X) = Ra2.Y
    b(P1.X)  = -P1.Y      (i.e. b(ι(P1).X) = ι(P1).Y)
    b(P2.X)  = -P2.Y      (i.e. b(ι(P2).X) = ι(P2).Y)

Mechanically identical to `CantorAddWitness.lean`'s `bMinus` (same
plain, non-confluent 4×4 Vandermonde shape) — only the input points
change (`Ra1,Ra2,ι(P1),ι(P2)` instead of `P1,P2,R1,R2`), and
`CantorAddWitness.lean`'s own trailing docstring already names this
exact construction (`bMinus ≡ -vA mod uA`, "the witness vanishes at
`A`'s HYPERELLIPTIC CONJUGATE, not `A` itself") without following
through — this file follows through, replacing the two-witness plan
entirely rather than adding a third file alongside it.

**Pole order and residual, same arithmetic as `bMinus`**:
`deg b ≤ 3` ⟹ `ordInfOfPair(-b,1) = -max(2·3,5) = -6` ⟹ 6 affine zeros.
Four are named (`Ra1,Ra2,ι(P1),ι(P2)`); factoring
`H.f - b² = denomPolyCA · uCANew` (`denomPolyCA` degree 4, the four
named linear factors) gives `uCANew`, degree 2 — **this IS `T`,
definitionally, not a fact requiring a separate matching proof.**

`div(f) = Ra1 + Ra2 + ι(P1) + ι(P2) + T - 6[∞]`, i.e. (moving `ι(A)` to
the other side using `div(f) `'s support and `A := [P1]+[P2]`,
`ι(A) := [ι(P1)]+[ι(P2)]`):

    div_aff(f) = C + ι(A) + T          (C := [Ra1]+[Ra2])

which is exactly `C - A + T` at the divisor-class level (`ι(P) ~ -P` in
the sense the Jacobian's own group law already uses `ι` for inversion —
`DivisorClassGroup.lean`'s existing convention, not a new one introduced
here). This is now a SINGLE `divToPairRatio`-eligible fact on its own
(no second function needed to pair against): the class of
`C + ι(A) + T - 2•[δ₀]` (mod the fixed basepoint correction) is
`toJacobian D` of a divisor built from one witness `f`, directly
matching `hAlphaRep`'s target shape once `T := S` (this file's `uCANew`)
is substituted into `AlphaLocusDegreeUniform.lean`'s `u`.

**Supersedes `TangentMumfordWitness.lean` (`f+`) and
`CantorAddWitness.lean` (`f-`) for the purpose of
`reducedClass_eq_of_isReduction'`.** Both those files are left in place
(their content is correct in isolation, and `bMinus`'s machinery is
reused verbatim below) but neither is the right witness for this
theorem — flagging this explicitly so a future pass doesn't resume the
abandoned two-witness residual-matching question. -/

noncomputable section

set_option maxHeartbeats 1000000

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The plain 4×4 Vandermonde interpolation matrix for `b`, the `C-A`
witness.** Row 0: `Ra1.X`. Row 1: `Ra2.X`. Row 2: `P1.X` (target value
`-P1.Y`, i.e. `ι(P1).Y`, supplied at the RHS, not here). Row 3: `P2.X`.
Identical shape to `CantorAddWitness.lean`'s `minusInterpMatrix` — the
matrix only depends on x-coordinates, so reusing the same four-node
Vandermonde structure with different nodes is exactly the right amount
of code reuse (no new determinant computation needed below beyond
substituting variable names). -/
def caInterpMatrix (Ra1X Ra2X P1X P2X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, Ra1X, Ra1X ^ 2, Ra1X ^ 3;
     1, Ra2X, Ra2X ^ 2, Ra2X ^ 3;
     1, P1X,  P1X ^ 2,  P1X ^ 3;
     1, P2X,  P2X ^ 2,  P2X ^ 3]

/-- **The RHS for `b`'s 4×4 solve.** Rows 0-1: ordinary curve values at
`Ra1, Ra2`. Rows 2-3: the NEGATED curve values at `P1, P2` — this is the
`ι` substitution, the entire content of "interpolate through `C - A`
rather than `C + A`." -/
def caInterpRHS (Ra1Y Ra2Y P1Y P2Y : k) : Fin 4 → k :=
  ![Ra1Y, Ra2Y, -P1Y, -P2Y]

/-- **Nondegeneracy: invertible iff the four x-coordinates are pairwise
distinct.** Identical proof to `minusInterpMatrix_det_ne_zero`
(`CantorAddWitness.lean`) — the determinant formula only depends on the
matrix's x-coordinate nodes, not on the RHS, so `ι`'s sign flip at
`P1,P2` doesn't affect this lemma at all. -/
theorem caInterpMatrix_det_ne_zero (Ra1X Ra2X P1X P2X : k)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X) :
    (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0 := by
  have hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det =
      (Ra2X - Ra1X) * (P1X - Ra1X) * (P2X - Ra1X) *
        (P1X - Ra2X) * (P2X - Ra2X) * (P2X - P1X) := by
    unfold caInterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (Ne.symm h12)) (sub_ne_zero.mpr (Ne.symm h1P1)))
    (sub_ne_zero.mpr (Ne.symm h1P2)))
    (sub_ne_zero.mpr (Ne.symm h2P1)))
    (sub_ne_zero.mpr (Ne.symm h2P2)))
    (sub_ne_zero.mpr (Ne.symm hPP))

/-- **`b`'s coefficients via Cramer's rule.** Same `det⁻¹ * cramer` idiom
as `minusCoeff`/`bPlusCoeff`. -/
def caCoeff (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k) (i : Fin 4) : k :=
  (caInterpMatrix Ra1X Ra2X P1X P2X).det⁻¹ *
    (Matrix.cramer (caInterpMatrix Ra1X Ra2X P1X P2X)
      (caInterpRHS Ra1Y Ra2Y P1Y P2Y) i)

/-- **`b` itself.** `∑_{i<4} C (caCoeff i) * X^i`, degree ≤ 3. -/
def bCA (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k) : Polynomial k :=
  Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 0) +
  Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 1) * X +
  Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 2) * X ^ 2 +
  Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3) * X ^ 3

theorem bCA_natDegree_le (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k) :
    (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).natDegree ≤ 3 := by
  unfold bCA
  compute_degree

/-- **Row identity, shared core.** Direct `Matrix.mulVec_cramer`
consequence, same shape as `bPlus_row_eq`/(the analogous lemma for
`minusCoeff`, inlined rather than factored out in `CantorAddWitness.lean`). -/
private theorem bCA_row_eq (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, caInterpMatrix Ra1X Ra2X P1X P2X r j *
      caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y j =
      caInterpRHS Ra1Y Ra2Y P1Y P2Y r := by
  have hexpand : ∑ j : Fin 4, caInterpMatrix Ra1X Ra2X P1X P2X r j *
      caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y j =
      (caInterpMatrix Ra1X Ra2X P1X P2X).det⁻¹ *
        (caInterpMatrix Ra1X Ra2X P1X P2X r ⬝ᵥ
          (Matrix.cramer (caInterpMatrix Ra1X Ra2X P1X P2X)
            (caInterpRHS Ra1Y Ra2Y P1Y P2Y))) := by
    unfold caCoeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (caInterpMatrix Ra1X Ra2X P1X P2X)
    (caInterpRHS Ra1Y Ra2Y P1Y P2Y)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

private theorem bCA_eval_eq_row (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y x : k) :
    (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y j := by
  unfold bCA
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem bCA_eval_Ra1 (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0) :
    (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra1X = Ra1Y := by
  rw [bCA_eval_eq_row]
  have hrow := bCA_row_eq Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet 0
  unfold caInterpMatrix caInterpRHS at hrow
  simpa using hrow

theorem bCA_eval_Ra2 (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0) :
    (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra2X = Ra2Y := by
  rw [bCA_eval_eq_row]
  have hrow := bCA_row_eq Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet 1
  unfold caInterpMatrix caInterpRHS at hrow
  simpa using hrow

/-- **`b` at `P1.X` equals `-P1.Y`** — the `ι`-substitution: `b` vanishes
against `P1`'s CONJUGATE, not `P1` itself. -/
theorem bCA_eval_P1 (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0) :
    (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P1X = -P1Y := by
  rw [bCA_eval_eq_row]
  have hrow := bCA_row_eq Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet 2
  unfold caInterpMatrix caInterpRHS at hrow
  simpa using hrow

theorem bCA_eval_P2 (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0) :
    (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P2X = -P2Y := by
  rw [bCA_eval_eq_row]
  have hrow := bCA_row_eq Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet 3
  unfold caInterpMatrix caInterpRHS at hrow
  simpa using hrow

/-- **`(X-Ra1.X) ∣ H.f - bCA²`.** Same shape as `dvd_pairNormBMinus_P1`:
`bCA.eval Ra1X = Ra1Y`, `Ra1Y² = H.f.eval Ra1X` (curve membership), so
`(H.f - bCA²).eval Ra1X = 0`. -/
theorem pairNormBCA_eval_Ra1_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) :
    (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2).eval Ra1X = 0 := by
  rw [eval_sub, eval_pow, bCA_eval_Ra1 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet, hRa1_curve, sub_self]

theorem pairNormBCA_eval_Ra2_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) :
    (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2).eval Ra2X = 0 := by
  rw [eval_sub, eval_pow, bCA_eval_Ra2 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet, hRa2_curve, sub_self]

/-- **`(X-P1.X) ∣ H.f - bCA²`.** Uses `(-P1Y)² = P1Y²` — the conjugate's
y-value squares to the same curve value, so this holds regardless of the
`ι` sign flip. -/
theorem pairNormBCA_eval_P1_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2).eval P1X = 0 := by
  rw [eval_sub, eval_pow, bCA_eval_P1 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet, neg_sq, hP1_curve, sub_self]

theorem pairNormBCA_eval_P2_eq_zero (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2).eval P2X = 0 := by
  rw [eval_sub, eval_pow, bCA_eval_P2 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet, neg_sq, hP2_curve, sub_self]

theorem dvd_pairNormBCA_Ra1 (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) :
    (X - C Ra1X) ∣ (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCA_eval_Ra1_eq_zero H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hRa1_curve

theorem dvd_pairNormBCA_Ra2 (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) :
    (X - C Ra2X) ∣ (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCA_eval_Ra2_eq_zero H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hRa2_curve

theorem dvd_pairNormBCA_P1 (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (X - C P1X) ∣ (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCA_eval_P1_eq_zero H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hP1_curve

theorem dvd_pairNormBCA_P2 (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (X - C P2X) ∣ (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCA_eval_P2_eq_zero H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hP2_curve

/-- **`denomPolyCA`, the degree-4 divisor `(X-Ra1.X)(X-Ra2.X)(X-P1.X)(X-P2.X)`.** -/
def denomPolyCA (Ra1X Ra2X P1X P2X : k) : Polynomial k :=
  (X - C Ra1X) * (X - C Ra2X) * (X - C P1X) * (X - C P2X)

theorem denomPolyCA_monic (Ra1X Ra2X P1X P2X : k) :
    (denomPolyCA Ra1X Ra2X P1X P2X).Monic := by
  unfold denomPolyCA
  exact (((Polynomial.monic_X_sub_C Ra1X).mul (Polynomial.monic_X_sub_C Ra2X)).mul
    (Polynomial.monic_X_sub_C P1X)).mul (Polynomial.monic_X_sub_C P2X)

theorem denomPolyCA_natDegree (Ra1X Ra2X P1X P2X : k) :
    (denomPolyCA Ra1X Ra2X P1X P2X).natDegree = 4 := by
  unfold denomPolyCA
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (Polynomial.X_sub_C_ne_zero Ra1X) (Polynomial.X_sub_C_ne_zero Ra2X))
        (Polynomial.X_sub_C_ne_zero P1X))
      (Polynomial.X_sub_C_ne_zero P2X),
    Polynomial.natDegree_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero Ra1X) (Polynomial.X_sub_C_ne_zero Ra2X))
      (Polynomial.X_sub_C_ne_zero P1X),
    Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero Ra1X) (Polynomial.X_sub_C_ne_zero Ra2X),
    Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]

/-- **All four factors divide `H.f - bCA²` at once.** -/
theorem dvd_pairNormBCA_full (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (X - C Ra1X) * (X - C Ra2X) * (X - C P1X) * (X - C P2X) ∣
      (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) := by
  have hd1 := dvd_pairNormBCA_Ra1 H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hRa1_curve
  have hd2 := dvd_pairNormBCA_Ra2 H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hRa2_curve
  have hd3 := dvd_pairNormBCA_P1 H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hP1_curve
  have hd4 := dvd_pairNormBCA_P2 H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet hP2_curve
  have hc12 : IsCoprime (X - C Ra1X : k[X]) (X - C Ra2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h12)
  have hc1P1 : IsCoprime (X - C Ra1X : k[X]) (X - C P1X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1P1)
  have hc2P1 : IsCoprime (X - C Ra2X : k[X]) (X - C P1X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2P1)
  have hc1P2 : IsCoprime (X - C Ra1X : k[X]) (X - C P2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1P2)
  have hc2P2 : IsCoprime (X - C Ra2X : k[X]) (X - C P2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2P2)
  have hcPP : IsCoprime (X - C P1X : k[X]) (X - C P2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact hPP)
  have hd12 : (X - C Ra1X) * (X - C Ra2X) ∣
      (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) :=
    hc12.mul_dvd hd1 hd2
  have hc12P1 : IsCoprime ((X - C Ra1X : k[X]) * (X - C Ra2X)) (X - C P1X) :=
    hc1P1.mul_left hc2P1
  have hd123 : (X - C Ra1X) * (X - C Ra2X) * (X - C P1X) ∣
      (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) :=
    hc12P1.mul_dvd hd12 hd3
  have hc123P2 : IsCoprime ((X - C Ra1X : k[X]) * (X - C Ra2X) * (X - C P1X)) (X - C P2X) :=
    (hc1P2.mul_left hc2P2).mul_left hcPP
  exact hc123P2.mul_dvd hd123 hd4

/-- **`uCANew` — THE OBJECT THAT IS `T`.** The exact quotient
`(H.f - bCA²) /ₘ denomPolyCA`. This is not "a residual we hope matches
`T`" — per this file's construction, `T` is DEFINED to be this, the
residual of the `C-A` interpolation. Any downstream file identifying `T`
(e.g. `AlphaLocusDegreeUniform.lean`'s `u`, once the missing link added
this pass is discharged) should substitute `u := uCANew` here, not
introduce a second independently-built quadratic. -/
def uCANew (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k) : Polynomial k :=
  (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) /ₘ
    denomPolyCA Ra1X Ra2X P1X P2X

theorem pairNormBCA_eq_denomPolyCA_mul_uCANew (H : HyperellipticPolynomial k)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2 =
      denomPolyCA Ra1X Ra2X P1X P2X *
        uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y := by
  have hdvd := dvd_pairNormBCA_full H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet
    h12 h1P1 h1P2 h2P1 h2P2 hPP hRa1_curve hRa2_curve hP1_curve hP2_curve
  have hmod : (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) %ₘ
      denomPolyCA Ra1X Ra2X P1X P2X = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyCA_monic Ra1X Ra2X P1X P2X)).mpr
      (by
        change (X - C Ra1X) * (X - C Ra2X) * (X - C P1X) * (X - C P2X) ∣
          (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2)
    (q := denomPolyCA Ra1X Ra2X P1X P2X)
  rw [hmod, zero_add] at hadd
  unfold uCANew
  exact hadd.symm

/-- **`bCA`'s pole order at infinity: `-6`.** Same weakened shape as
`bMinus_ordInfOfPair`/`bPlus_ordInfOfPair`: needs `caCoeff ... 3 ≠ 0`. -/
theorem bCA_ordInfOfPair (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hlead : caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3 ≠ 0) :
    ordInfOfPair (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = -6 := by
  have hdeg3 : (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).natDegree = 3 := by
    apply le_antisymm (bCA_natDegree_le Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y)
    unfold bCA
    have hcoeff3 : (Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 0) +
      Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 1) * X +
      Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 2) * X ^ 2 +
      Polynomial.C (caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3) *
        X ^ 3).coeff 3 =
        caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg : (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  rw [hAdeg, natDegree_one]
  norm_num

end DecoupledSystem
end Genus2Lean
