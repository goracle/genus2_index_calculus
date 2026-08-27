import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.LCanonicalElementary

/-! # The `f-` witness for `ROADMAP-principal-witness-assembly.md`'s
`A + T` construction (companion to `TangentMumfordWitness.lean`'s `f+`)

**REBUILT THIS PASS — the previous version of this file was wrong and is
discarded.** The earlier draft built `bMinus` via a CRT/Cantor-addition
congruence pair (`bMinus ≡ vC mod uC`, `bMinus ≡ -vA mod uA`), which
witnesses `C + ι(A)`, not `A + T`. A ChatGPT consultation (prompted
against that wrong construction) confirmed algebraically that no such
pair can ever cancel against `f+` to produce `C - A - T + 2•[δ₀]`: `f+`
and that old `f-` don't even share a common residual on the same sheet
(`gcd`/`dvd` argument: `u_C ∣ (bPlus - bMinus_old)`, and a shared
same-sheet residual `q` would need `q ∣ (bPlus - bMinus_old)` too, forcing
`q ∣ ℓ` for a degree-≤1 `ℓ`, impossible for `deg q = 2`). That whole
construction is the wrong pair of witnesses and is not being repaired.

**The correct construction, per the roadmap's own resolved arithmetic**
(`ROADMAP-principal-witness-assembly.md`, "Update within this same pass:
found and fixed a real miscount..." section): `f-` must be built the
SAME way `f+` was — direct interpolation through the actual named
points, then square-and-divide against `H.f` to read off the residual —
not as a composition of two independently-built two-point Mumford
witnesses. Concretely:

`f- := y - b_-(x)`, where `b_-` is the UNIQUE degree-≤3 polynomial
solving FOUR ORDINARY evaluation conditions (no tangency, no CRT, no
named quadratic `uC`/`uA` — this is deliberately simpler than the old
wrong draft):

    b_-(P1.X) = P1.Y
    b_-(P2.X) = P2.Y
    b_-(R1.X) = R1.Y
    b_-(R2.X) = R2.Y

Four simple point-value constraints pin down `b_-`'s four coefficients
via a PLAIN (non-confluent) 4×4 Vandermonde solve — actually simpler
than `bPlus`'s confluent case (`TangentMumfordWitness.lean`), which had
a repeated node (`δ₀`) carrying both a value and a derivative row. Here
all four nodes (`P1.X, P2.X, R1.X, R2.X`) are ordinary evaluation rows,
so `minusInterpMatrix` is a genuine Vandermonde matrix, invertible iff
the four x-coordinates are pairwise distinct (the classical Vandermonde
nondegeneracy condition, no confluent/Hermite subtlety).

**Degree/pole-order arithmetic** (confirmed by hand, matches `f+`'s own
corrected `-6` exactly — see the roadmap's "Update... found and fixed a
real miscount" section): `deg b_- ≤ 3` (generically `= 3`), so
`ordInfOfPair(-b_-, 1) = -max(2·3, 5) = -6`. This means `y - b_-(x)` has
6 total affine zeros. Four of them are the named points `P1, P2, R1, R2`
(assuming they're distinct and generic); `H.f - b_-² = denomPolyMinus *
uMinusNew` where `denomPolyMinus := (X-P1.X)(X-P2.X)(X-R1.X)(X-R2.X)`
(degree 4) and `uMinusNew` is the resulting degree-2 residual quotient —
exactly mirroring `TangentMumfordWitness.lean`'s `denomPoly`/`uANew`
pair, one level simpler (no squared factor, since there's no tangency
point here). `uMinusNew`'s two roots, lifted with `y = b_-(x)` (the SAME
sheet-choice `f+`'s own residual `uANew`-lift uses — see
`TangentMumfordWitness.lean`'s `pairNormBPlus_eq_denomPoly_mul_uANew`),
are `f-`'s residual pair.

**Whether this residual matches `f+`'s own residual (the roadmap's
`R+ ?= R-` question) is NOT decided here.** That is real
divisor/Jacobian content (the actual Abel–Jacobi/Cantor relation this
whole construction exists to witness), not mechanical composition — see
this project's convention of handing genuinely open math to ChatGPT
rather than guessing a `sorry`-free proof. This file only builds `b_-`
and its basic polynomial-level facts (degree bound, evaluation-row
lemmas, the factorization `H.f - b_-² = denomPolyMinus * uMinusNew`, and
`ordInfOfPair(-b_-, 1) = -6` under a nondegeneracy hypothesis mirroring
`bPlus_ordInfOfPair`'s). The residual-matching question is the next
thing to hand to ChatGPT once this file is confirmed build-green. -/

noncomputable section

set_option maxHeartbeats 1000000

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The plain 4×4 Vandermonde interpolation matrix for `b_-`.** Row 0:
evaluation at `P1.X` (`1, x, x², x³`). Row 1: evaluation at `P2.X`. Row
2: evaluation at `R1.X`. Row 3: evaluation at `R2.X` — all four rows the
SAME ordinary-evaluation shape (unlike `tangentInterpMatrix`, which has
a derivative row; there is no tangency condition anywhere in this
file). -/
def minusInterpMatrix (P1X P2X R1X R2X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, P1X, P1X ^ 2, P1X ^ 3;
     1, P2X, P2X ^ 2, P2X ^ 3;
     1, R1X, R1X ^ 2, R1X ^ 3;
     1, R2X, R2X ^ 2, R2X ^ 3]

/-- **The RHS vector for `b_-`'s 4×4 solve.** The target `y`-values
`P1.Y, P2.Y, R1.Y, R2.Y`. -/
def minusInterpRHS (P1Y P2Y R1Y R2Y : k) : Fin 4 → k :=
  ![P1Y, P2Y, R1Y, R2Y]

/-- **Nondegeneracy of the plain 4×4 Vandermonde system.** Invertible
iff `P1.X, P2.X, R1.X, R2.X` are pairwise distinct — the classical
Vandermonde determinant formula, `∏_{i<j} (xⱼ - xᵢ)` up to sign, no
confluent/Hermite subtlety since every row is an ordinary evaluation
row. Proved the same way `tangentInterpMatrix_det_ne_zero` was: cofactor
expansion via `Matrix.det_succ_row_zero` down to `Matrix.det_fin_three`,
then `ring`, rather than betting on an unverified `Matrix.det_vandermonde`
Mathlib name. -/
theorem minusInterpMatrix_det_ne_zero (P1X P2X R1X R2X : k)
    (h12 : P1X ≠ P2X) (h1R1 : P1X ≠ R1X) (h1R2 : P1X ≠ R2X)
    (h2R1 : P2X ≠ R1X) (h2R2 : P2X ≠ R2X) (hRR : R1X ≠ R2X) :
    (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0 := by
  have hdet : (minusInterpMatrix P1X P2X R1X R2X).det =
      (P2X - P1X) * (R1X - P1X) * (R2X - P1X) *
        (R1X - P2X) * (R2X - P2X) * (R2X - R1X) := by
    unfold minusInterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr (Ne.symm h12)) (sub_ne_zero.mpr (Ne.symm h1R1)))
    (sub_ne_zero.mpr (Ne.symm h1R2)))
    (sub_ne_zero.mpr (Ne.symm h2R1)))
    (sub_ne_zero.mpr (Ne.symm h2R2)))
    (sub_ne_zero.mpr (Ne.symm hRR))

/-- **`b_-`'s coefficients, via Cramer's rule.** Same idiom as
`bPlusCoeff` — `det⁻¹ * cramer`, one size (still 4×4, but non-confluent)
mirroring `TangentMumfordWitness.lean`'s pattern exactly. -/
def minusCoeff (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k) (i : Fin 4) : k :=
  (minusInterpMatrix P1X P2X R1X R2X).det⁻¹ *
    (Matrix.cramer (minusInterpMatrix P1X P2X R1X R2X)
      (minusInterpRHS P1Y P2Y R1Y R2Y) i)

/-- **`b_-` itself, as a polynomial.** `∑_{i<4} C (minusCoeff i) * X^i` —
degree ≤ 3 by construction. -/
def bMinus (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k) : Polynomial k :=
  Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 0) +
  Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 1) * X +
  Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 2) * X ^ 2 +
  Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 3) * X ^ 3

/-- **`b_-`'s degree bound: `≤ 3`.** Same style as `bPlus_natDegree_le`. -/
theorem bMinus_natDegree_le (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k) :
    (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).natDegree ≤ 3 := by
  unfold bMinus
  compute_degree

private theorem minus_row_eq (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, minusInterpMatrix P1X P2X R1X R2X r j *
      minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y j =
      minusInterpRHS P1Y P2Y R1Y R2Y r := by
  have hexpand : ∑ j : Fin 4, minusInterpMatrix P1X P2X R1X R2X r j *
      minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y j =
      (minusInterpMatrix P1X P2X R1X R2X).det⁻¹ *
        (minusInterpMatrix P1X P2X R1X R2X r ⬝ᵥ
          (Matrix.cramer (minusInterpMatrix P1X P2X R1X R2X)
            (minusInterpRHS P1Y P2Y R1Y R2Y))) := by
    unfold minusCoeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (minusInterpMatrix P1X P2X R1X R2X)
    (minusInterpRHS P1Y P2Y R1Y R2Y)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

/-- **`b_-`'s evaluation at an arbitrary `x`, as a row-vector dot
product.** Mirror of `bPlus_eval_eq_row`. -/
private theorem bMinus_eval_eq_row (P1X P2X R1X R2X P1Y P2Y R1Y R2Y x : k) :
    (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y j := by
  unfold bMinus
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- **`b_-` evaluates to `P1.Y` at `P1.X`.** Row 0. -/
theorem bMinus_eval_P1 (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0) :
    (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).eval P1X = P1Y := by
  rw [bMinus_eval_eq_row]
  have hrow0 := minus_row_eq P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet 0
  have hmat0 : minusInterpMatrix P1X P2X R1X R2X 0 =
      ![(1 : k), P1X, P1X ^ 2, P1X ^ 3] := by
    unfold minusInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat0] at hrow0
  simpa [minusInterpRHS] using hrow0

/-- **`b_-` evaluates to `P2.Y` at `P2.X`.** Row 1. -/
theorem bMinus_eval_P2 (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0) :
    (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).eval P2X = P2Y := by
  rw [bMinus_eval_eq_row]
  have hrow1 := minus_row_eq P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet 1
  have hmat1 : minusInterpMatrix P1X P2X R1X R2X 1 =
      ![(1 : k), P2X, P2X ^ 2, P2X ^ 3] := by
    unfold minusInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat1] at hrow1
  simpa [minusInterpRHS] using hrow1

/-- **`b_-` evaluates to `R1.Y` at `R1.X`.** Row 2. -/
theorem bMinus_eval_R1 (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0) :
    (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).eval R1X = R1Y := by
  rw [bMinus_eval_eq_row]
  have hrow2 := minus_row_eq P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet 2
  have hmat2 : minusInterpMatrix P1X P2X R1X R2X 2 =
      ![(1 : k), R1X, R1X ^ 2, R1X ^ 3] := by
    unfold minusInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat2] at hrow2
  simpa [minusInterpRHS] using hrow2

/-- **`b_-` evaluates to `R2.Y` at `R2.X`.** Row 3. -/
theorem bMinus_eval_R2 (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0) :
    (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).eval R2X = R2Y := by
  rw [bMinus_eval_eq_row]
  have hrow3 := minus_row_eq P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet 3
  have hmat3 : minusInterpMatrix P1X P2X R1X R2X 3 =
      ![(1 : k), R2X, R2X ^ 2, R2X ^ 3] := by
    unfold minusInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat3] at hrow3
  simpa [minusInterpRHS] using hrow3

/-- **`H.f - bMinus² = 0` at `P1.X`.** Mirror of
`pairNormBPlus_eval_Ra1_eq_zero`. -/
theorem pairNormBMinus_eval_P1_eq_zero (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = Hc.f.eval P1X) :
    (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2).eval P1X = 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_pow,
    bMinus_eval_P1 P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet, hP1_curve]
  ring

/-- **`H.f - bMinus² = 0` at `P2.X`.** Mirror of the above. -/
theorem pairNormBMinus_eval_P2_eq_zero (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = Hc.f.eval P2X) :
    (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2).eval P2X = 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_pow,
    bMinus_eval_P2 P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet, hP2_curve]
  ring

/-- **`H.f - bMinus² = 0` at `R1.X`.** Mirror of the above. -/
theorem pairNormBMinus_eval_R1_eq_zero (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hR1_curve : R1Y ^ 2 = Hc.f.eval R1X) :
    (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2).eval R1X = 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_pow,
    bMinus_eval_R1 P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet, hR1_curve]
  ring

/-- **`H.f - bMinus² = 0` at `R2.X`.** Mirror of the above. -/
theorem pairNormBMinus_eval_R2_eq_zero (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hR2_curve : R2Y ^ 2 = Hc.f.eval R2X) :
    (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2).eval R2X = 0 := by
  rw [Polynomial.eval_sub, Polynomial.eval_pow,
    bMinus_eval_R2 P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet, hR2_curve]
  ring

/-- **`(X - P1.X) ∣ H.f - bMinus²`.** Mirror of `dvd_pairNormBPlus_Ra1`. -/
theorem dvd_pairNormBMinus_P1 (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = Hc.f.eval P1X) :
    (X - C P1X) ∣ (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBMinus_eval_P1_eq_zero Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hP1_curve

/-- **`(X - P2.X) ∣ H.f - bMinus²`.** Mirror of the above. -/
theorem dvd_pairNormBMinus_P2 (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = Hc.f.eval P2X) :
    (X - C P2X) ∣ (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBMinus_eval_P2_eq_zero Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hP2_curve

/-- **`(X - R1.X) ∣ H.f - bMinus²`.** Mirror of the above. -/
theorem dvd_pairNormBMinus_R1 (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hR1_curve : R1Y ^ 2 = Hc.f.eval R1X) :
    (X - C R1X) ∣ (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBMinus_eval_R1_eq_zero Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hR1_curve

/-- **`(X - R2.X) ∣ H.f - bMinus²`.** Mirror of the above. -/
theorem dvd_pairNormBMinus_R2 (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (hR2_curve : R2Y ^ 2 = Hc.f.eval R2X) :
    (X - C R2X) ∣ (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBMinus_eval_R2_eq_zero Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hR2_curve

/-- **`denomPolyMinus`, the degree-4 monic divisor
`(X-P1.X)(X-P2.X)(X-R1.X)(X-R2.X)`, as a single polynomial.** Mirror of
`denomPoly` — one degree simpler shape (four DISTINCT simple linear
factors, no squared factor, since there's no tangency point in this
construction). -/
def denomPolyMinus (P1X P2X R1X R2X : k) : Polynomial k :=
  (X - C P1X) * (X - C P2X) * (X - C R1X) * (X - C R2X)

/-- **`denomPolyMinus` is monic.** Product of monic `(X - C _)`
factors. -/
theorem denomPolyMinus_monic (P1X P2X R1X R2X : k) :
    (denomPolyMinus P1X P2X R1X R2X).Monic := by
  unfold denomPolyMinus
  exact (((Polynomial.monic_X_sub_C P1X).mul (Polynomial.monic_X_sub_C P2X)).mul
    (Polynomial.monic_X_sub_C R1X)).mul (Polynomial.monic_X_sub_C R2X)

/-- **`denomPolyMinus` has degree exactly 4.** Four simple linear
factors: `1+1+1+1 = 4`. -/
theorem denomPolyMinus_natDegree (P1X P2X R1X R2X : k) :
    (denomPolyMinus P1X P2X R1X R2X).natDegree = 4 := by
  unfold denomPolyMinus
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (Polynomial.X_sub_C_ne_zero P1X) (Polynomial.X_sub_C_ne_zero P2X))
        (Polynomial.X_sub_C_ne_zero R1X))
      (Polynomial.X_sub_C_ne_zero R2X),
    Polynomial.natDegree_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero P1X) (Polynomial.X_sub_C_ne_zero P2X))
      (Polynomial.X_sub_C_ne_zero R1X),
    Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero P1X) (Polynomial.X_sub_C_ne_zero P2X),
    Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C]

/-- **All four simple factors divide `H.f - bMinus²` at once.** Direct
assembly from the four individual `dvd_pairNormBMinus_*` facts via
pairwise coprimality of distinct linear factors — mirror of
`dvd_pairNormBPlus_full`, one factor simpler (no squared term, so no
`.pow_right` needed anywhere). -/
theorem dvd_pairNormBMinus_full (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (h12 : P1X ≠ P2X) (h1R1 : P1X ≠ R1X) (h1R2 : P1X ≠ R2X)
    (h2R1 : P2X ≠ R1X) (h2R2 : P2X ≠ R2X) (hRR : R1X ≠ R2X)
    (hP1_curve : P1Y ^ 2 = Hc.f.eval P1X) (hP2_curve : P2Y ^ 2 = Hc.f.eval P2X)
    (hR1_curve : R1Y ^ 2 = Hc.f.eval R1X) (hR2_curve : R2Y ^ 2 = Hc.f.eval R2X) :
    (X - C P1X) * (X - C P2X) * (X - C R1X) * (X - C R2X) ∣
      (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) := by
  have hd1 := dvd_pairNormBMinus_P1 Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hP1_curve
  have hd2 := dvd_pairNormBMinus_P2 Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hP2_curve
  have hd3 := dvd_pairNormBMinus_R1 Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hR1_curve
  have hd4 := dvd_pairNormBMinus_R2 Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet hR2_curve
  have hc12 : IsCoprime (X - C P1X : k[X]) (X - C P2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h12)
  have hc1R1 : IsCoprime (X - C P1X : k[X]) (X - C R1X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1R1)
  have hc2R1 : IsCoprime (X - C P2X : k[X]) (X - C R1X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2R1)
  have hc1R2 : IsCoprime (X - C P1X : k[X]) (X - C R2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1R2)
  have hc2R2 : IsCoprime (X - C P2X : k[X]) (X - C R2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2R2)
  have hcR1R2 : IsCoprime (X - C R1X : k[X]) (X - C R2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact hRR)
  have hd12 : (X - C P1X) * (X - C P2X) ∣
      (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) :=
    hc12.mul_dvd hd1 hd2
  have hc12R1 : IsCoprime ((X - C P1X : k[X]) * (X - C P2X)) (X - C R1X) :=
    hc1R1.mul_left hc2R1
  have hd123 : (X - C P1X) * (X - C P2X) * (X - C R1X) ∣
      (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) :=
    hc12R1.mul_dvd hd12 hd3
  have hc123R2 : IsCoprime ((X - C P1X : k[X]) * (X - C P2X) * (X - C R1X)) (X - C R2X) :=
    (hc1R2.mul_left hc2R2).mul_left hcR1R2
  exact hc123R2.mul_dvd hd123 hd4

/-- **`uMinusNew`, the derived residual quadratic.** The exact quotient
`(H.f - bMinus²) /ₘ denomPolyMinus` — well-defined with zero remainder
by `dvd_pairNormBMinus_full`, mirror of `uANew`. -/
def uMinusNew (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k) : Polynomial k :=
  (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) /ₘ
    denomPolyMinus P1X P2X R1X R2X

/-- **`H.f - bMinus² = denomPolyMinus * uMinusNew`** — the defining
factorization, directly from `dvd_pairNormBMinus_full`'s zero-remainder
divisibility, mirror of `pairNormBPlus_eq_denomPoly_mul_uANew`. -/
theorem pairNormBMinus_eq_denomPolyMinus_mul_uMinusNew (Hc : HyperellipticPolynomial k)
    (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hdet : (minusInterpMatrix P1X P2X R1X R2X).det ≠ 0)
    (h12 : P1X ≠ P2X) (h1R1 : P1X ≠ R1X) (h1R2 : P1X ≠ R2X)
    (h2R1 : P2X ≠ R1X) (h2R2 : P2X ≠ R2X) (hRR : R1X ≠ R2X)
    (hP1_curve : P1Y ^ 2 = Hc.f.eval P1X) (hP2_curve : P2Y ^ 2 = Hc.f.eval P2X)
    (hR1_curve : R1Y ^ 2 = Hc.f.eval R1X) (hR2_curve : R2Y ^ 2 = Hc.f.eval R2X) :
    Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2 =
      denomPolyMinus P1X P2X R1X R2X *
        uMinusNew Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y := by
  have hdvd := dvd_pairNormBMinus_full Hc P1X P2X R1X R2X P1Y P2Y R1Y R2Y hdet
    h12 h1R1 h1R2 h2R1 h2R2 hRR hP1_curve hP2_curve hR1_curve hR2_curve
  have hmod : (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2) %ₘ
      denomPolyMinus P1X P2X R1X R2X = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyMinus_monic P1X P2X R1X R2X)).mpr
      (by
        change (X - C P1X) * (X - C P2X) * (X - C R1X) * (X - C R2X) ∣
          (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (Hc.f - (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) ^ 2)
    (q := denomPolyMinus P1X P2X R1X R2X)
  rw [hmod, zero_add] at hadd
  unfold uMinusNew
  exact hadd.symm

/-- **`b_-`'s pole order at infinity: `-6`, matching `f+`'s own `-6`
exactly.** WEAKENED, same shape as `bPlus_ordInfOfPair`: needs
`bMinusCoeff ... 3 ≠ 0` (`b_-` genuinely has degree 3, not less), since
the unconditional `= -6` claim is false when the four named points
happen to lie on a lower-degree curve. -/
theorem bMinus_ordInfOfPair (P1X P2X R1X R2X P1Y P2Y R1Y R2Y : k)
    (hlead : minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 3 ≠ 0) :
    ordInfOfPair (-bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y) (1 : k[X]) = -6 := by
  have hdeg3 : (bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).natDegree = 3 := by
    apply le_antisymm (bMinus_natDegree_le P1X P2X R1X R2X P1Y P2Y R1Y R2Y)
    unfold bMinus
    have hcoeff3 : (Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 0) +
      Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 1) * X +
      Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 2) * X ^ 2 +
      Polynomial.C (minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 3) *
        X ^ 3).coeff 3 =
        minusCoeff P1X P2X R1X R2X P1Y P2Y R1Y R2Y 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg : (-bMinus P1X P2X R1X R2X P1Y P2Y R1Y R2Y).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  rw [hAdeg, natDegree_one]
  norm_num

end DecoupledSystem
end Genus2Lean
