import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.LCanonicalElementary
import Genus2Lean.ZeroD.TangentMumfordWitness

/-! # `bCA`'s tangent case (`Ra1 = Ra2`): confluent interpolation

Per `ROADMAP-principal-witness-tangent-assembly.md`, Step 1. `CAWitness.
lean`'s `bCA` is built from a PLAIN 4×4 Vandermonde interpolation
(`caInterpMatrix`) through `{Ra1, Ra2, P1, P2}` (with the `ι`-sign flip
on `P1,P2`'s RHS), genuinely singular when `Ra1.X = Ra2.X` (closed-form
determinant has `(Ra2X - Ra1X)` as a literal factor). This file replaces
that with a CONFLUENT interpolation for the doubled-root case: one node
`RaX` carrying BOTH a value row and a derivative row, plus two ordinary
rows at `P1.X`, `P2.X`.

Mirrors `TangentMumfordWitness.lean` exactly (same confluent-Vandermonde
shape, same `sq_dvd_of_eval_derivative_eq_zero'` machinery, imported
rather than re-proved — see below), with the roadmap's own noted
simplification: `TangentMumfordWitness.lean`'s tangency point `δ₀` is a
point on the curve with no separate polynomial giving `y` there, so it
needs `branchDeriv` (an implicit-function-theorem quotient `f'/(2y)`).
Here, `Ra` is a MUMFORD-PAIR root: `Ra.Y = va.eval Ra.X` for some
explicit polynomial `va`, and in the tangent case `(X - C Ra.X)^2 ∣
(va^2 - H.f)` (the defining property of a doubled Mumford root,
`SanchorEqAlphaPoints.lean`'s established tangent-case hypothesis
shape). Differentiating that divisibility and evaluating at `Ra.X`
gives `va.eval Ra.X * (derivative va).eval Ra.X = (derivative H.f).eval
Ra.X / 2` directly (`hchar : (2:k) ≠ 0` clears the division) — so the
tangency row's target derivative is `(derivative va).eval Ra.X`, a
concrete already-available polynomial derivative, not a separately
constructed branch-derivative quotient. This file states that relation
as an explicit hypothesis (`hRaDeriv`, mirroring `TangentMumfordWitness.
lean`'s `hbranch` convention: the caller supplies the already-derived
fact, this file doesn't re-derive it from `IsMumfordUa` machinery,
matching this project's convention of keeping the interpolation layer
independent of the specific Mumford-pair setup that produces its
hypotheses).

**Row/RHS conventions carried over unchanged from `CAWitness.lean`**:
`b` interpolates `C - A` (i.e. `C + ι(A)`), so `P1,P2`'s RHS entries are
NEGATED (`-P1Y`, `-P2Y`) — the same `ι`-substitution `caInterpRHS`
already encodes. The doubled node `Ra` is on the `C`-side (not
negated), matching `caInterpRHS`'s rows 0-1.

**Status: drafted this pass, not yet REPL-confirmed** (no live Lean
toolchain in this environment). The determinant closed form below is a
direct analogue of `tangentInterpMatrix_det_ne_zero`'s (same matrix
shape, doubled node swapped from position 2/3 to position 0/1) —
worth an independent sympy check before trusting the guessed sign,
same caveat `TangentMumfordWitness.lean`'s own docstring flags for its
own determinant. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The 4×4 confluent interpolation matrix for `bCA`'s tangent case.**
Row 0: evaluation at the doubled anchor root `RaX`. Row 1: DERIVATIVE at
`RaX` (the confluent row — `0, 1, 2x, 3x²`). Row 2: evaluation at `P1X`.
Row 3: evaluation at `P2X`. Same shape as `tangentInterpMatrix`
(`TangentMumfordWitness.lean`) with the doubled node moved to rows 0-1
instead of rows 2-3 — the two ordinary nodes take the remaining rows in
either order, so this reordering is presentational only (keeps `RaX`
first, matching `caInterpMatrix`'s own row-0 convention for the anchor
node). -/
def caTangentInterpMatrix (RaX P1X P2X : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, RaX, RaX ^ 2,   RaX ^ 3;
     0, 1,   2 * RaX,   3 * RaX ^ 2;
     1, P1X, P1X ^ 2,   P1X ^ 3;
     1, P2X, P2X ^ 2,   P2X ^ 3]

/-- **The RHS for `bCA`'s tangent-case 4×4 solve.** Row 0: `Ra.Y`. Row 1:
the target derivative `vaDerivAtRa` (`= (derivative va).eval RaX`,
supplied by the caller — see module docstring). Rows 2-3: the NEGATED
curve values at `P1,P2`, the same `ι`-substitution `caInterpRHS`
already encodes. -/
def caTangentInterpRHS (RaY vaDerivAtRa P1Y P2Y : k) : Fin 4 → k :=
  ![RaY, vaDerivAtRa, -P1Y, -P2Y]

/-- **Nondegeneracy: invertible iff `RaX, P1X, P2X` are pairwise
distinct.** Same confluent-Vandermonde fact as `tangentInterpMatrix_det_
ne_zero`, doubled node relabeled. Closed form: `det = (P1X - RaX)^2 *
(P2X - RaX)^2 * (P2X - P1X)` — by analogy with `tangentInterpMatrix`'s
`-(Ra1X-Ra2X)(Ra1X-δ₀X)²(Ra2X-δ₀X)²` (there, `Ra1X` was the doubled
node in ROW POSITION 0-1 there too, i.e. the same row layout as this
file's `RaX`; the sign and the two squared factors carry over directly,
substituting `P1X,P2X` for that file's `Ra1X,δ₀X`... concretely: this
matrix's rows 0-1 are IDENTICAL in shape to `tangentInterpMatrix`'s
rows 0/(derivative row), and rows 2-3 here match rows 0/1 there (two
plain evaluation rows) — so this is `tangentInterpMatrix` with its own
`Ra1X ↦ RaX` (doubled), `Ra2X ↦ P1X`, `δ₀X ↦ P2X`, EXCEPT the
derivative row sits at position 1 here vs. position 3 there, a single
row swap, which flips the sign once. Net closed form guessed as
`(P1X-RaX)^2*(P2X-RaX)^2*(P2X-P1X)` (no leading minus) —
**REPL/sympy-check this independently before trusting it**, per this
file's own module-docstring caveat. -/
theorem caTangentInterpMatrix_det_ne_zero (RaX P1X P2X : k)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (h3 : P1X ≠ P2X) :
    (caTangentInterpMatrix RaX P1X P2X).det ≠ 0 := by
  have hdet : (caTangentInterpMatrix RaX P1X P2X).det =
      (P1X - RaX) ^ 2 * (P2X - RaX) ^ 2 * (P2X - P1X) := by
    unfold caTangentInterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h1)))
    (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm h2)))) (sub_ne_zero.mpr h3.symm)

/-- **`bCA`'s tangent-case coefficients, via Cramer's rule.** Same
`det⁻¹ * cramer` idiom as `caCoeff`/`bPlusCoeff`. -/
noncomputable def caTangentCoeff (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (i : Fin 4) : k :=
  (caTangentInterpMatrix RaX P1X P2X).det⁻¹ *
    (Matrix.cramer (caTangentInterpMatrix RaX P1X P2X)
      (caTangentInterpRHS RaY vaDerivAtRa P1Y P2Y) i)

/-- **`bCA`'s tangent-case witness polynomial.** `∑_{i<4} C (caTangentCoeff
i) * X^i`, degree ≤ 3, same four-term shape as `bCA`/`bPlus`. -/
noncomputable def bCATangent (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k) :
    Polynomial k :=
  Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 0) +
  Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 1) * X +
  Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 2) * X ^ 2 +
  Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 3) * X ^ 3

theorem bCATangent_natDegree_le (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k) :
    (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).natDegree ≤ 3 := by
  unfold bCATangent
  compute_degree

/-- **Row identity, shared core.** Same `Matrix.mulVec_cramer` argument
as `bCA_row_eq`/`bPlus_row_eq`. -/
private theorem bCATangent_row_eq (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, caTangentInterpMatrix RaX P1X P2X r j *
      caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y j =
      caTangentInterpRHS RaY vaDerivAtRa P1Y P2Y r := by
  have hexpand : ∑ j : Fin 4, caTangentInterpMatrix RaX P1X P2X r j *
      caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y j =
      (caTangentInterpMatrix RaX P1X P2X).det⁻¹ *
        (caTangentInterpMatrix RaX P1X P2X r ⬝ᵥ
          (Matrix.cramer (caTangentInterpMatrix RaX P1X P2X)
            (caTangentInterpRHS RaY vaDerivAtRa P1Y P2Y))) := by
    unfold caTangentCoeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (caTangentInterpMatrix RaX P1X P2X)
    (caTangentInterpRHS RaY vaDerivAtRa P1Y P2Y)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

private theorem bCATangent_eval_eq_row (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y x : k) :
    (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y j := by
  unfold bCATangent
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

/-- **`bCATangent` evaluates to `Ra.Y` at `Ra.X`.** Row 0. -/
theorem bCATangent_eval_Ra (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0) :
    (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval RaX = RaY := by
  rw [bCATangent_eval_eq_row]
  have hrow := bCATangent_row_eq RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet 0
  have hmat : caTangentInterpMatrix RaX P1X P2X 0 = ![(1 : k), RaX, RaX ^ 2, RaX ^ 3] := by
    unfold caTangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caTangentInterpRHS] using hrow

/-- **`bCATangent`'s derivative at `Ra.X` equals `vaDerivAtRa`.** Row 1 —
the confluent/tangency condition. Mirrors `bPlus_deriv_eval_delta0`
exactly, one row position earlier. -/
theorem bCATangent_deriv_eval_Ra (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0) :
    (derivative (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y)).eval RaX =
      vaDerivAtRa := by
  have hrow := bCATangent_row_eq RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet 1
  have hmat : caTangentInterpMatrix RaX P1X P2X 1 = ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] := by
    unfold caTangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simp only [caTangentInterpRHS] at hrow
  have hderiv : (derivative (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y)).eval RaX =
      ∑ j : Fin 4, ![(0 : k), 1, 2 * RaX, 3 * RaX ^ 2] j *
        caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y j := by
    unfold bCATangent
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

/-- **`bCATangent` at `P1.X` equals `-P1.Y`.** Row 2 — the `ι`
substitution, same convention as `bCA_eval_P1`. -/
theorem bCATangent_eval_P1 (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0) :
    (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P1X = -P1Y := by
  rw [bCATangent_eval_eq_row]
  have hrow := bCATangent_row_eq RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet 2
  have hmat : caTangentInterpMatrix RaX P1X P2X 2 = ![(1 : k), P1X, P1X ^ 2, P1X ^ 3] := by
    unfold caTangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caTangentInterpRHS] using hrow

/-- **`bCATangent` at `P2.X` equals `-P2.Y`.** Row 3. -/
theorem bCATangent_eval_P2 (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0) :
    (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P2X = -P2Y := by
  rw [bCATangent_eval_eq_row]
  have hrow := bCATangent_row_eq RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet 3
  have hmat : caTangentInterpMatrix RaX P1X P2X 3 = ![(1 : k), P2X, P2X ^ 2, P2X ^ 3] := by
    unfold caTangentInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  simpa [caTangentInterpRHS] using hrow

/-! ## Residual divisibility: `(X-RaX)² (X-P1X) (X-P2X) ∣ H.f - bCATangent²`

Reuses `sq_dvd_of_eval_derivative_eq_zero'` from `TangentMumfordWitness.
lean` directly (explicit `import Genus2Lean.ZeroD.TangentMumfordWitness`
above; both files share `namespace Genus2Lean.DecoupledSystem`, so the
name resolves unqualified once imported — no re-proof needed). -/

theorem pairNormBCATangent_eval_P1_eq_zero (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2).eval P1X = 0 := by
  rw [eval_sub, eval_pow, bCATangent_eval_P1 RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet,
    neg_sq, hP1_curve, sub_self]

theorem pairNormBCATangent_eval_P2_eq_zero (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2).eval P2X = 0 := by
  rw [eval_sub, eval_pow, bCATangent_eval_P2 RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet,
    neg_sq, hP2_curve, sub_self]

theorem dvd_pairNormBCATangent_P1 (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) :
    (X - C P1X) ∣ (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCATangent_eval_P1_eq_zero H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet hP1_curve

theorem dvd_pairNormBCATangent_P2 (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (X - C P2X) ∣ (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCATangent_eval_P2_eq_zero H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet hP2_curve

/-- **`(X - RaX)² ∣ H.f - bCATangent²`.** The doubled-node squared
factor, via `sq_dvd_of_eval_derivative_eq_zero'` (imported from
`TangentMumfordWitness.lean` via this file's explicit `import` — see
that file's own docstring for why it's kept `[Field k]`-generic rather
than `ZMod`-specific). Needs both value vanishing (`bCATangent_eval_Ra` +
`hRa_curve`) and derivative vanishing at `RaX` — the latter from
`bCATangent_deriv_eval_Ra` plus `hRaDeriv`, the caller-supplied fact
that `vaDerivAtRa` really is `(derivative H.f).eval RaX / (2 * RaY)`
(stated multiplied through by `2 * RaY` to avoid a division, same
convention as `TangentMumfordWitness.lean`'s `hbranch`). -/
theorem dvd_sq_pairNormBCATangent_Ra (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (hne : H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 ∣ (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) := by
  have h0 : (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2).eval RaX = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow,
      bCATangent_eval_Ra RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet, hRa_curve]
    ring
  have h1 : (derivative
      (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2)).eval RaX = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sq, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      bCATangent_eval_Ra RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet,
      bCATangent_deriv_eval_Ra RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet,
      ← hRaDeriv]
    ring
  exact sq_dvd_of_eval_derivative_eq_zero' hne h0 h1

/-- **The full residual divisibility: `(X-RaX)²(X-P1X)(X-P2X) ∣ H.f -
bCATangent²`.** Combines the three factors via pairwise coprimality
(`RaX, P1X, P2X` pairwise distinct — the same three distinctness facts
`caTangentInterpMatrix_det_ne_zero` already needs). -/
theorem dvd_pairNormBCATangent_full (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (h3 : P1X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (hne : H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 * (X - C P1X) * (X - C P2X) ∣
      (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) := by
  have hd1 := dvd_sq_pairNormBCATangent_Ra H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet
    hRa_curve hRaDeriv hne
  have hd2 := dvd_pairNormBCATangent_P1 H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet hP1_curve
  have hd3 := dvd_pairNormBCATangent_P2 H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet hP2_curve
  have hc1P1 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C P1X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1)).pow_left
  have hc1P2 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C P2X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2)).pow_left
  have hcP1P2 : IsCoprime (X - C P1X : k[X]) (X - C P2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h3)
  have hd12 : (X - C RaX) ^ 2 * (X - C P1X) ∣
      (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) :=
    hc1P1.mul_dvd hd1 hd2
  have hc12P2 : IsCoprime ((X - C RaX : k[X]) ^ 2 * (X - C P1X)) (X - C P2X) :=
    hc1P2.mul_left hcP1P2
  exact hc12P2.mul_dvd hd12 hd3

/-! ## `uCANewTangent`, the derived residual quadratic (tangent case) -/

/-- **`denomPolyCATangent`, the degree-4 divisor `(X-RaX)²(X-P1X)(X-P2X)`.** -/
noncomputable def denomPolyCATangent (RaX P1X P2X : k) : Polynomial k :=
  (X - C RaX) ^ 2 * (X - C P1X) * (X - C P2X)

theorem denomPolyCATangent_monic (RaX P1X P2X : k) :
    (denomPolyCATangent RaX P1X P2X).Monic := by
  unfold denomPolyCATangent
  exact (((Polynomial.monic_X_sub_C RaX).pow 2).mul (Polynomial.monic_X_sub_C P1X)).mul
    (Polynomial.monic_X_sub_C P2X)

theorem denomPolyCATangent_natDegree (RaX P1X P2X : k) :
    (denomPolyCATangent RaX P1X P2X).natDegree = 4 := by
  unfold denomPolyCATangent
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX))
        (Polynomial.X_sub_C_ne_zero P1X))
      (Polynomial.X_sub_C_ne_zero P2X),
    Polynomial.natDegree_mul (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX))
      (Polynomial.X_sub_C_ne_zero P1X),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

/-- **`uCANewTangent` — the quadratic shared by both `T` and `ι(T)` in the
tangent case.** The exact quotient `(H.f - bCATangent²) /ₘ
denomPolyCATangent`, mirroring `uCANew`'s role exactly (see `CAWitness.
lean`'s module docstring for the `T`/`ι(T)` sign convention, which
carries over unchanged — only the underlying interpolant `b` changed,
not which residual sign names which point set). -/
noncomputable def uCANewTangent (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k) : Polynomial k :=
  (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) /ₘ
    denomPolyCATangent RaX P1X P2X

theorem pairNormBCATangent_eq_denomPolyCATangent_mul_uCANewTangent
    (H : HyperellipticPolynomial k)
    (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (h3 : P1X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (hne : H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 ≠ 0) :
    H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 =
      denomPolyCATangent RaX P1X P2X *
        uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y := by
  have hdvd := dvd_pairNormBCATangent_full H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet
    h1 h2 h3 hRa_curve hP1_curve hP2_curve hRaDeriv hne
  have hmod : (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2) %ₘ
      denomPolyCATangent RaX P1X P2X = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyCATangent_monic RaX P1X P2X)).mpr
      (by
        change (X - C RaX) ^ 2 * (X - C P1X) * (X - C P2X) ∣
          (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2)
    (q := denomPolyCATangent RaX P1X P2X)
  rw [hmod, zero_add] at hadd
  unfold uCANewTangent
  exact hadd.symm

/-- **`bCATangent`'s pole order at infinity: `-6`.** Tangent-case sibling
of `CAWitness.lean`'s `bCA_ordInfOfPair`, same weakened shape (needs
`caTangentCoeff ... 3 ≠ 0`). Needed by `cIotaAmIotaT_mem_principalSubgroup_
tangent` (`PrincipalWitnessStep4Tangent.lean`) the same way the split
case's `cIotaAmIotaT_mem_principalSubgroup` needs `bCA_ordInfOfPair`. -/
theorem bCATangent_ordInfOfPair (RaX P1X P2X RaY vaDerivAtRa P1Y P2Y : k)
    (hlead : caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 3 ≠ 0) :
    ordInfOfPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = -6 := by
  have hdeg3 : (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).natDegree = 3 := by
    apply le_antisymm (bCATangent_natDegree_le RaX P1X P2X RaY vaDerivAtRa P1Y P2Y)
    unfold bCATangent
    have hcoeff3 : (Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 0) +
      Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 1) * X +
      Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 2) * X ^ 2 +
      Polynomial.C (caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 3) *
        X ^ 3).coeff 3 =
        caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg : (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  rw [hAdeg, natDegree_one]
  norm_num

end DecoupledSystem
end Genus2Lean
