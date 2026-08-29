import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.LCanonicalElementary
import Genus2Lean.ZeroD.TangentMumfordWitness

/-! # `bCA`'s TARGET-tangent case (`sa.P1 = sa.P2`, i.e. `T1 = T2`):
# confluent interpolation

Per `ROADMAP-split-hypothesis-elimination.md`'s "item 2 (new)" — the
TARGET axis mirror of `ROADMAP-principal-witness-tangent-assembly.md`
(which built the ANCHOR axis's `Ra1 = Ra2` tangent case, entirely in
`CAWitnessTangent.lean` and friends). This file is the target-side
twin: `CAWitness.lean`'s `bCA` is built from a plain 4×4 Vandermonde
interpolation through `{Ra1, Ra2, P1, P2}` (with the `ι`-sign flip on
`P1,P2`'s RHS), genuinely singular when `P1.X = P2.X` (closed-form
determinant has `(P2X - P1X)` as a literal factor, same shape as
`(Ra2X - Ra1X)` did for the anchor axis, just the other pair of rows).
This file replaces that with a CONFLUENT interpolation for the
TARGET's doubled-root case: one node `PX` carrying BOTH a value row
(`ι`-sign-flipped, i.e. `-PY`) and a derivative row (also flipped,
`-vDerivAtP`, matching the sign the ordinary value row already
carries), plus two ordinary (unflipped) rows at `Ra1.X, Ra2.X`.

**Confluent node lives on the `ι`-flipped side, unlike
`CAWitnessTangent.lean`'s.** This is the one genuine asymmetry versus
the anchor-tangent file: `caTangentInterpMatrix` doubles a row that
sits on the UNFLIPPED (`C`) side of `caInterpRHS`, so its RHS is
`![RaY, vaDerivAtRa, -P1Y, -P2Y]` with the derivative row unflipped
(row 1, paired with row-0's plain `RaY`). Here the doubled node is on
the FLIPPED (`ι(A)`) side, so both the value AND derivative rows at
that node carry a minus sign: `![Ra1Y, Ra2Y, -PY, -vDerivAtP]`. The
matrix itself (which only depends on x-coordinates, not on which side
of `caInterpRHS` a row's value comes from) is identical in shape to
`caTangentInterpMatrix` with the confluent rows moved from positions
0-1 to positions 2-3 — the same row permutation
`caTangentInterpMatrix`'s own docstring already notes when comparing
itself to `tangentInterpMatrix`.

**Tangency-row derivation, symmetric to `CAWitnessTangent.lean`'s own
"key simplification" note**: `P.Y = v.eval P.X` for some explicit
polynomial `v` (the target Mumford pair's own line, same shape as
`va` on the anchor side), and in the tangent case `(X - C P.X)^2 ∣
(v^2 - H.f)` — `IsMumfordTarget4`'s tangent instance, literally the
same `Prop` shape as `IsMumfordUa`'s tangent instance
(`Reduce/AlphaReduce.lean`, `PrincipalWitnessCAConnection.lean`'s
`divToPair_negV_one_S_eq`/`_eq_tangent` already rely on this same
"unfold to the same `Prop`" identification). Differentiating and
evaluating at `P.X` gives `v.eval P.X * (derivative v).eval P.X =
(derivative H.f).eval P.X / 2` exactly as before; `hchar` clears the
division. So `vDerivAtP := (derivative v).eval P.X`, supplied as a
caller hypothesis (`hPDeriv`, mirroring `CAWitnessTangent.lean`'s
`hRaDeriv` convention) — this file does not re-derive it from
`IsMumfordTarget4` itself, matching that file's own stated convention.

**Status: drafted this pass, not yet REPL-confirmed** (no live Lean
toolchain in this environment) — same caveat as `CAWitnessTangent.
lean`'s own module docstring, including the determinant's closed-form
sign, which should be checked independently (by direct expansion or a
sympy check) before being trusted. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The 4×4 confluent interpolation matrix for `bCA`'s target-tangent
case.** Row 0: evaluation at `Ra1X`. Row 1: evaluation at `Ra2X`. Row 2:
evaluation at the doubled target root `PX`. Row 3: DERIVATIVE at `PX`
(the confluent row). Same shape as `caTangentInterpMatrix` with the
confluent rows moved to positions 2-3 instead of 0-1 (the two ordinary
nodes take rows 0-1 here, matching `caInterpMatrix`'s own row-0/row-1
convention for the anchor pair, since the anchor pair is NOT doubled in
this file). -/
def caTangentTargetInterpMatrix (Ra1X Ra2X PX : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, Ra1X, Ra1X ^ 2, Ra1X ^ 3;
     1, Ra2X, Ra2X ^ 2, Ra2X ^ 3;
     1, PX,   PX ^ 2,   PX ^ 3;
     0, 1,    2 * PX,   3 * PX ^ 2]

/-- **The RHS for `bCA`'s target-tangent-case 4×4 solve.** Rows 0-1:
ordinary curve values at `Ra1, Ra2` (unflipped — same convention as
`caInterpRHS`). Row 2: `-PY`, the `ι`-flipped value at the doubled
target root. Row 3: `-vDerivAtP`, the `ι`-flipped target derivative
(`vDerivAtP := (derivative v).eval PX`, supplied by the caller — see
module docstring). Both row 2 and row 3 carry the flip, since both
come from the target ("`A`") side of `caInterpRHS`'s `C - A`
convention, unlike `caTangentInterpRHS`'s row 0/1 which sit on the
unflipped `C` side. -/
def caTangentTargetInterpRHS (Ra1Y Ra2Y PY vDerivAtP : k) : Fin 4 → k :=
  ![Ra1Y, Ra2Y, -PY, -vDerivAtP]

/-- **Nondegeneracy: invertible iff `Ra1X, Ra2X, PX` are pairwise
distinct.** Same confluent-Vandermonde fact as
`caTangentInterpMatrix_det_ne_zero`, with the doubled node relabeled
and moved to rows 2-3. Closed form: `det = (Ra1X - PX) * (Ra2X - PX) *
(Ra2X - Ra1X) * ... ` — by the same row-permutation argument
`caTangentInterpMatrix`'s own docstring uses (this matrix is
`caTangentInterpMatrix` with its `RaX ↦ PX` (still doubled, now rows
2-3), `P1X ↦ Ra1X`, `P2X ↦ Ra2X` (rows 0-1), i.e. the doubled node
moved from the TOP of the matrix to the BOTTOM). Net closed form
guessed as `(Ra1X - PX)^2 * (Ra2X - PX)^2 * (Ra2X - Ra1X)` — same
shape as `caTangentInterpMatrix_det_ne_zero`'s own with `P1X,P2X ↦
Ra1X,Ra2X` and `RaX ↦ PX` — **REPL/sympy-check this independently
before trusting it**, per `CAWitnessTangent.lean`'s own precedent. -/
theorem caTangentTargetInterpMatrix_det_ne_zero (Ra1X Ra2X PX : k)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X) :
    (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0 := by
  have hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det =
      (Ra1X - PX) ^ 2 * (Ra2X - PX) ^ 2 * (Ra2X - Ra1X) := by
    unfold caTangentTargetInterpMatrix
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring
  rw [hdet]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr h1))
    (pow_ne_zero 2 (sub_ne_zero.mpr h2))) (sub_ne_zero.mpr (Ne.symm h12))

/-- **`bCA`'s target-tangent-case coefficients, via Cramer's rule.**
Same `det⁻¹ * cramer` idiom as `caTangentCoeff`. -/
noncomputable def caTangentTargetCoeff (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (i : Fin 4) : k :=
  (caTangentTargetInterpMatrix Ra1X Ra2X PX).det⁻¹ *
    (Matrix.cramer (caTangentTargetInterpMatrix Ra1X Ra2X PX)
      (caTangentTargetInterpRHS Ra1Y Ra2Y PY vDerivAtP) i)

/-- **`bCA`'s target-tangent-case witness polynomial.** `∑_{i<4} C
(caTangentTargetCoeff i) * X^i`, degree ≤ 3, same four-term shape as
`bCA`/`bCATangent`. -/
noncomputable def bCATangentTarget (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k) :
    Polynomial k :=
  Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 0) +
  Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 1) * X +
  Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 2) * X ^ 2 +
  Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 3) * X ^ 3

theorem bCATangentTarget_natDegree_le (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k) :
    (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).natDegree ≤ 3 := by
  unfold bCATangentTarget
  compute_degree

/-- **Row identity, shared core.** Same `Matrix.mulVec_cramer` argument
as `bCATangent_row_eq`. -/
private theorem bCATangentTarget_row_eq (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, caTangentTargetInterpMatrix Ra1X Ra2X PX r j *
      caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP j =
      caTangentTargetInterpRHS Ra1Y Ra2Y PY vDerivAtP r := by
  have hexpand : ∑ j : Fin 4, caTangentTargetInterpMatrix Ra1X Ra2X PX r j *
      caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP j =
      (caTangentTargetInterpMatrix Ra1X Ra2X PX).det⁻¹ *
        (caTangentTargetInterpMatrix Ra1X Ra2X PX r ⬝ᵥ
          (Matrix.cramer (caTangentTargetInterpMatrix Ra1X Ra2X PX)
            (caTangentTargetInterpRHS Ra1Y Ra2Y PY vDerivAtP))) := by
    unfold caTangentTargetCoeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (caTangentTargetInterpMatrix Ra1X Ra2X PX)
    (caTangentTargetInterpRHS Ra1Y Ra2Y PY vDerivAtP)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

private theorem bCATangentTarget_eval_eq_row (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP x : k) :
    (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval x =
      ∑ j : Fin 4, ![1, x, x ^ 2, x ^ 3] j *
        caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP j := by
  unfold bCATangentTarget
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem bCATangentTarget_eval_Ra1 (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0) :
    (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval Ra1X = Ra1Y := by
  rw [bCATangentTarget_eval_eq_row]
  have hrow := bCATangentTarget_row_eq Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet 0
  unfold caTangentTargetInterpMatrix caTangentTargetInterpRHS at hrow
  simpa using hrow

theorem bCATangentTarget_eval_Ra2 (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0) :
    (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval Ra2X = Ra2Y := by
  rw [bCATangentTarget_eval_eq_row]
  have hrow := bCATangentTarget_row_eq Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet 1
  unfold caTangentTargetInterpMatrix caTangentTargetInterpRHS at hrow
  simpa using hrow

/-- **`bCA` at `PX` equals `-PY`** — the `ι`-substitution, same
convention as `bCA_eval_P1`/`bCATangent_eval_P1`: the doubled target
node sits on the flipped side. -/
theorem bCATangentTarget_eval_P (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0) :
    (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX = -PY := by
  rw [bCATangentTarget_eval_eq_row]
  have hrow := bCATangentTarget_row_eq Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet 2
  unfold caTangentTargetInterpMatrix caTangentTargetInterpRHS at hrow
  simpa using hrow

private theorem bCATangentTarget_deriv_eval_eq_row (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP x : k) :
    (derivative (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)).eval x =
      caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 1 +
      2 * x * caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 2 +
      3 * x ^ 2 * caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 3 := by
  unfold bCATangentTarget
  simp only [derivative_add, derivative_C_mul, derivative_X, derivative_X_pow, derivative_C,
    zero_add, eval_add, eval_mul, eval_C, eval_X, eval_one, eval_pow, eval_ofNat,
    Nat.cast_ofNat]
  ring

/-- **Derivative of `bCA` at `PX` equals `-vDerivAtP`** — the confluent
row's identity: the `ι`-flip applies to the derivative row too, since
both rows 2 and 3 sit on the target ("`A`") side. -/
theorem bCATangentTarget_deriv_eval_P (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0) :
    (derivative (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)).eval PX =
      -vDerivAtP := by
  rw [bCATangentTarget_deriv_eval_eq_row]
  have hrow := bCATangentTarget_row_eq Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet 3
  have hmat : caTangentTargetInterpMatrix Ra1X Ra2X PX 3 = ![(0 : k), 1, 2 * PX, 3 * PX ^ 2] := by
    unfold caTangentTargetInterpMatrix
    ext j; fin_cases j <;> rfl
  rw [hmat] at hrow
  unfold caTangentTargetInterpRHS at hrow
  rw [Fin.sum_univ_four] at hrow
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, zero_mul, one_mul, zero_add] at hrow
  linear_combination hrow

/-- **`(X-Ra1.X) ∣ H.f - bCATangentTarget²`.** Same shape as
`dvd_pairNormBCA_Ra1`. -/
theorem dvd_pairNormBCATangentTarget_Ra1 (H : HyperellipticPolynomial k)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) :
    (X - C Ra1X) ∣ (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_sub, eval_pow,
    bCATangentTarget_eval_Ra1 Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet, hRa1_curve, sub_self]

theorem dvd_pairNormBCATangentTarget_Ra2 (H : HyperellipticPolynomial k)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) :
    (X - C Ra2X) ∣ (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, eval_sub, eval_pow,
    bCATangentTarget_eval_Ra2 Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet, hRa2_curve, sub_self]

/-- **`(X-PX)² ∣ H.f - bCATangentTarget²`** — the squared-root
divisibility at the doubled target node, via
`sq_dvd_of_eval_derivative_eq_zero'` (`TangentMumfordWitness.lean`,
reused as-is). Mirrors `dvd_sq_pairNormBCATangent_Ra` exactly, with
the `ι`-flip on both the value (`PY`) and derivative (`vDerivAtP`)
rows consistently threaded through. -/
theorem dvd_sq_pairNormBCATangentTarget_P (H : HyperellipticPolynomial k)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0) :
    (X - C PX) ^ 2 ∣ (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) := by
  have h0 : (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2).eval PX = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow,
      bCATangentTarget_eval_P Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet, neg_sq, hP_curve]
    ring
  have h1 : (derivative
      (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2)).eval PX = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sq, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      bCATangentTarget_eval_P Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet,
      bCATangentTarget_deriv_eval_P Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet]
    linear_combination -hPDeriv
  exact sq_dvd_of_eval_derivative_eq_zero' hne h0 h1

/-- **The full residual divisibility: `(X-Ra1X)(X-Ra2X)(X-PX)² ∣ H.f -
bCATangentTarget²`.** Combines the three factors via pairwise
coprimality (`Ra1X, Ra2X, PX` pairwise distinct — the same three
distinctness facts `caTangentTargetInterpMatrix_det_ne_zero` already
needs). -/
theorem dvd_pairNormBCATangentTarget_full (H : HyperellipticPolynomial k)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0) :
    (X - C Ra1X) * (X - C Ra2X) * (X - C PX) ^ 2 ∣
      (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) := by
  have hd1 := dvd_pairNormBCATangentTarget_Ra1 H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet
    hRa1_curve
  have hd2 := dvd_pairNormBCATangentTarget_Ra2 H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet
    hRa2_curve
  have hd3 := dvd_sq_pairNormBCATangentTarget_P H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet
    hP_curve hPDeriv hne
  have hc12 : IsCoprime (X - C Ra1X : k[X]) (X - C Ra2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h12)
  have hc1P : IsCoprime (X - C Ra1X : k[X]) ((X - C PX) ^ 2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1)).pow_right
  have hc2P : IsCoprime (X - C Ra2X : k[X]) ((X - C PX) ^ 2) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2)).pow_right
  have hd12 : (X - C Ra1X) * (X - C Ra2X) ∣
      (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) :=
    hc12.mul_dvd hd1 hd2
  have hc12P : IsCoprime ((X - C Ra1X : k[X]) * (X - C Ra2X)) ((X - C PX) ^ 2) :=
    hc1P.mul_left hc2P
  exact hc12P.mul_dvd hd12 hd3

/-! ## `uCANewTangentTarget`, the derived residual quadratic
(target-tangent case) -/

/-- **`denomPolyCATangentTarget`, the degree-4 divisor
`(X-Ra1X)(X-Ra2X)(X-PX)²`.** -/
noncomputable def denomPolyCATangentTarget (Ra1X Ra2X PX : k) : Polynomial k :=
  (X - C Ra1X) * (X - C Ra2X) * (X - C PX) ^ 2

theorem denomPolyCATangentTarget_monic (Ra1X Ra2X PX : k) :
    (denomPolyCATangentTarget Ra1X Ra2X PX).Monic := by
  unfold denomPolyCATangentTarget
  exact ((Polynomial.monic_X_sub_C Ra1X).mul (Polynomial.monic_X_sub_C Ra2X)).mul
    ((Polynomial.monic_X_sub_C PX).pow 2)

theorem denomPolyCATangentTarget_natDegree (Ra1X Ra2X PX : k) :
    (denomPolyCATangentTarget Ra1X Ra2X PX).natDegree = 4 := by
  unfold denomPolyCATangentTarget
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero Ra1X) (Polynomial.X_sub_C_ne_zero Ra2X))
      (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero PX)),
    Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero Ra1X) (Polynomial.X_sub_C_ne_zero Ra2X),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

/-- **`uCANewTangentTarget` — the quadratic shared by both `T` and
`ι(T)` in the target-tangent case.** The exact quotient `(H.f -
bCATangentTarget²) /ₘ denomPolyCATangentTarget`, mirroring `uCANew`'s
role exactly (see `CAWitness.lean`'s module docstring for the `T`/
`ι(T)` sign convention, which carries over unchanged — only the
underlying interpolant `b` changed). -/
noncomputable def uCANewTangentTarget (H : HyperellipticPolynomial k)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k) : Polynomial k :=
  (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) /ₘ
    denomPolyCATangentTarget Ra1X Ra2X PX

theorem pairNormBCATangentTarget_eq_denomPolyCATangentTarget_mul_uCANewTangentTarget
    (H : HyperellipticPolynomial k)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0) :
    H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 =
      denomPolyCATangentTarget Ra1X Ra2X PX *
        uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP := by
  have hdvd := dvd_pairNormBCATangentTarget_full H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet
    h1 h2 h12 hRa1_curve hRa2_curve hP_curve hPDeriv hne
  have hmod : (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) %ₘ
      denomPolyCATangentTarget Ra1X Ra2X PX = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyCATangentTarget_monic Ra1X Ra2X PX)).mpr
      (by
        change (X - C Ra1X) * (X - C Ra2X) * (X - C PX) ^ 2 ∣
          (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2)
    (q := denomPolyCATangentTarget Ra1X Ra2X PX)
  rw [hmod, zero_add] at hadd
  unfold uCANewTangentTarget
  exact hadd.symm

/-- **`bCATangentTarget`'s pole order at infinity: `-6`.**
Target-tangent-case sibling of `bCA_ordInfOfPair`/`bCATangent_
ordInfOfPair`, same weakened shape (needs `caTangentTargetCoeff ... 3
≠ 0`). -/
theorem bCATangentTarget_ordInfOfPair (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hlead : caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 3 ≠ 0) :
    ordInfOfPair (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X]) = -6 := by
  have hdeg3 : (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).natDegree = 3 := by
    apply le_antisymm (bCATangentTarget_natDegree_le Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
    unfold bCATangentTarget
    have hcoeff3 : (Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 0) +
      Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 1) * X +
      Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 2) * X ^ 2 +
      Polynomial.C (caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 3) *
        X ^ 3).coeff 3 =
        caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg : (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  rw [hAdeg, natDegree_one]
  norm_num

end DecoupledSystem
end Genus2Lean
