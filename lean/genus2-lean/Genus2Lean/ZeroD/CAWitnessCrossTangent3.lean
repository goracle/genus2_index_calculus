import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.TangentMumfordWitness
import Genus2Lean.ZeroD.CAWitnessCrossTangent2

/-! # `bCA`'s CROSS-pair tangent case, part 3: residual divisibility and
`uCANewCross`

Continues `CAWitnessCrossTangent2.lean` (matrix/coefficients/`bCACross`/
row evaluations) with the `dvd`/`uCANew`-shaped consumers, mirroring
`CAWitnessTangent.lean`'s `dvd_pairNormBCATangent_full`/`uCANewTangent`
exactly, adapted for case 3's row layout: the squared factor sits at
the doubled node `RaX` (same as case 1's `RaX`), with two ordinary
linear factors at `Ra2X, P2X` (case 1's ordinary factors were at
`P1X, P2X` — same shape, different names, since case 3's doubled node
absorbed `P1`'s slot rather than `Ra2`'s). -/

noncomputable section

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

theorem pairNormBCACross_eval_Ra2_eq_zero (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) :
    (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2).eval Ra2X = 0 := by
  rw [eval_sub, eval_pow, bCACross_eval_Ra2 RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet,
    hRa2_curve, sub_self]

theorem pairNormBCACross_eval_P2_eq_zero (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2).eval P2X = 0 := by
  rw [eval_sub, eval_pow, bCACross_eval_P2 RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet,
    neg_sq, hP2_curve, sub_self]

theorem dvd_pairNormBCACross_Ra2 (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) :
    (X - C Ra2X) ∣ (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross_eval_Ra2_eq_zero H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet hRa2_curve

theorem dvd_pairNormBCACross_P2 (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X) :
    (X - C P2X) ∣ (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  exact pairNormBCACross_eval_P2_eq_zero H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet hP2_curve

/-- **`(X - RaX)² ∣ H.f - bCACross²`.** The doubled-node squared factor,
via `sq_dvd_of_eval_derivative_eq_zero'`. Needs both value vanishing
(`bCACross_eval_Ra` + `hRa_curve`) and derivative vanishing at `RaX`
(`bCACross_deriv_eval_Ra` + `hP1Deriv`). **Sign convention note,
DIFFERENT from cases 1/2's `hRaDeriv`/`hPDeriv`**: those state the
derivative hypothesis in "natural unflipped" form
(`2*Y*deriv = f'.eval X`) and apply the flip only inside the RHS row.
Here `hP1Deriv` is stated ALREADY flipped
(`2*RaY*(-vDerivAtP1) = f'.eval RaX`) because `bCACross_deriv_eval_Ra`
itself proves the derivative equals `-vDerivAtP1` (not `vDerivAtP1`) —
the flip already happened at the row-value level, so restating it
unflipped here would require introducing a spurious extra sign
cancellation. Algebraically checked (not just pattern-matched against
the other two files) against what `bCACross_deriv_eval_Ra` actually
proves before writing this hypothesis shape. Caller substituting the
real Mumford data should double check which form their own derivation
naturally produces and adjust the sign once, at the call site, rather
than assuming this matches `hPDeriv`'s shape verbatim.

Note the CURVE fact `hRa_curve` uses `Ra`'s own `Y` — since `Ra1 =
ι(sa.P1)`, `Ra.Y = -sa.P1.Y`, so `RaY² = sa.P1.Y²` and both are valid
square roots of `H.f.eval RaX`; caller supplies whichever is
convenient, this file doesn't force a specific one. -/
theorem dvd_sq_pairNormBCACross_Ra (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 ∣ (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) := by
  have h0 : (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2).eval RaX = 0 := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow,
      bCACross_eval_Ra RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet, hRa_curve]
    ring
  have h1 : (derivative
      (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2)).eval RaX = 0 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_sq, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      bCACross_eval_Ra RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet,
      bCACross_deriv_eval_Ra RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet,
      ← hP1Deriv]
    ring
  exact sq_dvd_of_eval_derivative_eq_zero' hne h0 h1

/-- **The full residual divisibility: `(X-RaX)²(X-Ra2X)(X-P2X) ∣ H.f -
bCACross²`.** Combines the three factors via pairwise coprimality
(`RaX, Ra2X, P2X` pairwise distinct — the same three distinctness
facts `caCrossInterpMatrix_det_ne_zero` already needs). -/
theorem dvd_pairNormBCACross_full (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0) :
    (X - C RaX) ^ 2 * (X - C Ra2X) * (X - C P2X) ∣
      (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) := by
  have hd1 := dvd_sq_pairNormBCACross_Ra H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet
    hRa_curve hP1Deriv hne
  have hd2 := dvd_pairNormBCACross_Ra2 H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet hRa2_curve
  have hd3 := dvd_pairNormBCACross_P2 H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet hP2_curve
  have hc1Ra2 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C Ra2X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h1)).pow_left
  have hc1P2 : IsCoprime ((X - C RaX : k[X]) ^ 2) (X - C P2X) :=
    (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h2)).pow_left
  have hcRa2P2 : IsCoprime (X - C Ra2X : k[X]) (X - C P2X) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
      rw [isUnit_iff_ne_zero, sub_ne_zero]; exact h3)
  have hd12 : (X - C RaX) ^ 2 * (X - C Ra2X) ∣
      (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) :=
    hc1Ra2.mul_dvd hd1 hd2
  have hc12P2 : IsCoprime ((X - C RaX : k[X]) ^ 2 * (X - C Ra2X)) (X - C P2X) :=
    hc1P2.mul_left hcRa2P2
  exact hc12P2.mul_dvd hd12 hd3

/-! ## `uCANewCross`, the derived residual quadratic (cross-tangent case) -/

/-- **`denomPolyCACross`, the degree-4 divisor `(X-RaX)²(X-Ra2X)(X-P2X)`.** -/
noncomputable def denomPolyCACross (RaX Ra2X P2X : k) : Polynomial k :=
  (X - C RaX) ^ 2 * (X - C Ra2X) * (X - C P2X)

theorem denomPolyCACross_monic (RaX Ra2X P2X : k) :
    (denomPolyCACross RaX Ra2X P2X).Monic := by
  unfold denomPolyCACross
  exact (((Polynomial.monic_X_sub_C RaX).pow 2).mul (Polynomial.monic_X_sub_C Ra2X)).mul
    (Polynomial.monic_X_sub_C P2X)

theorem denomPolyCACross_natDegree (RaX Ra2X P2X : k) :
    (denomPolyCACross RaX Ra2X P2X).natDegree = 4 := by
  unfold denomPolyCACross
  rw [Polynomial.natDegree_mul
      (mul_ne_zero (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX))
        (Polynomial.X_sub_C_ne_zero Ra2X))
      (Polynomial.X_sub_C_ne_zero P2X),
    Polynomial.natDegree_mul (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero RaX))
      (Polynomial.X_sub_C_ne_zero Ra2X),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

/-- **`uCANewCross` — the quadratic shared by both `T` and `ι(T)` in the
cross-tangent case.** The exact quotient `(H.f - bCACross²) /ₘ
denomPolyCACross`, mirroring `uCANew`/`uCANewTangent`'s role exactly. -/
noncomputable def uCANewCross (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k) : Polynomial k :=
  (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) /ₘ
    denomPolyCACross RaX Ra2X P2X

theorem pairNormBCACross_eq_denomPolyCACross_mul_uCANewCross
    (H : HyperellipticPolynomial k)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0) :
    H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 =
      denomPolyCACross RaX Ra2X P2X *
        uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y := by
  have hdvd := dvd_pairNormBCACross_full H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet
    h1 h2 h3 hRa_curve hRa2_curve hP2_curve hP1Deriv hne
  have hmod : (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) %ₘ
      denomPolyCACross RaX Ra2X P2X = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (denomPolyCACross_monic RaX Ra2X P2X)).mpr
      (by
        change (X - C RaX) ^ 2 * (X - C Ra2X) * (X - C P2X) ∣
          (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2)
        exact hdvd)
  have hadd := Polynomial.modByMonic_add_div
    (H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2)
    (q := denomPolyCACross RaX Ra2X P2X)
  rw [hmod, zero_add] at hadd
  unfold uCANewCross
  exact hadd.symm

end DecoupledSystem
end Genus2Lean
