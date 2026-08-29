import Mathlib
import Genus2Lean.ZeroD.CAWitnessCrossTangent3
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessStep3
import Genus2Lean.ZeroD.PrincipalWitnessStep4
import Genus2Lean.LPairFinrankOneOrdAtFrac
import Genus2Lean.PrincipalDivisorSubgroup

/-!
# Cross-pair variant 1 (`Ra1 = ι(sa.P1)`) assembly: the divisor identity
# and `principalSubgroup` membership

Direct mirror of `CAWitnessCrossTangent2Assembly.lean`/
`CAWitnessCrossTangent4Assembly.lean`, ported onto
`CAWitnessCrossTangent2.lean` + `CAWitnessCrossTangent3.lean`'s objects
(`caCrossInterpMatrix`/`bCACross`/`uCANewCross`, no numeric suffix —
this is the FIRST cross-pair variant discovered, so its raw-machinery
files predate the `V2`/`V3`/`V4` single-file convention and are split
across two files instead of one). Per
`ROADMAP-cawitness-tangent-interpolation.md`'s Part B, case 3: closes
the Assembly-tier gap for THIS variant, the last of the four symmetric
variants to reach this stage.

**Naming convention, matching `CAWitnessCrossTangent2.lean`/`3.lean`**:
`RaX` (doubled node, `= Ra1X = sa.P1.X`), `Ra2X` (ordinary anchor row
1, survives as an ordinary anchor point), `P2X` (ordinary target row
3, survives as `ιP2`; the doubled node's derivative data is
`vDerivAtP1`, matching this variant's own row-2 confluent slot — note
the doubled node here is NON-ADJACENT to the ordinary points in the
original row layout, rows 0/2, unlike variants 2/3/4's adjacent-row
doublings, per `CAWitnessCrossTangent2.lean`'s own docstring). Support
set: three points pre-residual (`Ra (mult 2), Ra2, ιP2`), degree
`2+1+1 = 4`, matching `denomPolyCACross`'s degree-4 denominator; the
residual then adds `T1, T2` for a five-point total support, same shape
as variants 2/3/4.

**RHS sign at `Ra`'s row**: per `CAWitnessCrossTangent2.lean`'s module
docstring, row 0 (`Ra`'s slot) is UNFLIPPED (`RaY`), since `Ra1` is an
anchor point regardless of which target point its `x`-coordinate
collides with — so `PtRa.Y = RaY` (not `-RaY`), matching an ordinary
anchor point's `C`-side convention.

**Derivative-hypothesis sign convention, DIFFERENT from variants 2/3/4**:
per `CAWitnessCrossTangent3.lean`'s own docstring (`dvd_sq_pairNormBCACross_Ra`),
`hP1Deriv` here is `2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX`
(already flipped, matching what `bCACross_deriv_eval_Ra` actually
proves — the flip happened at the row-value level, since this is the
non-adjacent case where the doubled node absorbed `P1`'s FLIPPED slot,
not an ordinary anchor slot). Checked directly against
`bCACross_deriv_eval_Ra`'s conclusion (`= -vDerivAtP1`), not assumed to
match variants 2/3/4's shape verbatim, per that file's own caution. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`bCACross`'s pole order at infinity: `-6`.** Same weakened shape
as `bCA_ordInfOfPair`/`bCACross2_ordInfOfPair`: needs
`caCrossCoeff ... 3 ≠ 0`. -/
theorem bCACross_ordInfOfPair (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hlead : caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 3 ≠ 0) :
    ordInfOfPair (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = -6 := by
  have hdeg3 : (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).natDegree = 3 := by
    apply le_antisymm (bCACross_natDegree_le RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y)
    unfold bCACross
    have hcoeff3 : (Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 0) +
      Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 1) * X +
      Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 2) * X ^ 2 +
      Polynomial.C (caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 3) *
        X ^ 3).coeff 3 =
        caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg : (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  rw [hAdeg, natDegree_one]
  norm_num

/-- **Local Layer-3-cross, doubled-node side: `ordAt Q denomPolyCACross
0 = 2` at `Ra`.** `denomPolyCACross = (X-C RaX)^2 * (X-C Ra2X) * (X-C
P2X)`; at `Q` with `Q.X = RaX`: the squared factor contributes `2`, the
other two linear factors each contribute `0`. -/
theorem ordAt_denomCACross_eq_two_at_Ra
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P2X : k) (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = RaX) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross RaX Ra2X P2X) (0 : k[X]) = 2 := by
  have heq : denomPolyCACross RaX Ra2X P2X =
      ((linX RaX) ^ 2 * linX Ra2X) * linX P2X := by
    unfold denomPolyCACross linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hR_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 2 := by
    have := ordAt_linX_pow_unramified (H := H) hchar RaX Q h_bot hQX hQY 2
    simpa using this
  have hR : ordAt Q (linX Ra2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra2X Q h_bot (hQX ▸ h1)
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P2X Q h_bot (hQX ▸ h2)
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hR_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) = 2 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX Ra2X)
      ((linX RaX) ^ 2) (linX Ra2X) rfl hL_ne hR_ne, hL, hR]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX Ra2X) * linX P2X)
    ((linX RaX) ^ 2 * linX Ra2X) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-cross, `Ra2` side: `ordAt Q denomPolyCACross 0 = 1`
at `Ra2`.** -/
theorem ordAt_denomCACross_eq_one_at_Ra2
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P2X : k) (h1 : RaX ≠ Ra2X) (h3 : Ra2X ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = Ra2X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross RaX Ra2X P2X) (0 : k[X]) = 1 := by
  have heq : denomPolyCACross RaX Ra2X P2X =
      ((linX RaX) ^ 2 * linX Ra2X) * linX P2X := by
    unfold denomPolyCACross linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hR_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX RaX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf RaX Q h_bot (hQX ▸ (Ne.symm h1))
    have h0ne : toPair H (linX RaX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero RaX) hA
    have : ((linX RaX : k[X]) ^ 2) = linX RaX * linX RaX := by ring
    rw [this, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX RaX * linX RaX)
      (linX RaX) (linX RaX) rfl h0ne h0ne, h0]
    norm_num
  have hR : ordAt Q (linX Ra2X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf Ra2X Q h_bot hQX hQY
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P2X Q h_bot (hQX ▸ h3)
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hR_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) = 1 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX Ra2X)
      ((linX RaX) ^ 2) (linX Ra2X) rfl hL_ne hR_ne, hL, hR]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX Ra2X) * linX P2X)
    ((linX RaX) ^ 2 * linX Ra2X) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-cross, `P2` side: `ordAt Q denomPolyCACross 0 = 1`
at `P2`.** -/
theorem ordAt_denomCACross_eq_one_at_P2
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P2X : k) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = P2X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross RaX Ra2X P2X) (0 : k[X]) = 1 := by
  have heq : denomPolyCACross RaX Ra2X P2X =
      ((linX RaX) ^ 2 * linX Ra2X) * linX P2X := by
    unfold denomPolyCACross linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hR_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX RaX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf RaX Q h_bot (hQX ▸ (Ne.symm h2))
    have h0ne : toPair H (linX RaX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero RaX) hA
    have : ((linX RaX : k[X]) ^ 2) = linX RaX * linX RaX := by ring
    rw [this, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX RaX * linX RaX)
      (linX RaX) (linX RaX) rfl h0ne h0ne, h0]
    norm_num
  have hR : ordAt Q (linX Ra2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra2X Q h_bot (hQX ▸ (Ne.symm h3))
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf P2X Q h_bot hQX hQY
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hR_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) = 0 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX Ra2X)
      ((linX RaX) ^ 2) (linX Ra2X) rfl hL_ne hR_ne, hL, hR]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX Ra2X) * linX P2X)
    ((linX RaX) ^ 2 * linX Ra2X) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **`f`'s divisor restricted to the three named points, cross case:
`2•[Ra] + [Ra2] + [ιP2]`.** `f := toPair H (-bCACross) 1`. `Ra` is the
doubled node (`Ra1 = ι(sa.P1)`, `Ra.Y = RaY` unflipped per
`CAWitnessCrossTangent2.lean`'s module docstring); `Ra2` is the
ordinary surviving anchor point; `PtιP2` is `sa.P2`'s hyperelliptic
conjugate, flipped as usual. Mirrors
`divToPair_eq_C_add_iotaA_of_split_cross2` exactly. -/
theorem divToPair_eq_C_add_iotaA_of_split_cross1
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtRa2 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval Ra2X ≠ 0)
    (hU_evalP2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P2X ≠ 0) :
    divToPair (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])
        ({PtRa, PtRa2, PtιP2} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtRa2 + single PtιP2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have hg_ne : toPair H (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hAU : pairNorm H (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) =
      denomPolyCACross RaX Ra2X P2X *
        (-uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) := by
    unfold pairNorm
    have hfact := pairNormBCACross_eq_denomPolyCACross_mul_uCANewCross H
      RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet h1 h2 h3
      hRa_curve hRa2_curve hP2_curve hP1Deriv hne
    have : (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) := by ring
    rw [neg_sq, this, hfact]
    ring
  have hdenom_ne : denomPolyCACross RaX Ra2X P2X ≠ 0 := by
    unfold denomPolyCACross
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (X_sub_C_ne_zero RaX)) (X_sub_C_ne_zero Ra2X))
      (X_sub_C_ne_zero P2X)
  have hA_ne : toPair H (denomPolyCACross RaX Ra2X P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hdenom_ne hA
  have hU_ne : toPair H (-uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hA, -⟩
    have : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval RaX = 0 := by
      rw [neg_eq_zero] at hA; rw [hA]; simp
    exact hU_evalRa this
  -- Doubled node `Ra`, `ordAt = 2`. Unflipped RHS: anchor-point sign.
  have hOrdRa : ordAt PtRa (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 2 := by
    apply ordAt_eq_two_of_old_point PtRa (h_bot PtRa) _ _
      (denomPolyCACross RaX Ra2X P2X) (-uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtRa.X +
          (-(1 : k[X])).eval PtRa.X * PtRa.Y ≠ 0
      simp only [hPtRaX, hPtRaY, eval_neg, eval_one]
      rw [bCACross_eval_Ra RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet]
      intro hcontra
      apply hRaY_ne
      have h2R : (2 : k) * RaY = 0 := by
        have : -RaY + (-1 : k) * RaY = -(2 * RaY) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross_eq_two_at_Ra hchar hsf RaX Ra2X P2X h1 h2
        PtRa (h_bot PtRa) hPtRaX (hPtRaY ▸ hRaY_ne)
    · simp only [hPtRaX, eval_neg]
      simpa using hU_evalRa
  -- Ordinary anchor point `Ra2`, `ordAt = 1`.
  have hOrdRa2 : ordAt PtRa2 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtRa2 (h_bot PtRa2) _ _
      (denomPolyCACross RaX Ra2X P2X) (-uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtRa2.X +
          (-(1 : k[X])).eval PtRa2.X * PtRa2.Y ≠ 0
      simp only [hPtRa2X, hPtRa2Y, eval_neg, eval_one]
      rw [bCACross_eval_Ra2 RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet]
      intro hcontra
      apply hRa2Y_ne
      have h2R : (2 : k) * Ra2Y = 0 := by
        have : -Ra2Y + (-1 : k) * Ra2Y = -(2 * Ra2Y) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross_eq_one_at_Ra2 hchar hsf RaX Ra2X P2X h1 h3
        PtRa2 (h_bot PtRa2) hPtRa2X (hPtRa2Y ▸ hRa2Y_ne)
    · simp only [hPtRa2X, eval_neg]
      simpa using hU_evalRa2
  -- Ordinary target-conjugate point `ιP2`, `ordAt = 1`, flipped RHS.
  have hOrdιP2 : ordAt PtιP2 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP2 (h_bot PtιP2) _ _
      (denomPolyCACross RaX Ra2X P2X) (-uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtιP2.X +
          (-(1 : k[X])).eval PtιP2.X * PtιP2.Y ≠ 0
      simp only [hPtιP2X, hPtιP2Y, eval_neg, eval_one]
      rw [bCACross_eval_P2 RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet]
      intro hcontra
      apply hP2Y_ne
      have h2R : (2 : k) * P2Y = 0 := by
        have : -(-P2Y) + (-1 : k) * (-P2Y) = 2 * P2Y := by ring
        rw [this] at hcontra
        exact hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross_eq_one_at_P2 hchar hsf RaX Ra2X P2X h2 h3
        PtιP2 (h_bot PtιP2) hPtιP2X (by rw [hPtιP2Y]; exact neg_ne_zero.mpr hP2Y_ne)
    · simp only [hPtιP2X, eval_neg]
      simpa using hU_evalP2
  -- Pairwise distinctness of the three named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hRaRa2' : PtRa ≠ PtRa2 := hne_of_X (hPtRaX ▸ hPtRa2X ▸ h1)
  have hRaιP2' : PtRa ≠ PtιP2 := hne_of_X (hPtRaX ▸ hPtιP2X ▸ h2)
  have hRa2ιP2' : PtRa2 ≠ PtιP2 := hne_of_X (hPtRa2X ▸ hPtιP2X ▸ h3)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    simpa [hOrdRa, hRaRa2', hRaιP2']
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hRa2Ra' : PtRa2 ≠ PtRa := hRaRa2'.symm
    simpa [hOrdRa2, hRa2Ra', hRa2ιP2']
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hιP2Ra' : PtιP2 ≠ PtRa := hRaιP2'.symm
    have hιP2Ra2' : PtιP2 ≠ PtRa2 := hRa2ιP2'.symm
    simpa [hOrdιP2, hιP2Ra', hιP2Ra2']
  · have hnmemS : P ∉ ({PtRa, PtRa2, PtιP2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa, hEqRa2, hEqιP2⟩
    simp only [if_neg hnmemS, if_neg hEqRa, if_neg hEqRa2, if_neg hEqιP2]
    ring

/-- **`f`'s `ordAt` at a root of the cross residual factor `uCANewCross`,
expressed via `uCANewCross`'s own `rootMultiplicity` — no pre-split, no
distinct-root hypothesis.** Sibling of
`ordAt_eq_rootMultiplicity_of_uCANewCross2_root`, same proof shape
verbatim with the cross objects substituted throughout. -/
theorem ordAt_eq_rootMultiplicity_of_uCANewCross_root
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (hU_ne0 : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y ≠ 0)
    (hAeval : (denomPolyCACross RaX Ra2X P2X : k[X]).eval P.X ≠ 0)
    (hPY : P.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P.X)
    (hPY_ne : P.Y ≠ 0)
    (m : ℕ)
    (hUmult : Polynomial.rootMultiplicity P.X
      (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) = m) :
    ordAt P (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k[X]) (1 : k[X]) = (m : ℤ) := by
  have hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0 := by
    intro hcontra
    apply hU_ne0
    show uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y = 0
    unfold uCANewCross
    rw [hcontra, Polynomial.zero_divByMonic]
  set E := -bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y with hE_def
  set U := uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y with hU_def
  set A := denomPolyCACross RaX Ra2X P2X with hA_def
  have hAUraw : pairNorm H E (1 : k[X]) = A * (-U) := by
    unfold pairNorm
    have hfact := pairNormBCACross_eq_denomPolyCACross_mul_uCANewCross H
      RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet h1 h2 h3
      hRa_curve hRa2_curve hP2_curve hP1Deriv hne
    have hring : (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2) := by ring
    rw [hE_def, neg_sq, hring, hfact]
    ring
  have hg_ne : toPair H E (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hA_ne0 : A ≠ 0 := by
    rw [hA_def]
    unfold denomPolyCACross
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (X_sub_C_ne_zero RaX)) (X_sub_C_ne_zero Ra2X))
      (X_sub_C_ne_zero P2X)
  have hA_ne : toPair H A (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hA_ne0 hA0
  have hUneg_ne0 : (-U : k[X]) ≠ 0 := neg_ne_zero.mpr hU_ne0
  have hU_ne : toPair H (-U) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hUneg_ne0 hA0
  have hgbar_ne_eval : E.eval P.X + (-(1 : k[X])).eval P.X * P.Y ≠ 0 := by
    rw [hE_def]
    simp only [eval_neg, eval_one]
    rw [hPY]
    intro hcontra
    have h2 : (2 : k) * (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P.X = 0 := by
      linear_combination -hcontra
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hchar
    · apply hPY_ne
      rw [hPY, h]
  have hN_eq_mult : ordAt P E (1 : k[X]) = ordAt P (pairNorm H E (1 : k[X])) (0 : k[X]) :=
    ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E (1 : k[X]) hg_ne hgbar_ne_eval
  have hA_ord : ordAt P A (0 : k[X]) = 0 := by
    have hAmult : Polynomial.rootMultiplicity P.X A = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by
        rw [Polynomial.IsRoot]; exact hAeval)
    have := ordAt_eq_rootMultiplicity_unramified (H := H) hchar A hA_ne0 P.X P h_bot rfl hPY_ne
    rw [this, hAmult]
    norm_num
  have hU_ord : ordAt P (-U) (0 : k[X]) = (m : ℤ) := by
    have hUneg_eq : (-U : k[X]) = Polynomial.C (-1 : k) * U := by
      rw [map_neg, map_one, neg_mul, one_mul]
    have hCU_ne : (Polynomial.C (-1 : k) * U : k[X]) ≠ 0 := hUneg_eq ▸ hUneg_ne0
    have hUneg_mult :
        Polynomial.rootMultiplicity P.X (-U : k[X]) = Polynomial.rootMultiplicity P.X U := by
      rw [hUneg_eq, Polynomial.rootMultiplicity_mul hCU_ne, Polynomial.rootMultiplicity_C]
      norm_num
    have := ordAt_eq_rootMultiplicity_unramified (H := H) hchar (-U) hUneg_ne0 P.X P h_bot rfl
      hPY_ne
    rw [this, hUneg_mult, hUmult]
  rw [hN_eq_mult, hAUraw,
    ordAt_add_of_pairNorm_eq_mul P h_bot (A * (-U)) A (-U) rfl hA_ne hU_ne, hA_ord, hU_ord]
  norm_num

/-- **`f`'s divisor restricted to the five named points, cross case:
`2•[Ra] + [Ra2] + [ιP2] + [T1] + [T2]`.** Widens
`divToPair_eq_C_add_iotaA_of_split_cross1`'s three-point conclusion by
the two residual points, exactly as
`divToPair_eq_C_add_iotaA_add_T_of_split_cross2` widens its own
three-point precursor. -/
theorem divToPair_eq_C_add_iotaA_add_T_of_split_cross1
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtRa2 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval Ra2X ≠ 0)
    (hU_evalP2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hAeval1 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X) :
    divToPair (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])
        ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtRa2 + single PtιP2 + single PtT1 + single PtT2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have h3pt : divToPair (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])
      ({PtRa, PtRa2, PtιP2} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtRa2 + single PtιP2 :=
    divToPair_eq_C_add_iotaA_of_split_cross1 hchar hsf RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y
      hdet h1 h2 h3 hRa_curve hRa2_curve hP2_curve hP1Deriv hRaY_ne hRa2Y_ne hP2Y_ne
      PtRa PtRa2 PtιP2 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP2X hPtιP2Y hne
      hU_evalRa hU_evalRa2 hU_evalP2
  have hne_of_X : ∀ {Q1' Q2' : H.Point}, Q1'.X ≠ Q2'.X → Q1' ≠ Q2' :=
    fun hX heq => hX (heq ▸ rfl)
  have hRaRa2' : PtRa ≠ PtRa2 := hne_of_X (hPtRaX ▸ hPtRa2X ▸ h1)
  have hRaιP2' : PtRa ≠ PtιP2 := hne_of_X (hPtRaX ▸ hPtιP2X ▸ h2)
  have hRa2ιP2' : PtRa2 ≠ PtιP2 := hne_of_X (hPtRa2X ▸ hPtιP2X ▸ h3)
  have hRaT1' : PtRa ≠ PtT1 := hne_of_X (hPtRaX ▸ hPtT1X ▸ hRaT1)
  have hRaT2' : PtRa ≠ PtT2 := hne_of_X (hPtRaX ▸ hPtT2X ▸ hRaT2)
  have hRa2T1' : PtRa2 ≠ PtT1 := hne_of_X (hPtRa2X ▸ hPtT1X ▸ hRa2T1)
  have hRa2T2' : PtRa2 ≠ PtT2 := hne_of_X (hPtRa2X ▸ hPtT2X ▸ hRa2T2)
  have hιP2T1' : PtιP2 ≠ PtT1 := hne_of_X (hPtιP2X ▸ hPtT1X ▸ hP2T1)
  have hιP2T2' : PtιP2 ≠ PtT2 := hne_of_X (hPtιP2X ▸ hPtT2X ▸ hP2T2)
  have hT1T2' : PtT1 ≠ PtT2 := hne_of_X (hPtT1X ▸ hPtT2X ▸ hTne)
  -- Extract the three original pointwise `ordAt` facts from `h3pt`.
  have hOrdRa : ordAt PtRa (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 2 := by
    have hL := congrArg (coeffAt PtRa) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa ∈ ({PtRa, PtRa2, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg hRaRa2', if_neg hRaιP2']
    ring
  have hOrdRa2 : ordAt PtRa2 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtRa2) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa2 ∈ ({PtRa, PtRa2, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRaRa2'), if_neg hRa2ιP2']
    ring
  have hOrdιP2 : ordAt PtιP2 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtιP2) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtιP2 ∈ ({PtRa, PtRa2, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRaιP2'), if_neg (Ne.symm hRa2ιP2')]
    ring
  -- The two new residual-point `ordAt = 1` facts.
  have hmult1 : Polynomial.rootMultiplicity T1X
      (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T1X T2X hT1 hT2 hTne Q1 hQ1_def hQ1T1
  have hmult2 : Polynomial.rootMultiplicity T2X
      (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T2X T1X hT2 hT1 (Ne.symm hTne) Q2 hQ2_def hQ2T2
  have hOrdT1 : ordAt PtT1 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewCross_root hchar hsf
      RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet h1 h2 h3
      hRa_curve hRa2_curve hP2_curve hP1Deriv PtT1 (h_bot PtT1) hU_ne0
      hAeval1 hPtT1Y hPtT1Y_ne 1 (hPtT1X ▸ hmult1)
    simpa using this
  have hOrdT2 : ordAt PtT2 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewCross_root hchar hsf
      RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hdet h1 h2 h3
      hRa_curve hRa2_curve hP2_curve hP1Deriv PtT2 (h_bot PtT2) hU_ne0
      hAeval2 hPtT2Y hPtT2Y_ne 1 (hPtT2X ▸ hmult2)
    simpa using this
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    have hMem : PtRa ∈ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa, if_pos rfl, if_neg hRaRa2', if_neg hRaιP2',
      if_neg hRaT1', if_neg hRaT2']
    ring
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hMem : PtRa2 ∈ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa2, if_neg (Ne.symm hRaRa2'), if_pos rfl, if_neg hRa2ιP2',
      if_neg hRa2T1', if_neg hRa2T2']
    ring
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hMem : PtιP2 ∈ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdιP2, if_neg (Ne.symm hRaιP2'), if_neg (Ne.symm hRa2ιP2'), if_pos rfl,
      if_neg hιP2T1', if_neg hιP2T2']
    ring
  by_cases hEqT1 : P = PtT1
  · rw [hEqT1]
    have hMem : PtT1 ∈ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT1, if_neg (Ne.symm hRaT1'), if_neg (Ne.symm hRa2T1'),
      if_neg (Ne.symm hιP2T1'), if_pos rfl, if_neg hT1T2']
    ring
  by_cases hEqT2 : P = PtT2
  · rw [hEqT2]
    have hMem : PtT2 ∈ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT2, if_neg (Ne.symm hRaT2'), if_neg (Ne.symm hRa2T2'),
      if_neg (Ne.symm hιP2T2'), if_neg (Ne.symm hT1T2'), if_pos rfl]
    ring
  · have hnmemS : P ∉ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa, hEqRa2, hEqιP2, hEqT1, hEqT2⟩
    rw [if_neg hnmemS, if_neg hEqRa, if_neg hEqRa2, if_neg hEqιP2, if_neg hEqT1, if_neg hEqT2]
    ring

/-- **`G₁`, cross case (variant 1): `2•[Ra] + [Ra2] + [ιP2] + [T1] +
[T2] - [T1]-[T2]-[ιT1]-[ιT2]-[δ₀]-[ιδ₀] ∈ principalSubgroup`.** Cross
sibling of `cIotaAmIotaT_mem_principalSubgroup_cross2`, on the
five-point `f`-support `{PtRa,PtRa2,PtιP2,PtT1,PtT2}`. Same
`divToPairRatio`/`AddSubgroup.subset_closure` assembly as its
predecessors, `bCACross_ordInfOfPair` supplying the `-6` pole order. -/
theorem cIotaAmIotaT_mem_principalSubgroup_cross1
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y : k)
    (hdet : (caCrossInterpMatrix RaX Ra2X P2X).det ≠ 0)
    (hlead : caCrossCoeff RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y 3 ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P2X) (h3 : Ra2X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtRa2 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval Ra2X ≠ 0)
    (hU_evalP2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval P2X ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (hU_ne0 : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y ≠ 0)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross H RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross RaX Ra2X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)] :
    (divToPair (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])
        ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) -
      divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])
          ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point) -
        divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y) (1 : k[X])
          ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point)
        ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCACross RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y, 1,
    ({PtRa, PtRa2, PtιP2, PtT1, PtT2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX T1X * linX T2X) * linX δ₀.X, 0,
    ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hT, hspec_hT, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero T1X) (linX_ne_zero T2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCACross_ordInfOfPair RaX Ra2X P2X RaY Ra2Y vDerivAtP1 P2Y hlead, ordInfOfPair_hT]

end DecoupledSystem
end Genus2Lean
