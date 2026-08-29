import Mathlib
import Genus2Lean.ZeroD.CAWitnessCrossTangentV3
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessStep3
import Genus2Lean.ZeroD.PrincipalWitnessStep4
import Genus2Lean.LPairFinrankOneOrdAtFrac
import Genus2Lean.PrincipalDivisorSubgroup

/-!
# Cross-pair variant 3 (`Ra2 = ι(sa.P1)`) assembly: the divisor identity
# and `principalSubgroup` membership

Per `ROADMAP-cawitness-tangent-interpolation.md`'s Part B, case 3 /
Suggested-order item 5: `CAWitnessCrossTangentV3.lean` supplies the raw
`bCACross3`/`uCANewCross3` polynomial machinery for the `Ra2X = P1X`
collision (`Ra2 = ι(sa.P1)` as points), but — per that doc's own
"wiring chain traced this pass" note — nothing downstream of it
exists yet: `divToPair_eq_C_add_iotaA_add_T_of_split` and
`cIotaAmIotaT_mem_principalSubgroup` (`PrincipalWitnessStep3.lean`/
`PrincipalWitnessStep4.lean`) have no cross-pair sibling, the same gap
Tier 1's `_tangent` work closed for the anchor/target axes. This file
closes that gap for THIS ONE variant, following
`CAWitnessDivisorTangent.lean` + `CAWitnessAssemblyTangent.lean` +
`PrincipalWitnessStep4Tangent.lean`'s three-file pattern collapsed into
one (variant files are already following the "one file, not three"
convention per `CAWitnessCrossTangentV2.lean`'s precedent).

**Naming convention, matching `CAWitnessCrossTangentV3.lean`**:
`Ra1X` (ordinary anchor row 0), `RaX` (doubled node, `= Ra2X = sa.P1.X`),
`P2X` (ordinary target row 3, survives as `ιP2`). The support set for
`f := y - bCACross3(x)` is FOUR points before the residual
(`PtRa1, PtRa (mult 2), PtιP2`) — one fewer than the tangent-anchor
case's three, since `Ra2`/`ιP1` collapse into `Ra` here — wait: three
points total pre-residual (`Ra1, Ra, ιP2`), degree `1+2+1 = 4`, matching
`bCACross3_natDegree_le`'s degree-3 numerator against a degree-4
denominator (`denomPolyCACross3`) exactly the way `denomPolyCATangent`'s
degree 4 matched the split case's degree-4 four-point denominator minus
one collapsed pair. Then the residual adds two more named points
`T1, T2`, for a five-point total support — same shape as the anchor/
target tangent cases.

**RHS sign at `Ra`'s row**: per `CAWitnessCrossTangentV3.lean`'s module
docstring, row 1 (`Ra`'s slot) is UNFLIPPED (`RaY`), since `Ra2` is an
anchor point regardless of which target point its `x`-coordinate
collides with — so `PtRa.Y = RaY` (not `-RaY`), matching an ordinary
anchor point's `C`-side convention, not the `ι(A)`-side flip `PtιP1`
would have gotten in the split case. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`bCACross3`'s pole order at infinity: `-6`.** Same weakened shape
as `bCA_ordInfOfPair`/`bCATangent_ordInfOfPair`: needs
`caCross3Coeff ... 3 ≠ 0`. -/
theorem bCACross3_ordInfOfPair (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hlead : caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 3 ≠ 0) :
    ordInfOfPair (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = -6 := by
  have hdeg3 : (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).natDegree = 3 := by
    apply le_antisymm (bCACross3_natDegree_le Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y)
    unfold bCACross3
    have hcoeff3 : (Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 0) +
      Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 1) * X +
      Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 2) * X ^ 2 +
      Polynomial.C (caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 3) *
        X ^ 3).coeff 3 =
        caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg : (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  rw [hAdeg, natDegree_one]
  norm_num

/-- **Local Layer-3-cross3, `Ra1` side: `ordAt Q denomPolyCACross3 0 =
1` at `Ra1`.** `denomPolyCACross3 = (X-C Ra1X) * (X-C RaX)^2 * (X-C
P2X)`; at `Q` with `Q.X = Ra1X`: the linear factor contributes `1`, the
squared factor and the other linear factor each contribute `0`. -/
theorem ordAt_denomCACross3_eq_one_at_Ra1
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X RaX P2X : k) (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = Ra1X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross3 Ra1X RaX P2X) (0 : k[X]) = 1 := by
  have heq : denomPolyCACross3 Ra1X RaX P2X =
      (linX Ra1X * (linX RaX) ^ 2) * linX P2X := by
    unfold denomPolyCACross3 linX; ring
  rw [heq]
  have hR_ne : toPair H (linX Ra1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra1X) hA
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hR : ordAt Q (linX Ra1X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf Ra1X Q h_bot hQX hQY
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX RaX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf RaX Q h_bot (hQX ▸ h1)
    have h0ne : toPair H (linX RaX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero RaX) hA
    have : ((linX RaX : k[X]) ^ 2) = linX RaX * linX RaX := by ring
    rw [this, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX RaX * linX RaX)
      (linX RaX) (linX RaX) rfl h0ne h0ne, h0]
    norm_num
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P2X Q h_bot (hQX ▸ h2)
  have h1_ne : toPair H (linX Ra1X * (linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hR_ne hL_ne
  have hstep1 : ordAt Q (linX Ra1X * (linX RaX) ^ 2) (0 : k[X]) = 1 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX Ra1X * (linX RaX) ^ 2)
      (linX Ra1X) ((linX RaX) ^ 2) rfl hR_ne hL_ne, hR, hL]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX Ra1X * (linX RaX) ^ 2) * linX P2X)
    (linX Ra1X * (linX RaX) ^ 2) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-cross3, doubled-node side: `ordAt Q denomPolyCACross3
0 = 2` at `Ra` (`= Ra2X = P1X`).** -/
theorem ordAt_denomCACross3_eq_two_at_Ra
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X RaX P2X : k) (h1 : Ra1X ≠ RaX) (h3 : RaX ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = RaX) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross3 Ra1X RaX P2X) (0 : k[X]) = 2 := by
  have heq : denomPolyCACross3 Ra1X RaX P2X =
      (linX Ra1X * (linX RaX) ^ 2) * linX P2X := by
    unfold denomPolyCACross3 linX; ring
  rw [heq]
  have hR_ne : toPair H (linX Ra1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra1X) hA
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hR : ordAt Q (linX Ra1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra1X Q h_bot (hQX ▸ (Ne.symm h1))
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 2 := by
    have := ordAt_linX_pow_unramified (H := H) hchar RaX Q h_bot hQX hQY 2
    simpa using this
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P2X Q h_bot (hQX ▸ h3)
  have h1_ne : toPair H (linX Ra1X * (linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hR_ne hL_ne
  have hstep1 : ordAt Q (linX Ra1X * (linX RaX) ^ 2) (0 : k[X]) = 2 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX Ra1X * (linX RaX) ^ 2)
      (linX Ra1X) ((linX RaX) ^ 2) rfl hR_ne hL_ne, hR, hL]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX Ra1X * (linX RaX) ^ 2) * linX P2X)
    (linX Ra1X * (linX RaX) ^ 2) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-cross3, `P2` side: `ordAt Q denomPolyCACross3 0 = 1`
at `P2`.** -/
theorem ordAt_denomCACross3_eq_one_at_P2
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X RaX P2X : k) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = P2X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross3 Ra1X RaX P2X) (0 : k[X]) = 1 := by
  have heq : denomPolyCACross3 Ra1X RaX P2X =
      ((linX Ra1X * (linX RaX) ^ 2)) * linX P2X := by
    unfold denomPolyCACross3 linX; ring
  rw [heq]
  have hR_ne : toPair H (linX Ra1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra1X) hA
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hR : ordAt Q (linX Ra1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra1X Q h_bot (hQX ▸ (Ne.symm h2))
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX RaX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf RaX Q h_bot (hQX ▸ (Ne.symm h3))
    have h0ne : toPair H (linX RaX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero RaX) hA
    have : ((linX RaX : k[X]) ^ 2) = linX RaX * linX RaX := by ring
    rw [this, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX RaX * linX RaX)
      (linX RaX) (linX RaX) rfl h0ne h0ne, h0]
    norm_num
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf P2X Q h_bot hQX hQY
  have h1_ne : toPair H (linX Ra1X * (linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hR_ne hL_ne
  have hstep1 : ordAt Q (linX Ra1X * (linX RaX) ^ 2) (0 : k[X]) = 0 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX Ra1X * (linX RaX) ^ 2)
      (linX Ra1X) ((linX RaX) ^ 2) rfl hR_ne hL_ne, hR, hL]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX Ra1X * (linX RaX) ^ 2) * linX P2X)
    (linX Ra1X * (linX RaX) ^ 2) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **`f`'s divisor restricted to the three named points, cross3 case:
`[Ra1] + 2•[Ra] + [ιP2]`.** `f := toPair H (-bCACross3) 1`. `Ra1` is the
ordinary surviving anchor point; `Ra` is the doubled node
(`Ra2 = ι(sa.P1)`, `Ra.Y = RaY` unflipped per `CAWitnessCrossTangentV3.
lean`'s module docstring — `Ra` is read here as an anchor point, not as
`ι(sa.P1)`, matching `bCACross3_eval_Ra`'s own unflipped RHS); `PtιP2`
is `sa.P2`'s hyperelliptic conjugate, flipped as usual. Mirrors
`divToPair_eq_C_add_iotaA_of_split_tangent` exactly, with the doubled
node's `hOrdRa` proof step (`ordAt = 2`) using `bCACross3_eval_Ra`'s
UNFLIPPED sign convention (`-RaY - RaY ≠ 0`, same non-Weierstrass
argument as an ordinary anchor point uses) rather than the `ιP1`-style
flipped-sign argument the split case's `Ra1`/`Ra2` never needed either
(they're always anchor points, never targets). -/
theorem divToPair_eq_C_add_iotaA_of_split_cross3
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRaY_ne : RaY ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval Ra1X ≠ 0)
    (hU_evalRa : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalP2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P2X ≠ 0) :
    divToPair (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])
        ({PtRa1, PtRa, PtιP2} : Finset H.Point) =
      single PtRa1 + (2 : ℤ) • single PtRa + single PtιP2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have hg_ne : toPair H (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hAU : pairNorm H (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) =
      denomPolyCACross3 Ra1X RaX P2X *
        (-uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) := by
    unfold pairNorm
    have hfact := pairNormBCACross3_eq_denomPolyCACross3_mul_uCANewCross3 H
      Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet h1 h2 h3
      hRa1_curve hRa_curve hP2_curve hP1Deriv hne
    have : (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) := by ring
    rw [neg_sq, this, hfact]
    ring
  have hdenom_ne : denomPolyCACross3 Ra1X RaX P2X ≠ 0 := by
    unfold denomPolyCACross3
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero Ra1X) (pow_ne_zero 2 (X_sub_C_ne_zero RaX)))
      (X_sub_C_ne_zero P2X)
  have hA_ne : toPair H (denomPolyCACross3 Ra1X RaX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hdenom_ne hA
  have hU_ne : toPair H (-uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hA, -⟩
    have : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval Ra1X = 0 := by
      rw [neg_eq_zero] at hA; rw [hA]; simp
    exact hU_evalRa1 this
  -- Ordinary anchor point `Ra1`, `ordAt = 1`.
  have hOrdRa1 : ordAt PtRa1 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtRa1 (h_bot PtRa1) _ _
      (denomPolyCACross3 Ra1X RaX P2X) (-uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtRa1.X +
          (-(1 : k[X])).eval PtRa1.X * PtRa1.Y ≠ 0
      simp only [hPtRa1X, hPtRa1Y, eval_neg, eval_one]
      rw [bCACross3_eval_Ra1 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet]
      intro hcontra
      apply hRa1Y_ne
      have h2R : (2 : k) * Ra1Y = 0 := by
        have : -Ra1Y + (-1 : k) * Ra1Y = -(2 * Ra1Y) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross3_eq_one_at_Ra1 hchar hsf Ra1X RaX P2X h1 h2
        PtRa1 (h_bot PtRa1) hPtRa1X (hPtRa1Y ▸ hRa1Y_ne)
    · simp only [hPtRa1X, eval_neg]
      simpa using hU_evalRa1
  -- Doubled node `Ra`, `ordAt = 2`. Unflipped RHS: anchor-point sign.
  have hOrdRa : ordAt PtRa (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 2 := by
    apply ordAt_eq_two_of_old_point PtRa (h_bot PtRa) _ _
      (denomPolyCACross3 Ra1X RaX P2X) (-uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtRa.X +
          (-(1 : k[X])).eval PtRa.X * PtRa.Y ≠ 0
      simp only [hPtRaX, hPtRaY, eval_neg, eval_one]
      rw [bCACross3_eval_Ra Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet]
      intro hcontra
      apply hRaY_ne
      have h2R : (2 : k) * RaY = 0 := by
        have : -RaY + (-1 : k) * RaY = -(2 * RaY) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross3_eq_two_at_Ra hchar hsf Ra1X RaX P2X h1 h3
        PtRa (h_bot PtRa) hPtRaX (hPtRaY ▸ hRaY_ne)
    · simp only [hPtRaX, eval_neg]
      simpa using hU_evalRa
  -- Ordinary target-conjugate point `ιP2`, `ordAt = 1`, flipped RHS.
  have hOrdιP2 : ordAt PtιP2 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP2 (h_bot PtιP2) _ _
      (denomPolyCACross3 Ra1X RaX P2X) (-uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtιP2.X +
          (-(1 : k[X])).eval PtιP2.X * PtιP2.Y ≠ 0
      simp only [hPtιP2X, hPtιP2Y, eval_neg, eval_one]
      rw [bCACross3_eval_P2 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet]
      intro hcontra
      apply hP2Y_ne
      have h2R : (2 : k) * P2Y = 0 := by
        have : -(-P2Y) + (-1 : k) * (-P2Y) = 2 * P2Y := by ring
        rw [this] at hcontra
        exact hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross3_eq_one_at_P2 hchar hsf Ra1X RaX P2X h2 h3
        PtιP2 (h_bot PtιP2) hPtιP2X (by rw [hPtιP2Y]; exact neg_ne_zero.mpr hP2Y_ne)
    · simp only [hPtιP2X, eval_neg]
      simpa using hU_evalP2
  -- Pairwise distinctness of the three named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hRa1Ra' : PtRa1 ≠ PtRa := hne_of_X (hPtRa1X ▸ hPtRaX ▸ h1)
  have hRa1ιP2' : PtRa1 ≠ PtιP2 := hne_of_X (hPtRa1X ▸ hPtιP2X ▸ h2)
  have hRaιP2' : PtRa ≠ PtιP2 := hne_of_X (hPtRaX ▸ hPtιP2X ▸ h3)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa1 : P = PtRa1
  · rw [hEqRa1]
    simpa [hOrdRa1, hRa1Ra', hRa1ιP2']
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    have hRaRa1' : PtRa ≠ PtRa1 := hRa1Ra'.symm
    simpa [hOrdRa, hRaRa1', hRaιP2']
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hιP2Ra1' : PtιP2 ≠ PtRa1 := hRa1ιP2'.symm
    have hιP2Ra' : PtιP2 ≠ PtRa := hRaιP2'.symm
    simpa [hOrdιP2, hιP2Ra1', hιP2Ra']
  · have hnmemS : P ∉ ({PtRa1, PtRa, PtιP2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa1, hEqRa, hEqιP2⟩
    simp only [if_neg hnmemS, if_neg hEqRa1, if_neg hEqRa, if_neg hEqιP2]
    ring

/-- **`f`'s `ordAt` at a root of the cross3 residual factor
`uCANewCross3`, expressed via `uCANewCross3`'s own `rootMultiplicity` —
no pre-split, no distinct-root hypothesis.** Sibling of
`ordAt_eq_rootMultiplicity_of_uCANewTangent_root`
(`CAWitnessResidualTangent.lean`), same proof shape verbatim with the
cross3 objects substituted throughout. -/
theorem ordAt_eq_rootMultiplicity_of_uCANewCross3_root
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (hU_ne0 : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y ≠ 0)
    (hAeval : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval P.X ≠ 0)
    (hPY : P.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P.X)
    (hPY_ne : P.Y ≠ 0)
    (m : ℕ)
    (hUmult : Polynomial.rootMultiplicity P.X
      (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) = m) :
    ordAt P (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k[X]) (1 : k[X]) = (m : ℤ) := by
  have hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0 := by
    intro hcontra
    apply hU_ne0
    show uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y = 0
    unfold uCANewCross3
    rw [hcontra, Polynomial.zero_divByMonic]
  set E := -bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y with hE_def
  set U := uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y with hU_def
  set A := denomPolyCACross3 Ra1X RaX P2X with hA_def
  have hAUraw : pairNorm H E (1 : k[X]) = A * (-U) := by
    unfold pairNorm
    have hfact := pairNormBCACross3_eq_denomPolyCACross3_mul_uCANewCross3 H
      Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet h1 h2 h3
      hRa1_curve hRa_curve hP2_curve hP1Deriv hne
    have hring : (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2) := by ring
    rw [hE_def, neg_sq, hring, hfact]
    ring
  have hg_ne : toPair H E (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hA_ne0 : A ≠ 0 := by
    rw [hA_def]
    unfold denomPolyCACross3
    exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero Ra1X) (pow_ne_zero 2 (X_sub_C_ne_zero RaX)))
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
    have h2 : (2 : k) * (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P.X = 0 := by
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

/-- **`f`'s divisor restricted to the five named points, cross3 case:
`[Ra1] + 2•[Ra] + [ιP2] + [T1] + [T2]`.** Widens
`divToPair_eq_C_add_iotaA_of_split_cross3`'s three-point conclusion by
the two residual points, exactly as
`divToPair_eq_C_add_iotaA_add_T_of_split_tangent` widens its own
three-point precursor — same corrected-support-set discipline that
file's docstring flags (the three-point support alone is NOT `f`'s full
zero set; `T1X, T2X` are genuine additional roots of `uCANewCross3`). -/
theorem divToPair_eq_C_add_iotaA_add_T_of_split_cross3
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRaY_ne : RaY ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval Ra1X ≠ 0)
    (hU_evalRa : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalP2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hAeval1 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X) :
    divToPair (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])
        ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) =
      single PtRa1 + (2 : ℤ) • single PtRa + single PtιP2 + single PtT1 + single PtT2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have h3pt : divToPair (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])
      ({PtRa1, PtRa, PtιP2} : Finset H.Point) =
      single PtRa1 + (2 : ℤ) • single PtRa + single PtιP2 :=
    divToPair_eq_C_add_iotaA_of_split_cross3 hchar hsf Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y
      hdet h1 h2 h3 hRa1_curve hRa_curve hP2_curve hP1Deriv hRa1Y_ne hRaY_ne hP2Y_ne
      PtRa1 PtRa PtιP2 hPtRa1X hPtRa1Y hPtRaX hPtRaY hPtιP2X hPtιP2Y hne
      hU_evalRa1 hU_evalRa hU_evalP2
  have hne_of_X : ∀ {Q1' Q2' : H.Point}, Q1'.X ≠ Q2'.X → Q1' ≠ Q2' :=
    fun hX heq => hX (heq ▸ rfl)
  have hRa1Ra' : PtRa1 ≠ PtRa := hne_of_X (hPtRa1X ▸ hPtRaX ▸ h1)
  have hRa1ιP2' : PtRa1 ≠ PtιP2 := hne_of_X (hPtRa1X ▸ hPtιP2X ▸ h2)
  have hRaιP2' : PtRa ≠ PtιP2 := hne_of_X (hPtRaX ▸ hPtιP2X ▸ h3)
  have hRa1T1' : PtRa1 ≠ PtT1 := hne_of_X (hPtRa1X ▸ hPtT1X ▸ hRa1T1)
  have hRa1T2' : PtRa1 ≠ PtT2 := hne_of_X (hPtRa1X ▸ hPtT2X ▸ hRa1T2)
  have hRaT1' : PtRa ≠ PtT1 := hne_of_X (hPtRaX ▸ hPtT1X ▸ hRaT1)
  have hRaT2' : PtRa ≠ PtT2 := hne_of_X (hPtRaX ▸ hPtT2X ▸ hRaT2)
  have hιP2T1' : PtιP2 ≠ PtT1 := hne_of_X (hPtιP2X ▸ hPtT1X ▸ hP2T1)
  have hιP2T2' : PtιP2 ≠ PtT2 := hne_of_X (hPtιP2X ▸ hPtT2X ▸ hP2T2)
  have hT1T2' : PtT1 ≠ PtT2 := hne_of_X (hPtT1X ▸ hPtT2X ▸ hTne)
  -- Extract the three original pointwise `ordAt` facts from `h3pt`.
  have hOrdRa1 : ordAt PtRa1 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtRa1) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa1 ∈ ({PtRa1, PtRa, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg hRa1Ra', if_neg hRa1ιP2']
    ring
  have hOrdRa : ordAt PtRa (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 2 := by
    have hL := congrArg (coeffAt PtRa) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa ∈ ({PtRa1, PtRa, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRa1Ra'), if_neg hRaιP2']
    ring
  have hOrdιP2 : ordAt PtιP2 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtιP2) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtιP2 ∈ ({PtRa1, PtRa, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRa1ιP2'), if_neg (Ne.symm hRaιP2')]
    ring
  -- The two new residual-point `ordAt = 1` facts.
  have hmult1 : Polynomial.rootMultiplicity T1X
      (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T1X T2X hT1 hT2 hTne Q1 hQ1_def hQ1T1
  have hmult2 : Polynomial.rootMultiplicity T2X
      (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T2X T1X hT2 hT1 (Ne.symm hTne) Q2 hQ2_def hQ2T2
  have hOrdT1 : ordAt PtT1 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewCross3_root hchar hsf
      Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet h1 h2 h3
      hRa1_curve hRa_curve hP2_curve hP1Deriv PtT1 (h_bot PtT1) hU_ne0
      hAeval1 hPtT1Y hPtT1Y_ne 1 (hPtT1X ▸ hmult1)
    simpa using this
  have hOrdT2 : ordAt PtT2 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewCross3_root hchar hsf
      Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hdet h1 h2 h3
      hRa1_curve hRa_curve hP2_curve hP1Deriv PtT2 (h_bot PtT2) hU_ne0
      hAeval2 hPtT2Y hPtT2Y_ne 1 (hPtT2X ▸ hmult2)
    simpa using this
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa1 : P = PtRa1
  · rw [hEqRa1]
    have hMem : PtRa1 ∈ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa1, if_pos rfl, if_neg hRa1Ra', if_neg hRa1ιP2',
      if_neg hRa1T1', if_neg hRa1T2']
    ring
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    have hMem : PtRa ∈ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa, if_neg (Ne.symm hRa1Ra'), if_pos rfl, if_neg hRaιP2',
      if_neg hRaT1', if_neg hRaT2']
    ring
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hMem : PtιP2 ∈ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdιP2, if_neg (Ne.symm hRa1ιP2'), if_neg (Ne.symm hRaιP2'), if_pos rfl,
      if_neg hιP2T1', if_neg hιP2T2']
    ring
  by_cases hEqT1 : P = PtT1
  · rw [hEqT1]
    have hMem : PtT1 ∈ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT1, if_neg (Ne.symm hRa1T1'), if_neg (Ne.symm hRaT1'),
      if_neg (Ne.symm hιP2T1'), if_pos rfl, if_neg hT1T2']
    ring
  by_cases hEqT2 : P = PtT2
  · rw [hEqT2]
    have hMem : PtT2 ∈ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT2, if_neg (Ne.symm hRa1T2'), if_neg (Ne.symm hRaT2'),
      if_neg (Ne.symm hιP2T2'), if_neg (Ne.symm hT1T2'), if_pos rfl]
    ring
  · have hnmemS : P ∉ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa1, hEqRa, hEqιP2, hEqT1, hEqT2⟩
    rw [if_neg hnmemS, if_neg hEqRa1, if_neg hEqRa, if_neg hEqιP2, if_neg hEqT1, if_neg hEqT2]
    ring

/-- **`G₁`, cross3 case: `[Ra1] + 2•[Ra] + [ιP2] + [T1] + [T2] -
[T1]-[T2]-[ιT1]-[ιT2]-[δ₀]-[ιδ₀] ∈ principalSubgroup`.** Cross3 sibling
of `cIotaAmIotaT_mem_principalSubgroup`/`cIotaAmIotaT_mem_
principalSubgroup_tangent`, on the five-point `f`-support
`{PtRa1,PtRa,PtιP2,PtT1,PtT2}`. Same `divToPairRatio`/
`AddSubgroup.subset_closure` assembly as both predecessors,
`bCACross3_ordInfOfPair` supplying the `-6` pole order. -/
theorem cIotaAmIotaT_mem_principalSubgroup_cross3
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y : k)
    (hdet : (caCross3InterpMatrix Ra1X RaX P2X).det ≠ 0)
    (hlead : caCross3Coeff Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y 3 ≠ 0)
    (h1 : Ra1X ≠ RaX) (h2 : Ra1X ≠ P2X) (h3 : RaX ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hP1Deriv : 2 * RaY * (-vDerivAtP1) = (derivative H.f).eval RaX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRaY_ne : RaY ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval Ra1X ≠ 0)
    (hU_evalRa : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval RaX ≠ 0)
    (hU_evalP2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval P2X ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T1X)
    (hT2 : (uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (hU_ne0 : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y ≠ 0)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross3 H Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross3 Ra1X RaX P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])).toNat)]
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
    (divToPair (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])
        ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) -
      divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])
          ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point) -
        divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y) (1 : k[X])
          ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point)
        ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCACross3 Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y, 1,
    ({PtRa1, PtRa, PtιP2, PtT1, PtT2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX T1X * linX T2X) * linX δ₀.X, 0,
    ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hT, hspec_hT, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero T1X) (linX_ne_zero T2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCACross3_ordInfOfPair Ra1X RaX P2X Ra1Y RaY vDerivAtP1 P2Y hlead, ordInfOfPair_hT]

end DecoupledSystem
end Genus2Lean
