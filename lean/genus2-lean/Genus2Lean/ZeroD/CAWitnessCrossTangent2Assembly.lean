import Mathlib
import Genus2Lean.ZeroD.CAWitnessCrossTangentV2
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessStep3
import Genus2Lean.ZeroD.PrincipalWitnessStep4
import Genus2Lean.LPairFinrankOneOrdAtFrac
import Genus2Lean.PrincipalDivisorSubgroup

/-!
# Cross-pair variant 2 (`Ra1 = ι(sa.P2)`) assembly: the divisor identity
# and `principalSubgroup` membership

Direct mirror of `CAWitnessCrossTangent4Assembly.lean`, ported onto
`CAWitnessCrossTangentV2.lean`'s objects. Per
`ROADMAP-cawitness-tangent-interpolation.md`'s Part B, case 3: closes
the Assembly-tier gap for THIS variant (the 2nd of the four symmetric
variants to reach this stage; variants 3/4 were already done).

**Naming convention, matching `CAWitnessCrossTangentV2.lean`**:
`RaX` (doubled node, `= Ra1X = sa.P2.X`), `Ra2X` (ordinary anchor row
1, survives as an ordinary anchor point), `P1X` (ordinary target row
2, survives as `ιP1`; the doubled node's derivative data is
`vDerivAtP2`, matching V2's own row-3 confluent slot). Support set:
three points pre-residual (`Ra (mult 2), Ra2, ιP1`), degree
`2+1+1 = 4`, matching `denomPolyCACross2`'s degree-4 denominator; the
residual then adds `T1, T2` for a five-point total support, same shape
as V4.

**RHS sign at `Ra`'s row**: per `CAWitnessCrossTangentV2.lean`'s module
docstring, row 0 (`Ra`'s slot) is UNFLIPPED (`RaY`), since `Ra1` is an
anchor point regardless of which target point its `x`-coordinate
collides with — so `PtRa.Y = RaY` (not `-RaY`), matching an ordinary
anchor point's `C`-side convention, not the `ι(A)`-side flip `PtιP1`
would have gotten in the split case.

**Denominator factor order differs from variant 4's**: `denomPolyCACross2
RaX Ra2X P1X = (X-RaX)^2 * (X-Ra2X) * (X-P1X)` (squared factor FIRST,
since the doubled node is `Ra` = row 0 here), whereas variant 4's
`denomPolyCACross4` has the squared factor in the MIDDLE position. The
local `ordAt_denomCACross2_eq_*` helper proofs below are re-derived
directly against this factor order, not copied verbatim from variant
4's `ordAt_denomCACross4_eq_*` proofs. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`bCACross2`'s pole order at infinity: `-6`.** Same weakened shape
as `bCA_ordInfOfPair`/`bCACross4_ordInfOfPair`: needs
`caCross2Coeff ... 3 ≠ 0`. -/
theorem bCACross2_ordInfOfPair (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hlead : caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 3 ≠ 0) :
    ordInfOfPair (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = -6 := by
  have hdeg3 : (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).natDegree = 3 := by
    apply le_antisymm (bCACross2_natDegree_le RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2)
    unfold bCACross2
    have hcoeff3 : (Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 0) +
      Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 1) * X +
      Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 2) * X ^ 2 +
      Polynomial.C (caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 3) *
        X ^ 3).coeff 3 =
        caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg : (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  rw [hAdeg, natDegree_one]
  norm_num

/-- **Local Layer-3-cross2, doubled-node side: `ordAt Q denomPolyCACross2
0 = 2` at `Ra` (`= RaX = P1X`'s conjugate site).** `denomPolyCACross2 =
(X-C RaX)^2 * (X-C Ra2X) * (X-C P1X)`; at `Q` with `Q.X = RaX`: the
squared factor contributes `2`, the other two linear factors each
contribute `0`. -/
theorem ordAt_denomCACross2_eq_two_at_Ra
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P1X : k) (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = RaX) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross2 RaX Ra2X P1X) (0 : k[X]) = 2 := by
  have heq : denomPolyCACross2 RaX Ra2X P1X =
      ((linX RaX) ^ 2 * linX Ra2X) * linX P1X := by
    unfold denomPolyCACross2 linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hR_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hF2_ne : toPair H (linX P1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P1X) hA
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 2 := by
    have := ordAt_linX_pow_unramified (H := H) hchar RaX Q h_bot hQX hQY 2
    simpa using this
  have hR : ordAt Q (linX Ra2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra2X Q h_bot (hQX ▸ h1)
  have hF2 : ordAt Q (linX P1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P1X Q h_bot (hQX ▸ h2)
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hR_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) = 2 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX Ra2X)
      ((linX RaX) ^ 2) (linX Ra2X) rfl hL_ne hR_ne, hL, hR]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX Ra2X) * linX P1X)
    ((linX RaX) ^ 2 * linX Ra2X) (linX P1X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-cross2, `Ra2` side: `ordAt Q denomPolyCACross2 0 =
1` at `Ra2`.** -/
theorem ordAt_denomCACross2_eq_one_at_Ra2
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P1X : k) (h1 : RaX ≠ Ra2X) (h3 : Ra2X ≠ P1X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = Ra2X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross2 RaX Ra2X P1X) (0 : k[X]) = 1 := by
  have heq : denomPolyCACross2 RaX Ra2X P1X =
      ((linX RaX) ^ 2 * linX Ra2X) * linX P1X := by
    unfold denomPolyCACross2 linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hR_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hF2_ne : toPair H (linX P1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P1X) hA
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
  have hF2 : ordAt Q (linX P1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P1X Q h_bot (hQX ▸ h3)
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hR_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) = 1 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX Ra2X)
      ((linX RaX) ^ 2) (linX Ra2X) rfl hL_ne hR_ne, hL, hR]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX Ra2X) * linX P1X)
    ((linX RaX) ^ 2 * linX Ra2X) (linX P1X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-cross2, `P1` side: `ordAt Q denomPolyCACross2 0 = 1`
at `P1`.** -/
theorem ordAt_denomCACross2_eq_one_at_P1
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P1X : k) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = P1X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCACross2 RaX Ra2X P1X) (0 : k[X]) = 1 := by
  have heq : denomPolyCACross2 RaX Ra2X P1X =
      ((linX RaX) ^ 2 * linX Ra2X) * linX P1X := by
    unfold denomPolyCACross2 linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hR_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hF2_ne : toPair H (linX P1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P1X) hA
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
  have hF2 : ordAt Q (linX P1X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf P1X Q h_bot hQX hQY
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hR_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX Ra2X) (0 : k[X]) = 0 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX Ra2X)
      ((linX RaX) ^ 2) (linX Ra2X) rfl hL_ne hR_ne, hL, hR]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX Ra2X) * linX P1X)
    ((linX RaX) ^ 2 * linX Ra2X) (linX P1X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **`f`'s divisor restricted to the three named points, cross2 case:
`2•[Ra] + [Ra2] + [ιP1]`.** `f := toPair H (-bCACross2) 1`. `Ra` is the
doubled node (`Ra1 = ι(sa.P2)`, `Ra.Y = RaY` unflipped per
`CAWitnessCrossTangentV2.lean`'s module docstring — `Ra` is read here
as an anchor point, not as `ι(sa.P2)`, matching `bCACross2_eval_Ra`'s
own unflipped RHS); `Ra2` is the ordinary surviving anchor point;
`PtιP1` is `sa.P1`'s hyperelliptic conjugate, flipped as usual. Mirrors
`divToPair_eq_C_add_iotaA_of_split_cross4` exactly, with the doubled
node's `hOrdRa` proof step (`ordAt = 2`) using `bCACross2_eval_Ra`'s
UNFLIPPED sign convention (`-RaY - RaY ≠ 0`, same non-Weierstrass
argument as an ordinary anchor point uses). -/
theorem divToPair_eq_C_add_iotaA_of_split_cross2
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0)
    (PtRa PtRa2 PtιP1 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P1X ≠ 0) :
    divToPair (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])
        ({PtRa, PtRa2, PtιP1} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtRa2 + single PtιP1 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have hg_ne : toPair H (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hAU : pairNorm H (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) =
      denomPolyCACross2 RaX Ra2X P1X *
        (-uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) := by
    unfold pairNorm
    have hfact := pairNormBCACross2_eq_denomPolyCACross2_mul_uCANewCross2 H
      RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet h1 h2 h3
      hRa_curve hRa2_curve hP1_curve hP2Deriv hne
    have : (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) := by ring
    rw [neg_sq, this, hfact]
    ring
  have hdenom_ne : denomPolyCACross2 RaX Ra2X P1X ≠ 0 := by
    unfold denomPolyCACross2
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (X_sub_C_ne_zero RaX)) (X_sub_C_ne_zero Ra2X))
      (X_sub_C_ne_zero P1X)
  have hA_ne : toPair H (denomPolyCACross2 RaX Ra2X P1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hdenom_ne hA
  have hU_ne : toPair H (-uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hA, -⟩
    have : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval RaX = 0 := by
      rw [neg_eq_zero] at hA; rw [hA]; simp
    exact hU_evalRa this
  -- Doubled node `Ra`, `ordAt = 2`. Unflipped RHS: anchor-point sign.
  have hOrdRa : ordAt PtRa (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 2 := by
    apply ordAt_eq_two_of_old_point PtRa (h_bot PtRa) _ _
      (denomPolyCACross2 RaX Ra2X P1X) (-uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtRa.X +
          (-(1 : k[X])).eval PtRa.X * PtRa.Y ≠ 0
      simp only [hPtRaX, hPtRaY, eval_neg, eval_one]
      rw [bCACross2_eval_Ra RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet]
      intro hcontra
      apply hRaY_ne
      have h2R : (2 : k) * RaY = 0 := by
        have : -RaY + (-1 : k) * RaY = -(2 * RaY) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross2_eq_two_at_Ra hchar hsf RaX Ra2X P1X h1 h2
        PtRa (h_bot PtRa) hPtRaX (hPtRaY ▸ hRaY_ne)
    · simp only [hPtRaX, eval_neg]
      simpa using hU_evalRa
  -- Ordinary anchor point `Ra2`, `ordAt = 1`.
  have hOrdRa2 : ordAt PtRa2 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtRa2 (h_bot PtRa2) _ _
      (denomPolyCACross2 RaX Ra2X P1X) (-uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtRa2.X +
          (-(1 : k[X])).eval PtRa2.X * PtRa2.Y ≠ 0
      simp only [hPtRa2X, hPtRa2Y, eval_neg, eval_one]
      rw [bCACross2_eval_Ra2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet]
      intro hcontra
      apply hRa2Y_ne
      have h2R : (2 : k) * Ra2Y = 0 := by
        have : -Ra2Y + (-1 : k) * Ra2Y = -(2 * Ra2Y) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross2_eq_one_at_Ra2 hchar hsf RaX Ra2X P1X h1 h3
        PtRa2 (h_bot PtRa2) hPtRa2X (hPtRa2Y ▸ hRa2Y_ne)
    · simp only [hPtRa2X, eval_neg]
      simpa using hU_evalRa2
  -- Ordinary target-conjugate point `ιP1`, `ordAt = 1`, flipped RHS.
  have hOrdιP1 : ordAt PtιP1 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP1 (h_bot PtιP1) _ _
      (denomPolyCACross2 RaX Ra2X P1X) (-uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtιP1.X +
          (-(1 : k[X])).eval PtιP1.X * PtιP1.Y ≠ 0
      simp only [hPtιP1X, hPtιP1Y, eval_neg, eval_one]
      rw [bCACross2_eval_P1 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet]
      intro hcontra
      apply hP1Y_ne
      have h2R : (2 : k) * P1Y = 0 := by
        have : -(-P1Y) + (-1 : k) * (-P1Y) = 2 * P1Y := by ring
        rw [this] at hcontra
        exact hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · exact ordAt_denomCACross2_eq_one_at_P1 hchar hsf RaX Ra2X P1X h2 h3
        PtιP1 (h_bot PtιP1) hPtιP1X (by rw [hPtιP1Y]; exact neg_ne_zero.mpr hP1Y_ne)
    · simp only [hPtιP1X, eval_neg]
      simpa using hU_evalP1
  -- Pairwise distinctness of the three named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hRaRa2' : PtRa ≠ PtRa2 := hne_of_X (hPtRaX ▸ hPtRa2X ▸ h1)
  have hRaιP1' : PtRa ≠ PtιP1 := hne_of_X (hPtRaX ▸ hPtιP1X ▸ h2)
  have hRa2ιP1' : PtRa2 ≠ PtιP1 := hne_of_X (hPtRa2X ▸ hPtιP1X ▸ h3)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    simpa [hOrdRa, hRaRa2', hRaιP1']
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hRa2Ra' : PtRa2 ≠ PtRa := hRaRa2'.symm
    simpa [hOrdRa2, hRa2Ra', hRa2ιP1']
  by_cases hEqιP1 : P = PtιP1
  · rw [hEqιP1]
    have hιP1Ra' : PtιP1 ≠ PtRa := hRaιP1'.symm
    have hιP1Ra2' : PtιP1 ≠ PtRa2 := hRa2ιP1'.symm
    simpa [hOrdιP1, hιP1Ra', hιP1Ra2']
  · have hnmemS : P ∉ ({PtRa, PtRa2, PtιP1} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa, hEqRa2, hEqιP1⟩
    simp only [if_neg hnmemS, if_neg hEqRa, if_neg hEqRa2, if_neg hEqιP1]
    ring

/-- **`f`'s `ordAt` at a root of the cross2 residual factor
`uCANewCross2`, expressed via `uCANewCross2`'s own `rootMultiplicity` —
no pre-split, no distinct-root hypothesis.** Sibling of
`ordAt_eq_rootMultiplicity_of_uCANewCross4_root`, same proof shape
verbatim with the cross2 objects substituted throughout. -/
theorem ordAt_eq_rootMultiplicity_of_uCANewCross2_root
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (hU_ne0 : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 ≠ 0)
    (hAeval : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval P.X ≠ 0)
    (hPY : P.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P.X)
    (hPY_ne : P.Y ≠ 0)
    (m : ℕ)
    (hUmult : Polynomial.rootMultiplicity P.X
      (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) = m) :
    ordAt P (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k[X]) (1 : k[X]) = (m : ℤ) := by
  have hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0 := by
    intro hcontra
    apply hU_ne0
    show uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 = 0
    unfold uCANewCross2
    rw [hcontra, Polynomial.zero_divByMonic]
  set E := -bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 with hE_def
  set U := uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 with hU_def
  set A := denomPolyCACross2 RaX Ra2X P1X with hA_def
  have hAUraw : pairNorm H E (1 : k[X]) = A * (-U) := by
    unfold pairNorm
    have hfact := pairNormBCACross2_eq_denomPolyCACross2_mul_uCANewCross2 H
      RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet h1 h2 h3
      hRa_curve hRa2_curve hP1_curve hP2Deriv hne
    have hring : (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2) := by ring
    rw [hE_def, neg_sq, hring, hfact]
    ring
  have hg_ne : toPair H E (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hA_ne0 : A ≠ 0 := by
    rw [hA_def]
    unfold denomPolyCACross2
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (X_sub_C_ne_zero RaX)) (X_sub_C_ne_zero Ra2X))
      (X_sub_C_ne_zero P1X)
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
    have h2 : (2 : k) * (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P.X = 0 := by
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

/-- **`f`'s divisor restricted to the five named points, cross2 case:
`2•[Ra] + [Ra2] + [ιP1] + [T1] + [T2]`.** Widens
`divToPair_eq_C_add_iotaA_of_split_cross2`'s three-point conclusion by
the two residual points, exactly as
`divToPair_eq_C_add_iotaA_add_T_of_split_cross4` widens its own
three-point precursor. -/
theorem divToPair_eq_C_add_iotaA_add_T_of_split_cross2
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0)
    (PtRa PtRa2 PtιP1 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P1X ≠ 0)
    (hU_ne0 : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T1X)
    (hT2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hAeval1 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X) :
    divToPair (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])
        ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtRa2 + single PtιP1 + single PtT1 + single PtT2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have h3pt : divToPair (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])
      ({PtRa, PtRa2, PtιP1} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtRa2 + single PtιP1 :=
    divToPair_eq_C_add_iotaA_of_split_cross2 hchar hsf RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2
      hdet h1 h2 h3 hRa_curve hRa2_curve hP1_curve hP2Deriv hRaY_ne hRa2Y_ne hP1Y_ne
      PtRa PtRa2 PtιP1 hPtRaX hPtRaY hPtRa2X hPtRa2Y hPtιP1X hPtιP1Y hne
      hU_evalRa hU_evalRa2 hU_evalP1
  have hne_of_X : ∀ {Q1' Q2' : H.Point}, Q1'.X ≠ Q2'.X → Q1' ≠ Q2' :=
    fun hX heq => hX (heq ▸ rfl)
  have hRaRa2' : PtRa ≠ PtRa2 := hne_of_X (hPtRaX ▸ hPtRa2X ▸ h1)
  have hRaιP1' : PtRa ≠ PtιP1 := hne_of_X (hPtRaX ▸ hPtιP1X ▸ h2)
  have hRa2ιP1' : PtRa2 ≠ PtιP1 := hne_of_X (hPtRa2X ▸ hPtιP1X ▸ h3)
  have hRaT1' : PtRa ≠ PtT1 := hne_of_X (hPtRaX ▸ hPtT1X ▸ hRaT1)
  have hRaT2' : PtRa ≠ PtT2 := hne_of_X (hPtRaX ▸ hPtT2X ▸ hRaT2)
  have hRa2T1' : PtRa2 ≠ PtT1 := hne_of_X (hPtRa2X ▸ hPtT1X ▸ hRa2T1)
  have hRa2T2' : PtRa2 ≠ PtT2 := hne_of_X (hPtRa2X ▸ hPtT2X ▸ hRa2T2)
  have hιP1T1' : PtιP1 ≠ PtT1 := hne_of_X (hPtιP1X ▸ hPtT1X ▸ hP1T1)
  have hιP1T2' : PtιP1 ≠ PtT2 := hne_of_X (hPtιP1X ▸ hPtT2X ▸ hP1T2)
  have hT1T2' : PtT1 ≠ PtT2 := hne_of_X (hPtT1X ▸ hPtT2X ▸ hTne)
  -- Extract the three original pointwise `ordAt` facts from `h3pt`.
  have hOrdRa : ordAt PtRa (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 2 := by
    have hL := congrArg (coeffAt PtRa) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa ∈ ({PtRa, PtRa2, PtιP1} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg hRaRa2', if_neg hRaιP1']
    ring
  have hOrdRa2 : ordAt PtRa2 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtRa2) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa2 ∈ ({PtRa, PtRa2, PtιP1} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRaRa2'), if_neg hRa2ιP1']
    ring
  have hOrdιP1 : ordAt PtιP1 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtιP1) h3pt
    rw [coeffAt_divToPair] at hL
    have hMem : PtιP1 ∈ ({PtRa, PtRa2, PtιP1} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRaιP1'), if_neg (Ne.symm hRa2ιP1')]
    ring
  -- The two new residual-point `ordAt = 1` facts.
  have hmult1 : Polynomial.rootMultiplicity T1X
      (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T1X T2X hT1 hT2 hTne Q1 hQ1_def hQ1T1
  have hmult2 : Polynomial.rootMultiplicity T2X
      (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T2X T1X hT2 hT1 (Ne.symm hTne) Q2 hQ2_def hQ2T2
  have hOrdT1 : ordAt PtT1 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewCross2_root hchar hsf
      RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet h1 h2 h3
      hRa_curve hRa2_curve hP1_curve hP2Deriv PtT1 (h_bot PtT1) hU_ne0
      hAeval1 hPtT1Y hPtT1Y_ne 1 (hPtT1X ▸ hmult1)
    simpa using this
  have hOrdT2 : ordAt PtT2 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewCross2_root hchar hsf
      RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hdet h1 h2 h3
      hRa_curve hRa2_curve hP1_curve hP2Deriv PtT2 (h_bot PtT2) hU_ne0
      hAeval2 hPtT2Y hPtT2Y_ne 1 (hPtT2X ▸ hmult2)
    simpa using this
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    have hMem : PtRa ∈ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa, if_pos rfl, if_neg hRaRa2', if_neg hRaιP1',
      if_neg hRaT1', if_neg hRaT2']
    ring
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hMem : PtRa2 ∈ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa2, if_neg (Ne.symm hRaRa2'), if_pos rfl, if_neg hRa2ιP1',
      if_neg hRa2T1', if_neg hRa2T2']
    ring
  by_cases hEqιP1 : P = PtιP1
  · rw [hEqιP1]
    have hMem : PtιP1 ∈ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdιP1, if_neg (Ne.symm hRaιP1'), if_neg (Ne.symm hRa2ιP1'), if_pos rfl,
      if_neg hιP1T1', if_neg hιP1T2']
    ring
  by_cases hEqT1 : P = PtT1
  · rw [hEqT1]
    have hMem : PtT1 ∈ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT1, if_neg (Ne.symm hRaT1'), if_neg (Ne.symm hRa2T1'),
      if_neg (Ne.symm hιP1T1'), if_pos rfl, if_neg hT1T2']
    ring
  by_cases hEqT2 : P = PtT2
  · rw [hEqT2]
    have hMem : PtT2 ∈ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT2, if_neg (Ne.symm hRaT2'), if_neg (Ne.symm hRa2T2'),
      if_neg (Ne.symm hιP1T2'), if_neg (Ne.symm hT1T2'), if_pos rfl]
    ring
  · have hnmemS : P ∉ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa, hEqRa2, hEqιP1, hEqT1, hEqT2⟩
    rw [if_neg hnmemS, if_neg hEqRa, if_neg hEqRa2, if_neg hEqιP1, if_neg hEqT1, if_neg hEqT2]
    ring

/-- **`G₁`, cross2 case: `2•[Ra] + [Ra2] + [ιP1] + [T1] + [T2] -
[T1]-[T2]-[ιT1]-[ιT2]-[δ₀]-[ιδ₀] ∈ principalSubgroup`.** Cross2 sibling
of `cIotaAmIotaT_mem_principalSubgroup_cross4`, on the five-point `f`-
support `{PtRa,PtRa2,PtιP1,PtT1,PtT2}`. Same `divToPairRatio`/
`AddSubgroup.subset_closure` assembly as its predecessors,
`bCACross2_ordInfOfPair` supplying the `-6` pole order. -/
theorem cIotaAmIotaT_mem_principalSubgroup_cross2
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 : k)
    (hdet : (caCross2InterpMatrix RaX Ra2X P1X).det ≠ 0)
    (hlead : caCross2Coeff RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 3 ≠ 0)
    (h1 : RaX ≠ Ra2X) (h2 : RaX ≠ P1X) (h3 : Ra2X ≠ P1X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X)
    (hP2Deriv : 2 * RaY * (-vDerivAtP2) = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0)
    (PtRa PtRa2 PtιP1 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hne : H.f - (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval RaX ≠ 0)
    (hU_evalRa2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval P1X ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T1X)
    (hT2 : (uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (hU_ne0 : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 ≠ 0)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewCross2 H RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross2 RaX Ra2X P1X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])).toNat)]
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
    (divToPair (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])
        ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) -
      divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])
          ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point) -
        divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2) (1 : k[X])
          ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point)
        ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCACross2 RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2, 1,
    ({PtRa, PtRa2, PtιP1, PtT1, PtT2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX T1X * linX T2X) * linX δ₀.X, 0,
    ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hT, hspec_hT, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero T1X) (linX_ne_zero T2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCACross2_ordInfOfPair RaX Ra2X P1X RaY Ra2Y P1Y vDerivAtP2 hlead, ordInfOfPair_hT]

end DecoupledSystem
end Genus2Lean
