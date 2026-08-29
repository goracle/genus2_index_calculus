import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangentTarget
import Genus2Lean.ZeroD.CAWitnessDivisorTangentTarget

/-!
# The three-point divisor identity for `CAWitnessTangentTarget.lean`'s
target-tangent-case `f := y - bCATangentTarget(x)`

Target-axis sibling of `CAWitnessAssemblyTangent.lean`'s
`divToPair_eq_C_add_iotaA_of_split_tangent`, per
`ROADMAP-split-hypothesis-elimination.md`'s "item 2 (new)". Support set
is THREE points (`{PtRa1, PtRa2, PtιP}`, `PtιP` carrying coefficient
`2`, not two separate `single PtιP1 + single PtιP2` — the doubled node
sits on the `ι`-flipped side here, unlike `CAWitnessAssemblyTangent.
lean`'s own doubled node which sits on the unflipped `Ra` side).

**`hg_ne_eval` at `PtιP`**: same computation as the split case's
`P1`/`P2` branches (`bCATangentTarget.eval PX = -PY` from
`bCATangentTarget_eval_P`, then the `PY - PY ≠ 0` non-Weierstrass
argument via `hchar`), run once instead of twice. -/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **Shared setup: `pairNorm`/nonvanishing facts feeding all three
pointwise `ordAt` lemmas below.** Factored out so
`ordAt_bCATangentTarget_eq_one_at_Ra1`/`_eq_one_at_Ra2`/`_eq_two_at_ιP`
each only need to redo the point-specific half of the argument. -/
private theorem bCATangentTarget_setup
    (hchar : (2 : k) ≠ 0)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0)
    (hU_evalP : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX ≠ 0) :
    toPair H (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X]) ≠ 0 ∧
    pairNorm H (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X]) =
      denomPolyCATangentTarget Ra1X Ra2X PX *
        (-uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ∧
    toPair H (denomPolyCATangentTarget Ra1X Ra2X PX) (0 : k[X]) ≠ 0 ∧
    toPair H (-uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (0 : k[X]) ≠ 0 := by
  refine ⟨by rw [Ne, toPair_eq_zero_iff]; exact fun ⟨_, hB⟩ => one_ne_zero hB, ?_, ?_, ?_⟩
  · unfold pairNorm
    have hfact := pairNormBCATangentTarget_eq_denomPolyCATangentTarget_mul_uCANewTangentTarget H
      Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
      hRa1_curve hRa2_curve hP_curve hPDeriv hne
    have : (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2) := by ring
    rw [neg_sq, this, hfact]
    ring
  · have hdenom_ne : denomPolyCATangentTarget Ra1X Ra2X PX ≠ 0 := by
      unfold denomPolyCATangentTarget
      exact mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero Ra1X) (X_sub_C_ne_zero Ra2X))
        (pow_ne_zero 2 (X_sub_C_ne_zero PX))
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hdenom_ne hA
  · rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hA, -⟩
    have : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX = 0 := by
      rw [neg_eq_zero] at hA; rw [hA]; simp
    exact hU_evalP this

/-- **Pointwise `ordAt` at `Ra1`: `ordAt PtRa1 (-bCATangentTarget) 1 =
1`.** Exported standalone (unlike `CAWitnessAssemblyTangent.lean`'s
inlined `hOrdRa1`) so `PrincipalWitnessStep4TangentTarget.lean` can
reuse it directly instead of re-deriving it via `coeffAt` extraction
from the 3-point theorem below. -/
theorem ordAt_bCATangentTarget_eq_one_at_Ra1
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hRa1Y_ne : Ra1Y ≠ 0)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval Ra1X ≠ 0)
    (hU_evalP : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX ≠ 0)
    (PtRa1 : H.Point) (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y) :
    ordAt PtRa1 (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X]) = 1 := by
  have h_bot : pointIdeal PtRa1 ≠ ⊥ := pointIdeal_ne_bot PtRa1
  obtain ⟨hg_ne, hAU, hA_ne, hU_ne⟩ := bCATangentTarget_setup (H := H) hchar
    Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
    hRa1_curve hRa2_curve hP_curve hPDeriv hne hU_evalP
  apply ordAt_eq_one_of_old_point PtRa1 h_bot _ _
    (denomPolyCATangentTarget Ra1X Ra2X PX)
    (-uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
    hg_ne _ hAU hA_ne hU_ne _ _
  · show (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PtRa1.X +
        (-(1 : k[X])).eval PtRa1.X * PtRa1.Y ≠ 0
    simp only [hPtRa1X, hPtRa1Y, eval_neg, eval_one]
    rw [bCATangentTarget_eval_Ra1 Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet]
    intro hcontra
    apply hRa1Y_ne
    have h2R : (2 : k) * Ra1Y = 0 := by
      have : -Ra1Y + (-1 : k) * Ra1Y = -(2 * Ra1Y) := by ring
      rw [this] at hcontra
      exact neg_eq_zero.mp hcontra
    rcases mul_eq_zero.mp h2R with h | h
    · exact absurd h hchar
    · exact h
  · exact ordAt_denomCATangentTarget_eq_one_at_Ra1 hchar hsf Ra1X Ra2X PX h12 h1
      PtRa1 h_bot hPtRa1X (hPtRa1Y ▸ hRa1Y_ne)
  · simp only [hPtRa1X, eval_neg]
    simpa using hU_evalRa1

/-- **Pointwise `ordAt` at `Ra2`: `ordAt PtRa2 (-bCATangentTarget) 1 =
1`.** Mirror of `ordAt_bCATangentTarget_eq_one_at_Ra1`. -/
theorem ordAt_bCATangentTarget_eq_one_at_Ra2
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hRa2Y_ne : Ra2Y ≠ 0)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0)
    (hU_evalRa2 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval Ra2X ≠ 0)
    (hU_evalP : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX ≠ 0)
    (PtRa2 : H.Point) (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y) :
    ordAt PtRa2 (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X]) = 1 := by
  have h_bot : pointIdeal PtRa2 ≠ ⊥ := pointIdeal_ne_bot PtRa2
  obtain ⟨hg_ne, hAU, hA_ne, hU_ne⟩ := bCATangentTarget_setup (H := H) hchar
    Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
    hRa1_curve hRa2_curve hP_curve hPDeriv hne hU_evalP
  apply ordAt_eq_one_of_old_point PtRa2 h_bot _ _
    (denomPolyCATangentTarget Ra1X Ra2X PX)
    (-uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
    hg_ne _ hAU hA_ne hU_ne _ _
  · show (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PtRa2.X +
        (-(1 : k[X])).eval PtRa2.X * PtRa2.Y ≠ 0
    simp only [hPtRa2X, hPtRa2Y, eval_neg, eval_one]
    rw [bCATangentTarget_eval_Ra2 Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet]
    intro hcontra
    apply hRa2Y_ne
    have h2R : (2 : k) * Ra2Y = 0 := by
      have : -Ra2Y + (-1 : k) * Ra2Y = -(2 * Ra2Y) := by ring
      rw [this] at hcontra
      exact neg_eq_zero.mp hcontra
    rcases mul_eq_zero.mp h2R with h | h
    · exact absurd h hchar
    · exact h
  · exact ordAt_denomCATangentTarget_eq_one_at_Ra2 hchar hsf Ra1X Ra2X PX h12 h2
      PtRa2 h_bot hPtRa2X (hPtRa2Y ▸ hRa2Y_ne)
  · simp only [hPtRa2X, eval_neg]
    simpa using hU_evalRa2

/-- **Pointwise `ordAt` at `ιP`: `ordAt PtιP (-bCATangentTarget) 1 =
2`.** The doubled node — mirror of the two lemmas above but via
`ordAt_eq_two_of_old_point`. -/
theorem ordAt_bCATangentTarget_eq_two_at_ιP
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hPY_ne : PY ≠ 0)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0)
    (hU_evalP : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX ≠ 0)
    (PtιP : H.Point) (hPtιPX : PtιP.X = PX) (hPtιPY : PtιP.Y = -PY) :
    ordAt PtιP (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X]) = 2 := by
  have h_bot : pointIdeal PtιP ≠ ⊥ := pointIdeal_ne_bot PtιP
  obtain ⟨hg_ne, hAU, hA_ne, hU_ne⟩ := bCATangentTarget_setup (H := H) hchar
    Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
    hRa1_curve hRa2_curve hP_curve hPDeriv hne hU_evalP
  apply ordAt_eq_two_of_old_point PtιP h_bot _ _
    (denomPolyCATangentTarget Ra1X Ra2X PX)
    (-uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
    hg_ne _ hAU hA_ne hU_ne _ _
  · show (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PtιP.X +
        (-(1 : k[X])).eval PtιP.X * PtιP.Y ≠ 0
    simp only [hPtιPX, hPtιPY, eval_neg, eval_one]
    rw [bCATangentTarget_eval_P Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet]
    intro hcontra
    apply hPY_ne
    have h2R : (2 : k) * PY = 0 := by
      have : -(-PY) + (-1 : k) * (-PY) = 2 * PY := by ring
      rw [this] at hcontra
      exact hcontra
    rcases mul_eq_zero.mp h2R with h | h
    · exact absurd h hchar
    · exact h
  · exact ordAt_denomCATangentTarget_eq_two_at_P hchar hsf Ra1X Ra2X PX h1 h2
      PtιP h_bot hPtιPX (by rw [hPtιPY]; exact neg_ne_zero.mpr hPY_ne)
  · simp only [hPtιPX, eval_neg]
    simpa using hU_evalP

/-- **`f`'s divisor restricted to the three named points, target-tangent
case: `[Ra1] + [Ra2] + 2•[ιP]`.** `f := toPair H (-bCATangentTarget) 1`.
`Ra1, Ra2` are the (ordinary, un-collapsed) anchor points; `PtιP` is the
hyperelliptic conjugate of the doubled target point `P` (`sa.P1 =
sa.P2`). Mirrors `divToPair_eq_C_add_iotaA_of_split_tangent` exactly,
now consuming the three standalone pointwise `ordAt` lemmas above. -/
theorem divToPair_eq_C_add_iotaA_of_split_tangent_target
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hPY_ne : PY ≠ 0)
    (PtRa1 PtRa2 PtιP : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιPX : PtιP.X = PX) (hPtιPY : PtιP.Y = -PY)
    (hne : H.f - (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval Ra1X ≠ 0)
    (hU_evalRa2 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval Ra2X ≠ 0)
    (hU_evalP : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX ≠ 0) :
    divToPair (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X])
        ({PtRa1, PtRa2, PtιP} : Finset H.Point) =
      single PtRa1 + single PtRa2 + (2 : ℤ) • single PtιP := by
  have hOrdRa1 := ordAt_bCATangentTarget_eq_one_at_Ra1 hchar hsf Ra1X Ra2X PX Ra1Y Ra2Y PY
    vDerivAtP hdet h1 h2 h12 hRa1_curve hRa2_curve hP_curve hPDeriv hRa1Y_ne hne hU_evalRa1
    hU_evalP PtRa1 hPtRa1X hPtRa1Y
  have hOrdRa2 := ordAt_bCATangentTarget_eq_one_at_Ra2 hchar hsf Ra1X Ra2X PX Ra1Y Ra2Y PY
    vDerivAtP hdet h1 h2 h12 hRa1_curve hRa2_curve hP_curve hPDeriv hRa2Y_ne hne hU_evalRa2
    hU_evalP PtRa2 hPtRa2X hPtRa2Y
  have hOrdιP := ordAt_bCATangentTarget_eq_two_at_ιP hchar hsf Ra1X Ra2X PX Ra1Y Ra2Y PY
    vDerivAtP hdet h1 h2 h12 hRa1_curve hRa2_curve hP_curve hPDeriv hPY_ne hne hU_evalP
    PtιP hPtιPX hPtιPY
  -- Pairwise distinctness of the three named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hRa12' : PtRa1 ≠ PtRa2 := hne_of_X (hPtRa1X ▸ hPtRa2X ▸ h12)
  have hRa1ιP' : PtRa1 ≠ PtιP := hne_of_X (hPtRa1X ▸ hPtιPX ▸ h1)
  have hRa2ιP' : PtRa2 ≠ PtιP := hne_of_X (hPtRa2X ▸ hPtιPX ▸ h2)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa1 : P = PtRa1
  · rw [hEqRa1]
    simpa [hOrdRa1, hRa12', hRa1ιP']
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hRa2Ra1' : PtRa2 ≠ PtRa1 := hRa12'.symm
    simpa [hOrdRa2, hRa2Ra1', hRa2ιP']
  by_cases hEqιP : P = PtιP
  · rw [hEqιP]
    have hιPRa1' : PtιP ≠ PtRa1 := hRa1ιP'.symm
    have hιPRa2' : PtιP ≠ PtRa2 := hRa2ιP'.symm
    simpa [hOrdιP, hιPRa1', hιPRa2']
  · have hnmemS : P ∉ ({PtRa1, PtRa2, PtιP} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa1, hEqRa2, hEqιP⟩
    simp only [if_neg hnmemS, if_neg hEqRa1, if_neg hEqRa2, if_neg hEqιP]
    ring

end DecoupledSystem
end Genus2Lean
