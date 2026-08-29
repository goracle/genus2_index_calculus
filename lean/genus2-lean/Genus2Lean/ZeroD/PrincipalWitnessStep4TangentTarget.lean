import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangentTarget
import Genus2Lean.ZeroD.CAWitnessDivisorTangentTarget
import Genus2Lean.ZeroD.CAWitnessAssemblyTangentTarget
import Genus2Lean.ZeroD.CAWitnessResidualTangentTarget
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessStep3
import Genus2Lean.ZeroD.PrincipalWitnessStep4
import Genus2Lean.PrincipalDivisorSubgroup

/-! # Target-axis sibling of `PrincipalWitnessStep4Tangent.lean`'s
# support-widening (`cIotaAmIotaT_mem_principalSubgroup_tangent`)

`ROADMAP-split-hypothesis-elimination.md`'s "item 2 (new)", continuing
past `CAWitnessAssemblyTangentTarget.lean`'s
`divToPair_eq_C_add_iotaA_of_split_tangent_target` (three-point support
`{PtRa1, PtRa2, PtιP}`). Exactly the same support-widening fix
`PrincipalWitnessStep4Tangent.lean`'s own module docstring explains for
the anchor axis: `f`'s divisor also vanishes at `T1X, T2X` (roots of
`uCANewTangentTarget`), which are never among the three named
interpolation nodes, so the honest `f`-support for the
`AddSubgroup.subset_closure` assembly is FIVE points,
`{PtRa1, PtRa2, PtιP, PtT1, PtT2}` (degree `1+1+2+1+1 = 6`, matching
`bCATangentTarget_ordInfOfPair`'s `-6` on the nose — same total as the
anchor-tangent case, just the doubled node sitting at position 3
instead of position 1).

Same proof shape as `PrincipalWitnessStep4Tangent.lean` throughout:
extract the three original `ordAt` values from
`divToPair_eq_C_add_iotaA_of_split_tangent_target` via `coeffAt`, add
the two new `ordAt = 1` facts at `PtT1, PtT2` from
`CAWitnessResidualTangentTarget.lean`'s
`ordAt_eq_rootMultiplicity_of_uCANewTangentTarget_root` composed with
`rootMultiplicity_uCANew_eq_one` (`PrincipalWitnessStep3.lean`, generic,
reused unchanged), then close the widened five-point divisor identity
by `eq_of_coeffAt_eq` and the ten pairwise-distinctness facts among the
five named points. `cIotaAmIotaT_mem_principalSubgroup_tangent_target`
itself is then the same `AddSubgroup.subset_closure` assembly as the
anchor-tangent version, with `bCATangentTarget_ordInfOfPair` supplying
the `-6` pole order. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`f`'s divisor restricted to the five named points, target-tangent
case: `[Ra1] + [Ra2] + 2•[ιP] + [T1] + [T2]`.** Widens
`divToPair_eq_C_add_iotaA_of_split_tangent_target`'s three-point
conclusion by the two residual points, exactly as
`divToPair_eq_C_add_iotaA_add_T_of_split_tangent` widens the anchor
axis's three-point conclusion. -/
theorem divToPair_eq_C_add_iotaA_add_T_of_split_tangent_target
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
    (hU_evalP : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX ≠ 0)
    (hU_ne0 : uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).IsRoot T1X)
    (hT2 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hAeval1 : (denomPolyCATangentTarget Ra1X Ra2X PX : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCATangentTarget Ra1X Ra2X PX : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hPT1 : PX ≠ T1X) (hPT2 : PX ≠ T2X) :
    divToPair (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X])
        ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) =
      single PtRa1 + single PtRa2 + (2 : ℤ) • single PtιP + single PtT1 + single PtT2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  -- The original three-point identity, support `{PtRa1,PtRa2,PtιP}`.
  have h3 : divToPair (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X])
      ({PtRa1, PtRa2, PtιP} : Finset H.Point) =
      single PtRa1 + single PtRa2 + (2 : ℤ) • single PtιP :=
    divToPair_eq_C_add_iotaA_of_split_tangent_target hchar hsf Ra1X Ra2X PX Ra1Y Ra2Y PY
      vDerivAtP hdet h1 h2 h12 hRa1_curve hRa2_curve hP_curve hPDeriv
      hRa1Y_ne hRa2Y_ne hPY_ne PtRa1 PtRa2 PtιP
      hPtRa1X hPtRa1Y hPtRa2X hPtRa2Y hPtιPX hPtιPY hne
      hU_evalRa1 hU_evalRa2 hU_evalP
  -- Pairwise distinctness of all five named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1' Q2' : H.Point}, Q1'.X ≠ Q2'.X → Q1' ≠ Q2' :=
    fun hX heq => hX (heq ▸ rfl)
  have hRa12' : PtRa1 ≠ PtRa2 := hne_of_X (hPtRa1X ▸ hPtRa2X ▸ h12)
  have hRa1ιP' : PtRa1 ≠ PtιP := hne_of_X (hPtRa1X ▸ hPtιPX ▸ h1)
  have hRa2ιP' : PtRa2 ≠ PtιP := hne_of_X (hPtRa2X ▸ hPtιPX ▸ h2)
  have hRa1T1' : PtRa1 ≠ PtT1 := hne_of_X (hPtRa1X ▸ hPtT1X ▸ hRa1T1)
  have hRa1T2' : PtRa1 ≠ PtT2 := hne_of_X (hPtRa1X ▸ hPtT2X ▸ hRa1T2)
  have hRa2T1' : PtRa2 ≠ PtT1 := hne_of_X (hPtRa2X ▸ hPtT1X ▸ hRa2T1)
  have hRa2T2' : PtRa2 ≠ PtT2 := hne_of_X (hPtRa2X ▸ hPtT2X ▸ hRa2T2)
  have hιPT1' : PtιP ≠ PtT1 := hne_of_X (hPtιPX ▸ hPtT1X ▸ hPT1)
  have hιPT2' : PtιP ≠ PtT2 := hne_of_X (hPtιPX ▸ hPtT2X ▸ hPT2)
  have hT1T2' : PtT1 ≠ PtT2 := hne_of_X (hPtT1X ▸ hPtT2X ▸ hTne)
  -- Extract the three original pointwise `ordAt` facts from `h3` via `coeffAt`.
  have hOrdRa1 : ordAt PtRa1 (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
      (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtRa1) h3
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa1 ∈ ({PtRa1, PtRa2, PtιP} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg hRa12', if_neg hRa1ιP']
    ring
  have hOrdRa2 : ordAt PtRa2 (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
      (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtRa2) h3
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa2 ∈ ({PtRa1, PtRa2, PtιP} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRa12'), if_neg hRa2ιP']
    ring
  have hOrdιP : ordAt PtιP (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
      (1 : k[X]) = 2 := by
    have hL := congrArg (coeffAt PtιP) h3
    rw [coeffAt_divToPair] at hL
    have hMem : PtιP ∈ ({PtRa1, PtRa2, PtιP} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRa1ιP'), if_neg (Ne.symm hRa2ιP')]
    ring
  -- The two new residual-point `ordAt = 1` facts.
  have hmult1 : Polynomial.rootMultiplicity T1X
      (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T1X T2X hT1 hT2 hTne Q1 hQ1_def hQ1T1
  have hmult2 : Polynomial.rootMultiplicity T2X
      (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T2X T1X hT2 hT1 (Ne.symm hTne) Q2 hQ2_def hQ2T2
  have hOrdT1 : ordAt PtT1 (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
      (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewTangentTarget_root hchar hsf
      Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
      hRa1_curve hRa2_curve hP_curve hPDeriv PtT1 (h_bot PtT1) hU_ne0
      hAeval1 hPtT1Y hPtT1Y_ne 1 (hPtT1X ▸ hmult1)
    simpa using this
  have hOrdT2 : ordAt PtT2 (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP)
      (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewTangentTarget_root hchar hsf
      Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
      hRa1_curve hRa2_curve hP_curve hPDeriv PtT2 (h_bot PtT2) hU_ne0
      hAeval2 hPtT2Y hPtT2Y_ne 1 (hPtT2X ▸ hmult2)
    simpa using this
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa1 : P = PtRa1
  · rw [hEqRa1]
    have hMem : PtRa1 ∈ ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa1, if_pos rfl, if_neg hRa12', if_neg hRa1ιP',
      if_neg hRa1T1', if_neg hRa1T2']
    ring
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hMem : PtRa2 ∈ ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa2, if_neg (Ne.symm hRa12'), if_pos rfl, if_neg hRa2ιP',
      if_neg hRa2T1', if_neg hRa2T2']
    ring
  by_cases hEqιP : P = PtιP
  · rw [hEqιP]
    have hMem : PtιP ∈ ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdιP, if_neg (Ne.symm hRa1ιP'), if_neg (Ne.symm hRa2ιP'), if_pos rfl,
      if_neg hιPT1', if_neg hιPT2']
    ring
  by_cases hEqT1 : P = PtT1
  · rw [hEqT1]
    have hMem : PtT1 ∈ ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT1, if_neg (Ne.symm hRa1T1'), if_neg (Ne.symm hRa2T1'),
      if_neg (Ne.symm hιPT1'), if_pos rfl, if_neg hT1T2']
    ring
  by_cases hEqT2 : P = PtT2
  · rw [hEqT2]
    have hMem : PtT2 ∈ ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT2, if_neg (Ne.symm hRa1T2'), if_neg (Ne.symm hRa2T2'),
      if_neg (Ne.symm hιPT2'), if_neg (Ne.symm hT1T2'), if_pos rfl]
    ring
  · have hnmemS : P ∉ ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa1, hEqRa2, hEqιP, hEqT1, hEqT2⟩
    rw [if_neg hnmemS, if_neg hEqRa1, if_neg hEqRa2, if_neg hEqιP,
      if_neg hEqT1, if_neg hEqT2]
    ring

/-- **`G₁`, target-tangent case: `[Ra1] + [Ra2] + 2•[ιP] + [T1] + [T2] -
[T1]-[T2]-[ιT1]-[ιT2]-[δ₀]-[ιδ₀] ∈ principalSubgroup`.** Target-tangent
sibling of `cIotaAmIotaT_mem_principalSubgroup_tangent`, on the
corrected five-point `f`-support `{PtRa1,PtRa2,PtιP,PtT1,PtT2}`. Same
`divToPairRatio`/`AddSubgroup.subset_closure` assembly as the anchor-
tangent version, `bCATangentTarget_ordInfOfPair` supplying the `-6`
pole order. -/
theorem cIotaAmIotaT_mem_principalSubgroup_tangent_target
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (hlead : caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 3 ≠ 0)
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
    (hU_evalP : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PX ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).IsRoot T1X)
    (hT2 : (uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (hU_ne0 : uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP ≠ 0)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewTangentTarget H Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCATangentTarget Ra1X Ra2X PX : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCATangentTarget Ra1X Ra2X PX : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1X ≠ T1X) (hRa1T2 : Ra1X ≠ T2X)
    (hRa2T1 : Ra2X ≠ T1X) (hRa2T2 : Ra2X ≠ T2X)
    (hPT1 : PX ≠ T1X) (hPT2 : PX ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X])).toNat)]
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
    (divToPair (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X])
        ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) -
      divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X])
          ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point) -
        divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP) (1 : k[X])
          ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point)
        ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCATangentTarget Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP, 1,
    ({PtRa1, PtRa2, PtιP, PtT1, PtT2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX T1X * linX T2X) * linX δ₀.X, 0,
    ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hT, hspec_hT, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero T1X) (linX_ne_zero T2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCATangentTarget_ordInfOfPair Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hlead, ordInfOfPair_hT]

end DecoupledSystem
end Genus2Lean
