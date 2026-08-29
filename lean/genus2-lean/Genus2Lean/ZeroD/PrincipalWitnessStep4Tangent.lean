import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangent
import Genus2Lean.ZeroD.CAWitnessDivisorTangent
import Genus2Lean.ZeroD.CAWitnessAssemblyTangent
import Genus2Lean.ZeroD.CAWitnessResidualTangent
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessStep3
import Genus2Lean.ZeroD.PrincipalWitnessStep4
import Genus2Lean.PrincipalDivisorSubgroup

/-! # Tangent-case sibling of `PrincipalWitnessStep4.lean`'s Part 3
# (`cIotaAmIotaT_mem_principalSubgroup`)

`ROADMAP-principal-witness-tangent-assembly.md`'s Step 4. `Ra1 = Ra2 =: Ra`
(the doubled anchor root) sibling of `cIotaAmIotaT_mem_principalSubgroup`.

**Corrected support set — fixes the bug traced in the "Root cause
found" writeup (2026-08-28).** A first draft of this file copied the
split case's `hsupp_f` shape onto a THREE-point support
`{PtRa, PtιP1, PtιP2}` — `f`'s divisor there
(`divToPair_eq_C_add_iotaA_of_split_tangent`) only assigns nonzero
`ordAt` at those three points, so `hsupp_f`'s claim that `ordAt P f = 0`
everywhere else was FALSE at `P = PtT1` and `P = PtT2`: `T1X, T2X` are
literally roots of `uCANewTangent`, and `f`'s zero set genuinely includes
them (`pairNormBCATangent_eq_denomPolyCATangent_mul_uCANewTangent` shows
`f`'s pair-norm factors through `uCANewTangent`, so `f` vanishes wherever
that residual does). This made `hsupp_f` an unsatisfiable-in-practice
hypothesis for any caller instantiating it against a real curve — not a
false *theorem* (vacuously fine with no honest witness supplied), but a
trap for the eventual caller, which would otherwise have had to thread
the same false claim one layer further up.

**Fix, following the split case's own precedent exactly** (the split
case already includes `PtT1, PtT2` in `f`'s six-point support, for the
identical reason): widen the support to FIVE points,
`{PtRa, PtιP1, PtιP2, PtT1, PtT2}` (`Ra` still doubled, degree
2+1+1+1+1 = 6, matching `bCATangent_ordInfOfPair`'s `-6` on the nose —
the split case's six named points minus one, since `Ra1,Ra2` collapse to
one point here). The two new `ordAt = 1` facts at `PtT1, PtT2` come from
`CAWitnessResidualTangent.lean`'s
`ordAt_eq_rootMultiplicity_of_uCANewTangent_root`, composed with
`rootMultiplicity_uCANew_eq_one` (`PrincipalWitnessStep3.lean` — generic
in its polynomial argument, so it applies to `uCANewTangent` unchanged,
no tangent-specific port needed) exactly as the split case's own
`hOrdT1`/`hOrdT2` do.

Same proof SHAPE otherwise as the split version: the goal is
`divToPairRatio` of `f := y - bCATangent(x)` (now support
`{Ra,ιP1,ιP2,T1,T2}`, five points) against `h_T := (linX T1X * linX T2X)
* linX δ₀X` (support `{T1,T2,ιT1,ιT2,δ₀,ιδ₀}`, unchanged from the split
case), closed via `AddSubgroup.subset_closure` off the caller-supplied
`hsupp_f`/`hspec_f`/`hsupp_hT`/`hspec_hT` (now genuinely provable) plus a
matching pole-order pair. `bCATangent_ordInfOfPair` (`CAWitnessTangent.
lean`) supplies that pole order (`-6`) in place of the split case's
`bCA_ordInfOfPair`; `ordInfOfPair_hT` (`PrincipalWitnessStep4.lean`,
already generic) is reused unchanged for the `h_T` side. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`f`'s divisor restricted to the five named points, tangent case:
`2•[Ra] + [ιP1] + [ιP2] + [T1] + [T2]`.** Widens
`divToPair_eq_C_add_iotaA_of_split_tangent`'s three-point conclusion by
the two residual points: the three original `ordAt` values are read off
that theorem's conclusion via `coeffAt` at each named point (using
pairwise distinctness), and the two new `ordAt = 1` values at `PtT1,
PtT2` come from `CAWitnessResidualTangent.lean`'s
`ordAt_eq_rootMultiplicity_of_uCANewTangent_root` composed with
`rootMultiplicity_uCANew_eq_one` (`PrincipalWitnessStep3.lean`, reused
unchanged — generic in its polynomial argument). -/
theorem divToPair_eq_C_add_iotaA_add_T_of_split_tangent
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X RaY P1Y P2Y vaDerivAtRa : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtιP1 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval RaX ≠ 0)
    (hU_evalP1 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).IsRoot T1X)
    (hT2 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hAeval1 : (denomPolyCATangent RaX P1X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCATangent RaX P1X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X) :
    divToPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
        ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtιP1 + single PtιP2 + single PtT1 + single PtT2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  -- The original three-point identity, support `{PtRa,PtιP1,PtιP2}`.
  have h3 : divToPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
      ({PtRa, PtιP1, PtιP2} : Finset H.Point) =
      (2 : ℤ) • single PtRa + single PtιP1 + single PtιP2 :=
    divToPair_eq_C_add_iotaA_of_split_tangent hchar hsf RaX P1X P2X RaY P1Y P2Y vaDerivAtRa
      hdet h1 h2 hPP hRa_curve hP1_curve hP2_curve hRaDeriv hRaY_ne hP1Y_ne hP2Y_ne
      PtRa PtιP1 PtιP2 hPtRaX hPtRaY hPtιP1X hPtιP1Y hPtιP2X hPtιP2Y hne
      hU_evalRa hU_evalP1 hU_evalP2
  -- Pairwise distinctness of all five named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1' Q2' : H.Point}, Q1'.X ≠ Q2'.X → Q1' ≠ Q2' :=
    fun hX heq => hX (heq ▸ rfl)
  have hRaιP1' : PtRa ≠ PtιP1 := hne_of_X (hPtRaX ▸ hPtιP1X ▸ h1)
  have hRaιP2' : PtRa ≠ PtιP2 := hne_of_X (hPtRaX ▸ hPtιP2X ▸ h2)
  have hιPP' : PtιP1 ≠ PtιP2 := hne_of_X (hPtιP1X ▸ hPtιP2X ▸ hPP)
  have hRaT1' : PtRa ≠ PtT1 := hne_of_X (hPtRaX ▸ hPtT1X ▸ hRaT1)
  have hRaT2' : PtRa ≠ PtT2 := hne_of_X (hPtRaX ▸ hPtT2X ▸ hRaT2)
  have hιP1T1' : PtιP1 ≠ PtT1 := hne_of_X (hPtιP1X ▸ hPtT1X ▸ hP1T1)
  have hιP1T2' : PtιP1 ≠ PtT2 := hne_of_X (hPtιP1X ▸ hPtT2X ▸ hP1T2)
  have hιP2T1' : PtιP2 ≠ PtT1 := hne_of_X (hPtιP2X ▸ hPtT1X ▸ hP2T1)
  have hιP2T2' : PtιP2 ≠ PtT2 := hne_of_X (hPtιP2X ▸ hPtT2X ▸ hP2T2)
  have hT1T2' : PtT1 ≠ PtT2 := hne_of_X (hPtT1X ▸ hPtT2X ▸ hTne)
  -- Extract the three original pointwise `ordAt` facts from `h3` via `coeffAt`,
  -- mirroring `coeffAt_divToPair`'s own `if P ∈ S then ordAt P A B else 0` shape
  -- explicitly rather than packing the case analysis into one `simp only` set.
  have hOrdRa : ordAt PtRa (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 2 := by
    have hL := congrArg (coeffAt PtRa) h3
    rw [coeffAt_divToPair] at hL
    have hMem : PtRa ∈ ({PtRa, PtιP1, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg hRaιP1', if_neg hRaιP2']
    ring
  have hOrdιP1 : ordAt PtιP1 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtιP1) h3
    rw [coeffAt_divToPair] at hL
    have hMem : PtιP1 ∈ ({PtRa, PtιP1, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRaιP1'), if_neg hιPP']
    ring
  have hOrdιP2 : ordAt PtιP2 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 1 := by
    have hL := congrArg (coeffAt PtιP2) h3
    rw [coeffAt_divToPair] at hL
    have hMem : PtιP2 ∈ ({PtRa, PtιP1, PtιP2} : Finset H.Point) := by simp
    rw [if_pos hMem] at hL
    rw [hL]
    simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul, eq_self, ite_true]
    rw [if_neg (Ne.symm hRaιP2'), if_neg (Ne.symm hιPP')]
    ring
  -- The two new residual-point `ordAt = 1` facts.
  have hmult1 : Polynomial.rootMultiplicity T1X
      (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T1X T2X hT1 hT2 hTne Q1 hQ1_def hQ1T1
  have hmult2 : Polynomial.rootMultiplicity T2X
      (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T2X T1X hT2 hT1 (Ne.symm hTne) Q2 hQ2_def hQ2T2
  have hOrdT1 : ordAt PtT1 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewTangent_root hchar hsf
      RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet h1 h2 hPP
      hRa_curve hP1_curve hP2_curve hRaDeriv PtT1 (h_bot PtT1) hU_ne0
      hAeval1 hPtT1Y hPtT1Y_ne 1 (hPtT1X ▸ hmult1)
    simpa using this
  have hOrdT2 : ordAt PtT2 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANewTangent_root hchar hsf
      RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hdet h1 h2 hPP
      hRa_curve hP1_curve hP2_curve hRaDeriv PtT2 (h_bot PtT2) hU_ne0
      hAeval2 hPtT2Y hPtT2Y_ne 1 (hPtT2X ▸ hmult2)
    simpa using this
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    have hMem : PtRa ∈ ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdRa, if_pos rfl, if_neg hRaιP1', if_neg hRaιP2',
      if_neg hRaT1', if_neg hRaT2']
    ring
  by_cases hEqιP1 : P = PtιP1
  · rw [hEqιP1]
    have hMem : PtιP1 ∈ ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdιP1, if_neg (Ne.symm hRaιP1'), if_pos rfl, if_neg hιPP',
      if_neg hιP1T1', if_neg hιP1T2']
    ring
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hMem : PtιP2 ∈ ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdιP2, if_neg (Ne.symm hRaιP2'), if_neg (Ne.symm hιPP'), if_pos rfl,
      if_neg hιP2T1', if_neg hιP2T2']
    ring
  by_cases hEqT1 : P = PtT1
  · rw [hEqT1]
    have hMem : PtT1 ∈ ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT1, if_neg (Ne.symm hRaT1'), if_neg (Ne.symm hιP1T1'),
      if_neg (Ne.symm hιP2T1'), if_pos rfl, if_neg hT1T2']
    ring
  by_cases hEqT2 : P = PtT2
  · rw [hEqT2]
    have hMem : PtT2 ∈ ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by simp
    rw [if_pos hMem, hOrdT2, if_neg (Ne.symm hRaT2'), if_neg (Ne.symm hιP1T2'),
      if_neg (Ne.symm hιP2T2'), if_neg (Ne.symm hT1T2'), if_pos rfl]
    ring
  · have hnmemS : P ∉ ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa, hEqιP1, hEqιP2, hEqT1, hEqT2⟩
    rw [if_neg hnmemS, if_neg hEqRa, if_neg hEqιP1, if_neg hEqιP2,
      if_neg hEqT1, if_neg hEqT2]
    ring

/-- **`G₁`, tangent case: `2•[Ra] + [ιP1] + [ιP2] + [T1] + [T2] -
[T1]-[T2]-[ιT1]-[ιT2]-[δ₀]-[ιδ₀] ∈ principalSubgroup`.** Tangent sibling
of `cIotaAmIotaT_mem_principalSubgroup`, now on the CORRECTED five-point
`f`-support `{PtRa,PtιP1,PtιP2,PtT1,PtT2}` (see this file's module
docstring for the bug this fixes). `f := y - bCATangent(x)`'s divisor on
that support (`divToPair_eq_C_add_iotaA_add_T_of_split_tangent` above)
minus `h_T := (linX T1X * linX T2X) * linX δ₀X`'s divisor
(`divToPair_hT_eq`, unchanged from the split case). Same
`divToPairRatio`/`AddSubgroup.subset_closure` assembly as the split
version, `bCATangent_ordInfOfPair` supplying the `-6` pole order in place
of `bCA_ordInfOfPair`. -/
theorem cIotaAmIotaT_mem_principalSubgroup_tangent
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X RaY P1Y P2Y vaDerivAtRa : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hlead : caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 3 ≠ 0)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtιP1 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hne : H.f - (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval RaX ≠ 0)
    (hU_evalP1 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval P2X ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).IsRoot T1X)
    (hT2 : (uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (hU_ne0 : uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y ≠ 0)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANewTangent H RaX P1X P2X RaY vaDerivAtRa P1Y P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 δ₀ : H.Point)
    (hAeval1 : (denomPolyCATangent RaX P1X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCATangent RaX P1X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : RaX ≠ T1X) (hRaT2 : RaX ≠ T2X)
    (hP1T1 : P1X ≠ T1X) (hP1T2 : P1X ≠ T2X)
    (hP2T1 : P2X ≠ T1X) (hP2T2 : P2X ≠ T2X)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])).toNat)]
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
    (divToPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
        ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) -
      divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
          ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) -
        divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X])
          ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point)
        ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y, 1,
    ({PtRa, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX T1X * linX T2X) * linX δ₀.X, 0,
    ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hT, hspec_hT, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero T1X) (linX_ne_zero T2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCATangent_ordInfOfPair RaX P1X P2X RaY vaDerivAtRa P1Y P2Y hlead, ordInfOfPair_hT]

end DecoupledSystem
end Genus2Lean
