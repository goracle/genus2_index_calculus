import Mathlib
import Genus2Lean.ZeroD.PrincipalWitnessStep4Tangent
import Genus2Lean.ZeroD.CAWitnessAssemblyTangent
import Genus2Lean.ZeroD.PrincipalWitnessFinalAssembly

/-! # Tangent siblings of `PrincipalWitnessFinalAssembly.lean`'s
# `cIotaAmIotaT_mem_of_le` / `cAmιTmδmιδ_mem_of_le`

`ROADMAP-principal-witness-tangent-assembly.md`'s Step 4 (remaining half)
and Step 5's prerequisite. Per that doc's own "innocent pass-through"
observation: both of these are thin compositions over the layer-3
theorems, with no new math of their own — `cIotaAmIotaT_mem_of_le_tangent`
pushes `cIotaAmIotaT_mem_principalSubgroup_tangent`
(`PrincipalWitnessStep4Tangent.lean`) forward along `hD` and rewrites via
`divToPair_eq_C_add_iotaA_of_split_tangent` (`CAWitnessAssemblyTangent.
lean`) + `divToPair_hT_eq` (`PrincipalWitnessStep4.lean`, unchanged, no
tangent version needed — see that file's own note); `cAmιTmδmιδ_mem_of_le_
tangent` is `G₁ - G₂ - G₃` exactly as the split version is, `G₂/G₃`
(`fiber_diff_mem_of_le`) themselves already fully generic and reused
verbatim. The only real difference throughout is bookkeeping: the anchor
pair `PtRa1,PtRa2` collapses to one point `PtRa` carrying coefficient `2`
instead of two coefficient-`1` terms — **plus one genuine extra term**:
`divToPair_eq_C_add_iotaA_of_split_tangent`'s `f`-divisor support is only
the three anchor/`ιP` points (`PtT1,PtT2` are not part of it, unlike the
split case's six-point support), so `-single PtT1 - single PtT2` survive
uncancelled into both this file's conclusions where the split case's
analogues have none — see each theorem's own docstring for the exact
shape. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`G₁`, tangent case, spelled out: `2•[Ra]+[ιP1]+[ιP2] - [T1]-[T2]-[ιT1]
-[ιT2]-[δ₀]-[ιδ₀] ∈ D.P`**, for any `D` with `hD : principalSubgroup H
hdeg ≤ D.P`. Tangent sibling of `cIotaAmIotaT_mem_of_le` — same proof
shape: push `cIotaAmIotaT_mem_principalSubgroup_tangent`'s conclusion
forward along `hD`, then rewrite both sides via
`divToPair_eq_C_add_iotaA_of_split_tangent` (`f`'s divisor, tangent case)
and `divToPair_hT_eq` (`h_T`'s divisor, unchanged). -/
theorem cIotaAmIotaT_mem_of_le_tangent
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
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
    (PtT1 PtT2 δ₀ : H.Point)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtιP1, PtιP2} : Finset H.Point) →
      ordAt P (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtιP1, PtιP2} : Finset H.Point),
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
    ((2 : ℤ) • single PtRa + single PtιP1 + single PtιP2 -
      single PtT1 - single PtT2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  have hraw := cIotaAmIotaT_mem_principalSubgroup_tangent (H := H) hdeg hchar hsf
    RaX P1X P2X RaY P1Y P2Y vaDerivAtRa hdet hlead h1 h2 hPP
    hRa_curve hP1_curve hP2_curve hRaDeriv hRaY_ne hP1Y_ne hP2Y_ne
    PtRa PtιP1 PtιP2 hPtRaX hPtRaY hPtιP1X hPtιP1Y hPtιP2X hPtιP2Y
    hne hU_evalRa hU_evalP1 hU_evalP2 T1X T2X hT1 hT2 hTne
    PtT1 PtT2 δ₀ hPtT1X hPtT1Y_ne hPtT2X hPtT2Y_ne h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hLHS := divToPair_eq_C_add_iotaA_of_split_tangent (H := H) hchar hsf
    RaX P1X P2X RaY P1Y P2Y vaDerivAtRa hdet h1 h2 hPP
    hRa_curve hP1_curve hP2_curve hRaDeriv hRaY_ne hP1Y_ne hP2Y_ne
    PtRa PtιP1 PtιP2 hPtRaX hPtRaY hPtιP1X hPtιP1Y hPtιP2X hPtιP2Y
    hne hU_evalRa hU_evalP1 hU_evalP2
  have hPtT12ne : PtT1.X ≠ PtT2.X := by rw [hPtT1X, hPtT2X]; exact hTne
  have hPtT1δ : PtT1.X ≠ δ₀.X := by rw [hPtT1X]; exact h1δ
  have hPtT2δ : PtT2.X ≠ δ₀.X := by rw [hPtT2X]; exact h2δ
  have hRHS := divToPair_hT_eq (H := H) hchar hsf PtT1 PtT2 δ₀
    hPtT12ne hPtT1δ hPtT2δ hPtT1Y_ne hPtT2Y_ne hδY
  have hmem := hD hraw
  rw [← hPtT1X, ← hPtT2X] at hmem
  rw [hLHS, hRHS] at hmem
  have heq : ((2 : ℤ) • single PtRa + single PtιP1 + single PtιP2 -
      (single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀)) : Divisor H) =
      ((2 : ℤ) • single PtRa + single PtιP1 + single PtιP2 -
      single PtT1 - single PtT2 -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) := by abel
  rwa [heq] at hmem

/-- **The honest (†), tangent case: `2•[Ra] - [P1] - [P2] - [T1]-[T2]
- [T1cur]-[T2cur] + [δ₀] + [ιδ₀] ∈ D.P`**, `G₁ - G₂ - G₃` composed, for any
`D` with `hD : principalSubgroup H hdeg ≤ D.P`. Tangent sibling of
`cAmιTmδmιδ_mem_of_le` — identical composition, `G₂ := fiber_diff_mem_of_le
PtP1 δ₀`, `G₃ := fiber_diff_mem_of_le PtP2 δ₀`, both reused verbatim (they
were already generic in the anchor and never depended on `Ra1 ≠ Ra2`).
**Extra `-[T1]-[T2]` terms versus the split case's own conclusion**: unlike
`cIotaAmIotaT_mem_of_le`'s six-point `f`-support (which already includes
bare `PtT1,PtT2` and cancels them against `divToPair_hT_eq`'s matching
`+PtT1+PtT2`), `divToPair_eq_C_add_iotaA_of_split_tangent`'s support is
only the three anchor/`ιP` points — `PtT1,PtT2` never appear on that side,
so nothing cancels them out of `hRHS`'s `+PtT1+PtT2` term. This is
reflected honestly in both this theorem's and `cIotaAmIotaT_mem_of_le_
tangent`'s stated conclusions, not papered over. -/
theorem cAmιTmδmιδ_mem_of_le_tangent
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
    [∀ (a : k) (S : Finset H.Point),
      ∀ P : S, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : k), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    (RaX P1X P2X RaY P1Y P2Y vaDerivAtRa : k)
    (hdet : (caTangentInterpMatrix RaX P1X P2X).det ≠ 0)
    (hlead : caTangentCoeff RaX P1X P2X RaY vaDerivAtRa P1Y P2Y 3 ≠ 0)
    (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa_curve : RaY ^ 2 = H.f.eval RaX)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRaDeriv : 2 * RaY * vaDerivAtRa = (derivative H.f).eval RaX)
    (hRaY_ne : RaY ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa PtP1 PtP2 PtιP1 PtιP2 : H.Point)
    (hPtRaX : PtRa.X = RaX) (hPtRaY : PtRa.Y = RaY)
    (hPtP1X : PtP1.X = P1X) (hPtP1Y : PtP1.Y = P1Y)
    (hPtP2X : PtP2.X = P2X) (hPtP2Y : PtP2.Y = P2Y)
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
    (PtT1 PtT2 δ₀ : H.Point)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa, PtιP1, PtιP2} : Finset H.Point) →
      ordAt P (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangent RaX P1X P2X RaY vaDerivAtRa P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa, PtιP1, PtιP2} : Finset H.Point),
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
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)]
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    ((2 : ℤ) • single PtRa - single PtP1 - single PtP2 -
      single PtT1 - single PtT2 -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  subst hT1eq; subst hT2eq
  have hG1 := cIotaAmIotaT_mem_of_le_tangent (H := H) hdeg hchar hsf D hD
    RaX P1X P2X RaY P1Y P2Y vaDerivAtRa hdet hlead h1 h2 hPP
    hRa_curve hP1_curve hP2_curve hRaDeriv hRaY_ne hP1Y_ne hP2Y_ne
    PtRa PtιP1 PtιP2 hPtRaX hPtRaY hPtιP1X hPtιP1Y hPtιP2X hPtιP2Y
    hne hU_evalRa hU_evalP1 hU_evalP2 T1X T2X hT1 hT2 hTne
    PtT1 PtT2 δ₀ hPtT1X hPtT1Y_ne hPtT2X hPtT2Y_ne h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hG2 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP1 δ₀
  have hG3 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP2 δ₀
  have hcombine := D.P.sub_mem (D.P.sub_mem hG1 hG2) hG3
  have hιPtP1X : (Point.iota PtP1).X = PtιP1.X := by rw [Point.iota_X, hPtP1X, hPtιP1X]
  have hιPtP1Y : (Point.iota PtP1).Y = PtιP1.Y := by rw [Point.iota_Y, hPtP1Y, hPtιP1Y]
  have hιPtP1 : Point.iota PtP1 = PtιP1 := Subtype.ext (Prod.ext hιPtP1X hιPtP1Y)
  have hιPtP2X : (Point.iota PtP2).X = PtιP2.X := by rw [Point.iota_X, hPtP2X, hPtιP2X]
  have hιPtP2Y : (Point.iota PtP2).Y = PtιP2.Y := by rw [Point.iota_Y, hPtP2Y, hPtιP2Y]
  have hιPtP2 : Point.iota PtP2 = PtιP2 := Subtype.ext (Prod.ext hιPtP2X hιPtP2Y)
  have heq :
      (((2 : ℤ) • single PtRa + single PtιP1 + single PtιP2 -
          single PtT1 - single PtT2 -
          single (Point.iota PtT1) - single (Point.iota PtT2) -
          single δ₀ - single (Point.iota δ₀)) -
        (single PtP1 + single (Point.iota PtP1) - single δ₀ - single (Point.iota δ₀)) -
        (single PtP2 + single (Point.iota PtP2) - single δ₀ - single (Point.iota δ₀))
        : Divisor H) =
      ((2 : ℤ) • single PtRa - single PtP1 - single PtP2 -
        single PtT1 - single PtT2 -
        single (Point.iota PtT1) - single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    rw [hιPtP1, hιPtP2]; abel
  rwa [heq] at hcombine

end DecoupledSystem
end Genus2Lean
