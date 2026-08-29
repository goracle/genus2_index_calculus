import Mathlib
import Genus2Lean.ZeroD.PrincipalWitnessStep4TangentTarget
import Genus2Lean.ZeroD.CAWitnessAssemblyTangentTarget
import Genus2Lean.ZeroD.PrincipalWitnessFinalAssembly

/-! # Target-axis siblings of `PrincipalWitnessFinalAssembly.lean`'s
# `cIotaAmIotaT_mem_of_le` / `cAmιTmδmιδ_mem_of_le`

`ROADMAP-split-hypothesis-elimination.md`'s "item 2 (new)", continuing
`PrincipalWitnessStep4TangentTarget.lean`. Target-axis mirror of
`PrincipalWitnessFinalAssemblyTangent.lean`: both theorems here are the
same thin, no-new-math compositions as their anchor-tangent
counterparts, over the target-tangent layer-3/4 theorems instead.

`cIotaAmIotaT_mem_of_le_tangent_target` pushes
`cIotaAmIotaT_mem_principalSubgroup_tangent_target`
(`PrincipalWitnessStep4TangentTarget.lean`) forward along `hD` and
rewrites via `divToPair_eq_C_add_iotaA_add_T_of_split_tangent_target`
(FIVE-point corrected support, `PrincipalWitnessStep4TangentTarget.
lean`) + `divToPair_hT_eq` (`PrincipalWitnessStep4.lean`, unchanged, no
tangent version needed, same as the anchor-tangent file's own reuse).
`[T1],[T2]` again appear on both sides of the raw membership and
cancel exactly as in the anchor-tangent case, leaving no leftover
`-[T1]-[T2]` terms.

**The one genuine asymmetry versus `PrincipalWitnessFinalAssemblyTangent.
lean`**: there, the doubled node (`Ra`) sits on the UNFLIPPED side, so
`cIotaAmIotaT_mem_of_le_tangent`'s conclusion carries a plain `2•single
PtRa` and the second theorem's `G₂,G₃ := fiber_diff_mem_of_le PtP1
δ₀`/`PtP2 δ₀` are two DIFFERENT ordinary target points, subtracted once
each, to cancel the split case's `+single PtιP1 + single PtιP2` (no
coefficient-2 anywhere on the target side there). Here, the doubled
node (`P`) sits on the FLIPPED side, so `cIotaAmIotaT_mem_of_le_tangent_
target`'s conclusion instead carries a plain `single PtRa1 + single
PtRa2` (anchor pair un-collapsed) and a coefficient-`2` term `2•single
PtιP`. Canceling that coefficient-2 term needs a coefficient-2 fiber
difference, not two distinct ones: `cAmιTmδmιδ_mem_of_le_tangent_target`'s
`G₂` is a single `fiber_diff_mem_of_le PtP δ₀` subtracted TWICE (via
`D.P.zsmul_mem` at `(2:ℤ)`, generic on any `AddSubgroupClass`), mirroring
the coefficient-2 the doubled target node carries throughout this file's
own `bCA`/`uCANew` construction (same convention as
`caTangentTargetInterpMatrix`'s doubled row). This is the reason this
file needed its own composition rather than a verbatim copy of
`PrincipalWitnessFinalAssemblyTangent.lean`'s `G₁-G₂-G₃` shape — traced
from the conclusion shapes, not assumed. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`G₁`, target-tangent case, spelled out: `[Ra1]+[Ra2]+2•[ιP] -
[ιT1]-[ιT2]-[δ₀]-[ιδ₀] ∈ D.P`**, for any `D` with `hD : principalSubgroup
H hdeg ≤ D.P`. Target-tangent sibling of `cIotaAmIotaT_mem_of_le`/
`cIotaAmIotaT_mem_of_le_tangent` — same proof shape: push
`cIotaAmIotaT_mem_principalSubgroup_tangent_target`'s conclusion forward
along `hD`, then rewrite both sides via
`divToPair_eq_C_add_iotaA_add_T_of_split_tangent_target` (`f`'s divisor,
target-tangent case, five-point corrected support) and `divToPair_hT_eq`
(`h_T`'s divisor, unchanged). `[T1],[T2]` cancel in the subtraction
exactly as in the anchor-tangent case. -/
theorem cIotaAmIotaT_mem_of_le_tangent_target
    [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (D : PrincipalDivisorData H) (hD : principalSubgroup H hdeg ≤ D.P)
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
    (single PtRa1 + single PtRa2 + (2 : ℤ) • single PtιP -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  have hraw := cIotaAmIotaT_mem_principalSubgroup_tangent_target (H := H) hdeg hchar hsf
    Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet hlead h1 h2 h12
    hRa1_curve hRa2_curve hP_curve hPDeriv hRa1Y_ne hRa2Y_ne hPY_ne
    PtRa1 PtRa2 PtιP hPtRa1X hPtRa1Y hPtRa2X hPtRa2Y hPtιPX hPtιPY
    hne hU_evalRa1 hU_evalRa2 hU_evalP T1X T2X hT1 hT2 hTne hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2 hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRa2T1 hRa2T2 hPT1 hPT2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hLHS := divToPair_eq_C_add_iotaA_add_T_of_split_tangent_target (H := H) hchar hsf
    Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet h1 h2 h12
    hRa1_curve hRa2_curve hP_curve hPDeriv hRa1Y_ne hRa2Y_ne hPY_ne
    PtRa1 PtRa2 PtιP hPtRa1X hPtRa1Y hPtRa2X hPtRa2Y hPtιPX hPtιPY
    hne hU_evalRa1 hU_evalRa2 hU_evalP hU_ne0 T1X T2X hT1 hT2 hTne
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 hAeval1 hAeval2 hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRa2T1 hRa2T2 hPT1 hPT2
  have hPtT12ne : PtT1.X ≠ PtT2.X := by rw [hPtT1X, hPtT2X]; exact hTne
  have hPtT1δ : PtT1.X ≠ δ₀.X := by rw [hPtT1X]; exact h1δ
  have hPtT2δ : PtT2.X ≠ δ₀.X := by rw [hPtT2X]; exact h2δ
  have hRHS := divToPair_hT_eq (H := H) hchar hsf PtT1 PtT2 δ₀
    hPtT12ne hPtT1δ hPtT2δ hPtT1Y_ne hPtT2Y_ne hδY
  have hmem := hD hraw
  rw [← hPtT1X, ← hPtT2X] at hmem
  rw [hLHS, hRHS] at hmem
  have heq : (single PtRa1 + single PtRa2 + (2 : ℤ) • single PtιP + single PtT1 + single PtT2 -
      (single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀)) : Divisor H) =
      (single PtRa1 + single PtRa2 + (2 : ℤ) • single PtιP -
      single (Point.iota PtT1) - single (Point.iota PtT2) -
      single δ₀ - single (Point.iota δ₀) : Divisor H) := by abel
  rwa [heq] at hmem

/-- **The honest (†), target-tangent case: `[Ra1]+[Ra2] - 2•[P] -
[T1cur]-[T2cur] + [δ₀] + [ιδ₀] ∈ D.P`**, `G₁ - 2•G₂` composed
(`G₂ := fiber_diff_mem_of_le PtP δ₀`, subtracted TWICE via
`D.P.zsmul_mem` at `(2:ℤ)`, not two distinct fiber differences — see
this file's module docstring for why the doubled `ιP` term needs this
instead of the anchor-tangent file's `G₁-G₂-G₃` shape), for any `D`
with `hD : principalSubgroup H hdeg ≤ D.P`. -/
theorem cAmιTmδmιδ_mem_of_le_tangent_target
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
    (Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP : k)
    (hdet : (caTangentTargetInterpMatrix Ra1X Ra2X PX).det ≠ 0)
    (hlead : caTangentTargetCoeff Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP 3 ≠ 0)
    (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX) (h12 : Ra1X ≠ Ra2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP_curve : PY ^ 2 = H.f.eval PX)
    (hPDeriv : 2 * PY * vDerivAtP = (derivative H.f).eval PX)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hPY_ne : PY ≠ 0)
    (PtRa1 PtRa2 PtP PtιP : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtPX : PtP.X = PX) (hPtPY : PtP.Y = PY)
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
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)]
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    (single PtRa1 + single PtRa2 - (2 : ℤ) • single PtP -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P := by
  classical
  subst hT1eq; subst hT2eq
  have hG1 := cIotaAmIotaT_mem_of_le_tangent_target (H := H) hdeg hchar hsf D hD
    Ra1X Ra2X PX Ra1Y Ra2Y PY vDerivAtP hdet hlead h1 h2 h12
    hRa1_curve hRa2_curve hP_curve hPDeriv hRa1Y_ne hRa2Y_ne hPY_ne
    PtRa1 PtRa2 PtιP hPtRa1X hPtRa1Y hPtRa2X hPtRa2Y hPtιPX hPtιPY
    hne hU_evalRa1 hU_evalRa2 hU_evalP T1X T2X hT1 hT2 hTne hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2 hPtT1X hPtT1Y hPtT1Y_ne hPtT2X hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRa2T1 hRa2T2 hPT1 hPT2 h1δ h2δ hδY
    hsupp_f hspec_f hsupp_hT hspec_hT
  have hG2 := fiber_diff_mem_of_le (H := H) hdeg hchar hsf D hD hspec_linX PtP δ₀
  have hG2' := D.P.zsmul_mem hG2 (2 : ℤ)
  have hcombine := D.P.sub_mem hG1 hG2'
  have hιPtPX : (Point.iota PtP).X = PtιP.X := by rw [Point.iota_X, hPtPX, hPtιPX]
  have hιPtPY : (Point.iota PtP).Y = PtιP.Y := by rw [Point.iota_Y, hPtPY, hPtιPY]
  have hιPtP : Point.iota PtP = PtιP := Subtype.ext (Prod.ext hιPtPX hιPtPY)
  have heq :
      ((single PtRa1 + single PtRa2 + (2 : ℤ) • single PtιP -
          single (Point.iota PtT1) - single (Point.iota PtT2) -
          single δ₀ - single (Point.iota δ₀)) -
        (2 : ℤ) • (single PtP + single (Point.iota PtP) - single δ₀ - single (Point.iota δ₀))
        : Divisor H) =
      (single PtRa1 + single PtRa2 - (2 : ℤ) • single PtP -
        single (Point.iota PtT1) - single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    rw [hιPtP]
    simp only [smul_sub, smul_add]
    abel
  rwa [heq] at hcombine

end DecoupledSystem
end Genus2Lean
