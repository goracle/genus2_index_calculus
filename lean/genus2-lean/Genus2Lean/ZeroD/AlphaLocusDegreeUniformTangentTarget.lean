import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.AlphaLocusDegreeUniformTangent
import Genus2Lean.ZeroD.PrincipalWitnessFinalAssemblyTangentTarget

/-! # Tangent-target (`T1 = T2`, equivalently `sa.P1 = sa.P2`) sibling
# of `reducedClass_eq_of_isReduction'`

`ROADMAP-split-hypothesis-elimination.md`'s "item 2 (new)" — the TARGET
axis mirror of `AlphaLocusDegreeUniformTangent.lean` (which built the
ANCHOR axis's `Ra1 = Ra2` tangent case). `reducedClass_eq_of_isReduction'`
itself is stated only for the fully-split target (`sa.P1 ≠ sa.P2` is
implicit throughout its Mumford-pair `(u,v)` construction, via `hcur`/
`hgcd`'s split branch), so the target-tangent case (`sa.P1 = sa.P2`, one
doubled target point `P`) needs its own theorem, exactly as the anchor
axis did. Mirrors `AlphaLocusDegreeUniformTangent.lean`'s own structure
and two-theorem split (`hDP_tangent_target_aux` isolating the large
CA-witness hypothesis zone, main theorem consuming its already-elaborated
conclusion) for the same reason that file needed it: this file's own
`caTangentTargetInterpMatrix`/`uCANewTangentTarget`/`bCATangentTarget`/
`denomPolyCATangentTarget` zone is structurally parallel to (and no
cheaper to elaborate than) the anchor-tangent file's own zone.

**Anchor axis is UNCHANGED from the split theorem here** — this roadmap
item only scopes the target (`sa.P1=sa.P2`) tangent case, mirroring
`AlphaLocusDegreeUniformTangent.lean`'s own restriction (that file
leaves the target axis alone). Consequently this file's main theorem's
signature is the split theorem's signature with `sa.P1 sa.P2` (as the
single doubled point `PtP`) and the target Mumford pair `(u,v)`'s
tangency data substituted for the split target scaffolding: `u` (was
`Ra1,Ra2` on the anchor axis, is `sa.P1,sa.P2` here) collapses via
`hu_eq : u = (X - C PtP.X)^2`, `hPY : PtP.Y = v.eval PtP.X`, `hSmem`/
`hPmem` in place of the split case's cardinality-based
`Sanchor_eq_of_anchor_roots`, and `vDerivAtP`/`hPDeriv` supply the
confluent derivative-row value `CAWitnessTangentTarget.lean` needs.
The ANCHOR side (`Ra1,Ra2`/`Sanchor`/`ua`/`va`) is identical to the split
theorem's own — `Sanchor_eq_of_anchor_roots` (unchanged, NOT the
`_tangent` sibling) and `divToPair_negVa_one_Sanchor_eq` (unchanged) are
reused verbatim, exactly mirroring the anchor-tangent file's own
symmetric reuse of the target-side machinery unchanged.

- `Sanchor_eq_of_anchor_roots_tangent` (`SanchorEqAlphaPoints.lean`) —
  reused here for the TARGET side (`S = {PtP}`), not the anchor side.
  Fully generic in its `Sanchor`/`va` naming (its own docstring already
  notes the pattern is symmetric), so applies unchanged with `S`/`v`/`PtP`
  substituted for `Sanchor`/`va`/`P1`.
- `divToPair_negV_one_S_eq_tangent` (`PrincipalWitnessCAConnection.lean`)
  — collapses to `2 • single PtP` (one doubled target point), the
  target-side twin of `divToPair_negVa_one_Sanchor_eq_tangent` (both
  already exist, per that file's own docstring pairing them).
- `cAmιTmδmιδ_mem_of_le` → `cAmιTmδmιδ_mem_of_le_tangent_target`
  (`PrincipalWitnessFinalAssemblyTangentTarget.lean`) — `hDP`'s source,
  giving `[Ra1]+[Ra2]-2•[P]-[T1]-[T2]+[δ₀]+[ιδ₀] ∈ D.P` (the target-tangent
  shape: anchor pair un-collapsed, target coefficient `2` instead of the
  anchor-tangent file's `2•[Ra]-[P1]-[P2]`). -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

-- **`hDP_tangent_target_aux`**: isolates the ~35-binder "target
-- construction" zone (`hdet`..`hspec_hT`), mirroring
-- `AlphaLocusDegreeUniformTangent.lean`'s own `hDP_tangent_aux` for the
-- identical elaboration-cost reason stated there. Thin specialization of
-- `cAmιTmδmιδ_mem_of_le_tangent_target`
-- (`PrincipalWitnessFinalAssemblyTangentTarget.lean`) to this file's
-- `Ra1`/`Ra2`/`P`/`T1`/`T2` naming; argument order in the proof term below
-- is copied directly from that theorem's own signature, checked
-- binder-by-binder against it.
set_option maxHeartbeats 800000 in
theorem hDP_tangent_target_aux {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    {D : PrincipalDivisorData H}
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (hD : principalSubgroup H hdeg ≤ D.P)
    [∀ (a : F p) (Sfin : Finset H.Point),
      ∀ P : Sfin, Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : F p), ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    (Ra1 : H.Point) (Ra2 : H.Point) (PtP : H.Point)
    (vDerivAtP : F p)
    (hdet : (caTangentTargetInterpMatrix Ra1.X Ra2.X PtP.X).det ≠ 0)
    (hlead : caTangentTargetCoeff Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP 3 ≠ 0)
    (h1 : Ra1.X ≠ PtP.X) (h2 : Ra2.X ≠ PtP.X) (h12 : Ra1.X ≠ Ra2.X)
    (hRa1_curve : Ra1.Y ^ 2 = H.f.eval Ra1.X) (hRa2_curve : Ra2.Y ^ 2 = H.f.eval Ra2.X)
    (hP_curve : PtP.Y ^ 2 = H.f.eval PtP.X)
    (hPDeriv : 2 * PtP.Y * vDerivAtP = (derivative H.f).eval PtP.X)
    (hRa1Y_ne : Ra1.Y ≠ 0) (hRa2Y_ne : Ra2.Y ≠ 0) (hPY_ne : PtP.Y ≠ 0)
    (hne : H.f - (bCATangentTarget Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP) ^ 2 ≠ 0)
    (hU_evalRa1 :
      (uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP).eval Ra1.X ≠ 0)
    (hU_evalRa2 :
      (uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP).eval Ra2.X ≠ 0)
    (hU_evalP :
      (uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP).eval PtP.X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hPtT1 : (uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP).IsRoot PtT1.X)
    (hPtT2 : (uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP).IsRoot PtT2.X)
    (hPtT12X : PtT1.X ≠ PtT2.X)
    (hU_ne0 : uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP ≠ 0)
    (Q1 Q2 : Polynomial (F p))
    (hQ1_def : uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP =
      (Polynomial.X - Polynomial.C PtT1.X) * (Polynomial.X - Polynomial.C PtT2.X) * Q1)
    (hQ1T1 : Q1.eval PtT1.X ≠ 0)
    (hQ2_def : uCANewTangentTarget H Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP =
      (Polynomial.X - Polynomial.C PtT2.X) * (Polynomial.X - Polynomial.C PtT1.X) * Q2)
    (hQ2T2 : Q2.eval PtT2.X ≠ 0)
    (δ₀ : H.Point)
    (hAeval1 : (denomPolyCATangentTarget Ra1.X Ra2.X PtP.X : Polynomial (F p)).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCATangentTarget Ra1.X Ra2.X PtP.X : Polynomial (F p)).eval PtT2.X ≠ 0)
    (hPtT1Y : PtT1.Y =
      (bCATangentTarget Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2Y : PtT2.Y =
      (bCATangentTarget Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1.X ≠ PtT1.X) (hRa1T2 : Ra1.X ≠ PtT2.X)
    (hRa2T1 : Ra2.X ≠ PtT1.X) (hRa2T2 : Ra2.X ≠ PtT2.X)
    (hPT1 : PtP.X ≠ PtT1.X) (hPT2 : PtP.X ≠ PtT2.X)
    (h1δ : PtT1.X ≠ δ₀.X) (h2δ : PtT2.X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({Ra1, Ra2, Point.iota PtP, PtT1, PtT2} :
        Finset H.Point) →
      ordAt P (-bCATangentTarget Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP)
        (1 : Polynomial (F p)) = 0)
    (hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangentTarget Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({Ra1, Ra2, Point.iota PtP, PtT1, PtT2} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCATangentTarget Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP)
          (1 : Polynomial (F p))).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : Polynomial (F p)) = 0)
    (hspec_hT : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : Polynomial (F p))).toNat)]
    (T1cur T2cur : H.Point)
    (hT1eq : T1cur = Point.iota PtT1) (hT2eq : T2cur = Point.iota PtT2) :
    (single Ra1 + single Ra2 - (2 : ℤ) • single PtP -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P :=
  cAmιTmδmιδ_mem_of_le_tangent_target (H := H) hdeg hchar hsf D hD
    hspec_linX
    Ra1.X Ra2.X PtP.X Ra1.Y Ra2.Y PtP.Y vDerivAtP
    hdet hlead h1 h2 h12
    hRa1_curve hRa2_curve hP_curve hPDeriv
    hRa1Y_ne hRa2Y_ne hPY_ne
    Ra1 Ra2 PtP (Point.iota PtP)
    rfl rfl rfl rfl rfl rfl rfl rfl
    hne hU_evalRa1 hU_evalRa2 hU_evalP
    PtT1.X PtT2.X hPtT1 hPtT2 hPtT12X hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2 rfl hPtT1Y hPtT1Y_ne rfl hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRa2T1 hRa2T2 hPT1 hPT2 h1δ h2δ hδY hsupp_f hspec_f hsupp_hT hspec_hT
    T1cur T2cur hT1eq hT2eq

/-!
Same reasoning as `AlphaLocusDegreeUniformTangent.lean`'s own module
docstring for this split: the final theorem consumes dependent records,
the large CA-witness hypotheses stay isolated in `hDP_tangent_target_aux`
above, and the small divisor-zero witnesses reuse
`sampleP1P2_sub_two_delta_mem` (`AlphaLocusDegreeUniformTangent.lean`,
generic in its own right — it doesn't depend on whether `sa.P1,sa.P2` are
literally distinct, only on the divisor-zero membership of
`single sa.P1 + single sa.P2 - 2•single δ₀`, so no target-tangent variant
is needed here). -/

set_option maxHeartbeats 800000 in
structure TangentTargetCoefficientData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  coeff_c0 : F p
  coeff_c1 : F p
  coeff_c2 : F p
  coeff_c3 : F p
  coeff_c4 : F p
  coeff_ua0 : F p
  coeff_ua1 : F p
  coeff_va0 : F p
  coeff_va1 : F p
  coeff_hf : H.f = curvePoly p coeff_c0 coeff_c1 coeff_c2 coeff_c3 coeff_c4
  coeff_hMumfordUa : IsMumfordUa p coeff_c0 coeff_c1 coeff_c2 coeff_c3 coeff_c4
      coeff_ua0 coeff_ua1 coeff_va0 coeff_va1

set_option maxHeartbeats 800000 in
structure TangentTargetReductionData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  coeffs : TangentTargetCoefficientData sa
  hReducedClass :
    sa.reducedClass =
      sa.alpha • aClass -
        toJacobian D
          (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
            sampleP1P2_sub_two_delta_mem sa⟩ : Divisor0 H)

set_option maxHeartbeats 800000 in
structure TangentTargetAssemblyData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  as_coeffs : TangentTargetCoefficientData sa
  as_Sanchor : Finset H.Point
  as_S : Finset H.Point
  as_va : Polynomial (F p)
  as_ua : Polynomial (F p)
  as_v : Polynomial (F p)
  hva : as_va = (Polynomial.C as_coeffs.coeff_va1 : Polynomial (F p)) *
      (Polynomial.X : Polynomial (F p)) + (Polynomial.C as_coeffs.coeff_va0 : Polynomial (F p))
  hv : as_v = (Polynomial.C sa.toSampleTarget.v1 : Polynomial (F p)) *
      (Polynomial.X : Polynomial (F p)) + (Polynomial.C sa.toSampleTarget.v0 : Polynomial (F p))
  hua : as_ua = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C as_coeffs.coeff_ua1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C as_coeffs.coeff_ua0 : Polynomial (F p))
  hmemAnchor : (divToPair (H := H) (-as_va) 1 as_Sanchor -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H
  hAlphaRep : sa.alpha • aClass =
      toJacobian D (Subtype.mk (divToPair (H := H) (-as_va) 1 as_Sanchor -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmemAnchor)
  hSanchorMem : ∀ Q ∈ as_Sanchor, as_ua.eval Q.X = 0 ∧ Q.Y = as_va.eval Q.X
  huafree : Squarefree as_ua
  hSanchorCard : as_Sanchor.card = as_ua.natDegree
  hmem : (divToPair (H := H) (-as_v) 1 as_S -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H
  as_q : Jacobian H D
  hq : as_q = toJacobian D (Subtype.mk (single (Point.iota δ₀) - single δ₀ : Divisor H)
      (single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀))
  as_Ra1 : H.Point
  as_Ra2 : H.Point
  hRa12ne : as_Ra1 ≠ as_Ra2
  hRa12Xne : as_Ra1.X ≠ as_Ra2.X
  hRa1Root : as_ua.IsRoot as_Ra1.X
  hRa2Root : as_ua.IsRoot as_Ra2.X
  hRa1Y : as_Ra1.Y = as_va.eval as_Ra1.X
  hRa2Y : as_Ra2.Y = as_va.eval as_Ra2.X
  as_u : Polynomial (F p)
  hu : as_u = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C sa.toSampleTarget.u1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p))
  as_PtP : H.Point
  hu_eq : as_u = (Polynomial.X - Polynomial.C as_PtP.X) ^ 2
  hPY : as_PtP.Y = as_v.eval as_PtP.X
  hSmem : ∀ Q ∈ as_S, as_u.eval Q.X = 0 ∧ Q.Y = as_v.eval Q.X
  hPmem : as_PtP ∈ as_S
  chchar : (2 : F p) ≠ 0
  as_Uco : Polynomial (F p)
  as_UcoT : Polynomial (F p)
  hAU : pairNorm H (-as_va) (1 : Polynomial (F p)) = as_ua * as_Uco
  hUco_ne : as_Uco ≠ 0
  hUco_evalRa1 : as_Uco.eval as_Ra1.X ≠ 0
  hUco_evalRa2 : as_Uco.eval as_Ra2.X ≠ 0
  hAUT : pairNorm H (-as_v) (1 : Polynomial (F p)) = as_u * as_UcoT
  hUcoT_ne : as_UcoT ≠ 0
  hUcoT_evalP : as_UcoT.eval as_PtP.X ≠ 0
  hRa1Y_ne : as_Ra1.Y ≠ 0
  hRa2Y_ne : as_Ra2.Y ≠ 0
  hPY_ne : as_PtP.Y ≠ 0
  hDP : (single as_Ra1 + single as_Ra2 - (2 : ℤ) • single as_PtP -
      single sa.P1 - single sa.P2 + single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P

-- Isolate the expensive specialized divisor-arithmetic elaboration from
-- the large dependent assembly theorem, mirroring
-- `AlphaLocusDegreeUniformTangent.lean`'s `tangent_anchor_sum_of_data`
-- exactly (anchor side, split — unchanged, both machinery and
-- distinctness hypothesis, since this file's tangent case is on the
-- TARGET axis only).
set_option maxHeartbeats 800000 in
theorem anchor_sum_of_data_target_tangent
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    (ua0 ua1 va0 va1 : F p)
    (Ra1 Ra2 : H.Point) (hRa1ne : Ra1 ≠ Ra2) (hRa1Xne : Ra1.X ≠ Ra2.X)
    (ua va : Polynomial (F p))
    (hua : ua = (Polynomial.X : Polynomial (F p)) ^ 2 + Polynomial.C ua1 * Polynomial.X
      + Polynomial.C ua0)
    (huafree : Squarefree ua)
    (hAnchorRoots : ua.IsRoot Ra1.X ∧ ua.IsRoot Ra2.X)
    (hRa1Y : Ra1.Y = va.eval Ra1.X) (hRa2Y : Ra2.Y = va.eval Ra2.X)
    (Sanchor : Finset H.Point)
    (hSanchorMem : ∀ Q ∈ Sanchor, ua.eval Q.X = 0 ∧ Q.Y = va.eval Q.X)
    (hSanchorCard : Sanchor.card = ua.natDegree) :
    Sanchor = ({Ra1, Ra2} : Finset H.Point) :=
  Sanchor_eq_of_anchor_roots (H := H) ua va hua huafree Ra1 Ra2 hRa1ne hRa1Xne
    hAnchorRoots hRa1Y hRa2Y Sanchor hSanchorMem hSanchorCard

-- Target-side sum, target-tangent case: mirrors
-- `AlphaLocusDegreeUniformTangent.lean`'s `tangent_anchor_sum_of_data`
-- exactly, with the anchor/target roles swapped (`S`/`v`/`PtP` in place
-- of `Sanchor`/`va`/`Ra`).
set_option maxHeartbeats 800000 in
theorem target_sum_of_data_tangent
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    (hchar : (2 : F p) ≠ 0)
    (u0 u1 v0 v1 : F p)
    (PtP : H.Point)
    (hu_eq : (Polynomial.X ^ 2 + Polynomial.C u1 * Polynomial.X +
      Polynomial.C u0 : Polynomial (F p)) =
      (Polynomial.X - Polynomial.C PtP.X) ^ 2)
    (v : Polynomial (F p)) (hv : v =
      (Polynomial.C v1 : Polynomial (F p)) * Polynomial.X +
        (Polynomial.C v0 : Polynomial (F p)))
    (UcoT : Polynomial (F p))
    (hAUT : pairNorm H (-v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C u1 * Polynomial.X +
        Polynomial.C u0 : Polynomial (F p)) * UcoT)
    (hUcoT_ne : UcoT ≠ 0)
    (hPY_ne : PtP.Y ≠ 0)
    (hPY : PtP.Y = v.eval PtP.X)
    (hUcoT_evalP : UcoT.eval PtP.X ≠ 0)
    (S : Finset H.Point)
    (hSEq : S = ({PtP} : Finset H.Point)) :
    divToPair (H := H) (-v) 1 S = (2 : ℤ) • single PtP := by
  -- Same coefficient-extraction move as `tangent_anchor_sum_of_data`:
  -- `divToPair_negV_one_S_eq_tangent`'s own `hua_eq` wants the specific
  -- `-2*R`/`R*R` shape, not the general `u1`/`u0` shape, so extract via
  -- evaluation at two points (not `coeff`) then close with
  -- `linear_combination` (`F p` is not a linear order).
  have heval0 : u0 = PtP.X ^ 2 := by
    have h := congrArg (fun q => Polynomial.eval 0 q) hu_eq
    simpa using h
  have hevalNeg1 : 1 - u1 + u0 = (PtP.X + 1) ^ 2 := by
    have h := congrArg (fun q => Polynomial.eval (-1) q) hu_eq
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub] at h
    linear_combination h
  have hcoeff1 : u1 = -2 * PtP.X := by linear_combination heval0 - hevalNeg1
  have hcoeff0 : u0 = PtP.X * PtP.X := by linear_combination heval0
  have hu_eq' : (Polynomial.X ^ 2 + Polynomial.C (-2 * PtP.X) * Polynomial.X +
      Polynomial.C (PtP.X * PtP.X) : Polynomial (F p)) =
      (Polynomial.X - Polynomial.C PtP.X) ^ 2 := by
    rw [← hcoeff1, ← hcoeff0]
    exact hu_eq
  have hAUT' : pairNorm H (-v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C (-2 * PtP.X) * Polynomial.X +
        Polynomial.C (PtP.X * PtP.X) : Polynomial (F p)) * UcoT := by
    rw [← hcoeff1, ← hcoeff0]
    exact hAUT
  exact divToPair_negV_one_S_eq_tangent (H := H) hchar hu_eq'
    v hv UcoT hAUT' hUcoT_ne PtP hPY_ne rfl hPY hUcoT_evalP S hSEq

/--
Target-tangent assembly, with the expensive hypotheses bundled before the
main theorem is elaborated. `hDP` should normally be produced by
`hDP_tangent_target_aux`; all of the CA-witness side conditions needed
for that construction are intentionally absent from this theorem's
signature. -/
theorem reducedClass_eq_of_isReduction'_tangent_target
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (base : TangentTargetReductionData sa)
    (d : TangentTargetAssemblyData sa)
    (hcoeff : d.as_coeffs = base.coeffs) :
    sa.reducedClass + d.as_q =
      toJacobian D (Subtype.mk (divToPair (H := H) (-d.as_v) 1 d.as_S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) d.hmem) := by
  classical
  -- Anchor side unchanged from the split theorem: `Sanchor_eq_of_
  -- anchor_roots` (NOT the tangent sibling — the anchor pair is genuinely
  -- distinct in this file, only the target is doubled).
  have hSanchorEq : d.as_Sanchor = ({d.as_Ra1, d.as_Ra2} : Finset H.Point) :=
    anchor_sum_of_data_target_tangent d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1
      d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
      d.as_Ra1 d.as_Ra2 d.hRa12ne d.hRa12Xne d.as_ua d.as_va d.hua d.huafree
      ⟨d.hRa1Root, d.hRa2Root⟩ d.hRa1Y d.hRa2Y d.as_Sanchor d.hSanchorMem d.hSanchorCard
  -- Target side doubled: `Sanchor_eq_of_anchor_roots_tangent`, applied
  -- here to `S`/`v`/`PtP` (fully generic, per that lemma's own docstring).
  have hu_eq_spelled :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) =
        (Polynomial.X - Polynomial.C d.as_PtP.X) ^ 2 := by
    rw [← d.hu]
    exact d.hu_eq
  have hSEq : d.as_S = ({d.as_PtP} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots_tangent d.as_u d.as_v d.as_PtP d.hu_eq d.hPY
      d.as_S d.hSmem d.hPmem
  have huafree' : Squarefree (Polynomial.X ^ 2 +
      Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X +
      Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) := by
    rw [← d.hua]
    exact d.huafree
  have hRa1Root' :
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X +
        Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)).IsRoot d.as_Ra1.X := by
    rw [← d.hua]
    exact d.hRa1Root
  have hRa2Root' :
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X +
        Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)).IsRoot d.as_Ra2.X := by
    rw [← d.hua]
    exact d.hRa2Root
  have hAU' : pairNorm H (-d.as_va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X +
        Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) * d.as_Uco := by
    rw [← d.hua]
    exact d.hAU
  have hAUT' : pairNorm H (-d.as_v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) * d.as_UcoT := by
    rw [← d.hu]
    exact d.hAUT
  have hSanchorSum : divToPair (H := H) (-d.as_va) 1 d.as_Sanchor =
      single d.as_Ra1 + single d.as_Ra2 := by
    exact DecoupledSystem.divToPair_negVa_one_Sanchor_eq (H := H) d.chchar
      (c0 := d.as_coeffs.coeff_c0) (c1 := d.as_coeffs.coeff_c1)
      (c2 := d.as_coeffs.coeff_c2) (c3 := d.as_coeffs.coeff_c3)
      (c4 := d.as_coeffs.coeff_c4)
      (ua0 := d.as_coeffs.coeff_ua0) (ua1 := d.as_coeffs.coeff_ua1)
      (va0 := d.as_coeffs.coeff_va0) (va1 := d.as_coeffs.coeff_va1)
      d.as_coeffs.coeff_hf d.as_coeffs.coeff_hMumfordUa huafree' d.as_va d.hva
      d.as_Uco hAU' d.hUco_ne d.as_Ra1 d.as_Ra2 d.hRa12ne d.hRa1Y_ne d.hRa2Y_ne
      hRa1Root' hRa2Root' d.hRa1Y d.hRa2Y d.hUco_evalRa1 d.hUco_evalRa2
      d.as_Sanchor hSanchorEq
  have hSSum : divToPair (H := H) (-d.as_v) 1 d.as_S = (2 : ℤ) • single d.as_PtP := by
    exact target_sum_of_data_tangent d.chchar
      sa.toSampleTarget.u0 sa.toSampleTarget.u1
      sa.toSampleTarget.v0 sa.toSampleTarget.v1
      d.as_PtP hu_eq_spelled d.as_v d.hv d.as_UcoT hAUT' d.hUcoT_ne
      d.hPY_ne d.hPY d.hUcoT_evalP d.as_S hSEq
  set aAnchor : Divisor0 H := ⟨divToPair (H := H) (-d.as_va) 1 d.as_Sanchor -
    (single δ₀ + single (Point.iota δ₀)), d.hmemAnchor⟩ with haAnchor_def
  set aTarget : Divisor0 H := ⟨divToPair (H := H) (-d.as_v) 1 d.as_S -
    (single δ₀ + single (Point.iota δ₀)), d.hmem⟩ with haTarget_def
  set aP1P2Nι : Divisor0 H := ⟨single sa.P1 + single sa.P2 -
      (single δ₀ + single (Point.iota δ₀)), by
        have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
        have h2 := single_sub_single_mem_Divisor0 sa.P2 (Point.iota δ₀)
        have heq2 : single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀)) =
            (single sa.P1 - single δ₀) + (single sa.P2 - single (Point.iota δ₀)) := by
          abel
        rw [heq2]
        exact add_mem h1 h2⟩ with haP1P2Nι_def
  set aQ : Divisor0 H := ⟨single (Point.iota δ₀) - single δ₀,
    single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀⟩ with haQ_def
  have hred : sa.reducedClass = sa.alpha • aClass -
      (toJacobian D aP1P2Nι + d.as_q) := by
    have hN2 :
        (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
          by
            have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
            have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
            have heq2 : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
                (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
              rw [two_zsmul]
              abel
            rw [heq2]
            exact add_mem h1 h2⟩ : Divisor0 H) = aP1P2Nι + aQ := by
      apply Subtype.ext
      show single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) +
          (single (Point.iota δ₀) - single δ₀)
      rw [two_zsmul]
      abel
    rw [base.hReducedClass, hN2, map_add, d.hq]
  have hgoal : sa.alpha • aClass - (toJacobian D aP1P2Nι + d.as_q) + d.as_q =
      toJacobian D aTarget := by
    have hcancel : sa.alpha • aClass - (toJacobian D aP1P2Nι + d.as_q) + d.as_q =
        sa.alpha • aClass - toJacobian D aP1P2Nι := by
      abel
    rw [hcancel, d.hAlphaRep]
    have hcoe : ((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
        ((aTarget : Divisor0 H) : Divisor H) =
        (single d.as_Ra1 + single d.as_Ra2 - (2 : ℤ) • single d.as_PtP -
          single sa.P1 - single sa.P2 + single δ₀ + single (Point.iota δ₀) : Divisor H) := by
      show (aAnchor.1 - aP1P2Nι.1) - aTarget.1 =
        single d.as_Ra1 + single d.as_Ra2 - (2 : ℤ) • single d.as_PtP -
          single sa.P1 - single sa.P2 + single δ₀ + single (Point.iota δ₀)
      show (divToPair (H := H) (-d.as_va) 1 d.as_Sanchor -
          (single δ₀ + single (Point.iota δ₀)) -
          (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀)))) -
          (divToPair (H := H) (-d.as_v) 1 d.as_S -
            (single δ₀ + single (Point.iota δ₀))) =
        single d.as_Ra1 + single d.as_Ra2 - (2 : ℤ) • single d.as_PtP -
          single sa.P1 - single sa.P2 + single δ₀ + single (Point.iota δ₀)
      rw [hSanchorSum, hSSum]
      abel
    have hmemD : (((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
        ((aTarget : Divisor0 H) : Divisor H)) ∈ D.P := by
      rw [hcoe]
      exact d.hDP
    have hmemD' : (((aAnchor - aP1P2Nι - aTarget : Divisor0 H)) : Divisor H) ∈ D.P := by
      have hval : (((aAnchor - aP1P2Nι - aTarget : Divisor0 H)) : Divisor H) =
          (((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
            ((aTarget : Divisor0 H) : Divisor H)) := by
        rfl
      rw [hval]
      exact hmemD
    have hmemAddSub : (aAnchor - aP1P2Nι - aTarget : Divisor0 H) ∈
        D.P.addSubgroupOf (Divisor0 H) := by
      rw [AddSubgroup.mem_addSubgroupOf]
      exact hmemD'
    have hJeq := (QuotientAddGroup.eq_iff_sub_mem
      (N := D.P.addSubgroupOf (Divisor0 H))).mpr hmemAddSub
    have hsub_eq : toJacobian D aAnchor - toJacobian D aP1P2Nι =
        toJacobian D (aAnchor - aP1P2Nι) := (map_sub _ _ _).symm
    rw [hsub_eq]
    change QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H))
        (aAnchor - aP1P2Nι) =
      QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H)) aTarget
    exact hJeq
  calc sa.reducedClass + d.as_q
      = (sa.alpha • aClass - (toJacobian D aP1P2Nι + d.as_q)) + d.as_q := by rw [hred]
    _ = toJacobian D aTarget := hgoal
    _ = toJacobian D (Subtype.mk (divToPair (H := H) (-d.as_v) 1 d.as_S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) d.hmem) := rfl

end DecoupledSystem
end Genus2Lean
