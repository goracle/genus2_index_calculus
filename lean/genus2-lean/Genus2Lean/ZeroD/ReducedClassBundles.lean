import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.AlphaLocusDegreeUniformTangent

/-! # Shared `CoefficientData`/`ReductionData` bundles for the seven
`reducedClass_eq_of_isReduction'` variants

`ROADMAP-reducedClass-dispatcher.md`, "Suggested order" step 2. Per
that doc's own field-by-field diff of the two ALREADY-bundled variants
(`TangentCoefficientData`/`TangentReductionData`,
`AlphaLocusDegreeUniformTangent.lean`; `TangentTargetCoefficientData`/
`TangentTargetReductionData`, `AlphaLocusDegreeUniformTangentTarget.lean`):

- **`ReductionData` is IDENTICAL across both existing instances** —
  same `coeffs` projection, same `hReducedClass` statement, same proof
  term (`sampleP1P2_sub_two_delta_mem`). Nothing in it mentions
  `Ra`/`Ra2`/tangency/cross-identification at all; it is entirely
  about `sa.P1,sa.P2,δ₀`, which every one of the seven variants shares
  unchanged. One shared structure genuinely suffices.
- **`CoefficientData` differs by exactly one field** between the two
  existing instances: `TangentCoefficientData` (anchor doubled) has
  `coeff_hMumfordTarget : IsMumfordTarget4 ...`;
  `TangentTargetCoefficientData` (target doubled) has
  `coeff_hMumfordUa : IsMumfordUa ...` instead. Each file only names
  the Mumford fact for the side it does NOT make tangent — a real
  asymmetry, not an oversight. Resolved here by carrying BOTH fields
  unconditionally (`coeff_hMumfordUa` AND `coeff_hMumfordTarget`):
  this costs the caller one extra `Prop` to supply, not new proof
  content (both facts are independently available in any real
  instantiation, since the tangency itself is pinned down elsewhere,
  in the construction-specific `AssemblyData` tier that step 3 of the
  roadmap still owes) and lets every branch of the eventual dispatcher
  share one coefficient bundle rather than converting between two
  near-identical types depending on which branch fired.

This file does NOT yet touch the two existing
`Tangent(Target)?CoefficientData`/`...ReductionData` structures or
their call sites (it only imports `AlphaLocusDegreeUniformTangent.lean`
for `sampleP1P2_sub_two_delta_mem`, the shared proof-term helper — no
circularity risk, since that file predates this one and doesn't import
it back). Per the roadmap's own step 2 note, editing those existing
structures is a real edit to already-proved code and belongs with the
REPL-tested, one-theorem-at-a-time pass that comes after this file
exists and REPL-confirms clean on its own. This file is purely
additive: two new structures, no existing theorem's signature changed
yet. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-- **Shared curve/coefficient layer**, common to all seven
`reducedClass_eq_of_isReduction'` variants. Carries BOTH
`coeff_hMumfordUa` and `coeff_hMumfordTarget` (see module docstring for
why this is a superset of either existing `Tangent`/`TangentTarget`
`CoefficientData`, not a narrower common core) so every variant's
dispatcher branch can consume the same bundle type. -/
structure CoefficientData
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
  coeff_hMumfordTarget : IsMumfordTarget4 p coeff_c0 coeff_c1 coeff_c2 coeff_c3 coeff_c4
      sa.toSampleTarget.u0 sa.toSampleTarget.u1
      sa.toSampleTarget.v0 sa.toSampleTarget.v1

/-- **Shared `reducedClass`-decomposition layer**, common to all seven
variants. Identical to both existing `Tangent`/`TangentTarget`
`ReductionData` structures — `hReducedClass` mentions only
`sa.P1,sa.P2,δ₀`, never the anchor/target tangency data that
distinguishes the seven branches, so no per-variant field is needed
here at all. -/
structure ReductionData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  coeffs : CoefficientData sa
  hReducedClass :
    sa.reducedClass =
      sa.alpha • aClass -
        toJacobian D
          (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
            sampleP1P2_sub_two_delta_mem sa⟩ : Divisor0 H)

set_option maxHeartbeats 8000000 in
/-- **Construction-specific assembly layer for the BASE (fully split)
`reducedClass_eq_of_isReduction'` theorem.** `ROADMAP-reducedClass-
dispatcher.md`, "Suggested order" step 3: this is the everything-else
tier that `ReductionData`/`CoefficientData` deliberately excluded,
copied field-for-field from that theorem's current flat signature
(`AlphaLocusDegreeUniform.lean` lines 882-1121, diffed directly against
`AlphaLocusDegreeUniformCross1.lean`'s own flat signature to confirm
exactly which fields are split-specific vs. shared — per that diff,
`Sanchor,S,va,u,v` and the `T1,T2`-split machinery are IDENTICAL across
all five non-tangent variants, and only the `Ra1,Ra2,hdet,hlead,
h1P1..hPP,hRa1_curve..,hU_eval*,PtT1,PtT2,Q1,Q2,hQ*,hAeval*,hPtT*Y*,
hsupp_f,hspec_f`-block is genuinely construction-specific to the base
theorem's four-free-point `caInterpMatrix`/`caCoeff`/`uCANew`/`bCA`/
`denomPolyCA` construction). Named `as_`-prefixed for data fields and
plain for hypotheses, mirroring `TangentAssemblyData`'s own convention
field-for-field. `as_q`/`hq` carries the dispatcher-relevant
compensating term, exactly as `TangentAssemblyData.as_q` does. -/
structure SplitAssemblyData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  as_coeffs : CoefficientData sa
  as_Sanchor : Finset H.Point
  as_S : Finset H.Point
  as_va : Polynomial (F p)
  as_u : Polynomial (F p)
  as_v : Polynomial (F p)
  hva : as_va = (Polynomial.C as_coeffs.coeff_va1 : Polynomial (F p)) *
      (Polynomial.X : Polynomial (F p)) + (Polynomial.C as_coeffs.coeff_va0 : Polynomial (F p))
  hu : as_u = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C sa.toSampleTarget.u1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p))
  hv : as_v = (Polynomial.C sa.toSampleTarget.v1 : Polynomial (F p)) *
      (Polynomial.X : Polynomial (F p)) + (Polynomial.C sa.toSampleTarget.v0 : Polynomial (F p))
  hsuppAnchor : ∀ P, P ∉ as_Sanchor → ordAt (H := H) P (-as_va) 1 = 0
  hmemAnchor : (divToPair (H := H) (-as_va) 1 as_Sanchor -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H
  hAlphaRep : sa.alpha • aClass =
      toJacobian D (Subtype.mk (divToPair (H := H) (-as_va) 1 as_Sanchor -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmemAnchor)
  hsupp : ∀ P, P ∉ as_S → ordAt (H := H) P (-as_v) 1 = 0
  hSmem : ∀ P ∈ as_S, as_u.eval P.X = 0 ∧ P.Y = as_v.eval P.X
  hufree : Squarefree as_u
  hScard : as_S.card = as_u.natDegree
  as_ua : Polynomial (F p)
  hua : as_ua = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C as_coeffs.coeff_ua1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C as_coeffs.coeff_ua0 : Polynomial (F p))
  hSanchorMem : ∀ P ∈ as_Sanchor, as_ua.eval P.X = 0 ∧ P.Y = as_va.eval P.X
  huafree : Squarefree as_ua
  hSanchorCard : as_Sanchor.card = as_ua.natDegree
  hmem : (divToPair (H := H) (-as_v) 1 as_S -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H
  as_q : Jacobian H D
  hq : as_q = toJacobian D (Subtype.mk (single (Point.iota δ₀) - single δ₀ : Divisor H)
      (single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀))
  as_Ra1 : H.Point
  as_Ra2 : H.Point
  hRa12Xne : as_Ra1.X ≠ as_Ra2.X
  hRa1Root : as_ua.IsRoot as_Ra1.X
  hRa2Root : as_ua.IsRoot as_Ra2.X
  hRa1Y : as_Ra1.Y = as_va.eval as_Ra1.X
  hRa2Y : as_Ra2.Y = as_va.eval as_Ra2.X
  as_T1 : H.Point
  as_T2 : H.Point
  hT12Xne : as_T1.X ≠ as_T2.X
  hT1Root : as_u.IsRoot as_T1.X
  hT2Root : as_u.IsRoot as_T2.X
  hT1Y : as_T1.Y = as_v.eval as_T1.X
  hT2Y : as_T2.Y = as_v.eval as_T2.X
  hchar : (2 : F p) ≠ 0
  hsf : Squarefree H.f
  as_Uco : Polynomial (F p)
  as_UcoT : Polynomial (F p)
  hAU : pairNorm H (-as_va) (1 : Polynomial (F p)) = as_ua * as_Uco
  hUco_ne : as_Uco ≠ 0
  hUco_evalRa1 : as_Uco.eval as_Ra1.X ≠ 0
  hUco_evalRa2 : as_Uco.eval as_Ra2.X ≠ 0
  hAUT : pairNorm H (-as_v) (1 : Polynomial (F p)) = as_u * as_UcoT
  hUcoT_ne : as_UcoT ≠ 0
  hUcoT_evalT1 : as_UcoT.eval as_T1.X ≠ 0
  hUcoT_evalT2 : as_UcoT.eval as_T2.X ≠ 0
  hRa1Y_ne : as_Ra1.Y ≠ 0
  hRa2Y_ne : as_Ra2.Y ≠ 0
  hT1Y_ne : as_T1.Y ≠ 0
  hT2Y_ne : as_T2.Y ≠ 0
  hdet : (caInterpMatrix as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X).det ≠ 0
  hlead : caCoeff as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y 3 ≠ 0
  h1P1 : as_Ra1.X ≠ sa.P1.X
  h1P2 : as_Ra1.X ≠ sa.P2.X
  h2P1 : as_Ra2.X ≠ sa.P1.X
  h2P2 : as_Ra2.X ≠ sa.P2.X
  hPP : sa.P1.X ≠ sa.P2.X
  hRa1_curve : as_Ra1.Y ^ 2 = H.f.eval as_Ra1.X
  hRa2_curve : as_Ra2.Y ^ 2 = H.f.eval as_Ra2.X
  hP1_curve : sa.P1.Y ^ 2 = H.f.eval sa.P1.X
  hP2_curve : sa.P2.Y ^ 2 = H.f.eval sa.P2.X
  hP1Y_ne : sa.P1.Y ≠ 0
  hP2Y_ne : sa.P2.Y ≠ 0
  hU_evalRa1 :
      (uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).eval as_Ra1.X ≠ 0
  hU_evalRa2 :
      (uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).eval as_Ra2.X ≠ 0
  hU_evalP1 :
      (uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).eval sa.P1.X ≠ 0
  hU_evalP2 :
      (uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).eval sa.P2.X ≠ 0
  hU_ne0 : uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y ≠ 0
  as_PtT1 : H.Point
  as_PtT2 : H.Point
  hPtT1X : as_PtT1.X ≠ as_PtT2.X
  hPtT1 :
      (uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).IsRoot as_PtT1.X
  hPtT2 :
      (uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).IsRoot as_PtT2.X
  as_Q1 : Polynomial (F p)
  as_Q2 : Polynomial (F p)
  hQ1_def : uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y =
      (Polynomial.X - Polynomial.C as_PtT1.X) * (Polynomial.X - Polynomial.C as_PtT2.X) * as_Q1
  hQ1T1 : as_Q1.eval as_PtT1.X ≠ 0
  hQ2_def : uCANew H as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y =
      (Polynomial.X - Polynomial.C as_PtT2.X) * (Polynomial.X - Polynomial.C as_PtT1.X) * as_Q2
  hQ2T2 : as_Q2.eval as_PtT2.X ≠ 0
  hAeval1 : (denomPolyCA as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X : Polynomial (F p)).eval as_PtT1.X ≠ 0
  hAeval2 : (denomPolyCA as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X : Polynomial (F p)).eval as_PtT2.X ≠ 0
  hPtT1Y :
      as_PtT1.Y = (bCA as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).eval as_PtT1.X
  hPtT1Y_ne : as_PtT1.Y ≠ 0
  hPtT2Y :
      as_PtT2.Y = (bCA as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y).eval as_PtT2.X
  hPtT2Y_ne : as_PtT2.Y ≠ 0
  h1δ : as_PtT1.X ≠ δ₀.X
  h2δ : as_PtT2.X ≠ δ₀.X
  hδY : δ₀.Y ≠ 0
  hT1eq : as_T1 = Point.iota as_PtT1
  hT2eq : as_T2 = Point.iota as_PtT2
  hsupp_f : ∀ P, P ∉ ({as_Ra1, as_Ra2, Point.iota sa.P1, Point.iota sa.P2, as_PtT1, as_PtT2} :
      Finset H.Point) →
    ordAt P (-bCA as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y)
      (1 : Polynomial (F p)) = 0
  hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
    (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
      ({toPair H (-bCA as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y) 1} :
        Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P
  [hspec_f_finite : ∀ P : ({as_Ra1, as_Ra2, Point.iota sa.P1, Point.iota sa.P2, as_PtT1, as_PtT2} :
      Finset H.Point),
    Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
      (ordAt P.1 (-bCA as_Ra1.X as_Ra2.X sa.P1.X sa.P2.X as_Ra1.Y as_Ra2.Y sa.P1.Y sa.P2.Y)
        (1 : Polynomial (F p))).toNat)]
  hsupp_hT : ∀ P, P ∉ ({as_PtT1, as_PtT2, Point.iota as_PtT1, Point.iota as_PtT2, δ₀,
      Point.iota δ₀} : Finset H.Point) →
    ordAt P ((linX as_PtT1.X * linX as_PtT2.X) * linX δ₀.X) (0 : Polynomial (F p)) = 0
  hspec_hT : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
    (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
      ({toPair H ((linX as_PtT1.X * linX as_PtT2.X) * linX δ₀.X) 0} :
        Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P
  [hspec_hT_finite : ∀ P : ({as_PtT1, as_PtT2, Point.iota as_PtT1, Point.iota as_PtT2, δ₀,
      Point.iota δ₀} : Finset H.Point),
    Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
      (ordAt P.1 ((linX as_PtT1.X * linX as_PtT2.X) * linX δ₀.X)
        (0 : Polynomial (F p))).toNat)]
  [hspec_linX_finite : ∀ (a : F p) (Sfin : Finset H.Point),
    ∀ P : Sfin, Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
  hspec_linX : ∀ (a : F p), ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
    (Associates.mk vv.asIdeal).count
      (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
        ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P

/-- **The base (fully split) theorem, bundled.** `ROADMAP-reducedClass-
dispatcher.md`, "Suggested order" step 3: relocated here from
`AlphaLocusDegreeUniform.lean` (see that file's module docstring, the
note right before its own "Task (B)" section, for why the move was
necessary rather than optional — that file cannot import
`SplitAssemblyData` back from here without creating an import cycle,
since this file already imports it for `SampleTargetFromAlpha`. -/
theorem reducedClass_eq_of_isReduction' {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    -- **Bundled this pass** (`ROADMAP-reducedClass-dispatcher.md`,
    -- "Suggested order" step 3): the ~100-hypothesis flat signature this
    -- theorem used to carry is now the two `ReducedClassBundles.lean`
    -- structures `base`/`d`, mirroring `_tangent`'s existing
    -- `(base : TangentReductionData sa) (d : TangentAssemblyData sa)`
    -- shape exactly. `hcoeff` bridges `d`'s own coefficient view to
    -- `base`'s, the same role it plays in `_tangent`'s signature.
    (base : ReductionData sa)
    (d : SplitAssemblyData sa)
    (hcoeff : d.as_coeffs = base.coeffs)
    (u0 u1 v0 v1 : F p)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
        d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
        u0 u1 v0 v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          u0 u1 v0 v1)
        (uRS4General p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
          d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          u0 u1 v0 v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
        d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
        sa.P1.X sa.P1.Y
        d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
        u0 u1 v0 v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
          d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          u0 u1 v0 v1)
        (uRS4Tangent p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
          d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          u0 u1 v0 v1))
    (hr : isReduction' sa d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
      d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
      d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
      u0 u1 v0 v1 hcur hgcd hcurT hgcdT)
    (hdeg : H.f.natDegree = 5)
    (hD : principalSubgroup H hdeg ≤ D.P) :
    sa.reducedClass + d.as_q =
      toJacobian D (Subtype.mk (divToPair (H := H) (-d.as_v) 1 d.as_S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) d.hmem) := by
  classical
  -- **`Sanchor`'s own split, correctly**: `d.as_Sanchor = {d.as_Ra1, d.as_Ra2}`
  -- (`Sanchor`'s own two named points), NOT `{sa.P1, sa.P2}`. Same
  -- `Sanchor_eq_of_anchor_roots` lemma as before, but instantiated at
  -- `d.as_Ra1,d.as_Ra2` (fresh points naming `Sanchor`'s own roots) instead
  -- of `sa.P1,sa.P2` (a different, independently-existing pair).
  have hRa12ne : d.as_Ra1 ≠ d.as_Ra2 := fun h => d.hRa12Xne (by rw [h])
  have hSanchorEq : d.as_Sanchor = ({d.as_Ra1, d.as_Ra2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots d.as_ua d.as_va d.hua d.huafree
      d.as_Ra1 d.as_Ra2 hRa12ne d.hRa12Xne ⟨d.hRa1Root, d.hRa2Root⟩ d.hRa1Y d.hRa2Y d.as_Sanchor
      d.hSanchorMem d.hSanchorCard
  -- **`S`'s own split**, same lemma applied to `u`/`v`/`S`/`T1`/`T2`.
  have hT12ne : d.as_T1 ≠ d.as_T2 := fun h => d.hT12Xne (by rw [h])
  have hSEq : d.as_S = ({d.as_T1, d.as_T2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots (ua0 := sa.toSampleTarget.u0) (ua1 := sa.toSampleTarget.u1)
      d.as_u d.as_v d.hu d.hufree
      d.as_T1 d.as_T2 hT12ne d.hT12Xne ⟨d.hT1Root, d.hT2Root⟩ d.hT1Y d.hT2Y d.as_S
      d.hSmem d.hScard
  -- **Collapse `divToPair (-va) 1 Sanchor` and `divToPair (-v) 1 S`** to
  -- the concrete two-point sums, via `PrincipalWitnessCAConnection.lean`.
  -- `d.huafree`/`d.hufree` have type `Squarefree d.as_ua`/`Squarefree
  -- d.as_u`; the callees below want `Squarefree (X^2+C ua1*X+C ua0)`/the
  -- `u` mirror — the same polynomial via `d.hua`/`d.hu`, but not
  -- syntactically, so rewrite the root hypotheses before passing them to
  -- the connection lemmas.
  have huafree' : Squarefree (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
      + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) := d.hua ▸ d.huafree
  have hufree' : Squarefree (Polynomial.X ^ 2 +
      Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
      + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) := d.hu ▸ d.hufree
  -- `d.hAU`/`d.hAUT` are stated against `d.as_ua`/`d.as_u` (this bundle's
  -- own named polynomials); the callees below want the spelled-out
  -- quadratic `X^2+C ua1*X+C ua0`/the `u` mirror — same object via
  -- `d.hua`/`d.hu`, not syntactically, so rewrite here too (same pattern
  -- as `huafree'`/`hufree'` just above).
  have hRa1Root' :
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
        + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)).IsRoot d.as_Ra1.X := by
    rw [← d.hua]
    exact d.hRa1Root
  have hRa2Root' :
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
        + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)).IsRoot d.as_Ra2.X := by
    rw [← d.hua]
    exact d.hRa2Root
  have hT1Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot d.as_T1.X := by
    rw [← d.hu]
    exact d.hT1Root
  have hT2Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot d.as_T2.X := by
    rw [← d.hu]
    exact d.hT2Root
  have hAU' : pairNorm H (-d.as_va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
        + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) * d.as_Uco :=
    d.hua ▸ d.hAU
  have hAUT' : pairNorm H (-d.as_v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
        + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) * d.as_UcoT :=
    d.hu ▸ d.hAUT
  have hSanchorSum : divToPair (H := H) (-d.as_va) 1 d.as_Sanchor
      = single d.as_Ra1 + single d.as_Ra2 :=
    DecoupledSystem.divToPair_negVa_one_Sanchor_eq (H := H) d.hchar
      (c0 := d.as_coeffs.coeff_c0) (c1 := d.as_coeffs.coeff_c1) (c2 := d.as_coeffs.coeff_c2)
      (c3 := d.as_coeffs.coeff_c3) (c4 := d.as_coeffs.coeff_c4)
      (ua0 := d.as_coeffs.coeff_ua0) (ua1 := d.as_coeffs.coeff_ua1)
      (va0 := d.as_coeffs.coeff_va0) (va1 := d.as_coeffs.coeff_va1)
      d.as_coeffs.coeff_hf d.as_coeffs.coeff_hMumfordUa huafree' d.as_va d.hva d.as_Uco hAU'
      d.hUco_ne
      d.as_Ra1 d.as_Ra2 hRa12ne d.hRa1Y_ne d.hRa2Y_ne hRa1Root' hRa2Root' d.hRa1Y d.hRa2Y
      d.hUco_evalRa1 d.hUco_evalRa2 d.as_Sanchor hSanchorEq
  have hSSum : divToPair (H := H) (-d.as_v) 1 d.as_S = single d.as_T1 + single d.as_T2 :=
    DecoupledSystem.divToPair_negV_one_S_eq (H := H) d.hchar
      (c0 := d.as_coeffs.coeff_c0) (c1 := d.as_coeffs.coeff_c1) (c2 := d.as_coeffs.coeff_c2)
      (c3 := d.as_coeffs.coeff_c3) (c4 := d.as_coeffs.coeff_c4)
      (u0 := sa.toSampleTarget.u0) (u1 := sa.toSampleTarget.u1)
      (v0 := sa.toSampleTarget.v0) (v1 := sa.toSampleTarget.v1)
      d.as_coeffs.coeff_hf d.as_coeffs.coeff_hMumfordTarget hufree' d.as_v d.hv d.as_UcoT hAUT'
      d.hUcoT_ne
      d.as_T1 d.as_T2 hT12ne d.hT1Y_ne d.hT2Y_ne hT1Root' hT2Root' d.hT1Y d.hT2Y
      d.hUcoT_evalT1 d.hUcoT_evalT2 d.as_S hSEq
  -- **The concrete-coordinate assembly (†)**: `C - A - ι(T) + [δ₀] + [ιδ₀]
  -- ∈ D.P`, `C := {d.as_Ra1,d.as_Ra2}`, `A := {sa.P1,sa.P2}`, instantiated
  -- at the actual named points. `T1cur T2cur := d.as_T1 d.as_T2` via
  -- `d.hT1eq`/`d.hT2eq` (`S := ι(T)` convention). `d.hspec_linX` is the
  -- explicit arg right after `hD`. The `Module.Finite` instance-implicit
  -- bracket right before it is NOT auto-resolved from `d`'s own instance
  -- fields — `d.hspec_linX_finite` is a plain structure PROJECTION, and
  -- instance search does not look inside arbitrary projections to find
  -- it, so it must be registered as a local instance explicitly first.
  haveI := d.hspec_linX_finite
  haveI := d.hspec_f_finite
  haveI := d.hspec_hT_finite
  have hDP := cAmιTmδmιδ_mem_of_le (H := H) hdeg d.hchar d.hsf D hD
    d.hspec_linX
    d.as_Ra1.X d.as_Ra2.X sa.P1.X sa.P2.X d.as_Ra1.Y d.as_Ra2.Y sa.P1.Y sa.P2.Y
    d.hdet d.hlead d.hRa12Xne d.h1P1 d.h1P2 d.h2P1 d.h2P2 d.hPP
    d.hRa1_curve d.hRa2_curve d.hP1_curve d.hP2_curve
    d.hRa1Y_ne d.hRa2Y_ne d.hP1Y_ne d.hP2Y_ne
    d.as_Ra1 d.as_Ra2 sa.P1 sa.P2 (Point.iota sa.P1) (Point.iota sa.P2)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    d.hU_evalRa1 d.hU_evalRa2 d.hU_evalP1 d.hU_evalP2 d.hU_ne0
    d.as_PtT1.X d.as_PtT2.X d.hPtT1 d.hPtT2 d.hPtT1X
    d.as_Q1 d.as_Q2 d.hQ1_def d.hQ1T1 d.hQ2_def d.hQ2T2
    d.as_PtT1 d.as_PtT2 δ₀ d.hAeval1 d.hAeval2 rfl d.hPtT1Y d.hPtT1Y_ne rfl d.hPtT2Y d.hPtT2Y_ne
    d.h1δ d.h2δ d.hδY d.hsupp_f d.hspec_f d.hsupp_hT d.hspec_hT
    d.as_T1 d.as_T2 d.hT1eq d.hT2eq
  -- **Bridge `D.P` membership to a `toJacobian` equation**, exactly the
  -- `s_add_s_eq_s_add_s_iff` pattern (`DivisorClassGroup.lean`), applied to
  -- the concrete divisor `hDP` supplies rather than re-derived generically.
  -- `sa.reducedClass + d.as_q - toJacobian D aTarget`, unfolded all the way
  -- to `Divisor0 H` representatives, is EXACTLY `hDP`'s divisor — so this
  -- is a single `abel`-after-unfolding argument, not a multi-step
  -- `set`/`map_sub` composition.
  set aAnchor : Divisor0 H := ⟨divToPair (H := H) (-d.as_va) 1 d.as_Sanchor -
    (single δ₀ + single (Point.iota δ₀)), d.hmemAnchor⟩ with haAnchor_def
  set aTarget : Divisor0 H := ⟨divToPair (H := H) (-d.as_v) 1 d.as_S -
    (single δ₀ + single (Point.iota δ₀)), d.hmem⟩ with haTarget_def
  set aP1P2Nι : Divisor0 H := ⟨single sa.P1 + single sa.P2 -
      (single δ₀ + single (Point.iota δ₀)),
    by
      have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
      have h2 := single_sub_single_mem_Divisor0 sa.P2 (Point.iota δ₀)
      have heq2 : single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀)) =
          (single sa.P1 - single δ₀) + (single sa.P2 - single (Point.iota δ₀)) := by abel
      rw [heq2]; exact add_mem h1 h2⟩ with haP1P2Nι_def
  set aQ : Divisor0 H := ⟨single (Point.iota δ₀) - single δ₀,
    single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀⟩ with haQ_def
  -- `reducedClass`'s `N₂({P1,P2})` term equals `Nι({P1,P2}) + d.as_q` at
  -- the `Divisor0 H` level. **Proved via `Subtype.ext`/`congrArg` on the
  -- underlying divisor value, NOT `show`-matching the whole term** — an
  -- earlier draft tried to `show` the RHS of `sa.reducedClass`'s
  -- definitional unfolding verbatim and failed: the `Subtype.mk` proof
  -- component built inline differs syntactically from `reducedClass`'s
  -- own stored proof term, and `show` needs full syntactic (up to defeq)
  -- reconstruction of BOTH components, not just the value, so it never
  -- matched. Proof irrelevance makes the two proof terms interchangeable
  -- for `Jacobian`-level equality, but reaching that needs `Subtype.ext`
  -- (which only asks the VALUES to agree) rather than a raw `show`.
  have hred : sa.reducedClass = sa.alpha • aClass - (toJacobian D aP1P2Nι + d.as_q) := by
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
        (aP1P2Nι : Divisor H) + (aQ : Divisor H)
      rw [haP1P2Nι_def, haQ_def]
      show single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) +
          (single (Point.iota δ₀) - single δ₀)
      rw [two_zsmul]
      abel
    rw [base.hReducedClass, hN2, map_add, d.hq]
  rw [hred, d.hAlphaRep]
  -- Goal now: `toJacobian D aAnchor - (toJacobian D aP1P2Nι + d.as_q) +
  -- d.as_q = toJacobian D aTarget`, which simplifies (the two `d.as_q`s
  -- cancel) to `toJacobian D aAnchor - toJacobian D aP1P2Nι = toJacobian D
  -- aTarget`, i.e. `toJacobian D (aAnchor - aP1P2Nι - aTarget) = 0`, i.e.
  -- `aAnchor - aP1P2Nι - aTarget ∈ D.P` (as `Divisor0 H` mod `D.P`) —
  -- exactly `hDP` once `hSanchorSum`/`hSSum` unfold the `divToPair` terms.
  have hcancel : toJacobian D aAnchor - (toJacobian D aP1P2Nι + d.as_q) + d.as_q =
      toJacobian D aAnchor - toJacobian D aP1P2Nι := by abel
  have hcoe : ((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H) =
      (single d.as_Ra1 + single d.as_Ra2 - single sa.P1 - single sa.P2 -
        single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    show (aAnchor.1 - aP1P2Nι.1) - aTarget.1 =
      single d.as_Ra1 + single d.as_Ra2 - single sa.P1 - single sa.P2 -
        single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀)
    rw [haAnchor_def, haP1P2Nι_def, haTarget_def]
    show (divToPair (H := H) (-d.as_va) 1 d.as_Sanchor
          - (single δ₀ + single (Point.iota δ₀))) -
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) -
        (divToPair (H := H) (-d.as_v) 1 d.as_S - (single δ₀ + single (Point.iota δ₀))) =
      single d.as_Ra1 + single d.as_Ra2 - single sa.P1 - single sa.P2 -
        single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀)
    rw [hSanchorSum, hSSum]
    abel
  have hmemD : (((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H)) ∈ D.P := by
    rw [hcoe]; exact hDP
  have hmemD' : (((aAnchor - aP1P2Nι - aTarget : Divisor0 H)) : Divisor H) ∈ D.P := by
    have hval : (((aAnchor - aP1P2Nι - aTarget : Divisor0 H)) : Divisor H) =
        (((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
          ((aTarget : Divisor0 H) : Divisor H)) := by
      show aAnchor.1 - aP1P2Nι.1 - aTarget.1 = (aAnchor.1 - aP1P2Nι.1) - aTarget.1
      rfl
    rw [hval]; exact hmemD
  have hmemAddSub : (aAnchor - aP1P2Nι - aTarget : Divisor0 H) ∈
      D.P.addSubgroupOf (Divisor0 H) := by
    rw [AddSubgroup.mem_addSubgroupOf]; exact hmemD'
  have hJeq := (QuotientAddGroup.eq_iff_sub_mem
    (N := D.P.addSubgroupOf (Divisor0 H))).mpr hmemAddSub
  rw [hcancel, ← map_sub]
  change
    QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H)) (aAnchor - aP1P2Nι) =
      QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H)) aTarget
  exact hJeq

end DecoupledSystem
end Genus2Lean
