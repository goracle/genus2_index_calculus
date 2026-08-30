import Mathlib
import Genus2Lean.ZeroD.ReducedClassBundles
import Genus2Lean.ZeroD.AlphaLocusDegreeUniformCross3
import Genus2Lean.ZeroD.CAWitnessCrossTangentMemOfLe

/-! # `Cross3AssemblyData` bundle for `reducedClass_eq_of_isReduction'_cross3`

`ROADMAP-reducedClass-dispatcher.md`, "Suggested order" step 3, continued
to the cross variants: same shape as `ReducedClassBundles.lean`'s
`SplitAssemblyData`, reusing the shared `CoefficientData`/`ReductionData`
from that file, with the construction-specific tier swapped for
`AlphaLocusDegreeUniformCross3.lean`'s own four itemized differences
(module docstring there, read directly rather than assumed):

1. `sa.P2` is no longer a free point in the CA-witness-facing block — it
   is forced to `Point.iota Ra` via `hP1eq` (note: named for `sa.P1`,
   since the theorem's `hReducedClass`/`isReduction'` machinery keeps
   `sa.P1` fully free; it is `sa.P2` that collides with the anchor here),
   so `Cross3AssemblyData` has no free `sa.P2`-as-anchor-point the way
   `SplitAssemblyData` does; the anchor pair is named `as_Ra1`/`as_Ra`
   (matching the source file's own `Ra1`/`Ra` naming — the doubled point
   is `Ra`, unprimed, in the SECOND anchor slot, opposite of `Cross1`).
2. `caCross3InterpMatrix`/`caCross3Coeff`/`bCACross3`/`uCANewCross3`/
   `denomPolyCACross3` (three free points `Ra1X,RaX,P2X` plus derivative
   datum `vDerivAtP1`) replace the four-free-point split machinery.
3. `h1P1,h1P2,h2P1,h2P2,hPP` collapse to the three-hypothesis family
   `h1,h2,h3` (`Ra1X≠RaX`, `Ra1X≠P2X`, `RaX≠P2X`).
4. `hP2_curve`/`hP2Y_ne` (facts about the now-gone free `sa.P2`) are
   derived from `hRa_curve`/`hRaY_ne` via `Point.iota_X`/`Point.iota_Y`
   in the source theorem's proof, rather than taken as independent
   hypotheses; `hP1Deriv` (the derivative datum's defining equation)
   is the new independent hypothesis in their place.

`ReductionData`/`CoefficientData` are unchanged — reused directly from
`ReducedClassBundles.lean`, per that file's own confirmation these two
layers are identical across all seven variants. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

-- Bumped: this structure has ~55 fields with deeply nested dependent
-- types (uCANewCross3/bCACross3/caCross3InterpMatrix applications repeated
-- across many fields); elaborating the full field list exceeds the
-- default 200000-heartbeat budget even though no single field is
-- individually expensive (same root cause as ReducedClassBundles.lean's
-- SplitAssemblyData, which needed the identical bump).
set_option maxHeartbeats 1000000 in
/-- **Construction-specific assembly layer for the cross3
(`sa.P1 = ι(Ra)`) `reducedClass_eq_of_isReduction'_cross3` theorem.**
Mirrors `SplitAssemblyData` field-for-field where the two theorems'
hypothesis lists line up (`Sanchor,S,va,u,v`/target-side machinery is
identical, per that theorem's own docstring); the anchor/CA-witness tier
is replaced per the module docstring's itemized diff above. -/
structure Cross3AssemblyData
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
  -- **Anchor pair — `Ra1`/`Ra`, genuinely split (item 1/2 of the module
  -- docstring's diff): `sa.P2` is NOT a free point here, it is forced to
  -- `Point.iota as_Ra` by `hP1eq` below.**
  as_Ra1 : H.Point
  as_Ra : H.Point
  hRa12Xne : as_Ra1.X ≠ as_Ra.X
  hRa1Root : as_ua.IsRoot as_Ra1.X
  hRaRoot : as_ua.IsRoot as_Ra.X
  hRa1Y : as_Ra1.Y = as_va.eval as_Ra1.X
  hRaY : as_Ra.Y = as_va.eval as_Ra.X
  hP1eq : sa.P1 = Point.iota as_Ra
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
  hUco_evalRa : as_Uco.eval as_Ra.X ≠ 0
  hAUT : pairNorm H (-as_v) (1 : Polynomial (F p)) = as_u * as_UcoT
  hUcoT_ne : as_UcoT ≠ 0
  hUcoT_evalT1 : as_UcoT.eval as_T1.X ≠ 0
  hUcoT_evalT2 : as_UcoT.eval as_T2.X ≠ 0
  hRa1Y_ne : as_Ra1.Y ≠ 0
  hRaY_ne : as_Ra.Y ≠ 0
  hT1Y_ne : as_T1.Y ≠ 0
  hT2Y_ne : as_T2.Y ≠ 0
  -- **The cross3 `CAWitness` construction (item 2 of the diff)**: three
  -- free points `as_Ra1.X,as_Ra.X,sa.P2.X` plus `vDerivAtP1`, replacing
  -- `caInterpMatrix`/`uCANew`/`bCA`/`denomPolyCA`'s four-free-point forms.
  as_vDerivAtP1 : F p
  hdet : (caCross3InterpMatrix as_Ra1.X as_Ra.X sa.P2.X).det ≠ 0
  hlead : caCross3Coeff as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y 3 ≠ 0
  h1 : as_Ra1.X ≠ as_Ra.X
  h2 : as_Ra1.X ≠ sa.P2.X
  h3 : as_Ra.X ≠ sa.P2.X
  hRa1_curve : as_Ra1.Y ^ 2 = H.f.eval as_Ra1.X
  hRa_curve : as_Ra.Y ^ 2 = H.f.eval as_Ra.X
  hP2_curve : sa.P2.Y ^ 2 = H.f.eval sa.P2.X
  hP1Deriv : 2 * as_Ra.Y * (-as_vDerivAtP1) = (derivative H.f).eval as_Ra.X
  hP2Y_ne : sa.P2.Y ≠ 0
  hne : H.f - (bCACross3 as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y) ^ 2 ≠ 0
  hU_evalRa :
      (uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y).eval as_Ra.X ≠ 0
  hU_evalRa1 :
      (uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y).eval as_Ra1.X ≠ 0
  hU_evalP2 :
      (uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y).eval sa.P2.X ≠ 0
  hU_ne0 : uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y ≠ 0
  as_PtT1 : H.Point
  as_PtT2 : H.Point
  hPtT1X : as_PtT1.X ≠ as_PtT2.X
  hPtT1 :
      (uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y).IsRoot as_PtT1.X
  hPtT2 :
      (uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y).IsRoot as_PtT2.X
  as_Q1 : Polynomial (F p)
  as_Q2 : Polynomial (F p)
  hQ1_def : uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y =
      (Polynomial.X - Polynomial.C as_PtT1.X) * (Polynomial.X - Polynomial.C as_PtT2.X) * as_Q1
  hQ1T1 : as_Q1.eval as_PtT1.X ≠ 0
  hQ2_def : uCANewCross3 H as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y =
      (Polynomial.X - Polynomial.C as_PtT2.X) * (Polynomial.X - Polynomial.C as_PtT1.X) * as_Q2
  hQ2T2 : as_Q2.eval as_PtT2.X ≠ 0
  hAeval1 : (denomPolyCACross3 as_Ra1.X as_Ra.X sa.P2.X : Polynomial (F p)).eval as_PtT1.X ≠ 0
  hAeval2 : (denomPolyCACross3 as_Ra1.X as_Ra.X sa.P2.X : Polynomial (F p)).eval as_PtT2.X ≠ 0
  hPtT1Y :
      as_PtT1.Y = (bCACross3 as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y).eval as_PtT1.X
  hPtT1Y_ne : as_PtT1.Y ≠ 0
  hPtT2Y :
      as_PtT2.Y = (bCACross3 as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y).eval as_PtT2.X
  hPtT2Y_ne : as_PtT2.Y ≠ 0
  hRaT1 : as_Ra.X ≠ as_PtT1.X
  hRaT2 : as_Ra.X ≠ as_PtT2.X
  hRa1T1 : as_Ra1.X ≠ as_PtT1.X
  hRa1T2 : as_Ra1.X ≠ as_PtT2.X
  hP2T1 : sa.P2.X ≠ as_PtT1.X
  hP2T2 : sa.P2.X ≠ as_PtT2.X
  h1δ : as_PtT1.X ≠ δ₀.X
  h2δ : as_PtT2.X ≠ δ₀.X
  hδY : δ₀.Y ≠ 0
  hT1eq : as_T1 = Point.iota as_PtT1
  hT2eq : as_T2 = Point.iota as_PtT2
  hsupp_f : ∀ P, P ∉ ({as_Ra1, as_Ra, Point.iota sa.P2, as_PtT1, as_PtT2} :
      Finset H.Point) →
    ordAt P (-bCACross3 as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y)
      (1 : Polynomial (F p)) = 0
  hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
    (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
      ({toPair H (-bCACross3 as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y) 1} :
        Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P
  [hspec_f_finite : ∀ P : ({as_Ra1, as_Ra, Point.iota sa.P2, as_PtT1, as_PtT2} : Finset H.Point),
    Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
      (ordAt P.1 (-bCACross3 as_Ra1.X as_Ra.X sa.P2.X as_Ra1.Y as_Ra.Y as_vDerivAtP1 sa.P2.Y)
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
    ∀ P : Sfin, Module.Finite (F p) (CoordinateRing H ⧸
      pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
  hspec_linX : ∀ (a : F p), ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
    (Associates.mk vv.asIdeal).count
      (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
        ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P

-- Bumped for the same reason as Cross3AssemblyData above: the proof
-- body threads ~90 hypothesis/field references through several
-- multi-argument callee applications (cAmιTmδmιδ_mem_of_le_cross3 alone
-- takes 76 explicit args), and the cumulative elaboration cost exceeds
-- the default budget even though no single step is individually slow.
set_option maxHeartbeats 1000000 in
/-- **Cross3 theorem, bundled.** Mirrors `ReducedClassBundles.lean`'s
bundled base theorem, taking `(base : ReductionData sa) (d :
Cross3AssemblyData sa)` instead of the ~90-hypothesis flat signature.
Proof body is `AlphaLocusDegreeUniformCross3.lean`'s original proof with
every free variable replaced by its `d.`-projection, `hP1eq` handled
identically via `d.hP1eq` at the same point in the argument. -/
theorem reducedClass_eq_of_isReduction'_cross3 {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (base : ReductionData sa)
    (d : Cross3AssemblyData sa)
    (hcoeff : d.as_coeffs = base.coeffs)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
        d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
          d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
        d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
        sa.P1.X sa.P1.Y
        d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
          d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
          d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hr : isReduction' sa d.as_coeffs.coeff_c0 d.as_coeffs.coeff_c1 d.as_coeffs.coeff_c2
      d.as_coeffs.coeff_c3 d.as_coeffs.coeff_c4
      d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1 d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1
      hcur hgcd hcurT hgcdT)
    (hdeg : H.f.natDegree = 5)
    (hD : principalSubgroup H hdeg ≤ D.P) :
    sa.reducedClass + d.as_q =
      toJacobian D (Subtype.mk (divToPair (H := H) (-d.as_v) 1 d.as_S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) d.hmem) := by
  classical
  have hRa12ne : d.as_Ra1 ≠ d.as_Ra := fun h => d.hRa12Xne (by rw [h])
  have hSanchorEq : d.as_Sanchor = ({d.as_Ra1, d.as_Ra} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots d.as_ua d.as_va d.hua d.huafree
      d.as_Ra1 d.as_Ra hRa12ne d.hRa12Xne ⟨d.hRa1Root, d.hRaRoot⟩ d.hRa1Y d.hRaY d.as_Sanchor
      d.hSanchorMem d.hSanchorCard
  have hT12ne : d.as_T1 ≠ d.as_T2 := fun h => d.hT12Xne (by rw [h])
  have hSEq : d.as_S = ({d.as_T1, d.as_T2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots (ua0 := sa.toSampleTarget.u0) (ua1 := sa.toSampleTarget.u1)
      d.as_u d.as_v d.hu d.hufree
      d.as_T1 d.as_T2 hT12ne d.hT12Xne ⟨d.hT1Root, d.hT2Root⟩ d.hT1Y d.hT2Y d.as_S
      d.hSmem d.hScard
  have huafree' : Squarefree (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
      + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) := d.hua ▸ d.huafree
  have hufree' : Squarefree (Polynomial.X ^ 2 +
      Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
      + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) := d.hu ▸ d.hufree
  have hRaRoot' :
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
        + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)).IsRoot d.as_Ra.X := by
    rw [← d.hua]; exact d.hRaRoot
  have hRa1Root' :
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
        + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)).IsRoot d.as_Ra1.X := by
    rw [← d.hua]; exact d.hRa1Root
  have hT1Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot d.as_T1.X := by
    rw [← d.hu]; exact d.hT1Root
  have hT2Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot d.as_T2.X := by
    rw [← d.hu]; exact d.hT2Root
  have hAU' : pairNorm H (-d.as_va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X
        + Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) * d.as_Uco :=
    d.hua ▸ d.hAU
  have hAUT' : pairNorm H (-d.as_v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
        + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) * d.as_UcoT :=
    d.hu ▸ d.hAUT
  have hSanchorSum : divToPair (H := H) (-d.as_va) 1 d.as_Sanchor
      = single d.as_Ra + single d.as_Ra1 :=
    DecoupledSystem.divToPair_negVa_one_Sanchor_eq (H := H) d.hchar
      (c0 := d.as_coeffs.coeff_c0) (c1 := d.as_coeffs.coeff_c1) (c2 := d.as_coeffs.coeff_c2)
      (c3 := d.as_coeffs.coeff_c3) (c4 := d.as_coeffs.coeff_c4)
      (ua0 := d.as_coeffs.coeff_ua0) (ua1 := d.as_coeffs.coeff_ua1)
      (va0 := d.as_coeffs.coeff_va0) (va1 := d.as_coeffs.coeff_va1)
      d.as_coeffs.coeff_hf d.as_coeffs.coeff_hMumfordUa huafree' d.as_va d.hva d.as_Uco hAU'
      d.hUco_ne
      d.as_Ra1 d.as_Ra hRa12ne d.hRa1Y_ne d.hRaY_ne hRa1Root' hRaRoot' d.hRa1Y d.hRaY
      d.hUco_evalRa1 d.hUco_evalRa d.as_Sanchor hSanchorEq
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
  haveI := d.hspec_linX_finite
  haveI := d.hspec_f_finite
  haveI := d.hspec_hT_finite
  have hDP := cAmιTmδmιδ_mem_of_le_cross3 (H := H) hdeg d.hchar d.hsf D hD
    d.hspec_linX
    d.as_Ra1.X d.as_Ra.X sa.P2.X d.as_Ra1.Y d.as_Ra.Y d.as_vDerivAtP1 sa.P2.Y
    d.hdet d.hlead d.h1 d.h2 d.h3
    d.hRa1_curve d.hRa_curve d.hP2_curve d.hP1Deriv d.hRa1Y_ne d.hRaY_ne d.hP2Y_ne
    d.as_Ra1 d.as_Ra sa.P2 (Point.iota sa.P2)
    rfl rfl rfl rfl rfl rfl rfl rfl
    d.hne
    d.hU_evalRa1 d.hU_evalRa d.hU_evalP2 d.hU_ne0
    d.as_PtT1.X d.as_PtT2.X d.hPtT1 d.hPtT2 d.hPtT1X
    d.as_Q1 d.as_Q2 d.hQ1_def d.hQ1T1 d.hQ2_def d.hQ2T2
    d.as_PtT1 d.as_PtT2 δ₀ d.hAeval1 d.hAeval2
    rfl d.hPtT1Y d.hPtT1Y_ne rfl d.hPtT2Y d.hPtT2Y_ne
    d.hRa1T1 d.hRa1T2 d.hRaT1 d.hRaT2 d.hP2T1 d.hP2T2
    d.h1δ d.h2δ d.hδY d.hsupp_f d.hspec_f d.hsupp_hT d.hspec_hT
    d.as_T1 d.as_T2 d.hT1eq d.hT2eq
  set aAnchor : Divisor0 H := ⟨divToPair (H := H) (-d.as_va) 1 d.as_Sanchor -
    (single δ₀ + single (Point.iota δ₀)), d.hmemAnchor⟩ with haAnchor_def
  set aTarget : Divisor0 H := ⟨divToPair (H := H) (-d.as_v) 1 d.as_S -
    (single δ₀ + single (Point.iota δ₀)), d.hmem⟩ with haTarget_def
  set aP2P1Nι : Divisor0 H := ⟨single sa.P1 + single sa.P2 -
      (single δ₀ + single (Point.iota δ₀)),
    by
      have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
      have h2 := single_sub_single_mem_Divisor0 sa.P2 (Point.iota δ₀)
      have heq2 : single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀)) =
          (single sa.P1 - single δ₀) + (single sa.P2 - single (Point.iota δ₀)) := by abel
      rw [heq2]; exact add_mem h1 h2⟩ with haP2P1Nι_def
  set aQ : Divisor0 H := ⟨single (Point.iota δ₀) - single δ₀,
    single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀⟩ with haQ_def
  have hred : sa.reducedClass = sa.alpha • aClass - (toJacobian D aP2P1Nι + d.as_q) := by
    have hN2 :
        (⟨single sa.P2 + single sa.P1 - (2 : ℤ) • single δ₀,
          by
            have h1 := single_sub_single_mem_Divisor0 sa.P2 δ₀
            have h2 := single_sub_single_mem_Divisor0 sa.P1 δ₀
            have heq2 : single sa.P2 + single sa.P1 - (2 : ℤ) • single δ₀ =
                (single sa.P2 - single δ₀) + (single sa.P1 - single δ₀) := by
              rw [two_zsmul]
              abel
            rw [heq2]
            exact add_mem h1 h2⟩ : Divisor0 H) = aP2P1Nι + aQ := by
      apply Subtype.ext
      show single sa.P2 + single sa.P1 - (2 : ℤ) • single δ₀ =
        (aP2P1Nι : Divisor H) + (aQ : Divisor H)
      rw [haP2P1Nι_def, haQ_def]
      show single sa.P2 + single sa.P1 - (2 : ℤ) • single δ₀ =
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) +
          (single (Point.iota δ₀) - single δ₀)
      rw [two_zsmul]
      abel
    rw [base.hReducedClass, hN2, map_add, d.hq]
  rw [hred, d.hAlphaRep]
  have hcancel : toJacobian D aAnchor - (toJacobian D aP2P1Nι + d.as_q) + d.as_q =
      toJacobian D aAnchor - toJacobian D aP2P1Nι := by abel
  have hcoe : ((aAnchor - aP2P1Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H) =
      (single d.as_Ra + single d.as_Ra1 - single sa.P1 - single sa.P2 -
        single d.as_T1 - single d.as_T2 + single δ₀ +
        single (Point.iota δ₀) : Divisor H) := by
    show (aAnchor.1 - aP2P1Nι.1) - aTarget.1 =
      single d.as_Ra + single d.as_Ra1 - single sa.P1 - single sa.P2 -
        single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀)
    rw [haAnchor_def, haP2P1Nι_def, haTarget_def]
    show (divToPair (H := H) (-d.as_va) 1 d.as_Sanchor
          - (single δ₀ + single (Point.iota δ₀))) -
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) -
        (divToPair (H := H) (-d.as_v) 1 d.as_S - (single δ₀ + single (Point.iota δ₀))) =
      single d.as_Ra + single d.as_Ra1 - single sa.P1 - single sa.P2 -
        single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀)
    rw [hSanchorSum, hSSum]
    abel
  have hmemD : (((aAnchor - aP2P1Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H)) ∈ D.P := by
    rw [hcoe]
    rw [d.hP1eq]
    exact hDP
  have hmemD' : (((aAnchor - aP2P1Nι - aTarget : Divisor0 H)) : Divisor H) ∈ D.P := by
    have hval : (((aAnchor - aP2P1Nι - aTarget : Divisor0 H)) : Divisor H) =
        (((aAnchor - aP2P1Nι : Divisor0 H) : Divisor H) -
          ((aTarget : Divisor0 H) : Divisor H)) := by
      show aAnchor.1 - aP2P1Nι.1 - aTarget.1 = (aAnchor.1 - aP2P1Nι.1) - aTarget.1
      rfl
    rw [hval]; exact hmemD
  have hmemAddSub : (aAnchor - aP2P1Nι - aTarget : Divisor0 H) ∈
      D.P.addSubgroupOf (Divisor0 H) := by
    rw [AddSubgroup.mem_addSubgroupOf]; exact hmemD'
  have hJeq := (QuotientAddGroup.eq_iff_sub_mem
    (N := D.P.addSubgroupOf (Divisor0 H))).mpr hmemAddSub
  rw [hcancel, ← map_sub]
  change
    QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H)) (aAnchor - aP2P1Nι) =
      QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H)) aTarget
  exact hJeq

end DecoupledSystem
end Genus2Lean
