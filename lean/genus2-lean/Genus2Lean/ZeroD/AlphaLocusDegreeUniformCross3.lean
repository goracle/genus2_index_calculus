import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.CAWitnessCrossTangentMemOfLe

/-! # Cross-pair tangent (`Ra2 = ι(sa.P1)`) sibling of
`reducedClass_eq_of_isReduction'`

`ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3, step 5's
"still open" item: the top-level theorem consuming `cAmιTmδmιδ_mem_of_le_cross3`
(`CAWitnessCrossTangentMemOfLe.lean`, now built and REPL-confirmed).

**Same shape as `AlphaLocusDegreeUniformCross1.lean`, with the doubled node
on the SECOND anchor slot instead of the first.** There, `Ra1` was renamed
`Ra` and doubled with `sa.P1`, with `Ra2` surviving as an ordinary anchor
point. Here it is the other way round: `Ra1` survives as an ordinary anchor
point, and `Ra2` is renamed `Ra` and doubled with `sa.P1` via
`hP1eq : sa.P1 = Point.iota Ra`. The anchor pair `{Ra1, Ra}` stays genuinely
split (`caCross3InterpMatrix`'s own `h1 : Ra1X ≠ RaX` — checked directly,
`CAWitnessCrossTangentV3.lean`); `Sanchor`'s own construction
(`Sanchor_eq_of_anchor_roots`, `divToPair_negVa_one_Sanchor_eq`, both the
ORIGINAL split-case lemmas) carries over completely unchanged. The only
things that actually change relative to `reducedClass_eq_of_isReduction'`
are:

1. `sa.P1` is no longer a free point in the CA-witness-facing part of the
   signature — it is forced to be `Point.iota Ra` (the caller supplies
   `Ra` and the identity `hP1eq : sa.P1 = Point.iota Ra` instead of a free
   `Ra2`). It REMAINS free everywhere `isReduction'`'s own machinery
   (`hcur`/`hgcd`/`hcurT`/`hgcdT`/`hr`) references `sa.P1.X`/`sa.P1.Y` —
   that machinery only ever consumes those as opaque field values and does
   not care whether `sa.P1` happens to equal `ι(Ra)` elsewhere (checked
   directly against `isReduction'`'s definition, which never mentions
   `Ra1`/`Ra` at all).
2. `caInterpMatrix`/`caCoeff`/`bCA`/`uCANew`/`denomPolyCA` (four free
   points `Ra1,Ra2,P1,P2`) are replaced by `caCross3InterpMatrix`/
   `caCross3Coeff`/`bCACross3`/`uCANewCross3`/`denomPolyCACross3` (three
   free points `Ra1X,RaX,P2X` plus the derivative datum `vDerivAtP1` —
   `CAWitnessCrossTangentV3.lean`), matching `cAmιTmδmιδ_mem_of_le_cross3`'s
   own signature exactly.
3. `h1P1,h1P2,h2P1,h2P2,hPP` (six-hypothesis-family's cross/target members)
   disappear entirely — cross3's construction only needs `h1,h2,h3`
   (`Ra1X≠RaX`, `Ra1X≠P2X`, `RaX≠P2X`), the three-hypothesis nondegeneracy
   the roadmap's sympy check confirmed.
4. `hP1_curve`/`hP1Y_ne` (facts about the now-gone free `sa.P1`) are
   derived from `hRa_curve`/`hRaY_ne` via `Point.iota_X`/`Point.iota_Y`
   (`(ι Ra).Y = -Ra.Y`, so `(ι Ra).Y^2 = Ra.Y^2 = f.eval Ra.X = f.eval
   (ι Ra).X`) rather than taken as independent hypotheses.

Everything else — `isReduction'`'s own ~230-line hypothesis block, `S`/`T1
T2`/target-side machinery, the final `Divisor0`-level assembly/`abel`
argument — is copied from `reducedClass_eq_of_isReduction'` verbatim, since
none of it references the anchor/target CA-witness construction directly
(it only consumes `hDP`'s already-assembled conclusion). -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-- **Cross variant 3 top-level wiring**: `sa.reducedClass + q = toJacobian D
(target)`, for the case `sa.P1 = ι(Ra2)` (`Ra2`'s own conjugate collides
with the target's first point). Signature is `reducedClass_eq_of_isReduction'`'s
own, with `Ra2` renamed `Ra`, `sa.P1` forced via `hP1eq`, the six-hypothesis
family collapsed to `h1,h2,h3`, and the CA-witness functions swapped for
their `Cross3`-suffixed siblings; see the module docstring for the itemized
diff.

Renamed from `reducedClass_eq_of_isReduction'_cross3` to `..._cross3_flat`
(per `ROADMAP-reducedClass-dispatcher.md`'s bundling work, matching the
`_cross1_flat`/`_cross2_flat` convention already established): the bundled
version in `ReducedClassBundlesCross3.lean` now owns the unqualified name.
This flat theorem is grep-confirmed to have no external callers, so the
rename is safe; kept (rather than deleted) as a second, independently-
checkable proof route to the same conclusion. -/
theorem reducedClass_eq_of_isReduction'_cross3_flat {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (hReducedClass :
      sa.reducedClass =
        sa.alpha • aClass -
          toJacobian D
            (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
              by
                have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
                have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
                have heq2 : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
                    (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
                  rw [two_zsmul]
                  abel
                rw [heq2]
                exact add_mem h1 h2⟩ : Divisor0 H))
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (hdeg : H.f.natDegree = 5)
    (hD : principalSubgroup H hdeg ≤ D.P)
    (u0 u1 v0 v1 : F p)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
        u0 u1 v0 v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          ua0 ua1 va0 va1 u0 u1 v0 v1)
        (uRS4General p c0 c1 c2 c3 c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
          u0 u1 v0 v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4
        sa.P1.X sa.P1.Y ua0 ua1 va0 va1
        u0 u1 v0 v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          u0 u1 v0 v1)
        (uRS4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          u0 u1 v0 v1))
    (hr : isReduction' sa c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hcur hgcd hcurT hgcdT)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4
      sa.toSampleTarget.u0 sa.toSampleTarget.u1 sa.toSampleTarget.v0 sa.toSampleTarget.v1)
    (Sanchor S : Finset H.Point) (va u v : Polynomial (F p))
    (hva : va = (Polynomial.C va1 : Polynomial (F p)) * (Polynomial.X : Polynomial (F p))
      + (Polynomial.C va0 : Polynomial (F p)))
    (hu : u = (Polynomial.X : Polynomial (F p)) ^ 2 + (Polynomial.C sa.toSampleTarget.u1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)))
    (hv : v = (Polynomial.C sa.toSampleTarget.v1 : Polynomial (F p)) * (Polynomial.X : Polynomial (F p))
      + (Polynomial.C sa.toSampleTarget.v0 : Polynomial (F p)))
    (hsuppAnchor : ∀ P, P ∉ Sanchor → ordAt (H := H) P (-va) 1 = 0)
    (hmemAnchor : (divToPair (H := H) (-va) 1 Sanchor -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H)
    (hAlphaRep : sa.alpha • aClass =
      toJacobian D (Subtype.mk (divToPair (H := H) (-va) 1 Sanchor -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmemAnchor))
    (hsupp : ∀ P, P ∉ S → ordAt (H := H) P (-v) 1 = 0)
    (hSmem : ∀ P ∈ S, u.eval P.X = 0 ∧ P.Y = v.eval P.X)
    (hufree : Squarefree u)
    (hScard : S.card = u.natDegree)
    (ua : Polynomial (F p))
    (hua : ua = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C ua1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C ua0 : Polynomial (F p)))
    (hSanchorMem : ∀ P ∈ Sanchor, ua.eval P.X = 0 ∧ P.Y = va.eval P.X)
    (huafree : Squarefree ua)
    (hSanchorCard : Sanchor.card = ua.natDegree)
    (hmem : (divToPair (H := H) (-v) 1 S -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H)
    (q : Jacobian H D)
    (hq : q = toJacobian D (Subtype.mk (single (Point.iota δ₀) - single δ₀ : Divisor H)
      (single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀)) )
    -- **`Ra1`, `Ra`: `Sanchor`'s own two points, exactly as in the split
    -- theorem — the anchor pair itself is NOT tangent here (see module
    -- docstring).** `sa.P1` is deliberately absent as a free point below:
    -- it is forced to be `Point.iota Ra` via `hP1eq`, matching the
    -- `caCross3InterpMatrix` construction's own convention
    -- (`CAWitnessCrossTangentV3.lean`, `Ra2 = ι(sa.P1)`).
    (Ra1 Ra : H.Point)
    (hRa12Xne : Ra1.X ≠ Ra.X)
    (hRa1Root : ua.IsRoot Ra1.X) (hRaRoot : ua.IsRoot Ra.X)
    (hRa1Y : Ra1.Y = va.eval Ra1.X) (hRaY : Ra.Y = va.eval Ra.X)
    (hP1eq : sa.P1 = Point.iota Ra)
    (T1 T2 : H.Point)
    (hT12Xne : T1.X ≠ T2.X)
    (hT1Root : u.IsRoot T1.X) (hT2Root : u.IsRoot T2.X)
    (hT1Y : T1.Y = v.eval T1.X) (hT2Y : T2.Y = v.eval T2.X)
    [DecidableEq H.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (Uco UcoT : Polynomial (F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (F p)) = ua * Uco)
    (hUco_ne : Uco ≠ 0)
    (hUco_evalRa1 : Uco.eval Ra1.X ≠ 0) (hUco_evalRa : Uco.eval Ra.X ≠ 0)
    (hAUT : pairNorm H (-v) (1 : Polynomial (F p)) = u * UcoT)
    (hUcoT_ne : UcoT ≠ 0)
    (hUcoT_evalT1 : UcoT.eval T1.X ≠ 0) (hUcoT_evalT2 : UcoT.eval T2.X ≠ 0)
    (hRa1Y_ne : Ra1.Y ≠ 0) (hRaY_ne : Ra.Y ≠ 0)
    (hT1Y_ne : T1.Y ≠ 0) (hT2Y_ne : T2.Y ≠ 0)
    -- **The cross-pair `CAWitness` identification**: `caCross3InterpMatrix`'s
    -- own three free points `Ra1X,RaX,P2X` (`sa.P1` is gone, replaced by
    -- the `ι(Ra)`-identification `hP1eq` above), plus the target-derivative
    -- datum `vDerivAtP1` (`= -(derivative v).eval sa.P1.X`, per
    -- `CAWitnessCrossTangentV3.lean`'s own `hP1Deriv` convention).
    (vDerivAtP1 : F p)
    (hdet : (caCross3InterpMatrix Ra1.X Ra.X sa.P2.X).det ≠ 0)
    (hlead : caCross3Coeff Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y 3 ≠ 0)
    (h1 : Ra1.X ≠ Ra.X) (h2 : Ra1.X ≠ sa.P2.X) (h3 : Ra.X ≠ sa.P2.X)
    (hRa1_curve : Ra1.Y ^ 2 = H.f.eval Ra1.X) (hRa_curve : Ra.Y ^ 2 = H.f.eval Ra.X)
    (hP2_curve : sa.P2.Y ^ 2 = H.f.eval sa.P2.X)
    (hP1Deriv : 2 * Ra.Y * (-vDerivAtP1) = (derivative H.f).eval Ra.X)
    (hP2Y_ne : sa.P2.Y ≠ 0)
    (hne : H.f - (bCACross3 Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y) ^ 2 ≠ 0)
    (hU_evalRa1 : (uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y).eval Ra1.X ≠ 0)
    (hU_evalRa : (uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y).eval Ra.X ≠ 0)
    (hU_evalP2 : (uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y).eval sa.P2.X ≠ 0)
    (hU_ne0 : uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hPtT1X : PtT1.X ≠ PtT2.X)
    (hPtT1 : (uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y).IsRoot PtT1.X)
    (hPtT2 : (uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y).IsRoot PtT2.X)
    (Q1 Q2 : Polynomial (F p))
    (hQ1_def : uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y =
      (Polynomial.X - Polynomial.C PtT1.X) * (Polynomial.X - Polynomial.C PtT2.X) * Q1)
    (hQ1T1 : Q1.eval PtT1.X ≠ 0)
    (hQ2_def : uCANewCross3 H Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y =
      (Polynomial.X - Polynomial.C PtT2.X) * (Polynomial.X - Polynomial.C PtT1.X) * Q2)
    (hQ2T2 : Q2.eval PtT2.X ≠ 0)
    (hAeval1 : (denomPolyCACross3 Ra1.X Ra.X sa.P2.X : Polynomial (F p)).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross3 Ra1.X Ra.X sa.P2.X : Polynomial (F p)).eval PtT2.X ≠ 0)
    (hPtT1Y : PtT1.Y = (bCACross3 Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2Y : PtT2.Y = (bCACross3 Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRa1T1 : Ra1.X ≠ PtT1.X) (hRa1T2 : Ra1.X ≠ PtT2.X)
    (hRaT1 : Ra.X ≠ PtT1.X) (hRaT2 : Ra.X ≠ PtT2.X)
    (hP2T1 : sa.P2.X ≠ PtT1.X) (hP2T2 : sa.P2.X ≠ PtT2.X)
    (h1δ : PtT1.X ≠ δ₀.X) (h2δ : PtT2.X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hT1eq : T1 = Point.iota PtT1) (hT2eq : T2 = Point.iota PtT2)
    (hsupp_f : ∀ P, P ∉ ({Ra1, Ra, Point.iota sa.P2, PtT1, PtT2} :
        Finset H.Point) →
      ordAt P (-bCACross3 Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y) (1 : Polynomial (F p)) = 0)
    (hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross3 Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({Ra1, Ra, Point.iota sa.P2, PtT1, PtT2} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross3 Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y)
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
    [∀ (a : F p) (Sfin : Finset H.Point),
      ∀ P : Sfin, Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : F p), ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P) :
    sa.reducedClass + q =
      toJacobian D (Subtype.mk (divToPair (H := H) (-v) 1 S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmem) := by
  classical
  -- **`Sanchor`'s own split — unchanged from the split theorem**: `Ra1,Ra`
  -- are genuinely distinct (`hRa12Xne`), so the ORIGINAL `Sanchor_eq_of_
  -- anchor_roots` (not the anchor-tangent sibling) applies verbatim.
  have hRa12ne : Ra1 ≠ Ra := fun h => hRa12Xne (by rw [h])
  have hSanchorEq : Sanchor = ({Ra1, Ra} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots ua va hua huafree
      Ra1 Ra hRa12ne hRa12Xne ⟨hRa1Root, hRaRoot⟩ hRa1Y hRaY Sanchor
      hSanchorMem hSanchorCard
  have hT12ne : T1 ≠ T2 := fun h => hT12Xne (by rw [h])
  have hSEq : S = ({T1, T2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots (ua0 := sa.toSampleTarget.u0) (ua1 := sa.toSampleTarget.u1)
      u v hu hufree
      T1 T2 hT12ne hT12Xne ⟨hT1Root, hT2Root⟩ hT1Y hT2Y S hSmem hScard
  have huafree' : Squarefree (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X
      + Polynomial.C ua0 : Polynomial (F p)) := hua ▸ huafree
  have hufree' : Squarefree (Polynomial.X ^ 2 +
      Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
      + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) := hu ▸ hufree
  have hRa1Root' :
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)).IsRoot Ra1.X := by
    rw [← hua]; exact hRa1Root
  have hRaRoot' :
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)).IsRoot Ra.X := by
    rw [← hua]; exact hRaRoot
  have hT1Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot T1.X := by
    rw [← hu]; exact hT1Root
  have hT2Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot T2.X := by
    rw [← hu]; exact hT2Root
  have hAU' : pairNorm H (-va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)) * Uco :=
    hua ▸ hAU
  have hAUT' : pairNorm H (-v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
        + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) * UcoT :=
    hu ▸ hAUT
  have hSanchorSum : divToPair (H := H) (-va) 1 Sanchor = single Ra1 + single Ra :=
    DecoupledSystem.divToPair_negVa_one_Sanchor_eq (H := H) hchar
      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (ua0 := ua0) (ua1 := ua1) (va0 := va0) (va1 := va1)
      hf hMumfordUa huafree' va hva Uco hAU' hUco_ne
      Ra1 Ra hRa12ne hRa1Y_ne hRaY_ne hRa1Root' hRaRoot' hRa1Y hRaY
      hUco_evalRa1 hUco_evalRa Sanchor hSanchorEq
  have hSSum : divToPair (H := H) (-v) 1 S = single T1 + single T2 :=
    DecoupledSystem.divToPair_negV_one_S_eq (H := H) hchar
      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (u0 := sa.toSampleTarget.u0) (u1 := sa.toSampleTarget.u1)
      (v0 := sa.toSampleTarget.v0) (v1 := sa.toSampleTarget.v1)
      hf hMumfordTarget hufree' v hv UcoT hAUT' hUcoT_ne
      T1 T2 hT12ne hT1Y_ne hT2Y_ne hT1Root' hT2Root' hT1Y hT2Y
      hUcoT_evalT1 hUcoT_evalT2 S hSEq
  -- **The cross3 concrete-coordinate assembly (†)**: `[Ra1]+[Ra]-[ιRa] -
  -- [ιT1]-[ιT2] - [δ₀]-[ιδ₀]`-shaped fact, then rewritten below (via
  -- `hcoe`) into `[Ra1]+[Ra]-[ι(Ra)]-[sa.P2]-...` matching this theorem's
  -- own `single Ra1 + single Ra2 - single sa.P1 - single sa.P2 - ...`
  -- shape once `hP1eq` identifies `single sa.P1 = single (Point.iota Ra)`.
  have hDP := cAmιTmδmιδ_mem_of_le_cross3 (H := H) hdeg hchar hsf D hD
    hspec_linX
    Ra1.X Ra.X sa.P2.X Ra1.Y Ra.Y vDerivAtP1 sa.P2.Y
    hdet hlead h1 h2 h3
    hRa1_curve hRa_curve hP2_curve hP1Deriv hRa1Y_ne hRaY_ne hP2Y_ne
    Ra1 Ra sa.P2 (Point.iota sa.P2)
    rfl rfl rfl rfl rfl rfl rfl rfl
    hne
    hU_evalRa1 hU_evalRa hU_evalP2 hU_ne0
    PtT1.X PtT2.X hPtT1 hPtT2 hPtT1X
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2
    rfl hPtT1Y hPtT1Y_ne rfl hPtT2Y hPtT2Y_ne
    hRa1T1 hRa1T2 hRaT1 hRaT2 hP2T1 hP2T2
    h1δ h2δ hδY hsupp_f hspec_f hsupp_hT hspec_hT
    T1 T2 hT1eq hT2eq
  set aAnchor : Divisor0 H := ⟨divToPair (H := H) (-va) 1 Sanchor -
    (single δ₀ + single (Point.iota δ₀)), hmemAnchor⟩ with haAnchor_def
  set aTarget : Divisor0 H := ⟨divToPair (H := H) (-v) 1 S -
    (single δ₀ + single (Point.iota δ₀)), hmem⟩ with haTarget_def
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
  have hred : sa.reducedClass = sa.alpha • aClass - (toJacobian D aP1P2Nι + q) := by
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
    rw [hReducedClass, hN2, map_add, hq]
  rw [hred, hAlphaRep]
  have hcancel : toJacobian D aAnchor - (toJacobian D aP1P2Nι + q) + q =
      toJacobian D aAnchor - toJacobian D aP1P2Nι := by abel
  have hcoe : ((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H) =
      (single Ra1 + single Ra - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    show (aAnchor.1 - aP1P2Nι.1) - aTarget.1 =
      single Ra1 + single Ra - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
    rw [haAnchor_def, haP1P2Nι_def, haTarget_def]
    show (divToPair (H := H) (-va) 1 Sanchor - (single δ₀ + single (Point.iota δ₀))) -
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) -
        (divToPair (H := H) (-v) 1 S - (single δ₀ + single (Point.iota δ₀))) =
      single Ra1 + single Ra - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
    rw [hSanchorSum, hSSum]
    abel
  have hmemD : (((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H)) ∈ D.P := by
    rw [hcoe]
    -- `hDP`'s conclusion is stated in terms of `Point.iota Ra` where this
    -- goal (via `hcoe`) is stated in terms of `sa.P1` — bridge via `hP1eq`
    -- before the two divisors can be matched by `exact`.
    rw [hP1eq]
    exact hDP
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
