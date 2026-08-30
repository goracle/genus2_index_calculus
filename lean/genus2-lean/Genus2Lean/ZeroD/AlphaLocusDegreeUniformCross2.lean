import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.CAWitnessCrossTangentMemOfLe

/-! # Cross-pair tangent (`Ra1 = ι(sa.P2)`) sibling of
`reducedClass_eq_of_isReduction'`

`ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3, step 5's
"still open" item: the top-level theorem consuming `cAmιTmδmιδ_mem_of_le_cross2`
(`CAWitnessCrossTangentMemOfLe.lean`, now built and REPL-confirmed).

**Why this is simpler than the anchor-tangent sibling
(`AlphaLocusDegreeUniformTangent.lean`) despite looking similar in name.**
That file's `Ra1 = Ra2` case genuinely doubles the ANCHOR pair itself —
`Sanchor` collapses from two points to one, `ua` becomes a perfect square,
and `Sanchor_eq_of_anchor_roots_tangent`/`divToPair_negVa_one_Sanchor_eq_tangent`
(membership-only, no cardinality route) are needed in place of the split
lemmas. **Here the anchor pair `{Ra, Ra2}` stays genuinely split**
(`caCross2InterpMatrix`'s own `h1 : RaX ≠ Ra2X` — checked directly,
`CAWitnessCrossTangent2.lean`) — the confluence is between the anchor
point `Ra` and the TARGET point `sa.P2`, via `sa.P2 = Point.iota Ra` (the
only surviving sub-case per the roadmap's own case-3 analysis: the
same-point alternative is ruled out by `hRaY_ne`/`hchar` and is not
reachable here). Consequently `Sanchor`'s own construction
(`Sanchor_eq_of_anchor_roots`, `divToPair_negVa_one_Sanchor_eq`, both the
ORIGINAL split-case lemmas) carries over completely unchanged — the only
things that actually change relative to `reducedClass_eq_of_isReduction'`
are:

1. `sa.P2` is no longer a free point in the CA-witness-facing part of the
   signature — it is forced to be `Point.iota Ra` (the caller supplies
   `Ra` and the identity `hP2eq : sa.P2 = Point.iota Ra` instead of a free
   `Ra1`). It REMAINS free everywhere `isReduction'`'s own machinery
   (`hcur`/`hgcd`/`hcurT`/`hgcdT`/`hr`) references `sa.P2.X`/`sa.P2.Y` —
   that machinery only ever consumes those as opaque field values and does
   not care whether `sa.P2` happens to equal `ι(Ra)` elsewhere (checked
   directly against `isReduction'`'s definition, which never mentions
   `Ra`/`Ra2` at all).
2. `caInterpMatrix`/`caCoeff`/`bCA`/`uCANew`/`denomPolyCA` (four free
   points `Ra1,Ra2,P2,P1`) are replaced by `caCross2InterpMatrix`/
   `caCross2Coeff`/`bCACross2`/`uCANewCross2`/`denomPolyCACross2` (three free
   points `RaX,Ra2X,P1X` plus the derivative datum `vDerivAtP2` —
   `CAWitnessCrossTangent2.lean`), matching `cAmιTmδmιδ_mem_of_le_cross2`'s
   own signature exactly.
3. `h1P2,h1P1,h2P2,h2P1,hPP` (six-hypothesis-family's cross/target members)
   disappear entirely — cross2's construction only needs `h1,h2,h3`
   (`RaX≠Ra2X`, `RaX≠P1X`, `Ra2X≠P1X`), the three-hypothesis nondegeneracy
   the roadmap's sympy check confirmed.
4. `hP2_curve`/`hP2Y_ne` (facts about the now-gone free `sa.P2`) are
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

/-- **Cross variant 2 top-level wiring**: `sa.reducedClass + q = toJacobian D
(target)`, for the case `sa.P2 = ι(Ra)` (`Ra`'s own conjugate collides with
the target's first point). Signature is `reducedClass_eq_of_isReduction'`'s
own, with `Ra1` renamed `Ra`, `sa.P2` forced via `hP2eq`, the six-hypothesis
family collapsed to `h1,h2,h3`, and the CA-witness functions swapped for
their `Cross`-suffixed siblings; see the module docstring for the itemized
diff. -/
theorem reducedClass_eq_of_isReduction'_cross2 {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
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
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          ua0 ua1 va0 va1 sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c0 c1 c2 c3 c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4
        sa.P1.X sa.P1.Y ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hr : isReduction' sa c0 c1 c2 c3 c4 ua0 ua1 va0 va1 hcur hgcd hcurT hgcdT)
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
    -- **`Ra`, `Ra2`: `Sanchor`'s own two points, exactly as in the split
    -- theorem — the anchor pair itself is NOT tangent here (see module
    -- docstring).** `sa.P2` is deliberately absent as a free point below:
    -- it is forced to be `Point.iota Ra` via `hP2eq`, matching the
    -- `caCross2InterpMatrix` construction's own convention
    -- (`CAWitnessCrossTangent2.lean`, `Ra1 = ι(sa.P2)`).
    (Ra Ra2 : H.Point)
    (hRa12Xne : Ra.X ≠ Ra2.X)
    (hRaRoot : ua.IsRoot Ra.X) (hRa2Root : ua.IsRoot Ra2.X)
    (hRaY : Ra.Y = va.eval Ra.X) (hRa2Y : Ra2.Y = va.eval Ra2.X)
    (hP2eq : sa.P2 = Point.iota Ra)
    (T1 T2 : H.Point)
    (hT12Xne : T1.X ≠ T2.X)
    (hT1Root : u.IsRoot T1.X) (hT2Root : u.IsRoot T2.X)
    (hT1Y : T1.Y = v.eval T1.X) (hT2Y : T2.Y = v.eval T2.X)
    [DecidableEq H.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (Uco UcoT : Polynomial (F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (F p)) = ua * Uco)
    (hUco_ne : Uco ≠ 0)
    (hUco_evalRa : Uco.eval Ra.X ≠ 0) (hUco_evalRa2 : Uco.eval Ra2.X ≠ 0)
    (hAUT : pairNorm H (-v) (1 : Polynomial (F p)) = u * UcoT)
    (hUcoT_ne : UcoT ≠ 0)
    (hUcoT_evalT1 : UcoT.eval T1.X ≠ 0) (hUcoT_evalT2 : UcoT.eval T2.X ≠ 0)
    (hRaY_ne : Ra.Y ≠ 0) (hRa2Y_ne : Ra2.Y ≠ 0)
    (hT1Y_ne : T1.Y ≠ 0) (hT2Y_ne : T2.Y ≠ 0)
    -- **The cross-pair `CAWitness` identification**: `caCross2InterpMatrix`'s
    -- own three free points `RaX,Ra2X,P1X` (`sa.P2` is gone, replaced by
    -- the `ι(Ra)`-identification `hP2eq` above), plus the target-derivative
    -- datum `vDerivAtP2` (`= -(derivative v).eval sa.P2.X`, per
    -- `CAWitnessCrossTangent2.lean`'s own `hP2Deriv` convention).
    (vDerivAtP2 : F p)
    (hdet : (caCross2InterpMatrix Ra.X Ra2.X sa.P1.X).det ≠ 0)
    (hlead : caCross2Coeff Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2 3 ≠ 0)
    (h1 : Ra.X ≠ Ra2.X) (h2 : Ra.X ≠ sa.P1.X) (h3 : Ra2.X ≠ sa.P1.X)
    (hRa_curve : Ra.Y ^ 2 = H.f.eval Ra.X) (hRa2_curve : Ra2.Y ^ 2 = H.f.eval Ra2.X)
    (hP1_curve : sa.P1.Y ^ 2 = H.f.eval sa.P1.X)
    (hP2Deriv : 2 * Ra.Y * (-vDerivAtP2) = (derivative H.f).eval Ra.X)
    (hP1Y_ne : sa.P1.Y ≠ 0)
    (hne : H.f - (bCACross2 Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2).eval Ra.X ≠ 0)
    (hU_evalRa2 : (uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2).eval Ra2.X ≠ 0)
    (hU_evalP1 : (uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2).eval sa.P1.X ≠ 0)
    (hU_ne0 : uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2 ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hPtT1X : PtT1.X ≠ PtT2.X)
    (hPtT1 : (uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2).IsRoot PtT1.X)
    (hPtT2 : (uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2).IsRoot PtT2.X)
    (Q1 Q2 : Polynomial (F p))
    (hQ1_def : uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2 =
      (Polynomial.X - Polynomial.C PtT1.X) * (Polynomial.X - Polynomial.C PtT2.X) * Q1)
    (hQ1T1 : Q1.eval PtT1.X ≠ 0)
    (hQ2_def : uCANewCross2 H Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2 =
      (Polynomial.X - Polynomial.C PtT2.X) * (Polynomial.X - Polynomial.C PtT1.X) * Q2)
    (hQ2T2 : Q2.eval PtT2.X ≠ 0)
    (hAeval1 : (denomPolyCACross2 Ra.X Ra2.X sa.P1.X : Polynomial (F p)).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCACross2 Ra.X Ra2.X sa.P1.X : Polynomial (F p)).eval PtT2.X ≠ 0)
    (hPtT1Y : PtT1.Y = (bCACross2 Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2Y : PtT2.Y = (bCACross2 Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : Ra.X ≠ PtT1.X) (hRaT2 : Ra.X ≠ PtT2.X)
    (hRa2T1 : Ra2.X ≠ PtT1.X) (hRa2T2 : Ra2.X ≠ PtT2.X)
    (hP1T1 : sa.P1.X ≠ PtT1.X) (hP1T2 : sa.P1.X ≠ PtT2.X)
    (h1δ : PtT1.X ≠ δ₀.X) (h2δ : PtT2.X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hT1eq : T1 = Point.iota PtT1) (hT2eq : T2 = Point.iota PtT2)
    (hsupp_f : ∀ P, P ∉ ({Ra, Ra2, Point.iota sa.P1, PtT1, PtT2} :
        Finset H.Point) →
      ordAt P (-bCACross2 Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2) (1 : Polynomial (F p)) = 0)
    (hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCACross2 Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({Ra, Ra2, Point.iota sa.P1, PtT1, PtT2} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCACross2 Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2)
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
  -- **`Sanchor`'s own split — unchanged from the split theorem**: `Ra,Ra2`
  -- are genuinely distinct (`hRa12Xne`), so the ORIGINAL `Sanchor_eq_of_
  -- anchor_roots` (not the anchor-tangent sibling) applies verbatim.
  have hRa12ne : Ra ≠ Ra2 := fun h => hRa12Xne (by rw [h])
  have hSanchorEq : Sanchor = ({Ra, Ra2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots ua va hua huafree
      Ra Ra2 hRa12ne hRa12Xne ⟨hRaRoot, hRa2Root⟩ hRaY hRa2Y Sanchor
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
  have hRaRoot' :
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)).IsRoot Ra.X := by
    rw [← hua]; exact hRaRoot
  have hRa2Root' :
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)).IsRoot Ra2.X := by
    rw [← hua]; exact hRa2Root
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
  have hSanchorSum : divToPair (H := H) (-va) 1 Sanchor = single Ra + single Ra2 :=
    DecoupledSystem.divToPair_negVa_one_Sanchor_eq (H := H) hchar
      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (ua0 := ua0) (ua1 := ua1) (va0 := va0) (va1 := va1)
      hf hMumfordUa huafree' va hva Uco hAU' hUco_ne
      Ra Ra2 hRa12ne hRaY_ne hRa2Y_ne hRaRoot' hRa2Root' hRaY hRa2Y
      hUco_evalRa hUco_evalRa2 Sanchor hSanchorEq
  have hSSum : divToPair (H := H) (-v) 1 S = single T1 + single T2 :=
    DecoupledSystem.divToPair_negV_one_S_eq (H := H) hchar
      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (u0 := sa.toSampleTarget.u0) (u1 := sa.toSampleTarget.u1)
      (v0 := sa.toSampleTarget.v0) (v1 := sa.toSampleTarget.v1)
      hf hMumfordTarget hufree' v hv UcoT hAUT' hUcoT_ne
      T1 T2 hT12ne hT1Y_ne hT2Y_ne hT1Root' hT2Root' hT1Y hT2Y
      hUcoT_evalT1 hUcoT_evalT2 S hSEq
  -- **The cross2 concrete-coordinate assembly (†)**: `[Ra]+[Ra2]-[ιRa] -
  -- [ιT1]-[ιT2] - [δ₀]-[ιδ₀]`-shaped fact, then rewritten below (via
  -- `hcoe`) into `[Ra]+[Ra2]-[ι(Ra)]-[sa.P1]-...` matching this theorem's
  -- own `single Ra1 + single Ra2 - single sa.P2 - single sa.P1 - ...`
  -- shape once `hP2eq` identifies `single sa.P2 = single (Point.iota Ra)`.
  have hDP := cAmιTmδmιδ_mem_of_le_cross2 (H := H) hdeg hchar hsf D hD
    hspec_linX
    Ra.X Ra2.X sa.P1.X Ra.Y Ra2.Y sa.P1.Y vDerivAtP2
    hdet hlead h1 h2 h3
    hRa_curve hRa2_curve hP1_curve hP2Deriv hRaY_ne hRa2Y_ne hP1Y_ne
    Ra Ra2 sa.P1 (Point.iota sa.P1)
    rfl rfl rfl rfl rfl rfl rfl rfl
    hne
    hU_evalRa hU_evalRa2 hU_evalP1 hU_ne0
    PtT1.X PtT2.X hPtT1 hPtT2 hPtT1X
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2
    rfl hPtT1Y hPtT1Y_ne rfl hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hRa2T1 hRa2T2 hP1T1 hP1T2
    h1δ h2δ hδY hsupp_f hspec_f hsupp_hT hspec_hT
    T1 T2 hT1eq hT2eq
  set aAnchor : Divisor0 H := ⟨divToPair (H := H) (-va) 1 Sanchor -
    (single δ₀ + single (Point.iota δ₀)), hmemAnchor⟩ with haAnchor_def
  set aTarget : Divisor0 H := ⟨divToPair (H := H) (-v) 1 S -
    (single δ₀ + single (Point.iota δ₀)), hmem⟩ with haTarget_def
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
  have hred : sa.reducedClass = sa.alpha • aClass - (toJacobian D aP2P1Nι + q) := by
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
            exact add_mem h1 h2⟩ : Divisor0 H) = aP2P1Nι + aQ := by
      apply Subtype.ext
      show single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
        (aP2P1Nι : Divisor H) + (aQ : Divisor H)
      rw [haP2P1Nι_def, haQ_def]
      show single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) +
          (single (Point.iota δ₀) - single δ₀)
      rw [two_zsmul]
      abel
    rw [hReducedClass, hN2, map_add, hq]
  rw [hred, hAlphaRep]
  have hcancel : toJacobian D aAnchor - (toJacobian D aP2P1Nι + q) + q =
      toJacobian D aAnchor - toJacobian D aP2P1Nι := by abel
  have hcoe : ((aAnchor - aP2P1Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H) =
      (single Ra + single Ra2 - single sa.P2 - single sa.P1 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    show (aAnchor.1 - aP2P1Nι.1) - aTarget.1 =
      single Ra + single Ra2 - single sa.P2 - single sa.P1 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
    rw [haAnchor_def, haP2P1Nι_def, haTarget_def]
    show (divToPair (H := H) (-va) 1 Sanchor - (single δ₀ + single (Point.iota δ₀))) -
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) -
        (divToPair (H := H) (-v) 1 S - (single δ₀ + single (Point.iota δ₀))) =
      single Ra + single Ra2 - single sa.P2 - single sa.P1 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
    rw [hSanchorSum, hSSum]
    abel
  have hmemD : (((aAnchor - aP2P1Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H)) ∈ D.P := by
    rw [hcoe]
    -- `hDP`'s conclusion is stated in terms of `Point.iota Ra` where this
    -- goal (via `hcoe`) is stated in terms of `sa.P2` — bridge via `hP2eq`
    -- before the two divisors can be matched by `exact`.
    rw [hP2eq]
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
