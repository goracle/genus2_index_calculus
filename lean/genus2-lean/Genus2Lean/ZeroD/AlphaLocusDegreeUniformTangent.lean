import Mathlib
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.PrincipalWitnessFinalAssemblyTangent

/-! # Tangent-anchor (`Ra1 = Ra2`) sibling of `reducedClass_eq_of_isReduction'`

`ROADMAP-principal-witness-tangent-assembly.md`'s Step 5. Prerequisite
(`PrincipalWitnessFinalAssemblyTangent.lean`'s
`cAmιTmδmιδ_mem_of_le_tangent`) is done and REPL-confirmed (Step 4). This
file is the actual wiring: `reducedClass_eq_of_isReduction'` itself
(`AlphaLocusDegreeUniform.lean`) is stated only for the fully-split anchor
(`hRa12Xne : Ra1.X ≠ Ra2.X` is a hard hypothesis of that theorem, not a
case split inside it — the anchor is genuinely two distinct points
there), so the tangent anchor case (`Ra1 = Ra2`, one doubled anchor point
`Ra`) needs its own theorem, not an edit to the split one. Mirrors that
theorem's own proof exactly, with the anchor-side machinery swapped for
its tangent counterpart:

- `Sanchor_eq_of_anchor_roots` → `Sanchor_eq_of_anchor_roots_tangent`
  (`SanchorEqAlphaPoints.lean`) — `Sanchor = {Ra}`, membership-only, no
  cardinality hypothesis (the tangent case's `Sanchor.card = 1 ≠ 2 =
  ua.natDegree`, so the split lemma's cardinality route does not apply;
  `hRamem : Ra ∈ Sanchor` is supplied directly instead, matching that
  lemma's own documented calling convention).
- `divToPair_negVa_one_Sanchor_eq` → `divToPair_negVa_one_Sanchor_eq_tangent`
  (`PrincipalWitnessCAConnection.lean`) — collapses to `2 • single Ra`
  (one point, multiplicity 2) rather than `single Ra1 + single Ra2`.
- `cAmιTmδmιδ_mem_of_le` → `cAmιTmδmιδ_mem_of_le_tangent`
  (`PrincipalWitnessFinalAssemblyTangent.lean`) — `hDP`'s source, giving
  `2•[Ra]-[P1]-[P2]-[T1]-[T2]+[δ₀]+[ιδ₀] ∈ D.P` (Step 4's corrected,
  REPL-confirmed shape, matching the split case's own shape exactly once
  `Ra1+Ra2` collapses to `2•Ra` — no leftover `-[T1]-[T2]` terms, per that
  file's docstring). Unlike the split theorem (which computes its own
  `hDP` as a bare proof-body `have`, `AlphaLocusDegreeUniform.lean` line
  ~1204), this file keeps `hDP_tangent_aux` as a SEPARATE top-level
  theorem, and the main theorem below takes `hDP` as an abstract
  hypothesis. Confirmed this pass, the hard way: inlining the ~35
  `hdet`..`hspec_hT` binders directly into the main theorem's own
  signature (to mirror the split file exactly) still hits a `whnf`
  timeout — this file's version of that zone (`caTangentInterpMatrix`/
  `uCANewTangent`/`bCATangent`/`denomPolyCATangent`) is evidently more
  expensive to elaborate than the split file's analogous
  `caInterpMatrix`/`uCANew`/`bCA`/`denomPolyCA` zone, even though the two
  are structurally parallel. So this file genuinely needs the two-theorem
  split that the split file doesn't: `hDP_tangent_aux` carries the ~35
  binders and nothing else; the main theorem never sees them, only
  `hDP`'s already-elaborated type.

The target-side (`T1,T2`/`S`/`u`/`v`) machinery is UNCHANGED from the split
theorem — this roadmap only scopes the anchor (`Ra1=Ra2`) tangent case,
`hcurT`/`hgcdT`-style target-side tangency is a separate, already-scoped
branch of the top-level `reducedClass_eq_of_isReduction'` signature and is
not touched here. Consequently this theorem's signature is the split
theorem's signature with `Ra1 Ra2 hRa12Xne hRa1Root hRa2Root hRa1Y hRa2Y`
replaced by a single doubled point `Ra` and its tangency data
(`ua`/`hua` name the anchor quadratic; `hua_eq`/`hRaY`/`hRaDeriv` state
its tangency; `vaDerivAtRa` supplies the derivative-row value), everything
else identical. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

-- **`hDP_tangent_aux`**: isolates the ~35-binder "anchor construction"
-- zone (`hdet`..`hspec_hT`) that only ever feeds `hDP`'s derivation and
-- nothing else downstream — confirmed by bisection probes in an earlier
-- pass. Putting these directly in the main theorem's own signature (an
-- intermediate attempt this pass) still timed out at `whnf` (this file's
-- own accumulated cost is evidently higher than the split file's
-- analogous zone, even though it's structurally similar) — so unlike the
-- split file (`AlphaLocusDegreeUniform.lean`), which computes its `hDP`
-- as a bare proof-body `have` with no dedicated lemma, THIS file needs a
-- genuine second top-level declaration to keep either signature small
-- enough to elaborate. Thin specialization of `cAmιTmδmιδ_mem_of_le_tangent`
-- (`PrincipalWitnessFinalAssemblyTangent.lean`) to this file's `Ra`/
-- `sa.P1`/`sa.P2`/`T1`/`T2` naming; conclusion is exactly `hDP`'s type
-- in the main theorem's proof. Argument order in the proof term below is
-- copied directly from `cAmιTmδmιδ_mem_of_le_tangent`'s own signature
-- (`PrincipalWitnessFinalAssemblyTangent.lean` lines 170-244), checked
-- binder-by-binder against it, not against this file's own (previously
-- wrong) earlier draft of this call.
set_option maxHeartbeats 800000 in
theorem hDP_tangent_aux {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
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
    (Ra : H.Point) (P1 : H.Point) (P2 : H.Point)
    (vaDerivAtRa : F p)
    (hdet : (caTangentInterpMatrix Ra.X P1.X P2.X).det ≠ 0)
    (hlead : caTangentCoeff Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y 3 ≠ 0)
    (h1P1 : Ra.X ≠ P1.X) (h1P2 : Ra.X ≠ P2.X) (hPP : P1.X ≠ P2.X)
    (hRa_curve : Ra.Y ^ 2 = H.f.eval Ra.X)
    (hP1_curve : P1.Y ^ 2 = H.f.eval P1.X) (hP2_curve : P2.Y ^ 2 = H.f.eval P2.X)
    (hRaDeriv : 2 * Ra.Y * vaDerivAtRa = (derivative H.f).eval Ra.X)
    (hRaY_ne : Ra.Y ≠ 0) (hP1Y_ne : P1.Y ≠ 0) (hP2Y_ne : P2.Y ≠ 0)
    (hne : H.f - (bCATangent Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y) ^ 2 ≠ 0)
    (hU_evalRa : (uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y).eval Ra.X ≠ 0)
    (hU_evalP1 : (uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y).eval P1.X ≠ 0)
    (hU_evalP2 : (uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y).eval P2.X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hPtT1 : (uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y).IsRoot PtT1.X)
    (hPtT2 : (uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y).IsRoot PtT2.X)
    (hPtT1X : PtT1.X ≠ PtT2.X)
    (hU_ne0 : uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y ≠ 0)
    (Q1 Q2 : Polynomial (F p))
    (hQ1_def : uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y =
      (Polynomial.X - Polynomial.C PtT1.X) * (Polynomial.X - Polynomial.C PtT2.X) * Q1)
    (hQ1T1 : Q1.eval PtT1.X ≠ 0)
    (hQ2_def : uCANewTangent H Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y =
      (Polynomial.X - Polynomial.C PtT2.X) * (Polynomial.X - Polynomial.C PtT1.X) * Q2)
    (hQ2T2 : Q2.eval PtT2.X ≠ 0)
    (δ₀ : H.Point)
    (hAeval1 : (denomPolyCATangent Ra.X P1.X P2.X : Polynomial (F p)).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCATangent Ra.X P1.X P2.X : Polynomial (F p)).eval PtT2.X ≠ 0)
    (hPtT1Y : PtT1.Y = (bCATangent Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2Y : PtT2.Y = (bCATangent Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : Ra.X ≠ PtT1.X) (hRaT2 : Ra.X ≠ PtT2.X)
    (hP1T1 : P1.X ≠ PtT1.X) (hP1T2 : P1.X ≠ PtT2.X)
    (hP2T1 : P2.X ≠ PtT1.X) (hP2T2 : P2.X ≠ PtT2.X)
    (h1δ : PtT1.X ≠ δ₀.X) (h2δ : PtT2.X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({Ra, Point.iota P1, Point.iota P2, PtT1, PtT2} :
        Finset H.Point) →
      ordAt P (-bCATangent Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y) (1 : Polynomial (F p)) = 0)
    (hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangent Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({Ra, Point.iota P1, Point.iota P2, PtT1, PtT2} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCATangent Ra.X P1.X P2.X Ra.Y vaDerivAtRa P1.Y P2.Y)
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
    ((2 : ℤ) • single Ra - single P1 - single P2 -
      single T1cur - single T2cur +
      single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P :=
  cAmιTmδmιδ_mem_of_le_tangent (H := H) hdeg hchar hsf D hD
    hspec_linX
    Ra.X P1.X P2.X Ra.Y P1.Y P2.Y vaDerivAtRa
    hdet hlead h1P1 h1P2 hPP
    hRa_curve hP1_curve hP2_curve hRaDeriv
    hRaY_ne hP1Y_ne hP2Y_ne
    Ra P1 P2 (Point.iota P1) (Point.iota P2)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hne hU_evalRa hU_evalP1 hU_evalP2
    PtT1.X PtT2.X hPtT1 hPtT2 hPtT1X hU_ne0
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2 rfl hPtT1Y hPtT1Y_ne rfl hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hP1T1 hP1T2 hP2T1 hP2T2 h1δ h2δ hδY hsupp_f hspec_f hsupp_hT hspec_hT
    T1cur T2cur hT1eq hT2eq


/-!
The original version put the complete tangent construction in one theorem
signature.  The revision below makes the split explicit: the final theorem
consumes dependent records, and the large CA-witness hypotheses remain
isolated in `hDP_tangent_aux`, whose only output needed here is `hDP`. The
small divisor-zero witness used by `hReducedClass` is also a named theorem,
so the structure declaration itself contains no nested tactic block.
-/

/-- The degree-zero witness used in `TangentReductionData.hReducedClass`.
Keeping this as a separate theorem avoids putting a nested tactic proof inside
the large dependent structure field, which otherwise makes parser/elaborator
errors much harder to localize. -/
theorem sampleP1P2_sub_two_delta_mem
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)}
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) :
    (single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ : Divisor H) ∈ Divisor0 H := by
  have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
  have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
  have heq2 : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
      (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
    rw [two_zsmul]
    abel
  rw [heq2]
  exact add_mem h1 h2

set_option maxHeartbeats 800000 in
structure TangentCoefficientData
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
  coeff_hMumfordTarget : IsMumfordTarget4 p coeff_c0 coeff_c1 coeff_c2 coeff_c3 coeff_c4
      sa.toSampleTarget.u0 sa.toSampleTarget.u1
      sa.toSampleTarget.v0 sa.toSampleTarget.v1

set_option maxHeartbeats 800000 in
structure TangentReductionData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  coeffs : TangentCoefficientData sa
  hReducedClass :
    sa.reducedClass =
      sa.alpha • aClass -
        toJacobian D
          (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
            sampleP1P2_sub_two_delta_mem sa⟩ : Divisor0 H)

set_option maxHeartbeats 800000 in
structure TangentAssemblyData
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) where
  as_coeffs : TangentCoefficientData sa
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
  hmemAnchor : (divToPair (H := H) (-as_va) 1 as_Sanchor -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H
  hAlphaRep : sa.alpha • aClass =
      toJacobian D (Subtype.mk (divToPair (H := H) (-as_va) 1 as_Sanchor -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmemAnchor)
  hSmem : ∀ P ∈ as_S, as_u.eval P.X = 0 ∧ P.Y = as_v.eval P.X
  hufree : Squarefree as_u
  hScard : as_S.card = as_u.natDegree
  hmem : (divToPair (H := H) (-as_v) 1 as_S -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H
  as_q : Jacobian H D
  hq : as_q = toJacobian D (Subtype.mk (single (Point.iota δ₀) - single δ₀ : Divisor H)
      (single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀))
  as_ua : Polynomial (F p)
  hua : as_ua = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C as_coeffs.coeff_ua1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C as_coeffs.coeff_ua0 : Polynomial (F p))
  as_Ra : H.Point
  hua_eq : as_ua = (Polynomial.X - Polynomial.C as_Ra.X) ^ 2
  hRaY : as_Ra.Y = as_va.eval as_Ra.X
  hSanchorMem : ∀ Q ∈ as_Sanchor, as_ua.eval Q.X = 0 ∧ Q.Y = as_va.eval Q.X
  hRamem : as_Ra ∈ as_Sanchor
  as_T1 : H.Point
  as_T2 : H.Point
  hT12Xne : as_T1.X ≠ as_T2.X
  hT1Root : as_u.IsRoot as_T1.X
  hT2Root : as_u.IsRoot as_T2.X
  hT1Y : as_T1.Y = as_v.eval as_T1.X
  hT2Y : as_T2.Y = as_v.eval as_T2.X
  hchar : (2 : F p) ≠ 0
  as_Uco : Polynomial (F p)
  as_UcoT : Polynomial (F p)
  hAU : pairNorm H (-as_va) (1 : Polynomial (F p)) = as_ua * as_Uco
  hUco_ne : as_Uco ≠ 0
  hUco_evalRa : as_Uco.eval as_Ra.X ≠ 0
  hAUT : pairNorm H (-as_v) (1 : Polynomial (F p)) = as_u * as_UcoT
  hUcoT_ne : as_UcoT ≠ 0
  hUcoT_evalT1 : as_UcoT.eval as_T1.X ≠ 0
  hUcoT_evalT2 : as_UcoT.eval as_T2.X ≠ 0
  hRaY_ne : as_Ra.Y ≠ 0
  hT1Y_ne : as_T1.Y ≠ 0
  hT2Y_ne : as_T2.Y ≠ 0
  hDP : ((2 : ℤ) • single as_Ra - single sa.P1 - single sa.P2 -
      single as_T1 - single as_T2 + single δ₀ + single (Point.iota δ₀) : Divisor H) ∈ D.P


-- Isolate the expensive specialized divisor-arithmetic elaboration from the
-- large dependent assembly theorem.  This is intentionally a separate
-- declaration: the main theorem then only unifies against its small result.
set_option maxHeartbeats 800000 in
theorem tangent_anchor_sum_of_data
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    (hchar : (2 : F p) ≠ 0)
    (ua0 ua1 va0 va1 : F p)
    (Ra : H.Point)
    (hua_eq : (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X +
      Polynomial.C ua0 : Polynomial (F p)) =
      (Polynomial.X - Polynomial.C Ra.X) ^ 2)
    (va : Polynomial (F p)) (hva : va =
      (Polynomial.C va1 : Polynomial (F p)) * Polynomial.X +
        (Polynomial.C va0 : Polynomial (F p)))
    (Uco : Polynomial (F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X +
        Polynomial.C ua0 : Polynomial (F p)) * Uco)
    (hUco_ne : Uco ≠ 0)
    (hRaY_ne : Ra.Y ≠ 0)
    (hRa : Ra.Y = va.eval Ra.X)
    (hUco_evalRa : Uco.eval Ra.X ≠ 0)
    (Sanchor : Finset H.Point)
    (hSanchorEq : Sanchor = ({Ra} : Finset H.Point)) :
    divToPair (H := H) (-va) 1 Sanchor = (2 : ℤ) • single Ra := by
  -- The callee's `hua_eq` is stated in the specific `-2*R`/`R*R` coefficient
  -- shape (so its implicit `R`/`va0`/`va1` unify off the coefficients
  -- syntactically), not our general `ua1`/`ua0` shape. Deriving the
  -- specific-shape equation explicitly (via `ua1 = -2*Ra.X`, `ua0 =
  -- Ra.X*Ra.X`, both extracted from `hua_eq` by comparing coefficients)
  -- avoids forcing this through `isDefEq` unification, which is what was
  -- timing out.
  -- Extract `ua1`/`ua0` from `hua_eq` by evaluating at two points rather than
  -- comparing `coeff`s directly — `simp` normal forms for `Polynomial.coeff`
  -- on `(X - C Ra.X)^2` don't fully collapse, leaving an unreduced
  -- `(C Ra.X ^ 2).coeff _` residue that `simpa`/`linarith` alone can't close.
  -- Evaluation avoids this: `Polynomial.eval` reduces cleanly. Note `F p` is
  -- a finite field, not a linear order, so `linarith`/`nlinarith` don't
  -- apply here — everything below is closed with `ring`-based reasoning
  -- (`linear_combination`) instead.
  have heval0 : ua0 = Ra.X ^ 2 := by
    have h := congrArg (fun q => Polynomial.eval 0 q) hua_eq
    simpa using h
  have hevalNeg1 : 1 - ua1 + ua0 = (Ra.X + 1) ^ 2 := by
    have h := congrArg (fun q => Polynomial.eval (-1) q) hua_eq
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_sub] at h
    linear_combination h
  have hcoeff1 : ua1 = -2 * Ra.X := by linear_combination heval0 - hevalNeg1
  have hcoeff0 : ua0 = Ra.X * Ra.X := by linear_combination heval0
  have hua_eq' : (Polynomial.X ^ 2 + Polynomial.C (-2 * Ra.X) * Polynomial.X +
      Polynomial.C (Ra.X * Ra.X) : Polynomial (F p)) =
      (Polynomial.X - Polynomial.C Ra.X) ^ 2 := by
    rw [← hcoeff1, ← hcoeff0]
    exact hua_eq
  have hAU' : pairNorm H (-va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C (-2 * Ra.X) * Polynomial.X +
        Polynomial.C (Ra.X * Ra.X) : Polynomial (F p)) * Uco := by
    rw [← hcoeff1, ← hcoeff0]
    exact hAU
  exact divToPair_negVa_one_Sanchor_eq_tangent (H := H) hchar hua_eq'
    va hva Uco hAU' hUco_ne Ra hRaY_ne rfl hRa hUco_evalRa Sanchor hSanchorEq

-- Same isolation for the target-side divisor sum.  Keeping this application
-- outside the final theorem prevents its large hypothesis bundle from being
-- re-elaborated while the final equality is checked.
set_option maxHeartbeats 800000 in
theorem target_sum_of_data
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    (hchar : (2 : F p) ≠ 0)
    (c0 c1 c2 c3 c4 : F p)
    (u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hufree : Squarefree
      (Polynomial.X ^ 2 + Polynomial.C u1 * Polynomial.X + Polynomial.C u0 : Polynomial (F p)))
    (v : Polynomial (F p))
    (hv : v = (Polynomial.C v1 : Polynomial (F p)) * Polynomial.X + Polynomial.C v0)
    (UcoT : Polynomial (F p))
    (hAUT : pairNorm H (-v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C u1 * Polynomial.X + Polynomial.C u0 : Polynomial (F p)) * UcoT)
    (hUcoT_ne : UcoT ≠ 0)
    (T1 T2 : H.Point) (hT12ne : T1.X ≠ T2.X)
    (hT1Y_ne : T1.Y ≠ 0) (hT2Y_ne : T2.Y ≠ 0)
    (hT1Root :
      (Polynomial.X ^ 2 + Polynomial.C u1 * Polynomial.X + Polynomial.C u0 : Polynomial (F p)).IsRoot T1.X)
    (hT2Root :
      (Polynomial.X ^ 2 + Polynomial.C u1 * Polynomial.X + Polynomial.C u0 : Polynomial (F p)).IsRoot T2.X)
    (hT1Y : T1.Y = v.eval T1.X) (hT2Y : T2.Y = v.eval T2.X)
    (hUcoT_evalT1 : UcoT.eval T1.X ≠ 0) (hUcoT_evalT2 : UcoT.eval T2.X ≠ 0)
    (S : Finset H.Point)
    (hSEq : S = ({T1, T2} : Finset H.Point)) :
    divToPair (H := H) (-v) 1 S = single T1 + single T2 := by
  -- The callee's `hT12ne` is point-level (`T1cur ≠ T2cur`), while this
  -- theorem's own `hT12ne` is X-coordinate-level (`T1.X ≠ T2.X`, matching
  -- how the caller derives it). Points differing in `X` certainly differ
  -- as points, but the two propositions aren't defeq, so derive the
  -- point-level fact explicitly rather than passing the X-level one
  -- straight through.
  have hT12ne' : T1 ≠ T2 := fun h => hT12ne (by rw [h])
  exact DecoupledSystem.divToPair_negV_one_S_eq (H := H) hchar
    (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
    (u0 := u0) (u1 := u1) (v0 := v0) (v1 := v1)
    hf hMumfordTarget hufree v hv UcoT hAUT hUcoT_ne
    T1 T2 hT12ne' hT1Y_ne hT2Y_ne hT1Root hT2Root hT1Y hT2Y
    hUcoT_evalT1 hUcoT_evalT2 S hSEq

/--
Tangent-anchor assembly, with the expensive hypotheses bundled before the
main theorem is elaborated.  `hDP` should normally be produced by
`hDP_tangent_aux`; all of the CA-witness side conditions needed for that
construction are intentionally absent from this theorem's signature.
-/
theorem reducedClass_eq_of_isReduction'_tangent
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (base : TangentReductionData sa)
    (d : TangentAssemblyData sa)
    (hcoeff : d.as_coeffs = base.coeffs) :
    sa.reducedClass + d.as_q =
      toJacobian D (Subtype.mk (divToPair (H := H) (-d.as_v) 1 d.as_S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) d.hmem) := by
  classical
  -- `hcoeff : d.as_coeffs = base.coeffs` is an equality between two
  -- structure PROJECTIONS, not a free local variable, so `cases`/`subst`
  -- on it attempts dependent elimination against the ambient goal and
  -- fails ("Dependent elimination failed ... base.1 = d.1"). Rewrite with
  -- it only where actually needed instead (`hua_eq_spelled` below, the
  -- one place `base.coeffs` and `d.as_coeffs`-derived facts must line up).
  have hSanchorEq : d.as_Sanchor = ({d.as_Ra} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots_tangent d.as_ua d.as_va d.as_Ra d.hua_eq d.hRaY
      d.as_Sanchor d.hSanchorMem d.hRamem
  -- Stated against `d.as_coeffs` (not `base.coeffs`) since that's what's
  -- actually passed positionally to `tangent_anchor_sum_of_data` below —
  -- no `hcoeff` rewrite needed here.
  have hua_eq_spelled :
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X +
        Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) =
        (Polynomial.X - Polynomial.C d.as_Ra.X) ^ 2 := by
    rw [← d.hua]
    exact d.hua_eq
  have hT12ne : d.as_T1 ≠ d.as_T2 := fun h => d.hT12Xne (by rw [h])
  have hSEq : d.as_S = ({d.as_T1, d.as_T2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots
      (ua0 := sa.toSampleTarget.u0) (ua1 := sa.toSampleTarget.u1)
      d.as_u d.as_v d.hu d.hufree d.as_T1 d.as_T2 hT12ne d.hT12Xne
      ⟨d.hT1Root, d.hT2Root⟩ d.hT1Y d.hT2Y d.as_S d.hSmem d.hScard
  have hufree' : Squarefree (Polynomial.X ^ 2 +
      Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
      Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) := by
    rw [← d.hu]
    exact d.hufree
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
  have hAUT' : pairNorm H (-d.as_v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) * d.as_UcoT := by
    rw [← d.hu]
    exact d.hAUT
  have hAU' : pairNorm H (-d.as_va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C d.as_coeffs.coeff_ua1 * Polynomial.X +
        Polynomial.C d.as_coeffs.coeff_ua0 : Polynomial (F p)) * d.as_Uco := by
    rw [← d.hua]
    exact d.hAU
  have hSanchorSum : divToPair (H := H) (-d.as_va) 1 d.as_Sanchor =
      (2 : ℤ) • single d.as_Ra := by
    exact tangent_anchor_sum_of_data (H := H) d.hchar
      d.as_coeffs.coeff_ua0 d.as_coeffs.coeff_ua1
      d.as_coeffs.coeff_va0 d.as_coeffs.coeff_va1 d.as_Ra
      hua_eq_spelled d.as_va d.hva d.as_Uco hAU' d.hUco_ne
      d.hRaY_ne d.hRaY d.hUco_evalRa d.as_Sanchor hSanchorEq
  have hSSum : divToPair (H := H) (-d.as_v) 1 d.as_S = single d.as_T1 + single d.as_T2 := by
    exact target_sum_of_data (H := H) d.hchar
      base.coeffs.coeff_c0 base.coeffs.coeff_c1 base.coeffs.coeff_c2
      base.coeffs.coeff_c3 base.coeffs.coeff_c4
      sa.toSampleTarget.u0 sa.toSampleTarget.u1
      sa.toSampleTarget.v0 sa.toSampleTarget.v1
      base.coeffs.coeff_hf base.coeffs.coeff_hMumfordTarget hufree' d.as_v d.hv d.as_UcoT
      hAUT' d.hUcoT_ne d.as_T1 d.as_T2 d.hT12Xne d.hT1Y_ne d.hT2Y_ne
      hT1Root' hT2Root' d.hT1Y d.hT2Y d.hUcoT_evalT1 d.hUcoT_evalT2
      d.as_S hSEq
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
      -- Same `show`-not-`rw` fix as `hcoe` below: `aP1P2Nι`/`aQ` are `set`
      -- defs, definitionally equal to their `⟨_, _⟩` RHS, so unfold via
      -- `show` rather than `rw [haP1P2Nι_def, haQ_def]` (which hits the
      -- same coercion motive failure).
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
        ((2 : ℤ) • single d.as_Ra - single sa.P1 - single sa.P2 -
          single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀) : Divisor H) := by
      show (aAnchor.1 - aP1P2Nι.1) - aTarget.1 =
        (2 : ℤ) • single d.as_Ra - single sa.P1 - single sa.P2 -
          single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀)
      -- `aAnchor`/`aP1P2Nι`/`aTarget` are `set`-introduced, so they are
      -- DEFINITIONALLY equal to their RHS `⟨_, _⟩` terms — unfolding via
      -- `show` (definitional) rather than `rw [haAnchor_def, ...]` avoids
      -- the "motive is not type correct" failure that `rw` hits here: the
      -- membership proof bundled inside each `Subtype.mk` doesn't survive
      -- `rw`'s syntactic abstraction once the goal has passed through the
      -- `↑`/`.1` coercion.
      show (divToPair (H := H) (-d.as_va) 1 d.as_Sanchor -
          (single δ₀ + single (Point.iota δ₀)) -
          (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀)))) -
          (divToPair (H := H) (-d.as_v) 1 d.as_S -
            (single δ₀ + single (Point.iota δ₀))) =
        (2 : ℤ) • single d.as_Ra - single sa.P1 - single sa.P2 -
          single d.as_T1 - single d.as_T2 + single δ₀ + single (Point.iota δ₀)
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
