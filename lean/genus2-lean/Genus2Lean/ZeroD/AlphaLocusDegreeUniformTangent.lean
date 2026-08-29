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
  `2•[Ra]-[P1]-[P2]-[T1cur]-[T2cur]+[δ₀]+[ιδ₀] ∈ D.P` (Step 4's corrected,
  REPL-confirmed shape, matching the split case's own shape exactly once
  `Ra1+Ra2` collapses to `2•Ra` — no leftover `-[T1]-[T2]` terms, per that
  file's docstring).

`derivative H.f` (the tangency-row value `hRaDeriv` pins down) is factored
into its own `hfDeriv`/`hfDeriv_eq` binder pair rather than appearing
inline — see the note at that binder for why (`whnf` timeout diagnosis).

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

-- **`maxHeartbeats` bump.** Same signature-elaboration cost the split
-- theorem's own file hit (`AlphaLocusDegreeUniform.lean`'s note on
-- `reducedClass_eq_of_isReduction'`) — this theorem's signature is that
-- one's, so it times out at the default limit for the same reason (a
-- `whnf` timeout on the declaration itself, not a tactic-block issue).
-- Placed above the doc comment, per project convention (`set_option`/
-- `omit` go above the `/--`, never between it and the theorem).
-- **Testing at the split file's own `800000` first**, now that
-- `derivative H.f` is factored out of `hRaDeriv`'s type into its own
-- `hfDeriv`/`hfDeriv_eq` binder (see that binder's comment) — if the
-- `derivative`-headed subterm was the actual driver of the extra cost
-- over the split theorem's signature, this should build at the same
-- budget the split theorem needed. Bump further only if this still
-- times out.
set_option maxHeartbeats 800000 in
/-- **Tangent-anchor sibling of `reducedClass_eq_of_isReduction'`**: same
conclusion, `Ra1 = Ra2` (one doubled anchor point `Ra`, tangency data
`hua_eq`/`hRaY`/`hRaDeriv` in place of the split case's `hRa12Xne` pair).
Proof is the split theorem's proof verbatim with the anchor-side collapse
lemmas swapped for their tangent counterparts (see module docstring); the
target side (`T1,T2`/`u`/`v`/`S`) is untouched. -/
theorem reducedClass_eq_of_isReduction'_tangent {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
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
    (hmem : (divToPair (H := H) (-v) 1 S -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H)
    (q : Jacobian H D)
    (hq : q = toJacobian D (Subtype.mk (single (Point.iota δ₀) - single δ₀ : Divisor H)
      (single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀)) )
    -- **The tangent-anchor data, replacing the split theorem's
    -- `Ra1 Ra2 hRa12Xne hRa1Root hRa2Root hRa1Y hRa2Y`.** `Ra` is
    -- `Sanchor`'s single doubled root; `ua`/`hua` name the anchor
    -- quadratic explicitly (mirroring the split theorem's own `ua`/`hua`
    -- pair), and `hua_eq` states that quadratic's factored form directly
    -- (caller-supplied, matching `Sanchor_eq_of_anchor_roots_tangent`'s
    -- own documented convention — not derived from `Squarefree ua`,
    -- which would be false for a genuine double root). `vaDerivAtRa`/
    -- `hRaDeriv` supply the tangency row's derivative value, matching
    -- `cAmιTmδmιδ_mem_of_le_tangent`'s own `hRaDeriv` parameter.
    (ua : Polynomial (F p))
    (hua : ua = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C ua1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C ua0 : Polynomial (F p)))
    (Ra : H.Point)
    (hua_eq : ua = (Polynomial.X - Polynomial.C Ra.X) ^ 2)
    (hRaY : Ra.Y = va.eval Ra.X)
    (hSanchorMem : ∀ Q ∈ Sanchor, ua.eval Q.X = 0 ∧ Q.Y = va.eval Q.X)
    (hRamem : Ra ∈ Sanchor)
    (vaDerivAtRa : F p)
    -- **`derivative H.f` factored into its own binder** (`hfDeriv`/
    -- `hfDeriv_eq`) rather than appearing inline inside `hRaDeriv`'s type.
    -- Diagnostic per Claire's REPL (`whnf` timeout moved from the
    -- `set_option` line to the `theorem` line itself even at 1600000
    -- heartbeats): `derivative` is not `@[reducible]`, and unlike the
    -- split theorem's signature (which never mentions `derivative` at
    -- all), this is the one term here that forces the elaborator to
    -- carry an unreduced `derivative`-headed subterm through the rest of
    -- signature checking. Naming it once and stating `hRaDeriv` against
    -- the name instead should let elaboration treat it as opaque from
    -- the start rather than repeatedly revisiting `derivative H.f`.
    (hfDeriv : Polynomial (F p))
    (hfDeriv_eq : hfDeriv = derivative H.f)
    (hRaDeriv : 2 * Ra.Y * vaDerivAtRa = hfDeriv.eval Ra.X)
    (T1 T2 : H.Point)
    (hT12Xne : T1.X ≠ T2.X)
    (hT1Root : u.IsRoot T1.X) (hT2Root : u.IsRoot T2.X)
    (hT1Y : T1.Y = v.eval T1.X) (hT2Y : T2.Y = v.eval T2.X)
    [DecidableEq H.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (Uco UcoT : Polynomial (F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (F p)) = ua * Uco)
    (hUco_ne : Uco ≠ 0)
    (hUco_evalRa : Uco.eval Ra.X ≠ 0)
    (hAUT : pairNorm H (-v) (1 : Polynomial (F p)) = u * UcoT)
    (hUcoT_ne : UcoT ≠ 0)
    (hUcoT_evalT1 : UcoT.eval T1.X ≠ 0) (hUcoT_evalT2 : UcoT.eval T2.X ≠ 0)
    (hRaY_ne : Ra.Y ≠ 0)
    (hT1Y_ne : T1.Y ≠ 0) (hT2Y_ne : T2.Y ≠ 0)
    -- **The `CAWitness` identification, tangent case**: `ua,va` ARE
    -- `uCANewTangent,-bCATangent` built from `Ra,sa.P1,sa.P2`.
    (hdet : (caTangentInterpMatrix Ra.X sa.P1.X sa.P2.X).det ≠ 0)
    (hlead : caTangentCoeff Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y 3 ≠ 0)
    (h1P1 : Ra.X ≠ sa.P1.X) (h1P2 : Ra.X ≠ sa.P2.X) (hPP : sa.P1.X ≠ sa.P2.X)
    (hRa_curve : Ra.Y ^ 2 = H.f.eval Ra.X)
    (hP1_curve : sa.P1.Y ^ 2 = H.f.eval sa.P1.X) (hP2_curve : sa.P2.Y ^ 2 = H.f.eval sa.P2.X)
    (hP1Y_ne : sa.P1.Y ≠ 0) (hP2Y_ne : sa.P2.Y ≠ 0)
    (hne : H.f - (bCATangent Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y) ^ 2 ≠ 0)
    -- **`uCANewTangent H Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y
    -- sa.P2.Y` factored into its own binder** (`uCA`/`uCA_eq`) rather
    -- than appearing inline 8 times below. Test 1 (factoring `derivative
    -- H.f` out of `hRaDeriv`) did not fix the `whnf` timeout (Claire's
    -- REPL, still timed out at the split file's own `800000` budget), so
    -- this is Test 2: the repeated fully-applied `uCANewTangent` term is
    -- the other concrete structural difference from the split theorem's
    -- signature (which never repeats `uCANew`'s application against the
    -- SAME `Uco`/tangent-specific args this many times inline — the
    -- split file's own 9 occurrences of `uCANew H Ra1.X Ra2.X sa.P1.X
    -- sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y` are structurally the same
    -- pattern, so if this doesn't help either, the two files' cost is
    -- close enough that neither factoring alone explains the gap, and
    -- the fix is confirmed to be finding out concretely, not guessing
    -- further). Named once here; used as-is in the 8 hypotheses below,
    -- and unfolded via `uCA_eq` only where the proof body needs the
    -- expanded form (currently nowhere — all 8 pass through by name to
    -- `cAmιTmδmιδ_mem_of_le_tangent`'s own like-named binders).
    (uCA : Polynomial (F p))
    (uCA_eq : uCA = uCANewTangent H Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y)
    (hU_evalRa : uCA.eval Ra.X ≠ 0)
    (hU_evalP1 : uCA.eval sa.P1.X ≠ 0)
    (hU_evalP2 : uCA.eval sa.P2.X ≠ 0)
    (hU_ne0 : uCA ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hPtT1X : PtT1.X ≠ PtT2.X)
    (hPtT1 : uCA.IsRoot PtT1.X)
    (hPtT2 : uCA.IsRoot PtT2.X)
    (Q1 Q2 : Polynomial (F p))
    (hQ1_def : uCA =
      (Polynomial.X - Polynomial.C PtT1.X) * (Polynomial.X - Polynomial.C PtT2.X) * Q1)
    (hQ1T1 : Q1.eval PtT1.X ≠ 0)
    (hQ2_def : uCA =
      (Polynomial.X - Polynomial.C PtT2.X) * (Polynomial.X - Polynomial.C PtT1.X) * Q2)
    (hQ2T2 : Q2.eval PtT2.X ≠ 0)
    (hAeval1 : (denomPolyCATangent Ra.X sa.P1.X sa.P2.X : Polynomial (F p)).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCATangent Ra.X sa.P1.X sa.P2.X : Polynomial (F p)).eval PtT2.X ≠ 0)
    (hPtT1Y : PtT1.Y = (bCATangent Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2Y : PtT2.Y = (bCATangent Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hRaT1 : Ra.X ≠ PtT1.X) (hRaT2 : Ra.X ≠ PtT2.X)
    (hP1T1 : sa.P1.X ≠ PtT1.X) (hP1T2 : sa.P1.X ≠ PtT2.X)
    (hP2T1 : sa.P2.X ≠ PtT1.X) (hP2T2 : sa.P2.X ≠ PtT2.X)
    (h1δ : PtT1.X ≠ δ₀.X) (h2δ : PtT2.X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hT1eq : T1 = Point.iota PtT1) (hT2eq : T2 = Point.iota PtT2)
    (hsupp_f : ∀ P, P ∉ ({Ra, Point.iota sa.P1, Point.iota sa.P2, PtT1, PtT2} :
        Finset H.Point) →
      ordAt P (-bCATangent Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y) (1 : Polynomial (F p)) = 0)
    (hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCATangent Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({Ra, Point.iota sa.P1, Point.iota sa.P2, PtT1, PtT2} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCATangent Ra.X sa.P1.X sa.P2.X Ra.Y vaDerivAtRa sa.P1.Y sa.P2.Y)
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
  -- **`Sanchor`'s own split, tangent case**: `Sanchor = {Ra}`, via
  -- `Sanchor_eq_of_anchor_roots_tangent` (membership-only, no
  -- cardinality — see that lemma's own docstring for why the split
  -- lemma's `hSanchorCard` route does not apply here). `hua_eq`/
  -- `hSanchorMem` are already stated directly against `ua`, no bridging
  -- needed.
  have hSanchorEq : Sanchor = ({Ra} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots_tangent ua va Ra hua_eq hRaY Sanchor hSanchorMem hRamem
  -- **The spelled-quadratic-equals-square fact `divToPair_negVa_one_
  -- Sanchor_eq_tangent` actually wants** (in terms of `ua`'s own
  -- `ua0,ua1`, via transitivity of `hua` and `hua_eq` — not a fresh
  -- assumption, just the two already-given equalities for `ua`
  -- composed).
  have hua_eq_spelled :
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)) =
        (Polynomial.X - Polynomial.C Ra.X) ^ 2 := hua ▸ hua_eq
  -- **`S`'s own split** — unchanged from the split theorem, `T1,T2` are
  -- still genuinely distinct (the tangent case is scoped to the anchor
  -- only).
  have hT12ne : T1 ≠ T2 := fun h => hT12Xne (by rw [h])
  have hSEq : S = ({T1, T2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots (ua0 := sa.toSampleTarget.u0) (ua1 := sa.toSampleTarget.u1)
      u v hu hufree
      T1 T2 hT12ne hT12Xne ⟨hT1Root, hT2Root⟩ hT1Y hT2Y S hSmem hScard
  have hufree' : Squarefree (Polynomial.X ^ 2 +
      Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
      + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) := hu ▸ hufree
  have hT1Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot T1.X := by
    rw [← hu]
    exact hT1Root
  have hT2Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot T2.X := by
    rw [← hu]
    exact hT2Root
  have hAUT' : pairNorm H (-v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
        + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) * UcoT :=
    hu ▸ hAUT
  -- **Anchor-side collapse, tangent case**: `divToPair (-va) 1 Sanchor =
  -- 2 • single Ra`.
  have hAU' : pairNorm H (-va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X
        + Polynomial.C ua0 : Polynomial (F p)) * Uco := by
    rw [← hua]; exact hAU
  have hSanchorSum : divToPair (H := H) (-va) 1 Sanchor = (2 : ℤ) • single Ra :=
    divToPair_negVa_one_Sanchor_eq_tangent (H := H) hchar hua_eq_spelled
      va hva Uco hAU' hUco_ne Ra hRaY_ne rfl hRaY hUco_evalRa Sanchor hSanchorEq
  have hSSum : divToPair (H := H) (-v) 1 S = single T1 + single T2 :=
    DecoupledSystem.divToPair_negV_one_S_eq (H := H) hchar
      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (u0 := sa.toSampleTarget.u0) (u1 := sa.toSampleTarget.u1)
      (v0 := sa.toSampleTarget.v0) (v1 := sa.toSampleTarget.v1)
      hf hMumfordTarget hufree' v hv UcoT hAUT' hUcoT_ne
      T1 T2 hT12ne hT1Y_ne hT2Y_ne hT1Root' hT2Root' hT1Y hT2Y
      hUcoT_evalT1 hUcoT_evalT2 S hSEq
  -- **The concrete-coordinate assembly (†), tangent case**: `2•[Ra] -
  -- [P1] - [P2] - ι(T1) - ι(T2) + [δ₀] + [ιδ₀] ∈ D.P`.
  have hDP := cAmιTmδmιδ_mem_of_le_tangent (H := H) hdeg hchar hsf D hD
    hspec_linX
    Ra.X sa.P1.X sa.P2.X Ra.Y sa.P1.Y sa.P2.Y vaDerivAtRa
    hdet hlead h1P1 h1P2 hPP
    hRa_curve hP1_curve hP2_curve (hfDeriv_eq ▸ hRaDeriv)
    hRaY_ne hP1Y_ne hP2Y_ne
    Ra sa.P1 sa.P2 (Point.iota sa.P1) (Point.iota sa.P2)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hne (uCA_eq ▸ hU_evalRa) (uCA_eq ▸ hU_evalP1) (uCA_eq ▸ hU_evalP2)
    PtT1.X PtT2.X (uCA_eq ▸ hPtT1) (uCA_eq ▸ hPtT2) hPtT1X (uCA_eq ▸ hU_ne0)
    Q1 Q2 (uCA_eq ▸ hQ1_def) hQ1T1 (uCA_eq ▸ hQ2_def) hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2 rfl hPtT1Y hPtT1Y_ne rfl hPtT2Y hPtT2Y_ne
    hRaT1 hRaT2 hP1T1 hP1T2 hP2T1 hP2T2 h1δ h2δ hδY hsupp_f hspec_f hsupp_hT hspec_hT
    T1 T2 hT1eq hT2eq
  -- **Bridge `D.P` membership to a `toJacobian` equation** — identical to
  -- the split theorem from here, `hSanchorSum` now giving `2•single Ra`
  -- in place of `single Ra1 + single Ra2`.
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
      ((2 : ℤ) • single Ra - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    show (aAnchor.1 - aP1P2Nι.1) - aTarget.1 =
      (2 : ℤ) • single Ra - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
    rw [haAnchor_def, haP1P2Nι_def, haTarget_def]
    show (divToPair (H := H) (-va) 1 Sanchor - (single δ₀ + single (Point.iota δ₀))) -
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) -
        (divToPair (H := H) (-v) 1 S - (single δ₀ + single (Point.iota δ₀))) =
      (2 : ℤ) • single Ra - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
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
