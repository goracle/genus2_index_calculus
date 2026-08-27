import Mathlib
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.PrincipalWitnessAssembly

/-!
# Step 1 of `ROADMAP-principal-witness-assembly.md`: `div_aff(g) = A+C+T`

Per that roadmap's "Concrete next steps, in order", step 1: prove
`div_aff(g) = A+C+T` (and record the residual-side companion fact used for
`div_aff(u_new) = ρ+I`) via `eq_of_coeffAt_eq`/`coeffAt_divToPair`/
`coeffAt_single` (`PrincipalWitness.lean`), composing the six bare-`ordAt`
point-composition theorems already on file in `PrincipalWitnessAssembly.lean`.
Scoped, per that roadmap's own "Practical scoping for step 1" note, to the
FULLY-SPLIT case only (`hRne`/`hRane` both hold, i.e. neither `ua` nor
`u_target` has a repeated root) — the two repeated-root branches are
explicitly deferred there and are not attempted here either.

**Why this file exists separately from both `AlphaLocusDegreeUniform.lean`
and `PrincipalWitnessAssembly.lean`, rather than living in either.**
`PrincipalWitnessAssembly.lean` already imports `AlphaLocusDegreeUniform.lean`
(to state its six point-composition theorems against `SampleTargetFromAlpha`'s
ambient data). That makes `AlphaLocusDegreeUniform.lean → PrincipalWitnessAssembly.lean`
an import cycle, so `reducedClass_eq_of_isReduction'`'s proof (which needs
`PrincipalWitnessAssembly.lean`'s six theorems) cannot be filled in *inside*
`AlphaLocusDegreeUniform.lean` itself, where the theorem currently lives.
This is the same shape of problem `GeneralSharedRoot.lean`'s own trailing
note already flags having fixed once (relocating `npoly4Lcm4`/`uRS4General`/
`vRS4General` out of `PrincipalWitnessAssembly.lean` to break a cycle there)
— the fix here is the same idea: a new downstream leaf file importing both
sides. **`reducedClass_eq_of_isReduction'` itself is NOT filled in here**
(steps 2-5 of the roadmap are not yet worked out — see the roadmap's own
"Concrete next steps" items 2-4, in particular the still-open structural
question in item 4), but this file's lemma is genuine, real progress
toward it: once steps 2-4 are worked out, it composes with what is proved
here.

**What "`div_aff(g) = A+C+T`" means as an actual `Divisor Hc` equality.**
`A+C+T` is the divisor putting coefficient `1` on each of the six named
points `P1,P2` (`A`), `Ra1,Ra2` (`C`, `ua`'s roots), `R1,R2` (`T`,
`u_target`'s roots per the roadmap's corrected notation) and `0`
everywhere else — i.e. `single Pt1 + single Pt2 + single PtRa1 +
single PtRa2 + single PtR1 + single PtR2` as a literal `Divisor Hc` value.
The theorem below shows `divToPair E Y S = ` that sum, for `S` the
six-point `Finset`, `E,Y := Epoly4,Ypoly4`, i.e. `g`'s own affine divisor,
restricted to `S`, literally equals `A+C+T` — not merely "has value 1 at
each of the six points and value 0 elsewhere", which would leave open
whether `divToPair`'s definition secretly means something else; this
theorem is the actual `Divisor Hc`-level statement `eq_of_coeffAt_eq`
concludes. -/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {Hc : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing Hc)]

/-- **`div_aff(g) = A+C+T`, fully-split case: the literal `Divisor Hc`
equality.** `E,Y` are `Epoly4`/`Ypoly4` (via `hE_def`/`hY_def`); the six
named points are `P1,P2` (the interpolation points, `A`), `Ra1,Ra2` (`ua`'s
two roots, `C`), `R1,R2` (`u_target`'s two roots, `T`) — literally the
roadmap's `A + C + T`, `T := [R1]+[R2]`, per the roadmap's own corrected
notation. Each hypothesis block below is exactly one of
`PrincipalWitnessAssembly.lean`'s existing bare-`ordAt` theorems'
hypothesis list (`ordAt_eq_one_of_P1`/`_P2`/`_Ra1`/`_Ra2`/`_R1`/`_R2`); the
proof composes all six via `coeffAt_divToPair`/`coeffAt_single` +
`eq_of_coeffAt_eq`, case-splitting the query point `P` on whether it
equals one of the six named points (using `hPtDistinct`, the six points'
pairwise distinctness, itself derived from the `F p`-level distinctness
hypotheses already supplied) or none of them. -/
theorem divToPair_eq_A_add_C_add_T_of_split
    [DecidableEq Hc.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree Hc.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : Hc.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra1 Ra2 R1 R2 : F p)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (h12 : P1.1 ≠ P2.1)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (hRa1P1 : Ra1 ≠ P1.1) (hRa1P2 : Ra1 ≠ P2.1)
    (hRa1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra1 = 0)
    (hRa2P1 : Ra2 ≠ P1.1) (hRa2P2 : Ra2 ≠ P2.1)
    (hRa2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra2 = 0)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (hR1P1 : R1 ≠ P1.1) (hR1P2 : R1 ≠ P2.1)
    (hR1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R1 = 0)
    (hR2P1 : R2 ≠ P1.1) (hR2P2 : R2 ≠ P2.1)
    (hR2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R2 = 0)
    -- `Ra1 ≠ R1`, `Ra1 ≠ R2`, `Ra2 ≠ R1`, `Ra2 ≠ R2`: NOT re-derivable from
    -- `hnoroot34` alone at the level this file states things (`hnoroot34`
    -- says `ua`/`u_target` share no root, but `Ra1`/`Ra2` being roots of
    -- `ua` and `R1`/`R2` roots of `u_target` are only *assumed* via
    -- `huaRoot1`/`huaRoot2`/`htargetRoot1`/`htargetRoot2` — nothing above
    -- forces those specific values apart without this hypothesis spelled
    -- out, since `hnoroot34` is stated as a `¬∃`, not unfolded against
    -- these four named values automatically). Supplied directly rather
    -- than re-derived, matching this file's general policy of taking
    -- `PrincipalWitnessAssembly.lean`'s own hypothesis shapes as given.
    (hRa1R1 : Ra1 ≠ R1) (hRa1R2 : Ra1 ≠ R2) (hRa2R1 : Ra2 ≠ R1) (hRa2R2 : Ra2 ≠ R2)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hYP2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hYRa1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra1 ≠ 0)
    (hYRa2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra2 ≠ 0)
    (hYR1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (hYR2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (hU_evalP1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hU_evalP2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hU_evalRa1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra1 ≠ 0)
    (hU_evalRa2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra2 ≠ 0)
    (hU_evalR1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (hU_evalR2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (Pt1 Pt2 PtRa1 PtRa2 PtR1 PtR2 : Hc.Point)
    (hPt1X : Pt1.X = P1.1) (hPt1Y : Pt1.Y = P1.2) (hPt1Y_ne : Pt1.Y ≠ 0)
    (hPt2X : Pt2.X = P2.1) (hPt2Y : Pt2.Y = P2.2) (hPt2Y_ne : Pt2.Y ≠ 0)
    (hPtRa1X : PtRa1.X = Ra1) (hPtRa1Y : PtRa1.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra1)
    (hPtRa1Y_ne : PtRa1.Y ≠ 0)
    (hPtRa2X : PtRa2.X = Ra2) (hPtRa2Y : PtRa2.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra2)
    (hPtRa2Y_ne : PtRa2.Y ≠ 0)
    (hPtR1X : PtR1.X = R1) (hPtR1Y : PtR1.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R1)
    (hPtR1Y_ne : PtR1.Y ≠ 0)
    (hPtR2X : PtR2.X = R2) (hPtR2Y : PtR2.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R2)
    (hPtR2Y_ne : PtR2.Y ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    divToPair E Y ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) =
      single Pt1 + single Pt2 + single PtRa1 + single PtRa2 + single PtR1 + single PtR2 := by
  -- The six pointwise `ordAt = 1` facts, one per named point.
  have hOrd1 : ordAt Pt1 E Y = 1 :=
    ordAt_eq_one_of_P1 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Pt1 hPt1X hPt1Y hPt1Y_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYP1_ne hU_evalP1
      E Y A hE_def hY_def hA_def
  have hOrd2 : ordAt Pt2 E Y = 1 :=
    ordAt_eq_one_of_P2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Pt2 hPt2X hPt2Y hPt2Y_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYP2_ne hU_evalP2
      E Y A hE_def hY_def hA_def
  have hOrdRa1 : ordAt PtRa1 E Y = 1 :=
    ordAt_eq_one_of_Ra1 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Ra1 Ra2 huaRoot1 huaRoot2 hRane PtRa1 hPtRa1X hPtRa1Y hPtRa1Y_ne
      h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target hRa1P1 hRa1P2 hRa1target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYRa1_ne hU_evalRa1
      E Y A hE_def hY_def hA_def
  have hOrdRa2 : ordAt PtRa2 E Y = 1 :=
    ordAt_eq_one_of_Ra2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Ra1 Ra2 huaRoot1 huaRoot2 hRane PtRa2 hPtRa2X hPtRa2Y hPtRa2Y_ne
      h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target hRa2P1 hRa2P2 hRa2target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYRa2_ne hU_evalRa2
      E Y A hE_def hY_def hA_def
  have hOrdR1 : ordAt PtR1 E Y = 1 :=
    ordAt_eq_one_of_R1 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 R1 R2 htargetRoot1 htargetRoot2 hRne PtR1 hPtR1X hPtR1Y hPtR1Y_ne
      h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target hR1P1 hR1P2 hR1ua
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYR1_ne hU_evalR1
      E Y A hE_def hY_def hA_def
  have hOrdR2 : ordAt PtR2 E Y = 1 :=
    ordAt_eq_one_of_R2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 R1 R2 htargetRoot1 htargetRoot2 hRne PtR2 hPtR2X hPtR2Y hPtR2Y_ne
      h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target hR2P1 hR2P2 hR2ua
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYR2_ne hU_evalR2
      E Y A hE_def hY_def hA_def
  -- The six named points are pairwise distinct AS `Hc.Point` VALUES: derived
  -- from pairwise distinctness of their `.X` coordinates (an `Hc.Point`
  -- equality forces `.X` equality, so `.X`-distinctness gives `Hc.Point`
  -- distinctness by contraposition).
  have hne_of_X : ∀ {Q1 Q2 : Hc.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have h12' : Pt1 ≠ Pt2 := hne_of_X (hPt1X ▸ hPt2X ▸ h12)
  have hRa1P1' : PtRa1 ≠ Pt1 := hne_of_X (hPtRa1X ▸ hPt1X ▸ hRa1P1)
  have hRa1P2' : PtRa1 ≠ Pt2 := hne_of_X (hPtRa1X ▸ hPt2X ▸ hRa1P2)
  have hRa2P1' : PtRa2 ≠ Pt1 := hne_of_X (hPtRa2X ▸ hPt1X ▸ hRa2P1)
  have hRa2P2' : PtRa2 ≠ Pt2 := hne_of_X (hPtRa2X ▸ hPt2X ▸ hRa2P2)
  have hRane' : PtRa1 ≠ PtRa2 := hne_of_X (hPtRa1X ▸ hPtRa2X ▸ hRane)
  have hR1P1' : PtR1 ≠ Pt1 := hne_of_X (hPtR1X ▸ hPt1X ▸ hR1P1)
  have hR1P2' : PtR1 ≠ Pt2 := hne_of_X (hPtR1X ▸ hPt2X ▸ hR1P2)
  have hR2P1' : PtR2 ≠ Pt1 := hne_of_X (hPtR2X ▸ hPt1X ▸ hR2P1)
  have hR2P2' : PtR2 ≠ Pt2 := hne_of_X (hPtR2X ▸ hPt2X ▸ hR2P2)
  have hRne' : PtR1 ≠ PtR2 := hne_of_X (hPtR1X ▸ hPtR2X ▸ hRne)
  have hRa1R1' : PtRa1 ≠ PtR1 := hne_of_X (hPtRa1X ▸ hPtR1X ▸ hRa1R1)
  have hRa1R2' : PtRa1 ≠ PtR2 := hne_of_X (hPtRa1X ▸ hPtR2X ▸ hRa1R2)
  have hRa2R1' : PtRa2 ≠ PtR1 := hne_of_X (hPtRa2X ▸ hPtR1X ▸ hRa2R1)
  have hRa2R2' : PtRa2 ≠ PtR2 := hne_of_X (hPtRa2X ▸ hPtR2X ▸ hRa2R2)
  -- The six-point support set, fixed once here (before the case split
  -- below) so that no branch needs to re-elaborate the `{Pt1, Pt2, ...}`
  -- `Finset` literal after a `subst` has fired.
  have hmemPt1 : Pt1 ∈ ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) := by simp
  have hmemPt2 : Pt2 ∈ ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) := by simp
  have hmemPtRa1 : PtRa1 ∈ ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) := by simp
  have hmemPtRa2 : PtRa2 ∈ ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) := by simp
  have hmemPtR1 : PtR1 ∈ ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) := by simp
  have hmemPtR2 : PtR2 ∈ ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) := by simp
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, coeffAt_single]
  -- Each named-point branch reduces the six Kronecker-delta terms to a
  -- single `1`; `simpa` then closes the branch with the corresponding
  -- `ordAt ... = 1` hypothesis.  Reverse-oriented inequalities are supplied
  -- explicitly with `Ne.symm` where the conditional has the opposite order.
  by_cases hEq1 : P = Pt1
  · rw [hEq1]
    have hPt1Ra1' : Pt1 ≠ PtRa1 := fun h => hRa1P1' h.symm
    have hPt1Ra2' : Pt1 ≠ PtRa2 := fun h => hRa2P1' h.symm
    have hPt1R1' : Pt1 ≠ PtR1 := fun h => hR1P1' h.symm
    have hPt1R2' : Pt1 ≠ PtR2 := fun h => hR2P1' h.symm
    simpa [hOrd1, h12', hPt1Ra1', hPt1Ra2', hPt1R1', hPt1R2']
  by_cases hEq2 : P = Pt2
  · rw [hEq2]
    have hPt2Pt1' : Pt2 ≠ Pt1 := h12'.symm
    have hPt2Ra1' : Pt2 ≠ PtRa1 := fun h => hRa1P2' h.symm
    have hPt2Ra2' : Pt2 ≠ PtRa2 := fun h => hRa2P2' h.symm
    have hPt2R1' : Pt2 ≠ PtR1 := fun h => hR1P2' h.symm
    have hPt2R2' : Pt2 ≠ PtR2 := fun h => hR2P2' h.symm
    simpa [hOrd2, hPt2Pt1', hPt2Ra1', hPt2Ra2', hPt2R1', hPt2R2']
  by_cases hEqRa1 : P = PtRa1
  · rw [hEqRa1]
    simpa [hOrdRa1, hRa1P1', hRa1P2', hRane', hRa1R1', hRa1R2']
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hRa2Ra1' : PtRa2 ≠ PtRa1 := hRane'.symm
    simpa [hOrdRa2, hRa2P1', hRa2P2', hRa2Ra1', hRa2R1', hRa2R2']
  by_cases hEqR1 : P = PtR1
  · rw [hEqR1]
    have hR1Ra1' : PtR1 ≠ PtRa1 := hRa1R1'.symm
    have hR1Ra2' : PtR1 ≠ PtRa2 := hRa2R1'.symm
    simpa [hOrdR1, hR1P1', hR1P2', hR1Ra1', hR1Ra2', hRne']
  by_cases hEqR2 : P = PtR2
  · rw [hEqR2]
    have hR2Ra1' : PtR2 ≠ PtRa1 := hRa1R2'.symm
    have hR2Ra2' : PtR2 ≠ PtRa2 := hRa2R2'.symm
    have hR2R1' : PtR2 ≠ PtR1 := hRne'.symm
    simpa [hOrdR2, hR2P1', hR2P2', hR2Ra1', hR2Ra2', hR2R1']
  · have hnmemS : P ∉ ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEq1, hEq2, hEqRa1, hEqRa2, hEqR1, hEqR2⟩
    simp only [if_neg hnmemS, if_neg hEq1, if_neg hEq2, if_neg hEqRa1, if_neg hEqRa2,
      if_neg hEqR1, if_neg hEqR2]
    ring

/-- **`div_aff(g) = A+C+T`, `Ra1 = Ra2` repeated-root case: `ua` is a
perfect square.** The mirror of `divToPair_eq_A_add_C_add_T_of_split`
above for the case flagged as a real gap in
`ROADMAP-principal-witness-assembly.md`'s "Note (read before touching
step 1)": `ua`'s two roots collapse to a single point `Ra` of
multiplicity `2`, so `C`'s contribution to `A+C+T` is `(2:ℤ)•[Ra]`, not
`[Ra1]+[Ra2]` for two distinct points. `u_target` is still assumed split
(`hRne`), matching the roadmap's own scoping note (b) — the doubly-
repeated case (`R1=R2 ∧ Ra1=Ra2` simultaneously) is explicitly deferred
until both single mirrors exist (they now do, but composing them is a
separate, harder follow-up, not attempted here). Built from
`ordAtFrac_eq_two_of_Ra1_eq_Ra2_full`/`ordAt_eq_two_of_Ra1_eq_Ra2`
(`PrincipalWitnessAssembly.lean`, added alongside their `R1=R2` mirrors)
in place of `ordAtFrac_eq_one_of_Ra1_full`/`ordAt_eq_one_of_Ra1`; the
support `Finset` correspondingly drops to five points
(`{Pt1,Pt2,PtRa,PtR1,PtR2}`), and the RHS divisor carries an explicit
`(2:ℤ)•single PtRa` term instead of `single PtRa1 + single PtRa2`. -/
theorem divToPair_eq_A_add_C_add_T_of_split_Ra1_eq_Ra2
    [DecidableEq Hc.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree Hc.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : Hc.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra R1 R2 : F p)
    (huaSq : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) = (X - C Ra) ^ 2)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (h12 : P1.1 ≠ P2.1)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRaP1 : Ra ≠ P1.1) (hRaP2 : Ra ≠ P2.1)
    (hRatarget : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra = 0)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (hR1P1 : R1 ≠ P1.1) (hR1P2 : R1 ≠ P2.1)
    (hR1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R1 = 0)
    (hR2P1 : R2 ≠ P1.1) (hR2P2 : R2 ≠ P2.1)
    (hR2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R2 = 0)
    -- `Ra ≠ R1`, `Ra ≠ R2`: same status as `hRa1R1`/etc. above — not
    -- re-derivable from `hnoroot34` alone at this file's level, supplied
    -- directly.
    (hRaR1 : Ra ≠ R1) (hRaR2 : Ra ≠ R2)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hYP2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hYRa_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra ≠ 0)
    (hYR1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (hYR2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (hU_evalP1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hU_evalP2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hU_evalRa : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra ≠ 0)
    (hU_evalR1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (hU_evalR2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (Pt1 Pt2 PtRa PtR1 PtR2 : Hc.Point)
    (hPt1X : Pt1.X = P1.1) (hPt1Y : Pt1.Y = P1.2) (hPt1Y_ne : Pt1.Y ≠ 0)
    (hPt2X : Pt2.X = P2.1) (hPt2Y : Pt2.Y = P2.2) (hPt2Y_ne : Pt2.Y ≠ 0)
    (hPtRaX : PtRa.X = Ra) (hPtRaY : PtRa.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra)
    (hPtRaY_ne : PtRa.Y ≠ 0)
    (hPtR1X : PtR1.X = R1) (hPtR1Y : PtR1.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R1)
    (hPtR1Y_ne : PtR1.Y ≠ 0)
    (hPtR2X : PtR2.X = R2) (hPtR2Y : PtR2.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R2)
    (hPtR2Y_ne : PtR2.Y ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    divToPair E Y ({Pt1, Pt2, PtRa, PtR1, PtR2} : Finset Hc.Point) =
      single Pt1 + single Pt2 + (2 : ℤ) • single PtRa + single PtR1 + single PtR2 := by
  -- The point-composition facts: `ordAt = 1` at `P1,P2,R1,R2`, `ordAt = 2`
  -- at `Ra` (the repeated `ua`-root).
  have hOrd1 : ordAt Pt1 E Y = 1 :=
    ordAt_eq_one_of_P1 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Pt1 hPt1X hPt1Y hPt1Y_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYP1_ne hU_evalP1
      E Y A hE_def hY_def hA_def
  have hOrd2 : ordAt Pt2 E Y = 1 :=
    ordAt_eq_one_of_P2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Pt2 hPt2X hPt2Y hPt2Y_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYP2_ne hU_evalP2
      E Y A hE_def hY_def hA_def
  have hOrdRa : ordAt PtRa E Y = 2 :=
    ordAt_eq_two_of_Ra1_eq_Ra2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Ra huaSq PtRa hPtRaX hPtRaY hPtRaY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRaP1 hRaP2 hRatarget
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYRa_ne hU_evalRa
      E Y A hE_def hY_def hA_def
  have hOrdR1 : ordAt PtR1 E Y = 1 :=
    ordAt_eq_one_of_R1 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 R1 R2 htargetRoot1 htargetRoot2 hRne PtR1 hPtR1X hPtR1Y hPtR1Y_ne
      h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target hR1P1 hR1P2 hR1ua
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYR1_ne hU_evalR1
      E Y A hE_def hY_def hA_def
  have hOrdR2 : ordAt PtR2 E Y = 1 :=
    ordAt_eq_one_of_R2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 R1 R2 htargetRoot1 htargetRoot2 hRne PtR2 hPtR2X hPtR2Y hPtR2Y_ne
      h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target hR2P1 hR2P2 hR2ua
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYR2_ne hU_evalR2
      E Y A hE_def hY_def hA_def
  -- Pairwise distinctness of the five named points, as `Hc.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : Hc.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have h12' : Pt1 ≠ Pt2 := hne_of_X (hPt1X ▸ hPt2X ▸ h12)
  have hRaP1' : PtRa ≠ Pt1 := hne_of_X (hPtRaX ▸ hPt1X ▸ hRaP1)
  have hRaP2' : PtRa ≠ Pt2 := hne_of_X (hPtRaX ▸ hPt2X ▸ hRaP2)
  have hR1P1' : PtR1 ≠ Pt1 := hne_of_X (hPtR1X ▸ hPt1X ▸ hR1P1)
  have hR1P2' : PtR1 ≠ Pt2 := hne_of_X (hPtR1X ▸ hPt2X ▸ hR1P2)
  have hR2P1' : PtR2 ≠ Pt1 := hne_of_X (hPtR2X ▸ hPt1X ▸ hR2P1)
  have hR2P2' : PtR2 ≠ Pt2 := hne_of_X (hPtR2X ▸ hPt2X ▸ hR2P2)
  have hRne' : PtR1 ≠ PtR2 := hne_of_X (hPtR1X ▸ hPtR2X ▸ hRne)
  have hRaR1' : PtRa ≠ PtR1 := hne_of_X (hPtRaX ▸ hPtR1X ▸ hRaR1)
  have hRaR2' : PtRa ≠ PtR2 := hne_of_X (hPtRaX ▸ hPtR2X ▸ hRaR2)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEq1 : P = Pt1
  · rw [hEq1]
    have hPt1Ra' : Pt1 ≠ PtRa := fun h => hRaP1' h.symm
    have hPt1R1' : Pt1 ≠ PtR1 := fun h => hR1P1' h.symm
    have hPt1R2' : Pt1 ≠ PtR2 := fun h => hR2P1' h.symm
    simpa [hOrd1, h12', hPt1Ra', hPt1R1', hPt1R2']
  by_cases hEq2 : P = Pt2
  · rw [hEq2]
    have hPt2Pt1' : Pt2 ≠ Pt1 := h12'.symm
    have hPt2Ra' : Pt2 ≠ PtRa := fun h => hRaP2' h.symm
    have hPt2R1' : Pt2 ≠ PtR1 := fun h => hR1P2' h.symm
    have hPt2R2' : Pt2 ≠ PtR2 := fun h => hR2P2' h.symm
    simpa [hOrd2, hPt2Pt1', hPt2Ra', hPt2R1', hPt2R2']
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    simpa [hOrdRa, hRaP1', hRaP2', hRaR1', hRaR2']
  by_cases hEqR1 : P = PtR1
  · rw [hEqR1]
    have hR1Ra' : PtR1 ≠ PtRa := hRaR1'.symm
    simpa [hOrdR1, hR1P1', hR1P2', hR1Ra', hRne']
  by_cases hEqR2 : P = PtR2
  · rw [hEqR2]
    have hR2Ra' : PtR2 ≠ PtRa := hRaR2'.symm
    have hR2R1' : PtR2 ≠ PtR1 := hRne'.symm
    simpa [hOrdR2, hR2P1', hR2P2', hR2Ra', hR2R1']
  · have hnmemS : P ∉ ({Pt1, Pt2, PtRa, PtR1, PtR2} : Finset Hc.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEq1, hEq2, hEqRa, hEqR1, hEqR2⟩
    simp only [if_neg hnmemS, if_neg hEq1, if_neg hEq2, if_neg hEqRa, if_neg hEqR1,
      if_neg hEqR2]
    ring

/-- **`div_aff(g) = A+C+T`, doubly-repeated case: BOTH `ua` and `u_target`
are perfect squares (`Ra1 = Ra2 ∧ R1 = R2` simultaneously).** The
combination the roadmap explicitly deferred until both single mirrors
existed (`divToPair_eq_A_add_C_add_T_of_split_Ra1_eq_Ra2` above and
`ordAt_eq_two_of_R1_eq_R2`, `PrincipalWitnessAssembly.lean`'s
`PointCompositionR1` section) — they now do, so this is the direct
combination, not new machinery. `C`'s contribution collapses to
`(2:ℤ)•[Ra]` (as in the `Ra1=Ra2`-only case above) AND `T`'s contribution
collapses to `(2:ℤ)•[R]` (the `R1=R2` mirror), so only FOUR named points
remain (`Pt1,Pt2,PtRa,PtR`), each of the latter two carrying coefficient
`2`. Same `eq_of_coeffAt_eq`/`coeffAt_divToPair`/`by_cases`-per-point
proof shape as both single-repeated-root theorems, with one fewer branch
again (`PtR1`/`PtR2` merged into one `PtR` branch, mirroring how the
`Ra1=Ra2`-only theorem already merged `PtRa1`/`PtRa2`). -/
theorem divToPair_eq_A_add_C_add_T_of_split_Ra1_eq_Ra2_and_R1_eq_R2
    [DecidableEq Hc.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree Hc.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : Hc.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra R : F p)
    (huaSq : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) = (X - C Ra) ^ 2)
    (htargetSq : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) = (X - C R) ^ 2)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (h12 : P1.1 ≠ P2.1)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRaP1 : Ra ≠ P1.1) (hRaP2 : Ra ≠ P2.1)
    (hRatarget : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra = 0)
    (hRP1 : R ≠ P1.1) (hRP2 : R ≠ P2.1)
    (hRua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R = 0)
    -- `Ra ≠ R`: same status as `hRaR1`/`hRaR2` above — not re-derivable
    -- from `hnoroot34` alone at this file's level, supplied directly.
    (hRaR : Ra ≠ R)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hYP2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hYRa_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra ≠ 0)
    (hYR_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R ≠ 0)
    (hU_evalP1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hU_evalP2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hU_evalRa : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra ≠ 0)
    (hU_evalR : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R ≠ 0)
    (Pt1 Pt2 PtRa PtR : Hc.Point)
    (hPt1X : Pt1.X = P1.1) (hPt1Y : Pt1.Y = P1.2) (hPt1Y_ne : Pt1.Y ≠ 0)
    (hPt2X : Pt2.X = P2.1) (hPt2Y : Pt2.Y = P2.2) (hPt2Y_ne : Pt2.Y ≠ 0)
    (hPtRaX : PtRa.X = Ra) (hPtRaY : PtRa.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra)
    (hPtRaY_ne : PtRa.Y ≠ 0)
    (hPtRX : PtR.X = R) (hPtRY : PtR.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R)
    (hPtRY_ne : PtR.Y ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    divToPair E Y ({Pt1, Pt2, PtRa, PtR} : Finset Hc.Point) =
      single Pt1 + single Pt2 + (2 : ℤ) • single PtRa + (2 : ℤ) • single PtR := by
  -- `ordAt = 1` at `P1,P2`; `ordAt = 2` at both `Ra` (`ua`'s repeated
  -- root) and `R` (`u_target`'s repeated root).
  have hOrd1 : ordAt Pt1 E Y = 1 :=
    ordAt_eq_one_of_P1 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Pt1 hPt1X hPt1Y hPt1Y_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYP1_ne hU_evalP1
      E Y A hE_def hY_def hA_def
  have hOrd2 : ordAt Pt2 E Y = 1 :=
    ordAt_eq_one_of_P2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Pt2 hPt2X hPt2Y hPt2Y_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYP2_ne hU_evalP2
      E Y A hE_def hY_def hA_def
  have hOrdRa : ordAt PtRa E Y = 2 :=
    ordAt_eq_two_of_Ra1_eq_Ra2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 Ra huaSq PtRa hPtRaX hPtRaY hPtRaY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRaP1 hRaP2 hRatarget
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYRa_ne hU_evalRa
      E Y A hE_def hY_def hA_def
  have hOrdR : ordAt PtR E Y = 2 :=
    ordAt_eq_two_of_R1_eq_R2 p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 hf
      P1 P2 R htargetSq PtR hPtRX hPtRY hPtRY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRP1 hRP2 hRua
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne hYR_ne hU_evalR
      E Y A hE_def hY_def hA_def
  -- Pairwise distinctness of the four named points, as `Hc.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : Hc.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have h12' : Pt1 ≠ Pt2 := hne_of_X (hPt1X ▸ hPt2X ▸ h12)
  have hRaP1' : PtRa ≠ Pt1 := hne_of_X (hPtRaX ▸ hPt1X ▸ hRaP1)
  have hRaP2' : PtRa ≠ Pt2 := hne_of_X (hPtRaX ▸ hPt2X ▸ hRaP2)
  have hRP1' : PtR ≠ Pt1 := hne_of_X (hPtRX ▸ hPt1X ▸ hRP1)
  have hRP2' : PtR ≠ Pt2 := hne_of_X (hPtRX ▸ hPt2X ▸ hRP2)
  have hRaR' : PtRa ≠ PtR := hne_of_X (hPtRaX ▸ hPtRX ▸ hRaR)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, map_zsmul, coeffAt_single, smul_eq_mul]
  by_cases hEq1 : P = Pt1
  · rw [hEq1]
    have hPt1Ra' : Pt1 ≠ PtRa := fun h => hRaP1' h.symm
    have hPt1R' : Pt1 ≠ PtR := fun h => hRP1' h.symm
    simpa [hOrd1, h12', hPt1Ra', hPt1R']
  by_cases hEq2 : P = Pt2
  · rw [hEq2]
    have hPt2Pt1' : Pt2 ≠ Pt1 := h12'.symm
    have hPt2Ra' : Pt2 ≠ PtRa := fun h => hRaP2' h.symm
    have hPt2R' : Pt2 ≠ PtR := fun h => hRP2' h.symm
    simpa [hOrd2, hPt2Pt1', hPt2Ra', hPt2R']
  by_cases hEqRa : P = PtRa
  · rw [hEqRa]
    simpa [hOrdRa, hRaP1', hRaP2', hRaR']
  by_cases hEqR : P = PtR
  · rw [hEqR]
    have hRRa' : PtR ≠ PtRa := hRaR'.symm
    simpa [hOrdR, hRP1', hRP2', hRRa']
  · have hnmemS : P ∉ ({Pt1, Pt2, PtRa, PtR} : Finset Hc.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEq1, hEq2, hEqRa, hEqR⟩
    simp only [if_neg hnmemS, if_neg hEq1, if_neg hEq2, if_neg hEqRa, if_neg hEqR]
    ring


/-- **The residual-side companion fact, re-exported unchanged.** `div_aff
(u_new) = ρ+I` needs `ordAt P U 0 = 1` at each of `U`'s own (unnamed) two
roots — exactly `ordAt_eq_one_of_uRS4General_root`
(`PrincipalWitnessAssembly.lean`, `MumfordPairResidualCase` section),
re-exported here as an `abbrev` purely so callers of THIS file's step-1
composition can find the residual-side fact alongside the old-point-side
fact above, without a second import. No new proof content. -/
abbrev ordAt_u_new_eq_one_of_root := @ordAt_eq_one_of_uRS4General_root

end DecoupledSystem
end Genus2Lean
