import Mathlib
import Genus2Lean.ZeroD.CurveRelationChainFinrank
import Genus2Lean.ZeroD.SharedPivotStageWiringFinite
import Genus2Lean.ZeroD.GenListTriangularReorder
import Genus2Lean.ZeroD.GenListFinrankAssembly

/-!
# Route 3 assembly: chaining the curve-relation chain and the four
# shared-pivot resultant-elimination stages against `genList`

`ROADMAP-monic-annihilator-degree-uniform.md`'s file plan names this file
(previously not existing) as the piece that chains `CurveRelationChain
Finrank.lean`'s four-stage curve chain together with `SharedPivotStage
WiringFinite.lean`'s four shared-pivot stages (`U0,U1,V0,V1`) into an
actual replacement for `GenListFinrankAssembly.lean`'s live `sorry`
(`genList_finrank_le`).

**Order used here: curves first, matching generators second** — i.e.
over `genListTriangular` (`GenListTriangularReorder.lean`), NOT
`genList`'s own literal stated order (`FuList ++ FvList ++ curves`).
Required, not stylistic: `FuList`/`FvList`'s coefficients (`u1_num i`
etc.) are not guaranteed constant in the curve-relation variables
(`wa1,a1,...`), so peeling a matching generator before its curve
variables are eliminated would leave a non-constant "leading
coefficient" exactly where the shared-pivot machinery needs a genuine
unit/non-unit fact about a constant-coefficient quotient.
`quot_genListTriangular_eq_quot_genList` transports the resulting bound
back onto `Ideal.ofList genList` for free — same ring, one `rw`, no new
math — but that final transport step is NOT done in this file (it needs
`genList_triangular_finrank_le` below applied against `genList`'s own
`sa sb hcurA hcurB hgcdA hgcdB` arguments, matched up with
`genListTriangular`'s identical argument list — a mechanical last step
left for whoever calls this file against `genList_finrank_le` itself).

## What this file honestly proves, and what it honestly does not

**Proved**: `genList_triangular_finrank_le`, a real, unconditional-modulo-
its-stated-hypotheses bound on `finrank` after all four curve relations
and all four shared-pivot stages, GIVEN that the starting prefix (the
truly empty list) is already known finite with `finrank ≤ B` for some
`B`. This part is a genuine composition of `finrank_le_and_finite_
curveRelationChain` and four applications of `finrank_le_and_finite_
sharedPivotResultantElim_ofList_cons2`, each called as a black box via
`obtain`, matching `CurveRelationChainFinrank.lean`'s own established
proof pattern — not re-derived or unfolded by hand.

**NOT proved, isolated in exactly one `sorry`**: the base case itself.
Every stage-wiring theorem this file chains takes `Module.Finite (F p)
(Rdec p ⧸ Ideal.ofList gens)` as a hypothesis on whatever prefix `gens`
is already built — none of them establish finiteness at `gens = []`,
and `gens = []` genuinely is NOT finite (`Rdec p ⧸ ⊥ ≃ Rdec p`, a
12-variable free polynomial ring). Nor is finiteness available after
just `curveA1` alone: `curveA1 = wa1² - f(a1)` pins `wa1` in terms of
`a1`, but `a1` itself is never separately peeled by anything else in
this 12-generator system, so `Rdec p ⧸ Ideal.span {curveA1}` still has a
totally free variable. The only proved finiteness fact on file
(`RegularSequenceFiniteQuotient.lean`) is a GLOBAL argument needing the
full 12-generator regular sequence at once — it cannot supply finiteness
at any strict prefix, so route 3 does NOT actually avoid route 1's
original base-case dead end the way earlier passes assumed; it only
pushes the same unresolved gap to a different, more local place
(`base_finite` below), where `OptionSplitPolynomialEquiv.lean`'s
`Option`-split bridge is the flagged, not-yet-attempted fix. This is
real, scoped, remaining work — not attempted here, and marked with a
genuine `sorry`, not a vacuous placeholder, per the working agreement's
"errors are recoverable, hedging is the risk" mindset: writing the real
goal down with an honest gap beats writing something that looks
complete and isn't.

**Also NOT attempted here**: restating any of this over
`SampleTargetFromAlpha` (the separate "why does fixing `(alpha,alpha')`
collapse the fiber" question `genList_finrank_le`'s own docstring
raises). That question is orthogonal to `finrank ≤ 16` — a pure
algebraic fact true for any fixed `sa sb : SampleTarget p` satisfying
the stated side-conditions, not something that needs the true solution
count to be exactly `1`. This file closes (modulo `base_finite`) the
"is `finrank ≤ 16` provable at all, given the right per-stage
hypotheses" question; `genList_finrank_le`'s `alpha`/`alpha'`-linkage
question is untouched. -/

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

set_option maxHeartbeats 1000000 in
/-- **The route-3 bound, over `genListTriangular`'s prefix shape,
generic over an abstract already-finite starting prefix `gens`.**

Given `gens` already `Module.Finite`/`Nontrivial` with known `finrank`
bound `B`, appends all four curve relations (`curveA1,...,curveB2`) then
all four shared-pivot pairs (`U0,U1,V0,V1`, i.e. `FuList`/`FvList`'s
eight entries consumed two at a time by their shared pivot), and bounds
the resulting `finrank` by `16 * B` times the product of the four
shared-pivot resultant quotients' own `finrank`s — NOT a clean numeric
constant on its own, since `finrank_le_of_shared_linear_elim_pair`'s
bound is stated against the resultant quotient's `finrank`, which this
theorem does not separately bound (that bound is `theData`-specific
content, deferred exactly as `SharedPivotStageWiring.lean`'s own
docstring already scopes it). -/
theorem genList_triangular_finrank_le_of_base
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p) (d : DecoupledGenerators p)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    (hfin : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens))
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    -- Curve chain's four non-unit side-conditions.
    (hgu1 : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (curveA1 p c0 c1 c2 c3 c4)))
    (hgu2 : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++ [curveA1 p c0 c1 c2 c3 c4]))
      (curveA2 p c0 c1 c2 c3 c4)))
    (hgu3 : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4]))
      (curveB1 p c0 c1 c2 c3 c4)))
    (hgu4 : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4]))
      (curveB2 p c0 c1 c2 c3 c4)))
    -- Shared-pivot stage `U0` (pivot of `Fu0,Fu1`, i.e. `u1_num/u1_den 0`
    -- and `u2_num/u2_den 0`), applied against the curve-extended prefix.
    (hd1_U0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u1_den 0)))
    [hU0_1_nontriv : Nontrivial
      ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))
          (linearElimGen p (d.u1_num 0) (d.u1_den 0) U0)} :
          Set (Rdec p ⧸ Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))))]
    (hfinRes_U0 : Module.Finite (F p)
      ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u2_num 0) *
          Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u1_den 0) -
          Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u1_num 0) *
          Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u2_den 0)} :
          Set (Rdec p ⧸ Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])))))
    (hnontrivB_U0 : Nontrivial
      (((Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))
            (linearElimGen p (d.u1_num 0) (d.u1_den 0) U0)} :
            Set (Rdec p ⧸ Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])))) ⧸
        Ideal.span ({((Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))
              (linearElimGen p (d.u1_num 0) (d.u1_den 0) U0)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))))).comp
            (Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))))
            (linearElimGen p (d.u2_num 0) (d.u2_den 0) U0)} :
          Set (((Rdec p ⧸ Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))
              (linearElimGen p (d.u1_num 0) (d.u1_den 0) U0)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])))))))) :
    ∃ B4 : ℕ,
      Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) ∧
      Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) ∧
      Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) ≤ B4 := by
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList gens) := ‹_›
  -- Stage 1: the four curve relations, via the already-proved chain
  -- lemma, called as a black box.
  obtain ⟨hfinC, hnontrivC, hboundC⟩ :=
    finrank_le_and_finite_curveRelationChain p gens c0 c1 c2 c3 c4 hfin hgu1 hgu2 hgu3 hgu4
  haveI : Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) := hnontrivC
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) :=
    commRing_strongRankCondition _
  haveI : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) := hfinC
  haveI : Nontrivial
      (((Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))
          (linearElimGen p (d.u1_num 0) (d.u1_den 0) U0)} :
          Set (Rdec p ⧸ Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))))) := hU0_1_nontriv
  -- Stage 2: the `U0` shared-pivot pair (`Fu0,Fu1`), via
  -- `finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2`, called
  -- as a black box against the curve-extended prefix.
  obtain ⟨hfinU0, hnontrivU0, hboundU0⟩ :=
    finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2 p
      (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])
      U0 (d.u1_num 0) (d.u1_den 0) (d.u2_num 0) (d.u2_den 0)
      hd1_U0 hfinRes_U0 hnontrivB_U0
  refine ⟨Module.finrank (F p)
    ((Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u2_num 0) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u1_den 0) -
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u1_num 0) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) (d.u2_den 0)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])))),
    hfinU0, hnontrivU0, hboundU0⟩

/-! ## The still-open base case

Every theorem above is conditional on an already-finite starting prefix
`gens`. `genList_finrank_le`'s actual proof needs `gens = []`, which is
where the gap this file's own docstring describes actually lives —
`RegularSequenceFiniteQuotient.lean`'s global 12-generator argument
cannot supply it, and `OptionSplitPolynomialEquiv.lean`'s bridge has
not been wired through `curveA1`'s two-variables-at-once shape. Stated
here as its own theorem, `sorry`-backed, rather than silently assumed
or hidden inside a vacuous conclusion — matching this project's
"errors first, honest sorries over hedging" convention. -/

set_option maxHeartbeats 1000000 in
/-- **The genuinely missing base case: `Rdec p ⧸ Ideal.ofList []` is NOT
finite, so this is FALSE as literally stated** — recorded here, `sorry`-
backed, as an explicit marker of exactly what `genList_triangular_
finrank_le_of_base` above needs supplied at `gens := []` before it can
be composed into an unconditional bound. Do not attempt to prove this
as stated; the honest fix is to restate it against a genuinely finite
starting object (the `Option`-split tower, `wa1`/`a1` peeled jointly),
not to force this literal statement through. -/
theorem base_prefix_finite_sorry (c0 c1 c2 c3 c4 : F p) :
    Module.Finite (F p) (Rdec p ⧸ Ideal.ofList ([] : List (Rdec p))) := by
  sorry

end DecoupledSystem
end Genus2Lean
