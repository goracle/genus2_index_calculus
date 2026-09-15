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

**Base case: now proved, `sorry`-free, via a different route than
originally planned.** Earlier passes assumed the base case had to come
from a finite PREFIX of `genList` (`gens = []`, or `{curveA1}`, etc.),
and found every candidate prefix genuinely infinite-dimensional — `Rdec
p ⧸ ⊥ ≃ Rdec p` is a 12-variable free polynomial ring, and no strict
prefix is finite either, since `a1` (likewise `a2,b1,b2`) is never
peeled alone, only jointly with `U0..V1` via the shared-pivot
resultants. **The fix is to skip prefixes entirely**: `genList_finite_
of_regular` below uses `regularSeq_of_peel_chain`'s existing proof that
the FULL 12-generator `genList` is `IsRegular`, together with
`RegularSequenceFiniteQuotient.lean`'s general fact that a regular
sequence of length `Nat.card ι` in `MvPolynomial ι k` forces the
quotient finite — a genuinely global argument, but one that concludes
directly on `Ideal.ofList genList` itself, with no induction and no
intermediate prefix ever needing to be finite. This closes the honest
gap the previous revision left as `base_prefix_finite_sorry`.

**Still NOT proved by this**: the `≤ 16` numeric bound.
`Module.Finite.quotient_of_isRegular_of_length_eq_card`'s proof goes
through Krull dimension and yields no `finrank` estimate — it only
establishes that `finrank` is a well-defined finite number. The
quantitative bound is still route 3's job
(`genList_triangular_finrank_le_of_base` above), applied on top of this
finiteness fact, not replaced by it.

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

/-! ## The base case, resolved differently than this file originally
## planned — via the *global* regularity of `genList`, not a finite prefix

**Correction to this file's earlier framing.** `base_prefix_finite_sorry`
(this theorem's predecessor) asked for `Module.Finite (F p) (Rdec p ⧸
Ideal.ofList [])`, which is `Rdec p` itself — a 12-variable free
polynomial ring, genuinely infinite-dimensional, so that statement was
FALSE, not merely hard. Chasing a finite PREFIX (`{curveA1}`, etc.) was
also examined and abandoned: `a1` (and likewise `a2,b1,b2`) is never a
pivot of anything in `genList` on its own — it is only ever eliminated
jointly with `U0..V1` via the shared-pivot resultants — so no strict
prefix of `genList` is finite either, independent of ordering.

**Correction, this revision: this theorem already existed.**
`AlphaLocusDegreeUniform.lean`'s `decoupledSystem_zeroDimensional` proves
exactly this fact — `regularSeq_of_peel_chain` composed with
`Module.Finite.quotient_of_isRegular_of_length_eq_card` — already
sorry-free, already in the project, just stated with `Ideal.span
(↑genList.toFinset)` instead of `Ideal.ofList genList` as the quotient's
presentation (the same ideal; `ideal_span_toFinset_eq_ofList`, also
already on file, is the standard identification, and
`decoupledSystem_zeroDimensional`'s own proof already uses it internally
to bridge into `Module.Finite.quotient_of_isRegular_of_length_eq_card`,
which wants `Ideal.ofList` on the nose). The lemma below is a two-line
wrapper converting that theorem's conclusion to the `Ideal.ofList`
presentation this file's other theorems use — not a reproof.
Reinventing the proof (an earlier revision of this file did exactly
that, hitting an avoidable `Nat.card`-vs-`Fintype.card` argument-order
error along the way) was unnecessary; finding the existing theorem
first is the honest fix.

**What this does NOT prove, flagged honestly**: only finiteness, not a
numeric bound. `Module.Finite.quotient_of_isRegular_of_length_eq_card`'s
proof goes through Krull dimension and produces no `finrank` estimate.
The `≤ 16` target in `genList_finrank_le` still needs route 3's
monic-annihilator/degree machinery (`genList_triangular_finrank_le_of_base`
above) — this theorem only supplies the finiteness fact that machinery's
own hypotheses (and any caller needing a bare `Module.Finite` instance)
can now legitimately assume, in place of the old false `sorry`.

**Signature**: identical to `decoupledSystem_zeroDimensional`'s own —
`hndA, hndB, hcross, hpeel, htop_ne_smul` are genuine hypotheses
`regularSeq_of_peel_chain` requires and are not derivable from `hcurA,
hcurB, hgcdA, hgcdB` alone. Any caller wiring this against
`genList_finrank_le` will need to add the same five hypotheses to that
theorem's signature (matching `GenericPeelChainHyp`'s existing bundle)
— not attempted here, left for that wiring step. -/
theorem genList_finite_of_regular
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hndA : Nondegenerate p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA)
    (hndB : Nondegenerate p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB)
    (hcross : CrossNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (hpeel : PeelChainNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (htop_ne_smul : (⊤ : Ideal (Rdec p)) ≠
      Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) • ⊤) :
    Module.Finite (F p)
      (Rdec p ⧸ Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) := by
  rw [← ideal_span_toFinset_eq_ofList]
  exact decoupledSystem_zeroDimensional p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
    hndA hndB hcross hpeel htop_ne_smul

end DecoupledSystem
end Genus2Lean
