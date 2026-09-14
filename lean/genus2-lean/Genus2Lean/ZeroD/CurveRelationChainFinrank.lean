import Mathlib
import Genus2Lean.ZeroD.PeelChainStageFinite
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# The four-stage curve-relation chain, appended to an arbitrary prefix

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Update, later pass" section
(the shared-pivot correction) proposes eliminating `U0,U1,V0,V1` first via
their resultants, leaving `curveA1,curveA2,curveB1,curveB2` as a genuine
4-step one-variable-at-a-time triangular peel over whatever prefix that
elimination lands on. This file supplies exactly that 4-step chain, as a
single fold — the piece `IdxCurveStage0Wiring.lean` attempted and found
did NOT fit the OLD `Fin`-indexed one-slot-per-call architecture
(`FinSuccPeelChainFold.lean`'s `hstep`, which cannot accept a relation in
two brand-new variables at once). No such restriction applies here: this
file works directly over the literal `Ideal.ofList` prefix presentation
(`PeelChainStageFinite.lean`'s `finrank_le_and_finite_curveRelation_ofList_cons`,
file 46), which never needed `x` (a curve relation's sample-point variable,
e.g. `a1`) to be pre-peeled by any earlier stage — `curveFImage`/
`curveRelationGen` evaluate `X x` symbolically in whatever ring the prefix
quotient already is, treating it as a free (possibly non-constant) element
when `x` isn't yet fixed by any prior generator. So `curveA1`'s "two new
variables at once" shape, which broke the `Fin`-arity approach, is simply
not an obstruction for the literal-quotient approach at all — it never
was; the difficulty was specific to the superseded `finSuccEquiv`-based
architecture, not to the underlying mathematics. See
`ROADMAP-monic-annihilator-degree-uniform.md`'s "What's actually true"
correction for the fuller discussion.

**Scope**: fully generic over the starting prefix `gens : List (Rdec p)`
— NOT yet specialized to `gens = FuList ++ FvList` (the shape it will
actually be called at, once the resultant-elimination stage,
`SharedPivotStageWiring.lean`, is itself instantiated against `theData`'s
real values) or to discharging the four `hgu` non-unit hypotheses against
`theData`'s literal formulas. That final substitution is later Assembly
work, matching this project's established split (generic stage-wiring
first, `theData`-specific wiring last) that every other file in this
sub-effort already follows.

**Multiplier**: each curve-relation stage costs a factor of `2`
(`finrank_le_and_finite_curveRelation_ofList_cons`'s own bound), so four
stages cost `2^4 = 16` — matching `genList_finrank_le`'s target bound of
`16` exactly, IF the curve-relation chain is the only source of
multiplicative growth and the resultant-elimination stage before it
contributes a factor of `1` (i.e. is a genuine degree-preserving
elimination, not merely a bound). That final accounting is Assembly's
job, not this file's — flagged here only so the "why 16" question has a
one-line pointer instead of needing to be re-derived.

**Why `hgu1`–`hgu4` (the four non-unit hypotheses) are explicit, not
free**: identical reasoning to every other stage-wiring file in this
sub-effort — `finrank_le_and_finite_curveRelation_ofList_cons` needs
`¬ IsUnit (mk gens g)` for its own generator `g` at its own accumulated
prefix, and this is genuinely not derivable from nothing for an arbitrary
prefix (per `PeelChainStageFinite.lean`'s own docstring, it depends on
which prefix `g`'s image lands in, not just `g`'s shape in `Rdec p`
alone). Left as explicit hypotheses here, to be discharged against
`theData`'s real formulas at final Assembly, same split this project's
other stage-wiring files already follow. -/

namespace Genus2Lean
namespace DecoupledSystem

open Idx

variable (p : ℕ) [Fact (Nat.Prime p)]

/-! ## Bridge lemmas: `curveA1`/etc. as `curveRelationGen` applications

Proved standalone, with NO ambient typeclass context (no `StrongRankCondition`/
`Module.Finite`/`Nontrivial` in scope), matching the fix
`LinearElimDegreeBound.lean`'s own docstring already documents for the same
underlying trap: letting the elaborator `whnf`-unify an unfolded definition
against a goal that also carries a heavy instance stack can blow the
heartbeat budget even after raising `maxHeartbeats`, whereas the bare
equality alone (no instances in its statement) elaborates cheaply and can
then be `rw`'d in wherever needed. `curveA1`/`curveA2`/`curveB1`/`curveB2`
and `curveRelationGen ... w x` at the matching `w`/`x` unfold to the same
term (both reduce to `X w ^ 2 - (C c0 + C c1 * X x + ... + X x ^ 5)`), so
each of these four is `rfl`, proved in isolation. -/

theorem curveA1_eq_curveRelationGen (c0 c1 c2 c3 c4 : F p) :
    curveA1 p c0 c1 c2 c3 c4 = curveRelationGen p c0 c1 c2 c3 c4 wa1 a1 := rfl

theorem curveA2_eq_curveRelationGen (c0 c1 c2 c3 c4 : F p) :
    curveA2 p c0 c1 c2 c3 c4 = curveRelationGen p c0 c1 c2 c3 c4 wa2 a2 := rfl

theorem curveB1_eq_curveRelationGen (c0 c1 c2 c3 c4 : F p) :
    curveB1 p c0 c1 c2 c3 c4 = curveRelationGen p c0 c1 c2 c3 c4 wb1 b1 := rfl

theorem curveB2_eq_curveRelationGen (c0 c1 c2 c3 c4 : F p) :
    curveB2 p c0 c1 c2 c3 c4 = curveRelationGen p c0 c1 c2 c3 c4 wb2 b2 := rfl

set_option maxHeartbeats 1000000 in
/-- **The four-stage curve-relation chain, `curveRelationGen`-native
statement.** Stated directly in terms of `curveRelationGen ... w x`
rather than `curveA1`/etc., so the proof never needs the elaborator to
`whnf`-unify the two forms against a goal that also carries the
`StrongRankCondition`/`Module.Finite`/`Nontrivial` instance stack (the
exact trap `LinearElimDegreeBound.lean`'s `span_of_isUnit_mul_left`
already worked around the same way — see this file's bridge-lemma
section above). Given `gens` already `Module.Finite`/`Nontrivial`, and
the four curve relations' own non-unit hypotheses at their respective
accumulated prefixes, appending all four (in `genList`'s own stated tail
order, i.e. `wa1/a1` then `wa2/a2` then `wb1/b1` then `wb2/b2`) bounds
`finrank` by `16 * finrank gens` and exports `Module.Finite`/
`Nontrivial` on the fully-extended quotient.

**Every prefix below is written LEFT-NESTED, `gens ++ [g1] ++ [g2] ++
...` rather than `gens ++ [g1, g2, ...]`**: `finrank_le_and_finite_
curveRelation_ofList_cons`'s own conclusion is stated as `Ideal.ofList
(pre ++ [g])` for whatever `pre` it was called with, so calling it with
an already-left-nested `pre` produces an output whose prefix is
SYNTACTICALLY (not just propositionally) identical to the next stage's
expected input — no `List.append_assoc`/`simp` reassociation needed
anywhere in this proof, avoiding a `simp`-normal-form mismatch entirely
rather than trying to predict it.

**`[StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]` stays a plain
instance argument, not threaded through the chain**: every intermediate
ring in this fold is a further quotient of `Rdec p` by a growing ideal,
and `StrongRankCondition` is free for any nontrivial commutative ring
(`commRing_strongRankCondition`, `PeelChainAssemblyFinrank.lean`'s own
already-confirmed fact) — so this file supplies it once per stage, right
after that stage's own `Nontrivial` instance becomes available (which
`commRing_strongRankCondition` itself needs as a hypothesis), rather
than trying to derive it once up front. -/
theorem finrank_le_and_finite_curveRelationGenChain
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p)
    (hfin : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens))
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    (hgu1 : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList gens)
      (curveRelationGen p c0 c1 c2 c3 c4 wa1 a1)))
    (hgu2 : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1]))
      (curveRelationGen p c0 c1 c2 c3 c4 wa2 a2)))
    (hgu3 : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2]))
      (curveRelationGen p c0 c1 c2 c3 c4 wb1 b1)))
    (hgu4 : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1]))
      (curveRelationGen p c0 c1 c2 c3 c4 wb2 b2))) :
    Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
      [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wb2 b2])) ∧
    Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
      [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wb2 b2])) ∧
    Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
      [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wb2 b2])) ≤
      16 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens) := by
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList gens) :=
    commRing_strongRankCondition _
  -- Stage 1: append `curveRelationGen ... wa1 a1`.
  obtain ⟨hbound1, hfin1, hnontriv1⟩ :=
    finrank_le_and_finite_curveRelation_ofList_cons p gens c0 c1 c2 c3 c4 wa1 a1 hfin hgu1
  haveI : Nontrivial
      (Rdec p ⧸ Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1])) := hnontriv1
  haveI : StrongRankCondition
      (Rdec p ⧸ Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1])) :=
    commRing_strongRankCondition _
  -- Stage 2: append `curveRelationGen ... wa2 a2`. The callee's own
  -- output prefix is `(gens ++ [g1]) ++ [g2]`, syntactically identical
  -- (left-associated `++` needs no parens) to what stage 3 below expects.
  obtain ⟨hbound2, hfin2, hnontriv2⟩ :=
    finrank_le_and_finite_curveRelation_ofList_cons p
      (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1]) c0 c1 c2 c3 c4 wa2 a2 hfin1 hgu2
  haveI : Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2])) := hnontriv2
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList (gens ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2])) :=
    commRing_strongRankCondition _
  -- Stage 3: append `curveRelationGen ... wb1 b1`.
  obtain ⟨hbound3, hfin3, hnontriv3⟩ :=
    finrank_le_and_finite_curveRelation_ofList_cons p
      (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2])
      c0 c1 c2 c3 c4 wb1 b1 hfin2 hgu3
  haveI : Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
      [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1])) := hnontriv3
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList (gens ++
      [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
      [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1])) :=
    commRing_strongRankCondition _
  -- Stage 4: append `curveRelationGen ... wb2 b2`.
  obtain ⟨hbound4, hfin4, hnontriv4⟩ :=
    finrank_le_and_finite_curveRelation_ofList_cons p
      (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1])
      c0 c1 c2 c3 c4 wb2 b2 hfin3 hgu4
  refine ⟨hfin4, hnontriv4, ?_⟩
  calc Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1] ++ [curveRelationGen p c0 c1 c2 c3 c4 wb2 b2]))
      ≤ 2 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
          [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
          [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++
          [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1])) :=
        hbound4
    _ ≤ 2 * (2 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
          [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
          [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2]))) := by
        gcongr
    _ ≤ 2 * (2 * (2 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
          [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1])))) := by
        gcongr
    _ ≤ 2 * (2 * (2 * (2 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens)))) := by
        gcongr
    _ = 16 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens) := by ring

/-- **The same result, restated in `curveA1`/`curveA2`/`curveB1`/
`curveB2` form** — the shape `genList` and every other Assembly-facing
file in this project actually names. A thin `rw` corollary, kept
separate from the main proof above so the `curveA1 = curveRelationGen
... wa1 a1`-style unification (cheap on its own, per this file's bridge
lemmas) never has to happen INSIDE the instance-heavy main proof, only
once here at the end, matching `LinearElimDegreeBound.lean`'s own
established split for the same reason. -/
theorem finrank_le_and_finite_curveRelationChain
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p)
    (hfin : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens))
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    (hgu1 : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList gens)
      (curveA1 p c0 c1 c2 c3 c4)))
    (hgu2 : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++ [curveA1 p c0 c1 c2 c3 c4]))
      (curveA2 p c0 c1 c2 c3 c4)))
    (hgu3 : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4]))
      (curveB1 p c0 c1 c2 c3 c4)))
    (hgu4 : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4]))
      (curveB2 p c0 c1 c2 c3 c4))) :
    Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ∧
    Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ∧
    Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4])) ≤
      16 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens) := by
  rw [curveA1_eq_curveRelationGen] at hgu1 hgu2 hgu3 hgu4 ⊢
  rw [curveA2_eq_curveRelationGen] at hgu2 hgu3 hgu4 ⊢
  rw [curveB1_eq_curveRelationGen] at hgu3 hgu4 ⊢
  rw [curveB2_eq_curveRelationGen] at hgu4 ⊢
  -- After the rewrites above, `hgu3`/`hgu4`/goal are stated in terms of
  -- `curveRelationGen` (not `curveA1` etc.), but still as flat list literals
  -- (`gens ++ [g1, g2, ...]`), while the chain lemma below expects chained
  -- singleton appends (`gens ++ [g1] ++ [g2] ++ ...`). Same list, different
  -- `List` terms, so `exact` won't unify them directly — bridge with an
  -- explicit list equality (proved by plain `simp` on `cons_append`/
  -- `nil_append`/`append_assoc`) and `rw` each into exactly the
  -- hypothesis/goal whose literal it matches.
  have e3 : gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1,
        curveRelationGen p c0 c1 c2 c3 c4 wa2 a2]
      = gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] := by
    simp
  have e4 : gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1,
        curveRelationGen p c0 c1 c2 c3 c4 wa2 a2, curveRelationGen p c0 c1 c2 c3 c4 wb1 b1]
      = gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++ [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1] := by
    simp
  have e5 : gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1,
        curveRelationGen p c0 c1 c2 c3 c4 wa2 a2, curveRelationGen p c0 c1 c2 c3 c4 wb1 b1,
        curveRelationGen p c0 c1 c2 c3 c4 wb2 b2]
      = gens ++ [curveRelationGen p c0 c1 c2 c3 c4 wa1 a1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wa2 a2] ++ [curveRelationGen p c0 c1 c2 c3 c4 wb1 b1] ++
        [curveRelationGen p c0 c1 c2 c3 c4 wb2 b2] := by
    simp
  rw [e3] at hgu3
  rw [e4] at hgu4
  rw [e5]
  exact finrank_le_and_finite_curveRelationGenChain p gens c0 c1 c2 c3 c4 hfin hgu1 hgu2 hgu3 hgu4

end DecoupledSystem
end Genus2Lean
