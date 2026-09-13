import Mathlib
import Genus2Lean.ZeroD.PeelChainStageFinite

/-!
# Assembly, part 3: chaining all stages' finiteness-exporting bounds

`ROADMAP-monic-annihilator-degree-uniform.md`'s own stated next step,
per its Progress section's final paragraph ("the final Assembly step
... is still the next concrete step, and is now actually startable").
This file supplies the GENERIC n-stage chaining primitive item 5 calls
for: given a list of generators to append one at a time, plus a single
proof recipe for "one more step is valid, at any prefix that already
has `Finite`/`Nontrivial`," chain all of them by induction into one
bound on the full extended quotient.

**Scope of this file**: still the GENERIC step, not yet specialized to
`genList`'s literal 12 generators or `theData`'s actual field values —
that specialization (the true final wiring, discharging each stage's
`hgu`/`hd_unit` against `theData`'s real formulas and supplying the
concrete multiplier sequence `[1,1,1,1,1,1,1,1,2,2,2,2]`) is later
work, matching this project's established split between "generic
chaining primitive" (`QuotOfListChainFinrankStep.lean`'s one-stage
version, and this file's n-stage version) and "wiring to the literal
peel chain" (`CurveRelationStageWiring.lean`/`LinearElimStageWiring.lean`
for one stage each, still needed to cover all twelve).

**Why the per-stage fact (`hstep`) is a single hypothesis quantified
over an arbitrary prefix, not twelve already-applied terms supplied up
front**: each stage's own `Module.Finite`/`Nontrivial` hypotheses
(consumed by `finrank_le_and_finite_curveRelation_ofList_cons` /
`finrank_le_and_finite_linearElim_ofList_cons`) are about THAT stage's
own accumulated prefix, which is only known once the induction reaches
that point — stage `i`'s hypotheses cannot be discharged before stage
`i-1`'s conclusion exists. So the natural interface is a single proof
recipe `hstep`, general enough to be called again at each new prefix
the induction produces, rather than a list of pre-built per-stage
facts (which the caller couldn't have built without already running
the induction). The literal-12-generator wiring file (still to come)
will supply ONE concrete `hstep` per stage-shape (calling
`finrank_le_and_finite_curveRelation_ofList_cons` or
`finrank_le_and_finite_linearElim_ofList_cons` depending on which
generator index it's at), and this lemma's induction runs each one in
turn — `hstep` here is intentionally uniform, matching how
`QuotOfListChainFinrankStep.lean`'s own one-stage lemma stays agnostic
to which of the two per-stage shapes produced its `hstep`.

**Why `StrongRankCondition` never appears as a hypothesis or a field
here, even though the per-stage lemmas `hstep` will internally call
need it**: any commutative ring satisfies `StrongRankCondition` once
it is `Nontrivial` (`commRing_strongRankCondition`, confirmed via
direct web search of the current Mathlib4 source under
`Mathlib.LinearAlgebra.FreeModule.StrongRankCondition` — the
`OrzechProperty` route is unconditional for any `CommRing`, and
`Nontrivial` upgrades that to `StrongRankCondition`; not assumed from
memory). Every ring appearing in this induction (`R ⧸ Ideal.ofList
(some prefix)`) is always a `CommRing`, and this induction already
carries `Nontrivial` as an explicit invariant at every step — so
`StrongRankCondition` resolves by instance search the moment
`Nontrivial` is in local context, with nothing to thread separately.

**Multiplier bookkeeping**: `hstep` supplies each step's own bound
against a caller-chosen multiplier `d g`, a function of the generator
being appended (not a fixed constant), since the eventual 12-stage
application needs `d = 1` for the eight linear-elimination generators
and `d = 2` for the four curve-relation generators. The final bound's
multiplier is the product `(newGens.map d).prod`, composed via
`Module.finrank_mul_finrank` at each step — this exactly matches
`Module.finrank_mul_finrank`'s left-to-right tower law, applied once
per appended generator. -/

namespace Genus2Lean
namespace DecoupledSystem

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- **The n-stage fold.** `gens` is the starting prefix; `newGens` is
the list of generators to append one at a time, in order. `d` assigns
each generator its own multiplier (`1` or `2` in the eventual
12-stage application). `hstep` is the caller-supplied per-stage proof
recipe, called once per generator in `newGens`, always at the prefix
accumulated so far — general enough that ONE recipe covers every
stage, provided the recipe itself case-splits on which generator it
was handed (the eventual wiring file's job, not this lemma's).

Concludes `Module.Finite`/`Nontrivial`/the composed `finrank` bound on
the full `gens ++ newGens` quotient, with total multiplier
`(newGens.map d).prod`. -/
theorem finrank_le_and_finite_of_append
    (gens : List R) (newGens : List R) (d : R → ℕ)
    (hfin : Module.Finite k (R ⧸ Ideal.ofList gens))
    (hnontriv : Nontrivial (R ⧸ Ideal.ofList gens))
    (hstep : ∀ (pre : List R), Module.Finite k (R ⧸ Ideal.ofList pre) →
      Nontrivial (R ⧸ Ideal.ofList pre) → ∀ (g : R),
      Module.Finite k (R ⧸ Ideal.ofList (pre ++ [g])) ∧
        Nontrivial (R ⧸ Ideal.ofList (pre ++ [g])) ∧
        Module.finrank k (R ⧸ Ideal.ofList (pre ++ [g])) ≤
          d g * Module.finrank k (R ⧸ Ideal.ofList pre)) :
    Module.Finite k (R ⧸ Ideal.ofList (gens ++ newGens)) ∧
    Nontrivial (R ⧸ Ideal.ofList (gens ++ newGens)) ∧
    Module.finrank k (R ⧸ Ideal.ofList (gens ++ newGens)) ≤
      (newGens.map d).prod * Module.finrank k (R ⧸ Ideal.ofList gens) := by
  induction newGens generalizing gens with
  | nil =>
    -- `gens ++ [] = gens`; `([].map d).prod = 1`.
    rw [List.append_nil, List.map_nil, List.prod_nil, one_mul]
    exact ⟨hfin, hnontriv, le_refl _⟩
  | cons g rest ih =>
    -- One step: `hstep gens hfin hnontriv g` gives the extension by
    -- `g` alone. Its three components feed the INNER induction
    -- hypothesis `ih`, applied at the new prefix `gens ++ [g]`.
    obtain ⟨hfinStep, hnontrivStep, hboundStep⟩ := hstep gens hfin hnontriv g
    obtain ⟨hfinRest, hnontrivRest, hboundRest⟩ := ih (gens ++ [g]) hfinStep hnontrivStep
    -- `(gens ++ [g]) ++ rest = gens ++ (g :: rest)`, established once and
    -- used to rewrite the GOAL (via `rw`), rather than trying to push
    -- `simp`/`simpa` through the `Module.Finite`/`Nontrivial` typeclass
    -- wrappers and the quotient-ring `R ⧸ _` — that direction is fragile;
    -- rewriting the goal's `Ideal.ofList` argument directly is not.
    have hlist : gens ++ [g] ++ rest = gens ++ (g :: rest) := by
      rw [List.append_assoc, List.singleton_append]
    rw [← hlist]
    exact ⟨hfinRest, hnontrivRest, by
      rw [List.map_cons, List.prod_cons]
      calc Module.finrank k (R ⧸ Ideal.ofList (gens ++ [g] ++ rest))
          ≤ (rest.map d).prod * Module.finrank k (R ⧸ Ideal.ofList (gens ++ [g])) := hboundRest
        _ ≤ (rest.map d).prod * (d g * Module.finrank k (R ⧸ Ideal.ofList gens)) :=
            Nat.mul_le_mul_left _ hboundStep
        _ = d g * (rest.map d).prod * Module.finrank k (R ⧸ Ideal.ofList gens) := by ring⟩

end DecoupledSystem
end Genus2Lean
