import Mathlib
import Genus2Lean.ZeroD.PeelChainAssemblyFinrank
import Genus2Lean.ZeroD.PeelChainStageFinite

/-!
# Assembly, part 4: specializing the n-stage fold to `genList`'s literal
# 12 generators

The true remainder `ROADMAP-monic-annihilator-degree-uniform.md`'s
Progress section flags as "still the next concrete step, and now
actually startable": `PeelChainAssemblyFinrank.lean`'s
`finrank_le_and_finite_of_append` is a fully generic n-stage fold, not
yet applied to `genList`'s actual 12 generators or `theData`'s actual
field values. This file does that specialization.

**What this file is honest about, per the roadmap's own resolved "Open
Questions" diagnosis**: `hstep`'s per-generator side hypotheses
(`hgu : ¬IsUnit (mk g)` for the curve-relation shape,
`hd_unit : IsUnit (mk d)` **and** `hgu : ¬IsUnit (mk g)` for the
linear-elimination shape) are genuinely NEW per-stage hypotheses, not
already supplied by `Nondegenerate`/`CrossNondegenerate`
(`DecoupledSystemRegular.lean`) -- those give `≠ 0` facts about
`uRS`/`vRS` coefficients in the BASE field `F p`, or `IsSMulRegular`
facts about a COMBINED expression in an EXTENDED quotient, neither of
which is the isolated `IsUnit (mk_prefix d)` fact
`finrank_le_and_finite_linearElim_ofList_cons` actually needs on the
PREVIOUS-stage ring. This file therefore bundles all twelve needed
side-conditions into one new hypothesis structure
(`PeelChainFinrankHyp`), exactly the way `GenericPeelChainHyp` already
bundles its own genuinely-open content as named fields rather than
smuggling them in as unstated assumptions -- **it does not claim these
twelve conditions are proved, derivable, or even likely to hold for a
generic curve**; that investigation (matching them against `theData`'s
actual symbolic formulas, and hence against `Bad`'s eventual size, per
the roadmap's still-open item 6) is explicitly deferred, same as the
roadmap's own file plan scopes it.

**What this file DOES honestly discharge, with no new hypothesis**: the
curve-relation stages' `hgu` -- `curveRelationGen p c0 c1 c2 c3 c4 w x =
X w ^ 2 - (...)` has `MvPolynomial.totalDegree` at least 2 in `Rdec p`
itself (from the bare `X w ^ 2` term), hence its image in ANY quotient
ring is not "for free" a non-unit purely from this fact alone (quotienting
can manufacture units) -- so even this direction still needs a
hypothesis at the level of the actual prefix quotient, not just `Rdec p`.
Checked directly rather than assumed: NO existing lemma in this codebase
lifts "non-unit in `Rdec p`" to "non-unit in `Rdec p ⧸ Ideal.ofList
gens`" for an arbitrary prefix (quotienting is exactly the operation
that can turn a non-unit into a unit), so `hgu` for every stage,
curve-relation stages included, is included as an explicit field below,
not derived.

**Multiplier list, matching `genList`'s literal order** (`FuList ++
FvList ++ [curveA1, curveA2, curveB1, curveB2]`, `DecoupledSystemRegular
.lean` §5): eight `1`s (the linear-elimination stages) then four `2`s
(the curve-relation stages) -- `[1,1,1,1,1,1,1,1,2,2,2,2]`, exactly the
sequence `ROADMAP-monic-annihilator-degree-uniform.md`'s Progress
section names as still owed. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial
open TheDataDerivation

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

/-- **The twelve genuinely-open per-stage side conditions, bundled.**

**Deliberately generic over `d : DecoupledGenerators p` and
`Fu Fv : List (Rdec p)`, NOT parametrized by `(c0,...,c4,sa,sb,...)` and
tied to `theData`/`FuList`/`FvList` internally.** An earlier draft
stated this structure exactly like `GenericPeelChainHyp` — over the full
`(c0,...,c4,sa,sb,hcurA,hcurB,hgcdA,hgcdB)` parameter list, with `d`/
`Fu`/`Fv` as extra FIELDS carrying `= theData ...`/`= FuList ...`/
`= FvList ...` equalities — but Claire's REPL hit a `whnf` heartbeat
timeout at exactly that equality field's own type
(`d = theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB`), even
though the earlier fix (isolating `theData`'s application to appear
just once, in that one field, rather than twelve times) had already
been applied. So the problem isn't repetition of the heavy term at all
— it's that STATING even a single equality against `theData`'s full
application forces Lean to check it against `DecoupledGenerators p`,
which needs enough of `theData`'s own definition (itself built from
`coeffsToNumDen`/`towerToRdec`'s three-level tower) unfolded to matter.

**The fix**: make `d`/`Fu`/`Fv` genuinely free STRUCTURE PARAMETERS
(no `(c0,...,c4,sa,sb,...)` in this structure's signature at all, and
no equality field connecting them back), the same way
`finrank_le_and_finite_linearElim_ofList_cons`
(`PeelChainStageFinite.lean`) is already fully generic over `c d : Rdec
p` rather than tied to `theData` internally. This file's job is to state
what side conditions the twelve stages need in the abstract; connecting
`d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB`,
`Fu := FuList ...`, `Fv := FvList ...` at the real values becomes the
CALLER's job when they instantiate this structure (an ordinary function
application, not a fact this structure needs to state or carry
internally) — not yet REPL-confirmed this pass, this version was
written in direct response to the previous version's reported error,
not yet rebuilt. -/
structure PeelChainFinrankHyp (d : DecoupledGenerators p) (Fu Fv : List (Rdec p))
    (c0 c1 c2 c3 c4 : F p) : Prop where
  /-- `d.u1_den 0`'s image is a unit at the empty prefix (stage 0, `Fu0`). -/
  hd_unit0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList ([] : List (Rdec p)))
    (d.u1_den 0))
  /-- `d.u2_den 0`'s image is a unit at the prefix `[Fu0]` (stage 1). -/
  hd_unit1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (Fu.take 1)) (d.u2_den 0))
  /-- `d.u1_den 1`'s image is a unit at the prefix `[Fu0,Fu1]` (stage 2). -/
  hd_unit2 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (Fu.take 2)) (d.u1_den 1))
  /-- `d.u2_den 1`'s image is a unit at the prefix `[Fu0,Fu1,Fu2]` (stage 3). -/
  hd_unit3 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (Fu.take 3)) (d.u2_den 1))
  /-- `d.v1_den 0`'s image is a unit at the prefix `FuList` (stage 4). -/
  hd_unit4 : IsUnit (Ideal.Quotient.mk (Ideal.ofList Fu) (d.v1_den 0))
  /-- `d.v2_den 0`'s image is a unit at the prefix `FuList ++ [Fv0]` (stage 5). -/
  hd_unit5 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (Fu ++ Fv.take 1)) (d.v2_den 0))
  /-- `d.v1_den 1`'s image is a unit at the prefix `FuList ++ [Fv0,Fv1]` (stage 6). -/
  hd_unit6 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (Fu ++ Fv.take 2)) (d.v1_den 1))
  /-- `d.v2_den 1`'s image is a unit at the prefix `FuList ++ [Fv0,Fv1,Fv2]`
  (stage 7). -/
  hd_unit7 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (Fu ++ Fv.take 3)) (d.v2_den 1))
  /-- Each of the 8 matching-generator stages' own image is a non-unit at
  ITS OWN accumulated prefix (needed for `Nontrivial` of the one-step
  extension, `nontrivial_of_span_ne_top`). Bundled as one list-indexed
  field rather than 8 separately-named ones, since (unlike `hd_unit*`
  above) all 8 share the exact same "generator is degree-1 in a not-yet-
  eliminated free variable" shape and reasoning -- see this file's own
  docstring for why this still needs to be assumed, not derived, despite
  that shared reasoning suggesting it "should" always hold.

  Indexed via `List.getD` with junk default `0` rather than a dependent
  `GetElem` proof obligation — sidesteps needing `Fu.length`/`Fv.length`
  facts in scope inside this field's own type (an earlier draft used
  `[i.val]'(by ...)`, which would need a length fact available AS A
  HYPOTHESIS inside a later structure field's own type; whether an
  earlier `Prop`-valued structure field is automatically usable that way
  by plain tactics inside a later field's own proof obligation is not
  confirmed Lean 4 structure-telescope behavior, so this version avoids
  relying on it entirely). For `i.val` actually in range (`< 8`,
  guaranteed by `Fin 8`, combined with `Fu`/`Fv` each truly having
  length 4 once instantiated against `FuList`/`FvList`'s real 4-entry
  bodies at the point of USE, not inside this definition), `getD` and
  the real entry agree -- callers needing that agreement prove it then,
  from whatever equality connects their `Fu`/`Fv` to `FuList`/`FvList`. -/
  hgu_lin : ∀ i : Fin 8,
    ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList ((Fu ++ Fv).take i.val))
      ((Fu ++ Fv).getD i.val 0))
  /-- Each of the 4 curve-relation stages' own image is a non-unit at ITS
  OWN accumulated prefix (`FuList ++ FvList` plus however many curve
  relations already appended) -- same bundling reasoning and same
  `getD`-over-`GetElem` choice as `hgu_lin`. -/
  hgu_curve : ∀ i : Fin 4,
    ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList ((Fu ++ Fv ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]).take (8 + i.val)))
      ((Fu ++ Fv ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]).getD (8 + i.val) 0))

/-- **Placeholder for the true final wiring theorem** (not yet started
this pass): the actual instantiation of
`finrank_le_and_finite_of_append` against `genList`'s literal 12
generators, taking `PeelChainFinrankHyp` above and producing
`Module.Finite (F p) (Rdec p ⧸ Ideal.span (↑(genList ...).toFinset))`
plus the numeric bound `Module.finrank (F p) (...) ≤ 2^4` (the product
`[1,1,1,1,1,1,1,1,2,2,2,2].prod`), in the `Ideal.span ↑l.toFinset` form
`GenericPeelChainHyp.hfinrank_le` actually needs (bridged via
`ideal_span_toFinset_eq_ofList`, `AlphaLocusDegreeUniform.lean`).

**Why this is not attempted yet, honestly**: `hstep`'s uniform interface
(`∀ pre, Finite pre → Nontrivial pre → ∀ g, ...`) takes a SINGLE
generator `g` per call with no positional information -- but the twelve
real stages need twelve DIFFERENT proof recipes (which per-stage lemma
to call, `finrank_le_and_finite_linearElim_ofList_cons` vs
`finrank_le_and_finite_curveRelation_ofList_cons`, and which of
`PeelChainFinrankHyp`'s twelve fields to hand it), so building the
actual `hstep` argument means either (a) calling
`finrank_le_and_finite_of_append` twelve separate times, once per
generator, chaining each call's conclusion into the next call's
`hfin`/`hnontriv` hypotheses by hand (abandoning the generic fold's own
induction in favor of explicit sequential application -- simplest, and
likely the right move given `hstep` cannot naturally case-split on
"which of the 12 calls is this" without reintroducing exactly the
bookkeeping the fold was meant to avoid), or (b) reformulating `hstep`
to take a positional index and case-split internally. Route (a) looks
more promising on a first read (mirrors how `PeelChainAssembly.lean`'s
OWN 12-way `regularSeq_of_peel_chain` case split already works, so it
would match this project's existing style for exactly this kind of
chain) but has not been drafted or checked against
`FuList`/`FvList`/`curveA1`-etc.'s literal terms for whether the
`List.take`/`List.get` bookkeeping above actually unifies against
`genList`'s own associativity of `++` without further lemmas -- do that
check first, before writing twelve sequential `obtain`s by hand.

Left as a named `True` placeholder (not a `sorry`, per this project's
own inventory convention distinguishing genuinely-open work from live
tactic obligations) rather than omitted, so its docstring above is
attached to a real declaration and this file's own presence in a future
sorry/placeholder scan is self-documenting. -/
theorem genList_finrank_assembly_placeholder : True := trivial

end DecoupledSystem
end Genus2Lean
