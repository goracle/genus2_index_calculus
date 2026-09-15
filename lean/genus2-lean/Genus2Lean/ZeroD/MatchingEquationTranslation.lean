import Mathlib
import Genus2Lean.DivisorClassGroup

/-!
# The matching equation's solution set: translation structure, and what it does
# and doesn't establish about rigidity

Two standalone group-theory facts about the matching equation
`[P1]+[P2]-[P3]-[P4] = (alpha-alpha')•a` in `Jacobian H D`
(`DecoupledSystemRegular.lean`'s module docstring: "The matching condition
`R(alpha;P1,P2) = R(alpha';P3,P4)` is exactly `(P1+P2)-(P3+P4) =
(alpha-alpha')*a`"). Both are pure consequences of `Jacobian H D` being an
abelian group — no curve-specific or Mumford-coordinate content, and no
dependence on `Rdec p`/`genList`/`SampleTarget` at all, matching this
project's convention of splitting reusable algebra out from its
application (see e.g. `FinrankLeOfMonicAnnihilator.lean`'s own docstring
on the same split).

## What is, and is not, proved here

Worked out and checked directly against `ROADMAP-monic-annihilator-degree
-uniform.md`'s final correction and `ROADMAP-alpha-locus.md`'s "Newer
status update" (both in this directory) before writing this file, not
assumed: the geometric claim those two documents make — that the
solution set for a FIXED `(alpha,alpha')` is a single point, i.e. that
distinct solutions coincide outright — is asserted in
`ROADMAP-alpha-locus.md` as a finding from reasoning done outside Lean,
but that file says explicitly the finding is "not yet formalized" and
the mechanism behind it "not yet elucidated." **This file does not
supply that mechanism, and does not prove the solution set has exactly
one element.** What it proves instead:

1. `matching_solutions_translate_by_delta`: any two solutions of the
   matching equation are related by a single, common `Δ ∈ Jacobian H D`
   translating BOTH sides (`[P1]+[P2] = [P1']+[P2']+Δ` and
   `[P3]+[P4] = [P3']+[P4']+Δ` simultaneously, for the SAME `Δ`) — the
   corrected version of the argument (an earlier draft's definition of
   `Δ` did not follow from the two equations; this is the fixed one,
   checked by direct calculation below).
2. `finrank_finite_of_matching_translate` (over in
   `GenListFinrankAssembly.lean`, not this file — see that file's own
   docstring on why): once fact 1's `Δ`-parametrization is composed with
   `decoupledSystem_zeroDimensional`'s existing finiteness result (proved
   there for one fixed `sa, sb : SampleTarget p`, at the RING level —
   `Module.Finite (F p) (Rdec p ⧸ Ideal.span (genList ...))`, not
   directly a `Set`-level statement about Mumford-coordinate tuples),
   what is available is: for a FIXED target `(sa,sb)`, the associated
   ring is finite-dimensional. **Bridging that ring-level fact to a
   `Set`-level "the tuples of points solving the matching equation and
   reducing to `(sa,sb)` form a finite set" statement — which is what
   fact 1's `Δ` would need to range over a finite set of — is NOT
   established anywhere in this project as of this pass** (checked: no
   file states or uses `Nat.card`/`Set.Finite` for a *point*-level
   solution set, only for the *ring* `Rdec p ⧸ I` itself, e.g.
   `decoupledSystem_degree_uniform`'s own `Nat.card (Rdec p ⧸ _) ≤ d`).
   Constructing that bridge (an `F p`-algebra-hom-counting or
   `MaximalSpectrum`-style argument from `Module.Finite` to "finitely
   many `Idx → \bar{F p}`-valued zeros") is real additional content, not
   attempted in this file — so fact 1 below is stated and proved in
   full, but the "Δ ranges over a finite set" half of what was asked for
   this pass is **not** yet formalized, and is flagged here rather than
   asserted without the missing bridge.

**Update, later pass — the actual rigidity mechanism (`Δ = 0`, not just
"`Δ` ranges over a finite set") is now identified, per outside review's
correction, and its general-topology core is formalized in
`OrbitMapConstant.lean`.** The correct argument does NOT go through
finiteness-of-the-solution-set alone (a finite abstract group can act
nontrivially on a finite set, so that route was a dead end, confirmed
against the counterexample already discussed before this update landed).
The real mechanism: fact 1's `Δ`, ranging over ALL of `Jacobian H D` (not
just values realized by an actual second solution — any `Δ ∈ J` produces
a genuine translate, since a genus-2 curve's every degree-0 class is
`[Q1]+[Q2]-2[δ₀]` for some points `Q1,Q2`, by Riemann–Roch, matching the
`SampleTargetFromAlpha` structure this project already has), defines an
ALGEBRAIC orbit map `Δ ↦ G(Δ) • s` for each solution `s` — and `S` being
0-dimensional (`decoupledSystem_zeroDimensional`'s regular-sequence
result) plus `J` being CONNECTED (a fact about `J` as a variety, not
merely a group) forces that orbit map constant, hence `Δ = 0` given
faithfulness. `OrbitMapConstant.lean` formalizes the general-topology
core of this (`PreconnectedSpace` + `DiscreteTopology` + continuity ⟹
constant, via genuine current-Mathlib4 `PreconnectedSpace.constant`) —
see that file for exactly what is and is not proved, in particular that
`Jacobian H D` does NOT yet carry any topology in this project and
building one (Zariski, connectedness) is flagged there as a substantial
separate undertaking, not attempted.
-/

-- `Jacobian`, `PrincipalDivisorData` live in `namespace HyperellipticPolynomial`
-- (`DivisorClassGroup.lean`), not inside `Genus2Lean` — opening it here
-- (rather than re-declaring `namespace HyperellipticPolynomial` under
-- `Genus2Lean`, which would create a distinct, empty namespace that can't
-- see these definitions) is the pattern `AlphaLocusDegreeUniform.lean`
-- already uses for the same reason.
open HyperellipticPolynomial

namespace Genus2Lean
namespace HyperellipticPolynomialMatching

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-! ## Fact 1: any two solutions differ by a common translation -/

/-- **Any two solutions of the matching equation `[P1]+[P2]-[P3]-[P4] =
target` are related by a single common translation `Δ`, applied to BOTH
sides simultaneously.**

Pure `AddCommGroup` algebra, stated at the `Jacobian H D` level (so it
applies uniformly whether the four points are supplied directly or via
`s D δ₀`, `toJacobian`, or any other map into `Jacobian H D` — nothing
below inspects how `P1,P2,P3,P4` arose). Given two solutions
`(P1,P2,P3,P4)` and `(P1',P2',P3',P4')` of the SAME equation
`P1+P2-P3-P4 = target = P1'+P2'-P3'-P4'` (writing the four points'
already-embedded classes as plain `Jacobian H D` elements `P1 P2 P3 P4`
etc., matching this file's convention below), defining
`Δ := (P1+P2) - (P1'+P2')` (the ONLY definition that actually follows
from the two equations — see this file's module docstring on the earlier
draft's typo) gives `P1+P2 = P1'+P2'+Δ` immediately from `Δ`'s own
definition, and `P3+P4 = P3'+P4'+Δ` by subtracting the two hypotheses and
substituting. -/
theorem matching_solutions_translate_by_delta
    (target : Jacobian H D)
    (P1 P2 P3 P4 P1' P2' P3' P4' : Jacobian H D)
    (heq : P1 + P2 - P3 - P4 = target)
    (heq' : P1' + P2' - P3' - P4' = target) :
    ∃ Δ : Jacobian H D, P1 + P2 = P1' + P2' + Δ ∧ P3 + P4 = P3' + P4' + Δ := by
  refine ⟨(P1 + P2) - (P1' + P2'), by abel, ?_⟩
  -- From `heq`/`heq'`: `P1+P2-P3-P4 = P1'+P2'-P3'-P4'`, i.e.
  -- `(P1+P2)-(P1'+P2') = (P3+P4)-(P3'+P4')` — rearranged, exactly the
  -- claim with `Δ := (P1+P2)-(P1'+P2')` substituted in. `heq.trans
  -- heq'.symm` gives that combined equation directly; the goal then
  -- follows by pure `AddCommGroup` rearrangement: subtract the goal's
  -- two sides, show the difference equals `(P1'+P2'-P3'-P4') -
  -- (P1+P2-P3-P4)` by `abel` alone (a pure rearrangement, no hypothesis
  -- needed), then that difference is `0` by `hsub`.
  have hsub : P1 + P2 - P3 - P4 = P1' + P2' - P3' - P4' := heq.trans heq'.symm
  rw [← sub_eq_zero]
  have hrearrange : P3 + P4 - (P3' + P4' + ((P1 + P2) - (P1' + P2')))
      = (P1' + P2' - P3' - P4') - (P1 + P2 - P3 - P4) := by abel
  rw [hrearrange, ← hsub, sub_self]

end HyperellipticPolynomialMatching
end Genus2Lean
