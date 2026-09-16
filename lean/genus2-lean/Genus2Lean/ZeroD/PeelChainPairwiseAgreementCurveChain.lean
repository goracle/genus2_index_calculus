import Mathlib
import Genus2Lean.ZeroD.PeelChainPairwiseAgreementWiring
import Genus2Lean.ZeroD.CurveRelationChainFinrank
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# The four-stage curve-relation chain, pairwise-agreement-up-to-sign form

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Next concrete steps" item
2 (chain step 1's per-stage facts into one statement), curve-relation half,
built against the chosen "agree up to sign" route
(`PeelChainPairwiseAgreementWiring.lean`'s
`curveRelationGen_ofList_pairwise_eq_up_to_sign`). Mirrors
`CurveRelationChainFinrank.lean`'s `finrank_le_and_finite_curveRelationGenChain`
exactly in shape and stage order (`wa1/a1` then `wa2/a2` then `wb1/b1` then
`wb2/b2`, matching `genList`'s own tail order once the four curve relations
are moved to the front per `GenListTriangularReorder.lean`), but chains a
DIFFERENT kind of per-stage fact: instead of bounding `finrank` of one
abstract copy of the extended ring, this file compares TWO abstract
solution tuples `t1,t2,t3,t4` and `t1',t2',t3',t4' : A` (the four `w`-values
of two candidate solutions, both living in the SAME prefix ring `A := Rdec p
⧸ Ideal.ofList gens` — matching `PeelChainPairwiseAgreement.lean`'s own
module docstring on why this is a genuinely smaller, `A`-level claim, not a
`B`-level `Module.Finite` one) and concludes each pair agrees up to sign,
independently per stage — no chaining content is actually needed beyond
applying the single-stage fact four times, since (unlike the `finrank`
chain) no stage's hypothesis or conclusion depends on the PREVIOUS stage's
outcome: each `curveA*`/`curveB*` relation is a fact about `A` alone (via
`curveFImage`), not about a further-extended ring the previous stage built.

**Why this is simpler than `finrank_le_and_finite_curveRelationGenChain`,
concretely**: that theorem's four stages are genuinely sequential — each
appends a new generator to the PREVIOUS stage's already-extended ring, so
stage 2 literally cannot be stated without stage 1's output ring in its
signature. Here, all four `t_i, t_i'` pairs are elements of the SAME base
ring `A` from the start (they are the four `w`-variables' two candidate
values, not four nested ring extensions), so the four per-stage facts are
independent and can be proved by four separate applications of
`curveRelation_forces_eq_up_to_sign`, packaged into one `∧`-conjunction —
no `obtain`/`haveI`-threading of instances between stages is needed, unlike
the `finrank` chain's genuine fold.

**Output shape**: a 4-way conjunction of `Or`s (`t1 = t1' ∨ t1 = -t1'`,
etc.), the natural "16 candidate sign patterns" statement — deliberately
NOT collapsed into a single `Fin 4 → Bool`-indexed existential here, since
downstream callers (the eventual pairwise-agreement Assembly, chaining this
against the eight linear stages) will want to `rcases` each conjunct
independently, matching how `PeelChainPairwiseAgreementWiring.lean`'s own
linear-stage theorem is consumed elsewhere in this sub-effort. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial
open Idx

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **The four-stage curve-relation pairwise-agreement chain, up to sign,
`curveFImage`-native statement.** Given two candidate tuples
`(t1,t2,t3,t4)` and `(t1',t2',t3',t4') : A := Rdec p ⧸ Ideal.ofList gens`
(the four `w`-variables' two candidate values), both satisfying the SAME
four curve relations over the SAME prefix `gens`, each pair agrees up to
sign — independently, stage by stage, `2^4 = 16` candidate combined sign
patterns total. Needs `[IsDomain A]` once, matching
`curveRelationGen_ofList_pairwise_eq_up_to_sign`'s own hypothesis at each
of the four call sites (the `mul_eq_zero` step every stage's proof uses). -/
theorem curveChain_pairwise_eq_up_to_sign
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p)
    [IsDomain (Rdec p ⧸ Ideal.ofList gens)]
    (t1 t2 t3 t4 t1' t2' t3' t4' : Rdec p ⧸ Ideal.ofList gens)
    (ht1 : (Polynomial.aeval t1)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a1)) = 0)
    (ht1' : (Polynomial.aeval t1')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a1)) = 0)
    (ht2 : (Polynomial.aeval t2)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a2)) = 0)
    (ht2' : (Polynomial.aeval t2')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 a2)) = 0)
    (ht3 : (Polynomial.aeval t3)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b1)) = 0)
    (ht3' : (Polynomial.aeval t3')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b1)) = 0)
    (ht4 : (Polynomial.aeval t4)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b2)) = 0)
    (ht4' : (Polynomial.aeval t4')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b2)) = 0) :
    (t1 = t1' ∨ t1 = -t1') ∧ (t2 = t2' ∨ t2 = -t2') ∧
    (t3 = t3' ∨ t3 = -t3') ∧ (t4 = t4' ∨ t4 = -t4') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact curveRelationGen_ofList_pairwise_eq_up_to_sign p gens c0 c1 c2 c3 c4 a1
      t1 t1' ht1 ht1'
  · exact curveRelationGen_ofList_pairwise_eq_up_to_sign p gens c0 c1 c2 c3 c4 a2
      t2 t2' ht2 ht2'
  · exact curveRelationGen_ofList_pairwise_eq_up_to_sign p gens c0 c1 c2 c3 c4 b1
      t3 t3' ht3 ht3'
  · exact curveRelationGen_ofList_pairwise_eq_up_to_sign p gens c0 c1 c2 c3 c4 b2
      t4 t4' ht4 ht4'

end DecoupledSystem
end Genus2Lean
