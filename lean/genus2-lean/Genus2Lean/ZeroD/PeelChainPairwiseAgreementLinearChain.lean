import Mathlib
import Genus2Lean.ZeroD.PeelChainPairwiseAgreementWiring
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# The eight matching-generator stages, pairwise-agreement form

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Next concrete steps" item
2 (chain step 1's per-stage facts into one statement), linear half —
the counterpart to `PeelChainPairwiseAgreementCurveChain.lean`'s
four-stage curve chain, built against
`PeelChainPairwiseAgreementWiring.lean`'s `linearElim_ofList_pairwise_eq`.

**Shared-pivot structure, not a clean one-generator-per-variable list.**
Per the roadmap's own diagnosis (`FuList`/`FvList`, `DecoupledSystemRegular
.lean` §4bis-adjacent): `U0` is pivoted by BOTH `Fu0` (`d.u1_num/u1_den 0`)
and `Fu1` (`d.u2_num/u2_den 0`) — an over-determined pair for one variable
— and likewise `U1`/`Fu2`/`Fu3`, `V0`/`Fv0`/`Fv1`, `V1`/`Fv2`/`Fv3`. Unlike
`SharedPivotResultantElimFinite.lean`'s `finrank`-bounding treatment of
this same shared-pivot structure (which genuinely needs BOTH relations at
once, via their resultant, to bound `finrank` of the doubly-extended
ring), pairwise agreement needs only ONE of the two relations per pivot:
`linearElim_ofList_pairwise_eq` already concludes unconditional agreement
`t = t'` for two candidate values of the SAME peeled variable `u`
satisfying the SAME single relation in the SAME base ring
`A := Rdec p ⧸ Ideal.ofList gens` — no ring extension per stage, matching
`PeelChainPairwiseAgreementCurveChain.lean`'s own "all four `t_i,t_i'`
live in the same base ring" observation exactly. So each pivot's
agreement fact is proved from whichever one of its two generators has a
supplied `IsUnit` denominator hypothesis; the other generator is not
needed for THIS fact (it is still needed elsewhere, for the `finrank`
bound's resultant, which is a strictly stronger per-pivot claim than mere
agreement).

**Hypothesis choice, this file: use the FIRST generator of each shared
pair** (`Fu0` for `U0`, `Fu2` for `U1`, `Fv0` for `V0`, `Fv2` for `V1`) —
an arbitrary but fixed convention, since either suffices and using both
would just duplicate the same conclusion `t = t'` twice per pivot. A
caller who only has the SECOND generator's unit hypothesis available
should invoke `linearElim_ofList_pairwise_eq` directly against that
generator instead of this file's packaged theorem.

**Output shape**: a 4-way conjunction, one `t = t'` fact per pivot
(`U0,U1,V0,V1`), matching `curveChain_pairwise_eq_up_to_sign`'s own
4-way-conjunction packaging so the eventual 12-stage Assembly can
`rcases` each of the eight linear/four curve conjuncts uniformly. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial
open Idx

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **The four shared-pivot pairs' pairwise-agreement facts, `theData`-
native statement.** Given two candidate tuples of target values
`(U0v,U1v,V0v,V1v)` and `(U0v',U1v',V0v',V1v') : A := Rdec p ⧸
Ideal.ofList gens`, each satisfying `Fu0`/`Fu2`/`Fv0`/`Fv2`'s literal
relation (the first generator of each shared-pivot pair, per this file's
own convention above) over the same prefix `gens`, and each pivot's
denominator a unit in `A`, the two tuples agree on all four target
variables. -/
theorem theData_linear_pairwise_eq
    (gens : List (Rdec p)) (d : DecoupledGenerators p)
    (hdU0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 0)))
    (hdU1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1)))
    (hdV0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 0)))
    (hdV1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 1)))
    (U0v U1v V0v V1v U0v' U1v' V0v' V1v' : Rdec p ⧸ Ideal.ofList gens)
    (htU0 : (Polynomial.aeval U0v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 0))) = 0)
    (htU0' : (Polynomial.aeval U0v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 0))) = 0)
    (htU1 : (Polynomial.aeval U1v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1))) = 0)
    (htU1' : (Polynomial.aeval U1v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1))) = 0)
    (htV0 : (Polynomial.aeval V0v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 0))) = 0)
    (htV0' : (Polynomial.aeval V0v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 0))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 0))) = 0)
    (htV1 : (Polynomial.aeval V1v) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 1))) = 0)
    (htV1' : (Polynomial.aeval V1v') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_num 1))
      (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 1))) = 0) :
    U0v = U0v' ∧ U1v = U1v' ∧ V0v = V0v' ∧ V1v = V1v' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact linearElim_ofList_pairwise_eq p gens (d.u1_num 0) (d.u1_den 0) U0 hdU0
      U0v U0v' htU0 htU0'
  · exact linearElim_ofList_pairwise_eq p gens (d.u1_num 1) (d.u1_den 1) U1 hdU1
      U1v U1v' htU1 htU1'
  · exact linearElim_ofList_pairwise_eq p gens (d.v1_num 0) (d.v1_den 0) V0 hdV0
      V0v V0v' htV0 htV0'
  · exact linearElim_ofList_pairwise_eq p gens (d.v1_num 1) (d.v1_den 1) V1 hdV1
      V1v V1v' htV1 htV1'

end DecoupledSystem
end Genus2Lean
