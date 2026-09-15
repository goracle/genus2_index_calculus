import Mathlib
import Genus2Lean.ZeroD.PeelChainPairwiseAgreement
import Genus2Lean.ZeroD.CurveRelationStageWiring
import Genus2Lean.ZeroD.LinearElimStageWiring
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# Wiring pairwise agreement against `genList`'s literal generator shapes

Continuation of `PeelChainPairwiseAgreement.lean`'s abstract per-stage
facts (`linearElim_pairwise_eq`, `curveRelation_forces_eq`), specialized
to the literal `curveRelationGen`/`linearElimGen` shapes
`CurveRelationStageWiring.lean`/`LinearElimStageWiring.lean` already wire
against a generic `Ideal.ofList gens` prefix — mirroring those two files'
own conventions exactly (`gens : List (Rdec p)`, `w x : Idx`, `curveFImage`
for the curve stages), rather than introducing new naming.

## The genuinely negative finding this file records

**Checked directly against `curveA1`'s literal definition
(`DecoupledSystemRegular.lean` §3) and `SampleTarget`'s own field list,
not assumed**: there is no sign convention anywhere in the symbolic
algebra pinning `wa1` (or `wa2,wb1,wb2`) to one square root over the
other. `SampleTarget` carries only `u0,u1,v0,v1` — no `w`-fields at all —
and `curveA1 = wa1'^2 - f(a1')` is the ONLY constraint on `wa1` anywhere
in `Rdec p`'s free-polynomial presentation; `wa1` and `-wa1` are
interchangeable as far as this symbolic system is concerned. So
`curveRelation_forces_eq`'s `hsign : t ≠ -t'` hypothesis (`PeelChainPairwise
Agreement.lean`) is NOT derivable from `theData`/`genList`'s own
definitions — it is a genuine extra input this project does not currently
supply, most likely resolvable only by consulting `Reduce/AlphaReduce
.lean`'s actual Mumford-coordinate/Cantor-reduction construction (which
this file does not attempt) or by weakening the eventual uniqueness target
to "agree up to the four independent `w`-sign choices" (16 = 2^4 candidate
sign patterns, not literally the single point the roadmap's corrected
target originally hoped for) rather than genuine coordinatewise equality.
**This file states the needed hypothesis explicitly, by name, at each of
the four curve-relation call sites, rather than attempting a proof or a
workaround** — per this project's proof discipline (don't weaken a
theorem to dodge a proof one hasn't attempted, but also don't manufacture
a false derivation), this is exactly the "named, checkable, per-stage
condition" the roadmap's Core Strategy section already asks for, just
discovered to have no free derivation rather than assumed to have one.

## What this file wires, concretely

- **Linear stages (`Fu0`–`Fu3`, `Fv0`–`Fv3`) — unconditional, matching
  `linearElim_pairwise_eq`'s own unconditional shape.**
  `linearElim_ofList_pairwise_eq` specializes it to `linearElimGen`'s
  literal shape (`LinearElimStageWiring.lean`'s own generator), for two
  candidate values `t t' : Rdec p ⧸ Ideal.ofList gens` of the
  newly-peeled variable.
- **Curve-relation stages (`curveA1`,...,`curveB2`) — needs the `hsign`
  hypothesis above, stated explicitly, PLUS an `IsDomain` instance not
  discharged here.** `curveRelationGen_ofList_pairwise_eq` specializes
  `curveRelation_forces_eq` to `curveRelationGen`'s literal shape, taking
  `hsign` as an explicit hypothesis (NOT proved, per this file's own
  module docstring) and `[IsDomain (Rdec p ⧸ Ideal.ofList gens)]` as an
  explicit instance argument — needed by the abstract lemma's
  `mul_eq_zero` step, and, like `hsign`, NOT checked against any actual
  prefix of `genList` in this file; whether the real 8-or-more-generator
  prefixes this gets applied to are genuinely integral domains is a
  separate fact left for the wiring pass that instantiates `gens`.

## What this file does NOT do

Chain these per-stage facts across all twelve of `genList`'s literal
stages into one `x = x'` (all-12-coordinates) statement — that final
chaining, and the decision of whether to pursue the `Reduce`-specific
sign fact or the weaker "agree up to sign" target instead, are left to
the next pass, per the roadmap's own "Next concrete steps" list.
-/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial

variable (p : ℕ) [Fact (Nat.Prime p)]

/-! ## Linear-elimination stages: unconditional pairwise agreement -/

/-- **Pairwise agreement, wired to `linearElimGen`'s literal shape**
(`LinearElimStageWiring.lean`'s own generator, `c - X u * d` for
already-fixed `c d : Rdec p` — matching `Fu0 = d.u1_num 0 - U0' p *
d.u1_den 0`'s exact shape, `c := d.u1_num 0`, `d := d.u1_den 0`,
`u := U0`). Two candidate values `t, t' : A := Rdec p ⧸ Ideal.ofList gens`
of the newly-peeled variable `X u`, both satisfying the relation `mk c =
t * mk d` (`d`'s image `dA` a unit — the SAME per-stage hypothesis
`finrank_le_linearElim_ofList_cons` already needs), agree —
UNCONDITIONALLY, no side hypothesis, matching `linearElim_pairwise_eq`'s
own shape. Stated directly in terms of `mk c`/`mk d`'s images `cA dA`
(the shape `linearElimPoly` is a function of), rather than
`linearElimGen`'s own `Rdec p`-level literal — mirroring exactly how
`finrank_le_linearElim_ofList_cons`'s proof internally reduces the SAME
generator to precisely these images (`cA`/`dA`, that file's own `set`
lines) before invoking the abstract `finrank_le_of_linear_elim` fact this
theorem's counterpart, `linearElim_pairwise_eq`, plays the same role
for. -/
theorem linearElim_ofList_pairwise_eq
    (gens : List (Rdec p)) (c d : Rdec p) (u : Idx)
    (hd : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) d))
    (t t' : Rdec p ⧸ Ideal.ofList gens)
    (ht : (Polynomial.aeval t) (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) c)
      (Ideal.Quotient.mk (Ideal.ofList gens) d)) = 0)
    (ht' : (Polynomial.aeval t') (linearElimPoly
      (Ideal.Quotient.mk (Ideal.ofList gens) c)
      (Ideal.Quotient.mk (Ideal.ofList gens) d)) = 0) :
    t = t' :=
  linearElim_pairwise_eq (Ideal.Quotient.mk (Ideal.ofList gens) c)
    (Ideal.Quotient.mk (Ideal.ofList gens) d) hd t t' ht ht'

/-! ## Curve-relation stages: pairwise agreement, GIVEN the sign hypothesis
## this file's module docstring flags as not derivable from `theData` -/

/-- **Pairwise agreement, wired to `curveRelationGen`'s literal shape —
NEEDS `hsign`, per this file's module docstring.** Two candidate values
`t, t'` of the newly-peeled `w`-variable, both roots of the same
curve-relation image `curveFImage p gens c0 c1 c2 c3 c4 x` over the prefix
`A := Rdec p ⧸ Ideal.ofList gens`, agree PROVIDED `t ≠ -t'` — this
hypothesis is NOT proved or derived here (see module docstring: no sign
convention exists anywhere in `theData`'s symbolic algebra to derive it
from), it is taken as an explicit extra input, exactly matching
`curveRelation_forces_eq`'s own shape. -/
theorem curveRelationGen_ofList_pairwise_eq
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p) (x : Idx)
    [IsDomain (Rdec p ⧸ Ideal.ofList gens)]
    (t t' : Rdec p ⧸ Ideal.ofList gens)
    (ht : (Polynomial.aeval t)
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 x)) = 0)
    (ht' : (Polynomial.aeval t')
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 x)) = 0)
    (hsign : t ≠ -t') :
    t = t' :=
  curveRelation_forces_eq (curveFImage p gens c0 c1 c2 c3 c4 x) t t' ht ht' hsign

end DecoupledSystem
end Genus2Lean
