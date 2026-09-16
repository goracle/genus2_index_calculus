import Mathlib
import Genus2Lean.ZeroD.PeelChainPairwiseAgreementCurveChain
import Genus2Lean.ZeroD.PeelChainPairwiseAgreementLinearChain
import Genus2Lean.ZeroD.GenListTriangularReorder

/-!
# All twelve stages, pairwise agreement, chained against `genListTriangular`

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Next concrete steps" item
2, completed: chains `PeelChainPairwiseAgreementCurveChain.lean`'s
four-stage curve chain (agree up to sign) together with
`PeelChainPairwiseAgreementLinearChain.lean`'s four-shared-pivot linear
chain (agree unconditionally) into one statement about two candidate
solutions of all twelve of `genList`'s generators.

**Order: curves first, matching generators second**, mirroring
`GenListFinrankResultantAssembly.lean`'s own choice and
`GenListTriangularReorder.lean`'s `genListTriangular` presentation —
for the SAME reason given there (`FuList`/`FvList`'s coefficients are
only guaranteed independent of `U0,U1,V0,V1`, not of the curve
variables, so the curve relations must be eliminated first for the
matching generators' coefficients to be genuine constants of the
ambient quotient). Unlike the `finrank` assembly, this file does NOT
need to extend the ring stage by stage: pairwise agreement is a claim
about two elements of the SAME fixed quotient
`A := Rdec p ⧸ Ideal.ofList gens` at every stage (see
`PeelChainPairwiseAgreementCurveChain.lean`'s and
`PeelChainPairwiseAgreementLinearChain.lean`'s own docstrings for why),
so the curve stage's four facts and the linear stage's four facts are
proved over the SAME `gens := genListTriangular ...`'s underlying
prefix in one flat conjunction, not folded through four/eight nested
ring extensions.

**What this proves**: given two solution tuples of `genListTriangular`'s
twelve generators (equivalently, since `Ideal.ofList` only depends on the
generators as polynomials, of `theData`'s twelve target/sample-curve
values `wa1,wa2,wb1,wb2,U0,U1,V0,V1` — `a1,a2,b1,b2` are never pivoted,
so they do not appear as a conclusion here, matching the roadmap's own
observation that these four are coefficients only), living in
`A := Rdec p ⧸ Ideal.ofList gens` for `gens := []` (the fully-eliminated
quotient, i.e. `A = Rdec p ⧸ Ideal.ofList genListTriangular`), the two
solutions agree on `U0,U1,V0,V1` exactly and on `wa1,wa2,wb1,wb2` up to
independent sign choices — `2^4 = 16` candidate patterns overall.

**What this does NOT prove**: that the sign ambiguity resolves to a
single point, or that `Δ = 0` follows — per the roadmap's "actual
remaining blocker" section, that needs either a `Reduce`-side
non-degeneracy input (route (i)) or restating the ultimate goal at the
fiber/x-coordinate level (route (ii), the roadmap's recommended
default). This file only supplies the "up to 16 sign patterns"
uniqueness fact those routes both build on.

**Not yet done**: transporting this statement from `genListTriangular`'s
presentation back to `genList`'s own literal stated order. Mechanical,
via `quot_genListTriangular_eq_quot_genList` (`GenListTriangularReorder
.lean`) exactly as `GenListFinrankResultantAssembly.lean`'s own docstring
already flags for the `finrank` bound — left for whoever wires this
against `genList_finrank_le`/the eventual `SampleTargetFromAlpha`
restatement, since that step also needs deciding the `theData`
`sa,sb`-to-`genList`-argument correspondence this file does not touch. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial
open Idx

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **All twelve stages of `genListTriangular`, pairwise agreement.**
Two candidate solution tuples of the curve-relation `w`-values
(`t1,t2,t3,t4` / `t1',t2',t3',t4'`, i.e. `wa1,wa2,wb1,wb2`) and the
target values (`U0v,U1v,V0v,V1v` / `U0v',U1v',V0v',V1v'`), both living in
`A := Rdec p ⧸ Ideal.ofList gens` and both satisfying the same twelve
`genListTriangular`-shaped relations over `gens`, agree on the four
target variables exactly and on the four curve `w`-values up to
independent sign. Packaged as one flat conjunction (curve facts first,
matching four `Fu`/`Fv` shared-pivot facts second, matching
`genListTriangular`'s own curves-then-`Fu`-then-`Fv` order) rather than
re-deriving either chain's proof — this theorem is pure composition of
`curveChain_pairwise_eq_up_to_sign` and `theData_linear_pairwise_eq`,
called once each. -/
theorem genListTriangular_pairwise_eq_up_to_sign
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p) (d : DecoupledGenerators p)
    [IsDomain (Rdec p ⧸ Ideal.ofList gens)]
    (t1 t2 t3 t4 t1' t2' t3' t4' U0v U1v V0v V1v U0v' U1v' V0v' V1v' :
      Rdec p ⧸ Ideal.ofList gens)
    -- Curve-relation hypotheses (`wa1,wa2,wb1,wb2`, over the base `gens`).
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
      (curveRelationPoly (curveFImage p gens c0 c1 c2 c3 c4 b2)) = 0)
    -- Linear-stage hypotheses (`U0,U1,V0,V1`, `theData`-native, over the
    -- SAME base `gens` — matching `GenListFinrankResultantAssembly.lean`'s
    -- own choice to apply the linear stages against the curve-extended
    -- prefix at the `finrank` level; here, since no ring extension is
    -- needed, `gens` is simply whatever prefix the caller already has
    -- both the curve and linear relations holding over).
    (hdU0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 0)))
    (hdU1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1)))
    (hdV0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 0)))
    (hdV1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.v1_den 1)))
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
    ((t1 = t1' ∨ t1 = -t1') ∧ (t2 = t2' ∨ t2 = -t2') ∧
     (t3 = t3' ∨ t3 = -t3') ∧ (t4 = t4' ∨ t4 = -t4')) ∧
    (U0v = U0v' ∧ U1v = U1v' ∧ V0v = V0v' ∧ V1v = V1v') := by
  refine ⟨?_, ?_⟩
  · exact curveChain_pairwise_eq_up_to_sign p gens c0 c1 c2 c3 c4
      t1 t2 t3 t4 t1' t2' t3' t4' ht1 ht1' ht2 ht2' ht3 ht3' ht4 ht4'
  · exact theData_linear_pairwise_eq p gens d hdU0 hdU1 hdV0 hdV1
      U0v U1v V0v V1v U0v' U1v' V0v' V1v'
      htU0 htU0' htU1 htU1' htV0 htV0' htV1 htV1'

end DecoupledSystem
end Genus2Lean
