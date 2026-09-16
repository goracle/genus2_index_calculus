import Mathlib
import Genus2Lean.ZeroD.GenListFinrankResultantAssembly
import Genus2Lean.ZeroD.SharedPivotFourStageFinrank

/-!
# Closing the four-shared-pivot-stage gap: curves + `U0` + `U1,V0,V1`

`GenListFinrankResultantAssembly.lean`'s own module docstring names this
file's job explicitly: chain `genList_triangular_finrank_le_of_base`'s
curve-relation-then-`U0` output prefix into
`SharedPivotFourStageFinrank.lean`'s `finrank_le_and_finite_sharedPivot_
U1V0V1_chain`, which supplies the missing `U1,V0,V1` stages. Neither
source file does this wiring itself — `genList_triangular_finrank_le_of_base`
stops after `U0` (a gap flagged in `SharedPivotFourStageFinrank.lean`'s own
docstring, discovered this pass), and `finrank_le_and_finite_sharedPivot_
U1V0V1_chain` is deliberately generic over its starting prefix `gens`,
taking curve-then-`U0`-hood as an unstated but intended specialization
(again per that file's own docstring: "typically
`GenListFinrankResultantAssembly.lean`'s own curve-then-`U0` output
prefix, but genuinely arbitrary here").

**What this file adds, honestly**: nothing but composition. Both halves
are proved elsewhere and used here as black boxes via `obtain`, exactly
matching the calling convention `GenListFinrankResultantAssembly.lean`
already established for chaining `finrank_le_and_finite_curveRelationChain`
into `finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2`. The
only new content is the final `finrank` bound, obtained by chaining the
two stage's `≤`-bounds via `le_trans` and `Nat.mul_le_mul` (curve+`U0`'s
bound `B4` composes with `U1V0V1`'s bound `B'`, itself stated against the
curve+`U0` quotient's own `finrank` — i.e. `B'` genuinely depends on `B4`'s
witness ring, not a free second parameter, so the two `∃`s combine by
instantiating the second existential's own bound hypothesis with the
first's conclusion, not by multiplying two independent naturals).

**Not attempted here**: transporting the result from `genListTriangular`'s
order onto `genList`'s own literal order (`quot_genListTriangular_eq_quot_
genList`, per `GenListFinrankResultantAssembly.lean`'s own docstring, "a
mechanical last step left for whoever calls this file against
`genList_finrank_le` itself") — that transport is orthogonal to closing
the four-stage gap and stays out of scope for this file, consistent with
`GenListFinrankResultantAssembly.lean`'s own stated scope. -/

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

set_option maxHeartbeats 4000000 in
/-- **All four shared-pivot stages (`U0,U1,V0,V1`) chained after the
curve-relation chain**, closing the gap `SharedPivotFourStageFinrank.lean`'s
own docstring flags in `genList_triangular_finrank_le_of_base`. Given the
same curve-chain hypotheses that theorem needs, plus the raw `U1,V0,V1`
per-stage ingredient data (`IsUnit` of each pivot denominator,
`Module.Finite` of each resultant quotient, `Nontrivial` of each doubly-
extended ring) stated against the curve-then-`U0` prefix that theorem's
own proof produces, concludes `Module.Finite`/`Nontrivial`/a `finrank`
bound on the full eight-generator-extended prefix (four curve relations,
then all four shared-pivot pairs). -/
theorem genList_triangular_finrank_le_of_base_fourStage
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p) (d : DecoupledGenerators p)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    (hfin : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens))
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    -- Curve chain's four non-unit side-conditions (identical to
    -- `genList_triangular_finrank_le_of_base`'s own).
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
    -- `U0` stage, against the curve-extended prefix (identical to
    -- `genList_triangular_finrank_le_of_base`'s own).
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
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]))))))))
    -- Raw `U1,V0,V1` ingredient data, stated against the curve-then-`U0`
    -- prefix (`gens ++ [curves] ++ [Fu0,Fu1]`).
    (hd1_U1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) (d.u1_den 1)))
    [hU1_1_nontriv : Nontrivial ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))
        (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))))]
    (hfinRes_U1 : Module.Finite (F p) ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) (d.u2_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) (d.u1_den 1) -
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) (d.u1_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) (d.u2_den 1)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])))))
    (hnontrivB_U1 : Nontrivial
      (((Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
            [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
             linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))
            (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
            Set (Rdec p ⧸ Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])))) ⧸
        Ideal.span ({((Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))
              (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
                [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
                 linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))))).comp
            (Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))))
            (linearElimGen p (d.u2_num 1) (d.u2_den 1) U1)} :
          Set (((Rdec p ⧸ Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
            [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
             linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))
              (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
                [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
                 linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]))))))))
    -- `V0` stage, against `[curves,Fu0,Fu1,Fu2,Fu3]`.
    (hd1_V0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v1_den 0)))
    [hV0_1_nontriv : Nontrivial ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
        (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))]
    (hfinRes_V0 : Module.Finite (F p) ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v2_num 0) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v1_den 0) -
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v1_num 0) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v2_den 0)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])))))
    (hnontrivB_V0 : Nontrivial
      (((Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
            [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
             linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
            (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
            Set (Rdec p ⧸ Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])))) ⧸
        Ideal.span ({((Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
              (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
                [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
                 linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))).comp
            (Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))
            (linearElimGen p (d.v2_num 0) (d.v2_den 0) V0)} :
          Set (((Rdec p ⧸ Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
            [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
             linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
              (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
                [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
                 linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))))))
    -- `V1` stage, against `[curves,Fu0,Fu1,Fu2,Fu3,Fv0,Fv1]`.
    (hd1_V1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
      [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_den 1)))
    [hV1_1_nontriv : Nontrivial ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
        [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
        (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))))]
    (hfinRes_V1 : Module.Finite (F p) ((Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
        [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v2_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_den 1) -
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v2_den 1)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])))))
    (hnontrivB_V1 : Nontrivial
      (((Rdec p ⧸ Ideal.ofList (gens ++
          [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
           curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
          [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
           linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
          [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
            [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
             linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
            [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
             linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
            (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
            Set (Rdec p ⧸ Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
              [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])))) ⧸
        Ideal.span ({((Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
              [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
              (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
                [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
                 linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
                [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
                 linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))))).comp
            (Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
              [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))))
            (linearElimGen p (d.v2_num 1) (d.v2_den 1) V1)} :
          Set (((Rdec p ⧸ Ideal.ofList (gens ++
            [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
             curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
            [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
             linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
            [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
             linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
               curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
              [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
               linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
              [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
              (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
                 curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
                [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
                 linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
                [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
                 linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])))))))) :
    ∃ B : ℕ,
      Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0,
         linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1])) ∧
      Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0,
         linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1])) ∧
      Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0,
         linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1])) ≤ B := by
  -- Stage 1: curves + `U0`, via `genList_triangular_finrank_le_of_base`,
  -- called as a black box.
  obtain ⟨_B4, hfin4, hnontriv4, _hbound4⟩ :=
    genList_triangular_finrank_le_of_base p gens c0 c1 c2 c3 c4 d
      hfin hgu1 hgu2 hgu3 hgu4 hd1_U0 hfinRes_U0 hnontrivB_U0
  haveI : Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) := hnontriv4
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) :=
    commRing_strongRankCondition _
  haveI hfin4' : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])) := hfin4
  -- Stage 2: `U1,V0,V1`, via `finrank_le_and_finite_sharedPivot_
  -- U1V0V1_chain`, called as a black box against the curve+`U0` prefix.
  --
  -- The chain lemma's own `hd1_V1`/`hfinRes_V1`/`hnontrivB_V1` parameters
  -- are stated against `(chain's own gens) ++ [Fu1a,Fu1b,Fv0a,Fv0b]` -- a
  -- SINGLE 4-element list literal in one `++` -- whereas this theorem's
  -- own same-named hypotheses are stated against `gens ++ [curves] ++
  -- [Fu0..] ++ [Fu1..] ++ [Fv0..]`, four separate two-element-list `++`s.
  -- These list values are equal (by `List.append_assoc`) but not
  -- syntactically/definitionally equal, so Lean's unifier rejects the
  -- hypotheses outright at the call below unless we rewrite them first.
  have hlist_eq_V1 : gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0] ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1] ++
      [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0] =
    (gens ++
      [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
       curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
      [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
       linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]) ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
       linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0] := by
    simp [List.append_assoc]
  -- `hV1_1_nontriv` is an instance-implicit in this file's own signature
  -- (not passed positionally below), stated against the same
  -- wrongly-associated list as `hd1_V1` et al. -- it must be rewritten
  -- too so that the chain lemma's instance search can find it under its
  -- expected (correctly-associated) type.
  rw [hlist_eq_V1] at hd1_V1 hfinRes_V1 hnontrivB_V1 hV1_1_nontriv
  obtain ⟨B', hfin8, hnontriv8, hbound8⟩ :=
    finrank_le_and_finite_sharedPivot_U1V0V1_chain p
      (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0])
      d hfin4' hd1_U1 hfinRes_U1 hnontrivB_U1 hd1_V0 hfinRes_V0 hnontrivB_V0
      hd1_V1 hfinRes_V1 hnontrivB_V1
  refine ⟨B', ?_, ?_, ?_⟩
  · have heq : gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0,
         linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] =
      (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]) ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] := by
      simp [List.append_assoc]
    rw [heq]
    exact hfin8
  · have heq : gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0,
         linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] =
      (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]) ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] := by
      simp [List.append_assoc]
    rw [heq]
    exact hnontriv8
  · have heq : gens ++
        [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0,
         linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] =
      (gens ++ [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
        [linearElimGen p (d.u1_num 0) (d.u1_den 0) U0,
         linearElimGen p (d.u2_num 0) (d.u2_den 0) U0]) ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] := by
      simp [List.append_assoc]
    rw [heq]
    exact hbound8

end DecoupledSystem
end Genus2Lean
