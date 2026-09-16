import Mathlib
import Genus2Lean.ZeroD.SharedPivotStageWiringFinite

/-!
# All four shared-pivot stages (`U0,U1,V0,V1`), chained

`GenListFinrankResultantAssembly.lean`'s `genList_triangular_finrank_le_of_base`
calls `finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2`
exactly ONCE (for `U0`) despite its own module docstring describing all
four shared-pivot stages — a genuine gap in that file, discovered this
pass, not merely an omission in its docstring. This file supplies the
missing three applications (`U1,V0,V1`), chained after an arbitrary
already-finite starting prefix `gens` (matching
`finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2`'s own
genericity — nothing here is specific to "curve-extended" prefixes,
so this file composes with `GenListFinrankResultantAssembly.lean`'s
existing `U0` stage by taking `gens := ` that stage's own output prefix).

**Why one wrapper theorem rather than three separate ones.** Each stage's
hypotheses must be stated against the PREVIOUS stage's already-extended
prefix — genuinely growing, syntactically-nested types, the same reason
`GenListFinrankResultantAssembly.lean`'s own `U0` stage signature is
already large for just one stage. Three more at that same literal nesting
depth cannot be avoided by cleverness (Lean needs each hypothesis's true
type), so this file accepts the resulting long signature honestly rather
than hiding it — but chains all three calls in one proof via `obtain`/
`haveI`, following the exact `haveI`-then-`obtain` pattern
`GenListFinrankResultantAssembly.lean`'s own `U0` proof already
establishes, so the proof body itself stays a flat sequence of three
near-identical blocks rather than a bespoke argument. -/

namespace Genus2Lean
namespace DecoupledSystem

variable (p : ℕ) [Fact (Nat.Prime p)]

set_option maxHeartbeats 4000000 in
/-- **Chains `U1,V0,V1` after an already-established `U0`-stage prefix.**
Given `gens` already `Module.Finite`/`Nontrivial` (typically
`GenListFinrankResultantAssembly.lean`'s own curve-then-`U0` output
prefix, but genuinely arbitrary here), and the raw per-stage ingredient
data (`IsUnit` of each stage's pivot denominator, `Module.Finite` of each
stage's resultant quotient, `Nontrivial` of each stage's doubly-extended
ring) for `U1` then `V0` then `V1` in sequence — each against the prefix
the PREVIOUS stage in this list produces — concludes `Module.Finite`/
`Nontrivial`/a `finrank` bound on the fully-four-stage-extended prefix. -/
theorem finrank_le_and_finite_sharedPivot_U1V0V1_chain
    (gens : List (Rdec p)) (d : DecoupledGenerators p)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    (hfin : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens))
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    -- `U1` stage (pivot of `Fu2,Fu3`, i.e. `u1_num/u1_den 1`,
    -- `u2_num/u2_den 1`), against `gens`.
    (hd1_U1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1)))
    [hU1_1_nontriv : Nontrivial ((Rdec p ⧸ Ideal.ofList gens) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens)
        (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
        Set (Rdec p ⧸ Ideal.ofList gens)))]
    (hfinRes_U1 : Module.Finite (F p) ((Rdec p ⧸ Ideal.ofList gens) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) (d.u2_num 1) *
          Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_den 1) -
        Ideal.Quotient.mk (Ideal.ofList gens) (d.u1_num 1) *
          Ideal.Quotient.mk (Ideal.ofList gens) (d.u2_den 1)} :
        Set (Rdec p ⧸ Ideal.ofList gens))))
    (hnontrivB_U1 : Nontrivial
      (((Rdec p ⧸ Ideal.ofList gens) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens)
            (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
            Set (Rdec p ⧸ Ideal.ofList gens))) ⧸
        Ideal.span ({((Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList gens)
              (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
              Set (Rdec p ⧸ Ideal.ofList gens)))).comp
            (Ideal.Quotient.mk (Ideal.ofList gens)))
            (linearElimGen p (d.u2_num 1) (d.u2_den 1) U1)} :
          Set ((Rdec p ⧸ Ideal.ofList gens) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens)
              (linearElimGen p (d.u1_num 1) (d.u1_den 1) U1)} :
              Set (Rdec p ⧸ Ideal.ofList gens))))))
    -- `V0` stage (pivot of `Fv0,Fv1`, i.e. `v1_num/v1_den 0`,
    -- `v2_num/v2_den 0`), against `gens ++ [Fu2, Fu3]`.
    (hd1_V0 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v1_den 0)))
    [hV0_1_nontriv : Nontrivial
      ((Rdec p ⧸ Ideal.ofList (gens ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
          (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
          Set (Rdec p ⧸ Ideal.ofList (gens ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))]
    (hfinRes_V0 : Module.Finite (F p) ((Rdec p ⧸ Ideal.ofList (gens ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v2_num 0) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v1_den 0) -
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v1_num 0) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) (d.v2_den 0)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])))))
    (hnontrivB_V0 : Nontrivial
      (((Rdec p ⧸ Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
            (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
            Set (Rdec p ⧸ Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])))) ⧸
        Ideal.span ({((Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
              (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))).comp
            (Ideal.Quotient.mk (Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))
            (linearElimGen p (d.v2_num 0) (d.v2_den 0) V0)} :
          Set (((Rdec p ⧸ Ideal.ofList (gens ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))
              (linearElimGen p (d.v1_num 0) (d.v1_den 0) V0)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]))))))))
    -- `V1` stage (pivot of `Fv2,Fv3`, i.e. `v1_num/v1_den 1`,
    -- `v2_num/v2_den 1`), against `gens ++ [Fu2,Fu3,Fv0,Fv1]`.
    (hd1_V1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
       linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_den 1)))
    [hV1_1_nontriv : Nontrivial
      ((Rdec p ⧸ Ideal.ofList (gens ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
          (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
          Set (Rdec p ⧸ Ideal.ofList (gens ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
             linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
             linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))))]
    (hfinRes_V1 : Module.Finite (F p) ((Rdec p ⧸ Ideal.ofList (gens ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v2_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_den 1) -
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v2_den 1)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])))))
    (hnontrivB_V1 : Nontrivial
      (((Rdec p ⧸ Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
             linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
             linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
            (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
            Set (Rdec p ⧸ Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
               linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])))) ⧸
        Ideal.span ({((Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
               linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
              (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
                 linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
                 linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))))).comp
            (Ideal.Quotient.mk (Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
               linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))))
            (linearElimGen p (d.v2_num 1) (d.v2_den 1) V1)} :
          Set (((Rdec p ⧸ Ideal.ofList (gens ++
            [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
             linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
             linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
             linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
              [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
               linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
               linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
               linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]))
              (linearElimGen p (d.v1_num 1) (d.v1_den 1) V1)} :
              Set (Rdec p ⧸ Ideal.ofList (gens ++
                [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
                 linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
                 linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
                 linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])))))))) :
    ∃ B : ℕ,
      Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1])) ∧
      Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1])) ∧
      Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++
        [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
         linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
         linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
         linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1])) ≤ B := by
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList gens) := ‹_›
  -- Stage `U1`.
  obtain ⟨hfinU1, hnontrivU1, hboundU1⟩ :=
    finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2 p gens
      U1 (d.u1_num 1) (d.u1_den 1) (d.u2_num 1) (d.u2_den 1)
      hd1_U1 hfinRes_U1 hnontrivB_U1
  haveI : Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) := hnontrivU1
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) :=
    commRing_strongRankCondition _
  haveI : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])) := hfinU1
  -- Stage `V0`, against the `U1`-extended prefix.
  obtain ⟨hfinV0, hnontrivV0, hboundV0⟩ :=
    finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2 p
      (gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1])
      V0 (d.v1_num 0) (d.v1_den 0) (d.v2_num 0) (d.v2_den 0)
      hd1_V0 hfinRes_V0 hnontrivB_V0
  haveI : Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
       linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) := by
    have heq : gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0] =
      (gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]) ++
        [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0] := by
      simp [List.append_assoc]
    rw [heq]
    exact hnontrivV0
  haveI : StrongRankCondition (Rdec p ⧸ Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
       linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) :=
    commRing_strongRankCondition _
  haveI : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
       linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) := by
    have heq : gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0] =
      (gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1]) ++
        [linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
         linearElimGen p (d.v2_num 0) (d.v2_den 0) V0] := by
      simp [List.append_assoc]
    rw [heq]
    exact hfinV0
  -- Stage `V1`, against the `U1,V0`-extended prefix.
  obtain ⟨hfinV1, hnontrivV1, hboundV1⟩ :=
    finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2 p
      (gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])
      V1 (d.v1_num 1) (d.v1_den 1) (d.v2_num 1) (d.v2_den 1)
      hd1_V1 hfinRes_V1 hnontrivB_V1
  refine ⟨Module.finrank (F p)
    ((Rdec p ⧸ Ideal.ofList (gens ++
      [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
       linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
       linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
       linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v2_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_den 1) -
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v1_num 1) *
        Ideal.Quotient.mk (Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])) (d.v2_den 1)} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++
          [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
           linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
           linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
           linearElimGen p (d.v2_num 0) (d.v2_den 0) V0])))),
    ?_, ?_, ?_⟩
  · have heq : gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
        linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
        linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] =
      (gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]) ++
        [linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] := by
      simp [List.append_assoc]
    rw [heq]
    exact hfinV1
  · have heq : gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
        linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
        linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] =
      (gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]) ++
        [linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] := by
      simp [List.append_assoc]
    rw [heq]
    exact hnontrivV1
  · have heq : gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0,
        linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
        linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] =
      (gens ++ [linearElimGen p (d.u1_num 1) (d.u1_den 1) U1,
        linearElimGen p (d.u2_num 1) (d.u2_den 1) U1,
        linearElimGen p (d.v1_num 0) (d.v1_den 0) V0,
        linearElimGen p (d.v2_num 0) (d.v2_den 0) V0]) ++
        [linearElimGen p (d.v1_num 1) (d.v1_den 1) V1,
         linearElimGen p (d.v2_num 1) (d.v2_den 1) V1] := by
      simp [List.append_assoc]
    rw [heq]
    exact hboundV1

end DecoupledSystem
end Genus2Lean
