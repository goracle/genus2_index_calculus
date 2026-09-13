import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemRegular
import Genus2Lean.ZeroD.IdxEquivFin
import Genus2Lean.ZeroD.IdealOfListPerm
import Genus2Lean.ZeroD.CurveRelationStageWiring
import Genus2Lean.ZeroD.LinearElimStageWiring

/-!
# Item (d), steps 1–2: reordering `genList` to `idxEquivFin`'s triangular
# peel order

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Update, later pass" section
(the `RenameEquivOfListFinrankTransport.lean` entry) names four remaining
steps for item (d); this file supplies the first two. It does NOT yet touch
`finrank_le_finSucc_peel_chain`'s `hstep` (step 3, the genuinely open
per-stage content) or the final assembly (step 4) — those are separate,
later files.

**Why a reordering is needed at all.** `genList`'s literal stated order is
`FuList ++ FvList ++ [curveA1,curveA2,curveB1,curveB2]` — matching
generators first, curve relations last. `idxEquivFin`'s peel order is the
opposite at the top level: curve relations (interleaved with their own
sample variables) come FIRST, because `FuList`/`FvList`'s coefficients
(via `theData`'s `u1_indep`/`u2_indep`/`v1_indep`/`v2_indep` fields,
`DecoupledSystemRegular.lean` §4bis) are only guaranteed to avoid
`U0,U1,V0,V1` — they are NOT guaranteed constant in `wa1,wa2,wb1,wb2,
a1,a2,b1,b2`, so peeling a matching generator before its curve variables
are eliminated would leave a non-constant "leading coefficient" at exactly
the step `finSuccEquiv`'s monic-annihilator machinery needs a genuine
constant. This file makes the reordering precise and proves it is
ideal-preserving via `Ideal.ofList_perm`.

**What "triangular order" means here, concretely.** `genListTriangular`
lists the same twelve elements as `genList`, in the order
`[curveA1, curveA2, curveB1, curveB2] ++ FuList ++ FvList` — i.e. the four
curve relations moved to the front, `Fu`/`Fv` kept in their own existing
relative order after. This is coarser than `idxEquivFin`'s full
per-*variable* interleaving (which additionally threads each `wa`/`wb`
peel together with its own sample variable one at a time, and further
splits the eight matching generators across `U0,U1,V0,V1` individually) —
sharpening `genListTriangular` down to that full one-variable-at-a-time
shape is exactly step 2's remaining half, deferred to the file that
actually builds `hstep` (step 3), since only there does the finer
interleaving start to matter (curve relations alone are already
`Idx`-independent of one another and of `Fu`/`Fv`, so this coarser split
is enough to prove the permutation and get curves-before-matching-
generators, without yet committing to the exact 12-step
one-variable-at-a-time sequence step 3 will need). -/

namespace Genus2Lean
namespace DecoupledSystem

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

open TheDataDerivation

/-- **`genList`, reordered with the four curve relations first.** Same
twelve elements as `genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB`,
curve relations moved to the front. -/
noncomputable def genListTriangular (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) : List (Rdec p) :=
  [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
   curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] ++
    FuList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB ++
    FvList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB

/-- **`genListTriangular` is a permutation of `genList`.** Both are built
from the same three blocks (`FuList`, `FvList`, the four curve relations,
each block's own internal order untouched); only the block-level order
changes (`Fu,Fv,curve ↦ curve,Fu,Fv`), so this follows from
`List.Perm.append`-style block shuffling — proved here via generic
`List.Perm` lemmas about `++`, not by unfolding `FuList`/`FvList`/the
curve list's own definitions, so this proof is insensitive to whatever
those definitions' internals are. -/
theorem genListTriangular_perm_genList (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).Perm
      (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) := by
  unfold genListTriangular genList
  set Fu := FuList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB with hFu_def
  set Fv := FvList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB with hFv_def
  set Cs := [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
    curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4] with hCs_def
  -- Goal: `(Cs ++ Fu ++ Fv).Perm (Fu ++ Fv ++ Cs)`, i.e. (both sides
  -- left-associated by `++`'s notation) `((Cs ++ Fu) ++ Fv).Perm
  -- ((Fu ++ Fv) ++ Cs)`. Reassociate the LHS via `List.append_assoc` to
  -- `Cs ++ (Fu ++ Fv)`, then apply `List.perm_append_comm` at
  -- `l₁ := Cs`, `l₂ := Fu ++ Fv`.
  rw [List.append_assoc]
  exact List.perm_append_comm

/-- **Corollary**: the two one-step quotients are the SAME ring, so any
`Module.finrank`/`Module.Finite`/`Nontrivial` fact proved for one transfers
to the other for free, via `Ideal.quotient_ofList_perm_eq`
(`IdealOfListPerm.lean`) — the tool `genList_finrank_le`'s eventual proof
will use to go from a bound proved against `genListTriangular` back to
`genList`'s own literal stated order (this is step 4 of item (d)'s
remaining plan; this corollary is the piece that makes that step a
one-line `rw` once the triangular-order bound exists). -/
theorem quot_genListTriangular_eq_quot_genList (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    (Rdec p ⧸ Ideal.ofList (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) =
      (Rdec p ⧸ Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) :=
  Ideal.quotient_ofList_perm_eq
    (genListTriangular_perm_genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)

/-- **Sanity check**: `genListTriangular` still has all twelve generators
(no accidental drop/duplicate introduced by the reordering) — cheap guard
in the same spirit as `genList`'s own existing length check
(`DecoupledSystemRegular.lean` §5). -/
theorem genListTriangular_length (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).length =
      Fintype.card Idx :=
  (genListTriangular_perm_genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).length_eq.trans
    (genList_length p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)

end DecoupledSystem
end Genus2Lean
