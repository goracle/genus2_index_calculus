import Mathlib
import Genus2Lean.ZeroD.GenListFinrankFourStageAssembly
import Genus2Lean.ZeroD.GenListTriangularReorder

/-!
# Transporting the four-stage `finrank` bound onto `genList`'s literal order

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Corrections, this pass"
section (points 3–4) flags two separate gaps left after
`GenListFinrankFourStageAssembly.lean`:

1. **The mechanical gap, closed here.** That file's conclusion
   (`genList_triangular_finrank_le_of_base_fourStage`) is stated over
   `genListTriangular`'s REORDERED generator list (curves first), not
   `genList`'s own literal stated order (`FuList ++ FvList ++ curves`) —
   exactly the step that file's own docstring names as "not attempted
   here," and `GenListFinrankResultantAssembly.lean`'s docstring calls
   "a mechanical last step left for whoever calls this file against
   `genList_finrank_le` itself." Closed below via ONE application of
   `quot_genListTriangular_eq_quot_genList` (`GenListTriangularReorder
   .lean`).
2. **The genuinely open gap, NOT closed here, stated as a hypothesis
   rather than assumed away.** The chain has never actually been
   instantiated at a real starting `gens` — no file anywhere proves
   `Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)` for any `gens` this
   induction could legitimately start from. `gens := []` is false
   (`Rdec p ⧸ Ideal.ofList [] ≃ Rdec p`, a 12-variable free polynomial
   ring), and no strict prefix of `genListTriangular` is finite either
   (`a1,a2,b1,b2` are never a pivot alone, only jointly via the
   shared-pivot resultants). See the roadmap's "Corrections" point 4 for
   the full diagnosis and the likely route to closing it (revisiting
   route 2's abandoned `Option`/`Fin`-split base case, NOT the peeling
   architecture, which route 3 already handles correctly).

**Design choice: this file takes `genList_triangular_finrank_le_of_base_
fourStage`'s CONCLUSION as a hypothesis, not its ~200-line hypothesis
list.** That theorem's signature (curve-chain side conditions, `U0`'s
resultant data, `U1,V0,V1`'s per-stage data, all stated against a
literal, deeply-nested `gens`-dependent term) is long enough that
re-typing it by hand here risks a transcription mismatch invisible until
Claire's REPL catches it — the exact failure mode this project's
`description`-first tool-call convention and "read the actual file, not
a summary" discipline both exist to avoid. Taking the conclusion as an
opaque `∃ B, ...`-shaped hypothesis (`hchain` below) means any caller who
has actually produced that fact — by whatever route, including a future
fix to gap 2 above — can invoke this lemma with no risk of the two
files' signatures silently drifting apart. -/

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

/-- **The missing base case, named rather than assumed silently or
smuggled in as `gens := []`.** `Module.Finite (F p) (Rdec p ⧸
Ideal.ofList gens)` for SOME `gens : List (Rdec p)` genuinely finite over
`F p` — deliberately not fixed to any specific list, since no such list
is currently known anywhere in this codebase (confirmed: no file
establishes `Module.Finite` for any `Ideal.ofList gens` other than the
FULL `genList`/`genListTriangular`, which is not itself usable as a
*starting* prefix for this induction). A future proof of this `Prop`
(module docstring, gap 2) is what would let
`genList_triangular_finrank_le_of_base_fourStage` actually be invoked for
the first time anywhere in this project — as of this pass it has zero
call sites, generic-only. -/
def RouteThreeHasBaseCase (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ gens : List (Rdec p), Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens) ∧
    Nontrivial (Rdec p ⧸ Ideal.ofList gens) ∧
    StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)

/-- **Gap 1, closed: transport a `genListTriangular`-order `finrank`
bound onto `genList`'s own literal order.** Purely mechanical — the same
ring, one `rw` via `Ideal.ofList_perm` — with no dependence on how the
input bound `hchain` was itself established. This is the identity both
`GenListFinrankResultantAssembly.lean`'s and
`GenListFinrankFourStageAssembly.lean`'s own docstrings point to and
neither file performs.

**Fixed this pass: `rw`s the IDEAL equality (`Ideal.ofList_perm`), not
the quotient-RING equality (`quot_genListTriangular_eq_quot_genList`).**
The first attempt at this lemma used the latter and failed with "motive
is not type correct" — `Module.finrank` carries its `AddCommMonoid`/
`Module` instances as implicit arguments derived from the quotient
ring's own type, so rewriting a bare `R ⧸ I₁ = R ⧸ I₂` equality of TYPES
underneath `Module.finrank` asks `rw` to abstract over a type that
appears inside its own instance arguments — exactly the dependent-motive
failure `rw`'s documentation warns about. Rewriting `Ideal.ofList
genListTriangular = Ideal.ofList genList` (an equality of IDEALS,
`Ideal.ofList_perm`, `IdealOfListPerm.lean`) instead changes only the
`Ideal.ofList _` ARGUMENT inside `Rdec p ⧸ _`, so the instances
(`Submodule.Quotient.addCommMonoid` etc.) are rebuilt by `congrArg`
through a genuine subterm rewrite rather than needing to be transported
across an opaque type equality — no dependent-motive issue. -/
theorem finrank_le_genList_of_finrank_le_genListTriangular
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    {B : ℕ}
    (hchain : Module.finrank (F p)
      (Rdec p ⧸ Ideal.ofList
        (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) ≤ B) :
    Module.finrank (F p)
      (Rdec p ⧸ Ideal.ofList
        (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) ≤ B := by
  rwa [← Ideal.ofList_perm
    (genListTriangular_perm_genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)]

/-- **Corollary, stated against `genList_finrank_le`'s own shape**
(`GenListFinrankAssembly.lean`) — packages the transport above together
with `RouteThreeHasBaseCase`'s still-open status, so this is the single
lemma a future pass should reach for once gap 2 is closed, rather than
re-deriving the `rw` above from scratch. Takes `hchain` exactly as
`finrank_le_genList_of_finrank_le_genListTriangular` does (an already-
established `genListTriangular`-order bound) — this corollary adds
NOTHING beyond restating that theorem's conclusion with `≤ 16` in place
of a generic `≤ B`, since route 3's own accounting (four curve stages at
`×2` each, `16` total, per `CurveRelationChainFinrank.lean`'s own
docstring) is exactly what `hchain`'s witness `B` is expected to equal
once `RouteThreeHasBaseCase`'s witness contributes a multiplier of `1`
(a finite FIELD extension contributes `finrank = 1` iff it is `F p`
itself — genuinely part of gap 2, not re-derived here). -/
theorem finrank_le_sixteen_genList_of_finrank_le_sixteen_genListTriangular
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hchain : Module.finrank (F p)
      (Rdec p ⧸ Ideal.ofList
        (genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) ≤ 16) :
    Module.finrank (F p)
      (Rdec p ⧸ Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)) ≤ 16 :=
  finrank_le_genList_of_finrank_le_genListTriangular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA
    hgcdB hchain

end DecoupledSystem
end Genus2Lean
