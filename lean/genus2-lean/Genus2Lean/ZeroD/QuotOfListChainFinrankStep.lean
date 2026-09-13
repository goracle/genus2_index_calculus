import Mathlib
import Genus2Lean.ZeroD.QuotOfListChain

/-!
# Assembly, part 2: one `finrank`-chaining step over `Ideal.ofList` prefixes

Item 5 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, the
second Assembly file flagged as "not yet started" in that roadmap's
Progress section and in `QuotOfListChain.lean`'s own docstring. Bridges
`quotOfListCons_ringEquiv`'s ring isomorphism to an actual `finrank`
inequality on the literal one-step quotients `Rdec p ⧸ Ideal.ofList gens`
produced by extending a generator list one element at a time — the
missing link needed before `FinrankLeOfMonicAnnihilator.lean` /
`LinearElimDegreeBound.lean` / `LinearElimDegreeBoundExt.lean` /
`CurveRelationsDegreeBound.lean`'s four per-stage facts can be composed
twelve times via `Module.finrank_mul_finrank` into one bound on
`Rdec p ⧸ Ideal.ofList (genList ...)`.

**Scope of this file**: the GENERIC one-stage step, over any `CommRing R`
with a base field `k` and `Algebra k R` — not yet specialized to
`Rdec p`/`F p`/`genList`'s literal 12-element list. That final
specialization (plugging in `genList`'s actual `Fu0,...,Fv3,curveA1,...`
generators, the concrete `t := X <peeled var>` witness at each stage, and
discharging each stage's `ht`/`hgen`/unit hypotheses against `theData`'s
real formulas) is later work, per the roadmap's own repeated split
between "generic reusable step" (this file, and the four per-stage files
before it) and "wiring to the literal peel chain" (still ahead). Doing
the generic step first, once, means the eventual 12-fold specialization
is twelve applications of one already-proved lemma, not twelve fresh
proofs.

**Why a generic step, not a generic "chain of n steps" theorem**:
`List.foldr`/`List.foldl`-style induction over the whole `genList` at
once would need a SINGLE uniform per-stage hypothesis shape, but the
roadmap's own stage table has two structurally different shapes (linear
`c − X·d` for stages 0–7, already-monic `X² − C f` for stages 8–11) with
different per-stage side-conditions (`IsUnit d` vs. none) — forcing a
common shape onto both would be more awkward than proving one step at a
time and letting the eventual final-Assembly file apply this lemma (or
one of the four per-stage facts directly) 12 times in a row, once per
generator, matching how `regularSeq_of_peel_chain`'s own 12-way
`isRegular_cons_iff'` case split already works for the analogous
regularity chain -- not a new pattern for this project.

**Base-field algebra structure through the chain**: each one-step
quotient `R ⧸ Ideal.ofList gens` (`R` itself a `k`-algebra) inherits
`Algebra k (R ⧸ Ideal.ofList gens)` via `RingHom.toAlgebra` composed with
`Ideal.Quotient.mk` — the standard "quotient of a `k`-algebra by an ideal
is again a `k`-algebra" instance, needed so `Module.finrank k _` even
typechecks at every stage, and so `IsScalarTower k (R ⧸ Ideal.ofList
gens) (R ⧸ Ideal.ofList (gens ++ [g]))` holds (via
`quotOfListCons_ringEquiv`'s isomorphism transported back along
`Ideal.Quotient.mk`, matching `algebraMap k _` on the nose since both
sides ultimately factor through `algebraMap k R`). -/

namespace Genus2Lean

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- **The one-stage `finrank` bound, generic form.** Given the per-stage
`finrank` fact `hstep` for an ABSTRACT algebra pair `(A, B)` with
generator `t` (exactly the shape `finrank_le_of_monic_annihilator` /
`finrank_le_of_linear_elim` / `finrank_le_of_curve_relation` each
conclude, after their own hypotheses are discharged), transport it across
`quotOfListCons_ringEquiv` to the literal one-step quotients `R ⧸
Ideal.ofList gens` and `R ⧸ Ideal.ofList (gens ++ [g])`.

**Why this is stated with `hstep` as a bare hypothesis rather than
re-deriving it here**: this file's job is the transport step (turning an
abstract-`B` bound into a literal-one-step-quotient bound), not
re-proving any of the four already-closed per-stage facts — callers
apply THIS lemma with `hstep := finrank_le_of_linear_elim ...` (or
whichever per-stage fact fits that generator's shape) already fully
instantiated, matching the project's existing split between "single-stage
fact" and "chaining" files. -/
theorem finrank_le_ofList_cons
    (gens : List R) (g : R) (d : ℕ)
    (hstep : Module.finrank k
        ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) ≤
      d * Module.finrank k (R ⧸ Ideal.ofList gens)) :
    Module.finrank k (R ⧸ Ideal.ofList (gens ++ [g])) ≤
      d * Module.finrank k (R ⧸ Ideal.ofList gens) := by
  -- `quotOfListCons_ringEquiv gens g` is a `RingEquiv`, not yet known to
  -- respect the `k`-algebra structure on the nose — but `finrank` only
  -- needs a `k`-LINEAR equivalence, and any `RingEquiv` between two
  -- `k`-algebras that agrees with `algebraMap k _` on both sides upgrades
  -- to a `k`-algebra isomorphism (`AlgEquiv.ofRingEquiv`), which in turn
  -- gives a `k`-linear equivalence (`AlgEquiv.toLinearEquiv`) preserving
  -- `finrank` (`LinearEquiv.finrank_eq`). The `algebraMap`-agreement
  -- itself reduces to `quotOfListCons_ringEquiv_apply_mk_mk` applied at
  -- `x := <the image of an arbitrary k-element under algebraMap k R>`,
  -- since both quotients' `algebraMap k _` factor through `algebraMap k R`
  -- followed by the respective `Ideal.Quotient.mk`.
  have halg : ∀ c : k, quotOfListCons_ringEquiv gens g
      (algebraMap k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) c) =
      algebraMap k (R ⧸ Ideal.ofList (gens ++ [g])) c := by
    intro c
    -- Both sides' `algebraMap k _` unfold to `Ideal.Quotient.mk _
    -- (algebraMap k R c)` — the two-step side via `IsScalarTower.
    -- algebraMap_apply k R (R ⧸ Ideal.ofList gens)` then again one level
    -- up, the one-step side directly — landing exactly on
    -- `quotOfListCons_ringEquiv_apply_mk_mk gens g (algebraMap k R c)`.
    have hlhs : (algebraMap k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens)))) c =
        Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens)))
          (Ideal.Quotient.mk (Ideal.ofList gens) (algebraMap k R c)) := by
      -- Outer tower first (`k → R ⧸ gens → two-step quotient`): the goal's
      -- LHS is literally `algebraMap k (two-step)`, which this pattern
      -- matches; the inner tower's `algebraMap k (R ⧸ gens)` only becomes
      -- a literal subterm of the goal AFTER this rewrite exposes it.
      rw [IsScalarTower.algebraMap_apply k (R ⧸ Ideal.ofList gens)
        ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens)))]
      rw [IsScalarTower.algebraMap_apply k R (R ⧸ Ideal.ofList gens)]
      rfl
    have hrhs : (algebraMap k (R ⧸ Ideal.ofList (gens ++ [g]))) c =
        Ideal.Quotient.mk (Ideal.ofList (gens ++ [g])) (algebraMap k R c) := by
      rw [IsScalarTower.algebraMap_apply k R (R ⧸ Ideal.ofList (gens ++ [g]))]
      rfl
    rw [hlhs, hrhs]
    exact quotOfListCons_ringEquiv_apply_mk_mk gens g (algebraMap k R c)
  -- Package `halg` into the `AlgEquiv` and read off the `finrank` equality.
  set e : ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
      ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) ≃ₐ[k]
      (R ⧸ Ideal.ofList (gens ++ [g])) :=
    AlgEquiv.ofRingEquiv (f := quotOfListCons_ringEquiv gens g) halg with he_def
  have hfinrank_eq : Module.finrank k (R ⧸ Ideal.ofList (gens ++ [g])) =
      Module.finrank k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) :=
    (LinearEquiv.finrank_eq e.symm.toLinearEquiv)
  rw [hfinrank_eq]
  exact hstep

end Genus2Lean
