import Mathlib
import Genus2Lean.ZeroD.FinrankLeOfMonicAnnihilator

/-!
# Core lemma, finiteness-exporting version: unblocking the Assembly induction

`ROADMAP-monic-annihilator-degree-uniform.md`'s "Open questions" section
(the "NEW, discovered while scoping Assembly" entry) flags a real gap in
the naive Assembly plan: every wired per-stage lemma
(`finrank_le_curveRelation_ofList_cons`, `finrank_le_linearElim_ofList_cons`)
takes `[Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)]` as an EXPLICIT
hypothesis on the PREFIX ring `A`. A naive induction along the 12-stage
peel chain would need this to hold at every intermediate prefix, starting
from `gens = []`, i.e. `A = Rdec p` itself — but `Rdec p = MvPolynomial
Idx (F p)` is a polynomial ring, so `Module.Finite (F p) (Rdec p)` is
simply false, and the existing regularity-based finiteness fact
(`RegularSequenceFiniteQuotient.lean`'s `Module.Finite.quotient_of_isRegular_
of_length_eq_card`) only concludes finiteness at the FULL 12-generator
length, not at any proper prefix. So the induction's base case fails
outright if `Module.Finite` is treated as an input the induction has to
independently discharge at each step.

**The fix, per that roadmap section's own "Route (a)" diagnosis, checked
directly against `FinrankLeOfMonicAnnihilator.lean`'s actual proof term
(not assumed from the roadmap's prose) and confirmed correct**:
`finrank_le_of_monic_annihilator`'s own proof already constructs
`Module.Finite k (AdjoinRoot G)` internally, via `Module.Finite.trans A
(AdjoinRoot G)` — i.e. it derives finiteness of the EXTENDED algebra from
finiteness of the BASE algebra, not the other way around. So finiteness
is not something each stage needs supplied on its prefix from outside;
it is something each stage's own proof already produces for its extended
ring, and the induction should THREAD it forward as an output, starting
from the genuinely-true base case `Module.Finite (F p) (F p)` (any field
is finite-dimensional, rank 1, over itself), rather than trying to
independently re-derive `Module.Finite` at every intermediate prefix via
some other route.

**What this file adds, beyond `FinrankLeOfMonicAnnihilator.lean`**: a
restatement of the core lemma (`finrank_le_of_monic_annihilator_of_finite`)
that takes exactly the same hypotheses MINUS `[Module.Finite k A]` as a
typeclass assumption (still needed, but now taken as an explicit argument
so it can be threaded through an explicit induction rather than resolved
by instance search at each stage — instance search cannot see "the
previous stage's `B`", it can only see whatever's in the ambient
typeclass context) and CONCLUDES `Module.Finite k B` alongside the
`finrank` bound, by literally reusing the existing proof's internal
`Module.Finite.trans` step. A second wrapper, `nontrivial_of_span_ne_top`,
supplies the companion `Nontrivial B` fact whenever `B := A ⧸ Ideal.span
{g}` for a non-unit `g` (the shape both per-stage wiring files use) — the
same `IsUnit`/leading-coefficient-unit hypothesis each stage already
needs for its OWN `finrank` argument (a resultant/leading coefficient
being a unit is exactly the non-unit-ness failing, so this is free once
that hypothesis is in hand, not a fresh assumption).

**What this file does NOT do**: it does not touch `Rdec p`, `genList`,
or any project-specific peel-chain content — like
`FinrankLeOfMonicAnnihilator.lean` itself, this is generic algebra, kept
separate so the true Assembly file (still to come) only has to combine
already-proved generic facts with `genList`'s literal 12 generators. -/

namespace Genus2Lean

open Polynomial

variable {k A B : Type*} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B] [StrongRankCondition A]

/-- **The core lemma, restated with `Module.Finite k A` as an explicit
argument and `Module.Finite k B` exported as part of the conclusion.**
Identical hypotheses and proof content to `finrank_le_of_monic_annihilator`
— this is a thin repackaging, not new mathematical content — except that
`[Module.Finite k A]` is taken as a hypothesis `hfinA` rather than a
typeclass assumption (so an explicit induction can supply "the previous
stage's own conclusion" rather than relying on instance search to find
it), and the internally-constructed `Module.Finite k B` fact — already
present in `finrank_le_of_monic_annihilator`'s proof as an intermediate
step for `AdjoinRoot G`, transported to `B` via the surjection `φ` — is
surfaced as an explicit second conclusion, so the NEXT stage's induction
step can consume it in turn. -/
theorem finrank_le_of_monic_annihilator_of_finite
    (hfinA : Module.Finite k A)
    (G : Polynomial A) (hG : G.Monic) (t : B)
    (ht : (Polynomial.aeval t) G = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.Finite k B ∧ Module.finrank k B ≤ G.natDegree * Module.finrank k A := by
  haveI := hfinA
  set d := G.natDegree with hd_def
  have ht' : Polynomial.eval₂ ((Algebra.ofId A B : A →ₐ[A] B) : A →+* B) t G = 0 := by
    simpa [Polynomial.aeval_def] using ht
  set φ : AdjoinRoot G →ₐ[A] B := AdjoinRoot.liftAlgHom G (Algebra.ofId A B) t ht' with hφ_def
  have hφ_root : φ (AdjoinRoot.root G) = t :=
    AdjoinRoot.liftAlgHom_root G (Algebra.ofId A B) t ht'
  have hφ_surj : Function.Surjective φ := by
    have hrange : Algebra.adjoin A {t} ≤ φ.range := by
      rw [Algebra.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨AdjoinRoot.root G, hφ_root⟩
    rw [hgen] at hrange
    intro b
    have hb : b ∈ (⊤ : Subalgebra A B) := trivial
    have := hrange hb
    simpa [AlgHom.mem_range] using this
  haveI hfreeA : Module.Free A (AdjoinRoot G) := hG.free_adjoinRoot
  haveI hfinAdjoinA : Module.Finite A (AdjoinRoot G) := hG.finite_adjoinRoot
  have hdimA : Module.finrank A (AdjoinRoot G) = d := (AdjoinRoot.powerBasis' hG).finrank
  haveI : IsScalarTower k A (AdjoinRoot G) := inferInstance
  haveI hfink : Module.Finite k (AdjoinRoot G) := Module.Finite.trans A (AdjoinRoot G)
  have hφ_lin_surj : Function.Surjective (φ.toLinearMap.restrictScalars k) := hφ_surj
  -- **The new content versus `finrank_le_of_monic_annihilator`**: a
  -- surjective `k`-linear map out of a finite `k`-module has finite
  -- image, i.e. `B` (the whole codomain, by surjectivity) is itself a
  -- finite `k`-module — `Module.Finite.of_surjective`, applied to
  -- `φ.toLinearMap.restrictScalars k`.
  haveI hfinB : Module.Finite k B :=
    Module.Finite.of_surjective (φ.toLinearMap.restrictScalars k) hφ_lin_surj
  have hle : Module.finrank k B ≤ Module.finrank k (AdjoinRoot G) :=
    LinearMap.finrank_le_finrank_of_surjective hφ_lin_surj
  have htower : Module.finrank k (AdjoinRoot G) =
      Module.finrank k A * Module.finrank A (AdjoinRoot G) :=
    (Module.finrank_mul_finrank k A (AdjoinRoot G)).symm
  rw [hdimA] at htower
  refine ⟨hfinB, ?_⟩
  calc Module.finrank k B ≤ Module.finrank k (AdjoinRoot G) := hle
    _ = Module.finrank k A * d := htower
    _ = d * Module.finrank k A := Nat.mul_comm _ _

/-- **The companion `Nontrivial` fact.** Whenever `B` is presented as `A ⧸
Ideal.span {g}` for some `g : A` that is NOT a unit, `B` is nontrivial —
i.e. the quotient is by a proper ideal. This is exactly the shape both
per-stage wiring files (`CurveRelationStageWiring.lean`,
`LinearElimStageWiring.lean`) build `B` in, and the non-unit-ness needed
here is the FAILURE of the same `IsUnit`/leading-coefficient condition
each stage's own `finrank` argument is stated in terms of (a curve
relation `X² − C f`'s "leading coefficient" is the literal `1`, always a
unit, so `curveRelationGen` is never itself a unit in `A` for a
degree-2-shape stage; a linear-elimination generator `c − X·d` is a unit
in `A` only in a genuinely degenerate case having nothing to do with
`IsUnit d`, so the two conditions don't collide). -/
theorem nontrivial_of_span_ne_top {g : A} (hg : ¬ IsUnit g) :
    Nontrivial (A ⧸ Ideal.span ({g} : Set A)) :=
  Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top hg)

end Genus2Lean
