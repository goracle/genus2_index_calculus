import Mathlib
import Genus2Lean.ZeroD.FinrankLeOfMonicAnnihilatorFinite
import Genus2Lean.ZeroD.QuotOfListChain
import Genus2Lean.ZeroD.QuotOfListChainAdjoinTop
import Genus2Lean.ZeroD.CurveRelationStageWiring
import Genus2Lean.ZeroD.LinearElimStageWiring
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# Finiteness-exporting per-stage wiring, on the literal `Ideal.ofList` chain

Continuation of `FinrankLeOfMonicAnnihilatorFinite.lean`'s fix, specialized
to the literal `Rdec p ⧸ Ideal.ofList gens` one-step quotients
`CurveRelationStageWiring.lean`/`LinearElimStageWiring.lean` already wire
the plain `finrank` bound against. Those two files' own theorems
(`finrank_le_curveRelation_ofList_cons`, `finrank_le_linearElim_ofList_cons`)
still take `[Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)]` etc. as
typeclass hypotheses on the PREFIX — fine for a single application, but
exactly the shape that makes a naive 12-step induction fail its base
case, per `ROADMAP-monic-annihilator-degree-uniform.md`'s "NEW, discovered
while scoping Assembly" open question.

**What this file adds**: a second version of each per-stage wiring
theorem, concluding `Module.Finite (F p) (...)` and `Nontrivial (...)` on
the EXTENDED one-step quotient `Rdec p ⧸ Ideal.ofList (gens ++ [g])`
alongside the same `finrank` bound — so the not-yet-written Assembly file
can run an explicit induction that starts from the genuinely-true base
case (`Module.Finite (F p) (F p)`, trivial, since any field is
finite-dimensional of rank 1 over itself -- the actual base case
Assembly needs, applied before the first of the 12 stages) and, at each
of the 12 steps, feeds the PREVIOUS step's just-
concluded `Module.Finite`/`Nontrivial` facts into the hypotheses these
wiring theorems already ask for, while producing the SAME facts for the
next step in turn — never needing to independently re-derive finiteness
at an intermediate prefix via the (inapplicable, sub-full-length)
regular-sequence route.

**Proof strategy, both theorems**: identical to the existing
`finrank_le_curveRelation_ofList_cons`/`finrank_le_linearElim_ofList_cons`
proofs up through constructing `ht`/`hgen`, but call
`finrank_le_of_monic_annihilator_of_finite` (not
`finrank_le_of_monic_annihilator`) to also obtain `Module.Finite (F p) B`
on the two-step ring `B`, obtain `Nontrivial B` from
`nontrivial_of_span_ne_top` (needing the generator's image to be a
non-unit — free for the curve-relation shape since its "leading
coefficient" is a literal `1`'s negation pattern... see the per-theorem
docstring below for the precise non-unit argument in each case), then
transport both facts across `quotOfListCons_ringEquiv` (an `AlgEquiv`,
so it preserves `Module.Finite`/`Nontrivial` in either direction) onto
the literal one-step quotient the next stage's induction step needs. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **Transport `Module.Finite`/`Nontrivial` across `quotOfListCons_ringEquiv`.**
Generic packaging, no peel-chain-specific content: given the two facts on
the abstract two-step ring `(R ⧸ Ideal.ofList gens) ⧸ Ideal.span {mk g}`,
produce them on the literal one-step ring `R ⧸ Ideal.ofList (gens ++ [g])`
via the ring isomorphism `quotOfListCons_ringEquiv`, upgraded to a
`k`-algebra isomorphism `e'` exactly the way `QuotOfListChainFinrankStep.
lean`'s `finrank_le_ofList_cons` already does (via `AlgEquiv.ofRingEquiv`
plus the same `algebraMap`-agreement check, `halg` below, copied from
that file's own proof since both need exactly this fact). `Module.Finite`
transports along `e'.toLinearMap` via `Module.Finite.of_surjective` (the
same lemma the core finiteness-exporting theorem already uses); `Nontrivial`
transports along `e'.symm`'s surjectivity via `Function.Surjective.nontrivial`
-- both confirmed-present Mathlib4 names, no unverified API guessed. -/
theorem finite_and_nontrivial_ofList_cons_of_two_step
    {R k : Type*} [CommRing R] [Field k] [Algebra k R]
    (gens : List R) (g : R)
    (hfin : Module.Finite k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))))
    (hnontriv : Nontrivial ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens)))) :
    Module.Finite k (R ⧸ Ideal.ofList (gens ++ [g])) ∧
      Nontrivial (R ⧸ Ideal.ofList (gens ++ [g])) ∧
      Module.finrank k (R ⧸ Ideal.ofList (gens ++ [g])) =
        Module.finrank k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) := by
  set e := quotOfListCons_ringEquiv gens g
  -- `Module.Finite` transports along a surjective (in particular
  -- bijective) semilinear map out of a finite module -- `e.toRingEquiv`
  -- as a `RingHom` is a `k`-algebra map once composed with `algebraMap`,
  -- but the cheapest route is via `e.toAddEquiv`/`e`'s underlying
  -- additive-group isomorphism plus `Module.Finite.equiv`-style transport
  -- through the SAME base ring `k`: since `e` is a ring isomorphism
  -- fixing the image of `algebraMap k _` (the two sides literally share
  -- `algebraMap k R` composed with the respective quotient maps -- this
  -- is exactly `quotOfListCons_ringEquiv_apply_mk_mk`'s content, so `e`
  -- IS `k`-linear even though it is packaged as a bare `RingEquiv`), a
  -- `LinearEquiv` restricting `e` along `k` transports both facts at
  -- once. Package that `k`-linear structure once, here, rather than
  -- inside each per-stage caller.
  have halg : ∀ c : k, e (algebraMap k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
      ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) c) =
      algebraMap k (R ⧸ Ideal.ofList (gens ++ [g])) c := by
    intro c
    have hlhs : (algebraMap k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens)))) c =
        Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens)))
          (Ideal.Quotient.mk (Ideal.ofList gens) (algebraMap k R c)) := by
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
  set e' : ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
      ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) ≃ₐ[k]
      (R ⧸ Ideal.ofList (gens ++ [g])) := AlgEquiv.ofRingEquiv (f := e) halg
  haveI := hfin
  haveI := hnontriv
  -- `Module.Finite` transports along `e'.toLinearMap`, a surjective (in
  -- fact bijective) `k`-linear map out of the already-finite source —
  -- the SAME `Module.Finite.of_surjective` route already used inside
  -- `finrank_le_of_monic_annihilator_of_finite`, applied here to `e'`
  -- instead of the lift `φ`.
  have hfinExt : Module.Finite k (R ⧸ Ideal.ofList (gens ++ [g])) :=
    Module.Finite.of_surjective e'.toLinearMap e'.surjective
  -- `Function.Surjective.nontrivial {f : α → β} (hf : Surjective f)
  -- [Nontrivial β] : Nontrivial α` — i.e. it PULLS BACK nontriviality
  -- from the CODOMAIN to the DOMAIN along a surjection. To conclude
  -- `Nontrivial target` from the already-known `Nontrivial (two-step
  -- ring)`, the surjection needed is `target → (two-step ring)`, i.e.
  -- `e'.symm` (NOT `e'`, which runs the wrong way for this lemma).
  have hnontrivExt : Nontrivial (R ⧸ Ideal.ofList (gens ++ [g])) :=
    Function.Surjective.nontrivial e'.symm.surjective
  -- `AlgEquiv.toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂` is a
  -- confirmed-present Mathlib4 definition (`Mathlib.Algebra.Algebra.Equiv`,
  -- with `@[simp] AlgEquiv.toLinearEquiv_apply : e.toLinearEquiv a = e a`),
  -- and `LinearEquiv.finrank_eq` gives `finrank` equality directly across
  -- any `k`-linear equivalence -- no need to route through
  -- `LinearMap.finrank_le_finrank_of_surjective` (whose implicit map
  -- argument doesn't unify against an `AlgEquiv`-coerced surjectivity
  -- proof) or antisymmetry of `≤` at all.
  have hfinrankExt : Module.finrank k (R ⧸ Ideal.ofList (gens ++ [g])) =
      Module.finrank k ((R ⧸ Ideal.ofList gens) ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set (R ⧸ Ideal.ofList gens))) :=
    (LinearEquiv.finrank_eq e'.toLinearEquiv).symm
  exact ⟨hfinExt, hnontrivExt, hfinrankExt⟩

/-- **Stages 8–11, finiteness-exporting version.** Same conclusion as
`finrank_le_curveRelation_ofList_cons` (the `finrank` bound), plus
`Module.Finite (F p) (...)` and `Nontrivial (...)` on the EXTENDED
one-step quotient — so this can serve as one step of an explicit
induction rather than needing its `Module.Finite`/`Nontrivial` inputs
independently re-derived at every prefix.

**`Nontrivial B` for free, this shape's own reason**: `B := A ⧸
Ideal.span {mk g}` for `g := curveRelationGen ... w x = X w² − (curve
expression in `x`)`. `g` is not a unit in `Rdec p = MvPolynomial Idx (F
p)` (its `X w`-total-degree-2 leading term alone rules out any
constant/unit inverse -- concretely, `IsUnit` in a `MvPolynomial` ring
over a field forces `totalDegree = 0`, `MvPolynomial.isUnit_iff` /
`totalDegree_eq_zero_iff_isUnit`-style facts confirm this, and `g` has
`totalDegree ≥ 2`), hence its image in ANY quotient `A` is not
automatically a unit either -- but since deciding "is `mk_A g` a unit in
the quotient `A`" needs more than `g`'s own non-unit-ness in `Rdec p`
(quotienting can turn non-units into units), the cleanest route is
directly via `g` itself: `Ideal.span {mk_A g} ≠ ⊤` follows from `mk_A g`
not being a unit in `A`, and rather than re-deriving this per-instance
fact abstractly, this theorem instead takes it as an explicit hypothesis
`hgu : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) g)` -- the honest,
minimal per-stage side-condition (structurally parallel to
`hd_unit`/`IsUnit`-strength hypotheses the linear-elimination stages
already need), left for the Assembly file to discharge against
`theData`'s actual curve-relation values, rather than asserted here
without justification. -/
theorem finrank_le_and_finite_curveRelation_ofList_cons
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p) (w x : Idx)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    (hfinA : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens))
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    (hgu : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList gens)
      (curveRelationGen p c0 c1 c2 c3 c4 w x))) :
    Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 w x])) ≤
      2 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens) ∧
    Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 w x])) ∧
    Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 w x])) := by
  set A := Rdec p ⧸ Ideal.ofList gens with hA_def
  set g := curveRelationGen p c0 c1 c2 c3 c4 w x with hg_def
  set B := A ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A) with hB_def
  set f : A := curveFImage p gens c0 c1 c2 c3 c4 x with hf_def
  set t : B := Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X w)) with
    ht_def
  -- Identical `ht` construction to `finrank_le_curveRelation_ofList_cons`.
  have ht : (Polynomial.aeval t) (curveRelationPoly f) = 0 := by
    set φ : Rdec p →+* B :=
      (Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))).comp
        (Ideal.Quotient.mk (Ideal.ofList gens)) with hφ_def
    have hφg : φ g = 0 := by
      show Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) g) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have halgebraMap : ∀ y : A, algebraMap A B y = Ideal.Quotient.mk
        (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A)) y := fun y => rfl
    rw [curveRelationPoly, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C]
    rw [ht_def, halgebraMap, hf_def, curveFImage]
    have : φ g = Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X w) ^ 2 -
        Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens)
            (MvPolynomial.C c0 + MvPolynomial.C c1 * MvPolynomial.X x +
              MvPolynomial.C c2 * MvPolynomial.X x ^ 2 +
              MvPolynomial.C c3 * MvPolynomial.X x ^ 3 +
              MvPolynomial.C c4 * MvPolynomial.X x ^ 4 + MvPolynomial.X x ^ 5)) := by
      show Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens)
            (MvPolynomial.X w ^ 2 -
              (MvPolynomial.C c0 + MvPolynomial.C c1 * MvPolynomial.X x +
                MvPolynomial.C c2 * MvPolynomial.X x ^ 2 +
                MvPolynomial.C c3 * MvPolynomial.X x ^ 3 +
                MvPolynomial.C c4 * MvPolynomial.X x ^ 4 + MvPolynomial.X x ^ 5))) = _
      simp only [map_sub, map_pow]
    rw [← this, hφg]
  have hgen : Algebra.adjoin A ({t} : Set B) = (⊤ : Subalgebra A B) :=
    adjoin_singleton_eq_top_of_quotient _ t
  obtain ⟨hfinB, hbound⟩ := finrank_le_of_monic_annihilator_of_finite (k := F p)
    hfinA (curveRelationPoly f) (curveRelationPoly_monic f) t ht hgen
  rw [curveRelationPoly_natDegree] at hbound
  have hnontrivB : Nontrivial B := nontrivial_of_span_ne_top hgu
  obtain ⟨hfinExt, hnontrivExt, hfinrankExt⟩ :=
    finite_and_nontrivial_ofList_cons_of_two_step gens g hfinB hnontrivB
  exact ⟨le_of_eq_of_le hfinrankExt hbound, hfinExt, hnontrivExt⟩

/-- **Stages 0–7, finiteness-exporting version.** Same conclusion as
`finrank_le_linearElim_ofList_cons` (the `finrank` bound), plus
`Module.Finite (F p) (...)` and `Nontrivial (...)` on the extended
one-step quotient. **`Nontrivial B` here needs a genuinely separate
hypothesis from `hd_unit`**: `B := A ⧸ Ideal.span {mk g}` for
`g := linearElimGen ... u = c − X u * d`. Unlike the curve-relation
shape, `g`'s non-unit-ness in `A` is NOT automatic from `hd_unit : IsUnit
(mk_A d)` alone (indeed, `hd_unit` is exactly what makes the RESCALED
monic polynomial `X u − d⁻¹c` well-defined -- it says nothing about
whether `c − X u * d` itself happens to be a unit as an element of `A`,
which it structurally cannot be regardless of `d`, since it is degree-1
in the FREE generator `X u` and `A` is a further quotient of a
polynomial ring in which `X u` is not eliminated until exactly this
step -- but making that precise for an arbitrary prefix `gens` is exactly
the kind of per-stage fact the roadmap's `hd_unit`/`hv_ext`-style
philosophy asks to name explicitly rather than derive from nothing). This
theorem takes it as an explicit hypothesis `hgu`, matching the
curve-relation theorem's own honest scoping above. -/
theorem finrank_le_and_finite_linearElim_ofList_cons
    (gens : List (Rdec p)) (c d : Rdec p) (u : Idx)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    (hfinA : Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens))
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    (hd_unit : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) d))
    (hgu : ¬ IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) (linearElimGen p c d u))) :
    Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++ [linearElimGen p c d u])) ≤
      Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens) ∧
    Module.Finite (F p) (Rdec p ⧸ Ideal.ofList (gens ++ [linearElimGen p c d u])) ∧
    Nontrivial (Rdec p ⧸ Ideal.ofList (gens ++ [linearElimGen p c d u])) := by
  set A := Rdec p ⧸ Ideal.ofList gens with hA_def
  set g := linearElimGen p c d u with hg_def
  set B := A ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A) with hB_def
  set cA : A := Ideal.Quotient.mk (Ideal.ofList gens) c with hcA_def
  set dA : A := Ideal.Quotient.mk (Ideal.ofList gens) d with hdA_def
  set t : B := Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) with
    ht_def
  have ht : (Polynomial.aeval t) (linearElimPoly cA dA) = 0 := by
    set φ : Rdec p →+* B :=
      (Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))).comp
        (Ideal.Quotient.mk (Ideal.ofList gens)) with hφ_def
    have hφg : φ g = 0 := by
      show Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) g) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have halgebraMap : ∀ y : A, algebraMap A B y = Ideal.Quotient.mk
        (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A)) y := fun y => rfl
    rw [linearElimPoly, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.aeval_C, halgebraMap, halgebraMap]
    have hφg' : φ g = Ideal.Quotient.mk
          (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) c) -
        t * Ideal.Quotient.mk
          (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) d) := by
      show Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) (c - MvPolynomial.X u * d)) =
        Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) c) -
          Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) *
          Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) d)
      simp only [map_sub, map_mul]
    rw [← hφg', hφg]
  have hgen : Algebra.adjoin A ({t} : Set B) = (⊤ : Subalgebra A B) :=
    adjoin_singleton_eq_top_of_quotient _ t
  have ht' : (Polynomial.aeval t) (linearElimMonicPoly cA dA hd_unit) = 0 :=
    (aeval_linearElimPoly_eq_zero_iff cA dA hd_unit t).mp ht
  obtain ⟨hfinB, hbound⟩ := finrank_le_of_monic_annihilator_of_finite (k := F p)
    hfinA (linearElimMonicPoly cA dA hd_unit) (linearElimMonicPoly_monic cA dA hd_unit)
    t ht' hgen
  rw [linearElimMonicPoly_natDegree, one_mul] at hbound
  have hnontrivB : Nontrivial B := nontrivial_of_span_ne_top hgu
  obtain ⟨hfinExt, hnontrivExt, hfinrankExt⟩ :=
    finite_and_nontrivial_ofList_cons_of_two_step gens g hfinB hnontrivB
  exact ⟨le_of_eq_of_le hfinrankExt hbound, hfinExt, hnontrivExt⟩

end DecoupledSystem
end Genus2Lean
