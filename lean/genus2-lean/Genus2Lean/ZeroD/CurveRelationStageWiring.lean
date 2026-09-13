import Mathlib
import Genus2Lean.ZeroD.QuotOfListChainFinrankStep
import Genus2Lean.ZeroD.QuotOfListChainAdjoinTop
import Genus2Lean.ZeroD.CurveRelationsDegreeBound
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# Stages 8–11 wiring: curve relations against a literal `Ideal.ofList` prefix

Item 5 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, the
first concrete stage specialization — per the roadmap's own "Suggested
order" (do the already-monic curve-relation stages before the harder
linear-elimination bookkeeping, to confirm the whole Assembly chain
composes end-to-end on the easiest case first).

**What this file specializes**: `finrank_le_of_monic_annihilator`
(`FinrankLeOfMonicAnnihilator.lean`) and `finrank_le_ofList_cons`
(`QuotOfListChainFinrankStep.lean`) to the literal shape a curve-relation
generator takes — `g := w' ^ 2 - (c0 + c1*x' + c2*x'^2 + c3*x'^3 +
c4*x'^4 + x'^5)` for the newly-peeled variable `w' := X w : Rdec p` and
an already-fixed `x' := X x : Rdec p` (matching `curveA1`'s literal shape,
`DecoupledSystemRegular.lean` §3, with `w := wa1`, `x := a1`, and likewise
for `curveA2`/`curveB1`/`curveB2`) — generic over the prefix `gens : List
(Rdec p)` and the two generator symbols `w x : Idx`, NOT yet plugged in
against `genList`'s own literal 8-element `FuList ++ FvList` prefix (that
final substitution, and the parallel work for `curveA2`/`curveB1`/
`curveB2`, is later Assembly work once all 12 stages are ready to compose
via `Module.finrank_mul_finrank`).

**Why `finrank_le_of_monic_annihilator` directly, not
`finrank_le_of_curve_relation`'s `AdjoinRoot`**: `finrank_le_of_curve_
relation`'s conclusion is about `Module.finrank k (AdjoinRoot (X² − C f))`
— but Assembly's actual target ring, `(Rdec p ⧸ Ideal.ofList gens) ⧸
Ideal.span {mk gens g}`, is a quotient of the ALREADY-EXISTING ring `Rdec p
⧸ Ideal.ofList gens` by the (already fixed) generator's image, not a fresh
`Polynomial A ⧸ Ideal.span {G}` with `A` and `X` genuinely separate. These
two rings are isomorphic in principle, but bridging them would need an
extra `AdjoinRoot`-vs-literal-quotient identification this file avoids
entirely by applying `finrank_le_of_monic_annihilator`'s underlying fact
directly against `B := (Rdec p ⧸ Ideal.ofList gens) ⧸ Ideal.span {mk g}`,
with `t := mk (mk w')` — using `QuotOfListChainAdjoinTop.lean`'s
observation that `Algebra.adjoin A {t} = ⊤` is free for exactly this
"`B` is a quotient of `A`" shape, so only the annihilation fact `ht` needs
real proof. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The curve-relation polynomial's `A`-coefficient version, once `x`'s
image `x' : A := Rdec p ⧸ Ideal.ofList gens` is fixed — i.e. `curveF`
evaluated symbolically at the ALREADY-QUOTIENTED `x'`, matching what
`finrank_le_of_curve_relation`/`curveRelationPoly` calls `f`. -/
noncomputable def curveFImage (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p)
    (x : Idx) : Rdec p ⧸ Ideal.ofList gens :=
  Ideal.Quotient.mk (Ideal.ofList gens)
    (MvPolynomial.C c0 + MvPolynomial.C c1 * MvPolynomial.X x +
      MvPolynomial.C c2 * MvPolynomial.X x ^ 2 + MvPolynomial.C c3 * MvPolynomial.X x ^ 3 +
      MvPolynomial.C c4 * MvPolynomial.X x ^ 4 + MvPolynomial.X x ^ 5)

/-- **The literal curve-relation generator, as an element of `Rdec p`** —
matching `curveA1 p c0 c1 c2 c3 c4 = wa1'^2 - (C c0 + ... + a1'^5)`'s exact
shape (`DecoupledSystemRegular.lean` §3) but generic in which two `Idx`
symbols play the roles of `wa1`/`a1`. -/
noncomputable def curveRelationGen (c0 c1 c2 c3 c4 : F p) (w x : Idx) : Rdec p :=
  MvPolynomial.X w ^ 2 -
    (MvPolynomial.C c0 + MvPolynomial.C c1 * MvPolynomial.X x +
      MvPolynomial.C c2 * MvPolynomial.X x ^ 2 + MvPolynomial.C c3 * MvPolynomial.X x ^ 3 +
      MvPolynomial.C c4 * MvPolynomial.X x ^ 4 + MvPolynomial.X x ^ 5)

/-- **The stage-8-shape `finrank` bound, wired to a literal `Ideal.ofList`
prefix.** Given a prefix `gens`, base field `k := F p`, and the curve
relation `g := curveRelationGen ... w x` for two DISTINCT `Idx` symbols
`w, x` (distinctness needed so `X w` and `X x` are different ring
generators, matching `wa1 ≠ a1` etc. in the real peel chain), the extended
quotient's `finrank` is at most twice the prefix quotient's.

**Why `[StrongRankCondition ...]`/`[Module.Finite (F p) ...]`/
`[Nontrivial ...]` on `A := Rdec p ⧸ Ideal.ofList gens` are hypotheses
here, not free instances**: `finrank_le_of_monic_annihilator`
(`FinrankLeOfMonicAnnihilator.lean`) genuinely needs the first two to
bound `B`'s `finrank` via `AdjoinRoot`'s finite free module structure,
and `curveRelationPoly_monic`/`curveRelationPoly_natDegree`
(`CurveRelationsDegreeBound.lean`) are stated in a section requiring
`[Nontrivial A]`. For an ARBITRARY `gens : List (Rdec p)` (not yet the
literal `genList` prefix) none of these is derivable from nothing —
per `QuotOfListChain.lean`'s own docstring, discharging them for the
real 8-or-more-element prefixes is left to the not-yet-written final
Assembly file, which will supply them (by induction along the peel
chain, each stage's `A` being the previous stage's already-known-finite,
nontrivial `B`) when this lemma is actually invoked. -/
theorem finrank_le_curveRelation_ofList_cons
    (gens : List (Rdec p)) (c0 c1 c2 c3 c4 : F p) (w x : Idx)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    [Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)]
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)] :
    Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++ [curveRelationGen p c0 c1 c2 c3 c4 w x])) ≤
      2 * Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens) := by
  apply finrank_le_ofList_cons
  set A := Rdec p ⧸ Ideal.ofList gens with hA_def
  set g := curveRelationGen p c0 c1 c2 c3 c4 w x with hg_def
  set B := A ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A) with hB_def
  set f : A := curveFImage p gens c0 c1 c2 c3 c4 x with hf_def
  set t : B := Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X w)) with
    ht_def
  -- `G := curveRelationPoly f = X^2 - C f : Polynomial A` is monic of
  -- degree 2 (`CurveRelationsDegreeBound.lean`'s own already-proved
  -- facts), and `aeval t G = 0` unfolds to exactly `mk_B (mk_A (X w)^2 -
  -- mk_A f) = 0`, which is `mk_B (mk_A g) = 0` after unfolding `f`'s
  -- definition and `g`'s literal shape — true by construction, since `B`
  -- quotients by `Ideal.span {mk_A g}`.
  have ht : (Polynomial.aeval t) (curveRelationPoly f) = 0 := by
    -- `φ : Rdec p →+* B`, the composite two-step quotient map `mk_B ∘
    -- mk_A`. Since `g`'s image under `mk_A` generates the ideal `B`
    -- quotients by, `φ g = 0` (`hφg`). The goal is `aeval t (X^2 - C f) =
    -- 0` for `t = φ (X w)` and `f = mk_A (curveF-expression at x)`; since
    -- `aeval` on a `Polynomial A` at `t : B` (viewing `A →+* B` via
    -- `algebraMap`) applied to `X^2 - C f` equals `t^2 - algebraMap A B f`
    -- (`aeval_X_pow`/`aeval_C`/`map_sub`), and `algebraMap A B f` is
    -- literally `φ` applied to the SAME `Rdec p`-expression `f` unfolds
    -- to (since `algebraMap A B = mk_B` and `f = mk_A (...)`, so
    -- `algebraMap A B f = mk_B (mk_A (...)) = φ (...)`), the whole goal
    -- reduces to `φ (X w) ^ 2 - φ (curveF-expr at x) = 0`, i.e. `φ g = 0`
    -- once `g`'s own definition (`X w ^ 2 - (curveF-expr at x)`) is
    -- unfolded and `φ`'s ring-hom laws (`map_sub`/`map_pow`) distribute
    -- it — exactly `hφg`, no further content needed.
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
      -- `g` is *definitionally* `curveRelationGen p c0 c1 c2 c3 c4 w x`
      -- (from the `set` above), so we unfold it via `show` (relying on
      -- defeq) rather than `rw [hg_def]` — rewriting `g`'s *definition*
      -- propositionally would also rewrite the frozen occurrences of `g`
      -- inside `B`'s own type (`Ideal.span {mk_A g}`), which is exactly
      -- what triggered the "motive is not type correct" failure: `B`,
      -- `φ`'s codomain, and hence `φ`'s very type all mention `g`, so a
      -- naive `rw` there is an illegal dependent rewrite. `show` sidesteps
      -- this entirely since it only changes how the (unchanged) goal is
      -- displayed/elaborated, never touching `B`/`φ`'s actual type.
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
  -- `hgen : Algebra.adjoin A {t} = ⊤` is free since `B` is literally a
  -- quotient of `A` (`QuotOfListChainAdjoinTop.lean`'s
  -- `adjoin_singleton_eq_top_of_quotient`). `B` is *definitionally*
  -- `A ⧸ Ideal.span {mk_A g}` (from the `set B := ...` above), so the
  -- lemma applies to `t : B` directly, no rewrite needed.
  have hgen : Algebra.adjoin A ({t} : Set B) = (⊤ : Subalgebra A B) :=
    adjoin_singleton_eq_top_of_quotient _ t
  have := finrank_le_of_monic_annihilator (k := F p)
    (curveRelationPoly f) (curveRelationPoly_monic f) t ht hgen
  rwa [curveRelationPoly_natDegree] at this

end DecoupledSystem
end Genus2Lean
