import Mathlib

/-!
# Core lemma: a monic annihilator of degree `d` bounds `finrank` by `d * finrank` of the base

Item 1 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan: the single
reusable fact the whole plan is built on, split out on its own with zero
peel-chain-specific content so it can be checked (and reused) independently
of everything else in that roadmap.

**Statement, informally**: if `A` is a `k`-algebra of finite `k`-dimension,
`B` is an `A`-algebra, and some `t : B` satisfies a monic polynomial relation
`G ∈ A[T]` of degree `d` (i.e. `(Polynomial.aeval t) G = 0`), and `B` is
generated as an `A`-algebra by `t` alone (`Algebra.adjoin A {t} = ⊤`), then
`finrank k B ≤ d * finrank k A`.

**Why this is the right shape for the peel chain**: at each stage, `A` is the
algebra built from the previous stages, `B` is the algebra one variable
further along, and `t` is the newly-introduced variable. Every peel-chain
generator (`Fu0`, ..., `curveB2`) is, after dividing by a unit leading
coefficient, exactly a monic annihilator of the newly-adjoined variable over
the previous stage's algebra — so this one lemma, applied twelve times and
composed via `Module.finrank_mul_finrank`, is meant to be the entire
assembly's engine. This file supplies only the single-stage fact; chaining
across stages, and identifying each concrete peel-chain generator's monic
form, are separate, later files per the roadmap's file plan (items 2-5).

**Proof strategy** (per the roadmap's "Strategy, per ChatGPT consult"
section): `A[T]/(G) ↠ B` (via `Polynomial.aeval t`, using `Algebra.adjoin A
{t} = ⊤` for surjectivity), and `A[T]/(G)` has `A`-basis `1, T, ..., T^(d-1)`
since `G` is monic of degree `d` (`AdjoinRoot.powerBasis'`). A `k`-linear
surjection from an `A`-module of `k`-finrank `d * finrank k A` cannot
increase `k`-finrank, giving the bound.
-/

namespace Genus2Lean

open Polynomial

variable {k A B : Type*} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B] [StrongRankCondition A] [Module.Finite k A]

/-- **The core reusable fact.** `t : B` satisfies a monic degree-`d` relation
over `A` (via `G.aeval t = 0`), and `A`-adjoining `t` is all of `B`
(`Algebra.adjoin A {t} = ⊤`, i.e. `t` generates `B` as an `A`-algebra) — then
`B`'s `k`-dimension is at most `d` times `A`'s.

**`[Module.Finite k A]` is a real hypothesis, not incidental**: it's what
makes `AdjoinRoot G` (an `A`-module of finite `A`-rank `d`, via
`AdjoinRoot.powerBasis'`) also a finite-dimensional `k`-module via
`Module.Finite.trans`, which `LinearMap.finrank_le_finrank_of_surjective`
needs on its source. In the peel-chain application this is supplied
inductively: stage 0's base algebra is `k` itself (`finrank k k = 1`), and
each later stage's `A` is the previous stage's `B`, already known finite by
that stage's own instance of this theorem (via the `Module.Finite k B`
this proof establishes along the way as `hfink`, one tower step further). -/
theorem finrank_le_of_monic_annihilator
    (G : Polynomial A) (hG : G.Monic) (t : B)
    (ht : (Polynomial.aeval t) G = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤ G.natDegree * Module.finrank k A := by
  -- `AdjoinRoot G` is a free `A`-module with basis `1, root, ..., root^(d-1)`
  -- (`AdjoinRoot.powerBasis'`), so as a `k`-module it has `finrank k (AdjoinRoot G)
  -- = d * finrank k A` via the tower law.
  set d := G.natDegree with hd_def
  -- The `A`-algebra map `AdjoinRoot G →ₐ[A] B` sending the root to `t`,
  -- using `ht` to discharge the defining relation.
  set φ : AdjoinRoot G →ₐ[A] B := AdjoinRoot.liftHom G t ht with hφ_def
  -- `φ` is surjective: its range, as a subalgebra, contains `t` (it's
  -- `φ (AdjoinRoot.root G) = t` by `AdjoinRoot.liftHom_root`) and is closed
  -- under the `A`-algebra structure, so it contains `Algebra.adjoin A {t}`,
  -- which is everything by `hgen`.
  have hφ_surj : Function.Surjective φ := by
    have hrange : Algebra.adjoin A {t} ≤ φ.range := by
      rw [Algebra.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨AdjoinRoot.root G, AdjoinRoot.liftHom_root ht⟩
    rw [hgen] at hrange
    intro b
    have hb : b ∈ (⊤ : Subalgebra A B) := trivial
    have := hrange hb
    simpa [AlgHom.mem_range] using this
  -- `AdjoinRoot G` has a finite `A`-basis `1, root, ..., root^(d-1)`
  -- (`AdjoinRoot.powerBasis' hG`, dimension `d`), so it's a finite `A`-module,
  -- and hence (via `Module.Finite.trans`, using `[Module.Finite k A]`) a
  -- finite `k`-module too -- exactly what
  -- `LinearMap.finrank_le_finrank_of_surjective` needs on its source below.
  have hpb := AdjoinRoot.powerBasis' hG
  have hdimA : Module.finrank A (AdjoinRoot G) = d := hpb.finrank
  haveI hfinA : Module.Finite A (AdjoinRoot G) := Module.Finite.ofBasis hpb.basis
  -- `AdjoinRoot G`'s `k`-algebra structure factors through `A` (it's an
  -- `A`-algebra, and `A` is a `k`-algebra), so this scalar-tower instance
  -- should resolve automatically from Mathlib's generic algebra-tower
  -- machinery. **REPL check needed**: if `IsScalarTower.of_algebraMap_eq'`
  -- or an analogous lemma is needed explicitly here instead of plain
  -- inference, that's a one-line fix, not a sign anything upstream is wrong.
  haveI : IsScalarTower k A (AdjoinRoot G) := inferInstance
  haveI hfink : Module.Finite k (AdjoinRoot G) := Module.Finite.trans A (AdjoinRoot G)
  -- View `φ` as a `k`-linear map (it's `A`-linear, and `k → A` factors
  -- through the tower), then a surjective `k`-linear map out of a finite
  -- `k`-module cannot increase `k`-finrank.
  have hφ_lin_surj : Function.Surjective (φ.toLinearMap.restrictScalars k) := hφ_surj
  have hle : Module.finrank k B ≤ Module.finrank k (AdjoinRoot G) :=
    LinearMap.finrank_le_finrank_of_surjective hφ_lin_surj
  -- `finrank k (AdjoinRoot G) = finrank k A * d` via the tower law
  -- (`Module.finrank_mul_finrank`) for the `k ≤ A ≤ AdjoinRoot G` tower,
  -- combined with `hdimA` above.
  have htower : Module.finrank k (AdjoinRoot G) =
      Module.finrank k A * Module.finrank A (AdjoinRoot G) :=
    (Module.finrank_mul_finrank k A (AdjoinRoot G)).symm
  rw [hdimA] at htower
  calc Module.finrank k B ≤ Module.finrank k (AdjoinRoot G) := hle
    _ = Module.finrank k A * d := htower
    _ = d * Module.finrank k A := Nat.mul_comm _ _

end Genus2Lean
