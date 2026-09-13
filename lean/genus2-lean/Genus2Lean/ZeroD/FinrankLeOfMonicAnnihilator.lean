import Mathlib

/-!
# Core lemma: a monic annihilator of degree `d` bounds `finrank` by `d * finrank` of the base

Revision 02: fix the `AdjoinRoot.liftAlgHom_root` application by supplying
its explicit polynomial argument `G`.

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
section): `A[T]/(G) ↠ B` (via `AdjoinRoot.liftAlgHom`, using `Algebra.adjoin
A {t} = ⊤` for surjectivity), and `A[T]/(G) = AdjoinRoot G` has `A`-basis
`1, T, ..., T^(d-1)` since `G` is monic of degree `d`
(`AdjoinRoot.powerBasis'`). A `k`-linear surjection out of a finite
`k`-module cannot increase `k`-finrank, giving the bound once
`AdjoinRoot G`'s `k`-finrank is identified as `d * finrank k A` via the
tower law.

**Mathlib API note (corrected after a second REPL pass)**: the
algebra-lifting constructor is `AdjoinRoot.liftAlgHom (p : Polynomial R)
(i : R →ₐ[S] T) (x : T) (h : Polynomial.eval₂ (↑i) x p = 0) : AdjoinRoot p
→ₐ[S] T`. A first attempt instantiated `i := AlgHom.id A A`, but that
forces `T := A`, i.e. a map landing in `A` — wrong, since the root `t`
lives in `B`. The correct instantiation is `R := A`, `T := B`, `S := A`,
`i := Algebra.ofId A B : A →ₐ[A] B` (available from the ambient
`[Algebra A B]` instance), giving `AdjoinRoot G →ₐ[A] B` as needed; this
matches the general shape behind the simpler `AdjoinRoot.liftHom`, whose
defining equation is literally `liftHom f x hfx = liftAlgHom f (Algebra.ofId
R S) x hfx`. Since `↑(Algebra.ofId A B) = algebraMap A B`, the `eval₂`
hypothesis needed is `eval₂ (algebraMap A B) t G = 0`, which is exactly
what `Polynomial.aeval_def` unfolds `aeval t G = 0` to. Likewise
`AdjoinRoot.powerBasis'`'s dimension fact is exposed via `PowerBasis.finrank`
(`(AdjoinRoot.powerBasis' hG).finrank : finrank A (AdjoinRoot G) = (powerBasis'
hG).dim`, and `AdjoinRoot.powerBasis'_dim` separately gives `dim = G.natDegree`),
and the finite/free-module instances for `AdjoinRoot` of a monic polynomial
are supplied by `Polynomial.Monic.finite_adjoinRoot` /
`Polynomial.Monic.free_adjoinRoot` (both keyed off `hG`).
-/

namespace Genus2Lean

open Polynomial

variable {k A B : Type*} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [Algebra A B] [IsScalarTower k A B] [StrongRankCondition A] [Module.Finite k A]

/-- **The core reusable fact.** `t : B` satisfies a monic degree-`d` relation
over `A` (via `G.aeval t = 0`, equivalently `eval₂ (algebraMap A B) t G = 0`
via the `A →ₐ[A] B` algebra map `Algebra.ofId A B`), and `A`-adjoining `t` is
all of `B` (`Algebra.adjoin A {t} = ⊤`, i.e. `t` generates `B` as an
`A`-algebra) — then `B`'s `k`-dimension is at most `d` times `A`'s.

**`[Module.Finite k A]` is a real hypothesis, not incidental**: it's what
makes `AdjoinRoot G` (a finite `A`-module of rank `d`, via
`Polynomial.Monic.finite_adjoinRoot`/`AdjoinRoot.powerBasis'`) also a
finite-dimensional `k`-module via `Module.Finite.trans`, which
`LinearMap.finrank_le_finrank_of_surjective` needs on its source. In the
peel-chain application this is supplied inductively: stage 0's base algebra
is `k` itself (`finrank k k = 1`), and each later stage's `A` is the
previous stage's `B`, already known finite by that stage's own instance of
this theorem (via the `Module.Finite k B` this proof establishes along the
way, one tower step further). -/
theorem finrank_le_of_monic_annihilator
    (G : Polynomial A) (hG : G.Monic) (t : B)
    (ht : (Polynomial.aeval t) G = 0)
    (hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A B)) :
    Module.finrank k B ≤ G.natDegree * Module.finrank k A := by
  set d := G.natDegree with hd_def
  -- `ht : aeval t G = 0` unfolds to exactly the `eval₂` hypothesis
  -- `AdjoinRoot.liftAlgHom` wants, once `i := Algebra.ofId A B` is noted to
  -- act as `algebraMap A B`.
  have ht' : Polynomial.eval₂ ((Algebra.ofId A B : A →ₐ[A] B) : A →+* B) t G = 0 := by
    simpa [Polynomial.aeval_def] using ht
  -- The `A`-algebra map `AdjoinRoot G →ₐ[A] B` sending the root to `t`.
  set φ : AdjoinRoot G →ₐ[A] B := AdjoinRoot.liftAlgHom G (Algebra.ofId A B) t ht' with hφ_def
  -- `φ` is surjective: its range, as a subalgebra, contains `t` (it's
  -- `φ (AdjoinRoot.root G) = t` by `AdjoinRoot.liftAlgHom_root`) and is
  -- closed under the `A`-algebra structure, so it contains
  -- `Algebra.adjoin A {t}`, which is everything by `hgen`.
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
  -- `AdjoinRoot G` has a finite `A`-basis `1, root, ..., root^(d-1)`, so
  -- it's a finite (in fact free) `A`-module of rank `d`, and hence (via
  -- `Module.Finite.trans`, using `[Module.Finite k A]`) a finite
  -- `k`-module too -- exactly what `LinearMap.finrank_le_finrank_of_surjective`
  -- needs on its source below.
  haveI hfreeA : Module.Free A (AdjoinRoot G) := hG.free_adjoinRoot
  haveI hfinA : Module.Finite A (AdjoinRoot G) := hG.finite_adjoinRoot
  have hdimA : Module.finrank A (AdjoinRoot G) = d := (AdjoinRoot.powerBasis' hG).finrank
  -- `AdjoinRoot G`'s `k`-algebra structure factors through `A` (it's an
  -- `A`-algebra, and `A` is a `k`-algebra); this scalar-tower instance
  -- should resolve automatically from Mathlib's generic algebra-tower
  -- machinery. **REPL check needed**: if it doesn't resolve by
  -- `inferInstance`, that's a one-line fix, not a sign anything upstream
  -- is wrong.
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
