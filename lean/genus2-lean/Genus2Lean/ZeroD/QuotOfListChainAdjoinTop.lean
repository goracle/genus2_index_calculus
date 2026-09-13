import Mathlib

/-!
# Assembly: `Algebra.adjoin A {t} = ⊤` is automatic for `B := A ⧸ Ideal.span {c}`

Item 5 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, part of
the "chaining across stages" work. A small but load-bearing observation
that simplifies EVERY one of the 12 upcoming stage specializations, not
just one: each per-stage `finrank` lemma
(`finrank_le_of_monic_annihilator`/`finrank_le_of_linear_elim`/
`finrank_le_of_curve_relation`) needs `Algebra.adjoin A {t} = ⊤` for
whatever `t : B` it's applied with — but in EVERY peel-chain stage, `B` is
literally `A ⧸ Ideal.span {c}` for the newly-appended generator's image
`c`, i.e. `B` is a QUOTIENT of `A` itself, not a genuine ring extension
where a new generator is adjoined. Since `algebraMap A B` (`=
Ideal.Quotient.mk (Ideal.span {c})` composed appropriately) is already
SURJECTIVE, `Algebra.adjoin A {t} = ⊤` holds for `t` — in fact for ANY `t`,
including ones that play no real role in generating `B`. This means the
`hgen` hypothesis every per-stage lemma asks for is free at Assembly time;
the only real content at each of the 12 stages is the annihilation fact
`ht : aeval t G = 0`, which needs the newly-peeled variable's own defining
relation, not this genericity fact. -/

namespace Genus2Lean

variable {A : Type*} [CommRing A]

/-- **`Algebra.adjoin A {t} = ⊤` is automatic whenever `B` is presented as
a quotient of `A` itself.** Since `algebraMap A (A ⧸ I)` is
`Ideal.Quotient.mk I`, which is surjective, `A`'s own image already fills
`B` — the distinguished element `t` doesn't even need to participate;
`Algebra.adjoin A {t} ⊇ (algebraMap A B).range = ⊤` regardless of what `t`
is. This is exactly why every peel-chain stage's `hgen` hypothesis is free
at Assembly time: `B := A ⧸ Ideal.span {c}` for the newly-appended
generator's image `c`, never a genuine extension ring where a new
generator is needed to reach every element. -/
theorem adjoin_singleton_eq_top_of_quotient (I : Ideal A) (t : A ⧸ I) :
    Algebra.adjoin A ({t} : Set (A ⧸ I)) = ⊤ := by
  rw [eq_top_iff]
  intro b _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  -- `Ideal.Quotient.mk I a = algebraMap A (A ⧸ I) a` definitionally, and
  -- `algebraMap A B _ ∈ Algebra.adjoin A S` for ANY subalgebra-generating
  -- set `S`, since `Algebra.adjoin` always contains the image of the base
  -- ring.
  exact Subalgebra.algebraMap_mem _ a

end Genus2Lean
