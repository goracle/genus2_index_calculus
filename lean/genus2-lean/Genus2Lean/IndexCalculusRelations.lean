import Mathlib
set_option linter.style.header false

/-!
# What a relation is, and what "the same relation" means (gauge redundancy)

`IndexCalculusComplexity.lean` counts solves. This file fixes what one solve
*produces*, so that "a relation", "its right-hand side", and "two relations
that are gauge-redundant" are Lean objects rather than prose.

## The model (CORRECTED — an earlier version keyed everything on `alpha`)

`G` is the cryptographic subgroup `<a>`. A **relation** is a finite formal sum
of group elements together with a right-hand side `rhs • a`:

    (sum of terms) = rhs • a                                (*)

A **matching solve** at `(alpha, alpha')` finds points with (eq 1)

    P1 + P2 - P3 - P4 = (alpha - alpha') • a.

So the relation it produces has terms `[P1, P2, -P3, -P4]` and

    rhs = alpha - alpha'      (NOT `alpha`).

The earlier version of this file, and the roadmap block that cited it, took the
right-hand side to be `alpha` alone. That is wrong: eq 1 only ever sees the
difference (`eq1_gauge_invariant`, `MatchingEquationTranslation.lean`).

## Two kinds of gauge redundancy — both are "same right-hand side"

Write `A = P1 + P2`, `B = P3 + P4`, so eq 1 is `A - B = (alpha - alpha') • a`.

1. **Translation** (`matching_solutions_translate_by_delta`). Two solves with
   the same right-hand side have pair-sums related by one common `Δ`:
   `A = A' + Δ`, `B = B' + Δ`. Over the columns `(A, B, A', B', Δ)`:

        row 1   A  - B          1  -1   0   0   0
        row 2   A' - B'         0   0   1  -1   0
        t₁      A - A' - Δ      1   0  -1   0  -1
        t₂      B - B' - Δ      0   1   0  -1  -1

   `row 1 - row 2 = t₁ - t₂ = (1,-1,-1,1,0)`: the two rows differ by a
   combination of the translation relations only (equivalently, substitute
   `A' = A - Δ`, `B' = B - Δ` into row 2: the `Δ` coefficient is `-1 + 1 = 0`
   and row 2 becomes row 1). The right-hand sides agree as well, so their
   difference is a pure `sum = 0` row with no `a`-component. Formalized as
   `translation_rows_differ_by_translation_relations`.

2. **Common shift** `(alpha, alpha') ↦ (alpha + c, alpha' + c)`. The points
   stay put and the shift lands on the auxiliary target `D` instead. The
   relation is literally the same: same terms, same right-hand side
   (`MatchingSolve.shift_toRelation_terms`, `shift_toRelation_rhs`).

Type 2 is the case `Δ = 0` of type 1's shape, and *conversely* type 1 is
exhaustive: `gaugeRelated_iff_same_rhsElt` shows that two solves are
translation-related iff their right-hand sides are equal. So "same
right-hand side" is the single condition that captures every gauge
redundancy, and no third kind exists.

## Why `DistinctRHS` is keyed on the group element `rhs • a`

* Keying on `alpha` (old) accepts `(alpha, alpha')` and `(alpha + c, alpha' + c)`
  as different (`MatchingSolve.shift_alpha_ne`) — exactly the duplicates to
  reject.
* Keying on the integer `alpha - alpha'` still misses pairs whose integers
  differ by a multiple of `ord a`, which are the same element of `G`. The
  relation matrix lives in `G`, so the right notion of "same" is `rhs • a`.
  Distinct group elements imply distinct integers (`DistinctRHS.rhs_injective`),
  not conversely.

## What is NOT proved here

That gauge-redundant rows harm the solver's kernel is a claim about the linear
algebra the attack runs, not something this file formalizes. The algebraic
content is: same right-hand side ⟹ the difference row has right-hand side `0`
(`relation_sub_zero_of_same_rhsElt`). Also note: over the *point* factor base
the two rows of a translation pair are different vectors (different points);
they are related by translation relations only once the pair-sum classes and
`Δ` are adjoined as columns, as in the table above.

Nothing here is about the Jacobian, `Reduce`, or the 12x12 system: those
produce relations of shape `(*)`. The abstract `translate_of_same_diff` below
restates `MatchingEquationTranslation.matching_solutions_translate_by_delta`
for an arbitrary abelian group, so this file need not import the Jacobian layer.
-/

namespace IndexCalculus

variable {G : Type*} [AddCommGroup G]

/-! ## Relations and right-hand sides -/

/-- A relation: a list of group elements whose sum equals `rhs • a`. For a
matching solve, `rhs = alpha - alpha'` (see `MatchingSolve.toRelation`). -/
structure Relation (a : G) where
  terms : List G
  rhs : ℤ
  sum_eq : terms.sum = rhs • a

/-- The right-hand side as an element of `G`. Two relations are "the same
right-hand side" when this agrees, which is weaker than `rhs` agreeing as
integers (they may differ by a multiple of `ord a`). -/
def Relation.rhsElt {a : G} (r : Relation a) : G := r.rhs • a

/-- Equal integer right-hand sides give equal right-hand-side elements. -/
theorem Relation.rhsElt_eq_of_rhs_eq {a : G} {r₁ r₂ : Relation a}
    (h : r₁.rhs = r₂.rhs) : r₁.rhsElt = r₂.rhsElt := by
  unfold Relation.rhsElt
  rw [h]

/-- **Distinct right-hand sides.** A family of relations whose right-hand-side
*elements* `rhs • a` are pairwise distinct. -/
def DistinctRHS {a : G} {ι : Type*} (r : ι → Relation a) : Prop :=
  Function.Injective (fun i => (r i).rhsElt)

/-- Distinct right-hand-side elements force distinct integer right-hand sides. -/
theorem DistinctRHS.rhs_injective {a : G} {ι : Type*} {r : ι → Relation a}
    (hd : DistinctRHS r) : Function.Injective (fun i => (r i).rhs) := by
  intro i j hij
  exact hd (Relation.rhsElt_eq_of_rhs_eq hij)

/-- **Subtracting two relations subtracts their right-hand sides.** -/
theorem relation_sub_rhs {a : G} (r₁ r₂ : Relation a) :
    r₁.terms.sum - r₂.terms.sum = (r₁.rhs - r₂.rhs) • a := by
  rw [r₁.sum_eq, r₂.sum_eq, sub_smul]

/-- **Same right-hand side ⟹ the difference row has right-hand side `0`.** It
is a `sum = 0` row carrying no `a`-component. -/
theorem relation_sub_zero_of_same_rhsElt {a : G} (r₁ r₂ : Relation a)
    (h : r₁.rhsElt = r₂.rhsElt) :
    r₁.terms.sum - r₂.terms.sum = 0 := by
  rw [r₁.sum_eq, r₂.sum_eq]
  exact sub_eq_zero.mpr h

/-- Under `DistinctRHS`, distinct indices have distinct right-hand-side
elements, so the difference row's right-hand side is nonzero in `G`. -/
theorem sub_rhsElt_ne_zero_of_distinctRHS {a : G} {ι : Type*} {r : ι → Relation a}
    (hd : DistinctRHS r) {i j : ι} (hij : i ≠ j) :
    (r i).rhsElt - (r j).rhsElt ≠ 0 := by
  intro h
  exact hij (hd (sub_eq_zero.mp h))

/-- Integer form: distinct indices give `rhs_i - rhs_j ≠ 0` in `ℤ`. -/
theorem sub_rhs_ne_zero_of_distinctRHS {a : G} {ι : Type*} {r : ι → Relation a}
    (hd : DistinctRHS r) {i j : ι} (hij : i ≠ j) :
    (r i).rhs - (r j).rhs ≠ 0 := by
  intro h
  exact hij (hd.rhs_injective (sub_eq_zero.mp h))

/-! ## Abstract translation algebra (no Jacobian needed) -/

/-- **Translated pair-sums have the same difference.** Type 1's row identity at
the level of group elements: `A = A' + Δ`, `B = B' + Δ` gives `A - B = A' - B'`
(the `Δ` cancels: `-1 + 1 = 0`). -/
theorem diff_eq_of_translate (A B A' B' Δ : G)
    (hA : A = A' + Δ) (hB : B = B' + Δ) : A - B = A' - B' := by
  rw [hA, hB]
  abel

/-- **The row identity, as an `abel` fact.** `row 1 - row 2 = t₁ - t₂`, i.e.
`(A - B) - (A' - B') = (A - (A' + Δ)) - (B - (B' + Δ))`, for arbitrary
elements, no hypotheses. Being an identity in the free abelian group on
`A, B, A', B', Δ`, it is exactly the coefficient-vector computation
`(1,-1,-1,1,0) = (1,0,-1,0,-1) - (0,1,0,-1,-1)`. -/
theorem translation_rows_differ_by_translation_relations (A B A' B' Δ : G) :
    (A - B) - (A' - B') = (A - (A' + Δ)) - (B - (B' + Δ)) := by
  abel

/-- Same four-point difference ⟹ pair-sums differ by a common `Δ`. Abstract
form of `matching_solutions_translate_by_delta`. -/
theorem translate_of_same_diff (P1 P2 P3 P4 P1' P2' P3' P4' : G)
    (h : P1 + P2 - P3 - P4 = P1' + P2' - P3' - P4') :
    ∃ Δ : G, P1 + P2 = P1' + P2' + Δ ∧ P3 + P4 = P3' + P4' + Δ := by
  refine ⟨(P1 + P2) - (P1' + P2'), by abel, ?_⟩
  rw [← sub_eq_zero]
  have hre : P3 + P4 - (P3' + P4' + ((P1 + P2) - (P1' + P2')))
      = (P1' + P2' - P3' - P4') - (P1 + P2 - P3 - P4) := by abel
  rw [hre, ← h, sub_self]

/-- Common translation of both pair-sums ⟹ same four-point difference. -/
theorem same_diff_of_translate (P1 P2 P3 P4 P1' P2' P3' P4' Δ : G)
    (hA : P1 + P2 = P1' + P2' + Δ) (hB : P3 + P4 = P3' + P4' + Δ) :
    P1 + P2 - P3 - P4 = P1' + P2' - P3' - P4' := by
  calc P1 + P2 - P3 - P4 = (P1 + P2) - (P3 + P4) := by abel
    _ = (P1' + P2') - (P3' + P4') := diff_eq_of_translate _ _ _ _ Δ hA hB
    _ = P1' + P2' - P3' - P4' := by abel

/-! ## Matching solves, their relations, and the two gauge types -/

/-- A solve of eq 1 at `(alpha, alpha')`: four group elements (the classes of
the four points) with `P1 + P2 - P3 - P4 = (alpha - alpha') • a`. -/
structure MatchingSolve (a : G) where
  alpha : ℤ
  alpha' : ℤ
  P1 : G
  P2 : G
  P3 : G
  P4 : G
  eq1 : P1 + P2 - P3 - P4 = (alpha - alpha') • a

/-- The relation a solve produces. **Its right-hand side is `alpha - alpha'`.** -/
def MatchingSolve.toRelation {a : G} (s : MatchingSolve a) : Relation a where
  terms := [s.P1, s.P2, -s.P3, -s.P4]
  rhs := s.alpha - s.alpha'
  sum_eq := by
    rw [← s.eq1]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    abel

theorem MatchingSolve.toRelation_rhs {a : G} (s : MatchingSolve a) :
    s.toRelation.rhs = s.alpha - s.alpha' := rfl

/-- The relation's right-hand-side element is the four-point sum. -/
theorem MatchingSolve.toRelation_rhsElt {a : G} (s : MatchingSolve a) :
    s.toRelation.rhsElt = s.P1 + s.P2 - s.P3 - s.P4 := s.eq1.symm

/-- **Gauge type 2.** Shift `(alpha, alpha') ↦ (alpha + c, alpha' + c)`, keeping
the points fixed. -/
def MatchingSolve.shift {a : G} (s : MatchingSolve a) (c : ℤ) : MatchingSolve a where
  alpha := s.alpha + c
  alpha' := s.alpha' + c
  P1 := s.P1
  P2 := s.P2
  P3 := s.P3
  P4 := s.P4
  eq1 := by
    rw [s.eq1]
    congr 1
    ring

/-- A common shift produces literally the same terms. -/
theorem MatchingSolve.shift_toRelation_terms {a : G} (s : MatchingSolve a) (c : ℤ) :
    (s.shift c).toRelation.terms = s.toRelation.terms := rfl

/-- A common shift produces the same right-hand side: the shifts cancel. -/
theorem MatchingSolve.shift_toRelation_rhs {a : G} (s : MatchingSolve a) (c : ℤ) :
    (s.shift c).toRelation.rhs = s.toRelation.rhs := by
  show (s.alpha + c) - (s.alpha' + c) = s.alpha - s.alpha'
  ring

/-- **Why keying on `alpha` was wrong.** A nonzero shift changes `alpha`, so an
`alpha`-keyed distinctness check accepts the shifted duplicate as new. -/
theorem MatchingSolve.shift_alpha_ne {a : G} (s : MatchingSolve a) {c : ℤ}
    (hc : c ≠ 0) : (s.shift c).alpha ≠ s.alpha := by
  show s.alpha + c ≠ s.alpha
  omega

/-- Two solves are **gauge-related** when their pair-sums are translates of one
another by a single common `Δ` (gauge type 1; type 2 is the case of equal
points). -/
def GaugeRelated {a : G} (s₁ s₂ : MatchingSolve a) : Prop :=
  ∃ Δ : G, s₁.P1 + s₁.P2 = s₂.P1 + s₂.P2 + Δ ∧ s₁.P3 + s₁.P4 = s₂.P3 + s₂.P4 + Δ

/-- **Gauge-relatedness is exactly "same right-hand side".** -/
theorem gaugeRelated_iff_same_rhsElt {a : G} (s₁ s₂ : MatchingSolve a) :
    GaugeRelated s₁ s₂ ↔ s₁.toRelation.rhsElt = s₂.toRelation.rhsElt := by
  simp only [MatchingSolve.toRelation_rhsElt]
  unfold GaugeRelated
  constructor
  · rintro ⟨Δ, hA, hB⟩
    exact same_diff_of_translate _ _ _ _ _ _ _ _ Δ hA hB
  · intro h
    exact translate_of_same_diff _ _ _ _ _ _ _ _ h

/-- A common shift is gauge-related to the original (with `Δ = 0`). -/
theorem MatchingSolve.gaugeRelated_shift {a : G} (s : MatchingSolve a) (c : ℤ) :
    GaugeRelated s (s.shift c) :=
  ⟨0, (add_zero _).symm, (add_zero _).symm⟩

/-- **Gauge-related solves subtract to a `sum = 0` row.** -/
theorem toRelation_sub_zero_of_gaugeRelated {a : G} {s₁ s₂ : MatchingSolve a}
    (h : GaugeRelated s₁ s₂) :
    s₁.toRelation.terms.sum - s₂.toRelation.terms.sum = 0 :=
  relation_sub_zero_of_same_rhsElt _ _ ((gaugeRelated_iff_same_rhsElt s₁ s₂).1 h)

/-- **`DistinctRHS` excludes both gauge types at once.** In a family of solves
whose relations have distinct right-hand-side elements, no two distinct
members are gauge-related. -/
theorem not_gaugeRelated_of_distinctRHS {a : G} {ι : Type*} {s : ι → MatchingSolve a}
    (hd : DistinctRHS (fun i => (s i).toRelation)) {i j : ι} (hij : i ≠ j) :
    ¬ GaugeRelated (s i) (s j) :=
  fun h => hij (hd ((gaugeRelated_iff_same_rhsElt (s i) (s j)).1 h))

/-! ## Deduplication by right-hand side loses no rank

The point of the gauge-redundancy facts above: a relation `r₂` sharing its
`rhsElt` with some already-kept relation `r₁` contributes nothing a linear
solve needs beyond `r₁` — their difference is a `sum = 0` row, a pure
syzygy, not a new equation tying factor-base logs to a nonzero target. So a
family can be deduplicated down to *one relation per distinct `rhsElt`*
without losing any `rhsElt` the original family realized. This is the
precise sense in which "at most one usable relation per right-hand side" is
already fully justified by `gaugeRelated_iff_same_rhsElt` — no bound on how
many point-quadruples share a `Δ`, and no Sidon/second-moment input, is
needed for this claim; it is about redundancy of rows, not cardinality of
fibers. -/

/-- **A relation whose `rhsElt` is realized is gauge-redundant with some
member of a chosen representative sub-family, if that sub-family already
realizes the same `rhsElt`.** Precisely: given a target family `s : ι →
MatchingSolve a` and a representative `s' : ι → MatchingSolve a` (e.g. `s`
restricted to one index per distinct `rhsElt`) such that every `rhsElt` `s`
realizes is also realized by `s'`, every solve in `s` is gauge-related to
some solve in `s'`, hence its relation differs from that representative's
by a zero row. This is `gaugeRelated_iff_same_rhsElt` applied pointwise; the
content is packaging, not new algebra. -/
theorem exists_gaugeRelated_repr_of_rhsElt_mem {a : G} {ι ι' : Type*}
    (s : ι → MatchingSolve a) (s' : ι' → MatchingSolve a)
    (hcover : ∀ i : ι, ∃ i' : ι', (s' i').toRelation.rhsElt = (s i).toRelation.rhsElt)
    (i : ι) :
    ∃ i' : ι', GaugeRelated (s i) (s' i') ∧
      (s i).toRelation.terms.sum - (s' i').toRelation.terms.sum = 0 := by
  obtain ⟨i', hi'⟩ := hcover i
  refine ⟨i', (gaugeRelated_iff_same_rhsElt (s i) (s' i')).2 hi'.symm, ?_⟩
  exact relation_sub_zero_of_same_rhsElt _ _ hi'.symm

/-- **Deduplicating by `rhsElt` preserves every realized right-hand side,
and every discarded relation is gauge-redundant with the kept one.** Given
any family `s : ι → MatchingSolve a`, pick a section `rep : G → ι` of
`rhsElt ∘ s` over its image (i.e. for every realized target `g`, `rep g` is
some index whose relation has `rhsElt = g` — this is just "choose one
representative per right-hand side," available by choice since the image is
a set of realized targets, no further hypothesis needed beyond `s i₀`
witnessing `g` is realized). Then every `i : ι` is gauge-related to the
chosen representative `rep ((s i).toRelation.rhsElt)` for its own
right-hand side, so the deduplicated family `fun g => s (rep g)`
(ranging over the realized right-hand sides `g`) realizes the same set of
right-hand sides as `s` and every discarded solve differs from its kept
representative by a zero row. -/
theorem dedup_by_rhsElt_loses_no_rhs {a : G} {ι : Type*} (s : ι → MatchingSolve a)
    (rep : G → ι) (hrep : ∀ i : ι, (s (rep ((s i).toRelation.rhsElt))).toRelation.rhsElt =
      (s i).toRelation.rhsElt) (i : ι) :
    GaugeRelated (s i) (s (rep ((s i).toRelation.rhsElt))) ∧
      (s i).toRelation.terms.sum -
        (s (rep ((s i).toRelation.rhsElt))).toRelation.terms.sum = 0 := by
  have h := hrep i
  refine ⟨(gaugeRelated_iff_same_rhsElt (s i) (s (rep ((s i).toRelation.rhsElt)))).2 h.symm, ?_⟩
  exact relation_sub_zero_of_same_rhsElt _ _ h.symm

end IndexCalculus
