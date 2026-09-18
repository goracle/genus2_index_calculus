import Mathlib
set_option linter.style.header false

/-!
# What a relation is, and why gauge-shifted duplicates are not wanted

`IndexCalculusComplexity.lean` counts solves. This file fixes what one solve
*produces*, so that "a relation" and "the right-hand side of a relation" are
Lean objects and the requirement that relations have DIFFERENT right-hand
sides is a definition, not prose.

## The model

`G` is the cryptographic subgroup `<a>`. A **relation** is a finite formal sum
of factor-base elements together with a right-hand side `alpha • a`:

    (sum of factor-base terms) = alpha • a          (*)

Two relations with the same right-hand side, subtracted, give a row

    (sum of factor-base terms) = 0

whose right-hand side carries no information about the target divisor. That
is what a gauge-shifted duplicate is: same points, shifted `alpha`, and the
shift lands on both sides identically. Such a row can only put a vector into
the kernel of the relation matrix that does not point toward the target, so
the implementation asks for pairwise distinct right-hand sides.

Nothing here is about the Jacobian, `Reduce`, or the 12x12 system: those
produce relations of shape `(*)`, and this file only says what to do with
them once they exist.
-/

namespace IndexCalculus

variable {G : Type*} [AddCommGroup G]

/-- A relation: a list of factor-base elements whose sum, in `G`, equals
`alpha • a`. The list is data (which factor-base elements, with repetition);
`alpha` is the right-hand side's coefficient of the base element `a`. -/
structure Relation (a : G) where
  terms : List G
  alpha : ℤ
  sum_eq : terms.sum = alpha • a

/-- The right-hand-side coefficient of a relation. -/
def Relation.rhs {a : G} (r : Relation a) : ℤ := r.alpha

/-- **Distinct right-hand sides.** A family of relations has pairwise
distinct right-hand-side coefficients. This is the property the
implementation wants of the relation set. -/
def DistinctRHS {a : G} {ι : Type*} (r : ι → Relation a) : Prop :=
  Function.Injective (fun i => (r i).alpha)

/-- **Subtracting two relations subtracts their right-hand sides.** The row
`r₁ - r₂` has right-hand side `(alpha₁ - alpha₂) • a`. -/
theorem relation_sub_rhs {a : G} (r₁ r₂ : Relation a) :
    r₁.terms.sum - r₂.terms.sum = (r₁.alpha - r₂.alpha) • a := by
  rw [r₁.sum_eq, r₂.sum_eq, sub_smul]

/-- **A gauge-shifted duplicate has right-hand-side difference zero.** If two
relations have the same `alpha`, their difference row has right-hand side `0`:
it is a relation `(sum of factor-base terms) = 0` and carries no information
about the target. -/
theorem relation_sub_rhs_zero_of_same_alpha {a : G} (r₁ r₂ : Relation a)
    (h : r₁.alpha = r₂.alpha) :
    r₁.terms.sum - r₂.terms.sum = 0 := by
  rw [relation_sub_rhs, h, sub_self, zero_smul]

/-- **Under `DistinctRHS`, no two distinct relations in the family have
equal right-hand sides.** The contrapositive form used when building the
relation matrix: distinct indices give distinct `alpha`, so the difference
row's right-hand side coefficient `alpha_i - alpha_j` is nonzero as an
integer. -/
theorem sub_alpha_ne_zero_of_distinctRHS {a : G} {ι : Type*} {r : ι → Relation a}
    (hd : DistinctRHS r) {i j : ι} (hij : i ≠ j) :
    (r i).alpha - (r j).alpha ≠ 0 := by
  intro h
  exact hij (hd (sub_eq_zero.mp h))

end IndexCalculus
