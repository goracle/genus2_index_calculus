import Mathlib
set_option linter.style.header false

/-!
# Index calculus complexity: the balance `B ~ p^(2/5)`, total cost `p^(4/5)`

This file states the complexity derivation in the form the attack actually
runs, and deliberately does NOT go through `Complexity.lean` (which is built
on the Sidon / second-moment machinery and a per-relation hit rate
`B⁴/(c·N)`; none of that is used here).

## The model

* The factor base has `B` elements, living in the cryptographic subgroup
  `<a>` of order `~ p²`.
* **One solve** succeeds (yields a usable relation) with expected probability
  `B⁴ / p²`.
* We run `N` solves, so the expected number of relations is `N · B⁴ / p²`.
* We need `~ B` relations (the constant, `2B` in the implementation, does not
  affect the exponent), giving the solve budget `N ~ p² / B³`.
* Sparse linear algebra over the `B`-element factor base costs `~ B²`.
* Balancing `N ~ B²` gives `B² ~ p² / B³`, i.e. `B⁵ ~ p²`, `B ~ p^(2/5)`, and
  total cost `B² ~ p^(4/5)`.

## What is assumed, and what is not

Assumed, as named hypotheses (not proved here):

* the per-solve success probability `B⁴/p²` — this is `hRate` below, an
  algebraic input to the expected-relations count, not a derived fact;
* that `~ B` relations suffice to solve the discrete log (standard
  index-calculus assumption, `RelationsRequired` in `Complexity.lean`);
* that the residual chain that supplies the first `~ B/2` relations does not
  revisit points, and that different relations have different right-hand
  sides. Both are modeled in the file that defines a relation, not here.

Everything in this file is real-number algebra on top of those inputs.
-/

open Real

/-- **Expected number of relations from `N` solves**, each succeeding with
expected probability `B⁴/p²`. Pure bookkeeping: linearity of expectation. -/
noncomputable def expectedRelations (N B p : ℝ) : ℝ := N * (B ^ 4 / p ^ 2)

/-- **The solve budget that yields `B` relations.** If `N` solves are run
and `B⁵ = p²`, then `N = B²` solves yield exactly `B` expected relations:
`B² · B⁴ / p² = B⁶ / B⁵ = B`. -/
theorem expectedRelations_at_balance
    (B p : ℝ) (hB : 0 < B) (hp : 0 < p) (hbal : B ^ 5 = p ^ 2) :
    expectedRelations (B ^ 2) B p = B := by
  unfold expectedRelations
  have hp2 : p ^ 2 = B ^ 5 := hbal.symm
  have hB' : B ≠ 0 := ne_of_gt hB
  rw [hp2]
  field_simp

/-- **The balance equation.** Requiring `N` solves to produce `B` relations
(`N · B⁴ / p² = B`) and to equal the linear-algebra cost `B²` forces
`B⁵ = p²`. This is the "solve this: `B² ~ p²/B³`" step, as an implication. -/
theorem balance_forces_fifth_power
    (B p : ℝ) (hB : 0 < B) (hp : 0 < p)
    (hrel : expectedRelations (B ^ 2) B p = B) :
    B ^ 5 = p ^ 2 := by
  unfold expectedRelations at hrel
  have hp2 : p ^ 2 ≠ 0 := by positivity
  have hB' : B ≠ 0 := ne_of_gt hB
  -- `hrel : B ^ 2 * (B ^ 4 / p ^ 2) = B`. Clear the denominator, then cancel
  -- one factor of `B` explicitly (`mul_left_cancel₀`), rather than hoping a
  -- tactic does it.
  have h6 : B ^ 6 = B * p ^ 2 := by
    have hstep : B ^ 2 * (B ^ 4 / p ^ 2) * p ^ 2 = B * p ^ 2 := by rw [hrel]
    have hcancel : B ^ 4 / p ^ 2 * p ^ 2 = B ^ 4 := by
      field_simp
    calc B ^ 6 = B ^ 2 * B ^ 4 := by ring
      _ = B ^ 2 * (B ^ 4 / p ^ 2 * p ^ 2) := by rw [hcancel]
      _ = B ^ 2 * (B ^ 4 / p ^ 2) * p ^ 2 := by ring
      _ = B * p ^ 2 := hstep
  have h5 : B * B ^ 5 = B * p ^ 2 := by
    calc B * B ^ 5 = B ^ 6 := by ring
      _ = B * p ^ 2 := h6
  exact mul_left_cancel₀ hB' h5

/-- **`B = p^(2/5)` exactly when `B⁵ = p²`.** The exponent, as a real-power
statement. -/
theorem B_eq_rpow_of_fifth_power
    (B p : ℝ) (hB : 0 < B) (hp : 0 < p) (hbal : B ^ 5 = p ^ 2) :
    B = p ^ ((2 : ℝ) / 5) := by
  -- Same shape as `Complexity.lean`'s `hBeq` (REPL-tested there): write
  -- `B = (B ^ 5) ^ (1/5)` by turning `B ^ 5` into an `rpow` and using
  -- `rpow_mul`, then substitute `B ^ 5 = p ^ 2` and repeat for `p ^ 2`.
  have hB5 : B = ((B : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
    rw [← Real.rpow_natCast (B : ℝ) 5, ← Real.rpow_mul (le_of_lt hB)]
    norm_num [Real.rpow_one]
  calc B = ((B : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := hB5
    _ = ((p : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 5) := by rw [hbal]
    _ = p ^ ((2 : ℝ) / 5) := by
        rw [← Real.rpow_natCast (p : ℝ) 2, ← Real.rpow_mul (le_of_lt hp)]
        norm_num

/-- **The total cost is `B² = p^(4/5)`.** With `N = B²` solves (equal, at the
balance, to the linear-algebra cost), the total work is `B²`, and `B² = p^(4/5)`
when `B = p^(2/5)`. -/
theorem total_cost_eq_rpow
    (B p : ℝ) (hB : 0 < B) (hp : 0 < p) (hbal : B ^ 5 = p ^ 2) :
    B ^ 2 = p ^ ((4 : ℝ) / 5) := by
  have hBeq := B_eq_rpow_of_fifth_power B p hB hp hbal
  calc B ^ 2 = (p ^ ((2 : ℝ) / 5)) ^ (2 : ℕ) := by rw [hBeq]
    _ = p ^ ((4 : ℝ) / 5) := by
        rw [← Real.rpow_natCast (p ^ ((2 : ℝ) / 5)) 2, ← Real.rpow_mul (le_of_lt hp)]
        norm_num

/-- **The whole derivation, in one statement.** Given `B⁵ = p²`, running
`N = B²` solves at per-solve rate `B⁴/p²` yields `B` relations in expectation,
and the total cost `B²` equals `p^(4/5)`. -/
theorem index_calculus_complexity
    (B p : ℝ) (hB : 0 < B) (hp : 0 < p) (hbal : B ^ 5 = p ^ 2) :
    expectedRelations (B ^ 2) B p = B ∧ B ^ 2 = p ^ ((4 : ℝ) / 5) :=
  ⟨expectedRelations_at_balance B p hB hp hbal, total_cost_eq_rpow B p hB hp hbal⟩
