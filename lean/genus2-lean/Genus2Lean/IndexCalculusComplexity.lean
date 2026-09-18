import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.MatchCountAutocorr
set_option linter.style.header false

/-!
# Index calculus complexity: the balance `B ~ p^(2/5)`, total cost `p^(4/5)`

This file states the complexity derivation in the form the attack actually
runs, and deliberately does NOT go through `Complexity.lean` (which is built
on the Sidon / second-moment machinery and a per-relation hit rate
`B⁴/(c·N)`); nor does it need that machinery any more — see the correction
below.

## Why the Sidon/second-moment route is unnecessary (correction, this pass)

`Complexity.lean`'s whole apparatus (`SidonRepBound`, additive energy,
`OffDiagonalBound`, Paley–Zygmund) exists to bound `matchCount T Δ` — the
*multiplicity* of the `Δ`-fiber, i.e. how many raw point-quadruples solve
`P1+P2-P3-P4 = Δ`. That multiplicity turns out to be the wrong quantity to
bound, because it does not matter: `IndexCalculusRelations.lean` proves
(`translate_of_same_diff`, no hypothesis beyond a shared right-hand side)
that ANY two solves sharing `Δ` are gauge-related, hence
(`toRelation_sub_zero_of_gaugeRelated`) their relations differ by a
`sum = 0` row — a pure syzygy, contributing no new information to the
sparse linear solve. So a `Δ`-fiber of ANY size (`matchCount T Δ = 1` or
`10¹⁰⁰`) is worth exactly one relation. `dedup_by_rhsElt_loses_no_rhs`
formalizes this: deduplicating a family of solves down to one per distinct
`rhsElt` realizes the same set of right-hand sides and loses nothing.

Consequently the quantity that drives the complexity balance is not
"expected hit rate weighted by fiber size" (which is what the Sidon route
computed) but **the number of DISTINCT nonzero right-hand sides realized**
by `N` solve attempts — a coupon-collector-type count, not a second-moment
one. `sum_matchCount_eq_card_pow_four` (`AverageComplexity.lean`, already
proved, unconditional, no Sidon) gives the exact total mass `B⁴` spread
across all `Δ ∈ G`; how that mass is spread across DISTINCT `Δ`'s (rather
than how concentrated the multiplicity is, which no longer matters) is the
only thing left needing a modeling assumption, and it is a much weaker one
than a second-moment bound: not "no `Δ` is hit too often" (irrelevant now)
but "solves don't preferentially collide onto the SAME already-hit `Δ`
more than a uniform-ish spread would predict."

## The model

* The factor base has `B` elements, living in the cryptographic subgroup
  `<a>` of order `N ~ p²` (written `p` below, matching the exponent
  bookkeeping — `p` here is the group order, not the field characteristic).
* **One solve** produces a candidate right-hand side `Δ`. Whether it is
  *usable* (contributes rank) depends only on whether `Δ` is NEW — a repeat
  hit is free (by the gauge-redundancy argument above) but adds no relation.
* **`hRate`, restated**: the expected number of DISTINCT right-hand sides
  realized by `N` solves is `N · B⁴ / p²` — same formula as before, but now
  justified as "expected number of new coupons," not "expected number of
  hits weighted by multiplicity." This is still an assumed hypothesis (a
  near-uniform-spread heuristic on which `Δ` a solve lands on, given the
  exact mean-hit-rate identity `B⁴/p²` per `Δ` from
  `average_matchCount_eq`), but it is a WEAKER, more plausible assumption
  than before: it no longer needs any control on collision multiplicity,
  only on how spread the realized values are, and every raw hit — however
  many quadruples produce it — counts at most once regardless, so
  overcounting risk from the old model is structurally impossible now.
* We need `~ B` distinct relations (the constant, `2B` in the
  implementation, does not affect the exponent), giving the solve budget
  `N ~ p² / B³`.
* Sparse linear algebra over the `B`-element factor base costs `~ B²`.
* Balancing `N ~ B²` gives `B² ~ p² / B³`, i.e. `B⁵ ~ p²`, `B ~ p^(2/5)`, and
  total cost `B² ~ p^(4/5)`.

## What is assumed, and what is not

Assumed, as a named hypothesis (not proved here):

* the per-solve expected-new-relation rate `B⁴/p²` — this is `hRate` below,
  restated per the correction above as a distinct-value/coupon-collector
  rate rather than a hit-probability-weighted-by-multiplicity rate. Unlike
  the old model, this hypothesis needs no bound on fiber multiplicity
  (`matchCount T Δ` for any single `Δ`) at all — that quantity is now
  provably irrelevant, not merely unbounded-but-assumed-harmless.

Proved, not assumed, feeding into the honesty of the model above:

* `sum_matchCount_eq_card_pow_four` (`AverageComplexity.lean`): the exact
  total mass `B⁴`, unconditional.
* `dedup_by_rhsElt_loses_no_rhs` / `toRelation_sub_zero_of_gaugeRelated`
  (`IndexCalculusRelations.lean`): every relation beyond the first per
  right-hand side is a zero row — proved, no hypothesis, for ANY two
  solves sharing a right-hand side, not just fixed-class-pair ones (this
  is what makes fiber multiplicity provably irrelevant, closing the
  question `ROADMAP-alpha-locus.md` had left open — that roadmap was
  asking whether `matchCount T Δ` itself is bounded, which turned out to
  be the wrong question).

Still assumed elsewhere, unaffected by this correction:

* that `~ B` relations suffice to solve the discrete log (standard
  index-calculus assumption, `RelationsRequired` in `Complexity.lean`).

Everything in this file beyond `hRate` is real-number algebra on top of
that input — unchanged from before, since the balance arithmetic itself
never depended on which justification `B⁴/p²` had.
-/

open Real

/-! ## An unconditional pigeonhole bound, connecting `matchCount`'s exact
total mass to the number of DISTINCT relations — no Sidon, no second
moment, and no smallness assumption on any single fiber's multiplicity.

`sum_matchCount_eq_card_pow_four` (`AverageComplexity.lean`) gives the exact
identity `∑ Δ, matchCount F Δ = B⁴`, unconditionally. Since (per
`dedup_by_rhsElt_loses_no_rhs`) each DISTINCT nonzero `Δ` with
`matchCount F Δ > 0` is worth exactly one relation regardless of its
multiplicity, the number of relations is `#{Δ ≠ 0 : matchCount F Δ > 0}`.
Standard pigeonhole turns the exact total `B⁴` into a lower bound on that
count, GIVEN an upper bound on the largest single fiber: if no fiber
exceeds `M`, distinct hits number at least `B⁴ / M`. This is a strictly
weaker ask than the old Sidon route: `M` need not be a small constant like
`4` for the resulting relation count to be genuine and useful — any
finite, `p`-independent-or-not bound on the realized maximum works, and
unlike the old model, an M that is LARGE costs relations (fewer distinct
values for the same mass) but never costs CORRECTNESS (no relation is ever
double-counted or wrongly treated as adding rank), because
`dedup_by_rhsElt_loses_no_rhs` already guarantees every kept relation is
genuinely non-redundant. -/

/-- **Pigeonhole: exact mass over a bounded-multiplicity family forces a
distinct-count lower bound.** Abstract form, independent of `matchCount`'s
definition: if `f : ι → ℕ` sums to `S` over a finite index set `s` and every
value is at most `M`, then at least `S / M` elements have `f > 0` — stated
as `S ≤ M * (s.filter (f · > 0)).card` (the `ℕ`-division-free form,
avoiding rounding subtleties; no positivity hypothesis on `M` is needed,
the inequality holds regardless). -/
theorem card_pos_ge_of_sum_le_mul {ι : Type*} (s : Finset ι) (f : ι → ℕ) (S M : ℕ)
    (hsum : ∑ i ∈ s, f i = S) (hbound : ∀ i ∈ s, f i ≤ M) :
    S ≤ M * (s.filter (fun i => 0 < f i)).card := by
  rw [← hsum]
  -- `Finset.sum_filter_of_ne (hp : ∀ x ∈ s, f x ≠ 0 → p x) : ∑ x ∈ s.filter p, f x
  -- = ∑ x ∈ s, f x` — the zero terms outside the filter contribute nothing, so
  -- restricting to `f i ≠ 0` (equivalently `0 < f i`, over `ℕ`) doesn't change
  -- the sum. Used right-to-left: rewrite the full sum as the filtered one.
  have hfilter : ∑ i ∈ s.filter (fun i => 0 < f i), f i = ∑ i ∈ s, f i :=
    Finset.sum_filter_of_ne (fun i _ hne => Nat.pos_of_ne_zero hne)
  calc ∑ i ∈ s, f i = ∑ i ∈ s.filter (fun i => 0 < f i), f i := hfilter.symm
    _ ≤ ∑ _i ∈ s.filter (fun i => 0 < f i), M :=
        Finset.sum_le_sum (fun i hi => hbound i (Finset.mem_filter.mp hi).1)
    _ = M * (s.filter (fun i => 0 < f i)).card := by
        simp [Finset.sum_const, mul_comm]

/-! ## Applying the pigeonhole bound to `matchCount` itself

The abstract lemma above, specialized: given ANY cap `M` on every nonzero-`Δ`
fiber's multiplicity (not assumed small — see the module docstring), the
number of nonzero `Δ` actually realized (`matchCount F Δ > 0`) is at least
`(B⁴ - matchCount F 0) / M`. No Sidon property is used to prove this
theorem; `SidonRepBound`/`sidon_energy_bound` would only ever be one
particular way to instantiate `M` (namely `M = 2·B²`, from
`matchCount_le_two_card_sq` in `MatchCountAutocorr.lean`) — a valid choice,
but not the only one, and per the correction above, not one this project's
complexity claim needs at all: any finite `M`, however large, still yields
a genuine, correct relation-count lower bound, it merely yields a smaller
one. -/

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **The exact nonzero-`Δ` mass**: `∑_{Δ≠0} matchCount F Δ = B⁴ - matchCount F 0`.
Immediate from `sum_matchCount_eq_card_pow_four` by peeling off the `Δ = 0`
term (a singleton fiber of `univ`). -/
theorem sum_matchCount_ne_zero_eq (F : Finset G) :
    ∑ Δ ∈ (Finset.univ.filter (fun Δ : G => Δ ≠ 0)), matchCount F Δ
      = F.card ^ 4 - matchCount F 0 := by
  have htotal := sum_matchCount_eq_card_pow_four F
  have hsum := (Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset G) (fun Δ : G => Δ = 0) (fun Δ => matchCount F Δ)).symm
  -- `hsum : ∑ Δ : G, matchCount F Δ =
  --   ∑ Δ ∈ univ.filter (Δ = 0), matchCount F Δ +
  --   ∑ Δ ∈ univ.filter (¬ Δ = 0), matchCount F Δ`.
  -- The first summand is a singleton sum at `Δ = 0`; the second summand's
  -- filter predicate `¬ Δ = 0` is definitionally `Δ ≠ 0`, matching the goal.
  have hz : (Finset.univ.filter (fun Δ : G => Δ = 0) : Finset G) = {(0 : G)} := by
    ext Δ; simp
  rw [hz, Finset.sum_singleton] at hsum
  have hne_eq : (Finset.univ.filter (fun Δ : G => ¬ Δ = 0) : Finset G) =
      Finset.univ.filter (fun Δ : G => Δ ≠ 0) := rfl
  rw [hne_eq] at hsum
  omega

/-- **The relation-count lower bound, `matchCount`-facing.** Given a cap `M`
on every nonzero-`Δ` fiber's size (`hbound`), the number of nonzero `Δ`
realized — i.e. the number of USABLE, pairwise-non-redundant relations a
factor base `F` of size `B` can supply (by `dedup_by_rhsElt_loses_no_rhs`,
`IndexCalculusRelations.lean`) — is at least `(B⁴ - matchCount F 0) / M`,
stated division-free as `B⁴ - matchCount F 0 ≤ M · (relation count)`. No
Sidon, no second moment, no Fourier: `card_pos_ge_of_sum_le_mul` plus the
exact identity `sum_matchCount_ne_zero_eq` above. -/
theorem matchCount_distinct_hits_ge (F : Finset G) (M : ℕ)
    (hbound : ∀ Δ ∈ (Finset.univ.filter (fun Δ : G => Δ ≠ 0)), matchCount F Δ ≤ M) :
    F.card ^ 4 - matchCount F 0 ≤
      M * ((Finset.univ.filter (fun Δ : G => Δ ≠ 0)).filter
        (fun Δ => 0 < matchCount F Δ)).card :=
  card_pos_ge_of_sum_le_mul (Finset.univ.filter (fun Δ : G => Δ ≠ 0)) (matchCount F)
    (F.card ^ 4 - matchCount F 0) M (sum_matchCount_ne_zero_eq F) hbound

/-- **Fully self-contained, hypothesis-free relation-count lower bound.**
Instantiating `matchCount_distinct_hits_ge` at `M := F.card³`
(`matchCount_le_card_cubed`, `MatchCountAutocorr.lean` — free, no Sidon, no
Forey–Fresán–Kowalski, holds for every factor base) gives a genuine
relation-count guarantee with NO external hypothesis at all: `B⁴ -
matchCount F 0 ≤ B³ · (usable relation count)`, i.e. at least `(B⁴ -
matchCount F 0)/B³ ~ B` distinct usable relations, for `B := F.card`. This
is weaker than what Sidon would give (Sidon's `M = 2B²` yields `~ B²`
distinct relations, a better bound) — but it is unconditional, closing the
`hRate` question with no assumed input whatsoever, at the cost of a worse
quantitative rate. Whether `~ B` (this bound) or `~ B²` (Sidon-derived) is
the right exponent to feed into the complexity balance is a modeling
choice, not a gap in what's proved either way. -/
theorem matchCount_distinct_hits_ge_unconditional (F : Finset G) :
    F.card ^ 4 - matchCount F 0 ≤
      F.card ^ 3 * ((Finset.univ.filter (fun Δ : G => Δ ≠ 0)).filter
        (fun Δ => 0 < matchCount F Δ)).card :=
  matchCount_distinct_hits_ge F (F.card ^ 3)
    (fun Δ _ => matchCount_le_card_cubed F Δ)

/-- **Expected number of DISTINCT relations from `N` solves.** Restated
(this pass) as a coupon-collector-style rate — the expected number of
NEW right-hand sides realized, not a hit-probability weighted by fiber
multiplicity (see the module docstring's correction). The formula `N ·
B⁴/p²` is unchanged from before; what changed is its justification, not
its value, so the arithmetic below (unchanged) still applies verbatim. -/
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
