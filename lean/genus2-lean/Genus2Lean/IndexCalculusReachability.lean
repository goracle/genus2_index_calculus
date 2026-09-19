import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.IndexCalculusHitRate
set_option linter.style.header false

/-!
# Reachability: existence of a factor-base witness is not the same as the
# solver returning one

`IndexCalculusHitRate.lean` makes `hRate` precise as `HitRate F c`, a statement
about *existence*: at least a `B⁴/(c·|G|)` fraction of targets `Δ` have some
quadruple in `F⁴` with `P1 + P2 - P3 - P4 = Δ` (`matchCount F Δ ≠ 0`).

That is not what one solve delivers. A solve at `(α, α')` runs the square
12-equation system over the whole Jacobian, and factor-base membership is
checked *afterwards* (via the `O(B²)` log table). The system does not know
about `F`. At `Δ = α - α'` it returns one element of its full solution set
`Sol Δ ⊆ G⁴` (the finite variety `ZeroD/` bounds), and the solve is usable only
if that element lies in `F⁴`. So the per-solve success probability at `Δ` is

    q Δ  =  Pr[ the returned solution ∈ F⁴ ]

and `matchCount F Δ ≠ 0` only says `Sol Δ ∩ F⁴ ≠ ∅`, which is necessary for
`q Δ > 0` but nowhere near sufficient for `q Δ` to be large.

## What this file does

* `SolverReaches F d q` — the reachability hypothesis, as ONE named `Prop`:
  for every `Δ ≠ 0`, `matchCount F Δ ≤ d * q Δ`. Reading: `q Δ ≥ matchCount F Δ / d`.
  This is exactly what a solver returning a uniformly random element of a
  solution set of size `≤ d` would satisfy, since then
  `q Δ = |Sol Δ ∩ F⁴| / |Sol Δ| ≥ matchCount F Δ / d`.
  It is the ONLY place the `ZeroD/` uniform degree `d` enters the model.
* `expected_success_mass_ge` — from `SolverReaches`, the total success mass
  `∑_{Δ≠0} q Δ` is at least `(B⁴ - matchCount F 0) / d`. Pure double counting
  on top of `sum_matchCount_ne_zero_eq`; no Sidon, no second moment.
* `expected_successes_ge` — for a uniformly random `Δ`, the expected success
  probability of one solve is at least `(B⁴ - matchCount F 0) / (d · |G|)`.
  With `|G| = p²` this is `~ B⁴/(d p²)`: the model's `hRate` with a `1/d` loss.

## What is NOT proved here, and is genuinely open

* `SolverReaches` itself. It is a hypothesis about the solver, not a theorem.
  Two independent things would have to hold: (i) `|Sol Δ| ≤ d` uniformly
  (the `ZeroD/` degree bound, itself conditional on `GenericPeelChainHyp`),
  and (ii) the returned element is not adversarially biased away from `F⁴`
  (a uniform-pick heuristic). Neither is derived from the other.
* Nothing here says `Sol Δ ∩ F⁴` is reached when `Sol Δ` is large, i.e. this
  file makes the `1/d` loss explicit but cannot beat it.
* `q` is left abstract. This file does not model how `(α, α')` induces `Δ`, nor
  independence across solves.

## Why `SolverReaches` is stated as a cap, not as an equality

Equality `q Δ = matchCount F Δ / |Sol Δ|` would need `|Sol Δ|` as a second
function and its own hypotheses. The inequality `matchCount F Δ ≤ d * q Δ`
is all the accounting needs and is implied by that equality whenever
`|Sol Δ| ≤ d`.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **The reachability hypothesis.** `q Δ` is the probability that a solve
targeting `Δ` returns a quadruple in `F⁴`. `SolverReaches F d q` says that, off
`Δ = 0`, `q` is at least `matchCount F Δ / d`: the solver reaches a factor-base
witness with probability at least a `1/d` share of the witnesses that exist.
`d` is the uniform solution-set bound (`ZeroD/`'s degree bound). -/
def SolverReaches (F : Finset G) (d : ℕ) (q : G → ℝ) : Prop :=
  ∀ Δ : G, Δ ≠ 0 → (matchCount F Δ : ℝ) ≤ (d : ℝ) * q Δ

/-- **Total success mass, from reachability.** Summing `SolverReaches` over
`Δ ≠ 0` and using the exact nonzero-`Δ` mass `B⁴ - matchCount F 0` gives
`B⁴ - matchCount F 0 ≤ d · ∑_{Δ≠0} q Δ`. No Sidon, no second moment. -/
theorem expected_success_mass_ge (F : Finset G) (d : ℕ) (q : G → ℝ)
    (hreach : SolverReaches F d q) :
    ((F.card ^ 4 - matchCount F 0 : ℕ) : ℝ) ≤
      (d : ℝ) * ∑ Δ ∈ Finset.univ.filter (fun Δ : G => Δ ≠ 0), q Δ := by
  have hsum := sum_matchCount_ne_zero_eq F
  have hcast : ((F.card ^ 4 - matchCount F 0 : ℕ) : ℝ) =
      ∑ Δ ∈ Finset.univ.filter (fun Δ : G => Δ ≠ 0), (matchCount F Δ : ℝ) := by
    rw [← hsum]
    push_cast
    rfl
  rw [hcast, Finset.mul_sum]
  exact Finset.sum_le_sum (fun Δ hΔ => hreach Δ (Finset.mem_filter.mp hΔ).2)

/-- The `Δ = 0` term is at most `B³`, hence at most half of `B⁴` once `B ≥ 2`,
so the nonzero mass `B⁴ - matchCount F 0` is at least `B⁴ / 2`. -/
theorem nonzero_mass_ge_half (F : Finset G) (hB : 2 ≤ F.card) :
    F.card ^ 4 ≤ 2 * (F.card ^ 4 - matchCount F 0) := by
  have hm0 : matchCount F 0 ≤ F.card ^ 3 := matchCount_le_card_cubed F 0
  have h4 : 2 * F.card ^ 3 ≤ F.card ^ 4 := by
    calc 2 * F.card ^ 3 ≤ F.card * F.card ^ 3 := Nat.mul_le_mul hB (le_refl _)
      _ = F.card ^ 4 := by ring
  omega

/-- **Expected success probability of one solve at a uniformly random target.**
Under `SolverReaches F d q` with `d > 0` and `B ≥ 2`, the average of `q` over
`Δ ∈ G` is at least `B⁴ / (2 · d · |G|)`. This is `hRate` with two explicit
losses: `1/d` for reachability and `1/2` for discarding `Δ = 0`. -/
theorem expected_successes_ge (F : Finset G) (d : ℕ) (hd : 0 < d) (q : G → ℝ)
    (hq : ∀ Δ : G, 0 ≤ q Δ) (hB : 2 ≤ F.card)
    (hreach : SolverReaches F d q) :
    (F.card : ℝ) ^ 4 / (2 * (d : ℝ) * (Fintype.card G : ℝ)) ≤
      (∑ Δ : G, q Δ) / (Fintype.card G : ℝ) := by
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmass := expected_success_mass_ge F d q hreach
  have hhalf : (F.card : ℝ) ^ 4 ≤ 2 * ((F.card ^ 4 - matchCount F 0 : ℕ) : ℝ) := by
    exact_mod_cast nonzero_mass_ge_half F hB
  -- the sum over nonzero Δ is at most the full sum, since q ≥ 0
  have hsub : ∑ Δ ∈ Finset.univ.filter (fun Δ : G => Δ ≠ 0), q Δ ≤ ∑ Δ : G, q Δ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun Δ _ _ => hq Δ)
  have h1 : (F.card : ℝ) ^ 4 ≤ 2 * ((d : ℝ) * ∑ Δ : G, q Δ) := by
    calc (F.card : ℝ) ^ 4 ≤ 2 * ((F.card ^ 4 - matchCount F 0 : ℕ) : ℝ) := hhalf
      _ ≤ 2 * ((d : ℝ) * ∑ Δ ∈ Finset.univ.filter (fun Δ : G => Δ ≠ 0), q Δ) :=
          mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ ≤ 2 * ((d : ℝ) * ∑ Δ : G, q Δ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub hdR.le) (by norm_num)
  rw [div_le_div_iff₀ (by positivity) hN]
  calc (F.card : ℝ) ^ 4 * (Fintype.card G : ℝ)
      ≤ (2 * ((d : ℝ) * ∑ Δ : G, q Δ)) * (Fintype.card G : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hN.le
    _ = (∑ Δ : G, q Δ) * (2 * (d : ℝ) * (Fintype.card G : ℝ)) := by ring
