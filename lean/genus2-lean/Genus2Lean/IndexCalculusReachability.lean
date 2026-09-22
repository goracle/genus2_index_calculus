import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.IndexCalculusHitRate
import Genus2Lean.HitRateSumsetReduction
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
about `F`. At `Δ = (α - α') • a` it returns one element of its full solution
set `Sol Δ ⊆ G⁴` (the finite variety `ZeroD/` bounds), and the solve is usable
only if that element lies in `F⁴`. So the per-solve success probability at `Δ` is

    q Δ  =  Pr[ the returned solution ∈ F⁴ ]

and `matchCount F Δ ≠ 0` only says `Sol Δ ∩ F⁴ ≠ ∅`, which is necessary for
`q Δ > 0` but nowhere near sufficient for `q Δ` to be large.

## Correction, this pass: the solver is never even called at a direct-relation `Δ`

Per Claire: `α`, `α'` range over the arbitrary/free choices that set up a solve
attempt, and `a` is the fixed given generator, with `Δ := (α - α') • a` — this
is exactly `IndexCalculusRelations.lean`'s `Relation.rhsElt` (`r.rhs • a`,
`r.rhs = α - α'`), already on file, just not previously named `Δ` or wired to
`q`. Crucially: before ever invoking the 12-equation solver, the caller first
checks whether `Δ` already splits over the factor base directly —
`HitRateSumsetReduction.lean`'s `DirectRelation F Δ` (`Δ ∈ F - F`, `Δ ∈ F`, or
`Δ ∈ F + F`). If it does, that IS the relation and no solve is attempted at
all. So the solver's domain is not "every `Δ ≠ 0`" as this file previously had
it — it is exactly `goodMatch F Δ := ¬ DirectRelation F Δ`. `SolverReaches`
below is corrected to quantify over `goodMatch F Δ` instead of the coarser
`Δ ≠ 0`, and the downstream mass/expectation theorems are restricted to match.

This reuses `DirectRelation`/`goodMatch` from `HitRateSumsetReduction.lean`
purely as a definition — that file's own `hbad`/Sidon apparatus built on top
of `goodMatch` (Parts 2, 4–5) is still the superseded branch per
`ROADMAP-current.md`'s correction (1); nothing from that apparatus is used
here, only the exclusion predicate itself.

Note `goodMatch F Δ → Δ ≠ 0` whenever `F` is nonempty (`goodMatch_ne_zero`
below: taking `x = y` for any `x ∈ F` gives `Δ = x - x = 0` as a direct
relation, so `Δ = 0` is always excluded once `F ≠ ∅`) — so the old separate
`Δ ≠ 0` exclusion is now subsumed by `goodMatch`, not dropped.

## What this file does

* `SolverReaches F d q` — the reachability hypothesis, as ONE named `Prop`:
  for every `Δ` with `goodMatch F Δ` (i.e. `Δ` is not already a direct
  relation), `matchCount F Δ ≤ d * q Δ`. Reading: `q Δ ≥ matchCount F Δ / d`.
  This is exactly what a solver returning a uniformly random element of a
  solution set of size `≤ d` would satisfy, since then
  `q Δ = |Sol Δ ∩ F⁴| / |Sol Δ| ≥ matchCount F Δ / d`.
  It is the ONLY place the `ZeroD/` uniform degree `d` enters the model.
* `expected_success_mass_ge` — from `SolverReaches`, the total success mass
  `∑_{goodMatch F} q Δ` is at least `(∑_{goodMatch F} matchCount F Δ) / d`.
  Pure double counting; no Sidon, no second moment.
* `expected_successes_ge` — for a uniformly random `Δ`, the expected success
  probability of one solve is at least
  `(∑_{goodMatch F} matchCount F Δ) / (d · |G|)`. This is the model's `hRate`
  with a `1/d` loss, now scoped to the `Δ`'s the solver is ever actually
  asked about.

## What is NOT proved here, and is genuinely open

* `SolverReaches` itself. It is a hypothesis about the solver, not a theorem.
  Two independent things would have to hold: (i) `|Sol Δ| ≤ d` uniformly
  (the `ZeroD/` degree bound, itself conditional on `GenericPeelChainHyp`),
  and (ii) the returned element is not adversarially biased away from `F⁴`
  (a uniform-pick heuristic). Neither is derived from the other.
* Nothing here says `Sol Δ ∩ F⁴` is reached when `Sol Δ` is large, i.e. this
  file makes the `1/d` loss explicit but cannot beat it.
* `q` is left abstract. This file does not model independence across solves,
  nor bound `∑_{goodMatch F} matchCount F Δ` itself — that mass bound is
  exactly the still-open `hbad`-adjacent question `ROADMAP-current.md`
  tracks; this file only makes clear which `Δ`'s that mass needs to cover.

## Why `SolverReaches` is stated as a cap, not as an equality

Equality `q Δ = matchCount F Δ / |Sol Δ|` would need `|Sol Δ|` as a second
function and its own hypotheses. The inequality `matchCount F Δ ≤ d * q Δ`
is all the accounting needs and is implied by that equality whenever
`|Sol Δ| ≤ d`.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **`goodMatch` always excludes `Δ = 0`, once `F` is nonempty.** Taking
`x = y` for any `x ∈ F` gives `Δ = x - x = 0` as a `DirectRelation F Δ`
witness, so `¬ DirectRelation F 0` is impossible when `F` is nonempty:
`goodMatch F 0` is false. Consequently `goodMatch F Δ → Δ ≠ 0`. -/
theorem goodMatch_ne_zero (F : Finset G) (hF : F.Nonempty) {Δ : G}
    (hgood : goodMatch F Δ) : Δ ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hF
  exact hgood (Or.inl ⟨x, hx, x, hx, by abel⟩)

/-- **The reachability hypothesis.** `q Δ` is the probability that a solve
targeting `Δ` returns a quadruple in `F⁴`. `SolverReaches F d q` says that, at
every `Δ` the solver is actually ever asked about (`goodMatch F Δ`, i.e. `Δ`
is not already a direct relation via `F - F`, `F`, or `F + F`), `q` is at
least `matchCount F Δ / d`: the solver reaches a factor-base witness with
probability at least a `1/d` share of the witnesses that exist. `d` is the
uniform solution-set bound (`ZeroD/`'s degree bound). -/
def SolverReaches (F : Finset G) (d : ℕ) (q : G → ℝ) : Prop :=
  ∀ Δ : G, goodMatch F Δ → (matchCount F Δ : ℝ) ≤ (d : ℝ) * q Δ

/-- **Total success mass, from reachability.** Summing `SolverReaches` over
`goodMatch F` gives `∑_{goodMatch F} matchCount F Δ ≤ d · ∑_{goodMatch F} q Δ`.
No Sidon, no second moment — pure `Finset.sum_le_sum` on the exact domain the
solver is ever called on. -/
theorem expected_success_mass_ge (F : Finset G) (d : ℕ) (q : G → ℝ)
    (hreach : SolverReaches F d q) :
    (∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) ≤
      (d : ℝ) * ∑ Δ ∈ Finset.univ.filter (goodMatch F), q Δ := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun Δ hΔ => hreach Δ (Finset.mem_filter.mp hΔ).2)

/-- **Expected success probability of one solve at a uniformly random target.**
Under `SolverReaches F d q` with `d > 0`, the average of `q` over `Δ ∈ G` is at
least `(∑_{goodMatch F} matchCount F Δ) / (d · |G|)`. This is `hRate` with a
`1/d` reachability loss, restricted to the `Δ`'s the solver is ever asked
about (the old separate `1/2` loss for discarding `Δ = 0` is gone: `Δ = 0` is
already excluded by `goodMatch`, per `goodMatch_ne_zero`, whenever `F` is
nonempty — no separate discount needed). -/
theorem expected_successes_ge (F : Finset G) (d : ℕ) (hd : 0 < d) (q : G → ℝ)
    (hq : ∀ Δ : G, 0 ≤ q Δ)
    (hreach : SolverReaches F d q) :
    (∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) /
        ((d : ℝ) * (Fintype.card G : ℝ)) ≤
      (∑ Δ : G, q Δ) / (Fintype.card G : ℝ) := by
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmass := expected_success_mass_ge F d q hreach
  have hsub : ∑ Δ ∈ Finset.univ.filter (goodMatch F), q Δ ≤ ∑ Δ : G, q Δ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun Δ _ _ => hq Δ)
  have h1 : (∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) ≤
      (d : ℝ) * ∑ Δ : G, q Δ :=
    le_trans hmass (mul_le_mul_of_nonneg_left hsub hdR.le)
  rw [div_le_div_iff₀ (by positivity) hN]
  calc (∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) *
        (Fintype.card G : ℝ)
      ≤ ((d : ℝ) * ∑ Δ : G, q Δ) * (Fintype.card G : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hN.le
    _ = (∑ Δ : G, q Δ) * ((d : ℝ) * (Fintype.card G : ℝ)) := by ring
