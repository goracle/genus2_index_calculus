import Mathlib
import Genus2Lean.IndexCalculusReachability
import Genus2Lean.FiniteCouponCollector
set_option linter.style.header false

/-!
# Connecting `SolverReaches` to a coupon-collector bound, directly at the `q`-level

`IndexCalculusReachability.lean` gives `SolverReaches F d q`: on `goodMatch F Δ`,
`q Δ ≥ matchCount F Δ / d`, the per-solve probability the 12-equation solver lands
in `F⁴`. `FiniteCouponCollector.lean` proves a Bernoulli-style expected-distinct-
count bound, but over a literal finite seed space `Fin N → R` with a per-label
seed-count floor `k` — a combinatorial model with no place for `q`'s own internal
randomness (the solver's coin flips), which `SolverReaches`'s own docstring
deliberately leaves abstract ("`q` is left abstract... this file does not model
independence across solves").

**This file does not reify the solver's randomness into a second seed
coordinate.** Per Claire: reuse `FiniteCouponCollector`'s Bernoulli-bound
*technique* (`pow_one_sub_le_one_div_one_add_mul`), but state the coupon-collector
conclusion directly against `q`'s average success probability, treating each of
the `N` attempts as an independent draw of `Δ` (uniform over `G`) composed with
its own success/failure coin of bias `q Δ` — i.e. work at the level of a single
real number, the per-attempt average success probability `avgQ`, exactly the
quantity `expected_successes_ge` already lower-bounds. No `PMF`/`MeasureTheory`,
matching the rest of the project: `(1-avgQ)^N` is used as the SAME "probability
no attempt succeeds" quantity `pow_one_sub_le_one_div_one_add_mul` already bounds,
now interpreted (not modeled measure-theoretically) as the expected fraction of
`N`-attempt-sequences producing zero successes.

## What one attempt actually does, per Claire's model

An attempt draws a fresh `(α,α')`, i.e. a fresh `Δ` (this file: uniform over `G`,
matching `expected_successes_ge`'s own average-over-`G` framing). Two cases:

* `¬goodMatch F Δ`: `Δ` already splits over the factor base directly — a FREE
  relation, no solver call, and (per Claire, "mostly b") this counts as an
  immediate success. Coded below as probability `1` on `¬goodMatch`.
* `goodMatch F Δ`: the solver is invoked, succeeding with probability `q Δ`.

So the per-attempt, per-`Δ` "success given this Δ was drawn" probability is
`p Δ := if goodMatch F Δ then q Δ else 1` (`successProb` below), and the
per-attempt AVERAGE success probability (over the uniform draw of `Δ`) is
`avgSuccessProb F q := (∑ Δ, p Δ) / |G|` — strictly `≥`
`expected_successes_ge`'s bound, since it also credits the `¬goodMatch` mass at
rate `1` instead of `0`.

## Why the `¬goodMatch` mass need not be separately bounded

Claire's remark that `¬goodMatch` "shouldn't be hitting that much" (so that
treating it as free/negligible would be a fair simplification either way) turns
out not to be load-bearing for what follows: crediting `¬goodMatch F Δ` at
probability `1` can only INCREASE `avgSuccessProb` relative to crediting it at
whatever the true (unmodeled) rate is, so every bound proved here from a floor
on `expected_successes_ge`'s quantity is automatically also a valid bound on
`avgSuccessProb` — no separate mass estimate on `DirectRelation` is needed to
make this file's theorems honest. (A tighter analysis crediting `¬goodMatch` at
its EXACT rate, rather than the sound-but-loose floor of `1`, is a genuine
future improvement — not attempted here — since the true rate there is `1` only
in the sense that a direct relation IS accepted as the relation, not that the
model here proves anything about how large that free-relation mass is.)

## What this file proves

* `avgSuccessProb_ge` — `avgSuccessProb F q ≥ expected_successes_ge`'s own
  lower bound (immediate: `¬goodMatch` case contributes `≥ 0` either way, and
  strictly more once credited at `1`).
* `expected_zero_success_le` — the Bernoulli-style occupancy floor,
  reusing `pow_one_sub_le_one_div_one_add_mul` verbatim: if `avgQ ≤
  avgSuccessProb F q` (any sound lower bound — in particular
  `expected_successes_ge`'s conclusion) then `(1 - avgQ)^N ≤ 1/(1 + N·avgQ)`,
  interpreted as a bound on how much of the `N`-attempt weight has zero
  successes.
* `expected_successes_at_least` — the coupon-collector payoff: at least
  `1 - 1/(1+N·avgQ)` of the `N`-attempt weight, treated as an average success
  fraction, has at least one success — i.e. `N` attempts find a relation with
  "probability" (in this file's finite-combinatorics-flavored sense, matching
  the rest of the project's non-measure-theoretic treatment of expectation) at
  least `1 - 1/(1+N·avgQ)`, which `→ 1` as `N·avgQ → ∞`.
* `solverReaches_coupon_collector_bound` — the above assembled directly from
  `SolverReaches`, no new hypothesis beyond `hq1` (probabilities `≤ 1`).
* `occupancy_ge_half_of_rate` / `solverReaches_half_success_of_rate` — **this
  pass's addition, closing the asymptotic gap flagged in the previous
  version's docstring**: the `1-1/(1+N·avgQ)` shape only tends to `1` in the
  limit; these give a clean fixed threshold `≥ 1/2` once `N` meets a rate
  floor `avgQ ≥ 1/(C·N)` for some `C ∈ (0,1]` — the direct `q`-level analogue
  of `FiniteCouponCollector.lean`'s `avg_seenCount_ge_half_sq_of_rate`, minus
  that theorem's seed-space/pigeonhole scaffolding (`avgQ` is already the
  single quantity of interest here, no `B`/`k`/`d`/`H` decomposition needed).

## What this does NOT prove

* Independence across the `N` attempts is asserted by treating each attempt's
  success as its own independent Bernoulli trial of rate `avgQ` — exactly the
  same non-measure-theoretic stance `FiniteCouponCollector.lean`'s own module
  docstring takes (`Finset.card`-as-probability, no `PMF`). This file does not
  build a joint N-attempt sample space; `expected_zero_success_le` is proved as
  a bare real-number inequality about the function `N ↦ (1-avgQ)^N`, whose
  reading as "probability of zero successes in N i.i.d. Bernoulli(avgQ)
  trials" is the standard one but is not re-derived from a measure here.
* Distinctness of the relations found across multiple successes — this file
  bounds "at least one success in N attempts," not "at least `k` DISTINCT
  relations in N attempts" (that stronger claim is
  `FiniteCouponCollector.lean`'s own `avg_seenCount_ge`/
  `avg_seenCount_ge_half_sq_of_rate`, which needed the literal finite-seed-space
  model this file deliberately avoids). Reconciling the two — getting BOTH "no
  internal solver randomness modeled" AND "distinct-relation counting," not
  just "at least one relation" — is left open; see the module docstring's
  remark that (B) (this file's approach) and `FiniteCouponCollector`'s
  approach are genuinely different tradeoffs, not two views of the same proof.
* `SolverReaches F d q` itself, and the `¬goodMatch`-at-rate-`1` credit are
  both still hypotheses/modeling choices, not derived facts — exactly as
  `IndexCalculusReachability.lean`'s own "What is NOT proved here" section
  already states for `SolverReaches`.
* Wiring `avgQ` to the real curve's actual `B⁴/(d·p²)`-scale value (the
  remaining half of `ROADMAP-current.md`'s open item 1) and wiring `d` itself
  to `ZeroD/`'s degree bound (open item 2) — `occupancy_ge_half_of_rate`'s
  rate hypothesis `avgQ ≥ 1/(C·N)` is left abstract, exactly as `avgQ` and
  `d` were already left abstract by `SolverReaches` itself; this file supplies
  the threshold those two wirings will need to clear, not the wirings.

## Verification status

`avgSuccessProb`/`successProb`/`avgSuccessProb_ge_goodMatch_avg`/
`avgSuccessProb_nonneg`/`avgSuccessProb_le_one`/`expected_zero_success_le`/
`expected_successes_at_least`/`solverReaches_coupon_collector_bound`/
`avgQ_mem_Icc`: REPL-tested (Claire). One round of fixes in that pass: two
`Finset.sum_const` rewrites originally used `smul_eq_mul` (correct for a
`ℕ`-valued sum, the in-project precedent this file copied the idiom from —
e.g. `HitRateSumsetReduction.lean`'s `sum_matchCount_T_le`), but both sums
here are `ℝ`-valued (a real constant summed over a `Finset G`), so the
resulting `card • (x : ℝ)` is heterogeneous `ℕ`-nsmul, not the homogeneous
smul `smul_eq_mul` targets. Fixed to `nsmul_eq_mul` at both sites.

`occupancy_ge_half_of_rate`/`solverReaches_half_success_of_rate`: **drafted
without a Lean toolchain, this pass — NOT yet `lake build`-checked.** Same
proof shape as `FiniteCouponCollector.lean`'s already-REPL-confirmed
`avg_seenCount_ge_half_sq_of_rate` `hoccupancy_half` step, and the two
`avgQ`-bound derivations were factored into `avgQ_mem_Icc` (already
REPL-tested, unchanged from `solverReaches_coupon_collector_bound`'s own
proof) rather than re-derived, so the only genuinely new algebra is
`occupancy_ge_half_of_rate`'s `hdenom_ge`/`hfrac_le_half` block — worth a
close look on the next REPL pass.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **Per-`Δ` success probability, crediting a free `¬goodMatch` hit as
probability `1`.** `goodMatch F Δ` routes to the solver's own `q Δ`;
`¬goodMatch F Δ` is an immediate free relation (Claire, "mostly b"). -/
noncomputable def successProb (F : Finset G) (q : G → ℝ) (Δ : G) : ℝ :=
  if goodMatch F Δ then q Δ else 1

/-- **The per-attempt average success probability**, over a uniform draw of
`Δ` from `G` — the quantity one attempt of the "draw a fresh `(α,α')`, check
`goodMatch`, else solve" process succeeds with, in expectation. -/
noncomputable def avgSuccessProb (F : Finset G) (q : G → ℝ) : ℝ :=
  (∑ Δ : G, successProb F q Δ) / (Fintype.card G : ℝ)

/-- **`successProb` is nonnegative**, given `q` is (needed throughout below;
`SolverReaches`'s own docstring treats `q` as a probability, so `hq : ∀ Δ, 0 ≤
q Δ` is the same standing hypothesis `expected_successes_ge` already carries). -/
theorem successProb_nonneg (F : Finset G) (q : G → ℝ) (hq : ∀ Δ : G, 0 ≤ q Δ)
    (Δ : G) : 0 ≤ successProb F q Δ := by
  unfold successProb
  split
  · exact hq Δ
  · norm_num

/-- **`successProb` agrees with `q` on `goodMatch`.** Immediate from the
`if`; recorded for `Finset.sum_congr`-style rewriting below. -/
theorem successProb_eq_of_goodMatch {F : Finset G} {q : G → ℝ} {Δ : G}
    (h : goodMatch F Δ) : successProb F q Δ = q Δ := if_pos h

/-- **`avgSuccessProb` dominates `expected_successes_ge`'s own bound.**
Crediting `¬goodMatch F Δ` at probability `1` instead of `0` only adds
nonnegative mass to the sum (`successProb_nonneg`), so any lower bound valid
for the `goodMatch`-only average (`expected_successes_ge`'s conclusion,
`(∑_{goodMatch F} q)/|G|`, itself at most
`(∑_{goodMatch F} matchCount F Δ)/(d·|G|)`) is also a valid lower bound for
`avgSuccessProb`. Proved by splitting the full sum over `goodMatch F` /
`¬goodMatch F` (`Finset.sum_filter_add_sum_filter_not`), rewriting the
`goodMatch` piece to `q` via `successProb_eq_of_goodMatch`, and discarding the
nonnegative `¬goodMatch` piece. Combine with `expected_successes_ge` for the
full chain down to `SolverReaches`. -/
theorem avgSuccessProb_ge_goodMatch_avg (F : Finset G) (q : G → ℝ)
    (hq : ∀ Δ : G, 0 ≤ q Δ) :
    (∑ Δ ∈ Finset.univ.filter (goodMatch F), q Δ) / (Fintype.card G : ℝ) ≤
      avgSuccessProb F q := by
  unfold avgSuccessProb
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  -- `gcongr` discharges the "divide both sides by the same positive `|G|`"
  -- monotonicity step without committing to a specific `div_le_div_...`
  -- lemma name.
  gcongr
  have hsplit :
      ∑ Δ ∈ Finset.univ.filter (goodMatch F), successProb F q Δ +
        ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ goodMatch F Δ), successProb F q Δ =
      ∑ Δ : G, successProb F q Δ :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (goodMatch F) (successProb F q)
  have hgood_eq :
      ∑ Δ ∈ Finset.univ.filter (goodMatch F), successProb F q Δ =
        ∑ Δ ∈ Finset.univ.filter (goodMatch F), q Δ := by
    apply Finset.sum_congr rfl
    intro Δ hΔ
    exact successProb_eq_of_goodMatch (Finset.mem_filter.mp hΔ).2
  have hbad_nonneg :
      0 ≤ ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ goodMatch F Δ), successProb F q Δ :=
    Finset.sum_nonneg (fun Δ _ => successProb_nonneg F q hq Δ)
  calc ∑ Δ ∈ Finset.univ.filter (goodMatch F), q Δ
      = ∑ Δ ∈ Finset.univ.filter (goodMatch F), successProb F q Δ := hgood_eq.symm
    _ ≤ ∑ Δ ∈ Finset.univ.filter (goodMatch F), successProb F q Δ +
          ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ goodMatch F Δ), successProb F q Δ := by
        linarith
    _ = ∑ Δ : G, successProb F q Δ := hsplit

/-- **`avgSuccessProb` is nonnegative.** Sum of nonnegatives over `Fintype
G`, divided by `|G| > 0`. -/
theorem avgSuccessProb_nonneg (F : Finset G) (q : G → ℝ) (hq : ∀ Δ : G, 0 ≤ q Δ) :
    0 ≤ avgSuccessProb F q := by
  unfold avgSuccessProb
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  exact div_nonneg (Finset.sum_nonneg (fun Δ _ => successProb_nonneg F q hq Δ)) hN.le

/-- **`avgSuccessProb` is at most `1`.** Each `successProb F q Δ ≤ 1`
(`hq1 : ∀ Δ, q Δ ≤ 1`, the same standing bound a probability carries; the
`¬goodMatch` branch is literally `1`), so the average of `|G|` terms each
`≤ 1` is `≤ 1`. -/
theorem avgSuccessProb_le_one (F : Finset G) (q : G → ℝ) (hq1 : ∀ Δ : G, q Δ ≤ 1) :
    avgSuccessProb F q ≤ 1 := by
  unfold avgSuccessProb
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  rw [div_le_one hN]
  calc ∑ Δ : G, successProb F q Δ ≤ ∑ _Δ : G, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro Δ _
        unfold successProb
        split
        · exact hq1 Δ
        · exact le_refl 1
    _ = (Fintype.card G : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]

/-! ## The occupancy bound, reusing `FiniteCouponCollector`'s Bernoulli lemma -/

/-- **The Bernoulli-style occupancy floor, at the `q`-level.** If `avgQ` is
ANY sound lower bound on `avgSuccessProb F q` — in particular
`expected_successes_ge`'s conclusion composed with
`avgSuccessProb_ge_goodMatch_avg` above — then `(1-avgQ)^N ≤ 1/(1+N·avgQ)`.
Pure application of `pow_one_sub_le_one_div_one_add_mul`
(`FiniteCouponCollector.lean`); no new combinatorics, just the interpretation
change from "one seed-coordinate's occupancy" to "one attempt's success
probability." Needs `0 ≤ avgQ ≤ 1`, both immediate from `avgSuccessProb_nonneg`/
`avgSuccessProb_le_one` when `avgQ := avgSuccessProb F q` itself; a caller
using a weaker floor supplies its own bounds. -/
theorem expected_zero_success_le (avgQ : ℝ) (havgQ0 : 0 ≤ avgQ) (havgQ1 : avgQ ≤ 1)
    (N : ℕ) :
    (1 - avgQ) ^ N ≤ 1 / (1 + (N : ℝ) * avgQ) :=
  pow_one_sub_le_one_div_one_add_mul avgQ havgQ0 havgQ1 N

/-- **The coupon-collector payoff: at least one success in `N` attempts.**
`1 - (1-avgQ)^N` is the standard "probability of at least one success in `N`
i.i.d. Bernoulli(`avgQ`) trials" (complement of "all `N` fail"), and by
`expected_zero_success_le` this is at least `1 - 1/(1+N·avgQ)`, which `→ 1`
as `N·avgQ → ∞`. Stated as a bound on `1 - (1-avgQ)^N` directly rather than
introducing a separate `PMF`, matching `FiniteCouponCollector.lean`'s own
non-measure-theoretic stance (see module docstring). -/
theorem expected_successes_at_least (avgQ : ℝ) (havgQ0 : 0 ≤ avgQ) (havgQ1 : avgQ ≤ 1)
    (N : ℕ) :
    1 - 1 / (1 + (N : ℝ) * avgQ) ≤ 1 - (1 - avgQ) ^ N := by
  have h := expected_zero_success_le avgQ havgQ0 havgQ1 N
  linarith

/-- **Assembled statement: from `SolverReaches` to a coupon-collector floor.**
Given `SolverReaches F d q` and `d > 0`, `N` attempts (each: draw a fresh
`Δ`; free hit on `¬goodMatch`, else solve) succeed at least once with
"probability" (this file's finite/expectation-flavored sense, not a
measure-theoretic one — see module docstring) at least
`1 - 1/(1 + N·avgQ)`, where `avgQ := (∑_{goodMatch F} matchCount F Δ) /
(d·|G|)` is exactly `expected_successes_ge`'s own lower bound on
`expected_successes_ge`'s quantity, hence (by
`avgSuccessProb_ge_goodMatch_avg`) also a sound floor on the REAL
`avgSuccessProb F q`. This is the file's main theorem: it needs no new
hypothesis beyond what `SolverReaches`/`expected_successes_ge` already carry,
plus `hq1` (probabilities are `≤ 1`, not previously needed by
`IndexCalculusReachability.lean` since it never had to bound `q` above). 

 **`avgQ` (the `goodMatch`-mass average) lies in `[0,1]`.** Shared
bounds-derivation used by both `solverReaches_coupon_collector_bound` and
`solverReaches_half_success_of_rate` below, factored out so the two proofs
don't duplicate this step. `0 ≤` is immediate (nonneg sum over nonneg
denominator); `≤ 1` uses `SolverReaches` and `hq1` directly:
`matchCount F Δ ≤ d·q Δ ≤ d` termwise on `goodMatch F`, so the sum is at
most `d·|goodMatch F| ≤ d·|G|`, the exact denominator. -/
theorem avgQ_mem_Icc (F : Finset G) (d : ℕ) (hd : 0 < d) (q : G → ℝ)
    (hq1 : ∀ Δ : G, q Δ ≤ 1) (hreach : SolverReaches F d q) :
    0 ≤ (∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) /
          ((d : ℝ) * (Fintype.card G : ℝ)) ∧
    (∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) /
          ((d : ℝ) * (Fintype.card G : ℝ)) ≤ 1 := by
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨?_, ?_⟩
  · apply div_nonneg
    · exact Finset.sum_nonneg (fun Δ _ => by positivity)
    · positivity
  · rw [div_le_one (by positivity)]
    have hsum_le : ∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ) ≤
        ∑ Δ ∈ Finset.univ.filter (goodMatch F), (d : ℝ) := by
      apply Finset.sum_le_sum
      intro Δ hΔ
      have hq1Δ := hq1 Δ
      have hreachΔ := hreach Δ (Finset.mem_filter.mp hΔ).2
      calc (matchCount F Δ : ℝ) ≤ (d : ℝ) * q Δ := hreachΔ
        _ ≤ (d : ℝ) * 1 := mul_le_mul_of_nonneg_left hq1Δ hdR.le
        _ = (d : ℝ) := mul_one _
    calc ∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)
        ≤ ∑ _Δ ∈ Finset.univ.filter (goodMatch F), (d : ℝ) := hsum_le
      _ = (Finset.univ.filter (goodMatch F)).card * (d : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card G : ℝ) * (d : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hdR.le
          have : (Finset.univ.filter (goodMatch F)).card ≤ Fintype.card G := by
            calc (Finset.univ.filter (goodMatch F)).card ≤ (Finset.univ : Finset G).card :=
                  Finset.card_le_card (Finset.filter_subset _ _)
              _ = Fintype.card G := Finset.card_univ
          exact_mod_cast this
      _ = (d : ℝ) * (Fintype.card G : ℝ) := mul_comm _ _

theorem solverReaches_coupon_collector_bound
    (F : Finset G) (d : ℕ) (hd : 0 < d) (q : G → ℝ)
    (hq0 : ∀ Δ : G, 0 ≤ q Δ) (hq1 : ∀ Δ : G, q Δ ≤ 1)
    (hreach : SolverReaches F d q) (N : ℕ) :
    1 - 1 / (1 + (N : ℝ) *
        ((∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) /
          ((d : ℝ) * (Fintype.card G : ℝ)))) ≤
      1 - (1 -
        ((∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) /
          ((d : ℝ) * (Fintype.card G : ℝ)))) ^ N := by
  obtain ⟨havgQ0, havgQ1⟩ := avgQ_mem_Icc F d hd q hq1 hreach
  exact expected_successes_at_least _ havgQ0 havgQ1 N

/-! ## Closing the asymptotic gap: a clean `≥ 1/2` threshold

`solverReaches_coupon_collector_bound` gives `1 - 1/(1+N·avgQ)` as the
success floor for `N` attempts — correct but not yet in the "large `N`
clears a fixed threshold" shape `FiniteCouponCollector.lean`'s own
`avg_seenCount_ge_half_sq_of_rate` reached for the seed-space model. This
section proves the exact analogue at the `q`-level: once `N` is large enough
relative to a rate floor on `avgQ`, the success floor clears `1/2`.

Simpler than `avg_seenCount_ge_half_sq_of_rate`: there `k/d` first had to be
bounded via a pigeonhole argument against `|H|` before the rate hypothesis
made sense (hence that theorem's `B`, `C`, `hM`, `hkd` machinery). Here
`avgQ` is already the single real quantity of interest — no seed-count
pigeonhole, no `|H|` — so only the Bernoulli-threshold step survives,
stated directly against an abstract rate hypothesis `avgQ ≥ 1/(C·N)`. -/

/-- **The Bernoulli threshold, at the `avgQ`-level.** If `avgQ ≥ 1/(C·N)`
(`C > 0`, i.e. `N` attempts already meet a `1/C`-fraction-of-`1/avgQ` rate
floor) then `N·avgQ ≥ 1/C`, and `1/(1+N·avgQ) ≤ 1/2` once `C ≤ 1`
(`1+N·avgQ ≥ 1+1/C ≥ 2`). Pure algebra on `expected_zero_success_le`'s
conclusion — no new combinatorial content, same shape as
`avg_seenCount_ge_half_sq_of_rate`'s own `hoccupancy_half` step, restated
without that theorem's `B`/`k`/`d`/`H` scaffolding since `avgQ` is already
the quantity of interest here. -/
theorem occupancy_ge_half_of_rate
    (avgQ C : ℝ) (havgQ0 : 0 ≤ avgQ) (havgQ1 : avgQ ≤ 1) (hC0 : 0 < C) (hC1 : C ≤ 1)
    (N : ℕ) (hrate : 1 / (C * (N : ℝ)) ≤ avgQ) (hNpos : 0 < N) :
    (1 : ℝ) / 2 ≤ 1 - (1 - avgQ) ^ N := by
  have hNR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hCN_pos : (0:ℝ) < C * (N : ℝ) := by positivity
  have hbernoulli := expected_zero_success_le avgQ havgQ0 havgQ1 N
  have hdenom_ge : (2:ℝ) ≤ 1 + (N : ℝ) * avgQ := by
    have h1 : (1:ℝ) / C ≤ (N : ℝ) * avgQ := by
      have h2 : (N : ℝ) * (1 / (C * (N : ℝ))) ≤ (N : ℝ) * avgQ :=
        mul_le_mul_of_nonneg_left hrate hNR.le
      have h3 : (N : ℝ) * (1 / (C * (N : ℝ))) = 1 / C := by
        have hCne : C ≠ 0 := ne_of_gt hC0
        have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
        field_simp
      rw [h3] at h2
      exact h2
    have h4 : (1:ℝ) ≤ 1 / C := by
      rw [le_div_iff₀ hC0]
      linarith
    linarith
  have hdenom_pos : (0:ℝ) < 1 + (N : ℝ) * avgQ := by linarith
  have hfrac_le_half : 1 / (1 + (N : ℝ) * avgQ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hdenom_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith
  linarith [hbernoulli, hfrac_le_half]

/-- **Assembled: `SolverReaches` clears success probability `1/2` at a
sufficient budget `N`.** Combines `solverReaches_coupon_collector_bound`'s
floor with `occupancy_ge_half_of_rate`: given `SolverReaches F d q`, `C ∈
(0,1]`, and a budget `N` meeting the rate floor `avgQ ≥ 1/(C·N)` (where
`avgQ := (∑_{goodMatch F} matchCount F Δ)/(d·|G|)` is exactly the same
quantity `expected_successes_ge`/`SolverReaches` already produce), `N`
attempts find a relation with success floor at least `1/2`. This is the
`q`-level analogue of `avg_seenCount_ge_half_sq_of_rate`
(`FiniteCouponCollector.lean`): a clean, fixed threshold rather than the
`1-1/(1+N·avgQ)` shape that only tends to `1` in the limit. Wiring `avgQ`
itself to the real curve's `B⁴/(d·p²)`-scale value (closing open item 1's
remaining gap, per `ROADMAP-current.md`) and to `d`'s actual value (open
item 2) is NOT attempted here — this is the generic threshold statement
those two wirings will need to clear, once available. -/
theorem solverReaches_half_success_of_rate
    (F : Finset G) (d : ℕ) (hd : 0 < d) (q : G → ℝ)
    (hq0 : ∀ Δ : G, 0 ≤ q Δ) (hq1 : ∀ Δ : G, q Δ ≤ 1)
    (hreach : SolverReaches F d q) (C : ℝ) (hC0 : 0 < C) (hC1 : C ≤ 1)
    (N : ℕ) (hNpos : 0 < N)
    (hrate : 1 / (C * (N : ℝ)) ≤
      (∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) /
        ((d : ℝ) * (Fintype.card G : ℝ))) :
    (1 : ℝ) / 2 ≤
      1 - (1 -
        ((∑ Δ ∈ Finset.univ.filter (goodMatch F), (matchCount F Δ : ℝ)) /
          ((d : ℝ) * (Fintype.card G : ℝ)))) ^ N := by
  obtain ⟨havgQ0, havgQ1⟩ := avgQ_mem_Icc F d hd q hq1 hreach
  exact occupancy_ge_half_of_rate _ C havgQ0 havgQ1 hC0 hC1 N hrate hNpos
