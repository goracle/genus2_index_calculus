import Mathlib
set_option linter.style.header false

/-!
# A finite, `PMF`-free coupon-collector bound (ChatGPT consult, this pass)

## Background: why this file exists, and what it deliberately does NOT claim

`IndexCalculusComplexityRealHitCount.lean` proves a purely STRUCTURAL fact:
for the real curve, at least `B²/2` of the `B⁴` ordered point-quadruples
realize distinct `Δ`'s. Per the ChatGPT consult this pass (recorded in
`ROADMAP-current.md`), that structural fact does **not** by itself give a
coupon-collector theorem — what matters for coupon collection is the
PER-ATTEMPT probability of a solve landing on each `Δ`, not the number of
distinct `Δ`'s appearing somewhere among `B⁴` quadruples. Conflating "there
exist `≥ B²/2` good targets" with "a solve hits each of them with
probability `~1/B²`" is a live mistake the consult specifically flagged
(its §4): the `B²/2` targets could have wildly uneven multiplicities, and
depending on what the solve samples FROM (the `B⁴` quadruples themselves,
vs. the whole group `G`), the naive per-target probability could be far
smaller than what a coupon-collector argument needs.

This file builds only the GENERIC, curve-independent half — ChatGPT's
"Theorem B" — as an isolated finite-combinatorics lemma, with its own
honestly-scoped hypothesis (every target label is produced by at least `k`
out of `d` possible seeds, i.e. `q_Δ ≥ k/d`, the UNCONDITIONAL per-complete-
solve success probability, not a conditional-on-Δ-being-chosen one — see
the consult's §5 for why that distinction matters). Wiring `k`, `d`, and
`H` to this project's actual sampler is NOT attempted here — that is
exactly `IndexCalculusReachability.lean`'s `SolverReaches`, still open, and
doing that wiring honestly needs a real model of how `(α,α')` induces `Δ`
that nothing on file yet provides (see `ROADMAP-current.md` open item 1's
confirmed-not-actionable read).

## Why no `PMF`/`MeasureTheory`

Per the consult's §§1, 6, 8: the entire content is expressible as
`Finset.card` on the finite product type `Fin N → R` (`R` a finite seed
space), with the uniform "probability" of an event literally defined as
`(event's card) / d^N`. No integration, no independence typeclass, no
measure — matching this project's existing style (`PaleyZygmund.lean`,
`HitRateSumsetReduction.lean`'s second-moment arguments are the same kind
of finite-cardinality dressing-as-probability). The consult's §7 checked
current Mathlib4's `PMF`/`ProbabilityTheory` API and confirmed a small
usable slice exists if ever needed later, but recommended against reaching
for it now — this file follows that recommendation.

## What is proved here

* `card_never_hit_le`: for a single label `Δ` produced by at least `k` of
  `d` seeds, the number of `N`-seed-tuples that NEVER produce `Δ` is at
  most `(d-k)^N` (each coordinate independently avoids the `≥ k`
  `Δ`-producing seeds; `≤ (d-k)^N` such tuples by a direct product-set
  cardinality bound). Pure `Fintype`/`Finset.card` combinatorics.
* `sum_card_hit_ge`: summing the "seen" count over ALL `d^N` seed-tuples
  and over all `M := H.card` target labels gives a lower bound
  `M · (d^N - (d-k)^N)` on the total mass — the finite-cardinality analogue
  of `𝔼[X_N] ≥ M(1-(1-k/d)^N)` from the consult's eq (1)/(2), stated without
  dividing by `d^N` (so it is an exact `ℕ`-inequality, not a probability).

## What is explicitly NOT proved here (left for whoever wires this up)

* The variance/Chebyshev high-probability strengthening (consult §3) —
  noted as available, not built, since the expectation-level bound alone
  already matches what `IndexCalculusComplexity.lean`'s balance needs
  (consult §2: `d = O(B³)` already gives `Θ(B)` expected distinct hits at
  `N ~ B²`, matching the target exactly).
* Any connection to this project's actual `H.Point`/`Jacobian H D` model,
  `matchCount`, or `SampleTargetFromAlpha` — this file is deliberately
  curve-independent, generic in an arbitrary label type `G` and seed type
  `R`, exactly as the consult's §6 interface suggests.

## Verification status

Drafted without a Lean toolchain, per the working agreement — NOT `lake
build`-checked. This is genuinely new territory for the project (first use
of `Fintype (Fin N → R)`-style product-space cardinality reasoning); the
Mathlib lemma names below were chosen for their stated behavior, not
recalled with high confidence, and are the most likely spot to need a REPL
round-trip.
-/

open Finset

variable {G R : Type*} [DecidableEq G] [DecidableEq R] [Fintype R]

/-- **The per-label "never hit" bound.** Given a labelling function
`r : R → Option G` (a seed either produces some label or fails, `none`),
a single target `Δ : G`, and a lower bound `k` on the number of seeds
producing `Δ` (`hk : k ≤ (univ.filter (fun x => r x = some Δ)).card`),
the number of `N`-tuples `ω : Fin N → R` such that NO coordinate produces
`Δ` (`∀ i, r (ω i) ≠ some Δ`) is at most `(d - k)^N`, where `d :=
Fintype.card R`.

Proof idea: the "never hit" tuples are exactly `Fin N → (univ.filter (r ·
≠ some Δ))` — each coordinate drawn from the seeds NOT producing `Δ`, a
finset of size `d - k'` where `k' ≥ k` is the exact producing-count (so
`d - k' ≤ d - k`). Bounding via `Fintype.card_fun`-style product-cardinality
reasoning: `(Fintype.card {x // r x ≠ some Δ})^N ≤ (d - k)^N`. -/
theorem card_never_hit_le
    (r : R → Option G) (Δ : G) (N k : ℕ)
    (hk : k ≤ (univ.filter (fun x : R => r x = some Δ)).card) :
    (univ.filter (fun ω : Fin N → R => ∀ i, r (ω i) ≠ some Δ)).card ≤
      (Fintype.card R - k) ^ N := by
  classical
  -- The "avoiding" seeds form a finset of size `d - (producing count) ≤ d - k`.
  set avoid : Finset R := univ.filter (fun x : R => r x ≠ some Δ) with havoid
  set prod : Finset R := univ.filter (fun x : R => r x = some Δ) with hprod
  have hcard_split : avoid.card + prod.card = Fintype.card R := by
    have hprod_eq : prod = univ.filter (fun x : R => ¬ r x ≠ some Δ) := by
      rw [hprod]
      congr 1
      ext x
      simp [not_not]
    have : avoid.card + prod.card = (univ : Finset R).card := by
      rw [havoid, hprod_eq]
      exact Finset.filter_card_add_filter_neg_card_eq_card
        (p := fun x : R => r x ≠ some Δ)
    rwa [Finset.card_univ] at this
  have havoid_le : avoid.card ≤ Fintype.card R - k := by omega
  -- The event set is exactly the set of functions `Fin N → avoid`, viewed
  -- inside `Fin N → R`, so its cardinality is `avoid.card ^ N`.
  have hset_eq :
      (univ.filter (fun ω : Fin N → R => ∀ i, r (ω i) ≠ some Δ)) =
        Fintype.piFinset (fun _ : Fin N => avoid) := by
    ext ω
    simp [havoid, Fintype.mem_piFinset, Finset.mem_filter]
  rw [hset_eq, Fintype.card_piFinset]
  calc ∏ _i : Fin N, avoid.card = avoid.card ^ N := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (Fintype.card R - k) ^ N := Nat.pow_le_pow_left havoid_le N

/-- **The finite, `ℕ`-exact coupon-collector mass bound.** Let `H : Finset
G` be `M := H.card` target labels, each produced by at least `k` of `d :=
Fintype.card R` seeds (`hk`). Summing, over ALL `N`-tuples `ω`, the number
of `H`-labels seen at least once (`seenCount ω := (H.filter (fun Δ => ∃ i,
r (ω i) = some Δ)).card`), gives

    ∑ ω, seenCount ω ≥ M · (d^N - (d - k)^N).

This is the exact-`ℕ`, un-normalized form of the consult's `𝔼[X_N] ≥
M(1-(1-k/d)^N)` (eq (1)/(2)): dividing both sides by `d^N = Fintype.card
(Fin N → R)` recovers that inequality as an average, with no probability
notion needed to STATE or PROVE it — only to interpret it. -/
theorem sum_card_hit_ge
    (r : R → Option G) (H : Finset G) (N k : ℕ)
    (hk : ∀ Δ ∈ H, k ≤ (univ.filter (fun x : R => r x = some Δ)).card) :
    H.card * (Fintype.card R ^ N - (Fintype.card R - k) ^ N) ≤
      ∑ ω : Fin N → R,
        (H.filter (fun Δ => ∃ i, r (ω i) = some Δ)).card := by
  classical
  -- Swap the order of summation: sum over (Δ, ω) pairs, grouping first by Δ.
  have hswap :
      ∑ ω : Fin N → R, (H.filter (fun Δ => ∃ i, r (ω i) = some Δ)).card =
        ∑ Δ ∈ H, (univ.filter (fun ω : Fin N → R => ∃ i, r (ω i) = some Δ)).card := by
    have hcount : ∀ ω : Fin N → R,
        (H.filter (fun Δ => ∃ i, r (ω i) = some Δ)).card =
          ∑ Δ ∈ H, if ∃ i, r (ω i) = some Δ then 1 else 0 := by
      intro ω
      rw [Finset.card_filter]
    simp_rw [hcount]
    rw [Finset.sum_comm]
    congr 1
    ext Δ
    rw [Finset.card_filter]
  rw [hswap]
  -- For each Δ, bound its own sum via the complement of `card_never_hit_le`.
  have hper : ∀ Δ ∈ H,
      Fintype.card R ^ N - (Fintype.card R - k) ^ N ≤
        (univ.filter (fun ω : Fin N → R => ∃ i, r (ω i) = some Δ)).card := by
    intro Δ hΔ
    have htotal : (univ : Finset (Fin N → R)).card = Fintype.card R ^ N := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    have hnever := card_never_hit_le r Δ N k (hk Δ hΔ)
    have hcompl :
        (univ.filter (fun ω : Fin N → R => ∃ i, r (ω i) = some Δ)) =
          univ \ (univ.filter (fun ω : Fin N → R => ∀ i, r (ω i) ≠ some Δ)) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
        not_forall, not_ne_iff]
    rw [hcompl, Finset.card_sdiff, htotal]
    have hinter :
        (univ.filter (fun ω : Fin N → R => ∀ i, r (ω i) ≠ some Δ)) ∩ univ =
          (univ.filter (fun ω : Fin N → R => ∀ i, r (ω i) ≠ some Δ)) := by
      rw [Finset.inter_univ]
    rw [hinter]
    omega
  calc H.card * (Fintype.card R ^ N - (Fintype.card R - k) ^ N) =
      ∑ _Δ ∈ H, (Fintype.card R ^ N - (Fintype.card R - k) ^ N) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ Δ ∈ H, (univ.filter (fun ω : Fin N → R => ∃ i, r (ω i) = some Δ)).card :=
        Finset.sum_le_sum hper

/-- **Averaged form of `sum_card_hit_ge`**, dividing through by `d^N =
Fintype.card (Fin N → R)`: the AVERAGE, over all `N`-seed-tuples `ω`, of the
number of `H`-labels seen at least once is at least `M · (1 - (1 - k/d)^N)`
— the real-valued form of the consult's `𝔼[X_N] ≥ M(1-(1-k/d)^N)` (eq
(1)/(2)), now genuinely an average (division by the total tuple count
`d^N`), not just an unnormalized `ℕ`-mass bound. This is the shape needed
once `k`, `d`, `H` are wired to an actual sampler: `M` becomes the number of
reachable factor-base targets, `d^N` the total attempt-space, and the RHS
is the expected count of distinct relations found in `N` attempts. Wiring
is deliberately still not attempted here (see the module docstring); this
is the generic real-number restatement the wiring will need to state its
conclusion in, once available.

Needs `k ≤ Fintype.card R`: without it the ℕ-subtraction `d - k` inside
`sum_card_hit_ge` truncates at `0` rather than going negative, breaking the
real-number identity `(d-k)^N = d^N - ... ` this theorem needs verbatim.
This is a mild, always-satisfiable side condition in practice (`k` is a
lower bound on a single label's producing-seed count, itself at most `d`,
the total seed count), not a new mathematical assumption. -/
theorem avg_seenCount_ge
    (r : R → Option G) (H : Finset G) (N k : ℕ) (hd : 0 < Fintype.card R)
    (hkd : k ≤ Fintype.card R)
    (hk : ∀ Δ ∈ H, k ≤ (univ.filter (fun x : R => r x = some Δ)).card) :
    (H.card : ℝ) * (1 - (1 - (k : ℝ) / (Fintype.card R : ℝ)) ^ N) ≤
      (∑ ω : Fin N → R,
        (H.filter (fun Δ => ∃ i, r (ω i) = some Δ)).card : ℝ) /
        (Fintype.card R : ℝ) ^ N := by
  have hdR : (0 : ℝ) < (Fintype.card R : ℝ) := by exact_mod_cast hd
  have hdRpow : (0 : ℝ) < (Fintype.card R : ℝ) ^ N := by positivity
  have hnat := sum_card_hit_ge r H N k hk
  -- Cast the ℕ-inequality to ℝ, converting the truncated ℕ-subtraction
  -- `Fintype.card R - k` into genuine real subtraction via `Nat.cast_sub hkd`.
  have hnatR : (H.card : ℝ) * ((Fintype.card R : ℝ) ^ N - ((Fintype.card R : ℝ) - (k : ℝ)) ^ N) ≤
      (∑ ω : Fin N → R,
        (H.filter (fun Δ => ∃ i, r (ω i) = some Δ)).card : ℝ) := by
    have hcast : ((Fintype.card R - k : ℕ) : ℝ) = (Fintype.card R : ℝ) - (k : ℝ) :=
      Nat.cast_sub hkd
    have hle_pow : (Fintype.card R - k) ^ N ≤ Fintype.card R ^ N :=
      Nat.pow_le_pow_left (by omega) N
    calc (H.card : ℝ) * ((Fintype.card R : ℝ) ^ N - ((Fintype.card R : ℝ) - (k : ℝ)) ^ N)
        = (H.card : ℝ) * ((Fintype.card R : ℝ) ^ N - ((Fintype.card R - k : ℕ) : ℝ) ^ N) := by
          rw [hcast]
      _ = (H.card : ℝ) * (((Fintype.card R ^ N : ℕ) : ℝ) - (((Fintype.card R - k) ^ N : ℕ) : ℝ)) := by
          push_cast; ring
      _ = ((H.card * (Fintype.card R ^ N - (Fintype.card R - k) ^ N) : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sub hle_pow]
          try push_cast
          try ring
      _ ≤ (∑ ω : Fin N → R,
            (H.filter (fun Δ => ∃ i, r (ω i) = some Δ)).card : ℝ) := by
          exact_mod_cast hnat
  -- Divide through by `d^N > 0`; rewrite the LHS factor `(1 - k/d)^N` to
  -- match `((d - k)/d)^N`, which is exactly `(d-k)^N / d^N` by `div_pow`.
  have hkey : (H.card : ℝ) * (1 - (1 - (k : ℝ) / (Fintype.card R : ℝ)) ^ N) *
      (Fintype.card R : ℝ) ^ N ≤
      (∑ ω : Fin N → R,
        (H.filter (fun Δ => ∃ i, r (ω i) = some Δ)).card : ℝ) := by
    have hrw : (H.card : ℝ) * (1 - (1 - (k : ℝ) / (Fintype.card R : ℝ)) ^ N) *
        (Fintype.card R : ℝ) ^ N =
        (H.card : ℝ) * ((Fintype.card R : ℝ) ^ N - ((Fintype.card R : ℝ) - (k : ℝ)) ^ N) := by
      have hdne : (Fintype.card R : ℝ) ≠ 0 := hdR.ne'
      have hone : (1 : ℝ) - (k : ℝ) / (Fintype.card R : ℝ) =
          ((Fintype.card R : ℝ) - (k : ℝ)) / (Fintype.card R : ℝ) := by
        field_simp
      rw [hone, div_pow]
      field_simp
      try ring
    rw [hrw]
    exact hnatR
  rw [le_div_iff₀ hdRpow]
  exact hkey
