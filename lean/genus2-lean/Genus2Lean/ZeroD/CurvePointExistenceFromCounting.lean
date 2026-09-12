import Mathlib

/-!
# General finite-set existence lemma: enough points survive finitely many bad conditions

New this pass, toward `ROADMAP-degree-uniform-step3.md`'s Obligation 1 (`htop_ne_smul`).
A ChatGPT consult on the exact remaining gap (curve-point existence over `F p` satisfying
eight denominator-nonvanishing side conditions) produced a clean theorem package: given a
Hasse-Weil-style lower bound on the count of "good" ambient points (here: affine points of
the genus-2 curve, i.e. `#C(F p) - 1` for the point at infinity) and, for each of finitely
many "bad" conditions, an upper bound on how many ambient points can satisfy it (there: the
degree of the pole divisor at infinity of the `i`-th denominator, restricted to the curve),
a union bound gives: if the good-point count strictly exceeds the sum of the bad bounds, some
point avoids every bad condition.

**This file formalizes exactly that generic argument, with no curve-specific content at
all** — it is pure finite combinatorics (`Finset.card_biUnion_le` plus a counting argument),
deliberately kept independent of the genus-2/Hasse-Weil specifics so it can be reused for
any future "enough points survive finitely many algebraic obstructions" argument this project
needs, not just this one. The curve-specific instantiation (plugging in the actual `C(F p)`
finset, the actual `D_i` denominators, and the Hasse-Weil bound itself as a named hypothesis)
is deliberately NOT done here — seeing this pass to that instantiation needs `theData`'s
actual denominator formulas restricted to a doubled point (`sa = sb`, `a1 = a2`), which is
future work; this file supplies the general-purpose lemma that instantiation will invoke.

**Why a named hypothesis for Hasse-Weil, not a Lean proof of it**: the genus-2 Hasse-Weil
bound is a deep theorem (a case of the Weil conjectures for curves, resting on the Riemann-
Roch theorem and the Frobenius-eigenvalue argument) with no existing Mathlib formalization
to build on. Treating it as an explicit, precisely-stated, named hypothesis is the same
"honest weakening" discipline this project already applies to `Nondegenerate`,
`CrossNondegenerate`, etc. — not a shortcut, since the statement being assumed is exactly
the true classical theorem, stated precisely enough to be checked against a reference.

**Not yet REPL-confirmed** — drafted this pass; Claire tests via the REPL.
-/

namespace Genus2Lean

open Finset

/-- **The general existence lemma.** `good` is a finite set of "candidate" objects (e.g. the
affine `F p`-points of a curve). `bad : ι → Finset α` indexes finitely many "obstruction"
subsets of `good` (e.g. the zero locus of each denominator, intersected with `good`) — note
`bad i` need not itself be a subset of `good`; only `bad i ∩ good`'s size matters, which is
`≤ (bad i).card` unconditionally, so bounding `(bad i).card` directly (as the union-bound
argument below does) is sufficient and avoids an extra intersection hypothesis. If `good`'s
size strictly exceeds the sum of the `bad i` bounds, some element of `good` lies in none of
the `bad i`. -/
theorem exists_good_not_mem_bad {α ι : Type*} [DecidableEq α] (good : Finset α)
    (bad : ι → Finset α) (s : Finset ι) (bound : ι → ℕ)
    (hbound : ∀ i ∈ s, (bad i).card ≤ bound i)
    (hcard : (∑ i ∈ s, bound i) < good.card) :
    ∃ a ∈ good, ∀ i ∈ s, a ∉ bad i := by
  by_contra hcon
  push_neg at hcon
  -- Every element of `good` lies in some `bad i`, `i ∈ s`, i.e. `good ⊆ s.biUnion bad`.
  have hsub : good ⊆ s.biUnion bad := by
    intro a ha
    obtain ⟨i, hi, hai⟩ := hcon a ha
    exact Finset.mem_biUnion.mpr ⟨i, hi, hai⟩
  have h1 : good.card ≤ (s.biUnion bad).card := Finset.card_le_card hsub
  have h2 : (s.biUnion bad).card ≤ ∑ i ∈ s, (bad i).card := Finset.card_biUnion_le
  have h3 : ∑ i ∈ s, (bad i).card ≤ ∑ i ∈ s, bound i :=
    Finset.sum_le_sum hbound
  have : good.card ≤ ∑ i ∈ s, bound i := h1.trans (h2.trans h3)
  exact absurd this (not_le.mpr hcard)

/-- **Corollary, `Fintype`-indexed obstruction list** (the shape this project's eight
denominators actually come in — a fixed `Fin 8`, not an arbitrary finite index set with an
explicit carrier `s`). Same content as `exists_good_not_mem_bad`, specialized so the
instantiation site doesn't need to separately supply `s := Finset.univ`. -/
theorem exists_good_not_mem_bad_fintype {α ι : Type*} [DecidableEq α] [Fintype ι]
    (good : Finset α) (bad : ι → Finset α) (bound : ι → ℕ)
    (hbound : ∀ i, (bad i).card ≤ bound i)
    (hcard : (∑ i, bound i) < good.card) :
    ∃ a ∈ good, ∀ i, a ∉ bad i := by
  obtain ⟨a, ha, hgood⟩ :=
    exists_good_not_mem_bad good bad Finset.univ bound (fun i _ => hbound i) hcard
  exact ⟨a, ha, fun i => hgood i (Finset.mem_univ i)⟩

/-- **Packaging the Hasse-Weil-style hypothesis abstractly.** Rather than reaching for a
concrete `C(F p)` finset type at this general-infrastructure stage, state the numeric content
alone: given a natural number `n` (standing for `#(affine good points)`) satisfying a
Hasse-Weil-shaped lower bound `n ≥ p - k` for some explicit `k` (e.g. `k = 4 * Nat.sqrt p` for
genus 2, floor-rounded per the ChatGPT consult's integer-safe formulation), and a bound `B` on
the total size of all bad conditions combined, `p - k > B` (with `p, k, B : ℕ` and honest
truncated subtraction, so this is only useful when `p ≥ k`, matching the fact that the bound
is vacuous/useless for small `p` anyway) gives `n > B`, i.e. `exists_good_not_mem_bad`'s
`hcard` hypothesis is satisfied. This is a one-line arithmetic bridge, but naming it means the
curve-specific instantiation only needs to supply `p ≥ k` and `p - k > B` (both bare `Nat`
facts, checkable without unfolding what `good`/`bad` actually are) rather than re-deriving
`n > B` from the Hasse-Weil inequality's exact shape each time. -/
theorem hasseWeil_gives_surplus {n p k B : ℕ} (hpk : k ≤ p) (hn : p - k ≤ n)
    (hB : B < p - k) : B < n :=
  hB.trans_le hn

/-- **Composed form**, chaining `hasseWeil_gives_surplus` directly into
`exists_good_not_mem_bad_fintype` — the shape the eventual curve-specific instantiation will
actually invoke: supply the point count `n = good.card`, the Hasse-Weil-style bound `p - k ≤
n`, the per-obstruction bounds, and the single arithmetic fact `(∑ bound i) < p - k` (a bare
`Nat` inequality, in principle decidable/computable once `bound` and `p,k` are concrete
numerals), and get the existence conclusion directly, with no separate `hcard` bookkeeping
step at the call site. -/
theorem exists_good_not_mem_bad_of_hasseWeil {α ι : Type*} [DecidableEq α] [Fintype ι]
    (good : Finset α) (bad : ι → Finset α) (bound : ι → ℕ) {p k : ℕ}
    (hpk : k ≤ p) (hn : p - k ≤ good.card)
    (hbound : ∀ i, (bad i).card ≤ bound i)
    (hsurplus : (∑ i, bound i) < p - k) :
    ∃ a ∈ good, ∀ i, a ∉ bad i :=
  exists_good_not_mem_bad_fintype good bad bound hbound
    (hasseWeil_gives_surplus hpk hn hsurplus)

end Genus2Lean
