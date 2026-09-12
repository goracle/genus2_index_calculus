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
actual denominator formulas (no doubled-point restriction needed — see the second-consult
update below), which is future work; this file supplies the general-purpose lemma that
instantiation will invoke.

**Why a named hypothesis for Hasse-Weil, not a Lean proof of it**: the genus-2 Hasse-Weil
bound is a deep theorem (a case of the Weil conjectures for curves, resting on the Riemann-
Roch theorem and the Frobenius-eigenvalue argument) with no existing Mathlib formalization
to build on. Treating it as an explicit, precisely-stated, named hypothesis is the same
"honest weakening" discipline this project already applies to `Nondegenerate`,
`CrossNondegenerate`, etc. — not a shortcut, since the statement being assumed is exactly
the true classical theorem, stated precisely enough to be checked against a reference.

**Not yet REPL-confirmed** — drafted this pass; Claire tests via the REPL.

**Update, this pass — second ChatGPT consult, on exactly the two pieces this file's docstring
above flagged as future work (the pole-order bound turning "bounded-degree denominator" into a
concrete `bound i`, and the threshold on `p`).** Both are now settled cleanly, and neither needs
the doubled-point (`sa = sb`, `a1 = a2`) specialization at all — the consult confirmed the
hyperelliptic `±w` symmetry doesn't give a uniformly better argument than plain Hasse-Weil, so
the general (non-doubled) statement is the right target, not a special case of it. Key points,
added as new theorems below:

- **Pole-order bound from a monomial expansion.** For a genus-2 curve `y² = f(x)` (`f` monic
  quintic, matching `curvePoly`/`DataDerivationBasics.lean`), `ord_∞(x) = -2` and `ord_∞(y) = -5`
  at the point at infinity, so a polynomial `H(x,y) = Σ c_{r,s} x^r y^s` has pole order at
  infinity `≤ max` over nonzero terms of `2r + 5s` — this is `poleOrderBound_of_monomial` below,
  stated abstractly over the exponent multiset so it doesn't need `x,y` or the curve in scope.
  The crude fallback purely from ordinary total degree `d = max(r+s)` is `2r+5s ≤ 5(r+s) ≤ 5d`
  (`poleOrderBound_le_five_mul_totalDegree` below) — much weaker but needs nothing but `d`.
- **Corrected threshold, affine count.** The relevant Hasse-Weil bound is on *affine* points,
  `#C_aff(F p) ≥ p - ⌊4√p⌋` (the projective count `p+1-⌊4√p⌋` includes the point at infinity,
  which isn't itself a location any of the 8 denominators need to avoid) — this matches
  `hasseWeil_gives_surplus`'s existing `n ≥ p - k` shape above exactly (already correct, no fix
  needed there), with `k = 4 * Nat.sqrt p` as the existing file already used. For `B = 8 * 20`
  (say, if each of the 8 denominators has pole order `≤ 20`), the consult gives the explicit
  numeric threshold `p ≳ 8B + 8 + 4√(8B+4)`, e.g. `p ≥ 223` suffices for `B_tot = 160` (worked
  by hand in the consult: `p=223` satisfies `p - 4*Nat.sqrt p > 160`, `p=211` doesn't) — a sample
  numeric sanity check, not a general theorem; the general inequality
  `p - 4 * Nat.sqrt p > B_tot` (or the exact-floor form already in `hasseWeil_gives_surplus`) is
  what any actual instantiation should discharge directly for its own concrete `B_tot`, rather
  than re-deriving a closed form for the threshold in general.
- **Two-layer structure confirmed as the right shape** (matches this project's existing
  `Nondegenerate`/`CrossNondegenerate` "named hypothesis for the deep content" discipline): (1)
  an unconditional *geometric* genericity fact — nonzero rational functions on a curve have
  finite (hence proper-closed) zero loci, so a Zariski-generic point over the algebraic closure
  automatically avoids all 8 — needing nothing but "each `h_i` is not the zero function on `C`";
  then (2) the finite-field upgrade via Hasse-Weil + the pole-order counting bound, which is
  what actually gives an `F p`-rational witness. Layer (1) is not yet stated here (it would sit
  more naturally as a `Polynomial.roots`/`Multiset.card` fact once `theData`'s actual
  denominators are in scope) — noted for whoever does the curve-specific instantiation.

**REPL-confirmed green, later pass** (Claire) — `poleOrderBound_of_monomial`'s `Finset.le_sup`
call needed its binding function supplied explicitly (`Finset.le_sup (f := fun rs => 2 * rs.1 +
5 * rs.2) hrs`); Lean couldn't infer `f` from the expected-type shape alone. Fixed, no other
issues. All theorems in this file, old and new, build with no sorries.
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

/-! ## Pole-order-at-infinity bounds, from the second ChatGPT consult

For a genus-2 curve `y² = f(x)`, the point at infinity has `ord_∞(x) = -2`, `ord_∞(y) = -5`
(the standard hyperelliptic weighting: `x` has a double pole, `y` a pole of order `2·genus+1 =
5`, matching `deg f = 5`). A monomial `x^r y^s` therefore has pole order `2r + 5s` at infinity,
and a polynomial is bounded by the max over its nonzero monomials. This section states that
combinatorial fact abstractly, over a `Finset` of exponent pairs standing in for "the monomials
actually appearing with nonzero coefficient," so it doesn't need `x, y`, `K2`, or any
`Genus2Lean`-specific ring in scope — the curve-specific instantiation supplies the actual
support finset of whichever `Rdec p` element it's bounding. -/

/-- **The weighted pole-order bound.** `supp` is the finite set of `(r, s)` exponent pairs
appearing with nonzero coefficient in some polynomial `H(x, y) = Σ_{(r,s) ∈ supp} c_{r,s} x^r
y^s`. Its pole order at the point at infinity of `y² = f(x)` (`deg f = 5`) is at most the max
weighted degree `2r + 5s` over `supp` — immediate once stated, since `Finset.sup` over `supp` of
`2r + 5s` is by definition `≥` each individual term, and `0` (the empty-support / zero-polynomial
case) is a valid vacuous bound. Stated with the bound as an explicit hypothesis-free `Finset.sup`
rather than an existential, so the instantiation site gets a computable number directly from
`supp` rather than having to invoke `Finset.le_sup` itself each time. -/
theorem poleOrderBound_of_monomial (supp : Finset (ℕ × ℕ)) :
    ∀ rs ∈ supp, 2 * rs.1 + 5 * rs.2 ≤ supp.sup (fun rs => 2 * rs.1 + 5 * rs.2) :=
  fun rs hrs => Finset.le_sup (f := fun rs => 2 * rs.1 + 5 * rs.2) hrs

/-- **Crude fallback bound, ordinary total degree only.** If all that's known about `H` is an
ordinary total-degree bound `d` (`r + s ≤ d` for every monomial in its support, the usual notion
`MvPolynomial.totalDegree`/`Polynomial` machinery already produces), the weighted pole order
`2r + 5s` is still bounded, by `5d`: since `2r + 5s ≤ 5r + 5s = 5(r+s) ≤ 5d`. Much weaker than
`poleOrderBound_of_monomial` (which uses the actual `(r,s)` shape, not just `r+s`), but needs
nothing beyond a total-degree bound already available off-the-shelf, so it's the right fallback
when the monomial-by-monomial support of a `theData` denominator isn't easy to extract by hand. -/
theorem poleOrderBound_le_five_mul_totalDegree {r s d : ℕ} (hd : r + s ≤ d) :
    2 * r + 5 * s ≤ 5 * d :=
  calc 2 * r + 5 * s ≤ 5 * r + 5 * s := by omega
    _ = 5 * (r + s) := by ring
    _ ≤ 5 * d := Nat.mul_le_mul_left 5 hd

/-- **Composed form**: given a total-degree bound `d` for each of the (`Fintype`-indexed) `ι`
denominators, `5 * d` is a valid uniform `bound` for `exists_good_not_mem_bad_of_hasseWeil`'s
`bad i`, provided each `bad i`'s cardinality is in turn controlled by that denominator's pole
order (a fact about the specific curve/denominator pairing the curve-specific instantiation
supplies, not assumed here) — i.e. this lemma only discharges the "turn a degree bound into a
pole-order bound" arithmetic step, leaving `(bad i).card ≤ 2 * r_i + 5 * s_i ≤ 5 * d` as two
separate facts the instantiation site still assembles. Included as a convenience so a uniform
degree bound `d` across all 8 denominators (the common case, if their construction is symmetric)
collapses immediately to a single numeral `bound := fun _ => 5 * d` for the union-bound call. -/
theorem hasseWeil_of_uniform_totalDegree {α ι : Type*} [DecidableEq α] [Fintype ι]
    (good : Finset α) (bad : ι → Finset α) {r s : ι → ℕ} {d p k : ℕ}
    (hpk : k ≤ p) (hn : p - k ≤ good.card)
    (hrs : ∀ i, r i + s i ≤ d)
    (hbound : ∀ i, (bad i).card ≤ 2 * r i + 5 * s i)
    (hsurplus : Fintype.card ι * (5 * d) < p - k) :
    ∃ a ∈ good, ∀ i, a ∉ bad i := by
  have hsum : (∑ _i : ι, 5 * d) = Fintype.card ι * (5 * d) := by
    simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact exists_good_not_mem_bad_of_hasseWeil good bad (fun _ => 5 * d) hpk hn
    (fun i => (hbound i).trans (poleOrderBound_le_five_mul_totalDegree (hrs i)))
    (hsum ▸ hsurplus)

end Genus2Lean
