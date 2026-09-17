import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.Complexity
set_option linter.style.header false

/-!
# Bridging a uniform pointwise fiber bound into `OffDiagonalBound`

**Purpose.** `Complexity.lean`'s `OffDiagonalBound` (the genuinely open
remainder of the second-moment split, advisory-7 eq 12's `Δ ≠ 0` part) has,
until now, had exactly one thing feeding it: the Sidon-derived diagonal
share at `Δ = 0` (`sidonOffDiagonal_second_moment_bound`), which explicitly
does NOT touch the `Δ ≠ 0` terms at all. This file adds the other
half-machine: a generic reduction showing that ANY uniform pointwise cap on
`matchCount T Δ`, for every `Δ ≠ 0` simultaneously, forces `OffDiagonalBound`
directly — via the trivial bound `x² ≤ K·x` for `0 ≤ x ≤ K` plus the
unconditional total `∑_Δ matchCount T Δ = T.card⁴`
(`sum_matchCount_eq_card_pow_four`, `AverageComplexity.lean`). No new
mathematical content beyond that: this is bookkeeping connecting an existing
unconditional identity to an existing open hypothesis, in the same spirit as
`Complexity.lean`'s own `sidonOffDiagonal_second_moment_bound`.

**Why this matters now, not before.** `ROADMAP-alpha-locus.md`'s
"RESOLUTION" section, together with `MatchingEquationTranslation.lean`'s new
gauge-orbit-collapse result (`matching_solutions_translate_by_delta_gauge_orbit`)
and the already-proved `fixedTargetSolutions_ncard_le_four`
(`MatchingSolutionSwapSymmetry.lean`), together sketch — NOT yet assembled
into one Lean theorem, see that roadmap's own "What still needs doing"
section — a UNIFORM pointwise bound `deg(alpha,alpha') ≤ 4` across the whole
`(alpha,alpha')` family (modulo the `Bad` exceptional set,
`AlphaLocusDegreeUniform.lean`, still open). If and when that composition
lands as a genuine `∀ Δ ≠ 0, matchCount T Δ ≤ 4`-shaped theorem (translating
the `ZeroD/` subsystem's group-theoretic `deg(alpha,alpha')` language into
this file's `matchCount`/`Finset G` language — itself a real, not-yet-done
translation step, flagged explicitly below, not glossed over), this file's
`offDiagonalBound_of_uniform_matchCount_bound` turns it into
`OffDiagonalBound T (4 * T.card^4)` immediately, closing `Complexity.lean`'s
open hypothesis outright (taking `M := 4 * B⁴`, well inside the room
`hitProb_ge_of_sidon_and_offDiagonal` already budgets for `c > 4`).

**What this file does NOT do.** It does not construct the uniform pointwise
bound itself — that is exactly the composition `ROADMAP-alpha-locus.md`
still flags as outstanding, plus the `Bad`-exceptional-set accounting, plus
the `ZeroD/`-side `deg(alpha,alpha')` → this file's `matchCount T Δ`
translation. This file only proves the reduction "IF such a bound exists,
THEN `OffDiagonalBound` follows" — matching this project's convention
(`PaleyZygmund.lean`, `Complexity.lean`) of keeping a genuinely open
composition step visible as its own named hypothesis rather than assumed
silently.

**Relation to `CombinatorialSecondMoment.lean`.** That file proves a
DIFFERENT, already-closed statement with the same technique family: given
`SidonRepBound T` (hence the Sidon-derived pointwise cap
`matchCount_le_two_card_sq : matchCount T Δ ≤ 2·B²` for EVERY `Δ`, `Δ = 0`
included), it bounds the FULL second moment `∑_Δ matchCount T Δ²` by
`2·B⁶` — a real, unconditional-given-Sidon result, not itself sufficient
for `Complexity.lean`'s split (its `2·B⁶`/`B²`-shaped bound is the wrong
order for the `c·B⁴` shape `hitProb_ge_of_tight_secondMoment` needs, per
that file's own header, and it never separates the diagonal/off-diagonal
pieces). This file instead: (a) restricts to `Δ ≠ 0` only (matching
`OffDiagonalBound`'s own scope, which already excludes `Δ = 0` — that
term is handled separately, via `matchCount_zero_bound`, in
`Complexity.lean`); (b) takes the pointwise cap `K` as an explicit
hypothesis rather than deriving it from `SidonRepBound`, so it composes
with whatever bound `ROADMAP-alpha-locus.md`'s gauge-orbit route eventually
supplies, not only a Sidon-derived one. Genuinely complementary, not a
duplicate — `CombinatorialSecondMoment.lean` answers "what does Sidon-ness
alone buy you," this file answers "what does ANY uniform off-diagonal cap
buy you." -/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **The bridge.** If `matchCount T Δ ≤ K` for every `Δ ≠ 0` (a uniform
pointwise cap across the whole off-diagonal family — exactly the shape a
completed `deg(alpha,alpha') ≤ K` result from `ROADMAP-alpha-locus.md` would
supply once translated into this file's language), then
`OffDiagonalBound T (K * T.card^4)` holds.

Proof: for each `Δ ≠ 0`, `matchCount T Δ ^ 2 ≤ K * matchCount T Δ` (squaring
a nonnegative quantity bounded by `K` is bounded by `K` times itself —
`Nat.mul_le_mul_right`/`sq` unfolded, cast to `ℝ`). Summing over `Δ ≠ 0` and
bounding that partial sum by the FULL sum `∑_Δ matchCount T Δ = T.card^4`
(`sum_matchCount_eq_card_pow_four`, unconditional, unrelated to any
Sidon/genericity content) gives the claim — the same "drop to a smaller
nonnegative sum" step `sidonOffDiagonal_second_moment_bound` already uses
one level up. -/
theorem offDiagonalBound_of_uniform_matchCount_bound
    (T : Finset G) (K : ℕ) (hK : ∀ Δ : G, Δ ≠ 0 → matchCount T Δ ≤ K) :
    OffDiagonalBound T ((K : ℝ) * (T.card : ℝ) ^ 4) := by
  unfold OffDiagonalBound
  have hpt : ∀ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)),
      (matchCount T Δ : ℝ) ^ 2 ≤ (K : ℝ) * (matchCount T Δ : ℝ) := by
    intro Δ hΔ
    rw [Finset.mem_filter] at hΔ
    have hle : matchCount T Δ ≤ K := hK Δ hΔ.2
    have hleR : (matchCount T Δ : ℝ) ≤ (K : ℝ) := by exact_mod_cast hle
    have hnonneg : (0:ℝ) ≤ (matchCount T Δ : ℝ) := Nat.cast_nonneg _
    calc (matchCount T Δ : ℝ) ^ 2 = (matchCount T Δ : ℝ) * (matchCount T Δ : ℝ) := sq _
      _ ≤ (K : ℝ) * (matchCount T Δ : ℝ) := by
          exact mul_le_mul_of_nonneg_right hleR hnonneg
  have hsum_le : ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (matchCount T Δ : ℝ) ^ 2 ≤
      ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (K : ℝ) * (matchCount T Δ : ℝ) :=
    Finset.sum_le_sum hpt
  have hfactor : ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (K : ℝ) * (matchCount T Δ : ℝ) =
      (K : ℝ) * ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (matchCount T Δ : ℝ) := by
    rw [Finset.mul_sum]
  have hsub_le : ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (matchCount T Δ : ℝ) ≤
      ∑ Δ : G, (matchCount T Δ : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro Δ _ _
    exact Nat.cast_nonneg _
  have htotal : ∑ Δ : G, (matchCount T Δ : ℝ) = (T.card : ℝ) ^ 4 := by
    have h := sum_matchCount_eq_card_pow_four T
    have : (∑ Δ : G, (matchCount T Δ : ℝ)) = ((∑ Δ : G, matchCount T Δ : ℕ) : ℝ) := by
      push_cast; rfl
    rw [this, h]; push_cast; ring
  have hKnonneg : (0:ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  calc ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (matchCount T Δ : ℝ) ^ 2
      ≤ ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (K : ℝ) * (matchCount T Δ : ℝ) := hsum_le
    _ = (K : ℝ) * ∑ Δ ∈ (univ.filter (fun Δ : G => Δ ≠ 0)), (matchCount T Δ : ℝ) := hfactor
    _ ≤ (K : ℝ) * ∑ Δ : G, (matchCount T Δ : ℝ) :=
        mul_le_mul_of_nonneg_left hsub_le hKnonneg
    _ = (K : ℝ) * (T.card : ℝ) ^ 4 := by rw [htotal]

/-- **Specialized corollary at `K = 4`** — the concrete case the alpha-locus
roadmap's `deg(alpha,alpha') ≤ 4` claim (once assembled and translated,
see this file's module docstring) would instantiate directly, matching
`fixedTargetSolutions_ncard_le_four`'s literal bound. Stated separately
purely for readability at the call site — no new content over the general
theorem above. -/
theorem offDiagonalBound_of_uniform_matchCount_bound_four
    (T : Finset G) (hK4 : ∀ Δ : G, Δ ≠ 0 → matchCount T Δ ≤ 4) :
    OffDiagonalBound T (4 * (T.card : ℝ) ^ 4) := by
  have h := offDiagonalBound_of_uniform_matchCount_bound T 4 hK4
  simpa using h
