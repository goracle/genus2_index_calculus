import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.PaleyZygmund
import Genus2Lean.SidonEnergy
import Genus2Lean.MatchCountAutocorr
set_option linter.style.header false

/-!
# Genus-2 index calculus: a Fourier-free second-moment bound (advisory-7 eq 14-17)

This file gives a purely combinatorial proof of advisory-7 eq (17) — the explicit,
provably-extremal `B²`-shortfall bound `Pr(X>0) > B²/(2N)` — applied directly to
`T = s(F)` rather than to `F` itself. Unlike `SidonEnergy.lean`'s
`sidon_gives_hit_count_bound_of_ident`, this needs NO `hident` side-condition:
because we work with `matchCount T` throughout (not a bridge from `matchCount F`
via `repCount F`), `SidonRepBound T` alone is enough.

The advisory derives eq (17) via Fourier analysis on `G` (eq 14: Parseval twice;
eq 16: bounding the 8th Fourier moment via the 4th moment times a pointwise cap).
The route here is shorter: `matchCount_le_two_card_sq`
(`MatchCountAutocorr.lean`) gives the pointwise cap on `matchCount` directly, with
no Fourier transform needed at all, and combines with the already-proven
`sum_matchCount_eq_card_pow_four` to bound the second moment
`Σ_Δ matchCount(Δ)²` by `sup_Δ matchCount(Δ) · Σ_Δ matchCount(Δ)`.

Plugging into `PaleyZygmund.lean`'s already-proven `hit_count_ge_of_second_moment_bound`
reproduces advisory eq (17) exactly (in count form: `#{Δ : hit} ≥ B²/2`), confirming
the two routes agree. As with the rest of this project, this does NOT close the
open `E(S,S)` gap (advisory §7.4-7.6) — it only reproduces, by a cheaper route, the
same extremal `B²`-shortfall bound the advisory already identifies as falling short
of the target `Pr(X>0) ~ B⁴/N`. See `SidonEnergy.lean`'s header for that gap.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **Combinatorial (Fourier-free) second-moment bound**: given `SidonRepBound T`,
`Σ_Δ matchCount T Δ² ≤ 2 · B⁶`. This is `SecondMomentBound T (2·B⁶)` in the sense
of `PaleyZygmund.lean`, proved directly from `matchCount_le_two_card_sq` (the
pointwise cap) and `sum_matchCount_eq_card_pow_four` (the already-proven exact sum
`Σ_Δ matchCount T Δ = B⁴`), via `Σ Δ² ≤ (sup Δ) · Σ Δ`.

Note this is tighter than the advisory's own Fourier-derived bound (`< 2B⁶N` at
eq 16, before dividing by `N`) — expected, since the advisory's route goes through
an extra squaring step (bounding the 8th Fourier moment via the 4th) that this
direct route avoids. Both routes agree once carried through to the final
hit-count bound; see `sidon_gives_hit_count_bound_combinatorial` below. -/
theorem sidon_gives_second_moment_bound_combinatorial
    (T : Finset G) (hSidon : SidonRepBound T) :
    SecondMomentBound T (2 * (T.card : ℝ) ^ 6) := by
  unfold SecondMomentBound
  have hpt : ∀ Δ : G, (matchCount T Δ : ℝ) ^ 2 ≤
      (2 * (T.card : ℝ) ^ 2) * (matchCount T Δ : ℝ) := by
    intro Δ
    have hcap : matchCount T Δ ≤ 2 * T.card ^ 2 := matchCount_le_two_card_sq T hSidon Δ
    have hcap' : (matchCount T Δ : ℝ) ≤ 2 * (T.card : ℝ) ^ 2 := by exact_mod_cast hcap
    have hnn : (0:ℝ) ≤ matchCount T Δ := Nat.cast_nonneg _
    nlinarith
  have hsum_le :
      ∑ Δ : G, (matchCount T Δ : ℝ) ^ 2 ≤
        ∑ Δ : G, (2 * (T.card : ℝ) ^ 2) * (matchCount T Δ : ℝ) :=
    Finset.sum_le_sum (fun Δ _ => hpt Δ)
  have hsum_eq :
      ∑ Δ : G, (2 * (T.card : ℝ) ^ 2) * (matchCount T Δ : ℝ) =
        (2 * (T.card : ℝ) ^ 2) * ∑ Δ : G, (matchCount T Δ : ℝ) := by
    rw [Finset.mul_sum]
  have hbase : ∑ Δ : G, (matchCount T Δ : ℝ) = (T.card : ℝ) ^ 4 := by
    have h := sum_matchCount_eq_card_pow_four T
    have : (∑ Δ : G, (matchCount T Δ : ℝ)) = ((T.card ^ 4 : ℕ) : ℝ) := by
      rw [← h]; push_cast; rfl
    rw [this]; push_cast; ring
  calc ∑ Δ : G, (matchCount T Δ : ℝ) ^ 2
      ≤ ∑ Δ : G, (2 * (T.card : ℝ) ^ 2) * (matchCount T Δ : ℝ) := hsum_le
    _ = (2 * (T.card : ℝ) ^ 2) * ∑ Δ : G, (matchCount T Δ : ℝ) := hsum_eq
    _ = (2 * (T.card : ℝ) ^ 2) * (T.card : ℝ) ^ 4 := by rw [hbase]
    _ = 2 * (T.card : ℝ) ^ 6 := by ring

/-- **Hit-count bound, reproducing advisory eq (17)**: given `SidonRepBound T` and
`T` nonempty, at least `B²/2` values of `Δ` have `matchCount T Δ ≠ 0`. This is the
count form of advisory eq (17)'s `Pr(X>0) > B²/(2N)` — multiplying through by
`N = |G|` turns the probability bound into this count bound, and the two agree
exactly (see file header). Proved by composing
`sidon_gives_second_moment_bound_combinatorial` with the already-proven
`hit_count_ge_of_second_moment_bound` (`PaleyZygmund.lean`). -/
theorem sidon_gives_hit_count_bound_combinatorial
    (T : Finset G) (hSidon : SidonRepBound T) (hcard_pos : 0 < T.card) :
    (T.card : ℝ) ^ 2 / 2 ≤
      ((univ.filter (fun Δ => matchCount T Δ ≠ 0)).card : ℝ) := by
  have hM := sidon_gives_second_moment_bound_combinatorial T hSidon
  have hMpos : (0:ℝ) < 2 * (T.card : ℝ) ^ 6 := by
    have : (0:ℝ) < (T.card : ℝ) := by exact_mod_cast hcard_pos
    positivity
  have hstep := hit_count_ge_of_second_moment_bound T (2 * (T.card : ℝ) ^ 6) hM hMpos
  have heq : ((T.card : ℝ) ^ 4) ^ 2 / (2 * (T.card : ℝ) ^ 6) = (T.card : ℝ) ^ 2 / 2 := by
    have hne : (T.card : ℝ) ≠ 0 := by
      have : (0:ℝ) < (T.card : ℝ) := by exact_mod_cast hcard_pos
      exact ne_of_gt this
    field_simp
    try ring
  rw [heq] at hstep
  exact hstep
