import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.PaleyZygmund
import Genus2Lean.IndexCalculusComplexity
set_option linter.style.header false

/-!
# `hRate`, made explicit: the distinct-hit rate

`IndexCalculusComplexity.lean` derives `B ~ p^(2/5)` and total cost `p^(4/5)`
from a per-solve success rate `B⁴/p²`, which it calls `hRate`. That name only
appears in prose there: the rate is baked into the *definition*
`expectedRelations`, so nothing in Lean connects it to `matchCount`. This file
supplies the connection.

## What `hRate` is

A solve lands on a target `Δ ∈ G` and succeeds iff `matchCount F Δ ≠ 0`, i.e.
`Δ ∈ (F+F) − (F+F)`. For a uniformly random `Δ` the success probability is
`hitCount F / |G|`, and `hRate` says `hitCount F ≳ B⁴`. Since
`∑_Δ matchCount F Δ = B⁴` exactly (`sum_matchCount_eq_card_pow_four`), this is
the statement that the *average multiplicity over realized `Δ` is `O(1)`*.
The gauge-dedup argument (`IndexCalculusRelations.lean`) shows a repeated hit
adds no incorrect relation; it does not make repeated hits free, because each
one uses up mass a fresh `Δ` would have used.

## Definitions and results

* `hitCount F`, `HitRate F c` — `hRate` as a named hypothesis: at least a
  `B⁴/(c·|G|)` fraction of `G` is realized.
* Proved sufficient conditions, each giving `HitRate F c` for explicit `c`:
  `hitRate_of_tight_secondMoment` (`SecondMomentBound F (c·B⁴)`),
  `hitRate_of_uniform_cap` (`matchCount F Δ ≤ K` for every `Δ ≠ 0`),
  `hitRate_of_good_mass` (a cap `K` off a "bad" set of `Δ` carrying at most
  half the total mass — weaker than a uniform cap).
* Bridge to the model: `expectedRelations_le_of_hitRate`,
  `expected_successes_at_balance`.

## What does NOT supply `HitRate`

* The unconditional bound (`matchCount_distinct_hits_ge_unconditional`) gives
  only `hitCount ≳ B`; Sidon-ness alone gives only `~B²`
  (`sidon_gives_hit_count_bound_combinatorial`). Neither is close: at `~B`
  hits the attack costs `~p²`, at `~B²` about `p^(4/3)`, both worse than the
  generic `√|G| = p`. Only `~B⁴` reproduces `p^(4/5)`. Sidon-ness cannot be
  improved to reach it: a Sidon set of size `B` inside an interval of length
  `O(B²)` of `ℤ/ℓ` has `|F+F−F−F| = O(B²)`.
* Anything about points-per-class (the `ZeroD/` finiteness/degree work): that
  bounds how many point-quadruples give one pair of classes, whereas `HitRate`
  is about how the class-sums `F+F` overlap under translation.

## A normalization trap (`SidonBridge.lean`)

`card_le_of_normalized_secondMomentBound` shows that a hypothesis of the shape
`∑_Δ matchCount² ≤ C·B⁴/|G|` forces `|G| ≤ C`, because `m² ≥ m` over `ℕ`
gives `∑_Δ matchCount² ≥ B⁴`. `SidonBridge.lean`'s `GenericFactorBase` has
exactly this shape (its docstring describes the *normalized* expectation
`(∑ matchCount²)/|G|`, but the definition states the un-normalized sum), so it
is unsatisfiable for large `G` when `|s(F)| = |F|`, and
`hitCount_ge_of_generic` is vacuous. The correct hypothesis is
`SecondMomentBound F (C·B⁴)`, which is what `Complexity.lean` uses.
(`Complexity.lean`'s `hitProb_ge_of_tight_secondMoment` has a milder issue: its
conclusion is the raw *count* `≥ B⁴/(c·N)`, not the fraction its docstring
describes; `hitRate_of_tight_secondMoment` below is the fraction form.)

## Still unstated in the model

`expectedRelations` charges unit cost per solve. That is the uniform-degree /
0-dimensionality content of `ZeroD/` (`decoupledSystem_degree_uniform`), a
hypothesis different from and independent of `hRate`.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- `hitCount F` is the number of `Δ ∈ G` realized by some quadruple of `F`
(`matchCount F Δ ≠ 0`), i.e. `|(F+F) − (F+F)|`. It includes `Δ = 0`, which is
realized by every quadruple `(a,b,a,b)` and is useless as a relation; that is
one element of `G`, and this is the count `Paley–Zygmund` produces. -/
noncomputable def hitCount (F : Finset G) : ℕ :=
  (Finset.univ.filter (fun Δ : G => matchCount F Δ ≠ 0)).card

/-- **`hRate`, as a named hypothesis.** At least a `B⁴/(c·|G|)` fraction of
`Δ ∈ G` is realized by some quadruple of `F`. With `c = 1` this is the
"every quadruple lands on its own `Δ`" extreme; `c` measures the average
multiplicity over realized `Δ`. -/
def HitRate (F : Finset G) (c : ℝ) : Prop :=
  (F.card : ℝ) ^ 4 / (c * (Fintype.card G : ℝ)) ≤
    (hitCount F : ℝ) / (Fintype.card G : ℝ)

/-- The second moment is always at least `B⁴`: over `ℕ`, `m ≤ m²`, and
`∑_Δ matchCount T Δ = B⁴`. -/
theorem card_pow_four_le_secondMoment (T : Finset G) :
    T.card ^ 4 ≤ ∑ Δ : G, (matchCount T Δ) ^ 2 := by
  calc T.card ^ 4 = ∑ Δ : G, matchCount T Δ := (sum_matchCount_eq_card_pow_four T).symm
    _ ≤ ∑ Δ : G, (matchCount T Δ) ^ 2 :=
        Finset.sum_le_sum (fun Δ _ => by rw [sq]; exact Nat.le_mul_self _)

/-- Real-valued form: any `SecondMomentBound T M` has `M ≥ B⁴`. -/
theorem card_pow_four_le_of_secondMomentBound (T : Finset G) (M : ℝ)
    (hM : SecondMomentBound T M) : (T.card : ℝ) ^ 4 ≤ M := by
  have h := card_pow_four_le_secondMoment T
  have hR : (T.card : ℝ) ^ 4 ≤ ∑ Δ : G, (matchCount T Δ : ℝ) ^ 2 := by
    exact_mod_cast h
  have hM' : ∑ Δ : G, (matchCount T Δ : ℝ) ^ 2 ≤ M := hM
  exact le_trans hR hM'

/-- **Normalization trap.** A second-moment bound of the shape
`C · B⁴ / |G|` (as in `SidonBridge.lean`'s `GenericFactorBase`, whose
docstring means the *normalized* `(∑ matchCount²)/|G|` but whose definition
states the un-normalized sum) forces `|G| ≤ C`. So for `|G| > C` no nonempty
`T` satisfies it, and any theorem conditional on it is vacuous. -/
theorem card_le_of_normalized_secondMomentBound
    (T : Finset G) (hT : 0 < T.card) (C : ℝ)
    (hM : SecondMomentBound T (C * (T.card : ℝ) ^ 4 / (Fintype.card G : ℝ))) :
    (Fintype.card G : ℝ) ≤ C := by
  have h1 := card_pow_four_le_of_secondMomentBound T _ hM
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have hTR : (0:ℝ) < (T.card : ℝ) := by exact_mod_cast hT
  have hB4 : (0:ℝ) < (T.card : ℝ) ^ 4 := by positivity
  have h2 : (T.card : ℝ) ^ 4 * (Fintype.card G : ℝ) ≤ C * (T.card : ℝ) ^ 4 :=
    (le_div_iff₀ hN).mp h1
  have h3 : (T.card : ℝ) ^ 4 * (Fintype.card G : ℝ) ≤ (T.card : ℝ) ^ 4 * C := by
    calc (T.card : ℝ) ^ 4 * (Fintype.card G : ℝ) ≤ C * (T.card : ℝ) ^ 4 := h2
      _ = (T.card : ℝ) ^ 4 * C := mul_comm _ _
  exact le_of_mul_le_mul_left h3 hB4

/-- **Common tail of every sufficient condition.** A natural-number bound
`B⁴ ≤ 2 · K · hitCount F` (with `K > 0`) is exactly `HitRate F (2K)`. -/
theorem hitRate_of_nat_bound (F : Finset G) (K : ℕ) (hK : 0 < K)
    (h : F.card ^ 4 ≤ 2 * (K * hitCount F)) : HitRate F (2 * (K : ℝ)) := by
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have hKR : (0:ℝ) < (K : ℝ) := by exact_mod_cast hK
  have h2pos : (0:ℝ) < 2 * (K : ℝ) := by linarith
  have hcN : (0:ℝ) < 2 * (K : ℝ) * (Fintype.card G : ℝ) := mul_pos h2pos hN
  have hR : (F.card : ℝ) ^ 4 ≤ 2 * ((K : ℝ) * (hitCount F : ℝ)) := by
    exact_mod_cast h
  unfold HitRate
  rw [div_le_div_iff₀ hcN hN]
  calc (F.card : ℝ) ^ 4 * (Fintype.card G : ℝ)
      ≤ (2 * ((K : ℝ) * (hitCount F : ℝ))) * (Fintype.card G : ℝ) :=
        mul_le_mul_of_nonneg_right hR hN.le
    _ = (hitCount F : ℝ) * (2 * (K : ℝ) * (Fintype.card G : ℝ)) := by ring

/-- **`hRate` from a tight second moment (fraction form).** If
`SecondMomentBound F (c · B⁴)` then at least a `B⁴/(c·|G|)` fraction of `G` is
realized. This is `hit_count_ge_of_second_moment_bound` divided by `|G|`; it
is the statement `Complexity.lean`'s `hitProb_ge_of_tight_secondMoment`
describes in its docstring (that theorem's conclusion is the un-normalized
count, which is far weaker). -/
theorem hitRate_of_tight_secondMoment (F : Finset G) (c : ℝ) (hc : 0 < c)
    (hFcard : 0 < F.card)
    (hSecondMoment : SecondMomentBound F (c * (F.card : ℝ) ^ 4)) :
    HitRate F c := by
  have hFcardR : (0:ℝ) < (F.card : ℝ) := by exact_mod_cast hFcard
  have hFcardRne : (F.card : ℝ) ≠ 0 := ne_of_gt hFcardR
  have hcne : c ≠ 0 := ne_of_gt hc
  have hMpos : 0 < c * (F.card : ℝ) ^ 4 := by positivity
  have hcount := hit_count_ge_of_second_moment_bound F (c * (F.card : ℝ) ^ 4)
    hSecondMoment hMpos
  have heq : ((F.card : ℝ) ^ 4) ^ 2 / (c * (F.card : ℝ) ^ 4) = (F.card : ℝ) ^ 4 / c := by
    field_simp
  rw [heq] at hcount
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hN : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have h1 : (F.card : ℝ) ^ 4 ≤
      ((univ.filter (fun Δ : G => matchCount F Δ ≠ 0)).card : ℝ) * c := by
    rwa [div_le_iff₀ hc] at hcount
  unfold HitRate hitCount
  rw [div_le_div_iff₀ (mul_pos hc hN) hN]
  calc (F.card : ℝ) ^ 4 * (Fintype.card G : ℝ)
      ≤ (((univ.filter (fun Δ : G => matchCount F Δ ≠ 0)).card : ℝ) * c) *
          (Fintype.card G : ℝ) := mul_le_mul_of_nonneg_right h1 hN.le
    _ = ((univ.filter (fun Δ : G => matchCount F Δ ≠ 0)).card : ℝ) *
          (c * (Fintype.card G : ℝ)) := by ring

/-- **`hRate` from a uniform pointwise cap.** If `matchCount F Δ ≤ K` for every
`Δ ≠ 0` (the `matchCount ≤ 4`-shaped target of the old `ROADMAP-alpha-locus.md`)
and `B ≥ 2`, then `HitRate F (2K)`. The `Δ = 0` term is at most `B³`
(`matchCount_le_card_cubed`), which is at most half of `B⁴` once `B ≥ 2`. -/
theorem hitRate_of_uniform_cap (F : Finset G) (K : ℕ) (hK : 0 < K)
    (hB : 2 ≤ F.card) (hcap : ∀ Δ : G, Δ ≠ 0 → matchCount F Δ ≤ K) :
    HitRate F (2 * (K : ℝ)) := by
  have h1 := matchCount_distinct_hits_ge F K
    (fun Δ hΔ => hcap Δ (Finset.mem_filter.mp hΔ).2)
  have hsub : ((Finset.univ.filter (fun Δ : G => Δ ≠ 0)).filter
        (fun Δ : G => 0 < matchCount F Δ)) ⊆
      Finset.univ.filter (fun Δ : G => matchCount F Δ ≠ 0) := by
    intro Δ hΔ
    rw [Finset.mem_filter] at hΔ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hΔ.2.ne'⟩
  have hcard := Finset.card_le_card hsub
  have hm0 : matchCount F 0 ≤ F.card ^ 3 := matchCount_le_card_cubed F 0
  have h4 : 2 * F.card ^ 3 ≤ F.card ^ 4 := by
    calc 2 * F.card ^ 3 ≤ F.card * F.card ^ 3 := Nat.mul_le_mul hB (le_refl _)
      _ = F.card ^ 4 := by ring
  have h5 : K * ((Finset.univ.filter (fun Δ : G => Δ ≠ 0)).filter
        (fun Δ : G => 0 < matchCount F Δ)).card ≤ K * hitCount F :=
    Nat.mul_le_mul (le_refl K) hcard
  have h6 : F.card ^ 4 - matchCount F 0 ≤ K * hitCount F := le_trans h1 h5
  apply hitRate_of_nat_bound F K hK
  omega

/-- **Mass accounting for a cap that holds only off a bad set.** If
`matchCount F Δ ≤ K` for every `Δ` satisfying `good`, and the `Δ` failing
`good` carry total mass at most `badMass`, then
`B⁴ ≤ badMass + K · hitCount F`. This is the shape a genuinely hard uniform
bound would take once exceptional `Δ` (the `Bad` set of `ROADMAP-alpha-locus.md`)
are set aside: it needs the *mass* on the bad `Δ` to be small, not their
number. -/
theorem hitCount_bound_of_good_mass (F : Finset G) (good : G → Prop)
    [DecidablePred good] (K badMass : ℕ)
    (hgood : ∀ Δ : G, good Δ → matchCount F Δ ≤ K)
    (hbad : ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ good Δ), matchCount F Δ ≤ badMass) :
    F.card ^ 4 ≤ badMass + K * hitCount F := by
  have htotal : ∑ Δ : G, matchCount F Δ = F.card ^ 4 := sum_matchCount_eq_card_pow_four F
  have hsplit :
      ∑ Δ ∈ Finset.univ.filter good, matchCount F Δ +
        ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ good Δ), matchCount F Δ =
      ∑ Δ : G, matchCount F Δ :=
    Finset.sum_filter_add_sum_filter_not Finset.univ good (fun Δ => matchCount F Δ)
  have hgoodsum :
      ∑ Δ ∈ Finset.univ.filter good, matchCount F Δ ≤ K * hitCount F := by
    have h1 := card_pos_ge_of_sum_le_mul (Finset.univ.filter good) (matchCount F)
      (∑ Δ ∈ Finset.univ.filter good, matchCount F Δ) K rfl
      (fun Δ hΔ => hgood Δ (Finset.mem_filter.mp hΔ).2)
    have hsub : ((Finset.univ.filter good).filter (fun Δ : G => 0 < matchCount F Δ)) ⊆
        Finset.univ.filter (fun Δ : G => matchCount F Δ ≠ 0) := by
      intro Δ hΔ
      rw [Finset.mem_filter] at hΔ
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hΔ.2.ne'⟩
    have hcard := Finset.card_le_card hsub
    have h2 : K * ((Finset.univ.filter good).filter
        (fun Δ : G => 0 < matchCount F Δ)).card ≤ K * hitCount F :=
      Nat.mul_le_mul (le_refl K) hcard
    exact le_trans h1 h2
  calc F.card ^ 4 = ∑ Δ : G, matchCount F Δ := htotal.symm
    _ = ∑ Δ ∈ Finset.univ.filter good, matchCount F Δ +
          ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ good Δ), matchCount F Δ := hsplit.symm
    _ ≤ K * hitCount F + badMass := Nat.add_le_add hgoodsum hbad
    _ = badMass + K * hitCount F := Nat.add_comm _ _

/-- **`hRate` from a cap off a bad set of at most half the mass.** Weaker than
`hitRate_of_uniform_cap`: `matchCount F Δ ≤ K` is only needed for `good` `Δ`, and
the remaining `Δ` may be arbitrary as long as they carry at most half of `B⁴`. -/
theorem hitRate_of_good_mass (F : Finset G) (good : G → Prop) [DecidablePred good]
    (K badMass : ℕ) (hK : 0 < K)
    (hgood : ∀ Δ : G, good Δ → matchCount F Δ ≤ K)
    (hbad : ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ good Δ), matchCount F Δ ≤ badMass)
    (hhalf : 2 * badMass ≤ F.card ^ 4) :
    HitRate F (2 * (K : ℝ)) := by
  have hmain := hitCount_bound_of_good_mass F good K badMass hgood hbad
  apply hitRate_of_nat_bound F K hK
  omega

/-- **Bridge to the model.** Under `HitRate F c` and `|G| = p²`, the model's
`expectedRelations N B p = N · B⁴/p²` (with `B = |F|`) is at most
`c · N · hitCount F / |G|`, i.e. `c` times the exact expected number of
successful solves among `N` independent uniformly random targets. -/
theorem expectedRelations_le_of_hitRate (F : Finset G) (c N p : ℝ) (hc : 0 < c)
    (hN : 0 ≤ N) (hp : (Fintype.card G : ℝ) = p ^ 2) (hRate : HitRate F c) :
    expectedRelations N (F.card : ℝ) p ≤
      c * (N * ((hitCount F : ℝ) / (Fintype.card G : ℝ))) := by
  unfold expectedRelations
  unfold HitRate at hRate
  rw [← hp]
  have hNpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨0⟩
  have hGpos : (0:ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hNpos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hGne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hGpos
  have h2 : (F.card : ℝ) ^ 4 / (Fintype.card G : ℝ) =
      c * ((F.card : ℝ) ^ 4 / (c * (Fintype.card G : ℝ))) := by
    field_simp
  calc N * ((F.card : ℝ) ^ 4 / (Fintype.card G : ℝ))
      = N * (c * ((F.card : ℝ) ^ 4 / (c * (Fintype.card G : ℝ)))) := by rw [h2]
    _ ≤ N * (c * ((hitCount F : ℝ) / (Fintype.card G : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRate hc.le) hN
    _ = c * (N * ((hitCount F : ℝ) / (Fintype.card G : ℝ))) := by ring

/-- **The balance point, end to end from `HitRate`.** With `B⁵ = p² = |G|`, running
`N = B²` solves at random targets yields, in expectation, at least `B / c`
successes: `B ≤ c · (B² · hitCount F / |G|)`. Together with `total_cost_eq_rpow`
(`IndexCalculusComplexity.lean`) this is the whole `p^(4/5)` claim, with
`HitRate F c` as its only yield hypothesis. (These are successful solves; that
the `~B` successes land on distinct `Δ` is a separate birthday-type estimate,
not formalized.) -/
theorem expected_successes_at_balance (F : Finset G) (c p : ℝ) (hc : 0 < c)
    (hp : 0 < p) (hcardG : (Fintype.card G : ℝ) = p ^ 2) (hFpos : 0 < F.card)
    (hbal : (F.card : ℝ) ^ 5 = p ^ 2) (hRate : HitRate F c) :
    (F.card : ℝ) ≤
      c * ((F.card : ℝ) ^ 2 * ((hitCount F : ℝ) / (Fintype.card G : ℝ))) := by
  have hB : (0:ℝ) < (F.card : ℝ) := by exact_mod_cast hFpos
  have h := expectedRelations_le_of_hitRate F c ((F.card : ℝ) ^ 2) p hc
    (by positivity) hcardG hRate
  rw [expectedRelations_at_balance (F.card : ℝ) p hB hp hbal] at h
  exact h
