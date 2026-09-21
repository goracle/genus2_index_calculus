import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.SidonEnergy
import Genus2Lean.MatchCountAutocorr
import Genus2Lean.IndexCalculusHitRate
set_option linter.style.header false

/-!
# What the `≤ 2`-representation (Sidon) bound does and does not buy for `hRate`

`IndexCalculusHitRate.lean` reduces `hRate` (`HitRate T c`) to bounds on
`matchCount T Δ = #{(a,b,c,d) ∈ T⁴ : a+b-c-d = Δ}`. The point-level `≤ 4`
fixed-target work of `ZeroD/` feeds `SidonRepBound T` (`repCount ≤ 2`). This
file records exactly how far that reaches, in two parts.

## Part 1 — a NEGATIVE result: no constant cap on `matchCount` at `Δ ≠ 0`

For `x ≠ y` in `T`, the quadruples `(x, b, b, y)`, `b ∈ T`, all solve
`a+b-c-d = x-y`, so `matchCount T (x - y) ≥ |T|`
(`card_le_matchCount_sub`; numerically it is about `4|T| - 4`, from the four
placements of the cancelling pair). Hence

    `∀ Δ ≠ 0, matchCount T Δ ≤ K`

is FALSE as soon as `|T| > K` and `T` has two distinct elements
(`not_uniform_matchCount_cap`). This is independent of any geometry.

Consequences, all consequences of the same fact:
* `hitRate_of_uniform_cap` (`IndexCalculusHitRate.lean`) and
  `offDiagonalBound_of_uniform_matchCount_bound(_four)`
  (`UniformFiberBoundOffDiagonal.lean`) are true but have UNSATISFIABLE
  hypotheses in the regime that matters (`B` large, `K` constant, `K = 4`
  means any factor base with `B ≥ 5`). They are vacuous, not merely unproved.
* So "`matchCount ≤ 4` for `Δ ≠ 0`" was never a viable target, for a reason
  much simpler than the class-shift counterexample recorded in
  `ROADMAP-alpha-locus.md`. The pointwise-cap route to `hRate` is closed;
  what remains is a bound OFF the trivially-large `Δ ∈ T - T`, plus control of
  the mass ON that set (`hitRate_of_good_overlap`, Part 2).

## Part 2 — a POSITIVE reduction to the plain sumset `S = T + T`

`matchCount T Δ = Σ_g r(g)·r(g-Δ)` with `r = repCount T`. Let `S` be the
support of `r`, i.e. `T + T` as a SET (`pairSumSet`), and
`overlap S Δ = |S ∩ (S + Δ)|` (`shiftOverlap`). Then, with no hypothesis,
`overlap ≤ matchCount` and `matchCount ≠ 0 ↔ overlap ≠ 0`
(`shiftOverlap_le_matchCount`, `matchCount_ne_zero_iff`), and given
`SidonRepBound T` (`r ≤ 2` pointwise)

    `matchCount T Δ ≤ 4 · overlap (T+T) Δ`     (`matchCount_le_four_mul_shiftOverlap`).

So multiplicities are gone: up to a factor 4, `matchCount` at `Δ` is the
number of ways `Δ` is a difference of two elements of the SET `T + T`.
`hitRate_of_good_overlap` then gives `HitRate` from (i) a cap on `overlap`
for `Δ` in a `good` set and (ii) at most half of the total mass `B⁴` sitting
off `good`.

## What this does NOT prove (the honest remaining content)

* (ii), the mass on the bad set. The natural `good` is `Δ ∉ T - T`; the mass
  on `T - T` is `#{(a,b,c,d) : a+b-c-d ∈ T-T}`, at most the number of
  solutions of `a+b+y = c+d+x` in `T⁶` (third additive energy of `T`). The
  `≤ 4` / `≤ 2`-representation bounds are about degree-2 divisor classes and
  say nothing about degree-3 sums (a degree-3 class on a genus-2 curve
  contains a P¹ of effective divisors), so this energy bound is NOT supplied
  by anything on file. Heuristically the trivial solutions contribute
  `~ 4B³ ≪ B⁴/2`. Numerically, for greedily built `T ⊂ ℤ/N` with
  `repCount ≤ 2` VERIFIED (`B = 14, 20, 26`, `N ≈ 2·10⁵, 4·10⁵, 10⁶`) the
  mass on `T - T ∖ {0}` was `0.25, 0.18, 0.14` of `B⁴`, tracking `4/B`; that
  is evidence at tiny `B` (where `N/B⁴` is only `~ 2`), not a proof.
* A related consequence, same numerics: `Σ_{Δ≠0} matchCount² ≈ 16–18 · B⁴`
  (`|T-T| · (4B)²`, dominated by the trivial solutions). So
  `OffDiagonalBound T (4·B⁴)` — the CONCLUSION of
  `offDiagonalBound_of_uniform_matchCount_bound_four` — is itself false for such
  `T`, not just its hypothesis; a second-moment bound `c·B⁴` needs `c ≳ 18`.
  A constant `c` is not refuted, and that is the shape
  `hitRate_of_tight_secondMoment` consumes, so the viable target is the second
  moment (equivalently the good-mass form here), not a pointwise cap.
* (i), the overlap cap off `T - T`, i.e. that the SET `T + T` has bounded
  difference multiplicity away from the trivial differences. That is a
  genuinely additive-combinatorial statement about the actual factor base.
* Nothing here shows `SidonRepBound T` for an actual `T = s(F)`; it is an
  explicit hypothesis, exactly as in `MatchCountAutocorr.lean`.

**Verification status:** drafted without a Lean toolchain, per the working
agreement; not `lake build`-checked. Lemma names not already used elsewhere
in the project were avoided where an in-project precedent existed
(`Finset.card_le_card_of_injOn` as in `SidonEnergy.lean`, `Finset.sum_subset`
as in `RatioDivisorCollapse.lean`).
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Part 1: the trivial solutions -/

/-- **The trivial quadruples.** For `x, y ∈ T`, the `|T|` quadruples
`(x, b, b, y)` all satisfy `x + b - b - y = x - y`, so `matchCount T (x - y)`
is at least `|T|`. No Sidon hypothesis, no geometry. -/
theorem card_le_matchCount_sub {T : Finset G} {x y : G} (hx : x ∈ T) (hy : y ∈ T) :
    T.card ≤ matchCount T (x - y) := by
  unfold matchCount
  apply Finset.card_le_card_of_injOn (fun b : G => (x, b, b, y))
  · intro b hb
    have hb' : b ∈ T := Finset.mem_coe.mp hb
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
    · simp only [Finset.mem_product]
      exact ⟨hx, hb', hb', hy⟩
    · show x + b - b - y = x - y
      abel
  · intro b _ b' _ h
    simpa using congrArg (fun q : G × G × G × G => q.2.1) h

/-- **No constant cap on `matchCount` at nonzero `Δ`.** If `T` has two distinct
elements `x ≠ y` and `K < |T|`, the uniform cap `∀ Δ ≠ 0, matchCount T Δ ≤ K`
fails (at `Δ = x - y`). In particular the hypotheses of
`hitRate_of_uniform_cap`, `offDiagonalBound_of_uniform_matchCount_bound` and
`offDiagonalBound_of_uniform_matchCount_bound_four` are unsatisfiable once
`|T| > K` (`K = 4`: `|T| ≥ 5`). -/
theorem not_uniform_matchCount_cap {T : Finset G} {x y : G} (hx : x ∈ T) (hy : y ∈ T)
    (hxy : x ≠ y) (K : ℕ) (hK : K < T.card) :
    ¬ ∀ Δ : G, Δ ≠ 0 → matchCount T Δ ≤ K := by
  intro hcap
  have h1 := hcap (x - y) (sub_ne_zero.mpr hxy)
  have h2 := card_le_matchCount_sub hx hy
  omega

/-! ## Part 2: reduction to the plain sumset `T + T` -/

/-- `T + T` as a SET (no multiplicity): the support of `repCount T`. -/
noncomputable def pairSumSet (T : Finset G) : Finset G :=
  (T ×ˢ T).image (fun p : G × G => p.1 + p.2)

/-- `overlap S Δ = |S ∩ (S + Δ)|`: the number of `g ∈ S` with `g - Δ ∈ S`,
i.e. the number of ways `Δ` is a difference of two elements of the set `S`. -/
noncomputable def shiftOverlap (S : Finset G) (Δ : G) : ℕ :=
  (S.filter (fun g => g - Δ ∈ S)).card

/-- `repCount` is positive exactly on the sumset. -/
theorem repCount_pos_iff_mem_pairSumSet (T : Finset G) (g : G) :
    0 < repCount T g ↔ g ∈ pairSumSet T := by
  unfold repCount pairSumSet
  rw [Finset.card_pos, Finset.mem_image]
  constructor
  · rintro ⟨p, hp⟩
    rw [Finset.mem_filter] at hp
    exact ⟨p, hp.1, hp.2⟩
  · rintro ⟨p, hp, hg⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hg⟩⟩

/-- **`matchCount` only sees `g ∈ S` with `g - Δ ∈ S`.** The autocorrelation sum
restricted to the overlap set; every other term has a zero factor. No Sidon
hypothesis. -/
theorem matchCount_eq_sum_overlap (T : Finset G) (Δ : G) :
    matchCount T Δ =
      ∑ g ∈ (pairSumSet T).filter (fun g => g - Δ ∈ pairSumSet T),
        repCount T g * repCount T (g - Δ) := by
  rw [matchCount_eq_autocorr]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro g _ hg
  by_cases h1 : g ∈ pairSumSet T
  · have h2 : g - Δ ∉ pairSumSet T := fun h2 => hg (Finset.mem_filter.mpr ⟨h1, h2⟩)
    have h0 : repCount T (g - Δ) = 0 := by
      by_contra hne
      exact h2 ((repCount_pos_iff_mem_pairSumSet T (g - Δ)).mp (Nat.pos_of_ne_zero hne))
    simp [h0]
  · have h0 : repCount T g = 0 := by
      by_contra hne
      exact h1 ((repCount_pos_iff_mem_pairSumSet T g).mp (Nat.pos_of_ne_zero hne))
    simp [h0]

/-- **Lower bound, no hypothesis:** `overlap (T+T) Δ ≤ matchCount T Δ`. Each
overlap element `g` contributes `r(g)·r(g-Δ) ≥ 1·1`. -/
theorem shiftOverlap_le_matchCount (T : Finset G) (Δ : G) :
    shiftOverlap (pairSumSet T) Δ ≤ matchCount T Δ := by
  rw [matchCount_eq_sum_overlap]
  unfold shiftOverlap
  calc ((pairSumSet T).filter (fun g => g - Δ ∈ pairSumSet T)).card
      = ∑ g ∈ (pairSumSet T).filter (fun g => g - Δ ∈ pairSumSet T), 1 := by simp
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro g hg
        rw [Finset.mem_filter] at hg
        have h1 : 0 < repCount T g := (repCount_pos_iff_mem_pairSumSet T g).mpr hg.1
        have h2 : 0 < repCount T (g - Δ) :=
          (repCount_pos_iff_mem_pairSumSet T (g - Δ)).mpr hg.2
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos h1 h2).ne'

/-- **Upper bound under `SidonRepBound`:** `matchCount T Δ ≤ 4 · overlap (T+T) Δ`.
Each of the `overlap` surviving terms is `r(g)·r(g-Δ) ≤ 2·2`. -/
theorem matchCount_le_four_mul_shiftOverlap (T : Finset G) (hSidon : SidonRepBound T)
    (Δ : G) :
    matchCount T Δ ≤ 4 * shiftOverlap (pairSumSet T) Δ := by
  rw [matchCount_eq_sum_overlap]
  unfold shiftOverlap
  calc ∑ g ∈ (pairSumSet T).filter (fun g => g - Δ ∈ pairSumSet T),
          repCount T g * repCount T (g - Δ)
      ≤ ∑ g ∈ (pairSumSet T).filter (fun g => g - Δ ∈ pairSumSet T), 4 := by
        apply Finset.sum_le_sum
        intro g _
        calc repCount T g * repCount T (g - Δ) ≤ 2 * 2 :=
              Nat.mul_le_mul (hSidon g) (hSidon (g - Δ))
          _ = 4 := by norm_num
    _ = 4 * ((pairSumSet T).filter (fun g => g - Δ ∈ pairSumSet T)).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- `matchCount` and `overlap` vanish at exactly the same `Δ`. No hypothesis. -/
theorem matchCount_ne_zero_iff (T : Finset G) (Δ : G) :
    matchCount T Δ ≠ 0 ↔ shiftOverlap (pairSumSet T) Δ ≠ 0 := by
  constructor
  · intro h h0
    apply h
    unfold shiftOverlap at h0
    rw [matchCount_eq_sum_overlap, Finset.card_eq_zero.mp h0]
    simp
  · intro h h0
    apply h
    have := shiftOverlap_le_matchCount T Δ
    omega

/-- **`hitCount` depends only on the SET `T + T`.** -/
theorem hitCount_eq_card_overlap_ne_zero (T : Finset G) :
    hitCount T =
      (Finset.univ.filter (fun Δ : G => shiftOverlap (pairSumSet T) Δ ≠ 0)).card := by
  unfold hitCount
  congr 1
  apply Finset.filter_congr
  intro Δ _
  exact matchCount_ne_zero_iff T Δ

/-- **The overlap analogue of the negative result.** Under `SidonRepBound`,
`overlap (T+T) (x - y) ≥ |T| / 4`, so a constant cap on the overlap of the
sumset at ALL `Δ ≠ 0` fails as well: the caps must exclude `T - T`. -/
theorem not_uniform_overlap_cap {T : Finset G} (hSidon : SidonRepBound T)
    {x y : G} (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y) (K : ℕ) (hK : 4 * K < T.card) :
    ¬ ∀ Δ : G, Δ ≠ 0 → shiftOverlap (pairSumSet T) Δ ≤ K := by
  intro hcap
  have h1 := hcap (x - y) (sub_ne_zero.mpr hxy)
  have h2 := card_le_matchCount_sub hx hy
  have h3 := matchCount_le_four_mul_shiftOverlap T hSidon (x - y)
  omega

/-- **`HitRate` from an overlap cap off a `good` set of `Δ`, plus half the mass
off `good` being small.** This is `hitRate_of_good_mass` with the pointwise cap
supplied by `matchCount ≤ 4 · overlap`. The natural `good` is `Δ ∉ T - T`
(by `not_uniform_matchCount_cap` the trivial `Δ ∈ T - T` cannot be capped); the
two open inputs are the overlap cap `hgood` and the bad-mass bound `hbad`,
neither supplied by any theorem on file (see module docstring). -/
theorem hitRate_of_good_overlap (T : Finset G) (hSidon : SidonRepBound T)
    (good : G → Prop) [DecidablePred good] (K badMass : ℕ) (hK : 0 < K)
    (hgood : ∀ Δ : G, good Δ → shiftOverlap (pairSumSet T) Δ ≤ K)
    (hbad : ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ good Δ), matchCount T Δ ≤ badMass)
    (hhalf : 2 * badMass ≤ T.card ^ 4) :
    HitRate T (2 * ((4 * K : ℕ) : ℝ)) := by
  refine hitRate_of_good_mass T good (4 * K) badMass (by omega) ?_ hbad hhalf
  intro Δ hΔ
  calc matchCount T Δ ≤ 4 * shiftOverlap (pairSumSet T) Δ :=
        matchCount_le_four_mul_shiftOverlap T hSidon Δ
    _ ≤ 4 * K := Nat.mul_le_mul (le_refl 4) (hgood Δ hΔ)
