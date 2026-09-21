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
file records exactly how far that reaches, in four parts (Part 0, Parts 1-2,
Part 3 — see each part's own heading; Part 3 also corrects an error in an
earlier pass of this docstring, flagged there).

## Part 0 — the exclusion is exact, not just directionally suggestive

`trivial_quadruple_mem_sub`/`not_trivial_of_not_mem_sub`: the trivial
cancelling family (`(x,b,b,y)` and its three sign/position variants) occurs
ONLY on `Δ ∈ T - T`, no more and no less — i.e. `good := {Δ | Δ ∉ T - T}` is
exactly the complement of where cancellation can happen, not merely a set
chosen to make the bound below go through. This formalizes the "the rest of
the solutions have to be outside the fb" reading of Part 1: a `(U,V)` draw
whose resulting `Δ` avoids `T - T` is never secretly one of the forced
trivial hits, so restricting to `good` genuinely removes the pollution
Part 1 identifies, rather than just avoiding its worst instances.

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
* ~~(i), the overlap cap off `T - T`~~ — **RESOLVED, Part 3, this pass**:
  `overlap_le_sidon_energy` gives `overlap(Δ) ≤ 2B²` for EVERY `Δ`
  unconditionally from `SidonRepBound`, no `T - T` exclusion needed. An
  earlier pass of this docstring called this "a genuinely
  additive-combinatorial statement about the actual factor base" needing
  more than Sidon; that was wrong (Cauchy-Schwarz on the autocorrelation
  identity gets it directly, see Part 3). What (i)'s resolution does NOT
  buy: the resulting constant is `c = Θ(B²)`, not the `O(1)` `hRate` needs —
  see Part 3's module note for exactly what closing that gap would still
  require (a low-energy hypothesis on the sumset `T+T` itself, not on `T`).
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

/-- **The trivial family lives exactly on `T - T`, and nowhere else.**
Converse to `card_le_matchCount_sub`: if `Δ` is realized by a "trivial"
quadruple — one with a cancelling repeated entry, `(x,b,b,y)` or any of its
three sign/position variants `(x,b,y,b)`, `(b,x,b,y)`, `(b,x,y,b)` — then
`Δ = x - y` for some `x, y ∈ T`. Stated as the existential directly
(`∃ x ∈ T, ∃ y ∈ T, Δ = x - y`) rather than via `Finset`'s `-` instance or a
`Finset.mem_sub`-style lemma, to sidestep checking that instance's exact
definitional unfolding without a Lean toolchain; a caller with `Δ ∈ T - T`
in hand should be able to unfold that to this existential in one step, but
that translation is left to the caller.

This is the precise converse the model needs: it says a solve landing on
`Δ ∉ T - T` is *never* one of the trivial cancelling quadruples, so on that
set `matchCount` carries no forced floor and its whole value is genuine
overlap content, not an artifact of the cancelling family
`not_uniform_matchCount_cap` uses to kill the uniform-cap route. This is
exactly why `good := {Δ | Δ ∉ T - T}` (as used in `hitRate_of_good_overlap`)
is the right exceptional set, rather than an arbitrary choice: it is exactly
the complement of where the trivial family can occur, not merely a set that
happens to make the bound go through. -/
theorem trivial_quadruple_mem_sub {T : Finset G} {a b c d Δ : G}
    (hmatch : a + b - c - d = Δ)
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T)
    (htrivial : (a = c) ∨ (a = d) ∨ (b = c) ∨ (b = d)) :
    ∃ x ∈ T, ∃ y ∈ T, Δ = x - y := by
  rcases htrivial with hac | had | hbc | hbd
  · -- a = c: Δ = a + b - a - d = b - d
    exact ⟨b, hb, d, hd, by rw [← hmatch, hac]; abel⟩
  · -- a = d: Δ = a + b - c - a = b - c
    exact ⟨b, hb, c, hc, by rw [← hmatch, had]; abel⟩
  · -- b = c: Δ = a + b - b - d = a - d
    exact ⟨a, ha, d, hd, by rw [← hmatch, hbc]; abel⟩
  · -- b = d: Δ = a + b - c - b = a - c
    exact ⟨a, ha, c, hc, by rw [← hmatch, hbd]; abel⟩

/-- **Corollary, in `good`-exclusion form.** If `Δ ∉ T - T` (no `x, y ∈ T`
with `Δ = x - y`), then no quadruple of `T⁴` solving `matchCount`'s equation
has a cancelling repeated entry in any of the four trivial positions. This is
the contrapositive of `trivial_quadruple_mem_sub`, stated the way
`hitRate_of_good_overlap`'s `good` predicate will actually be used: as a
membership test on `Δ`, not on the witnessing quadruple. -/
theorem not_trivial_of_not_mem_sub {T : Finset G} {Δ : G}
    (hΔ : ¬ ∃ x ∈ T, ∃ y ∈ T, Δ = x - y)
    {a b c d : G} (hmatch : a + b - c - d = Δ)
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro heq <;> apply hΔ
  · exact trivial_quadruple_mem_sub hmatch ha hb hc hd (Or.inl heq)
  · exact trivial_quadruple_mem_sub hmatch ha hb hc hd (Or.inr (Or.inl heq))
  · exact trivial_quadruple_mem_sub hmatch ha hb hc hd (Or.inr (Or.inr (Or.inl heq)))
  · exact trivial_quadruple_mem_sub hmatch ha hb hc hd (Or.inr (Or.inr (Or.inr heq)))

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

/-! ## Part 3: the unconditional overlap cap (correction, this pass)

**Correction to Part 0's framing.** An earlier pass of this docstring
claimed `SidonRepBound` alone cannot bound `shiftOverlap` — that this was a
genuinely additive-combinatorial fact needing more structure than Sidon
supplies. That claim was WRONG, caught by an external check (ChatGPT,
prompted with exactly this question): `SidonRepBound` gives
`overlap (pairSumSet T) Δ ≤ 2 · T.card ^ 2` for EVERY `Δ`, unconditionally,
via Cauchy–Schwarz on the autocorrelation identity — no `T - T` exclusion,
no `good` set, no extra hypothesis needed. The confusion was mixing up
`|T+T|` (which Sidon forces to be LARGE, `≥ B²/2`) with `overlap(Δ)` (which
Cauchy–Schwarz bounds regardless of how large the ambient set `T+T` is).

**What this does and does not buy.** `overlap_le_sidon_energy` below,
combined with `hitRate_of_good_overlap` (`good := fun _ => True`, trivial),
gives `HitRate T c` for `c = Θ(B²)`. This is a real, unconditional theorem —
but it is far weaker than the `c = O(1)` the model actually wants
(`hitCount ≳ B⁴`, not `≳ B²`): plugging `c ~ B²` into `HitRate` only gives
`hitCount ≳ B²`, four orders of `B` short. So Part 0's exclusion of the
trivial family and this section's overlap cap are both real and both
necessary, but neither is SUFFICIENT for `hRate`; genuinely closing that gap
would need something like `E(T+T) ≲ |T+T|⁴/|G|` (a low-energy/genericity
hypothesis on the SUMSET `T+T`, not on `T` itself — Sidon-ness of `T` says
nothing about it) — a new named hypothesis, not derivable from `SidonRepBound`
alone, and not attempted here.

`hitCount_le_card_pow_four` records the complementary elementary fact
(no Sidon needed): `hitCount T ≤ B⁴`, since `hitCount = |pairSumSet T -
pairSumSet T|` as a plain set difference, and `|S - S| ≤ |S|² ≤ (B²)²`. This
puts `HitRate`'s target `hitCount ≳ B⁴/c` (for constant `c`) in context: it
asks `hitCount` to be within a constant factor of its own a priori MAXIMUM,
not for any kind of positive density inside `G` — `HitRate`'s two sides both
divide by `|G|`, so `|G|` cancels out of the actual content. (An external
check that first read `HitRate` as a density-in-`G` claim consequently
flagged `B⁴/|G| → 0` in the `B ~ p^(2/5)`, `|G| ~ p²` regime as an
"arithmetic impossibility" — correctly computed, but for a different,
stronger statement than the one `HitRate` actually makes; recorded here so a
future pass doesn't need to re-derive which reading is the right one.) -/

/-- **Overlap is bounded by the additive energy `E(T)`, unconditionally in
`Δ`.** `overlap(Δ) = |{g ∈ pairSumSet T : g - Δ ∈ pairSumSet T}|`, and every
such `g` contributes at least `1 ≤ r(g)·r(g-Δ)` to
`Q(Δ) := ∑_h r(h)·r(h-Δ) = matchCount T Δ` (`matchCount_eq_autocorr`). So
`overlap(Δ) ≤ matchCount T Δ` (this direction is `shiftOverlap_le_matchCount`,
already on file, no Sidon needed). Cauchy–Schwarz then bounds `matchCount`
itself: `Q(Δ)² = (∑_h r(h)·r(h-Δ))² ≤ (∑_h r(h)²)·(∑_h r(h-Δ)²) = E(T)²`
(`Finset.sum_mul_sq_le_sq_mul_sq`, reindexing the second factor by
`h ↦ h - Δ`, a bijection of `G`), so `Q(Δ) ≤ E(T) ≤ 2B²`
(`sidon_energy_bound_nat`). Composing the two gives the bound stated. -/
theorem overlap_le_sidon_energy (T : Finset G) (hSidon : SidonRepBound T) (Δ : G) :
    shiftOverlap (pairSumSet T) Δ ≤ 2 * T.card ^ 2 := by
  have hoverlap_le_match : shiftOverlap (pairSumSet T) Δ ≤ matchCount T Δ :=
    shiftOverlap_le_matchCount T Δ
  have hcs : (matchCount T Δ : ℝ) ^ 2 ≤
      (∑ g : G, (repCount T g : ℝ) ^ 2) * ∑ g : G, (repCount T (g - Δ) : ℝ) ^ 2 := by
    have heq : (matchCount T Δ : ℝ) =
        ∑ g : G, (repCount T g : ℝ) * (repCount T (g - Δ) : ℝ) := by
      rw [matchCount_eq_autocorr, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro g _
      exact Nat.cast_mul _ _
    rw [heq]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun g => (repCount T g : ℝ)) (fun g => (repCount T (g - Δ) : ℝ))
  have hreindex : (∑ g : G, (repCount T (g - Δ) : ℝ) ^ 2) = ∑ g : G, (repCount T g : ℝ) ^ 2 := by
    have hgoal := Fintype.sum_equiv (Equiv.addRight (-Δ))
      (fun g : G => (repCount T (g - Δ) : ℝ) ^ 2)
      (fun g : G => (repCount T g : ℝ) ^ 2)
      (fun g => by
        have : (Equiv.addRight (-Δ)) g = g - Δ := by
          simp [Equiv.coe_addRight, sub_eq_add_neg]
        rw [this])
    exact hgoal
  rw [hreindex] at hcs
  have hE : (∑ g : G, (repCount T g : ℝ) ^ 2) ≤ 2 * (T.card : ℝ) ^ 2 := by
    have h := sidon_energy_bound_nat T hSidon
    have h' : (∑ g : G, (repCount T g) ^ 2 : ℝ) ≤ ((2 * T.card ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa using h'
  have hcs' : (matchCount T Δ : ℝ) ^ 2 ≤ (2 * (T.card : ℝ) ^ 2) ^ 2 := by
    calc (matchCount T Δ : ℝ) ^ 2
        ≤ (∑ g : G, (repCount T g : ℝ) ^ 2) * (∑ g : G, (repCount T g : ℝ) ^ 2) := hcs
      _ ≤ (2 * (T.card : ℝ) ^ 2) * (2 * (T.card : ℝ) ^ 2) :=
          mul_le_mul hE hE (by positivity) (by positivity)
      _ = (2 * (T.card : ℝ) ^ 2) ^ 2 := by ring
  have hmatch_le : (matchCount T Δ : ℝ) ≤ 2 * (T.card : ℝ) ^ 2 := by
    have hnn : (0:ℝ) ≤ 2 * (T.card : ℝ) ^ 2 := by positivity
    nlinarith [sq_nonneg ((matchCount T Δ : ℝ) - 2 * (T.card : ℝ) ^ 2)]
  have hmatch_le' : matchCount T Δ ≤ 2 * T.card ^ 2 := by exact_mod_cast hmatch_le
  exact le_trans hoverlap_le_match hmatch_le'

/-- **`hitCount` is bounded by `B⁴`, unconditionally — no Sidon needed.**
`hitCount T = |{Δ : matchCount T Δ ≠ 0}| = |{Δ : overlap(Δ) ≠ 0}|`
(`hitCount_eq_card_overlap_ne_zero`) `= |pairSumSet T - pairSumSet T|` (as a
plain set difference: `Δ` is realized iff `Δ = g - g'` for some
`g, g' ∈ pairSumSet T`), and the difference map `pairSumSet T ×ˢ pairSumSet T
→ G` has image of size at most `(pairSumSet T).card ^ 2 ≤ (T.card ^ 2) ^ 2`
(`Finset.card_image_le`). Puts `HitRate`'s target `hitCount ≳ B⁴/c` in its
correct place: near the top of `hitCount`'s own possible range, not a
density claim about `|G|` (see the Part 3 module note above). -/
theorem hitCount_le_card_pow_four (T : Finset G) :
    hitCount T ≤ T.card ^ 4 := by
  have hset : (Finset.univ.filter (fun Δ : G => matchCount T Δ ≠ 0)) ⊆
      (pairSumSet T ×ˢ pairSumSet T).image (fun p : G × G => p.1 - p.2) := by
    intro Δ hΔ
    rw [Finset.mem_filter] at hΔ
    have hov : shiftOverlap (pairSumSet T) Δ ≠ 0 := (matchCount_ne_zero_iff T Δ).mp hΔ.2
    unfold shiftOverlap at hov
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hov)
    rw [Finset.mem_filter] at hg
    apply Finset.mem_image.mpr
    exact ⟨(g, g - Δ), Finset.mem_product.mpr ⟨hg.1, hg.2⟩, by
      show g - (g - Δ) = Δ
      exact sub_sub_cancel g Δ⟩
  have hcard := Finset.card_le_card hset
  have himg : ((pairSumSet T ×ˢ pairSumSet T).image (fun p : G × G => p.1 - p.2)).card ≤
      (pairSumSet T ×ˢ pairSumSet T).card := Finset.card_image_le
  have hprod : (pairSumSet T ×ˢ pairSumSet T).card = (pairSumSet T).card ^ 2 := by
    rw [Finset.card_product, sq]
  have hpss : (pairSumSet T).card ≤ T.card ^ 2 := by
    calc (pairSumSet T).card ≤ (T ×ˢ T).card := Finset.card_image_le
      _ = T.card ^ 2 := by rw [Finset.card_product, sq]
  unfold hitCount
  calc (Finset.univ.filter (fun Δ : G => matchCount T Δ ≠ 0)).card
      ≤ ((pairSumSet T ×ˢ pairSumSet T).image (fun p : G × G => p.1 - p.2)).card := hcard
    _ ≤ (pairSumSet T ×ˢ pairSumSet T).card := himg
    _ = (pairSumSet T).card ^ 2 := hprod
    _ ≤ (T.card ^ 2) ^ 2 := Nat.pow_le_pow_left hpss 2
    _ = T.card ^ 4 := by ring

/-! ## Part 4: `good` for the real matching step (open item 1 of
`ROADMAP-current.md`)

`hitRate_of_good_overlap` takes an arbitrary `good : G → Prop`; nothing
about it is specific to `good := fun Δ => ¬ ∃ x ∈ T, ∃ y ∈ T, Δ = x - y`.
`ROADMAP-current.md`'s stated model has THREE direct-relation shortcuts, not
one: a solve whose target `Δ` already splits as `Δ ∈ T - T`, `Δ ∈ T`
(read: as a single element, `Δ = t` for `t ∈ T` — the model's `a`-shift
convention makes a lone factor-base element itself a free relation), or
`Δ ∈ T + T` is accepted directly and never reaches the `(U,V)`-matching step
this file's `matchCount`/`overlap` machinery models. So the matching regime
only ever sees `Δ` outside the union of all three, and `goodMatch` below is
that union's complement — the honest `good` for THIS model, as opposed to
`good := fun Δ => ¬ ∃ x ∈ T, ∃ y ∈ T, Δ = x - y` (`T - T` alone), which was
only ever a stand-in exactly for Part 0's narrower claim (that the *trivial
cancelling quadruples* live only on `T - T`) and was never claimed to be the
model's actual exclusion set.

Widening the exclusion from `T - T` alone to all three sets can only help:
`goodMatch` is a SUBSET of `good` from Part 0/2 (`goodMatch_subset_good`
below), so the "no trivial cancelling family here" guarantee
(`not_trivial_of_not_mem_sub`) still applies unchanged, and the mass moved
from `good` into `¬goodMatch` (the `T` and `T + T` pieces) is mass that was
never part of the attack's accounting in the first place — it strengthens
`hitRate_of_good_overlap`'s premises to `hgood`/`hbad` on `goodMatch`
without weakening what those premises need to say. -/

/-- **The model's real exclusion set.** `Δ` triggers one of the three
direct-relation shortcuts: `Δ ∈ T - T`, `Δ ∈ T` (as a singleton element), or
`Δ ∈ T + T` (as a sumset element, `Δ = t₁ + t₂` for `t₁, t₂ ∈ T`). Stated,
like `trivial_quadruple_mem_sub`, as explicit existentials rather than via
`Finset`'s `-`/`+` instances, for the same reason given there. -/
def DirectRelation (T : Finset G) (Δ : G) : Prop :=
  (∃ x ∈ T, ∃ y ∈ T, Δ = x - y) ∨ (Δ ∈ T) ∨ (∃ x ∈ T, ∃ y ∈ T, Δ = x + y)

/-- **`goodMatch`: the `Δ` the matching step actually sees.** Complement of
`DirectRelation`. This is the `good` `ROADMAP-current.md` open item 1 asks
for, in place of the narrower `T - T`-only exclusion Part 0/2 used. -/
def goodMatch (T : Finset G) (Δ : G) : Prop := ¬ DirectRelation T Δ

instance (T : Finset G) : DecidablePred (goodMatch T) := fun Δ => by
  unfold goodMatch DirectRelation
  infer_instance

/-- **`goodMatch` is at least as strong an exclusion as Part 0's `T - T`-only
`good`.** Anything passing `goodMatch` (avoiding all three shortcuts) in
particular avoids `T - T`, so `not_trivial_of_not_mem_sub` applies to any
`goodMatch`-satisfying `Δ` unchanged: no cancelling quadruple realizes it. -/
theorem goodMatch_not_mem_sub {T : Finset G} {Δ : G} (h : goodMatch T Δ) :
    ¬ ∃ x ∈ T, ∃ y ∈ T, Δ = x - y := fun hex => h (Or.inl hex)

/-- **The `T - T`-only `good` set contains `goodMatch`.** Restated as a
`Finset.filter` subset, matching the shape `hitRate_of_good_overlap`'s
`hbad` sum ranges over: moving from `good := ¬ mem (T-T)` to `goodMatch`
only ever moves `Δ` from the "good" side to the "bad" side, never the
other way, so it cannot invalidate an `hgood` bound already established for
the wider `good`. -/
theorem goodMatch_subset_good (T : Finset G) :
    (Finset.univ.filter (goodMatch T)) ⊆
      (Finset.univ.filter (fun Δ : G => ¬ ∃ x ∈ T, ∃ y ∈ T, Δ = x - y)) := by
  intro Δ hΔ
  rw [Finset.mem_filter] at hΔ ⊢
  exact ⟨hΔ.1, goodMatch_not_mem_sub hΔ.2⟩

/-- **The overlap cap transfers to `goodMatch` for free.** `overlap_le_sidon_energy`
is unconditional in `Δ` (Part 3), so it holds on `goodMatch` in particular —
`hitRate_of_good_overlap`'s `hgood` premise is never the obstruction, for
EITHER choice of `good`. What remains open, exactly as flagged in the module
docstring's Part 2 "What this does NOT prove", is `hbad`: the mass carried
by `DirectRelation`, which is now honestly three pieces (`T - T`, `T`, and
`T + T`) instead of one, and is not bounded by anything on file — closing it
is still the outstanding content of open item 1, not this lemma. -/
theorem goodMatch_overlap_cap (T : Finset G) (hSidon : SidonRepBound T) :
    ∀ Δ : G, goodMatch T Δ → shiftOverlap (pairSumSet T) Δ ≤ 2 * T.card ^ 2 :=
  fun Δ _ => overlap_le_sidon_energy T hSidon Δ

/-- **`HitRate` via `goodMatch`, modulo the one open input.** Packages
`hitRate_of_good_overlap` with `good := goodMatch T` and the overlap cap
already discharged by `goodMatch_overlap_cap`, leaving exactly the mass bound
on `DirectRelation` (`hbad`) as the caller's hypothesis — the same open gap
`ROADMAP-current.md` names, now pinned to the model's actual three-part
exclusion set instead of the `T - T`-only stand-in. -/
theorem hitRate_of_goodMatch (T : Finset G) (hSidon : SidonRepBound T) (hT : 0 < T.card)
    (badMass : ℕ)
    (hbad : ∑ Δ ∈ Finset.univ.filter (fun Δ : G => ¬ goodMatch T Δ), matchCount T Δ ≤ badMass)
    (hhalf : 2 * badMass ≤ T.card ^ 4) :
    HitRate T (2 * ((4 * (2 * T.card ^ 2) : ℕ) : ℝ)) := by
  have hKpos : 0 < 2 * T.card ^ 2 := by positivity
  apply hitRate_of_good_overlap T hSidon (goodMatch T) (2 * T.card ^ 2) badMass
    hKpos (goodMatch_overlap_cap T hSidon) hbad hhalf
