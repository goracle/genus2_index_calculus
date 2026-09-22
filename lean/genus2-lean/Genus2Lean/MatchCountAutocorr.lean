import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.SidonEnergy
set_option linter.style.header false

/-!
# Genus-2 index calculus: matchCount as autocorrelation of repCount (advisory-7 §6.2/§7.5)

This file generalizes `SidonEnergy.lean`'s `matchCount_zero_eq_energy` (the `Δ = 0`
slice) to *every* `Δ`, and draws the one pointwise consequence that follows from
Sidon-ness alone.

Advisory-7's §6.2 correction states the identity in words:

    X(Δ) = Σ_g r_{T,T}(g) · r_{T,T}(g - Δ)

i.e. `matchCount` is the autocorrelation of `repCount` with itself. The advisory
uses this only descriptively, to explain why finiteness-of-fibers (§6.2) does NOT
bound `X(Δ)` pointwise. It does not go on to extract the pointwise Sidon bound
below — that is a small further observation made here, not lifted from the text.

Everything in this file is a direct corollary of lemmas already proved
unconditionally (`matchCount_zero_eq_energy`'s proof technique, `sum_repCount_eq_card_sq`)
plus the same `SidonRepBound` hypothesis already used in `SidonEnergy.lean`. No new
external theorem, no Fourier analysis — same style of erosion as the rest of this
project.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **Unconditional identity** (advisory-7 §6.2's correction, stated in words there):
`matchCount T Δ` — the count of quadruples `(a,b,c,d) ∈ T⁴` with `a+b-c-d=Δ` — equals
the autocorrelation of `repCount T` with itself at `Δ`. This generalizes
`matchCount_zero_eq_energy` (the `Δ = 0` case, where autocorrelation-at-0 is exactly
the additive energy `Σ_g r(g)²`) to every `Δ`.

Proof: identical fiberwise double-counting to `matchCount_zero_eq_energy` — group
quadruples `(a,b,c,d)` by `g := a+b`, and note `a+b-c-d=Δ ∧ a+b=g` iff `c+d=g-Δ ∧ a+b=g`. -/
theorem matchCount_eq_autocorr (T : Finset G) (Δ : G) :
    matchCount T Δ = ∑ g : G, repCount T g * repCount T (g - Δ) := by
  unfold matchCount repCount
  have hfiber :
      ((T ×ˢ T ×ˢ T ×ˢ T).filter
        (fun p : G × G × G × G => p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = Δ)).card =
        ∑ g : G,
          ((T ×ˢ T ×ˢ T ×ˢ T).filter
            (fun p : G × G × G × G =>
              p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = Δ ∧ p.1 + p.2.1 = g)).card := by
    have h := Finset.sum_fiberwise
      (s := (T ×ˢ T ×ˢ T ×ˢ T).filter
        (fun p : G × G × G × G => p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = Δ))
      (g := fun p : G × G × G × G => p.1 + p.2.1)
      (f := fun _ : G × G × G × G => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro g _
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.card_product]
  apply Finset.card_bij
    (i := fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2)))
  · rintro ⟨a, b, c, d⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨ha, hb, hc, hd⟩, heq, hsum⟩ := hp
    simp only [Finset.mem_product, Finset.mem_filter]
    refine ⟨⟨⟨ha, hb⟩, hsum⟩, ⟨hc, hd⟩, ?_⟩
    have h1 : a + b - (c + d) = Δ := by
      have : a + b - c - d = a + b - (c + d) := by abel
      rw [← this]; exact heq
    rw [hsum] at h1
    have h2 := sub_eq_iff_eq_add.mp h1
    rw [h2]; abel
  · rintro ⟨a, b, c, d⟩ hp ⟨a', b', c', d'⟩ hp' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨ha, hb⟩, hc, hd⟩ := heq
    simp [ha, hb, hc, hd]
  · rintro ⟨⟨a, b⟩, c, d⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter] at hq
    obtain ⟨⟨⟨ha, hb⟩, hab⟩, ⟨hc, hd⟩, hcd⟩ := hq
    refine ⟨(a, b, c, d), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, hb, hc, hd⟩, ?_, hab⟩
    have hgd : c + d = g - Δ := hcd
    calc a + b - c - d = g - (c + d) := by rw [← hab]; abel
      _ = g - (g - Δ) := by rw [hgd]
      _ = Δ := by abel

/-- **Reindexing lemma**: `Σ_g repCount T (g - Δ) = Σ_g repCount T g`, since
`g ↦ g - Δ` is a bijection of `G`. Used to turn the autocorrelation identity into
a clean pointwise bound below. -/
theorem sum_repCount_shift (T : Finset G) (Δ : G) :
    ∑ g : G, repCount T (g - Δ) = ∑ g : G, repCount T g := by
  apply Finset.sum_nbij' (fun g => g - Δ) (fun g => g + Δ)
  · intros; exact Finset.mem_univ _
  · intros; exact Finset.mem_univ _
  · intros; abel
  · intros; abel
  · intros; rfl

/-- **Sidon-only pointwise cap on `matchCount`, at every `Δ`** (not just `Δ = 0`).
This is the small further step past `matchCount_zero_bound` (`SidonEnergy.lean`):
combining the autocorrelation identity above with `SidonRepBound` (`repCount ≤ 2`
pointwise) and the reindexing lemma bounds `matchCount T Δ` uniformly, for every `Δ`
simultaneously, by `2 · B²` — not merely at the diagonal `Δ = 0`.

Proof: `matchCount T Δ = Σ_g repCount(g) · repCount(g-Δ) ≤ Σ_g 2 · repCount(g-Δ)
= 2 · Σ_g repCount(g-Δ) = 2 · Σ_g repCount(g) = 2 · B²`, using `sidon_energy_bound`'s
hypothesis, `sum_repCount_shift`, and `sum_repCount_eq_card_sq`. -/
theorem matchCount_le_two_card_sq (T : Finset G) (hSidon : SidonRepBound T) (Δ : G) :
    matchCount T Δ ≤ 2 * T.card ^ 2 := by
  rw [matchCount_eq_autocorr]
  have hpt : ∀ g : G, repCount T g * repCount T (g - Δ) ≤ 2 * repCount T (g - Δ) := by
    intro g
    exact Nat.mul_le_mul_right _ (hSidon g)
  calc ∑ g : G, repCount T g * repCount T (g - Δ)
      ≤ ∑ g : G, 2 * repCount T (g - Δ) := Finset.sum_le_sum (fun g _ => hpt g)
    _ = 2 * ∑ g : G, repCount T (g - Δ) := by rw [Finset.mul_sum]
    _ = 2 * ∑ g : G, repCount T g := by rw [sum_repCount_shift]
    _ = 2 * T.card ^ 2 := by rw [sum_repCount_eq_card_sq]

/-- **Trivial, unconditional pointwise cap on `matchCount`, no Sidon needed
— `matchCount T Δ ≤ T.card³`, at every `Δ`.** Same proof shape as
`matchCount_le_two_card_sq` above, with `SidonRepBound`'s `repCount ≤ 2`
replaced by the free `repCount_le_card` (`SidonEnergy.lean`). Weaker than
the Sidon bound (`B³` vs `2B²`) but requires no geometric input at all —
holds for EVERY factor base `T`. This is the bound `IndexCalculusComplexity
.lean`'s relation-count theorem (`matchCount_distinct_hits_ge`) can use to
get a fully self-contained complexity claim, with no external theorem
(Forey–Fresán–Kowalski or otherwise) anywhere in the chain. -/
theorem matchCount_le_card_cubed (T : Finset G) (Δ : G) :
    matchCount T Δ ≤ T.card ^ 3 := by
  rw [matchCount_eq_autocorr]
  have hpt : ∀ g : G, repCount T g * repCount T (g - Δ) ≤ T.card * repCount T (g - Δ) := by
    intro g
    exact Nat.mul_le_mul_right _ (repCount_le_card T g)
  calc ∑ g : G, repCount T g * repCount T (g - Δ)
      ≤ ∑ g : G, T.card * repCount T (g - Δ) := Finset.sum_le_sum (fun g _ => hpt g)
    _ = T.card * ∑ g : G, repCount T (g - Δ) := by rw [Finset.mul_sum]
    _ = T.card * ∑ g : G, repCount T g := by rw [sum_repCount_shift]
    _ = T.card * T.card ^ 2 := by rw [sum_repCount_eq_card_sq]
    _ = T.card ^ 3 := by ring

/-! ## §3. A pointwise LOWER bound on `matchCount`, via the pairwise-difference count

Everything above only bounds `matchCount` from ABOVE. This section adds the
missing pointwise lower bound, needed to give `ZeroD/FiniteCouponCollector`'s
coupon-collector theorem a target set `H` on which its uniform floor
hypothesis (`hk : ∀ Δ ∈ H, k ≤ ...`) is actually satisfiable — see that
file's docstring correction this pass for why the earlier attempt
(`H := {Δ : matchCount T Δ ≠ 0}`, `|H| ≥ B²/2`) doesn't carry a uniform
`matchCount` floor at all: existence of *some* nonzero value says nothing
about how large it is. This section's route: `T`'s pairwise-DIFFERENCE
structure (not its Sidon-capped pair-SUM structure `repCount`) gives both
the floor and a large-enough `H`, via an unconditional injection for the
floor and Cauchy–Schwarz plus the existing Sidon energy bound for `|H|`.
Sent to a ChatGPT consult this pass, which caught a mutual-exclusivity
issue in an earlier over-general attempt at this file and supplied the
`diffRepCount`/`diffSupport` route below. -/

/-- **The pairwise-difference representation count**: `diffRepCount T Δ` is
the number of ordered pairs `(x, y) ∈ T × T` with `x - y = Δ`. Note this is
NOT `repCount` (which counts SUMS `x + y = g`) — a genuinely different
function, needed because `matchCount`'s lower bound below comes from
DIFFERENCES, not sums. -/
noncomputable def diffRepCount (T : Finset G) (Δ : G) : ℕ :=
  ((T ×ˢ T).filter (fun p : G × G => p.1 - p.2 = Δ)).card

/-- **The target set `H`**: every `Δ` realized as some difference of two
`T`-elements — i.e. `diffRepCount`'s support, the same set as `T - T`
(pointwise Finset subtraction), stated via `filter`/`ne` to stay inside
this file's existing idiom rather than pull in the pointwise-subtraction
API (`Finset.sub`) fresh. -/
noncomputable def diffSupport (T : Finset G) : Finset G :=
  univ.filter (fun Δ => diffRepCount T Δ ≠ 0)

theorem mem_diffSupport {T : Finset G} {Δ : G} :
    Δ ∈ diffSupport T ↔ diffRepCount T Δ ≠ 0 := by
  unfold diffSupport
  simp

/-- Summing `diffRepCount T Δ` over every `Δ` recovers `T.card²` exactly —
unconditional, same shape as `sum_repCount_eq_card_sq`, since `p ↦ p.1 - p.2`
partitions `T ×ˢ T` by fiber. -/
theorem sum_diffRepCount_eq_card_sq (T : Finset G) :
    ∑ Δ : G, diffRepCount T Δ = T.card ^ 2 := by
  have hcard : (T ×ˢ T).card = T.card ^ 2 := by
    simp [Finset.card_product, sq]
  have hfiber :
      (T ×ˢ T).card =
        ∑ Δ ∈ (Finset.univ : Finset G),
          ((T ×ˢ T).filter (fun p : G × G => p.1 - p.2 = Δ)).card := by
    have h := Finset.sum_fiberwise (s := T ×ˢ T) (g := fun p : G × G => p.1 - p.2)
      (f := fun _ : G × G => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    rw [← h]
  rw [← hcard, hfiber]
  rfl

omit [Fintype G] in
/-- **The key pointwise lower bound, unconditional — no Sidon hypothesis
needed.** For any `Δ` and any `t ∈ T`, if `(x, y) ∈ T × T` satisfies
`x - y = Δ`, then the quadruple `(x, t, t, y) ∈ T⁴` satisfies
`x + t - t - y = x - y = Δ`, so it is counted by `matchCount T Δ`. Varying
`t` over `T` and `(x,y)` over all `diffRepCount T Δ`-many difference-pairs
gives `T.card * diffRepCount T Δ` DISTINCT such quadruples — distinct
because a quadruple `(x, t, t, y)` recovers `x` from its 1st coordinate,
`y` from its 4th, and `t` from its 2nd, so different `(x, y, t)` triples
give different quadruples. Formalized as an explicit injection
`(x, y, t) ↦ (x, t, t, y)` from `(diffRepCount`-fiber`) ×ˢ T` into the
`matchCount`-fiber. -/
theorem matchCount_ge_card_mul_diffRepCount (T : Finset G) (Δ : G) :
    T.card * diffRepCount T Δ ≤ matchCount T Δ := by
  unfold matchCount diffRepCount
  rw [mul_comm, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn
    (f := fun p : (G × G) × G => (p.1.1, p.2, p.2, p.1.2))
  · rintro ⟨⟨x, y⟩, t⟩ hp
    simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_product,
      Set.mem_setOf_eq, Finset.mem_filter] at hp
    obtain ⟨⟨hxy, hxyeq⟩, ht⟩ := hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hxy.1, ht, ht, hxy.2⟩, ?_⟩
    have heq : x + t - t - y = x - y := by abel
    rw [heq, hxyeq]
  · rintro ⟨⟨x, y⟩, t⟩ _ ⟨⟨x', y'⟩, t'⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hx, ht, _, hy⟩ := heq
    simp [hx, hy, ht]

/-- **Consequence, stated on `diffSupport`**: `matchCount T Δ ≥ T.card` for
every `Δ ∈ diffSupport T`. Immediate from `matchCount_ge_card_mul_diffRepCount`:
`diffRepCount T Δ ≥ 1` on `diffSupport T` by definition, so
`T.card * 1 ≤ T.card * diffRepCount T Δ ≤ matchCount T Δ`. -/
theorem matchCount_ge_card_of_mem_diffSupport (T : Finset G) (Δ : G)
    (hΔ : Δ ∈ diffSupport T) : T.card ≤ matchCount T Δ := by
  have hpos : 1 ≤ diffRepCount T Δ := Nat.one_le_iff_ne_zero.mpr (mem_diffSupport.mp hΔ)
  calc T.card = T.card * 1 := by ring
    _ ≤ T.card * diffRepCount T Δ := Nat.mul_le_mul_left _ hpos
    _ ≤ matchCount T Δ := matchCount_ge_card_mul_diffRepCount T Δ

/-- **Relabeling identity**: `Σ_Δ diffRepCount(Δ)² = matchCount T 0`. Both
sides count 4-tuples from `T` up to the same relation: the LHS groups
`(x,y,x',y') ∈ T⁴` by their shared difference `Δ := x-y = x'-y'`; the RHS,
`matchCount T 0`, counts `(a,b,c,d) ∈ T⁴` with `a+b-c-d=0`. The map
`(x,y,x',y') ↦ (x,y',x',y)` lands in the RHS fiber because `x-y=x'-y'`
rearranges (`sub_eq_sub_iff_add_eq_add`) to `x+y'=x'+y`, i.e.
`x+y'-x'-y=0`. Proved in two steps: the fiber identity (grouping by `Δ`,
same `Finset.sum_fiberwise`/`card_bij` pattern as `matchCount_eq_autocorr`),
then the explicit bijection above into `matchCount T 0`'s fiber. A
different relabeling from `matchCount_eq_autocorr`'s autocorrelation
identity, so proved independently. -/
theorem sum_diffRepCount_sq_eq_matchCount_zero (T : Finset G) :
    ∑ Δ : G, (diffRepCount T Δ) ^ 2 = matchCount T 0 := by
  unfold diffRepCount matchCount
  have hfiber :
      ((T ×ˢ T ×ˢ T ×ˢ T).filter
        (fun p : G × G × G × G => p.1 - p.2.1 = p.2.2.1 - p.2.2.2)).card =
        ∑ Δ : G,
          (((T ×ˢ T).filter (fun p : G × G => p.1 - p.2 = Δ)).card) ^ 2 := by
    have h := Finset.sum_fiberwise
      (s := (T ×ˢ T ×ˢ T ×ˢ T).filter
        (fun p : G × G × G × G => p.1 - p.2.1 = p.2.2.1 - p.2.2.2))
      (g := fun p : G × G × G × G => p.1 - p.2.1)
      (f := fun _ : G × G × G × G => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro Δ _
    rw [sq, ← Finset.card_product]
    apply Finset.card_bij
      (i := fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2)))
    · rintro ⟨a, b, c, d⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      have hmem := hp.1.1
      have heq := hp.1.2
      have hΔ := hp.2
      have ha := hmem.1
      have hb := hmem.2.1
      have hc := hmem.2.2.1
      have hd := hmem.2.2.2
      simp only [Finset.mem_product, Finset.mem_filter]
      refine ⟨⟨⟨ha, hb⟩, hΔ⟩, ⟨hc, hd⟩, ?_⟩
      exact heq.symm.trans hΔ
    · rintro ⟨a, b, c, d⟩ hp ⟨a', b', c', d'⟩ hp' heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨ha, hb⟩, hc, hd⟩ := heq
      simp [ha, hb, hc, hd]
    · rintro ⟨⟨a, b⟩, c, d⟩ hq
      simp only [Finset.mem_product, Finset.mem_filter] at hq
      obtain ⟨⟨⟨ha, hb⟩, hab⟩, ⟨hc, hd⟩, hcd⟩ := hq
      refine ⟨(a, b, c, d), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨⟨ha, hb, hc, hd⟩, ?_⟩, hab⟩
      exact hab.trans hcd.symm
  rw [← hfiber]
  apply Finset.card_bij
    (i := fun p _ => (p.1, p.2.2.2, p.2.2.1, p.2.1))
  · rintro ⟨x, y, x', y'⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hx, hy, hx', hy'⟩, heq⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hx, hy', hx', hy⟩, ?_⟩
    have hsum : x + y' = x' + y := sub_eq_sub_iff_add_eq_add.mp heq
    calc x + y' - x' - y = (x' + y) - x' - y := by rw [hsum]
      _ = 0 := by abel
  · rintro ⟨x, y, x', y'⟩ _ ⟨x₂, y₂, x₂', y₂'⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hx, hy', hx', hy⟩ := heq
    simp [hx, hy', hx', hy]
  · rintro ⟨a, b, c, d⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨ha, hb, hc, hd⟩, heq⟩ := hq
    refine ⟨(a, d, c, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, hd, hc, hb⟩, ?_⟩
    have hsum : a + b = c + d := by
      apply sub_eq_zero.mp
      calc a + b - (c + d) = a + b - c - d := by abel
        _ = 0 := heq
    exact sub_eq_sub_iff_add_eq_add.2 hsum

/-- **`|diffSupport T|` is large, via Cauchy–Schwarz — needs `SidonRepBound`.**
`Σ_Δ diffRepCount(Δ) = T.card²` (unconditional) and `Σ_Δ diffRepCount(Δ)² =
matchCount T 0 ≤ 2·T.card²` (under `SidonRepBound T`, via
`matchCount_zero_bound`, `SidonEnergy.lean`). Restricting both sums to
`diffSupport T` (terms outside vanish, so the restricted and unrestricted
sums agree) and applying Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`)
gives `(T.card²)² ≤ |diffSupport T| · 2·T.card²`, i.e.
`T.card²/2 ≤ |diffSupport T|`. -/
theorem card_diffSupport_ge_of_sidon (T : Finset G) (hSidon : SidonRepBound T) :
    (T.card : ℝ) ^ 2 / 2 ≤ ((diffSupport T).card : ℝ) := by
  have hsum_support : ∑ Δ ∈ diffSupport T, diffRepCount T Δ = T.card ^ 2 := by
    calc ∑ Δ ∈ diffSupport T, diffRepCount T Δ
        = ∑ Δ : G, diffRepCount T Δ := by
          apply Finset.sum_filter_ne_zero
      _ = T.card ^ 2 := sum_diffRepCount_eq_card_sq T
  have hsq_support : ∑ Δ ∈ diffSupport T, (diffRepCount T Δ) ^ 2 = matchCount T 0 := by
    have hsupp_eq : ∀ Δ : G, ((diffRepCount T Δ) ^ 2 ≠ 0) ↔ (diffRepCount T Δ ≠ 0) := by
      intro Δ
      simp
    calc ∑ Δ ∈ diffSupport T, (diffRepCount T Δ) ^ 2
        = ∑ Δ ∈ (univ.filter (fun Δ => (diffRepCount T Δ) ^ 2 ≠ 0)),
            (diffRepCount T Δ) ^ 2 := by
          apply Finset.sum_congr _ (fun _ _ => rfl)
          unfold diffSupport
          exact Finset.filter_congr (fun Δ _ => (hsupp_eq Δ).symm)
      _ = ∑ Δ : G, (diffRepCount T Δ) ^ 2 := by
          apply Finset.sum_filter_ne_zero
      _ = matchCount T 0 := sum_diffRepCount_sq_eq_matchCount_zero T
  have hcs : (∑ Δ ∈ diffSupport T, diffRepCount T Δ : ℝ) ^ 2 ≤
      (diffSupport T).card * ∑ Δ ∈ diffSupport T, (diffRepCount T Δ : ℝ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := diffSupport T)
      (f := fun Δ : G => (diffRepCount T Δ : ℝ))
    exact_mod_cast this
  have hsum_supportR : (∑ Δ ∈ diffSupport T, (diffRepCount T Δ : ℝ)) = (T.card : ℝ) ^ 2 := by
    exact_mod_cast hsum_support
  have hsq_supportR : (∑ Δ ∈ diffSupport T, (diffRepCount T Δ : ℝ) ^ 2) = (matchCount T 0 : ℝ) := by
    exact_mod_cast hsq_support
  rw [hsum_supportR, hsq_supportR] at hcs
  have hmzbound : (matchCount T 0 : ℝ) ≤ 2 * (T.card : ℝ) ^ 2 := by
    exact_mod_cast matchCount_zero_bound T hSidon
  have hmain : ((T.card : ℝ) ^ 2) ^ 2 ≤ (diffSupport T).card * (2 * (T.card : ℝ) ^ 2) := by
    calc ((T.card : ℝ) ^ 2) ^ 2 ≤ (diffSupport T).card * (matchCount T 0 : ℝ) := hcs
      _ ≤ (diffSupport T).card * (2 * (T.card : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hmzbound (by positivity)
  rcases eq_or_ne (T.card : ℝ) 0 with hB0 | hBne
  · rw [hB0]; norm_num
  · have hBpos : (0:ℝ) < (T.card : ℝ) := by
      have : (0:ℝ) ≤ (T.card : ℝ) := by positivity
      exact lt_of_le_of_ne this (Ne.symm hBne)
    have hBsqpos : (0:ℝ) < (T.card : ℝ) ^ 2 := by positivity
    have hfactor : (T.card : ℝ) ^ 2 * (T.card : ℝ) ^ 2 ≤
        (2 * (diffSupport T).card : ℝ) * (T.card : ℝ) ^ 2 := by
      calc (T.card : ℝ) ^ 2 * (T.card : ℝ) ^ 2 = ((T.card : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (diffSupport T).card * (2 * (T.card : ℝ) ^ 2) := hmain
        _ = (2 * (diffSupport T).card : ℝ) * (T.card : ℝ) ^ 2 := by ring
    have hcancel : (T.card : ℝ) ^ 2 ≤ 2 * (diffSupport T).card :=
      le_of_mul_le_mul_right hfactor hBsqpos
    linarith
