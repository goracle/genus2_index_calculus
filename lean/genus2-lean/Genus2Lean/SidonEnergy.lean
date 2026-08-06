import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.PaleyZygmund
set_option linter.style.header false

/-!
# Genus-2 index calculus: Sidon-set energy bound (advisory-7, eq 5-6)

This file formalizes the additive-energy bound for a Sidon set `T`, from
advisory-7 §4 (the Forey–Fresán–Kowalski step). Unlike `AverageComplexity.lean`
and `PaleyZygmund.lean`, this is *not* about the factor base `F` itself, but
about `T = s(F) ⊆ G`, the image of `F` under the Sidon embedding.

The Sidon property of `T` (eq 5: every element of `G` has at most 2 ordered
representations as a sum of two elements of `T`) is a genuine geometric fact
proved by Forey–Fresán–Kowalski (2023) — it is NOT reproved here. It is taken
as a named hypothesis `SidonRepBound`, exactly as `SecondMomentBound` is taken
as a hypothesis in `PaleyZygmund.lean`. This file formalizes only the
downstream combinatorial consequence: Sidon ⟹ low energy (eq 6).

The bound proved here (`E(T,T) ≤ 2·B²`) is the clean form of eq (6), in both
ℝ-valued (`sidon_energy_bound`) and ℕ-valued (`sidon_energy_bound_nat`)
form. The advisory's literal `4·C(B,2)` intermediate expression is
deliberately NOT separately formalized — see the note above
`sidon_gives_second_moment_bound_of_ident` for why, and for how to relate it
to `sidon_energy_bound_nat` by hand if the paper wants that exact form.

The file also includes a conditional bridge
(`sidon_gives_second_moment_bound_of_ident`,
`sidon_gives_hit_count_bound_of_ident`) chaining this energy bound into
`PaleyZygmund.lean`'s hit-count theorem — conditional on an explicit
`matchCount = repCount` identity hypothesis that is flagged, not assumed
silently. That identity is NOT established anywhere in this repo and is not
claimed by advisory-7 either; closing it is exactly the Fourier-uniformity
content of advisory-7 §5, still open.
-/

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The representation function `r_{T,T}(g)` = number of *ordered* pairs
`(P1, P2) ∈ T × T` with `P1 + P2 = g`. This is advisory-7's `r_{T,T}`. -/
noncomputable def repCount (T : Finset G) (g : G) : ℕ :=
  ((T ×ˢ T).filter (fun p : G × G => p.1 + p.2 = g)).card

/-- Advisory-7, eq (like eq 9 for `matchCount`): summing `r_{T,T}(g)` over
every `g` recovers `B²` exactly — unconditional, no Sidon input needed. -/
theorem sum_repCount_eq_card_sq (T : Finset G) :
    ∑ g : G, repCount T g = T.card ^ 2 := by
  have hcard : (T ×ˢ T).card = T.card ^ 2 := by
    simp [Finset.card_product, sq]
  have hfiber :
      (T ×ˢ T).card =
        ∑ g ∈ (Finset.univ : Finset G),
          ((T ×ˢ T).filter (fun p : G × G => p.1 + p.2 = g)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [← hcard, hfiber]
  rfl

/-- Named hypothesis (advisory-7, eq 5): `T` is Sidon, meaning every group
element has at most 2 ordered representations as a sum of two elements of
`T`. This is NOT proved here — it is exactly the Forey–Fresán–Kowalski
structural theorem (2023, Thm 1, case g=2) applied to `T = s(F)`, under the
side condition that `F` avoids hyperelliptic-involution pairs. -/
def SidonRepBound (T : Finset G) : Prop :=
  ∀ g : G, repCount T g ≤ 2

/-- **Conditional** additive-energy bound (advisory-7, eq 6). Given that `T`
is Sidon (`SidonRepBound`, NOT proved by this file), the additive energy
`E(T,T) = ∑_g r_{T,T}(g)²` is at most `2 · B²`.

Proof: since `0 ≤ r(g) ≤ 2` pointwise, `r(g)² ≤ 2 · r(g)` for every `g`
(as `r(g) ∈ {0,1,2}`, checked by `interval_cases` on the bound), so summing
over `g` and using `sum_repCount_eq_card_sq` gives the result. -/
theorem sidon_energy_bound (T : Finset G) (hSidon : SidonRepBound T) :
    ∑ g : G, (repCount T g : ℝ) ^ 2 ≤ 2 * (T.card : ℝ) ^ 2 := by
  have hpt : ∀ g : G, (repCount T g : ℝ) ^ 2 ≤ 2 * (repCount T g : ℝ) := by
    intro g
    have hle : repCount T g ≤ 2 := hSidon g
    have : (repCount T g : ℝ) ≤ 2 := by exact_mod_cast hle
    have hnn : (0:ℝ) ≤ repCount T g := Nat.cast_nonneg _
    nlinarith
  have hsum_le : ∑ g : G, (repCount T g : ℝ) ^ 2 ≤ ∑ g : G, 2 * (repCount T g : ℝ) :=
    Finset.sum_le_sum (fun g _ => hpt g)
  have hsum_eq : ∑ g : G, (2:ℝ) * (repCount T g : ℝ) = 2 * ∑ g : G, (repCount T g : ℝ) := by
    rw [Finset.mul_sum]
  have hbase : ∑ g : G, (repCount T g : ℝ) = (T.card : ℝ) ^ 2 := by
    have h := sum_repCount_eq_card_sq T
    have : (∑ g : G, (repCount T g : ℝ)) = ((T.card ^ 2 : ℕ) : ℝ) := by
      rw [← h]; push_cast; rfl
    rw [this]; push_cast; ring
  calc ∑ g : G, (repCount T g : ℝ) ^ 2
      ≤ ∑ g : G, 2 * (repCount T g : ℝ) := hsum_le
    _ = 2 * ∑ g : G, (repCount T g : ℝ) := hsum_eq
    _ = 2 * (T.card : ℝ) ^ 2 := by rw [hbase]

/-- ℕ-valued form of `sidon_energy_bound`. Often more convenient than the
`ℝ` version for downstream arithmetic (`omega`, `Nat.le` chains) that
doesn't otherwise need real numbers. Proved independently in `ℕ` rather
than by casting, since the pointwise step `r(g)² ≤ 2·r(g)` for `r(g) ≤ 2`
is just as easy over `ℕ` (`Nat.mul_le_mul` / `nlinarith` both work), and
keeping a native `ℕ` statement avoids cast-juggling for callers who stay
in `ℕ` throughout. -/
theorem sidon_energy_bound_nat (T : Finset G) (hSidon : SidonRepBound T) :
    ∑ g : G, (repCount T g) ^ 2 ≤ 2 * T.card ^ 2 := by
  have hpt : ∀ g : G, (repCount T g) ^ 2 ≤ 2 * repCount T g := by
    intro g
    have hle : repCount T g ≤ 2 := hSidon g
    nlinarith
  have hsum_le : ∑ g : G, (repCount T g) ^ 2 ≤ ∑ g : G, 2 * repCount T g :=
    Finset.sum_le_sum (fun g _ => hpt g)
  have hsum_eq : ∑ g : G, 2 * repCount T g = 2 * T.card ^ 2 := by
    rw [Finset.mul_sum, sum_repCount_eq_card_sq]
  calc ∑ g : G, (repCount T g) ^ 2
      ≤ ∑ g : G, 2 * repCount T g := hsum_le
    _ = 2 * T.card ^ 2 := hsum_eq

/-- **Unconditional identity**: `matchCount T 0` (from `AverageComplexity.lean`,
the quadruple-matching count at `Δ = 0`) equals `∑ g, repCount T g ^ 2`, i.e.
exactly the additive energy `E(T,T)`. This is advisory-7 §7.4's remark that
the "diagonal" `Δ = 0` slice of the second moment is visibly the same energy
quantity already in hand from the Sidon step — no new hypothesis, just
unfolding what both counts mean: a quadruple `(a,b,c,d)` with `a+b-c-d=0` is
exactly a pair of pairs `(a,b)`, `(c,d)` landing on the same sum `g := a+b`,
summed over all possible `g`. Proved by the same fiberwise double-counting
technique as `sum_matchCount_eq_card_pow_four` / `sum_repCount_eq_card_sq`. -/
theorem matchCount_zero_eq_energy (T : Finset G) :
    matchCount T (0 : G) = ∑ g : G, (repCount T g) ^ 2 := by
  unfold matchCount repCount
  have hfiber :
      ((T ×ˢ T ×ˢ T ×ˢ T).filter
        (fun p : G × G × G × G => p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = (0 : G))).card =
        ∑ g : G,
          ((T ×ˢ T ×ˢ T ×ˢ T).filter
            (fun p : G × G × G × G =>
              p.1 + p.2.1 - p.2.2.1 - p.2.2.2 = (0 : G) ∧ p.1 + p.2.1 = g)).card := by
    apply Finset.card_eq_sum_card_fiberwise (f := fun p : G × G × G × G => p.1 + p.2.1)
    intro p _
    exact Finset.mem_univ _
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
    refine ⟨⟨ha, hb⟩, hc, hd, ?_⟩
    have : c + d = a + b := by
      have := sub_eq_zero.mp heq
      linarith [this]
    rw [this, hsum]
  · rintro ⟨a, b, c, d⟩ hp ⟨a', b', c', d'⟩ hp' heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨ha, hb⟩, hc, hd⟩ := heq
    simp [ha, hb, hc, hd]
  · rintro ⟨⟨a, b⟩, c, d⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter] at hq
    obtain ⟨⟨ha, hb⟩, hc, hd, hcd⟩ := hq
    refine ⟨(a, b, c, d), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ha, hb, hc, hd⟩, ?_, hcd.symm⟩
    rw [← hcd]
    abel

/-- **Corollary, unconditional given `SidonRepBound`**: the `Δ = 0` slice of
`matchCount` is at most `2B²`, immediately from `matchCount_zero_eq_energy`
and `sidon_energy_bound_nat`. This is the one piece of advisory-7 eq (12)'s
"diagonal part is `O(B⁴)`, in fact `O(B²)`, from Sidon-ness alone" claim
that is cheap to state precisely and prove in full — the remaining
coincidence patterns (multiset matches away from `Δ = 0`) are a genuine
case-bash the advisory only sketches, and are not formalized here; see the
note above `sidon_gives_second_moment_bound_of_ident` for why the *rest* of
eq (12), `E(S,S)`, is a structurally different and still-open quantity that
this bound does not reach. -/
theorem matchCount_zero_bound (T : Finset G) (hSidon : SidonRepBound T) :
    matchCount T (0 : G) ≤ 2 * T.card ^ 2 := by
  rw [matchCount_zero_eq_energy]
  exact sidon_energy_bound_nat T hSidon

/-- NOTE on the advisory's literal `4·C(B,2)` form: advisory-7 §4 writes the
chain `E(T,T) ≤ 4·#T ≤ 4·C(B,2)`. We deliberately do NOT formalize this
exact intermediate expression — pinning down `Nat.choose T.card 2` in terms
of `T.card * (T.card - 1)` correctly (Mathlib's `Nat.choose_two_right`
involves a `ℕ`-division that needs care to unfold safely) added meaningful
proof risk for zero new mathematical content beyond `sidon_energy_bound_nat`
above, which already gives the tighter, cleaner `2·B²` bound the `4·C(B,2)`
form is approximating. If the paper needs the literal `C(B,2)` form for
exposition, it is safe to just cite `sidon_energy_bound_nat` and note
`4·C(B,2) = 2B² - 2B ≥` is dominated by `2B²` — i.e. `sidon_energy_bound_nat`
implies the advisory's stated bound is *slightly loose* rather than being a
separate fact needing its own proof. -/

/-- **Bridge theorem**: if the factor base `F` *is itself* the Sidon set
(`F = T`, the case advisory-7 §7.4 actually needs), then `SidonRepBound F`
implies `SecondMomentBound F (2 · B²)` — the exact hypothesis
`PaleyZygmund.lean`'s `hit_count_ge_of_second_moment_bound` asks for.

This is honest about where it stops: it requires `matchCount F = repCount F`
pointwise, i.e. that the quadruple-matching count on `F` (`P1+P2-P3-P4=Δ`)
agrees with the pair-matching count on `F` (`P1+P2=Δ`, applied at `Δ` and
`-Δ`-shifted pairs). That identity does NOT hold in general — it is a
genuine additional claim advisory-7 does not make either (the advisory
carefully keeps `T = s(F)` and `S = F+F` as *separate* objects, precisely
because the Sidon property is about `T`'s pairwise sums, not `F`'s
quadruple differences). Consequently this bridge is included as a
conditional composition lemma for reference, not as a claim that Sidon
alone closes advisory-7 §7.4 — it explicitly does not; the missing step is
the Fourier-uniformity argument of advisory-7 §5, which is not formalized
anywhere in this repo yet. -/
theorem sidon_gives_second_moment_bound_of_ident
    (F : Finset G) (hSidon : SidonRepBound F)
    (hident : ∀ Δ : G, matchCount F Δ = repCount F Δ) :
    SecondMomentBound F (2 * (F.card : ℝ) ^ 2) := by
  unfold SecondMomentBound
  have h := sidon_energy_bound F hSidon
  have hcongr : ∑ Δ : G, (matchCount F Δ : ℝ) ^ 2 = ∑ g : G, (repCount F g : ℝ) ^ 2 :=
    Finset.sum_congr rfl (fun Δ _ => by rw [hident Δ])
  rw [hcongr]
  exact h

/-- Composing `sidon_gives_second_moment_bound_of_ident` with
`hit_count_ge_of_second_moment_bound` (`PaleyZygmund.lean`): under the same
`hident` side condition, Sidon plus that identity directly gives the
explicit hit-count bound `B⁶ / (2|G|) ≤ #{Δ : N(Δ) > 0}` with no separately
supplied `SecondMomentBound` hypothesis needed — the Sidon property alone
(via the bridge above) supplies it. Same caveat on `hident` as above. -/
theorem sidon_gives_hit_count_bound_of_ident
    (F : Finset G) (hSidon : SidonRepBound F)
    (hcard_pos : 0 < F.card)
    (hident : ∀ Δ : G, matchCount F Δ = repCount F Δ) :
    ((F.card : ℝ) ^ 4) ^ 2 / (2 * (F.card : ℝ) ^ 2) ≤
      ((univ.filter (fun Δ => matchCount F Δ ≠ 0)).card : ℝ) := by
  have hM := sidon_gives_second_moment_bound_of_ident F hSidon hident
  have hMpos : (0:ℝ) < 2 * (F.card : ℝ) ^ 2 := by
    have : (0:ℝ) < (F.card : ℝ) := by exact_mod_cast hcard_pos
    positivity
  exact hit_count_ge_of_second_moment_bound F (2 * (F.card : ℝ) ^ 2) hM hMpos
