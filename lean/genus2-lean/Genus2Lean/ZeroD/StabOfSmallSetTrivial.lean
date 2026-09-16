import Mathlib

/-!
# `Stab(S)` is trivial when `S` is smaller than a prime-order cyclic
# subgroup it's stabilized by

Formalizes the abstract group-theory core of the NEW `Δ = 0` argument
recorded in `ROADMAP-alpha-locus.md`'s "Newest status update" section —
see that file for the full curve/Jacobian-level context, what standing
hypothesis (`P1,P2,P3,P4 ∈ ⟨a⟩`) this is meant to compose with, and why
it succeeds where `OrbitMapConstant.lean`'s connectedness route needed
machinery (`PreconnectedSpace (Jacobian H D)`) this codebase doesn't have.

**Deliberately has zero dependency on this project's curve/Jacobian
machinery** — pure statement about an abstract `AddCommGroup`, a fixed
element `a` of prime additive order, and a finite set smaller than that
order. This is intentional: whether `P1,P2,P3,P4 ∈ ⟨a⟩` actually holds
for this project's real `Jacobian H D`/`SampleTargetFromAlpha` setup is
open (per `ROADMAP-alpha-locus.md`: "I actually don't know how we'd show
that... I think that's probably not in general true" — Claire, this
pass) — so this file proves the group theory that IS true unconditionally,
without committing to how (or whether) the membership hypothesis gets
discharged.

## What this proves, in one line

If `a` has prime additive order `ell`, `Δ` is a multiple of `a`, and `Δ`
translation-stabilizes a finite, nonempty set `S` with `S.ncard < ell`,
then `Δ = 0`.

## Proof idea

If `Δ ≠ 0` and `Δ = k • a ∈ AddSubgroup.zmultiples a`, then
`ell • Δ = k • (ell • a) = k • 0 = 0` (since `addOrderOf a = ell` gives
`ell • a = 0`), so `addOrderOf Δ ∣ ell` (`addOrderOf_dvd_of_nsmul_eq_zero`).
`ell` prime forces `addOrderOf Δ ∈ {1, ell}`; `addOrderOf Δ = 1 ↔ Δ = 0`
(`AddMonoid.addOrderOf_eq_one_iff`) is excluded, so `addOrderOf Δ = ell`.

Then the `ell` elements `s₀, s₀+Δ, s₀+2Δ, ..., s₀+(ell-1)Δ` (any fixed
`s₀ ∈ S`) are pairwise distinct — `k ↦ s₀ + k•Δ`, `Fin ell → G`, is
injective, since `s₀+j•Δ = s₀+k•Δ` gives `(j-k)•Δ=0` (working in `ℤ` to
avoid `Fin` wraparound), forcing `ell ∣ (j-k)` by `addOrderOf_dvd_iff_
zsmul_eq_zero`-style reasoning, impossible for `0 < |j-k| < ell` — and
ALL lie in `S`, by induction using `S`'s `+Δ`-stability. Transporting
cardinality along this injection (`Set.ncard_image_of_injective` +
`Set.ncard_le_ncard`) gives `ell ≤ S.ncard`, contradicting
`S.ncard < ell`.

**Status (third pass): fixes two more REPL errors from the second
pass.** (1) `Set.ncard_le_of_subset` isn't the mathlib4 name — mathlib3
had that name, mathlib4 renamed it `Set.ncard_le_ncard` (same
signature: `s ⊆ t → t.Finite → s.ncard ≤ t.ncard`). (2) Step 2's
`rw [← natCast_zsmul, ← natCast_zsmul, hjk, sub_self]` failed to find
the `?n • ?a` pattern — `rw` needs an exact syntactic match and the
double-cast shape coming off `Fin ell` (`↑↑j`) didn't line up with
what the backward rewrite was looking for. Replaced with
`simp only [natCast_zsmul]` (unification-based, robust to how the
casts nest) followed by `rw [hjk, sub_self]` on the now-normalized
goal. All lemma names in this pass reconfirmed against current
Mathlib4 docs. Still NOT run against a live goal state (per this
project's working agreement, Claude does not use the Lean toolchain)
— Claire, please REPL-test again. -/

namespace Genus2Lean
namespace StabOfSmallSet

/-! ## Step 1: a nonzero element of a prime-order cyclic subgroup has
that same prime order -/

/-- **If `a` has prime additive order `ell` and `Δ` is a nonzero multiple
of `a`, then `Δ` itself has additive order exactly `ell`.** -/
theorem addOrderOf_eq_of_mem_zmultiples_of_ne_zero
    {G : Type*} [AddCommGroup G] {a : G} {ell : ℕ} [hp : Fact (Nat.Prime ell)]
    (ha : addOrderOf a = ell) {Δ : G} (hΔmem : Δ ∈ AddSubgroup.zmultiples a)
    (hΔne : Δ ≠ 0) :
    addOrderOf Δ = ell := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hΔmem
  -- `hk : k • a = Δ` (a `ℤ`-smul, since `AddSubgroup.mem_zmultiples_iff`
  -- is stated over `ℤ` throughout — deliberately staying in `ℤ`-smul for
  -- this whole proof rather than mixing in `ℕ`-smul via `addOrderOf_
  -- nsmul_eq_zero`, to sidestep needing an `SMulCommClass ℕ ℤ G`-style
  -- instance to relate the two scalar actions; `ℤ`-only avoids the
  -- question entirely, at the cost of using the `zsmul`-flavored
  -- lemmas throughout instead of the `nsmul`-flavored ones used
  -- elsewhere in this file (Steps 2/3, which work with `ℕ`-indexed
  -- orbits and so stay `ℕ`-native there instead).
  have hella : (ell : ℤ) • a = 0 := by
    have h1 : (addOrderOf a : ℤ) • a = 0 := by
      exact_mod_cast addOrderOf_nsmul_eq_zero a
    rwa [ha] at h1
  have hellΔ : (ell : ℤ) • Δ = 0 := by
    rw [← hk, smul_smul, mul_comm, ← smul_smul, hella, smul_zero]
  have hdvd : addOrderOf Δ ∣ ell := by
    have h := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hellΔ
    -- `h : (addOrderOf Δ : ℤ) ∣ (ell : ℤ)`; both sides are nonneg nat casts,
    -- so this transports directly to `addOrderOf Δ ∣ ell` in `ℕ`.
    exact_mod_cast h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out (addOrderOf Δ) hdvd) with h1 | hell
  · exfalso
    exact hΔne (AddMonoid.addOrderOf_eq_one_iff.mp h1)
  · exact hell

/-! ## Step 2: the orbit `{s₀, s₀+Δ, ..., s₀+(ell-1)Δ}` has exactly `ell`
distinct elements, all in `S`, when `Δ` has order `ell` and `S` is
`+Δ`-stable -/

/-- **The map `k ↦ s₀ + k•Δ`, `Fin ell → G`, is injective when `Δ` has
additive order `ell`.** -/
theorem orbit_injective_of_addOrderOf_eq
    {G : Type*} [AddCommGroup G] {Δ : G} {ell : ℕ}
    (hΔ : addOrderOf Δ = ell) (s₀ : G) :
    Function.Injective (fun k : Fin ell => s₀ + (k : ℕ) • Δ) := by
  intro j k hjk
  simp only [add_right_inj] at hjk
  -- `hjk : (j : ℕ) • Δ = (k : ℕ) • Δ`
  have hsub : ((j : ℕ) - (k : ℕ) : ℤ) • Δ = 0 := by
    have heq : ((j : ℕ) : ℤ) • Δ - ((k : ℕ) : ℤ) • Δ = 0 := by
      simp only [natCast_zsmul]
      rw [hjk, sub_self]
    rwa [← sub_smul] at heq
  -- `addOrderOf_dvd_iff_zsmul_eq_zero` is the `ℤ`-smul version, so its
  -- conclusion is the `ℤ`-divisibility `(addOrderOf Δ : ℤ) ∣ (↑j - ↑k : ℤ)`,
  -- not a `ℕ`-divisibility of `natAbs` — get that first, then convert.
  have hdvdZ : (addOrderOf Δ : ℤ) ∣ ((j : ℕ) - (k : ℕ) : ℤ) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr hsub
  have hdvd : addOrderOf Δ ∣ ((j : ℕ) - (k : ℕ) : ℤ).natAbs :=
    Int.natCast_dvd.mp hdvdZ
  rw [hΔ] at hdvd
  have hbound : ((j : ℕ) - (k : ℕ) : ℤ).natAbs < ell := by
    have hj := j.isLt
    have hk := k.isLt
    omega
  have : ((j : ℕ) - (k : ℕ) : ℤ).natAbs = 0 := by
    rcases Nat.eq_zero_or_pos (((j : ℕ) - (k : ℕ) : ℤ).natAbs) with h0 | hpos
    · exact h0
    · exfalso
      have := Nat.le_of_dvd hpos hdvd
      omega
  have : (j : ℕ) = (k : ℕ) := by omega
  exact Fin.ext this

/-- **Every point of the orbit `{s₀ + k•Δ : k ∈ Fin ell}` lies in `S`,
given `s₀ ∈ S` and `S` is stabilized by `+Δ`.** Plain induction on
`k : ℕ`. -/
theorem orbit_mem_of_stable
    {G : Type*} [AddCommGroup G] {Δ : G} {S : Set G}
    (hstab : ∀ x ∈ S, x + Δ ∈ S) {s₀ : G} (hs₀ : s₀ ∈ S) :
    ∀ k : ℕ, s₀ + k • Δ ∈ S := by
  intro k
  induction k with
  | zero => simpa using hs₀
  | succ n ih =>
    have hmem : s₀ + (n : ℕ) • Δ + Δ ∈ S := hstab _ ih
    simpa [succ_nsmul, add_assoc] using hmem

/-! ## Step 3: assembling — `Stab(S)` trivial when `|S| < ell` -/

/-- **Main theorem.** If `a` has prime additive order `ell`, `Δ` is a
multiple of `a`, and `Δ` stabilizes a finite, nonempty set `S` with
`S.ncard < ell` (via `∀ x ∈ S, x + Δ ∈ S` — the direction actually needed
downstream), then `Δ = 0`. -/
theorem delta_eq_zero_of_stabilizes_small_set
    {G : Type*} [AddCommGroup G] {a : G} {ell : ℕ} [Fact (Nat.Prime ell)]
    (ha : addOrderOf a = ell)
    {S : Set G} (hSfin : S.Finite) (hScard : S.ncard < ell)
    {s₀ : G} (hs₀ : s₀ ∈ S)
    {Δ : G} (hΔmem : Δ ∈ AddSubgroup.zmultiples a)
    (hstab : ∀ x ∈ S, x + Δ ∈ S) :
    Δ = 0 := by
  by_contra hΔne
  have hordΔ : addOrderOf Δ = ell :=
    addOrderOf_eq_of_mem_zmultiples_of_ne_zero ha hΔmem hΔne
  have hinj : Function.Injective (fun k : Fin ell => s₀ + (k : ℕ) • Δ) :=
    orbit_injective_of_addOrderOf_eq hordΔ s₀
  have hmem : ∀ k : Fin ell, s₀ + (k : ℕ) • Δ ∈ S :=
    fun k => orbit_mem_of_stable hstab hs₀ (k : ℕ)
  -- The image of `univ : Set (Fin ell)` under the orbit map is an
  -- `ell`-sized subset of `S`, forcing `ell ≤ S.ncard`, contradicting
  -- `S.ncard < ell`. Done entirely with the `Set.ncard`-native lemmas
  -- (`Set.ncard_image_of_injective`, `Set.ncard_univ`,
  -- `Set.ncard_le_ncard`) rather than detouring through `Nat.card`.
  have hsubset : (fun k : Fin ell => s₀ + (k : ℕ) • Δ) '' Set.univ ⊆ S := by
    rintro x ⟨k, -, rfl⟩
    exact hmem k
  have himg_card : ((fun k : Fin ell => s₀ + (k : ℕ) • Δ) '' Set.univ).ncard = ell := by
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    simp
  have hmono : ((fun k : Fin ell => s₀ + (k : ℕ) • Δ) '' Set.univ).ncard ≤ S.ncard :=
    Set.ncard_le_ncard hsubset hSfin
  rw [himg_card] at hmono
  omega

end StabOfSmallSet
end Genus2Lean
