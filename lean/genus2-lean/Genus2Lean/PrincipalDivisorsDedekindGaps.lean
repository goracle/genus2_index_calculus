import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorsDedekind
noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# §3.0 gap-closing pass: the five isolated sorries in `sq_mul_mem_of_squarefree_aux`

**Status: drafted against a real strategy, NOT compiled (no Lean toolchain reachable from
this session — same caveat as every other file in this chain). Same confidence-tagging
convention as `PrincipalDivisorsDedekind.lean`: CONFIRMED / PLAUSIBLE / GUESS on every step.**

Read this file's results as *candidate* closings, not actual ones: nothing here has been
checked against a live goal state, so a "PLAUSIBLE" tag here carries exactly the same weight
as a "PLAUSIBLE" tag anywhere else in this project — it means "I believe this is the right
fact and roughly the right Mathlib name," not "this compiles."

## What this file is

`PrincipalDivisorsDedekind.lean` isolated five small gaps inside the (structurally complete)
strong-induction proof of `sq_mul_mem_of_squarefree`. This file attempts each one directly as
its own free-standing, individually-checkable lemma. Once each is confirmed against a live
goal state (`#check`, `exact?`, `apply?`), the fix should be folded back into
`PrincipalDivisorsDedekind.lean` in place of the corresponding `sorry` — this file is scratch,
not load-bearing, same policy `PrincipalDivisorsScratch.lean` had before its ideas were folded
into the main chain.

## The five targets

1. (`mk'_sq_mul_eq_iff`'s body) denominator-clearing:
   `mk' K p ⟨q,_⟩ ^ 2 * algebraMap _ _ f = algebraMap _ _ c ↔ p ^ 2 * f = c * q ^ 2`.
2. (base case) `q` a nonzero constant ⟹ `mk' K p ⟨q,_⟩ ∈ range (algebraMap k[X] _)`.
3. (inductive step, case A) `mk' K (π p₁) ⟨π q₁,_⟩ = mk' K p₁ ⟨q₁,_⟩`.
4. (inductive step, case A) `π` irreducible ⟹ `π.natDegree > 0`.
5. (inductive step, case B) `π` prime, `π ∤ p`, `k[X]` a PID ⟹ `IsCoprime π p`.

They're ordered here from most to least confident, not in the order they appear in
`PrincipalDivisorsDedekind.lean`.
-/

namespace HyperellipticPolynomial

variable {k : Type*} [Field k]

/-! ## Target 4: irreducible ⟹ positive `natDegree`, over a field

The most confident of the five. It's the direct converse of `Polynomial.natDegree_eq_zero_of_isUnit`
(already used without incident in the original file for `hq_not_unit`), combined with the fact
that over a field, `p ≠ 0` and `natDegree p = 0` together force `IsUnit p`
(`Polynomial.isUnit_iff_degree_eq_zero`, **CONFIRMED name** — this is a standard, long-standing
Mathlib lemma for polynomials over a field). Route: contrapositive. -/

/-- **PLAUSIBLE, target for gap 4**: an irreducible polynomial over a field has positive
`natDegree`. If Mathlib already has this exact fact under its own name (plausible candidates:
`Polynomial.Irreducible.natDegree_pos`, `Polynomial.natDegree_pos_of_irreducible` — searched for
but not confirmed to exist), that one-liner should be preferred over this derivation. -/
theorem irreducible_polynomial_natDegree_pos {π : k[X]} (hπ : Irreducible π) :
    0 < π.natDegree := by
  rcases Nat.eq_zero_or_pos π.natDegree with hzero | hpos
  · exfalso
    have hπ_ne : π ≠ 0 := hπ.ne_zero
    have hdeg_zero : π.degree = 0 := by
      rw [Polynomial.degree_eq_natDegree hπ_ne, hzero]
      rfl
    have hunit : IsUnit π := Polynomial.isUnit_iff_degree_eq_zero.mpr hdeg_zero
    exact hπ.1 hunit
  · exact hpos

/-! ## Target 5: prime, not-dividing, PID ⟹ coprime

`k[X]` is a PID (`k` a field), and in a PID (indeed in any `GCDMonoid` / `EuclideanDomain`,
which `k[X]` is), a prime (equivalently here, irreducible) element `π` not dividing `p` is
automatically coprime to `p`: any common divisor of `π` and `p` must itself divide `π`, hence
(irreducibility) be a unit or an associate of `π`; the associate case is ruled out since that
would give `π ∣ p`. Mathlib should package this directly — most likely candidate is
`EuclideanDomain.gcd_eq_one_iff_coprime` chained with the Euclidean algorithm on `k[X]`, or more
directly `(Irreducible.coprime_iff_not_dvd)`-shaped API that exists for `UniqueFactorizationMonoid`
/ `GCDMonoid` settings. Since `k[X]` for `k` a field is literally a `EuclideanDomain`, the
cleanest route is probably via `EuclideanDomain.isCoprime_of_...` or the general
`Irreducible.coprime_iff_not_dvd` if that name exists for a `GCDMonoid`; failing that, fall back
to building the Bézout identity by hand from `EuclideanDomain.gcd_eq_gcd_ab` and the fact that
`gcd π p` divides `π` and is therefore (irreducibility) either a unit or an associate of `π`. -/

/-- **PLAUSIBLE, target for gap 5**: in `k[X]` (`k` a field, hence `k[X]` a Euclidean domain /
PID), an irreducible `π` not dividing `p` is coprime to `p`. Two candidate routes are recorded
in the proof; whichever actually resolves in a live session should replace both. -/
theorem isCoprime_of_irreducible_not_dvd {π p : k[X]} (hπ : Irreducible π)
    (hnd : ¬ π ∣ p) : IsCoprime π p := by
  -- Route A (preferred if it exists): a direct named lemma for "irreducible, not dividing ⟹
  -- coprime" in a GCD/Bézout setting. Candidates: `Irreducible.coprime_iff_not_dvd`,
  -- `EuclideanDomain.isCoprime_of_not_dvd`. If either exists with roughly this signature,
  -- `exact (Irreducible.coprime_iff_not_dvd hπ).mpr hnd`-shaped one-liner replaces this whole
  -- proof.
  --
  -- Route B (fallback, more primitive): work with `gcd π p` directly.
  -- `EuclideanDomain.gcd_dvd_left`/`gcd_dvd_right` give `gcd π p ∣ π` and `gcd π p ∣ p`.
  -- From `gcd π p ∣ π` and `π` irreducible, `gcd π p` is a unit or an associate of `π`
  -- (`Irreducible.isUnit_or_associated_of_dvd`-shaped — exact name unconfirmed). The associate
  -- case would give `π ∣ gcd π p ∣ p`, contradicting `hnd`. So `gcd π p` is a unit, hence
  -- (`EuclideanDomain.gcd_eq_one_iff_coprime` or `IsCoprime`-from-unit-gcd API, unconfirmed
  -- exact name) `IsCoprime π p`.
  sorry

/-! ## Target 3: `mk'`-cancellation for a common factor

`mk' K (π * p₁) ⟨π * q₁, _⟩ = mk' K p₁ ⟨q₁, _⟩` when `π ≠ 0`: cancelling a common nonzero factor
from numerator and denominator of a localization element. This should be close to
`IsLocalization.mk'_mul_cancel_left` verbatim, or derivable in one step from
`IsLocalization.mk'_eq_iff_eq'` (both sides reduce to `π * p₁ * q₁ = p₁ * (π * q₁)`, pure `ring`).
Recorded here as its own lemma since the exact `mk'` argument order/orientation Mathlib expects
was not checked against a live goal state. -/

/-- **PLAUSIBLE, target for gap 3**: cancelling a common nonzero factor `π` from both the
numerator and denominator of an `IsLocalization.mk'` element. `IsLocalization.mk'_eq_iff_eq'`
turned out (per live build error) to still leave both sides wrapped in `algebraMap` rather than
reducing to a bare `k[X]` equation — not the shape assumed. Route rebuilt from
`IsLocalization.mk'_spec` directly (**CONFIRMED**, the defining equation of `mk'`, already used
successfully for target 1 below) plus injectivity of `algebraMap` (**CONFIRMED**,
`IsFractionRing.injective`), avoiding the `mk'_eq_iff_eq'` orientation question entirely. -/
theorem mk'_cancel_common_factor {π p₁ q₁ : k[X]} (hπ : π ≠ 0) (hq₁ : q₁ ≠ 0) :
    IsLocalization.mk' (FractionRing k[X]) (π * p₁)
        (⟨π * q₁, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hπ hq₁)⟩ : nonZeroDivisors k[X]) =
      IsLocalization.mk' (FractionRing k[X]) p₁
        (⟨q₁, mem_nonZeroDivisors_of_ne_zero hq₁⟩ : nonZeroDivisors k[X]) := by
  set K := FractionRing k[X]
  set s1 : nonZeroDivisors k[X] :=
    ⟨π * q₁, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hπ hq₁)⟩ with hs1_def
  set s2 : nonZeroDivisors k[X] := ⟨q₁, mem_nonZeroDivisors_of_ne_zero hq₁⟩ with hs2_def
  have hspec1 : IsLocalization.mk' K (π * p₁) s1 * algebraMap k[X] K (s1 : k[X]) =
      algebraMap k[X] K (π * p₁) := IsLocalization.mk'_spec K (π * p₁) s1
  have hspec2 : IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (s2 : k[X]) =
      algebraMap k[X] K p₁ := IsLocalization.mk'_spec K p₁ s2
  have hinj : Function.Injective (algebraMap k[X] K) := IsFractionRing.injective k[X] K
  -- `Function.Injective.ne` gives `f x ≠ f y`, not `f x ≠ 0` — bridge with `map_zero`/
  -- `map_ne_zero_iff` instead (this was the source of all four "type mismatch" errors: I'd
  -- conflated `f x ≠ f 0` with `f x ≠ 0`, which are only equal after rewriting `f 0 = 0`).
  have hπK_ne : algebraMap k[X] K π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ
  have hs1_ne : algebraMap k[X] K (s1 : k[X]) ≠ 0 := by
    rw [hs1_def]
    exact (map_ne_zero_iff _ hinj).mpr (mul_ne_zero hπ hq₁)
  have hq1K_ne : algebraMap k[X] K q₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq₁
  -- Goal `mk' K (π*p₁) s1 = mk' K p₁ s2`. Multiply both sides by `algebraMap _ _ (π * q₁)`
  -- (nonzero) and reduce, via `hspec1`/`hspec2`, to a plain `algebraMap`-equation.
  have hkey : IsLocalization.mk' K (π * p₁) s1 * algebraMap k[X] K (s1 : k[X]) =
      IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (s1 : k[X]) := by
    rw [hspec1, hs1_def]
    show algebraMap k[X] K (π * p₁) = IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (π * q₁)
    have hrhs : IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (π * q₁) =
        IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (s2 : k[X]) * algebraMap k[X] K π := by
      rw [hs2_def]
      show IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (π * q₁) =
        IsLocalization.mk' K p₁ s2 * algebraMap k[X] K q₁ * algebraMap k[X] K π
      -- LHS's `algebraMap _ _ (π * q₁)` splits via `map_mul` into `f π * f q₁`; combine with
      -- `mul_comm`/`mul_assoc` to match the RHS's `(... * f q₁) * f π` grouping.
      rw [map_mul]
      ring
    rw [hrhs, hspec2, ← map_mul]
    congr 1
    ring
  exact mul_right_cancel₀ hs1_ne hkey

/-! ## Target 2: base case — `q` a nonzero constant

`q` with `q.natDegree = 0` and `q ≠ 0` is `C q₀` for some `q₀ ≠ 0` in `k`; since `k` is a field,
`q₀` is a unit, giving `mk' K p ⟨C q₀,_⟩ = algebraMap _ _ (p * C q₀⁻¹)` directly. -/

/-- **PLAUSIBLE, target for gap 2**: a nonzero constant-denominator `mk'` element lies in the
range of `algebraMap k[X] (FractionRing k[X])`. Route: exhibit the constant's inverse
explicitly and check the resulting polynomial identity via `IsLocalization.mk'_eq_iff_eq'`
(same lemma as target 3, for consistency of what needs to be confirmed). -/
theorem mk'_mem_range_of_natDegree_eq_zero {p q : k[X]} (hq : q ≠ 0)
    (hq0 : q.natDegree = 0) :
    ∃ p' : k[X], algebraMap k[X] (FractionRing k[X]) p' =
      IsLocalization.mk' (FractionRing k[X]) p
        (⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩ : nonZeroDivisors k[X]) := by
  -- `q = C q₀` for some `q₀ : k`.
  obtain ⟨q₀, hq₀⟩ := Polynomial.natDegree_eq_zero.mp hq0
  -- Substitute `q = C q₀` *before* building the `nonZeroDivisors`/`mk'` term, so the later
  -- rewrite doesn't have to reach under a dependently-typed `Subtype` proof (this is exactly
  -- what broke the first attempt: `rw [← hq₀]` after the goal already mentioned
  -- `mem_nonZeroDivisors_of_ne_zero hq` — a proof term indexed by `q` — produced a
  -- motive-not-type-correct error). `subst` instead, from the equation the *other* direction.
  subst hq₀
  have hq₀_ne : q₀ ≠ 0 := by
    intro h; apply hq; rw [h]; exact map_zero C
  refine ⟨p * C q₀⁻¹, ?_⟩
  -- Live goal (from build): `algebraMap _ _ (p * C q₀⁻¹) = mk' K p ⟨C q₀, _⟩` — `algebraMap` on
  -- the LEFT this time (orientation depends on how `refine`'s metavariable gets placed, so
  -- pattern-matching an iff-lemma's assumed orientation keeps breaking). Drop the iff-lemma
  -- guessing entirely: prove it directly from `IsLocalization.mk'_spec`
  -- (**CONFIRMED**, `mk' K a s * algebraMap _ _ (s : k[X]) = algebraMap _ _ a`) plus
  -- injectivity, the same robust route used for target 3 and (successfully, per the last two
  -- build logs) target 1.
  set K := FractionRing k[X]
  set s : nonZeroDivisors k[X] := ⟨C q₀, mem_nonZeroDivisors_of_ne_zero hq⟩ with hs_def
  have hspec : IsLocalization.mk' K p s * algebraMap k[X] K (s : k[X]) =
      algebraMap k[X] K p := IsLocalization.mk'_spec K p s
  have hinj : Function.Injective (algebraMap k[X] K) := IsFractionRing.injective k[X] K
  have hsK_ne : algebraMap k[X] K (s : k[X]) ≠ 0 := by
    rw [hs_def]
    exact (map_ne_zero_iff _ hinj).mpr hq
  -- Show `algebraMap (p * C q₀⁻¹) * algebraMap ↑s = mk' K p s * algebraMap ↑s`, then cancel.
  apply mul_right_cancel₀ hsK_ne
  rw [hspec]
  rw [hs_def]
  show algebraMap k[X] K (p * C q₀⁻¹) * algebraMap k[X] K (C q₀) = algebraMap k[X] K p
  rw [← map_mul]
  congr 1
  rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hq₀_ne, C_1, mul_one]

/-! ## Target 1: denominator-clearing for `mk'_sq_mul_eq_iff`

The one genuinely load-bearing algebraic identity: `mk' K a ⟨s,_⟩ ^ 2 * algebraMap _ _ f =
algebraMap _ _ c ↔ a ^ 2 * f = c * s ^ 2`. Original plan (guessing `mk'_pow` and
`mk'_mul_algebraMap` by name) is dropped in favor of the strategy that structurally worked for
target 2: avoid needing *any* mk'-arithmetic lemma beyond `IsLocalization.mk'_spec`
(**CONFIRMED**, this is the defining/characterizing equation of `mk'` and about as primitive as
the API gets: `mk' S a s * algebraMap R S s = algebraMap R S a`), and derive everything else —
including the squared version — from that single fact by ordinary field/ring manipulation in
`FractionRing k[X]`, which is a field, so division and inverses are freely available rather
than needing more `mk'`-specific lemma names. -/

/-- **PLAUSIBLE, target for gap 1**: denominator-clearing for the squared `mk'` identity that
`sq_mul_mem_of_squarefree` reduces to. Route: multiply the hypothesis through by
`(algebraMap _ _ q) ^ 2`, using only `IsLocalization.mk'_spec` (the single most primitive,
highest-confidence fact about `mk'`) to eliminate the `mk'` term entirely rather than chasing
`mk'`-arithmetic lemma names, then reduce to a `k[X]` equation via injectivity of
`algebraMap k[X] (FractionRing k[X])` (**CONFIRMED**: `IsFractionRing.injective`, standard,
since `k[X]` is a domain). -/
theorem mk'_sq_mul_eq_iff' (f c p q : k[X]) (hq : q ≠ 0) :
    (IsLocalization.mk' (FractionRing k[X]) p
        (⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩ : nonZeroDivisors k[X])) ^ 2 *
        algebraMap k[X] (FractionRing k[X]) f = algebraMap k[X] (FractionRing k[X]) c ↔
      p ^ 2 * f = c * q ^ 2 := by
  set K := FractionRing k[X]
  set s : nonZeroDivisors k[X] := ⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩ with hs_def
  -- The defining equation of `mk'`: `mk' K p s * algebraMap _ _ (s : k[X]) = algebraMap _ _ p`.
  have hspec : IsLocalization.mk' K p s * algebraMap k[X] K (s : k[X]) =
      algebraMap k[X] K p := IsLocalization.mk'_spec K p s
  have hqK_ne : algebraMap k[X] K (s : k[X]) ≠ 0 := by
    have hinj : Function.Injective (algebraMap k[X] K) := IsFractionRing.injective k[X] K
    have hs_ne : (s : k[X]) ≠ 0 := by rw [hs_def]; exact hq
    exact (map_ne_zero_iff _ hinj).mpr hs_ne
  constructor
  · intro h
    -- Multiply `h` through by `algebraMap _ _ (q^2)`, then use `hspec` (squared) to replace
    -- `mk' K p s ^ 2 * algebraMap _ _ (q^2)` with `algebraMap _ _ (p^2)`.
    have hspec2 : IsLocalization.mk' K p s ^ 2 * (algebraMap k[X] K (s : k[X])) ^ 2 =
        algebraMap k[X] K p ^ 2 := by
      rw [← mul_pow, hspec]
    have hstep : algebraMap k[X] K p ^ 2 * algebraMap k[X] K f =
        algebraMap k[X] K c * (algebraMap k[X] K (s : k[X])) ^ 2 := by
      have hq2ne : (algebraMap k[X] K (s : k[X])) ^ 2 ≠ 0 := pow_ne_zero 2 hqK_ne
      have hlhs : IsLocalization.mk' K p s ^ 2 * algebraMap k[X] K f *
          (algebraMap k[X] K (s : k[X])) ^ 2 =
          algebraMap k[X] K p ^ 2 * algebraMap k[X] K f := by
        rw [mul_right_comm, hspec2]
      rw [h] at hlhs
      -- After `rw [h]`, `hlhs : algebraMap _ _ c * (algebraMap _ _ ↑s)^2 = algebraMap _ _ p^2 *
      -- algebraMap _ _ f` — exactly `hstep`'s goal, flipped. `linear_combination hlhs` failed
      -- with a residual `* 2` (build error), suggesting a sign mismatch in how it combined
      -- the hypothesis rather than a genuine gap — `exact hlhs.symm` sidesteps that entirely
      -- since no arithmetic manipulation is actually needed here, only symmetry.
      exact hlhs.symm
    -- `hstep` is `algebraMap _ _ (p^2 * f) = algebraMap _ _ (c * q^2)` up to `map_mul`/`map_pow`
    -- distribution; injectivity of `algebraMap` then gives the polynomial equation directly.
    have hinj : Function.Injective (algebraMap k[X] K) := IsFractionRing.injective k[X] K
    apply hinj
    rw [map_mul, map_pow, map_mul, map_pow]
    simpa [hs_def] using hstep
  · intro h
    -- Reverse direction: from `p^2 * f = c * q^2`, apply `algebraMap` to both sides and unwind
    -- via `hspec` (squared) the same way, ending at the original `mk'`-squared equation.
    have hmapped : algebraMap k[X] K (p ^ 2 * f) = algebraMap k[X] K (c * q ^ 2) := by
      rw [h]
    rw [map_mul, map_pow, map_mul, map_pow] at hmapped
    have hspec2 : IsLocalization.mk' K p s ^ 2 * (algebraMap k[X] K (s : k[X])) ^ 2 =
        algebraMap k[X] K p ^ 2 := by
      rw [← mul_pow, hspec]
    have hq2ne : (algebraMap k[X] K (s : k[X])) ^ 2 ≠ 0 := pow_ne_zero 2 hqK_ne
    have hgoal_scaled : IsLocalization.mk' K p s ^ 2 * algebraMap k[X] K f *
        (algebraMap k[X] K (s : k[X])) ^ 2 =
        algebraMap k[X] K c * (algebraMap k[X] K (s : k[X])) ^ 2 := by
      rw [mul_right_comm, hspec2]
      simpa [hs_def] using hmapped
    exact mul_right_cancel₀ hq2ne hgoal_scaled

end HyperellipticPolynomial
