import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# §3, take 2: `IsDedekindDomain (CoordinateRing H)` via direct integral closedness

**Status: drafted against a real strategy, NOT compiled (no Lean toolchain reachable
from this session — see conversation). Read this file the way `PrincipalDivisorsScratch.lean`
already asks to be read: confidence-tag every step, don't let anything here become
load-bearing until it's actually been checked against a live goal state.**

## Why this file exists / how it differs from `PrincipalDivisorsScratch.lean`

`PrincipalDivisorsScratch.lean`'s plan was: build `FractionRing (CoordinateRing H)` as a
finite separable extension of `FractionRing (k[X])`, invoke
`integralClosure.isDedekindDomain_fractionRing` to get `IsDedekindDomain` on the abstract
`integralClosure (k[X]) (FractionRing (CoordinateRing H))`, and then separately prove
`CoordinateRing H` literally *equals* that integral closure so the result transports. That
last step was flagged there as unattempted and the likely hardest part.

This file takes a shortcut around exactly that transport step, using
`IsIntegralClosure.isDedekindDomain` (**CONFIRMED name/signature**, checked against current
Mathlib docs for `Mathlib.RingTheory.DedekindDomain.IntegralClosure`) directly:

```
theorem IsIntegralClosure.isDedekindDomain
    (A : Type*) (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] (C : Type*) [CommRing C]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]
    [FiniteDimensional K L] [IsDomain A] [Algebra.IsSeparable K L] [IsDomain C]
    [IsDedekindDomain A] : IsDedekindDomain C
```

Instantiating `C := CoordinateRing H` *directly* (rather than `C := integralClosure ...`)
means the "is `CoordinateRing H` equal to the integral closure" question is replaced by
supplying the typeclass `[IsIntegralClosure (CoordinateRing H) k[X] L]` where
`L := FractionRing (CoordinateRing H)`. That class unfolds
(**CONFIRMED**, `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure` /
`IsIntegrallyClosed`-adjacent files) to two conditions:

* `algebraMap (CoordinateRing H) L` is injective on the image of integral elements
  (automatic here: `CoordinateRing H → FractionRing (CoordinateRing H)` is the canonical
  localization map, injective since `CoordinateRing H` is a domain), and
* **the real content**: `∀ x : L, IsIntegral k[X] x ↔ ∃ y : CoordinateRing H, algebraMap _ _ y = x`.

So the entire file reduces to one genuine mathematical fact:
**every element of `FractionRing (CoordinateRing H)` integral over `k[X]` already lies in
`CoordinateRing H`.** That is proved below in `coordinateRing_isIntegrallyClosed_in_fractionField`
by the classical trace/norm argument for a squarefree quadratic extension. The one place that
argument has genuinely nontrivial (not just bookkeeping) content — "if `H.f` is squarefree and
`B ^ 2 * H.f ∈ k[X]` for `B ∈ k(X)`, then `B ∈ k[X]`" — is isolated as its own lemma
(`sq_mul_mem_of_squarefree`).

**Update (previous session): `sq_mul_mem_of_squarefree` is no longer one opaque `sorry`.** It has
a complete, fully-linked Gauss's-lemma-style proof (strong induction on denominator degree,
cancelling common irreducible factors, using `Squarefree f` to rule out the case where no further
cancellation is possible — see that lemma's docstring for the full case breakdown) split across
three declarations (`mk'_sq_mul_eq_iff`, `sq_mul_mem_of_squarefree_aux`,
`sq_mul_mem_of_squarefree` itself). The overall *structure* of that proof is load-bearing
(**CONFIRMED-tier**: ordinary `have`/`obtain`/`calc` bookkeeping, no exotic tactics).

**Update (this session): all five of that proof's small gaps are now closed.** They were split
off into two standalone scratch files, `PrincipalDivisorsDedekindGaps.lean` (targets 1–4:
denominator-clearing for `mk'`, the base-case unit/inverse identification, an `mk'`-cancellation
identity, an irreducible-factor-degree-positivity fact) and `PrincipalDivisorsDedekindGaps2.lean`
(target 5: "prime + not-dividing + PID ⟹ coprime", closed via `Irreducible.isUnit_gcd_iff` +
`gcd_isUnit_iff` rather than a named coprimality lemma). Per live build feedback all five compile
in those scratch files; this session folds each proof back in at its original `sorry` site here
(two as new standalone `private theorem`s — `irreducible_polynomial_natDegree_pos`,
`isCoprime_of_irreducible_not_dvd` — used at their call sites; the other three inlined directly
into `mk'_sq_mul_eq_iff`, the base case of `sq_mul_mem_of_squarefree_aux`, and its Case-A
`mk'`-cancellation step respectively), and both scratch files are now superseded and can be
retired. `sq_mul_mem_of_squarefree` and everything it depends on is therefore **CONFIRMED-tier,
fully proved, no `sorry`s** — modulo the recomposition itself not yet having been run through a
live Lean session (see note at the very bottom of this docstring). One new typeclass dependency
was introduced: `isCoprime_of_irreducible_not_dvd` needs `[DecidableEq k]`, discharged locally via
`classical` at its one call site rather than threading it through the file's ambient `variable`
block, so it doesn't leak into anything else's signature.

Everything downstream of `sq_mul_mem_of_squarefree` (§3.1, §3.2) is unchanged from before and
still **PLAUSIBLE-tier** scaffolding, not attempted this session — those two remaining `sorry`s
(`coordinateRing_isIntegrallyClosed_in_fractionField`, `coordinateRingIsDedekindDomain_viaIntegralClosure`)
are the next frontier, not today's.

**Recomposition caveat**: this fold-in was done by direct text surgery (matching goal shapes by
inspection against each scratch file's already-checked proof), not by re-running Lean — the
individual proofs are **CONFIRMED** in isolation (per the live feedback that closed them in the
scratch files) but their *transplant* into this file's exact local context (hypothesis names,
`subst` behavior at the Case-A cancellation site in particular — flagged inline there) is
**PLAUSIBLE** until the next `lake build` confirms it. Trust the process; if something doesn't
land, it'll be a small, precisely-located mismatch, not a sign the underlying math is wrong.
-/

namespace HyperellipticPolynomial

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-! ## §3.0 The one hard sub-lemma, isolated

Everything else in this file is scaffolding around this single fact. Its proof is fully
structured — strong induction with all cases linked together — and, as of this session, fully
closed: the five small gaps that used to stand in for specific named Mathlib facts are now
folded in (see the module docstring above for the fold-in details and the recomposition
caveat). The rest of the file's two remaining `sorry`s (§3.1, §3.2) should now be attemptable,
since `coordinateRing_isIntegrallyClosed_in_fractionField` is *definitionally* built by calling
this lemma at the point flagged ⚠ in its own docstring.
-/

/-! **The squarefree-radical lemma, overview.** If `f` is squarefree in `k[X]` and `b ∈ k(X)` is
such that `b² f` is (the image of) a polynomial, then `b` itself is already (the image of) a
polynomial. The actual theorem, `sq_mul_mem_of_squarefree`, is stated further below (after its
two helper lemmas `mk'_sq_mul_eq_iff` and `sq_mul_mem_of_squarefree_aux`) — this comment covers
the overview and proof strategy for all three together, since a `/-- -/` docstring can only
attach to the declaration immediately following it, not to a declaration several lemmas later
(confirmed the hard way against a real build: see this file's earlier note on `/-- -/` vs
`/-! -/` placement, which applies here for exactly the same reason).

This is genuinely a statement about `k(X) = FractionRing k[X]`, not raw polynomial divisibility:
the naive-looking polynomial statement "`q² ∣ p² f ⟹ q² ∣ f`" is false without first reducing
`p/q` to lowest terms (e.g. `p = q` makes `q² ∣ p² f` trivial for any `f`), which is exactly why
this lemma is phrased with `b : FractionRing k[X]` rather than with raw `p q : k[X]`.

## Proof strategy

Write `b = mk' K p ⟨q, _⟩` for some `p q : k[X]`, `q ≠ 0`, via `IsLocalization.mk'_surjective`
(**CONFIRMED**: basic `IsLocalization` surjectivity, holds for any localization, no UFD
structure needed). Clearing denominators turns the hypothesis `b² f = algebraMap _ _ c` into
the polynomial identity `p² f = c q²` (**PLAUSIBLE**: needs an `IsLocalization.mk'`-arithmetic
+ "clearing denominators" lemma — candidates `IsLocalization.mk'_eq_iff_eq'`,
`IsLocalization.eq_mk'_iff_mul_eq`; exact name/form not checked against a live goal state,
isolated below as `mk'_sq_mul_eq_iff`).

Then argue by strong induction on `q.natDegree` (isolated below as `sq_mul_mem_of_squarefree_aux`,
proved by `Nat.strong_induction_on`):

* **Base case `q.natDegree = 0`.** `q` is then a nonzero constant, hence a unit in `k[X]`
  (`k` a field — **CONFIRMED**, `Polynomial.isUnit_iff_degree_eq_zero`-style). So
  `b = mk' K p ⟨q,_⟩` is already `algebraMap _ _ (p * q⁻¹)` for the field-element inverse of
  `q`'s constant coefficient — concretely `b ∈ range (algebraMap k[X] K)`, done, and this case
  needs no squarefreeness at all.

* **Inductive step `q.natDegree > 0`.** `q` is then a non-unit (**CONFIRMED**, units of `k[X]`
  are exactly the nonzero constants when `k` is a field), so (`k[X]` a UFD, being a PID)
  `q` has an irreducible — hence prime — factor `π ∣ q` (**CONFIRMED**,
  `WfDvdMonoid.exists_irreducible_factor` / `UniqueFactorizationMonoid` machinery, standard).
  Case on whether `π ∣ p`:
  - **If `π ∣ p`:** write `p = π p₁`, `q = π q₁`; then `q₁.natDegree < q.natDegree` (dividing
    out a non-unit factor strictly decreases degree — **CONFIRMED**, degree is additive over
    products and `π` has positive degree) and `b = mk' K p₁ ⟨q₁,_⟩` is the *same* element `b`
    represented with a strictly smaller-degree denominator (**PLAUSIBLE**: cancellation lemma
    for `mk'`, e.g. `IsLocalization.mk'_mul_cancel_left`-shaped, exact name unconfirmed), and
    `p₁² f = c' q₁²` for the same `c` (dividing the original identity by `π²` — **CONFIRMED**
    once `p = πp₁`, `q = πq₁` are substituted and `π ≠ 0` is used to cancel, ordinary polynomial
    algebra). Apply the induction hypothesis.
  - **If `π ∤ p`:** derive a contradiction with `Squarefree f`. From `π ∣ q` get `π² ∣ q²`, hence
    `π² ∣ c q² = p² f`. Since `π` is prime and `π ∤ p`, `π` is coprime to `p` in the PID `k[X]`
    (**PLAUSIBLE**: "prime, not-dividing, PID ⟹ coprime" — candidates
    `EuclideanDomain.isCoprime_of_...`, `Irreducible.coprime_iff_not_dvd`, exact name
    unconfirmed), hence `π²` is coprime to `p²` (`IsCoprime.pow`, **CONFIRMED**, standard
    `IsCoprime` API). A prime power coprime to one factor of a product it divides must divide
    the other factor (**CONFIRMED**-family, `IsCoprime.dvd_of_dvd_mul_left`/`_right`), so
    `π² ∣ f`. But `π` is not a unit (irreducible), so `π² ∣ f` directly contradicts
    `Squarefree f` (**CONFIRMED**: `Squarefree` unfolds to exactly `∀ x, x * x ∣ f → IsUnit x`).
    So this case is vacuous.

Termination: `q.natDegree` strictly decreases in the only case that survives, so the induction
is well-founded. -/

/-! **Denominator-clearing, isolated.** The one localization-arithmetic fact the main proof
needs: if `mk' K p ⟨q,_⟩ ^ 2 * algebraMap _ _ f = algebraMap _ _ c`, then `p ^ 2 * f = c * q ^ 2`
as polynomials. **PLAUSIBLE, sorry'd**: mathematically immediate (squaring and clearing a single
denominator), but the exact Mathlib `IsLocalization.mk'` lemma names for "`mk' K a s ^ 2 =
mk' K (a^2) (s^2)`" and "`mk' K a s = algebraMap _ _ c ↔ a = c * s`" were not checked against a
live goal state — candidates `IsLocalization.mk'_pow`, `IsLocalization.mk'_eq_iff_eq'`,
`IsLocalization.mk'_eq_iff_eq`. This is exactly the kind of small, mechanical, individually
`exact?`-able gap the induction was structured to expose rather than bury. -/

/-- An irreducible polynomial over a field has positive `natDegree`. Contrapositive of
`Polynomial.isUnit_iff_degree_eq_zero`. (Folded in from `PrincipalDivisorsDedekindGaps.lean`,
target 4 — confirmed to build there per live feedback.) -/
private theorem irreducible_polynomial_natDegree_pos {π : k[X]} (hπ : Irreducible π) :
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

/-- Cancelling a common nonzero factor `π` from both the numerator and denominator of an
`IsLocalization.mk'` element. (Folded in from `PrincipalDivisorsDedekindGaps.lean`, target 3 —
confirmed to build there per live feedback; this is the full proof, not the earlier
`mk'_eq_iff_eq'`-based attempt that turned out to leave both sides wrapped in `algebraMap`.) -/
private theorem mk'_cancel_common_factor {π p₁ q₁ : k[X]} (hπ : π ≠ 0) (hq₁ : q₁ ≠ 0) :
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
  have hπK_ne : algebraMap k[X] K π ≠ 0 := (map_ne_zero_iff _ hinj).mpr hπ
  have hs1_ne : algebraMap k[X] K (s1 : k[X]) ≠ 0 := by
    rw [hs1_def]
    exact (map_ne_zero_iff _ hinj).mpr (mul_ne_zero hπ hq₁)
  have hq1K_ne : algebraMap k[X] K q₁ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hq₁
  have hkey : IsLocalization.mk' K (π * p₁) s1 * algebraMap k[X] K (s1 : k[X]) =
      IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (s1 : k[X]) := by
    rw [hspec1, hs1_def]
    show algebraMap k[X] K (π * p₁) = IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (π * q₁)
    have hrhs : IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (π * q₁) =
        IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (s2 : k[X]) * algebraMap k[X] K π := by
      rw [hs2_def]
      show IsLocalization.mk' K p₁ s2 * algebraMap k[X] K (π * q₁) =
        IsLocalization.mk' K p₁ s2 * algebraMap k[X] K q₁ * algebraMap k[X] K π
      rw [map_mul]
      ring
    rw [hrhs, hspec2, ← map_mul]
    congr 1
    ring
  exact mul_right_cancel₀ hs1_ne hkey

/-- In `k[X]` (`k` a field), an irreducible `π` not dividing `p` is coprime to `p`. Built from
`gcd`/`Irreducible.isUnit_gcd_iff` rather than a single named "irreducible + not-dividing ⟹
coprime" lemma. (Folded in from `PrincipalDivisorsDedekindGaps2.lean`'s
`isCoprime_of_irreducible_not_dvd'`, target 5 — this was the last of the five gaps closed; the
final proof needed `[DecidableEq k]`, which is why this lemma — and only this one of the five —
carries that extra typeclass assumption.) -/
private theorem isCoprime_of_irreducible_not_dvd [DecidableEq k]
    {π p : k[X]} (hπ : Irreducible π) (hnd : ¬ π ∣ p) : IsCoprime π p := by
  have hunit : IsUnit (gcd π p) := (hπ.isUnit_gcd_iff (y := p)).2 hnd
  exact (gcd_isUnit_iff π p).1 hunit

private theorem mk'_sq_mul_eq_iff (f c p q : k[X]) (hq : q ≠ 0) :
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
      exact hlhs.symm
    have hinj : Function.Injective (algebraMap k[X] K) := IsFractionRing.injective k[X] K
    apply hinj
    rw [map_mul, map_pow, map_mul, map_pow]
    simpa [hs_def] using hstep
  · intro h
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

/-- **The induction.** For every `q ≠ 0` and `p c : k[X]` with `p² f = c q²`, the
element `mk' K p ⟨q,_⟩` already lies in the range of `algebraMap k[X] (FractionRing k[X])`.
Proved by strong induction on `q.natDegree`; see the module-level docstring above
(`sq_mul_mem_of_squarefree`) for the full case breakdown. The two sub-steps that were the
genuinely uncertain part — the unit/inverse identification in the base case, and the
`mk'`-cancellation identity `mk' K (π p₁) ⟨π q₁,_⟩ = mk' K p₁ ⟨q₁,_⟩` in the inductive step's
surviving case — are now filled in (see module docstring's fold-in note), each via the matching
lemma from the two `...Gaps` scratch files. -/
private theorem sq_mul_mem_of_squarefree_aux (f : k[X]) (hf : Squarefree f) :
    ∀ n : ℕ, ∀ q : k[X], q.natDegree = n → ∀ (hq : q ≠ 0), ∀ p c : k[X],
      p ^ 2 * f = c * q ^ 2 →
      ∃ p' : k[X], algebraMap k[X] (FractionRing k[X]) p' =
        IsLocalization.mk' (FractionRing k[X]) p
          (⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩ : nonZeroDivisors k[X]) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hqdeg hq p c hpc
    rcases eq_or_ne q.natDegree 0 with hq0 | hq0
    · -- Base case: `q` is a nonzero constant, hence a unit in `k[X]` (`k` a field).
      -- `q = C q₀` for some `q₀ : k`, `q₀ ≠ 0`; exhibit `p' := p * C q₀⁻¹` directly.
      obtain ⟨q₀, hq₀⟩ := Polynomial.natDegree_eq_zero.mp hq0
      subst hq₀
      have hq₀_ne : q₀ ≠ 0 := by
        intro h; apply hq; rw [h]; exact map_zero C
      refine ⟨p * C q₀⁻¹, ?_⟩
      set K := FractionRing k[X]
      set s : nonZeroDivisors k[X] := ⟨C q₀, mem_nonZeroDivisors_of_ne_zero hq⟩ with hs_def
      have hspec : IsLocalization.mk' K p s * algebraMap k[X] K (s : k[X]) =
          algebraMap k[X] K p := IsLocalization.mk'_spec K p s
      have hinj : Function.Injective (algebraMap k[X] K) := IsFractionRing.injective k[X] K
      have hsK_ne : algebraMap k[X] K (s : k[X]) ≠ 0 := by
        rw [hs_def]
        exact (map_ne_zero_iff _ hinj).mpr hq
      apply mul_right_cancel₀ hsK_ne
      rw [hspec]
      rw [hs_def]
      show algebraMap k[X] K (p * C q₀⁻¹) * algebraMap k[X] K (C q₀) = algebraMap k[X] K p
      rw [← map_mul]
      congr 1
      rw [mul_assoc, ← C_mul, inv_mul_cancel₀ hq₀_ne, C_1, mul_one]
    · -- Inductive step: `q` has positive degree, hence is a non-unit, hence (`k[X]` a PID)
      -- has an irreducible factor.
      have hq_not_unit : ¬ IsUnit q := by
        intro hunit
        have := Polynomial.natDegree_eq_zero_of_isUnit hunit
        exact hq0 this
      -- **CONFIRMED-tier**: existence of an irreducible factor of a nonzero non-unit in a
      -- UFD (`k[X]` is a UFD, being a PID over a field).
      obtain ⟨π, hπ_irred, hπ_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hq_not_unit hq
      have hπ_prime : Prime π := hπ_irred.prime
      by_cases hπp : π ∣ p
      · -- Case A: cancel `π` from both `p` and `q`, recurse.
        obtain ⟨p₁, hp₁⟩ := hπp
        obtain ⟨q₁, hq₁⟩ := hπ_dvd
        have hπ_ne : π ≠ 0 := hπ_prime.ne_zero
        have hq₁_ne : q₁ ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hq₁
          exact hq hq₁
        have hq₁_deg_lt : q₁.natDegree < n := by
          have hq_eq : q.natDegree = π.natDegree + q₁.natDegree := by
            rw [hq₁, Polynomial.natDegree_mul hπ_ne hq₁_ne]
          -- `π` irreducible ⟹ `π.natDegree > 0` (over a field): closed via
          -- `irreducible_polynomial_natDegree_pos` (contrapositive of
          -- `Polynomial.isUnit_iff_degree_eq_zero`, matching `hq_not_unit`'s route above).
          have hπ_deg_pos : 0 < π.natDegree := irreducible_polynomial_natDegree_pos hπ_irred
          omega
        -- The polynomial identity descends: from `p = π p₁`, `q = π q₁`,
        -- `p² f = c q²` becomes `π² p₁² f = c π² q₁²`, and cancelling `π² ≠ 0`
        -- (`k[X]` a domain) gives `p₁² f = c q₁²`.
        have hπ2_ne : (π ^ 2 : k[X]) ≠ 0 := pow_ne_zero 2 hπ_ne
        have hp1c : p₁ ^ 2 * f = c * q₁ ^ 2 := by
          have hexp : π ^ 2 * (p₁ ^ 2 * f) = π ^ 2 * (c * q₁ ^ 2) := by
            have hpq : (π * p₁) ^ 2 * f = c * (π * q₁) ^ 2 := by
              rw [← hp₁, ← hq₁]; exact hpc
            calc π ^ 2 * (p₁ ^ 2 * f) = (π * p₁) ^ 2 * f := by ring
              _ = c * (π * q₁) ^ 2 := hpq
              _ = π ^ 2 * (c * q₁ ^ 2) := by ring
          exact mul_left_cancel₀ hπ2_ne hexp
        obtain ⟨p', hp'⟩ := ih q₁.natDegree hq₁_deg_lt q₁ rfl hq₁_ne p₁ c hp1c
        refine ⟨p', ?_⟩
        rw [hp']
        -- `mk' K p₁ ⟨q₁,_⟩ = mk' K p ⟨q,_⟩` given `p = π p₁`, `q = π q₁`: substitute and apply
        -- `mk'_cancel_common_factor` (folded in from `PrincipalDivisorsDedekindGaps.lean`,
        -- target 3 — confirmed to build there per live feedback). **One spot flagged for a
        -- live check**: `subst hp₁ hq₁` here eliminates `p`/`q` throughout the whole tactic
        -- block (including `hpc`, `hπp`, earlier `have`s) rather than just the goal — should
        -- be harmless since nothing above this line depends on `p`/`q` staying un-substituted,
        -- but if Lean complains about subst direction/ordering, `rw [hp₁, hq₁]` on just the
        -- goal (`mk' K p₁ ⟨q₁,_⟩ = mk' K p ⟨q,_⟩` → `mk' K p₁ ⟨q₁,_⟩ = mk' K (π*p₁) ⟨π*q₁,_⟩`)
        -- followed by `exact (mk'_cancel_common_factor hπ_ne hq₁_ne).symm` is the fallback.
        subst hp₁ hq₁
        exact (mk'_cancel_common_factor hπ_ne hq₁_ne).symm
      · -- Case B: `π ∤ p`. Derive `π² ∣ f`, contradicting `Squarefree f`.
        exfalso
        have hπ2_dvd_q2 : π ^ 2 ∣ q ^ 2 := pow_dvd_pow_of_dvd hπ_dvd 2
        have hπ2_dvd_rhs : π ^ 2 ∣ c * q ^ 2 := hπ2_dvd_q2.mul_left c
        have hπ2_dvd_lhs : π ^ 2 ∣ p ^ 2 * f := hpc ▸ hπ2_dvd_rhs
        -- "prime `π`, `π ∤ p`, PID ⟹ `IsCoprime π p`" — closed via
        -- `isCoprime_of_irreducible_not_dvd` (folded in from
        -- `PrincipalDivisorsDedekindGaps2.lean`'s `isCoprime_of_irreducible_not_dvd'`,
        -- target 5 — the last of the five gaps, confirmed to build there per live feedback).
        -- Note this lemma needs `[DecidableEq k]`, which is why that instance is threaded
        -- through this whole file's `variable {k : Type*} [Field k]` block below via a local
        -- instance at the point of use (see that lemma's own signature above).
        have hcoprime : IsCoprime π p := by
          classical
          exact isCoprime_of_irreducible_not_dvd hπ_irred hπp
        have hcoprime2 : IsCoprime (π ^ 2) (p ^ 2) := hcoprime.pow
        have hπ2_dvd_f : π ^ 2 ∣ f := hcoprime2.dvd_of_dvd_mul_left hπ2_dvd_lhs
        obtain ⟨d, hd⟩ := hπ2_dvd_f
        have hππ : π * π ∣ f := ⟨d, by rw [hd]; ring⟩
        have hunit : IsUnit π := hf π hππ
        obtain ⟨hπ_not_unit, -⟩ := hπ_irred
        exact hπ_not_unit hunit

/-- **The squarefree-radical lemma**, assembled from `mk'_sq_mul_eq_iff` and
`sq_mul_mem_of_squarefree_aux`. See the doc-comment on `sq_mul_mem_of_squarefree_aux`
and the module-level discussion above for the full proof strategy and confidence tags;
this final assembly step is itself **CONFIRMED-tier** (pure composition of the two
lemmas above via `IsLocalization.mk'_surjective`). -/
theorem sq_mul_mem_of_squarefree (f : k[X]) (hf : Squarefree f) (b : FractionRing k[X])
    (hb : ∃ c : k[X], b ^ 2 * algebraMap k[X] (FractionRing k[X]) f
      = algebraMap k[X] (FractionRing k[X]) c) :
    ∃ p : k[X], algebraMap k[X] (FractionRing k[X]) p = b := by
  obtain ⟨c, hc⟩ := hb
  obtain ⟨⟨p, q, hq⟩, hb_eq'⟩ := IsLocalization.mk'_surjective (nonZeroDivisors k[X]) b
  -- The raw destructuring leaves `hb_eq'` as an unreduced `Prod`/`Subtype`-match
  -- beta-redex rather than the clean `mk' K p ⟨q, hq⟩ = b` — force reduction with
  -- `simp only` (no lemmas needed, just definitional unfolding) so downstream `rw`s
  -- can match against it directly.
  have hb_eq : IsLocalization.mk' (FractionRing k[X]) p (⟨q, hq⟩ : nonZeroDivisors k[X]) = b := by
    simpa using hb_eq'
  -- `hq : q ∈ nonZeroDivisors k[X]`. In the domain `k[X]`,
  -- `nonZeroDivisors k[X] = {x | x ≠ 0}` (**CONFIRMED**: `mem_nonZeroDivisors_iff_ne_zero`,
  -- standard fact for any domain/`NoZeroDivisors` ring).
  have hq_ne : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
  -- `⟨q, hq⟩` and `⟨q, mem_nonZeroDivisors_of_ne_zero hq_ne⟩` are the same subtype
  -- element (`Subtype.ext rfl`, since the propositional proof component doesn't affect
  -- the underlying value) — record this once and reuse it, rather than re-deriving it
  -- at each use site.
  have hsubtype_eq : (⟨q, mem_nonZeroDivisors_of_ne_zero hq_ne⟩ : nonZeroDivisors k[X])
      = (⟨q, hq⟩ : nonZeroDivisors k[X]) := Subtype.ext rfl
  have hpc : p ^ 2 * f = c * q ^ 2 := by
    rw [← mk'_sq_mul_eq_iff f c p q hq_ne, hsubtype_eq, hb_eq]
    exact hc
  obtain ⟨p', hp'⟩ := sq_mul_mem_of_squarefree_aux f hf q.natDegree q rfl hq_ne p c hpc
  refine ⟨p', ?_⟩
  rw [hp', hsubtype_eq]
  exact hb_eq

/-! ## §3.1 `CoordinateRing H` is integrally closed in its own fraction field

This is the statement `IsIntegralClosure (CoordinateRing H) k[X] (FractionRing (CoordinateRing H))`
ultimately needs. It is proved via `IsIntegrallyClosed`-style reasoning directly on elements of
`FractionRing (CoordinateRing H)` written as `a + b·y` (mirroring `toPair`, but over
`FractionRing k[X]` instead of `k[X]` — an element of the fraction field of a degree-2
`AdjoinRoot` extension has this shape essentially by the same "coefficient extraction" argument
`toPair_eq_zero_iff` already used at the polynomial level, just one localization up). Rather
than build that fraction-field-level `toPair` analogue from scratch here (a genuinely separate
piece of AdjoinRoot/localization plumbing — see `finiteDimensional_fractionRing`'s caveat in
`PrincipalDivisorsScratch.lean`), this file states the target against an abstract `variable`
block of hypotheses (below) capturing exactly the decomposition properties the norm/trace
argument needs, so that argument can be checked independently of the `AdjoinRoot`/
`IsFractionRing` plumbing that would derive those hypotheses from `CoordinateRing H` itself.
That plumbing is left as this section's own remaining gap, distinct from (and probably easier
than, being pure API-hunting rather than new math) the `sq_mul_mem_of_squarefree` gap above.

Deliberately *not* packaged as a full `L ≃ FractionRing k[X] × FractionRing k[X]` ring/algebra
equivalence: what the norm/trace argument below actually consumes is only (a) the additive
decomposition of `x : L` as `a + b • yL`, and (b) that `IsIntegral k[X] x` for such `x` is
equivalent to the *scalar* pair `(2 * a, a^2 - b^2 * f)` (trace, norm) both being integral over
`k[X]` — i.e. both landing in the range of `algebraMap k[X] (FractionRing k[X])`, since `k[X]`
is already integrally closed. Stating exactly that (rather than a full ring isomorphism, which
would need `yL`'s multiplication table spelled out again at the localized level) keeps the
hypotheses below each individually checkable against `AdjoinRoot`/`IsFractionRing` lemmas one at
a time, rather than bundling everything into one opaque `Equiv` whose construction would itself
be a large separate proof obligation. -/

/-! **Not a `structure` at all — a `variable` block of hypotheses.** Two successive attempts at
bundling `L`'s typeclasses (`Field L`, `Algebra _ L`, `IsFractionRing _ L`, ...) as fields of one
`structure FractionFieldPairData` both hit a `(deterministic) timeout at whnf` during real
compilation (first with `[inst : ...]`-bracketed fields, then with plain fields registered via a
trailing `attribute [instance]` block — see conversation for both build logs). Bracketed or not,
the timeout persisted, which means the earlier diagnosis ("instance search firing mid-
elaboration before anything is registered") was wrong: the actual cost is Lean having to
unify/whnf-normalize `L`'s type across seven mutually-dependent typeclass fields *inside a single
structure declaration*, which is a known expensive pattern in Lean 4 independent of the
bracket/attribute distinction. The fix, used here: don't bundle at all. State `L` and its
instances as an ordinary `variable {L : Type*} [Field L] [...]` block, exactly the way Mathlib
itself always states results like `IsIntegralClosure.isDedekindDomain` (see that theorem's own
signature in the module docstring above — `A K L C` are all bare variables with bracket-instance
hypotheses, never fields of a bundling structure). This is strictly closer to idiomatic Mathlib
than the structure approach was, at the cost of every downstream theorem needing to repeat the
same `variable` block (acceptable — Lean's `variable`/`include` mechanism is designed for exactly
this, unlike hand-rolled structures).

The individual hypotheses below are the fraction-field analogues of `toPair`/`toPair_injective`/
`y_sq_eq` (`HyperellipticFunctionField.lean`, `PrincipalDivisors.lean`): `yL` stands in for the
image of `y H` in `L`, `pairL_exists`/`pairL_injective` say every element of `L` is uniquely
`a + b • yL` for `a b : FractionRing k[X]`, and `yL_sq` transports `y_sq_eq` up to `L`. Should
ultimately be *derived* from `CoordinateRing H` itself (any `x : L` is a ratio `α / s` with
`α : CoordinateRing H`, `s : k[X] \ {0}`; writing `α = toPair H A B` gives `x = (A/s) + (B/s) •
yL` directly) rather than assumed — kept as hypotheses here only so the trace/norm argument
below can be checked in isolation from that `AdjoinRoot`/`IsFractionRing` plumbing.
**PLAUSIBLE-tier**: mathematically immediate, Mathlib-API-tier for the derivation not confirmed.

NB: this is a `/-! -/` module-doc-style comment, not a `/-- -/` declaration docstring — a `/--
-/` immediately before `variable` is a syntax error (`variable` is not a declaration a docstring
can attach to; confirmed the hard way against a real build — see conversation). -/
variable {L : Type*} [Field L] [Algebra (CoordinateRing H) L]
  [IsFractionRing (CoordinateRing H) L] [Algebra k[X] L] [IsScalarTower k[X] (CoordinateRing H) L]
  [Algebra (FractionRing k[X]) L] [IsScalarTower k[X] (FractionRing k[X]) L]
  (yL : L) (pairL_exists : ∀ x : L,
    ∃ a b : FractionRing k[X], x = (algebraMap (FractionRing k[X]) L) a +
      (algebraMap (FractionRing k[X]) L) b * yL)
  (pairL_injective : ∀ a₁ b₁ a₂ b₂ : FractionRing k[X],
    (algebraMap (FractionRing k[X]) L) a₁ + (algebraMap (FractionRing k[X]) L) b₁ * yL =
      (algebraMap (FractionRing k[X]) L) a₂ + (algebraMap (FractionRing k[X]) L) b₂ * yL →
      a₁ = a₂ ∧ b₁ = b₂)
  (yL_sq : yL ^ 2 = (algebraMap k[X] L) H.f)

/-- **Target of §3.1, NOT proved**, but reduced here to a concrete, checkable proof skeleton.
Given the hypotheses above and `NonsingularData`, every element of `L` integral over `k[X]`
comes from `CoordinateRing H`.

Proof skeleton (the `sorry` below stands for the two steps marked ⚠, everything else is the
kind of bookkeeping `toPair_injective`/`toPair_eq_zero_iff` already model in this project):

1. Given `x : L` with `IsIntegral k[X] x`, obtain `a b : FractionRing k[X]` with
   `x = a + b • yL` via `pairL_exists`.
2. ⚠ Show `2 * a` and `a ^ 2 - b ^ 2 * H.f` are each integral over `k[X]`. Route: the conjugate
   `x' := a - b • yL` satisfies the same minimal-polynomial shape as `x` (swap `b ↦ -b`; uses
   `yL_sq` the same way `toPair_mul_involution`/`toPair_add_involution` use `y_sq_eq`), so
   `x` and `x'` are both integral over `k[X]`, hence so are their sum `2a` and product
   `a² - b²f` (integral elements of a field extension are closed under `+`/`*` — standard
   Mathlib fact, `IsIntegral.add`/`IsIntegral.mul`, **CONFIRMED** these exist in
   `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`).
3. Since `k[X]` is a PID, `IsIntegrallyClosed k[X]` holds (**CONFIRMED**-tier: PID ⟹ UFD ⟹
   integrally closed is a standard Mathlib instance chain, `UniqueFactorizationMonoid` →
   `IsIntegrallyClosed`), so integral-over-`k[X]` elements of `FractionRing k[X]` are literally
   in the range of `algebraMap k[X] (FractionRing k[X])` (`IsIntegrallyClosed.isIntegral_iff`,
   **CONFIRMED** name above). Apply this to get `2a = algebraMap _ _ p` and
   `a² - b²f = algebraMap _ _ q` for some `p q : k[X]`.
4. From `2 * a = algebraMap _ _ p` and `nd.char_ne_two`, `2` is a unit in `FractionRing k[X]`
   (image of a nonzero element of a field under `algebraMap k[X] (FractionRing k[X])`), so
   `a = algebraMap _ _ p / 2 = algebraMap _ _ (p /ₚ 2)`-shaped — concretely, `a` is already
   `algebraMap k[X] (FractionRing k[X])` of *some* polynomial once `char k ≠ 2` is used to
   divide `p` by the (invertible, in `k`, hence in `k[X]`) scalar `2`; this needs `2⁻¹ : k` to
   exist, i.e. genuinely uses `nd.char_ne_two`, not just `(2 : k[X]) ≠ 0`.
5. ⚠ From step 4's `a ∈ range (algebraMap k[X] _)` and step 3's `a² - b²f ∈ range (algebraMap
   k[X] _)`, get `b² f ∈ range (algebraMap k[X] _)` (subtract), then apply
   `sq_mul_mem_of_squarefree nd.squarefree_f b ⟨...⟩` to get `b ∈ range (algebraMap k[X] _)`
   too.
6. Assemble: `a = algebraMap _ _ A`, `b = algebraMap _ _ B` for `A B : k[X]`; then
   `x = a + b • yL = algebraMap (CoordinateRing H) L (toPair H A B)` by unfolding `toPair`
   and `yL`'s relation to `y H` (needs one more compatibility hypothesis not yet in this
   `variable` block — that `yL` really is the image of `y H`, not just *some* element
   satisfying `yL_sq` — flagged here as a gap a live session should patch before attempting
   this proof). -/
theorem coordinateRing_isIntegrallyClosed_in_fractionField
    (nd : NonsingularData H) :
    ∀ x : L, IsIntegral k[X] x →
      ∃ y : CoordinateRing H, algebraMap (CoordinateRing H) L y = x := by
  sorry

/-! ## §3.2 Assembly: `IsDedekindDomain (CoordinateRing H)`

This is mechanical given §3.1 — instantiate `IsIntegralClosure.isDedekindDomain` with
`A := k[X]`, `K := FractionRing k[X]`, `L := L`, `C := CoordinateRing H`. The typeclass
obligations (`[Algebra.IsSeparable K L]`, `[FiniteDimensional K L]`, `[IsScalarTower ...]`) are
all standard consequences of `L` being the fraction field of a degree-2 extension by a
separable polynomial (`nd.irreducible_defining_poly` + `nd.char_ne_two`, following
`PrincipalDivisorsScratch.lean`'s `defining_poly_separable` sketch — also unproved there, also
needed here, NOT re-derived in this file: this section inherits that gap as a hypothesis rather
than duplicating the `sorry`). -/

/-- **Final assembly, NOT proved** (depends on §3.1's `sorry`, plus the separability /
finite-dimensionality facts flagged in `PrincipalDivisorsScratch.lean` as their own unproved
steps — `defining_poly_separable`, `finiteDimensional_fractionRing`). Recorded here so the
*shape* of the final theorem is fixed, mirroring how `PrincipalDivisors.lean §4`
(`deg_div_eq_zero_deg5`) fixes its target shape before its proof exists. Once §3.1 and the two
scratch-file gaps are closed, this should assemble via
`IsIntegralClosure.isDedekindDomain k[X] (FractionRing k[X]) L (CoordinateRing H)` after
discharging its typeclass arguments — the `sorry` below stands in for exactly that
typeclass-assembly step, not for new mathematical content beyond §3.1. -/
theorem coordinateRingIsDedekindDomain_viaIntegralClosure
    (nd : NonsingularData H) :
    IsDedekindDomain (CoordinateRing H) := by
  sorry

end HyperellipticPolynomial
