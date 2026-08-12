import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.PrincipalDivisors
import Genus2Lean.GlobalDegreeBoundSpec
import Genus2Lean.LPairFinrankOneOrdAtFrac
set_option linter.style.header false

noncomputable section

open Classical
open Polynomial

variable {k : Type*} [Field k] (H : HyperellipticPolynomial k)

/-!
# Bridging `k[X]`-gcd coprimality to closed-point pole-boundedness

**Status: SCAFFOLD, not yet proved; §2's originally-planned statement was FALSE and
has been replaced.** This file exists to isolate the one genuinely new piece of
mathematics `ROADMAP-lpaircarrier-nonclosed-field.md`'s step 5 still needs, following
the ChatGPT consultation transcript on removing `[IsAlgClosed k]` from
`LPairFinrankOneOrdAtFrac.lean`.

**Post-mortem on the original plan (kept for the record — do not repeat this
mistake):** the original §2 target, `IsFullyCoprime a b c := IsCoprime (gcd a b) c`
implies `toPair H a b ∉ v.asIdeal ∨ toPair H c 0 ∉ v.asIdeal` for every closed point
`v`, is **false**. Counterexample (a second, independent ChatGPT consultation): at a
Weierstrass point `v = (X - α, y)` (`α` a simple root of `H.f`), take `a = c = X - α`,
`b = 1`. Then `gcd a b = 1` so `IsFullyCoprime a b c` holds vacuously, yet
`toPair H a b = (X - α) + y ∈ v.asIdeal` (both summands are) and
`toPair H c 0 = X - α ∈ v.asIdeal`. A second counterexample away from ramification
(`b = 1, c = X - α, a = -β` at a non-Weierstrass point `(α, β)`) shows the same
statement is false even split/inert, not just ramified. The root cause: `a + bY`
vanishing at a closed point is a statement about the *norm* `a² - b²·H.f`, not about
`gcd a b`. The fix — weaken the hypothesis, per this file's house rule of weakening a
false theorem before deleting it — is `IsNormCoprime a b c := IsCoprime (pairNorm H a
b) c`, i.e. `IsCoprime (a ^ 2 - b ^ 2 * H.f) c`. This is what §2 now proves, with a
complete, case-split-free proof (no ramified/split/inert trichotomy needed — that
trichotomy was a symptom of chasing the wrong, too-weak hypothesis, not a genuine
difficulty in the corrected statement).

## Why this file, not a direct edit to `LPairFinrankOneOrdAtFrac.lean`

`GlobalDegreeBoundSpec.lean`'s `natDegree_le_two_of_isPoleBoundedAtPairSpec` (and its
general-numerator cousin `natDegree_pairNorm_le_natDegree_pairNorm_add_two_of_
isPoleBoundedAtPairSpec`) is **already** the correct general closed-point degree bound
— no case-split on whether `f(α)` is a square, no manufactured witness point, works
uniformly across every residue degree. Confirmed against the ChatGPT transcript: this
is exactly their "Goal B" route (`§4` of their answer), and it's fully proved already,
no `sorry`.

What's missing is the *connective* fact: `LPairFinrankOneOrdAtFrac.lean`'s
`reduce_ordAtFrac_triple` (§6 of that file) already produces a triple `(a₀,b₀,c₀)`
that is coprime **in the full `k[X]`-gcd sense** — `g := gcd (gcd a b) c` is the
honest joint gcd of the *original* triple, so after dividing it out, `gcd (gcd a₀ b₀)
c₀` is a unit — but that file's `IsCoprimeAtRoots` definition only ever *records* the
weaker, rational-root-only consequence of this (`∀ α : k, c.eval α = 0 → ¬(a.eval α =
0 ∧ b.eval α = 0)`), because that's all `natDegree_le_two_of_isCoprimeAtRoots`'s
`IsAlgClosed`-based proof needed. The stronger fact was always available for free; it
was never surfaced or named. This file surfaces it, and uses it to build the
`HeightOneSpectrum`-indexed pointwise-unit fact `IsPoleBoundedAtPairSpec`'s clause
needs, closing the gap between `reduce_ordAtFrac_triple`'s output and
`GlobalDegreeBoundSpec.lean`'s input.

## Plan (corrected)

1. **`IsNormCoprime a b c := IsCoprime (pairNorm H a b) c`** (§1) — the correct
   `k[X]`-gcd statement: `a² - b²·H.f` and `c` share no common irreducible factor.
   `reduce_ordAtFrac_triple`'s output triple should satisfy this (needs re-checking
   against that theorem's actual `g`-division construction — flagged in §1's
   corollary below; this is a weaker ask than the old plan's, since a common factor of
   `a² - b²f` and `c` need not be a common factor of `a` and `b` and `c` individually,
   so this may already fall out, or may need a short separate argument).
   `IsFullyCoprime a b c := IsCoprime (gcd a b) c` (the original, too-weak notion) is
   kept only as a named historical artifact (§0) — it is **not** used by anything
   below, and no new code should assume it implies closed-point disjointness.
   `IsCoprimeAtRoots` is recovered as a corollary (§1b, now proved — direct
   `Polynomial.eval` argument, simpler than originally sketched).
2. **The genuinely new theorem (§2, now proved below):** `IsNormCoprime a b c`
   implies that for every closed point `v : HeightOneSpectrum (CoordinateRing H)`,
   `toPair H a b ∉ v.asIdeal ∨ toPair H c 0 ∉ v.asIdeal`. Proof: if both membership
   hold, `toPair_mul_involution` gives `algebraMap _ _ (pairNorm H a b) =
   toPair H a b * involution H (toPair H a b) ∈ v.asIdeal` (ideal absorbs the
   product since one factor already is), so `pairNorm H a b ∈ P` where
   `P := Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal` (prime, by
   `Ideal.comap_isPrime`); also `c ∈ P` directly, unfolding `toPair H c 0`. Then
   `P ⊇ span {pairNorm H a b, c}`, and `IsNormCoprime a b c` says that span is `⊤`,
   contradicting `P` proper. **No case split on ramified/split/inert** — the norm
   route sidesteps the trichotomy entirely, since it only ever needs the *product*
   `toPair H a b * involution H (toPair H a b)`, never the individual conjugate's
   membership.
3. **Assembly (§3, depends on §2):** convert `ordAtFrac`'s `H.Point`-only pointwise
   bound (`hzsupp₀` in `uniqueDegree2MapToP1_ordAtFrac`) plus §2's unit-somewhere fact
   into an honest `ordAtSpec`-based, `HeightOneSpectrum`-indexed pointwise bound
   matching `IsPoleBoundedAtPairSpec`'s clause, then invoke
   `natDegree_pairNorm_le_natDegree_pairNorm_add_two_of_isPoleBoundedAtPairSpec` (or
   the fixed-numerator version, once it's clear which numerator shape the call site
   actually has after `b₀ = 0` — see that theorem's own docstring on why the
   fixed-`(1,0)`-numerator version doesn't directly apply before `b₀ = 0` is known).
   §3 below is updated to consume `IsNormCoprime` instead of `IsFullyCoprime`; not yet
   attempted, still blocked only on wiring, not on new math.

**What this file does NOT attempt to resolve**: the `x₁ = x₂` / degree-1-vs-degree-2
distinction from the ChatGPT transcript's "Layer 3" (bounding `residueDeg v ≤ 2` for
`v` over a *linear* factor specifically) is not needed here — `GlobalDegreeBoundSpec.
lean`'s bound never required it, since it sums with `residueDeg`-weighting over the
*entire* spectrum rather than needing a small-residue-degree witness point. That part
of the ChatGPT transcript describes an alternative, more surgical route this file
deliberately does not take, since the already-proved global bound makes it
unnecessary. -/

namespace HyperellipticPolynomial

open Divisor

/-- **§0. `IsFullyCoprime`: HISTORICAL, the original (too weak) plan. Kept only as a
named artifact for the record — do NOT use this to conclude closed-point
disjointness, see the file docstring's counterexamples. Nothing below depends on
this. -/
def IsFullyCoprime (a b c : k[X]) : Prop :=
  IsCoprime (gcd a b) c

/-- **§1. `IsNormCoprime`: the correct `k[X]`-gcd statement.**

**Norm coprimality**: `pairNorm H a b = a² - b²·H.f` and `c` share no common
irreducible factor. This is the hypothesis that actually controls whether a closed
point can see both `a + bY` and `c` vanish (§2 below), unlike `IsFullyCoprime`
(`IsCoprime (gcd a b) c`), which is too weak (see file docstring). `IsCoprimeAtRoots
a b c` (`LPairFinrankOneOrdAtFrac.lean`) is recovered as a corollary (§1b below). -/
def IsNormCoprime (H : HyperellipticPolynomial k) (a b c : k[X]) : Prop :=
  IsCoprime (pairNorm H a b) c

/-- **`IsNormCoprime` implies `IsCoprimeAtRoots`.** If `α` were a shared rational
root of `(a,b,c)` — i.e. `c.eval α = 0` and `a.eval α = 0 ∧ b.eval α = 0` — then
evaluating `pairNorm H a b = a ^ 2 - b ^ 2 * H.f` at `α` gives `0² - 0² * H.f.eval α =
0`, so `α` is also a root of `pairNorm H a b`. Evaluating `IsNormCoprime`'s own Bézout
identity `u * pairNorm H a b + w * c = 1` at `α` then gives `u.eval α * 0 + w.eval α *
0 = 1`, i.e. `0 = 1` in `k` — immediate contradiction, since evaluation at a fixed
point is a ring homomorphism `k[X] → k` and therefore turns the Bézout witness
identity directly into a false equation. **Proved directly via `Polynomial.eval`'s
ring-hom structure** — no `linX`/`dvd`/unit machinery needed, simpler than the
originally-sketched route through `IsCoprime.isUnit_of_dvd'`. -/
theorem isCoprimeAtRoots_of_isNormCoprime (a b c : k[X])
    (hnc : IsNormCoprime H a b c) : IsCoprimeAtRoots a b c := by
  intro α hcα
  rintro ⟨haα, hbα⟩
  obtain ⟨u, w, huw⟩ := hnc
  have hnormα : (pairNorm H a b).eval α = 0 := by
    unfold pairNorm
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, haα, hbα]
    ring
  have heval := congrArg (Polynomial.eval α) huw
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    hnormα, hcα, mul_zero, add_zero] at heval
  exact zero_ne_one heval

variable {H} [IsDedekindDomain (CoordinateRing H)]

/-- **`reduce_ordAtFrac_triple`'s output is norm-coprime.** Unlike the old
`IsFullyCoprime` target, this is genuinely NOT automatic from `g := gcd (gcd a b) c`
being the joint gcd of the original triple — `gcd (gcd a₀ b₀) c₀` being a unit does
**not** imply `gcd (pairNorm H a₀ b₀) c₀` is a unit (that gap is exactly what the
file docstring's counterexamples exploit: at the counterexample triple, `gcd a b` and
`c` are already coprime). So this corollary needs a real (short) argument, not just
surfacing: a common irreducible factor `q` of `pairNorm H a₀ b₀ = a₀² - b₀²·H.f` and
`c₀` need not divide `a₀` or `b₀` individually, but it must divide `a₀² - b₀²·H.f`;
whether `reduce_ordAtFrac_triple`'s construction rules this out depends on facts about
`g` this docstring doesn't yet establish — flagged as needing its own check (possibly
another ChatGPT consultation) once §2 is confirmed and it's clear whether `§3`
actually needs this corollary in exactly this form, or whether `IsNormCoprime` can be
established for the assembly step's specific triple by a more direct route (e.g. from
`hzsupp`/`hinf` themselves, rather than by strengthening this reduction lemma). -/
theorem isNormCoprime_of_reduce_ordAtFrac_triple (x₁ x₂ : H.Point) (a b c : k[X])
    (hcne : c ≠ 0) (hab_ne : toPair H a b ≠ 0)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (hinf : ordInfOfPair a b ≥ ordInfOfPair c (0 : k[X])) :
    ∃ a₀ b₀ c₀ : k[X], c₀ ≠ 0 ∧ toPair H a₀ b₀ ≠ 0 ∧
      polePairToFraction (H := H) a b c 0 = polePairToFraction (H := H) a₀ b₀ c₀ 0 ∧
      (∀ P : H.Point, ordAtFrac P a₀ b₀ c₀ 0 ≥
        -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) ∧
      ordInfOfPair a₀ b₀ ≥ ordInfOfPair c₀ (0 : k[X]) ∧
      IsNormCoprime H a₀ b₀ c₀ := by
  sorry

/-- **§2. The genuinely new step: `IsNormCoprime` at the closed-point level.**

**No closed point sees both a norm-coprime numerator and denominator vanish.** The
`HeightOneSpectrum`-indexed generalization of `IsCoprimeAtRoots`'s role in the old
`IsAlgClosed`-based proof: there, "no rational root of `c` is also a root of both `a`
and `b`" was enough because every closed point *was* rational. Here, `v` ranges over
the full spectrum (any residue degree), and the claim is the same shape: `v` cannot
contain both `toPair H a b` and `toPair H c 0`.

**Corrected proof (second ChatGPT consultation, on the counterexample from the file
docstring), formalized below — no case split on ramified/split/inert; the earlier
plan's trichotomy was an artifact of the wrong hypothesis, not a genuine obstruction.**
`P := Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal` is prime
(`Ideal.comap_isPrime`, comap of `v.asIdeal`'s primality along the algebra map).
Suppose for contradiction both `toPair H a b ∈ v.asIdeal` and `toPair H c 0 ∈
v.asIdeal`. Unfolding `toPair`, `toPair H c 0 = algebraMap k[X] (CoordinateRing H) c`
(the `y H` term drops since its coefficient is `0`), so `c ∈ P` directly. For the
numerator: `toPair_mul_involution` gives
`toPair H a b * involution H (toPair H a b) = algebraMap _ _ (pairNorm H a b)`.
Since `toPair H a b ∈ v.asIdeal` and ideals absorb multiplication by anything, the
whole product lies in `v.asIdeal` regardless of whether the conjugate factor does —
**this is exactly the step the old, gcd-based attempt was missing**: it never needs
to know whether `v.asIdeal` contains the conjugate `toPair H a (-b)`, because
membership of one factor is already enough to place the *product* in the ideal. So
`algebraMap _ _ (pairNorm H a b) ∈ v.asIdeal`, hence `pairNorm H a b ∈ P` too. Now
`P` is a prime (in particular proper, `≠ ⊤`) ideal containing both `pairNorm H a b`
and `c`. Unfolding `IsNormCoprime H a b c := IsCoprime (pairNorm H a b) c` by its own
definition (`∃ u w, u * pairNorm H a b + w * c = 1`) puts `1 ∈ P` (each summand is in
`P` since `P` is an ideal), contradicting `P.IsPrime.ne_top`. This route (raw Bézout
witnesses + `Ideal.eq_top_iff_one`) avoids needing to name the exact `span`-based
`IsCoprime` characterization lemma at all. -/
theorem toPair_notMem_or_notMem_of_isNormCoprime
    (a b c : k[X]) (hnc : IsNormCoprime H a b c)
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    toPair H a b ∉ v.asIdeal ∨ toPair H c (0 : k[X]) ∉ v.asIdeal := by
  by_contra h
  push_neg at h
  obtain ⟨hab, hc⟩ := h
  set P : Ideal k[X] := Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal
    with hP_def
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hcP : c ∈ P := by
    have : algebraMap k[X] (CoordinateRing H) c ∈ v.asIdeal := by
      simpa [toPair] using hc
    simpa [hP_def, Ideal.mem_comap] using this
  have hnormP : pairNorm H a b ∈ P := by
    have hmem : toPair H a b * involution H (toPair H a b) ∈ v.asIdeal :=
      v.asIdeal.mul_mem_right _ hab
    have heq := toPair_mul_involution H a b
    rw [heq] at hmem
    simpa [hP_def, Ideal.mem_comap] using hmem
  -- `IsNormCoprime H a b c` unfolds to `IsCoprime (pairNorm H a b) c`, i.e.
  -- `∃ u v, u * pairNorm H a b + v * c = 1`. Both `pairNorm H a b` and `c` lie in
  -- `P`, so `1 ∈ P`, contradicting `P` proper.
  obtain ⟨u, w, huw⟩ := hnc
  have h1 : (1 : k[X]) ∈ P := by
    rw [← huw]
    exact P.add_mem (P.mul_mem_left u hnormP) (P.mul_mem_left w hcP)
  exact hPprime.ne_top (P.eq_top_iff_one.mpr h1)

/-- **§3. Assembly: `ordAtSpec`-based pointwise bound, ready for
`GlobalDegreeBoundSpec.lean`'s degree bound.**

**`ordAtSpec`-based pointwise pole bound**, `ordAtFrac`'s `HeightOneSpectrum`
analogue, needed to feed `natDegree_pairNorm_le_natDegree_pairNorm_add_two_of_
isPoleBoundedAtPairSpec`. Combines: (a) the rational-point-only bound `hzsupp₀` this
file's callers already have (from `reduce_ordAtFrac_triple`/`isNormCoprime_of_
reduce_ordAtFrac_triple`), specialized down from `H.Point` to `pointHeightOne' P` via
`ordAt_eq_ordAtSpec`; and (b) §2's fact that at every OTHER closed point (not of the
form `pointHeightOne' P` for `P ∈ {x₁,x₂}`), `ordAtSpec` of the norm-coprime
numerator/denominator pair can't both be positive, so the indicator-free bound
`ordAtSpec v A' B' ≤ ordAtSpec v A B` holds there unconditionally (no pole to bound at
all, since one side is always a unit). **Not yet attempted, but no longer blocked on
new math — §2 is proved; this is wiring.** -/
theorem ordAtSpec_sub_le_indicator_of_isNormCoprime
    (x₁ x₂ : H.Point) (a b c : k[X]) (hcne : c ≠ 0) (hab_ne : toPair H a b ≠ 0)
    (hnc : IsNormCoprime H a b c)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v c (0 : k[X]) ≤ ordAtSpec v a b +
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) := by
  sorry

end HyperellipticPolynomial
