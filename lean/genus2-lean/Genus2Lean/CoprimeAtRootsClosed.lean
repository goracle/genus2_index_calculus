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

**Status: SCAFFOLD, not yet proved.** This file exists to isolate the one genuinely
new piece of mathematics `ROADMAP-lpaircarrier-nonclosed-field.md`'s step 5 still needs,
following the ChatGPT consultation transcript on removing `[IsAlgClosed k]` from
`LPairFinrankOneOrdAtFrac.lean`. Nothing below is claimed correct yet; every `sorry`
below is either a direct target for a follow-up ChatGPT consultation or a mechanical
task once the surrounding shape is confirmed.

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

## Plan

1. **`IsFullyCoprime a b c := IsCoprime (gcd a b) c`** (§1) — the honest `k[X]`-gcd
   statement, strictly stronger than `IsCoprimeAtRoots`. `reduce_ordAtFrac_triple`
   already proves this for its output triple "for free" (its own `g := gcd (gcd a b)
   c` division already forces `gcd (gcd a₀ b₀) c₀` to be a unit — this just needs
   surfacing as an explicit corollary, `reduce_ordAtFrac_triple`'s existing proof body
   is *not* changed, only a new corollary is added referencing the same construction).
2. **The genuinely new theorem (§2, `sorry`'d below, ChatGPT-consultation target):**
   `IsFullyCoprime a b c` implies that for every closed point
   `v : HeightOneSpectrum (CoordinateRing H)`, `toPair H a b ∉ v.asIdeal ∨
   toPair H c 0 ∉ v.asIdeal` — i.e. no closed point (of any residue degree) can see
   both the numerator and denominator vanish simultaneously. This is the direct
   `HeightOneSpectrum`-indexed generalization of `IsCoprimeAtRoots`'s role in the old
   proof (there, "no shared *rational* root"; here, "no shared closed point of *any*
   degree"), and per the ChatGPT transcript this should go through the pullback
   `Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal`, a prime ideal of
   `k[X]` (hence `(0)` or `(q)` for `q` irreducible, since `k[X]` is a PID), with
   `IsFullyCoprime` ruling out the case where that pullback prime divides `gcd a b`
   and `c` simultaneously.
3. **Assembly (§3, depends on §2):** convert `ordAtFrac`'s `H.Point`-only pointwise
   bound (`hzsupp₀` in `uniqueDegree2MapToP1_ordAtFrac`) plus §2's unit-somewhere fact
   into an honest `ordAtSpec`-based, `HeightOneSpectrum`-indexed pointwise bound
   matching `IsPoleBoundedAtPairSpec`'s clause, then invoke
   `natDegree_pairNorm_le_natDegree_pairNorm_add_two_of_isPoleBoundedAtPairSpec` (or
   the fixed-numerator version, once it's clear which numerator shape the call site
   actually has after `b₀ = 0` — see that theorem's own docstring on why the
   fixed-`(1,0)`-numerator version doesn't directly apply before `b₀ = 0` is known).

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

/-- **§1. `IsFullyCoprime`: the honest `k[X]`-gcd statement.**

**The full `k[X]`-gcd coprimality**: `gcd a b` and `c` share no common
irreducible factor. Strictly stronger than `IsCoprimeAtRoots a b c`
(`LPairFinrankOneOrdAtFrac.lean`), which only rules out shared *rational* roots
(degree-1 irreducible factors with a root in `k`). `IsCoprimeAtRoots` is recovered
from this as a corollary (§1b below), not the other way around. -/
def IsFullyCoprime (a b c : k[X]) : Prop :=
  IsCoprime (gcd a b) c

/-- **`IsFullyCoprime` implies `IsCoprimeAtRoots`.** If `α` were a shared rational
root of `(a,b,c)`, then `linX α ∣ gcd a b` (`dvd_gcd`, `Polynomial.dvd_iff_isRoot`
both directions) and `linX α ∣ c` (`dvd_iff_isRoot`), so `linX α` divides both
`IsCoprime`'s witnesses, forcing `linX α` to be a unit — contradicting
`(linX α).natDegree = 1 ≠ 0`. Direct analogue of `reduce_ordAtFrac_triple`'s own
inline coprimality argument (`LPairFinrankOneOrdAtFrac.lean`, lines ~1727-1751), just
routed through `IsCoprime`'s standard API (`IsCoprime.isUnit_of_dvd'` or equivalent)
instead of the ad hoc `dvd_gcd`/`mul_dvd_mul_iff_left` chain that proof uses (which
only had access to the definition of `g`, not a packaged `IsCoprime` fact). -/
theorem isCoprimeAtRoots_of_isFullyCoprime (a b c : k[X])
    (hfc : IsFullyCoprime a b c) : IsCoprimeAtRoots a b c := by
  sorry

variable {H} [IsDedekindDomain (CoordinateRing H)]

/-- **`reduce_ordAtFrac_triple`'s output is fully coprime, not merely coprime-at-
roots.** Surfaces the stronger fact already implicit in that theorem's construction:
`g := gcd (gcd a b) c` is by definition the full joint gcd of the *original* triple
`(a,b,c)`, so `a₀ := a/g, b₀ := b/g, c₀ := c/g` satisfies `gcd (gcd a₀ b₀) c₀` is a
unit — this is a general fact about dividing out by the gcd (`EuclideanDomain`/
`GCDMonoid` API: "the gcd of `x/g, y/g` for `g = gcd x y` is a unit", then one more
step to fold `c` in), not anything specific to this project's objects.

**Implementation plan**: either (a) re-run `reduce_ordAtFrac_triple`'s existing
construction inline here with the extra conclusion appended (duplicating a `set g :=
...` and the `obtain`s), or (b) — cleaner — go back and add `IsFullyCoprime a₀ b₀ c₀`
as an extra conjunct in `reduce_ordAtFrac_triple`'s own existential in
`LPairFinrankOneOrdAtFrac.lean`, proved via a one-line addition right where that
theorem already establishes `g ∣ a₀`'s absence, i.e. right after (or replacing) its
existing `hcop : IsCoprimeAtRoots a₀ b₀ c₀ := by ...` block, since the full-gcd fact
is honestly no harder to prove there than the rational-root-restricted one currently
proved — probably easier, since it doesn't need to route through `linX α`/`natDegree`
at all. Option (b) is preferred: it keeps the "reduce" and "record what reduction
gives you" logic in one place. Not yet done either way — flagged as the concrete
mechanical follow-up once §2 below is resolved and it's clear exactly what shape of
coprimality fact §3's assembly step wants to consume. -/
theorem isFullyCoprime_of_reduce_ordAtFrac_triple (x₁ x₂ : H.Point) (a b c : k[X])
    (hcne : c ≠ 0) (hab_ne : toPair H a b ≠ 0)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)))
    (hinf : ordInfOfPair a b ≥ ordInfOfPair c (0 : k[X])) :
    ∃ a₀ b₀ c₀ : k[X], c₀ ≠ 0 ∧ toPair H a₀ b₀ ≠ 0 ∧
      polePairToFraction (H := H) a b c 0 = polePairToFraction (H := H) a₀ b₀ c₀ 0 ∧
      (∀ P : H.Point, ordAtFrac P a₀ b₀ c₀ 0 ≥
        -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) ∧
      ordInfOfPair a₀ b₀ ≥ ordInfOfPair c₀ (0 : k[X]) ∧
      IsFullyCoprime a₀ b₀ c₀ := by
  sorry

/-- **§2. The genuinely new step: `IsFullyCoprime` at the closed-point level.**

**This is the theorem to take to a fresh ChatGPT consultation if it doesn't fall out
directly.** Everything in §1 is bookkeeping around a fact that's already implicitly
proved elsewhere in the codebase; this is not.

**No closed point sees both a fully-coprime numerator and denominator vanish.**
The `HeightOneSpectrum`-indexed generalization of `IsCoprimeAtRoots`'s role in the old
`IsAlgClosed`-based proof: there, "no rational root of `c` is also a root of both `a`
and `b`" was enough because every closed point *was* rational. Here, `v` ranges over
the full spectrum (any residue degree), and the claim is the same shape: `v` cannot
contain both `toPair H a b` and `toPair H c 0`.

**Proof sketch (per the ChatGPT consultation transcript), not yet formalized:**
`P := Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal` is a prime ideal of
`k[X]` (comap of a prime along a ring hom is prime, standard Mathlib:
`Ideal.IsPrime.comap` or `Ideal.comap_isPrime`). Since `k[X]` is a PID, `P = ⊥` or
`P = Ideal.span {q}` for some irreducible `q`. If `toPair H a b ∈ v.asIdeal` and
`toPair H c 0 ∈ v.asIdeal`: unfolding `toPair`, `toPair H c 0 = algebraMap k[X]
(CoordinateRing H) c`, so `c ∈ P` directly. For the numerator, `toPair H a b =
algebraMap _ _ a + algebraMap _ _ b * y H` — getting `a ∈ P` (or `b ∈ P`, or some
combination) from `toPair H a b ∈ v.asIdeal` is NOT immediate, since `y H` isn't in
the image of `algebraMap k[X] (CoordinateRing H)` — this is the one place the
argument needs real input about how `CoordinateRing H`'s ring structure interacts
with `v.asIdeal`, not just soft ideal-theoretic pushing-around. Likely needs: `(algebraMap
_ _ a + algebraMap _ _ b * y H) ∈ v.asIdeal` and `(algebraMap _ _ a - algebraMap _ _
b * y H) ∈ v.asIdeal` (the conjugate) would together give `2 * algebraMap _ _ a ∈
v.asIdeal` and `2 * algebraMap _ _ b * y H ∈ v.asIdeal` — but we only have ONE of
these (`toPair H a b ∈ v.asIdeal`), not both; the conjugate's membership is exactly
what's NOT assumed. So this may need the norm instead: if `toPair H a b ∈ v.asIdeal`,
consider `toPair H a b * toPair H a (-b) = pairNorm H a b` (`toPair_mul_involution`,
already proved elsewhere in this project) — if `v.asIdeal` is prime and doesn't
contain `toPair H a (-b)` [needs justifying separately, or a case split], membership
of the product forces `pairNorm H a b = a² - b²·f ∈ v.asIdeal`, hence `a² - b²·f ∈
P` (a genuine `k[X]` fact, since `pairNorm H a b` literally IS `algebraMap k[X]
(CoordinateRing H) (a² - b² * H.f)` by `toPair_right_zero`-style unfolding) — combined
with `q ∣ c` (from `c ∈ P`) and `IsFullyCoprime a b c` (`gcd a b` coprime to `c`,
hence `q ∤ gcd a b`, hence `q` doesn't divide both `a` and `b`), there may be enough
to derive a contradiction, but the case split on whether `v.asIdeal` contains the
conjugate `toPair H a (-b)` is exactly the ramified/split/inert trichotomy from the
ChatGPT transcript's Layer-3 discussion resurfacing, and needs to be worked through
carefully rather than assumed away. **Flagging this as the one place a fresh
consultation is likely needed**, quoting this exact docstring paragraph as the
starting point, since the argument sketch above is not confirmed correct. -/
theorem toPair_notMem_or_notMem_of_isFullyCoprime
    (a b c : k[X]) (hfc : IsFullyCoprime a b c)
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    toPair H a b ∉ v.asIdeal ∨ toPair H c (0 : k[X]) ∉ v.asIdeal := by
  sorry

/-- **§3. Assembly: `ordAtSpec`-based pointwise bound, ready for
`GlobalDegreeBoundSpec.lean`'s degree bound.**

**`ordAtSpec`-based pointwise pole bound**, `ordAtFrac`'s `HeightOneSpectrum`
analogue, needed to feed `natDegree_pairNorm_le_natDegree_pairNorm_add_two_of_
isPoleBoundedAtPairSpec`. Combines: (a) the rational-point-only bound `hzsupp₀` this
file's callers already have (from `reduce_ordAtFrac_triple`/`isFullyCoprime_of_
reduce_ordAtFrac_triple`), specialized down from `H.Point` to `pointHeightOne' P` via
`ordAt_eq_ordAtSpec`; and (b) §2's fact that at every OTHER closed point (not of the
form `pointHeightOne' P` for `P ∈ {x₁,x₂}`), `ordAtSpec` of the fully-coprime
numerator/denominator pair can't both be positive, so the indicator-free bound
`ordAtSpec v A' B' ≤ ordAtSpec v A B` holds there unconditionally (no pole to bound at
all, since one side is always a unit). **Not yet attempted** — blocked on §2. -/
theorem ordAtSpec_sub_le_indicator_of_isFullyCoprime
    (x₁ x₂ : H.Point) (a b c : k[X]) (hcne : c ≠ 0) (hab_ne : toPair H a b ≠ 0)
    (hfc : IsFullyCoprime a b c)
    (hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥
      -((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v c (0 : k[X]) ≤ ordAtSpec v a b +
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) := by
  sorry

end HyperellipticPolynomial
