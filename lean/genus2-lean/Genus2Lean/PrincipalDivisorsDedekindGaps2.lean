import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorsDedekind
import Genus2Lean.PrincipalDivisorsDedekindGaps



noncomputable section


variable (k : Type*) [Field k] [DecidableEq k]

example : GCDMonoid (Polynomial k) := by
  infer_instance


set_option linter.style.header false

open Polynomial

/-!
# §3.0 gap-closing pass, part 2: target 5 — irreducible, not-dividing ⟹ coprime

**Status: drafted against a real strategy, NOT compiled by me (no Lean toolchain reachable
from this session). Same CONFIRMED / PLAUSIBLE / GUESS confidence tagging as the rest of this
project.** Targets 1–4 from `PrincipalDivisorsDedekindGaps.lean` are now confirmed to build
(per live feedback); this file is a fresh attempt at the fifth and last one, kept separate
since it's a self-contained lemma with no dependency on the other four.

## The target

`π` irreducible, `π ∤ p`, in `k[X]` (`k` a field, so `k[X]` is a PID / `EuclideanDomain`) ⟹
`IsCoprime π p`.

## Strategy

`k[X]` for `k` a field is registered as a `EuclideanDomain` in Mathlib, which comes with
Bézout coefficients via `EuclideanDomain.gcd_eq_gcd_ab` (**CONFIRMED-tier**: this is a
well-established, long-standing Mathlib lemma —
`gcd a b = a * EuclideanDomain.gcdA a b + b * EuclideanDomain.gcdB a b`). The plan:

1. Show `IsCoprime π (gcd π p)` is equivalent to `gcd π p` being a unit, once we know
   `gcd π p ∣ π` — since `π` irreducible means its only divisors (up to units) are units and
   associates of `π` itself.
2. Rule out "`gcd π p` is an associate of `π`": that would give `π ∣ gcd π p`, and
   `gcd π p ∣ p`, so `π ∣ p`, contradicting `hnd`.
3. So `gcd π p` is a unit, i.e. `IsUnit (gcd π p)`.
4. From `gcd π p = π * gcdA + p * gcdB` (Bézout) and `IsUnit (gcd π p)`, dividing through by
   the unit gives `1 = π * (gcdA / gcd) + p * (gcdB / gcd)` — a genuine Bézout identity for
   `1`, which is exactly `IsCoprime π p`'s definition (`∃ u v, u * π + v * p = 1`, up to
   argument order).

This avoids needing to know `Irreducible.coprime_iff_not_dvd` (or any single named lemma
packaging the whole fact) exists at all, at the cost of being a longer, more manual proof —
the same trade-off targets 2/3 in the sibling file ended up making, successfully, after their
first shorter attempts hit unconfirmed lemma names.
-/

namespace HyperellipticPolynomial

variable {k : Type*} [Field k] [DecidableEq k]

/-- **PLAUSIBLE, target for gap 5**: in `k[X]` (`k` a field), an irreducible `π` not dividing
`p` is coprime to `p`. Built from Bézout coefficients (`EuclideanDomain.gcd_eq_gcd_ab`) rather
than a single named "irreducible + not-dividing ⟹ coprime" lemma, whose exact name wasn't
confirmed to exist.

Named `isCoprime_of_irreducible_not_dvd'` (trailing prime) rather than reusing the identical
name from `PrincipalDivisorsDedekindGaps.lean`'s still-`sorry`'d stub of the same statement —
both files are imported together and share the `HyperellipticPolynomial` namespace, so the
unprimed name collides (confirmed by the build error). Once this proof is checked, the fix is
to delete the `sorry`'d stub in the first file and rename this one back to the unprimed name,
rather than keeping both permanently. -/
theorem isCoprime_of_irreducible_not_dvd' {π p : k[X]}
    (hπ : Irreducible π) (hnd : ¬ π ∣ p) :
    IsCoprime π p := by
  have hunit : IsUnit (gcd π p) := by
    exact (hπ.isUnit_gcd_iff (y := p)).2 hnd
  exact (gcd_isUnit_iff π p).1 hunit

end HyperellipticPolynomial
