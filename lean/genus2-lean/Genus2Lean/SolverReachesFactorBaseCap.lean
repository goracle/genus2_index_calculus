import Mathlib
import Genus2Lean.PointMatchCountFactorBaseCap
import Genus2Lean.IndexCalculusReachability
set_option linter.style.header false

/-!
# A concrete `SolverReaches (sidonSet D δ₀ F₀) (4·B²) (fun _ => 1)`, for the
# canonical `D` (`ROADMAP-current.md` open item 1, closing sub-gap (1b)'s
# `d`-side)

## Why this file exists

`ROADMAP-current.md`'s open item 1 splits into (1a) — connecting
`matchCount`/`SolverReaches`'s abstract `G := Jacobian H D` model to a real
`H.Point` factor base — and (1b) — actually wiring a concrete `d`/`q` INTO
`SolverReaches` itself. (1a) is closed by `ZeroD/MatchCountFactorBaseBridge.lean`'s

    matchCount_sidonSet_le_pointMatchCount :
      matchCount (sidonSet D δ₀ F₀) Δ ≤ pointMatchCount D δ₀ F₀ Δ

and the `d`-side of (1b) is closed by `PointMatchCountFactorBaseCap.lean`'s

    pointMatchCount_le_four_mul_card_sq :
      pointMatchCount D δ₀ F₀ Δ ≤ 4 * F₀.card ^ 2

for `D := principalDivisorData H hdeg`. Neither file chains these two
inequalities into an actual `SolverReaches` instance — `MatchCountFactorBaseBridge`
says explicitly it does not discharge `SolverReaches` itself, and
`PointMatchCountFactorBaseCap` only bounds `pointMatchCount`, never mentioning
`SolverReaches`/`matchCount`/`goodMatch` at all. **This file supplies exactly
that missing chain**, as a genuinely concrete instantiation:

    F := sidonSet (principalDivisorData H hdeg) δ₀ F₀
    d := 4 * F₀.card ^ 2
    q := fun _ => 1

`q ≡ 1` is the trivial (loosest possible) witness: since `matchCount F Δ ≤ d`
holds UNCONDITIONALLY in `Δ` (both bridging inequalities above are
`Δ`-uniform), `matchCount F Δ ≤ d = d · 1` for every `Δ`, so `SolverReaches`'s
defining inequality holds even restricted to `goodMatch F Δ` — no case split
on `goodMatch` is needed at all, since the bound is not `goodMatch`-specific.

## What this does NOT do

* It does not produce a NONTRIVIAL `q` — `q ≡ 1` says nothing about the
  solver's actual per-attempt success probability, only that `d` is a valid
  uniform cap on the raw witness count. The real content asked for by
  `IndexCalculusReachabilityCouponCollector.lean`'s `avgQ`/`solverReaches_*`
  theorems is a `q` reflecting the SOLVER's real behavior — that is a
  genuinely different (and still open) question, not addressed here. What
  this file supplies is only the piece those theorems need in the shape of
  a `SolverReaches` hypothesis to type-check against real `H.Point` data:
  concretely, feeding `q ≡ 1` into `avgQ_mem_Icc`/
  `solverReaches_coupon_collector_bound` gives `avgQ = 1` at this `d`, an
  informative but not tight instantiation (a solver that always succeeds
  whenever ANY witness exists — an idealized upper bound on solver quality,
  not a model of the real 12-equation solver).
* It does not compute `(sidonSet D δ₀ F₀).card` or otherwise relate `d`
  back to `B := F₀.card` in a form matching `ROADMAP-current.md`'s stated
  target `d ~ p^n`/model balance point — `d := 4 * F₀.card ^ 2` here is
  exactly `4 * B^2`, already the right SHAPE (`ROADMAP-current.md`'s model
  wants `d` polynomial in `B`), but no comparison to the model's own
  `B ~ p^(2/5)` balance point is made.
* It does not touch the still-genuinely-open half of item 1: a value for
  `q` that reflects the real solver's success probability (as opposed to
  this file's trivial `q ≡ 1` ceiling). See the module docstring of
  `IndexCalculusReachabilityCouponCollector.lean` for what remains there.

## Verification status

Drafted without a Lean toolchain, per the working agreement — NOT `lake
build`-checked. The proof is a two-line chain of already-`lake build`-green
inequalities (`matchCount_sidonSet_le_pointMatchCount`,
`pointMatchCount_le_four_mul_card_sq`) plus `mul_one`; no new nontrivial
Mathlib lemma is used.
-/

open HyperellipticPolynomial
open Divisor
open Genus2Lean.MatchCountFactorBaseBridge
open Genus2Lean.PointMatchCountFactorBaseCap

namespace Genus2Lean
namespace SolverReachesFactorBaseCap

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]
variable [DecidableEq H.Point] [Fintype H.Point]

/-- **The concrete `SolverReaches` instance.** For the canonical
`D := principalDivisorData H hdeg`, ANY real factor base `F₀ : Finset H.Point`
satisfying `AvoidsInvolutionPairs`/`NoWeierstrassPoints` (the standing
hypotheses `F₀` already carries elsewhere in the project — NOT used directly
in this proof, since `pointMatchCount_le_four_mul_card_sq` needs them, but
threaded through as hypotheses here for that reason), `sidonSet D δ₀ F₀`
reaches `SolverReaches` at `d := 4 * F₀.card ^ 2`, `q ≡ 1`.

Proof: chain the two bridging inequalities
(`matchCount_sidonSet_le_pointMatchCount`,
`pointMatchCount_le_four_mul_card_sq`), then `mul_one` to match `d · q Δ`'s
shape at `q Δ = 1`. The `goodMatch F Δ` hypothesis in `SolverReaches`'s
definition is accepted but unused (`_`), since the chained bound holds for
EVERY `Δ`, not just `goodMatch`-restricted ones. -/
theorem solverReaches_sidonSet_of_avoidsInvolutionPairs
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    {F₀ : Finset H.Point} (hAvoid : AvoidsInvolutionPairs F₀)
    (hNoWeier : NoWeierstrassPoints F₀)
    [Fintype (Jacobian H (principalDivisorData H hdeg))]
    [DecidableEq (Jacobian H (principalDivisorData H hdeg))]
    (δ₀ : H.Point) :
    SolverReaches (sidonSet (principalDivisorData H hdeg) δ₀ F₀)
      (4 * F₀.card ^ 2) (fun _ => 1) := by
  intro Δ _
  have hchain : (matchCount (sidonSet (principalDivisorData H hdeg) δ₀ F₀) Δ : ℝ)
      ≤ ((4 * F₀.card ^ 2 : ℕ) : ℝ) := by
    have h1 : matchCount (sidonSet (principalDivisorData H hdeg) δ₀ F₀) Δ
        ≤ pointMatchCount (principalDivisorData H hdeg) δ₀ F₀ Δ :=
      matchCount_sidonSet_le_pointMatchCount (principalDivisorData H hdeg) δ₀ F₀ Δ
    have h2 : pointMatchCount (principalDivisorData H hdeg) δ₀ F₀ Δ ≤ 4 * F₀.card ^ 2 :=
      pointMatchCount_le_four_mul_card_sq hdeg hchar hsf hAvoid hNoWeier δ₀ Δ
    exact_mod_cast h1.trans h2
  simpa using hchain

end SolverReachesFactorBaseCap
end Genus2Lean
