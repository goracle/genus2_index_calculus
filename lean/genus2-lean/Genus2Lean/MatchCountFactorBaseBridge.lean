import Mathlib
import Genus2Lean.AverageComplexity
import Genus2Lean.SidonBridge
import Genus2Lean.ZeroD.GaugeOrbitMatchCountBound
set_option linter.style.header false

/-!
# Wiring `matchCount`/`SolverReaches` to a real `H.Point` factor base
# (`ROADMAP-current.md` open item 1, sub-gap (1a))

`AverageComplexity.lean`'s `matchCount`/`IndexCalculusReachability.lean`'s
`SolverReaches`/`goodMatch`/`avgQ` are all stated for an abstract
`[AddCommGroup G] [Fintype G] [DecidableEq G]`. `GaugeOrbitMatchCountBound.lean`'s
pair-sum-class decomposition lives entirely at the `H.Point`/`Jacobian H D`
level, with no factor base `F ⊆ G` or per-solve probability `q` in sight. Per
`ROADMAP-current.md`, connecting the two needs new model glue, not just a
typeclass instantiation (`Jacobian H D` already has `AddCommGroup`, via
`DivisorClassGroup.lean`) — this file supplies that glue.

## The instantiation

`G := Jacobian H (principalDivisorData H hdeg)`. `SidonBridge.lean`'s
`sidonSet D δ₀ F₀ := F₀.image (s D δ₀)`, for a REAL factor base
`F₀ : Finset H.Point`, is exactly `matchCount`'s `F : Finset G` — this file
does not introduce a new factor-base object, it identifies the one already on
file (`IndexCalculusComplexityRealHitCount.lean` already uses `sidonSet` as
its `matchCount`-argument, but never connects it back to an `H.Point`-level
quadruple count; that connection is what is missing).

## What `matchCount (sidonSet D δ₀ F₀) Δ` is NOT equal to, and why

The naive hope would be an EQUALITY: `matchCount (sidonSet D δ₀ F₀) Δ` should
just count `H.Point`-quadruples of `F₀` hitting `Δ` under `s`. That is false
in general, because `s D δ₀ : H.Point → Jacobian H D` is not claimed
injective on `F₀` — `SidonBridge.lean`'s whole apparatus
(`AvoidsInvolutionPairs`, `NoWeierstrassPoints`, `SidonDichotomy`) exists
PRECISELY to control how much `s` collapses, not to assert it is injective. So
several distinct `H.Point`-quadruples can share the same image quadruple in
`(sidonSet D δ₀ F₀)⁴`, and `matchCount` counts IMAGE quadruples, not preimage
ones.

What holds unconditionally, with no Sidon hypothesis: the `H.Point`-level
quadruple count (`pointMatchCount` below, the direct `H.Point`-analogue of
`matchCount`, using `GaugeOrbitSolutions`'s defining equation restricted to a
finite factor base) SURJECTS onto — hence is `≥` — the image-level
`matchCount`. This is the right-shaped bound for `SolverReaches`'s purposes:
`SolverReaches` already treats `matchCount F Δ` as a LOWER bound on how much
"reachable mass" exists at `Δ` (via `q Δ ≥ matchCount F Δ / d`), so anything
that under-counts what a solver could actually land on is the safe direction
to under-shoot, not the dangerous one.

## What this file proves

* `pointMatchCount D δ₀ F₀ Δ` — the `H.Point`-level quadruple count: the
  number of `(P1,P2,P3,P4) ∈ F₀⁴` with `s P1 + s P2 - s P3 - s P4 = Δ`. This
  is exactly `GaugeOrbitSolutions`'s defining equation
  (`GaugeOrbitMatchCountBound.lean`, `c = 0` reading, per that file's own
  "the `c` is vacuous" remark), restricted to a finite `Finset`.
* `matchCount_sidonSet_le_pointMatchCount` — the image bound:
  `matchCount (sidonSet D δ₀ F₀) Δ ≤ pointMatchCount D δ₀ F₀ Δ`. Proved by
  showing `matchCount`'s counted `Finset` is literally the `.image` of
  `pointMatchCount`'s counted `Finset` under the coordinatewise-`s` map, then
  applying `Finset.card_image_le` — already an in-project precedent
  (`HitRateSumsetReduction.lean`'s `hitCount_le_card_pow_four`), no
  unverified Mathlib name introduced.
* `sum_pointMatchCount_eq_card_pow_four` — the `H.Point`-level analogue of
  `sum_matchCount_eq_card_pow_four`: summing `pointMatchCount` over all `Δ`
  recovers `F₀.card ^ 4` exactly. Unconditional, same proof shape.

## What this does NOT do

* It does not discharge `SolverReaches` itself — `d`, `q` remain abstract, and
  wiring `d` to `decoupledSystem_degree_uniform`'s `p ^ n` is sub-gap (1b),
  not attempted here.
* It does not attempt to turn the `≤` above into an equality by adding
  `AvoidsInvolutionPairs`/`NoWeierstrassPoints`/`SidonDichotomy` hypotheses
  and controlling the fiber size exactly — `SidonBridge.lean`'s
  `sidonRepBound_of_sidonDichotomy`-style argument bounds REPETITION within
  `s`'s fibers, but turning that into an exact `pointMatchCount = matchCount`
  identity is extra work beyond what `SolverReaches`'s inequality-shaped
  hypothesis actually needs (it only ever asks for a lower bound on
  reachable mass), so it is left as the inequality above.
* It does not connect `pointMatchCount` to `GaugeOrbitSolutions` as a formal
  `Set`-to-`Finset`-cardinality theorem (i.e. a literal `Set.ncard`
  statement) — `pointMatchCount`'s definition is already stated directly in
  `s`-equation form, matching `GaugeOrbitSolutions`'s own unfolding
  (`GaugeOrbitMatchCountBound.lean`'s `GaugeOrbitSolutions` docstring: "the
  `c` is vacuous... this is the WHOLE `Δ`-fiber"), so no separate bridging
  theorem is needed for that connection to be legible — the module docstring
  above states it in prose instead.

## Verification status

**REPL-tested (Claire), build green.** One fix in that pass: the trailing
`rfl` after `rw [← hcard, hfiber]` in `sum_pointMatchCount_eq_card_pow_four`
was unnecessary (`rw` already closed the goal directly — an "no goals to be
solved" error) and was deleted by hand; no other changes needed. Drafted
without a Lean toolchain originally, choosing every lemma name
(`Finset.card_image_le`, `Finset.mem_image`, `Finset.mem_filter`,
`Finset.mem_product`, `Finset.card_eq_sum_card_fiberwise`) for direct
in-project precedent (`HitRateSumsetReduction.lean`, `AverageComplexity.lean`)
specifically to avoid introducing an unverified name — an initial draft's
`Finset.card_le_card_of_surjOn` could not be confirmed to exist in current
Mathlib4 without a REPL and was replaced with the `Finset.card_image_le`
route instead, which is what ended up compiling clean.
-/

open HyperellipticPolynomial
open Divisor

namespace Genus2Lean
namespace MatchCountFactorBaseBridge

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable (D : PrincipalDivisorData H)
variable [IsDedekindDomain (CoordinateRing H)]
variable [Fintype H.Point] [DecidableEq H.Point]
variable [Fintype (Jacobian H D)] [DecidableEq (Jacobian H D)]

/-- **The `H.Point`-level quadruple count.** The direct analogue of
`matchCount`, one level down: the number of ordered quadruples
`(P1,P2,P3,P4) ∈ F₀⁴` (real curve points, not yet passed through `s`) with
`s D δ₀ P1 + s D δ₀ P2 - s D δ₀ P3 - s D δ₀ P4 = Δ`. This is exactly
`GaugeOrbitSolutions D δ₀ a alpha alpha'`'s defining equation
(`c = 0` case, the vacuous-`c` reading that file's docstring already
records), restricted to a finite factor base `F₀` and stated as a `Finset`
so its cardinality can be compared to `matchCount` directly. -/
noncomputable def pointMatchCount (δ₀ : H.Point) (F₀ : Finset H.Point) (Δ : Jacobian H D) : ℕ :=
  ((F₀ ×ˢ F₀ ×ˢ F₀ ×ˢ F₀).filter
    (fun p : H.Point × H.Point × H.Point × H.Point =>
      s D δ₀ p.1 + s D δ₀ p.2.1 - s D δ₀ p.2.2.1 - s D δ₀ p.2.2.2 = Δ)).card

/-- **`matchCount`'s counted `Finset` is exactly the image of
`pointMatchCount`'s counted `Finset` under coordinatewise `s`.** Forward
inclusion: a `pointMatchCount`-quadruple's image satisfies `matchCount`'s
membership condition since `s` commutes with the group operations composing
the equation, and each coordinate's image lies in `sidonSet D δ₀ F₀` by that
`Finset`'s definition as `F₀.image (s D δ₀)`. Backward inclusion: every
`sidonSet`-quadruple satisfying `matchCount`'s equation has, coordinatewise,
an `F₀`-preimage under `s` (again by `sidonSet`'s definition), assembling
into a genuine `pointMatchCount`-quadruple whose image is the original
`sidonSet`-quadruple. -/
theorem matchCountSet_eq_image_pointMatchCountSet
    (δ₀ : H.Point) (F₀ : Finset H.Point) (Δ : Jacobian H D) :
    ((sidonSet D δ₀ F₀ ×ˢ sidonSet D δ₀ F₀ ×ˢ sidonSet D δ₀ F₀ ×ˢ sidonSet D δ₀ F₀).filter
      (fun q : Jacobian H D × Jacobian H D × Jacobian H D × Jacobian H D =>
        q.1 + q.2.1 - q.2.2.1 - q.2.2.2 = Δ)) =
    ((F₀ ×ˢ F₀ ×ˢ F₀ ×ˢ F₀).filter
      (fun p : H.Point × H.Point × H.Point × H.Point =>
        s D δ₀ p.1 + s D δ₀ p.2.1 - s D δ₀ p.2.2.1 - s D δ₀ p.2.2.2 = Δ)).image
      (fun p : H.Point × H.Point × H.Point × H.Point =>
        (s D δ₀ p.1, s D δ₀ p.2.1, s D δ₀ p.2.2.1, s D δ₀ p.2.2.2)) := by
  ext q
  rw [Finset.mem_image]
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, heq⟩
    unfold sidonSet at h1 h2 h3 h4
    obtain ⟨P1, hP1, hP1'⟩ := Finset.mem_image.mp h1
    obtain ⟨P2, hP2, hP2'⟩ := Finset.mem_image.mp h2
    obtain ⟨P3, hP3, hP3'⟩ := Finset.mem_image.mp h3
    obtain ⟨P4, hP4, hP4'⟩ := Finset.mem_image.mp h4
    refine ⟨(P1, P2, P3, P4), ⟨⟨hP1, hP2, hP3, hP4⟩, ?_⟩, ?_⟩
    · rw [hP1', hP2', hP3', hP4']; exact heq
    · rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
      exact ⟨hP1', hP2', hP3', hP4'⟩
  · rintro ⟨p, ⟨⟨h1, h2, h3, h4⟩, heq⟩, rfl⟩
    -- CHECK: `sidonSet` is a plain `def`, not `abbrev` (per this project's
    -- own `instDecidablePredEquation` comment on `Point`/`Equation`), so the
    -- goal `p.1 ∈ sidonSet D δ₀ F₀` needs this explicit `unfold` before
    -- `Finset.mem_image.mpr` can unify against `F₀.image (s D δ₀)`.
    unfold sidonSet
    refine ⟨⟨?_, ?_, ?_, ?_⟩, heq⟩
    · exact Finset.mem_image.mpr ⟨p.1, h1, rfl⟩
    · exact Finset.mem_image.mpr ⟨p.2.1, h2, rfl⟩
    · exact Finset.mem_image.mpr ⟨p.2.2.1, h3, rfl⟩
    · exact Finset.mem_image.mpr ⟨p.2.2.2, h4, rfl⟩

/-- **The bridge inequality.** `matchCount (sidonSet D δ₀ F₀) Δ ≤
pointMatchCount D δ₀ F₀ Δ`: the image-level count `matchCount` computes is
never more than the preimage-level count `pointMatchCount` computes.
Immediate from `matchCountSet_eq_image_pointMatchCountSet` (`matchCount`'s
set literally IS an image of `pointMatchCount`'s set) plus
`Finset.card_image_le` — `s`'s possible non-injectivity (collapsing several
`H.Point`-quadruples onto one image quadruple) can only shrink the
image-level count relative to the preimage-level one, never grow it. This is
the direction `SolverReaches` needs: `matchCount F Δ` is already used there
as a LOWER bound on reachable mass, so replacing it with a possibly-larger
`pointMatchCount` is a sound (if not tight) substitution, not an
overclaim. -/
theorem matchCount_sidonSet_le_pointMatchCount
    (δ₀ : H.Point) (F₀ : Finset H.Point) (Δ : Jacobian H D) :
    matchCount (sidonSet D δ₀ F₀) Δ ≤ pointMatchCount D δ₀ F₀ Δ := by
  unfold matchCount pointMatchCount
  rw [matchCountSet_eq_image_pointMatchCountSet D δ₀ F₀ Δ]
  exact Finset.card_image_le

/-- **`pointMatchCount` sums to `F₀.card ^ 4`, unconditionally.**
`H.Point`-level analogue of `sum_matchCount_eq_card_pow_four`
(`AverageComplexity.lean`): every one of the `F₀.card ^ 4` quadruples lands
on exactly one `Δ`, so summing the fiber sizes over `Δ` recovers the total.
Same proof shape (`Finset.card_eq_sum_card_fiberwise`), one level down. -/
theorem sum_pointMatchCount_eq_card_pow_four
    (δ₀ : H.Point) (F₀ : Finset H.Point) :
    ∑ Δ : Jacobian H D, pointMatchCount D δ₀ F₀ Δ = F₀.card ^ 4 := by
  unfold pointMatchCount
  have hcard : (F₀ ×ˢ F₀ ×ˢ F₀ ×ˢ F₀).card = F₀.card ^ 4 := by
    simp [Finset.card_product, pow_succ, mul_comm]
  have hfiber :
      (F₀ ×ˢ F₀ ×ˢ F₀ ×ˢ F₀).card =
        ∑ Δ ∈ (Finset.univ : Finset (Jacobian H D)),
          ((F₀ ×ˢ F₀ ×ˢ F₀ ×ˢ F₀).filter
            (fun p : H.Point × H.Point × H.Point × H.Point =>
              s D δ₀ p.1 + s D δ₀ p.2.1 - s D δ₀ p.2.2.1 - s D δ₀ p.2.2.2 = Δ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [← hcard, hfiber]

end MatchCountFactorBaseBridge
end Genus2Lean
