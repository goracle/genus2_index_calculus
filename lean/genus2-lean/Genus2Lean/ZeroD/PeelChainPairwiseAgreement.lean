import Mathlib
import Genus2Lean.ZeroD.LinearElimDegreeBound
import Genus2Lean.ZeroD.CurveRelationsDegreeBound

/-!
# Pairwise agreement, per peel-chain stage

`ROADMAP-monic-annihilator-degree-uniform.md`'s "The actual remaining
blocker" section, CORRECTED this pass per a ChatGPT consult: the orbit-map/
connectedness route to `Δ = 0` is a dead end (the raw Jacobian matching
equation alone cannot force rigidity — genus 2 makes its solution set
positive-dimensional on its own; the SampleTarget polynomial equations are
where all the rigidity has to come from). The corrected target is a
**degree-1 / uniqueness** statement about the polynomial system itself:
two tuples of SampleTarget variables both solving the same fixed-`delta`
system agree coordinatewise. This file builds that fact one peel-chain
stage at a time, mirroring `LinearElimDegreeBound.lean`/
`CurveRelationsDegreeBound.lean`'s per-stage split exactly, but concluding
pairwise EQUALITY of the newly-peeled variable's two values instead of a
`finrank` bound.

**Why this is a genuinely separate (and smaller) claim than the `finrank`
bound**: `finrank_le_of_linear_elim`/`finrank_le_of_curve_relation` bound
the SIZE of the extended algebra `B` in one abstract copy of the peel
chain. Here there are two abstract copies of the SAME base algebra `A`
(sharing all previously-agreed coordinates) and two elements `t t' : A`
(not `: B` — the newly-peeled variable's two candidate values, still
living in the shared base ring `A`, before either is adjoined), and the
claim is `t = t'` given both satisfy the same relation over the same `A`.
No `finrank`/`Module.Finite`/tower-law content is needed at all for the
linear stages — pairwise agreement there is pure algebra in `A`, not a
dimension count.

## The two stage shapes, mirroring the `finrank` files exactly

- **Linear stages (`Fu0`–`Fu3`, `Fv0`–`Fv3`, `d = 1`)**: `t`'s value is
  literally FORCED by the relation `c = t * d` (`d` a unit) to
  `t = d⁻¹ * c` — a pure computation, already inlined once in
  `SharedPivotResultantElim.lean`'s proof (its `htval` step) and pulled
  out here as its own reusable lemma, `linearElim_forces_eq`, since both
  that file and this one need exactly the same fact. Two solutions `t, t'`
  of the SAME relation (same `c`, `d`) therefore agree immediately: both
  equal `d⁻¹ * c`, no further hypothesis needed.
- **Curve-relation stages (`curveA1`, ..., `d = 2`)**: `t² = f` does
  **NOT** force a unique `t` from `f` alone — this is exactly the
  "0-dimensional but not degree-1" gap the consult identified (a
  0-dimensional fiber can have several geometric points; a quadratic
  relation is the concrete source of that multiplicity here). Two roots
  `t, t'` of the same `X² − f` satisfy `(t-t')*(t+t') = 0`
  (`t² = t'² ⟹ t² - t'² = 0`), so agreement needs EITHER `t = t'`
  directly, or a side hypothesis ruling out `t = -t'` with `t ≠ t'` (e.g.
  `t + t' ≠ 0` if `A` has no zero divisors relevant here, or a sign
  convention pinning which square root is meant) — stated as an explicit
  extra hypothesis, `curveRelation_forces_eq`, rather than assumed to hold
  for free. **This is the one place this file does not yet fully close**;
  per the roadmap's own note, identifying which concrete side condition
  the four curve relations actually satisfy in `theData` (a sign
  convention on `wa1` etc., most likely — Mumford representation typically
  fixes a sign) is deferred to the wiring pass, not attempted here in the
  abstract setting.

## What this file does NOT do

Chain the twelve stages into one `x = x'` statement over `genList`'s
literal generators (that's the wiring pass, analogous to
`GenListFinrankAssembly.lean`/the not-yet-written
`GenListFinrankResultantAssembly.lean`), or connect the result back to
`matching_solutions_translate_by_delta`'s `Δ` (`MatchingEquationTranslation
.lean`) to conclude `Δ = 0` — both left to the next steps in the roadmap's
"Next concrete steps" list.
-/

namespace Genus2Lean

open Polynomial

variable {A : Type*} [CommRing A]

/-! ## Linear stages: agreement is automatic, both values are forced -/

/-- **The value-forcing computation**, pulled out of
`SharedPivotResultantElim.lean`'s inline proof (its `htval` step) as its
own reusable fact: if `t` satisfies the (non-monic) linear-elimination
relation `c = t * d` for a unit `d`, in ANY `A`-algebra `B`, then `t` is
forced to the single value `algebraMap A B (d⁻¹ * c)` — nothing about `B`
beyond being an `A`-algebra is used.

**Worked directly against `linearElimPoly`'s `aeval` unfolding, NOT via
`aeval_linearElimPoly_eq_zero_iff`**: that lemma (`LinearElimDegreeBound
.lean`) is stated under an ambient section carrying `[Nontrivial A]
[Algebra k A] [StrongRankCondition A] [Module.Finite k A]` etc. for its
OWN `finrank`-flavored theorems, and — since these are ordinary instance
arguments on the lemma itself, not merely in-scope conveniences — calling
it here would force this whole file to also carry a spurious `k`/finrank
typeclass stack that this file's actual content (pure `aeval` algebra,
no dimension-counting) never needs. Working directly with
`linearElimPoly`'s definition (`C c - X * C d`) avoids that entirely; the
computation itself is identical to `SharedPivotResultantElim.lean`'s
`htval` step, just restated as its own theorem over `linearElimPoly`
rather than the already-normalized `linearElimMonicPoly`. -/
theorem linearElim_forces_eq {B : Type*} [CommRing B] [Algebra A B]
    (c d : A) (hd : IsUnit d) (t : B)
    (ht : (Polynomial.aeval t) (linearElimPoly c d) = 0) :
    t = algebraMap A B (↑hd.unit⁻¹ * c) := by
  unfold linearElimPoly at ht
  rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_C, sub_eq_zero] at ht
  -- `ht : algebraMap A B c = t * algebraMap A B d`; solve for `t` using
  -- `hd.unit`'s inverse, mirroring `SharedPivotResultantElim.lean`'s own
  -- `hd1u : d1 * ↑hd1.unit⁻¹ = 1` cancellation exactly.
  have hdu : d * (↑hd.unit⁻¹ : A) = 1 := by
    nth_rewrite 1 [← hd.unit_spec]
    exact hd.unit.mul_inv
  have hstep : t * algebraMap A B d * algebraMap A B (↑hd.unit⁻¹ : A) =
      algebraMap A B c * algebraMap A B (↑hd.unit⁻¹ : A) := by rw [ht]
  rw [mul_assoc, ← map_mul, hdu, map_one, mul_one] at hstep
  -- `hstep : t = algebraMap A B c * algebraMap A B (↑hd.unit⁻¹)`; combine
  -- the two `algebraMap` factors (`map_mul`, forward direction) and
  -- reorder via `mul_comm` (`A` commutative) to match the goal's stated
  -- `↑hd.unit⁻¹ * c`.
  rw [hstep, ← map_mul, mul_comm (↑hd.unit⁻¹ : A) c]

/-- **Pairwise agreement, linear stages.** If `t, t' : B` both satisfy the
SAME linear-elimination relation `c = X * d` (same `c`, same `d`, same
unit witness `hd`) over the same base `A`, then `t = t'` — both are forced
to the identical value `algebraMap A B (d⁻¹ * c)` by
`linearElim_forces_eq`, no further hypothesis needed. This is the
degree-1-stage half of the peel chain's pairwise-agreement induction:
stages `Fu0`–`Fu3`, `Fv0`–`Fv3` (eight of the twelve) close via this one
lemma alone. -/
theorem linearElim_pairwise_eq {B : Type*} [CommRing B] [Algebra A B]
    (c d : A) (hd : IsUnit d) (t t' : B)
    (ht : (Polynomial.aeval t) (linearElimPoly c d) = 0)
    (ht' : (Polynomial.aeval t') (linearElimPoly c d) = 0) :
    t = t' := by
  rw [linearElim_forces_eq c d hd t ht, linearElim_forces_eq c d hd t' ht']

/-! ## Curve-relation stages: agreement needs an extra side condition -/

/-- **Two roots of the same curve relation `X² = f` differ by a sign**:
`(t - t') * (t + t') = 0`, immediate from `t² = f = t'²`. Stated
separately from `curveRelation_forces_eq` below since this half needs no
extra hypothesis at all — it's the "both roots satisfy this polynomial
identity" fact, true unconditionally, with the side hypothesis only
needed to rule out the `t = -t'` branch. -/
theorem curveRelation_sq_sub_sq_eq_zero {B : Type*} [CommRing B] [Algebra A B]
    (f : A) (t t' : B)
    (ht : (Polynomial.aeval t) (curveRelationPoly f) = 0)
    (ht' : (Polynomial.aeval t') (curveRelationPoly f) = 0) :
    (t - t') * (t + t') = 0 := by
  have ht2 : t ^ 2 = algebraMap A B f := by
    have h := ht
    unfold curveRelationPoly at h
    rwa [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at h
  have ht'2 : t' ^ 2 = algebraMap A B f := by
    have h := ht'
    unfold curveRelationPoly at h
    rwa [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at h
  have : t ^ 2 - t' ^ 2 = 0 := by rw [ht2, ht'2, sub_self]
  have hfact : (t - t') * (t + t') = t ^ 2 - t' ^ 2 := by ring
  rw [hfact, this]

/-- **Pairwise agreement, curve-relation stages — NEEDS a side
hypothesis, per this file's module docstring.** If `t, t'` are two roots
of the same `X² − C f`, and additionally `t + t' ≠ 0` fails to force
`t = -t'` as the ONLY alternative to `t = t'` (i.e. `IsDomain B` gives
`(t-t')*(t+t') = 0 → t = t' ∨ t = -t'`), then ruling out the `t = -t'`
branch via `hsign : t ≠ -t'` gives `t = t'`. **This file does not yet
identify whether `theData`'s actual `wa1`/`wa2`/`wb1`/`wb2` values satisfy
`hsign` for the SampleTarget pairs this project cares about** — flagged
here, not assumed, per the module docstring; likely resolved by whatever
sign convention `Reduce`'s Mumford-coordinate construction already fixes
for `w`, not attempted in this abstract setting. -/
theorem curveRelation_forces_eq {B : Type*} [CommRing B] [Algebra A B] [IsDomain B]
    (f : A) (t t' : B)
    (ht : (Polynomial.aeval t) (curveRelationPoly f) = 0)
    (ht' : (Polynomial.aeval t') (curveRelationPoly f) = 0)
    (hsign : t ≠ -t') :
    t = t' := by
  have hzero := curveRelation_sq_sub_sq_eq_zero f t t' ht ht'
  rcases mul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd (eq_neg_of_add_eq_zero_left h) hsign

end Genus2Lean
