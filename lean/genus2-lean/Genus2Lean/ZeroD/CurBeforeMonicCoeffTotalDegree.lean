import Mathlib
import Genus2Lean.ZeroD.NpolyCoeffTotalDegreeUniform
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationSolve
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# `curBeforeMonic.coeff {0,1,2}`'s own `IsRdecWitness` bound

Closes `ROADMAP-crossnondegenerate-degree-bound.md`'s "still fully
unresolved" gap: `crossResultant_totalDegree_le`/`crossResultantV_
totalDegree_le` (`CrossNondegenerateDegreeBound.lean`) carry a base-case
bound `D` on `uRS`/`vRS`'s coefficients as a HYPOTHESIS. `uRS`/`vRS` are
built from `curBeforeMonic`'s own coefficients, so pinning `D` down to a
concrete number needs a `totalDegree` bound on `curBeforeMonic.coeff
{0,1,2}` (its only nonzero coefficients, since `curBeforeMonic_natDegree_
le_two` bounds its degree). Mathlib has no general "totalDegree of an
exact polynomial quotient" lemma (`curBeforeMonic` is defined via three
nested `/ₘ` steps), so this file avoids division altogether and instead
uses the EXACT multiplication identity `Npoly_eq_curBeforeMonic_mul`
(`Npoly = curBeforeMonic * (t1X * t2X * U)`, already proved) plus the
triangular coefficient system this factorization forces, following a
ChatGPT consultation confirming this route (`Polynomial.coeff_mul_of_
natDegree_le` for the top coefficient; a small explicit `Finset.range`
unfolding for the other two, since `curBeforeMonic`/`Q`'s degrees are
tiny and fixed).

**The route, concretely.** Write `g := curBeforeMonic`, `Q := t1X * t2X *
U` (`t1X := X - C t1`, `t2X := X - C t2`, `U := X^2 + C u1 * X + C u0`,
`t1 := (anchor1 p ...).1`, `t2 := (anchor2 p ...).1`). `g.natDegree ≤ 2`
(`curBeforeMonic_natDegree_le_two`, unconditional) and `Q.natDegree ≤ 4`
(`t1X`/`t2X` each degree 1 via `Polynomial.monic_X_sub_C`'s companion
degree fact, `U` degree 2 via `uPoly_monic`'s own `compute_degree!`-closed
degree fact, `Polynomial.Monic.natDegree_mul` twice). Expanding `Q` by
hand (`t1X*t2X*U`, a routine `ring`-checkable polynomial identity in `X`
with coefficients in `t1,t2,u0,u1`) gives closed forms for `Q.coeff 2/3/4`:
`Q.coeff 4 = 1`, `Q.coeff 3 = -(t1+t2)+u1`, `Q.coeff 2 = t1*t2-(t1+t2)*u1+u0`.
`f := Npoly = g * Q` then gives, by direct (small, hand-checked) expansion
of a degree-`≤2` times degree-`≤4` product: `f.coeff 6 = g.coeff 2`,
`f.coeff 5 = g.coeff 1 + g.coeff 2 * Q.coeff 3`, `f.coeff 4 = g.coeff 0 +
g.coeff 1 * Q.coeff 3 + g.coeff 2 * Q.coeff 2` — a triangular system
(matching `Q`'s monicity: the diagonal coefficient of each equation is
literally `1`), solved directly for `g.coeff 2, g.coeff 1, g.coeff 0` in
that order, no division needed at any step.

**Lean proof shape for the three coefficient equations.** All three use
the SAME route (`Polynomial.coeff_mul_of_natDegree_le` was tried first
for `f.coeff 6` specifically, since `6 = 2+4` exactly, but REPL-confirmed
that name doesn't exist in this project's Mathlib snapshot — see the
`/-! ## Status -/` block below for the correction): rewrite `(g*Q).coeff
k` via `Polynomial.coeff_mul` + `Finset.Nat.sum_antidiagonal_eq_sum_
range_succ` into `∑ i ∈ Finset.range (k+1), g.coeff i * Q.coeff (k-i)`
(same idiom `NpolyCoeffTotalDegree.lean` already uses), then unfold the
(small, fixed: 7, 6, or 5 terms) `Finset.range` sum explicitly via
`Finset.sum_range_succ`/`Finset.sum_range_zero`, killing every term with
`i > 2` (`g.coeff i = 0`, `Polynomial.coeff_eq_zero_of_natDegree_lt`
against `g.natDegree ≤ 2`) or `k - i > 4` (`Q.coeff (k-i) = 0`, same
lemma against `Q.natDegree ≤ 4`) via `omega`-closed side goals, leaving
exactly the 1 (resp. 2, resp. 3) surviving terms the hand computation
above predicts.

**The `totalDegree` bound itself.** `t1`/`t2`'s own `towerToRdec` witness
bound is `≤7`/`≤6` (`t0_promoted_totalDegree_le` at `i=0`/`i=1` — `t1 :=
(anchor1 p ...).1`/`t2 := (anchor2 p ...).1` ARE exactly this promotion
chain applied to `t0 p 0`/`t0 p 1`, per `anchor1`/`anchor2`'s own
definitions, `DataDerivationSolve.lean`), and `u0`/`u1` (already `F p`-
valued) get the trivial `(C x, 1)` witness, `totalDegree 0` each side, via
`algebraMap_Fp_isRdecWitness`. Composing through `IsRdecWitness.add`/`.mul`/
`.neg` (`sub` as `add` + `neg`) for `Q.coeff 3`/`Q.coeff 2`'s formulas
above, using a single uniform bound `7` for BOTH components of `t1`/`t2`'s
witness (safe since `.add`'s combinator only needs an upper bound, not the
tight one) gives `Q.coeff 3 ≤ (14,14)`, `Q.coeff 2 ≤ (28,28)` — reported
here uniformly (`≤14`, `≤28`) rather than tracking numerator/denominator
separately, matching this file's own "one crude uniform numeral" style
(`NpolyCoeffTotalDegreeUniform.lean`'s precedent). `f.coeff {4,5,6} =
Npoly.coeff {4,5,6}` is `≤78848` uniformly on both sides (`Npoly_coeff_
isRdecWitness_uniform`, ALREADY `k`-independent — using this rather than
`Npoly_coeff_isRdecWitness`'s own `k`-dependent formula is what keeps the
final numeral small and simple). Solving the triangular system with
`IsRdecWitness.add`/`.mul`/`.neg` (bound arithmetic: `.mul`'s pair has
`totalDegree ≤` the SUM of its factors' bounds; `.add`'s pair has
`totalDegree ≤` the SUM of its two summands' bounds — both via
`MvPolynomial.totalDegree_mul`/`_add`, exactly as `IsRdecWitness_
finsetSum_totalDegree_le`'s own header derives) gives, in order:
`g.coeff 2 ≤ 78848`; `g.coeff 1 ≤ 78848 + (78848+14) = 157710`;
`g.coeff 0 ≤ 78848 + (157710+14) + (78848+28) = 315448`. A single
uniform bound `315448` covers all three (`g.coeff 0`'s is the largest,
monotone by construction), which is this file's final stated result.

**Not yet REPL-confirmed** — per project convention, Claude drafts,
Claire tests. See the `/-! ## Status -/` block at the end of this file
for the most recent REPL feedback and fixes applied.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)

/-- **`Q := t1X * t2X * U` has `natDegree ≤ 4`.** `t1X`/`t2X` are each
`X - C _`, degree exactly 1 (`Polynomial.degree_X_sub_C`); `U := X^2 +
C u1 * X + C u0` has degree exactly 2 (`uPoly_monic`'s own `compute_
degree!`-closed fact, promoted to `K2` via `Polynomial.natDegree_map_le`
— `U` here is already the `K2`-valued polynomial, defined as the `map` of
the `F p`-valued one per `Npoly_eq_curBeforeMonic_mul`'s own proof).
Combines via `Polynomial.natDegree_mul_le` twice (`≤`-only version,
unconditional, no nonzero-factor hypothesis needed). -/
theorem Qpoly_natDegree_le_four :
    ((X - C (anchor1 p c0 c1 c2 c3 c4).1) * (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
        (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
          C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).natDegree ≤ 4 := by
  have h1 : (X - C (anchor1 p c0 c1 c2 c3 c4).1 :
      Polynomial (K2 p c0 c1 c2 c3 c4)).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_sub_C]
  have h2 : (X - C (anchor2 p c0 c1 c2 c3 c4).1 :
      Polynomial (K2 p c0 c1 c2 c3 c4)).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_sub_C]
  have hUmap : (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
      C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) : Polynomial (K2 p c0 c1 c2 c3 c4)) =
      (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).map
        (algebraMap (F p) (K2 p c0 c1 c2 c3 c4)) := by
    simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
  have hUdeg0 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree ≤ 2 := by
    compute_degree
  have h3 : (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
      C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) :
      Polynomial (K2 p c0 c1 c2 c3 c4)).natDegree ≤ 2 := by
    rw [hUmap]
    exact le_trans Polynomial.natDegree_map_le hUdeg0
  have h12 := Polynomial.natDegree_mul_le
    (p := (X - C (anchor1 p c0 c1 c2 c3 c4).1 : Polynomial (K2 p c0 c1 c2 c3 c4)))
    (q := (X - C (anchor2 p c0 c1 c2 c3 c4).1 : Polynomial (K2 p c0 c1 c2 c3 c4)))
  have h123 := Polynomial.natDegree_mul_le
    (p := ((X - C (anchor1 p c0 c1 c2 c3 c4).1) * (X - C (anchor2 p c0 c1 c2 c3 c4).1) :
      Polynomial (K2 p c0 c1 c2 c3 c4)))
    (q := (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
      C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) : Polynomial (K2 p c0 c1 c2 c3 c4)))
  omega

set_option maxHeartbeats 20000000 in
/-- **`Npoly.coeff 6 = curBeforeMonic.coeff 2`.** The top-coefficient
case: `Npoly = g * Q` (`g := curBeforeMonic`, `Q` as above) with `g.natDegree
≤ 2`, `Q.natDegree ≤ 4`. Rewrites `(g*Q).coeff 6` via `Polynomial.coeff_mul`
+ `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` into an explicit 7-term
`Finset.range` sum, then unfolds it directly: every term but `i = 2`
vanishes (`i > 2` kills `g.coeff i` via `g.natDegree ≤ 2`; `i < 2` kills
`Q.coeff (6-i)` via `Q.natDegree ≤ 4`), leaving `g.coeff 2 * Q.coeff 4 =
g.coeff 2 * 1`. `Q.coeff 4 = 1` comes from a direct `ring`-checkable
expansion of `Q` into its four named coefficients (`sympy`-verified
against the hand computation in this file's header), with `t1`/`t2`/
`gu0`/`gu1` abstracted via `set`/`clear_value` first so `ring` treats
them as opaque atoms rather than unfolding the `K2` tower. -/
theorem curBeforeMonic_coeff_two_eq
    (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hMumford : IsMumfordTarget p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 6 =
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 := by
  -- **Correction, this edit**: the earlier draft used `Polynomial.coeff_
  -- mul_of_natDegree_le`, which REPL-confirmed does NOT exist under that
  -- name in this project's Mathlib snapshot (`Unknown constant` error) —
  -- an unconfirmed name that turned out to be mathlib3-only/stale, exactly
  -- the risk this project's own convention warns about. Fixed by dropping
  -- that lemma entirely and using the same `Polynomial.coeff_mul` +
  -- `Finset.range`-unfolding idiom this file already needs for `f.coeff
  -- 5`/`f.coeff 4` below (`NpolyCoeffTotalDegree.lean`'s own proven-safe
  -- pattern) — unifies all three coefficient proofs under one robust
  -- route instead of depending on a second, riskier API surface.
  have hgdeg := Genus2Lean.DecoupledSystem.curBeforeMonic_natDegree_le_two
    p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hQdeg := Qpoly_natDegree_le_four p c0 c1 c2 c3 c4 u0 u1
  have hfeq := Npoly_eq_curBeforeMonic_mul p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA hMumford
  set t1 := (anchor1 p c0 c1 c2 c3 c4).1
  set t2 := (anchor2 p c0 c1 c2 c3 c4).1
  set gu1 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1
  set gu0 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0
  clear_value t1 t2 gu1 gu0
  set g := curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1
  set Q := (X - C t1) * (X - C t2) * (X ^ 2 + C gu1 * X + C gu0) with hQ_def
  rw [hfeq]
  have hrange : (g * Q).coeff 6 =
      ∑ i ∈ Finset.range 7, g.coeff i * Q.coeff (6 - i) := by
    rw [Polynomial.coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => g.coeff i * Q.coeff j) 6
  rw [hrange]
  -- Unfold the 7-term sum explicitly; every term but `i = 2` vanishes
  -- (`i > 2` kills `g.coeff i` via `hgdeg`, `6 - i > 4` — i.e. `i < 2` —
  -- kills `Q.coeff (6-i)` via `hQdeg`), leaving `g.coeff 2 * Q.coeff 4`.
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hz0 : g.coeff 0 = 0 ∨ Q.coeff 6 = 0 := Or.inr
    (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hz1 : g.coeff 1 = 0 ∨ Q.coeff 5 = 0 := Or.inr
    (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hz3 : g.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hz4 : g.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hz5 : g.coeff 5 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hz6 : g.coeff 6 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hQ4 : Q.coeff 4 = 1 := by
    have heq : Q = X ^ 4 + C (- t1 - t2 + gu1) * X ^ 3 +
        C (t1 * t2 - t1 * gu1 - t2 * gu1 + gu0) * X ^ 2 +
        C (t1 * t2 * gu1 - t1 * gu0 - t2 * gu0) * X +
        C (t1 * t2 * gu0) := by
      rw [hQ_def]
      simp only [map_sub, map_add, map_neg, map_mul]
      ring
    rw [heq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  rcases hz0 with hz0 | hz0 <;> rcases hz1 with hz1 | hz1 <;>
    simp [hz0, hz1, hz3, hz4, hz5, hz6, hQ4]

set_option maxHeartbeats 20000000 in
/-- **`Npoly.coeff 5 = curBeforeMonic.coeff 1 + curBeforeMonic.coeff 2 *
Q.coeff 3`.** The second-from-top coefficient case, same route as
`curBeforeMonic_coeff_two_eq`: `(g*Q).coeff 5` unfolds (via `Polynomial.
coeff_mul` + `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` into a
6-term `Finset.range` sum) to `g.coeff 1 * Q.coeff 4 + g.coeff 2 *
Q.coeff 3` (every other term killed by `g.natDegree ≤ 2`/`Q.natDegree ≤
4`), and `Q.coeff 4 = 1` (same `hQ4` computation) collapses the first
term to `g.coeff 1`. -/
theorem curBeforeMonic_coeff_one_eq
    (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hMumford : IsMumfordTarget p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 5 =
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 +
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 *
        ((X - C (anchor1 p c0 c1 c2 c3 c4).1) * (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
          (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
            C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).coeff 3 := by
  have hgdeg := Genus2Lean.DecoupledSystem.curBeforeMonic_natDegree_le_two
    p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hQdeg := Qpoly_natDegree_le_four p c0 c1 c2 c3 c4 u0 u1
  have hfeq := Npoly_eq_curBeforeMonic_mul p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA hMumford
  set t1 := (anchor1 p c0 c1 c2 c3 c4).1
  set t2 := (anchor2 p c0 c1 c2 c3 c4).1
  set gu1 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1
  set gu0 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0
  clear_value t1 t2 gu1 gu0
  set g := curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1
  set Q := (X - C t1) * (X - C t2) * (X ^ 2 + C gu1 * X + C gu0) with hQ_def
  rw [hfeq]
  have hrange : (g * Q).coeff 5 =
      ∑ i ∈ Finset.range 6, g.coeff i * Q.coeff (5 - i) := by
    rw [Polynomial.coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => g.coeff i * Q.coeff j) 5
  rw [hrange]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- Surviving terms: `i = 1` (`Q.coeff 4`) and `i = 2` (`Q.coeff 3`);
  -- `i = 0` needs `Q.coeff 5 = 0` (kills it since `Q.natDegree ≤ 4`).
  have hz0 : g.coeff 0 = 0 ∨ Q.coeff 5 = 0 := Or.inr
    (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  have hz3 : g.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hz4 : g.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hz5 : g.coeff 5 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hQ4 : Q.coeff 4 = 1 := by
    have heq : Q = X ^ 4 + C (- t1 - t2 + gu1) * X ^ 3 +
        C (t1 * t2 - t1 * gu1 - t2 * gu1 + gu0) * X ^ 2 +
        C (t1 * t2 * gu1 - t1 * gu0 - t2 * gu0) * X +
        C (t1 * t2 * gu0) := by
      rw [hQ_def]
      simp only [map_sub, map_add, map_neg, map_mul]
      ring
    rw [heq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  rcases hz0 with hz0 | hz0 <;> simp [hz0, hz3, hz4, hz5, hQ4]

set_option maxHeartbeats 20000000 in
/-- **`Npoly.coeff 4 = curBeforeMonic.coeff 0 + curBeforeMonic.coeff 1 *
Q.coeff 3 + curBeforeMonic.coeff 2 * Q.coeff 2`.** The bottom
coefficient case, same route once more: `(g*Q).coeff 4` unfolds (5-term
`Finset.range` sum) to `g.coeff 0 * Q.coeff 4 + g.coeff 1 * Q.coeff 3 +
g.coeff 2 * Q.coeff 2` (all other terms killed by degree), and `Q.coeff
4 = 1` collapses the first term to `g.coeff 0`. -/
theorem curBeforeMonic_coeff_zero_eq
    (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hMumford : IsMumfordTarget p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 4 =
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 0 +
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 *
        ((X - C (anchor1 p c0 c1 c2 c3 c4).1) * (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
          (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
            C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).coeff 3 +
      (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 *
        ((X - C (anchor1 p c0 c1 c2 c3 c4).1) * (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
          (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
            C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).coeff 2 := by
  have hgdeg := Genus2Lean.DecoupledSystem.curBeforeMonic_natDegree_le_two
    p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hQdeg := Qpoly_natDegree_le_four p c0 c1 c2 c3 c4 u0 u1
  have hfeq := Npoly_eq_curBeforeMonic_mul p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA hMumford
  set t1 := (anchor1 p c0 c1 c2 c3 c4).1
  set t2 := (anchor2 p c0 c1 c2 c3 c4).1
  set gu1 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1
  set gu0 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0
  clear_value t1 t2 gu1 gu0
  set g := curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1
  set Q := (X - C t1) * (X - C t2) * (X ^ 2 + C gu1 * X + C gu0) with hQ_def
  rw [hfeq]
  have hrange : (g * Q).coeff 4 =
      ∑ i ∈ Finset.range 5, g.coeff i * Q.coeff (4 - i) := by
    rw [Polynomial.coeff_mul]
    exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => g.coeff i * Q.coeff j) 4
  rw [hrange]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- Surviving terms: `i = 0` (`Q.coeff 4`), `i = 1` (`Q.coeff 3`),
  -- `i = 2` (`Q.coeff 2`); nothing else to kill here since the range
  -- only has 5 terms (`i = 0,1,2,3,4`) and `g.coeff {3,4} = 0` already
  -- kills the remaining two.
  have hz3 : g.coeff 3 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hz4 : g.coeff 4 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hQ4 : Q.coeff 4 = 1 := by
    have heq : Q = X ^ 4 + C (- t1 - t2 + gu1) * X ^ 3 +
        C (t1 * t2 - t1 * gu1 - t2 * gu1 + gu0) * X ^ 2 +
        C (t1 * t2 * gu1 - t1 * gu0 - t2 * gu0) * X +
        C (t1 * t2 * gu0) := by
      rw [hQ_def]
      simp only [map_sub, map_add, map_neg, map_mul]
      ring
    rw [heq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  simp only [hz3, hz4, hQ4, mul_zero, mul_one, add_zero, zero_add]
  ring

set_option maxHeartbeats 20000000 in
/-- **`Q.coeff 3` and `Q.coeff 2`'s literal formulas**, as reusable
facts — same `heq` expansion `hQ4` above uses, read off at coefficients
3 and 2 instead of 4. Packaged as a pair rather than two separate
theorems since both come from the same `heq` rewrite and are always
needed together downstream (the `IsRdecWitness` composition for
`g.coeff 1`/`g.coeff 0`). -/
theorem Qpoly_coeff_three_and_two_eq :
    ((X - C (anchor1 p c0 c1 c2 c3 c4).1) * (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
        (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
          C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).coeff 3 =
      - (anchor1 p c0 c1 c2 c3 c4).1 - (anchor2 p c0 c1 c2 c3 c4).1 +
        algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1 ∧
    ((X - C (anchor1 p c0 c1 c2 c3 c4).1) * (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
        (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
          C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).coeff 2 =
      (anchor1 p c0 c1 c2 c3 c4).1 * (anchor2 p c0 c1 c2 c3 c4).1 -
        (anchor1 p c0 c1 c2 c3 c4).1 * algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1 -
        (anchor2 p c0 c1 c2 c3 c4).1 * algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1 +
        algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0 := by
  set t1 := (anchor1 p c0 c1 c2 c3 c4).1
  set t2 := (anchor2 p c0 c1 c2 c3 c4).1
  set gu1 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1
  set gu0 := algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0
  clear_value t1 t2 gu1 gu0
  have heq : (X - C t1) * (X - C t2) * (X ^ 2 + C gu1 * X + C gu0) =
      X ^ 4 + C (- t1 - t2 + gu1) * X ^ 3 +
      C (t1 * t2 - t1 * gu1 - t2 * gu1 + gu0) * X ^ 2 +
      C (t1 * t2 * gu1 - t1 * gu0 - t2 * gu0) * X +
      C (t1 * t2 * gu0) := by
    simp only [map_sub, map_add, map_neg, map_mul]
    ring
  rw [heq]
  refine ⟨?_, ?_⟩ <;>
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num

/-! ## Status, this pass

**Drafted, NOT yet REPL-confirmed** (rewritten this edit to fix a REPL-
reported `Unknown constant` error — see below). Adds `curBeforeMonic_
coeff_two_eq` (`Npoly.coeff 6 = curBeforeMonic.coeff 2`), the top-
coefficient case of the triangular system.

**`Unknown constant` error, fixed this edit**: the previous draft used
`Polynomial.coeff_mul_of_natDegree_le`, which REPL-confirmed does NOT
exist under that name in this project's Mathlib snapshot. Web search had
suggested this name was current Mathlib4 (`Mathlib.Algebra.Polynomial.
Degree.Lemmas`), but the REPL is ground truth and the search result was
apparently stale/mathlib3-only (a real historical name, `data.polynomial.
degree.lemmas`, that either never ported to Lean 4 under this name or was
renamed) — exactly the "ChatGPT/search confabulates a plausible-looking
name" risk this project's own convention warns about. **Fix**: dropped
that lemma entirely. All three coefficient equations (`f.coeff 6/5/4`)
now go through the SAME robust, already-proven-safe route this codebase
uses elsewhere (`NpolyCoeffTotalDegree.lean`'s own idiom): `Polynomial.
coeff_mul` + `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` to get an
explicit `Finset.range (k+1)` sum, then `Finset.sum_range_succ`/`_zero`
to unfold it into named terms, each killed by `Polynomial.coeff_eq_zero_
of_natDegree_lt` against `hgdeg`/`hQdeg` except the ones the hand
computation (this file's header) predicts survive. This is slightly more
verbose than the single-lemma route would have been but depends on
strictly fewer, already-load-bearing-elsewhere Mathlib names.

**Also carried over from the previous edit**: `t1`/`t2`/`gu1`/`gu0`
(`(anchor1/anchor2 p ...).1`, the two `algebraMap (F p) (K2 ...) u{0,1}`
terms) are abstracted via `set ... ; clear_value` immediately after
`hfeq`/`g`/`Q` are introduced, so the `ring` call inside `hQ4` treats them
as opaque atoms rather than re-elaborating the full `K2` tower — this was
the fix for a genuine REPL-reported heartbeat timeout in an earlier
version of this same theorem, kept since the underlying tower-depth
concern is unchanged by this edit's other fix.

**Still not attempted this pass**: `curBeforeMonic.coeff 1`/`.coeff 0`'s
own equations (`f.coeff 5`/`f.coeff 4`, same `Finset.range`-unfolding
route as `curBeforeMonic_coeff_two_eq` now uses, just with more surviving
terms per the hand computation in this file's header), `Q.coeff 3`/
`Q.coeff 2`'s own literal formulas as separate reusable `have`s (needed
by those two equations, same shape as `hQ4`'s `heq` above), and the final
`IsRdecWitness` composition assembling `≤315448`. Kept for the next edit
to stay under a reviewable diff size.

**Unsolved-goals error, fixed this edit**: REPL reported `hQ4`'s closing
`simp` left one goal open after `rw [heq]` — `simp`'s default set unfolded
`(X^4).coeff 4` to `1` but did not fully reduce the two cross terms
`(C _ * X^3).coeff 4`/`(C _ * X^2).coeff 4` to `0` (their `natDegree ≠ 4`
fact isn't in `simp`'s default closure for `Polynomial.coeff` on a bare
`C a * X^n` shape). **Fix**: replaced the bare `simp` with an explicit
`simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.
coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]` (turns every
`(C a * X^n).coeff 4` into `a * (if n = 4 then 1 else 0)`-shaped terms,
and the bare `C d` term into an `if 4 = 0 then d else 0` term) followed by
`norm_num` to discharge the resulting `if`-conditions (`4 ≠ 3,2,1,0`) and
finish the arithmetic. REPL-confirmed green this pass (whole project
builds).

**This pass — added the two remaining coefficient equations plus the
`Q.coeff {3,2}` literal formulas.** `curBeforeMonic_coeff_one_eq`
(`Npoly.coeff 5 = g.coeff 1 + g.coeff 2 * Q.coeff 3`) and
`curBeforeMonic_coeff_zero_eq` (`Npoly.coeff 4 = g.coeff 0 + g.coeff 1 *
Q.coeff 3 + g.coeff 2 * Q.coeff 2`) follow `curBeforeMonic_coeff_two_eq`'s
exact route (`Polynomial.coeff_mul` + `Finset.Nat.sum_antidiagonal_eq_
sum_range_succ` + `Finset.sum_range_succ`/`_zero` unfolding, `hQ4`'s same
`Q.coeff 4 = 1` computation), just with more surviving terms per the
6-term/5-term ranges. `curBeforeMonic_coeff_one_eq`'s closing step needed
an `hz0 : g.coeff 0 = 0 ∨ Q.coeff 5 = 0` disjunction (same pattern as
`curBeforeMonic_coeff_two_eq`'s `hz0`/`hz1`) since `g.natDegree ≤ 2` alone
doesn't kill the `i=0` term directly — `rcases`'d before the closing
`simp`. `curBeforeMonic_coeff_zero_eq`'s closing step needed no
disjunction (`g.coeff 3 = 0`/`g.coeff 4 = 0` suffice outright), but its
final `simp [...]; ring` was changed to `simp only [...]; ring` to avoid
a "no goals" error if `simp` alone happened to fully close the arithmetic
identity — `simp only` with this specific lemma list normalizes the
zero/one terms but leaves genuine commutativity/associativity to `ring`,
guaranteeing there's always a goal left for it. `Qpoly_coeff_three_and_
two_eq` packages `Q.coeff 3 = -t1-t2+gu1` and `Q.coeff 2 = t1*t2-t1*gu1-
t2*gu1+gu0` as a single `∧`-conjunction theorem (both come from the same
`heq` rewrite, always needed together downstream), proved via `refine
⟨?_, ?_⟩ <;> · simp only [...]; norm_num`, same coefficient-lemma list as
`hQ4`. **Not yet REPL-confirmed** — sent for testing this pass.

**Still not attempted**: the final `IsRdecWitness` composition
(`towerToRdec`-style bound assembly, target uniform numeral `≤315448` per
this file's header) that turns these four algebraic identities into the
actual `totalDegree` bound on `curBeforeMonic.coeff {0,1,2}` — this is
the file's actual stated deliverable and is still open. -/

end TheDataDerivation
end Genus2Lean
