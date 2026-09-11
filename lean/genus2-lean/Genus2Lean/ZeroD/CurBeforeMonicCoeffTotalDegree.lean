import Mathlib
import Genus2Lean.ZeroD.NpolyCoeffTotalDegreeUniform
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationSolve
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-! Revision 08: move coeff-zero equality transport outside IsRdecWitness to avoid isDefEq timeout.  This version takes forever to build, please do not add more stuff to it -/

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
Claire tests. As of this pass, the file's full deliverable
(`curBeforeMonic_coeff_totalDegree_le`, the `≤315448` composition) is
written and sorry-free; nothing in this file is still unstarted. See the
`/-! ## Status -/` block at the end of this file for the most recent
fixes applied and REPL feedback so far.
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

omit hp2 in
/-- **Generic bound propagation for `IsRdecWitness.add`/`.mul`/`.neg`.**
Given witness pairs for `a`/`b` whose BOTH components are `≤ Da`/`≤ Db`
uniformly, the combined witness for `a+b` (`.add`, pair `(na*db+nb*da,
da*db)`) and `a*b` (`.mul`, pair `(na*nb, da*db)`) both have BOTH
components `≤ Da+Db`, and `-a`'s witness (`.neg`, pair `(-na,da)`) has
the SAME uniform bound `Da` as `a`'s. Packaged as one small reusable
lemma (rather than re-deriving `totalDegree_add_le`/`_mul`/`_neg` by hand
at each call site) since this file's final assembly needs the SAME
"both components share one uniform numeral" bookkeeping repeatedly. -/
theorem uniformBound_add {Vars : Type*}
    {n1 d1 n2 d2 : MvPolynomial Vars (F p)} {D1 D2 : ℕ}
    (h1 : n1.totalDegree ≤ D1 ∧ d1.totalDegree ≤ D1)
    (h2 : n2.totalDegree ≤ D2 ∧ d2.totalDegree ≤ D2) :
    (n1 * d2 + n2 * d1).totalDegree ≤ D1 + D2 ∧ (d1 * d2).totalDegree ≤ D1 + D2 := by
  refine ⟨le_trans (MvPolynomial.totalDegree_add _ _) ?_, ?_⟩
  · exact max_le
      (le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add h1.1 h2.2))
      (le_trans (MvPolynomial.totalDegree_mul _ _)
        ((Nat.add_le_add h2.1 h1.2).trans_eq (Nat.add_comm D2 D1)))
  · exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add h1.2 h2.2)

omit hp2 in
theorem uniformBound_mul {Vars : Type*}
    {n1 d1 n2 d2 : MvPolynomial Vars (F p)} {D1 D2 : ℕ}
    (h1 : n1.totalDegree ≤ D1 ∧ d1.totalDegree ≤ D1)
    (h2 : n2.totalDegree ≤ D2 ∧ d2.totalDegree ≤ D2) :
    (n1 * n2).totalDegree ≤ D1 + D2 ∧ (d1 * d2).totalDegree ≤ D1 + D2 :=
  ⟨le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add h1.1 h2.1),
   le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add h1.2 h2.2)⟩

omit hp2 in
theorem uniformBound_neg {Vars : Type*}
    {n d : MvPolynomial Vars (F p)} {D : ℕ}
    (h : n.totalDegree ≤ D ∧ d.totalDegree ≤ D) :
    (-n).totalDegree ≤ D ∧ d.totalDegree ≤ D :=
  ⟨(MvPolynomial.totalDegree_neg _).le.trans h.1, h.2⟩

set_option maxHeartbeats 20000000 in
/-- **The final assembly: a single uniform `totalDegree` bound `≤315448`
on `curBeforeMonic.coeff {0,1,2}`.** This is the file's own stated
deliverable. Given the SAME hypothesis bundle `Npoly_coeff_isRdecWitness_
uniform` needs, produces `IsRdecWitness` witnesses for `g.coeff 2`,
`g.coeff 1`, `g.coeff 0` (`g := curBeforeMonic`) with `totalDegree ≤
78848`/`≤157710`/`≤315448` respectively, via `uniformBound_add`/`_mul`/
`_neg` composed exactly as this file's header derives: `t1`/`t2` (`≤7`
via `t0_promoted_totalDegree_le`) and `gu0`/`gu1` (`≤0`, trivial) combine
to `Q.coeff 3`/`Q.coeff 2`, matching the header's own estimate: `Q.coeff 3
≤ 14` (`7+7+0`) and `Q.coeff 2 ≤ 28` (`7+7+(7+0)+(7+0)+0`). **Note on an
earlier draft of this comment**: an intermediate pass here mistakenly
claimed the composition gives `Q.coeff 2 ≤ 21`, dropping one `(7+0)` term
from the addition tree (`uniformBound_mul hbt2 hbgu1`'s own contribution);
that arithmetic was wrong, and the resulting `≤315441` final bound it
implied was never actually the type this file's `have hQ2bound`/
`hg0bound` proved (the underlying `have`s were untyped `_ ∧ _`+bare
`norm_num` at the time and the elaborator never actually forced a
numeral, which is how the error went unnoticed until `norm_num` was given
an explicit target). `28`/`315448` are the correct, REPL-confirmed
numbers — this docstring now matches the header again. These combine with
`Npoly`'s own `≤78848` witnesses (`Npoly_coeff_isRdecWitness_uniform`) to
give `g.coeff 2 ≤ 78848`, `g.coeff 1 ≤ 157710`, `g.coeff 0 ≤ 315448`,
solved top-down via `curBeforeMonic_coeff_{two,one,zero}_eq` rearranged. -/
theorem curBeforeMonic_coeff_totalDegree_le {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars (F p)))
    (hι_t : ∀ i : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X i)))) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.tGen i)))
    (hι_w1 : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 0)))
    (hι_w2 : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
        (MvPolynomial.X (sg.wGen 1)))
    (hbidx : ∀ col : Fin 4, otherIdx.getD col.val 0 < 5)
    (hAne : ∀ row col : Fin 4,
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((matrixA_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row col ι
          hι_t hι_w1 hι_w2 (hbidx col)).choose.2) ≠ 0)
    (hRne : ∀ row : Fin 4,
      (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((rhsVec_entry_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 row ι
          hι_t hι_w1 hι_w2).choose.2) ≠ 0)
    (hDne : (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((matrixDet_totalDegree_le p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
          hι_t hι_w1 hι_w2 hbidx hAne).choose.2) ≠ 0)
    (hιdet_ne : ι (matrixA p c0 c1 c2 c3 c4 u0 u1 v0 v1).det ≠ 0)
    (hA : MatrixNondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hMumford : IsMumfordTarget p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    (∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2) nd ∧
      nd.1.totalDegree ≤ 78848 ∧ nd.2.totalDegree ≤ 78848) ∧
    (∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1) nd ∧
      nd.1.totalDegree ≤ 157710 ∧ nd.2.totalDegree ≤ 157710) ∧
    (∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
      IsRdecWitness p ι
        (algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p))))
        ((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 0) nd ∧
      nd.1.totalDegree ≤ 315448 ∧ nd.2.totalDegree ≤ 315448) := by
  set evalNd := algebraMap (MvPolynomial Vars (F p)) (FractionRing (MvPolynomial Vars (F p)))
  -- `t1`/`t2`'s witness, uniform `≤7` both components.
  have ht1 : IsRdecWitness p ι evalNd (anchor1 p c0 c1 c2 c3 c4).1
      (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1) :=
    towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg _ ι hι_t hι_w1 hι_w2
  have ht2 : IsRdecWitness p ι evalNd (anchor2 p c0 c1 c2 c3 c4).1
      (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1) :=
    towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 sg _ ι hι_t hι_w1 hι_w2
  have hb1 := t0_promoted_totalDegree_le p sg c0 c1 c2 c3 c4 0
  have hb2 := t0_promoted_totalDegree_le p sg c0 c1 c2 c3 c4 1
  have hbt1 : (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).1.totalDegree ≤ 7 ∧
      (towerToRdec p sg (anchor1 p c0 c1 c2 c3 c4).1).2.totalDegree ≤ 7 :=
    ⟨hb1.1, hb1.2.trans (by norm_num)⟩
  have hbt2 : (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).1.totalDegree ≤ 7 ∧
      (towerToRdec p sg (anchor2 p c0 c1 c2 c3 c4).1).2.totalDegree ≤ 7 :=
    ⟨hb2.1, hb2.2.trans (by norm_num)⟩
  -- `gu0`/`gu1`'s trivial witness, `totalDegree 0`.
  have hgu1 : IsRdecWitness p ι evalNd (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)
      (MvPolynomial.C u1, (1 : MvPolynomial Vars (F p))) :=
    algebraMap_Fp_isRdecWitness p ι u1
  have hgu0 : IsRdecWitness p ι evalNd (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)
      (MvPolynomial.C u0, (1 : MvPolynomial Vars (F p))) :=
    algebraMap_Fp_isRdecWitness p ι u0
  have hbgu1 : (MvPolynomial.C u1 : MvPolynomial Vars (F p)).totalDegree ≤ 0 ∧
      (1 : MvPolynomial Vars (F p)).totalDegree ≤ 0 := by
    simp [MvPolynomial.totalDegree_C]
  have hbgu0 : (MvPolynomial.C u0 : MvPolynomial Vars (F p)).totalDegree ≤ 0 ∧
      (1 : MvPolynomial Vars (F p)).totalDegree ≤ 0 := by
    simp [MvPolynomial.totalDegree_C]
  -- `Q.coeff 3 = -t1-t2+gu1`, `≤14` both components (`7+7+0`).
  have hQ3wit := IsRdecWitness.add p
    (IsRdecWitness.add p (IsRdecWitness.neg p ht1) (IsRdecWitness.neg p ht2)) hgu1
  have hQ3boundRaw := uniformBound_add p
    (uniformBound_add p (uniformBound_neg p hbt1) (uniformBound_neg p hbt2)) hbgu1
  have hQ3bound : _ ∧ _ :=
    ⟨hQ3boundRaw.1.trans (by norm_num : (7+7+0:ℕ) ≤ 14),
     hQ3boundRaw.2.trans (by norm_num : (7+7+0:ℕ) ≤ 14)⟩
  -- `Q.coeff 2 = t1*t2-t1*gu1-t2*gu1+gu0`. Composition tree: `(t1*t2) +
  -- (-(t1*gu1)) + (-(t2*gu1)) + gu0`, bounds `7+7 + (7+0) + (7+0) + 0 = 28`
  -- summed left-to-right by `uniformBound_add`'s nesting below.
  have hQ2wit := IsRdecWitness.add p
    (IsRdecWitness.add p
      (IsRdecWitness.add p (IsRdecWitness.mul p ht1 ht2)
        (IsRdecWitness.neg p (IsRdecWitness.mul p ht1 hgu1)))
      (IsRdecWitness.neg p (IsRdecWitness.mul p ht2 hgu1))) hgu0
  have hQ2boundRaw := uniformBound_add p
    (uniformBound_add p
      (uniformBound_add p (uniformBound_mul p hbt1 hbt2)
        (uniformBound_neg p (uniformBound_mul p hbt1 hbgu1)))
      (uniformBound_neg p (uniformBound_mul p hbt2 hbgu1))) hbgu0
  have hQ2bound : _ ∧ _ :=
    ⟨hQ2boundRaw.1.trans (by norm_num : (7+7+(7+0)+(7+0)+0:ℕ) ≤ 28),
     hQ2boundRaw.2.trans (by norm_num : (7+7+(7+0)+(7+0)+0:ℕ) ≤ 28)⟩
  -- `Q.coeff 2 ≤ 28` matches the header's estimate exactly (`7+7+(7+0)+
  -- (7+0)+0`); an earlier pass here mistakenly claimed `≤21` after
  -- dropping a `(7+0)` term from the addition tree. `28` is what this
  -- composition actually gives and is used from here on.
  have hgcoeff2eq := curBeforeMonic_coeff_two_eq p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA hMumford
  have hgcoeff1eq := curBeforeMonic_coeff_one_eq p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA hMumford
  have hgcoeff0eq := curBeforeMonic_coeff_zero_eq p c0 c1 c2 c3 c4 u0 u1 v0 v1 hA hMumford
  obtain ⟨ndN6, hwitN6, hbN6a, hbN6b⟩ :=
    Npoly_coeff_isRdecWitness_uniform p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne 6
  obtain ⟨ndN5, hwitN5, hbN5a, hbN5b⟩ :=
    Npoly_coeff_isRdecWitness_uniform p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne 5
  obtain ⟨ndN4, hwitN4, hbN4a, hbN4b⟩ :=
    Npoly_coeff_isRdecWitness_uniform p c0 c1 c2 c3 c4 sg u0 u1 v0 v1 ι
      hι_t hι_w1 hι_w2 hbidx hAne hRne hDne hιdet_ne 4
  -- `g.coeff 2 = Npoly.coeff 6`: reuse `ndN6` directly, `≤78848`.
  have hgwit2 : IsRdecWitness p ι evalNd
      ((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2) ndN6 := by
    rw [← hgcoeff2eq]; exact hwitN6
  -- Build the coefficient-1 witness once.  Both the coefficient-1 and
  -- coefficient-0 branches need the same expression and bound; keeping it
  -- outside the branches avoids duplicating a fairly expensive term tree.
  have hg1wit := IsRdecWitness.add p hwitN5
    (IsRdecWitness.neg p (IsRdecWitness.mul p hgwit2 hQ3wit))
  have hg1bound := uniformBound_add p ⟨hbN5a, hbN5b⟩
    (uniformBound_neg p (uniformBound_mul p ⟨hbN6a, hbN6b⟩ hQ3bound))
  have hg1bound' : _ ∧ _ :=
    ⟨hg1bound.1.trans (by norm_num : (78848+(78848+14):ℕ) ≤ 157710),
     hg1bound.2.trans (by norm_num : (78848+(78848+14):ℕ) ≤ 157710)⟩
  -- Expand only the two Q-coefficients that occur below.  Doing this once
  -- avoids asking `ring` to normalize the enormous `curBeforeMonic` terms.
  have hQ3coeff :
      ((X - C (anchor1 p c0 c1 c2 c3 c4).1) *
          (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
          (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
            C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).coeff 3 =
        -(anchor1 p c0 c1 c2 c3 c4).1 +
          -(anchor2 p c0 c1 c2 c3 c4).1 +
            (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) := by
    have hQexpand :
        (X - C (anchor1 p c0 c1 c2 c3 c4).1) *
            (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
            (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
              C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) =
          X ^ 4 +
            C (-(anchor1 p c0 c1 c2 c3 c4).1 -
              (anchor2 p c0 c1 c2 c3 c4).1 +
              (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) * X ^ 3 +
            C ((anchor1 p c0 c1 c2 c3 c4).1 *
                (anchor2 p c0 c1 c2 c3 c4).1 -
              (anchor1 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) -
              (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) +
              (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) * X ^ 2 +
            C ((anchor1 p c0 c1 c2 c3 c4).1 *
                (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) -
              (anchor1 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) -
              (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) * X +
            C ((anchor1 p c0 c1 c2 c3 c4).1 *
                (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) := by
      simp only [map_sub, map_add, map_neg, map_mul]
      ring
    rw [hQexpand]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num <;> ring
  have hQ2coeff :
      ((X - C (anchor1 p c0 c1 c2 c3 c4).1) *
          (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
          (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
            C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))).coeff 2 =
        (anchor1 p c0 c1 c2 c3 c4).1 * (anchor2 p c0 c1 c2 c3 c4).1 +
          -((anchor1 p c0 c1 c2 c3 c4).1 *
            (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) +
          -((anchor2 p c0 c1 c2 c3 c4).1 *
            (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) +
          (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) := by
    have hQexpand2 :
        (X - C (anchor1 p c0 c1 c2 c3 c4).1) *
            (X - C (anchor2 p c0 c1 c2 c3 c4).1) *
            (X ^ 2 + C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * X +
              C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) =
          X ^ 4 +
            C (-(anchor1 p c0 c1 c2 c3 c4).1 -
              (anchor2 p c0 c1 c2 c3 c4).1 +
              (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) * X ^ 3 +
            C ((anchor1 p c0 c1 c2 c3 c4).1 *
                (anchor2 p c0 c1 c2 c3 c4).1 -
              (anchor1 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) -
              (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) +
              (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) * X ^ 2 +
            C ((anchor1 p c0 c1 c2 c3 c4).1 *
                (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) -
              (anchor1 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) -
              (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) * X +
            C ((anchor1 p c0 c1 c2 c3 c4).1 *
                (anchor2 p c0 c1 c2 c3 c4).1 *
                (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)) := by
      simp only [map_sub, map_add, map_neg, map_mul]
      ring
    rw [hQexpand2]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num <;> ring
  have hgcoeff1eq' : (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 =
      (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 5 +
      (-((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 *
        (-(anchor1 p c0 c1 c2 c3 c4).1 +
          -(anchor2 p c0 c1 c2 c3 c4).1 +
            (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)))) := by
    rw [hgcoeff1eq, hQ3coeff]
    ring
  refine ⟨⟨ndN6, hgwit2, hbN6a, hbN6b⟩, ?_, ?_⟩
  · -- `g.coeff 1 = Npoly.coeff 5 - g.coeff 2 * Q.coeff 3`.
    -- IMPORTANT: `hg1wit` proves the RHS.  The equality is `LHS = RHS`,
    -- so transport it with the symmetric equality (`RHS = LHS`).
    -- `hg1bound'` has already discharged the arithmetic to the concrete
    -- target `157710`, so do not invoke `norm_num` again here.
    exact ⟨_, hgcoeff1eq'.symm ▸ hg1wit, hg1bound'.1, hg1bound'.2⟩
  · -- `g.coeff 0 = Npoly.coeff 4 - g.coeff 1*Q.coeff 3 - g.coeff 2*Q.coeff 2`.
    have hgwit1 := hg1wit
    rw [← hgcoeff1eq'] at hgwit1
    have hg1q3mul := IsRdecWitness.mul p hgwit1 hQ3wit
    have hneg_g1q3 := IsRdecWitness.neg p hg1q3mul
    have hN4part := IsRdecWitness.add p hwitN4 hneg_g1q3
    have hg2q2mul := IsRdecWitness.mul p hgwit2 hQ2wit
    have hneg_g2q2 := IsRdecWitness.neg p hg2q2mul
    have hg0wit := IsRdecWitness.add p hN4part hneg_g2q2

    have hg1q3bound := uniformBound_mul p hg1bound' hQ3bound
    have hneg_g1q3bound := uniformBound_neg p hg1q3bound
    have hN4partbound := uniformBound_add p ⟨hbN4a, hbN4b⟩ hneg_g1q3bound
    have hg2q2bound := uniformBound_mul p ⟨hbN6a, hbN6b⟩ hQ2bound
    have hneg_g2q2bound := uniformBound_neg p hg2q2bound
    have hg0bound := uniformBound_add p hN4partbound hneg_g2q2bound
    have hgcoeff0eq' : (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 0 =
        (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 4 +
        (-((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 *
          (-(anchor1 p c0 c1 c2 c3 c4).1 +
            -(anchor2 p c0 c1 c2 c3 c4).1 +
              (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)))) +
        (-((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 *
          ((anchor1 p c0 c1 c2 c3 c4).1 * (anchor2 p c0 c1 c2 c3 c4).1 +
            -((anchor1 p c0 c1 c2 c3 c4).1 *
              (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) +
            -((anchor2 p c0 c1 c2 c3 c4).1 *
              (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) +
            (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0)))) := by
      rw [hgcoeff0eq, hQ3coeff, hQ2coeff]
      ring
    have hbound315448 : (78848+(157710+14)+(78848+28):ℕ) ≤ 315448 := by decide
    have hg0bound' : _ ∧ _ :=
      ⟨hg0bound.1.trans hbound315448, hg0bound.2.trans hbound315448⟩
    have hthird :
        (∃ nd : MvPolynomial Vars (F p) × MvPolynomial Vars (F p),
          IsRdecWitness p ι evalNd
            ((Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 4 +
              (-((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 *
                (-(anchor1 p c0 c1 c2 c3 c4).1 +
                  -(anchor2 p c0 c1 c2 c3 c4).1 +
                    (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)))) +
              (-((curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 2 *
                ((anchor1 p c0 c1 c2 c3 c4).1 * (anchor2 p c0 c1 c2 c3 c4).1 +
                  -((anchor1 p c0 c1 c2 c3 c4).1 *
                    (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) +
                  -((anchor2 p c0 c1 c2 c3 c4).1 *
                    (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1)) +
                  (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0))))) nd ∧
          nd.1.totalDegree ≤ 315448 ∧ nd.2.totalDegree ≤ 315448) := by
      exact ⟨_, hg0wit, hg0bound'.1, hg0bound'.2⟩
    simpa only [hgcoeff0eq'] using hthird

/-! ## Status, this pass

**Rev05: patched, NOT yet REPL-confirmed** (rewritten this edit to fix a REPL-
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

**Earlier pass — added the two remaining coefficient equations plus the
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
`hQ4`.

**This pass — the final `IsRdecWitness` composition, the file's actual
stated deliverable, is now written and closed.**
`curBeforeMonic_coeff_totalDegree_le` assembles `t1`/`t2`'s `≤7` witness
(`towerToRdec_isRdecWitness` + `t0_promoted_totalDegree_le`), `gu0`/`gu1`'s
trivial `≤0` witness (`algebraMap_Fp_isRdecWitness`), and
`Npoly_coeff_isRdecWitness_uniform`'s `≤78848` witnesses at `k=4,5,6`,
composed through `uniformBound_add`/`_mul`/`_neg` and the four coefficient
identities (`curBeforeMonic_coeff_{two,one,zero}_eq` plus
`Qpoly_coeff_three_and_two_eq`, expanded inline via `hQ3coeff`/`hQ2coeff`
rather than reusing the packaged theorem, to avoid re-deriving the `Q`
expansion under a different `set`/`clear_value` context) to close
`g.coeff 2 ≤ 78848`, `g.coeff 1 ≤ 157710`, `g.coeff 0 ≤ 315448` — exactly
the header's numbers, no discrepancy found this pass. One earlier-flagged
arithmetic slip (`Q.coeff 2 ≤ 21` instead of `28`, from a dropped
`(7+0)` term) was already caught and fixed before this composition was
written, so it did not recur here. **Not yet REPL-confirmed** — sent for
testing this pass; this closes `ROADMAP-crossnondegenerate-degree-bound.md`'s
"still fully unresolved" gap once Claire's build confirms it (`D` becomes
the concrete numeral `315448` in `crossResultant_totalDegree_le`/
`crossResultantV_totalDegree_le`, `CrossNondegenerateDegreeBound.lean`).

**REPL-confirmed green** (whole project build) — supersedes every "not
yet REPL-confirmed"/"Rev05: patched, NOT yet REPL-confirmed" note earlier
in this file, including the final composition theorem
`curBeforeMonic_coeff_totalDegree_le`. `D = 315448` is now a confirmed,
not merely claimed, concrete bound. -/

end TheDataDerivation
end Genus2Lean
