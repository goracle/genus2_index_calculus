import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.ZeroD.CAWitness

/-! # `bCA`'s CROSS-pair tangent case (`Ra1.X = sa.P1.X`-style): the
same-sign sub-case is impossible

Per `ROADMAP-cawitness-tangent-interpolation.md`, Part B, case 3. Unlike
cases 1 (`Ra1X = Ra2X`) and 2 (`P1X = P2X`), a cross-pair collision
(one anchor point and one target point sharing an `x`-coordinate) is
NOT automatically a genuine tangency: since both points lie on the
curve `y² = f(x)` at the same `x`, their `y`-coordinates can only be
equal or negatives of each other — i.e. `Ra1 = sa.P1` or
`Ra1 = ι(sa.P1)`, nothing else (`AffinePoints.lean`'s `Point` is a
subtype of `k × k` cut out by the curve equation, so two points sharing
an `x`-coordinate have `y`-values that are both square roots of the
same `H.f.eval x`, hence equal or negated).

- `Ra1 = sa.P1` (the "same sign" sub-case, `Ra1.Y = sa.P1.Y`): this
  makes the anchor point and target point LITERALLY THE SAME POINT.
  That is not a tangency at all — it is excluded by this project's
  existing convention that anchor points (`Sanchor`/`Ra1,Ra2`) and
  target points (`{sa.P1,sa.P2}`) are honestly different divisors
  (`SanchorEqAlphaPoints.lean`'s module docstring: "`Sanchor` is not,
  and has no reason to be, `{sa.P1,sa.P2}`"). Nothing new to prove here
  beyond `Ra1 = sa.P1`; the caller-level exclusion belongs wherever
  `Ra1 ≠ sa.P1`-style hypotheses are ultimately required, not in this
  file.
- `Ra1 = ι(sa.P1)`, i.e. `Ra1.Y = -sa.P1.Y`: the only case that is a
  genuine confluent-interpolation tangency (handled separately, in the
  matrix-construction file this one is a prerequisite for — not
  attempted here).

This file proves the dichotomy itself (`eq_or_eq_iota_of_X_eq`) plus
the corollary the top-level theorem actually needs
(`eq_iota_of_X_eq_of_ne`): given the caller already has `Ra1 ≠ sa.P1`
(the existing anchor/target distinctness this project already treats
as basic — see docstring above), a shared `x`-coordinate forces the
`ι`-conjugate case outright. No `sorry`, no interpolation machinery —
pure point-and-curve algebra. -/

noncomputable section

open Polynomial

namespace HyperellipticPolynomial
namespace Point

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}

/-- **Two points on the curve sharing an `x`-coordinate are equal or
`ι`-conjugate.** Both `y`-values square to the same `H.f.eval x`
(`Y_sq` plus `hXeq`), so their difference-of-squares factors as
`(P.Y - Q.Y) * (P.Y + Q.Y) = 0`. -/
theorem eq_or_eq_iota_of_X_eq {P Q : H.Point} (hXeq : P.X = Q.X) :
    P = Q ∨ P = Point.iota Q := by
  have hsq : P.Y ^ 2 = Q.Y ^ 2 := by
    rw [Point.Y_sq, Point.Y_sq, hXeq]
  have hfactor : (P.Y - Q.Y) * (P.Y + Q.Y) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfactor with hd | hs
  · left
    have hYeq : P.Y = Q.Y := by linear_combination hd
    exact Subtype.ext (Prod.ext hXeq hYeq)
  · right
    have hXeq' : P.X = (Point.iota Q).X := by rw [Point.iota_X]; exact hXeq
    have hYeq' : P.Y = (Point.iota Q).Y := by rw [Point.iota_Y]; linear_combination hs
    exact Subtype.ext (Prod.ext hXeq' hYeq')

/-- **The corollary the top-level theorem needs**: given the existing
anchor/target distinctness convention (`Ra1 ≠ P1` as points, i.e. they
are not literally the same point of the curve — see module docstring),
a cross-pair `x`-coordinate collision forces the `ι`-conjugate case.
No `char ≠ 2`/`Y ≠ 0` hypothesis is needed for this direction (only for
ruling out `Ra1 = P1` in the first place, which this lemma takes as
given rather than re-deriving — deriving it needs a genuine reason two
constructed points coincide, which is caller-specific and out of scope
here). -/
theorem eq_iota_of_X_eq_of_ne {P Q : H.Point} (hXeq : P.X = Q.X)
    (hne : P ≠ Q) : P = Point.iota Q :=
  (eq_or_eq_iota_of_X_eq hXeq).resolve_left hne

end Point
end HyperellipticPolynomial
