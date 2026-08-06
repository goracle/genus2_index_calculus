import Mathlib
import Genus2Lean.HyperellipticFunctionField
noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# Genus-2 index calculus: affine points of `C` and the point-level involution

`HyperellipticFunctionField.lean` builds the coordinate ring `k[x,y]/(y²-f(x))`
and a *ring* involution `ι : CoordinateRing H →+* CoordinateRing H` sending
`y ↦ -y`. Advisory-7 §4 (the Forey–Fresán–Kowalski Sidon theorem) is a
statement about *points* `x ∈ C(k)` and the *point-level* hyperelliptic
involution `ι : C → C`, `(x,y) ↦ (x,-y)` — not directly about the ring. This
file supplies that missing layer: the affine point type, its embedding into
`CoordinateRing H`, and the point-level involution, together with the
naturality fact tying it back to `HyperellipticFunctionField.lean`'s
`involution`. This is the first of several files needed before the FFK
theorem itself (§4) can be stated, let alone proved: still missing after
this file are the Jacobian `J` (or a degree-0-divisor-class stand-in for it)
and the embedding map `s : C → J`.

Design note: only the affine model is covered here (points `(x,y)` with
`y² = f(x)`), not the points at infinity needed to compactify `C`. For
`H.f.natDegree = 6` there are two points at infinity (swapped by `ι`); for
`H.f.natDegree = 5` there is one (fixed by `ι`). Advisory-7's factor bases
are built from finite affine points (§7.1 "Verify the factor base excludes
hyperelliptic-involution pairs" is phrased in `(x,y)` terms throughout), so
the affine-only model is sufficient for the Sidon theorem's application
here; the points-at-infinity case is flagged as a gap, not silently assumed
away, should a fully general statement of FFK's theorem be wanted later.
-/

namespace HyperellipticPolynomial

variable {k : Type*} [Field k]

/-- An affine point of the genus-2 hyperelliptic curve `C : y² = f(x)`:
a pair `(x, y) : k × k` satisfying the defining equation. Mirrors the shape
of Mathlib's `WeierstrassCurve.Affine.Point` (an `(x,y)` pair subject to the
curve equation), for which no hyperelliptic (genus ≥ 2) analogue currently
exists in Mathlib. -/
def Equation (H : HyperellipticPolynomial k) (x y : k) : Prop :=
  y ^ 2 = H.f.eval x

/-- The type of affine points of `C`, as a subtype of `k × k`. -/
def Point (H : HyperellipticPolynomial k) : Type _ :=
  {p : k × k // H.Equation p.1 p.2}

namespace Point

variable {H : HyperellipticPolynomial k}

/-- Build an affine point from coordinates and a proof of the curve equation. -/
def mk (x y : k) (h : H.Equation x y) : H.Point :=
  ⟨(x, y), h⟩

@[simp] theorem equation (P : H.Point) : H.Equation P.1.1 P.1.2 := P.2

/-- The `x`-coordinate of an affine point. -/
def X (P : H.Point) : k := P.1.1

/-- The `y`-coordinate of an affine point. -/
def Y (P : H.Point) : k := P.1.2

@[simp] theorem Y_sq (P : H.Point) : P.Y ^ 2 = H.f.eval P.X := P.equation

/-- The point-level hyperelliptic involution `ι : C → C`, `(x,y) ↦ (x,-y)`.
This is the object advisory-7 §4's Sidon theorem is stated in terms of
(`x2 = ι(x1)`), distinct from `HyperellipticFunctionField.lean`'s ring-level
`involution`; `iota_toRingElem` below is the compatibility statement
connecting the two. -/
def iota (P : H.Point) : H.Point :=
  ⟨(P.X, -P.Y), by
    show (-P.Y) ^ 2 = H.f.eval P.X
    rw [neg_sq]; exact P.equation⟩

@[simp] theorem iota_X (P : H.Point) : (iota P).X = P.X := rfl

@[simp] theorem iota_Y (P : H.Point) : (iota P).Y = -P.Y := rfl

/-- The point-level involution is genuinely an involution: `ι(ι(P)) = P`. -/
@[simp] theorem iota_iota (P : H.Point) : iota (iota P) = P := by
  have hX : (iota (iota P)).X = P.X := by rw [iota_X, iota_X]
  have hY : (iota (iota P)).Y = P.Y := by rw [iota_Y, iota_Y, neg_neg]
  exact Subtype.ext (Prod.ext hX hY)

/-- `ι` has no fixed points away from `Y = 0` (the ramification/Weierstrass
points of `C`, where `x` is a root of `f`). This is the condition advisory-7
§4 needs when it asks the factor base to avoid "hyperelliptic-involution
pairs": for `P` with `P.Y ≠ 0`, `P` and `ι(P)` are always the two distinct
points above `P.X`. Needs `char k ≠ 2` explicitly — `HyperellipticPolynomial`
itself (`HyperellipticFunctionField.lean`) documents this as a standing
assumption for genus-2 models but does not enforce it as a hypothesis on the
structure, so it is stated here rather than silently inherited. -/
theorem iota_ne_self_of_Y_ne_zero (hchar : (2 : k) ≠ 0) {P : H.Point} (hY : P.Y ≠ 0) :
    iota P ≠ P := by
  intro heq
  apply hY
  have hy : (iota P).Y = P.Y := by rw [heq]
  rw [iota_Y] at hy
  have h2 : (2 : k) * P.Y = 0 := by linear_combination -hy
  rcases mul_eq_zero.mp h2 with h2' | hy0
  · exact absurd h2' hchar
  · exact hy0

end Point

variable {H : HyperellipticPolynomial k}

/-- The embedding `C(k) → CoordinateRing H` sending an affine point `(x,y)`
to `x + y·y` — the natural map realizing a point of the curve as an element
of its own coordinate ring. Defined directly as `toPair H (C x) (C y)`
(`HyperellipticFunctionField.lean`), so the naturality statement below
(`iota_toRingElem`) is an immediate consequence of the already-proven
`toPair_involution` rather than requiring its own unfolding argument. -/
noncomputable def Point.toRingElem (P : H.Point) : H.CoordinateRing :=
  toPair H (Polynomial.C P.X) (Polynomial.C P.Y)

/-- **Naturality**: the point-level involution `ι` and the ring-level
`involution` (`HyperellipticFunctionField.lean`) agree under `toRingElem` —
i.e. `toRingElem` intertwines the two involutions. This is what licenses
reusing `HyperellipticFunctionField.lean`'s ring machinery (`toPair_involution`,
`toPair_mul_involution`, `toPair_add_involution`) for point-level arguments
about `ι` going forward. -/
theorem Point.iota_toRingElem (P : H.Point) :
    (Point.iota P).toRingElem = H.involution P.toRingElem := by
  show toPair H (Polynomial.C (Point.iota P).X) (Polynomial.C (Point.iota P).Y) =
    H.involution (toPair H (Polynomial.C P.X) (Polynomial.C P.Y))
  rw [Point.iota_X, Point.iota_Y, map_neg, toPair_involution]

end HyperellipticPolynomial
