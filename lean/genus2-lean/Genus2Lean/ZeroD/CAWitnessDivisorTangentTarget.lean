import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangentTarget
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.LPairFinrankOneOrdAtFrac

/-!
# Divisor-level fact for `CAWitnessTangentTarget.lean`'s target-tangent
# case `f := y - bCATangentTarget(x)`

Target-axis sibling of `CAWitnessDivisorTangent.lean`'s
`ordAt_denomCATangent_eq_two_at_Ra`/`_eq_one_at_P1`/`_eq_one_at_P2`,
per `ROADMAP-split-hypothesis-elimination.md`'s "item 2 (new)" (the
target-axis mirror of `ROADMAP-principal-witness-tangent-assembly.md`,
which built only the anchor axis). Same recipe: `ordAt_eq_one_of_old_
point`/`ordAt_eq_two_of_old_point` (`PrincipalWitness.lean`) applied at
each named point, with `A := denomPolyCATangentTarget` and `U :=
-uCANewTangentTarget` — but here the doubled multiplicity-2 point is
`P` (the collapsed target pair), and `Ra1, Ra2` are the two ordinary
(multiplicity-1) points, the mirror image of `CAWitnessDivisorTangent.
lean`'s own role assignment.

Built as `ordAt_denomCATangentTarget_eq_one_at_Ra1`/`_eq_one_at_Ra2`/
`_eq_two_at_P`, same local three-factor composition
(`ordAt_linX_eq_one_of_ne_zero`/`ordAt_linX_eq_zero_of_ne'`/
`ordAt_linX_pow_unramified` glued via `ordAt_add_of_pairNorm_eq_mul`)
as `CAWitnessDivisorTangent.lean`'s own three theorems, with the
squared factor moved from the first named point to the third.

**Scoped to the target-tangent case only** (`Ra1X, Ra2X, PX` pairwise
distinct, `sa.P1 = sa.P2 =: P` already collapsed) — mirrors
`CAWitnessDivisorTangent.lean`'s own scoping precedent, just the other
axis.
-/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **Local Layer-3-tangent-target, `Ra1` side: `ordAt Q
denomPolyCATangentTarget 0 = 1` at `Ra1`.** `denomPolyCATangentTarget =
(X-C Ra1X) * (X-C Ra2X) * (X-C PX)^2`; at `Q` with `Q.X = Ra1X`, `Q.Y ≠
0`: the first factor contributes `1` (`ordAt_linX_eq_one_of_ne_zero`),
the other two contribute `0` each (`ordAt_linX_eq_zero_of_ne'`,
`ordAt_linX_pow_unramified` with the squared factor's order-0 branch
coming from `Ra1X ≠ PX`), composed via two applications of
`ordAt_add_of_pairNorm_eq_mul`. -/
theorem ordAt_denomCATangentTarget_eq_one_at_Ra1
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX : k) (h12 : Ra1X ≠ Ra2X) (h1 : Ra1X ≠ PX)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = Ra1X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCATangentTarget Ra1X Ra2X PX) (0 : k[X]) = 1 := by
  have heq : denomPolyCATangentTarget Ra1X Ra2X PX =
      (linX Ra1X * linX Ra2X) * (linX PX) ^ 2 := by
    unfold denomPolyCATangentTarget linX; ring
  rw [heq]
  have hR1_ne : toPair H (linX Ra1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra1X) hA
  have hR2_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hP_ne : toPair H ((linX PX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero PX)) hA
  have hR1 : ordAt Q (linX Ra1X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf Ra1X Q h_bot hQX hQY
  have hR2 : ordAt Q (linX Ra2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra2X Q h_bot (hQX ▸ h12)
  have hP : ordAt Q ((linX PX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX PX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf PX Q h_bot (hQX ▸ h1)
    have h0ne : toPair H (linX PX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero PX) hA
    have hsq : ((linX PX : k[X]) ^ 2) = linX PX * linX PX := by ring
    rw [hsq, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX PX * linX PX)
      (linX PX) (linX PX) rfl h0ne h0ne, h0]
    norm_num
  have h1_ne : toPair H (linX Ra1X * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hR1_ne hR2_ne
  have hstep1 : ordAt Q (linX Ra1X * linX Ra2X) (0 : k[X]) = 1 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX Ra1X * linX Ra2X)
      (linX Ra1X) (linX Ra2X) rfl hR1_ne hR2_ne, hR1, hR2]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX Ra1X * linX Ra2X) * (linX PX) ^ 2)
    (linX Ra1X * linX Ra2X) ((linX PX) ^ 2) rfl h1_ne hP_ne, hstep1, hP]
  norm_num

/-- **Local Layer-3-tangent-target, `Ra2` side.** Mirror of the `Ra1`
case. -/
theorem ordAt_denomCATangentTarget_eq_one_at_Ra2
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX : k) (h12 : Ra1X ≠ Ra2X) (h2 : Ra2X ≠ PX)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = Ra2X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCATangentTarget Ra1X Ra2X PX) (0 : k[X]) = 1 := by
  have heq : denomPolyCATangentTarget Ra1X Ra2X PX =
      (linX Ra2X * linX Ra1X) * (linX PX) ^ 2 := by
    unfold denomPolyCATangentTarget linX; ring
  rw [heq]
  have hR1_ne : toPair H (linX Ra1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra1X) hA
  have hR2_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hP_ne : toPair H ((linX PX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero PX)) hA
  have hR2 : ordAt Q (linX Ra2X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf Ra2X Q h_bot hQX hQY
  have hR1 : ordAt Q (linX Ra1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra1X Q h_bot (hQX ▸ h12.symm)
  have hP : ordAt Q ((linX PX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX PX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf PX Q h_bot (hQX ▸ h2)
    have h0ne : toPair H (linX PX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero PX) hA
    have hsq : ((linX PX : k[X]) ^ 2) = linX PX * linX PX := by ring
    rw [hsq, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX PX * linX PX)
      (linX PX) (linX PX) rfl h0ne h0ne, h0]
    norm_num
  have h1_ne : toPair H (linX Ra2X * linX Ra1X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hR2_ne hR1_ne
  have hstep1 : ordAt Q (linX Ra2X * linX Ra1X) (0 : k[X]) = 1 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX Ra2X * linX Ra1X)
      (linX Ra2X) (linX Ra1X) rfl hR2_ne hR1_ne, hR2, hR1]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX Ra2X * linX Ra1X) * (linX PX) ^ 2)
    (linX Ra2X * linX Ra1X) ((linX PX) ^ 2) rfl h1_ne hP_ne, hstep1, hP]
  norm_num

/-- **Local Layer-3-tangent-target, doubled `P` side: `ordAt Q
denomPolyCATangentTarget 0 = 2` at the doubled target node.** The
squared factor `(X-C PX)^2` contributes `2`
(`ordAt_linX_pow_unramified` with `m := 2`), the other two contribute
`0` each. -/
theorem ordAt_denomCATangentTarget_eq_two_at_P
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X PX : k) (h1 : Ra1X ≠ PX) (h2 : Ra2X ≠ PX)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = PX) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCATangentTarget Ra1X Ra2X PX) (0 : k[X]) = 2 := by
  have heq : denomPolyCATangentTarget Ra1X Ra2X PX =
      (linX Ra1X * linX Ra2X) * (linX PX) ^ 2 := by
    unfold denomPolyCATangentTarget linX; ring
  rw [heq]
  have hR1_ne : toPair H (linX Ra1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra1X) hA
  have hR2_ne : toPair H (linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero Ra2X) hA
  have hP_ne : toPair H ((linX PX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero PX)) hA
  have hR1 : ordAt Q (linX Ra1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra1X Q h_bot (hQX ▸ h1.symm)
  have hR2 : ordAt Q (linX Ra2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf Ra2X Q h_bot (hQX ▸ h2.symm)
  have hP : ordAt Q ((linX PX) ^ 2) (0 : k[X]) = 2 := by
    have := ordAt_linX_pow_unramified (H := H) hchar PX Q h_bot hQX hQY 2
    simpa using this
  have h1_ne : toPair H (linX Ra1X * linX Ra2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hR1_ne hR2_ne
  have hstep1 : ordAt Q (linX Ra1X * linX Ra2X) (0 : k[X]) = 0 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX Ra1X * linX Ra2X)
      (linX Ra1X) (linX Ra2X) rfl hR1_ne hR2_ne, hR1, hR2]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX Ra1X * linX Ra2X) * (linX PX) ^ 2)
    (linX Ra1X * linX Ra2X) ((linX PX) ^ 2) rfl h1_ne hP_ne, hstep1, hP]
  norm_num

end DecoupledSystem
end Genus2Lean
