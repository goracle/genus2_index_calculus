import Mathlib
import Genus2Lean.ZeroD.CAWitnessTangent
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.LPairFinrankOneOrdAtFrac

/-!
# Divisor-level fact for `CAWitnessTangent.lean`'s tangent-case `f :=
y - bCATangent(x)`

Tangent-case sibling of `CAWitnessDivisor.lean`'s
`divToPair_eq_C_add_iotaA_of_split`, per
`ROADMAP-principal-witness-tangent-assembly.md`'s Step 2 (traced here
before Step 3, as that doc's own "what NOT to do" section requires).
Same recipe as the split case — `ordAt_eq_one_of_old_point`/
`ordAt_eq_two_of_old_point` (`PrincipalWitness.lean`) applied at each
named point, with `A := denomPolyCATangent` and `U := -uCANewTangent` —
but with only THREE named points (`Ra, PtιP1, PtιP2`), `Ra` carrying
multiplicity `2` (the doubled anchor root) instead of two separate
`PtRa1, PtRa2` each carrying `1`.

**New Layer-3-tangent composition, not present in `PrincipalWitness.
lean`**: `denomPolyCATangent = (X-C RaX)² * (X-C P1X) * (X-C P2X)` needs
`ordAt Q ... = 2`, not `1` — `PrincipalWitness.lean`'s own
`ordAt_A_eq_one_of_eval_ne_zero` (Layer 3) is built for the FOUR-factor,
all-order-1 shape and doesn't generalize directly. Built here instead as
`ordAt_denomCATangent_eq_two_at_Ra`/`_eq_zero_at_P1`/`_eq_zero_at_P2` (a
local three-factor composition: `(linX RaX)^2` contributes order `2` via
`ordAt_linX_pow_unramified` (`LPairFinrankOneOrdAtFrac.lean`, already
proved for general `m`, no `rootMultiplicity` detour needed — mirrors
`SanchorMumfordOrdAt.lean`'s doubled-root precedent but through the more
direct existing lemma rather than that file's `rootMultiplicity_X_sub_
C_pow` route), composed with `ordAt_add_of_pairNorm_eq_mul` twice for the
other two factors' order-0 contributions — kept LOCAL to this file since
it is specific to `denomPolyCATangent`'s exact three-factor shape, same
placement choice `SanchorMumfordOrdAt.lean` made for its own analogous
`ordAt_ua_eq_two_of_mem_Sanchor_tangent`, not added to
`PrincipalWitness.lean` itself.

**Scoped to the tangent case only** (`RaX, P1X, P2X` pairwise distinct,
`Ra1 = Ra2 =: Ra` already collapsed) — mirrors `divToPair_eq_C_add_
iotaA_of_split`'s own scoping precedent, just one axis over.
-/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **Local Layer-3-tangent: `ordAt Q denomPolyCATangent 0 = 2` at the
doubled anchor point.** `denomPolyCATangent = (X-C RaX)^2 * (X-C P1X) *
(X-C P2X)`; at `Q` with `Q.X = RaX`, `Q.Y ≠ 0`: the squared factor
contributes `2` (`ordAt_linX_pow_unramified` with `m := 2`), the other
two contribute `0` each (`ordAt_linX_eq_zero_of_ne'`, from `RaX ≠ P1X`/
`RaX ≠ P2X`), composed via two applications of
`ordAt_add_of_pairNorm_eq_mul`. -/
theorem ordAt_denomCATangent_eq_two_at_Ra
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X : k) (h1 : RaX ≠ P1X) (h2 : RaX ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = RaX) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCATangent RaX P1X P2X) (0 : k[X]) = 2 := by
  have heq : denomPolyCATangent RaX P1X P2X =
      ((linX RaX) ^ 2 * linX P1X) * linX P2X := by
    unfold denomPolyCATangent linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hF1_ne : toPair H (linX P1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P1X) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 2 := by
    have := ordAt_linX_pow_unramified (H := H) hchar RaX Q h_bot hQX hQY 2
    simpa using this
  have hF1 : ordAt Q (linX P1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P1X Q h_bot (hQX ▸ h1)
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P2X Q h_bot (hQX ▸ h2)
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX P1X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hF1_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX P1X) (0 : k[X]) = 2 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX P1X)
      ((linX RaX) ^ 2) (linX P1X) rfl hL_ne hF1_ne, hL, hF1]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX P1X) * linX P2X)
    ((linX RaX) ^ 2 * linX P1X) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-tangent, `P1` side: `ordAt Q denomPolyCATangent 0 =
1` at `P1`.** `(X-C RaX)^2` contributes `0` (`Q.X = P1X ≠ RaX`), `(X-C
P1X)` contributes `1` (`ordAt_linX_eq_one_of_ne_zero`), `(X-C P2X)`
contributes `0`. -/
theorem ordAt_denomCATangent_eq_one_at_P1
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X : k) (h1 : RaX ≠ P1X) (hPP : P1X ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = P1X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCATangent RaX P1X P2X) (0 : k[X]) = 1 := by
  have heq : denomPolyCATangent RaX P1X P2X =
      ((linX RaX) ^ 2 * linX P1X) * linX P2X := by
    unfold denomPolyCATangent linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hF1_ne : toPair H (linX P1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P1X) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX RaX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf RaX Q h_bot (hQX ▸ (Ne.symm h1))
    have h0ne : toPair H (linX RaX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero RaX) hA
    have : ((linX RaX : k[X]) ^ 2) = linX RaX * linX RaX := by ring
    rw [this, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX RaX * linX RaX)
      (linX RaX) (linX RaX) rfl h0ne h0ne, h0]
    norm_num
  have hF1 : ordAt Q (linX P1X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf P1X Q h_bot hQX hQY
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P2X Q h_bot (hQX ▸ hPP)
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX P1X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hF1_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX P1X) (0 : k[X]) = 1 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX P1X)
      ((linX RaX) ^ 2) (linX P1X) rfl hL_ne hF1_ne, hL, hF1]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX P1X) * linX P2X)
    ((linX RaX) ^ 2 * linX P1X) (linX P2X) rfl h1_ne hF2_ne, hstep1, hF2]
  norm_num

/-- **Local Layer-3-tangent, `P2` side: `ordAt Q denomPolyCATangent 0 =
1` at `P2`.** Mirror of the `P1` case. -/
theorem ordAt_denomCATangent_eq_one_at_P2
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (RaX P1X P2X : k) (h2 : RaX ≠ P2X) (hPP : P1X ≠ P2X)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hQX : Q.X = P2X) (hQY : Q.Y ≠ 0) :
    ordAt Q (denomPolyCATangent RaX P1X P2X) (0 : k[X]) = 1 := by
  have heq : denomPolyCATangent RaX P1X P2X =
      ((linX RaX) ^ 2 * linX P2X) * linX P1X := by
    unfold denomPolyCATangent linX; ring
  rw [heq]
  have hL_ne : toPair H ((linX RaX) ^ 2) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (pow_ne_zero 2 (linX_ne_zero RaX)) hA
  have hF2_ne : toPair H (linX P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P2X) hA
  have hF1_ne : toPair H (linX P1X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => (linX_ne_zero P1X) hA
  have hL : ordAt Q ((linX RaX) ^ 2) (0 : k[X]) = 0 := by
    have h0 : ordAt Q (linX RaX) (0 : k[X]) = 0 :=
      ordAt_linX_eq_zero_of_ne' hchar hsf RaX Q h_bot (hQX ▸ (Ne.symm h2))
    have h0ne : toPair H (linX RaX) (0 : k[X]) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => (linX_ne_zero RaX) hA
    have : ((linX RaX : k[X]) ^ 2) = linX RaX * linX RaX := by ring
    rw [this, ordAt_add_of_pairNorm_eq_mul Q h_bot (linX RaX * linX RaX)
      (linX RaX) (linX RaX) rfl h0ne h0ne, h0]
    norm_num
  have hF2 : ordAt Q (linX P2X) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf P2X Q h_bot hQX hQY
  have hF1 : ordAt Q (linX P1X) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf P1X Q h_bot (hQX ▸ hPP.symm)
  have h1_ne : toPair H ((linX RaX) ^ 2 * linX P2X) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hF2_ne
  have hstep1 : ordAt Q ((linX RaX) ^ 2 * linX P2X) (0 : k[X]) = 1 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX RaX) ^ 2 * linX P2X)
      ((linX RaX) ^ 2) (linX P2X) rfl hL_ne hF2_ne, hL, hF2]
    norm_num
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (((linX RaX) ^ 2 * linX P2X) * linX P1X)
    ((linX RaX) ^ 2 * linX P2X) (linX P1X) rfl h1_ne hF1_ne, hstep1, hF1]
  norm_num

end DecoupledSystem
end Genus2Lean
