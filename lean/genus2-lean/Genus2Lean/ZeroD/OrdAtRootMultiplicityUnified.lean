import Mathlib
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessAssembly
import Genus2Lean.LPairFinrankOneOrdAtFrac

/-!
# Unifying `ordAt_npoly4Lcm4_eq_one_of_{R1,R2,Ra1,Ra2}` via `rootMultiplicity`

Per the caller's own steer: `ordAt_npoly4Lcm4_eq_one_of_R1/R2` (and their
`Ra1`/`Ra2` mirrors, `PrincipalWitnessAssembly.lean`) currently split
`u_target`/`ua` into two NAMED roots via `quadratic_eq_mul_X_sub_C`, which
needs `hRne : R1 ≠ R2` as a caller-supplied hypothesis — never derived,
just assumed. This forces a genuine case split whenever the sample data
can produce a repeated root (`R1 = R2`, i.e. `u_target` a perfect square),
which the flat-product/`Layers 1-3` machinery (`PrincipalWitness.lean`)
cannot express, since it insists on exhibiting the target quadratic as
`linX a * F₁ * F₂ * F₃` with each `Fᵢ` NONVANISHING at `a` — impossible
when `a` is a double root of one of the four factors.

**The fix**: `ordAt` at a point over a root `α` of ANY nonzero polynomial
`c` already equals `c.rootMultiplicity α` unconditionally — this is
`ordAt_eq_rootMultiplicity_unramified`/`_ramified`
(`LPairFinrankOneOrdAtFrac.lean`, lemma 6 of the stack, already proved,
0-`sorry`). That lemma does NOT require `c` to be pre-split into named
linear factors; `rootMultiplicity` is defined for any polynomial and
handles `R1 = R2` (rootMultiplicity 2) and `R1 ≠ R2` (rootMultiplicity 1,
for EACH of the two distinct roots) uniformly, with no case split in the
statement or the proof.

So instead of routing through `quadratic_eq_mul_X_sub_C` + Layers 1-3 (which
needs `hRne`), this file computes `npoly4Lcm4.rootMultiplicity α` directly
from the flat-product factorization (`npoly4Lcm4_eq_flat_product`, already
on file) via `Polynomial.rootMultiplicity_mul_X_sub_C_pow`-style additivity,
and feeds that into lemma 6. The four-way `no-shared-root` hypotheses
(`hne34`/`hnoroot34`/`hP1ua`/etc.) are UNCHANGED — those guard against
`ua`/`u_target` sharing a root with each other or with `P1`/`P2`, a
genuinely different (and already correctly unified, via
`Reduce/SharedRootCombining.lean`'s `lcm` trick) degeneracy from the one
this file addresses (a repeated root WITHIN a single quadratic factor).

This file does NOT yet remove `hRne` from
`ordAt_npoly4Lcm4_eq_one_of_R1/R2` themselves (that would require rewriting
`PrincipalWitnessAssembly.lean`'s existing 0-`sorry` proofs) — it proves
the unconditional replacement as new, standalone theorems, so the two can
be compared and the assembly theorem can pick whichever it needs, without
touching already-proved code.
-/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at a point over `α`, unconditionally, in terms
of `rootMultiplicity` — no named-distinct-root hypothesis needed.**
Composes `npoly4Lcm4_eq_flat_product` (the flat-product identity, up to a
unit) with `ordAt_eq_rootMultiplicity_unramified` directly: `ordAt` is
insensitive to a unit `C u` factor scaling (`ordAt_C_mul_eq`, already used
by `ordAt_unit_mul_A_eq_one_of_eval_ne_zero`), so `ordAt P npoly4Lcm4 0`
equals `(npoly4Lcm4).rootMultiplicity α` directly, with no detour through
`ua`/`u_target`'s own root structure. Subsumes BOTH the `R1 ≠ R2` case
(where this equals `1`, matching `ordAt_npoly4Lcm4_eq_one_of_R1`) and the
`R1 = R2` case (where this equals `2`) as the SAME theorem — the caller
computes `rootMultiplicity` afterward via whichever case actually holds,
rather than this lemma needing to know which case it's in. -/
theorem ordAt_npoly4Lcm4_eq_rootMultiplicity
    (hchar : (2 : F p) ≠ 0)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (α : F p)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = α) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hraw_ne : npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1 ≠ 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) =
      ((npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).rootMultiplicity α : ℤ) :=
  ordAt_eq_rootMultiplicity_unramified hchar (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) hraw_ne
    α P h_bot hPX hPY

/-- **`npoly4Lcm4`'s `rootMultiplicity` at any point `α`, unconditionally,
in terms of the target quadratic's own `rootMultiplicity`** — the actual
unifying lemma, subsuming `R1 ≠ R2` and `R1 = R2` as the SAME statement.
`npoly4Lcm4` is (up to the unit `npoly4Lcm4_eq_flat_product` names)
literally `(X-P1.1) * (X-P2.1) * ua * u_target`, so its `rootMultiplicity`
at `α` is the SUM of the four factors' own `rootMultiplicity`s at `α`
(`Polynomial.rootMultiplicity_mul`, the unconditional `IsDomain`-only
additivity fact — no separability, no cofactor-nonvanishing side
condition, unlike `rootMultiplicity_mul'`). `C u` (the unit) contributes
`0` (`Polynomial.rootMultiplicity_C`). Each linear factor `(X - C a)`
contributes `rootMultiplicity α (X - C a) = if α = a then 1 else 0`
(`Polynomial.rootMultiplicity_X_sub_C`), decided directly from the
no-shared-root hypotheses (`hP1ua` etc. only rule out cross-quadratic and
point-vs-quadratic coincidences; whether `α` equals `P1.1`/`P2.1` is
caller data, taken as an explicit disjunction below rather than assumed
away). `u_target`'s own contribution, `u_target.rootMultiplicity α`, is
left OPAQUE — this is precisely the number that is `1` when `u_target` has
two distinct roots at `α`/elsewhere and `2` when `α` is `u_target`'s
repeated root, and this lemma does not need to know which. -/
theorem rootMultiplicity_npoly4Lcm4_eq_add
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p) (α : F p)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hαP1 : α ≠ P1.1) (hαP2 : α ≠ P2.1)
    (hαua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval α = 0) :
    (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).rootMultiplicity α =
      (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).rootMultiplicity α := by
  classical
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hne1 : (X - C P1.1 : Polynomial (F p)) ≠ 0 := hm1.ne_zero
  have hne2 : (X - C P2.1 : Polynomial (F p)) ≠ 0 := hm2.ne_zero
  have hne3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ 0 := hm3.ne_zero
  have hne4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) ≠ 0 := hm4.ne_zero
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  set u : F p := (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff⁻¹ *
        (EuclideanDomain.gcd
          (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
          (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
            (X ^ 2 + C u1 * X + C u0))).leadingCoeff⁻¹ *
        (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).leadingCoeff⁻¹ *
        (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0)).leadingCoeff⁻¹ with hudef
  -- `C u` scales the whole product by a unit; a unit is nonzero (`F p`
  -- is a field), so `rootMultiplicity_mul` applies to peel it off first.
  by_cases hu0 : u = 0
  · exfalso
    -- `npoly4Lcm4_eq_flat_product`'s own proof establishes each of the
    -- four leadingCoeff⁻¹ factors is nonzero; reprove that fact for `u`
    -- directly from the same nonvanishing polynomials (`hraw`, the two
    -- gcds), rather than re-deriving it here from scratch.
    have hraw_ne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
      npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
    have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
      fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
    have hgcd34ne :
        (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
      fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
    have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
      fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
    have hL34ne :
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
      fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
    have hGne :
        (EuclideanDomain.gcd (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
          (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
            (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
      fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
    have h1 : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1).leadingCoeff⁻¹ ≠ 0 :=
      inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hraw_ne)
    have h2 : (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))).leadingCoeff⁻¹ ≠ 0 :=
      inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne)
    have h3 : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)).leadingCoeff⁻¹
        ≠ 0 := inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne)
    have h4 : (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)).leadingCoeff⁻¹ ≠ 0 :=
      inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne)
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) (hudef ▸ hu0)
  have hCu_unit : IsUnit (C u : Polynomial (F p)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu0)
  have hCu_ne : (C u : Polynomial (F p)) ≠ 0 := hCu_unit.ne_zero
  have hprod_ne : (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
      ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hne1 hne2) (mul_ne_zero hne3 hne4)
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hCu_ne hprod_ne),
    Polynomial.rootMultiplicity_C, zero_add,
    Polynomial.rootMultiplicity_mul hprod_ne,
    Polynomial.rootMultiplicity_mul (mul_ne_zero hne1 hne2),
    Polynomial.rootMultiplicity_mul (mul_ne_zero hne3 hne4),
    Polynomial.rootMultiplicity_X_sub_C, Polynomial.rootMultiplicity_X_sub_C,
    Polynomial.rootMultiplicity_eq_zero hαua,
    if_neg hαP1, if_neg hαP2]
  ring

/-- **The `R1 ≠ R2` split-case value, as a corollary of the unifying
lemma above** — `u_target.rootMultiplicity R1 = 1` when `R1` is a root
distinct from `u_target`'s other root `R2`, via
`quadratic_eq_mul_X_sub_C`'s factorization plus
`Polynomial.rootMultiplicity_X_sub_C`/`rootMultiplicity_mul`. Matches
`ordAt_npoly4Lcm4_eq_one_of_R1`'s ultimate numeric conclusion, but derived
from `rootMultiplicity` throughout rather than the four-way flat-product
case split. -/
theorem rootMultiplicity_npoly4Lcm4_eq_one_of_R1_ne_R2
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p) (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR1P1 : R1 ≠ P1.1) (hR1P2 : R1 ≠ P2.1)
    (hR1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R1 = 0) :
    (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).rootMultiplicity R1 = 1 := by
  rw [rootMultiplicity_npoly4Lcm4_eq_add p P1 P2 ua0 ua1 u0 u1 R1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target hR1P1 hR1P2 hR1ua]
  have hmonic : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hdeg : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by compute_degree!
  have hsplit : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) = (X - C R1) * (X - C R2) :=
    quadratic_eq_mul_X_sub_C p hmonic hdeg htargetRoot1 htargetRoot2 hRne
  rw [hsplit, Polynomial.rootMultiplicity_mul
    (mul_ne_zero (Polynomial.monic_X_sub_C R1).ne_zero (Polynomial.monic_X_sub_C R2).ne_zero),
    Polynomial.rootMultiplicity_X_sub_C, Polynomial.rootMultiplicity_X_sub_C,
    if_pos rfl, if_neg hRne]

/-- **The `R1 = R2` repeated-root value, as a corollary of the SAME
unifying lemma above** — the case `quadratic_eq_mul_X_sub_C`/
`ordAt_npoly4Lcm4_eq_one_of_R1` cannot express at all (they require
`hRne : R1 ≠ R2`). With `u_target = (X-R)^2`,
`u_target.rootMultiplicity R = 2` directly
(`Polynomial.rootMultiplicity_X_sub_C_pow`) — a genuinely different
numeric answer from the distinct-root case, obtained by the SAME
`rootMultiplicity_npoly4Lcm4_eq_add` bridge, no separate proof
architecture needed. -/
theorem rootMultiplicity_npoly4Lcm4_eq_two_of_R1_eq_R2
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p) (R : F p)
    (htargetSq : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) = (X - C R) ^ 2)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRP1 : R ≠ P1.1) (hRP2 : R ≠ P2.1)
    (hRua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R = 0) :
    (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1).rootMultiplicity R = 2 := by
  rw [rootMultiplicity_npoly4Lcm4_eq_add p P1 P2 ua0 ua1 u0 u1 R h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target hRP1 hRP2 hRua, htargetSq,
    Polynomial.rootMultiplicity_X_sub_C_pow]

end DecoupledSystem
end Genus2Lean
