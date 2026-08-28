import Mathlib
import Genus2Lean.ZeroD.CAWitness
import Genus2Lean.ZeroD.CAWitnessDivisor
import Genus2Lean.ZeroD.CAWitnessResidual
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.PrincipalWitnessStep3
import Genus2Lean.HyperellipticClassProof
import Genus2Lean.PrincipalDivisorSubgroup

/-! # `ROADMAP-principal-witness-assembly.md` step 3: `principalSubgroup`
membership

**Sign correction this pass (see `CAWitness.lean`'s module docstring and
`ROADMAP-principal-witness-assembly.md`'s corrected step 3): the target
is `C - A - ι(T) + 2•[δ₀]`, NOT the earlier (wrong) `C - A - T +
2•[δ₀]`.**

Starting point: `PrincipalWitnessStep3.lean`'s
`divToPair_eq_C_add_iotaA_add_T_of_split`, a literal `Divisor H` equality
`div_aff(f) = C + ι(A) + T` over the six named points
`{PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2}`. This file turns that into a
`principalSubgroup` membership via one matching-`ordInfOfPair`-`(-6)`
ratio generator, `f` against `h_A := linX(P1.X) * linX(P2.X) *
linX(δ₀.X)`.

**Plan, three pieces (`Part 1`/`Part 2`/`Part 3` below):**
1. `div(h_A) = A + ι(A) + 2•[δ₀]` (`divToPair_hA_eq`) — an
   `eq_of_coeffAt_eq`/six-way-`by_cases` computation, same idiom as
   `PrincipalWitnessStep3.lean`'s own six-point assembly and
   `CAWitnessDivisor.lean`'s four-point one, here for a plain
   product-of-three-`linX` divisor instead of the Cantor interpolant.
   Built on top of `ordAt_linX_mul3_eq_one_of_ne`/
   `ordAt_linX_mul3_eq_zero_of_notMem`, the 3-factor analogues of
   `PrincipalWitness.lean`'s existing `ordAt_mul4_...` composition
   lemmas (themselves built from `ordAt_mul_eq_one_of_ordAt_eq_one_zero`
   iterated).
2. `div(f) - div(h_A) = C - A + T - 2•[δ₀]` (the ratio generator itself,
   `ordInfOfPair(f) = ordInfOfPair(h_A) = -6`), hence
   `C - A + T - 2•[δ₀] ∈ principalSubgroup` (`cAmT_mem_principalSubgroup`).
3. Restate as `C - A - ι(T) + 2•[δ₀] ∈ principalSubgroup`
   (`cAmIotaT_mem_principalSubgroup`, the shape
   `AlphaLocusDegreeUniform.lean`'s goal actually needs, matching
   `S := ι(T)`), using the separately-principal fact
   `T + ι(T) - 4•[δ₀] ∈ principalSubgroup` (two single-`linX`
   generators, mirroring `HyperellipticClassProof.lean`'s
   `hyperellipticClass_principalDivisorData` pattern).

**All three `hspec`/`Module.Finite` Nullstellensatz-style side
conditions `principalSubgroup`'s own generating-set membership demands
(per `PrincipalDivisorSubgroup.lean`) are threaded through as extra
hypotheses, matching every other file in this stack that reaches
`principalSubgroup` directly (`HyperellipticClassProof.lean`'s
`hyperellipticClass_principalDivisorData`) — none of them are discharged
anywhere in this codebase yet.** -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-! ## Part 1: `div(h_A) = A + ι(A) + 2•[δ₀]` for
`h_A := (x-P1.X)(x-P2.X)(x-δ₀.X)` -/

/-- **`ordAt` of a triple product `(linX a * linX b) * linX c` is `1` at
a point `Q` with `Q.X = a`, `Q.Y ≠ 0`, given `b ≠ a` and `c ≠ a`.**
3-factor iteration of `ordAt_mul_eq_one_of_ordAt_eq_one_zero`
(`PrincipalWitness.lean`), the same composition
`ordAt_mul4_eq_one_of_ordAt_eq_one_zero_zero_zero` already does for four
factors — the designated (order-1) factor is always the leftmost of the
three, matching that lemma's own "no extra `mul_assoc` bookkeeping
beyond re-bracketing" convention. -/
theorem ordAt_linX_mul3_eq_one_of_ne
    [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (a b c : k)
    (hQX : Q.X = a) (hQY : Q.Y ≠ 0) (hbne : b ≠ a) (hcne : c ≠ a) :
    ordAt Q ((linX a * linX b) * linX c) (0 : k[X]) = 1 := by
  have hne : ∀ x : k, toPair H (linX x) (0 : k[X]) ≠ 0 := fun x => by
    rw [Ne, toPair_eq_zero_iff]; exact fun ⟨hA, _⟩ => linX_ne_zero x hA
  have hLa : ordAt Q (linX a) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf a Q h_bot hQX hQY
  have hQb : Q.X ≠ b := by rw [hQX]; exact Ne.symm hbne
  have hQc : Q.X ≠ c := by rw [hQX]; exact Ne.symm hcne
  have hLb : ordAt Q (linX b) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf b Q h_bot hQb
  have hLc : ordAt Q (linX c) (0 : k[X]) = 0 :=
    ordAt_linX_eq_zero_of_ne' hchar hsf c Q h_bot hQc
  have hab : ordAt Q (linX a * linX b) (0 : k[X]) = 1 :=
    ordAt_mul_eq_one_of_ordAt_eq_one_zero Q h_bot (linX a) (linX b)
      (hne a) (hne b) hLa hLb
  have hab_ne : toPair H (linX a * linX b) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']; exact mul_ne_zero (hne a) (hne b)
  -- Compose the two-factor case once more (`(linX a * linX b) * linX c`).
  exact ordAt_mul_eq_one_of_ordAt_eq_one_zero Q h_bot (linX a * linX b) (linX c)
    hab_ne (hne c) hab hLc

/-- **The companion `= 0` fact: away from `{Q : Q.X ∈ {a,b,c}}`,
`ordAt Q ((linX a * linX b) * linX c) 0 = 0`.** Each factor individually
has `ordAt = 0` (`ordAt_linX_eq_zero_of_ne'`), and `ordAt` of a product
of three each-`0`-order factors is `0` (two applications of
`ordAt_mul_eq_one_of_ordAt_eq_one_zero`'s underlying additivity fact,
`ordAt_add_of_pairNorm_eq_mul`, rather than that lemma's `=1` conclusion
— used here directly at the `0+0=0`/`0+0+0=0` level). -/
theorem ordAt_linX_mul3_eq_zero_of_notMem
    [DecidableEq k]
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (a b c : k)
    (hQa : Q.X ≠ a) (hQb : Q.X ≠ b) (hQc : Q.X ≠ c) :
    ordAt Q ((linX a * linX b) * linX c) (0 : k[X]) = 0 := by
  have hne : ∀ x : k, toPair H (linX x) (0 : k[X]) ≠ 0 := fun x => by
    rw [Ne, toPair_eq_zero_iff]; exact fun ⟨hA, _⟩ => linX_ne_zero x hA
  have h0a : ordAt Q (linX a) (0 : k[X]) = 0 := ordAt_eq_zero_of_eval_ne_zero Q (linX a) 0 (by
    simp only [Polynomial.eval_zero, mul_zero, add_zero]
    unfold linX; simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr hQa)
  have h0b : ordAt Q (linX b) (0 : k[X]) = 0 := ordAt_eq_zero_of_eval_ne_zero Q (linX b) 0 (by
    simp only [Polynomial.eval_zero, mul_zero, add_zero]
    unfold linX; simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr hQb)
  have h0c : ordAt Q (linX c) (0 : k[X]) = 0 := ordAt_eq_zero_of_eval_ne_zero Q (linX c) 0 (by
    simp only [Polynomial.eval_zero, mul_zero, add_zero]
    unfold linX; simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr hQc)
  have hab_ne : toPair H (linX a * linX b) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']; exact mul_ne_zero (hne a) (hne b)
  have hab : ordAt Q (linX a * linX b) (0 : k[X]) = 0 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX a * linX b) (linX a) (linX b) rfl (hne a) (hne b),
      h0a, h0b]
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX a * linX b) * linX c) (linX a * linX b) (linX c) rfl
    hab_ne (hne c), hab, h0c]

end DecoupledSystem
end Genus2Lean
