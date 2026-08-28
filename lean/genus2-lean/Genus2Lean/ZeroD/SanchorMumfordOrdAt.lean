import Mathlib
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.LPairFinrankOneOrdAtFrac

/-! # `ordAt` at a Mumford-pair point, directly from `IsMumfordUa`/`IsMumfordTarget4`

**Closes the gap flagged in `ROADMAP-principal-witness-assembly.md`'s
latest pass note**: `reducedClass_eq_of_isReduction'`
(`AlphaLocusDegreeUniform.lean`) needs `ordAt Q (-va) 1 = 1` for
`Q ∈ Sanchor` (and the `u`/`v`/`S` mirror) to connect `hAlphaRep`'s
`divToPair (-va) 1 Sanchor` to `CAWitness.lean`'s `f`-construction at the
point-SET level (no polynomial identity `va = bCA` ever needed — only
that both divisors assign coefficient `1` to the same named points).
`CAWitnessResidual.lean` proves the analogous fact for `uCANew`/`bCA`
via a heavyweight 4-point-interpolation factorization
(`pairNormBCA_eq_denomPolyCA_mul_uCANew`); that machinery isn't needed
here — `ua`/`va` are already a standalone named Mumford pair (not
derived from any interpolation), so the direct route is:
`ordAt_eq_rootMultiplicity_unramified` (`LPairFinrankOneOrdAtFrac.lean`,
unconditional) applied to `c := pairNorm H (-va) 1 = va²-H.f`, composed
with `ua ∣ (va²-H.f)` (from `IsMumfordUa`, rewriting `H.f` via `hf`) and
`ua`'s squarefreeness forcing `rootMultiplicity = 1` at any of its
(simple, by squarefreeness) roots. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open Genus2Lean.TheDataDerivation

namespace Genus2Lean
namespace DecoupledSystem

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {H : HyperellipticPolynomial (Genus2Lean.TheDataDerivation.F p)}
  [IsDedekindDomain (CoordinateRing H)]

/-- **`ua` (as a Mumford `u`-polynomial) divides `pairNorm H (-va) 1`.**
Direct unfold: `pairNorm H (-va) 1 = va^2 - H.f`, and `IsMumfordUa` is
literally `ua ∣ (va^2 - curvePoly ...)`; `hf` rewrites `H.f` to
`curvePoly ...` to match. -/
theorem ua_dvd_pairNorm_negVa_one
    {c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : Genus2Lean.TheDataDerivation.F p}
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (va : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hva : va = (C va1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) * X + C va0) :
    (X ^ 2 + C ua1 * X + C ua0) ∣ pairNorm H (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) := by
  unfold pairNorm
  have : (-va) ^ 2 - (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) ^ 2 * H.f =
      va ^ 2 - curvePoly p c0 c1 c2 c3 c4 := by
    rw [hf]; ring
  rw [this, hva]
  exact hMumfordUa

/-- **`ordAt Q ua 0 = 1` at a genuine root `Q.X` of `ua`, unramified
(`Q.Y ≠ 0`).** Direct, unconditional application of
`ordAt_eq_rootMultiplicity_unramified` (`LPairFinrankOneOrdAtFrac.lean`)
to `c := ua` itself — `ua`'s `rootMultiplicity` at its own root `Q.X`
is exactly `1` by squarefreeness (`Polynomial.rootMultiplicity_eq_one_iff_isRoot_and_...`-
style fact, discharged here directly via `Squarefree.rootMultiplicity_le_one`
composed with `IsRoot → rootMultiplicity ≥ 1`, both from Mathlib's
`Polynomial.rootMultiplicity` API). -/
theorem ordAt_ua_eq_one_of_mem_Sanchor
    (hchar : (2 : Genus2Lean.TheDataDerivation.F p) ≠ 0)
    {ua0 ua1 : Genus2Lean.TheDataDerivation.F p}
    (huafree : Squarefree
      (X ^ 2 + C ua1 * X + C ua0 : Polynomial (Genus2Lean.TheDataDerivation.F p)))
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥)
    (hQua : (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).IsRoot Q.X)
    (hQY_ne : Q.Y ≠ 0) :
    ordAt Q (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) (0 : Polynomial (Genus2Lean.TheDataDerivation.F p)) = 1 := by
  have hua_ne : (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := huafree.ne_zero
  have hmult := ordAt_eq_rootMultiplicity_unramified hchar
    (X ^ 2 + C ua1 * X + C ua0) hua_ne Q.X Q h_bot rfl hQY_ne
  rw [hmult]
  have h1 : 1 ≤ (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).rootMultiplicity Q.X :=
    Polynomial.rootMultiplicity_pos hua_ne |>.mpr hQua
  have h2 : (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).rootMultiplicity Q.X ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨q, hq, -⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      (X ^ 2 + C ua1 * X + C ua0 : Polynomial (Genus2Lean.TheDataDerivation.F p)) hua_ne Q.X
    have hdvd : (X - C Q.X) ^ 2 ∣ (X ^ 2 + C ua1 * X + C ua0 :
        Polynomial (Genus2Lean.TheDataDerivation.F p)) :=
      (pow_dvd_pow (X - C Q.X) hlt).trans ⟨q, hq⟩
    have hnotunit : ¬ IsUnit (X - C Q.X :
        Polynomial (Genus2Lean.TheDataDerivation.F p)) := by
      intro hu
      obtain ⟨r, hr⟩ := Polynomial.isUnit_iff.mp hu
      have hdeg : (X - C Q.X : Polynomial (Genus2Lean.TheDataDerivation.F p)).natDegree = 0 := by
        rw [← hr.2]; simp
      rw [Polynomial.natDegree_X_sub_C] at hdeg
      exact one_ne_zero hdeg
    exact hnotunit (huafree (X - C Q.X) (by simpa [sq] using hdvd))
  norm_cast
  omega

/-- **The point-level payoff: `ordAt Q (-va) 1 = 1` for `Q` a genuine
root of `ua` with `Q.Y = va.eval Q.X` (unramified, `Q.Y ≠ 0`).** Direct
application of `ordAt_eq_one_of_old_point` (lemma 16,
`PrincipalWitness.lean`) with `E := -va`, `Y := 1`, `A := ua`, `U :=`
`pairNorm H (-va) 1 /ₘ ua`'s companion cofactor — supplied here via the
already-proved `hAU`/`ua_dvd_pairNorm_negVa_one` factorization and
`ordAt_ua_eq_one_of_mem_Sanchor` just above for `hA_ord`. -/
theorem ordAt_negVa_one_eq_one_of_mem_Sanchor
    (hchar : (2 : Genus2Lean.TheDataDerivation.F p) ≠ 0)
    {c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : Genus2Lean.TheDataDerivation.F p}
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (huafree : Squarefree
      (X ^ 2 + C ua1 * X + C ua0 : Polynomial (Genus2Lean.TheDataDerivation.F p)))
    (va : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hva : va = (C va1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) * X + C va0)
    (Uco : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) =
      (X ^ 2 + C ua1 * X + C ua0) * Uco)
    (hUco_ne : Uco ≠ 0)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥)
    (hQY : Q.Y = va.eval Q.X) (hQY_ne : Q.Y ≠ 0)
    (hQua : (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).IsRoot Q.X)
    (hUco_eval : Uco.eval Q.X ≠ 0) :
    ordAt Q (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) = 1 := by
  have hg_ne : toPair H (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hg_ne_eval : (-va).eval Q.X +
      (-(1 : Polynomial (Genus2Lean.TheDataDerivation.F p))).eval Q.X * Q.Y ≠ 0 := by
    simp only [Polynomial.eval_neg, Polynomial.eval_one]
    rw [hQY]
    intro hz
    apply hQY_ne
    rw [hQY]
    have h2 : (2 : Genus2Lean.TheDataDerivation.F p) * va.eval Q.X = 0 := by
      linear_combination -hz
    rcases mul_eq_zero.mp h2 with h2' | h2'
    · exact absurd h2' hchar
    · exact h2'
  have hua_ne : (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := huafree.ne_zero
  have hA_ne : toPair H (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) (0 : Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hua_ne hA0
  have hU_ne : toPair H Uco (0 : Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hU0, _⟩ => hUco_ne hU0
  have hA_ord := ordAt_ua_eq_one_of_mem_Sanchor (H := H) hchar huafree Q h_bot hQua hQY_ne
  exact ordAt_eq_one_of_old_point Q h_bot (-va) 1
    (X ^ 2 + C ua1 * X + C ua0) Uco hg_ne hg_ne_eval hAU hA_ne hU_ne hA_ord
    (by simpa using hUco_eval)

/-! ## Tangent branch (`P1 = P2`): `ordAt = 2` mirrors of the above

`ua` is NOT squarefree here — it's the caller-supplied double factor
`(X - C R) ^ 2` (`hua_eq`), replacing `huafree` entirely (they're
mutually exclusive: a genuinely repeated root contradicts
squarefreeness). Mirrors `OrdAtRootMultiplicityUnified.lean`'s
`rootMultiplicity_npoly4Lcm4_eq_two_of_R1_eq_R2` pattern one level down
(this file's own `ua`/`va`, not `npoly4Lcm4`). -/

/-- **`ordAt Q ua 0 = 2` when `ua = (X - C R) ^ 2` and `Q.X = R`.**
Direct: `Polynomial.rootMultiplicity_X_sub_C_pow` gives `rootMultiplicity
R ((X - C R)^2) = 2` unconditionally (no case split, unlike the
squarefree/`by_contra` route in the split-case lemma above), then
`ordAt_eq_rootMultiplicity_unramified` transports it to `ordAt`; a
final `norm_num` discharges the resulting `(↑(2:ℕ):ℤ) = 2` cast. -/
theorem ordAt_ua_eq_two_of_mem_Sanchor_tangent
    (hchar : (2 : Genus2Lean.TheDataDerivation.F p) ≠ 0)
    {R : Genus2Lean.TheDataDerivation.F p}
    (hua_eq : (X ^ 2 + C (-2 * R) * X + C (R * R) :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) =
      (X - C R) ^ 2)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥)
    (hQX : Q.X = R) (hQY_ne : Q.Y ≠ 0) :
    ordAt Q (X ^ 2 + C (-2 * R) * X + C (R * R) :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) (0 : Polynomial (Genus2Lean.TheDataDerivation.F p)) = 2 := by
  have hua_ne : (X ^ 2 + C (-2 * R) * X + C (R * R) :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [hua_eq]
    exact ((Polynomial.monic_X_sub_C R).pow 2).ne_zero
  have hmult := ordAt_eq_rootMultiplicity_unramified hchar
    (X ^ 2 + C (-2 * R) * X + C (R * R)) hua_ne R Q h_bot hQX hQY_ne
  rw [hmult, hua_eq, Polynomial.rootMultiplicity_X_sub_C_pow]
  norm_num

/-- **The point-level payoff, tangent branch: `ordAt Q (-va) 1 = 2`.**
Mirrors `ordAt_negVa_one_eq_one_of_mem_Sanchor`, swapping in
`ordAt_eq_two_of_old_point` (lemma 16's `= 2` mirror,
`PrincipalWitness.lean`) and `ordAt_ua_eq_two_of_mem_Sanchor_tangent`
just above for `hA_ord`. `va`'s shape is unchanged from the split case
(`hva`); only `ua`'s factorization (`hua_eq`, double root, no
`huafree`) and the target multiplicity (`2`, not `1`) differ. -/
theorem ordAt_negVa_one_eq_two_of_mem_Sanchor_tangent
    (hchar : (2 : Genus2Lean.TheDataDerivation.F p) ≠ 0)
    {R va0 va1 : Genus2Lean.TheDataDerivation.F p}
    (hua_eq : (X ^ 2 + C (-2 * R) * X + C (R * R) :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) =
      (X - C R) ^ 2)
    (va : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (_hva : va = (C va1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) * X + C va0)
    (Uco : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) =
      (X ^ 2 + C (-2 * R) * X + C (R * R)) * Uco)
    (hUco_ne : Uco ≠ 0)
    (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥)
    (hQY : Q.Y = va.eval Q.X) (hQY_ne : Q.Y ≠ 0)
    (hQX : Q.X = R)
    (hUco_eval : Uco.eval Q.X ≠ 0) :
    ordAt Q (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) = 2 := by
  have hg_ne : toPair H (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hg_ne_eval : (-va).eval Q.X +
      (-(1 : Polynomial (Genus2Lean.TheDataDerivation.F p))).eval Q.X * Q.Y ≠ 0 := by
    simp only [Polynomial.eval_neg, Polynomial.eval_one]
    rw [hQY]
    intro hz
    apply hQY_ne
    rw [hQY]
    have h2 : (2 : Genus2Lean.TheDataDerivation.F p) * va.eval Q.X = 0 := by
      linear_combination -hz
    rcases mul_eq_zero.mp h2 with h2' | h2'
    · exact absurd h2' hchar
    · exact h2'
  have hua_ne : (X ^ 2 + C (-2 * R) * X + C (R * R) :
      Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [hua_eq]
    exact ((Polynomial.monic_X_sub_C R).pow 2).ne_zero
  have hA_ne : toPair H (X ^ 2 + C (-2 * R) * X + C (R * R) :
      Polynomial (Genus2Lean.TheDataDerivation.F p))
      (0 : Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hua_ne hA0
  have hU_ne : toPair H Uco (0 : Polynomial (Genus2Lean.TheDataDerivation.F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hU0, _⟩ => hUco_ne hU0
  have hA_ord := ordAt_ua_eq_two_of_mem_Sanchor_tangent (H := H) hchar hua_eq Q h_bot hQX hQY_ne
  exact ordAt_eq_two_of_old_point Q h_bot (-va) 1
    (X ^ 2 + C (-2 * R) * X + C (R * R)) Uco hg_ne hg_ne_eval hAU hA_ne hU_ne hA_ord
    (by simpa using hUco_eval)

end DecoupledSystem
end Genus2Lean
