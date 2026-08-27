import Mathlib
import Genus2Lean.ZeroD.CAWitness
import Genus2Lean.ZeroD.PrincipalWitness

/-!
# Divisor-level fact for `CAWitness.lean`'s `f := y - bCA(x)`

`CAWitness.lean` builds `bCA` (the degree-≤3 interpolant through `Ra1,
Ra2, ι(P1), ι(P2)`) and its residual factorization `H.f - bCA² =
denomPolyCA * uCANew`, entirely at the bare-polynomial level (`eval`,
`dvd`, `%ₘ`) — no `H.Point`/`Divisor H`/`ordAt` content yet. This file
supplies that missing layer, the single-witness analogue of
`PrincipalWitnessStep1.lean`'s `divToPair_eq_A_add_C_add_T_of_split` (for
`g := E+Y·y`) but for `f := toPair H (-bCA) 1` (`E := -bCA`, `Y := 1`,
i.e. `y - bCA(x)`).

**Recipe: `ordAt_eq_one_of_old_point` (`PrincipalWitness.lean`, lemma 16),**
applied at each of the four named points, with `A := denomPolyCA` and
`U := -uCANew` (the sign absorbed into `U`, not `A`, so `A`'s existing
`Layer 3`-style eval facts — `denomPolyCA`'s four linear factors — apply
unchanged; `ordAt`/`toPair`-nonvanishing facts are sign-invariant in `U`,
so this costs nothing). The key identity:

    pairNorm H (-bCA) 1 = bCA² - H.f = -(H.f - bCA²)
                         = -(denomPolyCA * uCANew) = denomPolyCA * (-uCANew)

`ordAt_eq_one_of_old_point`'s own hypotheses, instantiated:
- `hg_ne : toPair H (-bCA) 1 ≠ 0` — immediate, `toPair H (-bCA) 1`'s
  `B`-slot is `1 ≠ 0`, so `toPair_eq_zero_iff` rules out `= 0` outright.
- `hg_ne_eval : (-bCA).eval P.X + (-1).eval P.X * P.Y ≠ 0` — this is
  `f̄(P) = -bCA(P.X) - P.Y ≠ 0`, i.e. `bCA(P.X) ≠ -P.Y`. At each of the
  four named points `bCA` was built to satisfy `bCA(pt) = pt.Y` (ordinary
  points) or `= -P_i.Y` (the `ι`-substituted `P1,P2` rows) — the OTHER
  sheet's value, not this one — so this is nonzero given the named
  points aren't Weierstrass (`.Y ≠ 0`) and (for the `ιP1,ιP2` rows) that
  `bCA`'s own defining value `-P_iY` isn't itself `= -(- P_iY) = P_iY`,
  i.e. `P_iY ≠ -P_iY`, i.e. `2·P_iY ≠ 0` — needs `hchar`.
- `hAU`, `hA_ne`, `hU_ne`: as above.
- `hA_ord : ordAt P denomPolyCA 0 = 1` — `Layer 3`
  (`ordAt_A_eq_one_of_eval_ne_zero`), from the other three factors'
  plain-evaluation nonvanishing at the point in question (pairwise
  distinctness of the four x-coordinates).
- `hU_eval : (-uCANew).eval P.X ≠ 0` — supplied by the caller (mirrors
  `PrincipalWitnessAssembly.lean`'s own `hU_evalP1`-style hypotheses for
  `uRS4General`; nothing in this file's own machinery pins this down, it
  depends on `uCANew`'s actual roots being disjoint from the four named
  points, which is a genuine extra fact about the specific curve/point
  data, not derivable from `bCA`'s construction alone).

**Scoped to the fully-split case only** (all four x-coordinates pairwise
distinct) — matching `caInterpMatrix_det_ne_zero`'s own hypothesis list
and `PrincipalWitnessStep1.lean`'s own scoping precedent; repeated-root
branches (e.g. `Ra1 = Ra2`) are not attempted here.
-/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`f`'s divisor restricted to the four named points equals their
sum**, fully-split case. `f := toPair H (-bCA) 1`, i.e. `y - bCA(x)`;
`PtRa1, PtRa2` are `ua`'s roots (`C`), `PtιP1, PtιP2` are the
hyperelliptic conjugates of the two "old" points `P1, P2` (`ι(A)`) — per
`CAWitness.lean`'s own module docstring, this is `div_aff(f) = C + ι(A) +
T` restricted to the four named (non-residual) points, `T := uCANew`'s
root pair entering only implicitly via `hU_eval` here (its own points are
not part of this four-point statement — they get their own, separate
`ordAt = ±1` fact via `uCANew`'s residual bookkeeping, not attempted in
this file). -/
theorem divToPair_eq_C_add_iotaA_of_split
    [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa2 PtιP1 PtιP2 : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hU_evalRa1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra1X ≠ 0)
    (hU_evalRa2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P2X ≠ 0) :
    divToPair (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
        ({PtRa1, PtRa2, PtιP1, PtιP2} : Finset H.Point) =
      single PtRa1 + single PtRa2 + single PtιP1 + single PtιP2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  -- `f ≠ 0` as a ring element: its `B`-slot is `1 ≠ 0`.
  have hg_ne : toPair H (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  -- The shared `hAU` identity, common to all four points.
  have hAU : pairNorm H (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) =
      denomPolyCA Ra1X Ra2X P1X P2X *
        (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) := by
    unfold pairNorm
    have hfact := pairNormBCA_eq_denomPolyCA_mul_uCANew H Ra1X Ra2X P1X P2X
      Ra1Y Ra2Y P1Y P2Y hdet h12 h1P1 h1P2 h2P1 h2P2 hPP
      hRa1_curve hRa2_curve hP1_curve hP2_curve
    have : (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) := by ring
    rw [neg_sq, this, hfact]
    ring
  have hdenom_ne : denomPolyCA Ra1X Ra2X P1X P2X ≠ 0 := by
    unfold denomPolyCA
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (X_sub_C_ne_zero Ra1X) (X_sub_C_ne_zero Ra2X)) (X_sub_C_ne_zero P1X))
      (X_sub_C_ne_zero P2X)
  have hA_ne : toPair H (denomPolyCA Ra1X Ra2X P1X P2X) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hdenom_ne hA
  have hU_ne : toPair H (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hA, -⟩
    have : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra1X = 0 := by
      rw [neg_eq_zero] at hA; rw [hA]; simp
    exact hU_evalRa1 this
  -- The four pointwise `ordAt = 1` facts, via `ordAt_eq_one_of_old_point`
  -- + `Layer 3` (`ordAt_A_eq_one_of_eval_ne_zero`) for `hA_ord`.
  have hOrdRa1 : ordAt PtRa1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtRa1 (h_bot PtRa1) _ _
      (denomPolyCA Ra1X Ra2X P1X P2X) (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · -- `hg_ne_eval : f̄(PtRa1) ≠ 0`, i.e. `-bCA.eval Ra1X - Ra1Y ≠ 0`.
      show (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtRa1.X +
          (-(1 : k[X])).eval PtRa1.X * PtRa1.Y ≠ 0
      simp only [hPtRa1X, hPtRa1Y, eval_neg, eval_one]
      rw [bCA_eval_Ra1 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet]
      intro hcontra
      apply hRa1Y_ne
      have h2R : (2 : k) * Ra1Y = 0 := by
        have : -Ra1Y + (-1 : k) * Ra1Y = -(2 * Ra1Y) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · -- `hA_ord : ordAt PtRa1 denomPolyCA 0 = 1`, via Layer 3.
      have hL3 := ordAt_A_eq_one_of_eval_ne_zero (H := H) hchar hsf PtRa1 (h_bot PtRa1)
        Ra1X hPtRa1X (hPtRa1Y ▸ hRa1Y_ne)
        (linX Ra2X) (linX P1X) (linX P2X)
        (by unfold linX; simpa using (sub_ne_zero.mpr h12))
        (by unfold linX; simpa using (sub_ne_zero.mpr h1P1))
        (by unfold linX; simpa using (sub_ne_zero.mpr h1P2))
      have heq : denomPolyCA Ra1X Ra2X P1X P2X =
          ((linX Ra1X * linX Ra2X) * linX P1X) * linX P2X := by
        unfold denomPolyCA linX; ring
      rw [heq]
      exact hL3
    · -- `hU_eval : (-uCANew).eval PtRa1.X ≠ 0`.
      simp only [hPtRa1X, eval_neg]
      simpa using hU_evalRa1
  have hOrdRa2 : ordAt PtRa2 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtRa2 (h_bot PtRa2) _ _
      (denomPolyCA Ra1X Ra2X P1X P2X) (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtRa2.X +
          (-(1 : k[X])).eval PtRa2.X * PtRa2.Y ≠ 0
      simp only [hPtRa2X, hPtRa2Y, eval_neg, eval_one]
      rw [bCA_eval_Ra2 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet]
      intro hcontra
      apply hRa2Y_ne
      have h2R : (2 : k) * Ra2Y = 0 := by
        have : -Ra2Y + (-1 : k) * Ra2Y = -(2 * Ra2Y) := by ring
        rw [this] at hcontra
        exact neg_eq_zero.mp hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · have hL3 := ordAt_A_eq_one_of_eval_ne_zero (H := H) hchar hsf PtRa2 (h_bot PtRa2)
        Ra2X hPtRa2X (hPtRa2Y ▸ hRa2Y_ne)
        (linX Ra1X) (linX P1X) (linX P2X)
        (by unfold linX; simpa using (sub_ne_zero.mpr (Ne.symm h12)))
        (by unfold linX; simpa using (sub_ne_zero.mpr h2P1))
        (by unfold linX; simpa using (sub_ne_zero.mpr h2P2))
      have heq : denomPolyCA Ra1X Ra2X P1X P2X =
          ((linX Ra2X * linX Ra1X) * linX P1X) * linX P2X := by
        unfold denomPolyCA linX; ring
      rw [heq]
      exact hL3
    · simp only [hPtRa2X, eval_neg]
      simpa using hU_evalRa2
  have hOrdιP1 : ordAt PtιP1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP1 (h_bot PtιP1) _ _
      (denomPolyCA Ra1X Ra2X P1X P2X) (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · -- `f̄(PtιP1) ≠ 0`: `-bCA.eval P1X - (-P1Y) = -bCA.eval P1X + P1Y ≠ 0`.
      show (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtιP1.X +
          (-(1 : k[X])).eval PtιP1.X * PtιP1.Y ≠ 0
      simp only [hPtιP1X, hPtιP1Y, eval_neg, eval_one]
      rw [bCA_eval_P1 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet]
      intro hcontra
      apply hP1Y_ne
      have h2R : (2 : k) * P1Y = 0 := by
        have : -(-P1Y) + (-1 : k) * (-P1Y) = 2 * P1Y := by ring
        rw [this] at hcontra
        exact hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · have hL3 := ordAt_A_eq_one_of_eval_ne_zero (H := H) hchar hsf PtιP1 (h_bot PtιP1)
        P1X hPtιP1X (by rw [hPtιP1Y]; exact neg_ne_zero.mpr hP1Y_ne)
        (linX Ra1X) (linX Ra2X) (linX P2X)
        (by unfold linX; simpa using (sub_ne_zero.mpr (Ne.symm h1P1)))
        (by unfold linX; simpa using (sub_ne_zero.mpr (Ne.symm h2P1)))
        (by unfold linX; simpa using (sub_ne_zero.mpr hPP))
      have heq : denomPolyCA Ra1X Ra2X P1X P2X =
          ((linX P1X * linX Ra1X) * linX Ra2X) * linX P2X := by
        unfold denomPolyCA linX; ring
      rw [heq]
      exact hL3
    · simp only [hPtιP1X, eval_neg]
      simpa using hU_evalP1
  have hOrdιP2 : ordAt PtιP2 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP2 (h_bot PtιP2) _ _
      (denomPolyCA Ra1X Ra2X P1X P2X) (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtιP2.X +
          (-(1 : k[X])).eval PtιP2.X * PtιP2.Y ≠ 0
      simp only [hPtιP2X, hPtιP2Y, eval_neg, eval_one]
      rw [bCA_eval_P2 Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet]
      intro hcontra
      apply hP2Y_ne
      have h2R : (2 : k) * P2Y = 0 := by
        have : -(-P2Y) + (-1 : k) * (-P2Y) = 2 * P2Y := by ring
        rw [this] at hcontra
        exact hcontra
      rcases mul_eq_zero.mp h2R with h | h
      · exact absurd h hchar
      · exact h
    · have hL3 := ordAt_A_eq_one_of_eval_ne_zero (H := H) hchar hsf PtιP2 (h_bot PtιP2)
        P2X hPtιP2X (by rw [hPtιP2Y]; exact neg_ne_zero.mpr hP2Y_ne)
        (linX Ra1X) (linX Ra2X) (linX P1X)
        (by unfold linX; simpa using (sub_ne_zero.mpr (Ne.symm h1P2)))
        (by unfold linX; simpa using (sub_ne_zero.mpr (Ne.symm h2P2)))
        (by unfold linX; simpa using (sub_ne_zero.mpr (Ne.symm hPP)))
      have heq : denomPolyCA Ra1X Ra2X P1X P2X =
          ((linX P2X * linX Ra1X) * linX Ra2X) * linX P1X := by
        unfold denomPolyCA linX; ring
      rw [heq]
      exact hL3
    · simp only [hPtιP2X, eval_neg]
      simpa using hU_evalP2
  -- Pairwise distinctness of the four named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hRane' : PtRa1 ≠ PtRa2 := hne_of_X (hPtRa1X ▸ hPtRa2X ▸ h12)
  have hRa1ιP1' : PtRa1 ≠ PtιP1 := hne_of_X (hPtRa1X ▸ hPtιP1X ▸ h1P1)
  have hRa1ιP2' : PtRa1 ≠ PtιP2 := hne_of_X (hPtRa1X ▸ hPtιP2X ▸ h1P2)
  have hRa2ιP1' : PtRa2 ≠ PtιP1 := hne_of_X (hPtRa2X ▸ hPtιP1X ▸ h2P1)
  have hRa2ιP2' : PtRa2 ≠ PtιP2 := hne_of_X (hPtRa2X ▸ hPtιP2X ▸ h2P2)
  have hPP' : PtιP1 ≠ PtιP2 := hne_of_X (hPtιP1X ▸ hPtιP2X ▸ hPP)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, coeffAt_single]
  by_cases hEqRa1 : P = PtRa1
  · rw [hEqRa1]
    simpa [hOrdRa1, hRane', hRa1ιP1', hRa1ιP2']
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hRa2Ra1' : PtRa2 ≠ PtRa1 := hRane'.symm
    simpa [hOrdRa2, hRa2Ra1', hRa2ιP1', hRa2ιP2']
  by_cases hEqιP1 : P = PtιP1
  · rw [hEqιP1]
    have hιP1Ra1' : PtιP1 ≠ PtRa1 := hRa1ιP1'.symm
    have hιP1Ra2' : PtιP1 ≠ PtRa2 := hRa2ιP1'.symm
    simpa [hOrdιP1, hιP1Ra1', hιP1Ra2', hPP']
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hιP2Ra1' : PtιP2 ≠ PtRa1 := hRa1ιP2'.symm
    have hιP2Ra2' : PtιP2 ≠ PtRa2 := hRa2ιP2'.symm
    have hιP2ιP1' : PtιP2 ≠ PtιP1 := hPP'.symm
    simpa [hOrdιP2, hιP2Ra1', hιP2Ra2', hιP2ιP1']
  · have hnmemS : P ∉ ({PtRa1, PtRa2, PtιP1, PtιP2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEqRa1, hEqRa2, hEqιP1, hEqιP2⟩
    simp only [if_neg hnmemS, if_neg hEqRa1, if_neg hEqRa2, if_neg hEqιP1, if_neg hEqιP2]
    ring

end DecoupledSystem
end Genus2Lean
