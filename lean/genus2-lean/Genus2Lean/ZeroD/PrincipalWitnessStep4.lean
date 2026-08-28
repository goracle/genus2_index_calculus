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

**Second correction, this pass: the `T + ι(T) - 4•[δ₀] ∈ principalSubgroup`
"separately-principal fact" Part 3 was going to use (bullet 3 below, as
originally planned) is FALSE for a generic (non-Weierstrass) `δ₀`.**
Checked via ChatGPT consultation (`CHATGPT-LOG-principal-witness-assembly.md`):
passing to the smooth projective model, `div(x-a) = (P)+(ιP)-2[∞]` for any
`a = P.X`, so `T+ι(T) ~ 4[∞]` always — meaning `T+ι(T)-4[δ₀]` is principal
iff `4([δ₀]-[∞]) = 0` in the Jacobian, a special 4-torsion condition on
`δ₀`, not a general fact. The honest `linX`-witness fact is
`T + ι(T) - [δ₀] - [ι δ₀] - [δ₀] - [ι δ₀] ∈ principalSubgroup` (i.e.
`(x-T1.X)(x-T2.X)` against `(x-δ₀.X)²`, both pole order `-4`) — carries a
genuine `ι δ₀` term that does NOT reduce to a `δ₀`-multiple for generic
`δ₀`. **Part 2 below is unaffected — its own docstring never actually
needed the false `2•[δ₀]` simplification (see its corrected docstring) —
but Part 3 (bullet 3 below) needs a different derivation route than
originally planned, not yet found; see that section for status.** -/

/-!
Starting point: `PrincipalWitnessStep3.lean`'s
`divToPair_eq_C_add_iotaA_add_T_of_split`, a literal `Divisor H` equality
`div_aff(f) = C + ι(A) + T` over the six named points
`{PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2}`. This file turns that into a
`principalSubgroup` membership via one matching-`ordInfOfPair`-`(-6)`
ratio generator, `f` against `h_A := linX(P1.X) * linX(P2.X) *
linX(δ₀.X)`.

**Plan, three pieces (`Part 1`/`Part 2`/`Part 3` below):**
1. `div(h_A) = A + ι(A) + [δ₀] + [ι δ₀]` (`divToPair_hA_eq`) — an
   `eq_of_coeffAt_eq`/six-way-`by_cases` computation, same idiom as
   `PrincipalWitnessStep3.lean`'s own six-point assembly and
   `CAWitnessDivisor.lean`'s four-point one, here for a plain
   product-of-three-`linX` divisor instead of the Cantor interpolant.
   Built on top of `ordAt_linX_mul3_eq_one_of_ne`/
   `ordAt_linX_mul3_eq_zero_of_notMem`, the 3-factor analogues of
   `PrincipalWitness.lean`'s existing `ordAt_mul4_...` composition
   lemmas (themselves built from `ordAt_mul_eq_one_of_ordAt_eq_one_zero`
   iterated).
2. `div(f) - div(h_A) = C - A + T - [δ₀] - [ι δ₀]` (the ratio generator
   itself, `ordInfOfPair(f) = ordInfOfPair(h_A) = -6`), hence
   `C - A + T - [δ₀] - [ι δ₀] ∈ principalSubgroup`
   (`cAmT_mem_principalSubgroup`) — **DONE, build-green.**
3. **NOT YET DONE — blocked on finding the right derivation.** Originally
   planned as: restate as `C - A - ι(T) + 2•[δ₀] ∈ principalSubgroup`
   (`cAmIotaT_mem_principalSubgroup`, the shape
   `AlphaLocusDegreeUniform.lean`'s goal actually needs, matching
   `S := ι(T)`), using the separately-principal fact
   `T + ι(T) - 4•[δ₀] ∈ principalSubgroup`. **That auxiliary fact is
   false for generic `δ₀` (see the correction above) — this route does
   not work as stated.** `CAWitness.lean`'s own module docstring
   proposes an alternative direct route (three generators: `div(f) -
   div(h)` for `h := (x-Ra1.X)(x-Ra2.X)(x-δ₀.X)`, plus
   `div(x-P1.X)-div(x-δ₀.X)` and `div(x-P2.X)-div(x-δ₀.X)`) claimed to
   compose directly to `C - A - ι(T) + 2•[δ₀]` without the false
   `4•[δ₀]` step — but a by-hand term-by-term check of that route this
   pass did NOT close (extra `ι Ra1`, `ι Ra2`, `ι δ₀` terms appeared that
   don't cancel against the claimed target). A fresh ChatGPT pass has
   been asked to find the exact correct generator set; not yet returned.
   **Do not attempt to prove `T+ι(T)-4•[δ₀] ∈ principalSubgroup` or
   any Lean statement asserting it — it is false for a generic `δ₀`.**
   If `δ₀` genuinely needs a stronger hypothesis (e.g. its own
   `principalSubgroup`-related constraint, or fixing `δ₀` as a
   Weierstrass point elsewhere in the assembly) to make this step true,
   that is itself worth surfacing as a finding, not routed around.

**All `hspec`/`Module.Finite` Nullstellensatz-style side
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
    unfold linX
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_zero, zero_mul, add_zero]
    exact sub_ne_zero.mpr hQa)
  have h0b : ordAt Q (linX b) (0 : k[X]) = 0 := ordAt_eq_zero_of_eval_ne_zero Q (linX b) 0 (by
    unfold linX
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_zero, zero_mul, add_zero]
    exact sub_ne_zero.mpr hQb)
  have h0c : ordAt Q (linX c) (0 : k[X]) = 0 := ordAt_eq_zero_of_eval_ne_zero Q (linX c) 0 (by
    unfold linX
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_zero, zero_mul, add_zero]
    exact sub_ne_zero.mpr hQc)
  have hab_ne : toPair H (linX a * linX b) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']; exact mul_ne_zero (hne a) (hne b)
  have hab : ordAt Q (linX a * linX b) (0 : k[X]) = 0 := by
    rw [ordAt_add_of_pairNorm_eq_mul Q h_bot (linX a * linX b) (linX a) (linX b) rfl (hne a) (hne b)]
    omega
  rw [ordAt_add_of_pairNorm_eq_mul Q h_bot ((linX a * linX b) * linX c) (linX a * linX b) (linX c) rfl
    hab_ne (hne c)]
  omega

/-! ## Part 1 (continued): the assembled `Divisor H` equality for `h_A` -/

/-- **`div_aff(h_A) = P1 + P2 + ι(P1) + ι(P2) + 2•[δ₀]`, `h_A := (x-P1.X)(x-P2.X)(x-δ₀.X)`,
fully-split case.** Six named points `{P1, P2, ιP1, ιP2, δ₀, ιδ₀}`, same
`eq_of_coeffAt_eq`/`coeffAt_divToPair`/six-way-`by_cases` idiom as
`PrincipalWitnessStep3.lean`'s `divToPair_eq_C_add_iotaA_add_T_of_split` and
`CAWitnessDivisor.lean`'s four-point original. `δ₀`'s own `ordAt = 1` fact
(both at `δ₀` and at `ι δ₀`) is the one case not already covered by
`ordAt_linX_mul3_eq_one_of_ne` alone — the `(a,b,c) := (δ₀.X,P1.X,P2.X)`
instance handles `δ₀`, and `(a,b,c) := (δ₀.X,P2.X,P1.X)` (swapped `b,c`)
handles `ι δ₀` (same `X`-coordinate, so the same `ordAt_linX_mul3_eq_one_of_ne`
call works verbatim once re-pointed at `Point.iota δ₀`) — `h_A`'s factor
order is re-bracketed per point via `mul_comm`/`mul_left_comm` as needed so
the "designated" (order-1) factor is always leftmost, matching that lemma's
own convention. -/
theorem divToPair_hA_eq
    [DecidableEq k] [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 δ₀ : H.Point)
    (h12 : P1.X ≠ P2.X) (h1δ : P1.X ≠ δ₀.X) (h2δ : P2.X ≠ δ₀.X)
    (hP1Y : P1.Y ≠ 0) (hP2Y : P2.Y ≠ 0) (hδY : δ₀.Y ≠ 0) :
    divToPair ((linX P1.X * linX P2.X) * linX δ₀.X) (0 : k[X])
        ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} : Finset H.Point) =
      single P1 + single P2 + single (Point.iota P1) + single (Point.iota P2) +
        single δ₀ + single (Point.iota δ₀) := by
  classical
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  -- `ordAt = 1` at each of the six named points, via `ordAt_linX_mul3_eq_one_of_ne`
  -- with the designated factor re-bracketed to be leftmost each time.
  have hOrdP1 : ordAt P1 ((linX P1.X * linX P2.X) * linX δ₀.X) (0 : k[X]) = 1 :=
    ordAt_linX_mul3_eq_one_of_ne hchar hsf P1 (h_bot P1) P1.X P2.X δ₀.X rfl hP1Y
      (Ne.symm h12) (Ne.symm h1δ)
  have hOrdP2 : ordAt P2 ((linX P1.X * linX P2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf P2 (h_bot P2) P2.X P1.X δ₀.X rfl hP2Y
      h12 (Ne.symm h2δ)
    have heq : (linX P1.X * linX P2.X) * linX δ₀.X =
        (linX P2.X * linX P1.X) * linX δ₀.X := by ring
    rw [heq]; exact h
  have hOrdιP1 : ordAt (Point.iota P1) ((linX P1.X * linX P2.X) * linX δ₀.X) (0 : k[X]) = 1 :=
    ordAt_linX_mul3_eq_one_of_ne hchar hsf (Point.iota P1) (h_bot _) P1.X P2.X δ₀.X
      (Point.iota_X P1) (by simpa using hP1Y) (Ne.symm h12) (Ne.symm h1δ)
  have hOrdιP2 : ordAt (Point.iota P2) ((linX P1.X * linX P2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf (Point.iota P2) (h_bot _) P2.X P1.X δ₀.X
      (Point.iota_X P2) (by simpa using hP2Y) h12 (Ne.symm h2δ)
    have heq : (linX P1.X * linX P2.X) * linX δ₀.X =
        (linX P2.X * linX P1.X) * linX δ₀.X := by ring
    rw [heq]; exact h
  have hOrdδ : ordAt δ₀ ((linX P1.X * linX P2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf δ₀ (h_bot δ₀) δ₀.X P1.X P2.X rfl hδY
      h1δ h2δ
    have heq : (linX P1.X * linX P2.X) * linX δ₀.X =
        (linX δ₀.X * linX P1.X) * linX P2.X := by ring
    rw [heq]; exact h
  have hOrdιδ : ordAt (Point.iota δ₀) ((linX P1.X * linX P2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf (Point.iota δ₀) (h_bot _) δ₀.X P1.X P2.X
      (Point.iota_X δ₀) (by simpa using hδY) h1δ h2δ
    have heq : (linX P1.X * linX P2.X) * linX δ₀.X =
        (linX δ₀.X * linX P1.X) * linX P2.X := by ring
    rw [heq]; exact h
  -- Pairwise distinctness of all six named points, from `X`-coordinate facts.
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hP1P2 : P1 ≠ P2 := hne_of_X h12
  have hP1ιP1 : P1 ≠ Point.iota P1 := (Point.iota_ne_self_of_Y_ne_zero hchar hP1Y).symm
  have hP1ιP2 : P1 ≠ Point.iota P2 := hne_of_X (by rw [Point.iota_X]; exact h12)
  have hP1δ : P1 ≠ δ₀ := hne_of_X h1δ
  have hP1ιδ : P1 ≠ Point.iota δ₀ := hne_of_X (by rw [Point.iota_X]; exact h1δ)
  have hP2ιP1 : P2 ≠ Point.iota P1 := hne_of_X (by rw [Point.iota_X]; exact Ne.symm h12)
  have hP2ιP2 : P2 ≠ Point.iota P2 := (Point.iota_ne_self_of_Y_ne_zero hchar hP2Y).symm
  have hP2δ : P2 ≠ δ₀ := hne_of_X h2δ
  have hP2ιδ : P2 ≠ Point.iota δ₀ := hne_of_X (by rw [Point.iota_X]; exact h2δ)
  have hιP1ιP2 : Point.iota P1 ≠ Point.iota P2 := hne_of_X (by
    rw [Point.iota_X, Point.iota_X]; exact h12)
  have hιP1δ : Point.iota P1 ≠ δ₀ := hne_of_X (by rw [Point.iota_X]; exact h1δ)
  have hιP1ιδ : Point.iota P1 ≠ Point.iota δ₀ := hne_of_X (by
    rw [Point.iota_X, Point.iota_X]; exact h1δ)
  have hιP2δ : Point.iota P2 ≠ δ₀ := hne_of_X (by rw [Point.iota_X]; exact h2δ)
  have hιP2ιδ : Point.iota P2 ≠ Point.iota δ₀ := hne_of_X (by
    rw [Point.iota_X, Point.iota_X]; exact h2δ)
  have hδιδ : δ₀ ≠ Point.iota δ₀ := (Point.iota_ne_self_of_Y_ne_zero hchar hδY).symm
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, coeffAt_single]
  by_cases hEqP1 : P = P1
  · rw [hEqP1]
    have hMem : P1 ∈ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_pos rfl, if_neg hP1P2, if_neg hP1ιP1, if_neg hP1ιP2,
      if_neg hP1δ, if_neg hP1ιδ, hOrdP1]
    ring
  by_cases hEqP2 : P = P2
  · rw [hEqP2]
    have hMem : P2 ∈ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hP1P2), if_pos rfl, if_neg hP2ιP1, if_neg hP2ιP2,
      if_neg hP2δ, if_neg hP2ιδ, hOrdP2]
    ring
  by_cases hEqιP1 : P = Point.iota P1
  · rw [hEqιP1]
    have hMem : Point.iota P1 ∈ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hP1ιP1), if_neg (Ne.symm hP2ιP1), if_pos rfl,
      if_neg hιP1ιP2, if_neg hιP1δ, if_neg hιP1ιδ, hOrdιP1]
    ring
  by_cases hEqιP2 : P = Point.iota P2
  · rw [hEqιP2]
    have hMem : Point.iota P2 ∈ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hP1ιP2), if_neg (Ne.symm hP2ιP2), if_neg (Ne.symm hιP1ιP2),
      if_pos rfl, if_neg hιP2δ, if_neg hιP2ιδ, hOrdιP2]
    ring
  by_cases hEqδ : P = δ₀
  · rw [hEqδ]
    have hMem : δ₀ ∈ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hP1δ), if_neg (Ne.symm hP2δ), if_neg (Ne.symm hιP1δ),
      if_neg (Ne.symm hιP2δ), if_pos rfl, if_neg hδιδ, hOrdδ]
    ring
  by_cases hEqιδ : P = Point.iota δ₀
  · rw [hEqιδ]
    have hMem : Point.iota δ₀ ∈ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hP1ιδ), if_neg (Ne.symm hP2ιδ), if_neg (Ne.symm hιP1ιδ),
      if_neg (Ne.symm hιP2ιδ), if_neg (Ne.symm hδιδ), if_pos rfl, hOrdιδ]
    ring
  · rw [if_neg hEqP1, if_neg hEqP2, if_neg hEqιP1, if_neg hEqιP2, if_neg hEqδ, if_neg hEqιδ]
    have hnmemS : P ∉ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hEqP1 rfl
      · exact hEqP2 rfl
      · exact hEqιP1 rfl
      · exact hEqιP2 rfl
      · exact hEqδ rfl
      · exact hEqιδ rfl
    rw [if_neg hnmemS]
    ring

/-! ## Part 2: `div(f) - div(h_A) = C - A + T - [δ₀] - [ι δ₀] ∈ principalSubgroup` -/

/-- **`ordInfOfPair` of `h_A := (linX P1.X * linX P2.X) * linX δ₀.X` (as an
`(A,B)`-pair with `B = 0`) is `-6`.** Pure degree computation: each `linX`
factor has degree `1` (`linX_natDegree`), so the product has degree `3`
(`Polynomial.natDegree_mul` twice, valid since `k` is a field — no zero
divisors), and `ordInfOfPair`'s `B = 0` branch is `-(2 * natDegree)`. Matches
`CAWitness.lean`'s `bCA_ordInfOfPair` (`ordInfOfPair (-bCA) 1 = -6`) exactly,
which is what lets `f := toPair H (-bCA) 1` and `h_A := toPair H h_A_poly 0`
form a `principalSubgroup` ratio generator (`deg_divToPairRatio_eq_zero`
needs `ordInfOfPair` to MATCH, not both be `0` — see
`PrincipalDivisorSubgroup.lean`'s module docstring). -/
theorem ordInfOfPair_hA (a b c : k) :
    ordInfOfPair ((linX a * linX b) * linX c) (0 : k[X]) = -6 := by
  have hne : ∀ x : k, linX x ≠ (0 : k[X]) := fun x => by
    unfold linX; exact Polynomial.X_sub_C_ne_zero x
  have hab_ne : linX a * linX b ≠ (0 : k[X]) := mul_ne_zero (hne a) (hne b)
  have habc_ne : (linX a * linX b) * linX c ≠ (0 : k[X]) := mul_ne_zero hab_ne (hne c)
  have hdeg_ab : (linX a * linX b).natDegree = 2 := by
    rw [Polynomial.natDegree_mul (hne a) (hne b), linX_natDegree, linX_natDegree]
  have hdeg_abc : ((linX a * linX b) * linX c).natDegree = 3 := by
    rw [Polynomial.natDegree_mul hab_ne (hne c), hdeg_ab, linX_natDegree]
  unfold ordInfOfPair
  rw [if_neg (fun h => habc_ne h.1)]
  simp [hdeg_abc]

/-- **The ratio generator itself: `div_aff(f) - div_aff(h_A) =
Ra1 + Ra2 + ι(P1) + ι(P2) + T1 + T2 - P1 - P2 - ι(P1) - ι(P2) - δ₀ - ι(δ₀)
= C - A + T - [δ₀] - [ι δ₀]`, as membership in `principalSubgroup H hdeg`**
(`C := {Ra1,Ra2}`, `A := {P1,P2}`, `T := {PtT1,PtT2}`, matching this file's
module docstring). **Correction from an earlier pass's docstring here:**
`div(h_A)`'s own support is `{P1,ιP1,P2,ιP2,δ₀,ιδ₀}` (`divToPair_hA_eq`,
Part 1 above) — `h_A`'s `δ₀`-factor `linX δ₀.X` vanishes at BOTH `δ₀` and
`ι δ₀` (any single `linX` always hits its whole fiber), not `δ₀` alone, so
the honest difference carries `- [δ₀] - [ι δ₀]`, not `-2•[δ₀]`. A ChatGPT
consultation this pass (see `CHATGPT-LOG-principal-witness-assembly.md`)
confirmed the bare-`2•[δ₀]` claim in an earlier draft of this file's module
docstring was FALSE for a generic (non-Weierstrass) `δ₀`: it is equivalent
to the special 4-torsion condition `4([δ₀]-[∞]) = 0` in the Jacobian, not a
general fact. This theorem's actual Lean statement was never affected by
that error — it is a literal `Finset`-level divisor difference over eight
named points total (six from `f`, six from `h_A`, four shared), true and
provable regardless of how its docstring summarized it; only the prose
label needed fixing. `f := toPair H (-bCA) 1` and `h_A := toPair H h_A_poly
0` share `ordInfOfPair = -6` (`bCA_ordInfOfPair`/`ordInfOfPair_hA`), which
is EXACTLY `deg_divToPairRatio_eq_zero`'s matching condition — the two
individually-nonzero-pole-order functions cancel in the ratio, landing the
difference divisor in `principalSubgroup` even though neither summand alone
would. The `hsupp`/`hspec`/`Module.Finite` Nullstellensatz-style side
conditions are threaded through as caller-supplied hypotheses, per this
file's own module docstring — none of them are discharged anywhere in this
codebase yet (matching `HyperellipticClassProof.lean`'s
`hyperellipticClass_principalDivisorData`, the one other place in this
codebase that reaches `principalSubgroup` directly). -/
theorem cAmT_mem_principalSubgroup
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hlead : caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3 ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa2 PtιP1 PtιP2 P1 P2 δ₀ : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hP1X : P1.X = P1X) (hP1Y : P1.Y = P1Y)
    (hP2X : P2.X = P2X) (hP2Y : P2.Y = P2Y)
    (h1δ : P1X ≠ δ₀.X) (h2δ : P2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hU_evalRa1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra1X ≠ 0)
    (hU_evalRa2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T1X)
    (hT2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hAeval1 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])).toNat)]
    (hsupp_hA : ∀ P, P ∉ ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX P1X * linX P2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hA : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX P1X * linX P2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX P1X * linX P2X) * linX δ₀.X) (0 : k[X])).toNat)] :
    (divToPair (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
        ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) -
      divToPair ((linX P1X * linX P2X) * linX δ₀.X) (0 : k[X])
        ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
          ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) -
        divToPair ((linX P1X * linX P2X) * linX δ₀.X) (0 : k[X])
          ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
          ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point)
        ((linX P1X * linX P2X) * linX δ₀.X) (0 : k[X])
          ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y, 1,
    ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX P1X * linX P2X) * linX δ₀.X, 0,
    ({P1, P2, Point.iota P1, Point.iota P2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hA, hspec_hA, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero P1X) (linX_ne_zero P2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCA_ordInfOfPair Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hlead, ordInfOfPair_hA]

/-! ## Part 3: the honest generic-`δ₀` fact, and the confirmed gap

**ChatGPT consultation this pass (see `CHATGPT-LOG-principal-witness-assembly.md`)
confirmed, via an explicit three-generator computation, that the
originally-planned target `C - A - ι(T) + 2•[δ₀] ∈ principalSubgroup` is
FALSE for a generic (non-Weierstrass) `δ₀`.** The three matching-pole
generators available from this stack —

* `G₁ := div(f) - div(h_T)`, `h_T := (x-T1.X)(x-T2.X)(x-δ₀.X)`
  (`ordInfOfPair = -6` both sides, mirroring Part 1/2's `h_A` construction
  but against `T` instead of `A`) — gives
  `C + ι(A) + T - (T + ι(T) + [δ₀] + [ιδ₀]) = C + ι(A) - ι(T) - [δ₀] - [ιδ₀]`;
* `G₂ := div(x-P1.X) - div(x-δ₀.X)` (`divToPair_linX_eq`,
  `HyperellipticClassProof.lean`, already 0-`sorry`) — gives
  `P1 + ι(P1) - δ₀ - ιδ₀`;
* `G₃`, the `P2` mirror of `G₂` —

compose (`G₁ - G₂ - G₃`, term-by-term cancellation confirmed by hand and
by ChatGPT independently) to exactly

  `C - A - ι(T) + [δ₀] + [ιδ₀] ∈ principalSubgroup`     (†)

**not** the `2•[δ₀]` version. The discrepancy `(2•[δ₀]) - ([δ₀]+[ιδ₀]) =
[δ₀] - [ιδ₀]` is a genuine extra condition — equivalent, on the smooth
projective model, to `2([δ₀]-[∞]) = 0` in the Jacobian, a special
torsion condition on the basepoint `δ₀`, not a general fact. `δ₀` in
`AlphaLocusDegreeUniform.lean`'s `SampleTargetFromAlpha` is an arbitrary
caller-supplied basepoint with no such constraint, so **no proof of the
`2•[δ₀]` statement from this stack's generators exists, and none should
be attempted** — `[δ₀] - [ιδ₀] ∈ principalSubgroup` is false for generic
`δ₀`, exactly the same category of false statement as the already-rejected
`T + ι(T) - 4•[δ₀] ∈ principalSubgroup` from an earlier pass.

**This is a real finding about `AlphaLocusDegreeUniform.lean`'s theorem
statement, not a gap in this file's proof technique.** The `2•[δ₀]`
normalization there comes from the `s`-embedding (`DivisorClassGroup.lean`'s
`s D δ₀ P := toJacobian D ⟨single P - single δ₀, _⟩`, applied twice — a
*formal* `2•[δ₀]` inside `Divisor0 H`, unrelated to any `linX`-fiber
divisor) — it is not, and was never claimed to be, `div(x - δ₀.X) =
[δ₀]+[ιδ₀]`. Conflating the two is exactly the error (†) rules out.
**Next step, not done here**: `reducedClass_eq_of_isReduction'`'s own
`sorry` needs either (a) an added hypothesis pinning `δ₀` to a
Weierstrass point (`δ₀.Y = 0`, forcing `ι δ₀ = δ₀`, hence `[δ₀]+[ιδ₀] =
2•[δ₀]` trivially — the cheapest fix, but narrows the theorem's scope),
or (b) accepting (†)'s weaker conclusion and checking whether
`reducedClass_eq_of_isReduction'`'s actual goal can be restated/weakened
to match `[δ₀]+[ιδ₀]` throughout instead of `2•[δ₀]` (i.e. whether the
`s`-embedding itself could use `[δ₀]+[ιδ₀]` — unlikely, since that breaks
`s`'s degree-1 embedding property `DivisorClassGroup.lean` relies on
elsewhere), or (c) finding a genuinely different generator set not built
from this stack's `linX`/`f` ratios. Do not attempt (†)'s `2•[δ₀]`
strengthening directly — confirmed false, per above. -/

/-- **The honest fact: `C - A - ι(T) + [δ₀] + [ιδ₀] ∈ principalSubgroup`**,
for generic (not necessarily Weierstrass) `δ₀` — the correct three-generator
composition `G₁ - G₂ - G₃` described in this file's Part 3 docstring above.
`G₁` needs `h_T`'s own divisor fact (`divToPair_hT_eq` below, mirroring
Part 1's `divToPair_hA_eq` but against `T1X, T2X, δ₀` instead of
`P1X, P2X, δ₀`); `G₂`/`G₃` reuse `divToPair_linX_eq`
(`HyperellipticClassProof.lean`) directly at `P1`/`P2` against `δ₀`. -/
theorem divToPair_hT_eq
    [DecidableEq k] [DecidableEq H.Point]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (PtT1 PtT2 δ₀ : H.Point)
    (h12 : PtT1.X ≠ PtT2.X) (h1δ : PtT1.X ≠ δ₀.X) (h2δ : PtT2.X ≠ δ₀.X)
    (hT1Y : PtT1.Y ≠ 0) (hT2Y : PtT2.Y ≠ 0) (hδY : δ₀.Y ≠ 0) :
    divToPair ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) =
      single PtT1 + single PtT2 + single (Point.iota PtT1) + single (Point.iota PtT2) +
        single δ₀ + single (Point.iota δ₀) := by
  classical
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have hOrdT1 : ordAt PtT1 ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : k[X]) = 1 :=
    ordAt_linX_mul3_eq_one_of_ne hchar hsf PtT1 (h_bot PtT1) PtT1.X PtT2.X δ₀.X rfl hT1Y
      (Ne.symm h12) (Ne.symm h1δ)
  have hOrdT2 : ordAt PtT2 ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf PtT2 (h_bot PtT2) PtT2.X PtT1.X δ₀.X rfl hT2Y
      h12 (Ne.symm h2δ)
    have heq : (linX PtT1.X * linX PtT2.X) * linX δ₀.X =
        (linX PtT2.X * linX PtT1.X) * linX δ₀.X := by ring
    rw [heq]; exact h
  have hOrdιT1 : ordAt (Point.iota PtT1) ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : k[X]) = 1 :=
    ordAt_linX_mul3_eq_one_of_ne hchar hsf (Point.iota PtT1) (h_bot _) PtT1.X PtT2.X δ₀.X
      (Point.iota_X PtT1) (by simpa using hT1Y) (Ne.symm h12) (Ne.symm h1δ)
  have hOrdιT2 : ordAt (Point.iota PtT2) ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf (Point.iota PtT2) (h_bot _) PtT2.X PtT1.X δ₀.X
      (Point.iota_X PtT2) (by simpa using hT2Y) h12 (Ne.symm h2δ)
    have heq : (linX PtT1.X * linX PtT2.X) * linX δ₀.X =
        (linX PtT2.X * linX PtT1.X) * linX δ₀.X := by ring
    rw [heq]; exact h
  have hOrdδ : ordAt δ₀ ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf δ₀ (h_bot δ₀) δ₀.X PtT1.X PtT2.X rfl hδY
      h1δ h2δ
    have heq : (linX PtT1.X * linX PtT2.X) * linX δ₀.X =
        (linX δ₀.X * linX PtT1.X) * linX PtT2.X := by ring
    rw [heq]; exact h
  have hOrdιδ : ordAt (Point.iota δ₀) ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : k[X]) = 1 := by
    have h := ordAt_linX_mul3_eq_one_of_ne hchar hsf (Point.iota δ₀) (h_bot _) δ₀.X PtT1.X PtT2.X
      (Point.iota_X δ₀) (by simpa using hδY) h1δ h2δ
    have heq : (linX PtT1.X * linX PtT2.X) * linX δ₀.X =
        (linX δ₀.X * linX PtT1.X) * linX PtT2.X := by ring
    rw [heq]; exact h
  have hne_of_X : ∀ {Q1 Q2 : H.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hT1T2 : PtT1 ≠ PtT2 := hne_of_X h12
  have hT1ιT1 : PtT1 ≠ Point.iota PtT1 := (Point.iota_ne_self_of_Y_ne_zero hchar hT1Y).symm
  have hT1ιT2 : PtT1 ≠ Point.iota PtT2 := hne_of_X (by rw [Point.iota_X]; exact h12)
  have hT1δ : PtT1 ≠ δ₀ := hne_of_X h1δ
  have hT1ιδ : PtT1 ≠ Point.iota δ₀ := hne_of_X (by rw [Point.iota_X]; exact h1δ)
  have hT2ιT1 : PtT2 ≠ Point.iota PtT1 := hne_of_X (by rw [Point.iota_X]; exact Ne.symm h12)
  have hT2ιT2 : PtT2 ≠ Point.iota PtT2 := (Point.iota_ne_self_of_Y_ne_zero hchar hT2Y).symm
  have hT2δ : PtT2 ≠ δ₀ := hne_of_X h2δ
  have hT2ιδ : PtT2 ≠ Point.iota δ₀ := hne_of_X (by rw [Point.iota_X]; exact h2δ)
  have hιT1ιT2 : Point.iota PtT1 ≠ Point.iota PtT2 := hne_of_X (by
    rw [Point.iota_X, Point.iota_X]; exact h12)
  have hιT1δ : Point.iota PtT1 ≠ δ₀ := hne_of_X (by rw [Point.iota_X]; exact h1δ)
  have hιT1ιδ : Point.iota PtT1 ≠ Point.iota δ₀ := hne_of_X (by
    rw [Point.iota_X, Point.iota_X]; exact h1δ)
  have hιT2δ : Point.iota PtT2 ≠ δ₀ := hne_of_X (by rw [Point.iota_X]; exact h2δ)
  have hιT2ιδ : Point.iota PtT2 ≠ Point.iota δ₀ := hne_of_X (by
    rw [Point.iota_X, Point.iota_X]; exact h2δ)
  have hδιδ : δ₀ ≠ Point.iota δ₀ := (Point.iota_ne_self_of_Y_ne_zero hchar hδY).symm
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, coeffAt_single]
  by_cases hEqT1 : P = PtT1
  · rw [hEqT1]
    have hMem : PtT1 ∈ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_pos rfl, if_neg hT1T2, if_neg hT1ιT1, if_neg hT1ιT2,
      if_neg hT1δ, if_neg hT1ιδ, hOrdT1]
    ring
  by_cases hEqT2 : P = PtT2
  · rw [hEqT2]
    have hMem : PtT2 ∈ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hT1T2), if_pos rfl, if_neg hT2ιT1, if_neg hT2ιT2,
      if_neg hT2δ, if_neg hT2ιδ, hOrdT2]
    ring
  by_cases hEqιT1 : P = Point.iota PtT1
  · rw [hEqιT1]
    have hMem : Point.iota PtT1 ∈ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀,
        Point.iota δ₀} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hT1ιT1), if_neg (Ne.symm hT2ιT1), if_pos rfl,
      if_neg hιT1ιT2, if_neg hιT1δ, if_neg hιT1ιδ, hOrdιT1]
    ring
  by_cases hEqιT2 : P = Point.iota PtT2
  · rw [hEqιT2]
    have hMem : Point.iota PtT2 ∈ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀,
        Point.iota δ₀} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hT1ιT2), if_neg (Ne.symm hT2ιT2), if_neg (Ne.symm hιT1ιT2),
      if_pos rfl, if_neg hιT2δ, if_neg hιT2ιδ, hOrdιT2]
    ring
  by_cases hEqδ : P = δ₀
  · rw [hEqδ]
    have hMem : δ₀ ∈ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hT1δ), if_neg (Ne.symm hT2δ), if_neg (Ne.symm hιT1δ),
      if_neg (Ne.symm hιT2δ), if_pos rfl, if_neg hδιδ, hOrdδ]
    ring
  by_cases hEqιδ : P = Point.iota δ₀
  · rw [hEqιδ]
    have hMem : Point.iota δ₀ ∈ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀,
        Point.iota δ₀} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hT1ιδ), if_neg (Ne.symm hT2ιδ), if_neg (Ne.symm hιT1ιδ),
      if_neg (Ne.symm hιT2ιδ), if_neg (Ne.symm hδιδ), if_pos rfl, hOrdιδ]
    ring
  · rw [if_neg hEqT1, if_neg hEqT2, if_neg hEqιT1, if_neg hEqιT2, if_neg hEqδ, if_neg hEqιδ]
    have hnmemS : P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hEqT1 rfl
      · exact hEqT2 rfl
      · exact hEqιT1 rfl
      · exact hEqιT2 rfl
      · exact hEqδ rfl
      · exact hEqιδ rfl
    rw [if_neg hnmemS]
    ring

/-- **`ordInfOfPair` of `h_T := (linX T1.X * linX T2.X) * linX δ₀.X` is
`-6`.** Identical degree computation to `ordInfOfPair_hA` above, restated
for `T1, T2` in place of `P1, P2` (the underlying fact is generic in the
three linear-factor roots, so this is the same proof verbatim). -/
theorem ordInfOfPair_hT (a b c : k) :
    ordInfOfPair ((linX a * linX b) * linX c) (0 : k[X]) = -6 :=
  ordInfOfPair_hA a b c

/-- **`G₁ := div(f) - div(h_T) = C + ι(A) - ι(T) - [δ₀] - [ιδ₀] ∈
principalSubgroup`**, the first of the three generators in this file's
Part 3 docstring. Same `divToPairRatio`/`AddSubgroup.subset_closure`
idiom as `cAmT_mem_principalSubgroup` (Part 2), with `h_A` replaced by
`h_T` (`divToPair_hT_eq` above) and the matching `ordInfOfPair = -6`
fact supplied by `ordInfOfPair_hT`. -/
theorem cIotaAmIotaT_mem_principalSubgroup
    [DecidableEq k] [DecidableEq H.Point]
    (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (hlead : caCoeff Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y 3 ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (hRa1Y_ne : Ra1Y ≠ 0) (hRa2Y_ne : Ra2Y ≠ 0) (hP1Y_ne : P1Y ≠ 0) (hP2Y_ne : P2Y ≠ 0)
    (PtRa1 PtRa2 PtιP1 PtιP2 δ₀ : H.Point)
    (hPtRa1X : PtRa1.X = Ra1X) (hPtRa1Y : PtRa1.Y = Ra1Y)
    (hPtRa2X : PtRa2.X = Ra2X) (hPtRa2Y : PtRa2.Y = Ra2Y)
    (hPtιP1X : PtιP1.X = P1X) (hPtιP1Y : PtιP1.Y = -P1Y)
    (hPtιP2X : PtιP2.X = P2X) (hPtιP2Y : PtιP2.Y = -P2Y)
    (hU_evalRa1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra1X ≠ 0)
    (hU_evalRa2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval Ra2X ≠ 0)
    (hU_evalP1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P1X ≠ 0)
    (hU_evalP2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P2X ≠ 0)
    (hU_ne0 : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y ≠ 0)
    (T1X T2X : k)
    (hT1 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T1X)
    (hT2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).IsRoot T2X)
    (hTne : T1X ≠ T2X)
    (Q1 Q2 : Polynomial k)
    (hQ1_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T1X) * (X - C T2X) * Q1)
    (hQ1T1 : Q1.eval T1X ≠ 0)
    (hQ2_def : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y =
      (X - C T2X) * (X - C T1X) * Q2)
    (hQ2T2 : Q2.eval T2X ≠ 0)
    (PtT1 PtT2 : H.Point)
    (hAeval1 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval PtT2.X ≠ 0)
    (hPtT1X : PtT1.X = T1X)
    (hPtT1Y : PtT1.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2X : PtT2.X = T2X)
    (hPtT2Y : PtT2.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (h1δ : T1X ≠ δ₀.X) (h2δ : T2X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hsupp_f : ∀ P, P ∉ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) →
      ordAt P (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 0)
    (hspec_f : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X]) = 0)
    (hspec_hT : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX T1X * linX T2X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])).toNat)] :
    (divToPair (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
        ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) -
      divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
        ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) ∈
      principalSubgroup H hdeg := by
  have hgoal_eq :
      (divToPair (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
          ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) -
        divToPair ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point)) =
      divToPairRatio (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
          ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point)
        ((linX T1X * linX T2X) * linX δ₀.X) (0 : k[X])
          ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point) := rfl
  rw [hgoal_eq]
  apply AddSubgroup.subset_closure
  refine ⟨-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y, 1,
    ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point),
    fun ⟨_, hB⟩ => one_ne_zero hB, hsupp_f, hspec_f, ‹_›,
    (linX T1X * linX T2X) * linX δ₀.X, 0,
    ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
    ?_, hsupp_hT, hspec_hT, ‹_›, ?_, rfl⟩
  · refine fun ⟨hA, _⟩ => ?_
    exact mul_ne_zero (mul_ne_zero (linX_ne_zero T1X) (linX_ne_zero T2X)) (linX_ne_zero δ₀.X) hA
  · rw [bCA_ordInfOfPair Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hlead, ordInfOfPair_hT]

end DecoupledSystem
end Genus2Lean