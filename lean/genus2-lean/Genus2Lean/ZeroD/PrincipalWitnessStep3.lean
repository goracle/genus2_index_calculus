import Mathlib
import Genus2Lean.ZeroD.CAWitness
import Genus2Lean.ZeroD.CAWitnessDivisor
import Genus2Lean.ZeroD.CAWitnessResidual
import Genus2Lean.ZeroD.PrincipalWitness

/-!
# `ROADMAP-principal-witness-assembly.md` step 2: the complete divisor
# `div_aff(f) = C + ι(A) + T` for `f := y - bCA(x)`

`CAWitnessDivisor.lean` (step 1's four-named-point half) gives `f`'s
divisor restricted to `{Ra1, Ra2, ιP1, ιP2}`. `CAWitnessResidual.lean`
(also step 1) gives the pointwise `ordAt` fact at a single, abstract
root of the residual quadratic `uCANew`, via `uCANew`'s own
`rootMultiplicity` — deliberately left un-split into named roots there,
per that file's own docstring.

**This file supplies the missing splitting step and the final
assembly.** To state a concrete `Finset`-level `divToPair` equality, the
two residual roots have to be named after all (the same situation
`PrincipalWitnessStep2.lean`'s `divToPair_eq_rho_add_I_of_split` was in
for `uRS4General`, and its docstring's own justification: *"both roots
must be named after all"*). Named here as `T1X, T2X` with `T1X ≠ T2X`
(fully-split case only, matching every other file in this stack's own
scoping).

**Route: NOT `quadratic_eq_mul_X_sub_C` + `uCANew`'s degree.** That
would require establishing `uCANew.natDegree = 2` from scratch (`H.f`'s
degree, `bCA²`'s degree, and the `/ₘ`-quotient degree arithmetic) —
exactly the kind of extra bookkeeping the `rootMultiplicity`-first
design in `CAWitnessResidual.lean` was built to avoid needing. Instead:
given `uCANew.IsRoot T1X`, `uCANew.IsRoot T2X`, `T1X ≠ T2X`, coprimality
of `(X - C T1X)` and `(X - C T2X)` gives `(X-C T1X)*(X-C T2X) ∣ uCANew`,
i.e. `uCANew = (X-C T1X)*(X-C T2X)*Q` for some quotient `Q` — and
`rootMultiplicity T1X uCANew = 1` follows directly from `Q.eval T1X ≠ 0`
(supplied as a hypothesis, `hQT1`/`hQT2` below — this is exactly "`T1X`,
`T2X` are simple roots, nothing else coincides with them", the natural
per-point nondegeneracy fact at this stage, same spirit as
`CAWitnessDivisor.lean`'s own `hU_evalRa1`-style caller-supplied
hypotheses), with no reference to `uCANew`'s degree anywhere.

**Result**: one `Divisor H` equality over the full six-point support
`{Ra1, Ra2, ιP1, ιP2, PtT1, PtT2}`, obtained the same way every other
assembly theorem in this stack is: `eq_of_coeffAt_eq` +
`coeffAt_divToPair` + `by_cases` per named point (six-way case split
here, one more than `CAWitnessDivisor.lean`'s four). Feeds directly into
step 3 of the roadmap (`reducedClass_eq_of_isReduction'`'s `S`/`hSmem`/
`hufree`/`hScard` target shape), not attempted here. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`uCANew`'s `rootMultiplicity` at a named simple root is `1`.**
Pure polynomial-algebra step: `IsRoot` at `T1X`, `IsRoot` at a DIFFERENT
point `T2X`, coprimality of the two linear factors, and the quotient
`Q := uCANew /ₘ ((X-C T1X)*(X-C T2X))` not vanishing at `T1X` (`hQT1`) —
together these pin `rootMultiplicity T1X uCANew = 1` without ever
computing `uCANew`'s degree. -/
private theorem rootMultiplicity_uCANew_eq_one
    (U : Polynomial k) (hU_ne0 : U ≠ 0)
    (T1X T2X : k) (hT1 : U.IsRoot T1X) (hT2 : U.IsRoot T2X) (hTne : T1X ≠ T2X)
    (Q : Polynomial k) (hQ_def : U = (X - C T1X) * (X - C T2X) * Q)
    (hQT1 : Q.eval T1X ≠ 0) :
    Polynomial.rootMultiplicity T1X U = 1 := by
  have hQ_ne0 : Q ≠ 0 := by
    rintro rfl
    apply hU_ne0
    rw [hQ_def]; ring
  have hfac_ne0 : (X - C T1X) * (X - C T2X) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero T1X) (X_sub_C_ne_zero T2X)
  -- `rootMultiplicity T1X ((X-C T1X)*(X-C T2X)) = 1`.
  have hmul_mult : Polynomial.rootMultiplicity T1X ((X - C T1X) * (X - C T2X)) = 1 := by
    rw [Polynomial.rootMultiplicity_mul hfac_ne0, Polynomial.rootMultiplicity_X_sub_C_self]
    have : Polynomial.rootMultiplicity T1X (X - C T2X : Polynomial k) = 0 := by
      apply Polynomial.rootMultiplicity_eq_zero
      show ¬ (X - C T2X : Polynomial k).IsRoot T1X
      simp only [Polynomial.IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero]
      exact hTne
    rw [this]
  -- `rootMultiplicity T1X Q = 0` since `Q.eval T1X ≠ 0`.
  have hQ_mult : Polynomial.rootMultiplicity T1X Q = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    exact hQT1
  rw [hQ_def]
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hfac_ne0 hQ_ne0)]
  rw [hmul_mult]
  rw [hQ_mult]

/-- **The complete divisor `div_aff(f) = C + ι(A) + T`, fully-split
case, as a literal `Divisor H` equality.** Six named points: the four
from `CAWitnessDivisor.lean` (`Ra1, Ra2, ιP1, ιP2`) plus `uCANew`'s two
named simple roots `PtT1, PtT2`, each fed through
`CAWitnessResidual.lean`'s `ordAt_eq_rootMultiplicity_of_uCANew_root`
with `m := 1` via `rootMultiplicity_uCANew_eq_one` above. -/
theorem divToPair_eq_C_add_iotaA_add_T_of_split
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
    (hU_evalP2 : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P2X ≠ 0)
    -- The residual roots, named.
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
    (hPtT2Y_ne : PtT2.Y ≠ 0) :
    divToPair (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X])
        ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) =
      single PtRa1 + single PtRa2 + single PtιP1 + single PtιP2 +
        single PtT1 + single PtT2 := by
  have h_bot : ∀ P : H.Point, pointIdeal P ≠ ⊥ := pointIdeal_ne_bot
  have hg_ne : toPair H (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  -- The four named-point `ordAt = 1` facts, reused verbatim from
  -- `CAWitnessDivisor.lean`'s proof (same shared setup, replayed here
  -- so this theorem is self-contained at the `Divisor H`-equality level
  -- with a six-point support instead of that file's four-point one).
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
  have hOrdRa1 : ordAt PtRa1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtRa1 (h_bot PtRa1) _ _
      (denomPolyCA Ra1X Ra2X P1X P2X) (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtRa1.X +
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
    · have hL3 := ordAt_A_eq_one_of_eval_ne_zero (H := H) hchar hsf PtRa1 (h_bot PtRa1)
        Ra1X hPtRa1X (hPtRa1Y ▸ hRa1Y_ne)
        (linX Ra2X) (linX P1X) (linX P2X)
        (by unfold linX; simpa using (sub_ne_zero.mpr h12))
        (by unfold linX; simpa using (sub_ne_zero.mpr h1P1))
        (by unfold linX; simpa using (sub_ne_zero.mpr h1P2))
      have heq : denomPolyCA Ra1X Ra2X P1X P2X =
          ((linX Ra1X * linX Ra2X) * linX P1X) * linX P2X := by
        unfold denomPolyCA linX; ring
      rw [heq]; exact hL3
    · simp only [hPtRa1X, eval_neg]
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
      rw [heq]; exact hL3
    · simp only [hPtRa2X, eval_neg]
      simpa using hU_evalRa2
  have hOrdιP1 : ordAt PtιP1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    apply ordAt_eq_one_of_old_point PtιP1 (h_bot PtιP1) _ _
      (denomPolyCA Ra1X Ra2X P1X P2X) (-uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y)
      hg_ne _ hAU hA_ne hU_ne _ _
    · show (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval PtιP1.X +
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
      rw [heq]; exact hL3
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
      rw [heq]; exact hL3
    · simp only [hPtιP2X, eval_neg]
      simpa using hU_evalP2
  -- The two named RESIDUAL-point `ordAt = 1` facts, via
  -- `CAWitnessResidual.lean` + `rootMultiplicity_uCANew_eq_one` above.
  have hmult1 : Polynomial.rootMultiplicity T1X
      (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T1X T2X hT1 hT2 hTne Q1 hQ1_def hQ1T1
  have hmult2 : Polynomial.rootMultiplicity T2X
      (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) = 1 :=
    rootMultiplicity_uCANew_eq_one _ hU_ne0 T2X T1X hT2 hT1 (Ne.symm hTne) Q2 hQ2_def hQ2T2
  have hOrdT1 : ordAt PtT1 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANew_root hchar hsf
      Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet h12 h1P1 h1P2 h2P1 h2P2 hPP
      hRa1_curve hRa2_curve hP1_curve hP2_curve PtT1 (h_bot PtT1) hU_ne0
      hAeval1 hPtT1Y hPtT1Y_ne 1 (hPtT1X ▸ hmult1)
    simpa using this
  have hOrdT2 : ordAt PtT2 (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) (1 : k[X]) = 1 := by
    have := ordAt_eq_rootMultiplicity_of_uCANew_root hchar hsf
      Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y hdet h12 h1P1 h1P2 h2P1 h2P2 hPP
      hRa1_curve hRa2_curve hP1_curve hP2_curve PtT2 (h_bot PtT2) hU_ne0
      hAeval2 hPtT2Y hPtT2Y_ne 1 (hPtT2X ▸ hmult2)
    simpa using this
  -- Pairwise distinctness of all six named points, as `H.Point` values.
  have hne_of_X : ∀ {Q1' Q2' : H.Point}, Q1'.X ≠ Q2'.X → Q1' ≠ Q2' :=
    fun hX heq => hX (heq ▸ rfl)
  have hRane' : PtRa1 ≠ PtRa2 := hne_of_X (hPtRa1X ▸ hPtRa2X ▸ h12)
  have hRa1ιP1' : PtRa1 ≠ PtιP1 := hne_of_X (hPtRa1X ▸ hPtιP1X ▸ h1P1)
  have hRa1ιP2' : PtRa1 ≠ PtιP2 := hne_of_X (hPtRa1X ▸ hPtιP2X ▸ h1P2)
  have hRa2ιP1' : PtRa2 ≠ PtιP1 := hne_of_X (hPtRa2X ▸ hPtιP1X ▸ h2P1)
  have hRa2ιP2' : PtRa2 ≠ PtιP2 := hne_of_X (hPtRa2X ▸ hPtιP2X ▸ h2P2)
  have hPP' : PtιP1 ≠ PtιP2 := hne_of_X (hPtιP1X ▸ hPtιP2X ▸ hPP)
  -- These four pairs (`Ra1/Ra2/ιP1/ιP2` vs `T1/T2`) go through the
  -- corresponding `hU_eval*` nonvanishing fact rather than `▸`-chains on
  -- `IsRoot`/`eval` terms (a `▸` rewrite here needs to unify under an
  -- `eval _ = 0` head after substituting an `x`-coordinate equality,
  -- which is exactly the kind of unification the heartbeat timeout hit
  -- above — spelled out as an explicit `by`-tactic proof instead, no
  -- term-mode rewriting of `hT1`/`hT2` needed at all).
  -- Convert `hT1`/`hT2` (`IsRoot`) to plain `eval = 0` facts ONCE, via
  -- the library lemma rather than relying on `exact`'s own defeq check
  -- to unfold `IsRoot` through `uCANew`'s heavy `/ₘ`-quotient body each
  -- time — that unification is exactly what blew the heartbeat budget
  -- above (repeated `exact hT1`/`exact hT2` against an `eval = 0` goal).
  have hT1eval : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval T1X = 0 :=
    Polynomial.IsRoot.eq_zero hT1
  have hT2eval : (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval T2X = 0 :=
    Polynomial.IsRoot.eq_zero hT2
  have hRa1T1' : PtRa1 ≠ PtT1 := by
    apply hne_of_X; rw [hPtRa1X, hPtT1X]
    intro h; apply hU_evalRa1; rw [← h] at hT1eval; exact hT1eval
  have hRa1T2' : PtRa1 ≠ PtT2 := by
    apply hne_of_X; rw [hPtRa1X, hPtT2X]
    intro h; apply hU_evalRa1; rw [← h] at hT2eval; exact hT2eval
  have hRa2T1' : PtRa2 ≠ PtT1 := by
    apply hne_of_X; rw [hPtRa2X, hPtT1X]
    intro h; apply hU_evalRa2; rw [← h] at hT1eval; exact hT1eval
  have hRa2T2' : PtRa2 ≠ PtT2 := by
    apply hne_of_X; rw [hPtRa2X, hPtT2X]
    intro h; apply hU_evalRa2; rw [← h] at hT2eval; exact hT2eval
  have hιP1T1' : PtιP1 ≠ PtT1 := by
    apply hne_of_X; rw [hPtιP1X, hPtT1X]
    intro h; apply hU_evalP1; rw [← h] at hT1eval; exact hT1eval
  have hιP1T2' : PtιP1 ≠ PtT2 := by
    apply hne_of_X; rw [hPtιP1X, hPtT2X]
    intro h; apply hU_evalP1; rw [← h] at hT2eval; exact hT2eval
  have hιP2T1' : PtιP2 ≠ PtT1 := by
    apply hne_of_X; rw [hPtιP2X, hPtT1X]
    intro h; apply hU_evalP2; rw [← h] at hT1eval; exact hT1eval
  have hιP2T2' : PtιP2 ≠ PtT2 := by
    apply hne_of_X; rw [hPtιP2X, hPtT2X]
    intro h; apply hU_evalP2; rw [← h] at hT2eval; exact hT2eval
  have hT12' : PtT1 ≠ PtT2 := hne_of_X (hPtT1X ▸ hPtT2X ▸ hTne)
  -- `coeffAt` of the six `single`-summands at a query point `P`, via one
  -- targeted `if_pos`/`if_neg` rewrite per disjunct — avoids a `simpa`
  -- searching a big lemma set against a freshly-unfolded 6-way
  -- `Finset.mem_insert`/`ite` goal simultaneously (that shape is what
  -- blew the heartbeat budget). After `subst`, the goal's six conditions
  -- are (in order) `P = PtRa1`, `P = PtRa2`, `P = PtιP1`, `P = PtιP2`,
  -- `P = PtT1`, `P = PtT2` — matching the sum's own summand order, `P`
  -- always on the LEFT of each `=`. 
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, coeffAt_single]
  
  by_cases hEqRa1 : P = PtRa1
  · rw [hEqRa1]  -- Changed from subst hEqRa1
    have hMem : PtRa1 ∈ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_pos rfl, if_neg hRane', if_neg hRa1ιP1',
      if_neg hRa1ιP2', if_neg hRa1T1', if_neg hRa1T2', hOrdRa1]
    ring
    
  by_cases hEqRa2 : P = PtRa2
  · rw [hEqRa2]
    have hMem : PtRa2 ∈ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hRane'), if_pos rfl, if_neg hRa2ιP1',
      if_neg hRa2ιP2', if_neg hRa2T1', if_neg hRa2T2', hOrdRa2]
    ring
    
  by_cases hEqιP1 : P = PtιP1
  · rw [hEqιP1]
    have hMem : PtιP1 ∈ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hRa1ιP1'), if_neg (Ne.symm hRa2ιP1'), if_pos rfl, if_neg hPP',
      if_neg hιP1T1', if_neg hιP1T2', hOrdιP1]
    ring
    
  by_cases hEqιP2 : P = PtιP2
  · rw [hEqιP2]
    have hMem : PtιP2 ∈ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hRa1ιP2'), if_neg (Ne.symm hRa2ιP2'), if_neg (Ne.symm hPP'), if_pos rfl,
      if_neg hιP2T1', if_neg hιP2T2', hOrdιP2]
    ring
    
  by_cases hEqT1 : P = PtT1
  · rw [hEqT1]
    have hMem : PtT1 ∈ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hRa1T1'), if_neg (Ne.symm hRa2T1'), if_neg (Ne.symm hιP1T1'),
      if_neg (Ne.symm hιP2T1'), if_pos rfl, if_neg hT12', hOrdT1]
    ring
    
  by_cases hEqT2 : P = PtT2
  · rw [hEqT2]
    have hMem : PtT2 ∈ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true, eq_self]
    rw [if_pos hMem, if_neg (Ne.symm hRa1T2'), if_neg (Ne.symm hRa2T2'), if_neg (Ne.symm hιP1T2'),
      if_neg (Ne.symm hιP2T2'), if_neg (Ne.symm hT12'), if_pos rfl, hOrdT2]
    ring
    
  · rw [if_neg hEqRa1, if_neg hEqRa2, if_neg hEqιP1,
      if_neg hEqιP2, if_neg hEqT1, if_neg hEqT2]
    have hnmemS : P ∉ ({PtRa1, PtRa2, PtιP1, PtιP2, PtT1, PtT2} : Finset H.Point) := by
      intro h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hEqRa1 rfl
      · exact hEqRa2 rfl
      · exact hEqιP1 rfl
      · exact hEqιP2 rfl
      · exact hEqT1 rfl
      · exact hEqT2 rfl
    rw [if_neg hnmemS]
    ring


end DecoupledSystem
end Genus2Lean
