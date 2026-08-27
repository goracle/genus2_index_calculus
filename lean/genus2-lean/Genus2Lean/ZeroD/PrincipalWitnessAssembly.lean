import Mathlib
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.OrdAtRootMultiplicityUnified
-- `OrdAtRootMultiplicityUnified.lean` no longer imports this file (see
-- `GeneralSharedRoot.lean`'s "flat-product identity" note for why) — this
-- import direction is now acyclic.

/-!
# Assembling `reducedClass_eq_of_isReduction'` from `PrincipalWitness.lean`'s
# lemma stack

Per `ROADMAP-principal-witness-assembly.md`'s "Recommended order for the
next pass". This file does the wiring the roadmap scoped precisely:

1. The exact factorization equation `Npoly4 = npoly4Lcm4 * uRS4General`
   (up to the leading-coefficient unit already tracked by `uRS4General`'s
   own definition) — needed as an actual EQUATION (`hAU` in the
   `PrincipalWitness.lean` lemma-stack sense), not just the divisibility
   facts `npoly4Lcm4_dvd_Npoly4`/`uRS4General_dvd_Npoly4` already on file.
2. The geometric-classification bridge: connecting "`P` is a root of one
   of `npoly4Lcm4`'s four sub-factors" to `Finset H.Point`-membership in
   `Sold := Sanchor ∪ {sa.P1, sa.P2}` with `ordAt P (-va-or-similar) 1 = 1`
   (roadmap step 3, "the one piece of genuinely new Lean content").
3. Assembly into `reducedClass_eq_of_isReduction'` itself.

Scoped, per the roadmap's explicit recommendation, to the SPLIT case only
(both `ua`/`uRS4General` have two rational roots) — the irreducible case
is a documented non-goal here, not attempted.
-/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

/-!
The following three wrappers are deliberately opaque (`def`, not `abbrev`).
The P1 point-composition theorem has an unusually large declaration type:
`ordAtFrac` is fed three large polynomial expressions, and elaborating the
same expressions repeatedly was enough to hit the default 200k heartbeat
limit at the theorem declaration itself, before the proof body was entered.
Keeping the constructions behind named constants makes the declaration cheap;
the definitions unfold where the proof explicitly asks for them.
-/

def witnessE4 (p : ℕ) [Fact (Nat.Prime p)]
    (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Polynomial (F p) :=
  Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

def witnessY4 (p : ℕ) [Fact (Nat.Prime p)]
    (P1 P2 : F p × F p) (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p) : Polynomial (F p) :=
  Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1

def witnessA4 (p : ℕ) [Fact (Nat.Prime p)]
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p) : Polynomial (F p) :=
  npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1

/-! ## Step 1: the exact factorization equation

`npoly4Lcm4_dvd_Npoly4` only gives divisibility; the `PrincipalWitness.lean`
lemma stack (lemma 7/8/13/13c) needs the actual equation `pairNorm H E Y =
A * U`. This section derives it from `curBeforeMonic4General`'s definition
(`Npoly4 /ₘ npoly4Lcm4`) via `divByMonic_eq_of_dvd_mul` (already used for
exactly this purpose inside `uRS4General_dvd_Npoly4`'s own proof — this
section just names the intermediate fact as its own reusable lemma, since
`uRS4General_dvd_Npoly4`'s proof only produces `curBeforeMonic4General ∣
Npoly4`-flavored intermediate `have`s, not the plain product equation with
`npoly4Lcm4` on the other side). -/

section ExactFactorization

variable (p : ℕ) [hp : Fact (Nat.Prime p)]
variable (c0 c1 c2 c3 c4 : F p) (P1 P2 : F p × F p)
variable (ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)

/-- **`Npoly4 = npoly4Lcm4 * curBeforeMonic4General`, exactly** (no unit
slack yet — that's absorbed in the next lemma once `uRS4General`'s
`leadingCoeff⁻¹`-rescaling is folded in). Direct read-off of
`npoly4Lcm4_dvd_Npoly4`'s witness (`⟨k,hk⟩`) composed with
`divByMonic_eq_of_dvd_mul` — this is the same pair of facts
`uRS4General_dvd_Npoly4`'s own proof already derives internally as
`hstep`/`hk`, just extracted here as its own named, reusable lemma instead
of staying buried inside that proof. -/
theorem Npoly4_eq_npoly4Lcm4_mul_curBeforeMonic4General
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1 *
        curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := by
  have hLdvd := npoly4Lcm4_dvd_Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
    hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
  have hLmonic := npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  obtain ⟨k, hk⟩ := hLdvd
  have hstep :
      curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = k := by
    simp only [curBeforeMonic4General]
    exact divByMonic_eq_of_dvd_mul hLmonic hk
  rw [hk, hstep]

/-- **`Npoly4 = npoly4Lcm4 * uRS4General`, exactly** — the equation the
`PrincipalWitness.lean` lemma stack's `hAU`-shaped hypotheses need. Folds
in `uRS4General`'s `leadingCoeff⁻¹`-rescaling relative to
`curBeforeMonic4General`: `curBeforeMonic4General = leadingCoeff •
uRS4General` (since `uRS4General := C leadingCoeff⁻¹ *
curBeforeMonic4General` and `leadingCoeff ≠ 0`), so multiplying
`Npoly4_eq_npoly4Lcm4_mul_curBeforeMonic4General`'s RHS by
`leadingCoeff⁻¹`/`leadingCoeff` and re-associating gives this unit-free
form directly, with `npoly4Lcm4` (not `npoly4Lcm4` scaled) as the exact
left factor. -/
theorem Npoly4_eq_npoly4Lcm4_mul_uRS4General
    (hne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1) :
    Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1 *
        (C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff *
          uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) := by
  have hbase := Npoly4_eq_npoly4Lcm4_mul_curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2
    ua0 ua1 va0 va1 u0 u1 v0 v1 hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
  set q := curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hq
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hne
  have hunfold : uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      C q.leadingCoeff⁻¹ * q := rfl
  rw [hbase, hunfold]
  -- Goal is now `npoly4Lcm4 * q = npoly4Lcm4 * (C leadingCoeff * (C leadingCoeff⁻¹ * q))`;
  -- reduce the RHS's scalar pair to `1` and cancel.
  have hscale : C q.leadingCoeff * (C q.leadingCoeff⁻¹ * q) = q := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hlc, map_one, one_mul]
  rw [hscale]

end ExactFactorization

/-! ## Step 3: the geometric-classification bridge (roadmap step 3 proper)

The genuinely new content this roadmap flags: connect "`P` is a simple
root of one of `npoly4Lcm4`'s four flat sub-factors" to `ordAt P
npoly4Lcm4 0 = 1` at the K=4/`H.Point` level, so that `PrincipalWitness.
lean`'s lemmas 14/15 (`ordAtFrac_eq_one_of_old_point`/
`ordAtFrac_neg_eq_one_of_new_point`, both of which take `ordAt P A 0 = 1`
as a literal hypothesis) can actually be invoked at each of the 6 named
points (`sa.P1`, `sa.P2`, `ua`'s two roots, `u_target`'s two roots).

Step 1/Step 2 above supply the two facts (`Npoly4 = npoly4Lcm4 *
uRS4General` exactly; `npoly4Lcm4 = unit * flat product` in the split
case) that make this step MECHANICAL once composed with `PrincipalWitness.
lean`'s `ordAt_A_eq_one_of_eval_ne_zero` (Layer 3) — but "mechanical" here
still means instantiating Layer 3 once per point, threading `H.Point`
membership in `Sanchor ∪ {sa.P1,sa.P2}` vs `S` through each case, and
handling the `IsUnit`-scalar on `npoly4Lcm4`'s flat-product identity
(Layer 3's own `ordAt`-of-a-product lemmas are stated for exact products,
not up-to-unit ones, so `ordAt P (unit • flat) 0 = ordAt P flat 0` needed
its own one-line justification — this was the "one care point" the
roadmap's own resolution flagged and deferred, and Part C below closes it).

ChatGPT's reply confirmed the architecture and closed both
open sub-questions:

- **Part A (outer lcm step)**: no hidden interaction between the two
  inner `lcm`s — the outer coprimality is the ONLY extra ingredient
  needed, already exactly what `npoly4Lcm4_eq_flat_product` (Step 2
  above) uses. Nothing further to do here.
- **Part B (quadratic splitting)**: the coefficient-expansion route
  (`quadratic_eq_mul_X_sub_C`, already proved above) is confirmed as the
  right choice for this local assembly, over the general `Polynomial.
  roots`-product route.
- **Part C (unit-scaling invariance of `ordAt`)**: confirmed the
  `ordAt (C c * A) (C c * B) = ordAt A B`-style lemma is the right idiom
  — and it's ALREADY ON FILE, not something to prove fresh:
  `ordAt_C_zero`/`ordAt_C_mul_eq` (`RiemannRochGenus2.lean`). No new
  lemma needed; Step 3 just composes these with Layer 3.
- **Part D (six-point case split)**: recommended NOT six nested
  `by_cases`, but a two-stage approach — a `support_cases` lemma turning
  `P ∈ S` into a 6-way named disjunction, called from a `by_cases P ∈ S`
  split, with the "elsewhere" branch closed by `simp` from the two
  `hsuppAnchor`/`hsupp`-style non-membership facts. Deferred to the
  actual assembly at `reducedClass_eq_of_isReduction'`'s call site
  (`AlphaLocusDegreeUniform.lean`), matching the roadmap's own scoping
  (this file stays about the `E,Y,A,U`-level bridge, not the
  `SampleTargetFromAlpha`-specific wiring).

This section writes Part C (the unit-scaled Layer 3, generalized per
ChatGPT's recommendation around a single designated factor rather than
`P1`-specific), the one piece of new Lean content Steps A-C leave to
write. Part D (the `Sold`/`Snew` case-split assembly) is left for
`AlphaLocusDegreeUniform.lean`'s own proof body, per the roadmap's
explicit scoping (`PrincipalWitness.lean`/`PrincipalWitnessAssembly.lean`
stay ignorant of `SampleTargetFromAlpha`). -/

section GeometricBridge

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- **Generalized Layer 3, unit-scaled, around a single designated linear
factor `X - C a`** — per ChatGPT's explicit recommendation, this
supersedes needing four separately hand-written re-associations of the
flat product: the caller reshapes whichever of the four sub-factors is
`X - C a` to the front via `ring`/`mul_comm`-style rewriting (cheap, since
`Polynomial (F p)` is commutative) BEFORE calling this lemma, so this
lemma itself only ever sees the shape `((linX a * F₁) * F₂) * F₃`
directly — no index parameter needed. Adds exactly one new ingredient
relative to `PrincipalWitness.lean`'s own `ordAt_A_eq_one_of_eval_ne_zero`
(Layer 3): the leading `C u` unit scalar coming from
`npoly4Lcm4_eq_flat_product`'s RHS, discharged via `ordAt_C_zero`/
`ordAt_C_mul_eq` (`RiemannRochGenus2.lean`, already proved, confirmed by
ChatGPT as the right idiom — no fresh valuation-theoretic argument
needed). -/
theorem ordAt_unit_mul_A_eq_one_of_eval_ne_zero
    [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (a u : k) (hu : u ≠ 0)
    (hPX : P.X = a) (hPY : P.Y ≠ 0)
    (F₁ F₂ F₃ : k[X])
    (hF₁_eval : F₁.eval a ≠ 0) (hF₂_eval : F₂.eval a ≠ 0) (hF₃_eval : F₃.eval a ≠ 0) :
    ordAt P (Polynomial.C u * (((linX a * F₁) * F₂) * F₃)) (0 : k[X]) = 1 := by
  have hflat : ordAt P (((linX a * F₁) * F₂) * F₃) (0 : k[X]) = 1 :=
    ordAt_A_eq_one_of_eval_ne_zero hchar hsf P h_bot a hPX hPY F₁ F₂ F₃
      hF₁_eval hF₂_eval hF₃_eval
  have hF₁ne : F₁ ≠ 0 := fun h => hF₁_eval (by rw [h]; simp)
  have hF₂ne : F₂ ≠ 0 := fun h => hF₂_eval (by rw [h]; simp)
  have hF₃ne : F₃ ≠ 0 := fun h => hF₃_eval (by rw [h]; simp)
  have hflatne : (((linX a * F₁) * F₂) * F₃ : k[X]) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (linX_ne_zero a) hF₁ne) hF₂ne) hF₃ne
  have hPQ : ¬ (((linX a * F₁) * F₂) * F₃ = 0 ∧ (0 : k[X]) = 0) :=
    fun h => hflatne h.1
  have hstep := ordAt_C_mul_eq u hu (((linX a * F₁) * F₂) * F₃) 0 hPQ P
  simpa using hstep.trans hflat

/-! ## Step 4 (Part D, partial): instantiating the geometric bridge at each
of the four `npoly4Lcm4` roots that live on a linear sub-factor
(`sa.P1`/`sa.P2`) — the two quadratic-factor roots (`ua`'s two roots,
`u_target`'s two roots) additionally need `quadratic_eq_mul_X_sub_C` (Step
2 above) to split the quadratic into its two linear factors first, and are
NOT attempted in this section; see the trailing status note below for why.

This section composes `npoly4Lcm4_eq_flat_product` (Step 2) with
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero` (Part C) to get `ordAt P
npoly4Lcm4 0 = 1` at `P := H.Point.mk P1.1 P1.2 h1` (the point built from
`sa.P1`'s own coordinates), given the four coprimality-flavored
eval-nonvanishing hypotheses `npoly4Lcm4_eq_flat_product` already needs.
This is genuinely new Lean content (not previously on file anywhere) — the
first concrete instantiation of the flat-product bridge at a real point,
rather than left at the polynomial level. -/

section GeometricInstantiation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `P1`'s own coordinates
is `1`**, in the fully-split/no-shared-root case. Composes
`npoly4Lcm4_eq_flat_product` (the flat-product identity, up to an explicit
unit) with `ordAt_unit_mul_A_eq_one_of_eval_ne_zero` (the unit-scaled Layer
3) — the caller supplies the point itself (`P`, with `hPX`/`hPY` pinning
its coordinates to `P1`) rather than this lemma constructing `H.Point.mk`
internally, since `H.Equation`'s own proof obligation is exactly
`P1_on_curve`-shaped data this lemma has no way to manufacture on its own. -/
theorem ordAt_npoly4Lcm4_eq_one_of_P1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = P1.1) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Reshape the flat product so `linX P1.1 = X - C P1.1` sits at the front,
  -- matching `ordAt_unit_mul_A_eq_one_of_eval_ne_zero`'s expected shape
  -- `C u * (((linX a * F₁) * F₂) * F₃)`.
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX P1.1 * (X - C P2.1 : Polynomial (F p))) *
        (X ^ 2 + C ua1 * X + C ua0)) * (X ^ 2 + C u1 * X + C u0) := by
    simp only [linX]; ring
  rw [hshape]
  -- The unit `npoly4Lcm4_eq_flat_product` names is a product of four
  -- `leadingCoeff⁻¹` terms; each is nonzero because each underlying
  -- polynomial (`npoly4LcmRaw`, the two inner gcds) is itself nonzero, being
  -- built from products/gcds of nonzero monics (`X - C _`/quadratics with
  -- leading coefficient `1 ≠ 0`) — hence each `leadingCoeff` is nonzero, so
  -- each `leadingCoeff⁻¹` is nonzero, so the product of the four is nonzero.
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C P2.1) (X ^ 2 + C ua1 * X + C ua0) (X ^ 2 + C u1 * X + C u0)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr h12)
    (by rw [hPX] at *; exact hP1ua)
    (by rw [hPX] at *; exact hP1target)

end GeometricInstantiation

section GeometricInstantiation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `P2`'s own coordinates
is `1`** — the exact mirror of `ordAt_npoly4Lcm4_eq_one_of_P1`, reshaping
the flat product so `linX P2.1` sits at the front instead of `linX P1.1`
(via `mul_comm`/`ring`, same as the `P1` case but with the two linear
factors swapped). Same composition (`npoly4Lcm4_eq_flat_product` +
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero`), same four `leadingCoeff⁻¹`
nonzero-unit argument, only the designated linear factor and the
correspondingly-reordered `eval`-nonvanishing hypotheses change. -/
theorem ordAt_npoly4Lcm4_eq_one_of_P2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = P2.1) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Reshape the flat product so `linX P2.1 = X - C P2.1` sits at the front,
  -- matching `ordAt_unit_mul_A_eq_one_of_eval_ne_zero`'s expected shape
  -- `C u * (((linX a * F₁) * F₂) * F₃)`.
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX P2.1 * (X - C P1.1 : Polynomial (F p))) *
        (X ^ 2 + C ua1 * X + C ua0)) * (X ^ 2 + C u1 * X + C u0) := by
    simp only [linX]; ring
  rw [hshape]
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C P1.1) (X ^ 2 + C ua1 * X + C ua0) (X ^ 2 + C u1 * X + C u0)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr h12.symm)
    (by rw [hPX] at *; exact hP2ua)
    (by rw [hPX] at *; exact hP2target)

end GeometricInstantiation

end GeometricBridge

section GeometricInstantiationQuadratic

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `Ra1`'s own
coordinates is `1`**, where `Ra1, Ra2` are `ua`'s two distinct roots over
`F p` (the split case; the irreducible-quadratic fork is out of scope,
per the roadmap's "scope to the split case first" decision). Same overall
composition as the `P1`/`P2` cases (`npoly4Lcm4_eq_flat_product` +
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero`), but with one extra step
first: `quadratic_eq_mul_X_sub_C` rewrites `ua` itself into
`(X-C Ra1)*(X-C Ra2)` before the flat product is reshaped. Since Layer
3's underlying lemma only has 3 "other-factor" slots (`F₁ F₂ F₃`) and
splitting `ua` leaves 4 remaining flat factors (`Ra2`, `P1`, `P2`,
`u_target`), `P2` and `u_target` are merged into a single `F₃ := (X-C
P2.1) * u_target`, discharged via `Polynomial.eval_mul`/`mul_ne_zero` —
`F₁`/`F₂`/`F₃` carry no shape restriction in Layer 3's statement, only
`eval a ≠ 0`, so this merge is free. -/
theorem ordAt_npoly4Lcm4_eq_one_of_Ra1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = Ra1) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa1P1 : Ra1 ≠ P1.1) (hRa1P2 : Ra1 ≠ P2.1)
    (hRa1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra1 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `ua` into its two named linear factors, then reshape so
  -- `linX Ra1` sits at the front and `(X-C P2.1) * u_target` is merged
  -- into a single `F₃` slot.
  have huaSplit : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) =
      (X - C Ra1) * (X - C Ra2) := by
    have hmonic : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg huaRoot1 huaRoot2 hRane
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX Ra1 * (X - C Ra2 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0)) := by
    simp only [linX]; rw [huaSplit]; ring
  rw [hshape]
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0)).eval Ra1 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hRa1P2) hRa1target
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C Ra2) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRane)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRa1P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic

section GeometricInstantiationQuadratic2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `Ra2`'s own
coordinates is `1`** — the exact mirror of `ordAt_npoly4Lcm4_eq_one_of_Ra1`,
with `Ra1`/`Ra2` swapped throughout: `linX Ra2` sits at the front, `(X-C
Ra1)` is the designated-factor's companion, and the "no shared root"
hypotheses are `Ra2`'s own versions. Same composition and same
`P2`/`u_target` merge-into-`F₃` trick as the `Ra1` case. -/
theorem ordAt_npoly4Lcm4_eq_one_of_Ra2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = Ra2) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa2P1 : Ra2 ≠ P1.1) (hRa2P2 : Ra2 ≠ P2.1)
    (hRa2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra2 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `ua` into its two named linear factors, then reshape so
  -- `linX Ra2` sits at the front and `(X-C P2.1) * u_target` is merged
  -- into a single `F₃` slot.
  have huaSplit : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) =
      (X - C Ra1) * (X - C Ra2) := by
    have hmonic : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg huaRoot1 huaRoot2 hRane
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX Ra2 * (X - C Ra1 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0)) := by
    simp only [linX]; rw [huaSplit]; ring
  rw [hshape]
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0)).eval Ra2 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hRa2P2) hRa2target
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C Ra1) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C u1 * X + C u0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRane.symm)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRa2P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic2

section GeometricInstantiationQuadratic3

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `R1`'s own
coordinates is `1`**, where `R1, R2` are `u_target`'s two distinct roots
over `F p` (split case, per the same scoping as `Ra1`/`Ra2`). Mirrors
`ordAt_npoly4Lcm4_eq_one_of_Ra1` with the roles of `ua` and `u_target`
swapped: `u_target` is the quadratic that gets split via
`quadratic_eq_mul_X_sub_C`, `linX R1` is the designated factor, `(X-C R2)`
its companion, and `ua`/`P2` are merged into `F₃` this time (the mirror
of `Ra1`'s `P2`/`u_target` merge). -/
theorem ordAt_npoly4Lcm4_eq_one_of_R1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = R1) (hPY : P.Y ≠ 0)
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
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `u_target` into its two named linear factors, then reshape so
  -- `linX R1` sits at the front and `(X-C P2.1) * ua` is merged into a
  -- single `F₃` slot.
  have htargetSplit : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) =
      (X - C R1) * (X - C R2) := by
    have hmonic : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg htargetRoot1 htargetRoot2 hRne
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX R1 * (X - C R2 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0)) := by
    simp only [linX]; rw [htargetSplit]; ring
  rw [hshape]
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C ua1 * X + C ua0)).eval R1 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hR1P2) hR1ua
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C R2) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRne)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hR1P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic3

section GeometricInstantiationQuadratic4

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

/-- **`ordAt` of `npoly4Lcm4` at the point built from `R2`'s own
coordinates is `1`** — the exact mirror of `ordAt_npoly4Lcm4_eq_one_of_R1`,
with `R1`/`R2` swapped throughout: `linX R2` sits at the front, `(X-C R1)`
is the designated-factor's companion, and the "no shared root" hypotheses
are `R2`'s own versions. Same composition and same `P2`/`ua`
merge-into-`F₃` trick as the `R1` case. **This is the sixth and final
point-instantiation Part D needs** — completes the `P1`/`P2`/`Ra1`/`Ra2`/
`R1`/`R2` set. -/
theorem ordAt_npoly4Lcm4_eq_one_of_R2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (P1 P2 : F p × F p) (ua0 ua1 u0 u1 : F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = R2) (hPY : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR2P1 : R2 ≠ P1.1) (hR2P2 : R2 ≠ P2.1)
    (hR2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R2 = 0) :
    ordAt P (npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) (0 : Polynomial (F p)) = 1 := by
  rw [npoly4Lcm4_eq_flat_product p P1 P2 ua0 ua1 u0 u1 h12 hne34 hnoroot34
    hP1ua hP1target hP2ua hP2target]
  -- Split `u_target` into its two named linear factors, then reshape so
  -- `linX R2` sits at the front and `(X-C P2.1) * ua` is merged into a
  -- single `F₃` slot.
  have htargetSplit : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) =
      (X - C R1) * (X - C R2) := by
    have hmonic : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
    have hdeg : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).natDegree = 2 := by
      compute_degree!
    exact quadratic_eq_mul_X_sub_C p hmonic hdeg htargetRoot1 htargetRoot2 hRne
  have hshape :
      (((X - C P1.1 : Polynomial (F p)) * (X - C P2.1)) *
        ((X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) * (X ^ 2 + C u1 * X + C u0))) =
      ((linX R2 * (X - C R1 : Polynomial (F p))) *
        (X - C P1.1)) * ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0)) := by
    simp only [linX]; rw [htargetSplit]; ring
  rw [hshape]
  have hune : ∀ q : Polynomial (F p), q.Monic → q ≠ 0 → q.leadingCoeff⁻¹ ≠ 0 := by
    intro q _ hq0
    exact inv_ne_zero ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hq0)
  have hm1 : (X - C P1.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm2 : (X - C P2.1 : Polynomial (F p)).Monic := Polynomial.monic_X_sub_C _
  have hm3 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).Monic := by monicity!
  have hm4 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by monicity!
  have hL12ne : (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm1.ne_zero hm2.ne_zero
  have hL34ne :
      (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => (EuclideanDomain.lcm_eq_zero_iff.mp h).elim hm3.ne_zero hm4.ne_zero
  have hGne :
      (EuclideanDomain.gcd
        (EuclideanDomain.lcm (X - C P1.1 : Polynomial (F p)) (X - C P2.1))
        (EuclideanDomain.lcm (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
          (X ^ 2 + C u1 * X + C u0))) ≠ 0 :=
    fun h => hL12ne (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd12ne : (EuclideanDomain.gcd (X - C P1.1 : Polynomial (F p)) (X - C P2.1)) ≠ 0 :=
    fun h => hm1.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgcd34ne :
      (EuclideanDomain.gcd (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p))
        (X ^ 2 + C u1 * X + C u0)) ≠ 0 :=
    fun h => hm3.ne_zero (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hrawne : (npoly4LcmRaw p P1 P2 ua0 ua1 u0 u1) ≠ 0 :=
    npoly4LcmRaw_ne_zero p P1 P2 ua0 ua1 u0 u1
  have hF3_eval :
      ((X - C P2.1 : Polynomial (F p)) * (X ^ 2 + C ua1 * X + C ua0)).eval R2 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr hR2P2) hR2ua
  exact ordAt_unit_mul_A_eq_one_of_eval_ne_zero hchar hsf P h_bot _ _
    (mul_ne_zero (mul_ne_zero (mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hrawne |> inv_ne_zero)
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hGne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd12ne |> inv_ne_zero))
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hgcd34ne |> inv_ne_zero))
    hPX hPY (X - C R1) (X - C P1.1) ((X - C P2.1) * (X ^ 2 + C ua1 * X + C ua0))
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hRne.symm)
    (by rw [hPX] at *; simpa using sub_ne_zero.mpr hR2P1)
    (by rw [hPX] at *; exact hF3_eval)

end GeometricInstantiationQuadratic4

/-! ## Step 4 (roadmap item 1): composing the `P1` case — the first of six
point compositions

This is the actual assembly the roadmap's "what is still missing" list
(item 1) asks for, done here for `P1` as a template for the remaining
five points (`P2`, `Ra1`, `Ra2`, `R1`, `R2`). Composes:
- Step 1's exact factorization (`Npoly4_eq_npoly4Lcm4_mul_uRS4General`),
  reshaped into `pairNorm H Epoly4 Ypoly4 = A * U` form (`hAU` in
  `PrincipalWitness.lean`'s sense) via `pairNorm_eq_of_eq_curvePoly` and
  `Npoly4`'s own definition;
- Part D's `ordAt_npoly4Lcm4_eq_one_of_P1` (`ordAt P npoly4Lcm4 0 = 1`);
- `AlphaReduce.lean`'s `Epoly4_eval_add_Y_mul_Ypoly4_eval_P1_eq_zero`
  (`g(P1) = 0`, added this project — see `ROADMAP-principal-witness-
  assembly.md`'s pass #8);
- `PrincipalWitness.lean`'s lemma 14 (`ordAtFrac_eq_one_of_old_point`).

**One new hypothesis, not on file anywhere before this pass, added
honestly rather than derived or hidden**: `hYP1_ne : (Ypoly4 ...).eval
P1.1 ≠ 0`. Lemma 14's `hg_ne_eval` (misleadingly named — it is actually
the `ḡ(P) ≠ 0` hypothesis, per that lemma's own docstring/proof) needs
`ḡ(P1) ≠ 0`. Since `g(P1) = 0` gives `E.eval P1.1 = -P1.2 * Y.eval P1.1`,
`ḡ(P1) = E.eval P1.1 - P1.2 * Y.eval P1.1 = -2 * P1.2 * Y.eval P1.1`,
which is nonzero (given `hchar : (2:F p) ≠ 0`) iff `P1.2 ≠ 0` (already
`hPY` in `ordAt_npoly4Lcm4_eq_one_of_P1`'s hypothesis list) AND
`Y.eval P1.1 ≠ 0`. The latter is NOT derivable from any hypothesis
currently on file (checked: `hgcd`'s coprimality is between `Ypoly4` and
`uRS4General`, the RESIDUAL quadratic — not `npoly4Lcm4`/`A`, the OLD
factor `P1` is a root of; no lemma anywhere states or implies `Ypoly4`
doesn't vanish at `P1.X`). This is a genuine mathematical gap, not a
notational one — stating it as an explicit hypothesis here (rather than
guessing a derivation) matches this project's "don't over-assume, but
state what's actually needed" discipline, same as `hP1ua`/`hP1target`
etc. already do for the geometric-distinctness side. **Flagged for a
ChatGPT consult or direct check**: is `Ypoly4.eval P1.1 ≠ 0` actually true
unconditionally (geometrically: does the interpolating `Y`-component ever
vanish at one of the two points it's built to pass through, for generic
input data)?  or does it need a further nondegeneracy hypothesis on
`(P1,P2,ua,u)` beyond `MatrixNondegenerate4`? Not resolved this pass. -/

section PointCompositionP1

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `P1` case of the pointwise `ordAtFrac`-assembly:** the old-point
factor `A = npoly4Lcm4` has order one at `P1`, and the residual factor
`U` is therefore the denominator in `ordAtFrac P E Y U`. This is the exact
conclusion provided by `ordAtFrac_eq_one_of_old_point`. First of six point
compositions the assembly needs (see module-level status note above for the
other five, not yet done). -/
theorem ordAtFrac_eq_one_of_P1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (P : H.Point) (hPX : P.X = P1.1) (hPY : P.Y = P1.2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  -- `hNpoly4_eq₀`: proved BEFORE the `set`s above are introduced, and by
  -- `rfl` alone (this is definitional — `Npoly4`'s `def` body IS
  -- `Epoly4^2 - curvePoly*Ypoly4^2`, verbatim) rather than `unfold ...;
  -- ring`, which was timing out: with `E,Y,A,lc,U` all sitting in context
  -- as `set`-local-defs, `unfold`/`ring`'s `whnf` calls had to thread
  -- through all of them, not just `Npoly4`, to normalize a degree-≤8
  -- polynomial identity. Proving this cheap fact in terms of the plain
  -- `Epoly4 p ...`/`Ypoly4 p ...` names (no `E`/`Y` abbreviations yet)
  -- keeps the `rfl` local to `Npoly4`'s own unfolding.
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  -- `hAU`: `pairNorm H E Y = A * U`, from Step 1's factorization plus
  -- `Npoly4`'s definition and `hf`.
  have hAU : pairNorm H E Y = A * U := by
    -- `hfact : Npoly4 = npoly4Lcm4 * (C leadingCoeff * uRS4General)`, and
    -- `Npoly4` unfolds (definitionally) to `E^2 - curvePoly*Y^2`; `pairNorm
    -- H E Y` unfolds (via `hf`) to `E^2 - Y^2*curvePoly` — the same value,
    -- differing only by `mul_comm`, so `linear_combination` (not `rw`,
    -- which would need exact syntactic matches on both sides) closes the
    -- gap directly from the two component facts.
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    -- Orient the local set-equalities backwards.  `hfact` already contains
    -- the fully expanded definitions on its right-hand side, so rewriting
    -- forwards cannot see `A`, while rewriting backwards exposes `A * U`
    -- without unfolding any of the large polynomial definitions.
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  -- `A ≠ 0`, `U ≠ 0` as ring elements (`toPair H · 0`).
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_P1 p hchar hsf P1 P2 ua0 ua1 u0 u1
      P h_bot hPX hPY_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  -- `g(P1) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYP1_ne`) `hg_ne_eval` (really `ḡ(P1) ≠ 0`).
  have hgP1_eval : E.eval P1.1 + P1.2 * Y.eval P1.1 = 0 := by
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_Y_mul_Ypoly4_eval_P1_eq_zero p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA)
  -- `ḡ(P1) ≠ 0`: since `g(P1) = 0` gives `E(P1) = -P1.2 * Y(P1)`,
  -- we have `ḡ(P1) = E(P1) - Y(P1)*P1.2 = -2*Y(P1)*P1.2 ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, hPY, Polynomial.eval_neg]
    have hYZ : Y.eval P1.1 * P1.2 ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYP1_ne) (hPY ▸ hPY_ne)
    have hgP1_eval' : E.eval P1.1 + Y.eval P1.1 * P1.2 = 0 := by
      linear_combination hgP1_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval P1.1 * P1.2) = 0 := by
      linear_combination hgP1_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP1_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The bare `ordAt P E Y = 1` fact at `P1`** (`PrincipalWitness.lean`'s
lemma 16, `ordAt_eq_one_of_old_point`), as distinct from
`ordAtFrac_eq_one_of_P1`'s `ordAtFrac`-of-`h` conclusion just above —
needed for `ROADMAP-principal-witness-assembly.md`'s step 1
(`div_aff(g) = A+C+T` as a literal `divToPair`-value `Divisor H`
equality, which needs `ordAt P E Y` itself, not `h`'s valuation). Exact
copy of `ordAtFrac_eq_one_of_P1`'s derivation up to `hA_ord`/`hg_ne`/
`hgbar_eval`, plus one new hypothesis `hU_eval : U.eval P1.1 ≠ 0` (the
direct analogue of `ordAtFrac_eq_neg_one_of_uRS4General_root`'s `hUfac`
for this side — `hgcd`'s coprimality is between `Ypoly4`/`uRS4General`,
unrelated to whether `uRS4General` vanishes at `P1.1`, so this is a
genuinely separate fact, not derivable from anything already on file). -/
theorem ordAt_eq_one_of_P1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (P : H.Point) (hPX : P.X = P1.1) (hPY : P.Y = P1.2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hU_eval : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAt P E Y = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_P1 p hchar hsf P1 P2 ua0 ua1 u0 u1
      P h_bot hPX hPY_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  have hgP1_eval : E.eval P1.1 + P1.2 * Y.eval P1.1 = 0 := by
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_Y_mul_Ypoly4_eval_P1_eq_zero p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, hPY, Polynomial.eval_neg]
    have hYZ : Y.eval P1.1 * P1.2 ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYP1_ne) (hPY ▸ hPY_ne)
    have hgP1_eval' : E.eval P1.1 + Y.eval P1.1 * P1.2 = 0 := by
      linear_combination hgP1_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval P1.1 * P1.2) = 0 := by
      linear_combination hgP1_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP1_ne
    rw [← hY_def, hY0]
    simp
  have hU_eval' : U.eval P.X ≠ 0 := by
    rw [hPX, hU_def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne) hU_eval
  exact ordAt_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord hU_eval'

end PointCompositionP1

section PointCompositionP2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `P2` case of the pointwise `ordAtFrac`-assembly**, the exact mirror
of `ordAtFrac_eq_one_of_P1` with `P1`/`P2` swapped throughout: same
derivation of `hAU`/`hA_ne`/`hU_ne`/`hA_ord`/`hg_ne`/`hgbar_eval`, only the
designated point's own coordinates and `Epoly4_eval_add_Y_mul_Ypoly4_eval_
P2_eq_zero` (in place of the `_P1_` version) change. Second of six point
compositions the assembly needs. Named `_full` to avoid clashing with the
abstract `ordAtFrac_eq_one_of_P2` wrapper below (`PointwiseOrdAtFracAssembly`
section), which takes `hA_ord`/`hzero` as bare hypotheses instead of
deriving them from the raw interpolation data as this theorem does. -/
theorem ordAtFrac_eq_one_of_P2_full
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (P : H.Point) (hPX : P.X = P2.1) (hPY : P.Y = P2.2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D — the `P2` geometric instantiation.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_P2 p hchar hsf P1 P2 ua0 ua1 u0 u1
      P h_bot hPX hPY_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  -- `g(P2) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYP2_ne`) `hg_ne_eval` (really `ḡ(P2) ≠ 0`).
  have hgP2_eval : E.eval P2.1 + P2.2 * Y.eval P2.1 = 0 := by
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_Y_mul_Ypoly4_eval_P2_eq_zero p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA)
  -- `ḡ(P2) ≠ 0`: since `g(P2) = 0` gives `E(P2) = -P2.2 * Y(P2)`,
  -- we have `ḡ(P2) = E(P2) - Y(P2)*P2.2 = -2*Y(P2)*P2.2 ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, hPY, Polynomial.eval_neg]
    have hYZ : Y.eval P2.1 * P2.2 ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYP2_ne) (hPY ▸ hPY_ne)
    have hgP2_eval' : E.eval P2.1 + Y.eval P2.1 * P2.2 = 0 := by
      linear_combination hgP2_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval P2.1 * P2.2) = 0 := by
      linear_combination hgP2_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP2_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The bare `ordAt P E Y = 1` fact at `P2`** (`PrincipalWitness.lean`'s
lemma 16, `ordAt_eq_one_of_old_point`), the `P2` mirror of
`ordAt_eq_one_of_P1`, as distinct from `ordAtFrac_eq_one_of_P2_full`'s
`ordAtFrac`-of-`h` conclusion just above — needed for
`ROADMAP-principal-witness-assembly.md`'s step 1 (`div_aff(g) = A+C+T` as
a literal `divToPair`-value `Divisor H` equality, which needs
`ordAt P E Y` itself, not `h`'s valuation). Exact copy of
`ordAtFrac_eq_one_of_P2_full`'s derivation up to `hA_ord`/`hg_ne`/
`hgbar_eval`, plus one new hypothesis `hU_eval : U.eval P2.1 ≠ 0` (the
direct analogue of `ordAt_eq_one_of_P1`'s own `hU_eval` for this point). -/
theorem ordAt_eq_one_of_P2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (P : H.Point) (hPX : P.X = P2.1) (hPY : P.Y = P2.2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hU_eval : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAt P E Y = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_P2 p hchar hsf P1 P2 ua0 ua1 u0 u1
      P h_bot hPX hPY_ne h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  have hgP2_eval : E.eval P2.1 + P2.2 * Y.eval P2.1 = 0 := by
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_Y_mul_Ypoly4_eval_P2_eq_zero p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hA)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, hPY, Polynomial.eval_neg]
    have hYZ : Y.eval P2.1 * P2.2 ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYP2_ne) (hPY ▸ hPY_ne)
    have hgP2_eval' : E.eval P2.1 + Y.eval P2.1 * P2.2 = 0 := by
      linear_combination hgP2_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval P2.1 * P2.2) = 0 := by
      linear_combination hgP2_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP2_ne
    rw [← hY_def, hY0]
    simp
  have hU_eval' : U.eval P.X ≠ 0 := by
    rw [hPX, hU_def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne) hU_eval
  exact ordAt_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord hU_eval'

end PointCompositionP2

section PointCompositionRa1

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `Ra1` case of the pointwise `ordAtFrac`-assembly**, third of six
point compositions. Same overall shape as `ordAtFrac_eq_one_of_P1`/
`_P2_full` (lemma 14, `A := npoly4Lcm4` via `Npoly4_eq_npoly4Lcm4_mul_
uRS4General`, `hA_ord` via the already-proved `ordAt_npoly4Lcm4_eq_one_of_
Ra1`), but the `g(point) = 0` input is now the root-evaluation form
`Epoly4_eval_add_va_eval_mul_Ypoly4_eval_eq_zero_of_root_ua` (pass #10,
`AlphaReduce.lean`) rather than a named point's own coordinate: `Ra1` is a
root of `u_a`, not one of the interpolation points `P1`/`P2`, so its
curve `y`-value is `va.eval Ra1 := (C va1 * X + C va0).eval Ra1`
(supplied via `hMumfordUa`/`huaRoot1` rather than a free `P2.2`-style
hypothesis) — `hPY` here fixes `P.Y` to exactly that value instead of a
named point's second coordinate. -/
theorem ordAtFrac_eq_one_of_Ra1_full
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (hPX : P.X = Ra1)
    (hPY : P.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra1) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa1P1 : Ra1 ≠ P1.1) (hRa1P2 : Ra1 ≠ P2.1)
    (hRa1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYRa1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D — the `Ra1` geometric instantiation.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_Ra1 p hchar hsf P1 P2 ua0 ua1 u0 u1
      Ra1 Ra2 huaRoot1 huaRoot2 hRane P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRa1P1 hRa1P2 hRa1target
  -- `g(Ra1) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYRa1_ne`) `hg_ne_eval` (really `ḡ(Ra1) ≠ 0`).
  have hgRa1_eval : E.eval Ra1 + P.Y * Y.eval Ra1 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_va_eval_mul_Ypoly4_eval_eq_zero_of_root_ua p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA Ra1 huaRoot1)
  -- `ḡ(Ra1) ≠ 0`: since `g(Ra1) = 0` gives `E(Ra1) = -P.Y * Y(Ra1)`,
  -- we have `ḡ(Ra1) = E(Ra1) - Y(Ra1)*P.Y = -2*Y(Ra1)*P.Y ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval Ra1 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYRa1_ne) hPY_ne
    have hgRa1_eval' : E.eval Ra1 + Y.eval Ra1 * P.Y = 0 := by
      linear_combination hgRa1_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval Ra1 * P.Y) = 0 := by
      linear_combination hgRa1_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYRa1_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The bare `ordAt P E Y = 1` fact at `Ra1`** (`PrincipalWitness.lean`'s
lemma 16, `ordAt_eq_one_of_old_point`), the `Ra1` mirror of
`ordAt_eq_one_of_P1`/`_P2`, as distinct from `ordAtFrac_eq_one_of_Ra1_full`'s
`ordAtFrac`-of-`h` conclusion just above — needed for
`ROADMAP-principal-witness-assembly.md`'s step 1 (`div_aff(g) = A+C+T`).
Exact copy of `ordAtFrac_eq_one_of_Ra1_full`'s derivation up to `hA_ord`/
`hg_ne`/`hgbar_eval`, plus one new hypothesis `hU_eval : U.eval Ra1 ≠ 0`
(the direct analogue of `ordAt_eq_one_of_P1`/`_P2`'s own `hU_eval` for
this point). -/
theorem ordAt_eq_one_of_Ra1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (hPX : P.X = Ra1)
    (hPY : P.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra1) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa1P1 : Ra1 ≠ P1.1) (hRa1P2 : Ra1 ≠ P2.1)
    (hRa1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYRa1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra1 ≠ 0)
    (hU_eval : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAt P E Y = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_Ra1 p hchar hsf P1 P2 ua0 ua1 u0 u1
      Ra1 Ra2 huaRoot1 huaRoot2 hRane P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRa1P1 hRa1P2 hRa1target
  have hgRa1_eval : E.eval Ra1 + P.Y * Y.eval Ra1 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_va_eval_mul_Ypoly4_eval_eq_zero_of_root_ua p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA Ra1 huaRoot1)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval Ra1 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYRa1_ne) hPY_ne
    have hgRa1_eval' : E.eval Ra1 + Y.eval Ra1 * P.Y = 0 := by
      linear_combination hgRa1_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval Ra1 * P.Y) = 0 := by
      linear_combination hgRa1_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYRa1_ne
    rw [← hY_def, hY0]
    simp
  have hU_eval' : U.eval P.X ≠ 0 := by
    rw [hPX, hU_def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne) hU_eval
  exact ordAt_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord hU_eval'

end PointCompositionRa1

section PointCompositionRa2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `Ra2` case of the pointwise `ordAtFrac`-assembly**, fourth of six
point compositions — the exact mirror of `ordAtFrac_eq_one_of_Ra1_full`
with `Ra1`/`Ra2` swapped throughout: same use of
`Epoly4_eval_add_va_eval_mul_Ypoly4_eval_eq_zero_of_root_ua` (now at root
`Ra2`, via `huaRoot2` instead of `huaRoot1`) and
`ordAt_npoly4Lcm4_eq_one_of_Ra2` (in place of `_Ra1`) for `hA_ord`. -/
theorem ordAtFrac_eq_one_of_Ra2_full
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (hPX : P.X = Ra2)
    (hPY : P.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa2P1 : Ra2 ≠ P1.1) (hRa2P2 : Ra2 ≠ P2.1)
    (hRa2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra2 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYRa2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra2 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D — the `Ra2` geometric instantiation.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_Ra2 p hchar hsf P1 P2 ua0 ua1 u0 u1
      Ra1 Ra2 huaRoot1 huaRoot2 hRane P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRa2P1 hRa2P2 hRa2target
  -- `g(Ra2) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYRa2_ne`) `hg_ne_eval` (really `ḡ(Ra2) ≠ 0`).
  have hgRa2_eval : E.eval Ra2 + P.Y * Y.eval Ra2 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_va_eval_mul_Ypoly4_eval_eq_zero_of_root_ua p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA Ra2 huaRoot2)
  -- `ḡ(Ra2) ≠ 0`: since `g(Ra2) = 0` gives `E(Ra2) = -P.Y * Y(Ra2)`,
  -- we have `ḡ(Ra2) = E(Ra2) - Y(Ra2)*P.Y = -2*Y(Ra2)*P.Y ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval Ra2 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYRa2_ne) hPY_ne
    have hgRa2_eval' : E.eval Ra2 + Y.eval Ra2 * P.Y = 0 := by
      linear_combination hgRa2_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval Ra2 * P.Y) = 0 := by
      linear_combination hgRa2_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYRa2_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The bare `ordAt P E Y = 1` fact at `Ra2`** (`PrincipalWitness.lean`'s
lemma 16, `ordAt_eq_one_of_old_point`), the `Ra2` mirror of
`ordAt_eq_one_of_Ra1`, as distinct from `ordAtFrac_eq_one_of_Ra2_full`'s
`ordAtFrac`-of-`h` conclusion just above — needed for
`ROADMAP-principal-witness-assembly.md`'s step 1 (`div_aff(g) = A+C+T`).
Exact copy of `ordAtFrac_eq_one_of_Ra2_full`'s derivation up to `hA_ord`/
`hg_ne`/`hgbar_eval`, plus one new hypothesis `hU_eval : U.eval Ra2 ≠ 0`. -/
theorem ordAt_eq_one_of_Ra2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra1 Ra2 : F p)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (P : H.Point) (hPX : P.X = Ra2)
    (hPY : P.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRa2P1 : Ra2 ≠ P1.1) (hRa2P2 : Ra2 ≠ P2.1)
    (hRa2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra2 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYRa2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra2 ≠ 0)
    (hU_eval : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra2 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAt P E Y = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_Ra2 p hchar hsf P1 P2 ua0 ua1 u0 u1
      Ra1 Ra2 huaRoot1 huaRoot2 hRane P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRa2P1 hRa2P2 hRa2target
  have hgRa2_eval : E.eval Ra2 + P.Y * Y.eval Ra2 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_va_eval_mul_Ypoly4_eval_eq_zero_of_root_ua p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA Ra2 huaRoot2)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval Ra2 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYRa2_ne) hPY_ne
    have hgRa2_eval' : E.eval Ra2 + Y.eval Ra2 * P.Y = 0 := by
      linear_combination hgRa2_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval Ra2 * P.Y) = 0 := by
      linear_combination hgRa2_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYRa2_ne
    rw [← hY_def, hY0]
    simp
  have hU_eval' : U.eval P.X ≠ 0 := by
    rw [hPX, hU_def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne) hU_eval
  exact ordAt_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord hU_eval'

end PointCompositionRa2

section PointCompositionR1

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `R1` case of the pointwise `ordAtFrac`-assembly**, fifth of six
point compositions. `R1, R2` are `u_target`'s two roots — confirmed by
direct read of `ordAt_npoly4Lcm4_eq_one_of_R1`/`_R2`
(`GeometricInstantiationQuadratic3`/`4` above) that these are old-support
points (`ordAt P npoly4Lcm4 0 = 1`, exactly the same shape as `Ra1`/`Ra2`),
NOT the residual pair `uRS4General`'s own roots — `npoly4LcmRaw`'s
definition literally bakes `u_target` into the same outer `lcm` as `ua`,
so `u_target`'s roots are zeros of `npoly4Lcm4` by construction. This
matches `CHATGPT-LOG-principal-witness-assembly.md`'s own naming (`R1,R2`
:= "each of `u_target`'s two roots") and pass #5's "old vs residual"
correction — the class-level `Snew`/`ι(R_i)` split is a SEPARATE, later
bookkeeping step, not a fact about `g`'s own divisor at `R1` itself. So
this theorem is `ordAtFrac_eq_one_of_Ra1_full`'s exact mirror (lemma 14
via `ordAtFrac_eq_one_of_old_point`, `hA_ord` via
`ordAt_npoly4Lcm4_eq_one_of_R1`), with `ua`/`va`/`Ra1`/`Ra2` swapped for
`u_target`/`v`/`R1`/`R2` throughout, using
`Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u` (the
target-`u` mirror of the `ua`-root theorem, already on file in
`AlphaReduce.lean`) in place of the `_of_root_ua` version. -/
theorem ordAtFrac_eq_one_of_R1_full
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (hPX : P.X = R1)
    (hPY : P.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R1) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR1P1 : R1 ≠ P1.1) (hR1P2 : R1 ≠ P2.1)
    (hR1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYR1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D — the `R1` geometric instantiation.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_R1 p hchar hsf P1 P2 ua0 ua1 u0 u1
      R1 R2 htargetRoot1 htargetRoot2 hRne P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hR1P1 hR1P2 hR1ua
  -- `g(R1) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYR1_ne`) `hg_ne_eval` (really `ḡ(R1) ≠ 0`).
  have hgR1_eval : E.eval R1 + P.Y * Y.eval R1 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA R1 htargetRoot1)
  -- `ḡ(R1) ≠ 0`: since `g(R1) = 0` gives `E(R1) = -P.Y * Y(R1)`,
  -- we have `ḡ(R1) = E(R1) - Y(R1)*P.Y = -2*Y(R1)*P.Y ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval R1 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYR1_ne) hPY_ne
    have hgR1_eval' : E.eval R1 + Y.eval R1 * P.Y = 0 := by
      linear_combination hgR1_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval R1 * P.Y) = 0 := by
      linear_combination hgR1_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYR1_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The bare `ordAt P E Y = 1` fact at `R1`** (`PrincipalWitness.lean`'s
lemma 16, `ordAt_eq_one_of_old_point`), the `R1` mirror of
`ordAt_eq_one_of_Ra1`/`_Ra2`, as distinct from `ordAtFrac_eq_one_of_R1_full`'s
`ordAtFrac`-of-`h` conclusion just above — needed for
`ROADMAP-principal-witness-assembly.md`'s step 1 (`div_aff(g) = A+C+T`,
where `T := [R1]+[R2]` is `u_target`'s own root pair, per that theorem's
docstring — `R1`/`R2` are old-support points, NOT `uRS4General`'s
residual roots). Exact copy of `ordAtFrac_eq_one_of_R1_full`'s derivation
up to `hA_ord`/`hg_ne`/`hgbar_eval`, plus one new hypothesis
`hU_eval : U.eval R1 ≠ 0`. -/
theorem ordAt_eq_one_of_R1
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (hPX : P.X = R1)
    (hPY : P.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R1) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR1P1 : R1 ≠ P1.1) (hR1P2 : R1 ≠ P2.1)
    (hR1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R1 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYR1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (hU_eval : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAt P E Y = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_R1 p hchar hsf P1 P2 ua0 ua1 u0 u1
      R1 R2 htargetRoot1 htargetRoot2 hRne P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hR1P1 hR1P2 hR1ua
  have hgR1_eval : E.eval R1 + P.Y * Y.eval R1 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA R1 htargetRoot1)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval R1 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYR1_ne) hPY_ne
    have hgR1_eval' : E.eval R1 + Y.eval R1 * P.Y = 0 := by
      linear_combination hgR1_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval R1 * P.Y) = 0 := by
      linear_combination hgR1_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYR1_ne
    rw [← hY_def, hY0]
    simp
  have hU_eval' : U.eval P.X ≠ 0 := by
    rw [hPX, hU_def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne) hU_eval
  exact ordAt_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord hU_eval'

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `R1 = R2` repeated-root case of the pointwise `ordAtFrac`-assembly**
— the mirror of `ordAtFrac_eq_one_of_R1_full` for the case
`OrdAtRootMultiplicityUnified.lean` flags as previously unreachable: when
`u_target`'s two roots coincide (`u_target = (X - C R)^2`), the old point
over `R` contributes coefficient `2`, not `1`, to `h`'s divisor. Exact
copy of `ordAtFrac_eq_one_of_R1_full`'s derivation with `hA_ord` supplied
by `ordAt_npoly4Lcm4_eq_two_of_R1_eq_R2_rootMultiplicity` instead of
`ordAt_npoly4Lcm4_eq_one_of_R1`, and the final step routed through
`ordAtFrac_eq_two_of_old_point` instead of lemma 14. No `hRne`/`R2` in the
signature — `htargetSq` alone pins down the repeated root, matching how
`OrdAtRootMultiplicityUnified.lean`'s own repeated-root lemmas drop
`hRne`/`R2` in favor of `htargetSq`. -/
theorem ordAtFrac_eq_two_of_R1_eq_R2_full
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (R : F p)
    (htargetSq : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) = (X - C R) ^ 2)
    (P : H.Point) (hPX : P.X = R)
    (hPY : P.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRP1 : R ≠ P1.1) (hRP2 : R ≠ P2.1)
    (hRua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYR_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 2 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have htargetRoot : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval R = 0 := by
    rw [htargetSq]; simp
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 2 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_two_of_R1_eq_R2_rootMultiplicity p hchar P1 P2 ua0 ua1 u0 u1 R
      htargetSq P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRP1 hRP2 hRua
  have hgR_eval : E.eval R + P.Y * Y.eval R = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA R htargetRoot)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval R * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYR_ne) hPY_ne
    have hgR_eval' : E.eval R + Y.eval R * P.Y = 0 := by
      linear_combination hgR_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval R * P.Y) = 0 := by
      linear_combination hgR_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYR_ne
    rw [← hY_def, hY0]
    simp
  exact ordAtFrac_eq_two_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The bare `ordAt P E Y = 2` fact at the `R1 = R2` repeated root** —
the repeated-root mirror of `ordAt_eq_one_of_R1`, needed for the same
`div_aff(g) = A + C + T` step-1 bookkeeping in the case where `T`'s two
named points collapse to a single point with multiplicity `2`. Exact copy
of `ordAtFrac_eq_two_of_R1_eq_R2_full`'s derivation up to `hA_ord`/`hg_ne`/
`hgbar_eval`, plus `hU_eval : U.eval R ≠ 0`, routed through
`ordAt_eq_two_of_old_point` instead of `ordAtFrac_eq_two_of_old_point`. -/
theorem ordAt_eq_two_of_R1_eq_R2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (R : F p)
    (htargetSq : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)) = (X - C R) ^ 2)
    (P : H.Point) (hPX : P.X = R)
    (hPY : P.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hRP1 : R ≠ P1.1) (hRP2 : R ≠ P2.1)
    (hRua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYR_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R ≠ 0)
    (hU_eval : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAt P E Y = 2 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have htargetRoot : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval R = 0 := by
    rw [htargetSq]; simp
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 2 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_two_of_R1_eq_R2_rootMultiplicity p hchar P1 P2 ua0 ua1 u0 u1 R
      htargetSq P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hRP1 hRP2 hRua
  have hgR_eval : E.eval R + P.Y * Y.eval R = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA R htargetRoot)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval R * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYR_ne) hPY_ne
    have hgR_eval' : E.eval R + Y.eval R * P.Y = 0 := by
      linear_combination hgR_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval R * P.Y) = 0 := by
      linear_combination hgR_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYR_ne
    rw [← hY_def, hY0]
    simp
  have hU_eval' : U.eval P.X ≠ 0 := by
    rw [hPX, hU_def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne) hU_eval
  exact ordAt_eq_two_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord hU_eval'

end PointCompositionR1

section PointCompositionR2

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The `R2` case of the pointwise `ordAtFrac`-assembly**, sixth and
last of six point compositions — the exact mirror of
`ordAtFrac_eq_one_of_R1_full` with `R1`/`R2` swapped throughout: same use
of `Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u` (now at root
`R2`, via `htargetRoot2` instead of `htargetRoot1`) and
`ordAt_npoly4Lcm4_eq_one_of_R2` (in place of `_R1`) for `hA_ord`. -/
theorem ordAtFrac_eq_one_of_R2_full
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (hPX : P.X = R2)
    (hPY : P.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR2P1 : R2 ≠ P1.1) (hR2P2 : R2 ≠ P2.1)
    (hR2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R2 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYR2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAtFrac P E Y
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  -- `ordAt P A 0 = 1`, from Part D — the `R2` geometric instantiation.
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_R2 p hchar hsf P1 P2 ua0 ua1 u0 u1
      R1 R2 htargetRoot1 htargetRoot2 hRne P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hR2P1 hR2P2 hR2ua
  -- `g(R2) = 0`, giving both `hg_ne` (as a ring element) and (combined
  -- with `hYR2_ne`) `hg_ne_eval` (really `ḡ(R2) ≠ 0`).
  have hgR2_eval : E.eval R2 + P.Y * Y.eval R2 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA R2 htargetRoot2)
  -- `ḡ(R2) ≠ 0`: since `g(R2) = 0` gives `E(R2) = -P.Y * Y(R2)`,
  -- we have `ḡ(R2) = E(R2) - Y(R2)*P.Y = -2*Y(R2)*P.Y ≠ 0`.
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval R2 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYR2_ne) hPY_ne
    have hgR2_eval' : E.eval R2 + Y.eval R2 * P.Y = 0 := by
      linear_combination hgR2_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval R2 * P.Y) = 0 := by
      linear_combination hgR2_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ

  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYR2_ne
    rw [← hY_def, hY0]
    simp

  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- Large polynomial whnf from `set`-introduced abbreviations in the proof body.
/-- **The bare `ordAt P E Y = 1` fact at `R2`** (`PrincipalWitness.lean`'s
lemma 16, `ordAt_eq_one_of_old_point`), the `R2` mirror of
`ordAt_eq_one_of_R1` — sixth and last of the six bare-`ordAt` point
compositions `ROADMAP-principal-witness-assembly.md`'s step 1 needs, as
distinct from `ordAtFrac_eq_one_of_R2_full`'s `ordAtFrac`-of-`h`
conclusion just above. Exact copy of `ordAtFrac_eq_one_of_R2_full`'s
derivation up to `hA_ord`/`hg_ne`/`hgbar_eval`, plus one new hypothesis
`hU_eval : U.eval R2 ≠ 0`. -/
theorem ordAt_eq_one_of_R2
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (R1 R2 : F p)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (P : H.Point) (hPX : P.X = R2)
    (hPY : P.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R2) (hPY_ne : P.Y ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hR2P1 : R2 ≠ P1.1) (hR2P2 : R2 ≠ P2.1)
    (hR2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R2 = 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYR2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (hU_eval : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1) :
    ordAt P E Y = 1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ^ 2 := rfl
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = E ^ 2 -
        curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hE_def ▸ hY_def ▸ hNpoly4_eq₀
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      calc
        pairNorm H E Y = E ^ 2 - Y ^ 2 * curvePoly p c0 c1 c2 c3 c4 := hpn
        _ = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
          rw [mul_comm (Y ^ 2) (curvePoly p c0 c1 c2 c3 c4)]
    calc
      pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := hpn'
      _ = Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 := hNpoly4_eq.symm
      _ = A * U := hfact
  have hAmonic : A.Monic := by
    rw [hA_def]
    exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne0 : A ≠ 0 := hAmonic.ne_zero
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hA_ne0 h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hA_ord : ordAt P A (0 : Polynomial (F p)) = 1 := by
    rw [hA_def]
    exact ordAt_npoly4Lcm4_eq_one_of_R2 p hchar hsf P1 P2 ua0 ua1 u0 u1
      R1 R2 htargetRoot1 htargetRoot2 hRne P h_bot hPX hPY_ne h12 hne34 hnoroot34
      hP1ua hP1target hP2ua hP2target hR2P1 hR2P2 hR2ua
  have hgR2_eval : E.eval R2 + P.Y * Y.eval R2 = 0 := by
    rw [hPY]
    simpa [hE_def, hY_def] using
      (Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u p P1 P2 ua0 ua1 va0 va1
        u0 u1 v0 v1 hA R2 htargetRoot2)
  have hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [hPX, Polynomial.eval_neg]
    have hYZ : Y.eval R2 * P.Y ≠ 0 :=
      mul_ne_zero (by simpa [hY_def] using hYR2_ne) hPY_ne
    have hgR2_eval' : E.eval R2 + Y.eval R2 * P.Y = 0 := by
      linear_combination hgR2_eval
    intro hcontra
    have h2 : (2 : F p) * (Y.eval R2 * P.Y) = 0 := by
      linear_combination hgR2_eval' - hcontra
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYR2_ne
    rw [← hY_def, hY0]
    simp
  have hU_eval' : U.eval P.X ≠ 0 := by
    rw [hPX, hU_def, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne) hU_eval
  exact ordAt_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord hU_eval'

end PointCompositionR2

/-! ## Step 4a: a reusable PrincipalWitness assembly interface

The `P1` proof above contains an important bit of logic that is independent of
how the order-one fact was obtained.  Once the geometric side has supplied
`ordAt P A 0 = 1`, the remaining input to `ordAtFrac_eq_one_of_old_point` is
exactly the pair-norm factorization together with the two nonvanishing facts.
Making that interface explicit is useful for the other five points: each
geometric instantiation should now only have to produce the point-specific
`g = 0` / `bar g ≠ 0` facts and the common factorization data.

This theorem is intentionally just an interface theorem.  In particular, it
does not manufacture any of the point-specific hypotheses; doing so here would
hide precisely the nondegeneracy obligations that still need to be checked at
`P2`, `Ra1`, `Ra2`, `R1`, and `R2`.
-/
section PointCompositionInterface

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

omit [Fact (p ≠ 2)] in
/--
Generic old-point assembly for the `PrincipalWitness` lemma 14.

The geometric part of the proof is completely abstracted into
`hA_ord`.  The algebraic part is the equality
`pairNorm H E Y = A * U`; once that and the two evaluations distinguishing
`g := toPair H E Y` from `ḡ := toPair H E (-Y)` are available, the conclusion is
exactly the desired order-one statement for the fraction with denominator `U`.
-/
theorem ordAtFrac_eq_one_of_old_point_of_pairNorm
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hg_ne : toPair H E Y ≠ 0)
    (hgbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hgbar_eval hAU hA_ne hU_ne hA_ord

omit [Fact (p ≠ 2)] [IsDedekindDomain (CoordinateRing H)] in
/-- A zero-coefficient witness cannot vanish as a pair at `P` when its `Y`
coefficient is nonzero at `P.X`.  This is the small bridge needed repeatedly
when feeding the PrincipalWitness lemmas: `toPair_eq_zero_iff` is global,
whereas the pointwise hypotheses are stated using polynomial evaluation. -/
lemma toPair_ne_zero_of_eval_snd_ne
    (P : H.Point) (E Y : Polynomial (F p))
    (hY_eval : Y.eval P.X ≠ 0) :
    toPair H E Y ≠ 0 := by
  rw [Ne, toPair_eq_zero_iff]
  intro hzero
  exact hY_eval (by simp [hzero.2])

/-- Characteristic-`≠ 2` algebraic bridge for conjugating the `Y`-coefficient.
If `E + Y*y = 0` at a point, but `Y*y` is nonzero, then the conjugate
expression `E - Y*y` cannot also vanish.  This packages the recurring
`linear_combination`/`mul_eq_zero` argument from the point instantiations. -/
lemma eval_conj_ne_of_eval_add_mul_eq_zero
    {K : Type*} [Field K] (hchar : (2 : K) ≠ 0)
    {e y z : K} (hyz : y * z ≠ 0)
    (h : e + y * z = 0) :
    e + (-y) * z ≠ 0 := by
  intro h'
  have h2 : (2 : K) * (y * z) = 0 := by
    linear_combination h - h'
  exact hyz (by
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact h2yz)

end PointCompositionInterface


/-! ## Step 4 (continued): all six pointwise `ordAtFrac` assemblies

The remaining work in this step is deliberately separated from the geometric
root bookkeeping.  Step 3 supplies, at a given named point, the order-one fact
for `npoly4Lcm4` together with the interpolation identity saying that either
`g := E + Y*y` or its conjugate `bar g := E - Y*y` vanishes there.  The only
extra nondegeneracy needed to invoke the corresponding PrincipalWitness lemma
is the explicit pointwise hypothesis
`(Ypoly4 ...).eval P.X ≠ 0`.

This section packages the two algebraic patterns and then gives the five named
wrappers requested for P2/Ra1/Ra2/R1/R2.  The wrappers intentionally take the
pointwise interpolation identity and the Step-3 `ordAt` fact as hypotheses:
those are the completed geometric bridge inputs, while this section is only
responsible for the `ordAtFrac` assembly itself.
-/

section PointwiseOrdAtFracAssembly

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

omit [Fact (p ≠ 2)] in
/-- `P2` specialization of the old-point assembly.  The Step-3 geometry is
represented by `hA_ord` and `hzero`; the `hY` nonvanishing remains explicit.
-/
theorem ordAtFrac_eq_one_of_P2
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1)
    (hzero : E.eval P.X + P.Y * Y.eval P.X = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  have hYZ : Y.eval P.X * P.Y ≠ 0 := mul_ne_zero hY hPY
  have hzero' : E.eval P.X + Y.eval P.X * P.Y = 0 := by
    simpa [mul_comm] using hzero
  have hbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [Polynomial.eval_neg]
    exact eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZ hzero'
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hE0, hY0⟩
    apply hY
    rw [hY0]
    simp
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hbar_eval hAU hA_ne hU_ne hA_ord

omit [Fact (p ≠ 2)] in
/-- `Ra1` specialization of the old-point assembly. -/
theorem ordAtFrac_eq_one_of_Ra1
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1)
    (hzero : E.eval P.X + P.Y * Y.eval P.X = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  have hYZ : Y.eval P.X * P.Y ≠ 0 := mul_ne_zero hY hPY
  have hzero' : E.eval P.X + Y.eval P.X * P.Y = 0 := by
    simpa [mul_comm] using hzero
  have hbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [Polynomial.eval_neg]
    exact eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZ hzero'
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hE0, hY0⟩
    apply hY
    rw [hY0]
    simp
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hbar_eval hAU hA_ne hU_ne hA_ord

omit [Fact (p ≠ 2)] in
set_option maxHeartbeats 400000 in
-- Accumulated elaboration context in PointwiseOrdAtFracAssembly section.
/-- `Ra2` specialization of the old-point assembly. -/
theorem ordAtFrac_eq_one_of_Ra2
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 1)
    (hzero : E.eval P.X + P.Y * Y.eval P.X = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  have hYZ : Y.eval P.X * P.Y ≠ 0 := mul_ne_zero hY hPY
  have hzero' : E.eval P.X + Y.eval P.X * P.Y = 0 := by
    simpa [mul_comm] using hzero
  have hbar_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0 := by
    rw [Polynomial.eval_neg]
    exact eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZ hzero'
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨hE0, hY0⟩
    apply hY
    rw [hY0]
    simp
  exact ordAtFrac_eq_one_of_old_point P h_bot E Y A U
    hg_ne hbar_eval hAU hA_ne hU_ne hA_ord

set_option maxHeartbeats 400000 in
-- new-point (residual) case: P is a root of U, not A; uses lemma 13c.
theorem ordAtFrac_eq_one_of_R1
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 0)
    (hU_ord : ordAt P U (0 : Polynomial (F p)) = 1)
    (hbar_zero : E.eval P.X + (-Y).eval P.X * P.Y = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = -1 := by
  have hYZbar : (-Y).eval P.X * P.Y ≠ 0 :=
    mul_ne_zero (by simp [hY]) hPY
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; rintro ⟨-, hY0⟩; simp [hY0] at hY
  have hbar_global_ne : toPair H E (-Y) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩; apply hY
    have : Y = 0 := neg_eq_zero.mp hY0
    simp [this]
  have hg_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0 := by
    simp only [neg_neg]
    have h := eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZbar hbar_zero
    simpa [Polynomial.eval_neg] using h
  exact ordAtFrac_eq_neg_one_of_residual_point P h_bot E Y A U
    hg_ne hbar_global_ne hg_eval hAU hA_ne hU_ne hA_ord hU_ord

set_option maxHeartbeats 400000 in
-- new-point (residual) case: same as R1.
/-- `R2` specialization of the new-point assembly. -/
theorem ordAtFrac_eq_one_of_R2
    (hchar : (2 : F p) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (E Y A U : Polynomial (F p))
    (hAU : pairNorm H E Y = A * U)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 0)
    (hU_ord : ordAt P U (0 : Polynomial (F p)) = 1)
    (hbar_zero : E.eval P.X + (-Y).eval P.X * P.Y = 0)
    (hY : Y.eval P.X ≠ 0)
    (hPY : P.Y ≠ 0)
    (hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0)
    (hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = -1 := by
  have hYZbar : (-Y).eval P.X * P.Y ≠ 0 :=
    mul_ne_zero (by simp [hY]) hPY
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; rintro ⟨-, hY0⟩; simp [hY0] at hY
  have hbar_global_ne : toPair H E (-Y) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩; apply hY
    have : Y = 0 := neg_eq_zero.mp hY0
    simp [this]
  have hg_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0 := by
    simp only [Polynomial.eval_neg, neg_neg]
    have h := eval_conj_ne_of_eval_add_mul_eq_zero hchar hYZbar hbar_zero
    simpa [Polynomial.eval_neg] using h
  exact ordAtFrac_eq_neg_one_of_residual_point P h_bot E Y A U
    hg_ne hbar_global_ne hg_eval hAU hA_ne hU_ne hA_ord hU_ord

/-- Two explicit old-point cases can be wired directly to the old-point
PrincipalWitness theorem without manufacturing any hidden nondegeneracy.
This is the reusable case-split shape used by the eventual six-point caller.
-/
theorem ordAtFrac_eq_one_of_old_point_cases
    (P Q₁ Q₂ : H.Point)
    (hPcase : P = Q₁ ∨ P = Q₂)
    (hQ₁ : ordAtFrac Q₁ E Y U (0 : Polynomial (F p)) = 1)
    (hQ₂ : ordAtFrac Q₂ E Y U (0 : Polynomial (F p)) = 1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  rcases hPcase with rfl | rfl
  · exact hQ₁
  · exact hQ₂

/-- Four-way old-point dispatcher for `P1`, `P2`, `Ra1`, `Ra2`.  Each
branch is already the fully assembled pointwise valuation theorem, so the
case split itself introduces no additional nondegeneracy assumptions. -/
theorem ordAtFrac_eq_one_of_four_old_point_cases
    (P P1 P2 Ra1 Ra2 : H.Point)
    (hPcase : P = P1 ∨ P = P2 ∨ P = Ra1 ∨ P = Ra2)
    (hP1 : ordAtFrac P1 E Y U (0 : Polynomial (F p)) = 1)
    (hP2 : ordAtFrac P2 E Y U (0 : Polynomial (F p)) = 1)
    (hRa1 : ordAtFrac Ra1 E Y U (0 : Polynomial (F p)) = 1)
    (hRa2 : ordAtFrac Ra2 E Y U (0 : Polynomial (F p)) = 1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = 1 := by
  rcases hPcase with rfl | rfl | rfl | rfl
  · exact hP1
  · exact hP2
  · exact hRa1
  · exact hRa2

/-- Two-way new-point dispatcher for `R1`/`R2`.  The two branches carry the
negative valuation furnished by `ordAtFrac_neg_eq_one_of_new_point`. -/
theorem ordAtFrac_neg_eq_one_of_two_new_point_cases
    (P R1 R2 : H.Point)
    (hPcase : P = R1 ∨ P = R2)
    (hR1 : ordAtFrac R1 E Y U (0 : Polynomial (F p)) = -1)
    (hR2 : ordAtFrac R2 E Y U (0 : Polynomial (F p)) = -1) :
    ordAtFrac P E Y U (0 : Polynomial (F p)) = -1 := by
  rcases hPcase with rfl | rfl
  · exact hR1
  · exact hR2

end PointwiseOrdAtFracAssembly

/-! ## Step 4 (Mumford-pair strategy, per Claire's instruction): the residual
## case discharged via `uRS4General`/`vRS4General`'s OWN Mumford data,
## with no `H.Point` for the residual pair ever named

Per `ROADMAP-principal-witness-assembly.md`'s "Status update (this pass,
#11)", both ChatGPT replies suggested packaging the residual pair as
`uRS4General`'s own Mumford data `(U, V) := (uRS4General, vRS4General)`
rather than naming `ι(R1)`/`ι(R2)` as explicit `H.Point`s the way
`PointCompositionR1`/`PointCompositionR2` (old-point case, per pass #13)
do for `u_target`'s roots. This section implements that strategy for the
GENUINELY residual pair (`uRS4General`'s own two roots — the fresh output
of the reduction, distinct from `u_target`'s roots, which pass #13 already
confirmed are old-support, not residual). Nothing here replaces
`PointCompositionR1`/`R2` (those are correct, and about a different pair
of points); this section is the piece that was previously missing
entirely — no explicit-point composition for `uRS4General`'s own roots
existed anywhere in this file before this pass.

**The key move**: instead of extracting a named root `r` of `uRS4General`
(which is what `Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u`
does for `u_target`), this section works directly with `P : H.Point` such
that `uRS4General.eval P.X = 0` — i.e. `P` ranges over `uRS4General`'s
zero locus abstractly, the same way `reducedClass_eq_of_isReduction'`'s
own `S`/`hsupp` hypotheses already range over `(-v,1)`'s support without
naming individual points. The new divisibility fact
`uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General` (`GeneralSharedRoot.lean`,
added this pass, same file/section as `vRS4General_sq_eq_f_mod_uRS4General`,
same `hInv` hypothesis — no new assumption) is exactly the "no named root"
analogue of `u_dvd_Epoly4_add_Ypoly4_mul_v`: derived via the SAME Bézout
remainder idiom `vRS4General_sq_eq_f_mod_uRS4General`'s own proof uses
(`Polynomial.dvd_modByMonic_sub` giving `U ∣ V - (-E*G)`, combined with
`hInv : U ∣ Y*G - 1` scaled by `E`), just for the linear identity
`E + Y*V ≡ 0` instead of the quadratic `V² ≡ f`. -/

section MumfordPairResidualCase

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]

set_option maxHeartbeats 4000000 in
/-- **The residual-point `ordAtFrac` fact, stated for ANY `P` with
`P.X` a root of `uRS4General` — no named root, no `ι(R_i)`.** Given
`P.X`'s root-membership in `uRS4General` (`huRoot`), `P.Y` matching
`vRS4General`'s value at `P.X` up to sign (`hPY : P.Y = -vRS4General.eval
P.X`). This residual case needs `ḡ(P) = 0` (`toPair H E (-Y)` vanishing),
not `g(P) = 0` — matching `ordAtFrac_eq_one_of_R1`'s own `hbar_zero`-shaped
hypothesis, lemma 13c's actual requirement. The `+`-sign divisibility fact
`uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General` gives `E(P) +
Y(P)*V(P) = 0`, i.e. `E(P) = -Y(P)*V(P)`; with `P.Y = -V(P)` this makes
`ḡ(P) = E(P) - Y(P)*P.Y = -Y(P)*V(P) - Y(P)*(-V(P)) = 0`, and the usual
nondegeneracy data (`P.Y ≠ 0`, `Ypoly4.eval P.X ≠ 0`, `ordAt P A 0 = 0` —
`P` is genuinely NOT an old point), concludes `ordAtFrac P E Y U 0 = -1`
directly via lemma 13c
(`ordAtFrac_eq_neg_one_of_residual_point`, `PrincipalWitness.lean`).

This is the residual-case analogue of `ordAtFrac_eq_one_of_R1_full`
(the explicit-point route), but takes `huRoot : U.eval P.X = 0` and
`hPY` as its geometric input instead of a named field element `R1` plus
`htargetRoot1`/`hRne`/etc. Composing this with `hsupp`/`S` at the
eventual `AlphaLocusDegreeUniform.lean` call site should mean: for
`P ∈ S`, `hsupp`'s own definition of `S` (once pinned to `uRS4General`'s
zero locus, matching this theorem's own `huRoot` hypothesis) supplies
`huRoot` directly, with no per-point case split into "is `P` the first or
second root" ever needed — the six-way case split (Step 4's
`PointwiseOrdAtFracAssembly` dispatchers) collapses to a TWO-way split
(`P ∈ Sold` vs `P ∈ S`) for the residual half. **This collapse is the
actual payoff of the Mumford-pair strategy** — not proved as its own
composed theorem in this pass (that composition needs `S`'s concrete
definition fixed at the `AlphaLocusDegreeUniform.lean` call site, which
is out of scope for this file per its own module docstring), but this
theorem is the piece that makes it possible.

**Build error found and fixed (previous pass): `g`/`ḡ` branch confusion,
confirmed resolved — Claire's REPL reports this section now builds.**
The first version of this proof derived `g(P) = 0` (`E(P) + P.Y*Y(P) =
0`) from `huRoot`/`hPY`/`heval` and fed that into `hg_eval`/the final
`ordAtFrac_eq_neg_one_of_residual_point` call — but lemma 13c's own
signature (checked directly, `PrincipalWitness.lean`) needs `ḡ(P) = 0`
or `g(P) ≠ 0`, matching `ordAtFrac_eq_one_of_R1`'s already-build-clean
`hbar_zero`-shaped hypothesis, not `g(P) = 0`. Fixed by renaming the
derived fact to `hbar_zero : E.eval P.X + (-Y).eval P.X * P.Y = 0` and
deriving `hg_eval` (`g(P) ≠ 0`) from it via the standard char-`≠2`
conjugate argument. `hPY`'s signature-level negation (`P.Y =
-vRS4General.eval P.X`) was correct throughout and unchanged.

**The `hU_ord`/squarefreeness gap (this pass): closed via a new scoped
hypothesis, per a ChatGPT consultation confirming it's genuinely not
derivable.** Asked ChatGPT directly whether `Squarefree uRS4General` (or
simple-root-ness of `uRS4General` at `P.X`) follows from `hgcd`/`hInv`
(Bézout invertibility of `Ypoly4` mod `uRS4General`) alone, or together
with `uRS4General ∣ Npoly4 = E^2 - f*Y^2`. **Answer: no** — ChatGPT gave
an explicit counterexample (`U = (X-r)^2`, `Y = 1`, `G = 1` satisfies
`hInv` trivially since `Y*G - 1 = 0`; taking `E = f = 1` also satisfies
`U ∣ N` trivially) showing a repeated root is fully compatible with both
hypotheses. This matches the project's own existing convention:
`Squarefree H.f` is ALREADY taken as a bare hypothesis everywhere else in
this codebase (`LPairFinrankOneOrdAtFrac.lean`, `HyperellipticClassProof.lean`,
etc. — grepped and confirmed, never derived), so following that same
convention here rather than searching further for a derivation. Added
two new hypotheses to this theorem's signature: `hsf : Squarefree H.f`
(needed by `ordAt_linX_eq_one_of_ne_zero`, the existing Layer-1 lemma —
NOT a new axiom, just wiring in what Layer 1 already requires) and
`hUfac : ∃ Fco, uRS4General ... = linX P.X * Fco ∧ Fco.eval P.X ≠ 0` — the
MINIMAL local fact actually needed (simple-root-ness of `uRS4General`
AT `P.X` specifically, via an explicit factorization witness), not full
`Squarefree uRS4General` (a stronger, global statement this proof never
uses). This keeps the "no named second root" spirit of the Mumford-pair
strategy: `hUfac`'s witness `Fco` is a polynomial, never a named field
element for the second root's VALUE. `hU_ord` itself is now proved (no
`sorry`) via the exact Layer-1/Layer-2 composition
(`ordAt_linX_eq_one_of_ne_zero` + `ordAt_mul_eq_one_of_ordAt_eq_one_zero`)
already used elsewhere in this file for the named-point cases, plus
`ordAt_C_mul_eq` to strip the `C lc` unit scalar — same idiom as
`ordAt_unit_mul_A_eq_one_of_eval_ne_zero` above. **Not yet build-tested —
Claire's REPL to confirm**; the eventual `AlphaLocusDegreeUniform.lean`
call site will need to supply `hUfac` concretely (almost certainly via
`X^2 + bX + c = (X - r)*(X - r')` factorization once `uRS4General`'s
actual two roots are in hand there — still no NAMED root needed in
THIS file's signature, just at that downstream call site). One further
risk remains: `uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General`
itself (`GeneralSharedRoot.lean`) is new this pass and not yet
build-tested either — if it fails, this theorem fails with it, and the
`GeneralSharedRoot.lean` proof should be checked first. 

 **The bare `ordAt P U 0 = 1` fact at a root of `U := C lc *
uRS4General`, extracted standalone from `ordAtFrac_eq_neg_one_of_
uRS4General_root`'s own `hU_ord` derivation.** Needed for
`ROADMAP-principal-witness-assembly.md`'s step 1, second half
(`div_aff(u_new) = ρ+I`): `u_new := uRS4General` has no `y`-dependence, so
its own affine divisor is plain polynomial `ordAt`-bookkeeping at each of
its two roots `ρ1,ρ2` (ranged over abstractly here via `P`, per the
Mumford-pair strategy's deliberate choice not to name them) — this is
exactly the fact, not the `ordAtFrac`-of-`h = g/U` valuation that
`ordAtFrac_eq_neg_one_of_uRS4General_root` computes. Identical hypotheses
and proof to that theorem's own `hU_ord` `have`-block (Layer 1:
`ordAt_linX_eq_one_of_ne_zero` at `linX P.X`; Layer 2:
`ordAt_mul_eq_one_of_ordAt_eq_one_zero` combining with `Fco`'s zero order
via `hUfac`; `ordAt_C_mul_eq` to strip the `C lc` unit scalar) — pulled out
so the call site doesn't need to re-derive `E`/`Y`/`A`/`hAU`/`g`-side
machinery just to get this `U`-only fact. -/
theorem ordAt_eq_one_of_uRS4General_root
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (P1 P2 : F p × F p)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (hPY_ne : P.Y ≠ 0)
    (hUfac : ∃ Fco : Polynomial (F p),
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = linX P.X * Fco ∧
        Fco.eval P.X ≠ 0)
    (U : Polynomial (F p))
    (hU_def : U = C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    ordAt P U (0 : Polynomial (F p)) = 1 := by
  obtain ⟨Fco, hFeq, hFeval⟩ := hUfac
  have hL : ordAt P (linX P.X) (0 : Polynomial (F p)) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf P.X P h_bot rfl hPY_ne
  have hF_ord : ordAt P Fco (0 : Polynomial (F p)) = 0 :=
    ordAt_eq_zero_of_eval_ne_zero P Fco (0 : Polynomial (F p)) (by simpa using hFeval)
  have hL_ne : toPair H (linX P.X) (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => linX_ne_zero P.X hA
  have hF_ne0 : Fco ≠ 0 := fun h => hFeval (by rw [h]; simp)
  have hF_ne : toPair H Fco (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hF_ne0 hA
  have hflat : ordAt P (linX P.X * Fco) (0 : Polynomial (F p)) = 1 :=
    ordAt_mul_eq_one_of_ordAt_eq_one_zero P h_bot (linX P.X) Fco hL_ne hF_ne hL hF_ord
  have hlc_ne : (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff ≠ 0 :=
    (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne
  have hflat_ne0 : (linX P.X * Fco : Polynomial (F p)) ≠ 0 :=
    mul_ne_zero (linX_ne_zero P.X) hF_ne0
  have hPQ : ¬ ((linX P.X * Fco : Polynomial (F p)) = 0 ∧ (0 : Polynomial (F p)) = 0) :=
    fun h => hflat_ne0 h.1
  have hstep := ordAt_C_mul_eq
    (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    hlc_ne (linX P.X * Fco) (0 : Polynomial (F p)) hPQ P
  rw [hU_def, hFeq]
  simpa using hstep.trans hflat

theorem ordAtFrac_eq_neg_one_of_uRS4General_root
    (hchar : (2 : F p) ≠ 0)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (hInv :
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ∣
        Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
              (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) - 1)
    (P : H.Point)
    (huRoot : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P.X = 0)
    (hsf : Squarefree H.f)
    (hUfac : ∃ Fco : Polynomial (F p),
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = linX P.X * Fco ∧
        Fco.eval P.X ≠ 0)
    (hPY : P.Y = -(vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).eval P.X)
    (hPY_ne : P.Y ≠ 0)
    (hYP_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P.X ≠ 0)
    (A : Polynomial (F p))
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1)
    (hA_ord : ordAt P A (0 : Polynomial (F p)) = 0) :
    ordAtFrac P (Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (C ((curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff) *
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (0 : Polynomial (F p)) = -1 := by
  have h_bot : pointIdeal P ≠ ⊥ := pointIdeal_ne_bot P
  set E := Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hE_def
  set Y := Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hY_def
  set V := vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd with hV_def
  set lc := (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff
    with hlc_def
  set U := C lc * uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 with hU_def
  -- `ḡ(P) = 0`: `E.eval P.X + (-Y).eval P.X * P.Y = 0`, from `huRoot`/`hInv`
  -- via `uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General` evaluated at
  -- `P.X` (giving `E(P) + Y(P)*V(P) = 0`), combined with `hPY : P.Y =
  -- -V(P)`. This is the residual case's actual geometric fact — lemma 13c
  -- needs `ḡ(P) = 0`/`g(P) ≠ 0`, matching `ordAtFrac_eq_one_of_R1`'s own
  -- `hbar_zero`-shaped hypothesis, not `g(P) = 0`.
  have hbar_zero : E.eval P.X + (-Y).eval P.X * P.Y = 0 := by
    have hdvd := uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General p c0 c1 c2 c3 c4 P1 P2
      ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd hInv
    have hrdvd : (Polynomial.X - Polynomial.C P.X) ∣
        (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :=
      Polynomial.dvd_iff_isRoot.mpr huRoot
    have hfulldvd : (Polynomial.X - Polynomial.C P.X) ∣ (E + Y * V) :=
      hrdvd.trans hdvd
    have heval := Polynomial.dvd_iff_isRoot.mp hfulldvd
    rw [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul] at heval
    rw [Polynomial.eval_neg, hPY]
    linear_combination heval
  have hYZ : Y.eval P.X * P.Y ≠ 0 := mul_ne_zero hYP_ne hPY_ne
  -- `g(P) ≠ 0`: the conjugate of `ḡ(P) = 0` under char ≠ 2. If it also
  -- vanished, `ḡ(P) - g(P) = -2*Y(P)*P.Y = 0` forces `Y(P)*P.Y = 0`
  -- (since `2 ≠ 0`), contradicting `hYZ`.
  have hg_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0 := by
    rw [neg_neg]
    intro hcontra
    have hbar_zero' : E.eval P.X + -(Y.eval P.X) * P.Y = 0 := by
      rw [← Polynomial.eval_neg]; exact hbar_zero
    have h2 : (2 : F p) * (Y.eval P.X * P.Y) = 0 := by
      linear_combination hcontra - hbar_zero'
    rcases mul_eq_zero.mp h2 with h2c | h2yz
    · exact absurd h2c hchar
    · exact absurd h2yz hYZ
  have hg_ne : toPair H E Y ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP_ne
    rw [hY0]; simp
  have hgbar_global_ne : toPair H E (-Y) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    rintro ⟨-, hY0⟩
    apply hYP_ne
    have : Y = 0 := neg_eq_zero.mp hY0
    rw [this]; simp
  have hAU : pairNorm H E Y = A * U := by
    have hfact := Npoly4_eq_npoly4Lcm4_mul_uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1
      u0 u1 v0 v1 hcurne hA hP1_curve hP2_curve hMumfordUa hMumfordTarget
    have hpn := pairNorm_eq_of_eq_curvePoly hf E Y
    have hNpoly4_eq₀ : Npoly4 p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
        E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      simp only [hE_def, hY_def]; rfl
    rw [← hlc_def, ← hU_def, ← hA_def] at hfact
    have hpn' : pairNorm H E Y = E ^ 2 - curvePoly p c0 c1 c2 c3 c4 * Y ^ 2 := by
      rw [hpn]; ring
    rw [hpn', ← hNpoly4_eq₀, hfact]
  have hAmonic : A.Monic := by rw [hA_def]; exact npoly4Lcm4_monic p P1 P2 ua0 ua1 u0 u1
  have hA_ne : toPair H A (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hAmonic.ne_zero h.1
  have hUmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hU_ne0 : U ≠ 0 := by
    rw [hU_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr
      ((not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne)) hUmonic.ne_zero
  have hU_ne : toPair H U (0 : Polynomial (F p)) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]; exact fun h => hU_ne0 h.1
  have hU_ord : ordAt P U (0 : Polynomial (F p)) = 1 := by
    obtain ⟨Fco, hFeq, hFeval⟩ := hUfac
    have hL : ordAt P (linX P.X) (0 : Polynomial (F p)) = 1 :=
      ordAt_linX_eq_one_of_ne_zero hchar hsf P.X P h_bot rfl hPY_ne
    have hF_ord : ordAt P Fco (0 : Polynomial (F p)) = 0 :=
      ordAt_eq_zero_of_eval_ne_zero P Fco (0 : Polynomial (F p)) (by simpa using hFeval)
    have hL_ne : toPair H (linX P.X) (0 : Polynomial (F p)) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => linX_ne_zero P.X hA
    have hF_ne0 : Fco ≠ 0 := fun h => hFeval (by rw [h]; simp)
    have hF_ne : toPair H Fco (0 : Polynomial (F p)) ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun ⟨hA, _⟩ => hF_ne0 hA
    have hflat : ordAt P (linX P.X * Fco) (0 : Polynomial (F p)) = 1 :=
      ordAt_mul_eq_one_of_ordAt_eq_one_zero P h_bot (linX P.X) Fco hL_ne hF_ne hL hF_ord
    have hlc_ne : lc ≠ 0 := by
      rw [hlc_def]
      exact (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcurne
    have hflat_ne0 : (linX P.X * Fco : Polynomial (F p)) ≠ 0 :=
      mul_ne_zero (linX_ne_zero P.X) hF_ne0
    have hPQ : ¬ ((linX P.X * Fco : Polynomial (F p)) = 0 ∧ (0 : Polynomial (F p)) = 0) :=
      fun h => hflat_ne0 h.1
    have hstep := ordAt_C_mul_eq lc hlc_ne (linX P.X * Fco) (0 : Polynomial (F p)) hPQ P
    rw [hU_def, hFeq]
    simpa using hstep.trans hflat
  exact ordAtFrac_eq_neg_one_of_residual_point P h_bot E Y A U
    hg_ne hgbar_global_ne hg_eval hAU hA_ne hU_ne hA_ord hU_ord

end MumfordPairResidualCase

/-! ## Status note: Mumford-pair residual case scoped and written;
## the one genuine gap (`hU_ord`) closed via a scoped hypothesis, not a
## derivation — see update below

Per Claire's instruction to implement the Mumford-pair strategy (packaging
the residual pair as `uRS4General`/`vRS4General`'s own data rather than
naming `ι(R1)`/`ι(R2)` as explicit points), this pass adds:

1. **`uRS4General_dvd_Epoly4_add_Ypoly4_mul_vRS4General`**
   (`GeneralSharedRoot.lean`, `MumfordIdentity4General` section, right
   after `vRS4General_sq_eq_f_mod_uRS4General`) — the polynomial-level
   divisibility fact `uRS4General ∣ (Epoly4 + Ypoly4 * vRS4General)`,
   proved from the SAME `hInv` hypothesis
   `vRS4General_sq_eq_f_mod_uRS4General` already takes, via the same
   Bézout-remainder idiom (`Polynomial.dvd_modByMonic_sub` plus scaling),
   just for the linear identity instead of the quadratic one. This is new
   mathematical content (not previously on file in any form — confirmed
   by grep before writing it), but low-risk: every step is either a
   direct Mathlib lemma (`Polynomial.dvd_modByMonic_sub`) or `ring`/
   `dvd_add`-level algebra, matching the file's own `sq_mod_eq_of_dvd_4`
   proof style step-for-step.
2. **`ordAtFrac_eq_neg_one_of_uRS4General_root`** (this file,
   `MumfordPairResidualCase` section) — the residual-point `ordAtFrac`
   fact for an ARBITRARY `P` with `P.X` a root of `uRS4General`, no named
   root anywhere. Composes (1) with `Polynomial.dvd_iff_isRoot` (same
   two-step idiom `Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u`
   uses, but applied to `P.X` directly rather than a separately-quantified
   `r`), the `ḡ(P) ≠ 0`/`g(P) ≠ 0` sign-flip argument (copied from
   `PointCompositionR1`'s own confirmed-shape argument), the exact
   factorization equation (Step 1, already on file), and lemma 13c
   (`ordAtFrac_eq_neg_one_of_residual_point`, `PrincipalWitness.lean`).

**Update (this pass): the `sorry` is closed, via a scoped hypothesis, not
a derivation.** `hU_ord : ordAt P U 0 = 1` needed `P.X` to be a SIMPLE
root of `uRS4General` — genuinely different from `huRoot` (`P.X` IS a
root, not necessarily a simple one). Every explicit-point composition
elsewhere in this file gets this from `Layer 3`
(`ordAt_unit_mul_A_eq_one_of_eval_ne_zero`), which inherently needs a
named second root to establish simplicity — unavailable here by design
(that's the whole point of the Mumford-pair strategy). Consulted ChatGPT
on whether `uRS4General`'s squarefreeness (or simple-root-ness at `P.X`)
follows automatically from `hgcd`/`hInv`/`MatrixNondegenerate4`: **it does
not** — ChatGPT supplied an explicit counterexample (`U = (X-r)^2`, `Y =
1` satisfies both `hInv` and `U ∣ Npoly4` trivially while `U` is maximally
non-squarefree), closing off that route for good rather than leaving it
an open question. This also matches the project's existing convention —
`Squarefree H.f` is already a bare, never-derived hypothesis throughout
this codebase.

**Fix applied**: added `hsf : Squarefree H.f` (wiring in what
`ordAt_linX_eq_one_of_ne_zero`, i.e. Layer 1, already requires — not a
new axiom) and `hUfac : ∃ Fco, uRS4General ... = linX P.X * Fco ∧ Fco.eval P.X
≠ 0` to this theorem's signature — the MINIMAL local fact needed (simple-
root-ness of `uRS4General` at `P.X` specifically, via an explicit
factorization witness `F`), not the stronger global `Squarefree
uRS4General`. Still no NAMED root anywhere in this file's signature —
`hUfac`'s witness `Fco` is a polynomial, not a field-element value for the
second root; naming that root's actual value (if ever needed) is pushed
to the `AlphaLocusDegreeUniform.lean` call site, exactly where the
Mumford-pair strategy's docstring already says root-specific bookkeeping
belongs. `hU_ord` is now proved (no `sorry`) via the same Layer-1/Layer-2
composition (`ordAt_linX_eq_one_of_ne_zero` +
`ordAt_mul_eq_one_of_ordAt_eq_one_zero`) used elsewhere in this file for
the named-point cases, plus `ordAt_C_mul_eq` to strip the `C lc` unit
scalar. **Not yet build-tested — Claire's REPL to confirm** (the `g`/`ḡ`
fix from the previous pass IS confirmed build-clean; this `hU_ord` fix is
new and untested).
## explicit; P1 is the first concrete instantiation, and the `R_i`/`ι(R_i)`
## orientation is resolved for the eventual new-point cases.

**Current concrete Step-4 status:** P1 was already assembled end-to-end;
this pass adds the five remaining pointwise wrappers `P2`, `Ra1`, `Ra2`,
`R1`, and `R2`, plus the old/new case-split dispatchers.  Each wrapper
consumes the completed Step-3 inputs as explicit hypotheses: the order-one
fact for `A := npoly4Lcm4`, the appropriate interpolation zero (`g(P)=0`
for old points or `bar g(P)=0` for new points), and the pointwise
`Y.eval P.X ≠ 0` condition.  Thus the nondegeneracy condition is never
silently inferred.  The root-specific Step-3 theorems remain responsible
for producing those hypotheses from the named `P2`/`Ra1`/`Ra2`/`R1`/`R2`
geometry; this file's Step-4 layer now performs the complete `ordAtFrac`
assembly once they are supplied.  `ordAt_npoly4Lcm4_eq_one_of_P1`/`_P2`/
`_Ra1`/`_Ra2`/`_R1`/`_R2`. The
`ua`/`u_target`-root cases each needed one extra step
(`quadratic_eq_mul_X_sub_C` splitting the relevant quadratic into its two
named linear factors) plus a 3-slot/5-factor merge trick (Layer 3's
underlying lemma only has `F₁ F₂ F₃` slots, but splitting a quadratic
leaves 5 flat factors total — the "other" linear/quadratic pair not
containing the designated root is merged into a single `F₃`, which is
free since Layer 3 only needs `Fᵢ.eval a ≠ 0`, no shape constraint). Not
yet build-tested past `Ra2`/`R1`/`R2` as of writing this note — Claire's
REPL to confirm.

**Resolved this pass: the `R_i` vs `ι(R_i)` orientation question flagged
by the roadmap's "Status update, pass #7" section.** Traced directly
against two already-proved facts, not assumed either way:

- `vRS4General := -Epoly4 * gcdA(Ypoly4, uRS4General) mod uRS4General`
  (`GeneralSharedRoot.lean`, confirmed by direct read) — the standard
  Cantor/Mumford sign convention `v ≡ -E/Y mod U`. This means `g := toPair
  H Epoly4 Ypoly4`'s OWN zero at a root `r` of `uRS4General` is the point
  `(r, v(r))` — `g`'s interpolation was built to vanish there, by
  construction.
- Lemma 15 (`ordAtFrac_neg_eq_one_of_new_point`, `PrincipalWitness.lean`)
  identifies a "residual/new" point via `hgbar_ne : toPair H E (-Y) ≠ 0`
  becoming the VANISHING side at the call site (the lemma's own docstring:
  *"at a point where `ḡ(P) = 0`... `g(P) ≠ 0`"*) — i.e. the point that
  actually contributes to `D_new` in the assembly is where `ḡ := toPair H
  E (-Y)` vanishes, NOT where `g` itself vanishes.

Since `toPair H E (-Y)` vanishing at `(x_0,y_0)` means `E(x_0) -
Y(x_0)·y_0 = 0`, i.e. `y_0 = E(x_0)/Y(x_0) = -v(x_0)` (using
`vRS4General`'s confirmed minus sign), the point lemma 15 actually
selects at a root `r` of `uRS4General` is `(r, -v(r))` — the
HYPERELLIPTIC CONJUGATE of `g`'s own zero `(r, v(r))`.

**Conclusion: `D_new`'s two points are `ι(R1), ι(R2)` — the conjugates of
`R1`/`R2` as `g`'s own Mumford-selected points — NOT `R1, R2` directly.**
This is a real orientation fact the call-site assembly (composing lemmas
14/15 at each of the 6 named points, item 2 below) must get right: at
each of `R1`/`R2`, the "new point" case (lemma 15) is the one that
applies, and the `H.Point` it concludes about is `⟨R_i, -v(R_i)⟩`, not
`⟨R_i, v(R_i)⟩`. The 6 `ordAt_npoly4Lcm4_eq_one_of_*` theorems above are
unaffected by this (they only pin down `P.X`, taking `P.Y ≠ 0` and
`h_bot` as hypotheses rather than constructing `H.Point.mk` internally —
per each theorem's own docstring) — the orientation only matters once a
caller instantiates `P` concretely at the assembly call site.

**What is still missing, honestly, before `reducedClass_eq_of_isReduction'`
can lose its `sorry`** (do not attempt to fake past this list):

1. Composing each `ordAt P npoly4Lcm4 0 = 1` fact (the six theorems above)
   with `Npoly4 = npoly4Lcm4 * uRS4General` (Step 1, already proved) to
   get `ordAt P A 0 = 1` in `PrincipalWitness.lean`'s lemma-14/15 sense
   (`A := npoly4Lcm4` there), then applying lemmas 14/15 themselves at
   each of the 6 points — using the NOW-RESOLVED orientation above for the
   `R1`/`R2` cases (lemma 15, point `⟨R_i, -v(R_i)⟩`) versus `P1`/`P2`/
   `Ra1`/`Ra2` (lemma 14, point as constructed). Not attempted this pass.
2. **The `Sg`/`Su`/`divToPairRatio`/`principalSubgroup`-membership half of
   the roadmap's corrected two-step plan (its "Status update, pass #4/#5"
   sections) — SUPERSEDED, not just unstarted.** `ordInfOfPair` was found
   (`PrincipalDivisors.lean`) and computed directly: `ordInfOfPair(Epoly4,
   Ypoly4) = -8`, `ordInfOfPair(uRS4General, 0) = -4` — these do NOT match,
   so `divToPairRatio`/`principalSubgroup` (which demands an exact match)
   is confirmed the wrong tool for this witness. The correct route
   (confirmed via ChatGPT consultation, see
   `ROADMAP-principal-witness-assembly.md`'s "Status update, pass #7"
   and `CHATGPT-LOG-principal-witness-assembly.md` for the exact exchange):
   prove `div_aff(g) - div_aff(uRS4General) = D_old - D_new` directly via
   `eq_of_coeffAt_eq` (already on file), bypassing `principalSubgroup`
   membership entirely. **`Divisor H` is affine-only, so this identity
   carries NO `δ₀` term of any kind** — `eq_of_coeffAt_eq`'s own docstring
   (`PrincipalWitness.lean`) is explicit that this project's `Divisor H`
   model has no `δ₀`-coefficient slot to begin with; the `-8`/`-4` pole
   orders above are a fact about the point at infinity, invisible to
   `Divisor H`, and never surface as a `δ₀` coefficient. (An earlier
   version of this note claimed a `-4•[δ₀]` correction term here — that
   was a summarization error conflating a pole of order `4` at the point
   at infinity with a coefficient on the affine basepoint `δ₀`; see
   `CHATGPT-LOG-principal-witness-assembly.md`'s "pass #17" entry for the
   full trace of the error and its correction. `δ₀` only ever enters at
   the SEPARATE, one-level-up step of converting `D_old`/`D_new` into
   `Jacobian H D` elements via `reducedClass`'s own `- 2•[δ₀]` per
   2-point Mumford pair — see `AlphaLocusDegreeUniform.lean`'s
   `reducedClass` field — and that `2•[δ₀]` is unrelated to, and not
   derived from, the `g`/`uRS4General` pole-order gap.) `D_new`'s point
   labels in this identity use the now-resolved `ι(R1), ι(R2)` orientation
   above, not `R1, R2`. **Not yet written as Lean** — this is the next
   pass's actual target for this piece.

`reducedClass_eq_of_isReduction'` itself is NOT touched this pass and stays
`sorry` — the gap above is too large to close with a guessed proof term,
and this project's own convention (search/ask rather than guess) applies
doubly hard to a correction-term computation not yet checked against
`reducedClass`'s actual definition. -/

/-! ## Status note (this pass, #11): `P2`'s full concrete composition
## (item 1's pattern, second of six) is now on file, alongside `P1`'s

**What this pass adds**: `ordAtFrac_eq_one_of_P2_full`, in a new
`PointCompositionP2` section immediately after `PointCompositionP1`. This
is `ordAtFrac_eq_one_of_P1`'s exact mirror — same derivation of `hAU`
(via `Npoly4_eq_npoly4Lcm4_mul_uRS4General`), `hA_ne`/`hU_ne` (monic
non-zero-ness of `A := npoly4Lcm4` and `U := C leadingCoeff * uRS4General`),
`hA_ord` (via `ordAt_npoly4Lcm4_eq_one_of_P2`, already on file), and
`hg_ne`/`hgbar_eval` (via `Epoly4_eval_add_Y_mul_Ypoly4_eval_P2_eq_zero`,
already on file, confirmed present in `AlphaReduce.lean`) — with every
`P1`-specific occurrence (coordinates, hypothesis names) swapped for `P2`'s
own. No new mathematical content: this is the literal "item 1" composition
step the roadmap's own status notes describe, applied to the second of the
six named points, using only theorems already confirmed on file (this
pass added no new lemmas to `AlphaReduce.lean` or elsewhere — everything
`P2`'s composition needs was already present, just not yet wired together
into one end-to-end theorem the way `P1`'s was).

**Naming note**: called `ordAtFrac_eq_one_of_P2_full`, not bare
`ordAtFrac_eq_one_of_P2`, because that name is already taken by the
abstract wrapper in the `PointwiseOrdAtFracAssembly` section above (which
takes `hA_ord`/`hzero` as bare hypotheses rather than deriving them from
raw interpolation data). `P1`'s theorem never collided with anything
because no abstract `ordAtFrac_eq_one_of_P1` wrapper exists elsewhere in
this file — only `P2` (and, if fully composed in a future pass, `Ra1`/
`Ra2`/`R1`/`R2`) needs the `_full` suffix to disambiguate from its
already-existing abstract counterpart.

**Not yet build-tested — Claire's REPL to confirm**, though risk is
assessed as low: every step is a mechanical re-derivation of `P1`'s
already-confirmed-build-clean proof, swapping named constants only; no new
tactic sequence, no new lemma composition shape.

/-! ## Status note (this pass, #12): `Ra1`/`Ra2`'s full concrete
## compositions (third and fourth of six) are now on file

**What this pass adds**: `ordAtFrac_eq_one_of_Ra1_full` and
`ordAtFrac_eq_one_of_Ra2_full`, in new `PointCompositionRa1`/
`PointCompositionRa2` sections immediately after `PointCompositionP2`.
Same shape as `P1`/`P2_full` (lemma 14 via `ordAtFrac_eq_one_of_old_point`,
`hA_ord` via `ordAt_npoly4Lcm4_eq_one_of_Ra1`/`_Ra2`, already on file), but
the `g(point) = 0` input is now `Epoly4_eval_add_va_eval_mul_Ypoly4_eval_
eq_zero_of_root_ua` (pass #10, `AlphaReduce.lean`) at the named root
`Ra1`/`Ra2`, rather than a `P1`/`P2`-style theorem at a fixed interpolation
point. Since `Ra1`/`Ra2` aren't named parameters with their own `.2`
coordinate the way `P1`/`P2` are, each theorem takes an explicit `hPY :
P.Y = (C va1 * X + C va0).eval Ra{1,2}` hypothesis pinning `P.Y` to the
Mumford-representation `y`-value at that root, in place of the `P2.2`-style
hypothesis `P2_full` used. Everything else (the `hAU`/`hA_ne`/`hU_ne`
derivation, the `ḡ ≠ 0` sign-flip argument via `hchar`) is a direct copy of
`P2_full`'s proof body with the point-specific pieces substituted — no new
lemmas needed anywhere, same as the `P2` pass.

**Build note (from Claire, after the `P2_full` pass)**: `omit [...] in`
must sit directly above its theorem, with no doc comment (`/-- ... -/`)
between the `omit` line and the `theorem` line — an `omit` placed after a
preceding doc comment does not build. No `omit` was needed in this pass's
additions (no unused section variables), but noting this for the next
`R1`/`R2` pass and any future edits to the existing `omit` sites.

**Not yet build-tested — Claire's REPL to confirm**, though risk is
assessed low for the same reason as `P2_full`: mechanical re-derivation of
an already-confirmed-build-clean proof shape, with the `hPY`-as-root-value
substitution being the only structurally new piece (still a direct
application of an already-proved theorem, not new math).

**Correction (this pass, #13)**: the previous paragraph's plan was wrong,
caught by direct re-reading of the actual on-file Lean rather than trusting
this file's own prior status note. `ordAt_npoly4Lcm4_eq_one_of_R1`/`_R2`
(`GeometricInstantiationQuadratic3`/`4`, already on file before this pass)
take `htargetRoot1`/`htargetRoot2 : (X^2+C u1*X+C u0).IsRoot R{1,2}` as
hypotheses and conclude `ordAt P npoly4Lcm4 0 = 1` — i.e. `R1`/`R2` are
`u_target`'s own two roots, confirmed old-support (`npoly4LcmRaw`'s
definition literally folds `u_target` into the same outer `lcm` as `ua`,
`(X-P1.x)`, `(X-P2.x)`), matching `CHATGPT-LOG-principal-witness-assembly.
md`'s own naming ("`R1,R2` := each of `u_target`'s two roots") and pass
#5's "old vs residual" correction. They are NOT roots of `uRS4General`
(the genuinely fresh residual pair, which has no name anywhere in this
codebase yet) and do NOT need lemma 13c
(`ordAtFrac_eq_neg_one_of_residual_point`) — they need lemma 14
(`ordAtFrac_eq_one_of_old_point`), exactly like `Ra1`/`Ra2`. The abstract
`ordAtFrac_eq_one_of_R1`/`_R2` wrappers in `PointwiseOrdAtFracAssembly`
above (concluding `-1` via lemma 13c) anticipate a *different*,
not-yet-built residual pair and are unrelated to this pass's `R1`/`R2`;
they are left in place, unused for now, rather than deleted, since a
future residual-pair pass may still want that exact shape.

**What this pass adds**: `ordAtFrac_eq_one_of_R1_full` and
`ordAtFrac_eq_one_of_R2_full`, in new `PointCompositionR1`/
`PointCompositionR2` sections immediately after `PointCompositionRa2` —
the fifth and sixth (last) of the six point compositions Part D needs.
Exact mirror of `ordAtFrac_eq_one_of_Ra1_full`/`_Ra2_full`'s shape (lemma
14, `hA_ord` via `ordAt_npoly4Lcm4_eq_one_of_R1`/`_R2`), with `ua`/`va` and
`Ra1`/`Ra2` swapped for `u`/`v` (`X^2+C u1*X+C u0`, `C v1*X+C v0`) and
`R1`/`R2`, and `Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u`
(already on file in `AlphaReduce.lean`) in place of the `_of_root_ua`
root-evaluation theorem. `hPY : P.Y = (C v1*X+C v0).eval R{1,2}` follows
the same "positive lift, matching `g`'s own vanishing" convention
`Ra1_full`/`Ra2_full` used for `va`; this is the lift `g` was built to
vanish at (per this file's earlier "Resolved this pass" note on the
`R_i`/`ι(R_i)` orientation, which concerns a different, not-yet-built
residual-point theorem, not this one). No new lemmas needed anywhere —
`ordAt_npoly4Lcm4_eq_one_of_R1`/`_R2` and
`Epoly4_eval_add_v_eval_mul_Ypoly4_eval_eq_zero_of_root_u` were already on
file before this pass, just not yet composed into an end-to-end theorem.

**All six point compositions (`P1`, `P2`, `Ra1`, `Ra2`, `R1`, `R2`) are
now on file.** **Not yet build-tested — Claire's REPL to confirm**, same
low-risk assessment as `Ra1_full`/`Ra2_full`: mechanical re-derivation of
an already-confirmed-build-clean proof shape, no new tactic sequence.

**Still not done**: composing all six `_full` theorems together into the
actual `∀ P` case split `reducedClass_eq_of_isReduction'` needs (via the
`support_cases`/`by_cases P ∈ S`-style dispatch ChatGPT recommended, using
the `ordAtFrac_eq_one_of_four_old_point_cases`/
`ordAtFrac_neg_eq_one_of_two_new_point_cases` dispatchers already on file
above), plus the still-open `Sg`/`div_aff(g)`-to-`D_old - D_new` step
(item 2 of the earlier status note — a bare `Divisor H` equality with NO
`δ₀` term; see that note for why an earlier `-4•[δ₀]` phrasing here was
wrong). Both remain for `AlphaLocusDegreeUniform.lean`'s own proof body,
per this file's stated scoping. -/
-/

end DecoupledSystem
end Genus2Lean

