import Mathlib
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.ZeroD.AlphaLocusDegreeUniform
import Genus2Lean.ZeroD.PrincipalWitnessAssembly
import Genus2Lean.ZeroD.PrincipalWitnessStep1

/-!
# Step 2 of `ROADMAP-principal-witness-assembly.md`: `div_aff(u_new) = ρ+I`
# and the subtraction assembly `div_aff(g) - div_aff(u_new) = A+C+T-ρ-I`

Per that roadmap's "Concrete next steps, in order":

1. Step 1 (`div_aff(g) = A+C+T`, fully-split and both single/doubly-repeated-
   root variants) is done, in `PrincipalWitnessStep1.lean`.
2. Step 2, this file: first prove `div_aff(u_new) = ρ+I` (the residual-side
   companion, `u_new := uRS4General`, split into its own two named roots
   `ρ1,ρ2` and their conjugates `ι ρ1, ι ρ2`), then combine with step 1's
   fully-split theorem via plain `Divisor Hc`-level subtraction to get
   `div_aff(g) - div_aff(u_new) = A+C+T-ρ-I`.

**Scoping, matching step 1's own.** Only the fully-split case is assembled
here (`hRne`/`hRane` both hold, AND `uRS4General` itself has two distinct
roots `ρ1 ≠ ρ2`) — the repeated-root variants of THIS file's own new content
(`ρ1 = ρ2`, i.e. `uRS4General` a perfect square) are not attempted; nothing
in the roadmap flags that case as needed, since `uRS4General`'s two roots
are never named/constrained the way `ua`/`u_target`'s are, and the roadmap's
scoping note is specifically about `ua`/`u_target`, not `uRS4General`.

**Why `div_aff(u_new) = ρ+I` needs its own splitting step, not just re-use
of `ordAt_eq_one_of_uRS4General_root`.** That theorem (`PrincipalWitness
Assembly.lean`, `MumfordPairResidualCase` section) gives the bare pointwise
fact `ordAt P U 0 = 1` at ONE abstract root `P`, deliberately not naming
`uRS4General`'s two roots (the "no named second root" spirit of the
Mumford-pair strategy, per that theorem's own docstring). To state the
`Divisor Hc`-level equality `divToPair U 0 S = single ρ1' + single ρ2'` for
a concrete two-point `Finset`, both roots must be named after all — exactly
the same situation step 1 was in for `ua`/`u_target` (also degree-2,
originally left abstract, then split via `quadratic_eq_mul_X_sub_C` once a
concrete `Finset`-level statement was wanted). This file does that same
splitting for `uRS4General`, using `uRS4General_monic` +
`uRS4General_natDegree_eq_two` (`GeneralSharedRoot.lean` — the latter needs
the same `hlead`/`h12`/`hne34`/`hnoroot34`/`hP1ua`/`hP1target`/`hP2ua`/
`hP2target` hypothesis list `curBeforeMonic4General_natDegree_eq_two`
already needs, re-supplied here as this file's own hypotheses rather than
re-derived) to feed `quadratic_eq_mul_X_sub_C`, then applies
`ordAt_eq_one_of_uRS4General_root`
at each of the two resulting named roots (`hUfac` built directly from the
`(X-Cρ1)*(X-Cρ2)` factorization, mirroring `ordAt_eq_one_of_R1`'s own
`hUfac`-construction idiom one level up).

**`ρ` vs `I` naming.** Per the roadmap's own corrected notation, `ρ :=
[ρ1]+[ρ2]` is `u_new`'s own two AFFINE roots as `Hc.Point` values with
`Y ≠ 0` (so each root has both `P.Y = -V(P)` and its conjugate `ι P`, `V :=
vRS4General`), and `I := [ι ρ1]+[ι ρ2]`. This file names four points
(`Ptrho1, Ptrho2 : Hc.Point` for `ρ`, and their `Point.iota` images for
`I`) rather than eight, using `Point.iota` directly rather than re-deriving
each conjugate's coordinates from scratch — `iota_X`/`iota_Y` already give
`(ι P).X = P.X`, `(ι P).Y = -P.Y` unconditionally.

**No `δ₀` term**, exactly as the roadmap's "Workflow reminders" section
states: `Divisor Hc` is affine-only by construction, so the subtraction
`div_aff(g) - div_aff(u_new)` below is a literal `Divisor Hc`-level
equality with no infinity correction anywhere. -/

noncomputable section

open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Polynomial

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [Fact (p ≠ 2)]
variable {Hc : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing Hc)]

/-- **`div_aff(u_new) = ρ+I`, fully-split case (`u_new := uRS4General` has
two distinct roots `ρ1 ≠ ρ2`): the literal `Divisor Hc` equality.**
`u_new` has no `y`-dependence, so `divToPair U 0 S` (`U := C lc *
uRS4General`, `lc` the leading-coefficient unit already tracked by
`uRS4General`'s own normalization) restricted to the four-point support
`{Ptrho1, Ptrho2, Ptiota1, Ptiota2}` (`ρ1,ρ2` and their conjugates) puts
coefficient `1` on each — `ordAt = 1` at every one of `u_new`'s own
(unramified, since `Y ≠ 0`) affine zeros, both lifts of each of the two
roots. Same `eq_of_coeffAt_eq`/`coeffAt_divToPair`/`by_cases`-per-point
proof shape as step 1's fully-split theorem. -/
theorem divToPair_eq_rho_add_I_of_split
    [DecidableEq Hc.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree Hc.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : Hc.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (hlead : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨6, by norm_num⟩ ≠ 0)
    (h12 : P1.1 ≠ P2.1)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (rho1 rho2 : F p)
    (hrhoRoot1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).IsRoot rho1)
    (hrhoRoot2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).IsRoot rho2)
    (hrhone : rho1 ≠ rho2)
    (Ptrho1 Ptrho2 : Hc.Point)
    (hPtrho1X : Ptrho1.X = rho1)
    (hPtrho1Y : Ptrho1.Y = -(vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).eval rho1)
    (hPtrho1Y_ne : Ptrho1.Y ≠ 0)
    (hPtrho2X : Ptrho2.X = rho2)
    (hPtrho2Y : Ptrho2.Y = -(vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).eval rho2)
    (hPtrho2Y_ne : Ptrho2.Y ≠ 0)
    (U : Polynomial (F p))
    (hU_def : U = C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff *
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    divToPair U (0 : Polynomial (F p))
        ({Ptrho1, Ptrho2, Point.iota Ptrho1, Point.iota Ptrho2} : Finset Hc.Point) =
      single Ptrho1 + single Ptrho2 + single (Point.iota Ptrho1) + single (Point.iota Ptrho2) := by
  have hmonic : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).Monic :=
    uRS4General_monic p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hcurne
  have hdeg2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).natDegree = 2 :=
    uRS4General_natDegree_eq_two p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1
      hlead h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target
  -- Split `uRS4General` into its two named linear factors.
  have hsplit : uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
      (X - C rho1) * (X - C rho2) :=
    quadratic_eq_mul_X_sub_C p hmonic hdeg2 hrhoRoot1 hrhoRoot2 hrhone
  have h_bot1 : pointIdeal Ptrho1 ≠ ⊥ := pointIdeal_ne_bot Ptrho1
  have h_bot2 : pointIdeal Ptrho2 ≠ ⊥ := pointIdeal_ne_bot Ptrho2
  -- `ordAt = 1` at `Ptrho1`: `hUfac` witnessed by `Fco := X - C rho2`,
  -- nonvanishing at `rho1` since `rho1 ≠ rho2`.
  have hUfac1 : ∃ Fco : Polynomial (F p),
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = linX Ptrho1.X * Fco ∧
        Fco.eval Ptrho1.X ≠ 0 := by
    refine ⟨X - C rho2, ?_, ?_⟩
    · rw [hsplit, hPtrho1X]; unfold linX; ring
    · rw [hPtrho1X]
      simp only [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.mpr hrhone
  have hOrdRho1 : ordAt Ptrho1 U (0 : Polynomial (F p)) = 1 :=
    ordAt_eq_one_of_uRS4General_root p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
      P1 P2 hcurne Ptrho1 h_bot1 hPtrho1Y_ne hUfac1 U hU_def
  -- `ordAt = 1` at `Ptrho2`: `hUfac` witnessed by `Fco := X - C rho1`,
  -- nonvanishing at `rho2` since `rho1 ≠ rho2`.
  have hUfac2 : ∃ Fco : Polynomial (F p),
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 = linX Ptrho2.X * Fco ∧
        Fco.eval Ptrho2.X ≠ 0 := by
    refine ⟨X - C rho1, ?_, ?_⟩
    · rw [hsplit, hPtrho2X]; unfold linX; ring
    · rw [hPtrho2X]
      simp only [eval_sub, eval_X, eval_C]
      exact sub_ne_zero.mpr hrhone.symm
  have hOrdRho2 : ordAt Ptrho2 U (0 : Polynomial (F p)) = 1 :=
    ordAt_eq_one_of_uRS4General_root p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
      P1 P2 hcurne Ptrho2 h_bot2 hPtrho2Y_ne hUfac2 U hU_def
  -- The conjugates: `ι Ptrho1 ≠ Ptrho1` (unramified, `Y ≠ 0`), so
  -- `ordAt` at each conjugate is ALSO `1` — `U`'s value has no
  -- `y`-dependence, so `ordAt (ι P) U 0` depends only on `(ι P).X = P.X`,
  -- hence equals `ordAt P U 0` (the residual-point valuation only sees
  -- `.X`, not the branch of `y` over it, for a `y`-free polynomial).
  have hiota_ord1 : ordAt (Point.iota Ptrho1) U (0 : Polynomial (F p)) = 1 := by
    have h_bot1' : pointIdeal (Point.iota Ptrho1) ≠ ⊥ := pointIdeal_ne_bot (Point.iota Ptrho1)
    have hUfac1' : ∃ Fco : Polynomial (F p),
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
          linX (Point.iota Ptrho1).X * Fco ∧ Fco.eval (Point.iota Ptrho1).X ≠ 0 := by
      rw [Point.iota_X]; exact hUfac1
    have hiotaY_ne : (Point.iota Ptrho1).Y ≠ 0 := by
      rw [Point.iota_Y]; exact neg_ne_zero.mpr hPtrho1Y_ne
    exact ordAt_eq_one_of_uRS4General_root p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
      P1 P2 hcurne (Point.iota Ptrho1) h_bot1' hiotaY_ne hUfac1' U hU_def
  have hiota_ord2 : ordAt (Point.iota Ptrho2) U (0 : Polynomial (F p)) = 1 := by
    have h_bot2' : pointIdeal (Point.iota Ptrho2) ≠ ⊥ := pointIdeal_ne_bot (Point.iota Ptrho2)
    have hUfac2' : ∃ Fco : Polynomial (F p),
        uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 =
          linX (Point.iota Ptrho2).X * Fco ∧ Fco.eval (Point.iota Ptrho2).X ≠ 0 := by
      rw [Point.iota_X]; exact hUfac2
    have hiotaY_ne : (Point.iota Ptrho2).Y ≠ 0 := by
      rw [Point.iota_Y]; exact neg_ne_zero.mpr hPtrho2Y_ne
    exact ordAt_eq_one_of_uRS4General_root p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
      P1 P2 hcurne (Point.iota Ptrho2) h_bot2' hiotaY_ne hUfac2' U hU_def
  -- Pairwise distinctness of the four named points.
  have hne_of_X : ∀ {Q1 Q2 : Hc.Point}, Q1.X ≠ Q2.X → Q1 ≠ Q2 :=
    fun hX heq => hX (heq ▸ rfl)
  have hrho12' : Ptrho1 ≠ Ptrho2 := hne_of_X (hPtrho1X ▸ hPtrho2X ▸ hrhone)
  have hiota1_ne_self : Point.iota Ptrho1 ≠ Ptrho1 :=
    Point.iota_ne_self_of_Y_ne_zero hchar hPtrho1Y_ne
  have hiota2_ne_self : Point.iota Ptrho2 ≠ Ptrho2 :=
    Point.iota_ne_self_of_Y_ne_zero hchar hPtrho2Y_ne
  have hiota1_ne_rho2 : Point.iota Ptrho1 ≠ Ptrho2 :=
    hne_of_X (by rw [Point.iota_X, hPtrho1X, hPtrho2X]; exact hrhone)
  have hiota2_ne_rho1 : Point.iota Ptrho2 ≠ Ptrho1 :=
    hne_of_X (by rw [Point.iota_X, hPtrho2X, hPtrho1X]; exact hrhone.symm)
  have hiota_ne : Point.iota Ptrho1 ≠ Point.iota Ptrho2 :=
    hne_of_X (by rw [Point.iota_X, Point.iota_X, hPtrho1X, hPtrho2X]; exact hrhone)
  apply eq_of_coeffAt_eq
  intro P
  rw [coeffAt_divToPair]
  simp only [map_add, coeffAt_single]
  by_cases hEq1 : P = Ptrho1
  · rw [hEq1]
    simpa [hOrdRho1, hrho12', hiota1_ne_self.symm, hiota2_ne_rho1.symm]
  by_cases hEq2 : P = Ptrho2
  · rw [hEq2]
    simpa [hOrdRho2, hrho12'.symm, hiota1_ne_rho2.symm, hiota2_ne_self.symm]
  by_cases hEqI1 : P = Point.iota Ptrho1
  · rw [hEqI1]
    simpa [hiota_ord1, hiota1_ne_self, hiota1_ne_rho2, hiota_ne]
  by_cases hEqI2 : P = Point.iota Ptrho2
  · rw [hEqI2]
    simpa [hiota_ord2, hiota2_ne_self, hiota2_ne_rho1, hiota_ne.symm]
  · have hnmemS : P ∉ ({Ptrho1, Ptrho2, Point.iota Ptrho1, Point.iota Ptrho2} : Finset Hc.Point) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hEq1, hEq2, hEqI1, hEqI2⟩
    simp only [if_neg hnmemS, if_neg hEq1, if_neg hEq2, if_neg hEqI1, if_neg hEqI2]
    ring

/-- **Step 2 itself: `div_aff(g) - div_aff(u_new) = A+C+T - ρ - I`, fully-
split case, as a literal `Divisor Hc` equality.** Direct combination of
step 1's `divToPair_eq_A_add_C_add_T_of_split` (`PrincipalWitnessStep1.lean`)
with this file's `divToPair_eq_rho_add_I_of_split` above via plain
`Divisor Hc`-level subtraction (`Divisor Hc` is a full `AddCommGroup`, so
this is a `congrArg₂`/`rw`-level step, no new mathematics). Per the
roadmap's "Workflow reminders", this identity carries no `δ₀` term — the
LHS is a difference of two literal, affine-only `Divisor Hc` values, and
`Divisor Hc` has no infinity-coefficient slot for one to hide in. The
hypothesis list is the union of both composed theorems' hypothesis lists
(all six named old/target points from step 1, plus `u_new`'s own two named
roots and their conjugates from this file), stated flatly rather than via
an intermediate structure, matching this project's general preference for
explicit hypotheses over bundled records at this stage. -/
theorem divToPair_sub_eq_A_add_C_add_T_sub_rho_sub_I_of_split
    [DecidableEq Hc.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree Hc.f)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1 : F p)
    (hf : Hc.f = curvePoly p c0 c1 c2 c3 c4)
    (P1 P2 : F p × F p)
    (Ra1 Ra2 R1 R2 : F p)
    (hne34 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)) ≠ X ^ 2 + C u1 * X + C u0)
    (hnoroot34 : ¬ ∃ r : F p, (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval r = 0 ∧
        (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval r = 0)
    (h12 : P1.1 ≠ P2.1)
    (hlead : coeffsOut4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ⟨6, by norm_num⟩ ≠ 0)
    (hP1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P1.1 = 0)
    (hP1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P1.1 = 0)
    (hP2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval P2.1 = 0)
    (hP2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval P2.1 = 0)
    (huaRoot1 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra1)
    (huaRoot2 : (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).IsRoot Ra2)
    (hRane : Ra1 ≠ Ra2)
    (hRa1P1 : Ra1 ≠ P1.1) (hRa1P2 : Ra1 ≠ P2.1)
    (hRa1target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra1 = 0)
    (hRa2P1 : Ra2 ≠ P1.1) (hRa2P2 : Ra2 ≠ P2.1)
    (hRa2target : ¬ (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).eval Ra2 = 0)
    (htargetRoot1 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R1)
    (htargetRoot2 : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).IsRoot R2)
    (hRne : R1 ≠ R2)
    (hR1P1 : R1 ≠ P1.1) (hR1P2 : R1 ≠ P2.1)
    (hR1ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R1 = 0)
    (hR2P1 : R2 ≠ P1.1) (hR2P2 : R2 ≠ P2.1)
    (hR2ua : ¬ (X ^ 2 + C ua1 * X + C ua0 : Polynomial (F p)).eval R2 = 0)
    (hRa1R1 : Ra1 ≠ R1) (hRa1R2 : Ra1 ≠ R2) (hRa2R1 : Ra2 ≠ R1) (hRa2R2 : Ra2 ≠ R2)
    (hA : MatrixNondegenerate4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hP1_curve : P1.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P1.1)
    (hP2_curve : P2.2 ^ 2 = (curvePoly p c0 c1 c2 c3 c4).eval P2.1)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hcurne : curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 ≠ 0)
    (hYP1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hYP2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hYRa1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra1 ≠ 0)
    (hYRa2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra2 ≠ 0)
    (hYR1_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (hYR2_ne : (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (hU_evalP1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P1.1 ≠ 0)
    (hU_evalP2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval P2.1 ≠ 0)
    (hU_evalRa1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra1 ≠ 0)
    (hU_evalRa2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval Ra2 ≠ 0)
    (hU_evalR1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R1 ≠ 0)
    (hU_evalR2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).eval R2 ≠ 0)
    (Pt1 Pt2 PtRa1 PtRa2 PtR1 PtR2 : Hc.Point)
    (hPt1X : Pt1.X = P1.1) (hPt1Y : Pt1.Y = P1.2) (hPt1Y_ne : Pt1.Y ≠ 0)
    (hPt2X : Pt2.X = P2.1) (hPt2Y : Pt2.Y = P2.2) (hPt2Y_ne : Pt2.Y ≠ 0)
    (hPtRa1X : PtRa1.X = Ra1) (hPtRa1Y : PtRa1.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra1)
    (hPtRa1Y_ne : PtRa1.Y ≠ 0)
    (hPtRa2X : PtRa2.X = Ra2) (hPtRa2Y : PtRa2.Y = (C va1 * X + C va0 : Polynomial (F p)).eval Ra2)
    (hPtRa2Y_ne : PtRa2.Y ≠ 0)
    (hPtR1X : PtR1.X = R1) (hPtR1Y : PtR1.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R1)
    (hPtR1Y_ne : PtR1.Y ≠ 0)
    (hPtR2X : PtR2.X = R2) (hPtR2Y : PtR2.Y = (C v1 * X + C v0 : Polynomial (F p)).eval R2)
    (hPtR2Y_ne : PtR2.Y ≠ 0)
    (E Y A : Polynomial (F p))
    (hE_def : E = Epoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hY_def : Y = Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
    (hA_def : A = npoly4Lcm4 p P1 P2 ua0 ua1 u0 u1)
    (hgcd : IsCoprime (Ypoly4 p P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1)
      (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1))
    (rho1 rho2 : F p)
    (hrhoRoot1 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).IsRoot rho1)
    (hrhoRoot2 : (uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).IsRoot rho2)
    (hrhone : rho1 ≠ rho2)
    (Ptrho1 Ptrho2 : Hc.Point)
    (hPtrho1X : Ptrho1.X = rho1)
    (hPtrho1Y : Ptrho1.Y = -(vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).eval rho1)
    (hPtrho1Y_ne : Ptrho1.Y ≠ 0)
    (hPtrho2X : Ptrho2.X = rho2)
    (hPtrho2Y : Ptrho2.Y = -(vRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1 hgcd).eval rho2)
    (hPtrho2Y_ne : Ptrho2.Y ≠ 0)
    (U : Polynomial (F p))
    (hU_def : U = C (curBeforeMonic4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1).leadingCoeff *
      uRS4General p c0 c1 c2 c3 c4 P1 P2 ua0 ua1 va0 va1 u0 u1 v0 v1) :
    divToPair E Y ({Pt1, Pt2, PtRa1, PtRa2, PtR1, PtR2} : Finset Hc.Point) -
      divToPair U (0 : Polynomial (F p))
        ({Ptrho1, Ptrho2, Point.iota Ptrho1, Point.iota Ptrho2} : Finset Hc.Point) =
      single Pt1 + single Pt2 + single PtRa1 + single PtRa2 + single PtR1 + single PtR2 -
        (single Ptrho1 + single Ptrho2 + single (Point.iota Ptrho1) + single (Point.iota Ptrho2)) := by
  rw [divToPair_eq_A_add_C_add_T_of_split p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
      hf P1 P2 Ra1 Ra2 R1 R2 hne34 hnoroot34 h12 hP1ua hP1target hP2ua hP2target
      huaRoot1 huaRoot2 hRane hRa1P1 hRa1P2 hRa1target hRa2P1 hRa2P2 hRa2target
      htargetRoot1 htargetRoot2 hRne hR1P1 hR1P2 hR1ua hR2P1 hR2P2 hR2ua
      hRa1R1 hRa1R2 hRa2R1 hRa2R2
      hA hP1_curve hP2_curve hMumfordUa hMumfordTarget hcurne
      hYP1_ne hYP2_ne hYRa1_ne hYRa2_ne hYR1_ne hYR2_ne
      hU_evalP1 hU_evalP2 hU_evalRa1 hU_evalRa2 hU_evalR1 hU_evalR2
      Pt1 Pt2 PtRa1 PtRa2 PtR1 PtR2
      hPt1X hPt1Y hPt1Y_ne hPt2X hPt2Y hPt2Y_ne
      hPtRa1X hPtRa1Y hPtRa1Y_ne hPtRa2X hPtRa2Y hPtRa2Y_ne
      hPtR1X hPtR1Y hPtR1Y_ne hPtR2X hPtR2Y hPtR2Y_ne
      E Y A hE_def hY_def hA_def,
    divToPair_eq_rho_add_I_of_split p hchar hsf c0 c1 c2 c3 c4 ua0 ua1 va0 va1 u0 u1 v0 v1
      hf P1 P2 hlead h12 hne34 hnoroot34 hP1ua hP1target hP2ua hP2target hcurne
      hgcd rho1 rho2 hrhoRoot1 hrhoRoot2 hrhone
      Ptrho1 Ptrho2 hPtrho1X hPtrho1Y hPtrho1Y_ne hPtrho2X hPtrho2Y hPtrho2Y_ne
      U hU_def]

end DecoupledSystem
end Genus2Lean
