import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.LCanonicalElementary

/-! # The `f-` witness for `ROADMAP-principal-witness-assembly.md`'s
`A + T` construction (companion to `TangentMumfordWitness.lean`'s `f+`)

Per that roadmap's "Round 2 verdict / new target" section: `f- := y -
b_-(x)`, where `b_-` is the UNIQUE degree-≤3 polynomial solving the
**CRT/Cantor-addition congruences**

    b_- ≡ vC  (mod uC)      -- `C`'s own Mumford `v`-coefficient, `uC :=
                                X²+C c1*X+C c0`, `vC := C vC1*X + C vC0`
    b_- ≡ -vA (mod uA)      -- `-A`'s Mumford data, `uA := X²+C a1*X+C a0`,
                                `vA := C vA1*X + C vA0` (negated: this
                                witness needs `C + ι(A)`, NOT `C+A`, per
                                `CHATGPT-REPLY-step3-reduce-correctness.md`
                                §2-3 and the roadmap's own Round 1/2
                                write-up)

This is the classical Cantor-addition step for two degree-2 Mumford
divisors, done at the polynomial/coefficient level (per ChatGPT's own
recommendation: "the cleanest route may... formulate the residual
divisor initially at the polynomial/Mumford level rather than
immediately splitting it into `R1,R2`" — this file follows that advice,
taking `uC,uA,vC,vA`'s four coefficients as bare `k`-field inputs, never
naming or splitting either quadratic's roots).

**Why a 4×4 linear system, not a hand-derived Bezout/CRT closed form.**
A direct Bezout computation (find `s,t` with `s·uC+t·uA=1`, then
`v = vC·t·uA - vA·s·uC mod uC·uA`) was tried by hand first and produces
correct but extremely unwieldy closed-form coefficients (each a ratio of
degree-4 polynomials in `a0,a1,c0,c1` over their shared resultant). Per
this project's own conventions (deep, error-prone algebra is exactly
what should be avoided in favor of something mechanically checkable),
the congruences were instead unfolded directly into 4 LINEAR equations
on `b_-`'s 4 unknown coefficients (`b0,b1,b2,b3`) — `v mod uC` and
`v mod uA` are each computed by ordinary polynomial division by a monic
quadratic, giving 2 linear conditions apiece, no root-splitting or
Bezout identity needed at all. This is the exact same idiom
`TangentMumfordWitness.lean`'s `bPlus`/`tangentInterpMatrix` already
uses (Cramer's rule on an explicit 4×4 matrix) — `bMinus` below is that
same machinery, one new 4×4 matrix, confirmed independently via sympy
(`sympy.rem(Poly(b0+b1*X+b2*X²+b3*X³,X), Poly(X²+c1*X+c0,X))` etc.,
matched against the matrix rows below term-by-term before writing any
Lean).

**The matrix, derived (sympy-confirmed) as:**
```
row 0 (const. coeff of  b_- mod uC = vC):   b0        - c0*b2 + c0*c1*b3        = vC0
row 1 (X coeff of       b_- mod uC = vC):        b1  - c1*b2 + (c1²-c0)*b3      = vC1
row 2 (const. coeff of  b_- mod uA = -vA):  b0        - a0*b2 + a0*a1*b3        = -vA0
row 3 (X coeff of       b_- mod uA = -vA):       b1  - a1*b2 + (a1²-a0)*b3      = -vA1
```
**Determinant, confirmed (sympy) to equal `Res(uC,uA)`** (the resultant
of the two quadratics) — nonzero exactly when `uC,uA` are coprime, i.e.
share no common root, the natural nondegeneracy hypothesis (`C` and `A`
disjoint as point-pairs). No further factorization of this resultant is
attempted or needed; it is used only as an opaque nonzero scalar via
`hdet`, exactly as `tangentInterpMatrix_det_ne_zero`'s conclusion is used
by `bPlus`'s row lemmas without ever re-deriving its closed form at a
call site.

**Status: 0-`sorry`.** `cantorAddMatrix_det_ne_zero` is closed via a
kernel-vector argument (`Matrix.exists_mulVec_eq_zero_iff` gives a
nonzero kernel vector from `det = 0`; its rows unfold via
`modByMonic_uCPoly_eq`/`modByMonic_uAPoly_eq` to a degree contradiction
against coprimality — no resultant needed). Both `bMinus_mod_*`
congruence theorems (`bMinus_mod_uC_eq_vC`, `bMinus_mod_uA_eq_neg_vA`)
are filled via that same closed-form-remainder pair composed with
Cramer's-rule row extraction (`bMinus_coeff0_coeff1`/
`bMinus_coeff2_coeff3`). `bMinus_ordInfOfPair` (added this pass, mirrors
`bPlus_ordInfOfPair`'s weakened `hlead`-on-top-coefficient shape) gives
`ordInfOfPair(-bMinus,1) = -6`, matching `f+`'s own `-6` exactly — the
matched pole order the roadmap's "Round 2 verdict" pairing needs. Not
yet build-tested (no live Lean toolchain in this environment) — Claire's
REPL to confirm, per this project's own workflow convention.

**Still open (unchanged from before, genuinely ChatGPT-worthy):** the
divisor-level facts — `div_aff(y - bMinus) ⊇ A + T` (or the `ι`-conjugated
version matching the `bMinus ≡ -vA mod uA` sign convention already fixed
here) plus the matching degree-1 residual `[R]`, and confirming this `R`
is the SAME `R` as `f+`'s own residual. This is the next thing to hand to
ChatGPT — the sign/labeling conventions and both pole orders (`-6`/`-6`)
are now pinned down in actual Lean, not guessed in prose. -/

noncomputable section

set_option maxHeartbeats 5000000
-- The explicit polynomial division/Cramer proofs below normalize several nested
-- `Fin`/`Matrix`/`Polynomial.C` expressions; the larger budget is local to this file.

open Polynomial
open HyperellipticPolynomial

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k]

/-- **The 4×4 Cantor-addition matrix.** Unknowns are `b_-`'s four
coefficients `(b0,b1,b2,b3)`. Rows 0-1: the two coefficients of
`b_- mod uC` (`uC := X²+C c1*X+C c0`), matched against `vC`'s own two
coefficients. Rows 2-3: the two coefficients of `b_- mod uA`
(`uA := X²+C a1*X+C a0`), matched against `-vA`'s two coefficients.
Confirmed against sympy's `Poly.rem` before being written down (see
module docstring). -/
def cantorAddMatrix (c0 c1 a0 a1 : k) : Matrix (Fin 4) (Fin 4) k :=
  !![1, 0, -c0,      c0 * c1;
     0, 1, -c1,      c1 ^ 2 - c0;
     1, 0, -a0,      a0 * a1;
     0, 1, -a1,      a1 ^ 2 - a0]

/-- **The RHS vector for `b_-`'s 4×4 solve.** Rows 0-1: `vC`'s own
coefficients `vC0, vC1`. Rows 2-3: `-vA`'s coefficients, `-vA0, -vA1` —
the negation is exactly the `ι(A)` (hyperelliptic-conjugate-of-`A`)
substitution `CHATGPT-REPLY-step3-reduce-correctness.md` identifies as
the fix for the theorem's subtraction-shaped target (`C - A`, not
`C + A`). -/
def cantorAddRHS (vC0 vC1 vA0 vA1 : k) : Fin 4 → k :=
  ![vC0, vC1, -vA0, -vA1]

/-- **The quadratic `uC := X² + C c1 * X + C c0`.** Named once here so
the kernel-vector argument below and both row lemmas share the exact
same term (avoids any risk of an accidental definitional mismatch
between `unfold`-ed occurrences). -/
def uCPoly (c0 c1 : k) : Polynomial k := (X : k[X]) ^ 2 + Polynomial.C c1 * X + Polynomial.C c0

/-- **The quadratic `uA := X² + C a1 * X + C a0`.** -/
def uAPoly (a0 a1 : k) : Polynomial k := (X : k[X]) ^ 2 + Polynomial.C a1 * X + Polynomial.C a0

@[simp] theorem uCPoly_monic (c0 c1 : k) : (uCPoly c0 c1 : k[X]).Monic := by
  unfold uCPoly
  monicity!

@[simp] theorem uAPoly_monic (a0 a1 : k) : (uAPoly a0 a1 : k[X]).Monic := by
  unfold uAPoly
  monicity!

/-- **Degree-≤3 quotient-remainder identity for `uCPoly`.** For ANY
`b0,b1,b2,b3`, writing `q := C b0 + C b1*X + C b2*X² + C b3*X³`, this is
the explicit division `q = uCPoly*(C b3*X + C(b2-b3*c1)) + (remainder)`,
confirmed against sympy's `Poly.div` before being written down (module
docstring). Purely a `ring` identity — no coprimality or nonvanishing
needed for this lemma itself, it is shared by both the kernel-vector
argument (`cantorAddMatrix_det_ne_zero`) and `bMinus_mod_uC_eq_vC`. -/
private theorem uCPoly_div_eq (c0 c1 b0 b1 b2 b3 : k) :
    (Polynomial.C b1 - Polynomial.C b2 * Polynomial.C c1 - Polynomial.C b3 * Polynomial.C c0 +
        Polynomial.C b3 * Polynomial.C c1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C c0 +
        Polynomial.C b3 * Polynomial.C c0 * Polynomial.C c1) +
      uCPoly c0 c1 * (Polynomial.C b3 * X + (Polynomial.C b2 - Polynomial.C b3 * Polynomial.C c1)) =
      Polynomial.C b0 + Polynomial.C b1 * X + Polynomial.C b2 * X ^ 2 + Polynomial.C b3 * X ^ 3 := by
  unfold uCPoly
  ring

/-- **Degree-≤3 quotient-remainder identity for `uAPoly`.** Same shape as
`uCPoly_div_eq`, `a0,a1` in place of `c0,c1`. -/
private theorem uAPoly_div_eq (a0 a1 b0 b1 b2 b3 : k) :
    (Polynomial.C b1 - Polynomial.C b2 * Polynomial.C a1 - Polynomial.C b3 * Polynomial.C a0 +
        Polynomial.C b3 * Polynomial.C a1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C a0 +
        Polynomial.C b3 * Polynomial.C a0 * Polynomial.C a1) +
      uAPoly a0 a1 * (Polynomial.C b3 * X + (Polynomial.C b2 - Polynomial.C b3 * Polynomial.C a1)) =
      Polynomial.C b0 + Polynomial.C b1 * X + Polynomial.C b2 * X ^ 2 + Polynomial.C b3 * X ^ 3 := by
  unfold uAPoly
  ring

/-- **`q %ₘ uCPoly` in closed form, for `q`'s coefficients `b0,b1,b2,b3`.**
Immediate from `uCPoly_div_eq` plus `Polynomial.div_modByMonic_unique`
(the remainder's `degree < 2 = degree uCPoly` since it's an explicit
linear polynomial, `Polynomial.degree_linear_le`-style bound). -/
private theorem modByMonic_uCPoly_eq (c0 c1 b0 b1 b2 b3 : k) :
    (Polynomial.C b0 + Polynomial.C b1 * X + Polynomial.C b2 * X ^ 2 + Polynomial.C b3 * X ^ 3)
        %ₘ uCPoly c0 c1 =
      (Polynomial.C b1 - Polynomial.C b2 * Polynomial.C c1 - Polynomial.C b3 * Polynomial.C c0 +
          Polynomial.C b3 * Polynomial.C c1 ^ 2) * X +
        (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C c0 +
          Polynomial.C b3 * Polynomial.C c0 * Polynomial.C c1) := by
  have hdeg : ((Polynomial.C b1 - Polynomial.C b2 * Polynomial.C c1 -
        Polynomial.C b3 * Polynomial.C c0 + Polynomial.C b3 * Polynomial.C c1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C c0 +
        Polynomial.C b3 * Polynomial.C c0 * Polynomial.C c1) : k[X]).degree <
      (uCPoly c0 c1 : k[X]).degree := by
    have hlin : ((Polynomial.C b1 - Polynomial.C b2 * Polynomial.C c1 -
        Polynomial.C b3 * Polynomial.C c0 + Polynomial.C b3 * Polynomial.C c1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C c0 +
        Polynomial.C b3 * Polynomial.C c0 * Polynomial.C c1) : k[X]).degree < 2 := by
      convert (Polynomial.degree_linear_lt
        (a := b1 - b2 * c1 - b3 * c0 + b3 * c1 ^ 2)
        (b := b0 - b2 * c0 + b3 * c0 * c1)) using 1 <;>
        simp only [map_sub, map_add, map_mul, map_pow]
    have hCdeg : (uCPoly c0 c1 : k[X]).degree = 2 := by
      change ((X : k[X]) ^ 2 + Polynomial.C c1 * X + Polynomial.C c0).degree = 2
      convert (Polynomial.degree_quadratic (a := (1 : k)) (b := c1) (c := c0) (by simp)) using 1 <;>
        simp
    rw [hCdeg]
    exact hlin
  exact ((Polynomial.div_modByMonic_unique
    (Polynomial.C b3 * X + (Polynomial.C b2 - Polynomial.C b3 * Polynomial.C c1))
    ((Polynomial.C b1 - Polynomial.C b2 * Polynomial.C c1 - Polynomial.C b3 * Polynomial.C c0 +
        Polynomial.C b3 * Polynomial.C c1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C c0 +
        Polynomial.C b3 * Polynomial.C c0 * Polynomial.C c1))
    (uCPoly_monic c0 c1) ⟨uCPoly_div_eq c0 c1 b0 b1 b2 b3, hdeg⟩).2)

/-- **`q %ₘ uAPoly` in closed form.** Mirror of `modByMonic_uCPoly_eq`. -/
private theorem modByMonic_uAPoly_eq (a0 a1 b0 b1 b2 b3 : k) :
    (Polynomial.C b0 + Polynomial.C b1 * X + Polynomial.C b2 * X ^ 2 + Polynomial.C b3 * X ^ 3)
        %ₘ uAPoly a0 a1 =
      (Polynomial.C b1 - Polynomial.C b2 * Polynomial.C a1 - Polynomial.C b3 * Polynomial.C a0 +
          Polynomial.C b3 * Polynomial.C a1 ^ 2) * X +
        (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C a0 +
          Polynomial.C b3 * Polynomial.C a0 * Polynomial.C a1) := by
  have hdeg : ((Polynomial.C b1 - Polynomial.C b2 * Polynomial.C a1 -
        Polynomial.C b3 * Polynomial.C a0 + Polynomial.C b3 * Polynomial.C a1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C a0 +
        Polynomial.C b3 * Polynomial.C a0 * Polynomial.C a1) : k[X]).degree <
      (uAPoly a0 a1 : k[X]).degree := by
    have hlin : ((Polynomial.C b1 - Polynomial.C b2 * Polynomial.C a1 -
        Polynomial.C b3 * Polynomial.C a0 + Polynomial.C b3 * Polynomial.C a1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C a0 +
        Polynomial.C b3 * Polynomial.C a0 * Polynomial.C a1) : k[X]).degree < 2 := by
      convert (Polynomial.degree_linear_lt
        (a := b1 - b2 * a1 - b3 * a0 + b3 * a1 ^ 2)
        (b := b0 - b2 * a0 + b3 * a0 * a1)) using 1 <;>
        simp only [map_sub, map_add, map_mul, map_pow]
    have hAdeg : (uAPoly a0 a1 : k[X]).degree = 2 := by
      change ((X : k[X]) ^ 2 + Polynomial.C a1 * X + Polynomial.C a0).degree = 2
      convert (Polynomial.degree_quadratic (a := (1 : k)) (b := a1) (c := a0) (by simp)) using 1 <;>
        simp
    rw [hAdeg]
    exact hlin
  exact ((Polynomial.div_modByMonic_unique
    (Polynomial.C b3 * X + (Polynomial.C b2 - Polynomial.C b3 * Polynomial.C a1))
    ((Polynomial.C b1 - Polynomial.C b2 * Polynomial.C a1 - Polynomial.C b3 * Polynomial.C a0 +
        Polynomial.C b3 * Polynomial.C a1 ^ 2) * X +
      (Polynomial.C b0 - Polynomial.C b2 * Polynomial.C a0 +
        Polynomial.C b3 * Polynomial.C a0 * Polynomial.C a1))
    (uAPoly_monic a0 a1) ⟨uAPoly_div_eq a0 a1 b0 b1 b2 b3, hdeg⟩).2)

/-- **Nondegeneracy of the 4×4 Cantor-addition system, proved directly
from `IsCoprime`, no resultant needed.** Earlier draft of this file
planned to go via a closed-form determinant `= Res(uC,uA)` plus a
resultant-nonvanishing-iff-coprime Mathlib lemma; no such lemma was
found in the Mathlib4 API surface searched, so this pass instead proves
it directly: **kernel-vector argument.** If `det = 0`, `cantorAddMatrix`
has a nonzero vector `b` in its (right) kernel (`Matrix.exists_mulVec_eq_zero_iff`
kind of statement — via `¬(det ≠ 0) → ¬Function.Injective (mulVec M) →
∃ b ≠ 0, M.mulVec b = 0`, `LinearMap` non-injectivity from `det = 0`).
Writing `q := C b0+C b1*X+C b2*X²+C b3*X³`, `M.mulVec b = 0`'s four rows
are EXACTLY `q %ₘ uCPoly = 0` (rows 0-1, via `modByMonic_uCPoly_eq`
above with the RHS's `vC0=vC1=0` specialization) and `q %ₘ uAPoly = 0`
(rows 2-3, similarly) — so `uCPoly ∣ q` and `uAPoly ∣ q`
(`Polynomial.modByMonic_eq_zero_iff_dvd`). By `hcoprime`,
`uCPoly*uAPoly ∣ q` (`IsCoprime.mul_dvd`). But `deg q ≤ 3 <
4 = deg(uCPoly*uAPoly)`, forcing `q = 0` (a nonzero multiple of a
degree-4 polynomial has degree ≥ 4) — hence `b = 0`, contradicting `b ≠
0`. **Found the needed lemma this pass:** `Matrix.exists_mulVec_eq_zero_iff`
(`Mathlib.LinearAlgebra.Matrix.ToLinearEquiv` — `[Fintype n] [DecidableEq
n] [CommRing A] [IsDomain A] {M : Matrix n n A} : (∃ v ≠ 0, M.mulVec v =
0) ↔ M.det = 0`), applicable here since a field is an `IsDomain`. -/
theorem cantorAddMatrix_det_ne_zero (c0 c1 a0 a1 : k)
    (hcoprime : IsCoprime (uCPoly c0 c1 : k[X]) (uAPoly a0 a1 : k[X])) :
    (cantorAddMatrix c0 c1 a0 a1).det ≠ 0 := by
  intro hdet0
  obtain ⟨b, hbne, hbker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  set q : k[X] := Polynomial.C (b 0) + Polynomial.C (b 1) * X +
    Polynomial.C (b 2) * X ^ 2 + Polynomial.C (b 3) * X ^ 3 with hq
  have hrow0 : b 0 - c0 * b 2 + c0 * c1 * b 3 = 0 := by
    have h := congrFun hbker (0 : Fin 4)
    simp only [Matrix.mulVec, dotProduct, cantorAddMatrix, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Pi.zero_apply] at h
    linear_combination h
  have hrow1 : b 1 - c1 * b 2 + (c1 ^ 2 - c0) * b 3 = 0 := by
    have h := congrFun hbker (1 : Fin 4)
    simp only [Matrix.mulVec, dotProduct, cantorAddMatrix, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Pi.zero_apply] at h
    linear_combination h
  have hrow2 : b 0 - a0 * b 2 + a0 * a1 * b 3 = 0 := by
    have h := congrFun hbker (2 : Fin 4)
    simp only [Matrix.mulVec, dotProduct, cantorAddMatrix, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Pi.zero_apply] at h
    linear_combination h
  have hrow3 : b 1 - a1 * b 2 + (a1 ^ 2 - a0) * b 3 = 0 := by
    have h := congrFun hbker (3 : Fin 4)
    simp only [Matrix.mulVec, dotProduct, cantorAddMatrix, Fin.sum_univ_four,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three, Pi.zero_apply] at h
    linear_combination h
  -- `q %ₘ uCPoly = 0` from rows 0-1, via `modByMonic_uCPoly_eq` at `vC0=vC1=0`.
  have hqC : q %ₘ (uCPoly c0 c1 : k[X]) = 0 := by
    rw [hq, modByMonic_uCPoly_eq]
    have e0 : Polynomial.C (b 0) - Polynomial.C (b 2) * Polynomial.C c0 +
        Polynomial.C (b 3) * Polynomial.C c0 * Polynomial.C c1 = 0 := by
      have hc := congrArg Polynomial.C hrow0
      simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hc
      linear_combination hc
    have e1 : Polynomial.C (b 1) - Polynomial.C (b 2) * Polynomial.C c1 -
        Polynomial.C (b 3) * Polynomial.C c0 + Polynomial.C (b 3) * Polynomial.C c1 ^ 2 = 0 := by
      have hc := congrArg Polynomial.C hrow1
      simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hc
      linear_combination hc
    rw [e1, e0]; simp
  -- `q %ₘ uAPoly = 0` from rows 2-3, via `modByMonic_uAPoly_eq` at `vA0=vA1=0`
  -- (using `-vA0=0 ↔ vA0=0`, likewise `vA1`).
  have hqA : q %ₘ (uAPoly a0 a1 : k[X]) = 0 := by
    rw [hq, modByMonic_uAPoly_eq]
    have e0 : Polynomial.C (b 0) - Polynomial.C (b 2) * Polynomial.C a0 +
        Polynomial.C (b 3) * Polynomial.C a0 * Polynomial.C a1 = 0 := by
      have hc := congrArg Polynomial.C hrow2
      simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hc
      linear_combination hc
    have e1 : Polynomial.C (b 1) - Polynomial.C (b 2) * Polynomial.C a1 -
        Polynomial.C (b 3) * Polynomial.C a0 + Polynomial.C (b 3) * Polynomial.C a1 ^ 2 = 0 := by
      have hc := congrArg Polynomial.C hrow3
      simp only [map_sub, map_add, map_mul, map_pow, map_zero] at hc
      linear_combination hc
    rw [e1, e0]; simp
  have hdvdC : (uCPoly c0 c1 : k[X]) ∣ q :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (uCPoly_monic c0 c1)).mp hqC
  have hdvdA : (uAPoly a0 a1 : k[X]) ∣ q :=
    (Polynomial.modByMonic_eq_zero_iff_dvd (uAPoly_monic a0 a1)).mp hqA
  have hdvd : (uCPoly c0 c1 : k[X]) * (uAPoly a0 a1 : k[X]) ∣ q :=
    IsCoprime.mul_dvd hcoprime hdvdC hdvdA
  -- `q`'s coefficients ARE `b`'s entries (immediate from `q`'s own definition), so `q = 0`
  -- forces `b = 0` via `Polynomial.coeff` at `0,1,2,3` — proved first, used in both branches.
  have hcoeff0 : q.coeff 0 = b 0 := by
    simp [hq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hcoeff1 : q.coeff 1 = b 1 := by
    simp [hq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hcoeff2 : q.coeff 2 = b 2 := by
    simp [hq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hcoeff3 : q.coeff 3 = b 3 := by
    simp [hq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hqne : q ≠ 0 := by
    intro hq0
    apply hbne
    have hb0 : b 0 = 0 := by rw [← hcoeff0, hq0, Polynomial.coeff_zero]
    have hb1 : b 1 = 0 := by rw [← hcoeff1, hq0, Polynomial.coeff_zero]
    have hb2 : b 2 = 0 := by rw [← hcoeff2, hq0, Polynomial.coeff_zero]
    have hb3 : b 3 = 0 := by rw [← hcoeff3, hq0, Polynomial.coeff_zero]
    funext i
    match i with
    | 0 => exact hb0
    | 1 => exact hb1
    | 2 => exact hb2
    | 3 => exact hb3
  have hqdeg : q.degree < 4 := by
    rw [hq]
    have hnd : (Polynomial.C (b 0) + Polynomial.C (b 1) * X + Polynomial.C (b 2) * X ^ 2 +
        Polynomial.C (b 3) * X ^ 3 : k[X]).natDegree ≤ 3 := by
      compute_degree
    have hle : (Polynomial.C (b 0) + Polynomial.C (b 1) * X + Polynomial.C (b 2) * X ^ 2 +
        Polynomial.C (b 3) * X ^ 3 : k[X]).degree ≤ (3 : ℕ) :=
      Polynomial.degree_le_of_natDegree_le hnd
    exact lt_of_le_of_lt hle (by exact_mod_cast (by norm_num : (3 : ℕ) < 4))
  have hCdeg : (uCPoly c0 c1 : k[X]).degree = 2 := by
    simpa [uCPoly, one_mul] using
      (Polynomial.degree_quadratic (a := (1 : k)) (b := c1) (c := c0) (by simp))
  have hAdeg : (uAPoly a0 a1 : k[X]).degree = 2 := by
    simpa [uAPoly, one_mul] using
      (Polynomial.degree_quadratic (a := (1 : k)) (b := a1) (c := a0) (by simp))
  have hprod_deg : ((uCPoly c0 c1 : k[X]) * (uAPoly a0 a1 : k[X])).degree = 4 := by
    rw [Polynomial.degree_mul, hCdeg, hAdeg]; norm_num
  have hlt : q.degree < ((uCPoly c0 c1 : k[X]) * (uAPoly a0 a1 : k[X])).degree := by
    rw [hprod_deg]; exact hqdeg
  exact hqne (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hlt)

/-- **`b_-`'s coefficients, via Cramer's rule.** Same idiom as `bPlusCoeff`
(`TangentMumfordWitness.lean`), one new 4×4 system. -/
noncomputable def bMinusCoeff (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k) (i : Fin 4) : k :=
  (cantorAddMatrix c0 c1 a0 a1).det⁻¹ *
    (Matrix.cramer (cantorAddMatrix c0 c1 a0 a1)
      (cantorAddRHS vC0 vC1 vA0 vA1) i)

/-- **`b_-` itself, as a polynomial.** `∑_{i<4} C (bMinusCoeff i) * X^i` —
degree ≤ 3 by construction, same shape as `bPlus`. -/
noncomputable def bMinus (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k) : Polynomial k :=
  Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 0) +
  Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 1) * X +
  Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2) * X ^ 2 +
  Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) * X ^ 3

/-- **`b_-`'s degree bound: `≤ 3`.** Same style as `bPlus_natDegree_le`. -/
theorem bMinus_natDegree_le (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k) :
    (bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1).natDegree ≤ 3 := by
  unfold bMinus
  compute_degree

/-- **`ordInfOfPair(-bMinus, 1) = -6`**, matching `f+`'s
`bPlus_ordInfOfPair` exactly (same weakened `hlead`-on-top-coefficient
shape: `bMinusCoeff ... 3` can vanish for special input data, so it is
an explicit hypothesis, not derived). `A := -bMinus`, `B := 1`:
`ordInfOfPair A B = -(max (2·deg A) (2·deg B + 5))`. `deg B = 0`, second
term `5`. `hlead` plus `bMinus_natDegree_le` pin `deg A = 3` exactly, so
`2·deg A = 6 > 5`, giving `-6` — the same pole order as `f+`, as the
roadmap's "Round 2 verdict" matched-pole-order pairing needs. -/
theorem bMinus_ordInfOfPair (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hlead : bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3 ≠ 0) :
    ordInfOfPair (-bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1) (1 : k[X]) = -6 := by
  have hdeg3 : (bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1).natDegree = 3 := by
    apply le_antisymm (bMinus_natDegree_le c0 c1 a0 a1 vC0 vC1 vA0 vA1)
    unfold bMinus
    have hcoeff3 : (Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 0) +
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 1) * X +
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2) * X ^ 2 +
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) *
        X ^ 3).coeff 3 =
        bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3 := by
      simp [coeff_add, coeff_C_mul, coeff_X_pow]
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff3]; exact hlead)
  have hAdeg :
      (-bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1).natDegree = 3 := by
    rw [natDegree_neg]; exact hdeg3
  unfold ordInfOfPair
  have hB1 : ¬ ((-bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1) = 0 ∧
      (1 : k[X]) = 0) := fun h => one_ne_zero h.2
  rw [if_neg hB1, if_neg (one_ne_zero (α := k[X]))]
  rw [natDegree_one, hAdeg]
  rw [show (2 * ((3 : ℕ) : ℤ)) = 6 by norm_num,
    show (2 * ((0 : ℕ) : ℤ) + 5) = 5 by norm_num]
  rw [max_eq_left (by norm_num : (5 : ℤ) ≤ 6)]

/-- **Row identity, shared core for both `bMinus_mod_*` theorems.** Same
role and proof idiom as `TangentMumfordWitness.lean`'s `bPlus_row_eq`
(`Matrix.mulVec_cramer`-based): for any row `r`, `∑ⱼ M r j * bMinusCoeff j
= RHS r`. -/
private theorem bMinus_row_eq (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hdet : (cantorAddMatrix c0 c1 a0 a1).det ≠ 0) (r : Fin 4) :
    ∑ j : Fin 4, cantorAddMatrix c0 c1 a0 a1 r j *
      bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 j =
      cantorAddRHS vC0 vC1 vA0 vA1 r := by
  have hexpand : ∑ j : Fin 4, cantorAddMatrix c0 c1 a0 a1 r j *
      bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 j =
      (cantorAddMatrix c0 c1 a0 a1).det⁻¹ *
        (cantorAddMatrix c0 c1 a0 a1 r ⬝ᵥ
          (Matrix.cramer (cantorAddMatrix c0 c1 a0 a1)
            (cantorAddRHS vC0 vC1 vA0 vA1))) := by
    unfold bMinusCoeff dotProduct
    rw [Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [hexpand]
  have hmul := Matrix.mulVec_cramer (cantorAddMatrix c0 c1 a0 a1)
    (cantorAddRHS vC0 vC1 vA0 vA1)
  have hrow := congrFun hmul r
  simp only [Matrix.mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [hrow, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]

/-- **`bMinus`'s coefficients unfolded against a row, as a dot product.**
Direct analogue of `TangentMumfordWitness.lean`'s `bPlus_eval_eq_row`,
but for `bMinus` itself (not an evaluation) — since `bMinus`'s defining
conditions are congruences, this just re-exposes `bMinus`'s coefficient
tuple `(bMinusCoeff 0, ..., bMinusCoeff 3)` as `∑ⱼ (row r) j * coeff j`
for the two "identity-shaped" rows (rows whose entries are `0`/`1`
selectors) — used to read off `bMinusCoeff 0`/`bMinusCoeff 1` from rows
0-1 of `bMinus_row_eq` directly. -/
private theorem bMinus_coeff0_coeff1 (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hdet : (cantorAddMatrix c0 c1 a0 a1).det ≠ 0) :
    bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 0 -
        c0 * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2 +
        c0 * c1 * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3 = vC0 ∧
      bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 1 -
        c1 * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2 +
        (c1 ^ 2 - c0) * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3 = vC1 := by
  have hrow0 := bMinus_row_eq c0 c1 a0 a1 vC0 vC1 vA0 vA1 hdet 0
  have hrow1 := bMinus_row_eq c0 c1 a0 a1 vC0 vC1 vA0 vA1 hdet 1
  have hmat0 : cantorAddMatrix c0 c1 a0 a1 0 = ![(1 : k), 0, -c0, c0 * c1] := by
    unfold cantorAddMatrix; ext j; fin_cases j <;> rfl
  have hmat1 : cantorAddMatrix c0 c1 a0 a1 1 = ![(0 : k), 1, -c1, c1 ^ 2 - c0] := by
    unfold cantorAddMatrix; ext j; fin_cases j <;> rfl
  rw [hmat0] at hrow0
  rw [hmat1] at hrow1
  simp only [cantorAddRHS, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hrow0 hrow1
  constructor
  · linear_combination hrow0
  · linear_combination hrow1

/-- **Same as `bMinus_coeff0_coeff1`, for rows 2-3 (the `uA`/`-vA` pair).** -/
private theorem bMinus_coeff2_coeff3 (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hdet : (cantorAddMatrix c0 c1 a0 a1).det ≠ 0) :
    bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 0 -
        a0 * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2 +
        a0 * a1 * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3 = -vA0 ∧
      bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 1 -
        a1 * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2 +
        (a1 ^ 2 - a0) * bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3 = -vA1 := by
  have hrow2 := bMinus_row_eq c0 c1 a0 a1 vC0 vC1 vA0 vA1 hdet 2
  have hrow3 := bMinus_row_eq c0 c1 a0 a1 vC0 vC1 vA0 vA1 hdet 3
  have hmat2 : cantorAddMatrix c0 c1 a0 a1 2 = ![(1 : k), 0, -a0, a0 * a1] := by
    unfold cantorAddMatrix; ext j; fin_cases j <;> rfl
  have hmat3 : cantorAddMatrix c0 c1 a0 a1 3 = ![(0 : k), 1, -a1, a1 ^ 2 - a0] := by
    unfold cantorAddMatrix; ext j; fin_cases j <;> rfl
  rw [hmat2] at hrow2
  rw [hmat3] at hrow3
  simp only [cantorAddRHS, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at hrow2 hrow3
  constructor
  · linear_combination hrow2
  · linear_combination hrow3

/-- **`b_-` reduces to `vC` modulo `uC`.** Rows 0-1 of the linear system,
composed into the actual congruence statement (unlike `bPlus`, whose
four conditions are plain evaluations, `b_-`'s conditions are polynomial
congruences). Via `modByMonic_uCPoly_eq` (closed form of `q %ₘ uCPoly`
in terms of `q`'s coefficients) plus `bMinus_coeff0_coeff1` (those
coefficients satisfy exactly the equations making the closed form
collapse to `C vC1 * X + C vC0`). -/
theorem bMinus_mod_uC_eq_vC (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hdet : (cantorAddMatrix c0 c1 a0 a1).det ≠ 0) :
    (bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1) %ₘ (uCPoly c0 c1 : k[X]) =
      Polynomial.C vC1 * X + Polynomial.C vC0 := by
  unfold bMinus
  rw [modByMonic_uCPoly_eq]
  obtain ⟨h0, h1⟩ := bMinus_coeff0_coeff1 c0 c1 a0 a1 vC0 vC1 vA0 vA1 hdet
  have e0 : Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 0) -
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2) * Polynomial.C c0 +
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) * Polynomial.C c0 *
        Polynomial.C c1 = Polynomial.C vC0 := by
    have hc := congrArg Polynomial.C h0
    simp only [map_sub, map_add, map_mul] at hc
    linear_combination hc
  have e1 : Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 1) -
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2) * Polynomial.C c1 -
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) * Polynomial.C c0 +
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) * Polynomial.C c1 ^ 2 =
      Polynomial.C vC1 := by
    have hc := congrArg Polynomial.C h1
    simp only [map_sub, map_add, map_mul, map_pow] at hc
    linear_combination hc
  rw [e1, e0]


/-- **`b_-` reduces to `-vA` modulo `uA`.** Rows 2-3, mirror of
`bMinus_mod_uC_eq_vC`. -/
theorem bMinus_mod_uA_eq_neg_vA (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hdet : (cantorAddMatrix c0 c1 a0 a1).det ≠ 0) :
    (bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1) %ₘ (uAPoly a0 a1 : k[X]) =
      -(Polynomial.C vA1 * X + Polynomial.C vA0) := by
  unfold bMinus
  rw [modByMonic_uAPoly_eq]
  obtain ⟨h0, h1⟩ := bMinus_coeff2_coeff3 c0 c1 a0 a1 vC0 vC1 vA0 vA1 hdet
  have e0 : Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 0) -
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2) * Polynomial.C a0 +
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) * Polynomial.C a0 *
        Polynomial.C a1 = Polynomial.C (-vA0) := by
    have hc := congrArg Polynomial.C h0
    simp only [map_sub, map_add, map_mul] at hc
    linear_combination hc
  have e1 : Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 1) -
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 2) * Polynomial.C a1 -
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) * Polynomial.C a0 +
      Polynomial.C (bMinusCoeff c0 c1 a0 a1 vC0 vC1 vA0 vA1 3) * Polynomial.C a1 ^ 2 =
      Polynomial.C (-vA1) := by
    have hc := congrArg Polynomial.C h1
    simp only [map_sub, map_add, map_mul, map_pow] at hc
    linear_combination hc
  rw [e1, e0]
  simp only [map_neg]
  ring


end DecoupledSystem
end Genus2Lean
