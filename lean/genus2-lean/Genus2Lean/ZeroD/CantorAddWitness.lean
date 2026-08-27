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

**Status: scaffolding only, this pass.** The matrix/coefficient/`bMinus`
definitions and the degree bound are written and intended to typecheck;
the determinant-nonvanishing proof (`cantorAddMatrix_det_ne_zero`, the
`= Res(uC,uA)` identity plus its relation to `uC,uA` coprimality) and the
four row/congruence identities (`bMinus_mod_uC_eq_vC`-style) are left as
explicit `sorry`s for a follow-up pass — this file's job this pass is to
get the SHAPE right (matching `bPlus`'s architecture exactly) and get it
in front of Claire's REPL, not to close every proof obligation in one
sitting. Not yet build-tested (no live Lean toolchain in this
environment) — Claire's REPL to confirm, per this project's own
workflow convention. `ordInfOfPair(-bMinus,1) = -6` (matching `f+`,
needed for the roadmap's matched-pole-order pairing) is NOT yet stated
here — it needs `bMinus`'s degree to be exactly 3 (a `hlead`-style
hypothesis on the degree-3 coefficient, mirroring `bPlus_ordInfOfPair`'s
own `hlead` weakening), deferred to the next pass once the row
identities above are in hand to compute that coefficient explicitly. -/

noncomputable section

open Polynomial

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

/-- **Nondegeneracy of the 4×4 Cantor-addition system.** `cantorAddMatrix`'s
determinant equals `Res(uC, uA)` (the resultant of the two quadratics
`uC := X²+C c1*X+C c0`, `uA := X²+C a1*X+C a0`) — confirmed via sympy,
not yet re-derived in-proof here (`sorry`, this pass). Nonzero exactly
when `uC, uA` share no common root, i.e. `C` and `A`'s point-pairs are
disjoint (the natural nondegeneracy hypothesis for this whole
construction, mirroring `hR1P1`/`hR1P2`-style disjointness hypotheses
elsewhere in this project). Left as a hypothesis (`hcoprime`-shaped) at
call sites rather than derived from a lower-level disjointness fact here
— matching `tangentInterpMatrix_det_ne_zero`'s own role, one layer
removed (that theorem proves nonvanishing FROM pairwise-distinct roots;
this one is stated but not yet proved, since the natural hypothesis here
is coprimality of the two QUADRATICS directly, not four named roots). -/
theorem cantorAddMatrix_det_ne_zero (c0 c1 a0 a1 : k)
    (hcoprime :
      IsCoprime ((X : k[X]) ^ 2 + Polynomial.C c1 * X + Polynomial.C c0)
        ((X : k[X]) ^ 2 + Polynomial.C a1 * X + Polynomial.C a0)) :
    (cantorAddMatrix c0 c1 a0 a1).det ≠ 0 := by
  sorry

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

/-- **`b_-` reduces to `vC` modulo `uC`.** Rows 0-1 of the linear system,
composed into the actual congruence statement (unlike `bPlus`, whose
four conditions are plain evaluations, `b_-`'s conditions are polynomial
congruences — so the row lemmas here are stated as `%ₘ` facts, not
`.eval` facts). `sorry`, this pass — deferred alongside
`cantorAddMatrix_det_ne_zero` above. -/
theorem bMinus_mod_uC_eq_vC (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hdet : (cantorAddMatrix c0 c1 a0 a1).det ≠ 0) :
    (bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1) %ₘ
        ((X : k[X]) ^ 2 + Polynomial.C c1 * X + Polynomial.C c0) =
      Polynomial.C vC1 * X + Polynomial.C vC0 := by
  sorry

/-- **`b_-` reduces to `-vA` modulo `uA`.** Rows 2-3. `sorry`, this pass. -/
theorem bMinus_mod_uA_eq_neg_vA (c0 c1 a0 a1 vC0 vC1 vA0 vA1 : k)
    (hdet : (cantorAddMatrix c0 c1 a0 a1).det ≠ 0) :
    (bMinus c0 c1 a0 a1 vC0 vC1 vA0 vA1) %ₘ
        ((X : k[X]) ^ 2 + Polynomial.C a1 * X + Polynomial.C a0) =
      -(Polynomial.C vA1 * X + Polynomial.C vA0) := by
  sorry

end DecoupledSystem
end Genus2Lean
