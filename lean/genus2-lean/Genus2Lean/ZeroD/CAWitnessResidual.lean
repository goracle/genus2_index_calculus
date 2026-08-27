import Mathlib
import Genus2Lean.ZeroD.CAWitness
import Genus2Lean.ZeroD.PrincipalWitness
import Genus2Lean.LPairFinrankOneOrdAtFrac

/-!
# The residual-point `ordAt` fact for `CAWitness.lean`'s `f := y - bCA(x)`

`ROADMAP-principal-witness-assembly.md` step 1: `CAWitnessDivisor.lean`
handles `f`'s divisor at the four NAMED points (`Ra1, Ra2, ιP1, ιP2`).
This file handles the other side — `f`'s own zero at a root of the
residual factor `uCANew` (the quadratic that, per `CAWitness.lean`'s own
docstring, definitionally IS `T`). Direct analogue of
`PrincipalWitnessAssembly.lean`'s `ordAtFrac_eq_neg_one_of_uRS4General_root`,
but much simpler here: `Y = 1` throughout (a unit), so this is a bare
`ordAt`, not an `ordAtFrac` ratio — the residual root is a genuine
zero of `f` itself, not a pole-order computation on `f/U`.

**Goes through `OrdAtRootMultiplicityUnified.lean`'s approach, not
`hUfac`-style pre-factorization.** A first draft of this file assumed a
caller-supplied `hUfac : ∃ Fco, uCANew = linX P.X * Fco ∧ Fco.eval P.X ≠
0` — exactly the pre-split, `hRne`-shaped hypothesis
`OrdAtRootMultiplicityUnified.lean` exists to avoid (it silently assumes
`uCANew` has two DISTINCT roots, can't express `uCANew` being a perfect
square, and pushes the coprimality/factorization burden onto every call
site). Rejected on Claire's correction. **Fix**: `uCANew` is not a
product of named factors the way `npoly4Lcm4` is (so none of that file's
`rootMultiplicity_mul`-unpacking machinery is needed) — it is a single
atomic quadratic, so `ordAt_eq_rootMultiplicity_unramified`
(`LPairFinrankOneOrdAtFrac.lean`, lemma 6, unconditional: `ordAt Q c 0 =
c.rootMultiplicity α` for ANY `c ≠ 0`) applies to it DIRECTLY, with no
named-root hypothesis of any kind. This subsumes both the simple-root case
(`rootMultiplicity = 1`, what the assembly actually needs) and the
repeated-root case (`= 2`) as literal instances of the same unconditional
statement, exactly the way `ordAt_npoly4Lcm4_eq_rootMultiplicity` does for
`npoly4Lcm4`.

**Recipe.** Compose:
- `ordAt_eq_rootMultiplicity_unramified` applied to `A := denomPolyCA` at
  `P` (giving `ordAt P A 0 = A.rootMultiplicity P.X`, then `= 0` since
  `hAeval : A.eval P.X ≠ 0` forces `rootMultiplicity = 0`, no named-root
  detour), and to `U := uCANew` at `P` (giving `ordAt P U 0 =
  U.rootMultiplicity P.X` directly, left OPAQUE as a hypothesis
  `hUmult` — the caller supplies which multiplicity holds, `1` for the
  case the assembly needs, without this file forcing a pre-split).
- `ordAt_eq_ordAt_pairNorm_of_eval_eq_zero` (lemma 4/6): `ordAt P E Y =
  ordAt P (pairNorm H E Y) 0`, given `ḡ(P) ≠ 0`.
- `ordAt_add_of_pairNorm_eq_mul` (lemma 7): `ordAt P (A*U) 0 = ordAt P A
  0 + ordAt P U 0`, symmetric in `A`/`U`'s naming.

With `E := -bCA`, `Y := 1`: `pairNorm H E Y = A * (-U)` up to sign, so
`ordAt P E Y = 0 + ordAt P (-U) 0 = (-U).rootMultiplicity P.X`. Since
negation by a unit doesn't change rootMultiplicity, this equals `U`'s own
`rootMultiplicity P.X`, matching `hUmult` directly. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

variable {k : Type*} [Field k] [DecidableEq k]
variable {H : HyperellipticPolynomial k} [IsDedekindDomain (CoordinateRing H)]

/-- **`f`'s `ordAt` at a root of the residual factor `uCANew`, expressed
via `uCANew`'s own `rootMultiplicity` — no pre-split, no distinct-root
hypothesis.** `hUmult` is left as an explicit caller-supplied equation
(mirroring `rootMultiplicity_npoly4Lcm4_eq_add`'s own "leave it opaque"
convention) rather than fixed to `1`, so this single theorem covers both
the fully-split (`= 1`) and repeated-root (`= 2`) cases uniformly; the
assembly's own call site supplies `hUmult` with whichever value actually
holds for its data.

**Sign note.** `hPY : P.Y = bCA.eval P.X` pins `P` to the branch where `f
= y - bCA(x)` itself vanishes (not `ḡ`'s branch) — this is the hypothesis
that makes `hgbar_ne_eval` (`ḡ(P) ≠ 0`, needed below) provable from
`hchar`/`hPY_ne` alone, rather than an extra assumption. -/
theorem ordAt_eq_rootMultiplicity_of_uCANew_root
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k)
    (hdet : (caInterpMatrix Ra1X Ra2X P1X P2X).det ≠ 0)
    (h12 : Ra1X ≠ Ra2X) (h1P1 : Ra1X ≠ P1X) (h1P2 : Ra1X ≠ P2X)
    (h2P1 : Ra2X ≠ P1X) (h2P2 : Ra2X ≠ P2X) (hPP : P1X ≠ P2X)
    (hRa1_curve : Ra1Y ^ 2 = H.f.eval Ra1X) (hRa2_curve : Ra2Y ^ 2 = H.f.eval Ra2X)
    (hP1_curve : P1Y ^ 2 = H.f.eval P1X) (hP2_curve : P2Y ^ 2 = H.f.eval P2X)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥)
    (hU_ne0 : uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y ≠ 0)
    (hAeval : (denomPolyCA Ra1X Ra2X P1X P2X : k[X]).eval P.X ≠ 0)
    (hPY : P.Y = (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P.X)
    (hPY_ne : P.Y ≠ 0)
    (m : ℕ)
    (hUmult : Polynomial.rootMultiplicity P.X (uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) = m) :
    ordAt P (-bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y : k[X]) (1 : k[X]) = (m : ℤ) := by
  set E := -bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y with hE_def
  set U := uCANew H Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y with hU_def
  set A := denomPolyCA Ra1X Ra2X P1X P2X with hA_def
  -- `pairNorm H E 1 = A * (-U)`.
  have hAUraw : pairNorm H E (1 : k[X]) = A * (-U) := by
    unfold pairNorm
    have hfact := pairNormBCA_eq_denomPolyCA_mul_uCANew H Ra1X Ra2X P1X P2X
      Ra1Y Ra2Y P1Y P2Y hdet h12 h1P1 h1P2 h2P1 h2P2 hPP
      hRa1_curve hRa2_curve hP1_curve hP2_curve
    have hring : (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2 - (1 : k[X]) ^ 2 * H.f =
        -(H.f - (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y) ^ 2) := by ring
    rw [hE_def, neg_sq, hring, hfact]
    ring
  have hg_ne : toPair H E (1 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨_, hB⟩ => one_ne_zero hB
  have hA_ne0 : A ≠ 0 := by
    rw [hA_def]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (X_sub_C_ne_zero Ra1X) (X_sub_C_ne_zero Ra2X)) (X_sub_C_ne_zero P1X))
      (X_sub_C_ne_zero P2X)
  have hA_ne : toPair H A (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hA_ne0 hA0
  have hUneg_ne0 : (-U : k[X]) ≠ 0 := neg_ne_zero.mpr hU_ne0
  have hU_ne : toPair H (-U) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA0, _⟩ => hUneg_ne0 hA0
  -- `hgbar_ne_eval : E.eval P.X + (-1).eval P.X * P.Y ≠ 0`, i.e.
  -- `-bCA.eval P.X - P.Y ≠ 0`, i.e. `bCA.eval P.X ≠ -P.Y`. Given `hPY :
  -- P.Y = bCA.eval P.X`, this needs `bCA.eval P.X ≠ -bCA.eval P.X`, i.e.
  -- `2 * bCA.eval P.X ≠ 0`, i.e. (since `hchar`) `bCA.eval P.X ≠ 0`,
  -- i.e. (via `hPY`) `P.Y ≠ 0`, supplied directly as `hPY_ne`.
  have hgbar_ne_eval : E.eval P.X + (-(1 : k[X])).eval P.X * P.Y ≠ 0 := by
    rw [hE_def]
    simp only [eval_neg, eval_one]
    rw [hPY]
    intro hcontra
    have h2 : (2 : k) * (bCA Ra1X Ra2X P1X P2X Ra1Y Ra2Y P1Y P2Y).eval P.X = 0 := by
      linear_combination -hcontra
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hchar
    · apply hPY_ne
      rw [hPY, h]
  -- `ordAt P E 1 = ordAt P (pairNorm H E 1) 0` (lemma 4/6).
  have hN_eq_mult : ordAt P E (1 : k[X]) = ordAt P (pairNorm H E (1 : k[X])) (0 : k[X]) :=
    ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E (1 : k[X]) hg_ne hgbar_ne_eval
  -- `ordAt P A 0 = 0` — `P` not a root of `denomPolyCA`, via
  -- `rootMultiplicity` directly (no named-root detour): `A.eval P.X ≠ 0`
  -- means `P.X` isn't a root at all, so `rootMultiplicity = 0`.
  have hA_ord : ordAt P A (0 : k[X]) = 0 := by
    have hAmult : Polynomial.rootMultiplicity P.X A = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by
        rw [Polynomial.IsRoot]; exact hAeval)
    have := ordAt_eq_rootMultiplicity_unramified (H := H) hchar A hA_ne0 P.X P h_bot rfl hPY_ne
    rw [this, hAmult]
    norm_num
  -- `ordAt P (-U) 0 = U.rootMultiplicity P.X = m` — `rootMultiplicity`
  -- directly, no `hUfac` pre-factorization, unit-scaling-invariant.
  have hU_ord : ordAt P (-U) (0 : k[X]) = (m : ℤ) := by
    have hUneg_eq : (-U : k[X]) = Polynomial.C (-1 : k) * U := by
      rw [map_neg, map_one, neg_mul, one_mul]
    have hCU_ne : (Polynomial.C (-1 : k) * U : k[X]) ≠ 0 := hUneg_eq ▸ hUneg_ne0
    have hUneg_mult : Polynomial.rootMultiplicity P.X (-U : k[X]) = Polynomial.rootMultiplicity P.X U := by
      rw [hUneg_eq, Polynomial.rootMultiplicity_mul hCU_ne, Polynomial.rootMultiplicity_C]
      norm_num
    have := ordAt_eq_rootMultiplicity_unramified (H := H) hchar (-U) hUneg_ne0 P.X P h_bot rfl hPY_ne
    rw [this, hUneg_mult, hUmult]
  -- Assemble: `ordAt P E 1 = ordAt P (A*(-U)) 0 = ordAt P A 0 + ordAt P (-U) 0 = 0 + m`.
  rw [hN_eq_mult, hAUraw,
    ordAt_add_of_pairNorm_eq_mul P h_bot (A * (-U)) A (-U) rfl hA_ne hU_ne, hA_ord, hU_ord]
  norm_num

end DecoupledSystem
end Genus2Lean
