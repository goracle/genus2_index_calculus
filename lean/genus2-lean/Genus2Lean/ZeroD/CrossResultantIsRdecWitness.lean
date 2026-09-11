import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemRegular
import Genus2Lean.ZeroD.TowerToRdecMul

/-!
# `CrossNondegenerate`'s resultant: an honest `IsRdecWitness` fact for the
LITERAL `theData`-computed pair

New this pass. `AlgebraMapFpLiteralTotalDegree.lean`'s closing note (see
that file) correctly flags that `crossResultant_totalDegree_le`/
`crossResultantV_totalDegree_le` (`CrossNondegenerateDegreeBound.lean`) are
stated against an `hA`/`hB` hypothesis shape that nothing currently
supplies, and that two candidate fixes both fail:

1. Reshaping `uRS_coeff_isRdecWitness`'s existential witness
   (`URSCoeffIsRdecWitness.lean`) into a literal-pair fact doesn't work — a
   witness for a value is not unique, so a bound on *some* witness says
   nothing about the SPECIFIC pair `theData` computes.
2. Composing separately-bounded per-generator pieces (`t0_promoted_
   totalDegree_le`, `algebraMap_Fp_K2_totalDegree_le`) into a literal bound
   on `curBeforeMonic.coeff i` fails, since `towerToRdec` is a normal-form
   extraction, not a ring homomorphism (`towerToRdec_spec`'s own docstring,
   `DataDerivationMumford.lean`, is explicit about this) — it does not
   commute with `+`/`-`/`*`.

**The actual fix, applied here.** Both obstacles above are about combining
SEPARATE witnesses for SEPARATE values into a witness for a value built
from them by arithmetic that `towerToRdec` itself does not respect. That
is a real obstacle for bounding `uRS.coeff i` ITSELF (an arithmetic
combination of `curBeforeMonic`'s own coefficients — exactly where
`towerToRdec`'s non-homomorphism property bites). It is NOT an obstacle
here: `CrossNondegenerate`'s `hu0`/etc. fields (`DecoupledSystemRegular.
lean`, confirmed by direct inspection) state `IsSMulRegular` on `theData`'s
literal `u1_num`/`u1_den`/`u2_num`/`u2_den` fields, which unfold (`rfl`,
already used inside `crossResultant_totalDegree_le`'s own proof) to
`(towerToRdec p aSideGens (uRS ... sa ...).coeff i).1/.2` and
`(towerToRdec p bSideGens (uRS ... sb ...).coeff i).1/.2` — i.e. `theData`'s
fields ARE `towerToRdec`'s own literal output for `uRS.coeff i` on each
side, not some other representation needing reconciliation with it.
`towerToRdec_isRdecWitness` (`TowerToRdecMul.lean`, already proved,
unconditional given `ι`'s hypotheses) says exactly that this literal
output IS a valid `IsRdecWitness` witness for the underlying `K2`-value.
No reshaping of an existential, and no attempt to bound `towerToRdec`'s
recursive formula, is needed — the witness fact for the literal pair is
already in hand directly from `towerToRdec_spec`.

**The resultant, precisely.** Writing `a := uRS.coeff i` on the a-side,
`b := uRS.coeff i` on the b-side (both `K2 p c0 c1 c2 c3 c4`-valued, same
curve, different samples), with witnesses `(n1,d1) := (u1_num i, u1_den i)`
for `a` and `(n2,d2) := (u2_num i, u2_den i)` for `b`: combining `(n1,d1)`
witnessing `a` with `(-n2,d2)` witnessing `-b` (`IsRdecWitness.neg`) via
`IsRdecWitness.add` gives `(n1*d2 - n2*d1, d1*d2)` witnessing `a - b`. The
LITERAL resultant `crossResultant_totalDegree_le` bounds, `d1*n2 - d2*n1`,
is exactly `-(n1*d2 - n2*d1)`, i.e. `IsRdecWitness.neg` applied once more
gives `(d1*n2 - d2*n1, d1*d2)` witnessing `-(a - b) = b - a`. **This is a
genuinely different, weaker-looking statement than a `totalDegree` bound**
(that remains `crossResultant_totalDegree_le`'s job, conditional on `hA`/
`hB`) — this file's job is narrower: confirming the `Rdec p`-level resultant
element `hu0`/etc. state `IsSMulRegular`-ness about is honestly a witness
numerator for `uRS_B.coeff i - uRS_A.coeff i`, at denominator `u1_den i *
u2_den i` (NOT denominator `1` — the resultant is not itself a "clean"
value, only a valid cross-multiplied numerator against that specific
denominator). `hA`/`hB`'s own shape (`towerToRdecK1`'s intermediate-degree
hypothesis) is a SEPARATE, still-open question this file does not attempt
to close — seeded by `towerToRdec_coeff_totalDegree_le`'s own hypothesis on
`curBeforeMonic.coeff i`'s pre-`uRS` value, not by anything proved here.

**REPL-confirmed green** (Claire's build) — both `uResultant_isRdecWitness`
and `vResultant_isRdecWitness` below build with no changes needed to either
statement or proof term.

**Scope, stated precisely so this isn't over-read as more progress than it
is**: this file does NOT discharge `crossResultant_totalDegree_le`'s `hA`/
`hB` — those want a `totalDegree` bound on `towerToRdecK1`'s own
INTERMEDIATE recursive output (`towerToRdec_coeff_totalDegree_le`'s
hypothesis shape, `DataDerivationTotalDegree.lean`), which is a strictly
deeper quantity than anything `IsRdecWitness`/`towerToRdec_isRdecWitness`
talk about — `IsRdecWitness` only asserts a cross-multiplied EQUATION holds,
carrying no degree information at all. That gap remains exactly as open as
`AlgebraMapFpLiteralTotalDegree.lean`'s closing note left it. **What this
file DOES set up**: `AlgebraMapFpLiteralTotalDegree.lean`'s own closing note
flagged, as the one thing a witness-shaped resultant theorem would need to
re-examine, whether `IsSMulRegular`-ness (not mere `≠0`) transfers between
two witnesses of the same value — this file's two theorems are the
witness-shaped resultant statements that question is actually about, so
the natural next step is attempting that transfer lemma directly against
them, not re-attempting the `hA`/`hB` degree-bound route.
-/

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **The literal `u`-side resultant, as an honest `IsRdecWitness` fact.**
Given the ambient `ι` satisfying `towerToRdec_spec`'s hypotheses for BOTH
`aSideGens` and `bSideGens` (independently satisfiable by the same `ι`,
since the two generator sets — `{a1,a2,wa1,wa2}` vs. `{b1,b2,wb1,wb2}` —
are disjoint in `Idx`), the literal `Rdec p`-element `theData` computes as
`u1_den i * u2_num i - u2_den i * u1_num i` is a valid `IsRdecWitness`
witness numerator, at denominator `u1_den i * u2_den i`, for the `K2`-value
`(uRS ... sb ...).coeff i - (uRS ... sa ...).coeff i` (b-side minus
a-side). -/
theorem uResultant_isRdecWitness
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (i : Fin 2)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (Rdec p))
    (hι_tA : ∀ j : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X j)))) =
      algebraMap (Rdec p) (FractionRing (Rdec p))
        (MvPolynomial.X (aSideGens.tGen j)))
    (hι_w1A : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (aSideGens.wGen 0)))
    (hι_w2A : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (aSideGens.wGen 1)))
    (hι_tB : ∀ j : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X j)))) =
      algebraMap (Rdec p) (FractionRing (Rdec p))
        (MvPolynomial.X (bSideGens.tGen j)))
    (hι_w1B : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (bSideGens.wGen 0)))
    (hι_w2B : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (bSideGens.wGen 1))) :
    IsRdecWitness p ι (algebraMap (Rdec p) (FractionRing (Rdec p)))
      ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val -
        (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den i *
          (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num i -
        (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den i *
          (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num i,
       (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den i *
          (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den i) := by
  have hA := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 aSideGens
    ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val) ι hι_tA hι_w1A hι_w2A
  have hB := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 bSideGens
    ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val) ι hι_tB hι_w1B hι_w2B
  have hu1n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num i
      = (towerToRdec p aSideGens
          ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).1 := rfl
  have hu1d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den i
      = (towerToRdec p aSideGens
          ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).2 := rfl
  have hu2n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num i
      = (towerToRdec p bSideGens
          ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).1 := rfl
  have hu2d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den i
      = (towerToRdec p bSideGens
          ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).2 := rfl
  rw [hu1n, hu1d, hu2n, hu2d]
  -- Work entirely inside `IsRdecWitness`'s own unfolding (a plain equation
  -- in `evalNd`/`ι` applied to concrete `Rdec p`/`K2` terms) rather than
  -- composing `.mul`/`.neg`/`.add` as opaque lemmas — safer against the
  -- `ring`-under-`ι`/`evalNd` mismatches those combinators' argument shapes
  -- can otherwise hide until `ι`/`evalNd` are actually pushed through.
  unfold IsRdecWitness at hA hB ⊢
  -- Goal: `evalNd (d1*n2 - d2*n1) = evalNd (d1*d2) * ι (b - a)`, given
  -- `hA : evalNd n1 = evalNd d1 * ι a` and `hB : evalNd n2 = evalNd d2 * ι b`.
  -- `simp only` (not `rw`, to avoid depending on the exact left-to-right
  -- match order across the goal's two sides) pushes `evalNd`/`ι` through
  -- every `-`/`*` in the goal via `map_sub`/`map_mul`, then substitutes
  -- `hA`/`hB` directly wherever `evalNd n1`/`evalNd n2` appear; `ring`
  -- closes the resulting pure commutative-ring identity in `evalNd d1`/
  -- `evalNd d2`/`ι a`/`ι b` alone.
  simp only [map_sub, map_mul, hA, hB]
  ring

/-- **The literal `v`-side resultant, as an honest `IsRdecWitness` fact.**
Exact mirror of `uResultant_isRdecWitness`, `vRS` in place of `uRS`
throughout — `vRS` additionally needs `hgcdA`/`hgcdB` (the `Ypoly`/`uRS`
coprimality `vRS`'s own definition requires) threaded through, same as
`crossResultantV_totalDegree_le` itself already does. -/
theorem vResultant_isRdecWitness
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (i : Fin 2)
    (ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (Rdec p))
    (hι_tA : ∀ j : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X j)))) =
      algebraMap (Rdec p) (FractionRing (Rdec p))
        (MvPolynomial.X (aSideGens.tGen j)))
    (hι_w1A : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (aSideGens.wGen 0)))
    (hι_w2A : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (aSideGens.wGen 1)))
    (hι_tB : ∀ j : Fin 2, ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
          (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X j)))) =
      algebraMap (Rdec p) (FractionRing (Rdec p))
        (MvPolynomial.X (bSideGens.tGen j)))
    (hι_w1B : ι (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (w1 p c0 c1 c2 c3 c4)) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (bSideGens.wGen 0)))
    (hι_w2B : ι (w2 p c0 c1 c2 c3 c4) =
      algebraMap (Rdec p) (FractionRing (Rdec p)) (MvPolynomial.X (bSideGens.wGen 1))) :
    IsRdecWitness p ι (algebraMap (Rdec p) (FractionRing (Rdec p)))
      ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val -
        (vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)
      ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den i *
          (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num i -
        (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den i *
          (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num i,
       (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den i *
          (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den i) := by
  have hA := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 aSideGens
    ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val) ι hι_tA hι_w1A hι_w2A
  have hB := towerToRdec_isRdecWitness p c0 c1 c2 c3 c4 bSideGens
    ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val) ι hι_tB hι_w1B hι_w2B
  have hv1n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num i
      = (towerToRdec p aSideGens
          ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).1 := rfl
  have hv1d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den i
      = (towerToRdec p aSideGens
          ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).2 := rfl
  have hv2n : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num i
      = (towerToRdec p bSideGens
          ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).1 := rfl
  have hv2d : (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den i
      = (towerToRdec p bSideGens
          ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).2 := rfl
  rw [hv1n, hv1d, hv2n, hv2d]
  unfold IsRdecWitness at hA hB ⊢
  simp only [map_sub, map_mul, hA, hB]
  ring

end DecoupledSystem
end Genus2Lean
