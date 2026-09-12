import Mathlib
import Genus2Lean.ZeroD.DataDerivationTotalDegree

/-!
# `algebraMap (F p) (K2 p ...) x`'s LITERAL `towerToRdec` bound

New this pass. `ROADMAP-crossnondegenerate-degree-bound.md`'s final section
("Route (a)") scopes the remaining work to close `CrossNondegenerateDegreeBound.
lean`'s `hA`/`hB` hypotheses as: re-derive `curBeforeMonic.coeff i`'s `K0`-level
sub-pieces (`t1`/`t2`/`gu0`/`gu1`) in literal `towerToRdec`-computed form (not
`IsRdecWitness`, which bounds an arbitrary witness, not necessarily the literal
computed pair `crossResultant_totalDegree_le` needs). `t1`/`t2`'s literal bound
is ALREADY done (`t0_promoted_totalDegree_le`, `DataDerivationTotalDegree.lean`,
REPL-confirmed green) -- `(anchor1 p ...).1`/`(anchor2 p ...).1` are literally
`t0 p 0`/`t0 p 1` promoted through the same two-step `algebraMap` chain that
theorem already bounds. This file closes the other half: `gu0 := algebraMap
(F p) (K2 p ...) u0`, `gu1 := algebraMap (F p) (K2 p ...) u1` (`CurBeforeMonicCoeff
TotalDegree.lean`'s own names for `curBeforeMonic`'s `Q := (X-t1)(X-t2)*U`
factor's two constant coefficients).

**The route**: `algebraMap (F p) (K2 p ...) x` factors through `K0 p` via
`IsScalarTower.algebraMap_apply (F p) (K0 p) (K2 p ...)` -- this exact lemma
is already used for exactly this purpose elsewhere in this project
(`anchor1_not_isRoot_U`, `DataDerivationSolve.lean`), so the factorization
itself is not new. `algebraMap (F p) (K0 p) x` is in turn `IsLocalization.mk'
(K0 p) (MvPolynomial.C x) 1` (`IsLocalization.mk'_spec'` at denominator `1`,
same pattern `fAtT_eq_mk'_one`/`t0_totalDegree_le` already use), so
`baseFracToRing_totalDegree_le` gives `totalDegree ≤ 0` on both sides at the
`K0` base case (`MvPolynomial.C x` and `1` both have `totalDegree 0`). From
there, `towerToRdecK1_algebraMap_totalDegree_le`/`towerToRdec_algebraMap_
totalDegree_le` (already proved, REPL-confirmed) propagate this up through
the SAME two tower steps `t0_promoted_totalDegree_le` uses, at `D := 1`
(dominating the `≤0` base bound and the `1 ≤ D` floor those two theorems
need) then `D := 3` -- IDENTICAL numerals to `t0_promoted_totalDegree_le`'s
own composition, since the base bound here (`≤0`) is even better than `t0`'s
own (`≤1`), but folded into the same `D := 1`/`D := 3` steps for uniformity
rather than re-optimized.

**Not yet REPL-confirmed** -- drafted this pass, per project convention
Claude drafts and Claire tests. Directionally this closes exactly the
`gu0`/`gu1` gap Route (a) names; whether it composes with `t1`/`t2`'s bound
into a literal `curBeforeMonic.coeff {0,1,2}` bound is a SEPARATE question
(see this file's closing note) -- `towerToRdec` is not a ring homomorphism
(`towerToRdec_spec`'s own docstring, `DataDerivationMumford.lean`, is explicit
about this), so a literal bound on `towerToRdec` applied to `t1`, `t2`, `gu0`,
`gu1` individually does NOT compose through `+`/`-`/`*` into a literal bound
on `towerToRdec` applied to `curBeforeMonic.coeff i` itself (an arithmetic
combination of those pieces) -- only `IsRdecWitness`'s witness-pair
combinators (`.add`/`.mul`/`.neg`) compose that way, and those bound a
possibly-different witness, not the literal computed pair. This file closes
the `gu0`/`gu1` sub-piece Route (a) asks for; it does NOT by itself close
`crossResultant_totalDegree_le`'s `hA`/`hB` -- see this file's closing note
for the precise remaining gap, sharpening (not superseding)
`ROADMAP-crossnondegenerate-degree-bound.md`'s own "Route (a) vs (b)" framing.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **Base case**: `algebraMap (F p) (K0 p) x`'s `baseFracToRing` bound is
`≤ 0` on both sides -- it is literally `mk' (K0 p) (C x) 1`, and both `C x`
(`MvPolynomial.totalDegree_C`) and `1` (`MvPolynomial.totalDegree_one`) have
`totalDegree 0`. Same `mk'_spec'`-at-denominator-`1` idiom as `t0_totalDegree_
le`/`fAtT_eq_mk'_one`. -/
theorem algebraMap_Fp_K0_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (x : F p) :
    (baseFracToRing p sg (algebraMap (F p) (K0 p) x)).1.totalDegree ≤ 0 ∧
    (baseFracToRing p sg (algebraMap (F p) (K0 p) x)).2.totalDegree ≤ 0 := by
  have htower : algebraMap (F p) (K0 p) x
      = algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.C x) := by
    rw [IsScalarTower.algebraMap_eq (F p) (MvPolynomial (Fin 2) (F p)) (K0 p),
      RingHom.comp_apply]
    -- Goal now: `algebraMap (K0 p)` applied to `algebraMap (F p) (MvPolynomial ...) x`
    -- vs. applied to `MvPolynomial.C x` — reduces to the two inner values being
    -- equal, `algebraMap (F p) (MvPolynomial (Fin 2) (F p)) x = C x`, which holds
    -- by `MvPolynomial`'s own `Algebra (F p) _` instance definition (`rfl`-level),
    -- via `congrArg` so only that inner equality needs to typecheck.
    exact congrArg (algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p)) rfl
  have hv : algebraMap (F p) (K0 p) x
      = IsLocalization.mk' (K0 p) (MvPolynomial.C x : MvPolynomial (Fin 2) (F p))
        (1 : ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p)))) := by
    have hspec := IsLocalization.mk'_spec' (K0 p) (MvPolynomial.C x : MvPolynomial (Fin 2) (F p))
      (1 : ↥(nonZeroDivisors (MvPolynomial (Fin 2) (F p))))
    simp only [OneMemClass.coe_one, map_one, one_mul] at hspec
    rw [htower, ← hspec]
  rcases eq_or_ne (MvPolynomial.C x : MvPolynomial (Fin 2) (F p)) 0 with hzero | hne
  · -- `x = 0`: reuse the already-proved zero case directly rather than
    -- re-deriving `IsFractionRing.num`/`.den` of `0` by hand.
    have hx0 : x = 0 := (MvPolynomial.C_eq_zero (R := F p) (a := x)).mp hzero
    subst hx0
    rw [map_zero]
    exact ⟨(baseFracToRing_zero_one_totalDegree_eq_zero p sg).1.le,
      (baseFracToRing_zero_one_totalDegree_eq_zero p sg).2.1.le⟩
  · have hbound := baseFracToRing_totalDegree_le p sg
      (a := MvPolynomial.C x) (b := (1 : MvPolynomial (Fin 2) (F p))) one_ne_zero hne hv
    rwa [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_one] at hbound

/-- **`gu0`/`gu1`'s literal `towerToRdec` bound.** `algebraMap (F p) (K2 p ...)
x` factors as `algebraMap (K1 ...) (K2 ...) (algebraMap (K0 p) (K1 ...)
(algebraMap (F p) (K0 p) x))` -- the SAME two-step tower composite
`t0_promoted_totalDegree_le` bounds for `t0 p i`, here with `algebraMap (F p)
(K0 p) x` (base bound `≤0`, `algebraMap_Fp_K0_totalDegree_le`) in place of
`t0 p i` (base bound `≤1`). Propagated up through `towerToRdecK1_algebraMap_
totalDegree_le`/`towerToRdec_algebraMap_totalDegree_le` at the SAME `D := 1`/
`D := 3` steps `t0_promoted_totalDegree_le` uses (safe: `0 ≤ 1`), giving the
SAME `≤7`/`≤6` final bound. -/
theorem algebraMap_Fp_promoted_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 x : F p) :
    (towerToRdec p sg
        (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
          (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
            (algebraMap (F p) (K0 p) x)))).1.totalDegree ≤ 7 ∧
    (towerToRdec p sg
        (algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
          (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
            (algebraMap (F p) (K0 p) x)))).2.totalDegree ≤ 6 := by
  have h0 := algebraMap_Fp_K0_totalDegree_le p sg x
  have h1 := towerToRdecK1_algebraMap_totalDegree_le p sg c0 c1 c2 c3 c4
    (algebraMap (F p) (K0 p) x) ⟨h0.1.trans (Nat.zero_le 1), h0.2.trans (Nat.zero_le 1)⟩
  have h2 := towerToRdec_algebraMap_totalDegree_le p sg c0 c1 c2 c3 c4
    (D := 3) (by norm_num) (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
      (algebraMap (F p) (K0 p) x))
    ⟨h1.1.trans (by norm_num), h1.2.trans (by norm_num)⟩
  exact h2

/-- **`gu0`/`gu1` themselves, in the exact shape `curBeforeMonic`'s `Q`
factor uses.** `algebraMap (F p) (K2 p ...) x` (the literal term appearing
in `Qpoly_coeff_three_and_two_eq`'s formulas for `gu0`/`gu1`) equals the
tower composite `algebraMap_Fp_promoted_totalDegree_le` bounds, via
`IsScalarTower.algebraMap_apply` twice (`F p → K0 p → K2 p ...` and
`K0 p → K1 p ... → K2 p ...`), matching this project's own established
`IsScalarTower.algebraMap_apply` idiom (`anchor1_not_isRoot_U` et al.,
`DataDerivationSolve.lean`). -/
theorem algebraMap_Fp_K2_totalDegree_le {Vars : Type*} (sg : SideGens Vars)
    (c0 c1 c2 c3 c4 x : F p) :
    (towerToRdec p sg (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) x)).1.totalDegree ≤ 7 ∧
    (towerToRdec p sg (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) x)).2.totalDegree ≤ 6 := by
  have heq : algebraMap (F p) (K2 p c0 c1 c2 c3 c4) x
      = algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)
        (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (algebraMap (F p) (K0 p) x)) := by
    rw [IsScalarTower.algebraMap_apply (F p) (K0 p) (K2 p c0 c1 c2 c3 c4),
      IsScalarTower.algebraMap_apply (K0 p) (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4)]
  rw [heq]
  exact algebraMap_Fp_promoted_totalDegree_le p sg c0 c1 c2 c3 c4 x

/-! ## Status, this pass

**Drafted, NOT yet REPL-confirmed.** `algebraMap_Fp_K2_totalDegree_le` closes
the `gu0`/`gu1` half of `ROADMAP-crossnondegenerate-degree-bound.md`'s "Route
(a)" list (`t1`/`t2`/`gu0`/`gu1`) in the SAME literal-`towerToRdec` sense
`t0_promoted_totalDegree_le` already closed `t1`/`t2` -- both base generators
appearing in `curBeforeMonic`'s `Q := (X-t1)(X-t2)*(X²+C gu1 X+C gu0)` factor
now have an unconditional, literal `towerToRdec`-computed bound, no
`IsRdecWitness` needed.

**Deliberately flagged, not glossed over**: this does NOT close
`crossResultant_totalDegree_le`'s `hA`/`hB` on its own, and CANNOT be
composed with `t0_promoted_totalDegree_le` to reach a literal bound on
`curBeforeMonic.coeff {0,1,2}` (the actual quantity `hA`/`hB` need, one more
step up) by the arithmetic `curBeforeMonic_coeff_{two,one,zero}_eq` describe
(`g.coeff k` is a `+`/`-`/`*` combination of `Npoly.coeff j` and `t1,t2,gu0,
gu1`) -- `towerToRdec` is a normal-form EXTRACTION, not a ring homomorphism
(`towerToRdec_spec`'s own docstring in `DataDerivationMumford.lean` is
explicit: `towerToRdec (a*b)` is generally NOT `((towerToRdec a).1 *
(towerToRdec b).1, ...)`, since both `IsFractionRing.num/.den`'s reduced-
fraction choice and `modByMonicHom`'s remainder-normalization can produce a
different, more-reduced representative for a combined value than the raw
combination of the pieces' own witnesses). This is exactly why `IsRdecWitness`
was introduced as a SEPARATE predicate with its own `.add`/`.mul`/`.neg`
combinators (`TowerToRdecMul.lean`) -- those compose correctly through
arithmetic, but only bound *some* valid witness for the combined value, not
necessarily the literal `towerToRdec`-computed pair `theData`'s `u1_num`/
`u1_den` (and hence `crossResultant_totalDegree_le`'s `hA`/`hB`) are stated
against.

**The actual state of Route (a), corrected here**: `ROADMAP-crossnondegenerate-
degree-bound.md`'s closing paragraph frames "Route (a)" as reusing `t0_
promoted_totalDegree_le`/`Npoly_coeff_isRdecWitness_uniform`'s already-proved
infrastructure "top to bottom" to reach a literal bound with "nothing needing
to be re-proved, only reshaped" via `mk'_eq_iff_eq_mul`. That bridge lemma
(`IsLocalization.mk'_eq_iff_eq_mul`) genuinely converts a `K0`-level
`IsRdecWitness` hypothesis into an `IsLocalization.mk'`-witness fact (see that
roadmap section's own correct derivation) -- but `curBeforeMonic.coeff i`
itself is NOT a `K0`-level value reachable this way; it is built by `+`/`-`/
`*` from `Npoly.coeff j` (`K2`-level) and `t1,t2,gu0,gu1` (also `K2`-level,
now bounded literally by this file/`t0_promoted_totalDegree_le`), and no
amount of reshaping individual pieces' witnesses turns a `K2`-level
ARITHMETIC COMBINATION's literal `towerToRdec` output into something
recoverable from the pieces' own literal outputs, for the structural reason
above (`towerToRdec` is not a ring hom). So Route (a), as stated, does not
actually reach `crossResultant_totalDegree_le`'s `hA`/`hB` even once `t1`/
`t2`/`gu0`/`gu1` are ALL in literal form (this file finishes that part) --
the gap is one level up from where the roadmap's closing paragraph placed it.

**What DOES remain open, correctly located**: `URSCoeffIsRdecWitness.lean`'s
own closing note already flags the honest alternative -- rewrite
`crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le` themselves to
bound *a* witness for the resultant (`IsRdecWitness`-shaped conclusion, not a
literal-pair hypothesis), which `uRS_coeff_isRdecWitness`/`IsRdecWitness.mul`/
`.add`/`.neg` (already proved, `≤630896`-level) CAN supply directly, no new
gap. This is not yet done (a new theorem, not this file's job to add given
this file's own scope).

**Correction, later pass**: the paragraph originally here warned that such a
restated theorem would need an `IsSMulRegular`-transfers-between-witnesses
lemma before it could be used against `CrossNondegenerate`'s `hu0`/etc. That
concern was overstated. `CrossResultantIsRdecWitness.lean` (new file, later
pass) checked `hu0`/etc.'s actual statement directly: they quantify
`IsSMulRegular` over the LITERAL `Rdec p`-element `theData` computes (`Rdec p`
is concretely `MvPolynomial Idx (F p)`, no `K2`-level abstraction in sight at
that point), not over an abstract `K2`-value reachable through multiple
witnesses -- so there is no "different witness" for `hu0` to be confused
with, and no transfer lemma is needed to state or use a fact about that
specific element. The transfer question only arises for a hypothetical
theorem that tries to conclude `IsSMulRegular`-ness FROM a bound on an
arbitrarily-chosen `IsRdecWitness` witness of an abstract `K2`-value (which
is what an `IsRdecWitness`-shaped restatement of `crossResultant_totalDegree_
le` would produce, per the paragraph above) -- see `CrossResultantIsRdecWitness.
lean`'s own closing note for the full corrected account. `hu0`/etc. remain
fully open regardless (an `IsRdecWitness` fact about an element carries no
`IsSMulRegular` information about it either way), but not for the reason
this note originally gave. -/

end TheDataDerivation
end Genus2Lean
