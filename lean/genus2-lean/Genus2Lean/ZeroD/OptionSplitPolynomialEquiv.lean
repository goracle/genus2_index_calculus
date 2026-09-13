import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# The single-stage tower bridge: `Option`-split quotient ≃ₐ polynomial quotient

**Why this file exists.** `ROADMAP-monic-annihilator-degree-uniform.md`'s
Assembly plan hit a real gap (flagged and confirmed via ChatGPT
consultation, logged in that roadmap): the per-stage `finrank`/`Module.Finite`
wiring in `PeelChainStageFinite.lean`/`CurveRelationStageWiring.lean`/
`LinearElimStageWiring.lean` is built entirely on quotients of the AMBIENT
ring `Rdec p ⧸ Ideal.ofList gens`, and no prefix `gens` (including `gens =
[]`) ever makes that ring finite-dimensional over `F p` — `Rdec p` itself
is a 12-variable free polynomial ring, so the induction these files were
meant to feed has no valid base case. The fix (per ChatGPT, see this
project's chat log) is to run the finiteness/finrank induction on a
genuinely finite TOWER `A_0 = k, A_1 = A_0[X]/(Ḡ_0), ...`, built one
`Polynomial`-quotient at a time, and bridge back to the literal
`Rdec p ⧸ Ideal.ofList genList` presentation only at the very end.

**This file supplies exactly the "local stage equivalence" that bridge
needs, extracted from machinery `regular_of_linear_elim`
(`DecoupledSystemRegular.lean`) already builds and proves internally for a
DIFFERENT purpose (transporting `IsSMulRegular`) — the underlying ring
isomorphism is identical; only what gets transported across it differs.**
Rather than duplicate that construction, this file names it as its own
theorem so both regularity (existing) and finiteness/finrank (new, this
roadmap) can reuse the same isomorphism.

**Precisely what's proved**: for `τ` a variable type, `R` a commutative
ring, `gens' : List (MvPolynomial τ R)`, `I' := Ideal.ofList gens'`,
`B := MvPolynomial τ R ⧸ I'`, and `A := Ideal.ofList (gens'.map (rename
some)) : Ideal (MvPolynomial (Option τ) R)`, there is a ring isomorphism
`(MvPolynomial (Option τ) R ⧸ A) ≃+* Polynomial B`, sending
`mk A (rename some p) ↦ Polynomial.C (mk I' p)` for every `p : MvPolynomial
τ R`, and `mk A (X none) ↦ Polynomial.X`. This literally exhibits "the
ambient ring, mod everything already eliminated, with ONE new variable
`X none` still free" as `Polynomial` over "the same ring with that
variable already gone" — the "genuinely triangular, one variable at a
time" object the finiteness induction needs, as opposed to
`Rdec p ⧸ Ideal.ofList gens`, which still contains every unpeeled
variable no matter how large `gens` is.

**Upgraded to an `AlgEquiv`** (not just `RingEquiv`), via the same
`AlgEquiv.ofRingEquiv` + `algebraMap`-agreement pattern
`PeelChainStageFinite.lean`'s `finite_and_nontrivial_ofList_cons_of_two_step`
already uses for a structurally identical purpose — needed so
`Module.Finite`/`Nontrivial`/`Module.finrank` (all `k`-linear notions)
transport across it via the same `Module.Finite.of_surjective`/
`Function.Surjective.nontrivial`/`LinearEquiv.finrank_eq` route already
proved to work for that other isomorphism.

**Caveat this file does NOT resolve (left for the Assembly file)**: this
bridge only applies when `gens'` and `g` are genuinely split as
"already-eliminated variables" (`τ`) vs "the one variable being peeled
now" (`none` under `Option τ`) — i.e. the peel ORDER must be genuinely
triangular. Per this roadmap's own chat log, `genList`'s LITERAL order
(`FuList ++ FvList ++ [curveA1,...]`) is NOT triangular: `FuList`/`FvList`'s
coefficients (`u1_num i` etc.) depend on the curve-relation variables
(`wa1,wa2,a1,a2,wb1,wb2,b1,b2`), which are only peeled at stages 8–11,
AFTER the matching-generator stages in `genList`'s stated order. Assembly
must therefore apply this bridge along a REORDERED peel sequence (curve
relations first, then the eight matching generators), and separately
prove `Ideal.ofList` is invariant under `List.Perm` to transport the
resulting bound back onto `Ideal.ofList genList` in its original order —
neither of which this file attempts. -/

namespace Genus2Lean

open Polynomial MvPolynomial DecoupledSystem

variable {τ R : Type*} [CommRing R]

/-- **The core ring isomorphism**, extracted verbatim (same construction,
same proof obligations) from `regular_of_linear_elim`'s local `e`/`hIdealMap`.
`gens'` lives in `MvPolynomial τ R`; `A` is the ideal its image under
`rename some` generates in `MvPolynomial (Option τ) R`. -/
noncomputable def optionSplitQuotientRingEquiv (gens' : List (MvPolynomial τ R)) :
    (MvPolynomial (Option τ) R ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some))) ≃+*
      Polynomial (MvPolynomial τ R ⧸ Ideal.ofList gens') :=
  have hIdealMap : Ideal.map
      ((MvPolynomial.optionEquivLeft R τ).toRingEquiv :
        MvPolynomial (Option τ) R →+* Polynomial (MvPolynomial τ R))
      (Ideal.ofList (gens'.map (MvPolynomial.rename some))) =
      Ideal.map Polynomial.C (Ideal.ofList gens') := by
    rw [Ideal.map_ofList, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    show (MvPolynomial.optionEquivLeft R τ) (MvPolynomial.rename some p) = Polynomial.C p
    exact optionEquivLeft_rename_some p
  (Ideal.quotientEquiv (Ideal.ofList (gens'.map (MvPolynomial.rename some)))
    (Ideal.map Polynomial.C (Ideal.ofList gens'))
    (MvPolynomial.optionEquivLeft R τ).toRingEquiv hIdealMap.symm).trans
    (Ideal.ofList gens').polynomialQuotientEquivQuotientPolynomial.symm

/-- `optionSplitQuotientRingEquiv` sends `mk A (rename some p)` to
`Polynomial.C (mk I' p)`, for every `p : MvPolynomial τ R` — same proof as
`regular_of_linear_elim`'s local `he_C`. -/
theorem optionSplitQuotientRingEquiv_apply_rename_some
    (gens' : List (MvPolynomial τ R)) (p : MvPolynomial τ R) :
    optionSplitQuotientRingEquiv gens'
      (Ideal.Quotient.mk (Ideal.ofList (gens'.map (MvPolynomial.rename some)))
        (MvPolynomial.rename some p)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.ofList gens') p) := by
  unfold optionSplitQuotientRingEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  have hstep : (MvPolynomial.optionEquivLeft R τ).toRingEquiv (MvPolynomial.rename some p) =
      Polynomial.C p := optionEquivLeft_rename_some p
  rw [hstep, Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk]
  simp

/-- `optionSplitQuotientRingEquiv` sends `mk A (X none)` to
`Polynomial.X` — same proof as `regular_of_linear_elim`'s local `he_X`. -/
theorem optionSplitQuotientRingEquiv_apply_X_none (gens' : List (MvPolynomial τ R)) :
    optionSplitQuotientRingEquiv gens'
      (Ideal.Quotient.mk (Ideal.ofList (gens'.map (MvPolynomial.rename some)))
        (MvPolynomial.X none)) = Polynomial.X := by
  unfold optionSplitQuotientRingEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  have hstep : (MvPolynomial.optionEquivLeft R τ).toRingEquiv (MvPolynomial.X none) =
      Polynomial.X := MvPolynomial.optionEquivLeft_X_none R τ
  rw [hstep]
  change Polynomial.map (Ideal.Quotient.mk (Ideal.ofList gens')) Polynomial.X = Polynomial.X
  simp

/-- **`R`-algebra upgrade**, needed so `Module.Finite`/`Nontrivial`/
`Module.finrank` (base-ring-relative notions) transport across the
isomorphism. Specializes the base ring to `R` itself (matching how this
project always uses it: `Rdec p = MvPolynomial Idx (F p)`, base field
`F p` IS the coefficient ring `R`, so no extra scalar-tower layer is
needed beyond what `MvPolynomial`/`Ideal.Quotient`/`Polynomial`'s own
`Algebra R _` instances already supply). `optionSplitQuotientRingEquiv`
already agrees with both sides' `algebraMap R _` on the nose: chasing a
constant `c : R` down the LHS lands on `Ideal.Quotient.mk _ (rename some
(MvPolynomial.C c))` — a `rename-some`-shaped element, so
`optionSplitQuotientRingEquiv_apply_rename_some` applies directly with
`p := MvPolynomial.C c`, landing exactly on `Polynomial.C (mk _ (C c))`,
which is definitionally the RHS's `algebraMap R (Polynomial _) c`. -/
noncomputable def optionSplitQuotientAlgEquiv (gens' : List (MvPolynomial τ R)) :
    (MvPolynomial (Option τ) R ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some))) ≃ₐ[R]
      Polynomial (MvPolynomial τ R ⧸ Ideal.ofList gens') := by
  refine AlgEquiv.ofRingEquiv (f := optionSplitQuotientRingEquiv gens') ?_
  intro c
  have hL : algebraMap R (MvPolynomial (Option τ) R) c =
      MvPolynomial.rename (some : τ → Option τ) (MvPolynomial.C c) := by
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.rename_C]
  have hquot : algebraMap R (MvPolynomial (Option τ) R ⧸
      Ideal.ofList (gens'.map (MvPolynomial.rename some))) c =
      Ideal.Quotient.mk (Ideal.ofList (gens'.map (MvPolynomial.rename some)))
        (algebraMap R (MvPolynomial (Option τ) R) c) := by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Option τ) R)
      (MvPolynomial (Option τ) R ⧸ Ideal.ofList (gens'.map (MvPolynomial.rename some)))]
    rfl
  rw [hquot, hL, optionSplitQuotientRingEquiv_apply_rename_some]
  have hrhs : algebraMap R (Polynomial (MvPolynomial τ R ⧸ Ideal.ofList gens')) c =
      Polynomial.C (algebraMap R (MvPolynomial τ R ⧸ Ideal.ofList gens') c) := by
    rw [Polynomial.algebraMap_apply]
  rw [hrhs]
  congr 1

end Genus2Lean
