import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# The single-stage tower bridge, `Fin`-indexed: `MvPolynomial (Fin (n+1))`
# quotient ≃ₐ polynomial-over-`MvPolynomial (Fin n)` quotient

**Why this file exists, and why it is NOT just `OptionSplitPolynomialEquiv
.lean` reused as-is.** `ROADMAP-monic-annihilator-degree-uniform.md`'s
"CORRECTION, later pass" section (ChatGPT-consulted) diagnoses that
`optionSplitQuotientAlgEquiv`'s `Idx ≃ Option (Option (...))`-style
approach, while correct in shape, is more bespoke bookkeeping than
needed: Mathlib already supplies exactly the needed one-step bridge,
`MvPolynomial.finSuccEquiv K n : MvPolynomial (Fin (n+1)) K ≃ₐ[K]
Polynomial (MvPolynomial (Fin n) K)`, built internally from the SAME
`renameEquiv`/`optionEquivLeft` construction `optionSplitQuotientAlgEquiv`
re-derives by hand for `Option τ` — with `Fin.succ : Fin n → Fin (n+1)`
playing the role `some : τ → Option τ` plays there. This file is the
`Ideal.ofList`/generator-list-carrying analogue of `finSuccEquiv`, exactly
mirroring `optionSplitQuotientAlgEquiv`'s statement and proof shape
(same `Ideal.quotientEquiv` + `Ideal.map_ofList` + `polynomialQuotient
EquivQuotientPolynomial` skeleton) but with `Fin (n+1)`/`Fin.succ` in
place of `Option τ`/`some`, so the peel-chain Assembly (still to come)
never needs to build or reason about an `Option`-nested type at all —
only the fixed, once-built `idxEquivFin : Idx ≃ Fin 12`
(`IdxEquivFin.lean`) at the very end.

**Precisely what's proved**: for `n : ℕ`, `K` a field, `gens : List
(MvPolynomial (Fin n) K)`, `I := Ideal.ofList gens`,
`B := MvPolynomial (Fin n) K ⧸ I`, and `A := Ideal.ofList (gens.map
(rename Fin.succ)) : Ideal (MvPolynomial (Fin (n+1)) K)`, there is a
`K`-algebra isomorphism `(MvPolynomial (Fin (n+1)) K ⧸ A) ≃ₐ[K]
Polynomial B`, sending `mk A (rename Fin.succ p) ↦ Polynomial.C (mk I p)`
for every `p : MvPolynomial (Fin n) K`, and `mk A (X 0) ↦ Polynomial.X`.
Exactly `optionSplitQuotientAlgEquiv`'s statement with `τ := Fin n`,
`Option τ := Fin (n+1)`, `some := Fin.succ`, `none := (0 : Fin (n+1))`.

**Base ring fixed to a field `K`, unlike `OptionSplitPolynomialEquiv
.lean`'s general `CommRing R`** — this project only ever instantiates
this bridge at `K = F p`, and fixing it to a field lets this file state
its results with `Module.finrank`/`Module.Finite` directly rather than
leaving that to callers, since those notions need a field (or at least
a fixed base ring acting as scalars) to make sense of `finrank`. -/

namespace Genus2Lean

open Polynomial MvPolynomial

variable {K : Type*} [Field K]

/-- **Key computation, proved once via `ringHom_ext`** (checking agreement
only on `C` and `X`, rather than a hand-rolled induction on `q` whose case
names/shapes are easy to get subtly wrong): the ring homomorphism
`finSuccEquiv K n ∘ (rename Fin.succ)`, from `MvPolynomial (Fin n) K` to
`Polynomial (MvPolynomial (Fin n) K)`, is exactly `Polynomial.C`. Both
sides are ring homs `MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial
(Fin n) K)`; `MvPolynomial.ringHom_ext` reduces equality of ring homs out
of an `MvPolynomial` to agreement on `C a` and on `X i`, both immediate
from `finSuccEquiv_apply`'s explicit `eval₂Hom`/`Fin.cases` formula
(`Fin.cases_succ` fires since every image point is `Fin.succ`-shaped, so
`Fin.cases X (fun k => C (X k)) (Fin.succ k) = C (X k)` unconditionally —
no `none`/`X 0` case to worry about since `Fin.succ` never produces `0`). -/
theorem finSuccEquiv_comp_rename_succ_eq_C (n : ℕ) :
    (MvPolynomial.finSuccEquiv K n).toRingHom.comp
        ((MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1))).toRingHom) =
      (Polynomial.C : MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
  · intro i
    simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X,
      MvPolynomial.rename_X, Fin.cases_succ]

/-- Restated as a plain function equation, for direct `rw`/`show` use at
each call site. -/
theorem finSuccEquiv_rename_succ_apply (n : ℕ) (q : MvPolynomial (Fin n) K) :
    (MvPolynomial.finSuccEquiv K n) (MvPolynomial.rename Fin.succ q) = Polynomial.C q := by
  have := congrFun (congrArg (DFunLike.coe) (finSuccEquiv_comp_rename_succ_eq_C (K := K) n)) q
  simpa using this

noncomputable def finSuccSplitQuotientRingEquiv (n : ℕ) (gens : List (MvPolynomial (Fin n) K)) :
    (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) ≃+*
      Polynomial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) :=
  have hIdealMap : Ideal.map
      ((MvPolynomial.finSuccEquiv K n).toRingEquiv :
        MvPolynomial (Fin (n + 1)) K →+* Polynomial (MvPolynomial (Fin n) K))
      (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) =
      Ideal.map Polynomial.C (Ideal.ofList gens) := by
    rw [Ideal.map_ofList, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    show (MvPolynomial.finSuccEquiv K n) (MvPolynomial.rename Fin.succ q) = Polynomial.C q
    exact finSuccEquiv_rename_succ_apply n q
  (Ideal.quotientEquiv (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
    (Ideal.map Polynomial.C (Ideal.ofList gens))
    (MvPolynomial.finSuccEquiv K n).toRingEquiv hIdealMap.symm).trans
    (Ideal.ofList gens).polynomialQuotientEquivQuotientPolynomial.symm

/-- `finSuccSplitQuotientRingEquiv` sends `mk A (rename Fin.succ q)` to
`Polynomial.C (mk I q)`, for every `q : MvPolynomial (Fin n) K` — the
`Fin`-indexed analogue of `optionSplitQuotientRingEquiv_apply_rename_some`,
same proof shape. -/
theorem finSuccSplitQuotientRingEquiv_apply_rename_succ (n : ℕ)
    (gens : List (MvPolynomial (Fin n) K)) (q : MvPolynomial (Fin n) K) :
    finSuccSplitQuotientRingEquiv n gens
      (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (MvPolynomial.rename Fin.succ q)) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.ofList gens) q) := by
  unfold finSuccSplitQuotientRingEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  show (Ideal.ofList gens).polynomialQuotientEquivQuotientPolynomial.symm
      (Ideal.Quotient.mk (Ideal.map Polynomial.C (Ideal.ofList gens))
        ((MvPolynomial.finSuccEquiv K n) (MvPolynomial.rename Fin.succ q))) =
      Polynomial.C (Ideal.Quotient.mk (Ideal.ofList gens) q)
  rw [finSuccEquiv_rename_succ_apply, Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk]
  simp

/-- `finSuccSplitQuotientRingEquiv` sends `mk A (X 0)` to `Polynomial.X` —
the `Fin`-indexed analogue of `optionSplitQuotientRingEquiv_apply_X_none`.
-/
theorem finSuccSplitQuotientRingEquiv_apply_X_zero (n : ℕ)
    (gens : List (MvPolynomial (Fin n) K)) :
    finSuccSplitQuotientRingEquiv n gens
      (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (MvPolynomial.X 0)) = Polynomial.X := by
  unfold finSuccSplitQuotientRingEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  have hstep : (MvPolynomial.finSuccEquiv K n) (MvPolynomial.X (0 : Fin (n + 1))) =
      Polynomial.X := by
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    simp
  show (Ideal.ofList gens).polynomialQuotientEquivQuotientPolynomial.symm
      (Ideal.Quotient.mk (Ideal.map Polynomial.C (Ideal.ofList gens))
        ((MvPolynomial.finSuccEquiv K n) (MvPolynomial.X (0 : Fin (n + 1))))) =
      Polynomial.X
  rw [hstep]
  change Polynomial.map (Ideal.Quotient.mk (Ideal.ofList gens)) Polynomial.X = Polynomial.X
  simp

/-- **`K`-algebra upgrade**, needed so `Module.Finite`/`Nontrivial`/
`Module.finrank` transport across the isomorphism — the `Fin`-indexed
analogue of `optionSplitQuotientAlgEquiv`, same proof shape (chasing a
constant `c : K` down the LHS lands on a `rename Fin.succ`-shaped
element via `MvPolynomial.algebraMap_eq`/`rename_C`, so
`finSuccSplitQuotientRingEquiv_apply_rename_succ` applies directly). -/
noncomputable def finSuccSplitQuotientAlgEquiv (n : ℕ) (gens : List (MvPolynomial (Fin n) K)) :
    (MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) ≃ₐ[K]
      Polynomial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) := by
  refine AlgEquiv.ofRingEquiv (f := finSuccSplitQuotientRingEquiv n gens) ?_
  intro c
  have hL : algebraMap K (MvPolynomial (Fin (n + 1)) K) c =
      MvPolynomial.rename (Fin.succ : Fin n → Fin (n + 1)) (MvPolynomial.C c) := by
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.rename_C]
  have hquot : algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) c =
      Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (algebraMap K (MvPolynomial (Fin (n + 1)) K) c) := by
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (n + 1)) K)
      (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))]
    rfl
  rw [hquot, hL, finSuccSplitQuotientRingEquiv_apply_rename_succ]
  have hrhs : algebraMap K (Polynomial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)) c =
      Polynomial.C (algebraMap K (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) c) := by
    rw [Polynomial.algebraMap_apply]
  rw [hrhs]
  congr 1

end Genus2Lean
