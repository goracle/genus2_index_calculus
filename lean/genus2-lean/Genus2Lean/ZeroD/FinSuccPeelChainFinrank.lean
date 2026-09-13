import Mathlib
import Genus2Lean.ZeroD.FinSuccSplitPolynomialEquiv
import Genus2Lean.ZeroD.FinrankLeOfMonicAnnihilatorFinite
import Genus2Lean.ZeroD.QuotOfListChain

/-!
# Assembly, item (c): the `Fin n`-indexed peel with a genuine `n = 0` base case

`ROADMAP-monic-annihilator-degree-uniform.md`'s "CORRECTION, later pass"
section diagnoses the exact gap `GenListFinrankAssembly.lean`'s
`genList_finrank_le` `sorry` exposes: inducting on `Ideal.ofList` prefixes
of a FIXED-arity ring `Rdec p = MvPolynomial Idx (F p)` never reaches a
genuine base case, because every proper prefix (including the empty one,
`Rdec p` itself) still has free `Idx` variables and is therefore never
finite-dimensional over `F p` — no prefix of a fixed-arity polynomial
ring is finite until literally every variable is eliminated.
`PeelChainAssemblyFinrank.lean`'s `finrank_le_and_finite_of_append` is
honest about this: it takes `Module.Finite` on the STARTING prefix as a
hypothesis rather than manufacturing a false base case internally, so it
is correct but not, by itself, applicable starting from `gens = []`.

**The actual fix**: don't induct on `Ideal.ofList` prefixes of a
fixed-arity ring. Induct on the AMBIENT RING'S ARITY instead, peeling one
`Fin`-indexed variable at a time via `MvPolynomial.finSuccEquiv`
(`FinSuccSplitPolynomialEquiv.lean`'s `finSuccSplitQuotientAlgEquiv`): at
each step the base ring itself has one fewer free variable, so at `n = 0`
the ring `MvPolynomial (Fin 0) K` genuinely IS finite over `K`
(`MvPolynomial.isEmptyAlgEquiv K (Fin 0) : MvPolynomial (Fin 0) K ≃ₐ[K]
K`, since `Fin 0` is empty, giving `Module.finrank K (MvPolynomial
(Fin 0) K) = 1`) — the base case this project actually needs.

**Scope of this file**: fully generic over `n : ℕ`/`K`/`gens`, zero
`Idx`/`Rdec p`/`theData` content, matching this project's established
split between "generic reusable step" and "wiring to the literal peel
chain". This file supplies only the ONE-STAGE peel
(`finrank_le_and_finite_finSucc_peel`); folding it into an `n`-stage
induction with the genuine `n = 0` base case (`MvPolynomial.isEmptyAlgEquiv`)
is the next file, still to come, and the final `Idx`-specific wiring
(transporting `genList`'s twelve literal generators across
`idxEquivFin`/`renameEquiv` to discharge `GenListFinrankAssembly.lean`'s
`sorry`) is the file after that. -/

namespace Genus2Lean

open Polynomial MvPolynomial

variable {K : Type*} [Field K]

set_option maxHeartbeats 2000000 in
/-- **One-stage peel, `Fin`-indexed.** `A := MvPolynomial (Fin n) K ⧸
Ideal.ofList gens` is the algebra built from the first `n` variables'
relations so far. `g : MvPolynomial (Fin (n+1)) K` is the new generator
(a relation among the `Fin (n+1)`-indexed variables, extending `gens`
renamed via `Fin.succ`), and `G : Polynomial A` is its image under
`finSuccSplitQuotientAlgEquiv` (pinned down by `hg`) — a monic polynomial
annihilating the class of `X 0`.

**Proof, composing two already-proved facts, no new core content**:
(1) `finSuccSplitQuotientAlgEquiv n gens`, restricted one level further
via `Ideal.quotientEquiv` (using `hg` to show it carries `Ideal.span
{mk g}` onto `Ideal.span {G}`), identifies the LITERAL two-step quotient
`(MvPolynomial (Fin (n+1)) K ⧸ Ideal.ofList gens') ⧸ Ideal.span {mk g}`
with `B := Polynomial A ⧸ Ideal.span {G}` as `K`-algebras; (2)
`finrank_le_of_monic_annihilator_of_finite` bounds `finrank` on `B` (with
`t := mk X`, `ht` from `G` annihilating itself mod its own span, `hgen`
from `Polynomial.X` generating `Polynomial A` as an `A`-algebra); (3)
`quotOfListCons_ringEquiv` (`QuotOfListChain.lean`) identifies that
two-step quotient with the literal ONE-STEP quotient `MvPolynomial
(Fin (n+1)) K ⧸ Ideal.ofList (gens' ++ [g])` the caller actually wants. -/
theorem finrank_le_and_finite_finSucc_peel
    (n : ℕ) (gens : List (MvPolynomial (Fin n) K)) (g : MvPolynomial (Fin (n + 1)) K)
    (G : Polynomial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)) (hG : G.Monic)
    (hfinA : Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens))
    (hg_ne : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g))
    (hg : finSuccSplitQuotientAlgEquiv n gens
        (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g) = G) :
    Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ) ++ [g])) ∧
    Nontrivial (MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ) ++ [g])) ∧
    Module.finrank K (MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ) ++ [g])) ≤
      G.natDegree * Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) := by
  set A := MvPolynomial (Fin n) K ⧸ Ideal.ofList gens with hA_def
  set gens' := gens.map (MvPolynomial.rename Fin.succ) with hgens'_def
  set e := finSuccSplitQuotientAlgEquiv n gens with he_def
  set B := Polynomial A ⧸ Ideal.span ({G} : Set (Polynomial A)) with hB_def
  -- `t := mk X`, the class of the peeled variable in `B`.
  set t : B := Ideal.Quotient.mk _ Polynomial.X with ht_def
  have ht : (Polynomial.aeval t) G = 0 := by
    have hφ : (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A)))) G = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    -- `aeval t G = (mk : Polynomial A →+* B) (G.eval₂ C X)`, and
    -- `G.eval₂ C X = G` (`Polynomial.eval₂_C_X`), so this is `hφ`.
    have heval : (Polynomial.aeval t) G =
        (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A))))
          (G.eval₂ Polynomial.C Polynomial.X) := by
      rw [Polynomial.aeval_def]
      -- Prove the underlying fact for an arbitrary polynomial `p'`, by
      -- induction on `p'` (NOT on `G`): `G` is fixed throughout this
      -- proof (`B`, `t`, `hφ` above already depend on it), so inducting
      -- on `G` directly would incorrectly re-generalize those.
      -- `mk (C a) = algebraMap A B a`, proved via the named algebra-map
      -- lemmas rather than `rfl`: unfolding `A`/`B` (both `set`-bound
      -- quotient types) far enough for defeq is expensive and risks a
      -- heartbeat timeout, so we go through
      -- `Polynomial.algebraMap_apply` (`algebraMap A (Polynomial A) a =
      -- C a`, using that `algebraMap A A` is the identity) and
      -- `Ideal.Quotient.mk_algebraMap` (`mk (algebraMap A (Polynomial A)
      -- a) = algebraMap A (Polynomial A ⧸ _) a`) instead.
      have hCa : ∀ a : A, (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A))))
          (Polynomial.C a) = (algebraMap A B) a := by
        intro a
        have h1 : (Polynomial.C a : Polynomial A) = algebraMap A (Polynomial A) a := by
          simp [Polynomial.algebraMap_apply]
        rw [h1]
        exact Ideal.Quotient.mk_algebraMap A (Ideal.span ({G} : Set (Polynomial A))) a
      have hgen : ∀ p' : Polynomial A,
          Polynomial.eval₂ (algebraMap A B) t p' =
            (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A))))
              (p'.eval₂ Polynomial.C Polynomial.X) := by
        intro p'
        induction p' using Polynomial.induction_on with
        | C a => rw [Polynomial.eval₂_C, Polynomial.eval₂_C, hCa]
        | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq]
        | monomial p a _ =>
          simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
            Polynomial.eval₂_X, map_mul, map_pow, ht_def, hCa]
      exact hgen G
    rw [heval, Polynomial.eval₂_C_X]
    exact hφ
  have hgen : Algebra.adjoin A ({t} : Set B) = (⊤ : Subalgebra A B) := by
    have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span
        ({G} : Set (Polynomial A)))) := Ideal.Quotient.mk_surjective
    -- Same fact as `hCa` above (this `have` block is separate, so we
    -- re-derive it locally rather than reaching across).
    have hCa : ∀ a : A, (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A))))
        (Polynomial.C a) = (algebraMap A B) a := by
      intro a
      have h1 : (Polynomial.C a : Polynomial A) = algebraMap A (Polynomial A) a := by
        simp [Polynomial.algebraMap_apply]
      rw [h1]
      exact Ideal.Quotient.mk_algebraMap A (Ideal.span ({G} : Set (Polynomial A))) a
    rw [eq_top_iff]
    rintro b -
    obtain ⟨q, rfl⟩ := hsurj b
    induction q using Polynomial.induction_on with
    | C a =>
        rw [hCa]
        exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq =>
        have hcast : (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A)))) (p + q) =
            (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A)))) p +
              (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A)))) q := map_add _ _ _
        rw [hcast]
        exact Subalgebra.add_mem _ hp hq
    | monomial p a _ =>
        have hcast : (Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A))))
            (Polynomial.C a * Polynomial.X ^ (p + 1)) =
            algebraMap A B a * t ^ (p + 1) := by
          rw [map_mul, map_pow, hCa]
        rw [hcast]
        have ht_mem : t ∈ Algebra.adjoin A ({t} : Set B) :=
          Algebra.subset_adjoin (by simp)
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a)
          (Subalgebra.pow_mem _ ht_mem _)
  haveI : Nontrivial A := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hA
    letI : Subsingleton A := hA
    have hx : (Ideal.Quotient.mk (Ideal.ofList gens') g :
        MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') = 1 := by
      apply e.injective
      exact Subsingleton.elim _ _
    exact hg_ne (hx ▸ isUnit_one)
  obtain ⟨hfinB, hbound⟩ :=
    finrank_le_of_monic_annihilator_of_finite (k := K) hfinA G hG t ht hgen
  -- Step (1): identify the two-step `Fin (n+1)`-indexed quotient with `B`.
  have hmapEq : Ideal.span ({G} : Set (Polynomial A)) =
      Ideal.map e.toRingEquiv (Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
          Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) := by
    rw [Ideal.map_span, Set.image_singleton]
    have himg : e.toRingEquiv (Ideal.Quotient.mk (Ideal.ofList gens') g) = G := by
      show e (Ideal.Quotient.mk (Ideal.ofList gens') g) = G
      exact hg
    rw [himg]
  set e2 : ((MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') ⧸ Ideal.span
      ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
        Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) ≃+* B :=
    Ideal.quotientEquiv _ _ e.toRingEquiv hmapEq with he2_def
  have he2_alg : ∀ c : K, e2 (algebraMap K ((MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.ofList gens') ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
          Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) c) =
      algebraMap K B c := by
    intro c
    have hlhs : (algebraMap K ((MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList gens') ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')))) c =
        Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')))
          (algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') c) := by
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')
        ((MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')))]
      rfl
    rw [hlhs, he2_def, Ideal.quotientEquiv_mk]
    show Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A)))
        (e.toRingEquiv (algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') c)) =
      algebraMap K B c
    have hAlgE : e (algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') c) =
        algebraMap K (Polynomial A) c := e.commutes c
    show Ideal.Quotient.mk (Ideal.span ({G} : Set (Polynomial A)))
        (e (algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') c)) =
      algebraMap K B c
    rw [hAlgE]
    rfl
  set e2' : ((MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') ⧸ Ideal.span
      ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
        Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) ≃ₐ[K] B :=
    AlgEquiv.ofRingEquiv (f := e2) he2_alg with he2'_def
  have hfinTwoStep : Module.Finite K ((MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.ofList gens') ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
          Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) :=
    Module.Finite.equiv e2'.symm.toLinearEquiv
  have hfinrankTwoStep : Module.finrank K ((MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.ofList gens') ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
          Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) =
      Module.finrank K B := LinearEquiv.finrank_eq e2'.toLinearEquiv
  -- Step (3): identify that two-step quotient with the literal one-step
  -- quotient via `quotOfListCons_ringEquiv`.
  set e3 := quotOfListCons_ringEquiv gens' g with he3_def
  have he3_alg : ∀ c : K, e3 (algebraMap K ((MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.ofList gens') ⧸ Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
          Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) c) =
      algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList (gens' ++ [g])) c := by
    intro c
    have hlhs : (algebraMap K ((MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList gens') ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')))) c =
        Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')))
          (Ideal.Quotient.mk (Ideal.ofList gens')
            (algebraMap K (MvPolynomial (Fin (n + 1)) K) c)) := by
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')
        ((MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')))]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (n + 1)) K)
        (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens')]
      rfl
    have hrhs : (algebraMap K (MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList (gens' ++ [g]))) c =
        Ideal.Quotient.mk (Ideal.ofList (gens' ++ [g]))
          (algebraMap K (MvPolynomial (Fin (n + 1)) K) c) := by
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (n + 1)) K)
        (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList (gens' ++ [g]))]
      rfl
    rw [hlhs, hrhs]
    exact quotOfListCons_ringEquiv_apply_mk_mk gens' g (algebraMap K (MvPolynomial (Fin (n + 1)) K) c)
  set e3' : ((MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens') ⧸ Ideal.span
      ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
        Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) ≃ₐ[K]
      (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList (gens' ++ [g])) :=
    AlgEquiv.ofRingEquiv (f := e3) he3_alg with he3'_def
  have hfinExt : Module.Finite K (MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.ofList (gens' ++ [g])) :=
    Module.Finite.of_surjective e3'.toLinearMap e3'.surjective
  have hnontrivExt : Nontrivial (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList (gens' ++ [g])) := by
    have hG_ne : ¬ IsUnit G := by
      intro hGU
      apply hg_ne
      have hGU' : IsUnit (e.symm G) := hGU.map e.symm.toRingHom
      have he_symm : e.symm G =
          Ideal.Quotient.mk (Ideal.ofList gens') g := by
        rw [← hg]
        exact e.symm_apply_apply _
      rwa [he_symm] at hGU'
    haveI : Nontrivial B := nontrivial_of_span_ne_top hG_ne
    -- `e2' : two-step ≃ₐ[K] B`, `Nontrivial B` in context, so
    -- `e2'.toEquiv : two-step ≃ B` gives `Nontrivial (two-step)`.
    haveI hnontrivTwoStep : Nontrivial ((MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList gens') ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) :=
      e2'.toEquiv.nontrivial
    -- `e3' : two-step ≃ₐ[K] (one-step extended)`, `Nontrivial (two-step)`
    -- in context, so `e3'.toEquiv.symm : (one-step extended) ≃ two-step`
    -- gives `Nontrivial (one-step extended)`.
    exact e3'.toEquiv.symm.nontrivial
  have hfinrankExt : Module.finrank K (MvPolynomial (Fin (n + 1)) K ⧸
      Ideal.ofList (gens' ++ [g])) = Module.finrank K ((MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList gens') ⧸ Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens') g} :
            Set (MvPolynomial (Fin (n + 1)) K ⧸ Ideal.ofList gens'))) :=
    LinearEquiv.finrank_eq e3'.symm.toLinearEquiv
  refine ⟨hfinExt, hnontrivExt, ?_⟩
  rw [hfinrankExt, hfinrankTwoStep]
  exact hbound

end Genus2Lean
