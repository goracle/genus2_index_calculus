import Mathlib
import Genus2Lean.ZeroD.QuotOfListChainFinrankStep
import Genus2Lean.ZeroD.QuotOfListChainAdjoinTop
import Genus2Lean.ZeroD.SharedPivotResultantElim
import Genus2Lean.ZeroD.SharedPivotResultantElimFinite
import Genus2Lean.ZeroD.SharedPivotStageWiring
import Genus2Lean.ZeroD.LinearElimStageWiring
import Genus2Lean.ZeroD.FinrankLeOfSpanSurjective

/-!
# Finiteness-exporting version of the shared-pivot `Ideal.ofList` wiring

`SharedPivotStageWiring.lean`'s `finrank_le_sharedPivotResultantElim_
ofList_cons2` bounds `finrank` on the doubly-extended literal quotient
`Rdec p ⧸ Ideal.ofList (gens ++ [g1, g2])` but does not conclude
`Module.Finite`/`Nontrivial` there — the same gap
`PeelChainStageFinite.lean`'s own docstring already diagnosed for the
single-generator wiring theorems, and fixed there by adding a
`Module.Finite`/`Nontrivial`-exporting sibling for each. This file is
that sibling for the two-generator shared-pivot case, needed so
`GenListFinrankResultantAssembly.lean`'s four-stage resultant
elimination (`U0,U1,V0,V1`) can hand `Module.Finite`/`Nontrivial`
forward — to the next resultant stage, and ultimately to
`CurveRelationChainFinrank.lean`'s curve chain, which needs both as an
explicit hypothesis on its own starting prefix.

**Two new ingredients, beyond the `finrank`-only proof's own steps**:
1. `SharedPivotResultantElimFinite.lean`'s `finrank_le_and_finite_of_
   shared_linear_elim_pair` in place of `SharedPivotResultantElim.lean`'s
   `finrank_le_of_shared_linear_elim_pair` — gives `Module.Finite k B`
   directly, PROVIDED `Module.Finite k` is already known on the
   resultant quotient computed at the intermediate ring `A1` (i.e.
   `A1 ⧸ span {algebraMap A A1 (resultant)}`, not the outer `A ⧸ span
   {resultant}` this theorem's own hypothesis is naturally stated over).
2. `FinrankLeOfSpanSurjective.lean`'s new `finite_of_span_surjective` to
   bridge exactly that gap — transporting `Module.Finite` from the outer
   resultant quotient (`hfinRes`, this theorem's hypothesis) up to the
   `A1`-level one, along the same surjective algebra map `f1 : A →ₐ[F p]
   A1` the `finrank`-only proof already uses for the analogous `finrank`
   transport.

`Nontrivial B` is supplied directly as a hypothesis (`hnontrivB`),
matching `finrank_le_sharedPivotResultantElim_ofList_cons2`'s own
already-established pattern of taking the intermediate ring's
`Nontrivial` fact as an explicit assumption rather than deriving it —
surjectivity alone does not transport `Nontrivial` backwards from a
possibly-trivial codomain. -/

namespace Genus2Lean
namespace DecoupledSystem

variable (p : ℕ) [Fact (Nat.Prime p)]

set_option maxHeartbeats 4000000 in
/-- **Finiteness-exporting version of `finrank_le_sharedPivotResultantElim_
ofList_cons2`.** Same hypotheses, plus `Module.Finite (F p) (A ⧸ span
{resultant})` (at the OUTER prefix `gens`) and `Nontrivial B` (the
doubly-extended abstract ring). Concludes the same `finrank` bound,
plus `Module.Finite` and `Nontrivial` on the doubly-extended literal
quotient. -/
theorem finrank_le_and_finite_sharedPivotResultantElim_ofList_cons2
    (gens : List (Rdec p)) (u : Idx) (n1 d1 n2 d2 : Rdec p)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    [Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)]
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    [Nontrivial ((Rdec p ⧸ Ideal.ofList gens) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) (linearElimGen p n1 d1 u)} :
        Set (Rdec p ⧸ Ideal.ofList gens)))]
    (hd1 : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) d1))
    (hfinRes : Module.Finite (F p)
      ((Rdec p ⧸ Ideal.ofList gens) ⧸
        Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) n2 *
            Ideal.Quotient.mk (Ideal.ofList gens) d1 -
          Ideal.Quotient.mk (Ideal.ofList gens) n1 *
            Ideal.Quotient.mk (Ideal.ofList gens) d2} :
          Set (Rdec p ⧸ Ideal.ofList gens))))
    (hnontrivB : Nontrivial
      (((Rdec p ⧸ Ideal.ofList gens) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) (linearElimGen p n1 d1 u)} :
            Set (Rdec p ⧸ Ideal.ofList gens))) ⧸
        Ideal.span ({((Ideal.Quotient.mk
            (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) (linearElimGen p n1 d1 u)} :
              Set (Rdec p ⧸ Ideal.ofList gens)))).comp
            (Ideal.Quotient.mk (Ideal.ofList gens)))
            (linearElimGen p n2 d2 u)} :
          Set ((Rdec p ⧸ Ideal.ofList gens) ⧸
            Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) (linearElimGen p n1 d1 u)} :
              Set (Rdec p ⧸ Ideal.ofList gens)))))) :
    Module.Finite (F p)
      (Rdec p ⧸ Ideal.ofList (gens ++ [linearElimGen p n1 d1 u, linearElimGen p n2 d2 u])) ∧
    Nontrivial
      (Rdec p ⧸ Ideal.ofList (gens ++ [linearElimGen p n1 d1 u, linearElimGen p n2 d2 u])) ∧
    Module.finrank (F p)
        (Rdec p ⧸ Ideal.ofList
          (gens ++ [linearElimGen p n1 d1 u, linearElimGen p n2 d2 u])) ≤
      Module.finrank (F p)
        ((Rdec p ⧸ Ideal.ofList gens) ⧸
          Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) n2 *
              Ideal.Quotient.mk (Ideal.ofList gens) d1 -
            Ideal.Quotient.mk (Ideal.ofList gens) n1 *
              Ideal.Quotient.mk (Ideal.ofList gens) d2} :
            Set (Rdec p ⧸ Ideal.ofList gens))) := by
  rw [show gens ++ [linearElimGen p n1 d1 u, linearElimGen p n2 d2 u] =
      (gens ++ [linearElimGen p n1 d1 u]) ++ [linearElimGen p n2 d2 u] by
    rw [List.append_assoc]; rfl]
  set A := Rdec p ⧸ Ideal.ofList gens with hA_def
  set g1 := linearElimGen p n1 d1 u with hg1_def
  set n1A : A := Ideal.Quotient.mk (Ideal.ofList gens) n1 with hn1A_def
  set d1A : A := Ideal.Quotient.mk (Ideal.ofList gens) d1 with hd1A_def
  set n2A : A := Ideal.Quotient.mk (Ideal.ofList gens) n2 with hn2A_def
  set d2A : A := Ideal.Quotient.mk (Ideal.ofList gens) d2 with hd2A_def
  set A1 := A ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A) with hA1_def
  set φ1 : Rdec p →+* A1 :=
    (Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))).comp
      (Ideal.Quotient.mk (Ideal.ofList gens)) with hφ1_def
  set g2 := linearElimGen p n2 d2 u with hg2_def
  set B := A1 ⧸ Ideal.span ({φ1 g2} : Set A1) with hB_def
  set t : B := Ideal.Quotient.mk _ (φ1 (MvPolynomial.X u)) with ht_def
  have hd1A1 : IsUnit (algebraMap A A1 d1A) := hd1.map (algebraMap A A1)
  have ht1 : (Polynomial.aeval t) (linearElimPoly (algebraMap A A1 n1A) (algebraMap A A1 d1A))
      = 0 := by
    have hφ1g1 : algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens) g1) = 0 := by
      show Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) g1) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have hmkg1 : (Ideal.Quotient.mk (Ideal.ofList gens) g1 : A) =
        n1A - Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u) * d1A := by
      rw [hg1_def, linearElimGen, hn1A_def, hd1A_def, map_sub, map_mul]
    have hgoal : algebraMap A A1 n1A - algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens)
        (MvPolynomial.X u)) * algebraMap A A1 d1A = 0 := by
      have := congrArg (algebraMap A A1) hmkg1
      rw [map_sub, map_mul] at this
      rw [← this, hφ1g1]
    have hφ1X : algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) =
        φ1 (MvPolynomial.X u) := rfl
    rw [hφ1X] at hgoal
    rw [linearElimPoly, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.aeval_C]
    have ht_eq : t = algebraMap A1 B (φ1 (MvPolynomial.X u)) := rfl
    rw [ht_eq, ← map_mul, ← map_sub, hgoal, map_zero]
  have ht2 : (Polynomial.aeval t) (linearElimPoly (algebraMap A A1 n2A) (algebraMap A A1 d2A))
      = 0 := by
    have hmkg2 : (Ideal.Quotient.mk (Ideal.ofList gens) g2 : A) =
        n2A - Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u) * d2A := by
      rw [hg2_def, linearElimGen, hn2A_def, hd2A_def, map_sub, map_mul]
    have hφ1g2 : algebraMap A A1 n2A - algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens)
        (MvPolynomial.X u)) * algebraMap A A1 d2A = φ1 g2 := by
      have := congrArg (algebraMap A A1) hmkg2
      rw [map_sub, map_mul] at this
      rw [← this]
      rfl
    have hφ1X : algebraMap A A1 (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) =
        φ1 (MvPolynomial.X u) := rfl
    rw [hφ1X] at hφ1g2
    rw [linearElimPoly, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.aeval_C]
    have ht_eq : t = algebraMap A1 B (φ1 (MvPolynomial.X u)) := rfl
    rw [ht_eq, ← map_mul, ← map_sub, hφ1g2]
    show Ideal.Quotient.mk (Ideal.span ({φ1 g2} : Set A1)) (φ1 g2) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hgen : Algebra.adjoin A1 ({t} : Set B) = (⊤ : Subalgebra A1 B) :=
    adjoin_singleton_eq_top_of_quotient _ t
  -- `f1 : A →ₐ[F p] A1`, the same surjective quotient map the
  -- `finrank`-only proof uses to transport its own bound.
  set f1 : A →ₐ[F p] A1 :=
    Ideal.Quotient.mkₐ (F p) (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
    with hf1_def
  have hsurj : Function.Surjective (algebraMap A A1) := Ideal.Quotient.mk_surjective
  have hsurj' : Function.Surjective f1 := hsurj
  -- `f1 (n2A*d1A - n1A*d2A)` unfolds to the SAME element
  -- `finrank_le_of_shared_linear_elim_pair`'s own resultant argument
  -- computes (`algebraMap A A1 n2A * algebraMap A A1 d1A - algebraMap A
  -- A1 n1A * algebraMap A A1 d2A`) — same identity the `finrank`-only
  -- proof already establishes as `hgenEq`.
  have hgenEq : f1 (n2A * d1A - n1A * d2A) =
      algebraMap A A1 n2A * algebraMap A A1 d1A - algebraMap A A1 n1A * algebraMap A A1 d2A := by
    show algebraMap A A1 (n2A * d1A - n1A * d2A) = _
    rw [map_sub, map_mul, map_mul]
  -- **New step**: `Module.Finite` on the `A1`-level resultant quotient,
  -- transported from `hfinRes` (stated at the outer `A`) via
  -- `finite_of_span_surjective`.
  have hfinResA1 : Module.Finite (F p)
      (A1 ⧸ Ideal.span ({algebraMap A A1 n2A * algebraMap A A1 d1A -
          algebraMap A A1 n1A * algebraMap A A1 d2A} : Set A1)) := by
    rw [← hgenEq]
    exact finite_of_span_surjective (k := F p) f1 hsurj' (n2A * d1A - n1A * d2A)
  -- `finrank_le_and_finite_of_shared_linear_elim_pair` needs `hfinRes`
  -- stated with the resultant written as `n2*d1 - n1*d2` (its own
  -- argument order), matching `hfinResA1` up to `mul_comm`/associativity
  -- — here the two sides are already syntactically identical since
  -- `hgenEq`'s RHS is exactly `algebraMap A A1 n2A * algebraMap A A1 d1A
  -- - algebraMap A A1 n1A * algebraMap A A1 d2A`, the same shape the
  -- pair theorem's own `n2*d1-n1*d2` argument expects with
  -- `n1 := algebraMap A A1 n1A` etc.
  obtain ⟨hfinB, hbound⟩ := finrank_le_and_finite_of_shared_linear_elim_pair (k := F p)
    (algebraMap A A1 n1A) (algebraMap A A1 d1A) (algebraMap A A1 n2A) (algebraMap A A1 d2A)
    hd1A1 t ht1 ht2 hgen hfinResA1
  have htransport := finrank_le_of_span_surjective (k := F p) f1 hsurj' (n2A * d1A - n1A * d2A)
  rw [hgenEq] at htransport
  have hB_le_A : Module.finrank (F p) B ≤
      Module.finrank (F p) (A ⧸ Ideal.span ({n2A * d1A - n1A * d2A} : Set A)) :=
    le_trans hbound htransport
  clear hbound htransport hsurj hsurj' hgenEq hf1_def f1 hd1A1 ht1 ht2 hgen hfinResA1
  -- The same `AlgEquiv` `e23 : B ≃ₐ[F p] Rdec p ⧸ Ideal.ofList ((gens ++
  -- [g1]) ++ [g2])` the `finrank`-only proof builds, reused here to
  -- transport `Module.Finite`/`Nontrivial` forward as well as `finrank`.
  have hgenEq2 : Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++ [g1])) g2} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++ [g1]))) =
      Ideal.map (quotOfListCons_ringEquiv gens g1) (Ideal.span ({φ1 g2} : Set A1)) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 1
  let e2 : B ≃+* (Rdec p ⧸ Ideal.ofList (gens ++ [g1])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++ [g1])) g2} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++ [g1]))) :=
    Ideal.quotientEquiv (Ideal.span ({φ1 g2} : Set A1))
      (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++ [g1])) g2} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++ [g1]))))
      (quotOfListCons_ringEquiv gens g1) hgenEq2
  let e3 : (Rdec p ⧸ Ideal.ofList (gens ++ [g1])) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++ [g1])) g2} :
        Set (Rdec p ⧸ Ideal.ofList (gens ++ [g1]))) ≃+*
      Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2]) :=
    quotOfListCons_ringEquiv (gens ++ [g1]) g2
  let e23 : B ≃+* Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2]) :=
    e2.trans e3
  have halg23 : ∀ c : F p, e23 (algebraMap (F p) B c) = algebraMap (F p)
      (Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2])) c := by
    intro c
    have hlhs0 : algebraMap (F p) B c =
        Ideal.Quotient.mk (Ideal.span ({φ1 g2} : Set A1))
          (Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) (algebraMap (F p) (Rdec p) c))) := by
      rw [IsScalarTower.algebraMap_apply (F p) A1 B,
        IsScalarTower.algebraMap_apply (F p) A A1,
        IsScalarTower.algebraMap_apply (F p) (Rdec p) A]
      rfl
    show e23 (algebraMap (F p) B c) = _
    rw [hlhs0]
    show e2.trans e3 _ = _
    rw [RingEquiv.trans_apply]
    show e3 (e2 _) = _
    rw [show e2 (Ideal.Quotient.mk (Ideal.span ({φ1 g2} : Set A1))
          (Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) (algebraMap (F p) (Rdec p) c)))) =
        Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++ [g1])) g2} :
            Set (Rdec p ⧸ Ideal.ofList (gens ++ [g1]))))
          (quotOfListCons_ringEquiv gens g1
            (Ideal.Quotient.mk (Ideal.span
              ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
              (Ideal.Quotient.mk (Ideal.ofList gens) (algebraMap (F p) (Rdec p) c))))
      from Ideal.quotientEquiv_mk (Ideal.span ({φ1 g2} : Set A1))
        (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList (gens ++ [g1])) g2} :
          Set (Rdec p ⧸ Ideal.ofList (gens ++ [g1]))))
        (quotOfListCons_ringEquiv gens g1) hgenEq2
        (Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g1} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) (algebraMap (F p) (Rdec p) c)))]
    rw [quotOfListCons_ringEquiv_apply_mk_mk gens g1 (algebraMap (F p) (Rdec p) c)]
    show e3 (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.ofList (gens ++ [g1]))
      (algebraMap (F p) (Rdec p) c))) = _
    have hrhs : algebraMap (F p) (Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2])) c =
        Ideal.Quotient.mk (Ideal.ofList ((gens ++ [g1]) ++ [g2]))
          (algebraMap (F p) (Rdec p) c) := by
      rw [IsScalarTower.algebraMap_apply (F p) (Rdec p)
        (Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2]))]
      rfl
    rw [hrhs]
    exact quotOfListCons_ringEquiv_apply_mk_mk (gens ++ [g1]) g2 (algebraMap (F p) (Rdec p) c)
  set e23alg : B ≃ₐ[F p] Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2]) :=
    AlgEquiv.ofRingEquiv (f := e23) halg23 with he23alg_def
  have hBeq : Module.finrank (F p) B =
      Module.finrank (F p) (Rdec p ⧸ Ideal.ofList ((gens ++ [g1]) ++ [g2])) :=
    LinearEquiv.finrank_eq e23alg.toLinearEquiv
  -- Transport `Module.Finite`/`Nontrivial` forward along `e23alg`
  -- (already-known on `B`: `hfinB` from the `Module.Finite`-exporting
  -- pair theorem above, `hnontrivB` supplied directly) — an `AlgEquiv`
  -- is in particular a `k`-linear equivalence (`Module.Finite.equiv`).
  -- For `Nontrivial`, `Function.Surjective.nontrivial` PULLS a
  -- `Nontrivial` instance BACKWARDS along a surjection (codomain
  -- nontrivial ⟹ domain nontrivial) — the wrong direction here (`B` is
  -- the domain, the literal quotient is the codomain of `e23alg`); the
  -- right tool for pushing forward across a genuine bijection is
  -- `Equiv.nontrivial`, applied to `e23alg.toEquiv.symm : (literal
  -- quotient) ≃ B` with `[Nontrivial B]` in scope (`hnontrivB`), giving
  -- `Nontrivial (literal quotient)` directly.
  haveI : Nontrivial B := hnontrivB
  refine ⟨Module.Finite.equiv e23alg.toLinearEquiv,
    Equiv.nontrivial e23alg.toEquiv.symm, ?_⟩
  rw [← hBeq]
  exact hB_le_A

end DecoupledSystem
end Genus2Lean
