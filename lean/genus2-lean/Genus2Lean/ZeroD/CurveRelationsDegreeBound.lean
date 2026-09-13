import Mathlib
import Genus2Lean.ZeroD.FinrankLeOfMonicAnnihilator

/-!
# Stages 8–11 degree bound: the four curve relations

Item 4 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, and
step 2 of its "Suggested order" (done right after the core lemma, before
the matching-generator stages 0–7, since these four stages are already
literally monic and need no leading-coefficient/unit bookkeeping — the
fastest way to confirm `finrank_le_of_monic_annihilator` composes
correctly end-to-end).

**Shape, from `DecoupledSystemRegular.lean` §3**: each curve relation is
`curveA1 = wa1'² − f(a1)`, `curveA2 = wa2'² − f(a2)`, `curveB1 = wb1'² −
f(b1)`, `curveB2 = wb2'² − f(b2)` — literally `X² − C f` in the
newly-peeled variable (`wa1`, `wa2`, `wb1`, `wb2` respectively), already
monic of degree 2, matching the peel chain's own stage-by-stage table in
the roadmap (stages 8–11, `d = 2`).

**What this file provides**: a single generic per-stage lemma,
`finrank_le_of_curve_relation`, stated abstractly over any commutative
ring `A` (playing the role of "the algebra built from the previous
stages") and any `f : A` (playing the role of the already-quotiented
`f(a1)`/etc. value) — NOT yet specialized to `Rdec p` or wired into the
literal `genList`/`curveA1` definitions. That wiring (identifying `A`
with the actual 8-or-more-generator quotient `Rdec p ⧸ Ideal.ofList
prefix`, and `f` with the image of `c0 + c1·a1 + ... + a1⁵` there) is
left to the later Assembly file (item 5), per the roadmap's own
file-plan split between "single-stage fact" (this file) and "chaining
across stages, and identifying each concrete peel-chain generator's
monic form" (later files).

**Proof strategy**: apply `Genus2Lean.finrank_le_of_monic_annihilator`
with `G := X² − C f : Polynomial A`, `d := 2`, `B := A ⧸ Ideal.span
{X² − C f}`-shaped quotient realized as `AdjoinRoot (X² − C f)` (so that
`Algebra.adjoin A {t} = ⊤` is immediate via `AdjoinRoot.powerBasis'`
together with `PowerBasis.adjoin_gen_eq_top`, since `(AdjoinRoot.powerBasis'
hG).gen = AdjoinRoot.root G` by construction), and `t := AdjoinRoot.root
(X² − C f)`, with the annihilation fact `aeval t G = 0` obtained from
`AdjoinRoot.eval₂_root` (which gives the `eval₂`-shaped statement
directly) bridged to `aeval` via `Polynomial.aeval_def`/
`AdjoinRoot.algebraMap_eq` — the same bridging step used already in this
project's `regular_of_norm_eliminate_one` (`DecoupledSystemRegular.lean`)
for the analogous `w² = f` fact. -/

namespace Genus2Lean

open Polynomial

variable {k A : Type*} [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
  [StrongRankCondition A] [Module.Finite k A]

/-- The curve-relation polynomial `X² − C f`, monic of degree 2 for any
`f : A` (no hypotheses on `f` needed — unlike the matching generators,
there is no leading-coefficient-unit condition here, since the leading
coefficient of `X²` is literally `1`). -/
noncomputable def curveRelationPoly (f : A) : Polynomial A :=
  Polynomial.X ^ 2 - Polynomial.C f

theorem curveRelationPoly_monic (f : A) : (curveRelationPoly f).Monic := by
  unfold curveRelationPoly
  exact Polynomial.monic_X_pow_sub_C f (by norm_num)

theorem curveRelationPoly_natDegree (f : A) :
    (curveRelationPoly f).natDegree = 2 := by
  unfold curveRelationPoly
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C f : Polynomial A).degree = (2 : WithBot ℕ) :=
    Polynomial.degree_X_pow_sub_C (R := A) (n := 2) (by norm_num) f
  exact Polynomial.natDegree_eq_of_degree_eq_some hdeg

/-- **The per-stage fact for a curve relation.** `B := AdjoinRoot (X² −
C f)` is the `A`-algebra obtained by adjoining a root of the
curve-relation polynomial — exactly the shape `curveA1`/`curveA2`/
`curveB1`/`curveB2` take once the previous-stage variables have been
quotiented away, per this file's docstring. Its `k`-dimension is at
most twice `A`'s. -/
theorem finrank_le_of_curve_relation (f : A) :
    Module.finrank k (AdjoinRoot (curveRelationPoly f)) ≤ 2 * Module.finrank k A := by
  have hmonic : (curveRelationPoly f).Monic := curveRelationPoly_monic f
  have hdeg : (curveRelationPoly f).natDegree = 2 := curveRelationPoly_natDegree f
  set t : AdjoinRoot (curveRelationPoly f) := AdjoinRoot.root (curveRelationPoly f) with ht_def
  -- `AdjoinRoot.eval₂_root` gives the `eval₂`-shaped self-annihilation
  -- fact directly against `AdjoinRoot.of`; rewrite it into the `aeval`
  -- shape `finrank_le_of_monic_annihilator` wants via `Polynomial.aeval_def`
  -- and `AdjoinRoot.algebraMap_eq` (the same bridging step `DecoupledSystem
  -- Regular.lean`'s `regular_of_norm_eliminate_one` already uses for the
  -- analogous `w^2 = f` identity) — using the CANONICAL `AdjoinRoot`
  -- algebra instances throughout, not re-derived ones, to avoid a diamond.
  have ht : (Polynomial.aeval t) (curveRelationPoly f) = 0 := by
    have hroot := AdjoinRoot.eval₂_root (curveRelationPoly f)
    rw [Polynomial.aeval_def, ht_def, AdjoinRoot.algebraMap_eq]
    unfold curveRelationPoly at hroot ⊢
    rwa [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at hroot ⊢
  -- `t` generates `B` as an `A`-algebra: every element of `AdjoinRoot G`
  -- is `AdjoinRoot.mk G q` for some polynomial `q : Polynomial A`, and
  -- `AdjoinRoot.mk G q` lies in `Algebra.adjoin A {t}` by polynomial
  -- induction (`AdjoinRoot.mk_C`, `AdjoinRoot.mk_X` — the same confirmed
  -- lemmas this project's own `regular_of_norm_eliminate_one` already
  -- uses — plus `map_add`/`map_mul`), since `t` itself does and adjoin is
  -- closed under the algebra operations.
  --
  -- Proved as a standalone `have` over a fully generic `q`, BEFORE the
  -- `AdjoinRoot.induction_on` case split below: nesting a second,
  -- heavyweight induction inside that split's single branch was forcing
  -- Lean to re-elaborate the whole ambient context (`k`, `A`, all the
  -- typeclass args) at every polynomial-induction step, which is what
  -- blew the heartbeat budget. Pulling it out here means the case split
  -- below is just one `apply`.
  have hmem : ∀ q : Polynomial A,
      (AdjoinRoot.mk (curveRelationPoly f)) q ∈ Algebra.adjoin A {t} := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ ih₁ ih₂ =>
      rw [map_add]
      exact Subalgebra.add_mem _ ih₁ ih₂
    | monomial n a =>
      -- `C_mul_X_pow_eq_monomial : C a * X ^ n = monomial n a` (confirmed
      -- present in current Mathlib4, used e.g. in `Polynomial.Inductions`)
      -- — a single cheap rewrite, replacing the earlier `coeff`-level
      -- case-split proof of the same fact (that version, and a `simp`
      -- call before it, were the two heartbeat sinks that made this
      -- lemma time out; this route touches no `ite`s at all).
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, AdjoinRoot.mk_C, map_pow,
        AdjoinRoot.mk_X, ht_def]
      -- `Algebra.self_mem_adjoin_singleton` states `x ∈ Algebra.adjoin R {x}`
      -- directly, with no separate `Set.mem {x}` proof to elaborate — the
      -- previous `Algebra.subset_adjoin rfl` was making Lean unify that
      -- `rfl` against the full ambient class stack, which is what timed
      -- out.
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a)
        (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton A t) n)
  have hgen : Algebra.adjoin A {t} = (⊤ : Subalgebra A (AdjoinRoot (curveRelationPoly f))) := by
    rw [eq_top_iff]
    intro x _
    induction x using AdjoinRoot.induction_on with
    | ih q => exact hmem q
  have := finrank_le_of_monic_annihilator (k := k) (A := A)
    (B := AdjoinRoot (curveRelationPoly f)) (curveRelationPoly f) hmonic t ht hgen
  rwa [hdeg] at this

end Genus2Lean
