import Mathlib
import Genus2Lean.ZeroD.QuotOfListChainFinrankStep
import Genus2Lean.ZeroD.QuotOfListChainAdjoinTop
import Genus2Lean.ZeroD.LinearElimDegreeBound
import Genus2Lean.ZeroD.DecoupledSystemRegular

/-!
# Stages 0–3 wiring: linear-elimination generators against a literal
# `Ideal.ofList` prefix

Item 5 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, the
counterpart to `CurveRelationStageWiring.lean` for the matching-generator
stages (`Fu0`–`Fu3`, and by the same shape `Fv0`–`Fv3` once the fresh
`IsUnit`-strength hypothesis the roadmap's resolved Open Questions call
for is supplied — see `LinearElimDegreeBoundExt.lean`'s existing
per-stage re-exports of `finrank_le_of_linear_elim`, which this file's
wiring is equally usable for since the abstract statement is
shape-identical).

**What this file specializes**: `finrank_le_of_linear_elim`
(`LinearElimDegreeBound.lean`) and `finrank_le_ofList_cons`
(`QuotOfListChainFinrankStep.lean`) to the literal shape a
matching-generator takes — `g := c - X u * d` for the newly-peeled
variable `X u : Rdec p` and already-fixed `c d : Rdec p` (matching
`FuList`'s literal entries, `DecoupledSystemRegular.lean` §4, e.g.
`Fu0 = d.u1_num 0 - U0' p * d.u1_den 0`, i.e. `c := d.u1_num 0`,
`d := d.u1_den 0`, `u := U0`) — generic over the prefix `gens : List
(Rdec p)`, the newly-peeled generator symbol `u : Idx`, and the two
already-fixed coefficients `c d : Rdec p`, NOT yet plugged in against
`genList`'s own literal `FuList`/`FvList` entries (that final
substitution is later Assembly work, same split as
`CurveRelationStageWiring.lean`).

**Why `finrank_le_of_linear_elim` directly, not a fresh `AdjoinRoot`
argument**: identical reasoning to `CurveRelationStageWiring.lean`'s own
docstring — Assembly's actual target ring is a quotient of the
ALREADY-EXISTING ring `Rdec p ⧸ Ideal.ofList gens`, not a fresh
`Polynomial A ⧸ Ideal.span {G}`, so this file applies
`finrank_le_of_linear_elim`'s underlying fact directly against
`B := (Rdec p ⧸ Ideal.ofList gens) ⧸ Ideal.span {mk g}`, with
`t := mk (mk (X u))`, using `QuotOfListChainAdjoinTop.lean`'s free
`hgen` fact so only the annihilation fact `ht` needs real proof. -/

namespace Genus2Lean
namespace DecoupledSystem

open Polynomial

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- **The literal linear-elimination generator, as an element of
`Rdec p`** — matching `Fu0 = d.u1_num 0 - U0' p * d.u1_den 0`'s exact
shape (`DecoupledSystemRegular.lean` §4) but generic in which `Idx`
symbol plays the role of the newly-peeled variable (`U0`/`U1`/`V0`/`V1`)
and in the two already-fixed coefficients `c d : Rdec p` (playing the
roles of `u1_num i`/`u1_den i` etc.). -/
noncomputable def linearElimGen (c d : Rdec p) (u : Idx) : Rdec p :=
  c - MvPolynomial.X u * d

/-- **The stage-0-shape `finrank` bound, wired to a literal
`Ideal.ofList` prefix.** Given a prefix `gens`, base field `k := F p`,
already-fixed coefficients `c d : Rdec p` with `d`'s image in
`A := Rdec p ⧸ Ideal.ofList gens` a UNIT (the roadmap's own correctly-
scoped per-stage hypothesis — see `ROADMAP-monic-annihilator-degree-
uniform.md`'s "Strategy" section: bare non-vanishing of a resultant is
NOT enough to normalize to monic, only `IsUnit` is), and the
matching-generator relation `g := linearElimGen ... u` for a peeled
variable symbol `u : Idx`, the extended quotient's `finrank` is at most
the prefix quotient's (degree 1, unlike stages 8–11's degree 2).

**Why `[StrongRankCondition ...]`/`[Module.Finite (F p) ...]`/
`[Nontrivial ...]` on `A := Rdec p ⧸ Ideal.ofList gens` are hypotheses
here, not free instances**: identical reasoning to
`CurveRelationStageWiring.lean`'s own docstring — genuinely
undischargeable for an arbitrary prefix `gens`, left to the
not-yet-written final Assembly file (by induction along the peel
chain). `hd_unit : IsUnit (mk_A d)` is a FOURTH such per-stage
hypothesis specific to this shape, matching what
`LinearElimDegreeBoundExt.lean`'s `hv_den_unit` already supplies for
stages 4–7 and what stages 0–3 need equally, per the roadmap's resolved
Open Questions diagnosis (the existing `hFu*_reg`/`hv*_ext` REGULARITY
hypotheses are strictly weaker than `IsUnit` and do not supply this for
free). -/
theorem finrank_le_linearElim_ofList_cons
    (gens : List (Rdec p)) (c d : Rdec p) (u : Idx)
    [StrongRankCondition (Rdec p ⧸ Ideal.ofList gens)]
    [Module.Finite (F p) (Rdec p ⧸ Ideal.ofList gens)]
    [Nontrivial (Rdec p ⧸ Ideal.ofList gens)]
    (hd_unit : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) d)) :
    Module.finrank (F p) (Rdec p ⧸ Ideal.ofList (gens ++ [linearElimGen p c d u])) ≤
      Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens) := by
  rw [← one_mul (Module.finrank (F p) (Rdec p ⧸ Ideal.ofList gens))]
  apply finrank_le_ofList_cons
  set A := Rdec p ⧸ Ideal.ofList gens with hA_def
  set g := linearElimGen p c d u with hg_def
  set B := A ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A) with hB_def
  set cA : A := Ideal.Quotient.mk (Ideal.ofList gens) c with hcA_def
  set dA : A := Ideal.Quotient.mk (Ideal.ofList gens) d with hdA_def
  set t : B := Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) with
    ht_def
  -- `hd_unit`'s literal `mk_A d` was already folded to `dA` automatically
  -- by the `set dA := ...` line above (`set` rewrites all existing
  -- occurrences, including inside other hypotheses) — `hd_unit : IsUnit
  -- dA` already, no further rewrite needed here.
  -- `G := linearElimMonicPoly cA dA hd_unit : Polynomial A` is monic of
  -- degree 1 (`LinearElimDegreeBound.lean`'s own already-proved facts),
  -- and `aeval t (linearElimPoly cA dA) = 0` unfolds to exactly
  -- `mk_B (mk_A c) - mk_B (mk_A (X u)) * mk_B (mk_A d) = 0`, which is
  -- `mk_B (mk_A g) = 0` after unfolding `g`'s literal shape — true by
  -- construction, since `B` quotients by `Ideal.span {mk_A g}`.
  have ht : (Polynomial.aeval t) (linearElimPoly cA dA) = 0 := by
    -- `φ : Rdec p →+* B`, the composite two-step quotient map `mk_B ∘
    -- mk_A`, exactly as in `CurveRelationStageWiring.lean`.
    set φ : Rdec p →+* B :=
      (Ideal.Quotient.mk (Ideal.span
        ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))).comp
        (Ideal.Quotient.mk (Ideal.ofList gens)) with hφ_def
    have hφg : φ g = 0 := by
      show Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) g) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    -- `algebraMap A B` (what `aeval_C` produces) is literally `mk_B`
    -- applied to its `A`-argument — needed to bridge `aeval_C`'s output
    -- back to plain `Ideal.Quotient.mk` applications, exactly as
    -- `CurveRelationStageWiring.lean`'s `halgebraMap` does.
    have halgebraMap : ∀ y : A, algebraMap A B y = Ideal.Quotient.mk
        (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A)) y := fun y => rfl
    -- Unfold `aeval t (linearElimPoly cA dA) = aeval t (C cA - X * C dA)`
    -- via `map_sub`/`map_mul`/`aeval_C`/`aeval_X` to
    -- `algebraMap A B cA - t * algebraMap A B dA`, then bridge
    -- `algebraMap A B` back to `Ideal.Quotient.mk` via `halgebraMap` so
    -- the goal reads entirely in terms of plain quotient maps and `φ`.
    rw [linearElimPoly, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.aeval_C, halgebraMap, halgebraMap]
    -- Goal now: `mk_B (mk_A c) - t * mk_B (mk_A d) = 0`. Show this is
    -- `φ g` (which is `0` by `hφg`) via a `show`-based defeq unfolding
    -- of `g`, exactly the technique `CurveRelationStageWiring.lean` uses
    -- to avoid the "motive is not type correct" failure a
    -- `rw [hg_def, ...]` would trigger (since `g` also appears inside
    -- `B`'s own type).
    have hφg' : φ g = Ideal.Quotient.mk
          (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) c) -
        t * Ideal.Quotient.mk
          (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) d) := by
      show Ideal.Quotient.mk (Ideal.span
          ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
          (Ideal.Quotient.mk (Ideal.ofList gens) (c - MvPolynomial.X u * d)) =
        Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) c) -
          Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) (MvPolynomial.X u)) *
          Ideal.Quotient.mk (Ideal.span
            ({Ideal.Quotient.mk (Ideal.ofList gens) g} : Set A))
            (Ideal.Quotient.mk (Ideal.ofList gens) d)
      simp only [map_sub, map_mul]
    rw [← hφg', hφg]
  have hgen : Algebra.adjoin A ({t} : Set B) = (⊤ : Subalgebra A B) :=
    adjoin_singleton_eq_top_of_quotient _ t
  rw [one_mul]
  exact finrank_le_of_linear_elim (k := F p) cA dA hd_unit t ht hgen

end DecoupledSystem
end Genus2Lean
