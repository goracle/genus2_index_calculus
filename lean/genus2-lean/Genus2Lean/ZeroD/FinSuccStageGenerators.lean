import Mathlib
import Genus2Lean.ZeroD.FinSuccSplitPolynomialEquiv
import Genus2Lean.ZeroD.LinearElimDegreeBound
import Genus2Lean.ZeroD.CurveRelationsDegreeBound

/-!
# Item (d) step 3, generic half: `Fin`-indexed stage generators and their
# `finSuccSplitQuotientAlgEquiv` images

`ROADMAP-monic-annihilator-degree-uniform.md`'s item (d) step 3 needs,
for each of the 12 peel-chain stages, a generator `g : MvPolynomial
(Fin (n+1)) K` together with its monic image `G : Polynomial A` under
`finSuccSplitQuotientAlgEquiv n gens` — exactly the data
`finrank_le_finSucc_peel_chain`'s `hstep` argument (`FinSuccPeelChainFold
.lean`) must produce at each step. This file supplies that data
GENERICALLY, for the two stage shapes the roadmap's peel-chain table
identifies (linear-elimination stages 0–7, curve-relation stages 8–11),
with zero `Idx`/`Rdec p`/`theData` content — the actual `Idx`-specific
wiring (identifying `q₁`/`q₂`/`f` below with `genList`'s literal
`u1_num`/`u1_den`/etc. or `curveF`, and the peeled variable with a
specific `wa1`/`U0`/etc. under `idxEquivFin`) is separate, later work.

**Linear-elimination shape.** `genList`'s matching generators are, before
peeling, `c − X u * d` for `c, d` in the algebra already built from
earlier stages and `u` the newly-peeled variable — literally `linearElimGen`
(`LinearElimStageWiring.lean`)'s shape, restated here at `Fin (n+1)`/`X 0`
instead of `Rdec p`/`X u`. Concretely: given `q₁ q₂ : MvPolynomial (Fin n)
K` (playing `c`/`d` BEFORE quotienting), the `Fin`-indexed generator
`finSuccLinearElimGen q₁ q₂ := rename Fin.succ q₁ - X 0 * rename Fin.succ q₂`
has `finSuccSplitQuotientAlgEquiv`-image exactly `linearElimPoly (mk q₁)
(mk q₂) : Polynomial A` — a direct computation from
`finSuccSplitQuotientRingEquiv_apply_rename_succ`/`_apply_X_zero` plus
`finSuccSplitQuotientAlgEquiv` being a ring hom (so it distributes over
`-`/`*`). Given additionally `IsUnit (mk q₂)` (the per-stage `hd_unit`-style
hypothesis `GenListFinrankAssembly.lean`'s `PeelChainFinrankHyp` already
names), `linearElimPoly (mk q₁) (mk q₂)`'s own MONIC rescaling
`linearElimMonicPoly` (`LinearElimDegreeBound.lean`) is what actually gets
handed to `hstep`'s `G` slot — this file supplies both the raw image
computation (`finSuccLinearElimGen_image`) and the fully-packaged `hstep`
witness (`finSuccLinearElimGen_hstep_data`) so the `Idx`-wiring file can
call the latter directly without re-deriving the monic-rescaling step
each time.

**Curve-relation shape.** `genList`'s curve relations are `w'² − f` for
the newly-peeled variable `w` and an already-fixed `f` (in the algebra
built so far) — `curveRelationGen`'s shape (`CurveRelationStageWiring
.lean`), restated at `Fin (n+1)`/`X 0`. Concretely: given `q : MvPolynomial
(Fin n) K` (playing `f` before quotienting), `finSuccCurveRelationGen q :=
X 0 ^ 2 - rename Fin.succ q` has image exactly `curveRelationPoly (mk q) :
Polynomial A` — already monic (`curveRelationPoly_monic`, no unit
hypothesis needed), so the packaged `hstep` witness here
(`finSuccCurveRelationGen_hstep_data`) needs only the non-unit hypothesis
`hg_ne`, matching `PeelChainFinrankHyp`'s `hgu_curveA1`-style fields
exactly. -/

namespace Genus2Lean

open Polynomial MvPolynomial

variable {K : Type*} [Field K]

/-! ## Linear-elimination stages (0–7) -/

/-- The `Fin`-indexed linear-elimination generator, matching
`linearElimGen`'s shape at the newly-peeled variable `X 0 : MvPolynomial
(Fin (n+1)) K`. -/
noncomputable def finSuccLinearElimGen (n : ℕ) (q₁ q₂ : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.rename Fin.succ q₁ - MvPolynomial.X 0 * MvPolynomial.rename Fin.succ q₂

/-- A non-unit in the split quotient forces the base quotient to be nontrivial. -/
private theorem finSuccQuotient_nontrivial_of_not_unit
    (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (n + 1)) K)
    (hg_ne : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g)) :
    Nontrivial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hsub
  letI : Subsingleton (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) := hsub
  letI : Subsingleton
      (MvPolynomial (Fin (n + 1)) K ⧸
        Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) :=
    ⟨fun x y => (finSuccSplitQuotientAlgEquiv n gens).injective
      (Subsingleton.elim _ _)⟩
  apply hg_ne
  have hx : Ideal.Quotient.mk
      (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g = 1 :=
    Subsingleton.elim _ _
  rw [hx]
  exact isUnit_one

/-- **The image computation**: `finSuccLinearElimGen q₁ q₂`'s image under
`finSuccSplitQuotientAlgEquiv` is exactly `linearElimPoly (mk q₁) (mk q₂)`
— immediate from the two already-proved `apply` lemmas
(`finSuccSplitQuotientRingEquiv_apply_rename_succ`/`_apply_X_zero`) plus
`finSuccSplitQuotientAlgEquiv`'s ring-hom action on `-`/`*` (via `map_sub`/
`map_mul`, applied to its underlying `RingEquiv`). -/
theorem finSuccLinearElimGen_image (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (q₁ q₂ : MvPolynomial (Fin n) K) :
    finSuccSplitQuotientAlgEquiv n gens
      (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (finSuccLinearElimGen n q₁ q₂)) =
      linearElimPoly (Ideal.Quotient.mk (Ideal.ofList gens) q₁)
        (Ideal.Quotient.mk (Ideal.ofList gens) q₂) := by
  unfold finSuccLinearElimGen linearElimPoly
  change finSuccSplitQuotientRingEquiv n gens
      (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (MvPolynomial.rename Fin.succ q₁ - MvPolynomial.X 0 * MvPolynomial.rename Fin.succ q₂)) =
    Polynomial.C (Ideal.Quotient.mk (Ideal.ofList gens) q₁) -
      Polynomial.X * Polynomial.C (Ideal.Quotient.mk (Ideal.ofList gens) q₂)
  simp only [map_sub, map_mul,
    finSuccSplitQuotientRingEquiv_apply_rename_succ,
    finSuccSplitQuotientRingEquiv_apply_X_zero]

/-- **A chosen preimage of the rescaled coefficient `hd.unit⁻¹ * mk q₁`.**
Named so downstream statements (the eventual per-stage `hgu_Fu0`-style
hypotheses) can refer to it by name rather than inlining
`Classical.choose`. No claim of canonicity — `Ideal.Quotient.mk`
surjectivity gives existence only, and any preimage is equally good here
since only its image under `mk` (fixed by `finSuccLinearElimCoeff_spec`
below) is ever used downstream. -/
noncomputable def finSuccLinearElimCoeff (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (q₁ q₂ : MvPolynomial (Fin n) K) (hd_unit : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) q₂)) :
    MvPolynomial (Fin n) K :=
  (Ideal.Quotient.mk_surjective (I := Ideal.ofList gens)
    ((↑(hd_unit.unit⁻¹) : (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)) *
      Ideal.Quotient.mk (Ideal.ofList gens) q₁)).choose

/-- **The defining property of `finSuccLinearElimCoeff`**: its image under
`mk` is exactly the rescaled coefficient `hd.unit⁻¹ * mk q₁` — immediate
from `Classical.choose_spec`, packaged under a stable name so later files
never need to unfold `Classical.choose` directly. -/
theorem finSuccLinearElimCoeff_spec (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (q₁ q₂ : MvPolynomial (Fin n) K) (hd_unit : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) q₂)) :
    Ideal.Quotient.mk (Ideal.ofList gens) (finSuccLinearElimCoeff n gens q₁ q₂ hd_unit) =
      ((↑(hd_unit.unit⁻¹) : (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)) *
        Ideal.Quotient.mk (Ideal.ofList gens) q₁) :=
  (Ideal.Quotient.mk_surjective (I := Ideal.ofList gens)
    ((↑(hd_unit.unit⁻¹) : (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)) *
      Ideal.Quotient.mk (Ideal.ofList gens) q₁)).choose_spec

/-- **The `Fin`-indexed generator whose image is ALREADY the monic
rescaling** — `X 0 - rename Fin.succ (finSuccLinearElimCoeff ...)`, unlike
`finSuccLinearElimGen` (whose image is the raw non-monic `linearElimPoly`;
see `finSuccLinearElimGen_hstep_data`'s docstring for why that generator
cannot supply `hstep`'s literal-equality `hg` field). This is the
generator that actually gets used in the peel chain at this stage — it
generates the SAME ideal as `finSuccLinearElimGen n q₁ q₂` (both are
degree-1-in-`X 0` relations pinning `X 0` to the same value in the
quotient, `linearElimPoly_span_eq`'s underlying fact one level up), so
using this rescaled form instead of the raw one changes nothing about
which ring the peel chain actually builds. -/
noncomputable def finSuccLinearElimGenMonic (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (q₁ q₂ : MvPolynomial (Fin n) K) (hd_unit : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) q₂)) :
    MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.X 0 - MvPolynomial.rename Fin.succ (finSuccLinearElimCoeff n gens q₁ q₂ hd_unit)

/-- **The packaged `hstep` witness for a linear-elimination stage.** Given
`q₁ q₂` (the un-quotiented "numerator"/"denominator" at this stage) and
`hd_unit : IsUnit (mk q₂)`, produces the `⟨g, G, hG, hg_ne, hg⟩` bundle
`finrank_le_finSucc_peel_chain`'s `hstep` needs at this step, with
`g := finSuccLinearElimGenMonic ...` and `G := linearElimMonicPoly (mk q₁)
(mk q₂) hd_unit` — monic of degree 1, matching the roadmap's `d = 1`
multiplier for stages 0–7.

**Why `g` is `finSuccLinearElimGenMonic`, not `finSuccLinearElimGen`.**
`finSuccLinearElimGen n q₁ q₂`'s image under `finSuccSplitQuotientAlgEquiv`
is `linearElimPoly (mk q₁) (mk q₂)` (`finSuccLinearElimGen_image`) — the
RAW, non-monic polynomial. `linearElimPoly c d = (-(C d)) *
linearElimMonicPoly c d hd` is a genuine element-level identity in
`Polynomial A` (`linearElimPoly_eq_unit_mul`), but that only shows the
image is a UNIT MULTIPLE of the monic target, not literally equal to it —
and `hstep`'s `hg` field demands literal equality. `finSuccLinearElimGenMonic`
sidesteps this by construction: its image is `X - C (mk (finSuccLinearElimCoeff
...)) = X - C (hd_unit.unit⁻¹ * mk q₁) = linearElimMonicPoly (mk q₁) (mk q₂)
hd_unit` directly, by `finSuccLinearElimCoeff_spec` and
`linearElimMonicPoly`'s own definition — an honest computation, not a
further ideal-theoretic argument. -/
theorem finSuccLinearElimGen_hstep_data (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (q₁ q₂ : MvPolynomial (Fin n) K) (hd_unit : IsUnit (Ideal.Quotient.mk (Ideal.ofList gens) q₂))
    (hg_ne : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
      (finSuccLinearElimGenMonic n gens q₁ q₂ hd_unit))) :
    ∃ (g : MvPolynomial (Fin (n + 1)) K)
      (G : Polynomial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)),
      G.Monic ∧
      (¬ IsUnit (Ideal.Quotient.mk
        (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g)) ∧
      finSuccSplitQuotientAlgEquiv n gens
        (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g) = G := by
  letI : Nontrivial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) :=
    finSuccQuotient_nontrivial_of_not_unit n gens
      (finSuccLinearElimGenMonic n gens q₁ q₂ hd_unit) hg_ne
  refine ⟨finSuccLinearElimGenMonic n gens q₁ q₂ hd_unit,
    linearElimMonicPoly (Ideal.Quotient.mk (Ideal.ofList gens) q₁)
      (Ideal.Quotient.mk (Ideal.ofList gens) q₂) hd_unit,
    linearElimMonicPoly_monic _ _ hd_unit, hg_ne, ?_⟩
  unfold finSuccLinearElimGenMonic
  show finSuccSplitQuotientRingEquiv n gens
      (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (MvPolynomial.X 0 - MvPolynomial.rename Fin.succ
          (finSuccLinearElimCoeff n gens q₁ q₂ hd_unit))) =
    linearElimMonicPoly (Ideal.Quotient.mk (Ideal.ofList gens) q₁)
      (Ideal.Quotient.mk (Ideal.ofList gens) q₂) hd_unit
  simp only [map_sub, finSuccSplitQuotientRingEquiv_apply_X_zero,
    finSuccSplitQuotientRingEquiv_apply_rename_succ, finSuccLinearElimCoeff_spec]
  rfl

/-! ## Curve-relation stages (8–11) -/

/-- The `Fin`-indexed curve-relation generator, matching `curveRelationGen`'s
shape at the newly-peeled variable `X 0`. -/
noncomputable def finSuccCurveRelationGen (n : ℕ) (q : MvPolynomial (Fin n) K) :
    MvPolynomial (Fin (n + 1)) K :=
  MvPolynomial.X 0 ^ 2 - MvPolynomial.rename Fin.succ q

/-- **The image computation**: `finSuccCurveRelationGen q`'s image under
`finSuccSplitQuotientAlgEquiv` is exactly `curveRelationPoly (mk q)` —
already monic, no unit hypothesis needed. -/
theorem finSuccCurveRelationGen_image (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (q : MvPolynomial (Fin n) K) :
    finSuccSplitQuotientAlgEquiv n gens
      (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (finSuccCurveRelationGen n q)) =
      curveRelationPoly (Ideal.Quotient.mk (Ideal.ofList gens) q) := by
  unfold finSuccCurveRelationGen curveRelationPoly
  change finSuccSplitQuotientRingEquiv n gens
      (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ)))
        (MvPolynomial.X 0 ^ 2 - MvPolynomial.rename Fin.succ q)) =
    Polynomial.X ^ 2 - Polynomial.C (Ideal.Quotient.mk (Ideal.ofList gens) q)
  simp only [map_sub, map_pow, finSuccSplitQuotientRingEquiv_apply_X_zero,
    finSuccSplitQuotientRingEquiv_apply_rename_succ]

/-- **The packaged `hstep` witness for a curve-relation stage.** Given
`q` (the un-quotiented curve value) and `hg_ne`, produces the
`⟨g, G, hG, hg_ne, hg⟩` bundle directly — no unit hypothesis needed,
matching stages 8–11's already-monic shape (`d = 2`). -/
theorem finSuccCurveRelationGen_hstep_data (n : ℕ) (gens : List (MvPolynomial (Fin n) K))
    (q : MvPolynomial (Fin n) K)
    (hg_ne : ¬ IsUnit (Ideal.Quotient.mk
      (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) (finSuccCurveRelationGen n q))) :
    ∃ (g : MvPolynomial (Fin (n + 1)) K)
      (G : Polynomial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens)),
      G.Monic ∧
      (¬ IsUnit (Ideal.Quotient.mk
        (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g)) ∧
      finSuccSplitQuotientAlgEquiv n gens
        (Ideal.Quotient.mk (Ideal.ofList (gens.map (MvPolynomial.rename Fin.succ))) g) = G := by
  letI : Nontrivial (MvPolynomial (Fin n) K ⧸ Ideal.ofList gens) :=
    finSuccQuotient_nontrivial_of_not_unit n gens
      (finSuccCurveRelationGen n q) hg_ne
  exact ⟨finSuccCurveRelationGen n q, curveRelationPoly (Ideal.Quotient.mk (Ideal.ofList gens) q),
    curveRelationPoly_monic _, hg_ne, finSuccCurveRelationGen_image n gens q⟩

end Genus2Lean
