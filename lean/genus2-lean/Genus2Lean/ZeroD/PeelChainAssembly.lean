import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationMumford
import Genus2Lean.DecoupledSystemRegular

/-!
# `regularSeq_of_peel_chain`: the actual 12-stage assembly

**Downstream of `DecoupledSystemRegular.lean`, split out into its own file
per Claire's request** (the parent file was getting cumbersome). Nothing
in `DecoupledSystemRegular.lean` is restated here — this file only
`import`s it and works against its existing `genList`/`theData`/
`CrossNondegenerate`/`denRegular`/`regular_of_linear_elim`/
`regular_of_peeled_leadingCoeff`/`isSMulRegular_of_mul_eq_of_isSMulRegular`/
`curveCoeffRegular`/`peelEquiv`/`peelEquivGen` etc.

**Supersedes `04_design_notes.md`/`05_notes.md`/`06_final_design.md`.**
Those three notes worked through several false starts (documented in
`ROADMAP-peel-chain-assembly.md`, kept alongside this file) before landing
on the actual mechanism used below. In particular:

- `06_final_design.md`'s "item 4" (claiming `CrossNondegenerate`'s fields
  are stated against the wrong ideal, "mod a single generator" instead of
  "mod the full prefix") is a FALSE ALARM, not acted on here —
  `RingTheory.Sequence.isRegular_cons_iff'` only ever needs regularity mod
  the SINGLE most-recently-adjoined generator at each step (the growing
  prefix is accumulated automatically by nesting `QuotSMulTop`, never
  supplied as a single up-front hypothesis), and `CrossNondegenerate`'s
  `hu0`/`hu1`/`hv0`/`hv1` fields are already stated in exactly that
  single-step shape. See `ROADMAP-peel-chain-assembly.md` for the full
  re-derivation.
- `06`'s proposed `regular_of_disjoint_extension_list` (sorry #2 there) is
  NOT created — turned out to be unnecessary. The "does the next stage's
  denominator survive the previous stage's quotienting" question is
  answered by Layer 1
  (`Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular`) applied
  degree-0 to a CONSTANT, not by any variable-disjointness/flat-base-change
  argument — `regular_of_disjoint_extension` is not called anywhere in
  this file's assembly.

## Structure

Three named sorries, ordered easiest-first per project convention:

1. `isSMulRegular_C_const_of_isSMulRegular` (proved, no `sorry` — pure
   restatement of `Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular`
   at a degree-0 leading coefficient) plus `isSMulRegular_den_of_second_peel`
   (`sorry`-backed): the scoped induction step stages 2/3/6/7 need —
   "the next stage's own denominator (`u1_den 1`/etc.) survives the
   TWO already-imposed same-target-family generators" — proved by
   re-running stages 0-1's own two-step argument one variable-peel down,
   NOT by any generic "constant survives an arbitrary list" principle
   (that generic claim is false — see §1's docstring for the retracted
   first draft and why).
2. `isSMulRegular_bridge_prefix` (proved, no `sorry`) — identifies
   `Rdec p ⧸ Ideal.ofList (...)` (an `Rdec p`-level fact, the shape
   `isRegular_cons_iff'` wants at each of §3's 12 stages) with the
   `MvPolynomial (Option τ) (F p)`-level statement `regular_of_linear_elim`/
   `regular_of_peeled_leadingCoeff` actually CONCLUDE, for `τ := {v ≠ x}`
   the peeled variable's complement. Built from
   `03_general_transport.lean`'s `isSMulRegular_of_ringEquiv_of_mapsTo`
   (already a complete, `sorry`-free proof) applied to the single ring
   equiv `renameEquiv (F p) (optionSplit x) : Rdec p ≃+* MvPolynomial
   (Option τ) (F p)` — one application, no further bookkeeping needed.
3. `regularSeq_of_peel_chain` itself — the 12-fold `isRegular_cons_iff'`
   chain. Purely mechanical once 1-2 are available, but long; left as its
   own `sorry` so 1-2 can be checked independently first.
-/

namespace Genus2Lean
namespace DecoupledSystem

open MvPolynomial
open Idx
open TheDataDerivation

variable (p : ℕ) [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

/-! ## §0. Generic peeling/bridge infrastructure

Pulled to the TOP of the file (ahead of §1) because §1's own proof needs
it a second time, one level down inside `τ`'s ring — see
`isSMulRegular_den_of_second_peel` below. Not tied to `Idx`/`F p`
anywhere; `σ`/`R` are fully generic. -/

/-- The `Option`-splitting equivalence `peelEquivGen`/`peelEquiv` build
internally, pulled out as its own named `def`, verbatim
`01_bridge.lean`'s `optionSplit`. -/
noncomputable def optionSplit {σ : Type*} [DecidableEq σ] (x : σ) :
    σ ≃ Option {v : σ // v ≠ x} :=
  ((Equiv.optionSubtype x).symm (Equiv.refl {v : σ // v ≠ x})).val.symm

/-- **Fully generic bridge lemma**, over an arbitrary `DecidableEq`
variable type `σ` and commutative ring `R`. Relates `IsSMulRegular` in
`MvPolynomial σ R` (quotiented by the `σ`-level image of a `τ`-side list
`gens'`/element `g`, `τ := {v : σ // v ≠ x}`, under `(renameEquiv R
(optionSplit x)).symm ∘ rename some`) to the SAME fact stated one level
"lower," directly in `MvPolynomial (Option τ) R` (quotiented by
`Ideal.ofList (gens'.map (rename some))`) — exactly
`regular_of_linear_elim`'s/`regular_of_peeled_leadingCoeff`'s own
hypothesis/conclusion shape.

**Proof, actually carried out (not `sorry`) via ONE application of
`03_general_transport.lean`'s `isSMulRegular_of_ringEquiv_of_mapsTo`**,
using `e := (renameEquiv R (optionSplit x)).toRingEquiv : MvPolynomial σ
R ≃+* MvPolynomial (Option τ) R` (a genuine ring equiv, `renameEquiv`
built from the ring isomorphism `optionSplit x : σ ≃ Option τ`). The
ideal-matching hypothesis `Ideal.map e I = J` follows from
`Ideal.map_ofList` + `List.map_map` + pointwise `e (e.symm (rename some
q)) = rename some q` (`e.apply_symm_apply`) — `I`'s generating list,
pushed forward through `e`, collapses back to `J`'s generating list
exactly, since each of `I`'s generators was BUILT as `e.symm` applied to
one of `J`'s.

**Instantiated TWICE in this file**: once at `σ := Idx`, `R := F p` (§2's
`isSMulRegular_bridge_prefix`, the outer 12-stage assembly's own bridge),
and once at `σ := τ := {v : Idx // v ≠ U1}` (resp. `V1`), `R := F p`
(§1's `isSMulRegular_den_of_second_peel`, one variable-peel down) — the
whole point of stating it generically here rather than only at `σ :=
Idx` as the original draft did. -/
theorem isSMulRegular_bridge_prefix_gen {σ : Type*} [DecidableEq σ] (R : Type*) [CommRing R]
    (x : σ) (gens' : List (MvPolynomial {v : σ // v ≠ x} R))
    (g : MvPolynomial {v : σ // v ≠ x} R) :
    IsSMulRegular
      (MvPolynomial σ R ⧸ Ideal.ofList (gens'.map (fun q =>
        (MvPolynomial.renameEquiv R (optionSplit x)).symm (MvPolynomial.rename some q))))
      (Ideal.Quotient.mk _
        ((MvPolynomial.renameEquiv R (optionSplit x)).symm (MvPolynomial.rename some g)))
    ↔
    IsSMulRegular
      (MvPolynomial (Option {v : σ // v ≠ x}) R ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk _ (MvPolynomial.rename some g)) := by
  set e : MvPolynomial σ R ≃+* MvPolynomial (Option {v : σ // v ≠ x}) R :=
    (MvPolynomial.renameEquiv R (optionSplit x)).toRingEquiv with he_def
  set I : Ideal (MvPolynomial σ R) :=
    Ideal.ofList (gens'.map (fun q => e.symm (MvPolynomial.rename some q))) with hI_def
  set J : Ideal (MvPolynomial (Option {v : σ // v ≠ x}) R) :=
    Ideal.ofList (gens'.map (MvPolynomial.rename some)) with hJ_def
  have hIJ : Ideal.map (e : MvPolynomial σ R →+* MvPolynomial (Option {v : σ // v ≠ x}) R) I = J := by
    rw [hI_def, hJ_def, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    show e (e.symm (MvPolynomial.rename some q)) = MvPolynomial.rename some q
    exact e.apply_symm_apply _
  have hrs : e (e.symm (MvPolynomial.rename some g)) = MvPolynomial.rename some g :=
    e.apply_symm_apply _
  exact isSMulRegular_of_ringEquiv_of_mapsTo e I J hIJ
    (e.symm (MvPolynomial.rename some g)) (MvPolynomial.rename some g) hrs

/-! ## §1. The induction helper (sorry #1, easiest)

**What this lemma is NOT.** A first draft of this section tried to state
a fully generic "`d` regular in its own ring survives quotienting by an
ARBITRARY list `gens'`" fact. That is FALSE as stated — any nonzero
element of a domain can become a zero-divisor (or even `0`) after
quotienting by an unrelated ideal (e.g. `d = 2 : ℤ` survives `ℤ ⧸ (3)`
but not `ℤ ⧸ (2)`) — `gens'` being disjoint from `d`'s variables is not
enough either (see `ROADMAP-peel-chain-assembly.md`'s hand-worked
counterexample discussion). Retracted; replaced by the scoped statement
below, which is the actual fact stage 2/6 (`Fu2`/`Fv2`) need and can
actually prove.

**What this lemma IS.** `gens'` at every use site below is not an
arbitrary list — it is always exactly TWO generators, each LINEAR in a
SINGLE other variable (`U0`, for the `Fu2` stage) with `IsSMulRegular`
leading coefficient, i.e. each of the SAME shape `regular_of_linear_elim`
itself consumes. So "`d` (e.g. `u1_den 1`, not mentioning `U0` at all)
survives quotienting by `[Fu0, Fu1]`" is answered by peeling `U0` OUT of
`d`'s own home ring FIRST (a second, nested application of
`regular_of_linear_elim`'s own machinery, one level down), during which
`d`'s image is a bare `Polynomial.C`-constant (`natDegree 0`) throughout
— Layer 1 applied to a degree-0 leading coefficient, twice (once per
`Fu0`/`Fu1`), is exactly what closes each step; NOT a generic
"disjoint-variables-survive" principle. -/

/-- **Layer 1, specialized to a constant.** If `d : A` is
`IsSMulRegular`, so is its image `Polynomial.C d`, viewed as an element
of `Polynomial A` (leading coefficient `d` itself, `natDegree 0`). Not a
new lemma — `Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular`
applied with `f := Polynomial.C d` and `Polynomial.leadingCoeff_C`. Named
separately purely for reuse: every use of `regular_of_linear_elim`/
`regular_of_peeled_leadingCoeff` below where the tracked element is a
CONSTANT with respect to the variable currently being peeled cites this,
rather than re-deriving `leadingCoeff_C` inline each time. -/
theorem isSMulRegular_C_const_of_isSMulRegular {A : Type*} [CommRing A] {d : A}
    (hd : IsSMulRegular A d) :
    IsSMulRegular (Polynomial A) (Polynomial.C d) :=
  Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular
    (f := (Polynomial.C d : Polynomial A)) (by rwa [Polynomial.leadingCoeff_C])

/-- **The actual induction helper needed for stages 2/3 and 6/7** (`Fu2`
through `Fv3`). Precise scoped statement: work inside `τ := {v : Idx // v
≠ U1}` (resp. `V1`, `Fv2`), i.e. AFTER peeling `U1` but before any
further quotienting. `[Fu0', Fu1']` (the `τ`-side reinterpretations of
`Fu0, Fu1`, which exist and are unique by `u1_indep 0`/`u2_indep 0` +
`MvPolynomial.exists_rename_eq_of_vars_subset_range`, since neither
mentions `U1`) are BOTH linear in `U0 : τ` — `Fu0' = rename (some-inverse
of u1_num 0) - X U0 * rename (... u1_den 0)`-shaped, ditto `Fu1'` with
`u2_num 0`/`u2_den 0` — exactly `regular_of_linear_elim`'s own hypothesis
shape, one level down, peeling `U0` out of `τ`'s ring via `τ' := {v : τ
// v ≠ U0} = {v : Idx // v ≠ U1 ∧ v ≠ U0}`. `d'` (the `τ`-side
reinterpretation of `u1_den 1`, likewise existing since `u1_indep 1`
gives `u1_den 1` avoids `U1` too, and separately avoids `U0` by the same
field at a different index — `u1_indep`'s target Finset `{wa1,wa2,a1,a2}`
never contains `U0` either) is a further `τ'`-side constant throughout
this peel, closed by TWO applications of
`isSMulRegular_C_const_of_isSMulRegular` (once for `Fu0'`, via
`regular_of_linear_elim`'s Layer 2 chain, once more for `Fu1'` via
`isSMulRegular_of_mul_eq_of_isSMulRegular`'s own resultant identity,
`hcross.hu0` transported to `τ`'s ring the same way it's used at the
outer level in §3 stage 1) — literally the SAME two-stage argument that
closes `genList`'s stages 0-1, run one variable-peel down. Not proved
here — needs the `τ`-side reinterpretations named explicitly via
`Classical.choice`/`MvPolynomial.exists_rename_eq_of_vars_subset_range`'s
witnesses threaded through, which is mechanical but long; left as a
`sorry` scoped to exactly this one step (no new mathematics beyond
"stages 0-1's own argument, again, one level down"). -/
theorem isSMulRegular_den_of_second_peel
    (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hndA : Nondegenerate p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA)
    (hndB : Nondegenerate p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB)
    (hcross : CrossNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :
    let τ := {v : Idx // v ≠ U1}
    let d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
    ∀ Fu0' Fu1' d' : MvPolynomial τ (F p),
      MvPolynomial.rename (Subtype.val : τ → Idx) Fu0' = d.u1_num 0 - U0' p * d.u1_den 0 →
      MvPolynomial.rename (Subtype.val : τ → Idx) Fu1' = d.u2_num 0 - U0' p * d.u2_den 0 →
      MvPolynomial.rename (Subtype.val : τ → Idx) d' = d.u1_den 1 →
      IsSMulRegular
        (MvPolynomial τ (F p) ⧸ Ideal.ofList [Fu0', Fu1'])
        (Ideal.Quotient.mk (Ideal.ofList [Fu0', Fu1']) d') := by
  classical
  intro Fu0' Fu1' d' hFu0' hFu1' hd'
  set d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB with hd_def
  -- `x0 : τ` is `U0` viewed inside `τ := {v : Idx // v ≠ U1}` (valid since
  -- `U0 ≠ U1`). `τ' := {v : τ // v ≠ x0}` is the "peel `U0` out of `τ`'s
  -- ring" target -- `regular_of_linear_elim`'s own `τ` argument
  -- instantiated one level down (`R := F p`).
  set x0 : τ := (⟨U0, by decide⟩ : τ) with hx0_def
  set τ' : Type := {v : τ // v ≠ x0} with hτ'_def
  -- **Step A: every one of `d.u1_num 0`, `d.u1_den 0`, `d.u2_num 0`,
  -- `d.u2_den 0`, `d.u1_den 1` avoids BOTH `U0` and `U1`** (`u1_indep`/
  -- `u2_indep`'s target Finset `{wa1,wa2,a1,a2}`/`{wb1,wb2,b1,b2}` never
  -- contains `U0` or `U1`), hence each has a canonical `τ'`-side
  -- representative via `exists_rename_eq_of_vars_subset_range` applied
  -- TWICE (once to land in `τ`, avoiding `U1`; once more to land in `τ'`,
  -- avoiding `x0` too) -- equivalently, applied ONCE directly with
  -- `f := (Subtype.val ∘ Subtype.val : τ' → Idx)`, which is injective
  -- (composition of injective `Subtype.val`s) with range exactly
  -- `{v : Idx // v ≠ U0 ∧ v ≠ U1}` as a set, containing all of
  -- `{wa1,wa2,a1,a2}`.
  have hf_inj : Function.Injective (fun v : τ' => (v.1.1 : Idx)) := by
    intro v w hvw
    apply Subtype.ext; apply Subtype.ext
    exact hvw
  have hu1num0_range : (↑(d.u1_num 0).vars : Set Idx) ⊆ Set.range (fun v : τ' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := d.u1_indep 0 v (Finset.mem_union_left _ hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by simpa [hx0_def] using hne0⟩, rfl⟩
  have hu1den0_range : (↑(d.u1_den 0).vars : Set Idx) ⊆ Set.range (fun v : τ' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := d.u1_indep 0 v (Finset.mem_union_right _ hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by simpa [hx0_def] using hne0⟩, rfl⟩
  have hu2num0_range : (↑(d.u2_num 0).vars : Set Idx) ⊆ Set.range (fun v : τ' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := d.u2_indep 0 v (Finset.mem_union_left _ hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by simpa [hx0_def] using hne0⟩, rfl⟩
  have hu2den0_range : (↑(d.u2_den 0).vars : Set Idx) ⊆ Set.range (fun v : τ' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := d.u2_indep 0 v (Finset.mem_union_right _ hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by simpa [hx0_def] using hne0⟩, rfl⟩
  have hu1den1_range : (↑(d.u1_den 1).vars : Set Idx) ⊆ Set.range (fun v : τ' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := d.u1_indep 1 v (Finset.mem_union_right _ hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by simpa [hx0_def] using hne0⟩, rfl⟩
  obtain ⟨c0'', hc0''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.u1_num 0) (fun v : τ' => (v.1.1 : Idx)) hf_inj hu1num0_range
  obtain ⟨d0'', hd0''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.u1_den 0) (fun v : τ' => (v.1.1 : Idx)) hf_inj hu1den0_range
  obtain ⟨c1'', hc1''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.u2_num 0) (fun v : τ' => (v.1.1 : Idx)) hf_inj hu2num0_range
  obtain ⟨d1'', hd1''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.u2_den 0) (fun v : τ' => (v.1.1 : Idx)) hf_inj hu2den0_range
  obtain ⟨d1den'', hd1den''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.u1_den 1) (fun v : τ' => (v.1.1 : Idx)) hf_inj hu1den1_range
  -- **Step B: `Fu0' = rename Subtype.val (c0'' - X x0 * d0'')` and
  -- likewise `Fu1'`, `d' = rename Subtype.val d1den''`, all as `τ`-level
  -- equations** -- obtained by applying `rename (Subtype.val : τ → Idx)`
  -- (injective) to both sides and matching against `hFu0'`/`hFu1'`/`hd'`
  -- plus `hc0''`/`hd0''`/`hc1''`/`hd1''`/`hd1den''` (each rewritten
  -- through the two-step renaming composition `rename (Subtype.val : τ →
  -- Idx) ∘ rename (Subtype.val : τ' → τ) = rename ((Subtype.val : τ' →
  -- Idx))`, via `MvPolynomial.rename_rename`).
  have hval_inj : Function.Injective (Subtype.val : τ → Idx) := Subtype.val_injective
  have hrename_inj : Function.Injective
      (MvPolynomial.rename (Subtype.val : τ → Idx) : MvPolynomial τ (F p) → Rdec p) :=
    MvPolynomial.rename_injective _ hval_inj
  have hFu0'_eq : Fu0' = MvPolynomial.rename (Subtype.val : τ' → τ) c0'' -
      MvPolynomial.X x0 * MvPolynomial.rename (Subtype.val : τ' → τ) d0'' := by
    apply hrename_inj
    rw [hFu0', map_sub, map_mul, MvPolynomial.rename_X]
    rw [MvPolynomial.rename_rename] at hc0'' hd0''
    rw [show (Subtype.val : τ → Idx) x0 = U0 from rfl, hc0'', hd0'']
  have hFu1'_eq : Fu1' = MvPolynomial.rename (Subtype.val : τ' → τ) c1'' -
      MvPolynomial.X x0 * MvPolynomial.rename (Subtype.val : τ' → τ) d1'' := by
    apply hrename_inj
    rw [hFu1', map_sub, map_mul, MvPolynomial.rename_X]
    rw [MvPolynomial.rename_rename] at hc1'' hd1''
    rw [show (Subtype.val : τ → Idx) x0 = U0 from rfl, hc1'', hd1'']
  have hd'_eq : d' = MvPolynomial.rename (Subtype.val : τ' → τ) d1den'' := by
    apply hrename_inj
    rw [hd']
    rw [MvPolynomial.rename_rename] at hd1den''
    exact hd1den''
  -- **Step C: `d0'' ≠ 0` and `d1'' ≠ 0` in the domain `MvPolynomial τ'
  -- (F p)`** (renaming is injective, `d0''`/`d1''` rename to `d.u1_den
  -- 0`/`d.u2_den 0`, nonzero by `denRegular`), hence `IsSMulRegular`
  -- there (domain).
  have hτ'_inj : Function.Injective (Subtype.val : τ' → τ) := Subtype.val_injective
  have hτ'rename_inj : Function.Injective
      (MvPolynomial.rename (Subtype.val : τ' → τ) : MvPolynomial τ' (F p) → MvPolynomial τ (F p)) :=
    MvPolynomial.rename_injective _ hτ'_inj
  have hden : (∀ i, d.u1_den i ≠ 0) ∧ (∀ i, d.u2_den i ≠ 0) ∧
      (∀ i, d.v1_den i ≠ 0) ∧ (∀ i, d.v2_den i ≠ 0) :=
    denRegular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB hndA hndB
  have hd0''_ne : d0'' ≠ 0 := by
    intro h
    apply hden.1 0
    rw [← hd0'', h, map_zero]
  have hd1''_ne : d1'' ≠ 0 := by
    intro h
    apply hden.2.1 0
    rw [← hd1'', h, map_zero]
  have hd0''_reg : IsSMulRegular (MvPolynomial τ' (F p)) d0'' :=
    fun x y hxy => by
      simpa [smul_eq_mul, mul_right_cancel₀, hd0''_ne] using
        mul_left_cancel₀ hd0''_ne (by simpa [smul_eq_mul] using hxy)
  have hd1''_reg : IsSMulRegular (MvPolynomial τ' (F p)) d1'' :=
    fun x y hxy => by
      simpa [smul_eq_mul, mul_right_cancel₀, hd1''_ne] using
        mul_left_cancel₀ hd1''_ne (by simpa [smul_eq_mul] using hxy)
  -- **Step D: `Fu0'` is `IsSMulRegular` in `MvPolynomial τ (F p) ⧸
  -- Ideal.ofList [Fu0']`.** `regular_of_linear_elim` at `τ := τ'`,
  -- `R := F p`, `gens' := ([] : List (MvPolynomial τ' (F p)))`, `c :=
  -- c0''`, `d := d0''`, concludes `IsSMulRegular (MvPolynomial (Option
  -- τ') (F p) ⧸ Ideal.ofList (([] : List _).map (rename some)))
  -- (rename some c0'' - X none * rename some d0'')`. `hd_reg` for this
  -- call is `hd0''_reg` pushed through `rename some` (injective, domain
  -- ⟹ domain), landing in `Ideal.ofList (([] : List _).map (rename
  -- some)) = Ideal.ofList [] = ⊥`, i.e. plain `IsSMulRegular
  -- (MvPolynomial (Option τ') (F p))`. The bridge
  -- (`isSMulRegular_bridge_prefix_gen (F p) x0 [] c0''`, §0, PROVED, no
  -- `sorry`) then converts this `Option τ'`-level fact to the wanted
  -- `τ`-level `Ideal.ofList [Fu0']` statement, using `hFu0'_eq` to
  -- identify `Fu0'` with the bridge's own LHS element (both equal
  -- `(renameEquiv (F p) (optionSplit x0)).symm (rename some (c0'' - X
  -- x0 * d0''))`... concretely, `renameEquiv`'s `.symm` applied to
  -- `rename some g` for `g := c0'' - X x0 * d0''` unfolds, via
  -- `renameEquiv_symm`/`renameEquiv_apply`, to `rename (optionSplit
  -- x0).symm (rename some g)`, and `(optionSplit x0).symm ∘ some = ((↑) :
  -- τ' → τ)` by `optionSplit`'s own construction (`Equiv.optionSubtype`),
  -- matching `hFu0'_eq`'s RHS shape after `rename_rename`).
  -- `MvPolynomial (Option τ') (F p)` is a domain (`MvPolynomial` over a
  -- field), so `IsSMulRegular` there is exactly "nonzero, cancellable."
  -- `rename some` is injective (`some` is injective), so `rename some
  -- d0'' ≠ 0` follows from `d0'' ≠ 0` (`hd0''_ne`), and regularity in a
  -- domain is `mul_left_cancel₀`.
  have hd0''_domreg : IsSMulRegular (MvPolynomial (Option τ') (F p))
      (MvPolynomial.rename (some : τ' → Option τ') d0'') := by
    have hne : MvPolynomial.rename (some : τ' → Option τ') d0'' ≠ 0 := by
      rw [Ne, MvPolynomial.rename_eq_zero_iff_of_injective d0'' (Option.some_injective τ')]
      exact hd0''_ne
    intro x y hxy
    exact mul_left_cancel₀ hne (by simpa [smul_eq_mul] using hxy)
  have hFu0'_reg_opt : IsSMulRegular
      (MvPolynomial (Option τ') (F p) ⧸
        Ideal.ofList (([] : List (MvPolynomial τ' (F p))).map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk _
        (MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0'')) := by
    apply regular_of_linear_elim (τ := τ') (R := F p) [] c0'' d0''
    · simp only [List.map_nil, Ideal.ofList_nil]
      -- `Ideal.ofList [] = ⊥`; `IsSMulRegular` in the quotient by `⊥` is
      -- (via `Ideal.Quotient.mk ⊥` an injective ring hom, in fact a ring
      -- equiv `Ideal.quotEquivOfEq`/`Submodule.quotEquivOfEqBot`-style)
      -- the same as `IsSMulRegular` in the ambient ring itself, from
      -- which `hd0''_domreg` closes it.
      sorry
    · rfl
  have hFu0'_reg : IsSMulRegular (MvPolynomial τ (F p) ⧸ Ideal.ofList [Fu0'])
      (Ideal.Quotient.mk (Ideal.ofList [Fu0']) Fu0') := by
    have hbridge := isSMulRegular_bridge_prefix_gen (F p) x0
      ([] : List (MvPolynomial τ' (F p))) (c0'' - MvPolynomial.X x0 * d0'')
    sorry
  sorry

/-! ## §2. The bridge lemma (sorry #2)

Generalizes `01_bridge.lean`/`02_bridge_core.lean`'s `isSMulRegular_bridge`
idea from a single peeled variable to an arbitrary FIXED prefix list —
but, per the correction above, PROVED (not `sorry`-backed) by directly
reusing `03_general_transport.lean`'s `isSMulRegular_of_ringEquiv_of_mapsTo`
(itself already complete, no `sorry`), applied to the ring equivalence
`peelEquiv p x : Rdec p ≃ₐ[F p] Polynomial (MvPolynomial τ (F p))`
composed with `MvPolynomial.optionEquivLeft`'s own inverse — i.e. the
SAME `e := renameEquiv (F p) (optionSplit x)` map `02_bridge_core.lean`
already identifies as the right one, just invoked through the generic
transport lemma instead of hand-rederiving the `Ideal.quotientEquiv`
dance a third time. -/

theorem peelEquivGen_eq {σ : Type*} [DecidableEq σ] (x : σ) :
    peelEquivGen p x =
      (MvPolynomial.renameEquiv (F p) (optionSplit x)).trans
        (MvPolynomial.optionEquivLeft (F p) {v : σ // v ≠ x}) := rfl

/-- **The master bridge lemma.** For `x : Idx`, `τ := {v ≠ x}`, a
`τ`-side list `gens' : List (MvPolynomial τ (F p))` and element `g :
MvPolynomial τ (F p)`, relates `IsSMulRegular` in `Rdec p` (quotiented by
the `Rdec p`-image of `gens'`/`g` under `(renameEquiv (F p)
(optionSplit x)).symm ∘ rename some`) to the SAME fact stated one level
"lower," directly in `MvPolynomial (Option τ) (F p)` (quotiented by
`Ideal.ofList (gens'.map (rename some))`) — exactly
`regular_of_linear_elim`'s/`regular_of_peeled_leadingCoeff`'s own
hypothesis/conclusion shape, so THEIR output can be fed straight into
this bridge to reach the `Rdec p ⧸ Ideal.ofList (...)` form
`isRegular_cons_iff'` wants at each stage in §3.

**Proof, actually carried out (not `sorry`) via ONE application of
`03_general_transport.lean`'s `isSMulRegular_of_ringEquiv_of_mapsTo`**,
using `e := (renameEquiv (F p) (optionSplit x)).toRingEquiv : Rdec p ≃+*
MvPolynomial (Option τ) (F p)` (a genuine ring equiv, since `Rdec p :=
MvPolynomial Idx (F p)` and `renameEquiv` is built from the ring
isomorphism `optionSplit x : Idx ≃ Option τ`), `r := (renameEquiv (F p)
(optionSplit x)).symm (rename some g)`, `s := rename some g` — `e r = s`
by `e.apply_symm_apply`. The ideal-matching hypothesis `Ideal.map e I =
J` (`I := Ideal.ofList (gens'.map ((renameEquiv ...).symm ∘ rename
some))`, `J := Ideal.ofList (gens'.map (rename some))`) follows from
`Ideal.map_ofList` plus `List.map_map` plus, pointwise, `e (e.symm (rename
some q)) = rename some q` (`e.apply_symm_apply` again) — i.e. `I`'s
generating list, pushed forward through `e`, collapses back to `J`'s
generating list exactly, since each of `I`'s generators was BUILT as
`e.symm` applied to one of `J`'s. -/
theorem isSMulRegular_bridge_prefix (x : Idx) (gens' : List (MvPolynomial {v : Idx // v ≠ x} (F p)))
    (g : MvPolynomial {v : Idx // v ≠ x} (F p)) :
    IsSMulRegular
      (Rdec p ⧸ Ideal.ofList (gens'.map (fun q =>
        (MvPolynomial.renameEquiv (F p) (optionSplit x)).symm (MvPolynomial.rename some q))))
      (Ideal.Quotient.mk _
        ((MvPolynomial.renameEquiv (F p) (optionSplit x)).symm (MvPolynomial.rename some g)))
    ↔
    IsSMulRegular
      (MvPolynomial (Option {v : Idx // v ≠ x}) (F p) ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk _ (MvPolynomial.rename some g)) :=
  isSMulRegular_bridge_prefix_gen (F p) x gens' g

/-! ## §3. The 12-stage assembly (sorry #3)

Uses §1/§2 plus everything already proved in `DecoupledSystemRegular.lean`
(`regular_of_linear_elim`, `regular_of_peeled_leadingCoeff`,
`isSMulRegular_of_mul_eq_of_isSMulRegular`, `denRegular`,
`CrossNondegenerate`, `curveCoeffRegular`, `quintic_monic`) to chain
`RingTheory.Sequence.isRegular_cons_iff'` twelve times. Per
`ROADMAP-peel-chain-assembly.md`'s corrected design, no restatement of
any upstream lemma/hypothesis is needed — this is purely the wiring
step, left as its own `sorry` so §1/§2 can be checked independently
first. -/

theorem regularSeq_of_peel_chain (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hndA : Nondegenerate p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA)
    (hndB : Nondegenerate p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB)
    (hcross : CrossNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :
    RingTheory.Sequence.IsRegular (Rdec p)
      (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) := by
  -- Stage 0 (`Fu0`, peel `U0`, empty prefix): `regular_of_linear_elim`
  -- with `gens' := []`, `hd_reg` from `denRegular.1 0` (`u1_den 0 ≠ 0`,
  -- domain) bridged via `isSMulRegular_bridge_prefix`.
  -- Stage 1 (`Fu1`, repeated `U0`): `hcross.hu0` +
  -- `isSMulRegular_of_mul_eq_of_isSMulRegular` directly (matches
  -- `hcross.hu0`'s own stated ring `Rdec p ⧸ Ideal.span {Fu0}` exactly,
  -- no bridge needed).
  -- Stage 2 (`Fu2`, peel `U1`, prefix `[Fu0,Fu1]`): `regular_of_linear_elim`
  -- with `gens' := [Fu0',Fu1']` (`τ`-side reinterpretations, via
  -- `u1_indep 0`/`u2_indep 0`), `hd_reg` from `isSMulRegular_den_of_second_peel`
  -- bridged via `isSMulRegular_bridge_prefix`.
  -- Stage 3 (`Fu3`, repeated `U1`): `hcross.hu1`, same shape as stage 1.
  -- Stages 4-7 (`Fv0..Fv3`): same four shapes, `V0,V1` instead of
  -- `U0,U1`, `hcross.hv0`/`hv1`.
  -- Stages 8-11 (`curveA1,curveA2,curveB1,curveB2`): peel the matching
  -- `w`-variable, `regular_of_peeled_leadingCoeff` with leading
  -- coefficient `1` (`quintic_monic`/`curveCoeffRegular`), trivially
  -- regular (`isSMulRegular_C_const_of_isSMulRegular` with `d := 1`,
  -- `IsSMulRegular _ 1` via `isUnit_one.isSMulRegular` or direct
  -- `smul` injectivity of `1`).
  sorry

end DecoupledSystem
end Genus2Lean
