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
anywhere; `σ`/`R` are fully generic.

**Note on `03_general_transport.lean`:** its one lemma,
`isSMulRegular_of_ringEquiv_of_mapsTo`, is used throughout this file (§0's
own bridge lemma below, plus the `⊥`-quotient helper further down) but was
NOT yet merged into `DecoupledSystemRegular.lean`'s imports as of this
pass. Pasted in verbatim here (not re-derived) so this file compiles
standalone against the current import list; move it into
`DecoupledSystemRegular.lean` proper (or add a real `import` for
`03_general_transport.lean` once it becomes its own module) as a followup
-- purely a file-organization TODO, not a mathematical one, since the
proof itself is already complete/`sorry`-free. -/

/-- **Generic transport lemma**, pasted verbatim from
`03_general_transport.lean` (already complete there, no `sorry`) — see
that file's own docstring for the derivation. Given a ring equiv `e : R ≃+*
S` carrying ideal `I` to `J` and element `r` to `s`, `IsSMulRegular (R ⧸ I)
r` transports to `IsSMulRegular (S ⧸ J) s` via conjugating by the induced
quotient equiv `Ideal.quotientEquiv I J e hIJ.symm`. -/
theorem isSMulRegular_of_ringEquiv_of_mapsTo {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (hIJ : Ideal.map (e : R →+* S) I = J)
    (r : R) (s : S) (hrs : e r = s) :
    IsSMulRegular (R ⧸ I) (Ideal.Quotient.mk I r) ↔
      IsSMulRegular (S ⧸ J) (Ideal.Quotient.mk J s) := by
  set e' : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hIJ.symm with he'_def
  have he'_apply : e' (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J s := by
    rw [he'_def, Ideal.quotientEquiv_mk, hrs]
  have he'symm_apply : e'.symm (Ideal.Quotient.mk J s) = Ideal.Quotient.mk I r := by
    rw [← he'_apply, e'.symm_apply_apply]
  constructor
  · intro hreg x y hxy
    apply e'.injective
    have hxy' : (Ideal.Quotient.mk I r) • (e'.symm x) = (Ideal.Quotient.mk I r) • (e'.symm y) := by
      have hL : e' ((Ideal.Quotient.mk I r) • (e'.symm x)) =
          (Ideal.Quotient.mk J s) • x := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'_apply, e'.apply_symm_apply]
      have hR : e' ((Ideal.Quotient.mk I r) • (e'.symm y)) =
          (Ideal.Quotient.mk J s) • y := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'_apply, e'.apply_symm_apply]
      apply e'.injective
      rw [hL, hR, hxy]
    have := hreg hxy'
    rw [e'.symm.injective.eq_iff] at this
    exact this
  · intro hreg x y hxy
    apply e'.symm.injective
    have hxy' : (Ideal.Quotient.mk J s) • (e' x) = (Ideal.Quotient.mk J s) • (e' y) := by
      have hL : e'.symm ((Ideal.Quotient.mk J s) • (e' x)) =
          (Ideal.Quotient.mk I r) • x := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'symm_apply, e'.symm_apply_apply]
      have hR : e'.symm ((Ideal.Quotient.mk J s) • (e' y)) =
          (Ideal.Quotient.mk I r) • y := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'symm_apply, e'.symm_apply_apply]
      apply e'.symm.injective
      rw [hL, hR, hxy]
    have := hreg hxy'
    rw [e'.injective.eq_iff] at this
    exact this

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
  -- **Bridging `IsSMulRegular A r` to `IsSMulRegular (A ⧸ ⊥) (mk r)`.**
  -- Proved directly (NOT via the general ring-equiv transport lemma --
  -- that lemma relates two DIFFERENT quotient rings via an equiv between
  -- their AMBIENT rings, which isn't the shape here; going through it
  -- would need `A ⧸ ⊥` reinterpreted as `(A ⧸ ⊥) ⧸ ⊥` on one side, an
  -- unnecessary extra layer of quotienting). Instead: `mk := Ideal.Quotient.mk
  -- (⊥ : Ideal A)` is a ring hom, and it is INJECTIVE -- `mk x = mk y ↔ x -
  -- y ∈ ⊥ ↔ x = y` (`Ideal.Quotient.eq` + `Ideal.mem_bot`). Surjectivity is
  -- used implicitly, via `induction ... using Quotient.inductionOn'`
  -- rather than a named `mk_surjective` lemma whose exact spelling isn't
  -- independently confirmed -- `Quotient.inductionOn'` is the standard
  -- mechanism this codebase already uses for exactly this
  -- (`regular_of_linear_elim`'s own `hsmul_mk` step in
  -- `DecoupledSystemRegular.lean`). Injectivity alone drives both
  -- directions below: forward, generalize to representatives and cancel
  -- in `A`; backward, push into `A ⧸ ⊥`, apply `hreg`, pull back via
  -- injectivity.
  have isSMulRegular_bot_iff : ∀ {A : Type*} [CommRing A] (r : A),
      IsSMulRegular A r ↔ IsSMulRegular (A ⧸ (⊥ : Ideal A)) (Ideal.Quotient.mk ⊥ r) := by
    intro A _ r
    have hmk_inj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal A)) := by
      intro x y hxy
      have hmem : x - y ∈ (⊥ : Ideal A) := (Ideal.Quotient.eq _).mp hxy
      have hsub0 : x - y = 0 := Ideal.mem_bot.mp hmem
      exact sub_eq_zero.mp hsub0
    -- `•`-action of `A` on `A ⧸ ⊥` factors through `mk`'s own ring
    -- multiplication: for `a : A` and `z : A ⧸ ⊥`, `a • z = mk a * z`
    -- (defining property of the quotient-ring module structure, the same
    -- fact `regular_of_linear_elim`'s `hsmul_mk` step in
    -- `DecoupledSystemRegular.lean` establishes by `Quotient.inductionOn'`
    -- -- proved here directly by `rfl` on representatives, matching that
    -- file's own `show ... rfl`-style unfolding).
    have hsmul_mk : ∀ (a : A) (z : A ⧸ (⊥ : Ideal A)),
        a • z = Ideal.Quotient.mk (⊥ : Ideal A) a * z := by
      intro a z
      refine Quotient.inductionOn' z ?_
      intro z'
      show Ideal.Quotient.mk (⊥ : Ideal A) (a * z') =
          Ideal.Quotient.mk (⊥ : Ideal A) a * Ideal.Quotient.mk (⊥ : Ideal A) z'
      rw [map_mul]
    constructor
    · intro hreg x y hxy
      -- `revert hxy` before inducting on `x`/`y`, so the induction's
      -- generated motive correctly abstracts over `hxy` too (inducting
      -- with `hxy` left in context, un-generalized, would leave it
      -- referring to the pre-induction `x`/`y`, a mismatch). `refine
      -- Quotient.inductionOn' x ?_` on the now-`hxy`-free goal `∀ hxy, x =
      -- y` (an implication, since `hxy` was reverted into the goal)
      -- produces exactly the motive `Quotient.inductionOn'` expects.
      revert hxy
      refine Quotient.inductionOn' x ?_
      intro x'
      refine Quotient.inductionOn' y ?_
      intro y' hxy
      rw [hsmul_mk, hsmul_mk] at hxy
      have hxy'' : r * x' = r * y' := hmk_inj hxy
      exact congrArg (Ideal.Quotient.mk (⊥ : Ideal A)) (hreg hxy'')
    · -- Reverse direction: given `hreg : IsSMulRegular (A ⧸ ⊥) (mk r)`,
      -- show `IsSMulRegular A r`, i.e. `x y : A`, `hxy : r • x = r • y ⊢ x
      -- = y`. Push `x`/`y` down to `A ⧸ ⊥` via `mk`, apply `hreg` there
      -- (using `hsmul_mk` to match `mk`'s own `•`-action to ordinary
      -- multiplication pushed through `map_mul`), then pull back up via
      -- `hmk_inj`.
      intro hreg x y hxy
      apply hmk_inj
      apply hreg
      rw [hsmul_mk, hsmul_mk]
      rw [show (Ideal.Quotient.mk (⊥ : Ideal A)) r * Ideal.Quotient.mk (⊥ : Ideal A) x
            = Ideal.Quotient.mk (⊥ : Ideal A) (r * x) from (map_mul _ r x).symm,
          show (Ideal.Quotient.mk (⊥ : Ideal A)) r * Ideal.Quotient.mk (⊥ : Ideal A) y
            = Ideal.Quotient.mk (⊥ : Ideal A) (r * y) from (map_mul _ r y).symm]
      have hxy' : r * x = r * y := by
        rw [← smul_eq_mul, ← smul_eq_mul]; exact hxy
      exact congrArg (Ideal.Quotient.mk (⊥ : Ideal A)) hxy'
  have hFu0'_reg_opt : IsSMulRegular
      (MvPolynomial (Option τ') (F p) ⧸
        Ideal.ofList (([] : List (MvPolynomial τ' (F p))).map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk _
        (MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0'')) := by
    apply regular_of_linear_elim (τ := τ') (R := F p) [] c0'' d0''
    · simp only [List.map_nil, Ideal.ofList_nil]
      exact (isSMulRegular_bot_iff (MvPolynomial.rename (some : τ' → Option τ') d0'')).mp
        hd0''_domreg
    · rfl
  -- **`hFu0'_reg`: `Fu0'` is regular mod the EMPTY prefix `Ideal.ofList
  -- ([] : List (MvPolynomial τ (F p)))`** (matching `hFu0'_reg_opt`'s own
  -- `gens' := []`, and matching `isSMulRegular_bridge_prefix_gen`'s LHS
  -- shape exactly when instantiated at `gens' := []`) -- NOT "mod
  -- `Ideal.ofList [Fu0']`" (a mis-statement caught this pass: testing a
  -- generator's regularity against the ideal IT ITSELF spans is
  -- degenerate, since its own image there is always `0`). The
  -- correctly-scoped empty-prefix fact is exactly `isRegular_cons_iff'`'s
  -- FIRST-step requirement (`r := Fu0'`, `M := MvPolynomial τ (F p)`
  -- itself, `IsSMulRegular M r` unfolds to the SAME statement as
  -- `IsSMulRegular (M ⧸ ⊥) (mk r)` via `isSMulRegular_bot_iff` +
  -- `Ideal.ofList_nil`) and is exactly what feeds the SECOND step's
  -- `QuotSMulTop Fu0' M`-module, inside which `Fu1'`'s own regularity
  -- (the next stage) is then tested.
  --
  -- Proved by instantiating `isSMulRegular_bridge_prefix_gen (F p) x0 []
  -- (c0'' - X x0 * d0'')`: its RHS is `hFu0'_reg_opt`'s exact statement
  -- (`gens' := []`, `g := c0'' - X x0 * d0''`), and its LHS is
  -- `IsSMulRegular (MvPolynomial τ (F p) ⧸ Ideal.ofList (([] :
  -- List (MvPolynomial τ' (F p))).map (fun q => (renameEquiv (F p)
  -- (optionSplit x0)).symm (rename some q)))) (mk ((renameEquiv (F p)
  -- (optionSplit x0)).symm (rename some (c0'' - X x0 * d0''))))` --
  -- `[].map _ = []`, so the ideal collapses to `Ideal.ofList []`
  -- (matching the wanted statement's prefix exactly), and the bridge
  -- element equals `Fu0'` by `hFu0'_eq` plus unfolding `renameEquiv`'s
  -- `.symm` composed with `rename some` (the same identification already
  -- spelled out in the now-superseded inline comment this replaces).
  have hFu0'_reg : IsSMulRegular
      (MvPolynomial τ (F p) ⧸ Ideal.ofList ([] : List (MvPolynomial τ (F p))))
      (Ideal.Quotient.mk (Ideal.ofList ([] : List (MvPolynomial τ (F p)))) Fu0') := by
    have hbridge := isSMulRegular_bridge_prefix_gen (F p) x0
      ([] : List (MvPolynomial τ' (F p))) (c0'' - MvPolynomial.X x0 * d0'')
    simp only [List.map_nil] at hbridge
    rw [hbridge]
    rw [show (MvPolynomial.rename (some : τ' → Option τ') (c0'' - MvPolynomial.X x0 * d0'')) =
        MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0'' by
      rw [map_sub, map_mul, MvPolynomial.rename_X]]
    exact hFu0'_reg_opt
  -- **Step E: `Fu1'` is `IsSMulRegular` mod `Ideal.ofList [Fu0']`.**
  -- Apply `regular_of_linear_elim` a SECOND time, now at `τ := τ'` (one
  -- level further down than Step D), `R := F p`, `gens' := [c0'']`
  -- (`Fu0'` reinterpreted as a `τ'`-side element -- the SAME `c0'', d0''`
  -- Step A/B already produced), `c := c1''`, `d := d1''`. `hd_reg` for
  -- THIS call needs `d1''`'s `rename some` image regular mod
  -- `Ideal.ofList [rename some c0'']` in `MvPolynomial (Option τ') (F p)`
  -- -- this is a genuine `regular_of_disjoint_extension` instance (NOT
  -- the multi-generator mess earlier drafts worried about): `c0''` lives
  -- entirely in `u1_indep`'s A-side Finset `{wa1,wa2,a1,a2}` and `d1''`
  -- entirely in `u2_indep`'s B-side Finset `{wb1,wb2,b1,b2}` (both
  -- reinterpreted inside `τ'`, disjoint from each other and from `x0`),
  -- so splitting `τ'` as `σ₁ ⊕ σ₂` along "does this variable's `Idx`-image
  -- lie in `{wa1,wa2,a1,a2}`" separates `c0''` (lands entirely in `σ₁`)
  -- from `d1''` (lands entirely in `σ₂`) cleanly, with NO element
  -- straddling both sides (unlike `Fu0`/`Fu1` themselves at the OUTER
  -- level, which straddle their target variable and their own side --
  -- the whole reason this needed a second peel first: after Step
  -- A/B/D's peeling, `c0''`/`d0''`/`c1''`/`d1''` are honest τ'-side
  -- elements with NO further `x0`-dependence to straddle).
  classical
  set predA : τ' → Prop := fun v => (v.1.1 : Idx) ∈ ({wa1, wa2, a1, a2} : Finset Idx) with hpredA_def
  set σ₁ : Type := {v : τ' // predA v} with hσ₁_def
  set σ₂ : Type := {v : τ' // ¬ predA v} with hσ₂_def
  set esplit : σ₁ ⊕ σ₂ ≃ τ' := Equiv.sumCompl predA with hesplit_def
  -- `c0''`'s variables lie in `predA` (A-side, per `u1_indep 0`'s target
  -- Finset transported through `hc0''`/`f`'s range description already
  -- established in Step A) -- so `c0''` has a `σ₁`-side representative.
  have hc0''_predA : (↑c0''.vars : Set τ') ⊆ {v : τ' | predA v} := by
    intro v hv
    have hmem : ((fun w : τ' => (w.1.1 : Idx)) v) ∈ ({wa1, wa2, a1, a2} : Finset Idx) := by
      have hrange : (v.1.1 : Idx) ∈ (↑(d.u1_num 0).vars : Set Idx) := by
        have := congrArg MvPolynomial.vars hc0''
        rw [MvPolynomial.vars_rename_of_injective _ hf_inj] at this
        rw [this]; exact Finset.mem_image_of_mem _ hv
      exact d.u1_indep 0 v.1.1 (Finset.mem_union_left _ hrange)
    simpa [hpredA_def] using hmem
  have hd1''_predA : (↑d1''.vars : Set τ') ⊆ {v : τ' | ¬ predA v} := by
    intro v hv
    have hmem : ((fun w : τ' => (w.1.1 : Idx)) v) ∈ ({wb1, wb2, b1, b2} : Finset Idx) := by
      have hrange : (v.1.1 : Idx) ∈ (↑(d.u2_den 0).vars : Set Idx) := by
        have := congrArg MvPolynomial.vars hd1''
        rw [MvPolynomial.vars_rename_of_injective _ hf_inj] at this
        rw [this]; exact Finset.mem_image_of_mem _ hv
      exact d.u2_indep 0 v.1.1 (Finset.mem_union_right _ hrange)
    intro hcontra
    simp only [hpredA_def, Finset.mem_insert, Finset.mem_singleton] at hmem hcontra
    rcases hcontra with h | h | h | h <;> rw [h] at hmem <;> simp_all
  obtain ⟨c0₁, hc0₁⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    c0'' (Subtype.val : σ₁ → τ') Subtype.val_injective
    (by rw [Subtype.range_val]; exact hc0''_predA)
  obtain ⟨d1₂, hd1₂⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    d1'' (Subtype.val : σ₂ → τ') Subtype.val_injective
    (by rw [Subtype.range_val]; exact hd1''_predA)
  -- `c0₁ : MvPolynomial σ₁ (F p)`, `d1₂ : MvPolynomial σ₂ (F p)`, both
  -- honest disjoint-side elements. `d1₂` is nonzero (renaming injective,
  -- `d1'' ≠ 0` from `hd1''_ne`), hence `IsSMulRegular` in its own ring
  -- `MvPolynomial σ₂ (F p)` (a domain).
  have hd1₂_ne : d1₂ ≠ 0 := by
    intro h
    apply hd1''_ne
    rw [← hd1₂, h, map_zero]
  have hd1₂_reg : IsSMulRegular (MvPolynomial σ₂ (F p)) d1₂ :=
    fun x y hxy => by
      simpa [smul_eq_mul, mul_right_cancel₀, hd1₂_ne] using
        mul_left_cancel₀ hd1₂_ne (by simpa [smul_eq_mul] using hxy)
  -- **`regular_of_disjoint_extension` applied**: `d1₂`'s image (`rename
  -- Sum.inr d1₂`) survives quotienting `MvPolynomial (σ₁ ⊕ σ₂) (F p)` by
  -- `⟨rename Sum.inl c0₁⟩`.
  have hdisjoint := regular_of_disjoint_extension (R := F p) (σ₁ := σ₁) (σ₂ := σ₂)
    c0₁ hd1₂_reg
  -- Transport `hdisjoint` (stated over `σ₁ ⊕ σ₂`) back to `τ'` via
  -- `renameEquiv (F p) esplit : MvPolynomial (σ₁ ⊕ σ₂) (F p) ≃+*
  -- MvPolynomial τ' (F p)`, using `esplit`'s defining property
  -- (`Equiv.sumCompl_apply_inl`/`_inr`) to identify `esplit (Sum.inl v) =
  -- v.1` / `esplit (Sum.inr v) = v.1`, hence `rename esplit (rename
  -- Sum.inl c0₁) = rename Subtype.val c0₁ = c0''` (by `hc0₁` composed with
  -- `rename_rename`) and likewise for `d1₂`/`d1''`.
  set eO : MvPolynomial (σ₁ ⊕ σ₂) (F p) ≃+* MvPolynomial τ' (F p) :=
    (MvPolynomial.renameEquiv (F p) esplit).toRingEquiv with heO_def
  have heO_inl : eO (MvPolynomial.rename Sum.inl c0₁) = c0'' := by
    show MvPolynomial.rename (⇑esplit) (MvPolynomial.rename Sum.inl c0₁) = c0''
    rw [MvPolynomial.rename_rename]
    rw [show (⇑esplit ∘ Sum.inl : σ₁ → τ') = (Subtype.val : σ₁ → τ') from
      funext (fun v => Equiv.sumCompl_apply_inl predA v)]
    exact hc0₁
  have heO_inr : eO (MvPolynomial.rename Sum.inr d1₂) = d1'' := by
    show MvPolynomial.rename (⇑esplit) (MvPolynomial.rename Sum.inr d1₂) = d1''
    rw [MvPolynomial.rename_rename]
    rw [show (⇑esplit ∘ Sum.inr : σ₂ → τ') = (Subtype.val : σ₂ → τ') from
      funext (fun v => Equiv.sumCompl_apply_inr predA v)]
    exact hd1₂
  have hIdealMapO : Ideal.map (eO : MvPolynomial (σ₁ ⊕ σ₂) (F p) →+* MvPolynomial τ' (F p))
      (Ideal.ofList [MvPolynomial.rename Sum.inl c0₁]) = Ideal.ofList [c0''] := by
    rw [Ideal.ofList_singleton, Ideal.ofList_singleton, Ideal.map_span, Set.image_singleton, heO_inl]
  have hd1''_reg_mod_c0'' :
      IsSMulRegular (MvPolynomial τ' (F p) ⧸ Ideal.ofList [c0''])
        (Ideal.Quotient.mk (Ideal.ofList [c0'']) d1'') := by
    have := (isSMulRegular_of_ringEquiv_of_mapsTo eO
      (Ideal.ofList [MvPolynomial.rename Sum.inl c0₁]) (Ideal.ofList [c0''])
      hIdealMapO (MvPolynomial.rename Sum.inl c0₁) c0'' heO_inl).mp
    rw [← heO_inr]
    exact this hdisjoint
  -- Push `d1''`'s regularity (mod `⟨c0''⟩` in `τ'`'s ring) forward to the
  -- `Option τ'`-level fact `regular_of_linear_elim` needs as its `hd_reg`
  -- (`gens' := [c0'']`, `d := d1''`): plain functoriality of
  -- `Ideal.Quotient.mk`/`rename some`, matching the domain-preservation
  -- step Step D already used for the empty-prefix case, now for a
  -- singleton prefix -- `rename some` is injective, so nonzero survives,
  -- and `IsSMulRegular` in a domain is exactly `mul_left_cancel₀`, BUT
  -- here the ambient ring is a nontrivial quotient (not a domain
  -- outright), so instead of re-deriving from scratch we reuse
  -- `regular_of_linear_elim`'s OWN internal machinery is unavailable
  -- directly -- what IS available is the general fact that `rename some`
  -- (an injective ring hom into a LARGER polynomial ring not touching
  -- `none`) commutes with quotienting by a `gens'`-list not involving
  -- `none` either, i.e. this is exactly `isSMulRegular_bridge_prefix_gen`
  -- applied a THIRD time, now at `σ := τ'`, `x :=` (a placeholder single
  -- extra variable) -- **not needed**: `regular_of_linear_elim` itself
  -- takes `hd_reg` stated ALREADY at the `Option τ'` level, and the
  -- bridge from "regular mod `Ideal.ofList gens'` in the base ring" to
  -- "regular mod `Ideal.ofList (gens'.map (rename some))` in `Option`
  -- of that ring" for a NONZERODIVISOR/regular element is exactly
  -- `regular_of_peeled_leadingCoeff`'s/Layer 1's OWN transport shape one
  -- more time: `MvPolynomial (Option τ') (F p) ⧸ Ideal.ofList
  -- (gens'.map (rename some))` is `Polynomial` of `MvPolynomial τ' (F p)
  -- ⧸ Ideal.ofList gens'`, and `rename some d1''`'s image there is `C
  -- (mk d1'')`, regular by `isSMulRegular_C_const_of_isSMulRegular`
  -- applied to `hd1''_reg_mod_c0''`, transported through the SAME
  -- `optionEquivLeft`-based identification `regular_of_linear_elim`
  -- itself uses internally (`Ideal.quotientEquiv` + `optionEquivLeft`,
  -- exactly `hFu0'_reg_opt`'s own route, now with `gens' := [c0'']`
  -- instead of `[]`).
  set I'₁ : Ideal (MvPolynomial τ' (F p)) := Ideal.ofList [c0''] with hI'₁_def
  set A₁ : Ideal (MvPolynomial (Option τ') (F p)) :=
    Ideal.ofList (([c0''] : List (MvPolynomial τ' (F p))).map (MvPolynomial.rename some)) with hA₁_def
  have hIdealMap₁ : Ideal.map ((MvPolynomial.optionEquivLeft (F p) τ').toRingEquiv :
      MvPolynomial (Option τ') (F p) →+* Polynomial (MvPolynomial τ' (F p))) A₁ =
      Ideal.map Polynomial.C I'₁ := by
    rw [hA₁_def, hI'₁_def, Ideal.map_ofList, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    show (MvPolynomial.optionEquivLeft (F p) τ') (MvPolynomial.rename some q) = Polynomial.C q
    exact optionEquivLeft_rename_some q
  set e₁ : (MvPolynomial (Option τ') (F p) ⧸ A₁) ≃+* Polynomial (MvPolynomial τ' (F p) ⧸ I'₁) :=
    (Ideal.quotientEquiv A₁ (Ideal.map Polynomial.C I'₁)
      (MvPolynomial.optionEquivLeft (F p) τ').toRingEquiv hIdealMap₁.symm).trans
      I'₁.polynomialQuotientEquivQuotientPolynomial.symm with he₁_def
  have he₁_apply : ∀ x : MvPolynomial (Option τ') (F p) ⧸ A₁,
      e₁ x = I'₁.polynomialQuotientEquivQuotientPolynomial.symm
        ((Ideal.quotientEquiv A₁ (Ideal.map Polynomial.C I'₁)
          (MvPolynomial.optionEquivLeft (F p) τ').toRingEquiv hIdealMap₁.symm) x) := by
    intro x; rw [he₁_def, RingEquiv.trans_apply]
  have he₁_C : e₁ (Ideal.Quotient.mk A₁ (MvPolynomial.rename some d1'')) =
      Polynomial.C (Ideal.Quotient.mk I'₁ d1'') := by
    rw [he₁_apply, Ideal.quotientEquiv_mk]
    have hstep : (MvPolynomial.optionEquivLeft (F p) τ').toRingEquiv
        (MvPolynomial.rename some d1'') = Polynomial.C d1'' := optionEquivLeft_rename_some d1''
    rw [hstep, Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk]
    simp
  have hd1''_opt_reg : IsSMulRegular (MvPolynomial (Option τ') (F p) ⧸ A₁)
      (Ideal.Quotient.mk A₁ (MvPolynomial.rename some d1'')) := by
    have hsmul_mk₁ : ∀ (r : MvPolynomial (Option τ') (F p)) (x : MvPolynomial (Option τ') (F p) ⧸ A₁),
        r • x = Ideal.Quotient.mk A₁ r * x := by
      intro r x
      refine Quotient.inductionOn' x ?_
      intro x'
      show Ideal.Quotient.mk A₁ (r * x') = Ideal.Quotient.mk A₁ r * Ideal.Quotient.mk A₁ x'
      rw [map_mul]
    have hreg_poly : IsSMulRegular (Polynomial (MvPolynomial τ' (F p) ⧸ I'₁))
        (Polynomial.C (Ideal.Quotient.mk I'₁ d1'')) :=
      isSMulRegular_C_const_of_isSMulRegular hd1''_reg_mod_c0''
    intro x y hxy
    change (MvPolynomial.rename some d1'') • x = (MvPolynomial.rename some d1'') • y at hxy
    rw [hsmul_mk₁ _ x, hsmul_mk₁ _ y] at hxy
    apply e₁.injective
    have hstep : e₁ (Ideal.Quotient.mk A₁ (MvPolynomial.rename some d1'') * x) =
        e₁ (Ideal.Quotient.mk A₁ (MvPolynomial.rename some d1'') * y) := by rw [hxy]
    rw [map_mul, map_mul, he₁_C] at hstep
    have hxy' : (Polynomial.C (Ideal.Quotient.mk I'₁ d1'')) • e₁ x =
        (Polynomial.C (Ideal.Quotient.mk I'₁ d1'')) • e₁ y := by
      simpa [smul_eq_mul] using hstep
    exact hreg_poly hxy'
  -- **`Fu1'` regular mod `⟨Fu0'⟩` (in `τ`'s ring)**: `regular_of_linear_elim`
  -- at `τ := τ'`, `gens' := [c0'']`, `c := c1''`, `d := d1''`, `hd_reg :=
  -- hd1''_opt_reg`, concluding regularity of `rename some c1'' - X none *
  -- rename some d1''` mod `Ideal.ofList [rename some c0'']` in
  -- `MvPolynomial (Option τ') (F p)` -- exactly `hFu1'_reg_opt` below,
  -- matching `hFu1'_eq`'s shape.
  have hFu1'_reg_opt : IsSMulRegular
      (MvPolynomial (Option τ') (F p) ⧸
        Ideal.ofList (([c0''] : List (MvPolynomial τ' (F p))).map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk _
        (MvPolynomial.rename some c1'' - MvPolynomial.X none * MvPolynomial.rename some d1'')) := by
    apply regular_of_linear_elim (τ := τ') (R := F p) [c0''] c1'' d1''
    · exact hd1''_opt_reg
    · rfl
  -- Bridge `hFu1'_reg_opt` (at `Option τ'` level, prefix `[c0'']`) up to
  -- `τ`'s ring (prefix `[Fu0']`), via `isSMulRegular_bridge_prefix_gen (F
  -- p) x0 [c0''] (c1'' - X x0 * d1'')` -- the SAME bridge instance
  -- `hFu0'_reg` used, now with a nonempty `gens'`.
  have hFu1'_reg : IsSMulRegular
      (MvPolynomial τ (F p) ⧸ Ideal.ofList [Fu0'])
      (Ideal.Quotient.mk (Ideal.ofList [Fu0']) Fu1') := by
    have hbridge := isSMulRegular_bridge_prefix_gen (F p) x0
      ([c0''] : List (MvPolynomial τ' (F p))) (c1'' - MvPolynomial.X x0 * d1'')
    -- `(renameEquiv (F p) (optionSplit x0)).symm ∘ rename some = rename
    -- (Subtype.val : τ' → τ)`, since `renameEquiv _ e` unfolds to `rename
    -- e`/`rename e.symm` on the two sides and `(optionSplit x0).symm ∘
    -- some = (Subtype.val : τ' → τ)` by `optionSplit`'s own construction
    -- (`Equiv.optionSubtype`) -- both `rfl`-provable compositions, so the
    -- whole bridge LHS collapses onto plain `rename (Subtype.val : τ' →
    -- τ)` applied to the `τ'`-side list/element, matching `hFu0'_eq`/
    -- `hFu1'_eq`'s own RHS shape exactly.
    have hcollapse : ∀ q : MvPolynomial τ' (F p),
        (MvPolynomial.renameEquiv (F p) (optionSplit x0)).symm (MvPolynomial.rename some q) =
        MvPolynomial.rename (Subtype.val : τ' → τ) q := fun q => rfl
    simp only [List.map_cons, List.map_nil, hcollapse] at hbridge
    have hLHS_eq : MvPolynomial.rename (Subtype.val : τ' → τ) c0'' = Fu0' := by
      rw [hFu0'_eq, map_sub, map_mul, MvPolynomial.rename_X]
    have hRHS_eq : MvPolynomial.rename (Subtype.val : τ' → τ) (c1'' - MvPolynomial.X x0 * d1'') = Fu1' := by
      rw [hFu1'_eq, map_sub, map_mul, MvPolynomial.rename_X]
    rw [hLHS_eq, hRHS_eq] at hbridge
    rw [hbridge]
    rw [show (MvPolynomial.rename (some : τ' → Option τ') (c1'' - MvPolynomial.X x0 * d1'')) =
        MvPolynomial.rename some c1'' - MvPolynomial.X none * MvPolynomial.rename some d1'' by
      rw [map_sub, map_mul, MvPolynomial.rename_X]]
    exact hFu1'_reg_opt
  -- **Step F: `d'` is `IsSMulRegular` mod `Ideal.ofList [Fu0', Fu1']`
  -- (the lemma's actual target).** `d1den''` (the `τ'`-side
  -- reinterpretation of `d.u1_den 1`, per `hd1den''`) is A-side (per
  -- `u1_indep 1`), same side as `c0''`/`d0''` (`u1_indep 0`) but
  -- DISJOINT from `c1''`/`d1''` (`u2_indep 0`, B-side). So: (i) `d1den''`
  -- regular mod `⟨Fu0'⟩` needs the SAME Layer-1 "constant survives one
  -- linear peel" argument Step D/the `hd1''_opt_reg` block already used
  -- (no disjointness needed for THIS half, since `d1den''` and `Fu0'`
  -- share A-side variables -- it's the peeling itself, not
  -- disjointness, that makes this survive); (ii) `d1den''`'s image (now
  -- mod `⟨Fu0'⟩`) surviving the FURTHER quotient by `⟨Fu1'⟩` genuinely
  -- needs `regular_of_disjoint_extension`, since `d1den''` (A-side) and
  -- `Fu1'` (B-side + `x0`) ARE variable-disjoint -- exactly the
  -- `hd1''_reg_mod_c0''`-style argument, run with the roles of
  -- `(c0'',d1'')` swapped for `(Fu1'-as-a-single-generator, d1den'')`,
  -- and with the AMBIENT ring now `MvPolynomial τ (F p)` (already
  -- one quotient deep) rather than `τ'`'s bare ring.
  --
  -- Concretely: split `τ := {v ≠ U1}` itself (not `τ'`) as `σ₁' ⊕ σ₂'`
  -- along the SAME `predA`-style A-side/not-A-side predicate (now over
  -- `τ`, one variable wider than `τ'` since `τ` still contains `x0`),
  -- with `Fu1' : MvPolynomial τ (F p)` living entirely in `σ₂'` (its
  -- content is B-side `∪ {x0}`, and `x0 ∉ ASide`) and `d1den'' `'s
  -- `τ`-side image (`rename Subtype.val d1den''`) living entirely in
  -- `σ₁'`. `regular_of_disjoint_extension` then gives `d1den''`'s image
  -- regular mod `⟨Fu1'⟩` directly in `MvPolynomial τ (F p)` -- but this
  -- is regularity mod `⟨Fu1'⟩` ALONE, not the FULL `⟨Fu0', Fu1'⟩` we
  -- need; combining with (i) (regularity mod `⟨Fu0'⟩` alone) into
  -- regularity mod BOTH simultaneously is exactly the "growing prefix"
  -- gluing step the roadmap's `isSMulRegular_bridge_prefix`-style
  -- machinery handles at the OUTER (12-stage) level -- reusing the
  -- SAME two-generator Layer-1 construction already built above for
  -- `hFu1'_reg_opt`/`hd1''_opt_reg`, now with `gens' := [Fu0']`
  -- (`τ`-level, one generator) playing the earlier `[c0'']`'s role, and
  -- `d1den''`'s `τ`-image playing `d1''`'s role -- i.e. apply THE SAME
  -- CONSTRUCTION recursively: `d1den''` (A-side, disjoint from `Fu1'`'s
  -- B-side+x0 content) regular mod `⟨Fu1'⟩` via `regular_of_disjoint_extension`
  -- (fresh instance, `σ₁ := ` the "B-side + x0" split of `τ`, `σ₂ := `
  -- A-side), THEN `regular_of_linear_elim`-style Layer 1 promotes
  -- "regular mod `⟨Fu1'⟩` alone" to "regular mod `⟨Fu0', Fu1'⟩`" by
  -- treating `Fu0'` as the SECOND peel step exactly as `hFu1'_reg`
  -- itself did for `Fu1'` against `⟨Fu0'⟩` -- but IN THE OTHER ORDER
  -- (`Fu1'` first, `Fu0'` second), which is fine since `IsRegular`'s
  -- underlying ideal `Ideal.ofList [Fu0',Fu1']` doesn't care about
  -- generator order (only `RingTheory.Sequence.IsRegular` the ORDERED
  -- LIST does, and this `have` is about the ideal-level `IsSMulRegular`
  -- fact alone, not the ordered sequence itself).
  --
  -- This is now a full second copy of the `hFu1'_reg`-style two-peel
  -- argument, applied to a different pair (`d1den''` in place of
  -- `Fu1'`'s `c1''`/`d1''` payload, `Fu1'` in place of `Fu0'` as "the
  -- generator already imposed") -- long but mechanical, left as its own
  -- named local sub-`sorry` this pass so the ALREADY-COMPLETE
  -- `hFu0'_reg`/`hFu1'_reg` results above (the genuinely new content of
  -- this lemma) can be checked in the REPL independently first, per
  -- Claire's own "ship a real, checkable partial proof, easiest first"
  -- convention -- this closing step is mechanical repetition of the
  -- SAME pattern just built twice above, not new mathematics, so
  -- deferring it costs no insight, only typing.
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
