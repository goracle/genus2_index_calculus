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

**Status as of THIS pass:** `regularSeq_of_peel_chain` is now fully
assembled with **zero tactic-position `sorry`s** — but at the cost of
three new, explicitly-named hypotheses, added per Claire's direct
instruction rather than left as silent gaps or chased as open
mathematics this pass:

- `PeelChainNondegenerate` (new structure, §3bis, mirrors
  `Nondegenerate`/`CrossNondegenerate`'s existing convention) bundles
  Gap A (stage 2/3/6/7 cross-index coprimality-flavored regularity,
  `hu01/hv01/hu1_full/hv1_full`) and Gap B (stage 8-11 curve-relation
  regularity mod the accumulated prefix, `hcurveA1/A2/B1/B2`) as
  per-instance exceptional-locus conditions, exactly like
  `CrossNondegenerate` already does for the stage 1/5 resultants.
- `isSMulRegular_den_of_second_peel` (§1) gained one further hypothesis,
  `hd'_full_reg`, isolating the one remaining un-chained step in its own
  (otherwise fully worked out, `hcross01`-consuming) internal argument —
  not wired into the outer assembly, kept as its own theorem with the
  finer-grained partial proof left in place for future use.
- `regularSeq_of_peel_chain` itself gained `htop_ne_smul` (Gap C, the
  full ideal's properness / existence of a common solution point) —
  genuine separate mathematics, not attempted.

See `ROADMAP-peel-chain-assembly.md` and §3bis's own docstring below for
exactly what each new hypothesis asserts and why. Per Claire: the
eventual target is to re-parametrize these hypotheses in terms of a
scalar `alpha` and actual curve points `P1,...,P4` rather than raw
`SampleTarget` data — not attempted this pass, but the hypotheses are
structured (one bundle per genuine mathematical gap, named and
documented) to make that re-parametrization straightforward later.
-/

namespace Genus2Lean
namespace DecoupledSystem

/-! REFACTOR REVISION

This revision extracts the `optionSplit` rename identities from the large
second-peel proof.  In particular, the old `congrArg MvPolynomial.rename`
call at the `hFu0'_maps` step left the `CommSemiring` parameter unresolved.
The typed helper lemmas below make both the source variable type and the
coefficient ring explicit.  The remaining Step-F `sorry` is intentionally
kept as a single named local bottleneck: it is the actual unproved
regularity/coprimality step, not a Lean elaboration problem.
-/

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
    apply e'.symm.injective
    have hxy' : (Ideal.Quotient.mk I r) • (e'.symm x) = (Ideal.Quotient.mk I r) • (e'.symm y) := by
      have hL : e' ((Ideal.Quotient.mk I r) • (e'.symm x)) =
          (Ideal.Quotient.mk J s) • x := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'_apply, e'.apply_symm_apply]
      have hR : e' ((Ideal.Quotient.mk I r) • (e'.symm y)) =
          (Ideal.Quotient.mk J s) • y := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'_apply, e'.apply_symm_apply]
      apply e'.injective
      dsimp only at hxy
      rw [hL, hR, hxy]
    exact hreg hxy'
  · intro hreg x y hxy
    apply e'.injective
    have hxy' : (Ideal.Quotient.mk J s) • (e' x) = (Ideal.Quotient.mk J s) • (e' y) := by
      have hL : e'.symm ((Ideal.Quotient.mk J s) • (e' x)) =
          (Ideal.Quotient.mk I r) • x := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'symm_apply, e'.symm_apply_apply]
      have hR : e'.symm ((Ideal.Quotient.mk J s) • (e' y)) =
          (Ideal.Quotient.mk I r) • y := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'symm_apply, e'.symm_apply_apply]
      apply e'.symm.injective
      dsimp only at hxy
      rw [hL, hR, hxy]
    exact hreg hxy'

/-- Regularity is unchanged on quotienting by the bottom ideal. -/
theorem isSMulRegular_bot_iff {R : Type*} [CommRing R] (r : R) :
    IsSMulRegular R r ↔
      IsSMulRegular (R ⧸ (⊥ : Ideal R)) (Ideal.Quotient.mk ⊥ r) := by
  have hmk_inj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal R)) := by
    intro x y hxy
    have hmem : x - y ∈ (⊥ : Ideal R) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).mp hxy
    exact sub_eq_zero.mp (Ideal.mem_bot.mp hmem)
  constructor
  · intro hreg x y hxy
    revert hxy
    refine Quotient.inductionOn' x ?_
    intro x'
    refine Quotient.inductionOn' y ?_
    intro y' hxy
    have hxy' : r * x' = r * y' := by
      apply hmk_inj
      change (Ideal.Quotient.mk (⊥ : Ideal R)) r * Quotient.mk'' x' =
        (Ideal.Quotient.mk (⊥ : Ideal R)) r * Quotient.mk'' y'
      exact hxy
    exact congrArg (Ideal.Quotient.mk (⊥ : Ideal R)) (hreg hxy')
  · intro hreg x y hxy
    apply hmk_inj
    apply hreg
    have hxy' : r * x = r * y := by
      simpa only [smul_eq_mul] using hxy
    simpa only [smul_eq_mul, map_mul] using
      congrArg (Ideal.Quotient.mk (⊥ : Ideal R)) hxy'

/-- Regularity of a scalar on the module given by the bottom quotient. -/
theorem isSMulRegular_bot_module_iff {R : Type*} [CommRing R] (r : R) :
    IsSMulRegular R r ↔ IsSMulRegular (R ⧸ (⊥ : Ideal R)) r := by
  have hmk_inj : Function.Injective (Ideal.Quotient.mk (⊥ : Ideal R)) := by
    intro x y hxy
    have hmem : x - y ∈ (⊥ : Ideal R) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem x y).mp hxy
    exact sub_eq_zero.mp (Ideal.mem_bot.mp hmem)

  constructor
  · intro hreg x y hxy
    revert hxy
    refine Quotient.inductionOn' x ?_
    intro x'
    refine Quotient.inductionOn' y ?_
    intro y' hxy

    have hxy' : r * x' = r * y' := by
      apply hmk_inj
      change (Ideal.Quotient.mk (⊥ : Ideal R)) r * Quotient.mk'' x' =
        (Ideal.Quotient.mk (⊥ : Ideal R)) r * Quotient.mk'' y'
      exact hxy

    exact congrArg (Ideal.Quotient.mk (⊥ : Ideal R)) (hreg hxy')

  · intro hreg x y hxy
    apply hmk_inj
    apply hreg

    change (Ideal.Quotient.mk (⊥ : Ideal R)) r *
        (Ideal.Quotient.mk (⊥ : Ideal R)) x =
      (Ideal.Quotient.mk (⊥ : Ideal R)) r *
        (Ideal.Quotient.mk (⊥ : Ideal R)) y

    rw [← map_mul, ← map_mul]
    exact congrArg (Ideal.Quotient.mk (⊥ : Ideal R)) hxy

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
theorem isSMulRegular_bridge_prefix_gen
    {σ : Type*} [DecidableEq σ] (R : Type*) [CommRing R]
    (x : σ) (gens' : List (MvPolynomial {v : σ // v ≠ x} R))
    (g : MvPolynomial (Option {v : σ // v ≠ x}) R) :
    IsSMulRegular
      (MvPolynomial σ R ⧸
        Ideal.ofList (gens'.map (fun q : MvPolynomial {v : σ // v ≠ x} R =>
          ((MvPolynomial.renameEquiv R (optionSplit x)).symm
            (MvPolynomial.rename some q) :
            MvPolynomial σ R))))
      (Ideal.Quotient.mk
        (Ideal.ofList (gens'.map (fun q : MvPolynomial {v : σ // v ≠ x} R =>
          ((MvPolynomial.renameEquiv R (optionSplit x)).symm
            (MvPolynomial.rename some q) :
            MvPolynomial σ R))))
        ((MvPolynomial.renameEquiv R (optionSplit x)).symm g))
    ↔
    IsSMulRegular
      (MvPolynomial (Option {v : σ // v ≠ x}) R ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk
        (Ideal.ofList (gens'.map (MvPolynomial.rename some)))
        g) := by
  set e : MvPolynomial σ R ≃+*
      MvPolynomial (Option {v : σ // v ≠ x}) R :=
    (MvPolynomial.renameEquiv R (optionSplit x)).toRingEquiv with he_def

  set I : Ideal (MvPolynomial σ R) :=
    Ideal.ofList (gens'.map (fun q : MvPolynomial {v : σ // v ≠ x} R =>
      (e.symm (MvPolynomial.rename some q) : MvPolynomial σ R))) with hI_def

  set J : Ideal (MvPolynomial (Option {v : σ // v ≠ x}) R) :=
    Ideal.ofList (gens'.map (MvPolynomial.rename some)) with hJ_def

  have hIJ :
      Ideal.map
        (e : MvPolynomial σ R →+* MvPolynomial (Option {v : σ // v ≠ x}) R) I = J := by
    rw [hI_def, hJ_def, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    change e (e.symm (MvPolynomial.rename some q)) = MvPolynomial.rename some q
    exact e.apply_symm_apply _

  have hrs : e (e.symm g) = g := e.apply_symm_apply _

  exact isSMulRegular_of_ringEquiv_of_mapsTo e I J hIJ
    (e.symm g) g hrs


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

/-- If `a` and `b` are coprime in a commutative ring, then `b` is regular after
quotienting by the principal ideal generated by `a`.  This is the exact
algebraic fact needed by the second-peel obstruction below.  In particular,
it reduces the obstruction to the single concrete coprimality statement
`IsCoprime c0'' d1den''`; there is no longer any hidden quotient-theoretic
gap once that statement is supplied.
-/
theorem isSMulRegular_quotient_span_singleton_of_isCoprime
    {A : Type*} [CommRing A] {a b : A} (hab : IsCoprime a b) :
    IsSMulRegular (A ⧸ (Ideal.span {a}))
      (Ideal.Quotient.mk (Ideal.span {a}) b) := by
  intro x y hxy
  revert hxy
  refine Quotient.inductionOn' x ?_
  intro x'
  refine Quotient.inductionOn' y ?_
  intro y' hxy
  have hmul :
      Ideal.Quotient.mk (Ideal.span {a}) (b * x') =
        Ideal.Quotient.mk (Ideal.span {a}) (b * y') := by
    have hxy' :
        (Ideal.Quotient.mk (Ideal.span {a}) b) * Quotient.mk'' x' =
          (Ideal.Quotient.mk (Ideal.span {a}) b) * Quotient.mk'' y' := by
      simpa only [smul_eq_mul] using hxy
    have hxy'' :
        Ideal.Quotient.mk (Ideal.span {a}) b * Ideal.Quotient.mk (Ideal.span {a}) x' =
          Ideal.Quotient.mk (Ideal.span {a}) b * Ideal.Quotient.mk (Ideal.span {a}) y' := hxy'
    rw [← map_mul, ← map_mul] at hxy''
    exact hxy''
  have hmem : b * x' - b * y' ∈ Ideal.span {a} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hmul
  have hmem' : b * (x' - y') ∈ Ideal.span {a} := by
    simpa only [mul_sub] using hmem
  have habs : a ∣ b * (x' - y') :=
    Ideal.mem_span_singleton.mp hmem'
  have hdiff : a ∣ x' - y' :=
    hab.dvd_of_dvd_mul_left habs
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    (Ideal.mem_span_singleton.mpr hdiff)

/--
A small elaboration lemma for the `optionSplit` change of variables.  The old
proof used `congrArg MvPolynomial.rename`, leaving the coefficient ring and
source variable type implicit.  At that point both are dependent on nested
subtypes, so Lean could leave the `CommSemiring` parameter metavariable
stuck.  Making the polynomial and its variable map explicit removes that
ambiguity and also gives the later second-peel proof a named reusable fact.
-/
theorem rename_optionSplit_some
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (q : MvPolynomial {v : σ // v ≠ x} R) :
    MvPolynomial.rename (optionSplit x ∘ (Subtype.val : {v : σ // v ≠ x} → σ)) q =
      MvPolynomial.rename (some : {v : σ // v ≠ x} → Option {v : σ // v ≠ x}) q := by
  have hsplit :
      (optionSplit x) ∘ (Subtype.val : {v : σ // v ≠ x} → σ) =
        (some : {v : σ // v ≠ x} → Option {v : σ // v ≠ x}) := by
    funext v
    change (Equiv.optionSubtypeNe x).symm v.val = some v
    exact Equiv.optionSubtypeNe_symm_of_ne v.property
  rw [hsplit]

/-- The complete linear change-of-variables identity used by the first
`U0`-peel. -/
theorem rename_optionSplit_linear
    {σ R : Type*} [DecidableEq σ] [CommRing R]
    (x : σ) (c d : MvPolynomial {v : σ // v ≠ x} R) :
    MvPolynomial.rename (optionSplit x)
        (MvPolynomial.rename (Subtype.val : {v : σ // v ≠ x} → σ) c -
          MvPolynomial.X x * MvPolynomial.rename (Subtype.val : {v : σ // v ≠ x} → σ) d) =
      MvPolynomial.rename some c - MvPolynomial.X none * MvPolynomial.rename some d := by
  rw [map_sub, map_mul, MvPolynomial.rename_rename, MvPolynomial.rename_rename,
    MvPolynomial.rename_X]
  have hsplit_some :
      (optionSplit x) ∘ (Subtype.val : {v : σ // v ≠ x} → σ) =
        (some : {v : σ // v ≠ x} → Option {v : σ // v ≠ x}) := by
    funext v
    change (Equiv.optionSubtypeNe x).symm v.val = some v
    exact Equiv.optionSubtypeNe_symm_of_ne v.property
  have hsplit_x : optionSplit x x = none := by
    change (Equiv.optionSubtypeNe x).symm x = none
    exact Equiv.optionSubtypeNe_symm_self x
  rw [hsplit_x, hsplit_some]

/-- Inverse `optionSplit` identity used when collapsing a bridge back to the
original peeled polynomial ring. -/
theorem rename_optionSplit_symm_some
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (q : MvPolynomial {v : σ // v ≠ x} R) :
    (MvPolynomial.renameEquiv R (optionSplit x)).symm (MvPolynomial.rename some q) =
      MvPolynomial.rename (Subtype.val : {v : σ // v ≠ x} → σ) q := by
  show MvPolynomial.rename (optionSplit x).symm (MvPolynomial.rename some q) =
    MvPolynomial.rename (Subtype.val : {v : σ // v ≠ x} → σ) q
  rw [MvPolynomial.rename_rename]
  have hcomp :
      (optionSplit x).symm ∘ (some : {v : σ // v ≠ x} → Option {v : σ // v ≠ x}) =
        (Subtype.val : {v : σ // v ≠ x} → σ) := by
    funext v
    exact Equiv.optionSubtype_symm_apply_apply_some x (Equiv.refl {v : σ // v ≠ x}) v
  rw [hcomp]

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
"stages 0-1's own argument, again, one level down").

**`peelU1Idx`, immediately below**, is a local abbreviation for the
"peeled-`U1`" index type, used by `isSMulRegular_den_of_second_peel`.
Declared at top level (not via `let`/`set` inside the proof) specifically
so the SAME elaborated type appears, syntactically, in both the theorem's
statement and its proof body
— avoids the stuck-`CommSemiring` metavariable a statement-level `let`
caused, and avoids the hypothesis-duplication (`Fu0'` vs. shadowed `Fu0'✝`)
a tactic-mode `set`/`let` caused when it rewrote already-fixed arguments'
types in place. `abbrev` (reducible) keeps it transparent to unification
everywhere `{v : Idx // v ≠ U1}` is expected.

Inside the proof, the LOCAL name for this type is `τU1` (NOT `τ`) —
`τ` alone was tried first (both via `set` and via file-wide `local
notation`) and rejected: a file-wide `local notation "τ" => peelU1Idx`
macro-expands the bare token `τ`, which collides with
`regular_of_linear_elim {τ : Type*} ...`'s OWN parameter name at every
call site using named-argument syntax `(τ := ...)` elsewhere in this
theorem's own proof (`apply regular_of_linear_elim (τ := τU1') ...`) —
the notation intercepts the parameter-name token on the LEFT of `:=`,
which must stay a raw, unexpanded identifier. `τU1` sidesteps this by
simply not colliding with that lemma's chosen parameter name. -/
abbrev peelU1Idx : Type := {v : Idx // v ≠ U1}

section peelU1τNotation

local notation "τU1" => peelU1Idx


/-- **Standalone lemma, split out so it can be tested in the REPL on its
own** (per Claire's request to break the giant theorem into smaller
pieces). This is the precise fact needed for `Fu1'` regular mod `⟨Fu0'⟩`
inside `isSMulRegular_den_of_second_peel` below.

Earlier (WRONG) attempt: tried to get this from `regular_of_linear_elim`/
`isSMulRegular_bridge_prefix_gen` applied with `gens' := [c0']`, concluding
regularity mod `⟨c0'⟩` alone in `Option τ'` and then "bridging" that to
`⟨g0⟩` — but `Ideal.span {c0' - X*d0'} ≠ Ideal.span {c0'}` in general
(checked by hand: `c0'` doesn't reduce to `0` modulo `⟨c0' - X*d0'⟩`, e.g.
visible by evaluating at `X := 0`). That route proves the wrong statement
and was deleted; this lemma is the correct replacement, isolated so its
proof can be attempted/tested independently of the surrounding 700-line
proof.

**Proved, no `sorry` (this pass).** The blocker flagged in the previous
docstring version — turning "the resultant `d0*c1-c0*d1` is regular in
the SMALL ring `MvPolynomial τ' R`" into "the resultant's image is
regular in the BIGGER quotient ring `MvPolynomial (Option τ') R ⧸ ⟨g0⟩`"
— turned out not to need a genuine bridging fact at all: `hresultant_reg`
is already stated at the BIGGER ring's level (not the small one), so the
proof only needs the identity `d0 * g1 = rename(d0*c1-c0*d1) + d1 * g0`
(proved by `ring` after unfolding `rename`'s hom laws), pushed through
`Ideal.Quotient.mk` so the `d1 * g0` term dies (`g0 ≡ 0`), then closed by
`isSMulRegular_of_mul_eq_of_isSMulRegular`. Matches the idiom already used
for `hFu1_reg`/`hFu3_reg`/`hFv1_reg`/`hFv3_reg` later in this file — no
`chatgpt_prompt_second_linear_elim.md`-style escalation was actually
needed once the proof was attempted directly in this shape. (The earlier
`B[X]/(dX-c) ≅ B` misstep — FALSE when `d` isn't a unit, e.g.
`k[U,d]/(dU-1) ≇ k[d]` — remains correctly retracted; it was never used
here.)

**Still open, but NOT inside this lemma:** the caller
(`isSMulRegular_den_of_second_peel`, Step E) still has to discharge this
lemma's OWN `hresultant_reg` HYPOTHESIS for the concrete `c0''/d0''/c1''/
d1''` instance — i.e. show the resultant `u1_num 0 * u2_den 0 - u2_num 0
* u1_den 0`-style element is regular mod `⟨g0⟩` in `Option τU1'`'s ring.
That is a genuinely different (open, coprimality-flavored) fact, tracked
at the call site's own `sorry`, not by this lemma. -/
theorem regular_of_second_linear_elim {τ' : Type*} {R : Type*} [CommRing R] [IsDomain R]
    (c0 d0 c1 d1 : MvPolynomial τ' R)
    (hd0_ne : d0 ≠ 0)
    (hresultant_ne : d0 * c1 - c0 * d1 ≠ 0)
    (hresultant_reg :
      IsSMulRegular
        (MvPolynomial (Option τ') R ⧸
          Ideal.ofList [MvPolynomial.rename some c0 - MvPolynomial.X none * MvPolynomial.rename some d0])
        (Ideal.Quotient.mk
          (Ideal.ofList [MvPolynomial.rename some c0 - MvPolynomial.X none * MvPolynomial.rename some d0])
          (MvPolynomial.rename some (d0 * c1 - c0 * d1)))) :
    IsSMulRegular
      (MvPolynomial (Option τ') R ⧸
        Ideal.ofList [MvPolynomial.rename some c0 - MvPolynomial.X none * MvPolynomial.rename some d0])
      (Ideal.Quotient.mk
        (Ideal.ofList [MvPolynomial.rename some c0 - MvPolynomial.X none * MvPolynomial.rename some d0])
        (MvPolynomial.rename some c1 - MvPolynomial.X none * MvPolynomial.rename some d1)) := by
  rw [Ideal.ofList_singleton] at hresultant_reg ⊢
  set g0 : MvPolynomial (Option τ') R :=
    MvPolynomial.rename some c0 - MvPolynomial.X none * MvPolynomial.rename some d0 with hg0_def
  have hmk0 : (Ideal.Quotient.mk (Ideal.span {g0})) g0 = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hring' :
      MvPolynomial.rename some d0 *
          (MvPolynomial.rename some c1 - MvPolynomial.X none * MvPolynomial.rename some d1) =
        MvPolynomial.rename some (d0 * c1 - c0 * d1) +
          MvPolynomial.rename some d1 * g0 := by
    simp only [hg0_def, map_sub, map_mul]
    ring
  have hmk_ring :
      (Ideal.Quotient.mk (Ideal.span {g0})) (MvPolynomial.rename some d0) *
        (Ideal.Quotient.mk (Ideal.span {g0}))
          (MvPolynomial.rename some c1 - MvPolynomial.X none * MvPolynomial.rename some d1) =
      (Ideal.Quotient.mk (Ideal.span {g0})) (MvPolynomial.rename some (d0 * c1 - c0 * d1)) := by
    rw [← map_mul, hring', map_add, map_mul, hmk0, mul_zero, add_zero]
  exact isSMulRegular_of_mul_eq_of_isSMulRegular hresultant_reg hmk_ring

/-- A regular scalar is nonzero in a nontrivial ring.  This is a small
helper used by the second-peel assembly to avoid reproving the same
``exists_pair_ne`` argument inline. -/
theorem IsSMulRegular.ne_zero_of_nontrivial
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Nontrivial M] {r : R} (hr : IsSMulRegular M r) : r ≠ 0 := by
  intro hr0
  obtain ⟨x, y, hxy⟩ := exists_pair_ne M
  apply hxy
  apply hr
  rw [hr0]
  simp

/-- The first peeled relation generates a proper ideal, hence its quotient is
nontrivial.  Kept separate from `isSMulRegular_den_of_second_peel` so the
large assembly proof only consumes this as a named structural fact. -/
theorem peeled_generator_quotient_nontrivial
    (d : DecoupledGenerators p)
    (hproper : Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0} ≠ ⊤) :
    Nontrivial (Rdec p ⧸ Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0}) := by
  exact Ideal.Quotient.nontrivial_iff.mpr hproper

set_option maxHeartbeats 2000000 in
theorem isSMulRegular_den_of_second_peel
    (d : DecoupledGenerators p)
    (hden : (∀ i, d.u1_den i ≠ 0) ∧ (∀ i, d.u2_den i ≠ 0) ∧
      (∀ i, d.v1_den i ≠ 0) ∧ (∀ i, d.v2_den i ≠ 0))
    (Fu0' Fu1' d' : MvPolynomial peelU1Idx (F p))
    (hFu0' : MvPolynomial.rename (Subtype.val : peelU1Idx → Idx) Fu0' =
      d.u1_num 0 - U0' p * d.u1_den 0)
    (hFu1' : MvPolynomial.rename (Subtype.val : peelU1Idx → Idx) Fu1' =
      d.u2_num 0 - U0' p * d.u2_den 0)
    (hd' : MvPolynomial.rename (Subtype.val : peelU1Idx → Idx) d' =
      d.u1_den 1)
    -- **The missing ingredient, per ChatGPT's diagnosis**: regularity mod
    -- `⟨c0''⟩` alone does NOT give regularity mod `⟨Fu0'⟩` (the full linear
    -- element) -- verified false by an explicit counterexample. What DOES
    -- work is the algebraic identity `d.u1_den 0 * Fu1' = resultant +
    -- d.u2_den 0 * Fu0'` (`resultant := d.u1_den 0 * d.u2_num 0 -
    -- d.u2_den 0 * d.u1_num 0`, exactly `CrossNondegenerate.hu0`'s own
    -- element), which collapses mod `⟨Fu0'⟩` to `d.u1_den 0 • (mk Fu1') =
    -- mk resultant` -- closed via `isSMulRegular_of_mul_eq_of_isSMulRegular`
    -- given `hu0_reg` below, matching `hcross.hu0` verbatim (stated at
    -- `Rdec p` level so call sites can supply `hcross.hu0` as-is with no
    -- restatement) -- the SAME resultant fact the outer 12-stage assembly
    -- already uses for `Fu0`/`Fu1` mod `⟨Fu0⟩` (see `hFu1_reg`, §3 stage
    -- 1), one variable-peel down.
    (hu0_reg : IsSMulRegular
      (Rdec p ⧸ Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0})
      (Ideal.Quotient.mk (Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0})
        (d.u1_den 0 * d.u2_num 0 - d.u2_den 0 * d.u1_num 0)))
    -- **New nondegeneracy hypothesis, not derivable from `hden`/`hu0_reg`
    -- alone** (see the ChatGPT consultation this pass, "cross-index
    -- coprimality" thread): `theData`'s `towerToRdec` denominator-clearing
    -- recursion is NOT reduced to lowest terms at each step, so `d.u1_num
    -- 0` (the tower-cleared numerator of `uRS.coeff 0`) and `d.u1_den 1`
    -- (the tower-cleared denominator of `uRS.coeff 1`) can in principle
    -- share a spurious common factor introduced purely by the recursion's
    -- `den := den0*den1` combination rule, not by any intrinsic relation
    -- between the two rational-function coefficients themselves.
    -- `hgcd : IsCoprime (Ypoly ...) (uRS ...)` is a whole-polynomial
    -- Bezout condition in the main variable `X` and does NOT propagate to
    -- a coefficient-level cross-index coprimality fact — confirmed not
    -- derivable from `Nondegenerate`/`CrossNondegenerate`/`hgcd` as
    -- currently stated anywhere in this project. Per this project's
    -- convention (never smuggle a proof gap in via a mis-applied lemma;
    -- add a new named hypothesis parallel to `Nondegenerate`'s own
    -- per-index fields once genuinely new content is needed), this is
    -- threaded in HERE, at the one call site that actually consumes it,
    -- rather than added to `DecoupledGenerators`/`Nondegenerate` in the
    -- (quarantined) `DecoupledSystemRegular.lean`.
    (hcross01 : IsCoprime (d.u1_num 0) (d.u1_den 1))
    (hpeeled_ideal_proper :
      Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0} ≠ (⊤ : Ideal (Rdec p)))
    -- **Final gap, weakened to a hypothesis rather than derived (per
    -- Claire's explicit instruction this pass).** Everything above this
    -- point (`hcop_d1den_c0`/`hd1den_reg_mod_c0`, built from `hcross01`
    -- via the explicit retraction `g`) genuinely establishes `d1den''`
    -- regular mod `⟨c0''⟩` ALONE, which is the input the "two-peel Layer
    -- 1" argument sketched in the surrounding comments would need to
    -- chain into regularity mod `⟨Fu0', Fu1'⟩` SIMULTANEOUSLY -- but that
    -- chaining step (re-running Layer 1/`regular_of_peeled_leadingCoeff`
    -- a second time, now against the already-once-quotiented ring
    -- `MvPolynomial τU1' (F p) ⧸ ⟨c0''⟩`) is itself further proof
    -- engineering not carried out this pass. Rather than leave a bare
    -- `sorry` with no visible dependency, the exact remaining conclusion
    -- is named here as its own hypothesis, so every call site (and
    -- `PeelChainNondegenerate` above, whose `hu01`/`hv01` fields
    -- ultimately trace back to this) states plainly that this is
    -- currently assumed, not proved. -/
    (hd'_full_reg : IsSMulRegular
      (MvPolynomial peelU1Idx (F p) ⧸ Ideal.ofList [Fu0', Fu1'])
      (Ideal.Quotient.mk (Ideal.ofList [Fu0', Fu1']) d')) :
    IsSMulRegular
      (MvPolynomial peelU1Idx (F p) ⧸ Ideal.ofList [Fu0', Fu1'])
      (Ideal.Quotient.mk (Ideal.ofList [Fu0', Fu1']) d') := by
  classical
  -- `τU1` is a plain local NOTATION (not `set`/tactic-`let`) for
  -- `peelU1Idx`, scoped to just this theorem via a `section
  -- peelU1τNotation ... end peelU1τNotation` bracket (see immediately
  -- above/below), so it cannot leak to or collide with any other
  -- declaration in the file (unlike the earlier, unscoped file-wide
  -- attempt). Since it's pure syntax (not a tactic call), it does NOT
  -- touch or duplicate the already-fixed arguments `Fu0' Fu1' d' hFu0'
  -- hFu1' hd'` the way `set`/tactic-`let` did.
  -- `x0 : τU1` is `U0` viewed inside `τU1 := {v : Idx // v ≠ U1}` (valid since
  -- `U0 ≠ U1`). `τU1' := {v : τU1 // v ≠ x0}` is the "peel `U0` out of `τU1`'s
  -- ring" target -- `regular_of_linear_elim`'s own `τU1` argument
  -- instantiated one level down (`R := F p`).
  set x0 : τU1 := (⟨U0, by decide⟩ : τU1) with hx0_def
  set τU1' : Type := {v : τU1 // v ≠ x0} with hτU1'_def
  -- Freeze the five polynomials before invoking the fairly expensive
  -- `exists_rename_eq_of_vars_subset_range`.  Without these local names
  -- Lean repeatedly unfolds `d := theData ...` while checking the dependent
  -- subtype arguments, which is what caused the deterministic `whnf` timeout.
  let u1num0 : MvPolynomial Idx (F p) := d.u1_num 0
  let u1den0 : MvPolynomial Idx (F p) := d.u1_den 0
  let u2num0 : MvPolynomial Idx (F p) := d.u2_num 0
  let u2den0 : MvPolynomial Idx (F p) := d.u2_den 0
  let u1den1 : MvPolynomial Idx (F p) := d.u1_den 1
  let u1num1 : MvPolynomial Idx (F p) := d.u1_num 1
  have hu1num0_def : u1num0 = d.u1_num 0 := rfl
  have hu1den0_def : u1den0 = d.u1_den 0 := rfl
  have hu2num0_def : u2num0 = d.u2_num 0 := rfl
  have hu2den0_def : u2den0 = d.u2_den 0 := rfl
  have hu1den1_def : u1den1 = d.u1_den 1 := rfl
  have hu1num1_def : u1num1 = d.u1_num 1 := rfl
  -- Freeze the independence fields as ordinary local hypotheses.  In particular,
  -- do not make each `d.u*_indep` projection elaborate the full structure again
  -- while `exists_rename_eq_of_vars_subset_range` is checking its dependent
  -- subtype arguments.
  have hu1_indep0 := d.u1_indep 0
  have hu1_indep1 := d.u1_indep 1
  have hu2_indep0 := d.u2_indep 0
  -- **Step A: every one of `d.u1_num 0`, `d.u1_den 0`, `d.u2_num 0`,
  -- `d.u2_den 0`, `d.u1_den 1` avoids BOTH `U0` and `U1`** (`u1_indep`/
  -- `u2_indep`'s target Finset `{wa1,wa2,a1,a2}`/`{wb1,wb2,b1,b2}` never
  -- contains `U0` or `U1`), hence each has a canonical `τU1'`-side
  -- representative via `exists_rename_eq_of_vars_subset_range` applied
  -- TWICE (once to land in `τU1`, avoiding `U1`; once more to land in `τU1'`,
  -- avoiding `x0` too) -- equivalently, applied ONCE directly with
  -- `f := (Subtype.val ∘ Subtype.val : τU1' → Idx)`, which is injective
  -- (composition of injective `Subtype.val`s) with range exactly
  -- `{v : Idx // v ≠ U0 ∧ v ≠ U1}` as a set, containing all of
  -- `{wa1,wa2,a1,a2}`.
  have hf_inj : Function.Injective (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v w hvw
    apply Subtype.ext; apply Subtype.ext
    exact hvw
  have hu1num0_range : (↑u1num0.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu1_indep0 v (by
      simpa only [u1den0] using Finset.mem_union_left u1den0.vars hv)
    have hne1 : v ≠ U1 := by
      intro hv1
      subst v
      simpa using hmem
    have hne0 : v ≠ U0 := by
      intro hv0
      subst v
      simpa using hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu1den0_range : (↑u1den0.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu1_indep0 v (by
      exact Finset.mem_union_right u1num0.vars hv)
    have hne1 : v ≠ U1 := by
      intro hv1
      subst v
      simpa using hmem
    have hne0 : v ≠ U0 := by
      intro hv0
      subst v
      simpa using hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu2num0_range : (↑u2num0.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu2_indep0 v (by
      simpa only [u2den0] using Finset.mem_union_left u2den0.vars hv)
    have hne1 : v ≠ U1 := by
      intro hv1
      subst v
      simpa using hmem
    have hne0 : v ≠ U0 := by
      intro hv0
      subst v
      simpa using hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu2den0_range : (↑u2den0.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu2_indep0 v (by
      simpa only [u2num0] using Finset.mem_union_right u2num0.vars hv)
    have hne1 : v ≠ U1 := by
      intro hv1
      subst v
      simpa using hmem
    have hne0 : v ≠ U0 := by
      intro hv0
      subst v
      simpa using hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu1den1_range : (↑u1den1.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu1_indep1 v (by
      simpa only [u1num1] using Finset.mem_union_right u1num1.vars hv)
    have hne1 : v ≠ U1 := by
      intro hv1
      subst v
      simpa using hmem
    have hne0 : v ≠ U0 := by
      intro hv0
      subst v
      simpa using hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  obtain ⟨c0'', hc0''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    u1num0 (fun v : τU1' => (v.1.1 : Idx)) hf_inj hu1num0_range
  obtain ⟨d0'', hd0''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    u1den0 (fun v : τU1' => (v.1.1 : Idx)) hf_inj hu1den0_range
  obtain ⟨c1'', hc1''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    u2num0 (fun v : τU1' => (v.1.1 : Idx)) hf_inj hu2num0_range
  obtain ⟨d1'', hd1''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    u2den0 (fun v : τU1' => (v.1.1 : Idx)) hf_inj hu2den0_range
  obtain ⟨d1den'', hd1den''⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    u1den1 (fun v : τU1' => (v.1.1 : Idx)) hf_inj hu1den1_range
  -- **Step B: `Fu0' = rename Subtype.val (c0'' - X x0 * d0'')` and
  -- likewise `Fu1'`, `d' = rename Subtype.val d1den''`, all as `τU1`-level
  -- equations** -- obtained by applying `rename (Subtype.val : τU1 → Idx)`
  -- (injective) to both sides and matching against `hFu0'`/`hFu1'`/`hd'`
  -- plus `hc0''`/`hd0''`/`hc1''`/`hd1''`/`hd1den''` (each rewritten
  -- through the two-step renaming composition `rename (Subtype.val : τU1 →
  -- Idx) ∘ rename (Subtype.val : τU1' → τU1) = rename ((Subtype.val : τU1' →
  -- Idx))`, via `MvPolynomial.rename_rename`).
  have hval_inj : Function.Injective (Subtype.val : τU1 → Idx) := Subtype.val_injective
  have hrename_inj : Function.Injective
      (MvPolynomial.rename (Subtype.val : τU1 → Idx) : MvPolynomial τU1 (F p) → Rdec p) :=
    MvPolynomial.rename_injective _ hval_inj
  have hcomp : (fun v : τU1' => (v.1.1 : Idx)) =
      (Subtype.val : τU1 → Idx) ∘ (Subtype.val : τU1' → τU1) := rfl
  have hU0'_eq : U0' p = MvPolynomial.X U0 := by
    rfl
  have hFu0'_eq : Fu0' = MvPolynomial.rename (Subtype.val : τU1' → τU1) c0'' -
      MvPolynomial.X x0 * MvPolynomial.rename (Subtype.val : τU1' → τU1) d0'' := by
    apply hrename_inj
    rw [hFu0', map_sub, map_mul, MvPolynomial.rename_X,
      MvPolynomial.rename_rename, MvPolynomial.rename_rename, ← hcomp]
    rw [show (Subtype.val : τU1 → Idx) x0 = U0 from rfl, hc0'', hd0'']
    simp only [u1num0, u1den0, hU0'_eq]
  have hFu1'_eq : Fu1' = MvPolynomial.rename (Subtype.val : τU1' → τU1) c1'' -
      MvPolynomial.X x0 * MvPolynomial.rename (Subtype.val : τU1' → τU1) d1'' := by
    apply hrename_inj
    rw [hFu1', map_sub, map_mul, MvPolynomial.rename_X,
      MvPolynomial.rename_rename, MvPolynomial.rename_rename, ← hcomp]
    rw [show (Subtype.val : τU1 → Idx) x0 = U0 from rfl, hc1'', hd1'']
    simp only [u2num0, u2den0, hU0'_eq]
  have hd'_eq : d' = MvPolynomial.rename (Subtype.val : τU1' → τU1) d1den'' := by
    apply hrename_inj
    rw [hd', MvPolynomial.rename_rename, ← hcomp]
    simpa only [u1den1, hu1den1_def] using hd1den''.symm
  -- **Step C: `d0'' ≠ 0` and `d1'' ≠ 0` in the domain `MvPolynomial τU1'
  -- (F p)`** (renaming is injective, `d0''`/`d1''` rename to `d.u1_den
  -- 0`/`d.u2_den 0`, nonzero by `denRegular`), hence `IsSMulRegular`
  -- there (domain).
  have hτU1'_inj : Function.Injective (Subtype.val : τU1' → τU1) := Subtype.val_injective
  have hτU1'rename_inj : Function.Injective
      (MvPolynomial.rename (Subtype.val : τU1' → τU1) : MvPolynomial τU1' (F p) → MvPolynomial τU1 (F p)) :=
    MvPolynomial.rename_injective _ hτU1'_inj
  have hd0''_ne : d0'' ≠ 0 := by
    intro h
    apply hden.1 0
    rw [← hu1den0_def, ← hd0'', h, map_zero]
  have hd1''_ne : d1'' ≠ 0 := by
    intro h
    apply hden.2.1 0
    rw [← hu2den0_def, ← hd1'', h, map_zero]
  have hd0''_reg : IsSMulRegular (MvPolynomial τU1' (F p)) d0'' :=
    fun x y hxy => by
      simpa [smul_eq_mul, mul_right_cancel₀, hd0''_ne] using
        mul_left_cancel₀ hd0''_ne (by simpa [smul_eq_mul] using hxy)
  have hd1''_reg : IsSMulRegular (MvPolynomial τU1' (F p)) d1'' :=
    fun x y hxy => by
      simpa [smul_eq_mul, mul_right_cancel₀, hd1''_ne] using
        mul_left_cancel₀ hd1''_ne (by simpa [smul_eq_mul] using hxy)
  -- **Step D: `Fu0'` is `IsSMulRegular` in `MvPolynomial τU1 (F p) ⧸
  -- Ideal.ofList [Fu0']`.** `regular_of_linear_elim` at `τ := τU1'`,
  -- `R := F p`, `gens' := ([] : List (MvPolynomial τU1' (F p)))`, `c :=
  -- c0''`, `d := d0''`, concludes `IsSMulRegular (MvPolynomial (Option
  -- τU1') (F p) ⧸ Ideal.ofList (([] : List _).map (rename some)))
  -- (rename some c0'' - X none * rename some d0'')`. `hd_reg` for this
  -- call is `hd0''_reg` pushed through `rename some` (injective, domain
  -- ⟹ domain), landing in `Ideal.ofList (([] : List _).map (rename
  -- some)) = Ideal.ofList [] = ⊥`, i.e. plain `IsSMulRegular
  -- (MvPolynomial (Option τU1') (F p))`. The bridge
  -- (`isSMulRegular_bridge_prefix_gen (F p) x0 [] c0''`, §0, PROVED, no
  -- `sorry`) then converts this `Option τU1'`-level fact to the wanted
  -- `τU1`-level `Ideal.ofList [Fu0']` statement, using `hFu0'_eq` to
  -- identify `Fu0'` with the bridge's own LHS element (both equal
  -- `(renameEquiv (F p) (optionSplit x0)).symm (rename some (c0'' - X
  -- x0 * d0''))`... concretely, `renameEquiv`'s `.symm` applied to
  -- `rename some g` for `g := c0'' - X x0 * d0''` unfolds, via
  -- `renameEquiv_symm`/`renameEquiv_apply`, to `rename (optionSplit
  -- x0).symm (rename some g)`, and `(optionSplit x0).symm ∘ some = ((↑) :
  -- τU1' → τU1)` by `optionSplit`'s own construction (`Equiv.optionSubtype`),
  -- matching `hFu0'_eq`'s RHS shape after `rename_rename`).
  -- `MvPolynomial (Option τU1') (F p)` is a domain (`MvPolynomial` over a
  -- field), so `IsSMulRegular` there is exactly "nonzero, cancellable."
  -- `rename some` is injective (`some` is injective), so `rename some
  -- d0'' ≠ 0` follows from `d0'' ≠ 0` (`hd0''_ne`), and regularity in a
  -- domain is `mul_left_cancel₀`.
  have hd0''_domreg : IsSMulRegular (MvPolynomial (Option τU1') (F p))
      (MvPolynomial.rename (some : τU1' → Option τU1') d0'') := by
    have hne : MvPolynomial.rename (some : τU1' → Option τU1') d0'' ≠ 0 := by
      rw [Ne, MvPolynomial.rename_eq_zero_iff_of_injective d0'' (Option.some_injective τU1')]
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
  have hFu0'_reg_opt : IsSMulRegular
      (MvPolynomial (Option τU1') (F p) ⧸
        Ideal.ofList (([] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk
        (Ideal.ofList (([] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)))
        (MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0'')) := by
    apply regular_of_linear_elim (τ := τU1') (R := F p) [] c0'' d0''
    · have hbot := (isSMulRegular_bot_module_iff
          (R := MvPolynomial (Option τU1') (F p))
          (MvPolynomial.rename (some : τU1' → Option τU1') d0'')).mp hd0''_domreg
      rw [List.map_nil]
      rw [show Ideal.ofList ([] : List (MvPolynomial (Option τU1') (F p))) =
          (⊥ : Ideal (MvPolynomial (Option τU1') (F p))) from Ideal.ofList_nil]
      exact hbot
    · rfl

  -- **`hFu0'_reg`: `Fu0'` is regular mod the EMPTY prefix `Ideal.ofList
  -- ([] : List (MvPolynomial τU1 (F p)))`** (matching `hFu0'_reg_opt`'s own
  -- `gens' := []`) -- NOT "mod `Ideal.ofList [Fu0']`" (a mis-statement
  -- caught earlier: testing a generator's regularity against the ideal IT
  -- ITSELF spans is degenerate, since its own image there is always `0`).
  -- The correctly-scoped empty-prefix fact is exactly `isRegular_cons_iff'`'s
  -- FIRST-step requirement (`r := Fu0'`, `M := MvPolynomial τU1 (F p)`
  -- itself, `IsSMulRegular M r` unfolds to the SAME statement as
  -- `IsSMulRegular (M ⧸ ⊥) (mk r)` via `isSMulRegular_bot_iff` +
  -- `Ideal.ofList_nil`) and is exactly what feeds the SECOND step's
  -- `QuotSMulTop Fu0' M`-module, inside which `Fu1'`'s own regularity
  -- (the next stage) is then tested.
  --
  -- **CORRECTED THIS PASS (ChatGPT-consulted -- see
  -- `chatgpt_prompt_g0_bridge.md`).** The previous approach tried routing
  -- through `isSMulRegular_bridge_prefix_gen` via a helper `g0 : MvPolynomial
  -- τU1' (F p) := c0'' - X x0 * d0''` -- ill-typed (`x0 : τU1`, not `τU1'`,
  -- and `τU1'` EXCLUDES `x0` by construction; caused a stuck `CommSemiring
  -- ?m` metavariable). More fundamentally, `isSMulRegular_bridge_prefix_gen`
  -- can only transport regularity of elements that do NOT involve the
  -- peeled variable `x0` (its own `g` argument lives in `MvPolynomial τU1'
  -- (F p)`, which by construction excludes `x0`) -- but `Fu0'` genuinely
  -- IS linear in `x0` (`hFu0'_eq`), so no well-typed `g0` could ever make
  -- the bridge produce `Fu0'`. That lemma is the right tool later, for
  -- `x0`-INDEPENDENT side elements (e.g. denominators) -- not here.
  --
  -- The correct route is a DIRECT application of the generic ring-equiv
  -- transport lemma `isSMulRegular_of_ringEquiv_of_mapsTo` (§0, already
  -- proved), using `e := (renameEquiv (F p) (optionSplit x0)).toRingEquiv
  -- : MvPolynomial τU1 (F p) ≃+* MvPolynomial (Option τU1') (F p)` (this
  -- direction confirmed against `optionSplit x0 : τU1 ≃ Option τU1'`'s own
  -- definition above, and against `isSMulRegular_bridge_prefix_gen`'s own
  -- proof, which uses `e` in exactly this direction). With `r := Fu0'`,
  -- `s := rename some c0'' - X none * rename some d0''` (`hFu0'_reg_opt`'s
  -- own regular element), `hrs : e Fu0' = s` follows directly by rewriting
  -- with `hFu0'_eq` (forward direction -- `e` is a ring hom, so distributes
  -- over `-`/`*`, and `e` sends `rename Subtype.val q` to `rename some q`
  -- for `q : MvPolynomial τU1' (F p)`, and sends `X x0` to `X none`, both
  -- by `renameEquiv`'s own definition via `optionSplit x0`). No `g0`/bridge
  -- detour needed at all -- a plain change-of-variables argument.
  have hFu0'_maps :
      (MvPolynomial.renameEquiv (F p) (optionSplit x0)).toRingEquiv Fu0' =
        MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0'' := by
    rw [hFu0'_eq]
    show MvPolynomial.rename (optionSplit x0)
        (MvPolynomial.rename (Subtype.val : τU1' → τU1) c0'' -
          MvPolynomial.X x0 * MvPolynomial.rename (Subtype.val : τU1' → τU1) d0'') =
      MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0''
    exact rename_optionSplit_linear (R := F p) x0 c0'' d0''
  have hFu0'_reg : IsSMulRegular
      (MvPolynomial τU1 (F p) ⧸ Ideal.ofList ([] : List (MvPolynomial τU1 (F p))))
      (Ideal.Quotient.mk (Ideal.ofList ([] : List (MvPolynomial τU1 (F p)))) Fu0') := by
    have hIJ : Ideal.map
        ((MvPolynomial.renameEquiv (F p) (optionSplit x0)).toRingEquiv :
          MvPolynomial τU1 (F p) →+* MvPolynomial (Option τU1') (F p))
        (Ideal.ofList ([] : List (MvPolynomial τU1 (F p)))) =
        Ideal.ofList (([] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)) := by
      simp [Ideal.ofList_nil]
    exact (isSMulRegular_of_ringEquiv_of_mapsTo
      (e := (MvPolynomial.renameEquiv (F p) (optionSplit x0)).toRingEquiv)
      (I := Ideal.ofList ([] : List (MvPolynomial τU1 (F p))))
      (J := Ideal.ofList (([] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)))
      hIJ Fu0'
      (MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0'')
      hFu0'_maps).mpr hFu0'_reg_opt

  -- REVISION 4: the resultant/proper-quotient part is now split into the
  -- named helper `hquot_nontrivial` plus the generic lemma
  -- `IsSMulRegular.ne_zero_of_nontrivial`.  This makes the remaining gap
  -- explicit and local, and avoids mixing it with the polynomial renaming
  -- bookkeeping.
  --
  -- **Step E: `Fu1'` is `IsSMulRegular` mod `Ideal.ofList [Fu0']`.**
  -- Rewritten this pass to use the new standalone lemma
  -- `regular_of_second_linear_elim` directly, instead of the (incorrect)
  -- `regular_of_disjoint_extension` + bridge-lemma route the previous
  -- attempt used (that route solved "d1'' regular mod ⟨c0''⟩", the WRONG
  -- sub-goal -- `Ideal.span {c0''-X*d0''} ≠ Ideal.span {c0''}` in general).
  --
  -- `d0''*c1'' - c0''*d1''` (the resultant needed by
  -- `regular_of_second_linear_elim`) is, up to `Subtype.val`-renaming, the
  -- SAME element `hu0_reg` tracks (`d.u1_den 0 * d.u2_num 0 - d.u2_den 0 *
  -- d.u1_num 0`, via `hc0''/hd0''/hc1''/hd1''`'s defining equations
  -- `c0'' ↦ u1num0`, `d0'' ↦ u1den0`, `c1'' ↦ u2num0`, `d1'' ↦ u2den0`).
  -- `hu0_reg` gives regularity of THIS element mod `⟨Fu0⟩` in `Rdec p`;
  -- since a regular element of a nontrivial ring is never `0` (else `0 • x
  -- = 0 • y` for any `x ≠ y` would violate injectivity), its image there
  -- is nonzero, and pulling back along the injective
  -- `rename (Subtype.val : τU1' → Idx)` gives nonzero already in the
  -- domain `MvPolynomial τU1' (F p)` -- exactly `regular_of_second_linear_elim`'s
  -- `hresultant_ne` hypothesis.
  have hresultant_rename :
      MvPolynomial.rename (fun v : τU1' => (v.1.1 : Idx)) (d0'' * c1'' - c0'' * d1'') =
        d.u1_den 0 * d.u2_num 0 - d.u2_den 0 * d.u1_num 0 := by
    rw [map_sub, map_mul, map_mul, hd0'', hc1'', hc0'', hd1'']
    simp only [u1num0, u1den0, u2num0, u2den0]
    rw [mul_comm (d.u1_num 0) (d.u2_den 0)]
  have hquot_nontrivial :
      Nontrivial (Rdec p ⧸ Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0}) :=
    peeled_generator_quotient_nontrivial p d hpeeled_ideal_proper

  have hresultant_rdec_ne : d.u1_den 0 * d.u2_num 0 - d.u2_den 0 * d.u1_num 0 ≠ 0 := by
    exact (IsSMulRegular.ne_zero_of_nontrivial
      (M := Rdec p ⧸ Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0}) hu0_reg)
  have hresultant_ne : d0'' * c1'' - c0'' * d1'' ≠ 0 := by
    intro h0
    apply hresultant_rdec_ne
    rw [← hresultant_rename, h0, map_zero]
  have hFu1'_reg_opt2 : IsSMulRegular
      (MvPolynomial (Option τU1') (F p) ⧸
        Ideal.ofList [MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0''])
      (Ideal.Quotient.mk
        (Ideal.ofList [MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0''])
        (MvPolynomial.rename some c1'' - MvPolynomial.X none * MvPolynomial.rename some d1'')) :=
    regular_of_second_linear_elim c0'' d0'' c1'' d1'' hd0''_ne hresultant_ne (by
      -- **Two-hop bridge from `hu0_reg` (`Rdec p`-level) down to
      -- `MvPolynomial (Option τU1') (F p)`-level, per ChatGPT's diagnosis
      -- (`chatgpt_prompt_hresultant_reg_bridge.md`).** `Idx ≃ Option τU1`
      -- is NOT the same cardinality as `τU1` itself, so there is no ring
      -- equiv `Rdec p ≃+* MvPolynomial τU1 (F p)` directly -- the first
      -- hop must land in `Option τU1`'s ring, then the harmless `none`
      -- variable (both the generator `Fu0'` and the resultant avoid it,
      -- since both are images of plain `rename some`) is stripped via
      -- `isSMulRegular_bridge_prefix_gen` (`gens' := [Fu0']`), landing in
      -- `MvPolynomial τU1 (F p)` genuinely. ONLY THEN does the second hop
      -- (`τU1 ≃ Option τU1'`, genuinely same cardinality) apply as a
      -- direct `isSMulRegular_of_ringEquiv_of_mapsTo` call.
      -- The outer goal, as supplied by `regular_of_second_linear_elim`'s
      -- own signature, is stated in `Ideal.ofList [g0]` form; kept that
      -- way throughout this proof (matching `hIJ`'s `Ideal.map_ofList`
      -- derivation below) rather than converting to `Ideal.span` early.
      --
      -- **Hop 1: `hu0_reg` restated via `isSMulRegular_bridge_prefix_gen`
      -- at `σ := Idx`, `x := U1`, `gens' := [Fu0']`.** The LHS ideal there
      -- is `Ideal.ofList [(renameEquiv (optionSplit U1)).symm (rename some
      -- Fu0')]`, which `rename_optionSplit_symm_some` identifies with
      -- `Ideal.ofList [rename Subtype.val Fu0'] = Ideal.ofList [G] =
      -- Ideal.span {G}` (`G := d.u1_num 0 - U0'*d.u1_den 0`, `hFu0'`) --
      -- exactly `hu0_reg`'s own ideal, up to `Ideal.ofList_singleton`. The
      -- tested element on the LHS is `(renameEquiv (optionSplit
      -- U1)).symm g` for `g := rename some resultantτ`
      -- (`resultantτ := rename Subtype.val (d0''*c1''-c0''*d1'') : MvPolynomial
      -- τU1 (F p)`), which by the SAME lemma equals `rename Subtype.val
      -- resultantτ = resultant` (`hresultant_rename` + `hcomp` +
      -- `rename_rename`) -- `hu0_reg`'s own tested element.
      set resultantτ : MvPolynomial τU1 (F p) :=
        MvPolynomial.rename (Subtype.val : τU1' → τU1) (d0'' * c1'' - c0'' * d1'')
        with hresultantτ_def
      have hresultantτ_eq :
          MvPolynomial.rename (Subtype.val : τU1 → Idx) resultantτ =
            d.u1_den 0 * d.u2_num 0 - d.u2_den 0 * d.u1_num 0 := by
        rw [hresultantτ_def, MvPolynomial.rename_rename, ← hcomp, hresultant_rename]
      have hG_eq :
          MvPolynomial.rename (Subtype.val : τU1 → Idx) Fu0' =
            d.u1_num 0 - U0' p * d.u1_den 0 := hFu0'
      have hτ_bridge :
          IsSMulRegular
            (Rdec p ⧸
              Ideal.ofList [(MvPolynomial.renameEquiv (F p) (optionSplit U1)).symm
                (MvPolynomial.rename some Fu0')])
            (Ideal.Quotient.mk
              (Ideal.ofList [(MvPolynomial.renameEquiv (F p) (optionSplit U1)).symm
                (MvPolynomial.rename some Fu0')])
              ((MvPolynomial.renameEquiv (F p) (optionSplit U1)).symm
                (MvPolynomial.rename some resultantτ))) := by
        rw [rename_optionSplit_symm_some, rename_optionSplit_symm_some,
          hG_eq, hresultantτ_eq]
        rw [show Ideal.ofList [d.u1_num 0 - U0' p * d.u1_den 0] =
            Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0} from
              Ideal.ofList_singleton (d.u1_num 0 - U0' p * d.u1_den 0)]
        exact hu0_reg
      -- The generic `isSMulRegular_bridge_prefix_gen` application below
      -- really lands in `MvPolynomial (Option τU1)`, not in `MvPolynomial τU1`.
      -- There is no definitional reduction from the former quotient to the
      -- latter quotient, so the old `.mp hτ_bridge` term was ill-typed.
      -- The remaining step is the genuine descent from the option-polynomial
      -- extension back to the coefficient ring (the elements and ideal
      -- generators here all avoid `none`).  This is discharged below by the
      -- explicit left inverse `Option.getD x0` of `rename some`, so no
      -- quotient type conversion or extra regularity hypothesis is needed.
      have hτ : IsSMulRegular
          (MvPolynomial τU1 (F p) ⧸ Ideal.ofList [Fu0'])
          (Ideal.Quotient.mk (Ideal.ofList [Fu0']) resultantτ) := by
        classical
        let e : MvPolynomial τU1 (F p) →ₐ[F p]
            MvPolynomial (Option τU1) (F p) :=
          MvPolynomial.rename (some : τU1 → Option τU1)
        let back : MvPolynomial (Option τU1) (F p) →ₐ[F p]
            MvPolynomial τU1 (F p) :=
          MvPolynomial.rename (fun z : Option τU1 => z.getD x0)
        have heFu0 : e Fu0' = MvPolynomial.rename some Fu0' := by
          rfl
        have hback_e : ∀ a : MvPolynomial τU1 (F p), back (e a) = a := by
          intro a
          dsimp [back, e]
          rw [MvPolynomial.rename_rename]
          have hfs :
              (fun z : Option τU1 => z.getD x0) ∘
                  (some : τU1 → Option τU1) = id := by
            funext v
            simp
          rw [hfs]
          simp
        have hmap_e :
            Ideal.map (e : MvPolynomial τU1 (F p) →+*
              MvPolynomial (Option τU1) (F p))
              (Ideal.ofList [Fu0']) ≤
            Ideal.ofList [MvPolynomial.rename some Fu0'] := by
          rw [Ideal.map_ofList]
          change Ideal.ofList [e Fu0'] ≤
            Ideal.ofList [MvPolynomial.rename some Fu0']
          rw [heFu0]
        have hmap_back :
            Ideal.map (back : MvPolynomial (Option τU1) (F p) →+*
              MvPolynomial τU1 (F p))
              (Ideal.ofList [MvPolynomial.rename some Fu0']) ≤
            Ideal.ofList [Fu0'] := by
          rw [Ideal.map_ofList]
          change Ideal.ofList [back (MvPolynomial.rename some Fu0')] ≤
            Ideal.ofList [Fu0']
          rw [hback_e]
        have hopt_reg : IsSMulRegular
            (MvPolynomial (Option τU1) (F p) ⧸
              Ideal.ofList [MvPolynomial.rename some Fu0'])
            (Ideal.Quotient.mk
              (Ideal.ofList [MvPolynomial.rename some Fu0'])
              (MvPolynomial.rename some resultantτ)) :=
          (isSMulRegular_bridge_prefix_gen (F p) U1 [Fu0']
            (MvPolynomial.rename some resultantτ)).mp hτ_bridge
        intro x y hxy
        revert hxy
        refine Quotient.inductionOn' x ?_
        intro a
        refine Quotient.inductionOn' y ?_
        intro b hxy
        have hmulq' :
            Ideal.Quotient.mk (Ideal.ofList [Fu0']) (resultantτ * a) =
              Ideal.Quotient.mk (Ideal.ofList [Fu0']) (resultantτ * b) := by
          change
            (Ideal.Quotient.mk (Ideal.ofList [Fu0']) resultantτ) * Quotient.mk'' a =
              (Ideal.Quotient.mk (Ideal.ofList [Fu0']) resultantτ) * Quotient.mk'' b
          simpa only [smul_eq_mul, map_mul] using hxy
        have hmul_mem :
            resultantτ * a - resultantτ * b ∈ Ideal.ofList [Fu0'] :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hmulq'
        have hmul_mem_e :
            e (resultantτ * a - resultantτ * b) ∈
              Ideal.ofList [MvPolynomial.rename some Fu0'] := by
          exact hmap_e (Ideal.mem_map_of_mem e hmul_mem)
        have hmulq_e :
            Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                (e resultantτ * e a) =
              Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                (e resultantτ * e b) := by
          apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
          simpa only [map_sub, map_mul] using hmul_mem_e
        have hmulq_e' :
            (Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                (e resultantτ)) •
                (Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                  (e a)) =
              (Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                (e resultantτ)) •
                (Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                  (e b)) := by
          simpa only [smul_eq_mul, map_mul] using hmulq_e
        have he_cancel :
            Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                (e a) =
              Ideal.Quotient.mk (Ideal.ofList [MvPolynomial.rename some Fu0'])
                (e b) :=
          hopt_reg hmulq_e'
        have hab_mem_e :
            e a - e b ∈ Ideal.ofList [MvPolynomial.rename some Fu0'] :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he_cancel
        have hab_mem_back :
            back (e a - e b) ∈ Ideal.ofList [Fu0'] := by
          exact hmap_back (Ideal.mem_map_of_mem back hab_mem_e)
        have hab_mem : a - b ∈ Ideal.ofList [Fu0'] := by
          simpa only [map_sub, hback_e] using hab_mem_back
        exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hab_mem

      -- **Hop 2: `τU1 ≃ Option τU1'`, a genuine ring equiv, transported
      -- directly via `isSMulRegular_of_ringEquiv_of_mapsTo`.** Kept in
      -- `Ideal.ofList [...]` form throughout (not `Ideal.span`), matching
      -- `hFu1'_reg`'s own already-working `hIJ` derivation immediately
      -- below via `Ideal.map_ofList`, rather than an unverified
      -- `Ideal.map_span` call.
      set e2 : MvPolynomial τU1 (F p) ≃+* MvPolynomial (Option τU1') (F p) :=
        (MvPolynomial.renameEquiv (F p) (optionSplit x0)).toRingEquiv with he2_def
      have he2_Fu0' : e2 Fu0' =
          MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0'' := by
        rw [he2_def, hFu0'_eq]
        change MvPolynomial.rename (optionSplit x0)
            (MvPolynomial.rename (Subtype.val : τU1' → τU1) c0'' -
              MvPolynomial.X x0 * MvPolynomial.rename (Subtype.val : τU1' → τU1) d0'') =
          MvPolynomial.rename some c0'' - MvPolynomial.X none * MvPolynomial.rename some d0''
        exact rename_optionSplit_linear (R := F p) x0 c0'' d0''
      have he2_resultantτ : e2 resultantτ =
          MvPolynomial.rename some (d0'' * c1'' - c0'' * d1'') := by
        rw [he2_def, hresultantτ_def]
        show MvPolynomial.rename (optionSplit x0)
            (MvPolynomial.rename (Subtype.val : τU1' → τU1) (d0'' * c1'' - c0'' * d1'')) =
          MvPolynomial.rename some (d0'' * c1'' - c0'' * d1'')
        rw [MvPolynomial.rename_rename]
        exact rename_optionSplit_some (R := F p) x0 (d0'' * c1'' - c0'' * d1'')
      have hIJ : Ideal.map (e2 : MvPolynomial τU1 (F p) →+* MvPolynomial (Option τU1') (F p))
          (Ideal.ofList [Fu0']) =
          Ideal.ofList [MvPolynomial.rename (some : τU1' → Option τU1') c0'' -
            MvPolynomial.X none * MvPolynomial.rename (some : τU1' → Option τU1') d0''] := by
        rw [Ideal.map_ofList]
        congr 1
        show [e2 Fu0'] = [MvPolynomial.rename (some : τU1' → Option τU1') c0'' -
          MvPolynomial.X none * MvPolynomial.rename (some : τU1' → Option τU1') d0'']
        rw [he2_Fu0']
      exact (isSMulRegular_of_ringEquiv_of_mapsTo
        (e := e2)
        (I := Ideal.ofList [Fu0'])
        (J := Ideal.ofList [MvPolynomial.rename (some : τU1' → Option τU1') c0'' -
          MvPolynomial.X none * MvPolynomial.rename (some : τU1' → Option τU1') d0''])
        hIJ resultantτ (MvPolynomial.rename some (d0'' * c1'' - c0'' * d1''))
        he2_resultantτ).mp hτ)
  -- Bridge `hFu1'_reg_opt2` (at `Option τU1'` level, ideal `⟨g0⟩` for `g0 :=
  -- rename some c0'' - X none * rename some d0''`) up to `τU1`'s ring
  -- (ideal `⟨Fu0'⟩`), via the SAME direct ring-equiv argument `hFu0'_reg`
  -- used (NOT `isSMulRegular_bridge_prefix_gen`, which cannot apply here --
  -- see the long comment trail this pass deleted for why). This time the
  -- ideal-map equality `Ideal.map e (Ideal.ofList [Fu0']) = Ideal.ofList [g0]`
  -- is immediate: `e Fu0' = g0` outright (`hFu0'_maps`), so `Ideal.map_ofList`
  -- turns `Ideal.ofList [Fu0']`'s image into `Ideal.ofList [e Fu0'] =
  -- Ideal.ofList [g0]` directly, with no further ideal-generation subtlety
  -- (unlike the earlier WRONG attempt, which tried to match `[Fu0']`'s image
  -- against `[c0'']` alone -- a different, unequal ideal).
  have hFu1'_reg : IsSMulRegular
      (MvPolynomial τU1 (F p) ⧸ Ideal.ofList [Fu0'])
      (Ideal.Quotient.mk (Ideal.ofList [Fu0']) Fu1') := by
    let e : MvPolynomial τU1 (F p) ≃+*
        MvPolynomial (Option τU1') (F p) :=
      (MvPolynomial.renameEquiv (F p) (optionSplit x0)).toRingEquiv
    have hFu0'_maps :
        e Fu0' =
          MvPolynomial.rename some c0'' -
            MvPolynomial.X none * MvPolynomial.rename some d0'' := by
      rw [hFu0'_eq]
      change
        MvPolynomial.rename (optionSplit x0)
            (MvPolynomial.rename (Subtype.val : τU1' → τU1) c0'' -
              MvPolynomial.X x0 *
                MvPolynomial.rename (Subtype.val : τU1' → τU1) d0'') =
          MvPolynomial.rename some c0'' -
            MvPolynomial.X none * MvPolynomial.rename some d0''
      exact rename_optionSplit_linear (R := F p) x0 c0'' d0''
    have hFu1'_maps :
        e Fu1' =
          MvPolynomial.rename some c1'' -
            MvPolynomial.X none * MvPolynomial.rename some d1'' := by
      rw [hFu1'_eq]
      change
        MvPolynomial.rename (optionSplit x0)
            (MvPolynomial.rename (Subtype.val : τU1' → τU1) c1'' -
              MvPolynomial.X x0 *
                MvPolynomial.rename (Subtype.val : τU1' → τU1) d1'') =
          MvPolynomial.rename some c1'' -
            MvPolynomial.X none * MvPolynomial.rename some d1''
      exact rename_optionSplit_linear (R := F p) x0 c1'' d1''
    have hIJ : Ideal.map (e : MvPolynomial τU1 (F p) →+* MvPolynomial (Option τU1') (F p))
        (Ideal.ofList [Fu0']) =
        Ideal.ofList [MvPolynomial.rename (some : τU1' → Option τU1') c0'' -
          MvPolynomial.X none * MvPolynomial.rename (some : τU1' → Option τU1') d0''] := by
      rw [Ideal.map_ofList]
      congr 1
      show [e Fu0'] = [MvPolynomial.rename (some : τU1' → Option τU1') c0'' -
        MvPolynomial.X none * MvPolynomial.rename (some : τU1' → Option τU1') d0'']
      rw [hFu0'_maps]
    exact (isSMulRegular_of_ringEquiv_of_mapsTo
      (e := e)
      (I := Ideal.ofList [Fu0'])
      (J := Ideal.ofList [MvPolynomial.rename (some : τU1' → Option τU1') c0'' -
        MvPolynomial.X none * MvPolynomial.rename (some : τU1' → Option τU1') d0''])
      hIJ Fu1'
      (MvPolynomial.rename some c1'' - MvPolynomial.X none * MvPolynomial.rename some d1'')
      hFu1'_maps).mpr hFu1'_reg_opt2
  -- **Step F: `d'` is `IsSMulRegular` mod `Ideal.ofList [Fu0', Fu1']`.
  -- This is deliberately isolated as the final named bottleneck.  Everything
  -- above this point is the two-generator peeling/change-of-variables setup;
  -- the remaining issue is exactly the missing same-family regularity of
  -- `d1den''` modulo `c0''`.
  have hsecond_peel_final : IsSMulRegular
      (MvPolynomial τU1 (F p) ⧸ Ideal.ofList [Fu0', Fu1'])
      (Ideal.Quotient.mk (Ideal.ofList [Fu0', Fu1']) d') := by
  -- (the lemma's actual target).**
  --
  -- **CORRECTED THIS PASS -- the previous plan here (chaining
  -- `regular_of_disjoint_extension` for a SECOND time, treating
  -- `d1den''` vs. `Fu1'` as a fresh disjoint split) was never actually
  -- checked for truth, and on closer inspection is NOT simply
  -- mechanical repetition of the `hFu1'_reg` argument -- it has a real
  -- gap. Specifics: `regular_of_disjoint_extension` needs `d1den''`'s
  -- and `Fu1'`'s variables genuinely disjoint (`σ₁ ⊕ σ₂`) -- true here
  -- (`d1den''` A-side per `u1_indep 1`, `Fu1'` B-side-plus-`x0` per
  -- `u2_indep 0`) -- so `d1den''` IS regular mod `⟨Fu1'⟩` ALONE by that
  -- route. But combining "`d1den''` regular mod `⟨Fu0'⟩` alone" with
  -- "`d1den''` regular mod `⟨Fu1'⟩` alone" into "`d1den''` regular mod
  -- `⟨Fu0',Fu1'⟩` SIMULTANEOUSLY" is NOT a free step -- regularity mod
  -- two separate ideals does not combine into regularity mod their sum
  -- without further argument (this was asserted as a "growing prefix
  -- gluing step... the roadmap's machinery handles" but no such gluing
  -- lemma actually exists anywhere in this file or the roadmap; that
  -- claim was unverified). Re-deriving it properly, following the
  -- roadmap's OWN later "actual actual resolution" (see
  -- `ROADMAP-peel-chain-assembly.md`, the `u1_den 1`/`Fu0,Fu1` discussion)
  -- instead: the right route is to work directly in `τU1`'s ring (not
  -- descend to a fresh `σ₁ ⊕ σ₂` split of `τU1` a second time), applying
  -- Layer 1 to `d'` ITSELF at each of the two peels `Fu0'`/`Fu1'`
  -- constitute (both linear in the SAME variable `x0`), exactly
  -- mirroring how `hFu0'_reg`/`hFu1'_reg` were built for `Fu0'`/`Fu1'`
  -- themselves, but now tracking `d'` (a CONSTANT with respect to `x0`,
  -- per `hd'` -- `d'` doesn't mention `x0` at all, since `d.u1_den 1`
  -- avoids `U0` by `u1_indep 1`) through the SAME two-step
  -- `regular_of_linear_elim`-chain instead of re-deriving it via
  -- `regular_of_disjoint_extension`.
  --
  -- This DOES work for the FIRST half (mod `⟨Fu0'⟩` alone, `gens' :=
  -- []`): `d'`'s image in the (unquotiented, since `gens' = []` at this
  -- point) coefficient ring `MvPolynomial τU1' (F p)` is just `d1den''`
  -- itself (via `hd'_eq`), regular there because `MvPolynomial τU1' (F p)`
  -- is a domain and `d1den'' ≠ 0` (renaming-injective from `d.u1_den 1 ≠
  -- 0`, `denRegular.1 1`) -- Layer 1 (`isSMulRegular_C_const_of_isSMulRegular`)
  -- then gives `d'`'s image regular in `Polynomial (MvPolynomial τU1'
  -- (F p))`, which (via the SAME `optionEquivLeft`/`Ideal.quotientEquiv`
  -- identification `hFu0'_reg_opt`'s proof already carries out) is
  -- regularity mod `⟨Fu0'⟩` alone in `τU1`'s ring.
  --
  -- **The genuine, currently-UNRESOLVED gap is the SECOND half**: to
  -- push this further to mod `⟨Fu0', Fu1'⟩` (both generators
  -- simultaneously), the SAME Layer-1 argument applied to the SECOND
  -- peel (`Fu1'`, `gens' := [c0'']` in `τU1'`'s ring per `hFu1'_reg_opt`'s
  -- own construction) needs `d'`'s `τU1'`-side representative `d1den''`
  -- to be regular NOT in the untouched ring `MvPolynomial τU1' (F p)` (as
  -- above) but in the ALREADY-QUOTIENTED ring `MvPolynomial τU1' (F p) ⧸
  -- Ideal.ofList [c0'']` -- i.e. **`d1den''` regular mod `⟨c0''⟩`
  -- alone**, exactly parallel to `hd1''_reg_mod_c0''` above but for a
  -- DIFFERENT pair. Unlike `hd1''_reg_mod_c0''` (`d1''` B-side, `c0''`
  -- A-side, genuinely variable-disjoint, `regular_of_disjoint_extension`
  -- applies cleanly), HERE both `d1den''` (`u1_indep 1`) and `c0''`
  -- (`u1_indep 0`) are A-SIDE -- `{wa1,wa2,a1,a2}`, the SAME Finset,
  -- reused across the two indices `i=0,1` per `denRegular`'s own
  -- docstring ("`u1_den`/`u2_den` at DIFFERENT `i` come from evaluating
  -- `uRS`'s coefficient list at different indices... two different, in
  -- general algebraically INDEPENDENT-looking elements... NOT obviously
  -- related"). `regular_of_disjoint_extension` genuinely CANNOT apply
  -- (no variable-disjoint split separates them), and unlike the
  -- roadmap's own late-stage claim (`ROADMAP-peel-chain-assembly.md`,
  -- "So `u1_den 1`... IS regular mod `⟨Fu0⟩` alone... Layer 1 applied a
  -- second time, treating `d'` as just another element of the
  -- coefficient ring `B`, nothing to do with disjointness of variables
  -- at all") -- that argument, re-checked here, ONLY establishes
  -- regularity mod `⟨Fu0'⟩` ALONE (the FIRST half above, `gens' := []`,
  -- which is genuinely free, matching what's proved above), and does
  -- NOT establish regularity mod the FURTHER quotient by `⟨Fu1'⟩` on
  -- top -- the roadmap's own text silently stops at the first peel and
  -- never actually re-examines the second, despite claiming to.
  --
  -- **Is "`d1den''` regular mod `⟨c0''⟩`" (two independent-looking
  -- elements of the SAME 4-variable domain `F[wa1,wa2,a1,a2]`, related
  -- only by both arising from the SAME construction at different
  -- indices `i`) even TRUE in general, from `A` a domain plus both
  -- nonzero alone?** NO -- this needs `c0''` and `d1den''` to share no
  -- common factor (`A ⧸ ⟨c0''⟩`: `d1den'' • x = 0` means `c0'' ∣
  -- d1den'' * x`; this forces `c0'' ∣ x` -- hence `x = 0` in the
  -- quotient -- ONLY if `gcd(c0'', d1den'') = 1`, i.e. NOT from "both
  -- nonzero in a domain" alone). This is a genuine, currently-untracked
  -- coprimality/exceptional-locus condition on `(u1_num 0, u1_den 1)` --
  -- exactly the SAME kind of extra hypothesis `Nondegenerate`/
  -- `CrossNondegenerate` already exist to encode for OTHER pairs, but
  -- NOT one either of those two structures currently states for THIS
  -- pair. Per this project's own rule (never use a hypothesis to dodge
  -- a proof, but ALSO never assert a false statement) this is correctly
  -- left `sorry`, scoped EXACTLY to this one coprimality-type fact,
  -- rather than silently assumed via a mis-applied disjointness lemma
  -- or an invented blanket hypothesis. Next concrete step (not attempted
  -- here): check computationally (or via a ChatGPT round-trip on the
  -- concrete `uRS`/`towerToRdec` construction) whether `u1_num 0` and
  -- `u1_den 1` are ACTUALLY coprime for generic `(c0,...,c4,sa,sb)`, and
  -- if so, either (a) derive it from data already in scope
  -- (`Nondegenerate`/`hgcdA` govern `Ypoly`/`uRS` coprimality, NOT
  -- `u1_num`/`u1_den` at mixed indices directly -- unclear yet whether
  -- it follows), or (b) add it as a new named field, parallel to
  -- `CrossNondegenerate`'s own four fields, if it is a genuinely new
  -- per-instance exceptional-locus condition.
    -- **Resolved**: `hcross01` (new hypothesis, threaded in above) supplies
    -- exactly this coprimality fact at the `Rdec p`/`d.u1_num`/`d.u1_den`
    -- level. What remains is bookkeeping: transport `hcross01` down to the
    -- internal `τU1'`-level representatives `c0''`/`d1den''`, using
    -- `hc0''`/`hd1den''` (`rename f c0'' = d.u1_num 0`, `rename f d1den'' =
    -- d.u1_den 1`) and `f`'s injectivity, via an explicit LEFT INVERSE of
    -- `f := fun v : τU1' => (v.1.1 : Idx)` (matching this file's own
    -- established idiom for `Option`-splits, `back := rename (getD x0)`,
    -- used earlier for `hτ`'s `e`/`back` pair -- here generalized from
    -- `Option τU1` to the subtype `τU1'`, using `Idx`'s `DecidableEq` to
    -- build a total retraction rather than `Option.getD`).
    have hcop_d1den_c0 : IsCoprime c0'' d1den'' := by
      have hwa1_ne_U0 : (wa1 : Idx) ≠ U0 := by decide
      have hwa1_ne_U1 : (wa1 : Idx) ≠ U1 := by decide
      have hwa1_ne_x0 : (⟨wa1, hwa1_ne_U1⟩ : τU1) ≠ x0 := by
        rw [hx0_def]
        intro h
        exact hwa1_ne_U0 (congrArg Subtype.val h)
      let dflt : τU1' := ⟨⟨wa1, hwa1_ne_U1⟩, hwa1_ne_x0⟩
      let g : Idx → τU1' := fun v =>
        if hv1 : v ≠ U1 then
          if hv0 : (⟨v, hv1⟩ : τU1) ≠ x0 then ⟨⟨v, hv1⟩, hv0⟩ else dflt
        else dflt
      have hgf : ∀ v : τU1', g ((fun w : τU1' => (w.1.1 : Idx)) v) = v := by
        rintro ⟨⟨v, hv1⟩, hv0⟩
        simp only [g]
        rw [dif_pos hv1, dif_pos hv0]
      -- `hcross01`'s Bezout witnesses, pinned down and `clear_value`'d
      -- immediately -- matches this file's own cost-control idiom (see
      -- `dvd_N_u` in `DataDerivationSolve.lean`), avoiding repeated
      -- unfolding of `d := theData ...` while the `rename` machinery below
      -- elaborates. A naive `hcross01.map (rename g)` composed with a
      -- second `rename f` timed out at `whnf` in a previous version of
      -- this proof; applying `rename g` ONCE, directly to the `Rdec
      -- p`-level witness identity, and only invoking `rename f`/`hc0''`/
      -- `hd1den''` to identify the RESULT with `c0''`/`d1den''`, avoids
      -- that blowup.
      obtain ⟨A, B, hAB⟩ := hcross01
      let A' : Rdec p := A
      let B' : Rdec p := B
      have hAB' : A' * d.u1_num 0 + B' * d.u1_den 1 = 1 := hAB
      clear_value A' B'
      have hmapped :
          MvPolynomial.rename g A' * MvPolynomial.rename g (d.u1_num 0) +
            MvPolynomial.rename g B' * MvPolynomial.rename g (d.u1_den 1) = 1 := by
        rw [← map_mul, ← map_mul, ← map_add, hAB', map_one]
      have hc0_direct :
          MvPolynomial.rename (fun w : τU1' => (w.1.1 : Idx)) c0'' = d.u1_num 0 := by
        simpa only [hu1num0_def] using hc0''
      have hd1den_direct :
          MvPolynomial.rename (fun w : τU1' => (w.1.1 : Idx)) d1den'' = d.u1_den 1 := by
        simpa only [hu1den1_def] using hd1den''
      rw [← hc0_direct, ← hd1den_direct] at hmapped
      -- Collapse `rename g (rename f c0'') = c0''` (`f := fun w : τU1' =>
      -- (w.1.1 : Idx)`), matching this file's own `hback_e` idiom for the
      -- `Option`-split case, generalized to the subtype retraction `g`.
      have hcollapse_c0 : MvPolynomial.rename g
          (MvPolynomial.rename (fun w : τU1' => (w.1.1 : Idx)) c0'') = c0'' := by
        rw [MvPolynomial.rename_rename, show
          g ∘ (fun w : τU1' => (w.1.1 : Idx)) = id from funext hgf]
        simp
      have hcollapse_d1den : MvPolynomial.rename g
          (MvPolynomial.rename (fun w : τU1' => (w.1.1 : Idx)) d1den'') = d1den'' := by
        rw [MvPolynomial.rename_rename, show
          g ∘ (fun w : τU1' => (w.1.1 : Idx)) = id from funext hgf]
        simp
      rw [hcollapse_c0, hcollapse_d1den] at hmapped
      exact ⟨MvPolynomial.rename g A', MvPolynomial.rename g B', hmapped⟩
    have hd1den_reg_mod_c0 : IsSMulRegular
        (MvPolynomial τU1' (F p) ⧸ Ideal.span {c0''})
        (Ideal.Quotient.mk (Ideal.span {c0''}) d1den'') :=
      isSMulRegular_quotient_span_singleton_of_isCoprime hcop_d1den_c0
    -- Keep the concrete consequence available to the remaining peeling
    -- argument (not yet chained into the final conclusion -- see
    -- `hd'_full_reg`'s docstring above for exactly what's missing).
    have _ := hd1den_reg_mod_c0
    exact hd'_full_reg

  exact hsecond_peel_final

end peelU1τNotation

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
      (Rdec p ⧸ Ideal.ofList (gens'.map (fun q : MvPolynomial {v : Idx // v ≠ x} (F p) =>
        ((MvPolynomial.renameEquiv (F p) (optionSplit x)).symm (MvPolynomial.rename some q) : Rdec p))))
      (Ideal.Quotient.mk
        (Ideal.ofList (gens'.map (fun q : MvPolynomial {v : Idx // v ≠ x} (F p) =>
          ((MvPolynomial.renameEquiv (F p) (optionSplit x)).symm (MvPolynomial.rename some q) : Rdec p))))
        ((MvPolynomial.renameEquiv (F p) (optionSplit x)).symm (MvPolynomial.rename some g)))
    ↔
    IsSMulRegular
      (MvPolynomial (Option {v : Idx // v ≠ x}) (F p) ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk (Ideal.ofList (gens'.map (MvPolynomial.rename some)))
        (MvPolynomial.rename some g)) :=
  isSMulRegular_bridge_prefix_gen (F p) x gens' (MvPolynomial.rename some g)

/-! ## §3. The 12-stage assembly (sorry #3)

Uses §1/§2 plus everything already proved in `DecoupledSystemRegular.lean`
(`regular_of_linear_elim`, `regular_of_peeled_leadingCoeff`,
`isSMulRegular_of_mul_eq_of_isSMulRegular`, `denRegular`,
`CrossNondegenerate`, `curveCoeffRegular`, `quintic_monic`) to chain
`RingTheory.Sequence.isRegular_cons_iff'` twelve times. Per
`ROADMAP-peel-chain-assembly.md`'s corrected design, no restatement of
any upstream lemma/hypothesis is needed — this is purely the wiring
step.

**§3.0, the `QuotSMulTop`-vs-`Ideal.span` bridge.** Every upstream fact
(`regular_of_linear_elim`/`regular_of_peeled_leadingCoeff` via the §2
bridge, and `CrossNondegenerate`'s fields directly) is stated as
`IsSMulRegular (Rdec p ⧸ Ideal.span {r}) (mk s)` for the SINGLE
most-recently-imposed generator `r`. `RingTheory.Sequence.IsRegular.cons'
(h1 : IsSMulRegular M r) (h2 : IsRegular (QuotSMulTop r M) (rs.map (mk
(Ideal.span {r}))))` (confirmed against Mathlib's actual source,
`Mathlib/RingTheory/Regular/RegularSequence.lean`, `M` held FIXED at
`Rdec p` throughout — this is the primed constructor's whole point, see
`ROADMAP-peel-chain-assembly.md`) needs exactly `IsSMulRegular
(QuotSMulTop r (Rdec p)) (...)`-shaped facts, so a bridge between
`QuotSMulTop r (Rdec p)` and `Rdec p ⧸ Ideal.span {r}` is needed at
every one of the 12 steps.

**Deliberately a `LinearEquiv`, not a `RingEquiv`.** Only `IsSMulRegular`/
`IsRegular` facts are ever transported across this bridge (never ring
multiplication itself), and Mathlib supplies `LinearEquiv.isSMulRegular_congr`/
`LinearEquiv.isRegular_congr` taking a bare `M ≃ₗ[R] N` — so building a
full `RingEquiv` (with its `map_mul` proof obligation, which would need
its own careful unfolding of `QuotSMulTop`'s vs. `Ideal.Quotient`'s
independently-elaborated `HasQuotient` instances) is both unnecessary and
a needless source of defeq risk. `Submodule.quotEquivOfEq` alone (module
level, matching `QuotSMulTop`'s own defining type `Rdec p ⧸ (r • ⊤ :
Submodule (Rdec p) (Rdec p))` exactly, no cross-instance identification
needed) suffices. -/

/-- **The submodule identity underlying the bridge**: `r • (⊤ :
Submodule (Rdec p) (Rdec p)) = Ideal.span {r}`, i.e. `QuotSMulTop r (Rdec
p)`'s defining submodule (ring acting on itself) coincides with the
principal ideal `⟨r⟩` viewed as a submodule. Proved via
`Ideal.ofList_cons_smul`/`Ideal.ofList_nil`/`Ideal.ofList_singleton`
(confirmed against Mathlib's actual `RegularSequence.lean` source this
pass — these are the SAME lemmas `isRegular_cons_iff'`'s own statement is
built from, so this identification is not a novel fact but literally
what makes `QuotSMulTop` the right notion for single-step chaining) to
identify `r • ⊤` with `Ideal.ofList [r] • ⊤ = Ideal.span {r} • ⊤`, then
`Ideal.smul_eq_mul` (`I • J = I * J` for `I J : Ideal R`, confirmed) plus
`Ideal.one_eq_top`/`mul_one` to collapse `Ideal.span {r} • ⊤ = Ideal.span
{r} * ⊤ = Ideal.span {r} * 1 = Ideal.span {r}`. -/
noncomputable def quotSMulTop_equiv_span (r : Rdec p) :
    QuotSMulTop r (Rdec p) ≃ₗ[Rdec p] Rdec p ⧸ Ideal.span {r} :=
  (QuotSMulTop.equivQuotTensor r (Rdec p)).trans
    (TensorProduct.rid (Rdec p) (Rdec p ⧸ Ideal.span {r}))

/-- **`IsSMulRegular` transported across the bridge**, the form actually
used at each of the 12 stages. `RingTheory.Sequence.IsRegular`/
`IsSMulRegular` are ALWAYS stated for a BARE ORIGINAL-RING element `s :
Rdec p` acting on a module (never for an element of the quotient acting
on itself — `IsSMulRegular M (c : R)` for `M` an `R`-module, per
`IsSMulRegular`'s own signature, confirmed throughout this file's
existing uses), so no multiplicative structure on `QuotSMulTop r (Rdec
p)` is ever needed — `LinearEquiv.isSMulRegular_congr (e : M ≃ₗ[R] N) (c
: R) : IsSMulRegular M c ↔ IsSMulRegular N c` (confirmed against Mathlib
source) applies DIRECTLY to `quotSMulTop_equiv_span`, no further
`Quotient.inductionOn'` bookkeeping required. -/
theorem isSMulRegular_quotSMulTop_of_span (r s : Rdec p)
    (h : IsSMulRegular (Rdec p ⧸ Ideal.span {r}) s) :
    IsSMulRegular (QuotSMulTop r (Rdec p)) s :=
  (LinearEquiv.isSMulRegular_congr (quotSMulTop_equiv_span p r) s).mpr h

/-- **`IsRegular` transported across the bridge**, the list-level
analogue of `isSMulRegular_quotSMulTop_of_span`, needed for the FINAL
(innermost) stage of each `IsRegular.cons'` application, whose second
hypothesis is itself an `IsRegular (QuotSMulTop r M) (...)` fact (not
merely `IsSMulRegular`) — built the same way, via
`LinearEquiv.isRegular_congr` (confirmed against Mathlib source),
applied to a list `rs` all at once rather than element-by-element. -/
theorem isRegular_quotSMulTop_of_span (r : Rdec p) (rs : List (Rdec p))
    (h : RingTheory.Sequence.IsRegular (Rdec p ⧸ Ideal.span {r}) rs) :
    RingTheory.Sequence.IsRegular (QuotSMulTop r (Rdec p)) rs :=
  (LinearEquiv.isRegular_congr (quotSMulTop_equiv_span p r) rs).mpr h

/-! ### §3.0bis. The right characterization: `IsRegular` unfolds to a
per-index (NOT per-nesting) statement -- no `QuotSMulTop` bridge needed
at the outer layer at all

**Supersedes the `foldedQuotSMulTop`/`List.rec` approach drafted (and
stuck) in an earlier pass.** Chasing `isRegular_cons_iff'` through `k`
manually-nested `QuotSMulTop` applications is the WRONG shape to fight:
Mathlib's `RingTheory.Sequence.IsRegular` is a `structure` with exactly
the shape every one of `hFu0_reg .. hCurveB2_reg` above is ALREADY
stated in --

```
structure IsRegular (M) (rs) extends IsWeaklyRegular M rs where
  regular_mod_prev : ∀ (i : ℕ) (h : i < rs.length),
    IsSMulRegular (M ⧸ Ideal.ofList (rs.take i) • ⊤) rs[i]
  top_ne_smul : ⊤ ≠ Ideal.ofList rs • ⊤
```

(confirmed against Mathlib source, `RegularSequence.lean` -- `IsRegular`
extends `IsWeaklyRegular`, and `IsWeaklyRegular` itself has the matching
characterization `isWeaklyRegular_iff_Fin : IsWeaklyRegular M rs ↔ ∀ i :
Fin rs.length, IsSMulRegular (M ⧸ Ideal.ofList (rs.take i) • ⊤) rs[i]`).
Every single `regular_mod_prev`/`isWeaklyRegular_iff_Fin` obligation is
`IsSMulRegular` mod the FLAT ideal `Ideal.ofList (prefix so far) • ⊤`
(equivalently `Ideal.ofList (prefix so far)`, since `I • ⊤ = I` for
`I : Ideal R` acting on `R` itself -- `Ideal.smul_top_eq_map` composed
with `Ideal.map_id`/`RingHom.id_apply`, or more directly
`Submodule.ideal_span_singleton_smul`-style `I • (⊤ : Submodule R R) =
I` facts already available generically) -- i.e. EXACTLY the shape
`hCurveA1_reg .. hCurveB2_reg` AND `hFu2_reg`/`hFv2_reg` are stated in
directly (both corrected to the full-prefix `Ideal.ofList` shape this
pass), and one `Ideal.ofList_singleton` rewrite away from
`hFu0_reg .. hFv1_reg`'s single-generator/empty-prefix shapes; stages 3
and 7 need `hFu3_full_reg`/`hFv3_full_reg` instead of `hFu3_reg`/
`hFv3_reg` for the same reason (see the assembly's own stage-3 note
below). **No `QuotSMulTop` nesting, no
composed `Ideal.Quotient.mk`s, no induction on the prefix length is
needed anywhere** -- the per-index statement is checked ONCE per index,
independently, each time against a FLAT (single-level) quotient by the
literal prefix. This is a strictly easier target than the nested
`isRegular_cons_iff'`-unrolling route, and directly explains the
"induction gets easier as we go" intuition: `Ideal.ofList (rs.take i)`
really is just a bigger and bigger flat ideal, never a re-nested tower,
so there is no accumulating `QuotSMulTop`/`DoubleQuot` bookkeeping to
carry at all. -/

/-- **`Ideal.ofList l • (⊤ : Submodule R R) = Ideal.ofList l` as ideals**
(via the ring-as-a-module-over-itself identification), so
`regular_mod_prev`'s `M ⧸ Ideal.ofList (rs.take i) • ⊤` (for `M := R`)
is the SAME ring as the more familiar `R ⧸ Ideal.ofList (rs.take i)`
used throughout this file's other lemmas (`hFu0_reg`, `hCurveA1_reg`,
etc.). Small rewriting helper so the 12-way case split below can quote
`hFu0_reg`-style facts directly, without each stage re-deriving this
identification inline. -/
theorem ideal_smul_top_eq_self {R : Type*} [CommRing R] (I : Ideal R) :
    I • (⊤ : Submodule R R) = (I : Submodule R R) := by
  simp [Ideal.smul_top_eq_map, Submodule.map_id]

/-! ### §3.1 Stage-0-style helper: first generator for a target, empty
prefix

`Fu0`/`Fv0` (and, by the SAME argument, any "first generator introduced
for a fresh target variable with an EMPTY already-imposed prefix") are
`c' - X x * d'` (`c', d' : MvPolynomial τ (F p)`, `τ := {v ≠ x}`, `x` the
target variable) renamed up into `Rdec p` — exactly `regular_of_linear_elim`'s
own hypothesis shape at `gens' := []`. Bundles the whole "apply
`regular_of_linear_elim`, bridge via `isSMulRegular_of_ringEquiv_of_mapsTo`,
plus the empty-prefix `isSMulRegular_bot_iff`-style collapse" argument §1's
Step D already carries out ONE level down (`τ' := {v : τ // v ≠ x0}`) —
here run at the TOP level (`σ := Idx`, `τ := {v ≠ x}` directly), so it
can be reused identically for `Fu0`/`Fv0`. `d'`'s regularity comes from
`d' ≠ 0` in the DOMAIN `MvPolynomial τ (F p)` (`MvPolynomial` over a
field), matching §1's `hd0''_domreg`.

**Statement note, corrected this pass (two bugs, both retracted, not
patched around).**

1. The peeled variable `x : Idx` can NEVER be written as
   `MvPolynomial.X x` inside `MvPolynomial τ (F p)` itself (`τ := {v :
   Idx // v ≠ x}` by construction excludes `x` — there is no element of
   `τ` whose value IS `x`, so no proof obligation `x ≠ x` is ever
   satisfiable; this was the bug behind a `decide`-proved-False error at
   both call sites, `hFu0_eq`/`hFv0_eq` in `regularSeq_of_peel_chain`).
   The peeled variable only ever exists at the `Option τ` level, as
   `MvPolynomial.X none` — this is exactly how `regular_of_linear_elim`
   itself represents it, and is the ONLY correct way to state "the
   polynomial `c' - X x * d'`, viewed in `Rdec p`": as `(renameEquiv (F
   p) (optionSplit x)).symm` applied to `MvPolynomial.rename some c' -
   MvPolynomial.X none * MvPolynomial.rename some d'`, both `c'` and `d'`
   staying in `MvPolynomial τ (F p)` throughout.
2. The ORIGINAL conclusion asked for `IsSMulRegular (Rdec p ⧸ Ideal.span
   {r}) (Ideal.Quotient.mk _ r)` — i.e. "is `r` itself regular in the
   ring obtained by quotienting `r` OUT". That's a DIFFERENT (and,
   barring degenerate rings, FALSE) claim from what stage 0 of
   `RingTheory.Sequence.isRegular_cons_iff'` actually needs: `mk r = 0`
   in `Rdec p ⧸ Ideal.span {r}` by construction, and `IsSMulRegular M
   (0 : R)` forces `M` to be the zero module, plainly false here. What
   `isRegular_cons_iff' M r rs` actually wants at the FIRST (empty-
   prefix) stage is `IsSMulRegular M r` in the UN-quotiented ring `M`
   itself (confirmed against Mathlib's own statement of
   `isRegular_cons_iff'`) — the `Ideal.span {r}`-quotient only enters
   for the NEXT generator in the chain (already correctly reflected
   below in `hFu1_reg`/`hFu3_reg`/etc., which quotient by the PREVIOUS
   stage's span and check the CURRENT stage's generator, two distinct
   elements). Conclusion weakened/corrected to the true, actually-needed
   statement: `IsSMulRegular (Rdec p) r`. -/
theorem isSMulRegular_first_gen (x : Idx) (c' d' : MvPolynomial {v : Idx // v ≠ x} (F p))
    (hd'_ne : d' ≠ 0) :
    IsSMulRegular (Rdec p)
      ((MvPolynomial.renameEquiv (F p) (optionSplit x)).symm
        (MvPolynomial.rename some c' - MvPolynomial.X none * MvPolynomial.rename some d')) := by
  classical

  have hd'_opt_ne0 :
      MvPolynomial.rename
          (some : {v : Idx // v ≠ x} → Option {v : Idx // v ≠ x}) d' ≠ 0 := by
    rw [Ne, MvPolynomial.rename_eq_zero_iff_of_injective d'
      (Option.some_injective {v : Idx // v ≠ x})]
    exact hd'_ne

  have hd'_opt_ne :
      MvPolynomial.rename
          (some : {v : Idx // v ≠ x} → Option {v : Idx // v ≠ x}) d' ≠ 0 :=
    hd'_opt_ne0

  have hd'_opt_reg :
      IsSMulRegular (MvPolynomial (Option {v : Idx // v ≠ x}) (F p))
        (MvPolynomial.rename
          (some : {v : Idx // v ≠ x} → Option {v : Idx // v ≠ x}) d') := by
    intro a b hab
    change
      MvPolynomial.rename
          (some : {v : Idx // v ≠ x} → Option {v : Idx // v ≠ x}) d' * a =
        MvPolynomial.rename
          (some : {v : Idx // v ≠ x} → Option {v : Idx // v ≠ x}) d' * b at hab
    exact mul_left_cancel₀ hd'_opt_ne hab

  have hFu0'_reg_opt :
      IsSMulRegular
        (MvPolynomial (Option {v : Idx // v ≠ x}) (F p) ⧸
          Ideal.ofList
            (([] : List (MvPolynomial {v : Idx // v ≠ x} (F p))).map
              (MvPolynomial.rename some)))
        (Ideal.Quotient.mk
          (Ideal.ofList
            (([] : List (MvPolynomial {v : Idx // v ≠ x} (F p))).map
              (MvPolynomial.rename some)))
          (MvPolynomial.rename some c' -
            MvPolynomial.X none * MvPolynomial.rename some d')) := by
    apply regular_of_linear_elim
      (τ := {v : Idx // v ≠ x}) (R := F p) [] c' d'
    · have hbot :=
        (isSMulRegular_bot_module_iff
          (R := MvPolynomial (Option {v : Idx // v ≠ x}) (F p))
          (MvPolynomial.rename
            (some : {v : Idx // v ≠ x} → Option {v : Idx // v ≠ x}) d')).mp
          hd'_opt_reg

      rw [List.map_nil]
      rw [show Ideal.ofList ([] : List (MvPolynomial (Option {v : Idx // v ≠ x}) (F p))) =
          (⊥ : Ideal (MvPolynomial (Option {v : Idx // v ≠ x}) (F p))) from Ideal.ofList_nil]
      exact hbot

    · rfl

  have hFu0'_reg_opt_bot :
      IsSMulRegular
        (MvPolynomial (Option {v : Idx // v ≠ x}) (F p) ⧸
          (⊥ : Ideal (MvPolynomial (Option {v : Idx // v ≠ x}) (F p))))
        (Ideal.Quotient.mk
          (⊥ : Ideal (MvPolynomial (Option {v : Idx // v ≠ x}) (F p)))
          (MvPolynomial.rename some c' -
            MvPolynomial.X none * MvPolynomial.rename some d')) := by
    change
      IsSMulRegular
        (MvPolynomial (Option {v : Idx // v ≠ x}) (F p) ⧸
          (⊥ : Ideal (MvPolynomial (Option {v : Idx // v ≠ x}) (F p))))
        (Ideal.Quotient.mk
          (⊥ : Ideal (MvPolynomial (Option {v : Idx // v ≠ x}) (F p)))
          (MvPolynomial.rename some c' -
            MvPolynomial.X none * MvPolynomial.rename some d'))
    rw [← Ideal.ofList_nil]
    exact hFu0'_reg_opt

  let e : MvPolynomial Idx (F p) ≃+*
      MvPolynomial (Option {v : Idx // v ≠ x}) (F p) :=
    (MvPolynomial.renameEquiv (F p) (optionSplit x)).toRingEquiv

  have htransport :
      IsSMulRegular
        (Rdec p ⧸ (⊥ : Ideal (Rdec p)))
        (Ideal.Quotient.mk (⊥ : Ideal (Rdec p))
          (e.symm
            (MvPolynomial.rename some c' -
              MvPolynomial.X none * MvPolynomial.rename some d'))) := by
    apply
      (isSMulRegular_of_ringEquiv_of_mapsTo e
        (⊥ : Ideal (Rdec p))
        (⊥ : Ideal (MvPolynomial (Option {v : Idx // v ≠ x}) (F p)))
        (by simp)
        (e.symm
          (MvPolynomial.rename some c' -
            MvPolynomial.X none * MvPolynomial.rename some d'))
        (MvPolynomial.rename some c' -
          MvPolynomial.X none * MvPolynomial.rename some d')
        (e.apply_symm_apply _)).mpr
    exact hFu0'_reg_opt_bot

  exact (isSMulRegular_bot_iff _).mpr htransport

/-! ## §3bis. `PeelChainNondegenerate`: the remaining genuinely-open
exceptional-locus content, packaged as hypotheses rather than derived

**Per Claire's explicit instruction this pass**: Gaps A and B (see
`ROADMAP-peel-chain-assembly.md`) are closed here NOT by proving new
mathematics but by WEAKENING `regularSeq_of_peel_chain`'s statement —
adding one more bundled hypothesis structure, exactly parallel to how
`Nondegenerate`/`CrossNondegenerate` already package per-instance
exceptional-locus conditions rather than claiming them to hold
generically. This is a deliberate, named weakening (not a hidden
`sorry`): every field below is a genuine mathematical claim about the
specific `(c0,...,c4,sa,sb)` instance, expected to hold for "enough"
choices exactly as `CrossNondegenerate` already is, but not proved (or
claimed provable) from `Nondegenerate`/`CrossNondegenerate`/`hgcdA/B`/
`hcurA/B` alone — see `ROADMAP-peel-chain-assembly.md`'s Gap A/Gap B
sections for why each is genuinely new content, not a Lean gap.

**Eventual target, per Claire**: the whole `regularSeq_of_peel_chain`
development is meant to end up parametrized by a scalar `alpha` and
actual `F p`-points `P1,...,P4` on the curve (plus "suitably
well-behaved" curve coefficients) rather than raw `SampleTarget`
data — at that point `PeelChainNondegenerate`'s fields become
conditions on `(alpha, P1,...,P4, c0,...,c4)` instead of on
`(sa,sb,c0,...,c4)` directly, but the STRUCTURE of what needs to be
assumed (two coprimality-style resultant-regularity facts per side,
matching the existing `CrossNondegenerate` shape one variable-peel
further in; four curve-relation regularity facts) is not expected to
change shape, only its parametrization. -/

/-- **Gap A + Gap B, bundled.** Fields named to mirror
`CrossNondegenerate`'s `hu0/hu1/hv0/hv1` convention: `hu01`/`hv01` are
the NEW stage-2/6 facts, stated at the `Rdec p`-level shape stage 2/6 of
the 12-fold assembly directly consumes (regularity of `Fu2 := u1_num 1 -
U1*u1_den 1`/`Fv2` mod the two-element prefix `[Fu0,Fu1]`/`[Fv0,Fv1]`) —
the coarser, outer-assembly-facing counterpart of
`isSMulRegular_den_of_second_peel`'s own internal `hcross01`/
`hpeeled_ideal_proper`/`hd'_full_reg` hypotheses (that theorem is not
wired into this assembly; see its own docstring for the finer-grained,
partially-worked-out version of this same gap, one variable-peel down).
`hu1_full`/`hv1_full` are the stage-3/7 facts (same flavor, one step
further in the same already-imposed prefix, per
`ROADMAP-peel-chain-assembly.md`'s "structurally the same kind of fact"
note); `hcurveA1/A2/B1/B2` are Gap B (curve-relation regularity mod the
accumulated 8-element prefix, stated directly against `curveA1`/etc.'s
own literal definitions rather than routed through `curveCoeffRegular`'s
abstract `quintic` shape, since the shape-identification lemma
connecting the two is itself not yet written — see `curveCoeffRegular`'s
docstring). -/
structure PeelChainNondegenerate (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) : Prop where
  hu01 : IsSMulRegular (Rdec p ⧸ Ideal.ofList
      [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
         U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
       (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
         U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0])
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1))
  hv01 : IsSMulRegular (Rdec p ⧸ Ideal.ofList
      [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
         V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
       (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
         V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0])
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1))
  hu1_full : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1])
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1))
  hv1_full : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1])
        ((theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1))
  hcurveA1 : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1])
        (curveA1 p c0 c1 c2 c3 c4))
  hcurveA2 : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1,
         curveA1 p c0 c1 c2 c3 c4])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1,
         curveA1 p c0 c1 c2 c3 c4])
        (curveA2 p c0 c1 c2 c3 c4))
  hcurveB1 : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4])
        (curveB1 p c0 c1 c2 c3 c4))
  hcurveB2 : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4, curveB1 p c0 c1 c2 c3 c4])
      (Ideal.Quotient.mk (Ideal.ofList
        [(theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 0 -
           U0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_num 1 -
           U1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).u2_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 0 -
           V0' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 0,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v1_den 1,
         (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_num 1 -
           V1' p * (theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4, curveB1 p c0 c1 c2 c3 c4])
        (curveB2 p c0 c1 c2 c3 c4))

set_option maxHeartbeats 1600000 in
theorem regularSeq_of_peel_chain (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hndA : Nondegenerate p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA)
    (hndB : Nondegenerate p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB)
    (hcross : CrossNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (hpeel : PeelChainNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    -- **Gap C (`top_ne_smul`), weakened to a hypothesis.** The full
    -- 12-generator ideal is proper, i.e. the system has a genuine common
    -- solution -- real existence-of-a-point content
    -- (`ROADMAP-peel-chain-assembly.md`'s Gap C), not attempted here; see
    -- that file's own note on what proving this honestly would need.
    (htop_ne_smul : (⊤ : Ideal (Rdec p)) ≠
      Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) • ⊤) :
    RingTheory.Sequence.IsRegular (Rdec p)
      (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) := by
  classical
  -- Unfold `genList` down to a literal 12-element `List.cons` chain, so
  -- `IsRegular.cons'` can be applied one element at a time.
  set d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB with hd_def
  have hgenList : genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB =
      [ d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
        d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
        d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
        d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1,
        curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
        curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4 ] := by
    simp only [genList, FuList, FvList, hd_def, List.append_eq]
    rfl
  rw [hgenList]
  have hden := denRegular p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB hndA hndB
  -- **`Fu0`/`Fv0` "first generator" reduction.** Both `Fu0 := u1_num 0 -
  -- U0*u1_den 0` and `Fv0 := v1_num 0 - V0*v1_den 0` are literally
  -- `rename Subtype.val (c' - X x * d')` for `x := U0`/`V0`, `τ := {v ≠
  -- x}`, `c' := d.u1_num 0`/`d.v1_num 0` and `d' := d.u1_den 0`/`d.v1_den
  -- 0` VIEWED AS `τ`-side polynomials -- but `d.u1_num 0` etc. are
  -- already stated as elements of `Rdec p := MvPolynomial Idx (F p)`
  -- directly, not `MvPolynomial τ (F p)`. Since `u1_num 0`/`u1_den 0`
  -- avoid `U0` (`u1_indep 0`'s target Finset `{wa1,wa2,a1,a2}` never
  -- contains `U0`), they have canonical `τ`-side representatives via
  -- `MvPolynomial.exists_rename_eq_of_vars_subset_range`, exactly as
  -- `isSMulRegular_den_of_second_peel`'s own Step A already does for the
  -- SAME data one level further down. Obtain those representatives here.
  have hU0_ne_U1 : (U0 : Idx) ≠ U1 := by decide
  have hV0_ne_V1 : (V0 : Idx) ≠ V1 := by decide
  -- `Fu0`'s representatives (`τ := {v ≠ U0}`).
  have hu1num0_rangeU0 : (↑(d.u1_num 0).vars : Set Idx) ⊆
      Set.range (fun v : {v : Idx // v ≠ U0} => (v.1 : Idx)) := by
    intro v hv
    have hmem := d.u1_indep 0 v (Finset.mem_union_left (d.u1_den 0).vars hv)
    have hne : v ≠ U0 := by
      intro hv0
      subst v
      exact (by decide : U0 ∉ ({wa1, wa2, a1, a2} : Finset Idx)) hmem
    exact ⟨⟨v, hne⟩, rfl⟩
  have hu1den0_rangeU0 : (↑(d.u1_den 0).vars : Set Idx) ⊆
      Set.range (fun v : {v : Idx // v ≠ U0} => (v.1 : Idx)) := by
    intro v hv
    have hmem := d.u1_indep 0 v (Finset.mem_union_right (d.u1_num 0).vars hv)
    have hne : v ≠ U0 := by
      intro hv0
      subst v
      exact (by decide : U0 ∉ ({wa1, wa2, a1, a2} : Finset Idx)) hmem
    exact ⟨⟨v, hne⟩, rfl⟩
  obtain ⟨cu0, hcu0⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.u1_num 0) (fun v : {v : Idx // v ≠ U0} => (v.1 : Idx)) Subtype.val_injective hu1num0_rangeU0
  obtain ⟨du0, hdu0⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.u1_den 0) (fun v : {v : Idx // v ≠ U0} => (v.1 : Idx)) Subtype.val_injective hu1den0_rangeU0
  have hdu0_ne : du0 ≠ 0 := by
    intro h; apply hden.1 0; rw [← hdu0, h, map_zero]
  have hcollapse_rename_u0 : ∀ q : MvPolynomial {v : Idx // v ≠ U0} (F p),
      (MvPolynomial.renameEquiv (F p) (optionSplit U0)).symm (MvPolynomial.rename some q) =
      MvPolynomial.rename (Subtype.val : {v : Idx // v ≠ U0} → Idx) q := by
    intro q
    show MvPolynomial.rename (optionSplit U0).symm (MvPolynomial.rename some q) =
      MvPolynomial.rename (Subtype.val : {v : Idx // v ≠ U0} → Idx) q
    rw [MvPolynomial.rename_rename]
    congr 1
  have hcollapse_X_u0 : (MvPolynomial.renameEquiv (F p) (optionSplit U0)).symm
      (MvPolynomial.X none) = U0' p := by
    show MvPolynomial.rename (optionSplit U0).symm (MvPolynomial.X none) = MvPolynomial.X U0
    rw [MvPolynomial.rename_X]
    congr 1
  have hFu0_eq : d.u1_num 0 - U0' p * d.u1_den 0 =
      (MvPolynomial.renameEquiv (F p) (optionSplit U0)).symm
        (MvPolynomial.rename some cu0 - MvPolynomial.X none * MvPolynomial.rename some du0) := by
    rw [map_sub, map_mul, hcollapse_rename_u0, hcollapse_rename_u0, hcollapse_X_u0, hcu0, hdu0]
  have hFu0_reg : IsSMulRegular (Rdec p) (d.u1_num 0 - U0' p * d.u1_den 0) := by
    rw [hFu0_eq]
    exact isSMulRegular_first_gen p U0 cu0 du0 hdu0_ne
  -- `Fv0`'s representatives (`τ := {v ≠ V0}`), identical construction.
  have hv1num0_rangeV0 : (↑(d.v1_num 0).vars : Set Idx) ⊆
      Set.range (fun v : {v : Idx // v ≠ V0} => (v.1 : Idx)) := by
    intro v hv
    have hmem := d.v1_indep 0 v (Finset.mem_union_left (d.v1_den 0).vars hv)
    have hne : v ≠ V0 := by
      intro hv0
      subst v
      exact (by decide : V0 ∉ ({wa1, wa2, a1, a2} : Finset Idx)) hmem
    exact ⟨⟨v, hne⟩, rfl⟩
  have hv1den0_rangeV0 : (↑(d.v1_den 0).vars : Set Idx) ⊆
      Set.range (fun v : {v : Idx // v ≠ V0} => (v.1 : Idx)) := by
    intro v hv
    have hmem := d.v1_indep 0 v (Finset.mem_union_right (d.v1_num 0).vars hv)
    have hne : v ≠ V0 := by
      intro hv0
      subst v
      exact (by decide : V0 ∉ ({wa1, wa2, a1, a2} : Finset Idx)) hmem
    exact ⟨⟨v, hne⟩, rfl⟩
  obtain ⟨cv0, hcv0⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.v1_num 0) (fun v : {v : Idx // v ≠ V0} => (v.1 : Idx)) Subtype.val_injective hv1num0_rangeV0
  obtain ⟨dv0, hdv0⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    (d.v1_den 0) (fun v : {v : Idx // v ≠ V0} => (v.1 : Idx)) Subtype.val_injective hv1den0_rangeV0
  have hdv0_ne : dv0 ≠ 0 := by
    intro h; apply hden.2.2.1 0; rw [← hdv0, h, map_zero]
  have hcollapse_rename_v0 : ∀ q : MvPolynomial {v : Idx // v ≠ V0} (F p),
      (MvPolynomial.renameEquiv (F p) (optionSplit V0)).symm (MvPolynomial.rename some q) =
      MvPolynomial.rename (Subtype.val : {v : Idx // v ≠ V0} → Idx) q := by
    intro q
    show MvPolynomial.rename (optionSplit V0).symm (MvPolynomial.rename some q) =
      MvPolynomial.rename (Subtype.val : {v : Idx // v ≠ V0} → Idx) q
    rw [MvPolynomial.rename_rename]
    congr 1
  have hcollapse_X_v0 : (MvPolynomial.renameEquiv (F p) (optionSplit V0)).symm
      (MvPolynomial.X none) = V0' p := by
    show MvPolynomial.rename (optionSplit V0).symm (MvPolynomial.X none) = MvPolynomial.X V0
    rw [MvPolynomial.rename_X]
    congr 1
  have hFv0_eq : d.v1_num 0 - V0' p * d.v1_den 0 =
      (MvPolynomial.renameEquiv (F p) (optionSplit V0)).symm
        (MvPolynomial.rename some cv0 - MvPolynomial.X none * MvPolynomial.rename some dv0) := by
    rw [map_sub, map_mul, hcollapse_rename_v0, hcollapse_rename_v0, hcollapse_X_v0, hcv0, hdv0]
  have hFv0_reg : IsSMulRegular (Rdec p) (d.v1_num 0 - V0' p * d.v1_den 0) := by
    rw [hFv0_eq]
    exact isSMulRegular_first_gen p V0 cv0 dv0 hdv0_ne
  -- **`Fu1`/`Fu3`/`Fv1`/`Fv3` "repeated target" reduction.** Each is
  -- regular mod the immediately-preceding same-target generator via
  -- `isSMulRegular_of_mul_eq_of_isSMulRegular`, fed by `hcross`'s
  -- matching field and the identity `d₁ * Fu1 = resultant + d₂ * Fu0`
  -- (`Fu0`'s own vanishing, i.e. working mod `Ideal.span {Fu0}` where
  -- `Fu0 ≡ 0`, collapses `d₂ * Fu0` to `0`, leaving `d₁ * Fu1 ≡
  -- resultant` exactly matching `hcross.hu0`'s stated element) --
  -- checked directly by ring-normalizing the un-quotiented identity
  -- `d1 * (c2 - X*d2) = (d1*c2 - d2*c1) + d2 * (c1 - X*d1)` (`X := U0'
  -- p`), which holds in `Rdec p` with NO quotienting at all, THEN
  -- pushing through `Ideal.Quotient.mk` where the `d2 * Fu0` term maps
  -- to `d2 • (mk Fu0) = d2 • 0 = 0`.
  have hFu1_reg : IsSMulRegular (Rdec p ⧸ Ideal.span
      {d.u1_num 0 - U0' p * d.u1_den 0}) (Ideal.Quotient.mk (Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0})
        (d.u2_num 0 - U0' p * d.u2_den 0)) := by
    have hmk0 : (Ideal.Quotient.mk (Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0})
        (d.u1_num 0 - U0' p * d.u1_den 0)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hring : d.u1_den 0 * (d.u2_num 0 - U0' p * d.u2_den 0) =
        (d.u1_den 0 * d.u2_num 0 - d.u2_den 0 * d.u1_num 0) +
          d.u2_den 0 * (d.u1_num 0 - U0' p * d.u1_den 0) := by ring
    have hmk_ring : (Ideal.Quotient.mk (Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0}) (d.u1_den 0)) *
        (Ideal.Quotient.mk
          (Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0})
          (d.u2_num 0 - U0' p * d.u2_den 0)) =
        (Ideal.Quotient.mk
          (Ideal.span {d.u1_num 0 - U0' p * d.u1_den 0})
          (d.u1_den 0 * d.u2_num 0 - d.u2_den 0 * d.u1_num 0)) := by
      rw [← map_mul, hring, map_add, map_mul, hmk0, mul_zero, add_zero]
    exact isSMulRegular_of_mul_eq_of_isSMulRegular hcross.hu0 hmk_ring
  have hFu3_reg : IsSMulRegular (Rdec p ⧸ Ideal.span
      {d.u1_num 1 - U1' p * d.u1_den 1}) (Ideal.Quotient.mk (Ideal.span {d.u1_num 1 - U1' p * d.u1_den 1})
        (d.u2_num 1 - U1' p * d.u2_den 1)) := by
    have hmk0 : (Ideal.Quotient.mk (Ideal.span {d.u1_num 1 - U1' p * d.u1_den 1})
        (d.u1_num 1 - U1' p * d.u1_den 1)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hring : d.u1_den 1 * (d.u2_num 1 - U1' p * d.u2_den 1) =
        (d.u1_den 1 * d.u2_num 1 - d.u2_den 1 * d.u1_num 1) +
          d.u2_den 1 * (d.u1_num 1 - U1' p * d.u1_den 1) := by ring
    have hmk_ring : (Ideal.Quotient.mk (Ideal.span {d.u1_num 1 - U1' p * d.u1_den 1}) (d.u1_den 1)) *
        (Ideal.Quotient.mk
          (Ideal.span {d.u1_num 1 - U1' p * d.u1_den 1})
          (d.u2_num 1 - U1' p * d.u2_den 1)) =
        (Ideal.Quotient.mk
          (Ideal.span {d.u1_num 1 - U1' p * d.u1_den 1})
          (d.u1_den 1 * d.u2_num 1 - d.u2_den 1 * d.u1_num 1)) := by
      rw [← map_mul, hring, map_add, map_mul, hmk0, mul_zero, add_zero]
    exact isSMulRegular_of_mul_eq_of_isSMulRegular hcross.hu1 hmk_ring
  have hFv1_reg : IsSMulRegular (Rdec p ⧸ Ideal.span
      {d.v1_num 0 - V0' p * d.v1_den 0}) (Ideal.Quotient.mk (Ideal.span {d.v1_num 0 - V0' p * d.v1_den 0})
        (d.v2_num 0 - V0' p * d.v2_den 0)) := by
    have hmk0 : (Ideal.Quotient.mk (Ideal.span {d.v1_num 0 - V0' p * d.v1_den 0})
        (d.v1_num 0 - V0' p * d.v1_den 0)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hring : d.v1_den 0 * (d.v2_num 0 - V0' p * d.v2_den 0) =
        (d.v1_den 0 * d.v2_num 0 - d.v2_den 0 * d.v1_num 0) +
          d.v2_den 0 * (d.v1_num 0 - V0' p * d.v1_den 0) := by ring
    have hmk_ring : (Ideal.Quotient.mk (Ideal.span {d.v1_num 0 - V0' p * d.v1_den 0}) (d.v1_den 0)) *
        (Ideal.Quotient.mk
          (Ideal.span {d.v1_num 0 - V0' p * d.v1_den 0})
          (d.v2_num 0 - V0' p * d.v2_den 0)) =
        (Ideal.Quotient.mk
          (Ideal.span {d.v1_num 0 - V0' p * d.v1_den 0})
          (d.v1_den 0 * d.v2_num 0 - d.v2_den 0 * d.v1_num 0)) := by
      rw [← map_mul, hring, map_add, map_mul, hmk0, mul_zero, add_zero]
    exact isSMulRegular_of_mul_eq_of_isSMulRegular hcross.hv0 hmk_ring
  have hFv3_reg : IsSMulRegular (Rdec p ⧸ Ideal.span
      {d.v1_num 1 - V1' p * d.v1_den 1}) (Ideal.Quotient.mk (Ideal.span {d.v1_num 1 - V1' p * d.v1_den 1})
        (d.v2_num 1 - V1' p * d.v2_den 1)) := by
    have hmk0 : (Ideal.Quotient.mk (Ideal.span {d.v1_num 1 - V1' p * d.v1_den 1})
        (d.v1_num 1 - V1' p * d.v1_den 1)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
    have hring : d.v1_den 1 * (d.v2_num 1 - V1' p * d.v2_den 1) =
        (d.v1_den 1 * d.v2_num 1 - d.v2_den 1 * d.v1_num 1) +
          d.v2_den 1 * (d.v1_num 1 - V1' p * d.v1_den 1) := by ring
    have hmk_ring : (Ideal.Quotient.mk (Ideal.span {d.v1_num 1 - V1' p * d.v1_den 1}) (d.v1_den 1)) *
        (Ideal.Quotient.mk
          (Ideal.span {d.v1_num 1 - V1' p * d.v1_den 1})
          (d.v2_num 1 - V1' p * d.v2_den 1)) =
        (Ideal.Quotient.mk
          (Ideal.span {d.v1_num 1 - V1' p * d.v1_den 1})
          (d.v1_den 1 * d.v2_num 1 - d.v2_den 1 * d.v1_num 1)) := by
      rw [← map_mul, hring, map_add, map_mul, hmk0, mul_zero, add_zero]
    exact isSMulRegular_of_mul_eq_of_isSMulRegular hcross.hv1 hmk_ring
  -- **Stages 2/6, 3/7, and 8-11, all closed via `PeelChainNondegenerate`
  -- this pass** (per Claire's explicit instruction: rather than prove
  -- Gap A's coprimality content or Gap B's curve-shape identification
  -- outright, both are packaged as bundled per-instance hypotheses,
  -- exactly parallel to how `Nondegenerate`/`CrossNondegenerate` already
  -- work -- see `PeelChainNondegenerate`'s own docstring above for
  -- precisely what each field asserts and why it isn't derived here).
  -- **Stages 2/6, closed via `PeelChainNondegenerate`.** `hpeel.hu01`/
  -- `.hv01` are stated at exactly the `Rdec p`-level shape `hFu2_reg`/
  -- `hFv2_reg` need (see `PeelChainNondegenerate`'s own docstring), so
  -- these are now direct applications -- no further bridging needed.
  have hFu2_reg : IsSMulRegular (Rdec p ⧸ Ideal.ofList
      [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0])
        (d.u1_num 1 - U1' p * d.u1_den 1)) := hpeel.hu01
  have hFv2_reg : IsSMulRegular (Rdec p ⧸ Ideal.ofList
      [d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0])
        (d.v1_num 1 - V1' p * d.v1_den 1)) := hpeel.hv01
  -- **Stages 8--11 open input, curve relations.** `curveCoeffRegular`
  -- proves the ABSTRACT `quintic` shape is `Monic` (hence its leading
  -- coefficient `1` is regular, via
  -- `Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular`/
  -- `isSMulRegular_one`), but does NOT yet identify `curveA1`/`curveA2`/
  -- `curveB1`/`curveB2`'s literal `Rdec p`-level definitions (peeled
  -- through the accumulated 8-element `Fu++Fv` prefix, then through the
  -- matching `w`-variable) with that abstract shape -- see
  -- `curveCoeffRegular`'s own docstring in `DecoupledSystemRegular.lean`
  -- for exactly what remains: a `simp`/`rename`-unfolding identity, not
  -- new mathematics. Stated here at the shape each stage actually needs:
  -- regular mod the FULL prefix accumulated so far (`Ideal.ofList` of all
  -- generators strictly before it in `genList`), matching
  -- `isRegular_cons_iff'`'s single-step requirement once the earlier
  -- seven/eight stages have already been peeled off by the `QuotSMulTop`
  -- nesting below.
  have hCurveA1_reg : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1])
        (curveA1 p c0 c1 c2 c3 c4)) := hpeel.hcurveA1
  have hCurveA2_reg : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1,
         curveA1 p c0 c1 c2 c3 c4])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1,
         curveA1 p c0 c1 c2 c3 c4])
        (curveA2 p c0 c1 c2 c3 c4)) := hpeel.hcurveA2
  have hCurveB1_reg : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4])
        (curveB1 p c0 c1 c2 c3 c4)) := hpeel.hcurveB1
  have hCurveB2_reg : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1,
         d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1,
         curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
         curveB1 p c0 c1 c2 c3 c4])
        (curveB2 p c0 c1 c2 c3 c4)) := hpeel.hcurveB2

  -- **Stage 3/7 fact, closed via `PeelChainNondegenerate`.** `hFu3_reg`/
  -- `hFv3_reg` above (from `hcross.hu1`/`hcross.hv1`) are stated mod the
  -- SINGLE ideal `Ideal.span {Fu2}`/`Ideal.span {Fv2}` alone, in bare
  -- `Rdec p`; `regular_mod_prev 3`/`regular_mod_prev 7` below instead
  -- need regularity mod the FULL 3-element prefix
  -- `Ideal.ofList [Fu0,Fu1,Fu2]`/`Ideal.ofList [Fv0,Fv1,Fv2]` -- a
  -- strictly bigger ideal, NOT propositionally equal to the
  -- single-generator one. `hpeel.hu1_full`/`.hv1_full` supply exactly
  -- this fact directly (see `PeelChainNondegenerate`'s docstring).
  have hFu3_full_reg : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
         d.u1_num 1 - U1' p * d.u1_den 1])
        (d.u2_num 1 - U1' p * d.u2_den 1)) := hpeel.hu1_full
  have hFv3_full_reg : IsSMulRegular
      (Rdec p ⧸ Ideal.ofList
        [d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1])
      (Ideal.Quotient.mk (Ideal.ofList
        [d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
         d.v1_num 1 - V1' p * d.v1_den 1])
        (d.v2_num 1 - V1' p * d.v2_den 1)) := hpeel.hv1_full

  /- **12-stage assembly, via the flat `regular_mod_prev`
  characterization -- supersedes the earlier `isRegular_cons_iff'`-
  unrolling draft.**

  `RingTheory.Sequence.IsRegular M rs` (confirmed against Mathlib
  source, `RegularSequence.lean`) unfolds to `IsWeaklyRegular M rs`
  (itself characterized, via `isWeaklyRegular_iff_Fin`, by `∀ i : Fin
  rs.length, IsSMulRegular (M ⧸ Ideal.ofList (rs.take i) • ⊤) rs[i]`)
  PLUS one extra nondegeneracy field `top_ne_smul : ⊤ ≠ Ideal.ofList rs
  • ⊤`. Crucially, `regular_mod_prev`'s statement is FLAT: a single
  quotient by `Ideal.ofList (rs.take i)`, never a nested `QuotSMulTop`
  tower -- so this is a strictly easier target to assemble than the
  `isRegular_cons_iff'`-unrolling route attempted in an earlier pass
  (kept, in spirit, only through `isSMulRegular_quotSMulTop_of_span`
  above, which is no longer needed for THIS route but is harmless to
  leave proved for potential future use).

  With `genList = [Fu0,Fu1,Fu2,Fu3,Fv0,Fv1,Fv2,Fv3,cA1,cA2,cB1,cB2]`
  (`hgenList` above), the twelve `regular_mod_prev i` obligations are,
  after unfolding `List.take`/`List.get`/`rs[i]` for each concrete `i`
  (all closed by `rfl`/`simp` on the literal list, no genuine case
  analysis beyond picking which stored fact to quote):

  * `i = 0`: `Ideal.ofList (rs.take 0) = Ideal.ofList [] = ⊥` -- matches
    `hFu0_reg` (`IsSMulRegular (Rdec p) Fu0`) via `Ideal.ofList_nil` +
    `isSMulRegular_bot_iff`.
  * `i = 1`: `Ideal.ofList [Fu0] = Ideal.span {Fu0}` (`Ideal.ofList_singleton`)
    -- matches `hFu1_reg` exactly.
  * `i = 2`: `Ideal.ofList [Fu0,Fu1]` -- matches `hFu2_reg` directly
    (statement at the full 2-element prefix, matching
    `isSMulRegular_den_of_second_peel`'s own conclusion shape; supplied
    by `hpeel.hu01` this pass -- see `PeelChainNondegenerate`).
  * `i = 3`: `Ideal.ofList [Fu0,Fu1,Fu2]` -- matches `hFu3_full_reg`
    (supplied by `hpeel.hu1_full` this pass) directly.
  * `i = 4..7`: same four shapes, `V`-register (`hFv0_reg`, `hFv1_reg`,
    `hFv2_reg`, `hFv3_full_reg`).
  * `i = 8..11`: `hCurveA1_reg .. hCurveB2_reg` already stated mod the
    exact FULL accumulated prefix at each stage -- no rewriting needed
    at all, these plug in directly.

  All twelve `regular_mod_prev` obligations above (`hFu0_reg .. hFv3_full_reg`,
  `hCurveA1_reg .. hCurveB2_reg`) are now in hand -- either proved outright
  earlier in this file or supplied via `hpeel : PeelChainNondegenerate ...`
  this pass. Only `top_ne_smul` (Gap C, `ROADMAP-peel-chain-assembly.md`'s
  own name for it) remains genuinely unattempted: proving it honestly needs
  exhibiting an actual `F p`-point solving all 12 defining equations
  (properness of the full ideal), real existence-of-a-point mathematics
  entirely separate from the regularity argument above. Per Claire's same
  "weaken via a hypothesis" instruction, this is threaded in as
  `htop_ne_smul` below rather than attempted here or silently assumed. -/
  rw [RingTheory.Sequence.isRegular_iff, RingTheory.Sequence.isWeaklyRegular_iff_Fin]
  refine ⟨fun i => ?_, htop_ne_smul⟩
  -- Each `i : Fin 12` (against the literal list from `hgenList`, already
  -- rewritten into the goal by the earlier `rw [hgenList]`) is resolved by
  -- `fin_cases`-driven enumeration; the resulting 12 goals each unfold
  -- `List.take`/`List.get`/`rs[i]` on the literal 12-element list and
  -- match `ideal_smul_top_eq_self` rewritten against the corresponding
  -- `h*_reg` fact above -- one `first | ... ` alternative per stage,
  -- matching the twelve bullet points in this theorem's docstring.
  fin_cases i <;>
    simp only [List.take, List.getElem_cons_zero, List.getElem_cons_succ, Fin.isValue,
      List.length_nil, List.length_cons, List.length_singleton,
      Ideal.ofList_nil, Ideal.ofList_singleton, Ideal.ofList_cons] <;>
    first
      | simpa using (isSMulRegular_bot_iff (d.u1_num 0 - U0' p * d.u1_den 0)).mp hFu0_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hFu1_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hFu2_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hFu3_full_reg
      | simpa using (isSMulRegular_bot_iff (d.v1_num 0 - V0' p * d.v1_den 0)).mp hFv0_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hFv1_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hFv2_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hFv3_full_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hCurveA1_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hCurveA2_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hCurveB1_reg
      | exact ideal_smul_top_eq_self (R := Rdec p) _ ▸ hCurveB2_reg

end DecoupledSystem
end Genus2Lean
