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
theorem isSMulRegular_bridge_prefix_gen {σ : Type*} [DecidableEq σ] (R : Type*) [CommRing R]
    (x : σ) (gens' : List (MvPolynomial {v : σ // v ≠ x} R))
    (g : MvPolynomial {v : σ // v ≠ x} R) :
    IsSMulRegular
      (MvPolynomial σ R ⧸ Ideal.ofList (gens'.map (fun q : MvPolynomial {v : σ // v ≠ x} R =>
        ((MvPolynomial.renameEquiv R (optionSplit x)).symm (MvPolynomial.rename some q) :
          MvPolynomial σ R))))
      (Ideal.Quotient.mk
        (Ideal.ofList (gens'.map (fun q : MvPolynomial {v : σ // v ≠ x} R =>
          ((MvPolynomial.renameEquiv R (optionSplit x)).symm (MvPolynomial.rename some q) :
            MvPolynomial σ R))))
        ((MvPolynomial.renameEquiv R (optionSplit x)).symm (MvPolynomial.rename some g)))
    ↔
    IsSMulRegular
      (MvPolynomial (Option {v : σ // v ≠ x}) R ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk (Ideal.ofList (gens'.map (MvPolynomial.rename some)))
        (MvPolynomial.rename some g)) := by
  set e : MvPolynomial σ R ≃+* MvPolynomial (Option {v : σ // v ≠ x}) R :=
    (MvPolynomial.renameEquiv R (optionSplit x)).toRingEquiv with he_def
  set I : Ideal (MvPolynomial σ R) :=
    Ideal.ofList (gens'.map (fun q : MvPolynomial {v : σ // v ≠ x} R =>
      (e.symm (MvPolynomial.rename some q) : MvPolynomial σ R))) with hI_def
  set J : Ideal (MvPolynomial (Option {v : σ // v ≠ x}) R) :=
    Ideal.ofList (gens'.map (MvPolynomial.rename some)) with hJ_def
  have hIJ : Ideal.map (e : MvPolynomial σ R →+* MvPolynomial (Option {v : σ // v ≠ x}) R) I = J := by
    rw [hI_def, hJ_def, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    change e (e.symm (MvPolynomial.rename some q)) = MvPolynomial.rename some q
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
      d.u1_den 1) :
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
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu1den0_range : (↑u1den0.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu1_indep0 v (by
      exact Finset.mem_union_right u1num0.vars hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu2num0_range : (↑u2num0.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu2_indep0 v (by
      simpa only [u2den0] using Finset.mem_union_left u2den0.vars hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu2den0_range : (↑u2den0.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu2_indep0 v (by
      simpa only [u2num0] using Finset.mem_union_right u2num0.vars hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
    exact ⟨⟨⟨v, hne1⟩, by rw [hx0_def]; exact fun h => hne0 (congrArg Subtype.val h)⟩, rfl⟩
  have hu1den1_range : (↑u1den1.vars : Set Idx) ⊆ Set.range (fun v : τU1' => (v.1.1 : Idx)) := by
    intro v hv
    have hmem := hu1_indep1 v (by
      simpa only [u1num1] using Finset.mem_union_right u1num1.vars hv)
    have hne1 : v ≠ U1 := by rintro rfl; fin_cases hmem
    have hne0 : v ≠ U0 := by rintro rfl; fin_cases hmem
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
    rw [map_sub, map_mul, MvPolynomial.rename_rename, MvPolynomial.rename_rename,
      MvPolynomial.rename_X]
    congr 2
    · congr 1
      funext v
      show (optionSplit x0) (Subtype.val v) = some v
      have := Equiv.optionSubtype_apply_val_apply x0 (Equiv.refl τU1') v
      simpa using this
    · show (optionSplit x0) x0 = none
      exact Equiv.optionSubtype_apply_apply_self x0 (Equiv.refl τU1')
    · congr 1
      funext v
      show (optionSplit x0) (Subtype.val v) = some v
      have := Equiv.optionSubtype_apply_val_apply x0 (Equiv.refl τU1') v
      simpa using this
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

  -- **Step E: `Fu1'` is `IsSMulRegular` mod `Ideal.ofList [Fu0']`.**
  -- Apply `regular_of_linear_elim` a SECOND time, now at `τ := τU1'` (one
  -- level further down than Step D), `R := F p`, `gens' := [c0'']`
  -- (`Fu0'` reinterpreted as a `τU1'`-side element -- the SAME `c0'', d0''`
  -- Step A/B already produced), `c := c1''`, `d := d1''`. `hd_reg` for
  -- THIS call needs `d1''`'s `rename some` image regular mod
  -- `Ideal.ofList [rename some c0'']` in `MvPolynomial (Option τU1') (F p)`
  -- -- this is a genuine `regular_of_disjoint_extension` instance (NOT
  -- the multi-generator mess earlier drafts worried about): `c0''` lives
  -- entirely in `u1_indep`'s A-side Finset `{wa1,wa2,a1,a2}` and `d1''`
  -- entirely in `u2_indep`'s B-side Finset `{wb1,wb2,b1,b2}` (both
  -- reinterpreted inside `τU1'`, disjoint from each other and from `x0`),
  -- so splitting `τU1'` as `σ₁ ⊕ σ₂` along "does this variable's `Idx`-image
  -- lie in `{wa1,wa2,a1,a2}`" separates `c0''` (lands entirely in `σ₁`)
  -- from `d1''` (lands entirely in `σ₂`) cleanly, with NO element
  -- straddling both sides (unlike `Fu0`/`Fu1` themselves at the OUTER
  -- level, which straddle their target variable and their own side --
  -- the whole reason this needed a second peel first: after Step
  -- A/B/D's peeling, `c0''`/`d0''`/`c1''`/`d1''` are honest τU1'-side
  -- elements with NO further `x0`-dependence to straddle).
  classical
  set predA : τU1' → Prop := fun v => (v.1.1 : Idx) ∈ ({wa1, wa2, a1, a2} : Finset Idx) with hpredA_def
  set σ₁ : Type := {v : τU1' // predA v} with hσ₁_def
  set σ₂ : Type := {v : τU1' // ¬ predA v} with hσ₂_def
  set esplit : σ₁ ⊕ σ₂ ≃ τU1' := Equiv.sumCompl predA with hesplit_def
  -- `c0''`'s variables lie in `predA` (A-side, per `u1_indep 0`'s target
  -- Finset transported through `hc0''`/`f`'s range description already
  -- established in Step A) -- so `c0''` has a `σ₁`-side representative.
  have hc0''_predA : (↑c0''.vars : Set τU1') ⊆ {v : τU1' | predA v} := by
    intro v hv
    have hmem : ((fun w : τU1' => (w.1.1 : Idx)) v) ∈ ({wa1, wa2, a1, a2} : Finset Idx) := by
      have hrange : (v.1.1 : Idx) ∈ (↑u1num0.vars : Set Idx) := by
        have hdeg := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mp hv
        have hdeg_rename :=
          MvPolynomial.degreeOf_rename_of_injective hf_inj v (p := c0'')
        have hdeg' : MvPolynomial.degreeOf ((fun v : τU1' => (v.1.1 : Idx)) v)
            (MvPolynomial.rename (fun v : τU1' => (v.1.1 : Idx)) c0'') ≠ 0 := by
          rw [hdeg_rename]
          exact hdeg
        rw [hc0''] at hdeg'
        exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mpr hdeg'
      exact hu1_indep0 v.1.1 (Finset.mem_union_left u1den0.vars hrange)
    simpa [hpredA_def] using hmem
  have hd1''_predA : (↑d1''.vars : Set τU1') ⊆ {v : τU1' | ¬ predA v} := by
    intro v hv
    have hmem : ((fun w : τU1' => (w.1.1 : Idx)) v) ∈ ({wb1, wb2, b1, b2} : Finset Idx) := by
      have hrange : (v.1.1 : Idx) ∈ (↑u2den0.vars : Set Idx) := by
        have hdeg := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mp hv
        have hdeg_rename :=
          MvPolynomial.degreeOf_rename_of_injective hf_inj v (p := d1'')
        have hdeg' : MvPolynomial.degreeOf ((fun v : τU1' => (v.1.1 : Idx)) v)
            (MvPolynomial.rename (fun v : τU1' => (v.1.1 : Idx)) d1'') ≠ 0 := by
          rw [hdeg_rename]
          exact hdeg
        rw [hd1''] at hdeg'
        exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mpr hdeg'
      exact hu2_indep0 v.1.1 (Finset.mem_union_right u2num0.vars hrange)
    intro hcontra
    have hA : (v.1.1 : Idx) ∈ ({wa1, wa2, a1, a2} : Finset Idx) := by
      simpa [hpredA_def] using hcontra
    have hB : (v.1.1 : Idx) ∈ ({wb1, wb2, b1, b2} : Finset Idx) := hmem
    exact (Finset.disjoint_left.mp (by decide :
      Disjoint ({wa1, wa2, a1, a2} : Finset Idx)
        ({wb1, wb2, b1, b2} : Finset Idx))) hA hB
  obtain ⟨c0₁, hc0₁⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    c0'' (Subtype.val : σ₁ → τU1') Subtype.val_injective
    (by
      intro v hv
      exact ⟨⟨v, hc0''_predA hv⟩, rfl⟩)
  obtain ⟨d1₂, hd1₂⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range
    d1'' (Subtype.val : σ₂ → τU1') Subtype.val_injective
    (by
      intro v hv
      exact ⟨⟨v, hd1''_predA hv⟩, rfl⟩)
  -- `c0₁ : MvPolynomial σ₁ (F p)`, `d1₂ : MvPolynomial σ₂ (F p)`, both
  -- honest disjoint-side elements. `d1₂` is nonzero (renaming injective,
  -- `d1'' ≠ 0` from `hd1''_ne`), hence `IsSMulRegular` in its own ring
  -- `MvPolynomial σ₂ (F p)` (a domain).
  have hd1₂_ne : d1₂ ≠ 0 := by
    intro h
    apply hd1''_ne
    rw [← hd1₂, h, map_zero]
  have hd1₂_reg : IsSMulRegular (MvPolynomial σ₂ (F p)) d1₂ := by
    intro x y hxy
    apply mul_left_cancel₀ hd1₂_ne
    simpa only [smul_eq_mul] using hxy
  -- **`regular_of_disjoint_extension` applied**: `d1₂`'s image (`rename
  -- Sum.inr d1₂`) survives quotienting `MvPolynomial (σ₁ ⊕ σ₂) (F p)` by
  -- `⟨rename Sum.inl c0₁⟩`.
  have hdisjoint := regular_of_disjoint_extension (R := F p) (σ₁ := σ₁) (σ₂ := σ₂)
    c0₁ hd1₂_reg
  -- Transport `hdisjoint` (stated over `σ₁ ⊕ σ₂`) back to `τU1'` via
  -- `renameEquiv (F p) esplit : MvPolynomial (σ₁ ⊕ σ₂) (F p) ≃+*
  -- MvPolynomial τU1' (F p)`, using `esplit`'s defining property
  -- (`Equiv.sumCompl_apply_inl`/`_inr`) to identify `esplit (Sum.inl v) =
  -- v.1` / `esplit (Sum.inr v) = v.1`, hence `rename esplit (rename
  -- Sum.inl c0₁) = rename Subtype.val c0₁ = c0''` (by `hc0₁` composed with
  -- `rename_rename`) and likewise for `d1₂`/`d1''`.
  set eO : MvPolynomial (σ₁ ⊕ σ₂) (F p) ≃+* MvPolynomial τU1' (F p) :=
    (MvPolynomial.renameEquiv (F p) esplit).toRingEquiv with heO_def
  have heO_inl : eO (MvPolynomial.rename Sum.inl c0₁) = c0'' := by
    show MvPolynomial.rename (⇑esplit) (MvPolynomial.rename Sum.inl c0₁) = c0''
    rw [MvPolynomial.rename_rename]
    rw [show (⇑esplit ∘ Sum.inl : σ₁ → τU1') = (Subtype.val : σ₁ → τU1') from
      funext (fun v => Equiv.sumCompl_apply_inl v)]
    exact hc0₁
  have heO_inr : eO (MvPolynomial.rename Sum.inr d1₂) = d1'' := by
    show MvPolynomial.rename (⇑esplit) (MvPolynomial.rename Sum.inr d1₂) = d1''
    rw [MvPolynomial.rename_rename]
    rw [show (⇑esplit ∘ Sum.inr : σ₂ → τU1') = (Subtype.val : σ₂ → τU1') from
      funext (fun v => Equiv.sumCompl_apply_inr v)]
    exact hd1₂
  have hIdealMapO : Ideal.map (eO : MvPolynomial (σ₁ ⊕ σ₂) (F p) →+* MvPolynomial τU1' (F p))
      (Ideal.ofList [MvPolynomial.rename Sum.inl c0₁]) = Ideal.ofList [c0''] := by
    rw [Ideal.ofList_singleton, Ideal.ofList_singleton, Ideal.map_span, Set.image_singleton]
    change Ideal.span {eO (MvPolynomial.rename Sum.inl c0₁)} = Ideal.span {c0''}
    rw [heO_inl]
  have hd1''_reg_mod_c0'' :
      IsSMulRegular (MvPolynomial τU1' (F p) ⧸ Ideal.ofList [c0''])
        (Ideal.Quotient.mk (Ideal.ofList [c0'']) d1'') := by
    have htransport := (isSMulRegular_of_ringEquiv_of_mapsTo eO
      (Ideal.ofList [MvPolynomial.rename Sum.inl c0₁]) (Ideal.ofList [c0''])
      hIdealMapO (MvPolynomial.rename Sum.inr d1₂) d1'' heO_inr).mp
    simpa [heO_inr] using htransport hdisjoint
  -- Push `d1''`'s regularity (mod `⟨c0''⟩` in `τU1'`'s ring) forward to the
  -- `Option τU1'`-level fact `regular_of_linear_elim` needs as its `hd_reg`
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
  -- applied a THIRD time, now at `σ := τU1'`, `x :=` (a placeholder single
  -- extra variable) -- **not needed**: `regular_of_linear_elim` itself
  -- takes `hd_reg` stated ALREADY at the `Option τU1'` level, and the
  -- bridge from "regular mod `Ideal.ofList gens'` in the base ring" to
  -- "regular mod `Ideal.ofList (gens'.map (rename some))` in `Option`
  -- of that ring" for a NONZERODIVISOR/regular element is exactly
  -- `regular_of_peeled_leadingCoeff`'s/Layer 1's OWN transport shape one
  -- more time: `MvPolynomial (Option τU1') (F p) ⧸ Ideal.ofList
  -- (gens'.map (rename some))` is `Polynomial` of `MvPolynomial τU1' (F p)
  -- ⧸ Ideal.ofList gens'`, and `rename some d1''`'s image there is `C
  -- (mk d1'')`, regular by `isSMulRegular_C_const_of_isSMulRegular`
  -- applied to `hd1''_reg_mod_c0''`, transported through the SAME
  -- `optionEquivLeft`-based identification `regular_of_linear_elim`
  -- itself uses internally (`Ideal.quotientEquiv` + `optionEquivLeft`,
  -- exactly `hFu0'_reg_opt`'s own route, now with `gens' := [c0'']`
  -- instead of `[]`).
  set I'₁ : Ideal (MvPolynomial τU1' (F p)) := Ideal.ofList [c0''] with hI'₁_def
  set A₁ : Ideal (MvPolynomial (Option τU1') (F p)) :=
    Ideal.ofList (([c0''] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)) with hA₁_def
  have hIdealMap₁ : Ideal.map ((MvPolynomial.optionEquivLeft (F p) τU1').toRingEquiv :
      MvPolynomial (Option τU1') (F p) →+* Polynomial (MvPolynomial τU1' (F p))) A₁ =
      Ideal.map Polynomial.C I'₁ := by
    rw [hA₁_def, hI'₁_def, Ideal.map_ofList, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    show (MvPolynomial.optionEquivLeft (F p) τU1') (MvPolynomial.rename some q) = Polynomial.C q
    exact optionEquivLeft_rename_some q
  set e₁ : (MvPolynomial (Option τU1') (F p) ⧸ A₁) ≃+* Polynomial (MvPolynomial τU1' (F p) ⧸ I'₁) :=
    (Ideal.quotientEquiv A₁ (Ideal.map Polynomial.C I'₁)
      (MvPolynomial.optionEquivLeft (F p) τU1').toRingEquiv hIdealMap₁.symm).trans
      I'₁.polynomialQuotientEquivQuotientPolynomial.symm with he₁_def
  have he₁_apply : ∀ x : MvPolynomial (Option τU1') (F p) ⧸ A₁,
      e₁ x = I'₁.polynomialQuotientEquivQuotientPolynomial.symm
        ((Ideal.quotientEquiv A₁ (Ideal.map Polynomial.C I'₁)
          (MvPolynomial.optionEquivLeft (F p) τU1').toRingEquiv hIdealMap₁.symm) x) := by
    intro x; rw [he₁_def, RingEquiv.trans_apply]
  have he₁_C : e₁ (Ideal.Quotient.mk A₁ (MvPolynomial.rename some d1'')) =
      Polynomial.C (Ideal.Quotient.mk I'₁ d1'') := by
    rw [he₁_apply, Ideal.quotientEquiv_mk]
    have hstep : (MvPolynomial.optionEquivLeft (F p) τU1').toRingEquiv
        (MvPolynomial.rename some d1'') = Polynomial.C d1'' := optionEquivLeft_rename_some d1''
    rw [hstep, Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk]
    simp
  have hd1''_opt_reg : IsSMulRegular (MvPolynomial (Option τU1') (F p) ⧸ A₁)
      (Ideal.Quotient.mk A₁ (MvPolynomial.rename some d1'')) := by
    have hsmul_mk₁ : ∀ (r : MvPolynomial (Option τU1') (F p)) (x : MvPolynomial (Option τU1') (F p) ⧸ A₁),
        r • x = Ideal.Quotient.mk A₁ r * x := by
      intro r x
      refine Quotient.inductionOn' x ?_
      intro x'
      show Ideal.Quotient.mk A₁ (r * x') = Ideal.Quotient.mk A₁ r * Ideal.Quotient.mk A₁ x'
      rw [map_mul]
    have hreg_poly : IsSMulRegular (Polynomial (MvPolynomial τU1' (F p) ⧸ I'₁))
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
  -- **`Fu1'` regular mod `⟨Fu0'⟩` (in `τU1`'s ring)**: `regular_of_linear_elim`
  -- at `τ := τU1'`, `gens' := [c0'']`, `c := c1''`, `d := d1''`, `hd_reg :=
  -- hd1''_opt_reg`, concluding regularity of `rename some c1'' - X none *
  -- rename some d1''` mod `Ideal.ofList [rename some c0'']` in
  -- `MvPolynomial (Option τU1') (F p)` -- exactly `hFu1'_reg_opt` below,
  -- matching `hFu1'_eq`'s shape.
  have hFu1'_reg_opt : IsSMulRegular
      (MvPolynomial (Option τU1') (F p) ⧸
        Ideal.ofList (([c0''] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)))
      (Ideal.Quotient.mk _
        (MvPolynomial.rename some c1'' - MvPolynomial.X none * MvPolynomial.rename some d1'')) := by
    apply regular_of_linear_elim (τ := τU1') (R := F p) [c0''] c1'' d1''
    · exact hd1''_opt_reg
    · rfl
  -- Bridge `hFu1'_reg_opt` (at `Option τU1'` level, prefix `[c0'']`) up to
  -- `τU1`'s ring (prefix `[Fu0']`), via `isSMulRegular_bridge_prefix_gen (F
  -- p) x0 [c0''] (c1'' - X x0 * d1'')` -- the SAME bridge instance
  -- `hFu0'_reg` used, now with a nonempty `gens'`.
  have hFu1'_reg : IsSMulRegular
      (MvPolynomial τU1 (F p) ⧸ Ideal.ofList [Fu0'])
      (Ideal.Quotient.mk (Ideal.ofList [Fu0']) Fu1') := by
    set g1 : MvPolynomial τU1' (F p) := c1'' - MvPolynomial.X x0 * d1'' with hg1_def
    have hbridge :
        IsSMulRegular
          (MvPolynomial τU1 (F p) ⧸
            Ideal.ofList (([c0''] : List (MvPolynomial τU1' (F p))).map (fun q : MvPolynomial τU1' (F p) =>
              ((MvPolynomial.renameEquiv (F p) (optionSplit x0)).symm (MvPolynomial.rename some q) :
                MvPolynomial τU1 (F p)))))
          (Ideal.Quotient.mk
            (Ideal.ofList (([c0''] : List (MvPolynomial τU1' (F p))).map (fun q : MvPolynomial τU1' (F p) =>
              ((MvPolynomial.renameEquiv (F p) (optionSplit x0)).symm (MvPolynomial.rename some q) :
                MvPolynomial τU1 (F p)))))
            ((MvPolynomial.renameEquiv (F p) (optionSplit x0)).symm
              (MvPolynomial.rename some g1)))
        ↔
        IsSMulRegular
          (MvPolynomial (Option τU1') (F p) ⧸
            Ideal.ofList (([c0''] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)))
          (Ideal.Quotient.mk
            (Ideal.ofList (([c0''] : List (MvPolynomial τU1' (F p))).map (MvPolynomial.rename some)))
            (MvPolynomial.rename some g1)) :=
      isSMulRegular_bridge_prefix_gen (σ := τU1) (F p) x0
        ([c0''] : List (MvPolynomial τU1' (F p))) g1
    -- `(renameEquiv (F p) (optionSplit x0)).symm ∘ rename some = rename
    -- (Subtype.val : τU1' → τU1)`, since `renameEquiv _ e` unfolds to `rename
    -- e`/`rename e.symm` on the two sides and `(optionSplit x0).symm ∘
    -- some = (Subtype.val : τU1' → τU1)` by `optionSplit`'s own construction
    -- (`Equiv.optionSubtype`) -- both `rfl`-provable compositions, so the
    -- whole bridge LHS collapses onto plain `rename (Subtype.val : τU1' →
    -- τU1)` applied to the `τU1'`-side list/element, matching `hFu0'_eq`/
    -- `hFu1'_eq`'s own RHS shape exactly.
    have hcollapse : ∀ q : MvPolynomial τU1' (F p),
        (MvPolynomial.renameEquiv (F p) (optionSplit x0)).symm (MvPolynomial.rename some q) =
        MvPolynomial.rename (Subtype.val : τU1' → τU1) q := by
      intro q
      show MvPolynomial.rename (optionSplit x0).symm (MvPolynomial.rename some q) =
        MvPolynomial.rename (Subtype.val : τU1' → τU1) q
      rw [MvPolynomial.rename_rename]
      congr 1
      funext v
      show ((optionSplit x0).symm) (some v) = v.val
      exact Equiv.optionSubtype_symm_apply_apply_some x0 (Equiv.refl τU1') v
    simp only [List.map_cons, List.map_nil, hcollapse] at hbridge
    have hLHS_eq : MvPolynomial.rename (Subtype.val : τU1' → τU1) c0'' = Fu0' := by
      rw [hFu0'_eq, map_sub, map_mul, MvPolynomial.rename_X]
    have hRHS_eq : MvPolynomial.rename (Subtype.val : τU1' → τU1) g1 = Fu1' := by
      rw [hg1_def, hFu1'_eq, map_sub, map_mul, MvPolynomial.rename_X]
    rw [hLHS_eq, hRHS_eq] at hbridge
    rw [hbridge]
    rw [show (MvPolynomial.rename (some : τU1' → Option τU1') g1) =
        MvPolynomial.rename some c1'' - MvPolynomial.X none * MvPolynomial.rename some d1'' by
      rw [hg1_def]
      simp only [map_sub, map_mul, MvPolynomial.rename_X]]
    exact hFu1'_reg_opt
  -- **Step F: `d'` is `IsSMulRegular` mod `Ideal.ofList [Fu0', Fu1']`
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
  sorry

end peelU1τNotation

set_option maxHeartbeats 200000

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
  isSMulRegular_bridge_prefix_gen (F p) x gens' g

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
  -- **Stages 2/6 (`Fu2`, `Fv2`: peel `U1`/`V1`, prefix `[Fu0,Fu1]`/
  -- `[Fv0,Fv1]`) and stages 8-11 (curve relations) are NOT closed this
  -- pass.** Stage 2/6 route through `isSMulRegular_den_of_second_peel`
  -- (§1), whose own remaining `sorry` (see that theorem's docstring,
  -- corrected this pass per the ChatGPT round-trip on
  -- `IsSMulRegular`-mod-a-principal-ideal) is a genuine open
  -- mathematical gap: `u1_den 1`/`v1_den 1` regular mod `⟨u1_num 0⟩`/
  -- `⟨v1_num 0⟩` needs `IsCoprime` (or "no shared irreducible factor"),
  -- NOT merely both nonzero in the domain `Rdec p` -- confirmed
  -- precisely by the ChatGPT consultation (`d'` regular mod `(c0)` in a
  -- UFD `iff gcd(c0,d') = 1`, with an explicit `F[x,y]`/`(xy)`/`x`
  -- counterexample showing "both nonzero" alone is insufficient). This
  -- coprimality is NOT currently a field of `Nondegenerate`/
  -- `CrossNondegenerate`, and it is NOT attempted here whether it
  -- follows from data already in scope (`hgcdA`/`hgcdB`/`hndA`/`hndB`
  -- govern `Ypoly`/`uRS` coprimality, a DIFFERENT pair of polynomials
  -- than `u1_num 0`/`u1_den 1` directly) -- left open, matching §1's own
  -- now-corrected docstring, rather than silently assumed. Stages 8-11
  -- route through `curveCoeffRegular`, whose OWN docstring already flags
  -- that the concrete curve-relation blob (`curveA1`, etc.) has not yet
  -- been shown to literally equal the abstract `quintic` shape after
  -- peeling -- also left open there, not re-derived here.
  --
  -- What IS established above (`hFu0_reg`, `hFv0_reg`, `hFu1_reg`,
  -- `hFu3_reg`, `hFv1_reg`, `hFv3_reg`): 6 of the 12 stages' underlying
  -- `IsSMulRegular` facts (`hFu0_reg`/`hFv0_reg` plain, in `Rdec p`
  -- itself -- the FIRST stage of a regular sequence has no preceding
  -- quotient to speak of; `hFu1_reg`/etc. genuinely quotient-shaped,
  -- `IsSMulRegular (Rdec p ⧸ Ideal.span {prev}) (mk next)`), fully
  -- proved, no `sorry`. Wiring these (plus the two still-open stages)
  -- into the actual 12-fold `IsRegular.cons'` chain -- converting each
  -- `Ideal.span`-shaped fact to the `QuotSMulTop`-shaped one
  -- `IsRegular.cons'` needs via §3.0's `isSMulRegular_quotSMulTop_of_span`,
  -- and correctly nesting each subsequent stage's ambient module -- is
  -- itself substantial remaining work, deferred to the next pass so the
  -- six genuinely complete facts above can be checked in the REPL
  -- independently first.
  sorry

end DecoupledSystem
end Genus2Lean
