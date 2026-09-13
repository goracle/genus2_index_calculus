# ZeroD extended file index (ZeroD-internal coverage complete)

**Purpose**: extend `DEGREE-BOUND-FILES-INDEX-README.md`'s per-file index
(35 files, all `totalDegree`/`IsRdecWitness` degree-bound content — its
own opening note previously mis-stated this as 33; corrected there) to
the rest of `ZeroD/`. Written the same way that file was: by reading each
file's imports, module docstring, and top-level declarations directly,
not copied from any roadmap's own summary or from `ZeroD-README.md`'s
one-line directory map (though nothing found here contradicts that map —
see "Relationship to `ZeroD-README.md`" below).

**Coverage: all 71 not-yet-indexed `.lean` files, across two passes**
(the 71 = all of `ZeroD/` minus the 35 the degree-bound index already
covers, minus three Emacs autosave files — `#CantorAddWitness.lean#`,
`#CurBeforeMonicCoeffTotalDegree.lean#`, `#QuadCoordBound.lean#` — which
are not real source and are excluded from every count in this document).
The first pass covered 40 files (Parts 1-4 below: `TheDataDerivation/`,
`Reduce/`, the top-level regular-sequence/degree-uniform chain, and the
`CAWitness*` family). This pass covered the remaining 31: the
`PrincipalWitness*` family (Part 5, 12 files), `ReducedClassBundles*`/
`ReducedClassDispatch` (Part 6, 6 files), and 9 further singletons
(Part 7 — two of which, `CleanWitness.lean` and `SymmetricCurveWitness.
lean`, turned out on cross-check to already be indexed in
`DEGREE-BOUND-FILES-INDEX-README.md` as files 34/35; the full write-up
for both now lives there only, with a pointer left at files 77/82 here,
so the true count of files this document adds beyond the degree-bound
index's own 35 is 69, not 71 — see that file's own opening note).
**Every `.lean` file inside `ZeroD/` is now described somewhere in one
of the two index documents** — see the "Not yet covered" section near
the bottom of this file for what remains (top-level `Genus2Lean/` files
only, an explicit stretch goal, not `ZeroD/`-internal).

**Sorry status, verified this pass** (comment-stripped scan, whole-word
`sorry` token, run across the entirety of `ZeroD/` — not just the files
below): **zero live sorries**, matching `ZeroD-STATUS.md`'s own last
verified count. Every file below is individually confirmed sorry-free as
of this pass (the `CAWitness*` family in Part 4 was re-checked file by
file, not just swept in the whole-directory total).

## Relationship to `ZeroD-README.md`

`ZeroD-README.md`'s "Directory map" section already summarizes most of
these files in one line each, and its "dependency chain, traced from
imports" ASCII diagram already lays out how `TheDataDerivation/` →
`DecoupledSystemRegular.lean` → `PeelChainAssembly.lean` →
`RegularSequenceFiniteQuotient.lean` → `AlphaLocusDegreeUniform*.lean`
chain together, plus the separate `Reduce/` branch. This document doesn't
replace that map — it goes one level deeper: full declaration lists,
each file's own stated status/REPL-confirmation claims, and enough of
each docstring's own reasoning to work from this file alone most of the
time instead of re-opening the `.lean` source. Read `ZeroD-README.md`
first for orientation; read this for detail once you know which file you
need.

---

## Part 1: `TheDataDerivation/` (4 files — the `theData` foundation)

Read in dependency order; each imports the previous. All four share the
`Genus2Lean.TheDataDerivation` namespace (opened in file 1, closed at the
bottom of file 4). Together these build `theData`, the K=2 symbolic-anchor
Mumford-reduction tower that everything else in `ZeroD/` sits on top of.

### 1. `TheDataDerivation/DataDerivationBasics.lean` (1224 lines)
Imports: `Mathlib` only.

First of four files splitting what was originally one oversized
`TheDataDerivation.lean`; purely organizational, no mathematical content
changed by the split. Builds: the symbolic base field `F p := ZMod p`
(replacing an earlier fixed numeral `curveP`), the curve polynomial
`curvePoly` (`f(x) = c0+c1x+c2x²+c3x³+c4x⁴+x⁵`, monic quintic, symbolic in
both `p` and `(c0,...,c4)`) with `curvePoly_natDegree`/`_ne_zero`/
`_natDegree_odd`, the squarefreeness/irreducibility machinery
(`not_isSquare_of_odd_natDegree`, `irreducible_X_sq_sub_C_of_not_isSquare`,
`RatFunc.not_isSquare_algebraMap_of_odd_natDegree`,
`sq_sub_curve_irreducible`, `fAtT_not_isSquare`/`fAtT_i_not_isSquare`/
`fAtT_prod_not_isSquare`, `quadratic_extension_square_criterion`,
`fAtT_p_not_isSquare`), and the Riemann–Roch basis combinatorics
(`rrBasisCandidates`, `rrBasis5`, `rrBasis5_flag`, `xmodUTable`,
`reduceMonomialModU`, `uPoly_monic`, `xmodUTable_correct`). **Own
docstring claims "none of this has been checked against an actual Lean
toolchain" — stale, per this project's working agreement build is now
green project-wide; not fixed this pass (out-of-scope, no Lean edits this
session), flagged here so the next person doesn't need to rediscover it.**
**Status: sorry-free** (confirmed by this pass's project-wide scan).

### 2. `TheDataDerivation/DataDerivationTower.lean` (220 lines)
Imports: `DataDerivationBasics`.

Second of four. Builds §4.2 item 3: the fraction field `K0` (the
fraction field of `MvPolynomial (Fin 2) (F p)`, deliberately an `abbrev`
rather than a `def` so instance search unfolds it — **not** Mathlib's
single-variable `RatFunc`, flagged explicitly as a trap to avoid), then
the two-step tower `K1`, `K2` via `AdjoinRoot`. `t0`, `fAtT` set up the
two symbolic anchor abscissas; `w1`/`w2` are the corresponding adjoined
ordinates. **Both field instances were previously bare `axiom`s and are
now real theorems**: `factIrreducible_K1_proved` (from `curvePoly`'s odd
degree) and `factIrreducible_K2_proved` (from the quadratic-extension
square criterion plus non-squareness of `fAtT ... 1` and
`fAtT ... 0 * fAtT ... 1` in `K0`) back the `factIrreducible_K1`/
`factIrreducible_K2` instances. Needs `[Fact (p ≠ 2)]` from here on —
`factIrreducible_K2`'s square criterion genuinely needs `char ≠ 2` (so
`2xy=0 ⟹ xy=0`). **Status: sorry-free.**

### 3. `TheDataDerivation/DataDerivationSolve.lean` (2399 lines)
Imports: `DataDerivationTower`.

Third of four, the largest of the tower files. Builds §4.2 items 4–5 (the
`4×4` Cramer's-rule linear solve — `matrixA`, `rhsVec`,
`MatrixNondegenerate`, `cramerSolution`, `coeffsOut`, `Epoly`, `Ypoly`,
`fAtX`, `Npoly` = `E²-fY²`) and item 6 (exact division of `Npoly` by
`(X-t1)`, `(X-t2)`, and the target `u(x)`). The combinatorial scaffolding
(`yIdx`, `otherIdx`, `otherMap`, `otherMap_injective`/`_surjOn`,
`sum_otherIdx_add_y`, `coeffsOut_otherMap`) isolates which RR-basis slot
carries the `y`-coefficient so `matrixA`'s row/column unfolding has a
clean case split. `anchor1`/`anchor2` (the two symbolic anchor points as
`K2`-pairs) get `anchor1_ne_anchor2`/`anchor1_coprime_anchor2`,
`anchor{1,2}_defining_eq`, and (this file's headline result)
`anchor{1,2}_curve_relation` — split into a purely-definitional half
(`w{1,2}_sq_eq`) and an eval/algebraMap-compatibility half
(`fAtX_eval_anchor{1,2}_eq`), both fully proved by directly-verified
Mathlib4 lemma names rather than guessed ones. `dvd_N_anchor1`/
`dvd_N_anchor2`/`dvd_N_u` (the three factors of `Npoly`'s divisibility)
are all fully proved, closing what this file's own docstring calls "the
remaining item-6 gaps." `IsMumfordTarget`, `curBeforeMonic`, and the
not-yet-a-root/coprimality lemmas (`anchor{1,2}_not_isRoot_U`,
`anchor{1,2}_coprime_U`) round out the exact-division chain, culminating
in `Npoly_eq_curBeforeMonic_mul`. **Own docstring still says "no Lean
toolchain was available this pass" for the newly-closed lemmas — same
stale-build-status caveat as file 1, not fixed this pass.** **Status:
sorry-free.**

### 4. `TheDataDerivation/DataDerivationMumford.lean` (1079 lines)
Imports: `DataDerivationSolve`, `DataDerivationTower`.

Fourth and last of four. Builds §4.2 items 7–8 (`uRS`, the monic
normalization of `curBeforeMonic` — `uRS_monic` proved via
`Polynomial.natDegree_C_mul_eq_of_mul_eq_one`, confirmed against
Mathlib4 source rather than guessed; `vRS` via the mod-`uRS` inverse; the
Mumford identity `vRS_sq_eq_f_mod_uRS`, `v_RS² ≡ f mod u_RS`, taking
`hcur`/`hNu`/`hInv` as explicit threaded hypotheses rather than
re-deriving them) and the un-numbered "bridge to `Rdec`" section
(`SideGens`, `baseFracToRing`, `towerToRdecK1`, `towerToRdec`,
`towerToRdec_vars_subset`/`_den_vars_subset`,
`adjoinRoot_quadratic_normal_form`, `towerToRdecK1_spec`,
`towerToRdec_spec`) — the denominator-clearing machinery that lets
`DecoupledSystemRegular.lean` assemble `theData` from a symbolic tower
element down to a concrete `Rdec p` (`MvPolynomial`) ring element. **This
file's own docstring history is worth reading if you need to trust its
claims**: earlier passes had `vRS`'s coprimality/Mumford-identity content
as `sorry`, since fixed once `DataDerivationSolve.lean`'s `dvd_N_u`
closed — the docstring narrates this evolution explicitly rather than
silently overwriting the earlier claim, matching this project's
stale-claim-tracking convention. **Status: sorry-free** (this file's own
"later pass" note already says so; reconfirmed by this pass's scan).

---

## Part 2: `Reduce/` (7 files — the K=4 Cantor-reduction algorithm)

This directory **is** "task (A)"/"`Reduce`" from `ROADMAP-alpha-locus.md`
(per `ZeroD-README.md`'s own directory map) — not a stub. All seven files
share the `Genus2Lean.TheDataDerivation` namespace (same as Part 1, not a
typo) and import `DataDerivationBasics` for `F p`/`curvePoly`/
`rrBasisCandidates`/`xmodUTable`/`reduceMonomialModU`, reused unchanged.

### 5. `Reduce/AlphaReduce.lean` (4211 lines)
Imports: `DataDerivationBasics`.

The largest file in `ZeroD/`. Re-derives `DataDerivationSolve.lean`'s
K=2 Cramer's-rule/exact-division pattern for **K=4** anchors over plain
`F p` (no tower/field-extension needed here — unlike the K=2 case, the
four anchors — `P1`, `P2`, and `(u_a,v_a)`'s own two roots — are concrete
field elements, not symbolic curve-relation variables). Builds
`rrBasis7` (`nb=7`, proved-not-asserted literal value via a `Perm`+
`Sorted`-uniqueness route that sidesteps a Lean 4.19+ kernel-irreducibility
blocker on `mergeSort`, lean4#5192 — the same technique
`chatgpt_prompt_mergesort_decide.md` supplied), the K=4 combinatorial
layer (`otherMap4`, `sum_otherIdx7_add_y`, `coeffsOut4_otherMap`),
`matrixA4`/`rhsVec4`/`MatrixNondegenerate4`/`cramerSolution4`/
`coeffsOut4`/`Epoly4`/`Ypoly4`/`Npoly4`/`curBeforeMonic4`, and — the key
design decision this file's own header calls out — treats `(u_a,v_a)`'s
two "extra" anchors as ONE quadratic-factor row-block (`u_a` divides
directly, no root-splitting) rather than as two literal points, avoiding
having to decide whether `u_a` splits over `F p`. `uRS4`/`vRS4` (monic
normalization / mod-inverse, mirroring `DataDerivationMumford.lean`
exactly) and `vRS4_sq_eq_f_mod_uRS4` (the K=4 Mumford identity) are built.
The combining step — `uRS4 ∣ Npoly4` from the four separate
`dvd_N_P1`/`dvd_N_P2`/`dvd_N_ua`/`dvd_N_u4` facts — is closed via
`prod_dvd_of_pairwise_coprime_four`, needing **six pairwise-coprimality
hypotheses** (`h12`, `h13`, ..., all six pairs) as raw assumptions; this
is the gap `SharedRootCombining.lean`/`GeneralSharedRoot.lean`
subsequently relax. `Reduce`/`ReduceTangent`/`ReduceDispatch` (the actual
`F p × F p × F p × F p`-valued output functions) are defined at the very
end. A separate tangent-anchor branch (`dvd_N_P1P2_tangent`,
`curBeforeMonic4Tangent`, `uRS4Tangent`, `vRS4Tangent`,
`vRS4Tangent_sq_eq_f_mod_uRS4Tangent(_full)`) handles the `m=2`
(`P1=P2` or another pairwise coincidence) case, using
`rootMultiplicity_ge_two_of_eval_derivative_eq_zero`/
`sq_dvd_of_eval_derivative_eq_zero` for the confluent-root argument.
**Own docstring is an unusually long, honestly-narrated history of
several superseded "not yet started"/"still open" claims — read its
final paragraph, not its middle sections, for the accurate as-of-now
state.** **Confirmed against Claire's REPL: this whole file compiles
clean, 0 errors** (two Taylor-shift argument-order bugs in
`comp_X_add_C_coeff_one`/`_zero`, fixed). **Status: sorry-free.** **What
remains open per the file's own final accounting**: (1) `Reduce`'s
*correctness* (that its output really is the Mumford reduction of
`alpha•a - P1 - P2`) is not proved — `Reduce` itself is fully defined and
its underlying machinery is fully wired, but no theorem here connects the
two; (2) the six-coprimality hypothesis bundle `uRS4_dvd_Npoly4`/
`vRS4_sq_eq_f_mod_uRS4` needs is exactly task (B)'s `Bad` exceptional-locus
question from `ROADMAP-alpha-locus.md`, not derived from anything smaller
here.

### 6. `Reduce/SharedRootCombining.lean` (426 lines)
Imports: `DataDerivationBasics`, `AlphaReduce`.

Relaxes exactly one of file 5's six coprimality hypotheses:
`IsCoprime u_a target` (`h34`) is **false** whenever `alpha•a` and the
target divisor share a Jacobian-point root — not an excludable
measure-zero coincidence for a generic genus-2 curve. Fix: replace the
`u_a`/`target` factor pair by `lcm u_a target` (`lcm_dvd_of_dvd_dvd`,
via `EuclideanDomain.lcm_dvd`, unconditional — no coprimality needed for
this step). What remains is combining `lcm u_a target` (degree ≤4,
exactly 3 in the shared-root case) with `P1`/`P2` — now only **four**
hypotheses instead of six (`prod_dvd_of_coprime_to_lcm`). Builds
`uaTargetLcm4`, `npoly4_dvd_of_shared_root`,
`npoly4_quotient_eq_lcm_mul_of_shared_root`,
`curBeforeMonic4LcmShared`/`uRS4LcmShared`/`vRS4LcmShared` (parallel
LCM-based versions of file 5's objects), `vRS4LcmShared_sq_eq_f_mod_
uRS4LcmShared`, and the disjunctive wrapper
`uRS4_dvd_Npoly4_or_shared_root` (either the original six-hypothesis
route succeeds, or the shared-root LCM route does). **Status:
sorry-free.**

### 7–10. `Reduce/P1TargetSharedRoot.lean` (444 lines), `Reduce/P1UaSharedRoot.lean` (380 lines), `Reduce/P2TargetSharedRoot.lean` (383 lines), `Reduce/P2UaSharedRoot.lean` (380 lines)
Imports: each imports `DataDerivationBasics`, `AlphaReduce`,
`SharedRootCombining`; the `P1*` files additionally import each other
(`P1UaSharedRoot` imports `P1TargetSharedRoot`, `P2TargetSharedRoot`
imports `P1TargetSharedRoot`, `P2UaSharedRoot` imports
`P1TargetSharedRoot`) — a naming/ordering artifact, not a real dependency
each actually needs.

**Four near-identical one-off files, each relaxing a single different
pairwise-coprimality hypothesis the same way file 6 relaxes `h34`**: `P1`
vs `target` (file 7, `h14`), `P1` vs `u_a` (file 8), `P2` vs `target`
(file 9), `P2` vs `u_a` (file 10). Same shape every time: an `xxLcm4`
def, `npoly4_dvd_of_xx_shared_root`, `npoly4_quotient_eq_xx_lcm_mul_of_
shared_root`, `curBeforeMonic4XxShared`/`uRS4XxShared`/`vRS4XxShared`,
`vRS4XxShared_sq_eq_f_mod_uRS4XxShared`, and a disjunctive
`uRS4_dvd_Npoly4_or_xx_shared_root` (plus, in files 7/9 — the `*Target*`
pair only — a further `vRS4_sq_eq_f_mod_uRS4_or_xx_shared_root`). File 7
additionally proves `isCoprime_X_sub_C_iff_eval_ne_zero` (`IsCoprime
(X-C a) q ↔ q.eval a ≠ 0`, over any field — the sharper linear-vs-quadratic
characterization these four files' "linear anchor/target vs the other
factor" case gets that file 6's quadratic-vs-quadratic case doesn't need).
**All four are superseded in scope by file 11 (`GeneralSharedRoot.lean`)
— see that file's own docstring, which explicitly names this exact
four-file family as what it replaces** (a `2^6`-pattern combinatorial
explosion problem: once more than one pairwise-coprimality hypothesis can
fail simultaneously, none of files 6–10 individually apply, and a further
one-off file per new collision pattern doesn't scale). Not deleted — kept
as-is, still compiling, still sorry-free — but file 11 is what to reach
for on new work, not these. **Status (all four): sorry-free.**

### 11. `Reduce/GeneralSharedRoot.lean` (1693 lines)
Imports: `DataDerivationBasics`, `AlphaReduce`, `SharedRootCombining`.

**The general replacement for the whole files 6–10 family** (per its own
docstring, quoted almost verbatim in file 7–10's entry above). Two
load-bearing theorems need no case enumeration at all: (1)
`lcm_dvd_of_four_dvd` — for ANY four divisors of `N` in a Euclidean
domain, `lcm(lcm q1 q2)(lcm q3 q4) ∣ N`, **zero** coprimality hypotheses,
absorbing every one of the `2^6` possible collision patterns at once
(`lcm` is idempotent regardless of *why* two factors aren't coprime); (2)
`not_coprime_quadratics_iff` — two monic quadratics over `F p` fail to be
coprime iff they share a literal root in `F p` **or are equal outright**
(the Galois-collapse fact Claire asked to double-check: if `u_a` is
irreducible and shares one root with `target` in the splitting field
`F p²`, Frobenius forces the other root to match too). The rest of the
file (`GeneralQuotient`/`GeneralOutput`/`MumfordIdentity4General`/
`ReduceDispatchGeneral`, using fact (1)) is the actual wiring:
`npoly4Lcm4` combines all four `Npoly4` factors via nested `lcm`
UNCONDITIONALLY (`npoly4Lcm4_dvd_Npoly4`); `curBeforeMonic4General`/
`uRS4General`/`vRS4General` are the corresponding general objects, with
`uRS4General_dvd_Npoly4` now holding unconditionally too — **this is a
genuine correctness fix, not a repackaging**, since file 5's
`uRS4`/`curBeforeMonic4` are silently WRONG (drop a remainder) whenever
any of the six original hypotheses fails, while `uRS4General` sidesteps
this by construction; `vRS4General_sq_eq_f_mod_uRS4General` is the
hypothesis-free Mumford identity; `ReduceGeneral`/`ReduceDispatchGeneral`
are `Reduce`'s output read off the general objects (`ReduceDispatchGeneral`
is the actual Cantor-reduction algorithm `GeneralSharedRoot.lean`'s own
header calls "the thing task (A) in `ROADMAP-alpha-locus.md` originally
called unstarted"). Sharper case-analysis theorems
(`isCoprime_linear_pair_of_ne`, `isCoprime_quadratic_pair_of_ne_of_no_
shared_root`, `isCoprime_X_sub_C_of_not_isRoot`,
`isCoprime_lcm12_lcm34_of_no_shared_root`, `monicQuadratic_eq_
reconstruct`, `lcm_eq_C_leadingCoeff_inv_mul_of_monic_coprime`,
`quadratic_eq_mul_X_sub_C`) sharpen `npoly4Lcm4`'s degree down to exactly
6 (`npoly4Lcm4_natDegree_eq_six`) under an explicit no-shared-root
hypothesis, and pin `ReduceGeneral`'s output as an honest
`IsMumfordTarget4` instance (`ReduceGeneral_isMumfordTarget4`). **Status:
sorry-free.** Per `ZeroD-README.md`'s own directory map: "in good shape,
not a live risk" — proved correct at the polynomial level, worth a REPL
re-confirmation before building directly on top of it but not where this
project's risk currently sits.

---

## Part 3: top-level `ZeroD/` regular-sequence / degree-uniform chain (10 files)

The main dependency spine `ZeroD-README.md`'s ASCII diagram traces from
`TheDataDerivation` down through `decoupledSystem_degree_uniform`.

### 12. `DecoupledSystemRegular.lean` (3190 lines)
Imports: `TheDataDerivation.DataDerivationMumford`.

Builds the 12-variable matching system `01_elim2_main.jl`'s
`build_decoupled_system` constructs: `Idx` (the 12-variable index type),
`Rdec` (`MvPolynomial Idx (F p)`), `DecoupledGenerators`, `SampleTarget`
(the `alpha`-agnostic `(u0,u1,v0,v1)` bundle), `theData` (assembled from
`TheDataDerivation`'s `uRS`/`vRS`/`towerToRdec` — **not** left opaque, per
this file's own "Update this pass" note, though the assembly does carry
four explicit hypotheses `hcurA/B`/`hgcdA/B` inherited from
`TheDataDerivation`'s own exceptional-locus conditions), `FuList`/
`FvList`/`genList` (the actual 12 generators), and — the bulk of the
file's real mathematical content — a chain of generic commutative-algebra
regularity lemmas building toward "is this list a regular sequence":
`regular_linear_of_regular_coeff`, `regular_of_linear_elim`,
`regular_of_norm_eliminate_one`/`regular_of_norm_eliminate`,
`aeval_X_comp_injective_ne_zero`, `towerToRdec_den_ne_zero`,
`Nondegenerate`/`uRS_coeff_ne_zero`/`vRS_coeff_ne_zero`, `denRegular`,
`CrossNondegenerate` (bundling the `hu0`/`hu1`/`hv0`/`hv1` per-instance
exceptional-locus hypotheses — **by this struct's own docstring,
*designed* to be false for many curves, not a target for future
unconditional proof, per `ZeroD-STATUS.md`'s later-pass note**),
`MvPolynomial.isSMulRegular_C_of_isSMulRegular`, `regular_of_disjoint_
extension(_list)`, `regular_of_extension_into_algebra`,
`isSMulRegular_of_mul_eq_of_isSMulRegular`, `peelEquivGen`/`peelEquiv`,
`Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular`,
`regular_of_peeled_leadingCoeff`, `quintic`/`quintic_monic`,
`curveCoeffRegular`. **The file's own §6 header is explicitly flagged as
STALE HISTORY, not current** — it originally stated (and its docstring
narrates this honestly) that `decoupledSystem_isRegularSequence`/
`decoupledSystem_zeroDimensional` lived here and were `sorry`-backed via
an abandoned "eight/four-variable" route; both theorems have since
**moved to `AlphaLocusDegreeUniform.lean`** (file 15 below) and are
proved there via the peel-chain approach instead (file 13). Nothing
upstream of that move (`Idx`, `Rdec`, `SampleTarget`, `theData`,
`genList`, `Nondegenerate`, `CrossNondegenerate`) changed — this file
stays scoped to fixed-target machinery, agnostic to where the target
came from. **Status: sorry-free** — every `sorry` mention still in the
file's prose is historical narration of a since-superseded route, not a
live tactic use (confirmed by this pass's scan).

### 13. `PeelChainAssembly.lean` (3798 lines)
Imports: `TheDataDerivation.DataDerivationMumford`, `DecoupledSystemRegular`.

Split out of `DecoupledSystemRegular.lean` at Claire's request once that
file got unwieldy; only imports it, restates nothing. Builds
`regularSeq_of_peel_chain`: the actual 12-stage regular-sequence
assembly, peeling `genList`'s twelve generators one variable at a time
via `regular_of_linear_elim`/`Polynomial.Monic.isRegular`
(`isSMulRegular_of_ringEquiv_of_mapsTo`, `isSMulRegular_bot_iff`/`_module_
iff`, `optionSplit`, `isSMulRegular_bridge_prefix_gen`/`_prefix`,
`isSMulRegular_C_const_of_isSMulRegular`, `isSMulRegular_quotient_span_
singleton_of_isCoprime`, `rename_optionSplit_some`/`_linear`/`_symm_some`,
`peelU1Idx`, `regular_of_second_linear_elim`,
`isSMulRegular_den_of_second_peel`, `peelEquivGen_eq`,
`quotSMulTop_equiv_span`, `isSMulRegular_quotSMulTop_of_span`,
`isRegular_quotSMulTop_of_span`, a local `IsRegular` structure extending
`IsWeaklyRegular`, `ideal_smul_top_eq_self`, `isSMulRegular_first_gen`).
Explicitly SUPERSEDES three superseded design-note files
(`04_design_notes.md`/`05_notes.md`/`06_final_design.md`, kept alongside
in `oldroadmaps/` for history) and corrects a false alarm one of them
raised about `CrossNondegenerate`'s fields being stated against the wrong
ideal (they aren't — `isRegular_cons_iff'` only ever needs regularity mod
the single most-recently-adjoined generator, matching `CrossNondegenerate`'s
existing single-step shape). **`PeelChainNondegenerate`** (a new structure,
mirroring `Nondegenerate`/`CrossNondegenerate`'s own convention) bundles
what the file's docstring calls "Gap A" (stage 2/3/6/7 cross-index
regularity — `hu01`/`hv01`/`hu1_full`/`hv1_full` plus, per a later
correction, `hv0_ext`–`hv3_ext` for stages 4–7) and "Gap B" (stage 8–11
curve-relation regularity, `hcurveA1/A2/B1/B2`) as genuine per-instance
exceptional-locus hypotheses. **Own docstring narrates a real
mid-project correction**: the originally-hoped-for route for stages 4–7
(extending same-side sub-prefix facts to the full prefix via a
disjoint-variable-block bridge, `gapA_disjoint_bridge`) turned out to be
**unsatisfiable for this project's actual variable-sharing pattern** — a
ChatGPT consultation supplied a concrete counterexample — so
`gapA_disjoint_bridge` remains in the file, proved, but **unused**;
stages 4–7 instead take their full-prefix facts as four new raw
hypotheses (`hv0_ext`–`hv3_ext`). `regularSeq_of_peel_chain` itself also
takes `htop_ne_smul` (**"Gap C"**: the full ideal's properness / existence
of a common solution point) as an explicit hypothesis — genuine separate
mathematics, not attempted here (this is the same `htop_ne_smul` gap
`ZeroD-README.md`'s "Open gaps" item 3 discusses at length, and which
`MvPolynomialSharedTargetSolve.lean`/`TowerToRdecRenameSymmetry.lean`,
both already covered in the degree-bound index, subsequently make partial
progress on). **Status: `regularSeq_of_peel_chain` and its private
12-way case-split helper `regularSeq_of_peel_chain_assembly` both have
zero tactic-position `sorry`s** (own docstring's explicit claim, matching
this pass's project-wide scan).

### 14. `RegularSequenceFiniteQuotient.lean` (317 lines)
Imports: `Mathlib` only.

**Generic commutative algebra — no `Genus2Lean`-specific content**, per
`ZeroD-README.md`'s own directory map. Factored out purely so
`decoupledSystem_zeroDimensional` (file 15) can be a one-line
instantiation rather than a bespoke 12-variable argument. Main result:
`Module.Finite.quotient_of_isRegular_of_length_eq_card` — if
`rs : List R` is `IsRegular` on `R = MvPolynomial ι k` (`k` a field, `ι`
finite) and `rs.length = Nat.card ι`, then `R ⧸ Ideal.ofList rs` is a
finite-dimensional `k`-vector space. **Own docstring records a genuine
retracted false claim, worth reading if you're tempted to reuse the
retracted statement**: an earlier version of this file's key lemma
(`ringKrullDim_quotient_ofList_le_zero`, "`rs.length = ringKrullDim R`
alone implies the quotient is 0-dimensional") is **FALSE**, not merely
unproved — counterexample `R=k[x,y]`, `rs=[x,x]`: `Ideal.ofList`
collapses the duplicate to `Ideal.span {x}`, giving `R⧸(x) ≅ k[y]` with
`ringKrullDim=1≠0`. Krull's height theorem only bounds height from
*above* by generator count; it says nothing about whether that many
generators actually cut dimension down that much. Diagnosed via a
ChatGPT consultation, verified against Mathlib4 source directly (not
taken on faith), and the false lemma was **deleted outright**, not kept
as a stub — replaced by an explicit regular-sequence Krull-dimension
induction (`isSMulRegular_self_iff_mem_nonZeroDivisors`,
`smul_top_eq_span_singleton`, `quotSMulTop_isRegular_congr`,
`ringEquiv_quot_cons_ofList`, `ringKrullDim_quotient_ofList_cons_add_
length_le`, `ringKrullDim_quotient_ofList_add_length_le_of_isRegular`,
`ringKrullDim_quotient_ofList_eq_zero_of_isRegular`) using the correct
`IsRegular`-hypothesis-based dimension-drop argument instead. **Do not
resurrect the deleted lemma verbatim** — any replacement needs the
`IsRegular`/full-height hypothesis baked in from the start. **Status:
sorry-free**, including the file's own headline arithmetic gap
(`hlen'`, `rs.length = ringKrullDim (MvPolynomial ι k)`), closed this
pass via `MvPolynomial.ringKrullDim_of_isNoetherianRing` +
`ringKrullDim_eq_zero_of_field`, both confirmed against Mathlib4 source.

### 15. `AlphaLocusDegreeUniform.lean` (1294 lines)
Imports: `DecoupledSystemRegular`, `Genus2Lean.DivisorClassGroup`,
`Reduce.AlphaReduce`, `Reduce.GeneralSharedRoot`, `PeelChainAssembly`,
`RegularSequenceFiniteQuotient`, `Genus2Lean.PrincipalDivisorSubgroup`,
`SanchorEqAlphaPoints`, `PrincipalWitnessCAConnection`.

**The organizing file for the whole `alpha`-parametrized picture**, per
its own header: where `SampleTarget` gets connected to an actual `alpha`
and the Jacobian (task (A) from `ROADMAP-alpha-locus.md`), and where
`decoupledSystem_degree_uniform` — **the target theorem this entire
`ZeroD/` effort exists to state and prove**, per `ZeroD-README.md`'s
one-sentence goal — actually gets stated. Own docstring is explicit about
what is and is not honest here: general Cantor/Mumford reduction from an
arbitrary divisor class down to Mumford normal form is genuinely not what
gets proved (`Reduce`, defined in `AlphaReduce.lean`, only reduces the
`P1,P2` + `(u_a,v_a)`-anchor shape, and its own *correctness* is still
open per that file's entry above) — so `SampleTargetFromAlpha` packages
`alpha`/`P1`/`P2` together with a **hypothesis field** asserting
`(u0,u1,v0,v1)` is what `Reduce` *would* produce, stated as a
specification rather than computed, mirroring how `DecoupledGenerators`
already handles `Fu_decoupled`/`Fv_decoupled`. Builds `alphaPairDelta`,
`isReduction'`/`isReductionOf`, `IsSmallExceptionalSet`, and (**both
proved outright, per this pass's confirmation — a real milestone flagged
explicitly in the file's own docstring**) `decoupledSystem_
isRegularSequence` (calling `regularSeq_of_peel_chain`, file 13) and
`decoupledSystem_zeroDimensional` (calling file 14's `Module.Finite.
quotient_of_isRegular_of_length_eq_card`, via the bridging lemma
`ideal_span_toFinset_eq_ofList`). **The headline target theorem,
`decoupledSystem_degree_uniform`, is ALSO now proved — but its proof is
flagged by `ZeroD-README.md`'s own "Open gaps" item 2 as CIRCULAR and
needing to be redone, not merely re-verified**: it closes via
`GenericPeelChainHyp`, a hypothesis bundle whose `hfinrank_le` field
states the uniform bound itself as an assumption (`Bad := ∅` witnesses
the existential) — this is the goal restated as its own premise, not a
weakened-but-honest hypothesis in the `Nondegenerate` style. Resolving
this is exactly what the degree-bound index's 33-file effort (files 1–33
of `DEGREE-BOUND-FILES-INDEX-README.md`) exists to make possible — once a
real uniform bound is proved, `GenericPeelChainHyp` should be replaced
with the actual proved pieces, not re-collapsed into one bundle. Also
defines `reducedClass_eq_of_isReduction'` — the fully-split-anchor,
fully-split-target case; **six further case-split siblings live in
other files** (files 16–19 below plus `ReducedClassBundlesCross{1-4}.lean`,
not yet indexed here — see "Not yet covered"). **Status: sorry-free.**

### 16. `AlphaLocusDegreeUniformTangent.lean` (612 lines)
Imports: `AlphaLocusDegreeUniform`, `PrincipalWitnessFinalAssemblyTangent`.

The **anchor-tangent** (`Ra1 = Ra2`, one doubled anchor point) sibling of
`reducedClass_eq_of_isReduction'` — that theorem's own `hRa12Xne : Ra1.X
≠ Ra2.X` hypothesis rules the tangent case out by construction, so it
needs its own file rather than a case split inside the original.
Target-side (`T1`,`T2`/`S`/`u`/`v`) machinery is completely unchanged
from the split theorem; only the anchor side is swapped for its tangent
counterpart (`Sanchor_eq_of_anchor_roots_tangent`, membership-only rather
than cardinality-based, since `Sanchor.card = 1 ≠ 2` in this case;
`divToPair_negVa_one_Sanchor_eq_tangent`; `cAmιTmδmιδ_mem_of_le_tangent`).
Builds `hDP_tangent_aux` as a genuinely **separate top-level theorem**
from the main result, unlike the split file's inlined `have` — the file's
own docstring documents a real, hard-won reason: inlining the ~35 binders
directly (to mirror the split file) hits a `whnf` elaboration timeout,
because this file's `caTangentInterpMatrix`/`uCANewTangent`/`bCATangent`/
`denomPolyCATangent` zone is more expensive to elaborate than the split
file's structurally-parallel zone. Builds `TangentCoefficientData`/
`TangentReductionData`/`TangentAssemblyData`, `tangent_anchor_sum_of_data`,
`target_sum_of_data`, culminating in
`reducedClass_eq_of_isReduction'_tangent`. **Status: sorry-free.**

### 17. `AlphaLocusDegreeUniformTangentTarget.lean` (542 lines)
Imports: `AlphaLocusDegreeUniform`, `AlphaLocusDegreeUniformTangent`,
`PrincipalWitnessFinalAssemblyTangentTarget`.

The **target-axis mirror** of file 16 — where file 16 doubles the
*anchor* pair (`Ra1=Ra2`), this file doubles the *target* pair
(`sa.P1=sa.P2`, one doubled target point `PtP`), which the split
theorem's `hcur`/`hgcd` split-branch construction otherwise rules out.
Anchor side is completely unchanged from the split theorem here (mirror
image of file 16's own restriction) — `Sanchor_eq_of_anchor_roots`
(the ORIGINAL, non-tangent version) and `divToPair_negVa_one_Sanchor_eq`
are reused verbatim for the anchor side, while the target side gets
`Sanchor_eq_of_anchor_roots_tangent`/`divToPair_negV_one_S_eq_tangent`
(same lemmas file 16 used for its anchor side, reused here for the
target side instead — both fully generic in naming already, per that
file's own docstring). Same two-theorem split as file 16 for the same
elaboration-cost reason (`hDP_tangent_target_aux` isolated from the main
theorem). Builds `TangentTargetCoefficientData`/`TangentTargetReductionData`/
`TangentTargetAssemblyData`, `anchor_sum_of_data_target_tangent`,
`target_sum_of_data_tangent`, culminating in
`reducedClass_eq_of_isReduction'_tangent_target`. **Status: sorry-free.**

### 18–21. `AlphaLocusDegreeUniformCross1.lean` (421 lines), `AlphaLocusDegreeUniformCross2.lean` (421 lines), `AlphaLocusDegreeUniformCross3.lean` (415 lines), `AlphaLocusDegreeUniformCross4.lean` (407 lines)
Imports (all four): `AlphaLocusDegreeUniform`,
`CAWitnessCrossTangentMemOfLe` (not yet indexed — see "Not yet covered").

**Four parallel files, one per anchor/target-point confluence case**:
Cross1 = `Ra1 = ι(sa.P1)`, Cross2 = `Ra1 = ι(sa.P2)`, Cross3 =
`Ra2 = ι(sa.P1)`, Cross4 = `Ra2 = ι(sa.P2)` (`ι` = the hyperelliptic
involution). These are genuinely simpler than files 16/17's tangent
cases, per Cross1's own docstring: the anchor pair `{Ra,Ra2}` (or
whichever pair is not the confluent one) **stays split** — confluence
here is between one anchor point and one *involution-image* target
point, the only surviving sub-case per `ROADMAP-cawitness-tangent-
interpolation.md`'s Part B case-3 analysis (the same-point alternative is
ruled out by `hRaY_ne`/`hchar`). Consequently `Sanchor`'s own
construction (`Sanchor_eq_of_anchor_roots`, `divToPair_negVa_one_
Sanchor_eq`) carries over **completely unchanged** from the split
theorem in all four files — what actually changes is: (1) the confluent
target point is no longer free, forced via an explicit identity
hypothesis (e.g. `hP1eq : sa.P1 = Point.iota Ra` for Cross1); (2) the
four free points feeding the CA-witness interpolation matrix collapse to
three plus a derivative datum (`caCrossInterpMatrix`/`caCrossCoeff`/
`bCACross`/`uCANewCross`/`denomPolyCACross`, matching whichever
`cAmιTmδmιδ_mem_of_le_crossN` signature `CAWitnessCrossTangentMemOfLe.lean`
supplies); (3) the six-hypothesis coprimality family collapses to just
**three** nondegeneracy hypotheses (confirmed by a sympy check per the
roadmap); (4) the now-forced point's curve-membership/non-root facts are
DERIVED from the free point's (via `Point.iota_X`/`Point.iota_Y`) rather
than assumed independently. Each file's single theorem is named
`reducedClass_eq_of_isReduction'_crossN_flat` (`N`∈{1,2,3,4}) — the
`_flat` suffix distinguishes these from the (not yet indexed)
`ReducedClassBundlesCrossN.lean` files' own `reducedClass_eq_of_
isReduction'_crossN` theorems, which appear (by name similarity, not yet
confirmed by reading those files) to be a bundled restatement of the
same case over shared `CoefficientData`/`ReductionData` — **check both
before assuming which one a call site wants**. **Status (all four):
sorry-free.**

---

## Part 4: `CAWitness*` family (22 files) — the single-witness Cantor interpolation

**Supersedes the earlier two-witness plan** (`TangentMumfordWitness.lean`'s
`f+` and `CantorAddWitness.lean`'s `f-`, both still separately in
`ZeroD/`, not yet indexed — see "Not yet covered"). Per `CAWitness.lean`'s
own opening correction: building two independent interpolations and
hoping their residuals coincide can never work by construction, since
nothing forces two unrelated 4-point Vandermonde solves to land on the
same residual quadratic. The fix, used throughout this whole family:
build ONE function `f := y - b(x)` interpolating `C - A` directly (`C :=
[Ra1]+[Ra2]`, `A := [P1]+[P2]`, via `C + ι(A)`, `ι` the hyperelliptic
involution), and let its residual quadratic BE the target `T` by
construction — no separate matching proof needed. All 22 files below
build variants of this single idea: split case, anchor-tangent
(`Ra1=Ra2`), target-tangent (`sa.P1=sa.P2`), and all four cross-pair
tangent cases (one anchor point confluent with one — involution-imaged —
target point).

### 34. `CAWitness.lean` (477 lines)
Imports: `HyperellipticFunctionField`, `AffinePoints`, `DivisorClassGroup`,
`PrincipalDivisors`, `PrincipalDivisorSubgroup`, `LCanonicalElementary`,
`Reduce.GeneralSharedRoot`.

**The base (fully-split) case, and the file every other `CAWitness*` file
either mirrors or builds on.** Builds `caInterpMatrix`/`caInterpRHS` (the
plain 4×4 Vandermonde system through `Ra1,Ra2,P1,P2`, with `P1,P2`'s RHS
entries negated for the `ι`-substitution), `caInterpMatrix_det_ne_zero`,
`caCoeff`, `bCA` (the degree-≤3 interpolant), its four eval facts
(`bCA_eval_Ra1`/`_Ra2`/`_P1`/`_P2`), the residual factorization
`H.f - bCA² = denomPolyCA * uCANew` (`denomPolyCA_monic`/`_natDegree`,
`dvd_pairNormBCA_full`, `pairNormBCA_eq_denomPolyCA_mul_uCANew`) —
**`uCANew` (a quadratic) definitionally IS the reduction target `T`**,
not a separately-proved coincidence — and `bCA_ordInfOfPair` (pole order
`-6` at infinity, needing `caCoeff ... 3 ≠ 0`). **Own docstring records a
genuine, later-corrected sign bug worth knowing about before trusting
`AlphaLocusDegreeUniform.lean`'s own `S`/`v` construction**: the
class-level identity is `C - A + T - 2•[δ₀]` (bare `T`), not
`C - A - T + 2•[δ₀]` as an earlier draft claimed, and the target-Mumford-
pair identification is `S := ι(T)`, **not** `S := T` — checked
exhaustively via a ChatGPT consultation (`CHATGPT-LOG-principal-witness-
assembly.md`) that there is no alternative witness sharing `f`'s four
named zeros but with residual `ι(T)` instead of `T` (the 4-point
Vandermonde interpolation is already unique, so `T` bare is the only
residual `f`'s construction can produce — only the point-pair
identification needs the `ι`, not `uCANew` itself). This correction
changes nothing already proved in this file (or in files 41/44 below) —
it only affects how `AlphaLocusDegreeUniform.lean`'s `S`/`v` should be
built from `uCANew`/`bCA`. **Status: sorry-free.**

### 35. `CAWitnessTangent.lean` (438 lines)
Imports: `HyperellipticFunctionField`, `AffinePoints`, `DivisorClassGroup`,
`PrincipalDivisors`, `PrincipalDivisorSubgroup`, `LCanonicalElementary`,
`TangentMumfordWitness`.

The **anchor-tangent** (`Ra1=Ra2`) sibling — file 34's plain Vandermonde
is genuinely singular when `Ra1.X=Ra2.X` (closed-form determinant has
`(Ra2X-Ra1X)` as a literal factor), so this file replaces it with a
CONFLUENT interpolation: one node `RaX` carrying both a value row and a
derivative row, plus two ordinary rows at `P1.X`,`P2.X`. Mirrors
`TangentMumfordWitness.lean` exactly (same confluent-Vandermonde shape),
with one genuine simplification over that file: `Ra` here is a
Mumford-pair root (`Ra.Y = va.eval Ra.X` for an explicit `va`), so the
tangency row's target derivative is directly `(derivative va).eval Ra.X`
— a concrete already-available polynomial derivative — rather than
needing `TangentMumfordWitness.lean`'s `branchDeriv` implicit-function-
theorem quotient. Builds `caTangentInterpMatrix`/`caTangentInterpRHS`/
`caTangentInterpMatrix_det_ne_zero`, `caTangentCoeff`, `bCATangent` and
its four facts (`_eval_Ra`, `_deriv_eval_Ra`, `_eval_P1`, `_eval_P2`),
the residual factorization (`dvd_sq_pairNormBCATangent_Ra`,
`dvd_pairNormBCATangent_full`, `denomPolyCATangent`,
`uCANewTangent`, `pairNormBCATangent_eq_denomPolyCATangent_mul_
uCANewTangent`), and `bCATangent_ordInfOfPair`. **Own docstring's status
note ("drafted this pass, not yet REPL-confirmed") is the most recent
claim found in the file itself** — not contradicted anywhere else in the
file, though the working agreement's whole-project build-green claim
should be treated as the more current signal if the two conflict; not
resolved this pass (no Lean edits made). **Status: sorry-free.**

### 36. `CAWitnessTangentTarget.lean` (413 lines)
Imports: `HyperellipticFunctionField`, `AffinePoints`, `DivisorClassGroup`,
`PrincipalDivisors`, `PrincipalDivisorSubgroup`, `LCanonicalElementary`,
`TangentMumfordWitness`.

The **target-tangent** (`sa.P1=sa.P2`) mirror of file 35 — same
confluent-interpolation fix, this time for the case `P1.X=P2.X` (the
`(P2X-P1X)` determinant factor vanishing). The doubled node here lives
on the `ι`-FLIPPED side of `caInterpRHS` (unlike file 35's doubled node,
which sits on the unflipped `C`-side) — so **both** the value and
derivative rows at the doubled node carry a minus sign
(`![Ra1Y,Ra2Y,-PY,-vDerivAtP]`), the one genuine asymmetry between this
file and file 35 despite an otherwise identical matrix shape (confluent
rows just moved from positions 0–1 to positions 2–3). Same tangency-row
derivation as file 35, symmetric: `vDerivAtP := (derivative v).eval P.X`
supplied as a caller hypothesis (`hPDeriv`), not re-derived internally.
Builds `caTangentTargetInterpMatrix`/`caTangentTargetInterpRHS`/
`_det_ne_zero`, `caTangentTargetCoeff`, `bCATangentTarget` and its facts
(`_eval_Ra1`/`_Ra2`/`_P`/`_deriv_eval_P`), the residual factorization
(`dvd_sq_pairNormBCATangentTarget_P`, `dvd_pairNormBCATangentTarget_full`,
`denomPolyCATangentTarget`, `uCANewTangentTarget`,
`pairNormBCATangentTarget_eq_..._mul_uCANewTangentTarget`), and
`bCATangentTarget_ordInfOfPair`. **Same "drafted, not yet REPL-confirmed"
status note as file 35**, same caveat about the working agreement's
build-green claim being more current. **Status: sorry-free.**

### 37. `CAWitnessDivisor.lean` (296 lines)
Imports: `CAWitness`, `PrincipalWitness`.

**Lifts file 34's bare-polynomial facts to actual `H.Point`/`Divisor
H`/`ordAt` content** — the single-witness analogue of
`PrincipalWitnessStep1.lean`'s `divToPair_eq_A_add_C_add_T_of_split`, but
for `f := toPair H (-bCA) 1`. Own docstring lays out the full recipe
(`ordAt_eq_one_of_old_point` from `PrincipalWitness.lean`, applied at
each of the four named points with `A := denomPolyCA`, `U := -uCANew`)
in enough detail to work from directly. Builds one theorem:
`divToPair_eq_C_add_iotaA_of_split` — `f`'s divisor restricted to the
four named points is `[Ra1]+[Ra2]+[ιP1]+[ιP2]`. **Scoped to the
fully-split case only** (matching `caInterpMatrix_det_ne_zero`'s own
hypothesis list); repeated-root branches are files 38/39's job, not
this file's. **Status: sorry-free.**

### 38. `CAWitnessDivisorTangent.lean` (192 lines)
Imports: `CAWitnessTangent`, `PrincipalWitness`, `LPairFinrankOneOrdAtFrac`.

Tangent-case sibling of file 37 — same recipe, but only THREE named
points (`Ra, PtιP1, PtιP2`), `Ra` carrying multiplicity `2`. **Builds a
genuinely new three-factor `ordAt`-composition lemma not present in
`PrincipalWitness.lean` itself**: `denomPolyCATangent = (X-C RaX)² *
(X-C P1X) * (X-C P2X)` needs `ordAt Q ... = 2` at the doubled node, which
`PrincipalWitness.lean`'s own `ordAt_A_eq_one_of_eval_ne_zero` (built for
the four-factor, all-order-1 shape) doesn't handle directly — built here
as three local theorems (`ordAt_denomCATangent_eq_two_at_Ra`/`_eq_one_
at_P1`/`_eq_one_at_P2`) composing `ordAt_linX_pow_unramified`
(`LPairFinrankOneOrdAtFrac.lean`, already proved for general `m`) with
`ordAt_add_of_pairNorm_eq_mul` twice, kept LOCAL to this file (same
placement choice `SanchorMumfordOrdAt.lean` made for its own analogous
lemma, not added to `PrincipalWitness.lean` itself). **Ends here — no
assembled `divToPair_eq_...` theorem in this file** (unlike file 37);
that assembly step is file 40's job, once these three `ordAt` facts are
available as inputs. **Status: sorry-free.**

### 39. `CAWitnessDivisorTangentTarget.lean` (185 lines)
Imports: `CAWitnessTangentTarget`, `PrincipalWitness`,
`LPairFinrankOneOrdAtFrac`.

Target-axis mirror of file 38 — three local `ordAt` lemmas
(`ordAt_denomCATangentTarget_eq_one_at_Ra1`/`_eq_one_at_Ra2`/`_eq_two_
at_P`, note the doubled multiplicity is at `P` here, not at the anchor
node, mirroring file 36's own axis flip relative to file 35). Also ends
without an assembled `divToPair_eq_...` theorem — file 41 does that
assembly. **Status: sorry-free.**

### 40. `CAWitnessAssemblyTangent.lean` (192 lines)
Imports: `CAWitnessTangent`, `CAWitnessDivisorTangent`.

**The assembly file 38 sets up for** — the tangent-case sibling of file
37's `divToPair_eq_C_add_iotaA_of_split`, now that file 38's three
`ordAt_denomCATangent_eq_...` facts are available to supply the needed
`hA_ord` inputs. Builds `divToPair_eq_C_add_iotaA_of_split_tangent`:
`f`'s divisor restricted to the three named points, tangent case, is
`2•[Ra]+[ιP1]+[ιP2]` — matching the roadmap's stated conclusion shape
(one fewer case-split branch than the split file's six-point `by_cases`
chain needs, since `PtRa1`/`PtRa2` collapse into one branch here).
**Status: sorry-free.**

### 41. `CAWitnessAssemblyTangentTarget.lean` (270 lines)
Imports: `CAWitnessTangentTarget`, `CAWitnessDivisorTangentTarget`.

Target-axis mirror of file 40, using file 39's `ordAt` facts. Builds a
private shared-setup lemma (`bCATangentTarget_setup`) plus three
pointwise `ordAt` theorems (`ordAt_bCATangentTarget_eq_one_at_Ra1`/
`_eq_one_at_Ra2`/`_eq_two_at_ιP`) and the assembled
`divToPair_eq_C_add_iotaA_of_split_tangent_target`: `f`'s divisor
restricted to the three named points is `[Ra1]+[Ra2]+2•[ιP]`, `ιP`
(the doubled target point's involution image) carrying the multiplicity
this time, mirroring file 40's structure with the doubled coefficient on
the opposite side. **Status: sorry-free.**

### 42. `CAWitnessResidual.lean` (171 lines)
Imports: `CAWitness`, `PrincipalWitness`, `LPairFinrankOneOrdAtFrac`.

**Handles the OTHER side of `f`'s divisor** — its zero at a root of the
residual factor `uCANew` (`T`, definitionally, per file 34's own
docstring) — the direct analogue of `PrincipalWitnessAssembly.lean`'s
`ordAtFrac_eq_neg_one_of_uRS4General_root`, genuinely simpler here since
`Y=1` throughout (a unit), so this is a bare `ordAt`, not an `ordAtFrac`
ratio. **Own docstring records a real rejected-first-draft correction,
worth reading before designing a similar file**: an early draft assumed
a caller-supplied `hUfac : ∃ Fco, uCANew = linX P.X * Fco ∧ Fco.eval P.X
≠ 0` — exactly the pre-split hypothesis shape
`OrdAtRootMultiplicityUnified.lean` exists to avoid (silently assumes
`uCANew` has two distinct roots, can't express a perfect-square residual,
pushes factorization burden onto every call site) — rejected on Claire's
correction. **Fix**: `uCANew` is a single atomic quadratic, not a product
of named factors, so `ordAt_eq_rootMultiplicity_unramified`
(`LPairFinrankOneOrdAtFrac.lean`, unconditional for any nonzero
polynomial) applies directly, with no named-root hypothesis — subsuming
both the simple-root case (what the assembly needs) and the
repeated-root case as literal instances of one unconditional statement.
Builds one theorem: `ordAt_eq_rootMultiplicity_of_uCANew_root`. **Status:
sorry-free.**

### 43. `CAWitnessResidualTangent.lean` (153 lines)
Imports: `CAWitnessTangent`, `PrincipalWitness`, `LPairFinrankOneOrdAtFrac`.

Tangent-case sibling of file 42 — same recipe, `bCA→bCATangent` etc.
**Flags a genuine, already-fixed bug in a downstream file, worth knowing
about if touching that file**: `PrincipalWitnessStep4Tangent.lean`'s
`cIotaAmIotaT_mem_principalSubgroup_tangent` had been missing this fact
entirely — its `hsupp_f` claimed `ordAt P f = 0` for every `P` outside
`{PtRa,PtιP1,PtιP2}`, which is **false** at the residual points
`PtT1,PtT2` — this file's theorem
(`ordAt_eq_rootMultiplicity_of_uCANewTangent_root`) is exactly the
missing piece that feeds that file's corrected docstring/signature.
**Status: sorry-free.**

### 44. `CAWitnessResidualTangentTarget.lean` (134 lines)
Imports: `CAWitnessTangentTarget`, `PrincipalWitness`,
`LPairFinrankOneOrdAtFrac`.

Target-axis sibling of file 43 (itself the anchor-axis sibling of file
42) — same support-widening fix applies identically one axis over.
Builds `ordAt_eq_rootMultiplicity_of_uCANewTangentTarget_root`. **Status:
sorry-free.**

### 45. `CAWitnessCrossTangent.lean` (84 lines)
Imports: `HyperellipticFunctionField`, `AffinePoints`, `CAWitness`.

**The small foundational file the whole cross-pair family sits on.**
Per `ROADMAP-cawitness-tangent-interpolation.md` Part B case 3: unlike
the anchor-tangent (`Ra1X=Ra2X`) and target-tangent (`P1X=P2X`) cases,
a CROSS-pair collision (one anchor point and one target point sharing an
`x`-coordinate) is not automatically a genuine tangency, since two
points on `y²=f(x)` sharing an `x` can only be equal or `ι`-conjugate.
Proves the dichotomy (`eq_or_eq_iota_of_X_eq`: `P=Q ∨ P=Point.iota Q`
from a shared `x`-coordinate) and the corollary the top-level theorems
actually need (`eq_iota_of_X_eq_of_ne`: given the caller already knows
`Ra1≠sa.P1`, per this project's standing anchor/target-distinctness
convention, a shared `x` forces the `ι`-conjugate case outright). Pure
point-and-curve algebra, no interpolation machinery, no `sorry`.
**Status: sorry-free.**

### 46. `CAWitnessCrossTangentImpossibility.lean` (123 lines)
Imports: `HyperellipticFunctionField`, `AffinePoints`, `CAWitness`,
`CAWitnessCrossTangent`.

**A small, valuable, genuinely generic file — covers all four cross
variants at once** rather than needing four near-duplicate copies. The
key subtlety its docstring is emphatic about: the "same-sign" branch
(`Ra=P1` literally) is NOT ruled out by deriving it from the
interpolation matrix (that would be circular — each `caCrossN`-family
construction only supplies its row identity `Ra.Y=-P1.Y` once its own
`ι`-identification already holds). Instead this file proves the narrower,
correctly-scoped claim: GIVEN both `Ra.X=P1.X` and the construction's own
row identity `Ra.Y=-P1.Y` (plus `hchar`/`Ra.Y≠0`), the same-sign branch is
inconsistent (`false_of_eq_and_rowZero`, `ne_of_rowZero`), so
`eq_iota_of_X_eq_of_ne` (file 45) concludes `Ra=Point.iota P1` outright
(`eq_iota_of_X_eq_of_rowZero`). **Includes an explicit instantiation
table** for which `Ra`/`P1` pair each of the four cross variants plugs
in (Cross1: `Ra1`/`sa.P1`; Cross2: `Ra1`/`sa.P2`; Cross3: `Ra2`/`sa.P1`;
Cross4: `Ra2`/`sa.P2`) — useful for tracing which theorem each
`AlphaLocusDegreeUniformCrossN.lean` file (already indexed, Part 3 above)
actually needs. **Status: sorry-free.**

### 47–48. `CAWitnessCrossTangent2.lean` (231 lines) + `CAWitnessCrossTangent3.lean` (200 lines) — together, **cross variant 1** (`Ra1 = ι(sa.P1)`)
Imports: file 47 imports `HyperellipticFunctionField`, `AffinePoints`,
`TangentMumfordWitness`, `CAWitnessCrossTangent` (file 45); file 48
imports the same plus file 47 itself.

**The first cross-pair variant discovered, predating the later
one-file-per-variant convention files 49–51 use — split across two files
for that historical reason, not a structural difference.** Confluent
interpolation for `Ra1.X = sa.P1.X`: the doubled node collapses rows 0
and 2 of the original `[Ra1,Ra2,P1,P2]` layout — **non-adjacent**, unlike
the anchor/target-tangent cases' adjacent doublings. Determinant
independently sympy-verified (`-(x-P2X)²(P2X-Ra2X)(x-Ra2X)²`) before
writing any Lean, own docstring notes this explicitly as a step up from
an earlier, unverified guess. File 47 builds
`caCrossInterpMatrix`/`caCrossInterpRHS`/`_det_ne_zero`, `caCrossCoeff`,
`bCACross` and its eval/derivative facts (`_eval_Ra`, `_eval_Ra2`,
`_deriv_eval_Ra`, `_eval_P2`); file 48 continues with the residual
divisibility chain (`dvd_pairNormBCACross_Ra2`/`_P2`,
`dvd_sq_pairNormBCACross_Ra`, `dvd_pairNormBCACross_full`,
`denomPolyCACross`, `uCANewCross`,
`pairNormBCACross_eq_denomPolyCACross_mul_uCANewCross`). **Status (both):
sorry-free.**

### 49–51. `CAWitnessCrossTangentV2.lean` (338 lines), `CAWitnessCrossTangentV3.lean` (354 lines), `CAWitnessCrossTangentV4.lean` (355 lines) — **cross variants 2, 3, 4**
Imports (all three): `HyperellipticFunctionField`, `AffinePoints`,
`TangentMumfordWitness`, `CAWitnessCrossTangent` (file 45).

**Each a single self-contained file** (matrix through residual
factorization together) — per V2's own docstring, deliberately combining
what files 47–48 needed two files for, "since the shape is now
established and three more separate checkpoint files per variant would
be pure duplication." V2 = `Ra1=ι(sa.P2)` (doubles rows 0,3 — the SAME
non-adjacent shape as files 47–48, just shifted; determinant
`-(x-Ra2X)²(Ra2X-P1X)(x-P1X)²`). V3 = `Ra2=ι(sa.P1)` (doubles rows 1,2 —
**adjacent**, the same row-position shape files 35/36's anchor/target-
tangent cases use, just shifted down one row — genuinely different from
V2's non-adjacent shape, own docstring is explicit about this
distinction). V4 = `Ra2=ι(sa.P2)` (doubles rows 1,3 — non-adjacent again,
same shape as V2/files-47-48 just shifted, NOT V3's adjacent shape). Each
builds the full parallel chain: `caCrossNInterpMatrix`/`InterpRHS`/`_det_
ne_zero`, `caCrossNCoeff`, `bCACrossN` and its per-row eval/derivative
facts, `dvd_..._full`, `denomPolyCACrossN`, `uCANewCrossN`,
`pairNormBCACrossN_eq_denomPolyCACrossN_mul_uCANewCrossN`. **Status (all
three): sorry-free.**

### 52–55. `CAWitnessCrossTangent1Assembly.lean` (715 lines), `CAWitnessCrossTangent2Assembly.lean` (711 lines), `CAWitnessCrossTangent3Assembly.lean` (721 lines), `CAWitnessCrossTangent4Assembly.lean` (718 lines) — the four cross-variant divisor/`principalSubgroup` assemblies
Imports (all four): the corresponding `CAWitnessCrossTangent*` matrix
file (file 48 for Cross1, files 49/50/51 for Cross2/3/4), `PrincipalWitness`,
`PrincipalWitnessStep3`, `PrincipalWitnessStep4`,
`LPairFinrankOneOrdAtFrac`, `PrincipalDivisorSubgroup`.

**Each file runs the complete pole-order → `ordAt` → divisor-identity →
residual → `principalSubgroup`-membership pipeline for one cross variant,
entirely self-contained** (the pattern files 37+38+40, or 39+41, needed
three separate files to build for the anchor/target-tangent axes, each
Assembly file collapses into one). Per each file's own docstring, this
closes what `ROADMAP-cawitness-tangent-interpolation.md`'s Part B case 3
"still open" wiring item asked for. Each builds, in order:
`bCACrossN_ordInfOfPair` (pole order `-6`), three local
`ordAt_denomCACrossN_eq_..._at_...` facts (mirroring files 38/39's
technique, one order-2 at the doubled node plus two order-1's, adapted to
each variant's own row layout), the assembled
`divToPair_eq_C_add_iotaA_of_split_crossN` (the three-named-point divisor
identity), `ordAt_eq_rootMultiplicity_of_uCANewCrossN_root` (file 42's
residual technique, ported), the five-point
`divToPair_eq_C_add_iotaA_add_T_of_split_crossN`, and finally
**`cIotaAmIotaT_mem_principalSubgroup_crossN`** — the raw
`principalSubgroup`-membership fact each variant needs, feeding file 56
below. Sign/row-layout details are genuinely variant-specific (Cross1's
doubled node absorbed a FLIPPED slot so its derivative hypothesis is
already negated, unlike Cross2/3/4 — file 52's own docstring flags this
explicitly as checked directly against `bCACross_deriv_eval_Ra`'s actual
conclusion, not assumed to match the other three verbatim) but the
overall pipeline shape is identical across all four. **Status (all
four): sorry-free.**

### 56. `CAWitnessCrossTangentMemOfLe.lean` (951 lines)
Imports: all four Assembly files (52–55), `PrincipalWitnessStep4`,
`PrincipalWitnessFinalAssembly`.

**The capstone of the whole cross-pair family — supplies exactly the
theorems `AlphaLocusDegreeUniformCross{1,2,3,4}.lean` (Part 3, files
18–21 above) import this file for.** Per its own docstring: two further
steps beyond what files 52–55 already supply. (1) The `hD`-pushforward/
`single`-sum rewrite (mirroring `PrincipalWitnessFinalAssembly.lean`'s
`cIotaAmIotaT_mem_of_le` line for line, once per variant) —
`cIotaAmIotaT_mem_of_le_cross{1,2,3,4}`. (2) The further `G₁-G₂-G₃`
composition using `fiber_diff_mem_of_le` (`PrincipalWitnessFinalAssembly.
lean`) against the doubled node and the surviving un-doubled target point
per variant — `cAmιTmδmιδ_mem_of_le_cross{1,2,3,4}`, **exactly the
theorem names files 18–21 cite as their `hDP`/`hDP`-analogue source** (a
three-point, not four-point, surviving-support version of
`PrincipalWitnessFinalAssembly.lean`'s own `cAmιTmδmιδ_mem_of_le`). **Not
attempted here, per own docstring**: the eventual top-level
`reducedClass_eq_of_isReduction'`-style theorem actually consuming these
four `(†)`-shaped facts — that consumption is exactly what files 18–21
do, in their respective files, not this one. **Status: sorry-free.**

---

## Part 5: `PrincipalWitness*` family (12 files) — the `reducedClass_eq_of_isReduction'` proof stack

Read in dependency order. This is the largest and most historically
tangled family in `ZeroD/`: it carries the actual proof of
`reducedClass_eq_of_isReduction'` (the theorem `AlphaLocusDegreeUniform.
lean`/`AlphaLocusDegreeUniformCross{1,2,3,4}.lean` all ultimately need),
including several genuine false-lemma-found-and-corrected episodes worth
reading in full rather than trusting a one-line summary of. The theorem
itself now lives in `ReducedClassBundles.lean` (Part 6 below) — these 12
files build everything it's assembled from.

### 57. `PrincipalWitness.lean` (1061 lines)
Imports: `Mathlib`, `PrincipalDivisorSubgroup`, `Reduce/AlphaReduce`,
`Reduce/GeneralSharedRoot`, `TheDataDerivation/DataDerivationBasics`,
`RiemannRochGenus2`, `LCanonicalElementary`, `LPairFinrankOneOrdAtFrac`,
`HyperellipticClassProof` (three of these — `RiemannRochGenus2`,
`LCanonicalElementary`, `LPairFinrankOneOrdAtFrac` — are imported
directly rather than transitively, with the file's own opening comment
working through a cycle-safety check for each one by hand).

Starts the actual proof of `reducedClass_eq_of_isReduction'`'s
divisor-class content, following `CHATGPT-REPLY-step3-reduce-correctness.
md`/`ROADMAP-reduce-divisor-correctness.md`'s three-lemma skeleton (§3a-
§3e): residual-intersection (already done elsewhere), residual-Mumford
(already confirmed elsewhere), and principal-witness (`div(h) = D_old -
D_new`, `h = g/u_new`, `g = E + Y·y` — this file), built as many small
named lemmas rather than attempted whole. Deliberately kept ignorant of
`SampleTargetFromAlpha`/`aClass`/`hr`/`sa.reducedClass` (per the ChatGPT
reply's own §16 recommendation) so it works for both the general
(`P1 ≠ P2`) and tangent (`P1 = P2`) branches without duplication.

**17 numbered lemmas** (the file's own docstring numbers them explicitly,
worth reading in full for the exact composition order), covering: the
norm identity `g·ḡ = N` at the `toPair`/`CoordinateRing` level (lemma 1);
residue-nonzero ⇒ valuation-zero (lemma 2, `ordAt_eq_zero_of_eval_ne_
zero`); the `(A,B)`-pair form of the norm identity (lemmas 3-4); `ordAt P
g` as a root multiplicity of `N`, unramified and ramified (lemmas 5-6);
the `N = A·U` factorization at the pair level (lemma 7,
`toPair_mul_right_zero'`); `ordAtFrac P E Y U 0 = ordAt P A 0` at a
residual point (lemma 8); `coeffAt_divToPair`, the pointwise coefficient
identity for `divToPair` (lemma 9); the Weierstrass/ramification-point
witness `div(x-x0) = 2•[P]` (lemma 10, restating an already-proved fact
from `HyperellipticClassProof.lean`); `Divisor H` extensionality via
`coeffAt` (`eq_of_coeffAt_eq`) plus the pointwise-coefficient assembly
`coeffAt_sub_eq_of_forall`/`divToPair_eq_of_coeffAt_diff_eq_zero` (lemma
11); `pairNorm H E (-Y) = pairNorm H E Y` (lemma 12); the residual-point
mirror of lemma 8 (lemma 13); the unconditional `g`/`ḡ` sum identity at a
residual point (lemma 13b) and its concrete `= -1` composition for the
standard disjoint-simple-root case (lemma 13c) — together resolving a
genuine three-way sign ambiguity (`+1`/`-1`/`-2`) that neither lemma 8
nor 13 alone could settle; then **three "layers"** (per a ChatGPT
follow-up's own naming) for computing `ordAt P A 0` at the named points
WITHOUT going through `Polynomial.roots`: Layer 1 (`ordAt_linX_eq_one_
of_ne_zero`/`_zero_of_ne'`), Layer 2 (`ordAt_mul_eq_one_of_ordAt_eq_
one_zero`/its 4-factor iteration), and Layer 3 (`ordAt_A_eq_one_of_eval_
ne_zero`, the Cantor-specific instantiation avoiding `rootMultiplicity`
exposure at the call site); finally lemmas 16-17 (`ordAt_eq_one_of_old_
point`, `ordAtFrac_eq_two_of_old_point`, `ordAt_eq_two_of_old_point`),
closing a genuine gap found while starting `ROADMAP-principal-witness-
assembly.md`'s "corrected chain" step 1 — lemmas 14/15 (mentioned in the
docstring, defined via the layers above) give `ordAtFrac`, not the bare
`ordAt` that `div_aff(g)`'s own `divToPair`-value needs, and recovering
one from the other needs `ordAt P U 0` independently, which lemma 16
supplies as an explicit caller-supplied hypothesis. **Not attempted
here** (by the file's own design): the actual assembly theorem wiring
these into `SampleTargetFromAlpha`'s concrete situation — that's
`PrincipalWitnessAssembly.lean`, next. **Status: sorry-free.**

### 58. `PrincipalWitnessStep1.lean` (563 lines)
Imports: `PrincipalWitness`, `AlphaLocusDegreeUniform`,
`PrincipalWitnessAssembly`.

`ROADMAP-principal-witness-assembly.md` step 1: `div_aff(g) = A+C+T`, the
literal `Divisor Hc`-level equality (not just "value 1 at six points, 0
elsewhere") over the six named points `P1,P2` (`A`), `Ra1,Ra2` (`C`),
`R1,R2` (`T`). Lives in its own file (rather than either
`AlphaLocusDegreeUniform.lean` or `PrincipalWitnessAssembly.lean`)
specifically to avoid an import cycle: `PrincipalWitnessAssembly.lean`
already imports `AlphaLocusDegreeUniform.lean`, so a theorem needing both
can't live in either. **Three variants**, scoped by which of `ua`/
`u_target` are split vs. have a repeated root:
`divToPair_eq_A_add_C_add_T_of_split` (both split, six-point support),
`divToPair_eq_A_add_C_add_T_of_split_Ra1_eq_Ra2` (anchor pair collapses
to one doubled point `Ra`, five-point support with `(2:ℤ)•single PtRa`),
and `divToPair_eq_A_add_C_add_T_of_split_Ra1_eq_Ra2_and_R1_eq_R2` (the
doubly-repeated case, both `ua`/`u_target` collapsed). The doubly-
repeated-target-alone case (`R1=R2`, `ua` still split) is explicitly
**not** covered — only the anchor-side single-repeat and the
simultaneous-both-repeat cases are, per the roadmap's own scoping note.
Also re-exports `PrincipalWitnessAssembly.lean`'s residual-side
`ordAt_eq_one_of_uRS4General_root` as `ordAt_u_new_eq_one_of_root` (an
`abbrev`, no new content) so callers of this file's composition can find
both halves without a second import. **Status: sorry-free.**

### 59. `PrincipalWitnessStep2.lean` (342 lines)
Imports: `PrincipalWitness`, `AlphaLocusDegreeUniform`,
`PrincipalWitnessAssembly`, `PrincipalWitnessStep1`.

Step 2: `div_aff(u_new) = ρ+I` (the residual-side companion,
`divToPair_eq_rho_add_I_of_split`, splitting `uRS4General`'s two
unnamed roots `ρ1,ρ2` into named points the same way step 1 split
`ua`/`u_target` — via `uRS4General_monic`/`_natDegree_eq_two` feeding
`quadratic_eq_mul_X_sub_C`), then the subtraction assembly
`divToPair_sub_eq_A_add_C_add_T_sub_rho_sub_I_of_split` combining step 1
+ this file's own theorem via plain `Divisor Hc`-level subtraction —
**no `δ₀` term anywhere**, since `Divisor Hc` is affine-only by
construction. Scoped, matching step 1, to the fully-split case only
(`uRS4General` itself assumed to have two distinct roots `ρ1 ≠ ρ2` — its
own repeated-root variant is not attempted, unlike `ua`/`u_target`'s,
since nothing in the roadmap flags it as needed). **Status: sorry-free.**

### 60. `PrincipalWitnessStep3.lean` (451 lines)
Imports: `CAWitness`, `CAWitnessDivisor`, `CAWitnessResidual`,
`PrincipalWitness`.

`ROADMAP-principal-witness-assembly.md` step 2: the complete divisor
`div_aff(f) = C + ι(A) + T` for `f := y - bCA(x)`, over the full
six-point support `{Ra1, Ra2, ιP1, ιP2, PtT1, PtT2}`. Supplies the
missing splitting step `CAWitnessResidual.lean` deliberately left out
(naming `uCANew`'s two residual roots `T1X, T2X`), via
`rootMultiplicity_uCANew_eq_one` — **NOT** via
`quadratic_eq_mul_X_sub_C` + establishing `uCANew.natDegree = 2` from
scratch (the file's own docstring flags this as the extra bookkeeping
the `rootMultiplicity`-first design in `CAWitnessResidual.lean` exists
to avoid); instead, given `uCANew.IsRoot T1X`/`T2X` and `T1X ≠ T2X`,
coprimality gives `(X-CT1X)(X-CT2X) ∣ uCANew`, and simplicity of each
root follows directly from the quotient's own nonvanishing at that
root (`hQT1`/`hQT2`, caller-supplied), no degree fact needed anywhere.
`rootMultiplicity_uCANew_eq_one` is stated **generically in its
polynomial argument** (not specific to `uCANew`), which is exactly why
`PrincipalWitnessStep4Tangent.lean`/`PrincipalWitnessStep4TangentTarget.
lean` (files 63-64 below) can reuse it unchanged against
`uCANewTangent`/`uCANewTangentTarget` with no port needed.
`divToPair_eq_C_add_iotaA_add_T_of_split` is the six-way-`by_cases`
assembly theorem. Feeds directly into step 3 of the roadmap
(`reducedClass_eq_of_isReduction'`'s `S`/`hSmem`/`hufree`/`hScard`
target shape) — not attempted here. **Status: sorry-free.**

### 61. `PrincipalWitnessStep4.lean` (768 lines)
Imports: `CAWitness`, `CAWitnessDivisor`, `CAWitnessResidual`,
`PrincipalWitness`, `PrincipalWitnessStep3`, `HyperellipticClassProof`,
`PrincipalDivisorSubgroup`.

`ROADMAP-principal-witness-assembly.md` step 3: turning step 3's
`div_aff(f) = C + ι(A) + T` into `principalSubgroup` membership.
**Contains two sign/scope corrections this pass, both worth reading
directly rather than trusting a paraphrase**: (1) the actual target is
`C - A - ι(T) + 2•[δ₀]`, not the earlier `C - A - T + 2•[δ₀]`; (2) a
"separately-principal fact" `T + ι(T) - 4•[δ₀] ∈ principalSubgroup` that
an earlier plan wanted to use turned out to be **FALSE for a generic
(non-Weierstrass) `δ₀`** — passing to the smooth projective model,
`T+ι(T) ~ 4[∞]` always, so that statement is equivalent to a special
4-torsion condition on `δ₀`, not a general fact. **Do not attempt to
prove that statement or any Lean statement asserting it.**

**Three parts.** Part 1 (`ordAt_linX_mul3_eq_one_of_ne`/`_zero_of_
notMem`, `divToPair_hA_eq`, `ordInfOfPair_hA`): `div(h_A) = A + ι(A) +
[δ₀] + [ι δ₀]` for `h_A := (x-P1.X)(x-P2.X)(x-δ₀.X)`, via 3-factor
analogues of `PrincipalWitness.lean`'s own composition lemmas. Part 2
(`cAmT_mem_principalSubgroup`, **DONE, build-green**): the ratio
generator `div(f)-div(h_A)`, giving `C - A + T - [δ₀] - [ιδ₀] ∈
principalSubgroup`. Part 3: the honest fact actually provable from this
stack's generators is `C - A - ι(T) + [δ₀] + [ιδ₀] ∈ principalSubgroup`
(marked `(†)` in the file), **not** the originally-planned `2•[δ₀]`
version — the discrepancy `[δ₀]-[ιδ₀]` is itself a genuine extra
(false-for-generic-`δ₀`) condition. `divToPair_hT_eq`/`ordInfOfPair_hT`
build `h_T := (x-T1X)(x-T2X)(x-δ₀.X)`'s divisor fact (mirroring Part 1's
`h_A` construction), and **`cIotaAmIotaT_mem_principalSubgroup`** proves
exactly `G₁ := div(f) - div(h_T) ∈ principalSubgroup` — the first of the
three generators (`G₁-G₂-G₃`) the file's docstring says compose (by hand
and via ChatGPT, confirmed term-by-term) to `(†)`; `G₂`/`G₃` themselves
are NOT built in this file (see `PrincipalWitnessFinalAssembly.lean`,
file 65, which supplies them and does the composition). A trailing
"Update" note records that `reducedClass_eq_of_isReduction'` was later
proved (`ReducedClassBundles.lean`, 0 live sorry) with `hδY : δ₀.Y ≠ 0`
in its hypotheses, ruling out the cheapest fix (pinning `δ₀` to a
Weierstrass point) — which of the file's own listed alternatives (b)/(c)
was actually taken is **not traced in this file**; read
`ReducedClassBundles.lean`'s own proof directly rather than trusting
this note's three-option framing as exhaustive. **Status: sorry-free**
(all "sorry" occurrences in the file are prose, describing this
now-resolved history).

### 62. `PrincipalWitnessStep4Tangent.lean` (340 lines)
Imports: `CAWitnessTangent`, `CAWitnessDivisorTangent`,
`CAWitnessAssemblyTangent`, `CAWitnessResidualTangent`,
`PrincipalWitness`, `PrincipalWitnessStep3`, `PrincipalWitnessStep4`,
`PrincipalDivisorSubgroup`.

`ROADMAP-principal-witness-tangent-assembly.md` step 4: the `Ra1 = Ra2
=: Ra` (doubled anchor) sibling of `cIotaAmIotaT_mem_principalSubgroup`.
**Fixes a real bug found this pass, traced in a "Root cause found"
writeup (2026-08-28)**: a first draft copied the split case's `hsupp_f`
onto a three-point support `{PtRa, PtιP1, PtιP2}`, but `f`'s divisor
there genuinely vanishes at `T1X, T2X` too (roots of `uCANewTangent`),
making that `hsupp_f` an unsatisfiable-in-practice hypothesis for any
real instantiation. **Fix**: widen the support to five points,
`{PtRa, PtιP1, PtιP2, PtT1, PtT2}` (degree `2+1+1+1+1=6`, matching
`bCATangent_ordInfOfPair`'s `-6`), following the split case's own
precedent of already including `PtT1,PtT2` in its six-point support for
the identical reason. `divToPair_eq_C_add_iotaA_add_T_of_split_tangent`
is the corrected five-point assembly; `cIotaAmIotaT_mem_principalSubgroup_
tangent` is the tangent mirror of file 61's `cIotaAmIotaT_mem_
principalSubgroup`, same proof shape. **Status: sorry-free.**

### 63. `PrincipalWitnessStep4TangentTarget.lean` (320 lines)
Imports: `CAWitnessTangentTarget`, `CAWitnessDivisorTangentTarget`,
`CAWitnessAssemblyTangentTarget`, `CAWitnessResidualTangentTarget`,
`PrincipalWitness`, `PrincipalWitnessStep3`, `PrincipalWitnessStep4`,
`PrincipalDivisorSubgroup`.

`ROADMAP-split-hypothesis-elimination.md`'s "item 2 (new)" — the
target-axis mirror of file 62, applying the exact same support-widening
fix (three-point `{PtRa1, PtRa2, PtιP}` support from
`CAWitnessAssemblyTangentTarget.lean` widened to five points
`{PtRa1, PtRa2, PtιP, PtT1, PtT2}`, degree `1+1+2+1+1=6`, matching
`bCATangentTarget_ordInfOfPair`'s `-6` — same total as the anchor-tangent
case, doubled node now at position 3 instead of position 1).
`divToPair_eq_C_add_iotaA_add_T_of_split_tangent_target` and
`cIotaAmIotaT_mem_principalSubgroup_tangent_target` are the resulting
pair, same proof shape as file 62 throughout, reusing
`rootMultiplicity_uCANew_eq_one` (`PrincipalWitnessStep3.lean`) unchanged.
**Status: sorry-free.**

### 64. `PrincipalWitnessAssembly.lean` (3695 lines — the largest file in `ZeroD/`)
Imports: `PrincipalWitness`, `AlphaLocusDegreeUniform`,
`OrdAtRootMultiplicityUnified` (a comment notes this last import
direction is now acyclic, since `OrdAtRootMultiplicityUnified.lean` no
longer imports this file back).

Assembles `reducedClass_eq_of_isReduction'` from `PrincipalWitness.
lean`'s lemma stack, per `ROADMAP-principal-witness-assembly.md`'s
"Recommended order for the next pass." Scoped, per that roadmap, to the
SPLIT case only (both `ua`/`uRS4General` have two rational roots) — the
irreducible case is a documented non-goal. **Section structure** (18
named `section`/`end` blocks): `ExactFactorization` (the actual equation
`Npoly4 = npoly4Lcm4 * uRS4General`, not just the divisibility fact
already on file elsewhere); `GeometricBridge` plus four
`GeometricInstantiationQuadratic{,2,3,4}` sections (connecting "`P` is a
root of one of `npoly4Lcm4`'s four sub-factors" to `Finset H.Point`
membership); six `PointComposition{P1,P2,Ra1,Ra2,R1,R2}` sections (the
per-named-point `ordAtFrac` assemblies — by far the bulk of the file's
line count, ~2000 lines across the six); `PointCompositionInterface`
(a reusable assembly interface, `Step 4a`); `PointwiseOrdAtFracAssembly`
(all six pointwise `ordAtFrac` facts gathered); and
`MumfordPairResidualCase` (the residual-pair strategy, per Claire's own
instruction, avoiding ever naming `ι(R1)`/`ι(R2)` as explicit points).

**Three `def`-not-`abbrev` wrappers up top** (`witnessE4`, `witnessY4`,
`witnessA4`) exist purely to dodge a heartbeats problem: re-elaborating
the same large polynomial expressions repeatedly was enough to hit the
default 200k-heartbeat limit at declaration time, before any proof body
was even entered.

**Resolved this pass: the `R_i` vs `ι(R_i)` orientation question**
(flagged in an earlier roadmap pass) — traced directly against
`vRS4General`'s own definition (`v ≡ -E/Y mod U`) and lemma 15's own
docstring, concluding `D_new`'s two points are `ι(R1), ι(R2)` — the
HYPERELLIPTIC CONJUGATES of `g`'s own Mumford-selected zeros — not
`R1, R2` directly. This is flagged as a real fact the call-site assembly
must get right, not a cosmetic renaming.

**The Mumford-pair residual case's one genuine gap, and how it closed**:
`hU_ord : ordAt P U 0 = 1` (for `P.X` a root of `uRS4General`, no named
second root) needed `P.X` to be a SIMPLE root — different from merely
being a root. ChatGPT consultation confirmed this does NOT follow
automatically from `hgcd`/`hInv`/`MatrixNondegenerate4` (explicit
counterexample supplied: `U=(X-r)²`, `Y=1` satisfies both while `U` is
maximally non-squarefree). **Fix**: added `hsf : Squarefree H.f` (already
implicit elsewhere in the project) and a new hypothesis `hUfac`
supplying the minimal local fact (an explicit factorization witness for
simplicity at `P.X` specifically) — not the stronger global `Squarefree
uRS4General`, and still no named second root anywhere in the signature.

A long trailing "Status note" block (~300 lines, around line 3385)
records the full history of what was and wasn't closed pass-by-pass —
worth reading directly for anyone touching this file, since it also
records that the `Sg`/`Su`/`divToPairRatio`/`principalSubgroup` route
originally planned for the final step was **superseded, not just
unstarted**: `ordInfOfPair(Epoly4,Ypoly4) = -8` and
`ordInfOfPair(uRS4General,0) = -4` don't match, so `principalSubgroup`
membership (which demands an exact pole-order match) was confirmed the
wrong tool; the correct route (`eq_of_coeffAt_eq`-based `D_old - D_new`,
carrying **no `δ₀` term** since `Divisor H` is affine-only) is what
`ReducedClassBundles.lean` actually implements. **Status: sorry-free**
(all "sorry" mentions in the file, including one describing
`reducedClass_eq_of_isReduction'` itself as "stays `sorry`" at the time
that note was written, are historical prose about a gap since closed
elsewhere — confirmed no live tactic-mode `sorry` remains).

### 65. `PrincipalWitnessCAConnection.lean` (239 lines)
Imports: `SanchorMumfordOrdAt`, `PrincipalWitnessFinalAssembly`.

Connects `(ua,va)`/`(u,v)` (the standalone named Mumford pairs) to
`CAWitness.lean`'s `uCANew`/`bCA` (the interpolation construction).
**A ChatGPT consultation this pass explicitly recommends NOT proving
`uCANew = uRS4General`** — the two constructions solve genuinely
different interpolation problems (plain 4-point Vandermonde vs. a
7-dimensional Riemann–Roch/Cramer basis) and forcing that equality risks
proving something false; `uRS4General`/`curBeforeMonic4General`/`Npoly4`
are abandoned for this theorem's purposes. **Instead**: the
identification is taken as a new caller-supplied hypothesis (`ua`/`va`,
resp. `u`/`v`, ARE `uCANew`/`-bCA`, built from `Ra1,Ra2,sa.P1,sa.P2`) —
the same category of premise `hMumfordUa`/`hMumfordTarget`/
`hAnchorRoots` already are throughout this project ("caller supplies the
real Mumford data," not a proof obligation), specialized to this
project's fixed `Y := 1` convention. Uses `SanchorMumfordOrdAt.lean`'s
machinery (built purely from `IsMumfordUa`/`IsMumfordTarget4`, no
dependence on `uCANew`/`bCA`) to collapse `divToPair (-va) 1 Sanchor` and
its target mirror down to explicit `single`-sum forms —
`divToPair_negVa_one_Sanchor_eq`, `divToPair_negV_one_S_eq`, and their
`_tangent` mirrors — exactly the shape `cAmιTmδmιδ_mem_of_le`
(`PrincipalWitnessFinalAssembly.lean`) needs directly. **Status:
sorry-free.**

### 66. `PrincipalWitnessFinalAssembly.lean` (331 lines)
Imports: `PrincipalWitnessStep3`, `PrincipalWitnessStep4`.

`ROADMAP-principal-witness-assembly.md`, closing step 0 (part c): the
full `principalSubgroup` assembly, generic in `D : PrincipalDivisorData
H` rather than the concrete `principalDivisorData H hdeg`, so it can
feed `reducedClass_eq_of_isReduction'` directly via that theorem's own
`hD : principalSubgroup H hdeg ≤ D.P`. **Builds `G₂`/`G₃` and the
composition file 61 (`PrincipalWitnessStep4.lean`) left in prose only.**
`fiber_diff_mem_of_le` is the generic-`D` version of
`HyperellipticClassProof.lean`'s `hyperellipticClass_principalDivisorData`
(same proof, `D` abstracted); `cIotaAmIotaT_mem_of_le` pushes file 61's
`cIotaAmIotaT_mem_principalSubgroup` forward along `hD` and rewrites into
an explicit `single`-sum statement (`G₁`, spelled out); `cAmιTmδmιδ_mem_
of_le` is `G₁ - G₂ - G₃`, composed by hand (`abel` after unfolding all
three to explicit sums), giving exactly the honest fact `(†)` (file 61's
naming) as a membership in `D.P`, generic `D`. **Not wired in here**:
`sa.reducedClass`'s own `N₂`-to-`Nι` normalization bridge via `q` — done
inside `reducedClass_eq_of_isReduction'`'s own proof body
(`ReducedClassBundles.lean`), not here. **Status: sorry-free.**

### 67. `PrincipalWitnessFinalAssemblyTangent.lean` (283 lines)
Imports: `PrincipalWitnessStep4Tangent`, `CAWitnessAssemblyTangent`,
`PrincipalWitnessFinalAssembly`.

Tangent siblings of file 66's two theorems. Per the roadmap's own
"innocent pass-through" observation, both are thin compositions with no
new math: `cIotaAmIotaT_mem_of_le_tangent` pushes file 62's
`cIotaAmIotaT_mem_principalSubgroup_tangent` forward and rewrites via the
FIVE-point corrected support; `cAmιTmδmιδ_mem_of_le_tangent` is `G₁-G₂-G₃`
exactly as the split version, with `G₂`/`G₃` (`fiber_diff_mem_of_le`)
reused verbatim from file 66 since that theorem is already fully generic.
A "Post Step-4 support-fix update" note confirms an earlier draft's
worry (that `PtT1,PtT2` would survive uncancelled) no longer applies once
the five-point support fix (file 62) is in place — they DO cancel, same
as the split case. **Status: sorry-free.**

### 68. `PrincipalWitnessFinalAssemblyTangentTarget.lean` (287 lines)
Imports: `PrincipalWitnessStep4TangentTarget`,
`CAWitnessAssemblyTangentTarget`, `PrincipalWitnessFinalAssembly`.

Target-axis mirror of file 67. **The one genuine asymmetry, per the
file's own docstring**: in the anchor-tangent case (file 67), the
doubled node (`Ra`) sits on the UNFLIPPED side, so its `G₁` carries a
plain `2•single PtRa` and `G₂,G₃` are two DIFFERENT ordinary target
points subtracted once each. Here, the doubled node (`P`) sits on the
FLIPPED side, so `cIotaAmIotaT_mem_of_le_tangent_target`'s conclusion
instead carries `single PtRa1 + single PtRa2` (anchor pair un-collapsed)
and a coefficient-`2` term `2•single PtιP` — canceling that needs a
coefficient-2 fiber difference, not two distinct ones, so
`cAmιTmδmιδ_mem_of_le_tangent_target`'s `G₂` is a single `fiber_diff_
mem_of_le PtP δ₀` subtracted TWICE (via `D.P.zsmul_mem` at `(2:ℤ)`,
generic on any `AddSubgroupClass`). **Status: sorry-free.**

## Part 6: `ReducedClassBundles*`/`ReducedClassDispatch` (6 files) — bundling and dispatching the seven `reducedClass_eq_of_isReduction'` variants

`ROADMAP-reducedClass-dispatcher.md`'s staged plan: step 2 bundles the
shared/differing hypothesis groups into named structures per variant,
step 3 relocates each variant's actual theorem behind its bundle (fixing
import cycles the flat versions couldn't avoid), and this family's final
file (`ReducedClassDispatch.lean`) is the step-1/2 top-level router tying
all seven variants into one callable interface. **This is where
`reducedClass_eq_of_isReduction'` itself — the theorem the entire
`PrincipalWitness*` family (Part 5) and much of Parts 1-4 exist to
support — is actually proved and, in its five fully-split cross variants,
dispatched.**

### 69. `ReducedClassBundles.lean` (558 lines)
Imports: `AlphaLocusDegreeUniform`, `AlphaLocusDegreeUniformTangent`.

Builds the two structures shared across **all seven** variants
(`CoefficientData`, carrying BOTH `coeff_hMumfordUa` and
`coeff_hMumfordTarget` unconditionally — a deliberate superset of either
existing `Tangent`/`TangentTarget`-specific bundle, confirmed by a
field-by-field diff of those two pre-existing bundles to differ by
exactly one field each; and `ReductionData`, confirmed IDENTICAL across
both pre-existing instances, so one shared structure genuinely
suffices), plus the base (fully-split, four-free-point) variant's own
construction-specific tier, `SplitAssemblyData` — the large (~160-field)
structure carrying every hypothesis `AlphaLocusDegreeUniform.lean`'s
original flat theorem needed, diffed directly against
`AlphaLocusDegreeUniformCross1.lean`'s own flat signature to confirm
exactly which fields are split-specific vs. shared.

**Contains `reducedClass_eq_of_isReduction'` itself** — the bundled,
base (fully split) form of the capstone theorem, relocated here from
`AlphaLocusDegreeUniform.lean` because that file cannot import
`SplitAssemblyData` back without an import cycle (this file already
imports `AlphaLocusDegreeUniform.lean` for `SampleTargetFromAlpha`).
Carries `set_option maxHeartbeats 8000000` (a 40x increase over the
default). **Status: sorry-free** (0 live sorry, confirmed by direct
grep — this is also the specific claim `PrincipalWitnessStep4.lean` and
`PrincipalWitnessAssembly.lean`'s own trailing notes point to when they
describe a since-resolved historical gap).

### 70. `ReducedClassBundlesCross1.lean` (455 lines)
Imports: `ReducedClassBundles`, `AlphaLocusDegreeUniformCross1`,
`CAWitnessCrossTangentMemOfLe`.

Same shape as file 69's `SplitAssemblyData`, reusing the shared
`CoefficientData`/`ReductionData` from that file, with the
construction-specific tier (`Cross1AssemblyData`) swapped for
`AlphaLocusDegreeUniformCross1.lean`'s own four itemized differences
(read directly from that file's own module docstring, not assumed):
`sa.P1` is forced to `Point.iota Ra` via `hP1eq` (so no free `as_Ra1` —
the anchor pair is named `as_Ra`/`as_Ra2`, "the point that collides is
`Ra`, unprimed"); the three-free-point `caCrossInterpMatrix`/`caCrossCoeff`
/`bCACross`/`uCANewCross`/`denomPolyCACross` machinery (plus a derivative
datum `vDerivAtP1`) replaces the four-free-point split construction;
`h1P1,h1P2,h2P1,h2P2,hPP` collapse to a three-hypothesis family
`h1,h2,h3`; `hP1_curve`/`hP1Y_ne` are gone, replaced by `hP1Deriv` (the
derivative datum's defining equation). Contains
`reducedClass_eq_of_isReduction'_cross1`. **Status: sorry-free.**

### 71. `ReducedClassBundlesCross2.lean` (455 lines)
Imports: `ReducedClassBundles`, `AlphaLocusDegreeUniformCross2`,
`CAWitnessCrossTangentMemOfLe`.

Mirror of file 70 with `sa.P2` (not `sa.P1`) forced to `Point.iota Ra`
via `hP2eq`; three free points are `RaX,Ra2X,P1X` plus derivative datum
`vDerivAtP2`; `hP2_curve`/`hP2Y_ne` are gone, replaced by `hP2Deriv`.
Otherwise textually parallel to file 70 — `ReductionData`/
`CoefficientData` reused unchanged. Contains
`reducedClass_eq_of_isReduction'_cross2`. **Status: sorry-free.**

### 72. `ReducedClassBundlesCross3.lean` (453 lines)
Imports: `ReducedClassBundles`, `AlphaLocusDegreeUniformCross3`,
`CAWitnessCrossTangentMemOfLe`.

The doubled point here is in the SECOND anchor slot (`as_Ra1`/`as_Ra`,
opposite of Cross1's naming), and it is `sa.P2` (not `sa.P1`, despite the
identifying hypothesis being named `hP1eq` — the file's own docstring
flags this naming subtlety explicitly: `hReducedClass`/`isReduction'`
machinery keeps `sa.P1` fully free; it's `sa.P2` that collides with the
anchor) that is forced to `Point.iota Ra`. Free points:
`Ra1X,RaX,P2X` plus derivative datum `vDerivAtP1`. `hP2_curve`/`hP2Y_ne`
(facts about the now-gone free `sa.P2`) are DERIVED from `hRa_curve`/
`hRaY_ne` via `Point.iota_X`/`Point.iota_Y` inside the theorem's own
proof, rather than taken as independent hypotheses — a genuine
asymmetry versus Cross1/Cross2, where the corresponding facts are
independent hypotheses throughout. Contains
`reducedClass_eq_of_isReduction'_cross3`. **Status: sorry-free.**

### 73. `ReducedClassBundlesCross4.lean` (493 lines)
Imports: `ReducedClassBundles`, `AlphaLocusDegreeUniformCross4`,
`CAWitnessCrossTangentMemOfLe`.

Same shape as file 72's `Cross3AssemblyData` (doubled point `as_Ra` in
the second anchor slot), but here it is `sa.P2` (not `sa.P1`, opposite of
Cross3) that is forced to `Point.iota as_Ra` via `hP2eq`; the surviving
free target point is `sa.P1`, so `hP1_curve`/`hP1Y_ne` are ordinary
independent hypotheses (exactly as `sa.P2`'s counterparts were in
Cross1/Cross2), with `hP1Deriv` (via `vDerivAtP2`) supplying the
derivative datum for the doubled anchor point. Free points:
`Ra1X,RaX,P1X`. The file's own docstring flags a further subtlety
(`single sa.P1 + single sa.P2` vs. the reverse ordering) in how the
un-bundled original `..._cross4_flat` in `AlphaLocusDegreeUniformCross4.
lean` states its own `hReducedClass` — worth checking directly if that
ordering ever matters at a call site. Contains
`reducedClass_eq_of_isReduction'_cross4`. **Status: sorry-free.**

### 74. `ReducedClassDispatch.lean` (465 lines)
Imports: `ReducedClassBundles`, `ReducedClassBundlesCross{1,2,3,4}`,
`AlphaLocusDegreeUniformTangentTarget` (which transitively pulls in the
two pre-existing tangent-axis bundle pairs from
`AlphaLocusDegreeUniformTangent.lean`/`AlphaLocusDegreeUniformTangentTarget.
lean`, confirmed by direct read this pass to already exist in bundled
form, needing no further bundling work before this file could be
written).

**The top-level router over all seven `reducedClass_eq_of_isReduction'`
variants** — the capstone `def` of the entire `ZeroD/` dispatch layer.
Two-level dispatch, per the roadmap's own "Proposed shape": an outer,
decidable dispatch on `X`-coordinates only (`Ra1.X = Ra2.X` → tangent-
anchor; `sa.P1.X = sa.P2.X` → tangent-target; else → both-split), and an
inner, NOT-decidable dispatch (`CrossCase`, a five-constructor sum type
— `generic` plus one constructor per `Cross{1,2,3,4}` theorem's own
`hP1eq`/`hP2eq`-shaped hypothesis) taken as caller-supplied data, since
`Ra = ι(P)` needs a row-level `Y`-fact no `X`-coordinate equality alone
determines. **Simultaneous anchor+target tangency is explicitly NOT
covered by any of the seven theorems** — the dispatcher takes an
explicit `hRaT : Ra1.X ≠ Ra2.X ∨ sa.P1.X ≠ sa.P2.X` ruling that
configuration out, rather than papering over it with a `sorry`-guarded
eighth branch (the "not with a `sorry`" phrasing is a design statement
in the docstring, not a live `sorry` anywhere in the file).

**Resolves the roadmap's own flagged `q`/conclusion-shape ambiguity**:
checked directly this pass that all seven bundles' `as_q`/`hq` fields are
**textually identical** (`hq : as_q = toJacobian D ⟨single (Point.iota
δ₀) - single δ₀, ...⟩`, depending only on `δ₀`, shared via `sa` — not a
genuine per-branch unknown), so the dispatcher fixes one `q` up front and
every branch's own `hq` discharges `d.as_q = q` by direct rewrite,
letting the whole dispatcher return one fixed conclusion shape regardless
of which of the seven branches fires.

**Records a real proof-technique bug found via Claire's REPL and its
fix**, worth reading directly if writing similar dispatch code
elsewhere: calling the bundled theorem first and then trying to `rw` the
dispatcher's caller-fixed `v`/`S`/`hmem` into its conclusion afterward
fails with "motive is not type correct" (`d.hmem`'s own type mentions
`d.as_v`/`d.as_S` dependently, so `rw` can't abstract them out without
also transporting the proof term itself). **Fix**: `subst` the branch's
`dV`/`dS` equalities BEFORE calling the theorem, then close the residual
`Subtype.mk`-proof-component mismatch via `convert ... using 2` (proof
irrelevance) — the specific `using 2` depth confirmed against the actual
goal shape, not assumed from a smaller example.

Declares `CrossCase` (the five-constructor inductive) and
`reducedClassDispatch` (a `def`, not a `theorem`, since it pattern-
matches on `cc : CrossCase ...` and returns a term-level proof per
branch) — one signature accepting all seven bundle-pairs (`base`/`d` for
each of tangent-anchor, tangent-target, and generic-cross, plus a
separate `Cross{1,2,3,4}`-specific bundle-pair-and-hypothesis-tuple per
cross case), matching the roadmap's own "Bundling, not flattening"
conclusion (a caller only ever has the ONE matching bundle-pair in hand;
the other six are simply unused whichever branch fires). **Status:
sorry-free** (the file's one "sorry" occurrence is the prose phrase
"rather than papering over it with a `sorry`-guarded fourth branch" —
describing what was deliberately NOT done, not a live tactic).

## Part 7: nine remaining singletons

Nine files with no strong grouping among themselves, covering: two
alternative Cantor-witness constructions built independently of the
`CAWitness*`/`PrincipalWitness*` machinery (files 75, 83); a generic
polynomial-algebra lemma about Cantor reduction (76); a reusable
algebraic-bookkeeping structure (77); a unifying `rootMultiplicity`-based
replacement for four case-split theorems elsewhere (78); a genuinely
separate, non-self-referential alternative to `isReduction'` (79); a
missing-hypothesis diagnosis-and-fix for `Sanchor`/`sa.P1,sa.P2` (80); a
small `ordAt`-at-a-Mumford-point helper (81); and a Hasse-Weil-avoiding
symbolic curve-witness construction (82). **Two of these nine
(`SymmetricCurveWitness.lean`, `TangentMumfordWitness.lean`) carry their
own "not yet build-tested" caveats in their own docstrings** — flagged
individually below, and worth treating with more caution than this
pass's other 25 files, all of which describe themselves as REPL-confirmed.

### 75. `CantorAddWitness.lean` (465 lines)
Imports: `HyperellipticFunctionField`, `AffinePoints`,
`DivisorClassGroup`, `PrincipalDivisors`, `PrincipalDivisorSubgroup`,
`LCanonicalElementary`.

The `f-` witness for `ROADMAP-principal-witness-assembly.md`'s `A + T`
construction — companion to file 83's `f+`. **Rebuilt this pass; its own
previous version is explicitly discarded as wrong**: an earlier draft
built `bMinus` via a CRT/Cantor-addition congruence pair, which a
ChatGPT consultation confirmed algebraically witnesses `C + ι(A)`, not
`A + T` (a `gcd`/`dvd` argument shows the old construction's residual
can never share a factor with `f+`'s own residual on the same sheet).
**The corrected construction**: `f- := y - b_-(x)`, `b_-` the unique
degree-≤3 polynomial solving FOUR ORDINARY evaluation conditions
(`b_-(P1.X)=P1.Y`, ..., `b_-(R2.X)=R2.Y` — a plain, non-confluent 4×4
Vandermonde solve, actually simpler than file 83's confluent case since
there's no tangency point here). Builds the full parallel stack to file
83's: `minusInterpMatrix`/`minusInterpRHS`/`minusCoeff`/`bMinus`, the
degree bound and four evaluation-row lemmas, the factorization
`H.f - b_-² = denomPolyMinus * uMinusNew`, and `bMinus_ordInfOfPair =
-6` under a nondegeneracy hypothesis. **Explicitly NOT decided here**:
whether this residual matches `f+`'s own residual (the roadmap's own
"`R+ ?= R-`" question) — flagged as genuine open divisor/Jacobian
content, the actual Abel–Jacobi/Cantor relation this whole construction
exists to witness, appropriately handed to ChatGPT rather than guessed.
**Status: sorry-free.**

### 76. `CantorReductionStep.lean` (201 lines)
Imports: `Mathlib` only.

Proves that one step of Cantor reduction (`(u,v) → (u_next,v_next)`
inside `00_sample_specs.jl`'s `cantor_add` reduction loop) preserves the
Mumford identity `u ∣ f - v²`, addressing a gap flagged in
`DataDerivationSolve.lean`: `IsMumfordTarget` is currently carried there
as a bare, undischarged hypothesis, and this file is intended (combined
with a base-case fact and induction over `cantor_add`'s structure) to
eventually discharge it from Cantor's own correctness instead. **Scope:
only the reduction step**, not the earlier composition-via-`gcdx` half
of `cantor_add` — that remains a separate, not-yet-attempted lemma.
Deliberately generic over a field `K`, matching `DataDerivationMumford.
lean`'s `sq_mod_eq_of_dvd` style, so it applies wherever a Mumford pair
over any field shows up. **Explicitly flags itself as "Not yet checked
against the actual Lean toolchain"** (no REPL was available in the pass
that wrote it) — every named Mathlib lemma used is one this project has
separately confirmed elsewhere, but the file's own docstring is candid
that "matches lemmas verified elsewhere" isn't the same as "this file
itself has been built," and recommends a `lake build` confirmation
before relying on it downstream. A trailing note records substantial
outside-Lean numerical verification of the broader Cantor-correctness
claim this file is one piece of (an 18-instance Python reimplementation
check of `p_divrem`/`p_mul`/`p_sub` across the full `cantor_mul`
double-and-add path, all exact) — strong evidence, but explicitly not a
kernel-checked proof. **Status: sorry-free** (zero occurrences of the
word at all, not even in prose).

### 77. `CleanWitness.lean` (285 lines) — see `DEGREE-BOUND-FILES-INDEX-README.md` file 34
Also indexed, with the full write-up, as file 34 of the degree-bound
index (it belongs to that effort — reusable `IsRdecWitness`-cleanliness
infrastructure for the `hA`/`hB` degree-bound chain). Duplicated here by
an earlier indexing-pass accident; not repeating the full entry a second
time. **Status: sorry-free.**

### 78. `OrdAtRootMultiplicityUnified.lean` (488 lines)
Imports: `PrincipalWitness`, `LPairFinrankOneOrdAtFrac`.

Unifies `ordAt_npoly4Lcm4_eq_one_of_{R1,R2,Ra1,Ra2}`
(`PrincipalWitnessAssembly.lean`, Part 5 above) via `rootMultiplicity`,
per an explicit caller steer. Those four theorems currently split
`u_target`/`ua` into two NAMED roots via `quadratic_eq_mul_X_sub_C`,
needing `hRne`/`hRane : R1 ≠ R2` (etc.) as a never-derived, caller-
supplied hypothesis — forcing a genuine case split whenever the sample
data can produce a repeated root, which `PrincipalWitness.lean`'s own
flat-product/Layer-1-3 machinery cannot express (it insists on each
factor being nonvanishing at the target point, impossible for a double
root). **The fix**: `ordAt` at a root `α` of ANY nonzero polynomial `c`
already equals `c.rootMultiplicity α` unconditionally (`ordAt_eq_
rootMultiplicity_unramified`/`_ramified`, `LPairFinrankOneOrdAtFrac.lean`
lemma 6, already 0-sorry) — this doesn't need `c` pre-split into named
linear factors, and handles `R1=R2` (multiplicity 2) and `R1≠R2`
(multiplicity 1 at each) uniformly with no case split anywhere in the
statement. Computes `npoly4Lcm4.rootMultiplicity α` directly from the
flat-product factorization via `Polynomial.rootMultiplicity_mul_X_sub_
C_pow`-style additivity (`rootMultiplicity_npoly4Lcm4_eq_add`/`_add'`),
then splits into the `R1≠R2`/`R1=R2` (and `Ra1≠Ra2`/`Ra1=Ra2`) cases as
straightforward corollaries. **Does NOT remove `hRne` from the existing
`PrincipalWitnessAssembly.lean` theorems** — that would mean rewriting
already-proved, 0-sorry code; instead proves the unconditional
replacement as new, standalone theorems, so the two versions can be
compared and the eventual assembly theorem picks whichever it needs.
**Status: sorry-free.**

### 79. `SampleTargetFromAlphaWitness.lean` (434 lines)
Imports: `AlphaLocusDegreeUniform`, `Reduce/GeneralSharedRoot`.

`ROADMAP-alpha-to-degree-uniform.md` Part A's request for a real witness
that `SampleTargetFromAlpha.isReduction` need not be an unconstrained
`Prop`. **Diagnoses that `isReduction'` doesn't actually fit this job**:
tracing the roadmaps to see what `isReduction'`/`isReductionOf` were
FOR, this file finds `isReduction'` is a self-referential FIXED-POINT
condition (feeds `sa`'s own coordinates back into `ReduceDispatchGeneral`
as input, demands the output equal them) — designed to eventually be
instantiated once a real reduction pipeline exists, and confirmed by
direct inspection that `reducedClass_eq_of_isReduction'`
(`ReducedClassBundles.lean`) never actually unfolds its `hr :
isReduction' ...` hypothesis in its own proof body (`d :
SplitAssemblyData sa` already supplies the witnessing data structurally,
so `hr` is a real but currently-inert non-vacuity obligation on that
theorem's caller). **Design decision (Claire's direction): rather than
patch `isReduction'`, quarantine it entirely** (still available,
untouched, to invoke later) **and build a new, narrower, self-contained
predicate, `isReductionOutputOf`, here instead** — it says only "`sa`'s
coordinates equal `ReduceDispatchGeneral`'s output on some given input
data," with no self-reference and no connection to `reducedClass`/the
divisor class `sa` represents. `mk_sampleTargetFromAlpha_of_
reduceDispatch` builds such a sample directly from `ReduceDispatchGeneral`'s
own output, so `isReductionOutputOf` is discharged by the output tuple's
own `rfl` — genuinely immediate, no fixed point, no idempotence gap.
**Explicitly does NOT touch `Reduce`'s own correctness** (whether
`ReduceDispatchGeneral`'s output really is the Mumford reduction of
`alpha • aClass - ([P1]+[P2]-2•[δ₀])` in the divisor-class sense) — that
remains `reducedClass_eq_of_isReduction'`'s territory, untouched by this
file. **Status: sorry-free.**

### 80. `SanchorEqAlphaPoints.lean` (206 lines)
Imports: `PrincipalWitness`, `SanchorMumfordOrdAt`, `Reduce/AlphaReduce`,
`Reduce/GeneralSharedRoot`.

Closes `ROADMAP-principal-witness-assembly.md`'s step 0: diagnoses that
**nothing in `reducedClass_eq_of_isReduction'`'s signature ever actually
asserts `Sanchor = {sa.P1, sa.P2}`** — `CAWitness.lean`'s witness
construction takes `P1X,P2X,P1Y,P2Y` as bare free variables, while the
theorem separately has `sa.P1,sa.P2 : H.Point` and `Sanchor : Finset
H.Point` (tied to `ua`'s root set), but checked exhaustively that
`sa.P1`/`sa.P2` appear ONLY in `hcur`/`hgcd`/`hcurT`/`hgcdT` (feeding the
reduction machinery that produces the TARGET data), never alongside
`ua`/`va`/`Sanchor`. `hMumfordUa` says `(ua,va)` is SOME valid Mumford
pair for `alpha • aClass` — it says nothing about `ua`'s roots being
`sa.P1.X,sa.P2.X` specifically. **This is a genuinely missing
hypothesis, not a renaming.** Supplies the missing link as a new
hypothesis `hAnchorRoots : ua.IsRoot sa.P1.X ∧ ua.IsRoot sa.P2.X` (of the
same "caller supplies the real Mumford data" character as
`hMumfordUa`/`hMumfordTarget`) plus `Sanchor_eq_of_anchor_roots` (fully-
split case) and `Sanchor_eq_of_anchor_roots_tangent`, which turn that
hypothesis into the `Finset` equality `Sanchor = {sa.P1, sa.P2}` via the
same `quadratic_eq_mul_X_sub_C` factorization used throughout
`PrincipalWitnessAssembly.lean`/`OrdAtRootMultiplicityUnified.lean`, just
applied to `sa.P1.X,sa.P2.X` as the named roots. **`hAnchorRoots` needs
to be added to `reducedClass_eq_of_isReduction'`'s own signature** the
next time that theorem's proof body is revisited from scratch — check
directly whether `ReducedClassBundles.lean`'s actual `SplitAssemblyData`
already carries an equivalent field (it does — see `hSanchorMem`, Part 6
above — rather than assuming this file's proposed fix is still pending).
**Status: sorry-free.**

### 81. `SanchorMumfordOrdAt.lean` (251 lines)
Imports: `PrincipalWitness`, `Reduce/AlphaReduce`,
`LPairFinrankOneOrdAtFrac`.

Closes a gap flagged in a `ROADMAP-principal-witness-assembly.md` pass
note: `reducedClass_eq_of_isReduction'` needs `ordAt Q (-va) 1 = 1` for
`Q ∈ Sanchor` (and the `u`/`v`/`S` mirror) to connect `hAlphaRep`'s
`divToPair (-va) 1 Sanchor` to `CAWitness.lean`'s `f`-construction at the
point-SET level — no polynomial identity `va = bCA` ever needed, only
that both divisors assign coefficient 1 to the same named points.
Unlike `CAWitnessResidual.lean`'s heavyweight 4-point-interpolation
factorization route (needed there because `uCANew`/`bCA` ARE derived
from interpolation), `ua`/`va` here are already a standalone named
Mumford pair, so the direct route suffices: `ordAt_eq_rootMultiplicity_
unramified` (`LPairFinrankOneOrdAtFrac.lean`, unconditional) applied to
`c := pairNorm H (-va) 1 = va²-H.f`, composed with `ua ∣ (va²-H.f)`
(from `IsMumfordUa`) and `ua`'s squarefreeness forcing `rootMultiplicity
= 1` at any of its (simple, by squarefreeness) roots.
`ua_dvd_pairNorm_negVa_one` is the divisibility fact;
`ordAt_ua_eq_one_of_mem_Sanchor`/`ordAt_negVa_one_eq_one_of_mem_Sanchor`
are the resulting `ordAt` facts, plus tangent mirrors
(`_eq_two_of_mem_Sanchor_tangent`) for the doubled-root case. **Status:
sorry-free.**

### 82. `SymmetricCurveWitness.lean` (212 lines) — ⚠ not yet REPL-tested, per its own docstring — see `DEGREE-BOUND-FILES-INDEX-README.md` file 35
Also indexed, with the full write-up, as file 35 of the degree-bound
index (it belongs to the Obligation-1/`htop_ne_smul` sub-effort that
shares that directory). Duplicated here by an earlier indexing-pass
accident; not repeating the full entry a second time. **Same caution
applies as noted there**: not yet REPL-tested, sorry-free by direct
grep only.

### 83. `TangentMumfordWitness.lean` (639 lines) — ⚠ not yet build-tested, per its own docstring
Imports: `HyperellipticFunctionField`, `AffinePoints`,
`DivisorClassGroup`, `PrincipalDivisors`, `PrincipalDivisorSubgroup`,
`LCanonicalElementary`.

The `f+` witness for `ROADMAP-principal-witness-assembly.md`'s
`C + 2•[δ₀]` construction — companion to file 75's `f-`. `f+ := y -
b_+(x)`, `b_+` the unique degree-≤3 polynomial satisfying two ordinary
evaluation conditions (`Ra1.Y`/`Ra2.Y` at `Ra1.X`/`Ra2.X`) PLUS a full
tangency PAIR of conditions at `δ₀` (value AND derivative — a confluent
4-condition Vandermonde-style solve, `tangentInterpMatrix`).
**Corrected condition count this pass, from 3 to 4**: an earlier draft
used only the derivative condition at `δ₀`, dropping the value
condition — wrong, since order-2 vanishing needs BOTH to vanish
(matching `Reduce/AlphaReduce.lean`'s own two-row tangent-point
precedent). With 4 conditions, `b_+` has degree ≤3 and `ordInf(y-b_+) =
-max(2·3,5) = -6`, matching `f-`'s own pole order — both landing at `-6`
with a shared degree-2 residual divisor `R` (the file's own docstring:
`6 = 2+2+deg R ⟹ deg R = 2`), which is the `R` the roadmap's construction
needs, to be matched against `f-`'s own residual (not decided in either
file — see file 75's own "NOT decided here" note). **Status update
recorded in the docstring: all 7 original `sorry`s filled this pass** —
`bPlus_natDegree_le`, the confluent-Vandermonde determinant
`tangentInterpMatrix_det_ne_zero` (closed form
`-(Ra1X-Ra2X)(Ra1X-δ₀X)²(Ra2X-δ₀X)²`, cross-checked via sympy before the
Lean proof), the four row-identity theorems (`bPlus_eval_Ra1`/`_Ra2`/
`_delta0`/`bPlus_deriv_eval_delta0`, via a shared Cramer's-rule helper),
and `bPlus_ordInfOfPair` — **explicitly WEAKENED**: the original
unconditional `=-6` claim is FALSE in general (the degree-3 coefficient
can vanish for special input data), so it now takes `hlead : bPlusCoeff
... 3 ≠ 0` as an explicit hypothesis (not yet used by any other file at
the time of writing, so this doesn't break existing callers). **The
file's own docstring explicitly states "Not yet build-tested (no live
Lean toolchain in this environment) — Claire's REPL to confirm,"** and
flags two specific spots as most likely to need REPL-driven adjustment
(a bare `simp` before `Matrix.det_fin_four`, and the `push_cast; ring`
closings in the eval/derivative lemmas) — treat this file with the same
extra caution as file 82 until that confirmation has actually happened.
**No live `sorry` token anywhere in the file** (confirmed by direct
grep), same caveat as file 82 about what that guarantee is and isn't
worth for an unbuilt file.

---

## Not yet covered — outside `ZeroD/` entirely, stretch goal only

Every `.lean` file inside `ZeroD/` is now covered by either
`DEGREE-BOUND-FILES-INDEX-README.md` (35 files, numbered 1-35 — its own
opening note previously mis-stated this as 33; corrected there) or this
document (numbered 1-83, spanning Parts 1-4 from the previous pass and
Parts 5-7 this pass). Those 83 numbers name only 71 distinct filenames,
because this document reuses many numbers per header for file groups
(e.g. "18-21", "47-48") — and of those 71, two (`CleanWitness.lean`,
`SymmetricCurveWitness.lean`, at files 77/82 here) duplicate degree-bound
files 34/35 rather than adding new content, so this document's actual
distinct contribution beyond the degree-bound index is 69 files. Total
unique real source files: 35 (degree-bound) + 69 (this document's
distinct contribution) = **104 real source files**, matching `ZeroD/`'s
actual file count (the three Emacs autosave files,
`#CantorAddWitness.lean#`, `#CurBeforeMonicCoeffTotalDegree.lean#`,
`#QuadCoordBound.lean#`, are not real source and remain excluded from
every count in both documents).

Outside `ZeroD/`, a matching index for the top-level `Genus2Lean/` files
was flagged as a stretch goal in the previous pass and remains
unstarted: `AffinePoints.lean`, `Complexity.lean`, `AverageComplexity.lean`,
`CombinatorialSecondMoment.lean`, `CoprimeAtRootsClosed.lean`,
`DedekindClosure{2,3,4,5}.lean`, `DivisorClassGroup.lean`, `FFKSidon.lean`,
`GlobalDegreeBoundSpec.lean`, `HyperellipticClassProof.lean`,
`HyperellipticFunctionField.lean`, `LCanonicalElementary.lean`, the
`LPairFinrankOne*` family, `MatchCountAutocorr.lean`, `NonSquareFiberPoint.
lean`, `PaleyZygmund.lean`, `PrincipalDivisor*` family, `PrincipalSubgroup
Collapse.lean`, `RatioDivisorCollapse.lean`, `RiemannRochCrux.lean`,
`RiemannRochGenus2.lean`, `SidonBridge.lean`, `SidonDichotomyGeneral.lean`,
`SidonEnergy.lean`, `SumsetEnergy.lean`, `addcomb.lean`, `sidonbound.lean`
— none of these have been read this pass or the previous one; this
document says nothing about any of them, which is different from saying
they're fine.

## Sorry status, this pass (whole-directory re-verification)

Re-ran a comment-stripped, whole-word `sorry` scan across the entirety of
`ZeroD/` (both the `.lean` files this pass newly read and everything the
previous pass and `DEGREE-BOUND-FILES-INDEX-README.md` already covered).
**Result: zero live sorries**, matching every prior pass's own claim and
`ZeroD-STATUS.md`'s last verified count. All 27 files read this pass
(Parts 5-7 above) are individually confirmed sorry-free — every "sorry"
token that turns up in any of them under a naive grep is a docstring/
prose mention (typically "0 live sorry" or "sorry-free," describing a
now-resolved historical gap), not a live tactic use.

**One false-positive scare worth recording so the next pass doesn't
repeat the investigation**: an automated, regex-based "strip `/- -/`
block comments, then grep for `sorry`" script flagged
`CurBeforeMonicCoeffTotalDegree.lean` (a file covered in
`DEGREE-BOUND-FILES-INDEX-README.md`, not this pass) as having a live
`sorry`. Direct inspection of the actual file at the flagged offset
showed this was **entirely a stripping artifact** — the regex's
non-nested handling of `/- -/` blocks miscounted line numbers, and the
matched text was literally the substring "sorry-free" inside a
"written and sorry-free; nothing in this file is still unstarted"
sentence. A manual `grep -n '\bsorry\b'` directly against the raw file
(no stripping) confirms the file's only occurrence of the word is that
same "sorry-free" phrase. **Do not trust any automated comment-stripping
sorry-scan without manually verifying at least one flagged hit against
the raw file** — nested or docstring-heavy `/-! ... -/` blocks (this
project's dominant comment style) are exactly the case naive `.*?`
non-greedy block-comment regexes get wrong.

## For whoever continues this

`ZeroD/`'s own per-file coverage is now complete across the two index
documents (`DEGREE-BOUND-FILES-INDEX-README.md` + this file). The
natural next steps, in rough priority order:

1. **The stretch goal above** — a matching index for top-level
   `Genus2Lean/` files, if that's still wanted. None of those 27+ files
   have been read for indexing purposes by either pass.
2. **Spot-check the two "not yet build-tested" files** flagged in Part 7
   (`SymmetricCurveWitness.lean`, `TangentMumfordWitness.lean`) against
   an actual REPL run, if that hasn't happened since either file was
   written — both are sorry-free by inspection but explicitly
   self-described as unconfirmed against the toolchain, which is a
   different and weaker guarantee than every other file this pass or
   the previous one covered.
3. If anyone touches `PrincipalWitnessStep4.lean`'s Part 3, `Principal
   WitnessAssembly.lean`'s `MumfordPairResidualCase` section, or
   `ReducedClassBundles.lean`'s `reducedClass_eq_of_isReduction'` itself:
   read those three files' own trailing "Status note" prose in full
   first (summarized in Part 5/6 above, but the originals carry more
   hand-derivation detail than this index reproduces) — each records a
   genuine false-lemma-found-and-corrected episode, and re-deriving one
   of the same wrong routes from scratch is a real risk if only this
   summary is consulted.

Same re-derive-don't-trust caveat as `DEGREE-BOUND-FILES-INDEX-README.md`'s
own opening note applies here too: if you've touched any of the files
covered above (Parts 1-7) since this was written, re-verify rather than
trust this document blindly.
