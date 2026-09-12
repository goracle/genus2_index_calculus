# Degree-bound files: index

**Purpose**: a single file to read instead of paging through the ~9,000
lines / 29 files that make up the `totalDegree`/`IsRdecWitness` degree-bound
effort AND the separate Obligation-1 (`htop_ne_smul`) sub-effort that
shares this directory. Written by reading every file's imports, module
docstring, and top-level declarations directly — not copied from any
roadmap's own summary. Re-derive this (or at least spot-check it) if
you've touched any of these files since it was written, the same way
`ZeroD-STATUS.md` warns for the sorry inventory.

**Sorry status, verified this pass** (comment-stripped scan, whole-word
`sorry` token, all 29 files below): **zero live sorries**, project-wide,
across this entire group. Any mention of "sorry" you find inside one of
these files is docstring prose about the project's history/conventions,
not a live tactic use — matches the top-level `ZeroD-STATUS.md` claim
that all of `ZeroD/` is currently sorry-free. (Files 28/29 also carry a
couple of honestly-named `True := trivial` placeholder theorems for open
work — not sorries, but not proved content either; see their entries.)

Ordered by recency (oldest first, most recent last) — later files build on
earlier ones and the later docstrings are more likely to reflect current
reality when they disagree with an earlier file's own status note.

---

### 1. `DataDerivationTotalDegree.lean` (1410 lines)
Imports: `TheDataDerivation.DataDerivationMumford`.

The foundation of the whole chain. Bounds `MvPolynomial.totalDegree`
uniformly in the curve coefficients `(c0,...,c4)`/anchor data `(sa,sb)`
(neither is a ring variable) through `towerToRdec`'s numerator/denominator
output, propagating a bound down through the three-level tower recursion
`K2 → K1 → K0 → Rdec`. Provides the base-case machinery: `IsFractionRing`
num/den bounds, `baseFracToRing_totalDegree_le`, `combine_totalDegree_le`,
`towerToRdecK1_totalDegree_le`, `towerToRdec_totalDegree_le`, generic
`det`/`Finset.prod`/Cramer-determinant bounds (`det_totalDegree_le`,
`cramerDeltaA_totalDegree_le`, `cramerNumeratorEntry/Det_totalDegree_le`,
`cramerRatioDet_num_totalDegree_le`), and the `coeffsToNumDen`-shaped
corollary `towerToRdec_coeff_totalDegree_le` that lets `theData`'s eight
fields get their bounds in one application. REPL-confirmed for the bulk of
its content; `towerToRdec_coeff_totalDegree_le` was flagged (at write time)
as a pure substitution corollary not yet independently re-confirmed, low
risk. **Status: sorry-free.**

### 2. `CrossNondegenerateDegreeBound.lean` (302 lines)
Imports: `DataDerivationTotalDegree`, `DecoupledSystemRegular`.

States `crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le`: a
`totalDegree` bound on each of `CrossNondegenerate`'s four resultants
(`d₁*c₂ - d₂*c₁`, one per `hu0/hu1/hv0/hv1`). **Conditional** on a base-case
hypothesis `hA`/`hB` — a degree bound `D` on `uRS.coeff i`/`vRS.coeff i`
themselves, which at the time this file was written did not yet exist
unconditionally (it traces through `curBeforeMonic`'s three nested `/ₘ`
steps, for which Mathlib has no general totalDegree-transfer lemma). This
`hA`/`hB` gap is exactly what files 15/19/20 below eventually address.
REPL-confirmed green, both theorems, later pass. **Status: sorry-free
(but its own headline results are gated on a hypothesis — see files 15–20
for that hypothesis's status).**

### 3. `CramerEntryTotalDegree.lean` (381 lines)
Imports: `DataDerivationTotalDegree`.

Bounds `matrixA`/`rhsVec`'s entries at the `K2` level by classifying every
leaf that feeds them into exactly three kinds: (1) `t0` anchor abscissas
(`algebraMap`-lifted `MvPolynomial.X i`, trivial degree), (2) `w1`/`w2`
tower-adjoined roots (trivial normal form, `modByMonicHom_root_eq_X`,
proved here — not assumed), and (3) `reduceMonomialModU` output (bare
`F p` constants). Deliberately narrower than a ChatGPT-suggested fully
general "raw algebraic complexity" calculus, since these three leaf shapes
cover everything actually needed. **Status: sorry-free.**

### 4. `AnchorTotalDegree.lean` (169 lines)
Imports: `DataDerivationTotalDegree`.

Bounds `anchor1.2`/`anchor2.2` (the anchor *ordinates* `w1`/`w2`, as
opposed to file 1's abscissa bound) — pure assembly from already-proved
pieces, no new Mathlib API or mathematical content. Split into its own
file rather than appending to file 1, which was already near the
project's 1500-line-per-file guideline. **Status: sorry-free.**

### 5. `RRBasisTotalDegree.lean` (140 lines)
Imports: `TheDataDerivation.DataDerivationSolve`.

Supplies a purely combinatorial fact: a bound on `rrBasis5`'s exponent
components (`rrBasis5_order_le_six`, `rrBasis5_bi_le_three`), needed for
the `px ^ bi` factor in `matrixA`'s entries. Reuses the pigeonhole-style
witness-list technique already used elsewhere in the project
(`rrBasis5_bj_eq_zero_of_ne_yIdx`'s proof). **REPL-confirmed green (whole
project build). Status: sorry-free.**

### 6. `MatrixEntryTotalDegree.lean` (812 lines)
Imports: `AnchorTotalDegree`, `RRBasisTotalDegree`, `TowerToRdecMul`.

Assembles `matrixA`'s entrywise `totalDegree` bounds, culminating in
`matrixA_entry_totalDegree_le` (covers `matrixA row col` for any
`row : Fin 4`). Does **not** attempt `rhsVec`'s entry theorem — `rhsVec`
uses a different unfolding shape (fixed `bi_n`/`bj_n` vs. `matrixA`'s
`col`-dependent version), left to file 8. `matrixA_row0`–`row3` are
REPL-confirmed green (row2/row3 needed a heartbeat-limit increase — see
this project's heartbeats convention); `matrixA_entry_totalDegree_le`
itself was drafted but not yet independently re-sent to the REPL as of
this file's own last status note. **Status: sorry-free.**

### 7. `TowerToRdecMul.lean` (206 lines)
Imports: `TheDataDerivation.DataDerivationMumford`.

Defines the key abstraction the rest of the chain depends on:
**`IsRdecWitness`**, a field-agnostic numerator/denominator witness
predicate phrased via cross-multiplication (`evalTo n = evalTo d * v`)
rather than literal `towerToRdec` output — because `towerToRdec` is a
normal-form extraction, **not a ring homomorphism**, so it doesn't compose
through `+`/`*`. Given `IsRdecWitness`, proves `.mul` (multiplicativity —
witnesses for `a`,`b` combine into a witness for `a*b`) as "essentially
trivial algebra" once phrased this way (per a ChatGPT consultation).
Deliberately does **not** prove `towerToRdec (a*b) = (product pair)` —
that's false in general. `.div` is also proved here. **Status:
sorry-free.**

### 8. `RhsVecTotalDegree.lean` (456 lines)
Imports: `MatrixEntryTotalDegree`.

Closes the `rhsVec` entry theorem file 6 left open. Gets a simplification
`matrixA` didn't: `rrBasis5_yIdx_eq` pins `bi_n = 0`, `bj_n = 1` as
concrete literals (not merely `≤ 3`), collapsing most of the induction
needed for `matrixA`. Also adds `IsRdecWitness.neg` (missing from file 7,
a two-line corollary). Result: `rhsVec_entry_totalDegree_le`. Flagged (at
write time) as not yet independently REPL-confirmed. **Status:
sorry-free.**

### 9. `CramerWitnessAssembly.lean` (262 lines)
Imports: `TowerToRdecMul`, `DataDerivationTotalDegree`.

Bridges "every entry has an `IsRdecWitness`" (files 6, 8) to "the whole
**determinant** has an `IsRdecWitness`" — `matrixDet_isRdecWitness_of_
entries`, `cramerSolution_isRdecWitness_of_entries`. Route: builds a small
self-contained `hmapdet` helper (`f N.det = (N.map f).det`) directly from
`Matrix.det_apply'`, rather than trusting an unconfirmed Mathlib lemma
name for that fact — a first draft tried `RingHom.map_det` and hit a real
signature mismatch, caught by REPL testing. **Status: sorry-free.**

### 10. `CoeffsOutTotalDegree.lean` (455 lines)
Imports: `CramerWitnessAssembly`, `MatrixEntryTotalDegree`, `RhsVecTotalDegree`.

Assembles an actual **`totalDegree` bound** (not just an `IsRdecWitness`
existence fact) on `cramerSolution`/`coeffsOut`: `cramerNumerator_
totalDegree_le`, `matrixDet_totalDegree_le`, `cramerSolution_totalDegree_
le`, `coeffsOut_yIdx_isRdecWitness`. Uses `Classical.choose` to extract
concrete witnesses from the purely-existential per-entry facts in files 6
and 8 (legitimate — a downstream bound only needs *some* valid witness,
not the canonical one). **Flags one genuinely open, unresolved
hypothesis**: needs `evalNd (b i j) ≠ 0` for the *chosen* witness
denominators, which is not the same fact as `MatrixNondegenerate`
(`matrixA.det ≠ 0`), and no bridge between the two existed anywhere in
this project as of this pass. **Status: sorry-free** (open point is a
named hypothesis, per project convention — not a sorry).

### 11. `NpolyTotalDegree.lean` (320 lines)
Imports: `CoeffsOutTotalDegree`.

Scopes (and partially closes) a bound on `Npoly.coeff k` — the base case
`D` that file 2's `crossResultant_totalDegree_le` still carries as an open
hypothesis. Proves `algebraMap_Fp_isRdecWitness` (constants pushed through
the tower's algebra map get a trivial witness) and `Ypoly_coeff_
isRdecWitness`. Flags `Epoly`'s bound (four `bj=0` slots, harder than
`Ypoly`'s one) as not yet attempted here — closed in file 12. **Status:
sorry-free.**

### 12. `EpolyTotalDegree.lean` (413 lines)
Imports: `NpolyTotalDegree`.

Closes the `Epoly` case file 11 left open. Computes `rrBasis5`'s literal
5-element list directly (`[(0,0,0),(2,1,0),(4,2,0),(5,0,1),(6,3,0)]`) to
show `Epoly.coeff k` picks out at most one of four nonzero terms, then
bounds each via `cramerSolution_totalDegree_le` (file 10). Result:
`Epoly_coeff_isRdecWitness`. **Status: sorry-free.**

### 13. `NpolyCoeffTotalDegree.lean` (567 lines)
Imports: `EpolyTotalDegree`.

Assembles `Npoly.coeff k`'s own bound from `Epoly`/`Ypoly`/`fAtX`'s
coefficient witnesses, unrolled through `Npoly := Epoly^2 - fAtX*Ypoly^2`'s
`coeff_mul`/`coeff_sub` expansion. Introduces the reusable combinator
`IsRdecWitness_finsetSum` (a witness for a whole `Finset.sum`, given
witnesses for each term) — the missing "sum" case alongside `.mul`/`.add`/
`.neg`. Result: `Npoly_coeff_isRdecWitness`, but the bound this produces
still **grows with `k`**. **Status: sorry-free.**

### 14. `NpolyCoeffTotalDegreeUniform.lean` (96 lines)
Imports: `NpolyCoeffTotalDegree`, `DecoupledSystemRegular`.

Turns file 13's k-dependent bound into a single fixed numeral,
`Npoly_coeff_isRdecWitness_uniform`. Uses `Npoly.natDegree ≤ 6`
(already proved elsewhere) to kill every `k > 6` coefficient (trivially
`0`), and monotonicity of file 13's own formula to bound every `k ≤ 6`
case by the `k = 6` value: **`78848`**. **Status: sorry-free.**

### 15. `CurBeforeMonicCoeffTotalDegree.lean` (831 lines)
Imports: `NpolyCoeffTotalDegreeUniform`, `TheDataDerivation.DataDerivationSolve`,
`DecoupledSystemRegular`.

**Note the in-file warning: "This version takes forever to build, please
do not add more stuff to it."** Currently on Revision 08 (moved coeff-zero
equality transport outside `IsRdecWitness` to avoid an `isDefEq` timeout —
treat this file as build-time-sensitive; don't casually extend it.

Closes the base-case gap files 2/11 flagged: a `totalDegree` bound on
`curBeforeMonic.coeff {0,1,2}` (its only possibly-nonzero coefficients).
Mathlib has no general totalDegree-transfer lemma for `Polynomial.
divByMonic` chains, so this file avoids division entirely: uses the EXACT
multiplication identity `Npoly = curBeforeMonic * (t1X * t2X * U)` plus
the triangular coefficient system that factorization forces (a ChatGPT-
confirmed route). Result: `curBeforeMonic_coeff_totalDegree_le`, bound
**`≤ 315448`**, uniform across coeff 0/1/2. **Status: sorry-free** (but
budget your build-time expectations for this one specifically).

### 16. `URSCoeffIsRdecWitness.lean` (400 lines)
Imports: `CurBeforeMonicCoeffTotalDegree`.

Bridges file 15's `curBeforeMonic` bound to `uRS.coeff i`'s bound (`uRS :=
C curBeforeMonic.leadingCoeff⁻¹ * curBeforeMonic`) via `IsRdecWitness.div`
(file 7) — needs one genuine case split on which of coeff{0,1,2} is the
leading coefficient (`natDegree ≤ 2`, not `= 2` unconditionally),
handled by `interval_cases`/`omega`. Result: `uRS_coeff_isRdecWitness`,
bound **`≤ 630896`** (315448 + 315448, matching `.mul`'s additive bound
convention). **Status: sorry-free.**

### 17. `MvPolynomialTotalDegreeMulEq.lean` (262 lines)
Imports: `Mathlib` only — **no `Genus2Lean` imports, fully generic**.

Standalone commutative-algebra infrastructure: `MvPolynomial.totalDegree`
is *exact* (not just `≤`) for products of nonzero elements over a domain
(`MvPolynomial.totalDegree_mul_of_ne_zero`), and the corollary actually
needed downstream, `MvPolynomial.totalDegree_le_of_mul_eq_of_ne_zero`
(`c*a' = a`, `a ≠ 0`, domain ⟹ `c.totalDegree ≤ a.totalDegree`). Filled a
real Mathlib gap found this pass — no equality/reverse-direction lemma
existed under any plausible name; proved via
`homogeneousComponent`/`IsHomogeneous.totalDegree`. Applies to `F p`
trivially (`[CommRing R] [IsDomain R]`, no closed-field or curve-specific
content). **Status: sorry-free.**

### 18. `AlgebraMapFpLiteralTotalDegree.lean` (218 lines)
Imports: `DataDerivationTotalDegree`.

Closes the second half of the literal (not existential) `hA`/`hB` gap
`CrossNondegenerateDegreeBound.lean` (file 2) needs: bounds `gu0 :=
algebraMap (F p) (K2 ...) u0` / `gu1 := ... u1` (`curBeforeMonic`'s `Q`
factor's constant coefficients), by factoring the algebra map through `K0`
(`IsScalarTower.algebraMap_apply`, already used elsewhere in the project
for the same purpose) then propagating via file 1's tower-step theorems.
The first half (`t1`/`t2`'s literal bound) was already done in file 1.
**Status: sorry-free.**

### 19. `CrossResultantIsRdecWitness.lean` (245 lines)
Imports: `DecoupledSystemRegular`, `TowerToRdecMul`.

The actual resolution of file 2's `hA`/`hB` hypothesis, found after two
candidate fixes were checked and explicitly ruled out (both documented in
this file's own header: (1) reshaping an existential witness into a
literal-pair fact doesn't work, since a witness isn't unique; (2)
composing separately-bounded pieces fails because `towerToRdec` doesn't
respect `+`/`*`). **The actual fix**: `CrossNondegenerate`'s `hu0`/etc.
fields, on direct inspection, unfold via `rfl` to exactly `theData`'s
literal `towerToRdec`-computed fields — so there's no reconciliation
needed between "a witness" and "the specific pair" in the first place.
Result: `uResultant_isRdecWitness`/`vResultant_isRdecWitness`. **This is
listed in `ZeroD-README.md` as a separate, genuinely weaker honest fact
(`IsRdecWitness`, not `totalDegree`) about the same resultant elements —
does NOT by itself discharge file 2's `hA`/`hB` totalDegree hypothesis;
check `ZeroD-README.md`'s "item 1" update before assuming either file
closes the other.** **Status: sorry-free.**

### 20. `QuadraticCoordinateBridge.lean` (225 lines)
Imports: `TheDataDerivation.DataDerivationMumford`, `DataDerivationTotalDegree`.

An attempted further step beyond file 19: extracting degree-bounded
witnesses for a quadratic tower element's two *normal-form coordinates*
(`d0`,`d1` with `v = d0 + d1*w`) from a witness for `v` as a whole (the
"conjugate trick" `ROADMAP-crossnondegenerate-degree-bound.md` describes).
**Explicitly documents two routes that do NOT work** (checked by hand,
not assumed): (1) a single witness equation is one linear equation in two
unknowns, and no Galois automorphism swapping `w ↦ -w` is available
anywhere in this project to supply a second; (2) `IsRdecWitness`'s witness
pair is always base-ring-valued, so there's no `w`-coordinate structure on
it to decompose via a 2×2 Cramer solve (ChatGPT's originally proposed
route). **Conclusion: the coordinate bound needs to come from directly
tracing the arithmetic construction, not reverse-engineered from an
existing whole-value witness** — flagged as a genuinely separate,
not-yet-attempted derivation. **Status: sorry-free** (this file proves
useful supporting lemmas — `w1_sq_eq_public`, the `K1`/`K2` quadratic
normal forms, `base_isRdecWitness_bridge`, `num_den_isRdecWitness` — but
does *not* itself close the coordinate-bound gap it scopes).

### 21. `IdealOfListNeTopFromEval.lean` (110 lines)
Imports: `Mathlib` only — **fully generic, no `Genus2Lean` content**.

Separate sub-effort: infrastructure toward `ROADMAP-degree-uniform-
step3.md`'s Obligation 1 (`htop_ne_smul`), not the degree-bound chain
above. Proves the general commutative-algebra fact that a ring hom into
any nontrivial ring sending every generator in a list to `0` proves the
generated ideal is proper (`Ideal.ofList_ne_top_of_forall_eval_eq_zero`
and two variants). Deliberately does **not** construct the actual curve
point or solve the matching equations — that's separate, curve-specific
future work. **Status: sorry-free.**

### 22. `MvPolynomialLinearSolve.lean` (102 lines)
Imports: `Mathlib` only — **fully generic**.

Second piece of the same Obligation-1 infrastructure as file 21: given
`n - X j * d` (one of `genList`'s 8 matching generators) where `j` doesn't
appear in `n` or `d`, shows the equation vanishes at *some* value of
`X j` (namely `n/d` evaluated) while leaving every other coordinate fixed.
Does not yet apply this to `genList`'s actual 8 generators or exhibit the
curve-side assignment — left for a later pass combining this with file 21.
**Status: sorry-free.**

### 23. `NegateVarTotalDegree.lean` (223 lines)
Imports: `Mathlib` only — **fully generic**.

Standalone infrastructure toward file 20's "conjugate trick": proves that
negating one `MvPolynomial` generator variable (fixing all others) is an
involutive ring automorphism that preserves `totalDegree` **exactly**
(not just as an upper bound), since it only flips monomial signs, never
touching the exponent tuple — so `support`, and hence `totalDegree`
(a `Finset.sup` over `support`), is unchanged verbatim. Does **not** build
the actual 2×2 Cramer solve the conjugate trick needs, or touch any
`Genus2Lean`-specific type — pure generic algebra, left for a later
pass. **Status: sorry-free.**

### 24. `QuadraticCoordArith.lean` (215 lines)
Imports: `TowerToRdecMul`.

Attacks file 20's coordinate-bound gap from a different angle than the
(ruled-out) "reverse-engineer from a whole-value witness" route: traces
the arithmetic construction directly. For a monic quadratic
`g := X^2 - C c`, proves the explicit closed-form coordinate
multiplication rule `(x0+x1 w)(y0+y1 w) = (x0 y0 + c x1 y1) + (x0 y1 + x1
y0) w` (`mk_mul_coord_eq`), fully generically (`CommRing R`, no
`Field`/`Genus2Lean` content) — reusable verbatim at both the `K1` and `K2`
tower levels. **§1 (the identity) is complete and REPL-tested; §2
(packaging it as an `IsRdecWitness` bridge) is explicitly NOT drafted** —
its own header records why a first attempt was type-incorrect and lists
two concrete options for next time. Closing `hA`/`hB` fully still needs
§1/§2 threaded through `curBeforeMonic.coeff i`'s actual construction
(file 15), not attempted here. **Status: sorry-free** (as far as it goes
— §2 is scoped, not proved).

### 25. `TowerToRdecRenameSymmetry.lean` (442 lines)
Imports: `TheDataDerivation.DataDerivationMumford`, `DecoupledSystemRegular`.

Separate sub-effort — Obligation 1 (`htop_ne_smul`), not the `hA`/`hB`
chain. Proves `towerToRdec`'s rename-equivariance in full generality
(`towerToRdec_rename`: renaming `SideGens` along any `ρ` intertwining two
records' `tGen`/`wGen` maps commutes with `towerToRdec`), then specializes
to `idxSwap` (the a-side/b-side variable-pairing involution) to get
`towerToRdec_bSideGens_eq_rename_idxSwap`. **Punchline, stated in full
generality as `cross_resultant_slot_eq_zero_of_symmetric`, with four named
one-line corollaries matching `CrossNondegenerate`'s `hu0`/`hu1`/`hv0`/`hv1`
exactly**: for the special case `sa = sb` and an `idxSwap`-symmetric
assignment, all four cross-resultants vanish identically, no curve
computation needed. **Note the later ChatGPT consult recorded in
`CurvePointExistenceFromCounting.lean`/`ROADMAP-degree-uniform-step3.md`
found this `sa = sb` specialization unnecessary for the counting-existence
argument** — this file's result is still a genuine, useful fact (a free
proof of (c) in the symmetric sub-case), just not on the critical path the
project ended up taking. **Status: sorry-free.**

### 26. `MvPolynomialSharedTargetSolve.lean` (105 lines)
Imports: `MvPolynomialLinearSolve`.

Corrects file 22's own closing note. `FuList`/`FvList` do NOT have one
generator per target variable — each of `U0,U1,V0,V1` is shared by TWO
generators (one per sample), which can only vanish simultaneously if the
corresponding `CrossNondegenerate` cross-resultant vanishes at the chosen
point. Proves the actual solve for one shared-target pair given that
vanishing. **Flags precisely that Obligation 1's closure is NOT
independent of the cross-resultant story the way an earlier roadmap
framing suggested.** **Status: sorry-free.**

### 27. `GenListNeTopFromCurvePoint.lean` (770 lines)
Imports: `MvPolynomialSharedTargetSolve`, `IdealOfListNeTopFromEval`,
`DecoupledSystemRegular`.

The actual `Genus2Lean`-specific composition files 21/22/26 were all
building toward. Chains file 26's single-pair solver across all 4 targets
from one shared curve-side assignment (`genList_exists_common_zero_of_
curve_witness`), using a new general lemma
(`MvPolynomial.eval_eq_eval_of_update_notMem`) to show each later update
leaves earlier pairs'/the curve relations' evaluations undisturbed, then
composes with file 21 into `ideal_ofList_genList_ne_top_of_curve_witness`.
**`genList_exists_common_zero_of_curve_witness` is REPL-confirmed green;
`ideal_ofList_genList_ne_top_of_curve_witness` was not yet independently
re-confirmed as of this file's own last status note.** Narrows Obligation
1's remaining gap to exactly: a curve-side assignment satisfying (a) the 4
curve relations, (b) the 8 denominators nonzero, (c) the 4 cross-resultants
vanishing — everything else is now built. **Status: sorry-free.**

### 28. `TowerCoeffWitnessDescent.lean` (583 lines)
Imports: `TowerToRdecMul`, `TheDataDerivation.DataDerivationMumford`,
`QuadraticCoordinateBridge`.

Continues file 20/24's coordinate-bound line, per a ChatGPT consult on
exactly this question. `coeffDescent_core` (the `Δ*e0=R0`/`Δ*e1=R1`
algebraic identity, pure `ring`) and `coeffDescent_totalDegree_le` (the
degree-bound half, direct `totalDegree_mul`/`_add`/`_sub` chasing) are
both proved, plus `_b0` specializations matching the fact that this
project's actual `K1_poly_monic`/`K2_poly_monic` always have `b = 0`.
**Corrects an earlier wrong assumption in-file**: `coeffDescent_core` and
`towerToRdec`/`towerToRdecK1` solve *opposite-direction* problems and do
not compose the way a first draft assumed — caught and documented
(`coeffDescent_purpose_note`) before being asserted as a theorem, not
after. **Still genuinely open**: `norm_ne_zero_iff_placeholder` needs a
real Mathlib `AdjoinRoot`/norm API lookup (not attempted, per the
project's "don't guess an API shape" convention), and the actual assembly
decomposing an existing whole-element witness (e.g. file 15's `≤315448`
fact) via `coeffDescent_core` still needs that witness's construction
inspected directly — flagged as the concrete next step, not attempted
this pass. **Status: sorry-free** (two `True := trivial` placeholder
theorems, `norm_ne_zero_iff_placeholder`/`coeffDescent_purpose_note`,
mark open work honestly rather than hiding it — not live sorries, but
don't mistake them for proved content either).

### 29. `CurvePointExistenceFromCounting.lean` (210 lines)
Imports: `Mathlib` only — **fully generic, no `Genus2Lean` content**.

Separate sub-effort — Obligation 1's part (a) (curve-point existence),
not the `hA`/`hB` chain. First ChatGPT consult produced the general
finite-combinatorics package: `exists_good_not_mem_bad`/`_fintype` (a
union-bound existence lemma: if `#good` strictly exceeds the sum of `#bad
i` bounds, some point avoids every `bad i`) and `hasseWeil_gives_surplus`/
`exists_good_not_mem_bad_of_hasseWeil` (packaging a Hasse-Weil-style
`n ≥ p - k` hypothesis into that lemma's `hcard` side condition). **Second
consult, later pass**, added the piece needed to actually apply this:
`poleOrderBound_of_monomial` (exact `2r+5s` pole-order-at-infinity weight
for a genus-2 curve `y²=f(x)`, `deg f = 5`), `poleOrderBound_le_five_mul_
totalDegree` (crude `≤5d` fallback from ordinary total degree), and
`hasseWeil_of_uniform_totalDegree` (composed form taking a single uniform
degree bound `d` straight to the existence conclusion). **Also determined,
this consult: the doubled-point (`sa=sb`,`a1=a2`) specialization file
25 built is not needed here** — no argument beats plain Hasse-Weil for
this case, so the general `sa≠sb` statement is the right target to
instantiate directly. **Not yet REPL-confirmed** — drafted this pass;
Claire tests via the REPL. Curve-specific instantiation (plugging in
`theData`'s actual denominators' degree bounds) is still future work.

---

## Open gaps, cross-referenced (read this before assuming the chain is done)

- **File 2's `hA`/`hB` hypothesis** (a literal, not merely existential,
  `totalDegree` bound on `uRS.coeff i`/`vRS.coeff i`) is the throughline
  most of files 15–20 exist to close. As of file 20's own header, the
  "conjugate trick" (extracting per-coordinate bounds from a whole-value
  witness) has **two ruled-out routes** and no proved route yet — the
  coordinate-level bound itself is still open. File 19 closes an adjacent
  but weaker fact (`IsRdecWitness`, not `totalDegree`) and does **not**
  discharge `hA`/`hB` on its own.
- **File 10's open hypothesis** (`evalNd (b i j) ≠ 0` for chosen
  witnesses, distinct from `MatrixNondegenerate`) had no bridge anywhere
  in the project as of that file's writing — check whether one has been
  built since before treating `coeffsOut`'s bound as unconditional.
- Files 21–22 (Obligation 1, `htop_ne_smul`) are a **separate sub-effort**
  from the `totalDegree`/`hA`/`hB` chain above — don't conflate the two
  when scoping new work; they share this directory but not a dependency
  edge.
- **Files 25–29 continue both sub-efforts and are the current frontier**:
  25 (Obligation 1, `sa=sb` cross-resultant symmetry — later found
  unnecessary for the counting-existence route file 29 takes), 26–27
  (Obligation 1, the actual `genList`/`htop_ne_smul` composition, now
  narrowing the remaining gap to a curve-side witness satisfying (a)/(b)/
  (c)), 24/28 (the `hA`/`hB` coordinate-bound line, still open — 24's §2
  unwritten, 28's final assembly unattempted), 29 (Obligation 1's part (a),
  general counting machinery now complete pending curve-specific
  instantiation). Cross-reference `ROADMAP-degree-uniform-step3.md`'s own
  three-obligation split before assuming any one of these closes more than
  it actually does.
