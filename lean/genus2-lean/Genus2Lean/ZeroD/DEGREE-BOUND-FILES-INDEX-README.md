# Degree-bound files: index

**Purpose**: a single file to read instead of paging through the ~10,000
lines / 35 files that make up the `totalDegree`/`IsRdecWitness` degree-bound
effort AND the separate Obligation-1 (`htop_ne_smul`) sub-effort that
shares this directory. Written by reading every file's imports, module
docstring, and top-level declarations directly — not copied from any
roadmap's own summary. Re-derive this (or at least spot-check it) if
you've touched any of these files since it was written, the same way
`ZeroD-STATUS.md` warns for the sorry inventory.

**Note on file 34/35's overlap with the extended index**: `CleanWitness.
lean` (file 34) and `SymmetricCurveWitness.lean` (file 35) are ALSO
indexed in `ZERO-D-EXTENDED-INDEX-README.md` (as its files 77/82) — a
genuine accidental double-entry from the two indexing passes, not an
intentional shared appendix. This file keeps the full write-up for both;
the extended index now just points back here. Don't double-count these
two when tallying `ZeroD/`'s total file coverage across both documents.

**Sorry status, verified this pass** (comment-stripped scan, whole-word
`sorry` token, all 35 files below): **zero live sorries**, project-wide,
across this entire group. Any mention of "sorry" you find inside one of
these files is docstring prose about the project's history/conventions,
not a live tactic use — matches the top-level `ZeroD-STATUS.md` claim
that all of `ZeroD/` is currently sorry-free. (Files 28/29 also carry a
couple of honestly-named `True := trivial` placeholder theorems for open
work — not sorries, but not proved content either; see their entries.)

Ordered by recency (oldest first, most recent last) — later files build on
earlier ones and the later docstrings are more likely to reflect current
reality when they disagree with an earlier file's own status note.

**Files 36–49 added, later pass**: a separate sub-effort from files
1–35 above — `ROADMAP-monic-annihilator-degree-uniform.md`'s
finite-dimension (`finrank`) bound track, not the
`totalDegree`/`IsRdecWitness` chain those 35 files cover. **Sorry status
for files 36–49, verified this pass** (same comment-stripped, whole-word
`sorry` scan as the note above): **zero live sorries** across all
fourteen. File 49 (`GenListFinrankAssembly.lean`) was the stub as of that
pass — since superseded, see the note below and files 50–54's own
entries: it now carries one genuine LIVE `sorry` (not a `True := trivial`
placeholder any more), and the correction that made this necessary
(`ROADMAP-monic-annihilator-degree-uniform.md`'s "CORRECTION, later
pass" section) is exactly what files 50–54 exist to eventually close.

**Files 50–54 added, later pass still — the base-case correction and its
partial resolution.** A re-run of the whole-project sorry scan this pass
(the same script `ZeroD-STATUS.md` documents) found `ZeroD-STATUS.md`'s
own "zero sorries under `ZeroD/`" claim already stale: `genList_finrank_
assembly_placeholder`'s honest `True := trivial` stub was, at some point
after file 49 was first written, replaced with a genuine `sorry` in
`genList_finrank_le` — because the file plan file 49 describes (routes
(a)/(b), both inducting directly on `Ideal.ofList` prefixes of the
fixed-arity `Rdec p`) turned out to have **no valid base case**: no
prefix of a fixed-arity polynomial ring is finite-dimensional until every
variable is eliminated, including the empty prefix (`Rdec p` itself, a
12-variable free polynomial ring). Files 50–54 are the ChatGPT-consulted
fix: instead of inducting on `Ideal.ofList` prefixes of `Rdec p`, induct
on the ambient ring's ARITY via `MvPolynomial.finSuccEquiv`, so the
`n = 0` case genuinely is `K`-finite (`MvPolynomial (Fin 0) K ≃ₐ[K] K`).
This index now covers 55 files total. **Sorry status for files 50–55,
verified this pass**: **zero live sorries** across files 50–54 — but file
55 (`GenListFinrankAssembly.lean`, re-entered below under its
post-correction status) is the one file in this whole 55-file index that
currently has a live `sorry`, and closing it (the literal `Idx`-specific
wiring, item (d) of the roadmap's revised plan) is the actual next step,
not yet done as of this pass.

**Files 79–84 added, this pass — six files found unindexed in either
this document or `ZERO-D-EXTENDED-INDEX-README.md`.** Two threads: (79)
`StabOfSmallSetTrivial`, (80) `MatchingSolutionSwapSymmetry`, (81)
`SampleTargetFromAlphaPairMemA`, (82)
`DecoupledSystemDegreeUniformFixedTarget` are the `Δ=0`/fixed-target
line that supersedes the old `genList_finrank_le`/`Stab(S)` route for
closing the 8th-moment gap's degree-uniform target outright (see entry
82's own note). (83) `GenListFinrankFourStageTransport` and (84)
`GenListPairwiseAgreementTransport` are mechanical order-transport
files for the still-live `finrank`/pairwise-agreement chain (entries
55/78/76), each naming a genuinely open base-case gap as a hypothesis
rather than closing it. This index now covers 84 files total. **Sorry
status for files 79–84, verified this pass**: **zero live sorries**
across all six — file 55's `sorry` (above) remains the only live sorry
project-wide across this whole 84-file index, and per entry 82's note it
may now be moot: the fixed-target route entries 79–82 build does not
need `genList_finrank_le` at all.

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

### 7. `TowerToRdecMul.lean` (206 lines at write time, 257 now — grown since)
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

### 18. `AlgebraMapFpLiteralTotalDegree.lean` (218 lines at write time, 229 now — grown since)
Imports: `DataDerivationTotalDegree`.

Closes the second half of the literal (not existential) `hA`/`hB` gap
`CrossNondegenerateDegreeBound.lean` (file 2) needs: bounds `gu0 :=
algebraMap (F p) (K2 ...) u0` / `gu1 := ... u1` (`curBeforeMonic`'s `Q`
factor's constant coefficients), by factoring the algebra map through `K0`
(`IsScalarTower.algebraMap_apply`, already used elsewhere in the project
for the same purpose) then propagating via file 1's tower-step theorems.
The first half (`t1`/`t2`'s literal bound) was already done in file 1.
**Status: sorry-free.**

### 19. `CrossResultantIsRdecWitness.lean` (245 lines at write time, 279 now — grown since)
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

### 29. `CurvePointExistenceFromCounting.lean` (210 lines at write time, 214 now — grown since)
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

### 30. `QuadCoordBound.lean` (306 lines)
Imports: `QuadraticCoordArith`.

Continues file 24's "trace the arithmetic construction directly" route
against the coordinate-bound gap: `HasQuadBound dg c x a0 a1`, a
coordinate-level bound predicate parametrized by an abstract "degree"
function `dg : R → ℕ` (not fixed to `MvPolynomial.totalDegree`, so the
same machinery serves both the `K0→K1` and `K1→K2` tower steps by
instantiating `dg` differently at each call site). Proves the full
closure suite `.zero`/`.one`/`.add`/`.neg`/`.sub`/`.pow`/`.mul` — the last
needs a genuine extra hypothesis (`dc`, a bound on the extension's own
constant `c`), matching the same structural need `K2CoordArith.lean`
(file 32) inherits one level up. **REPL-confirmed green, later pass**
(five issues surfaced and fixed on the first REPL run — see the file's
own "Update" note — including a `mul` proof rewritten twice before
landing on a `set`/`rw`-free final form to avoid a `whnf` timeout, the
same failure mode file 32 hit and fixed the same way). **Status:
sorry-free.**

### 31. `HasRdecBound.lean` (179 lines)
Imports: `QuadCoordBound`, `TowerToRdecMul`, `NpolyTotalDegree`,
`RhsVecTotalDegree`.

Instantiates file 30's abstract `dg` slot with a RELATION rather than a
function: **`HasRdecBound ι evalNd v D`** := `v` has *some*
`IsRdecWitness` (file 7) numerator/denominator pair both `totalDegree ≤
D` — needed because "has a bounded witness" doesn't fit `dg : R → ℕ`'s
shape (a value can have witnesses at many degrees, no canonical one).
Proves the four closure lemmas fresh against this relation
(`hasRdecBound_zero/_neg/_add/_mul`, confirmed against the actual
combinator suite in files 7/11/8, not assumed) — `.add`'s bound is a SUM
not a `max` (unlike file 30's abstract `.add`, since clearing a common
denominator via cross-multiplication genuinely costs more than plain
coordinate addition), documented explicitly as a deliberate, harmless
divergence from file 30's shape. Also defines `HasQuadCoordBound`,
file 30's `HasQuadBound` restated against `HasRdecBound` for both
coordinates directly. **Not yet independently REPL-confirmed as of this
file's own last status note** (though file 32, built on top of it,
subsequently was). **Status: sorry-free.**

### 32. `K2CoordArith.lean` (401 lines)
Imports: `QuadraticCoordArith`, `QuadraticCoordinateBridge`, `HasRdecBound`.

**`K2`-native version of files 24/30/31's machinery, purpose-built (per
its own header) as a THIRD route around file 20's coordinate-bound dead
end**: propagate degree bounds FORWARD through a construction's own
`.add`/`.mul`/`.neg` arithmetic, rather than extracting them backward from
an opaque whole-value witness (both of file 20's ruled-out routes were
backward-extraction attempts). Provides `coord0`/`coord1` (`K2`'s own
canonical `AdjoinRoot.modByMonicHom`-coordinate extraction, no
representative-choice ambiguity), the identities `coord{0,1}_add/_neg/
_sub/_mul` (`coord_mul` proved via `mk_mul_coord_eq`, file 24), and
`HasCoordBoundK2` with closure lemmas `hasCoordBoundK2_add/_neg/_sub/
_mul` built on file 31's `HasRdecBound`. **REPL-confirmed green**, after
three rounds of fixes (all now recorded in the file's own "Update" note):
(1) `coord_mul`'s multiplication-identity proof originally timed out at
`whnf`/hit an `isDefEq` timeout from combining a surjection-witness
substitution (`rw [← hfa]`) with a heavy lemma rewrite
(`AdjoinRoot.modByMonicHom_mk`/`mk_mul_coord_eq`) in one `rw` call —
fixed by splitting into standalone `have`s plus `congrArg`, mirroring
file 30's own documented fix for the identical failure mode, plus
correcting a wrong-direction `rw [hfa]` that should have been `rw [←
hfa]`; (2) `hasCoordBoundK2_add/_neg/_sub` originally used `rw
[coord{0,1}_{add,neg,sub}]` directly against a `HasRdecBound` goal, which
fails with "motive is not type correct" (`HasRdecBound` is generic in an
implicit `[CommRing K]`, and `K1 p ...` is reducibly-but-not-syntactically
an `AdjoinRoot`, so `rw`'s automatic motive search generalizes the wrong
instance) — fixed with explicit `Eq.mpr (congrArg (fun t => HasRdecBound
p ι evalNd t D) heq) proof` in place of every such `rw`; (3)
`hasCoordBoundK2_mul`'s first branch built a bound for the wrong
parenthesization of `k2Const * coord1 a * coord1 b` (left-associative
`*`, so `(k2Const * coord1 a) * coord1 b`, not `k2Const * (coord1 a *
coord1 b)`) — fixed by regrouping the two `.mul` applications to match.
Claire also raised `coord_mul`'s own heartbeat limit for the final green
build. **Does NOT close file 2's `hA`/`hB`, confirmed by direct
comparison against files 18/19's own closing notes (both predate this
file): `towerToRdec` is not a ring homomorphism, so this file's closure
lemmas — built on the same existential-witness category as `IsRdecWitness`
itself — inherit the identical structural limitation those two files
already independently found. See `ROADMAP-crossnondegenerate-degree-
bound.md`'s final "Update" section for the full account.** **Status:
sorry-free** (correct, reusable `K2`-arithmetic infrastructure; not
itself a step toward `hA`/`hB`).

### 33. `UrsVrsCoeffQuadCoordBound.lean` (95 lines)
Imports: `URSCoeffIsRdecWitness`, `HasRdecBound`.

An earlier, narrower attempt at the same gap file 32 was built to work
around — predates file 32 (see the two files' timestamps) and reaches an
incomplete state consistent with (not contradicted by) file 32's later,
more general finding. Proves only the representative-existence half of
a "reshape a whole-value witness into its own coordinates" bridge
(`uRS_coeff_exists_rep`: `uRS.coeff i` has SOME `Polynomial (K1 ...)`
representative whose `%ₘ`-remainder computes its canonical
`modByMonicHom` coordinates) — pure `AdjoinRoot.mk_surjective` +
`AdjoinRoot.modByMonicHom_mk`, no degree content. Its own header
explicitly flags the degree half as NOT attempted in this file. **Status:
sorry-free** (as far as it goes — no degree-bound theorem is proved
here; superseded in intent, not contradicted, by file 32's from-scratch
`K2`-native route).

### 34. `CleanWitness.lean` (285 lines)
Imports: `TowerCoeffWitnessDescent`.

A reusable structure, `CleanWitness` (a triple `(N0,N1,D0)` representing
a "clean at `w`" witness pair `n = N0+N1·w`, `d = D0` — no `w` at all in
the denominator, for a fixed generator `w := X (sg.wGen 1)`), for
propagating cleanliness through `IsRdecWitness.add`/`.mul`/`.neg`
without re-deriving the bookkeeping by hand at every node of every
future `Q.coeff i`/`g.coeff i` witness tree — packaging what
`TowerCoeffWitnessDescent.lean` (file 28) established by hand for one
specific tree (`Q.coeff 3`) into a reusable gadget. **Deliberately
scoped, not general-purpose**: matches exactly the shape
`towerToRdec_output_shape` produces (whose denominator never contains
`sg.wGen 1`), which is why a `D1` (`w`-coefficient on the denominator)
is never carried at all — mirroring this project's `b=0` convention
throughout (`K1_poly_monic`/`K2_poly_monic` are always `X² - C(const)`).
Provides `CleanWitness.toPair` (the bridge to `IsRdecWitness`'s own pair
shape), `.add`/`.mul`/`.neg` (the algebraic operations), `toPair_add`/
`toPair_neg` (proved as pure `MvPolynomial` identities, `ring`-checkable,
no `w²=c` relation needed — `.add`/`.neg` never create a `w²` term),
`evalNd_toPair_mul` (`.mul` matches `IsRdecWitness.mul`'s raw pair only
AFTER `evalNd`, proved directly from `w² = φc` rather than via
`mul_clean_reduce` composition, which mismatched `κ`/`φc` bookkeeping on
a first attempt), and the matching `totalDegree` bounds
(`add_totalDegree_le`/`neg_totalDegree_le`/`mul_totalDegree_le`) for all
three operations, stated using the same `hA`/`hB`-named hypothesis shape
files 2/18/19/32 already use. **Does not itself close file 2's `hA`/`hB`**
— it's infrastructure for assembling a concrete witness tree (e.g.
`Q.coeff 3`'s), not a proof that such a tree closes the bound; the
concrete next step (naming each base witness's own `(N0,N1,D0)` triple
and folding it through `.add`/`.mul`/`.neg`) is flagged in the file's own
docstring as not attempted here. **Status: REPL-confirmed this pass** —
build green, all four theorems (`toPair_add`, `toPair_neg`,
`evalNd_toPair_mul`, and the three `totalDegree` bounds) typecheck;
sorry-free.

### 35. `SymmetricCurveWitness.lean` (212 lines) — ⚠ not yet REPL-tested, per its own docstring
Imports: `GenListNeTopFromCurvePoint`, `TowerToRdecRenameSymmetry`.

Builds a concrete, symbolic curve witness for `ROADMAP-degree-uniform-
step3.md`'s Obligation 1, **deliberately avoiding Hasse-Weil entirely**
(unlike file 29's `CurvePointExistenceFromCounting.lean` counting/
genericity approach): for a genuine DLP-attack instance, the attacker
already HAS two known curve points (that's what a discrete-log match
consists of), so existence of SOME point is never actually in question —
what's needed is turning "one known point" into a full `assign`
satisfying the curve relations (a), the nonvanishing-denominators
condition (b), and the vanishing cross-resultants (c). File 25
(`TowerToRdecRenameSymmetry.lean`) already supplies (c) for free (its
`cross_resultant_*_eq_zero_of_symmetric` facts hold identically, by pure
symmetry, at any `assign` fixed by `idxSwap` — the same symmetry file 25
found unnecessary for the counting-existence route file 29 actually
took, reused here for a different route instead). **Plan**: take one
curve point pair, build the symmetric `assign` that copies it onto the
b-side coordinates verbatim (`symmetricAssign`), get (c) free from the
reused symmetry file, and reduce (a) from 4 independent conditions to
the 2 the input point already satisfies (the b-side conditions become
identical to the a-side ones under the copy). **(b) is explicitly NOT
attempted here** — a genuine nonvanishing check on `theData`'s 8
denominators at this specific `assign`, left for later.
`symmetricAssign_idxSwap_fixed`, `symmetricAssign_curveA{1,2}_eq_
curveB{1,2}`, `symmetricAssign_curve_relations`, and
`symmetricAssign_cross_resultants` are the resulting theorems. **The
file's own final line reads "Status: new file, not yet REPL-tested"** —
distinct from every other file in this index, all of which describe
themselves as REPL-confirmed; treat this one with correspondingly more
caution until Claire's REPL has actually run it. **No live `sorry` token
anywhere in the file** (confirmed by direct grep), which is a weaker
guarantee than usual here given the untested status — a `sorry`-free
file that hasn't been built can still fail to typecheck for other
reasons.

### 36. `FinrankLeOfMonicAnnihilator.lean` (148 lines)
Imports: none project-internal (`Mathlib` only).

Belongs to a separate sub-effort from files 1–35 above:
`ROADMAP-monic-annihilator-degree-uniform.md`'s finite-dimension-bound
track, not the `totalDegree`/`IsRdecWitness` chain. Item 1 of that
roadmap's file plan and the engine the rest of the track is built on.
States `finrank_le_of_monic_annihilator`: if `B` is an `A`-algebra, `A`
is `k`-finite, `t : B` satisfies a monic degree-`d` polynomial relation
over `A`, and `t` generates `B` as an `A`-algebra
(`Algebra.adjoin A {t} = ⊤`), then `finrank k B ≤ d * finrank k A`. Proof
route: `AdjoinRoot.liftAlgHom` surjects `AdjoinRoot G ↠ B`, and
`AdjoinRoot G` is a finite free `A`-module of rank `d`
(`AdjoinRoot.powerBasis'`), giving `finrank k (AdjoinRoot G) = finrank k
A * d` via the tower law, from which a surjective `k`-linear image
(`LinearMap.finrank_le_finrank_of_surjective`) cannot exceed. Its own
docstring flags one API-correction pass (the `AdjoinRoot.liftAlgHom`
instantiation: `i := Algebra.ofId A B`, not `AlgHom.id A A`). **Status:
sorry-free.**

### 37. `CurveRelationsDegreeBound.lean` (143 lines)
Imports: `FinrankLeOfMonicAnnihilator`.

Same sub-effort as file 36. Item 4 of the roadmap's file plan (done
before the harder linear-elimination stages, since curve relations are
already literally monic). Specializes file 36 to the shape
`X² − C f`(degree 2, matching stages 8–11's `curveA1`/`curveA2`/
`curveB1`/`curveB2`, per `DecoupledSystemRegular.lean` §3) — abstractly
over any `f : A`, not yet tied to `Rdec p`. Provides
`curveRelationPoly`/`curveRelationPoly_monic`/`_natDegree`, and the
headline `finrank_le_of_curve_relation : finrank k (AdjoinRoot
(curveRelationPoly f)) ≤ 2 * finrank k A`. Its own comments flag a
heartbeat-budget fix mid-proof (pulling a polynomial-induction `have`
out of a case split, and swapping a `coeff`-level case-split proof of
`C a * X^n = monomial n a` for the direct lemma
`C_mul_X_pow_eq_monomial`). **Status: sorry-free.**

### 38. `LinearElimDegreeBound.lean` (162 lines)
Imports: `FinrankLeOfMonicAnnihilator`.

Same sub-effort. Item 2 of the roadmap's file plan, covering stages
0–3's shape: `c − X·d`, linear but NOT monic as written (leading
coefficient `-d`). Takes `IsUnit d` (not bare `d ≠ 0`, per the roadmap's
own "Strategy" section) and rescales to the monic `X − C(d⁻¹c)` (a unit
multiple, so it generates the same ideal via
`Ideal.span_singleton_mul_left_unit`), then applies file 36's core fact
with `d_deg := 1`. Provides `linearElimPoly`/`linearElimMonicPoly` (+
monic/natDegree facts), the unit-multiple identity
`linearElimPoly_eq_unit_mul`, the ideal-equality corollary
`linearElimPoly_span_eq`, the root-transport iff
`aeval_linearElimPoly_eq_zero_iff`, and the headline
`finrank_le_of_linear_elim : finrank k B ≤ finrank k A`. **Status:
sorry-free.**

### 39. `LinearElimDegreeBoundExt.lean` (104 lines)
Imports: `LinearElimDegreeBound`.

Same sub-effort. Item 3 of the roadmap's file plan, covering stages 4–7
(`Fv0`–`Fv3`). Its own docstring notes these are LITERALLY the same
`c − X·d` shape as stages 0–3, so no new proof content is needed — file
38's `finrank_le_of_linear_elim` already covers them as-is. This file's
only content is four re-exported corollaries
(`finrank_le_of_Fv0`/`_Fv1`/`_Fv2`/`_Fv3`) under stage-facing names for
Assembly to call, each a direct application of file 38's lemma. Flags
(per the roadmap's now-resolved Open Question) that each stage's
`IsUnit (v*_den i)` hypothesis is genuinely new data Assembly must
supply — NOT already available from the existing `hv0_ext`–`hv3_ext`
(`IsSMulRegular`) hypotheses, a different-strength condition about a
different ring. **Status: sorry-free.**

### 40. `QuotOfListChain.lean` (119 lines)
Imports: none project-internal (`Mathlib` only).

Same sub-effort. Item 5 of the roadmap's file plan, Assembly part 1: the
purely ring-theoretic bridge needed to chain the abstract per-stage
`finrank` facts (files 36–39, 37) onto the literal one-step quotients
`Rdec p ⧸ Ideal.ofList (...)` — since each abstract lemma's `B` is a
generic `A`-algebra, but the real target is a ONE-STEP quotient by the
WHOLE extended generator list, not literally a quotient-of-a-quotient.
Provides `quotOfListCons_ringEquiv : (R ⧸ Ideal.ofList gens) ⧸ Ideal.span
{mk gens g} ≃+* R ⧸ Ideal.ofList (gens ++ [g])` (via
`Ideal.ofList_append` + `DoubleQuot.quotQuotEquivQuotSup` +
`Ideal.quotEquivOfEq`), and the point-tracking corollary
`quotOfListCons_ringEquiv_apply_mk_mk` (needed since the per-stage
hypotheses are about specific elements, not just an abstract ring
shape). **Status: sorry-free.**

### 41. `QuotOfListChainFinrankStep.lean` (137 lines)
Imports: `QuotOfListChain`.

Same sub-effort. Item 5, Assembly part 2: bridges file 40's ring
isomorphism to an actual `finrank` inequality on the literal one-step
quotients. Provides the GENERIC one-stage step
`finrank_le_ofList_cons`, taking an already-proved abstract-`B`
`finrank` bound (`hstep`) as a bare hypothesis and transporting it
across `quotOfListCons_ringEquiv` — upgraded to a `k`-algebra
isomorphism via `AlgEquiv.ofRingEquiv` plus an `algebraMap`-agreement
check, then `LinearEquiv.finrank_eq`. Deliberately one step at a time
rather than a whole-chain fold, since the two per-stage shapes (linear
vs. degree-2) don't share one hypothesis form. **Status: sorry-free.**

### 42. `QuotOfListChainAdjoinTop.lean` (48 lines)
Imports: none project-internal (`Mathlib` only).

Same sub-effort. Item 5, a small but load-bearing Assembly observation:
every per-stage `finrank` lemma (files 36, 38, 37) needs
`Algebra.adjoin A {t} = ⊤`, but at every real peel-chain stage `B` is
literally `A ⧸ Ideal.span {c}` — a QUOTIENT of `A`, not a genuine
extension — so `algebraMap A B` is already surjective and
`Algebra.adjoin A {t} = ⊤` holds for ANY `t`, not just a genuinely
generating one. Provides `adjoin_singleton_eq_top_of_quotient`, making
every stage's `hgen` hypothesis free at Assembly time; only each
stage's own annihilation fact `ht` needs real proof. **Status:
sorry-free.**

### 43. `CurveRelationStageWiring.lean` (183 lines)
Imports: `QuotOfListChainFinrankStep`, `QuotOfListChainAdjoinTop`,
`CurveRelationsDegreeBound`, `DecoupledSystemRegular`.

Same sub-effort. Item 5, the first concrete stage specialization
(stages 8–11): wires file 36's core lemma (applied directly, not via
file 37's `AdjoinRoot`, to avoid an extra identification step — see its
own docstring) and file 41's one-step transport to the literal shape a
curve-relation generator takes in `Rdec p`. Provides `curveFImage`,
`curveRelationGen` (`X w² − (curve expression in x)`, matching
`curveA1`'s literal shape generically over which two `Idx` symbols play
`wa1`/`a1`), and the headline
`finrank_le_curveRelation_ofList_cons`, generic over an arbitrary prefix
`gens` — NOT yet plugged into `genList`'s literal 8-element prefix.
Takes `[StrongRankCondition ...]`/`[Module.Finite (F p) ...]`/
`[Nontrivial ...]` on the prefix as explicit hypotheses, since none is
derivable for an arbitrary `gens` (left to later Assembly). **Status:
sorry-free.**

### 44. `LinearElimStageWiring.lean` (168 lines)
Imports: `QuotOfListChainFinrankStep`, `QuotOfListChainAdjoinTop`,
`LinearElimDegreeBound`, `DecoupledSystemRegular`.

Same sub-effort. Item 5, the counterpart to file 43 for stages 0–3
(and, shape-identically, 4–7). Provides `linearElimGen` (`c − X u * d`,
matching `Fu0`'s literal shape) and the headline
`finrank_le_linearElim_ofList_cons`, taking `hd_unit : IsUnit (mk_A d)`
as a fourth genuinely-needed per-stage hypothesis (matching file 39's
`hv_den_unit`) alongside the same `[StrongRankCondition]`/
`[Module.Finite]`/`[Nontrivial]` hypotheses file 43 needs. **Status:
sorry-free.**

### 45. `FinrankLeOfMonicAnnihilatorFinite.lean` (145 lines)
Imports: `FinrankLeOfMonicAnnihilator`.

Same sub-effort. Fixes a real gap the roadmap's "Open questions" section
flags as discovered while scoping Assembly: the wired per-stage lemmas
(files 43, 44) take `[Module.Finite (F p) (...)]` on the PREFIX as an
explicit hypothesis, but a naive 12-step induction's base case
(`gens = []`, i.e. `A = Rdec p` itself, a polynomial ring) is simply
false for that instance — `Module.Finite (F p) (Rdec p)` does not hold.
The fix (checked directly against file 36's actual proof, not assumed):
file 36's proof already INTERNALLY derives `Module.Finite k B` from
`Module.Finite k A`, so finiteness should be THREADED FORWARD by the
induction as an output, starting from the true base case
`Module.Finite (F p) (F p)`, rather than independently re-derived at
each prefix. Provides `finrank_le_of_monic_annihilator_of_finite` (file
36's core lemma, restated with `Module.Finite k A` as an explicit
argument and `Module.Finite k B` exported alongside the `finrank`
bound) and `nontrivial_of_span_ne_top` (the companion `Nontrivial`
fact for `B := A ⧸ Ideal.span {g}` whenever `g` is a non-unit).
Project-agnostic, no `Rdec p`/`genList` content. **Status: sorry-free.**

### 46. `PeelChainStageFinite.lean` (323 lines)
Imports: `FinrankLeOfMonicAnnihilatorFinite`, `QuotOfListChain`,
`QuotOfListChainAdjoinTop`, `CurveRelationStageWiring`,
`LinearElimStageWiring`, `DecoupledSystemRegular`.

Same sub-effort. Continuation of file 45's fix, specialized to the
literal `Rdec p ⧸ Ideal.ofList gens` one-step quotients files 43/44
already wire. Provides `finite_and_nontrivial_ofList_cons_of_two_step`
(generic transport of `Module.Finite`/`Nontrivial`/`finrank`-equality
across file 40's ring isomorphism, upgraded to a `k`-algebra
isomorphism), then the finiteness-exporting versions of files 43/44's
headline theorems:
`finrank_le_and_finite_curveRelation_ofList_cons` and
`finrank_le_and_finite_linearElim_ofList_cons`, each concluding
`Module.Finite`/`Nontrivial` on the EXTENDED quotient alongside the
`finrank` bound, so a not-yet-written Assembly induction can thread
these forward starting from the true `F p`-over-itself base case. Both
new theorems take an honest new hypothesis `hgu : ¬ IsUnit (mk_A g)`
(the generator's own non-unit-ness at its accumulated prefix, needed
for `Nontrivial` via `nontrivial_of_span_ne_top`) — its own docstring is
explicit that this is NOT automatic from the generator's non-unit-ness
in `Rdec p` alone, since quotienting can manufacture units. **Status:
sorry-free.**

### 47. `PeelChainAssemblyFinrank.lean` (130 lines)
Imports: `PeelChainStageFinite`.

Same sub-effort. Assembly part 3, per the roadmap's Progress section
("the final Assembly step ... is now actually startable"): the GENERIC
n-stage chaining primitive, `finrank_le_and_finite_of_append`, folding
an arbitrary list of generators onto a starting prefix by induction,
given a single caller-supplied per-stage proof recipe `hstep` (called
again at each new prefix the induction produces, since a stage's own
`Module.Finite`/`Nontrivial` hypotheses aren't known until the previous
stage's conclusion exists). Threads a per-generator multiplier function
`d : R → ℕ` through `Module.finrank_mul_finrank`, so the final bound's
multiplier is `(newGens.map d).prod`. Notes `StrongRankCondition` never
needs threading separately since any `Nontrivial` `CommRing` gets it for
free (`commRing_strongRankCondition`, confirmed via direct web search,
not assumed from memory). Still fully generic — NOT yet applied to
`genList`'s literal 12 generators. **Status: sorry-free.**

### 48. `OptionSplitPolynomialEquiv.lean` (164 lines)
Imports: `DecoupledSystemRegular`.

Same sub-effort. Addresses a deeper gap surfaced via ChatGPT
consultation (logged in the roadmap): the whole `Rdec p ⧸
Ideal.ofList gens`-based induction (files 43/44/46/47) has NO valid base
case for ANY prefix, since `Rdec p` is a 12-variable free polynomial
ring end-to-end — the fix is to run the finiteness/finrank induction on
a genuinely finite TOWER built one `Polynomial`-quotient at a time, and
bridge back to the literal `Ideal.ofList genList` presentation only at
the end. This file extracts, as its own reusable theorem, a ring
isomorphism `regular_of_linear_elim` (`DecoupledSystemRegular.lean`)
already builds and proves internally for a different purpose
(transporting `IsSMulRegular`): `optionSplitQuotientRingEquiv :
(MvPolynomial (Option τ) R ⧸ Ideal.ofList (gens'.map (rename some))) ≃+*
Polynomial (MvPolynomial τ R ⧸ Ideal.ofList gens')` — i.e. "the ambient
ring mod everything already eliminated, with one new variable still
free" IS `Polynomial` over "the same ring with that variable already
gone." Provides the two point-tracking corollaries
(`_apply_rename_some`, `_apply_X_none`) and the `R`-algebra upgrade
`optionSplitQuotientAlgEquiv`. Its own docstring is explicit about a
caveat it does NOT resolve: this bridge only applies along a genuinely
TRIANGULAR peel order, and `genList`'s literal order (`FuList ++
FvList ++ [curveA1,...]`) is NOT triangular (`FuList`/`FvList`'s
coefficients depend on the curve-relation variables, peeled only at
stages 8–11) — Assembly must apply this bridge along a REORDERED
sequence and separately prove `Ideal.ofList`'s `List.Perm`-invariance to
transport the bound back. **Status: sorry-free** (per its own
docstring; not itself flagged untested, unlike file 35).

### 49. (superseded — see file 55) `GenListFinrankAssembly.lean` as it
stood at the ORIGINAL time of writing this index entry: a `True :=
trivial` placeholder, `genList_finrank_assembly_placeholder`, standing in
for the not-yet-attempted final wiring, with two candidate routes
reasoned through in its docstring (twelve sequential explicit
applications vs. an `hstep` reformulated to case-split on a positional
index). **This description is stale as of files 50–55** — the file's
actual current content (same filename, since revised) is entry 55 below,
which describes what it now contains and why the placeholder became a
live `sorry` instead of getting filled in directly. Kept as its own
numbered entry (rather than deleted) only so this index's file-50-onward
numbering doesn't retroactively renumber files 1–48 above; treat entry 55
as the authoritative description of `GenListFinrankAssembly.lean` and
do not act on this entry's placeholder-era description.

### 50. `IdxEquivFin.lean` (117 lines)
Imports: `DecoupledSystemRegular`.

Same sub-effort. Step 1 of the ChatGPT-consulted correction described in
the note above `ROADMAP-monic-annihilator-degree-uniform.md`'s
"CORRECTION, later pass" section: rather than hand-rolling an `Idx ≃
Option (Option (...))` chain, reindex `Idx` through `Fin 12` and peel
via Mathlib's own `MvPolynomial.finSuccEquiv`. Provides `idxToFin`/
`finToIdx` (explicit case-matching tables, not derived from `Fintype`,
so the specific TRIANGULAR order below is guaranteed rather than left to
an unspecified `Fintype`-derived enumeration) and the packaged
`idxEquivFin : Idx ≃ Fin 12`, both directions closed by `decide`. **The
order is deliberately NOT `Idx`'s own constructor order**: curve-relation
variables (`wa1,wa2,wb1,wb2`) must be peeled before the matching-generator
variables (`U0,U1,V0,V1`), since `FuList`/`FvList`'s coefficients depend
on the curve-relation variables — peeling `U0`,etc. first would leave a
non-constant leading coefficient at the step that needs one. Chosen
order: `0↦wa1,1↦a1,2↦wa2,3↦a2,4↦wb1,5↦b1,6↦wb2,7↦b2,8↦U0,9↦U1,10↦V0,
11↦V1` — each curve variable immediately followed by its own sample
variable, matching `genList`'s own stated tail order for the four curve
relations. Also provides twelve `@[simp]` point lemmas
(`idxEquivFin_wa1`, etc.), each `rfl`. **Status: sorry-free.**

### 51. `FinSuccSplitPolynomialEquiv.lean` (170 lines)
Imports: `DecoupledSystemRegular`.

Same sub-effort. Step 2 of the correction: the `Ideal.ofList`/generator-
list-carrying analogue of Mathlib's `MvPolynomial.finSuccEquiv`, exactly
mirroring file 48 (`OptionSplitPolynomialEquiv.lean`)'s statement and
proof skeleton (`Ideal.quotientEquiv` + `Ideal.map_ofList` +
`polynomialQuotientEquivQuotientPolynomial`) but with `Fin (n+1)`/
`Fin.succ` in place of `Option τ`/`some`, so later Assembly never needs
to construct or reason about an `Option`-nested type at all. Fixes the
base ring to a field `K` (unlike file 48's general `CommRing R`), since
this project only ever instantiates it at `K = F p` and `Module.finrank`/
`Module.Finite` need a field to make sense of directly. Provides
`finSuccEquiv_comp_rename_succ_eq_C`/`finSuccEquiv_rename_succ_apply`
(the key computation, proved via `MvPolynomial.ringHom_ext` rather than a
hand-rolled `induction_on` — deliberately, since a first attempt guessed
Lean-3-flavored case names, `h_C`/`h_add`/`h_X`, that don't match Lean
4's actual `C`/`add`/`mul_X`, caught and corrected before presenting),
`finSuccSplitQuotientRingEquiv` (the ring isomorphism itself),
`finSuccSplitQuotientRingEquiv_apply_rename_succ`/`_apply_X_zero` (point-
tracking corollaries), and the `K`-algebra upgrade
`finSuccSplitQuotientAlgEquiv`. **Status: sorry-free.**

### 52. `FinSuccPeelChainFinrank.lean` (311 lines)
Imports: `FinSuccSplitPolynomialEquiv`, `FinrankLeOfMonicAnnihilatorFinite`,
`QuotOfListChain`.

Same sub-effort. Item (b) of the roadmap's revised file plan: the
ONE-STAGE `Fin`-indexed peel, composing three already-proved facts (no
new core mathematical content, per its own docstring) — (1)
`finSuccSplitQuotientAlgEquiv`, restricted one level further via
`Ideal.quotientEquiv`, identifies the literal two-step quotient
`(MvPolynomial (Fin (n+1)) K ⧸ Ideal.ofList gens') ⧸ Ideal.span {mk g}`
with `Polynomial A ⧸ Ideal.span {G}` as `K`-algebras; (2)
`finrank_le_of_monic_annihilator_of_finite` (file 45) bounds `finrank` on
that two-step ring; (3) `quotOfListCons_ringEquiv` (file 40) identifies
the two-step quotient with the literal ONE-STEP quotient the caller
actually wants. Provides the headline
`finrank_le_and_finite_finSucc_peel`, concluding `Module.Finite`/
`Nontrivial`/the `finrank` bound on `MvPolynomial (Fin (n+1)) K ⧸
Ideal.ofList (gens.map (rename Fin.succ) ++ [g])`, given the new
generator's monic image `G` under the split (pinned by an explicit
hypothesis `hg`) and its non-unit-ness (`hg_ne`). Fully generic over
`n`/`K`/`gens`/`g` — zero `Idx`/`Rdec p`/`theData` content. Needed a
raised heartbeat limit (`set_option maxHeartbeats 2000000`), flagged
in-file. **Status: sorry-free.**

### 53. `FinSuccPeelChainFold.lean` (124 lines)
Imports: `FinSuccPeelChainFinrank`.

Same sub-effort. Item (c) of the roadmap's revised file plan and the
actual fix for the base-case gap file 55 (formerly file 49's stub)
exposed: the GENERIC `n`-stage fold, mirroring file 47's
`finrank_le_and_finite_of_append` in interface shape (a single
dependently-typed `hstep` proof recipe, callable again at whatever stage
the induction has reached, since each stage's own witness data is only
determined once the induction gets there) but with a GENUINE `n = 0`
base case built in rather than assumed: `MvPolynomial (Fin 0) K ≃ₐ[K] K`
(`MvPolynomial.isEmptyAlgEquiv`, since `Fin 0` is empty) really is
`K`-finite, unlike file 47's `Rdec p`-prefix base case, which is provably
false for `gens = []`. `hstep` is stated to return a witness bundle
(`g`,`G`, proofs) EXISTENTIALLY, since the generic fold has no fixed
formula for the per-stage generator at this level of genericity — the
headline `finrank_le_finSucc_peel_chain` therefore concludes an
EXISTENTIAL `∃ gensN bound, ...` rather than a bound on a caller-specified
list. **Load-bearing caveat for file 55's wiring, confirmed by direct
ChatGPT consult (see `ZeroD-README.md`/this project's working chat log
for the full exchange)**: this existential shape cannot, by itself, be
used to recover a bound on any SPECIFIC list like `genList` — the
induction existentially forgets every choice it makes along the way, so
file 55's actual closing proof needs either a non-existential 12-step
direct unfolding (calling file 52's one-stage lemma twelve times
explicitly against `genList`'s literal generators) or a strengthened
fold that threads the generator list through as data; this file supplies
only the existential version, useful as a generic reusability statement
but NOT the form file 55 ends up calling directly. Fully generic — zero
`Idx`/`Rdec p`/`theData` content. **Status: sorry-free.**

### 54. `IdealOfListPerm.lean` (97 lines)
Imports: none project-internal (`Mathlib` only — fully generic).

Same sub-effort (infrastructure needed by the base-case correction, files
50–53/55, though the fact itself is stated with no `Genus2Lean`-specific
content). Proves `Ideal.ofList` only depends on a list's underlying
elements, not its order: `Ideal.ofList_perm {l₁ l₂ : List R} (h :
l₁.Perm l₂) : Ideal.ofList l₁ = Ideal.ofList l₂`, plus the quotient-ring
corollary `Ideal.quotient_ofList_perm_eq`. **Load-bearing for file 55's
wiring**: `genList`'s literal stated order (`FuList ++ FvList ++
[curveA1,...]`) is NOT the triangular peel order `idxEquivFin` (file 50)
induces, so closing file 55's `sorry` needs exactly this fact to
transport a bound proved against the triangular reordering back onto
`Ideal.ofList genList` in its own stated order. Proof deliberately avoids
`unfold`ing `Ideal.ofList`'s raw definition (not independently
re-confirmed via direct source inspection this pass, only its public
API) — proceeds instead by structural induction on `List.Perm`'s four
constructors (`nil`/`cons`/`swap`/`trans`), using only already-confirmed
project-trusted lemmas (`Ideal.ofList_nil`, `Ideal.ofList_cons`) plus
`sup_assoc`/`sup_left_comm` for the `swap` case. **Status: sorry-free.**
(Numbered after files 50–53 despite being logically closer to a
generic-infrastructure file like 40/42 — placed here rather than
earlier since it was written in the same later pass as the arity-peel
correction and is only actually needed once that correction's wiring,
file 55, is attempted.)

### 55. `GenListFinrankAssembly.lean` (310 lines, current — supersedes
entry 49's description) — ⚠ current live `sorry`, next step
Imports: `PeelChainAssemblyFinrank`, `PeelChainStageFinite`.

Same sub-effort. Assembly part 4, **now on its post-correction revision**:
entry 49 described an earlier state of this same file (a `True :=
trivial` placeholder, `genList_finrank_assembly_placeholder`). That
placeholder has since been superseded by an actual attempt at the
specialization, written against the twelve literal `Ideal.ofList`-prefix
generators directly (route (a) from entry 49's docstring: twelve
separately-named fields — `hd_unit_Fu0`,...,`hgu_curveB2` — rather than
an indexed `List.take`/`getD` lookup, sidestepping the associativity-
unification risk entry 49 flagged as unchecked). Provides
`PeelChainFinrankHyp` (the twelve-field bundle, generic over
`d : DecoupledGenerators p` and `c0,...,c4 : F p`, deliberately not tied
to `theData` internally — same `whnf` heartbeat-timeout reasoning entry
49 already recorded) and the headline `genList_finrank_le`, which states
the actual target — `Module.finrank (F p) (Rdec p ⧸ Ideal.ofList
(genList ...)) ≤ 16` — but **ends in a live `sorry`, not a placeholder**:
its own docstring is explicit that the twelve-sequential-application
proof sketch it describes cannot actually start, because the base case
(`Module.Finite (F p) (Rdec p ⧸ Ideal.ofList [])`, i.e. `Module.Finite
(F p) (Rdec p)`) is FALSE — `Rdec p` is a 12-variable polynomial ring,
infinite-dimensional over `F p`. This is the exact gap files 50–54 exist
to fix (peel by ARITY via `finSuccEquiv`, not by `Ideal.ofList` prefix),
but as of this pass that fix has not yet been wired THROUGH this
specific theorem. **This is the one live `sorry` anywhere in this whole
54-file index, and the one live `sorry` anywhere under `ZeroD/` per this
pass's fresh whole-project scan** (superseding `ZeroD-STATUS.md`'s own
"zero sorries under `ZeroD/`" claim, which predates this file's
placeholder-to-`sorry` transition). **Closing it needs**: either (i) a
non-existential 12-step direct unfolding calling file 52's one-stage
lemma explicitly against `genList`'s twelve literal generators in
`idxEquivFin`'s triangular order (not `genList`'s own stated order), or
(ii) file 53's existential fold instantiated some other way — see this
project's working chat log for a ChatGPT-consulted architecture
(`explicit 12-step peeling → List.Perm → Ideal.ofList_perm (file 54) →
Ideal.map_ofList + Ideal.quotientEquiv → LinearEquiv.finrank_eq`) that
recommends (i), plus a reusable rename-transport lemma
(`finrank_ofList_le_of_finrank_ofList_map_rename_le`, not yet written as
its own file) bridging the `MvPolynomial (Fin 12) K`-side bound back to
`Rdec p`/`Idx` via `MvPolynomial.renameEquiv`. **This is the file (and
gap) to pick up next.**

---

### 56. `FinSuccPeelChainFinrank.lean` (311 lines)
Imports: `FinSuccSplitPolynomialEquiv`, `FinrankLeOfMonicAnnihilatorFinite`,
`QuotOfListChain`.

Item (c)'s fix for entry 55's actual obstruction: induct on the ambient
ring's ARITY (`Fin n → Fin (n+1)` via `MvPolynomial.finSuccEquiv`), not on
`Ideal.ofList` prefixes of a fixed-arity ring — the latter never reaches a
genuine base case, since even the empty prefix of `Rdec p` is still
infinite-dimensional. At `n = 0`, `MvPolynomial (Fin 0) K ≃ₐ[K] K`
(`Fin 0` empty) is genuinely finite, giving the real base case this
project needed. Supplies the ONE-STAGE peel lemma only, fully generic
over `n`/`K`/`gens`, zero `Idx` content. `sorry` mentions are docstring
prose only (referencing entry 55's live sorry), not live in this file.

### 57. `FinSuccPeelChainFold.lean` (124 lines)
Imports: `FinSuccPeelChainFinrank`.

The n-stage fold of entry 56's one-stage lemma, starting the induction at
the genuine `n = 0`/`gens = []` base case. `hstep` here is a single
dependently-typed proof recipe (quantified over an arbitrary
already-reached stage `i` and prefix), not a fixed shape repeated `n`
times, mirroring `PeelChainAssemblyFinrank.lean`'s `hstep` shape one level
more dependent. `sorry` mention is docstring prose only.

### 58. `RenameEquivOfListFinrankTransport.lean` (169 lines)
Imports: none beyond `Mathlib`.

The transport lemma bridging a `finrank` bound proved in
`MvPolynomial (Fin 12) K` (via entries 56–57's peel over `idxEquivFin`)
back onto the literal `Rdec p ⧸ Ideal.ofList genList` statement in
`MvPolynomial Idx K`. Built from `Ideal.map_ofList` +
`Ideal.quotientEquiv` composed once, using `MvPolynomial.renameEquiv`
re-derived as a plain `RingEquiv` (`renameRingEquiv`) since the
ideal/quotient machinery wants `≃+*` not `≃ₐ[K]`. Fully generic over an
arbitrary variable-set equivalence `e : σ ≃ τ` — no `Idx`/`Rdec p`/
`theData` content, reusable for any future `MvPolynomial`-reindexing
transport.

### 59. `GenListTriangularReorder.lean` (139 lines)
Imports: `DecoupledSystemRegular`, `IdxEquivFin`, `IdealOfListPerm`,
`CurveRelationStageWiring`, `LinearElimStageWiring`.

Item (d) steps 1–2: reorders `genList`'s literal stated order
(`FuList ++ FvList ++` curve relations) into `genListTriangular`
(curve relations FIRST, `Fu`/`Fv` after) — the order `idxEquivFin`'s peel
actually needs, since `Fu`/`Fv`'s coefficients are only guaranteed
constant in `U0,U1,V0,V1`, not in the curve-relation variables
`wa1,wa2,wb1,wb2,a1,a2,b1,b2`; peeling a matching generator before its
curve variables are eliminated would leave a non-constant "leading
coefficient" where `finSuccEquiv`'s monic-annihilator machinery needs an
actual constant. Proves the reorder is ideal-preserving via
`Ideal.ofList_perm`. Does not yet touch step 3 (`hstep` itself) or step 4
(final assembly).

### 60. `FinSuccStageGenerators.lean` (256 lines)
Imports: `FinSuccSplitPolynomialEquiv`, `LinearElimDegreeBound`,
`CurveRelationsDegreeBound`.

Item (d) step 3, generic half: for each of the 12 peel-chain stages,
supplies a `Fin`-indexed generator and its `finSuccSplitQuotientAlgEquiv`
image, covering both stage shapes the roadmap's peel-chain table
identifies — linear-elimination stages 0–7 (`finSuccLinearElimGen q1 q2
:= rename Fin.succ q1 - X 0 * rename Fin.succ q2`, image exactly
`linearElimPoly (mk q1) (mk q2)`) and curve-relation stages 8–11. Zero
`Idx`/`Rdec p`/`theData` content — the actual `Idx`-specific wiring
(identifying these with `genList`'s literal `u1_num`/`u1_den`/`curveF`
etc.) is separate, later work (see entry 61).

### 61. `IdxCurveStage0Wiring.lean` (90 lines) — documents a gap, no live sorry
Imports: `FinSuccStageGenerators`, `IdxEquivFin`, `GenListTriangularReorder`.

Item (d)'s true remainder: the `Idx`-specific `hstep` specialization,
attempted for exactly ONE stage (stage 0 of the triangular order,
`curveA1`, also `n = 0`) as a deliberately small first step rather than
committing to all twelve at once. **Finds a genuine architectural gap**,
recorded (not worked around): `curveA1 = X wa1^2 - f(X a1)` is a relation
in TWO `Idx` variables (`wa1` and `a1`), neither separately peeled by any
other generator, so it does not fit `finSuccCurveRelationGen`'s one-new-
variable-at-a-time shape at `n = 0`. This is exactly the finding
`CurveRelationChainFinrank.lean` (entry 65) supersedes — see that entry
and `ROADMAP-monic-annihilator-degree-uniform.md`'s "What's actually
true" correction for why the literal-`Ideal.ofList`-prefix approach
(entry 46) sidesteps this obstruction entirely, making entries 56–61's
`Fin`-arity architecture unnecessary for the curve-relation stages
specifically (it may still be relevant for the linear-elimination
stages, unresolved as of this pass).

### 62. `SharedPivotResultantElim.lean` (186 lines)
Imports: `LinearElimDegreeBound`, `FinrankLeOfMonicAnnihilatorFinite`.

The roadmap's shared-pivot correction's key missing piece: bounds
`finrank` for a ring extended by ONE new variable `X` subject to TWO
simultaneous linear relations `n1 - X*d1`/`n2 - X*d2` (exactly `U0`'s
`Fu0`/`Fu1` shape, etc.), in terms of `finrank` of the SAME base ring
further quotiented by the classical resultant `n1*d2 - n2*d1` alone — no
`X` involved. The ideal/finrank-level upgrade of
`MvPolynomialSharedTargetSolve.lean`'s point-existence finding that two
such relations are simultaneously satisfiable exactly where their
resultant vanishes.

### 63. `SharedPivotStageWiring.lean` (383 lines)
Imports: `QuotOfListChainFinrankStep`, `QuotOfListChainAdjoinTop`,
`SharedPivotResultantElim`, `LinearElimStageWiring`,
`FinrankLeOfSpanSurjective`.

Wires entry 62's abstract resultant bound to the literal `Ideal.ofList`
two-generator extension `gens ++ [g1, g2]` — the shape `FuList`/`FvList`'s
pairs actually take in `genList` — by composing
`finrank_le_ofList_cons` (entry 41) with itself once. Generic over the
prefix, the peeled symbol `u : Idx`, and the four coefficients
`n1 d1 n2 d2 : Rdec p` — not yet specialized to which of `U0/U1/V0/V1`
this is or to `theData`'s actual values.

### 64. `FinrankLeOfSpanSurjective.lean` (165 lines)
Imports: none beyond `Mathlib`.

Small standalone lemma the shared-pivot wiring needs: if `f : A →ₐ[k] A1`
is a surjective `k`-algebra map and `r : A`, then
`finrank k (A1 ⧸ span {f r}) ≤ finrank k (A ⧸ span {r})` — needed because
entry 62's bound is naturally stated over an earlier prefix ring `A0`,
but the literal peel chain's next stage needs it transported across the
surjection `A0 ↠ A`. Also exports the `Module.Finite`-transport analogue
(`finite_of_span_surjective`), used by entry 67.

### 65. `CurveRelationChainFinrank.lean` (288 lines)
Imports: `PeelChainStageFinite`, `DecoupledSystemRegular`.

**Resolves entry 61's gap by taking a different architecture, not by
patching it.** Supplies the four-stage `curveA1,curveA2,curveB1,curveB2`
chain directly over the literal `Ideal.ofList` prefix presentation
(entry 46's `finrank_le_and_finite_curveRelation_ofList_cons`), which
never needed a curve relation's sample-point variable to be pre-peeled by
any earlier stage — it evaluates `X x` symbolically in whatever ring the
prefix quotient already is. So `curveA1`'s "two new variables at once"
shape, which broke the `Fin`-arity approach (entry 61), is simply not an
obstruction here — the difficulty was specific to the superseded
`finSuccEquiv`-based architecture (entries 56–61), not to the underlying
mathematics. Generic over the starting prefix; not yet specialized to
`gens = FuList ++ FvList` (pending entry 63's own instantiation against
`theData`).

### 66. `SharedPivotStageWiringFinite.lean` (292 lines)
Imports: `QuotOfListChainFinrankStep`, `QuotOfListChainAdjoinTop`,
`SharedPivotResultantElim`, `SharedPivotResultantElimFinite`,
`SharedPivotStageWiring`, `LinearElimStageWiring`,
`FinrankLeOfSpanSurjective`.

The `Module.Finite`/`Nontrivial`-exporting sibling of entry 63, needed so
the eventual four-stage `U0,U1,V0,V1` resultant elimination can hand
finiteness forward to the next stage (or to entry 65's curve chain,
which needs it as an explicit hypothesis on its starting prefix) — a
`finrank` bound alone doesn't supply that, same gap `PeelChainStageFinite
.lean` (entry 46) already diagnosed and fixed for the single-generator
case.

### 67. `SharedPivotResultantElimFinite.lean` (148 lines)
Imports: `SharedPivotResultantElim`.

The `Module.Finite`-exporting sibling of entry 62 itself (one level below
entry 66): re-derives entry 62's proof to additionally export
`Module.Finite k B` via the same surjective `k`-linear map
`ψₗ : (A ⧸ span {resultant}) →ₗ[k] B` its `finrank` bound already builds,
using `Module.Finite.of_surjective` — the same transport
`FinrankLeOfSpanSurjective.lean`'s `hfin` step uses for the one-hop
version.

### 68. `MatchingEquationTranslation.lean` (145 lines) — separate
`matching-equation` sub-effort, not part of the `totalDegree` chain above
Imports: `DivisorClassGroup`.

Two standalone `AddCommGroup` facts about the matching equation
`[P1]+[P2]-[P3]-[P4] = (alpha-alpha')•a` in `Jacobian H D`, with no
curve-specific or Mumford-coordinate content. Proves
`matching_solutions_translate_by_delta`: any two solutions of the same
matching equation are related by a single common `Δ` translating both
sides simultaneously (`Δ := (P1+P2)-(P1'+P2')`). Explicit about what it
does NOT prove: that the solution set for a fixed `(alpha,alpha')` is a
single point — that is asserted in `ROADMAP-alpha-locus.md` from
reasoning done outside Lean, flagged there as "not yet formalized." Was
building-red as of this pass (see the Fix note below); now green.

### 69. `OrbitMapConstant.lean` (120 lines) — same sub-effort as entry 68
Imports: `Mathlib` only — deliberately no `DivisorClassGroup` import,
since it never names `Jacobian`/`PrincipalDivisorData` directly (see the
Fix note below for why that matters).

The general-topology core of entry 68's "actual rigidity mechanism"
update: proves `orbit_map_constant_of_preconnected_of_discrete` (a
continuous map from a preconnected space to a discrete space is
constant, via genuine current-Mathlib4 `PreconnectedSpace.constant`) and
composes it with an explicit `Faithful`-style hypothesis
(`delta_eq_zero_of_orbit_constant_and_faithful`) to conclude `Δ = 0`.
Explicit about what it does NOT attempt: giving `Jacobian H D` an actual
`TopologicalSpace` instance, let alone proving it `PreconnectedSpace` —
this project has zero uses of `TopologicalSpace`/`Scheme`/`PrimeSpectrum`
anywhere, and current Mathlib4 has no Jacobian-of-a-curve machinery to
build on. Both theorems therefore take `PreconnectedSpace`/
`DiscreteTopology`/faithfulness as explicit hypotheses on abstract
`J`/`S`, not yet instantiated against `Jacobian H D` itself.

### Fix, this pass: `MatchingEquationTranslation.lean` (entry 68 above)
was building-red as of this pass's `lake build`, fixed here. Root cause:
the file wrapped its content in `namespace Genus2Lean` then `namespace
HyperellipticPolynomial`, but `Jacobian`/`PrincipalDivisorData`
(`DivisorClassGroup.lean`) live in a TOP-LEVEL `namespace
HyperellipticPolynomial`, not inside `Genus2Lean` — so the file's own
`namespace HyperellipticPolynomial` declaration created a distinct,
empty `Genus2Lean.HyperellipticPolynomial` namespace that could not see
those definitions, producing "unknown identifier" errors at every use.
`AlphaLocusDegreeUniform.lean` already documents this exact namespace
shape in its own comment (just above its `open HyperellipticPolynomial`
line) and uses the correct pattern: `open HyperellipticPolynomial` at
top level, THEN enter `namespace Genus2Lean` under a different inner
namespace name. Fixed by following that pattern exactly (`open
HyperellipticPolynomial` before `namespace Genus2Lean`, inner namespace
renamed to `HyperellipticPolynomialMatching` to avoid re-shadowing) — no
downstream file referenced the old fully-qualified name
(`Genus2Lean.HyperellipticPolynomial.matching_solutions_translate_by_delta`),
so nothing else needed updating. The proof body itself (pure
`AddCommGroup`/`abel` algebra) was already correct; the `abel_nf made no
progress` error the build log also showed was a downstream symptom of
the same unresolved-identifier cascade, not a separate bug.
`OrbitMapConstant.lean` (entry 69) was unaffected — it never names
`Jacobian`/`PrincipalDivisorData`, only abstract `J`/`S`, so the same
namespace mistake had nothing to break there.

### 70. `MatchingEquationDeltaInvariance.lean` (new, this session) — same
`matching-equation` sub-effort as entries 68–69
Imports: `DivisorClassGroup`.

Formalizes "Lemma 0" from this session's GPT consult (a genuinely new
fact, not previously in this codebase, distinct from entry 68's own
`matching_solutions_translate_by_delta`): the matching equation
`P1+P2-P3-P4 = (alpha-alpha') • a` depends on `(alpha,alpha')` only
through `delta := alpha - alpha'` — two pairs sharing the same `delta`
define the literal same equation (`matching_target_eq_of_sub_eq`,
`ring`/`zsmul`-level, not an isomorphism claim) and hence the literal
same solution set (`solution_set_eq_of_sub_eq`, `Set` equality). Also
proves the auxiliary "`D`-coordinate" gauge-shift fact
(`dcoord_shift`: `P1+P2-(alpha+beta)•a = (P1+P2-alpha•a)-beta•a`) the
writeup uses to describe common `(alpha,alpha')`-shifts as moving only
the auxiliary coordinate, not the `Pᵢ` themselves. States its own
caveat explicitly, reproduced from the GPT writeup rather than dropped:
`alpha • a` for `alpha : ℤ` only sweeps out `AddSubgroup.zmultiples a`
as `alpha` varies, not all of `Jacobian H D` — so this file's results do
NOT by themselves justify constructing `G(Δ)` for an arbitrary
`Δ ∈ Jacobian H D` (needed for the full rigidity argument via entry 69);
that remains a separate fact about the `Reduce`/Mumford construction,
not attempted here or anywhere else in this project yet.

### 71. `GenListFinrankResultantAssembly.lean` (329 lines)
Imports: `CurveRelationChainFinrank`, `SharedPivotStageWiringFinite`,
`GenListTriangularReorder`, `GenListFinrankAssembly`.

**The file entries 63/66 named as not-yet-existing — now written, and now
the correct entry point for "does `GenListFinrankResultantAssembly.lean`
exist" instead of the stale "no" this index gave at the bottom of this
document before this pass.** Chains entry 65's four-stage curve-relation
chain with entry 66's shared-pivot machinery, over `genListTriangular`
(curves first, matching generators second — order is load-bearing, not
stylistic: `FuList`/`FvList`'s coefficients are only guaranteed constant
once the curve variables are already eliminated). Proves
`genList_triangular_finrank_le`, a real bound GIVEN the starting (empty)
prefix is already `Module.Finite` — supplied honestly, not smuggled in,
since `Module.Finite (F p) (F p)` (rank 1) is the genuinely-true base case
(no longer `base_prefix_finite_sorry`, an earlier false placeholder this
file's own docstring flags as corrected this pass).

**Read the gap this file leaves before treating it as "genList_finrank_le,
closed" — it is not, quite.** Its own module docstring calls out only
applying the shared-pivot stage ONCE (for `U0`), not all four
(`U0,U1,V0,V1`) its docstring otherwise describes — entry 78 below is
what actually closes that. Also not done here: the final mechanical
transport of the bound from `genListTriangular`'s reordered presentation
back onto `genList`'s own literal stated order
(`quot_genListTriangular_eq_quot_genList`, one `rw`, explicitly left for
"whoever calls this file against `genList_finrank_le` itself"). Sorry-free
throughout (checked directly, comment-stripped).

### 72. `PeelChainPairwiseAgreement.lean` (221 lines)
Imports: `LinearElimDegreeBound`, `CurveRelationsDegreeBound`.

**Starts the "pairwise agreement" line — the roadmap's corrected
replacement for the abandoned orbit-map/connectedness route to `Δ = 0`**
(see `ROADMAP-monic-annihilator-degree-uniform.md`'s "actual remaining
blocker" section; entries 68/69's connectedness machinery is NOT reused
here, per that roadmap's own explicit correction). A genuinely smaller
claim than the `finrank` bound: two abstract copies of the same base ring
`A` (not an extended `B`), asking whether two elements `t t' : A`
satisfying the same relation must be equal, not how big the extension is.
Linear stages (`d=1`): unconditional — `t`'s value is literally forced to
`d⁻¹·c` (`linearElim_forces_eq`/`linearElim_pairwise_eq`, pulled out of
entry 62's own inline computation as a reusable lemma, that file's proof
untouched). Curve stages (`d=2`): needs an explicit side condition —
`curveRelation_sq_sub_sq_eq_zero` gives `(t-t')(t+t')=0` unconditionally,
closed to `t=t'` only via a stated `t ≠ -t'` hypothesis
(`curveRelation_forces_eq`, `IsDomain B` needed for the two-branch split).
Sorry-free.

### 73. `PeelChainPairwiseAgreementWiring.lean` (185 lines)
Imports: `PeelChainPairwiseAgreement`, `CurveRelationStageWiring`,
`LinearElimStageWiring`, `DecoupledSystemRegular`.

Specializes entry 72's abstract facts against `genList`'s literal
`linearElimGen`/`curveRelationGen` shapes (entries 43/44's own
conventions). **Records a genuinely negative finding, checked directly
against `curveA1`'s literal definition and `SampleTarget`'s field list,
not assumed**: there is NO sign convention anywhere in `theData`'s
symbolic algebra pinning `wa1`/`wa2`/`wb1`/`wb2` to one square root over
the other — `wa1` and `-wa1` are genuinely interchangeable in `Rdec p`'s
free-polynomial presentation. So the curve-relation `t ≠ -t'` hypothesis
from entry 72 is stated explicitly at each of the four call sites here,
not derived. Also settles — negatively — the once-open "16 sign patterns"
framing: `[P]+[ι(P)]=0` in `J` always (Mumford, *Tata Lectures on Theta
II* ch. IIIa §1), so flipping a subset of the four points changes the
matching equation by `-2·Σ ε_i[P_i]`, zero only under a genuine 2-torsion
condition — most of the naive 16 patterns do NOT satisfy the matching
equation in general, so treat every "up to sign" theorem in this file and
its downstream users (entries 74/76) as fiber-level content only, not
`Δ = 0` content, without a separate non-degeneracy input. Linear-stage
wiring (`linearElim_ofList_pairwise_eq`) has no such gap — unconditional.
Sorry-free.

### 74. `PeelChainPairwiseAgreementLinearChain.lean` (107 lines)
Imports: `PeelChainPairwiseAgreementWiring`, `DecoupledSystemRegular`.

The eight matching-generator stages (`Fu0`–`Fu3`,`Fv0`–`Fv3`), chained.
**Shared-pivot structure again** (`U0` pivoted by both `Fu0` and `Fu1`,
etc. — same shape entries 62/66's `finrank` treatment has), but pairwise
agreement is strictly cheaper here than the `finrank` bound: it needs
only ONE of each pivot's two generators (whichever has a supplied
`IsUnit` denominator), not both-via-resultant. This file's fixed
convention: uses the FIRST generator of each shared pair (`Fu0` for `U0`,
`Fu2` for `U1`, `Fv0` for `V0`, `Fv2` for `V1`) — a caller with only the
second generator's hypothesis should call entry 73's
`linearElim_ofList_pairwise_eq` directly instead. Sorry-free.

### 75. `PeelChainPairwiseAgreementCurveChain.lean` (101 lines)
Imports: `PeelChainPairwiseAgreementWiring`, `CurveRelationChainFinrank`,
`DecoupledSystemRegular`.

The four curve-relation stages, agreement-up-to-sign form, mirroring
entry 65's `finrank_le_and_finite_curveRelationGenChain` in shape and
stage order — but, unlike that theorem's genuinely sequential four
stages (each over the PREVIOUS stage's extended ring), all four `t_i,t_i'`
pairs here live in the SAME base ring `A` from the start, so the four
per-stage facts are independent: no `obtain`/`haveI` instance-threading
between stages, just four applications of
`curveRelation_forces_eq_up_to_sign` packaged into one conjunction.
Sorry-free.

### 76. `GenListPairwiseAgreementAssembly.lean` (150 lines)
Imports: `PeelChainPairwiseAgreementCurveChain`,
`PeelChainPairwiseAgreementLinearChain`, `GenListTriangularReorder`.

**Closes the roadmap's "Next concrete steps" item 2** — chains entries
74/75 into one statement about two candidate solutions of all twelve of
`genList`'s generators. Order: curves first, matching generators second,
same reason as entry 71 (`FuList`/`FvList`'s coefficients aren't constant
until the curve variables are eliminated) and the same
`genListTriangular` presentation entry 71 uses. Unlike the `finrank`
assembly, needs no stage-by-stage ring extension — pairwise agreement is
a claim about two elements of the SAME fixed quotient at every stage, so
all eight facts (four up-to-sign, four exact) combine in one flat
conjunction over one shared prefix. Concludes: `(t1=t1' ∨ t1=-t1') ∧ ...`
(curve `w`-values, up to sign) `∧ (U0v=U0v' ∧ U1v=U1v' ∧ V0v=V0v' ∧
V1v=V1v')` (matching-generator values, exact) — note `a1,a2,b1,b2` never
appear as a conclusion here, matching the roadmap's own observation that
these four are coefficients only, never a pivot. **Does not yet address**
the roadmap's own still-open (i)/(ii) fork (route (ii): keep the ≤16
bound, defer sharpening 16→1) or the `SampleTargetFromAlpha` linkage
(roadmap "Next concrete steps" item 3) — this file closes item 2 only.
Sorry-free.

### 77. `SharedPivotFourStageFinrank.lean` (423 lines)
Imports: `SharedPivotStageWiringFinite`.

**Fixes a real gap discovered in entry 71, not merely documented by it**:
entry 71's `genList_triangular_finrank_le_of_base` calls the shared-pivot
stage lemma exactly ONCE (for `U0`) despite its own module docstring
describing all four shared-pivot stages (`U0,U1,V0,V1`). This file
supplies the missing three (`U1,V0,V1`), generic over an arbitrary
already-`Module.Finite`/`Nontrivial` starting prefix (composes with
entry 71's `U0`-stage output, but nothing here is specific to
curve-extended prefixes). One wrapper theorem rather than three separate
ones, since each stage's hypotheses must be stated against the previous
stage's already-extended (syntactically nested, genuinely large) prefix
type — accepted honestly here via `obtain`/`haveI` chaining rather than
hidden. Sorry-free.

### 78. `GenListFinrankFourStageAssembly.lean` (744 lines)
Imports: `GenListFinrankResultantAssembly`, `SharedPivotFourStageFinrank`.

**The file that actually closes the four-shared-pivot-stage gap entry 71
left open** — chains entry 71's curve-then-`U0` output prefix into entry
77's `U1,V0,V1` stages. Pure composition, both halves used as black
boxes via `obtain`; the only new content is the final `finrank` bound via
`le_trans`/`Nat.mul_le_mul` (the second stage's bound genuinely depends on
the first stage's witness ring — the two `∃`s combine by instantiation,
not by multiplying two independent naturals). **Still not done, per its
own docstring, and the one remaining item before `genList_finrank_le`
itself can cite this file**: the `genListTriangular` → `genList` order
transport (entry 71's `quot_genListTriangular_eq_quot_genList`,
mechanical, not yet invoked here either). Sorry-free. As of this pass,
this file — not entry 71 — is the true terminus of the `finrank` numeric
chain (route 3's "Core reusable fact" list should be read as entries
36/45/62/65/66/71/77/78 together, not entry 71 alone).

### 79. `StabOfSmallSetTrivial.lean` (194 lines)
Imports: none from this project (pure `Mathlib`).

**A separate sub-effort from the `totalDegree`/`finrank` chain above —
the `Δ = 0` group-theory argument for `ROADMAP-alpha-locus.md`'s "Newest
status update" section.** Deliberately has zero dependency on this
project's curve/Jacobian machinery: proves the abstract fact that if `a`
has prime additive order `ell`, `Δ` is a multiple of `a`, and `Δ`
translation-stabilizes a finite nonempty set `S` with `S.ncard < ell`,
then `Δ = 0` (`delta_eq_zero_of_stabilizes_small_set`). Proof: `ell •
Δ = 0` forces `addOrderOf Δ ∈ {1, ell}`; if `Δ ≠ 0` then `addOrderOf Δ =
ell`, giving `ell` pairwise-distinct elements `s₀ + k•Δ` (`k : Fin ell`)
all in `S` (via `orbit_injective_of_addOrderOf_eq`/`orbit_mem_of_stable`),
contradicting `S.ncard < ell`. Third-pass file per its own status note
(two Mathlib4-naming/`rw`-unification fixes: `Set.ncard_le_of_subset` →
`Set.ncard_le_ncard`; a brittle `rw` on a double-cast `Fin ell` term
replaced with `simp only [natCast_zsmul]`). Whether `P1,P2,P3,P4 ∈ ⟨a⟩`
actually holds for this project's real setup is explicitly left open —
this file proves only the unconditional group theory. **Status:
sorry-free.**

### 80. `MatchingSolutionSwapSymmetry.lean` (290 lines)
Imports: `DivisorClassGroup`, `RiemannRochGenus2`,
`LPairFinrankOneOrdAtFracSpec`.

**Corrected, this pass, per ChatGPT consult, from a previous version that
tried to bound the wrong set.** The earlier draft attempted a
difference-only solution set (`s P1 + s P2 - s P3 - s P4 = target`),
which is NOT `p`-independently bounded (the pair-sum class can range over
infinitely many values with only their difference pinned) — its two
`sorry`s were symptoms of a false statement, not a technique gap. Fixed
by pinning BOTH pair-sums separately to fixed classes `A B : Jacobian H
D` (`FixedTargetSolutions`): `IsOnlyEffectiveInClass` now applies
directly to each fixed-class condition independently, giving
`fixedTargetSolutions_ncard_le_four`: at most 4 elements, unconditional
in `p`, no `Bad`/exceptional set. Standing hypothesis carried, not
discharged: `hbridge : D.P ≤ principalSubgroup H hdeg` (the
`IsOnlyEffectiveInClass`/`s_add_s_eq_s_add_s_iff` bridge direction).
`swapImages`/`swapImages_ncard_le`/`pairFiber_ncard_le_two` are reused
unchanged from the pre-correction version (already correct, sorry-free).
**Status: sorry-free** (the two `sorry`s the docstring mentions are
historical, describing the superseded prior version, not live in this
file).

### 81. `SampleTargetFromAlphaPairMemA.lean` (111 lines)
Imports: `AlphaLocusDegreeUniform`, `MatchingSolutionSwapSymmetry`,
`StabOfSmallSetTrivial`.

Proves the one honest unconditional consequence of
`SampleTargetFromAlpha`'s `memZmultiplesA` field — roadmap step 3,
subgroup closure: two samples' pair-sum classes both lying in
`⟨aClass⟩` implies their difference does too
(`sub_mem_zmultiples_of_mem_mem`, pure `AddSubgroup` closure, no
curve-specific content), then instantiated for two
`SampleTargetFromAlpha` samples as
`sampleTargetFromAlpha_pairSum_sub_mem_zmultiplesA`. **Explicitly flags
what does NOT follow next**: composing this `Δ`-membership fact with
entry 79's `delta_eq_zero_of_stabilizes_small_set` is not the one-line
corollary the roadmap's steps 4–6 sketch might suggest, because entry
80's corrected `FixedTargetSolutions` pins both pair-sums to constants —
its image under the pair-sum map is a singleton, leaving no room for
genuine `Δ`-translation to act on. Diagnosed as a real reconciliation
gap between the roadmap's original (difference-only) `S` and the
corrected `FixedTargetSolutions`, not a Lean-engineering shortcut to hunt
for. **Status: sorry-free.**

### 82. `DecoupledSystemDegreeUniformFixedTarget.lean` (122 lines)
Imports: `AlphaLocusDegreeUniform`, `MatchingSolutionSwapSymmetry`.

**The file that actually closes the 8th-moment gap's degree-uniform
target, superseding the old `genList_finrank_le`/`Stab(S)` route
entirely, per Claire's direction this pass.** The old route
(`decoupledSystem_degree_uniform` in `AlphaLocusDegreeUniform.lean`, via
`GenericPeelChainHyp`/`Rdec p ⧸ Ideal.span (genList ...)`) was chasing a
strictly harder problem than needed. Entry 80's
`fixedTargetSolutions_ncard_le_four` already **is** the needed
`p`-independent bound; this file just restates it directly in terms of
`SampleTargetFromAlpha` (`fixedTargetSolutions_ncard_le_four_
sampleTargetFromAlpha`, `d := 4`, proved outright — no existential search
over a `p^n` placeholder). No new mathematical content: pure assembly.
Note the conclusion type genuinely differs from the old target
(`Set.ncard` over a point-tuple set, not `Nat.card` over a ring
quotient) — see the file's own docstring for why this is the same
underlying goal, not the same statement shape. Hypotheses carried
unchanged from entry 80: `hbridge`, and `IsOnlyEffectiveInClass` for both
pairs. **Status: sorry-free** (the single `sorry` the docstring mentions
is a reference to the OLD superseded route's `genList_finrank_le`, not
live in this file).

### 83. `GenListFinrankFourStageTransport.lean` (145 lines)
Imports: `GenListFinrankFourStageAssembly`, `GenListTriangularReorder`.

Closes the mechanical half of the two gaps
`ROADMAP-monic-annihilator-degree-uniform.md`'s "Corrections, this pass"
flags after entry 78: entry 78's conclusion is stated over
`genListTriangular`'s reordered generator list, not `genList`'s literal
stated order — closed here via one application of
`quot_genListTriangular_eq_quot_genList` (entry 59). The genuinely open
half is NOT closed here and is named as a hypothesis rather than assumed
away: `RouteThreeHasBaseCase`, "no file anywhere proves `Module.Finite (F
p) (Rdec p ⧸ Ideal.ofList gens)` for any `gens` this induction could
legitimately start from" — `gens := []` is false (a 12-variable free
polynomial ring), and no strict prefix of `genListTriangular` is finite
either. **Design choice**: takes entry 78's ~200-hypothesis conclusion as
an opaque `hchain` hypothesis rather than re-typing its full signature,
to avoid a transcription mismatch invisible until REPL-caught — matches
this project's "read the actual file, not a summary" discipline.
Delivers `finrank_le_genList_of_finrank_le_genListTriangular` (generic
bound `B`) and `finrank_le_sixteen_genList_of_finrank_le_sixteen_
genListTriangular` (the concrete `≤ 16` corollary route 3's four-stage
accounting is expected to instantiate, pending gap 2 above). **Status:
sorry-free.**

### 84. `GenListPairwiseAgreementTransport.lean` (559 lines)
Imports: `GenListPairwiseAgreementAssembly`, `GenListTriangularReorder`.

The identical transport problem one file over, for the pairwise-agreement
line instead of the `finrank` line: entry 76's
`genListTriangular_pairwise_eq_up_to_sign` is generic in `gens`/`d` and
only meaningful for the project's real twelve equations once specialized
at `gens := genListTriangular ...` — this file does that specialization,
concluding `genList_pairwise_eq_up_to_sign`. Mechanical, not new
content: the pairwise-agreement theorem never depended on `gens`'s order
(confirmed by direct inspection of entries 74/75's generic evaluation
against `Ideal.ofList gens`). **Two real REPL errors surfaced and fixed
this pass**, both documented as reusable lessons: (1) a missing `open
TheDataDerivation`; (2) a `whnf` heartbeat timeout from a first-draft
signature that repeated the fully-applied `genList .../theData ...` terms
52 times combined — fixed structurally (not by unrolling) by stating the
theorem generically over `gens : List (Rdec p)` and `d :
DecoupledGenerators p`, tied in via `Eq` hypotheses `hgens`/`hd` rather
than inlining applied terms, mirroring entry 84's own source theorem and
entry 83's documented design choice. Also documents a related but
distinct gotcha: rewrite the IDEAL equality (`Ideal.ofList_perm`), not
the quotient-RING type equality (`quot_genListTriangular_eq_quot_
genList`) — rewriting the ring-type equality directly hits "motive is not
type correct," since the domain/ring structure derives from that type.
**Status: sorry-free.**

## Open gaps, cross-referenced (read this before assuming the chain is done)

- **File 2's `hA`/`hB` hypothesis** (a literal, not merely existential,
  `totalDegree` bound on `uRS.coeff i`/`vRS.coeff i`) is the throughline
  most of files 15–20/24/30–33 exist to address. **Settled, later pass,
  as a structural dead end rather than an open target** — see files
  18/19's closing notes, confirmed independently again from file 32's
  own investigation and cross-referenced in `ROADMAP-crossnondegenerate-
  degree-bound.md`'s final "Update" section: `towerToRdec` is not a ring
  homomorphism, so no witness-existence-based closure (`IsRdecWitness`,
  `HasRdecBound`, `HasCoordBoundK2` — files 7/31/32 alike) can produce
  the literal computed-pair bound `hA`/`hB` want, regardless of whether
  the closure operates at the whole-value or coordinate level. File 19
  already supplies the correct, weaker, actually-reachable fact instead
  (an `IsRdecWitness` bound on the literal resultant element). `hA`/`hB`
  should be read as an intentional hypothesis from here on, not
  unproved-but-provable debt — there is no live "next step" against it.
- **File 10's open hypothesis** (`evalNd (b i j) ≠ 0` for chosen
  witnesses, distinct from `MatrixNondegenerate`) had no bridge anywhere
  in the project as of that file's writing — check whether one has been
  built since before treating `coeffsOut`'s bound as unconditional.
- Files 21–22 (Obligation 1, `htop_ne_smul`) are a **separate sub-effort**
  from the `totalDegree`/`hA`/`hB` chain above — don't conflate the two
  when scoping new work; they share this directory but not a dependency
  edge.
- **Files 25–29 continue both sub-efforts**: 25 (Obligation 1, `sa=sb`
  cross-resultant symmetry — later found unnecessary for the
  counting-existence route file 29 takes), 26–27 (Obligation 1, the
  actual `genList`/`htop_ne_smul` composition, now narrowing the
  remaining gap to a curve-side witness satisfying (a)/(b)/(c)), 28
  (the `hA`/`hB` coordinate-bound line, as it stood before files 30–33 —
  see below), 29 (Obligation 1's part (a), general counting machinery
  now complete pending curve-specific instantiation).
- **Files 30–33 are the most recent continuation of the `hA`/`hB`
  coordinate-bound line (files 20/24/28) and are where that line ends,
  per the point above** — not because the gap closed, but because it was
  determined to be structurally unreachable this way. File 30
  generalizes file 24's identity into a reusable `HasQuadBound` closure
  suite; file 31 instantiates it as `HasRdecBound`, a relation rather
  than a function; file 32 (`K2CoordArith.lean`) builds the `K2`-native
  version of the same machinery as a deliberate third attempt at file
  20's dead end, gets it fully REPL-confirmed, and is the file whose own
  investigation finally nails down why no version of this approach can
  reach `hA`/`hB`; file 33 is an earlier, narrower, superseded-in-intent
  attempt at the same idea. Anyone tempted to build a *fourth*
  witness/coordinate-bound-closure attempt against `hA`/`hB` should read
  file 32's closing note and `ROADMAP-crossnondegenerate-degree-bound.
  md`'s final section first — the obstruction is structural
  (non-homomorphism), not a matter of finding the right closure lemma
  shape.
- Cross-reference `ROADMAP-degree-uniform-step3.md`'s own three-obligation
  split before assuming any one file closes more than it actually does.
- **Two competing peel architectures now coexist for item (d)/entry 55's
  sorry, and they are NOT both live.** Entries 56–61 build a `Fin
  n`-arity-indexed peel (`finSuccEquiv`-based) and, at entry 61, find it
  cannot accept `curveA1`-shaped two-new-variable-at-once relations —
  that finding is real and stands, but entry 65
  (`CurveRelationChainFinrank.lean`) shows the underlying difficulty was
  specific to the `Fin`-arity architecture, not to the mathematics: the
  literal-`Ideal.ofList`-prefix approach (entry 46, extended by entries
  62–67's shared-pivot resultant machinery) handles `curveA1` directly,
  with no analogous obstruction. As of this pass the literal-prefix +
  shared-pivot line (46, 62–67, 65) is the one still being extended;
  entries 56–60's generic `Fin`-arity machinery is not itself wrong, but
  entry 61 is its last active use — don't resume building more
  `Fin`-arity-specific stage wiring against `curveA1`-style relations
  without first checking whether entry 65's route has since closed that
  need. **Also unresolved as of this pass**: whether the literal-prefix
  route is being used for the linear-elimination stages (0–7) too, or
  whether those still route through entries 56–60/`idxEquivFin` — check
  before assuming either.
- **Stale as of this pass — corrected: `GenListFinrankResultantAssembly.
  lean` now exists (entry 71)**, and the four-shared-pivot-stage gap it
  initially left half-done (only `U0`, not `U0,U1,V0,V1`) is also closed,
  by entries 77–78. The true terminus of the `finrank` numeric chain is
  entry 78 (`GenListFinrankFourStageAssembly.lean`), not entry 71 alone —
  see entries 71/77/78 above for the honest account of what each piece
  does and does not close. What entry 78 still leaves undone: the
  mechanical `genListTriangular` → `genList` order transport, needed
  before this chain can be cited as literally proving
  `genList_finrank_le` as stated in entry 55/`GenListFinrankAssembly
  .lean`. Separately, entries 72–76 close the roadmap's Step 1
  (pairwise agreement) in full — see entry 76's own docstring for what
  it does and does not yet feed into (the `SampleTargetFromAlpha`
  linkage, roadmap item 3, is still not started).
- **The actual blocker for entry 55, per `ROADMAP-monic-annihilator-
  degree-uniform.md`'s latest corrections, is not wiring at all.** Two
  corrections deep: (1) the "integrality" question (does `finrank ≤ 16`
  hold for `sa, sb` ranging over ALL of `SampleTarget p`?) turned out to
  be the wrong question — it's false, because for fixed arbitrary
  targets the solution locus is 2-dimensional, not 0-dimensional
  (`D_anchorA`/`D_anchorB` only pinned in their difference). (2) The
  roadmap's own correction identifies the fix: `sa, sb` must come from a
  shared `SampleTargetFromAlpha`-style structure with `alpha`, `alpha'`,
  and a base point `a` FIXED first (`AlphaLocusDegreeUniform.lean`
  already has this shape) — entry 55's theorem, quantified over
  arbitrary `sa sb : SampleTarget p` with no `alpha`/`alpha'`/`a` link,
  is therefore not just unproved but not even the right statement to
  attempt. **What is genuinely still missing, per that same roadmap
  section**: a formalizable account of WHY fixing `(alpha, alpha')`
  collapses the family to a single 0-dimensional fiber — flagged there
  as not elucidated anywhere in this project. `MatchingEquationTranslation
  .lean`/`OrbitMapConstant.lean` (the separate matching-equation
  sub-effort, not part of this `totalDegree` chain) supply half of an
  answer to exactly this question. **Update, same session**: the
  `alpha - alpha'`-invariance half of that mechanism is now formalized
  as entry 70, `MatchingEquationDeltaInvariance.lean` — still not wired
  into this roadmap section or into `OrbitMapConstant.lean`'s
  hypotheses, and entry 70's own docstring flags the same `zmultiples
  a`-vs-all-of-`Jacobian H D` caveat the roadmap should account for
  before treating this as closing the gap.
