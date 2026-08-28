# Roadmap: proving `reducedClass_eq_of_isReduction'`

## Goal

`reducedClass_eq_of_isReduction'` (`AlphaLocusDegreeUniform.lean`, line
786, `sorry` at line 870) is the last un-proved piece of
`ROADMAP-reduce-divisor-correctness.md`'s Step 3: it shows Cantor
reduction's output really represents the claimed Jacobian class.

This file was heavily compacted this pass — the full pass-by-pass history
(including two abandoned constructions and several corrected bugs) is in
`ROADMAP-principal-witness-assembly-HISTORY.md.bak`. Read that only if a
past dead end needs re-diagnosing; everything live is below.

**Ground truth this pass (recomputed directly from the files, not carried
forward from old prose):**
- `AlphaLocusDegreeUniform.lean`: 1180 lines, exactly 2 real `sorry`s —
  line 870 (`reducedClass_eq_of_isReduction'`, this file's target) and
  line 963 (`decoupledSystem_degree_uniform`, an unrelated downstream
  theorem, out of scope here).
- `PeelChainAssembly.lean` and `DecoupledSystemRegular.lean`: genuinely
  **0 `sorry`** right now (previous roadmap drafts miscounted by matching
  the word "sorry" inside prose/comments — re-verified with a strict
  `:= sorry` / standalone-`sorry`-line grep).
- `CAWitness.lean` (417 ln) and `CAWitnessDivisor.lean` (296 ln): both
  0-`sorry`, build-green per Claire. **These are the live witness
  construction.**
- `CantorAddWitness.lean` (`f-`) and `TangentMumfordWitness.lean` (`f+`):
  **deprecated.** Left in the tree (content correct in isolation,
  `bMinus`'s Vandermonde machinery is reused verbatim by `CAWitness.lean`)
  but superseded — do not resume the two-witness residual-matching
  question they were built around.

## The witness construction (`CAWitness.lean` + `CAWitnessDivisor.lean`)

Old plan: build two independent interpolations (`f+` through
`C, 2•[δ₀]`; `f-` through `A, T`) and hope their residual quadratics
coincide. Abandoned — nothing forces two unrelated Vandermonde solves to
land on the same residual.

**Current plan:** build ONE function `f := y - bCA(x)`, `bCA` the
degree-≤3 interpolant solving the plain 4×4 Vandermonde system through
`Ra1, Ra2, ι(P1), ι(P2)` (`ι` = hyperelliptic involution, i.e. negate the
`P1,P2` target y-values). Its residual quadratic `uCANew` **is** `T` by
construction — no separate matching proof needed. Concretely:

- `bCA_ordInfOfPair` : `ordInfOfPair(-bCA, 1) = -6` (6 affine zeros).
- `pairNormBCA_eq_denomPolyCA_mul_uCANew` : the factorization
  `H.f - bCA² = denomPolyCA · uCANew`, `denomPolyCA` the four named
  linear factors, `uCANew` the degree-2 residual = `T`.
- `divToPair_eq_C_add_iotaA_of_split` (`CAWitnessDivisor.lean`, 0-sorry):
  the four-point divisor fact, `div_aff(f)` restricted to the four named
  points `= [Ra1]+[Ra2]+[ιP1]+[ιP2]`, fully-split case (`hdet ≠ 0`, all
  four x-coords pairwise distinct), Weierstrass points excluded
  (`hRa1Y_ne` etc.), and `uCANew`'s roots disjoint from the four named
  points supplied by the caller (`hU_evalRa1` etc., not yet derived from
  anything more primitive).

This is the single-witness analogue of `PrincipalWitnessStep1.lean`'s
`divToPair_eq_A_add_C_add_T_of_split` for the old `g`-based plan — same
recipe (`ordAt_eq_one_of_old_point`, `PrincipalWitness.lean` lemma 16),
now applied to `f = y - bCA(x)` instead of `g = E+Y·y`.

## Concrete next steps, in order

1. **State and prove the residual-point divisor fact for `f`**: at a root
   `r` of `uCANew`, what is `ordAt` of the corresponding `H.Point`?
   **Done, build-green** (Claire confirmed), `CAWitnessResidual.lean`
   (`ordAt_eq_rootMultiplicity_of_uCANew_root`). Goes through `uCANew`'s own `rootMultiplicity`
   directly (via `ordAt_eq_rootMultiplicity_unramified`,
   `LPairFinrankOneOrdAtFrac.lean` lemma 6, unconditional), NOT a
   pre-split `hUfac`-style hypothesis — a first draft used `hUfac : ∃
   Fco, uCANew = linX P.X * Fco ∧ ...` and was rejected on Claire's
   correction: that's exactly the coprimality/named-distinct-root
   overhead `OrdAtRootMultiplicityUnified.lean` exists to eliminate.
   `uCANew` itself isn't a product of named factors the way `npoly4Lcm4`
   is, so none of that file's `rootMultiplicity_mul`-unpacking is
   needed — `ordAt_eq_rootMultiplicity_unramified` applies to it
   directly, and the theorem takes the target multiplicity `m` as an
   opaque parameter (matching `rootMultiplicity_npoly4Lcm4_eq_add`'s own
   convention) so it covers the simple-root (`m=1`) and repeated-root
   (`m=2`) cases uniformly with no case split in the statement.
   **Do not reuse `ordAt_eq_one_of_old_point` for this** — checked and
   rejected separately: its `hA_ord : ordAt P A 0 = 1` hypothesis is
   shaped for `P` being a root of the NAMED factor, the opposite case
   from a residual root. If the REPL rejects this file, the likely
   trouble spots are: `Polynomial.rootMultiplicity_mul`/
   `Polynomial.rootMultiplicity_C`/`Polynomial.rootMultiplicity_eq_zero`
   (names confirmed via web search this pass, not sympy/REPL-checked),
   `ordAt_eq_rootMultiplicity_unramified`'s exact argument order (`c`
   before `α`), and the `hgbar_ne_eval`/`linear_combination` sign
   arithmetic (worked out by hand).
2. **Assemble the complete divisor**: `div_aff(f) = C + ι(A) + T` (four
   named points from step 1 above, residual pair from step 1 here),
   giving `f`'s full 6-zero affine divisor matching `ordInfOfPair = -6`.
   **Drafted this pass**, `PrincipalWitnessStep3.lean`
   (`divToPair_eq_C_add_iotaA_add_T_of_split`) — **not yet build-tested,
   Claire's REPL next.** `uCANew`'s two residual roots had to be named
   (`T1X, T2X`) to state a concrete `Finset`-level `divToPair` fact —
   deliberately NOT via `quadratic_eq_mul_X_sub_C` + `uCANew`'s degree
   (would need `uCANew.natDegree = 2` from scratch); instead a local
   `rootMultiplicity_uCANew_eq_one` helper gets `rootMultiplicity = 1` at
   each named root straight from `IsRoot`/coprimality/a per-point
   quotient-nonvanishing hypothesis (`hQT1`/`hQT2`), then feeds
   `CAWitnessResidual.lean`'s theorem with `m := 1`. Combined with
   `CAWitnessDivisor.lean`'s four-point fact via one `eq_of_coeffAt_eq`/
   `coeffAt_divToPair`/six-way-`by_cases` proof (not two separate
   `divToPair`s subtracted, unlike the old `PrincipalWitnessStep2.lean`
   precedent — simpler here since both halves share the same `(E,Y) =
   (-bCA,1)` pair, so one direct six-point Finset suffices). If the REPL
   rejects this file, likely trouble spots: `Polynomial.rootMultiplicity_mul`
   (non-primed, `IsDomain`, confirmed via web search this pass, not
   REPL-checked) vs `rootMultiplicity_mul'`'s eval-side-condition variant;
   the `hQ1_def`/`hQ2_def` argument-order mismatch (`(X-C T1X)*(X-C T2X)`
   vs `(X-C T2X)*(X-C T1X)`, deliberately swapped between the two calls so
   each `Q.eval` hypothesis is about the OTHER factor's quotient) reaching
   `rootMultiplicity_uCANew_eq_one` correctly; and the `hPtT1X ▸ hmult1`-style
   rewrites lining up `PtT1.X`/`T1X` across `CAWitnessResidual.lean`'s own
   `P.X`-parametrized statement.
3. **Connect to `reducedClass_eq_of_isReduction'`'s actual target.**
   **Sign bug found and fixed this pass** (Claire + ChatGPT) in the
   algebra this step previously stated — the "restate here since it's
   short" version below was WRONG in an earlier draft (`C - A - T +
   2•[δ₀]`, bare `T`, wrong signs); corrected version follows, with the
   actual fix landing as a naming/identification correction in
   `CAWitness.lean` (see that file's module docstring), not a change to
   `f`/`bCA`/`uCANew` themselves. With `x := ⟨A-2δ₀,_⟩`, `y :=
   ⟨C-2δ₀,hmemAnchor⟩` (`hAlphaRep`), `z := ⟨S-2δ₀,hmem⟩` (`S` =
   `AlphaLocusDegreeUniform.lean`'s target Mumford point set) all
   `: Divisor0 H`, the goal `sa.reducedClass = toJacobian D z` reduces
   (via `hAlphaRep` and `toJacobian` additivity) to showing
   `C - A - S + 2•[δ₀] ∈ principalSubgroup H hdeg`. `div_aff(f) =
   C+ι(A)+T` gives, via the three matching-`ordInfOfPair`-`(-6)`
   generators (`div(f) - div(h)` for `h := (x-R1.X)(x-R2.X)(x-δ₀.X)`,
   `{R1,R2} := C`'s points, plus `div(x-P1.X)-div(x-δ₀.X)` and
   `div(x-P2.X)-div(x-δ₀.X)`), the relation
   `C - A - ι(T) + 2•[δ₀] ∈ principalSubgroup H hdeg` — **`ι(T)`, not
   bare `T`**. This matches the goal's `C - A - S + 2•[δ₀]` exactly once
   `S := ι(T)` (`v := -bCA` mod `uCANew`, NOT `v := bCA` — see
   `CAWitness.lean`'s corrected docstring), not `S := T` as an earlier
   pass claimed. Checked exhaustively that no alternative witness
   shares `f`'s four named zeros while producing `ι(T)` directly as its
   OWN residual (the 4-point Vandermonde interpolation is unique, so
   `T` bare is the only residual `f`'s construction can produce) — the
   `ι` has to be applied at the `S := ι(T)` identification step, not
   absorbed into a different witness. This step is: turn `div_aff(f) =
   C+ι(A)+T` plus `ordInfOfPair(f) = -6`, together with the two
   `[Pi]+ι[Pi]-2[δ₀]`-type generators for `P1`/`P2` (`divToPair_linX_eq`,
   `HyperellipticClassProof.lean`, already on file, 0-`sorry`), into the
   `principalSubgroup` membership directly, then compose with (2) —
   **and separately, fix `AlphaLocusDegreeUniform.lean`'s `S`/`v`
   construction to use `v := -bCA` (mod `uCANew`) as its `S := ι(T)`
   witness**, since as stated (`S := T`, `v := bCA`) the theorem's own
   `hSmem`/`u`/`v` parameters would be asking for the wrong divisor
   class and the goal would be false as currently spelled out.
4. **Assemble into `reducedClass_eq_of_isReduction'`'s proof body** once
   (1)-(3) are in hand.
5. Tangent branch (`P1 = P2`) and Weierstrass sub-case (`P1 = P2 ∧ Y = 0`)
   are separate, smaller follow-ups after the general case closes.
6. **Also fix the stale docstring directly above the theorem** (lines
   ~780-785 in `AlphaLocusDegreeUniform.lean`) — it still describes the
   abandoned `f+`/`f-` residual-matching question as the open problem.
   Update it to point at `CAWitness.lean`'s single-witness construction
   once step 3 lands, so the next pass doesn't get misled by its own
   file's comment the way this roadmap file itself was.

## Workflow reminders specific to this file

- Don't reintroduce `f+`/`f-` (`TangentMumfordWitness.lean` /
  `CantorAddWitness.lean`) as the plan — confirmed superseded. Their code
  is fine to cite/reuse (esp. `bMinus`'s Vandermonde idiom, which
  `bCA` already copies), just not as the two-witness strategy.
- `div_aff(f)` for `f := toPair H (-bCA) 1` has **no `δ₀` term** —
  `Divisor H` is affine-only; `δ₀` only enters via `reducedClass`'s own
  `-2•[δ₀]` normalization (`Finsupp`-degree bookkeeping, unrelated to any
  pole-order computation — this was over-audited in a past pass, treat it
  as settled).
- `H.Point` in this codebase is purely affine — no point-at-infinity
  constructor anywhere. Any imported reasoning (ChatGPT or otherwise)
  using "`k·∞`"-style terms needs translating into a purely affine
  argument before it can be used here.
- When stuck on step 1/3 above, ask ChatGPT per project convention — this
  is genuine function-field construction, not lemma composition, if the
  adaptation from `ordAtFrac_eq_neg_one_of_uRS4General_root` isn't
  mechanical.
