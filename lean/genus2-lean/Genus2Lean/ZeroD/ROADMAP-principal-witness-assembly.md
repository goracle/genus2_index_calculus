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
  construction — but see the gap/fix section immediately below: their
  `P1,P2` are still free variables, not yet wired to `Sanchor`.**
- `SanchorMumfordOrdAt.lean` (new this pass): the `A`↔`alpha•aClass`
  bridge — proves `Sanchor`'s points have `ordAt = 1` in `(-va,1)`'s
  divisor, directly from `hMumfordUa`/`IsMumfordUa`. See the dedicated
  section below.
- `SanchorEqAlphaPoints.lean` (new this pass, drafted not yet
  REPL-tested): step 0 itself — proves `Sanchor = {sa.P1, sa.P2}` given
  a new hypothesis (`hAnchorRoots`, not yet threaded into
  `AlphaLocusDegreeUniform.lean`'s actual theorem signature) pinning
  `ua`'s roots to `sa.P1.X, sa.P2.X`.
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

## **Gap found and closed this pass: `A` was never tied to `alpha • aClass`**

**The bug.** `CAWitness.lean`'s witness construction (`bCA`,
`caInterpMatrix`, `caCoeff`, everything downstream) takes `P1X P2X P1Y
P2Y : k` as bare free variables. Nothing in that file — or anywhere
between it and `AlphaLocusDegreeUniform.lean` — ever says these are
`sa.P1, sa.P2` (`SampleTargetFromAlpha`'s actual anchor points, the ones
`reducedClass := alpha • aClass - toJacobian(...[P1]+[P2]...)` is
literally built from). `A := [P1]+[P2]` in this roadmap's prose was
consequently a **generic, unconstrained pair of points** on the
`CAWitness` side — not provably `sa`'s `P1,P2`, hence not provably tied
to `alpha • aClass` at all. `AlphaLocusDegreeUniform.lean` does have a
correct link on its OWN side (`hAlphaRep : sa.alpha • aClass = toJacobian
D (Sanchor's divisor, -va, 1)`, plus `hSanchorMem`/`huafree`/
`hSanchorCard` pinning `Sanchor` to `ua`'s root set) — but that link
terminates at `Sanchor`/`ua`/`va`, and nothing carried it across to
`CAWitness.lean`'s `A`/`P1`/`P2`. The two sides were never actually the
same object as far as the type-checker was concerned, which is why `T`
and the `δ₀`-coefficient bookkeeping downstream kept coming out with
inconsistent signs across passes — the assembly was silently reasoning
about two unrelated anchors.

**Why this matters concretely:** `A`'s only real job in the whole
argument is to be a divisor with `A = [P1]+[P2]` where `(P1,P2)` are
*the same points `sa`'s `alpha • aClass - [P1] - [P2] + 2•[δ₀]` uses* —
i.e. `A` has to be `Sanchor`'s twin, not an independent pair. Every
downstream sign/identification question this file has flagged across
passes (`S := ι(T)` vs `S := T`, `v := -bCA` vs `v := bCA`, the
`C - A - ι(T) + 2•[δ₀]` vs `C - A - T + 2•[δ₀]` back-and-forth) was
being worked out symbolically, without ever pinning `A` down to a
concrete, `alpha`-linked divisor to check the arithmetic against — so
disagreements had no ground truth to resolve against and kept
recurring.

**The fix, landed this pass: `SanchorMumfordOrdAt.lean`.** This new file
is the missing bridge, built directly against `Sanchor`/`ua`/`va` (the
objects `hAlphaRep` already ties to `alpha • aClass`), not against
`CAWitness.lean`'s free `P1,P2`:
- `ua_dvd_pairNorm_negVa_one`: unfolds `pairNorm H (-va) 1 = va² - H.f`
  and matches it against `IsMumfordUa`'s own `ua ∣ (va² - curvePoly ...)`
  — i.e. confirms `ua` really is the `u`-polynomial of the pair `(-va,1)`
  built from `alpha • aClass`'s Mumford data (`hMumfordUa`, already a
  hypothesis of `reducedClass_eq_of_isReduction'`), not an unrelated
  quadratic.
- `ordAt_ua_eq_one_of_mem_Sanchor`: `ordAt Q ua 0 = 1` at any genuine,
  unramified (`Q.Y ≠ 0`) root `Q` of `ua` — via
  `ordAt_eq_rootMultiplicity_unramified` plus squarefreeness forcing
  `rootMultiplicity = 1` (proved directly from `Squarefree`'s definition:
  a multiplicity-≥2 root would make `(X - C Q.X)^2 ∣ ua`, and
  `X - C Q.X` is never a unit, contradicting `huafree`).
- `ordAt_negVa_one_eq_one_of_mem_Sanchor`: the point-level payoff, `ordAt
  Q (-va) 1 = 1` for `Q ∈ Sanchor` — i.e. `Sanchor`'s points really do
  each carry order exactly `1` in `divToPair (-va) 1 Sanchor`, matching
  what `A`'s (`= Sanchor`'s twin, now that the two are identified) role
  in the assembly needs. Via `ordAt_eq_one_of_old_point` (lemma 16,
  `PrincipalWitness.lean`) fed `ua`'s order-1 fact and the cofactor
  `Uco` from `hAU : pairNorm H (-va) 1 = ua * Uco`.

**What this means for `A` going forward: `A` is `Sanchor`, not a fresh
pair of points.** Concretely, the fix is a *naming* correction, not new
math — `CAWitness.lean`'s `P1,P2` (wherever they appear: `caInterpMatrix`,
`bCA`, `divToPair_hA_eq`'s `h_A := linX(P1.X)*linX(P2.X)*linX(δ₀.X)` in
`PrincipalWitnessStep4.lean`) need to be instantiated AT `Sanchor`'s two
points specifically (equivalently, `ua`'s two roots, per `hSanchorMem`),
not left as free variables satisfied by any generic pair. Every theorem
in `CAWitness.lean`/`CAWitnessDivisor.lean`/`PrincipalWitnessStep3.lean`/
`PrincipalWitnessStep4.lean` that currently quantifies over free `P1 P2 :
H.Point` (or `k`-valued coordinates for them) should be read as
implicitly requiring the caller to supply `Sanchor`'s own two points at
the point where they connect to `reducedClass_eq_of_isReduction'` — the
theorems themselves don't need restating (they're correct for ANY valid
input Mumford pair), but the assembly step that calls them with `A`
needs to call them with `Sanchor`'s pair, not silently assume it. **This
was never actually wired up — it should be checked explicitly the next
time `PrincipalWitnessStep4.lean`'s Part 2/Part 3 (see "Plan" above) are
assembled into `reducedClass_eq_of_isReduction'`'s proof body**, since
that's the first point in the pipeline where `A` and `Sanchor` need to
be shown/asserted equal rather than merely both existing.

**Status: the ordAt-level gap (`Sanchor`'s points really do have order 1
in `(-va,1)`'s divisor) is closed** — `SanchorMumfordOrdAt.lean` proves
it, build-green pending Claire's REPL confirmation of the latest fixes
(`Polynomial.Squarefree.rootMultiplicity_le_one` doesn't exist in
Mathlib4, replaced with a from-definition argument; a stray `linarith`
call on `F p`, which has no linear order, replaced with
`linear_combination` + `mul_eq_zero` against `hchar`). **The
`Sanchor = {sa.P1, sa.P2}` identification itself is now drafted** —
`SanchorEqAlphaPoints.lean` (`Sanchor_eq_of_anchor_roots`), not yet
REPL-tested — see step 0 below for exactly what's still needed to land
it (a new hypothesis in `reducedClass_eq_of_isReduction'`'s own
signature, plus rewiring the downstream call sites to actually use
`sa.P1,sa.P2` instead of free variables).

## Concrete next steps, in order

0. **(New, highest priority) Wire `Sanchor` into `CAWitness.lean`'s `A`
   slot at the assembly layer.** **Drafted this pass**,
   `SanchorEqAlphaPoints.lean` (`Sanchor_eq_of_anchor_roots`) — **not yet
   REPL-tested.** Proves `Sanchor = {sa.P1, sa.P2}` (fully-split case)
   from `ua`'s factorization at two named roots
   (`quadratic_eq_mul_X_sub_C`, same idiom as `PrincipalWitnessAssembly.
   lean`/`OrdAtRootMultiplicityUnified.lean`'s existing `Ra1`/`Ra2`
   splits) plus `hSanchorMem`/`hSanchorCard`'s membership/cardinality
   pin, via `Finset.eq_of_subset_of_card_le`. **Needs a genuinely new
   hypothesis added to `reducedClass_eq_of_isReduction'`'s own
   signature**, not derivable from what's currently there:
   `hAnchorRoots : ua.IsRoot sa.P1.X ∧ ua.IsRoot sa.P2.X` (plus
   `sa.P1.Y = va.eval sa.P1.X`/the `P2` mirror, i.e. `sa.P1,sa.P2`
   actually lying on `(-va,1)`'s zero set) — same category of premise as
   `hMumfordUa`/`hMumfordTarget`, "caller supplies the real Mumford
   data," not a proof obligation. **Still open after this file lands:**
   (a) Claire's REPL confirmation; (b) actually adding `hAnchorRoots` to
   `reducedClass_eq_of_isReduction'`'s signature (not done here — this
   file states the standalone lemma, it doesn't touch
   `AlphaLocusDegreeUniform.lean` itself); (c) instantiating
   `CAWitness.lean`'s `P1X P1Y P2X P2Y` inputs at `sa.P1.X, sa.P1.Y,
   sa.P2.X, sa.P2.Y` throughout `CAWitness.lean`/`CAWitnessDivisor.lean`/
   `PrincipalWitnessStep3.lean`/`PrincipalWitnessStep4.lean`'s call
   sites — the lemma proves `A = Sanchor` as a `Finset`, it doesn't by
   itself rewrite every downstream free-variable call site to use it.
   Do (a)-(c) before resuming step 3 below; step 3's `principalSubgroup`
   assembly is only meaningful once `A` and `Sanchor` are the same Lean
   object throughout, not just provably equal in one isolated lemma.
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
   2•[δ₀]`, bare `T`, wrong signs); corrected version follows. **Note
   (later pass): the root cause of these recurring sign disagreements
   was diagnosed and fixed separately — see "Gap found and closed this
   pass: `A` was never tied to `alpha • aClass`" above — `A` had no
   concrete identification with `Sanchor` to check signs against. The
   algebra below is still the right target; step 0 above is the
   prerequisite for actually being able to verify it.** With `x :=
   ⟨A-2δ₀,_⟩`, `y :=
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
   **Correction, this pass: step 3's `2•[δ₀]` target is FALSE for
   generic `δ₀` — confirmed by an explicit three-generator computation
   (Claire + ChatGPT, `CHATGPT-LOG-principal-witness-assembly.md`).**
   The same three generators listed above (`G₁ := div(f)-div(h)`,
   `G₂ := div(x-P1.X)-div(x-δ₀.X)`, `G₃` the `P2` mirror) compose,
   term-by-term, to `C - A - ι(T) + [δ₀] + [ιδ₀] ∈ principalSubgroup` —
   **`[δ₀]+[ιδ₀]`, not `2•[δ₀]`**. The gap `2•[δ₀] - ([δ₀]+[ιδ₀]) =
   [δ₀]-[ιδ₀]` is a genuine extra condition (equivalent to `2([δ₀]-[∞])
   = 0` in the Jacobian on the smooth model — a torsion condition on the
   basepoint, not general). `AlphaLocusDegreeUniform.lean`'s `δ₀` is a
   fully generic basepoint (the `s`-embedding's `2•[δ₀]` is a *formal*
   double, from `s` applied twice — unrelated to a `linX`-fiber divisor,
   which is where `[δ₀]+[ιδ₀]` actually comes from), so **the `2•[δ₀]`
   target as originally planned cannot be proved from this stack's
   generators, and no other generator set is expected to fix it** — this
   is a fact about the Jacobian, not a missing Lean lemma. **Landed this
   pass**: `PrincipalWitnessStep4.lean` Part 3
   (`cIotaAmIotaT_mem_principalSubgroup`, `divToPair_hT_eq`,
   `ordInfOfPair_hT`), proving the honest `[δ₀]+[ιδ₀]` version,
   build-green pending Claire's REPL confirmation. **Open question for
   next session** (not resolved here): does
   `reducedClass_eq_of_isReduction'` need (a) a Weierstrass hypothesis on
   `δ₀` (`δ₀.Y = 0` ⟹ `ι δ₀ = δ₀` ⟹ `[δ₀]+[ιδ₀] = 2•[δ₀]` trivially — the
   cheapest fix, narrows scope), (b) a restatement of the whole
   `SampleTargetFromAlpha`/`s`-embedding pipeline in terms of
   `[δ₀]+[ιδ₀]` instead of `2•[δ₀]` (checked as unlikely — probably
   breaks `s`'s use elsewhere as a degree-1 embedding), or (c) a
   different generator set entirely. Ask ChatGPT to weigh (a) vs (b)
   before picking one, since (a) requires touching every downstream
   caller of `SampleTargetFromAlpha`/`reducedClass_eq_of_isReduction'`
   to supply the new hypothesis, and (b) requires auditing
   `DivisorClassGroup.lean`'s `s`/`s_add_s_eq_s_add_s_iff` for any use of
   `s`'s degree-1-embedding property that `[δ₀]+[ιδ₀]` would break.
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
