# ZeroD / index-calculus model: where things actually stand

Written 2026-09-21 from the module docstrings of the 13 most recent files
(listed at the bottom) plus Claire's stated hit-rate logic. It replaces every
roadmap/README that used to live at the top of `ZeroD/`; those are now in
`oldroadmaps/` as session logs. **The `.lean` docstrings are ground truth;
this file is a map, not a spec.** Lines marked *(read)* are my reading of
the files and should be corrected if wrong.

## Correction, this pass: the `HitRate`/`hbad` branch is superseded, not open

**`IndexCalculusHitRate.lean` and everything built on it —
`HitRateSumsetReduction`'s `good`/`goodMatch`/`DirectRelation`/`hbad`
machinery (Parts 2 and 4–5) included — solves a problem the project's own
`IndexCalculusComplexity.lean` already declared unnecessary, for an
independent reason.** `IndexCalculusComplexity.lean`'s own docstring:
`matchCount`'s fiber *multiplicity* (how many quadruples land on a given
`Δ`) is the wrong quantity to bound at all, because
`IndexCalculusRelations.lean`'s `translate_of_same_diff` +
`dedup_by_rhsElt_loses_no_rhs` prove that any two solves sharing a `Δ` are
gauge-related, so a big fiber is worth exactly ONE relation regardless of
its size. The complexity claim goes through `expectedRelations` /
`matchCount_distinct_hits_ge_unconditional` (a coupon-collector /
distinct-count argument, unconditional, no Sidon) and
`IndexCalculusReachability`'s `SolverReaches` (also unconditional, "pure
double counting" per its own docstring) instead. Neither of those imports
or calls `hitRate_of_good_overlap`, `hitRate_of_goodMatch`, or
`hitRate_of_good_mass` — grepped this pass, confirmed zero live callers
outside `IndexCalculusHitRate.lean`/`HitRateSumsetReduction.lean`
themselves. (`IndexCalculusReachability` imports `IndexCalculusHitRate`
only for the bare `HitRate` type/def, not for anything `good`-related.)

So the `T+T`/Fourier gap surfaced this session (bounding `hbad`'s `T+T`
piece needs Plancherel on the finite-abelian dual, nothing else in the
project uses that Mathlib area) is **not a hole to fill** — it's a
symptom of continuing to build out a branch the project moved past. Same
shape as the already-flagged-dead gauge-shift branch (open item 5 below):
built for a target (`matchCount ≤ K` pointwise, then `good`/`hbad`
accounting) that a later, better argument made unnecessary, but nobody
went back to prune or flag it at the time.

**Confirmed this pass:** `expectedRelations_le_of_hitRate` and
`expected_successes_at_balance` — `IndexCalculusHitRate.lean`'s only
bridge-to-the-model theorems — are also uncalled anywhere outside their
own file. `IndexCalculusComplexity.lean`'s actual headline result
(`index_calculus_complexity`) is built entirely from
`expectedRelations_at_balance`/`balance_forces_fifth_power`/
`total_cost_eq_rpow`, none of which touch `HitRate`. So the whole
`IndexCalculusHitRate.lean` file — not just its `good`/`hbad` corner — is
disconnected from the live proof graph.

**Downgraded this pass:** `IndexCalculusHitRate.lean` and
`HitRateSumsetReduction.lean` Parts 2, 4, 5 (the `good`/`goodMatch`/
`DirectRelation`/`hbad` material) are superseded, kept for reference,
same status as the gauge-shift branch (item 5 below) — not further open
work. `HitRateSumsetReduction` Part 1 (negative pointwise-cap result) and
Part 3 (`overlap_le_sidon_energy`, `matchCount_le_two_card_sq`) are also
only reachable via this now-superseded branch — checked, nothing live
imports `HitRateSumsetReduction` outside `IndexCalculusReachability`'s
bare-type import chain traced above, so the whole file is downstream of
the superseded branch, not just Parts 2/4/5.

## Correction, this pass (2): `SidonRepBound T` for the real `T = s(F)` is
already proved, `sorry`-free — but stranded, same pattern as above

**`SidonDichotomyGeneral.lean` already proves `SidonRepBound (sidonSet
(principalDivisorData H hdeg) δ₀ F)` for the actual `T = s(F)`, over the
real field, unconditionally — no `sorry`, no unproved `SidonDichotomy`
needed.** The degree-2 argument (`P1+P2` and its collisions are governed
by `H.Point`'s degree-2-map-to-`ℙ¹` structure, per Riemann–Roch) is exactly
right and is what
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1_general`
(`LPairFinrankOneOrdAtFracSpec.lean`) already formalizes. Chain:
`sidonRepBound_of_sidonDichotomy_nonInvolution_general` needs only
`hchar`, `hsf`, and two checkable-by-construction side conditions on `F`
— `AvoidsInvolutionPairs F` and `NoWeierstrassPoints F` (`SidonBridge.lean`;
costs at most `2g+2=6` points out of `~p` available, per that file's own
docstring) — and sidesteps the one genuinely-open piece
(`sidonDichotomy_general`'s involution-branch `sorry`, `x₂ = ι x₁`, needing
`IsOnlyFibersInCanonicalClass` general-`k`, proved nowhere in the
codebase) entirely, by construction, rather than needing it discharged.

**But: same stranding pattern as `HitRate`/`hbad` above.** `SidonRepBound`
is called only from `Complexity.lean` (in prose, and by
`UniformFiberBoundOffDiagonal.lean`, neither in the live 13-file import
closure) — `IndexCalculusComplexity.lean`'s own correction already says
the whole Sidon/second-moment apparatus `SidonRepBound` feeds is
unnecessary for the live model (fiber multiplicity is irrelevant, see
correction (1) above). So former item 1 (`SidonRepBound T` open) is now:
proved, but for a branch (`Complexity.lean`/`SidonDichotomyGeneral.lean`
→ `HitRateSumsetReduction`'s Sidon-fed parts) that the live proof graph
doesn't currently call into. Not renumbered off the open list below by
deletion (per "don't touch completed proofs, just note and move on") —
removed as a numbered open item since there's nothing left to prove here,
kept as a note in case the live model ever needs `SidonRepBound` again
(e.g. if `HitRateSumsetReduction`'s branch gets revisited).

## The model in one paragraph

A solve at fixed `(α, α')` looks for points with `P1+P2-P3-P4 = (α-α')·a`
(eq 1). Schematically `reduce(P1+P2-α·a) = (U,V) = reduce(P3+P4-α'·a)`, so
one draws the Mumford divisor `(U,V)` from `~p²` choices, and that divisor
determines all four `P`'s (up to the swaps in each pair). Success needs the
`P`'s to land in the factor base `F`, `|F| = B`, which has probability
`~B⁴/p²` per `(α,α')` (ignoring the trivial `b-b` family). With `~B` distinct
relations needed and sparse linear algebra `~B²`, the balance is
`B ~ p^(2/5)`, total cost `p^(4/5)`.

Direct-relation rule: if `Δ = (α-α')·a` already splits with both `u`-roots in
`F` (i.e. `Δ ∈ T-T`, `T`, or `T+T`), that is accepted as the relation and
no draw is made on the reduce equation. So the matching regime only ever sees
`Δ` outside those sets, and the trivial quadruples `(x,b,b,y)` (which force
`Δ = x-y ∈ T-T`) do not occur there.

## Proved (each REPL-tested per Claire)

| File | What it gives |
|---|---|
| `ZeroD/FixedTargetBoundCanonical` | `≤ 4` fixed-target bound for the canonical `D`, with `hbridge` and `IsOnlyEffectiveInClass` discharged. Needs `hchar`, `hsf`, and non-involution pairs (`P2 ≠ ι P1`); FALSE without the last. **This pass:** the non-involution fact is now a required field (`.hne`) of `SampleTargetFromAlpha` itself (`AlphaLocusDegreeUniform.lean`) rather than a separately-threaded caller hypothesis — no `SampleTargetFromAlpha` can be built without it. Resolves open item 2 below. |
| `ZeroD/InvolutionPairsCount` | involution pairs are exactly `#H.Point` of `#H.Point²`: rejecting them costs a factor `1 - 1/#Points`. (`#Points ~ p` is Hasse–Weil, not on file.) |
| `IndexCalculusRelations` | a solve's relation has `rhs = (α-α')·a`; two solves are gauge-related iff same `rhs`; `DistinctRHS` excludes all gauge duplicates. |
| `IndexCalculusComplexity` | balance `B ~ p^(2/5)`, cost `p^(4/5)` from a named per-solve rate `hRate = B⁴/p²`. |
| `IndexCalculusHitRate` | **Superseded, this pass** — see correction (1) above. `hRate` made explicit as `HitRate F c` with sufficient conditions, but disconnected from the live proof graph: `IndexCalculusComplexity`'s actual result doesn't route through it. |
| `HitRateSumsetReduction` | **Downstream of the superseded branch, this pass** — see correction (1) above. Content kept for reference: (1) NEGATIVE: no constant cap `matchCount T Δ ≤ K` at `Δ ≠ 0`. (2) POSITIVE: `matchCount ≤ 4·overlap(T+T)` under `SidonRepBound`. (3) `overlap(Δ) ≤ 2B²` unconditionally. (4)–(5) `goodMatch`/`DirectRelation`/`hbad` 3-piece split, `T`-piece proved, `T-T`/`T+T` pieces open — moot per the correction, not pursued further. |
| `SidonDichotomyGeneral` | **Proved, `sorry`-free.** `sidonRepBound_of_sidonDichotomy_nonInvolution_general`: `SidonRepBound (sidonSet (principalDivisorData H hdeg) δ₀ F)` for the real `T = s(F)`, general `k`, from `hchar`/`hsf`/`AvoidsInvolutionPairs F`/`NoWeierstrassPoints F` only. Also carries `hitCount_ge_of_sidonDichotomy_nonInvolution_general`: `≥ B²/2` distinct relations, unconditional, real curve. **No longer purely stranded — this pass**, see `IndexCalculusComplexityRealHitCount` below. |
| `IndexCalculusComplexityRealHitCount` | **New, this pass.** Chains `SidonDichotomyGeneral`'s `hitCount_ge_of_sidonDichotomy_nonInvolution_general` (`≥ B²/2` distinct relations, real curve, unconditional) into `IndexCalculusComplexity`'s balance point `B⁵=p²`: at that balance, the real curve's existence guarantee (`B²/2`) already covers the `~B` relations the model calls for, with room to spare. Settles, for the actual curve, the "which fiber-cap instantiation" question `IndexCalculusComplexity`'s own docstring had left as an unmade modeling choice. Does NOT close the reachability gap (below) — this is a static existence fact over the whole `B⁴`-quadruple space, not a statement about `N` solve attempts. |
| `ZeroD/GaugeOrbitMatchCountBound` | earlier "gauge orbit = swapImages" claim was false; honest replacement: the `Δ`-fiber is a union over pair-sum classes of `≤4` fibers. |
| `ZeroD/AlphaUnionGaugeCollapse` | any second sample with the same `α-α'` is gauge-accounted for by the reference `≤4` fiber. |

## Open, in order of importance

1. **`IndexCalculusReachability`'s `SolverReaches` takes `|Sol Δ| ≤ d`.**
   *(read, confirmed this pass — not actionable without new modeling
   decisions.)* `matchCount`/`SolverReaches`/`Sol Δ` live in the abstract
   group model (`G`/`Finset G`/`AverageComplexity.lean`); `Sol Δ` itself
   is never a defined term anywhere, just prose motivating `SolverReaches`
   as a hypothesis. `GaugeOrbitMatchCountBound`'s pair-sum-class
   decomposition lives entirely at the `H.Point`/`Jacobian H D` level,
   with no notion of a factor base `F` or per-solve probability `q` at
   all. The two files share no common object to restate the bound in
   terms of — bridging them means inventing new model glue (how factor-
   base membership in `G` corresponds to pair-sum classes over
   `H.Point`), not discharging an existing proof obligation. Left as is.
2. **Reachability/sampling gap: turning "relations exist" into "a solver
   finds them."** `IndexCalculusComplexityRealHitCount` (new, this pass)
   establishes that at the balance point `B⁵=p²`, at least `B²/2` distinct
   relations genuinely exist for the real curve, unconditionally — matching
   the `~B²` exponent the balance needs, not just the weaker unconditional
   `~B` bound. What is NOT established: that `N ~ B²` solve *attempts* (a
   randomized search over the whole group, one candidate returned per
   attempt, checked afterward for factor-base membership) actually finds
   `~B` of those relations. This is a coupon-collector-style claim needing
   genuine expectation/probability machinery (indicator variables, linearity
   of expectation) that nothing in this project has ever used — no `PMF`,
   `MeasureTheory`, or `ProbabilityTheory` import anywhere in the codebase;
   the project's existing "probability" results (`PaleyZygmund.lean`,
   `HitRateSumsetReduction.lean`) are all finite-combinatorics second-moment
   arguments in disguise, not measure-theoretic ones. **Sent to ChatGPT
   this pass** for a scoping verdict: whether a finite-combinatorics
   coupon-collector argument avoiding `PMF`/`MeasureTheory` entirely is
   viable, or what minimal slice of Mathlib's probability API would be
   needed, or whether a deterministic worst-case reformulation sidesteps
   the need for expectation machinery altogether. Awaiting Claire's
   response back from that consult before attempting any Lean.

*(Former item 2, "sampler must reject `P2 = ι P1`": resolved, this pass —
`SampleTargetFromAlpha` now carries the non-involution fact as a required
field, see the `Proved` table above.)*

*(Former gauge-shift-branch item: dropped from this list per Claire's
instruction — worth noting, not worth archiving. No longer tracked here.)*

*(Former item 1, `SidonRepBound T` for the real `T = s(F)`: resolved, see
correction (2) above — proved, not open, just stranded off the live path.)*

## Deprecated branch (kept, not extended)

The degree-uniform 0-dimensional-system route (`decoupledSystem_degree_uniform`,
`GenericPeelChainHyp`, peel-chain finrank assembly, `CrossNondegenerate`
degree-bound files). The one live `sorry` under `ZeroD/` is here:
`GenListFinrankAssembly.lean : genList_finrank_le`. Only 29 of 154 `ZeroD/`
modules are in the import closure of the 13 files below.

## Live `sorry` inventory (comment-stripped scan, 2026-09-21): 8

`RiemannRochGenus2` (`finrank_L_pair`, `finrank_L_canonical`),
`RiemannRochCrux` (`uniqueDegree2MapToP1`,
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1`), `PrincipalSubgroupCollapse`
(`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1'`), `SidonDichotomyGeneral`
(`sidonDichotomy_general`), `LCanonicalElementary`
(`isOnlyFibersInCanonicalClass_of_elementary`), `ZeroD/GenListFinrankAssembly`
(`genList_finrank_le`). The scan script is in `oldroadmaps/ZeroD-STATUS.md`.
Importing a file with a `sorry` is not depending on it: to check the headline
result, run `#print axioms` on `fixedTargetSolutions_ncard_le_four_canonical`
and look for `sorryAx`. (`hitRate_of_good_overlap` dropped from this check —
superseded, see correction above; not a headline result.) Same check is
worth running on `index_calculus_complexity_real_hitCount`
(`IndexCalculusComplexityRealHitCount.lean`, new this pass) — it imports
`SidonDichotomyGeneral`, which carries `sidonDichotomy_general`'s live
`sorry` in an unrelated declaration; the theorems it actually calls
(`hitCount_ge_of_sidonDichotomy_nonInvolution_general` and its dependents)
were already `sorry`-free per the inventory above, so this should come back
clean, but hasn't been explicitly `#print axioms`-checked yet.

## Files this map is built from (oldest to newest)

`ZeroD/AlphaUnionGaugeCollapse`, `ZeroD/GaugeOrbitMatchCountBound`,
`IndexCalculusRelations`, `IndexCalculusComplexity`, `CantorCompositionStep`,
`AlphaReducedClassShift`, `CantorMulMumford`, `GaugeShiftAssembly`,
`IndexCalculusHitRate`, `IndexCalculusReachability`,
`ZeroD/FixedTargetBoundCanonical`, `ZeroD/InvolutionPairsCount`,
`HitRateSumsetReduction`. Plus, read a previous pass while chasing item 1
(resolved, correction (2) above): `SidonDichotomyGeneral`,
`SidonBridge`, `FFKSidon`, `DivisorClassGroup`.

**Updated 2026-09-22**: `ZeroD/AlphaLocusDegreeUniform`
(`SampleTargetFromAlpha`'s new `.hne` field),
`ZeroD/SampleTargetFromAlphaWitness` (threading `.hne` through the one real
constructor) — both REPL-confirmed green. Plus the new file
`IndexCalculusComplexityRealHitCount` (chaining `SidonDichotomyGeneral`'s
hit-count bound into `IndexCalculusComplexity`'s balance point),
REPL-confirmed green.
