# ZeroD / index-calculus model: where things actually stand

Written 2026-09-21 from the module docstrings of the 13 most recent files
(listed at the bottom) plus Claire's stated hit-rate logic. It replaces every
roadmap/README that used to live at the top of `ZeroD/`; those are now in
`oldroadmaps/` as session logs. **The `.lean` docstrings are ground truth;
this file is a map, not a spec.** Lines marked *(read)* are my reading of
the files and should be corrected if wrong.

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
| `ZeroD/FixedTargetBoundCanonical` | `≤ 4` fixed-target bound for the canonical `D`, with `hbridge` and `IsOnlyEffectiveInClass` discharged. Needs `hchar`, `hsf`, and non-involution pairs (`P2 ≠ ι P1`); FALSE without the last. |
| `ZeroD/InvolutionPairsCount` | involution pairs are exactly `#H.Point` of `#H.Point²`: rejecting them costs a factor `1 - 1/#Points`. (`#Points ~ p` is Hasse–Weil, not on file.) |
| `IndexCalculusRelations` | a solve's relation has `rhs = (α-α')·a`; two solves are gauge-related iff same `rhs`; `DistinctRHS` excludes all gauge duplicates. |
| `IndexCalculusComplexity` | balance `B ~ p^(2/5)`, cost `p^(4/5)` from a named per-solve rate `hRate = B⁴/p²`. |
| `IndexCalculusHitRate` | `hRate` made explicit as `HitRate F c`; proved sufficient conditions (`hitRate_of_tight_secondMoment`, `_of_uniform_cap`, `_of_good_mass`). Corrects Complexity: repeated hits are free of error but not free of cost, so average multiplicity over realized `Δ` must be `O(1)`. |
| `HitRateSumsetReduction` | (1) NEGATIVE: no constant cap `matchCount T Δ ≤ K` at `Δ ≠ 0` (trivial `(x,b,b,y)` family gives `≥ |T|`), so the pointwise-cap route is closed. (2) POSITIVE: `matchCount ≤ 4·overlap(T+T)` under `SidonRepBound`; `hitRate_of_good_overlap`. (3) `overlap(Δ) ≤ 2B²` unconditionally (Cauchy-Schwarz), but that's `c=Θ(B²)` not `O(1)`. (4) `goodMatch`/`DirectRelation`/`hitRate_of_goodMatch`: the real 3-part exclusion set, overlap cap discharged, `hbad` isolated as the one open input — **not yet REPL-tested this pass**. |
| `ZeroD/GaugeOrbitMatchCountBound` | earlier "gauge orbit = swapImages" claim was false; honest replacement: the `Δ`-fiber is a union over pair-sum classes of `≤4` fibers. |
| `ZeroD/AlphaUnionGaugeCollapse` | any second sample with the same `α-α'` is gauge-accounted for by the reference `≤4` fiber. |

## Open, in order of importance

1. **`HitRate` for the real factor base — `good` now pinned down; `hbad` is the
   remaining gap.** `HitRateSumsetReduction` Part 4 (this pass) defines
   `DirectRelation T Δ := (Δ ∈ T-T) ∨ (Δ ∈ T) ∨ (Δ ∈ T+T)` (as existentials,
   project convention) and `goodMatch T := ¬ DirectRelation T`, matching the
   stated model exactly. `goodMatch_overlap_cap` discharges the overlap-cap
   input for free (Part 3's `overlap_le_sidon_energy` is unconditional in
   `Δ`), and `hitRate_of_goodMatch` packages the whole thing, so the ONLY
   remaining input is `hbad`: a bound on `∑_{Δ ∈ DirectRelation} matchCount T Δ`
   (now honestly three pieces — `T-T`, `T`, `T+T` — not just the `T-T` energy
   discussed in Part 2's "What this does NOT prove"). Still not supplied by
   anything on file; still needs either the third-additive-energy bound on
   `T-T` already flagged, or a fresh argument for the `T` and `T+T` pieces
   (heuristically smaller, `~B` and `~B²` against a `B⁴/2` budget, but
   unproved). Restating the whole thing as the random-`(U,V)` count `~B⁴/p²`
   is still open too.
2. **`SidonRepBound T` for the actual `T = s(F)`** is an explicit hypothesis
   everywhere it is used.
3. **`IndexCalculusReachability`'s `SolverReaches` takes `|Sol Δ| ≤ d`.**
   *(read)* By `GaugeOrbitMatchCountBound` the full `Δ`-fiber is a union of
   `≤4` fibers over ~`p²` divisors `(U,V)`; the `≤4` is per `(U,V)`, not per
   `Δ`. Decide whether that file's model should be restated per-`(U,V)`.
4. **Sampler must reject `P2 = ι P1`** (cost quantified above); nothing on
   file enforces it.
5. **Gauge-shift branch** (`CantorCompositionStep`, `CantorMulMumford`,
   `AlphaReducedClassShift`, `GaugeShiftAssembly`): built to support a
   shift-then-reduce argument for the pointwise `matchCount ≤ K` target, which
   `HitRateSumsetReduction` Part 1 closes as unviable. *(read)* Probably no
   longer on the critical path; `CantorMulMumford` still carries the
   `CantorAddWitness` existence hypothesis. Confirm before archiving.

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
results, run `#print axioms` on `fixedTargetSolutions_ncard_le_four_canonical`
and `hitRate_of_good_overlap` and look for `sorryAx`.

## Files this map is built from (oldest to newest)

`ZeroD/AlphaUnionGaugeCollapse`, `ZeroD/GaugeOrbitMatchCountBound`,
`IndexCalculusRelations`, `IndexCalculusComplexity`, `CantorCompositionStep`,
`AlphaReducedClassShift`, `CantorMulMumford`, `GaugeShiftAssembly`,
`IndexCalculusHitRate`, `IndexCalculusReachability`,
`ZeroD/FixedTargetBoundCanonical`, `ZeroD/InvolutionPairsCount`,
`HitRateSumsetReduction`.
