# Roadmap: `reducedClass_eq_of_isReduction'` dispatcher

## Why this doc exists

Per `ROADMAP-cawitness-tangent-interpolation.md`'s items 6-8 (this
pass): all seven top-level theorems this doc dispatches over —
`reducedClass_eq_of_isReduction'` (split), `..._tangent` (anchor
`Ra1.X=Ra2.X`), `..._tangent_target` (target `sa.P1.X=sa.P2.X`, equiv.
`T1.X=T2.X`), and `..._cross{1,2,3,4}` (the four `Ra_i = ι(sa.P_j)`
variants) — are individually complete, 0-`sorry`, REPL-confirmed. None
has a caller anywhere in the codebase. This is the design for the
dispatcher that would give them one.

**This doc is a design, not yet Lean.** Per Claire's instruction to
design first — case-split shape and hypothesis threading across 8
branches is a real decision surface, not a mechanical port, so it's
worth agreeing the shape before writing ~1500 lines against it.

## The case space, confirmed by direct read (not assumed)

Every one of the seven theorems fixes `sa`'s anchor pair `Ra1,Ra2` and
target pair `sa.P1,sa.P2` (via `T1,T2`, the roots of the reduced
Mumford `u`) at one specific point in this 3-axis space:

- **Anchor axis**: `Ra1.X = Ra2.X` or `≠`.
- **Target axis**: `sa.P1.X = sa.P2.X` (equivalently `T1.X = T2.X`,
  confirmed identical by `AlphaLocusDegreeUniformTargetTarget.lean`'s
  own docstring) or `≠`.
- **Cross axis**: whether any of `Ra1.X = sa.P1.X`, `Ra1.X = sa.P2.X`,
  `Ra2.X = sa.P1.X`, `Ra2.X = sa.P2.X` holds, GIVEN anchor and target
  are each still split (`Ra1.X ≠ Ra2.X`, `sa.P1.X ≠ sa.P2.X`) — this
  is the domain the four `Cross{1,2,3,4}` theorems occupy, confirmed
  by reading their signatures directly: all four keep `hRa12Xne`/
  `hT12Xne`-shaped hypotheses (`Ra1 ≠ Ra` etc., `T1.X ≠ T2.X`) for the
  UNCOLLAPSED pair, and only the fifth relation (one specific
  anchor-target coordinate collision, forced to the `ι`-conjugate
  identity via the impossibility lemma) varies.

**Confirmed disjoint, confirmed exhaustive-as-far-as-built:**
- `_tangent` requires `Ra1.X = Ra2.X`, and independently keeps
  `hT12Xne : T1.X ≠ T2.X` — never touches the target or cross axes.
- `_tangent_target` requires `sa.P1.X = sa.P2.X` (target collapsed)
  and keeps the anchor pair split — never touches the anchor or cross
  axes.
- Each `_cross{N}` requires anchor AND target each still split
  (`h1,h2,h3`-style three-hypothesis nondegeneracy, confirmed against
  `CAWitnessCrossTangent{2,3,4}.lean`), plus exactly one of the four
  cross identities.
- The base (split) theorem requires all of `hRa12Xne`, `hT12Xne`, AND
  the six-hypothesis family `h1P1,h1P2,h2P1,h2P2,hPP` (four cross +
  `hRa12Xne`'s target twin) — i.e. genuinely no collision anywhere.

**Not built, confirmed not needed by any live caller** (per items 6
and 7 of the parent roadmap, this pass): simultaneous anchor+target
tangency, and any tangent variant crossed with a cross-pair collision.
Both are real gaps in principle but currently vacuous — no caller
supplies data landing there. The dispatcher below therefore has a
CATCH-ALL branch for these (see "Uncovered residual case" below)
rather than pretending the case space is fully closed.

**The genuinely impossible sub-case** (`Ra_i = sa.P_j` as literal
point equality, not just `X`-coordinate collision) is ruled out by
`CAWitnessCrossTangentImpossibility.lean`'s `eq_iota_of_X_eq_of_rowZero`
— but only CONDITIONALLY, once the specific `Cross{N}` construction's
own doubled-row identity (`Ra.Y = -P.Y`) is already in scope. This is
the module's own documented limitation (see its docstring, quoted
below) and directly shapes the dispatcher's own decidability question
— see "The undecidable step" below.

## What the dispatcher can and cannot decide on its own

A genuinely general dispatcher would want to case on `Decidable`
propositions like `Ra1.X = Ra2.X` and dispatch automatically. Two of
the three axes are fine:

- **Anchor axis** (`Ra1.X = Ra2.X`): decidable given `DecidableEq
  (F p)`, which the ambient field already has. Clean `if`.
- **Target axis** (`sa.P1.X = sa.P2.X`): same, clean `if`.

**The cross axis is NOT cleanly decidable by the dispatcher itself.**
Per the impossibility file's own docstring (quoted in full in
`ROADMAP-cawitness-tangent-interpolation.md`'s notes on
`CAWitnessCrossTangentImpossibility.lean`): "the construction
presupposes the identification, so using it that way would be
circular... it is NOT 'derive `Ra = ι(P1)` from `Ra.X = P1.X` using the
interpolation matrix's rows'... a caller who has BOTH `Ra.X = P1.X`
AND the construction's own row identity in scope cannot also have
`Ra = P1`." In other words: `eq_iota_of_X_eq_of_rowZero` needs
`hRowZero : Ra.Y = -P1.Y` as an INPUT, and that fact is not visible
from `Ra1.X = sa.P1.X` alone — it's a fact about which of the two
square roots of `H.f.eval x` the caller's actual data happens to
supply for each point, which the dispatcher has no way to compute
from bare field equality.

**Consequence**: the dispatcher cannot be a single `if`-`then`-`else`
chain purely on `X`-coordinate equalities for the cross branches. It
needs the CALLER to additionally supply, for whichever `X`-coordinate
collision holds (if any), the corresponding `Y`-level fact — either
`Ra_i.Y = sa.P_j.Y` (same-sign, ruled impossible downstream) or
`Ra_i.Y = -sa.P_j.Y` (the `ι`-identity the `Cross{N}` theorem needs).
This is not a new hypothesis invented for the dispatcher — every
`Cross{N}` theorem already has this data implicitly, since `hP1eq :
sa.P1 = Point.iota Ra` (an `H.Point` equality) unpacks to exactly
`Ra.X = sa.P1.X ∧ Ra.Y = -sa.P1.Y` via `Subtype.ext_iff`/`Prod.ext_iff`
plus `Point.iota_X`/`Point.iota_Y` — confirmed these three exist with
exactly these names/statement shapes in `AffinePoints.lean` (`H.Point`
is a plain `Subtype`, no separate `Point.ext_iff` exists, checked
directly rather than assumed). So the honest dispatcher signature
takes the SAME `H.Point`-level data the four `Cross{N}` theorems
already take (`hP1eq`-shaped hypotheses), not raw field equalities —
it doesn't need to rediscover anything, only route.

## Proposed shape

**Two-level dispatch, mirroring `ReduceDispatchGeneral`'s own idiom
one layer up** (`GeneralSharedRoot.lean` line 1277) rather than
inventing a new pattern:

1. **Outer level — decidable, on `X`-coordinates only:**
   `if hRa : Ra1.X = Ra2.X then ... else if hT : sa.P1.X = sa.P2.X
   then ... else ...` — three-way split into tangent-anchor,
   tangent-target, and "both split" branches. Clean, no new
   hypotheses needed beyond what's already in scope (`DecidableEq (F
   p)` off the ambient field).

2. **Inner level (only inside the "both split" branch) — NOT
   decidable, taken as a caller-supplied `Prop`-valued case
   description**, structured as a single sum type rather than four
   more nested `if`s guarded by undecidable propositions (an `if`
   needs `Decidable`, and per the section above, the cross conditions
   genuinely aren't, from `X`-coordinates alone). Concretely, a small
   inductive:

   ```lean
   /-- Which (if any) cross-pair identification holds, once anchor and
   target are each confirmed split. `none` is the fully-generic case
   (all four `h1P1,h1P2,h2P1,h2P2` hold); each `some` variant names
   the one `H.Point`-level identity the caller has established. -/
   inductive CrossCase (Ra1 Ra2 : H.Point) (P1 P2 : H.Point) : Type
     | generic (h1P1 : Ra1.X ≠ P1.X) (h1P2 : Ra1.X ≠ P2.X)
               (h2P1 : Ra2.X ≠ P1.X) (h2P2 : Ra2.X ≠ P2.X) : CrossCase Ra1 Ra2 P1 P2
     | cross1  (h : P1 = Point.iota Ra1) : CrossCase Ra1 Ra2 P1 P2
     | cross2  (h : P2 = Point.iota Ra1) : CrossCase Ra1 Ra2 P1 P2
     | cross3  (h : P1 = Point.iota Ra2) : CrossCase Ra1 Ra2 P1 P2
     | cross4  (h : P2 = Point.iota Ra2) : CrossCase Ra1 Ra2 P1 P2
   ```

   The caller builds one `CrossCase` constructor (their choice — this
   is DATA the caller supplies, matching the "caller supplies the real
   Mumford/witness data" convention already used everywhere else in
   this file for `hdet`, `hMumfordUa`, etc., not a fact the dispatcher
   derives). The dispatcher then `match`es on it and calls the
   corresponding one of `reducedClass_eq_of_isReduction'` (generic) /
   `_cross1` / `_cross2` / `_cross3` / `_cross4`.

   **Why a `match` on caller-supplied data instead of nested
   `Decidable if`s**: this is the direct, honest reflection of the
   "undecidable step" finding above — dressing it up as an `if` with a
   manufactured `Decidable` instance (e.g. `Classical.dec`) would
   silently make the dispatcher NON-COMPUTABLE in a way that hides the
   real content (which branch fires would stop being determined by
   the `X`-coordinate data alone, exactly the circularity the
   impossibility file's docstring warns against). A `match` on an
   explicit `CrossCase` argument keeps that honest: the type signature
   itself documents that resolving the cross case needs more than
   field equality.

3. **The `False`/impossible same-sign branch**: per the impossibility
   file, `Ra = P1` (as opposed to `Ra = ι(P1)`) under the row-identity
   hypothesis is `False` — but that's a fact about a SPECIFIC
   construction already having committed to a row convention, not
   something the dispatcher itself needs to rule out. The dispatcher's
   `CrossCase` inductive simply doesn't have a constructor for "same
   point" — a caller who genuinely has `Ra1 = sa.P1` (not just same
   `X`) cannot express that case at all via this type, which is
   correct: no top-level theorem exists for it, and per the
   impossibility lemma, none needs to (it's unreachable whenever the
   caller's own data comes from one of the `CAWitness`-family
   constructions, which all commit to the `ι`-row convention).

## Uncovered residual case — flagged, not silently swallowed

The outer `if`-`if`-`else` above is only 3-way (anchor-tangent /
target-tangent / both-split), matching the 3 built branches at that
level. **Simultaneous anchor+target tangency is NOT a fourth outer
branch** — no such theorem exists (item 6 of the parent roadmap
confirmed no caller needs it yet). Two honest options, to decide with
Claire before writing this, not silently picked:

- **(a) Partial dispatcher**: signature takes `hRa : Ra1.X ≠ Ra2.X ∨
  sa.P1.X ≠ sa.P2.X` (rules out the simultaneous case as an explicit
  hypothesis) or equivalent, so the function is total on its
  restricted domain and the missing case is visible in the type, not
  hidden in an unreachable-`False`-branch. Matches the pattern
  `dvd_pairNormBCA_full`'s own docstring uses elsewhere in this
  project (state what's NOT covered as a hypothesis, don't paper over
  it).
- **(b) Defer the fourth branch's existence question entirely**: give
  the dispatcher a `sorry`-guarded fourth branch (`Ra1.X = Ra2.X ∧
  sa.P1.X = sa.P2.X` case raises `False.elim` from a `sorry`d
  "no caller needs this yet, revisit if one does" placeholder) — NOT
  recommended, since it violates the project's own "no `sorry`s except
  genuinely deferred hard math" convention for something that isn't
  hard math, just unbuilt.

**Recommendation: (a).** It's honest, keeps the dispatcher 0-`sorry`
immediately, and if a caller later needs the simultaneous case, the
type signature is the natural place that forces revisiting it (adding
a fourth theorem AND updating the dispatcher's hypothesis, not
discovering a silent gap at proof time).

## Concrete signature sketch

```lean
/-- **Top-level dispatcher.** Routes to whichever of the seven
`reducedClass_eq_of_isReduction'` variants matches `sa`'s actual
anchor/target configuration. Per "Uncovered residual case" above,
callers must additionally supply `hRaT : Ra1.X ≠ Ra2.X ∨ sa.P1.X ≠
sa.P2.X` (rules out the not-yet-built simultaneous-tangency case);
everything else (all seven variants' own hypothesis blocks) is
threaded through as-is via seven separate hypothesis BUNDLES rather
than flattened, to keep this signature legible — see "Bundling"
below. -/
def reducedClassDispatch {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H} {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (Ra1 Ra2 : H.Point)
    (hRaT : Ra1.X ≠ Ra2.X ∨ sa.P1.X ≠ sa.P2.X)
    (cc : Ra1.X ≠ Ra2.X → sa.P1.X ≠ sa.P2.X →
      CrossCase Ra1 Ra2 sa.P1 sa.P2)
    -- ... plus one hypothesis BUNDLE per branch (see below) ...
    : sa.reducedClass + q = toJacobian D target := by
  by_cases hRa : Ra1.X = Ra2.X
  · exact reducedClass_eq_of_isReduction'_tangent ... -- (bundle for this branch)
  · by_cases hT : sa.P1.X = sa.P2.X
    · exact reducedClass_eq_of_isReduction'_tangent_target ...
    · match cc hRa hT with
      | .generic h1P1 h1P2 h2P1 h2P2 =>
          exact reducedClass_eq_of_isReduction' ...
      | .cross1 h => exact reducedClass_eq_of_isReduction'_cross1 ...
      | .cross2 h => exact reducedClass_eq_of_isReduction'_cross2 ...
      | .cross3 h => exact reducedClass_eq_of_isReduction'_cross3 ...
      | .cross4 h => exact reducedClass_eq_of_isReduction'_cross4 ...
```

**Bundling, not flattening — the real signature-design decision.**
Each of the seven variants has on the order of 40-60 hypotheses
(`reducedClass_eq_of_isReduction'` itself runs to line 808-~1210, well
past a hundred lines of signature). Flattening all seven into one
mega-signature is a non-starter (guaranteed name clashes — every
variant reuses `Sanchor`, `S`, `va`, `u`, `v`, `ua`, `Uco`, etc. — and
unreadable regardless). The right shape is almost certainly **one
`structure` per branch, bundling that branch's own post-`sa`
hypothesis block**, mirroring how `TangentReductionData`/
`TangentAssemblyData`-style structures already package the tangent
branches' own scaffolding elsewhere in this codebase (per this
roadmap's parent doc, Part B's own notes on those structures). Then
`reducedClassDispatch` takes one argument per branch, each of an
`Option`-like or sum-indexed bundle type, OR — simpler — is only
CALLED once the caller has already decided which branch applies (the
`by_cases`/`match` structure above still routes, but the caller
supplies only the ONE relevant bundle for their actual case, with the
other six left as unused/opaque via the bundle types' own
existentials). **Checked directly, this pass, and the picture is now precise, not
just "one data point":** grepped every `AlphaLocusDegreeUniform*.lean`
file for top-level `structure` definitions and confirmed each
variant's ACTUAL top-level theorem signature (not just its
docstring's own framing):

- **`_tangent`** (`AlphaLocusDegreeUniformTangent.lean`): ALSO already
  bundled — `structure TangentCoefficientData`/`TangentReductionData`/
  `TangentAssemblyData` (lines 214/235/250) exist, and the real
  top-level theorem (line 433, confirmed by reading past the file's
  earlier `hDP_tangent_aux` — a SEPARATE, flat-signature helper theorem
  that only produces `hDP`'s premise, not the main result) takes
  exactly `(base : TangentReductionData sa) (d : TangentAssemblyData
  sa) (hcoeff : ...)` and concludes `sa.reducedClass + d.as_q = ...`
  — the SAME two-bundle, `d.as_q`-conclusion shape as
  `_tangent_target`. (The flat ~35-hypothesis signature visible
  earlier in that file, quoted in this doc's first draft, was
  `hDP_tangent_aux` — internal scaffolding, not the theorem a
  dispatcher would call.)
- **`_tangent_target`**: bundled, as already found
  (`TangentTargetReductionData`/`TangentTargetAssemblyData`).
- **The split theorem and all four `_cross{N}`**: grepped, ZERO
  top-level `structure` definitions in `AlphaLocusDegreeUniform.lean`
  or any `AlphaLocusDegreeUniformCross{1,2,3,4}.lean` file (only
  `SampleTargetFromAlpha`, an unrelated pre-existing structure `sa`
  itself has type). These five theorems genuinely have flat,
  ~100+-hypothesis top-level signatures, each with its own bare `q :
  Jacobian H D` parameter and `sa.reducedClass + q = ...` conclusion.

**So the real shape is: 2 of 7 variants (both tangent-axis ones)
already bundled identically; 5 of 7 (split + all four cross) flat and
mutually consistent with each other.** This sharpens the design task
considerably — it is not "invent a bundling scheme," it's "write
`SplitReductionData`/`SplitAssemblyData`-style bundle structures for
the split theorem and one bundle-pair per cross variant, mirroring
`TangentReductionData`/`TangentAssemblyData`'s existing field
breakdown field-for-field where the two theorems' hypothesis lists
line up (most of the ~100 hypotheses are IDENTICAL boilerplate — Uco/
UcoT cofactor data, hspec_f/hspec_hT spectrum conditions, hsupp_f/
hsupp_hT support conditions — across all seven variants; only the
anchor/target-construction-specific slice differs, e.g. `caInterpMatrix`
vs. `caTangentInterpMatrix` vs. `caCrossInterpMatrix`)." The
`q`-vs-`d.as_q` mismatch resolves itself once the five flat theorems
get bundle structures with their own `..._q` field mirroring
`TangentAssemblyData.as_q` — not a separate fix, the same task.

**Conclusion shape checked directly for all seven, one real
discrepancy found and it matters for the design above.**
`reducedClass_eq_of_isReduction'`, `_tangent`, and all four
`_cross{1,2,3,4}` conclude `sa.reducedClass + q = toJacobian D
<target>` with a bare `q : Jacobian H D` hypothesis-parameter
(identical `hq` definition in each: `toJacobian D (single (Point.iota
δ₀) - single δ₀ ...)`, confirmed by grep across all six files). **But
`_tangent_target` does NOT** — its conclusion is `sa.reducedClass +
d.as_q = toJacobian D ...`, where `d : TangentTargetAssemblyData sa`
is an already-existing BUNDLE STRUCTURE, and `d.as_q` is one of its
fields (confirmed by direct read, `AlphaLocusDegreeUniformTangentTarget.lean`
line 378-390). `_tangent_target` ALSO takes a second bundle, `base :
TangentTargetReductionData sa`.

**This is direct, already-in-the-codebase precedent for the "Bundling"
section's option (i)** (seven new named structures) — not a
hypothetical to weigh against option (ii), but confirmation that at
least one of the seven variants ALREADY made that choice, for exactly
the reason this doc's own "Bundling" section gives (avoiding a
100+-hypothesis flat signature). **Revises the recommendation below**:
option (i) isn't a candidate to evaluate against `isReductionOf`'s
existential pattern, it's the pattern this codebase has already
chosen once; the remaining work is checking whether
`_tangent`/`_cross{1,2,3,4}`/the split theorem already have (or would
need newly-written) analogous bundle structures, and whether
`TangentTargetReductionData`/`TangentTargetAssemblyData`'s own shape
(two bundles, `base`+`d`, not one) is what the other six should mirror
or a target-tangent-specific wrinkle. **Also means the dispatcher's
return type is NOT uniform across all seven as originally sketched**
— the `_tangent_target` branch's conclusion mentions `d.as_q`/
`d.as_v`/`d.as_S` (bundle-relative names) where the other six mention
bare `q`/`v`/`S`, so the dispatcher's own top-level statement needs
either its own fresh `q`/`v`/`S`-shaped conclusion with each branch's
`have`-step unifying to it (the `calc` block at
`AlphaLocusDegreeUniformTangentTarget.lean` line 535 already does
exactly this internally, worth reading before assuming the mismatch
is a blocker — it may already reduce to the same underlying
`toJacobian D ...` term post-unfolding), or the dispatcher takes `d`/
`base`-shaped bundles for ALL seven branches (extending the existing
two-bundle convention outward) rather than mixing flat and bundled
signatures. **This needs to be resolved as part of item 1 below
(bundling design), not deferred further** — it's the same design
question, now with one concrete data point pointing at a specific
answer rather than two abstract options.

## Suggested order

1. **DONE this pass — `TangentReductionData`/`TangentAssemblyData`'s
   field breakdown, read directly.** Three-tier structure, confirmed
   by reading `AlphaLocusDegreeUniformTangent.lean` lines 214-300+
   (only skimmed the tail past `as_Uco`/`as_UcoT`, but the pattern is
   established by line 300):
   - **`{Prefix}CoefficientData sa`** — the curve/coefficient layer:
     `coeff_c0..c4` (curve coefficients), `coeff_ua0/ua1/va0/va1`
     (anchor Mumford pair), `coeff_hf`/`coeff_hMumfordTarget` (the two
     linking facts). Small, and — worth checking before writing five
     copies — plausibly IDENTICAL across all seven variants (nothing
     in this layer looks anchor/target-construction-specific), in
     which case it may not need a `{Prefix}` at all, just one shared
     `CoefficientData sa` every bundle-pair reuses.
   - **`{Prefix}ReductionData sa`** — small, just `coeffs :
     {Prefix}CoefficientData sa` plus `hReducedClass` (the
     `sa.reducedClass = sa.alpha • aClass - toJacobian D (...)`
     identity). Also plausibly IDENTICAL across variants — this
     identity doesn't mention `Ra`/`Ra2`/tangency at all, it's about
     `sa.P1,sa.P2,δ₀` only, same in every branch (confirmed: this is
     exactly `hReducedClass`'s own statement in the split/cross
     theorems' flat signatures too, word for word).
   - **`{Prefix}AssemblyData sa`** — the large tier, ~35+ fields,
     genuinely construction-specific (this is where `caInterpMatrix`
     vs. `caTangentInterpMatrix` vs. `caCrossInterpMatrix`'s differing
     free-point counts show up: `as_Ra`/`as_Ra1,as_Ra2`/`as_RaX,as_Ra2X`
     etc. per variant). `as_q`/`hq` (the dispatcher-conclusion-relevant
     field) lives here, third field from a natural reading order but
     genuinely mid-list positionally (line 279-281) — not fixed at the
     start or end, so don't assume a fixed slot when writing the other
     five.

   **Checked directly, this pass — partially confirmed, one real
   asymmetry found.** Diffed `TangentTargetCoefficientData`/
   `TangentTargetReductionData` (lines 189-222) against `TangentData`'s
   own (lines 214-247):
   - **`ReductionData` layer: IDENTICAL**, confirmed word-for-word —
     both are exactly `coeffs : {Prefix}CoefficientData sa` plus the
     same `hReducedClass` statement (`sa.reducedClass = sa.alpha •
     aClass - toJacobian D (single sa.P1 + single sa.P2 - 2•single
     δ₀, ...)`, same proof term `sampleP1P2_sub_two_delta_mem sa` in
     both). **One shared `ReductionData sa` structure genuinely
     suffices for all seven** — nothing here is anchor/target/cross
     specific.
   - **`CoefficientData` layer: NOT identical — one field differs.**
     `TangentCoefficientData` (the ANCHOR-tangent file) has
     `coeff_hMumfordTarget : IsMumfordTarget4 ...`;
     `TangentTargetCoefficientData` (the TARGET-tangent file) has
     `coeff_hMumfordUa : IsMumfordUa ...` instead — the opposite side's
     Mumford fact. Everything else in this layer (`coeff_c0..c4`,
     `coeff_ua0/ua1/va0/va1`, `coeff_hf`) is identical between the two.
     Reading why: each file only names the Mumford fact for the side
     it DOESN'T make tangent (`_tangent` doubles the anchor, so needs
     `IsMumfordTarget4` fixed as ordinary data; `_tangent_target`
     doubles the target, so needs `IsMumfordUa` fixed instead) — a
     real, meaningful asymmetry, not an accidental omission. **Two
     honest options for the dispatcher's shared layer**: (a) one
     `CoefficientData` with BOTH `coeff_hMumfordUa` AND
     `coeff_hMumfordTarget` fields (a superset — costs nothing to
     supply both even where only one was previously required, since
     `hMumfordUa`/`hMumfordTarget` are themselves just `Prop`s the
     caller proves once), used uniformly by all seven; or (b) keep
     `CoefficientData` variant-specific after all, just for this one
     field. **(a) is almost certainly right** — it's one extra field
     to prove, not new proof content (both facts are already
     independently available to any real caller, since `_tangent`'s
     OTHER hypotheses elsewhere already pin down `ua`'s tangency
     directly, e.g. `hua_eq` in `AssemblyData` — the `CoefficientData`-
     layer Mumford fact is closer to a naming/bookkeeping convenience
     than load-bearing math specific to one branch), and it lets the
     dispatcher's outer `if`/`match` share one coefficient bundle
     across all three levels of the case split rather than needing to
     re-derive or convert between two slightly different
     `CoefficientData` types depending which branch fired.
2. Write ONE shared `CoefficientData sa` (with both
   `coeff_hMumfordUa`/`coeff_hMumfordTarget` fields, per the option-(a)
   finding above) and ONE shared `ReductionData sa` (identical across
   all seven, confirmed) — these replace what would otherwise be seven
   near-duplicate pairs, and every existing `Tangent(Target)?
   CoefficientData`/`...ReductionData` can plausibly be DELETED and
   replaced by the shared version rather than left as redundant
   parallel structures (check this — `_tangent`/`_tangent_target`'s
   own proofs reference `base.coeffs.coeff_hMumfordTarget` etc.
   directly, so the rename needs to reach those call sites too, not
   just the structure definition).
3. Write `SplitAssemblyData` for the base
   `reducedClass_eq_of_isReduction'` theorem (the large,
   construction-specific tier only — reusing the shared
   `CoefficientData`/`ReductionData` from step 2) — it's the one every
   cross variant's own docstring describes as "everything else copied
   ... verbatim" from, so getting its bundle right first gives the
   other four a checked template. Rewrite the base theorem's own
   signature to take `(base : ReductionData sa) (d : SplitAssemblyData
   sa) (hcoeff : ...)` instead of ~100 flat hypotheses (mechanical,
   but confirm nothing downstream currently calls the FLAT version
   before doing this rewrite in place — grepped earlier this pass,
   nothing does, so this is safe). Then write
   `Cross{1,2,3,4}AssemblyData` (four more, construction-specific tier
   only) and rewrite each `_cross{N}` theorem's signature to match,
   using the split theorem's new bundle as the direct template (each
   cross variant's own docstring already itemizes exactly how it
   differs from the split theorem — that itemization is the diff
   against the split bundle's fields too, not just the flat
   signature). Budget a new file given the 1500-line ceiling — likely
   `ReducedClassBundles.lean` (the shared `CoefficientData`/
   `ReductionData` plus all five construction-specific
   `AssemblyData`s together) plus editing the five existing
   `_cross{N}`/split theorem files in place to consume the new
   bundles.
4. Write `CrossCase` and `reducedClassDispatch` itself in a new file,
   importing all seven `AlphaLocusDegreeUniform*.lean` files plus the
   new bundles file. With all seven variants now uniformly bundled
   (two bundles + one `hcoeff`-style consistency hypothesis each) and
   uniformly concluding `sa.reducedClass + <bundle>.as_q = ...`, the
   dispatcher's own signature and `by_cases`/`match` body should be
   close to what's sketched above, modulo threading which bundle type
   each branch of the `match`/`if` expects.
5. REPL-test (Claire) — steps 2-3's bundle rewrites are the part most
   likely to surface friction (existing proofs inside each theorem
   reference flat hypothesis names directly; bundling means touching
   every internal `have`/`rw` that used e.g. `h1P1` to instead use
   `bundle.h1P1` or a local `have h1P1 := bundle.h1P1` shim at the top
   — mechanical but genuinely touches already-proved code, unlike the
   pure-addition pattern most of this project's prior passes have
   used). Step 4's dispatcher body itself should be comparatively
   easy — new code, not edits to proven code — once 2-3 are green.
6. Once green: this is the actual endpoint the parent roadmap's
   module docstring named at the very top
   (`ROADMAP-cawitness-tangent-interpolation.md`'s "Endpoint" — though
   note that doc's stated endpoint was narrower, about
   `dvd_pairNormBCA_full`'s hypotheses specifically; THIS dispatcher is
   the broader, actually-useful endpoint of the whole tangent-case
   effort, giving every one of the seven theorems a real caller for
   the first time).

**Risk flag for step 2-3, worth Claire's attention before starting**:
bundling means editing five theorems whose proofs are currently
complete and green. Per the project's own conventions, this is exactly
the kind of change worth doing carefully/incrementally (one theorem's
bundle-rewrite, REPL-confirmed, before starting the next) rather than
all five at once, so a mistake in, say, the split theorem's bundle
fields doesn't get compounded into four cross-variant copies before
being caught.

## Status update (this pass)

**Step 2-3 DONE, REPL-confirmed green, 0-`sorry`.** `ReducedClassBundles.lean`
now holds the shared `CoefficientData` (superset, both
`coeff_hMumfordUa`/`coeff_hMumfordTarget` fields — option (a) from the
"Bundling" section above, confirmed landed) and shared `ReductionData`,
plus `SplitAssemblyData`/`reducedClass_eq_of_isReduction'` (bundled base
theorem). All four cross variants are bundled and green as their own
files — `ReducedClassBundlesCross{1,2,3,4}.lean`, each with its own
`Cross{N}AssemblyData` and `reducedClass_eq_of_isReduction'_cross{N}`
(bare name, matching the base theorem's own naming, not a flat/bundled
suffix pair). Confirmed all five bundled theorems now take exactly
`(base : ReductionData sa) (d : Cross{N}AssemblyData sa) (hcoeff : ...)`
plus the same `hcur/hgcd/hcurT/hgcdT/hr/hdeg/hD` tail every variant
shares, uniformly concluding `sa.reducedClass + d.as_q = toJacobian D ...`.

**Naming convention, confirmed uniform across all five bundle files,
one fix made along the way**: `Cross{1,2,3}`'s own source files
(`AlphaLocusDegreeUniformCross{1,2,3}.lean`) already named their
pre-existing flat theorem `..._cross{N}_flat`, leaving the bare
`..._cross{N}` name free for the bundled version. `AlphaLocusDegreeUniformCross4.lean`
did NOT follow this convention — its flat theorem used the bare name,
which collided when `ReducedClassBundlesCross4.lean` tried to declare
its own bundled theorem under the same bare name in the same namespace.
Fixed by renaming the SOURCE file's flat theorem to
`reducedClass_eq_of_isReduction'_cross4_flat` (confirmed zero callers
before renaming), rather than giving the new bundled theorem an
off-convention suffix — all five bundled theorems now share the exact
same `..._cross{N}` bare-name pattern the base theorem
(`reducedClass_eq_of_isReduction'`) also uses, with no exceptions.

**P1/P2 ordering — a real, recurring bug class this pass surfaced, worth
flagging for future bundle-writing (tangent/tangent_target unification,
if attempted, or any future bundle file)**: `SplitAssemblyData`/`Cross{1,2,3}`
were all written assuming `ReductionData.hReducedClass`'s literal term
order (`single sa.P1 + single sa.P2`, P1 first). **Correction, checked
directly rather than left as an assumption**: `AlphaLocusDegreeUniformCross{1,2}.lean`'s
own unbundled source files ALSO use `sa.P1 + sa.P2` throughout (grepped
directly, this pass, to confirm before writing this note) — so `Cross1`/
`Cross2`'s bundles needed no reordering at all, and only ONE of the four
cross variants' own source files disagrees: `AlphaLocusDegreeUniformCross4.lean`
states its internal `hReducedClass`/`aP2P1Nι`/`hN2`/`hcoe` bookkeeping
with the OPPOSITE order (`sa.P2 + sa.P1`), self-consistently within that
file. (`Cross3`'s two REPL-caught bugs this pass were NOT a source-order
mismatch — `Cross3`'s own source, per the module docstring's live
"Sanchor_eq_of_anchor_roots"/point-argument order, agrees with the shared
convention; those two bugs were transcription slips made while hand-writing
the bundle, not a source-file disagreement to check for. `Cross4`'s is
the one genuine source-order disagreement.) This is harmless in the
unbundled theorem (everything there agrees with itself) but becomes a live

footgun the moment a bundle reuses the SHARED `ReductionData` — every
P1/P2-order-sensitive line has to be checked against the shared
struct's actual stated order, not copied verbatim from the source
file's own (possibly opposite) convention. Two concrete instances of
exactly this mistake were caught and fixed only via REPL round-trips
this pass (`Cross3`'s `hSanchorSum`/`hcoe` term order, then its `hN2`
term order, in two separate build attempts) before `Cross4` got the
same check applied proactively. **Any future bundle-writing pass should
diff the target source file's own `hReducedClass`/`aP2P1Nι`/`hN2`/`hcoe`
literal term order against `ReducedClassBundles.lean`'s
`ReductionData.hReducedClass` BEFORE transcribing those four `have`/`set`
blocks, not after a build failure surfaces it** — cheaper to check once
up front than to burn a REPL round-trip per swapped pair.

**Still open — the two tangent-axis variants remain unbundled onto the
SHARED types.** `_tangent`/`_tangent_target` were already bundled
before this pass began, but onto their OWN
`TangentCoefficientData`/`TangentReductionData`/`TangentAssemblyData`
and `TangentTarget`-prefixed counterparts respectively — NOT onto
`ReducedClassBundles.lean`'s shared `CoefficientData`/`ReductionData`.
Confirmed by direct read this pass: `TangentCoefficientData` carries
only `coeff_hMumfordTarget` (no `coeff_hMumfordUa`), the mirror image of
`TangentTargetCoefficientData`'s own `coeff_hMumfordUa`-only field —
exactly the asymmetry the "Bundling" section above already diagnosed
and proposed fixing via the shared type's now-landed superset. This
unification (rewire `_tangent`/`_tangent_target` to take the shared
`CoefficientData`/`ReductionData` instead of their own, deleting the
four now-redundant `Tangent(Target)?CoefficientData`/`...ReductionData`
structs) is NOT required for the dispatcher to work — a `match`/`if`
dispatcher can call seven theorems with seven different bundle-argument
shapes just fine, it only loses the ability to share one coefficient
bundle across all three branches of the OUTER `if` (per "Proposed
shape" above). Recommend treating this as optional cleanup, not a
dispatcher blocker — worth doing if the dispatcher's own signature
gets awkward without it, safe to skip otherwise.

**Not started: `CrossCase` and the dispatcher itself (step 4).** No
`reducedClassDispatch` or `CrossCase` definition exists anywhere in the
codebase yet (confirmed by grep, this pass). This is the actual
remaining work — see "Next steps" immediately below.

## Next steps

1. **Write `CrossCase` as its own small inductive**, per the "Proposed
   shape" section above — four `some`-style constructors
   (`cross1`/`cross2`/`cross3`/`cross4`, each carrying the one
   `H.Point`-level identity the corresponding bundled theorem's own
   `hP1eq`/`hP2eq`-shaped hypothesis needs) plus `generic` (carrying the
   four `h1P1,h1P2,h2P1,h2P2`-shaped nondegeneracy hypotheses
   `SplitAssemblyData` itself already has as fields — check field names
   directly against `SplitAssemblyData` before writing this, don't
   assume they still match the roadmap's original sketch verbatim).
   Small, new code — low risk, good first step.
2. **Write `reducedClassDispatch` itself**, outer `if hRa : Ra1.X = Ra2.X
   then ... else if hT : sa.P1.X = sa.P2.X then ... else match cc hRa hT
   with ...`, per "Proposed shape." Each branch's `exact` call is one of
   the seven now-bundled theorems (`reducedClass_eq_of_isReduction'`,
   `_tangent`, `_tangent_target`, `_cross{1,2,3,4}`), each taking its own
   bundle-argument shape — since tangent/tangent_target are NOT unified
   onto the shared bundle (see above), the dispatcher's own signature
   needs to take all seven bundle types as separate arguments (or
   existentially-wrapped ones per branch), not a single shared bundle
   parameter. Confirm the `d.as_q`/`base.hReducedClass`-shaped conclusion
   mismatch flagged in "Concrete signature sketch" above (five variants
   conclude with a bare `q`, `_tangent_target` — and now, since it's
   bundled the same way, `_tangent` — conclude with `d.as_q`) still needs
   resolving at this step; it was flagged, not resolved, by this pass.
3. **New file** for both (`ReducedClassDispatch.lean` or similar),
   importing all seven `AlphaLocusDegreeUniform*.lean` files plus
   `ReducedClassBundles.lean` and `ReducedClassBundlesCross{1,2,3,4}.lean`.
   Well under the 1500-line ceiling — the dispatcher body itself should
   be short (new code, not edits to proven code, so no reason to expect
   the same per-line proof weight as the bundle files).
4. **REPL-test incrementally**: get the outer `if`/`if` skeleton
   type-checking first with the two tangent-axis branches (simplest,
   since they need no `CrossCase` match), then add the `CrossCase`
   match and its four branches one constructor at a time — mirrors this
   pass's own "one file, one REPL round-trip" discipline, which caught
   the two P1/P2-ordering bugs and the Cross4 naming collision
   individually rather than compounding them.
5. Once green: this is the roadmap's actual endpoint (see original
   step 6 above) — every one of the seven `reducedClass_eq_of_isReduction'`
   variants gets a real caller for the first time.

