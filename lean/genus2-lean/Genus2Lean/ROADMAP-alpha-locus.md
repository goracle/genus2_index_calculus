# Roadmap: proving eq 1 is 0-dimensional *uniformly in `(alpha,alpha')`* —
# why this is the real target, and how it closes the 8th-moment gap

## TL;DR (supersedes the previous version of this roadmap)

The previous version of this roadmap treated "is the matching system
0-dimensional" (Question 1 in advisory-6/7 §6.3) and "is `E(S,S)` small
enough" (Question 4, the 8th-moment gap) as unrelated questions, connected
only by loose analogy. That was wrong, and it came from an incorrect
mental model of what `X(Delta)` is a union over.

**Corrected picture.** Eq 1 —

    [P1]+[P2] - alpha*a = [P3]+[P4] - alpha'*a      (eq 1)

— is one equation in the four unknowns `P1,P2,P3,P4` (equivalently, in
Mumford-coordinate form, the twelve unknowns
`wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1` that
`DecoupledSystemRegular.lean`'s `decoupledSystem` actually encodes), for
**fixed** `alpha,alpha'`. `U0,U1,V0,V1` are not free/chosen — they are
*derived from* whichever `P1,P2` (resp. `P3,P4`) solve the equation; you
do not get to pick them independently and then ask which points hit them.
So the solution variety `V(alpha,alpha')` — as a subset of `C x C x C x C`
(or its Mumford-coordinate encoding) — is *the entire set* of 4-tuples
satisfying eq 1 for that `(alpha,alpha')`, and

    X(Delta) = #{ (P1,P2,P3,P4) in F^4 : eq 1 holds for alpha,alpha' with
                   alpha - alpha' = Delta }
             = #{ F-rational points of V(alpha,alpha') that lie in F^4 }
             <= #{ all points of V(alpha,alpha') }
             = deg(alpha,alpha')

directly, with no extra union or fiber-counting step: `X(Delta)` is
literally counting points of the *same* variety `decoupledSystem` cuts
out, intersected with `F^4`, not points of a different collection of
varieties (one per choice of `P1,P2`). If `deg(alpha,alpha') = O(1)`
**uniformly**, i.e. bounded by a constant independent of `p` (and of the
specific `alpha,alpha'`, outside a genuinely small — not just
codimension-1-but-possibly-huge — exceptional set), then `X(Delta) = O(1)`
for every `Delta` in that range, and:

    B^4 = sum_Delta X(Delta)  <=  O(1) * #{Delta : X(Delta) > 0}
    ==>  #{Delta : X(Delta) > 0} = Omega(B^4)

which is *more* than enough hit-density for (H0)/(4) — it gives the
density bound directly, with no Cauchy-Schwarz loss, no Sidon-set theory,
no Fourier uniformity argument, and no Shkredov higher-energy dichotomy.
**A genuinely uniform degree bound on `decoupledSystem`'s solution variety,
across the relevant range of `(alpha,alpha')`, closes advisory-6/7's
Question 4 outright, by a two-line counting argument, not by anything in
section 7.**

This reclassifies what was previously called "Question 3" (uniform
fiber-degree stability, §6.3) from a downgraded "detail" back to the single
highest-value target in the whole project: it is not a nice-to-have that
completes Question 1's genericity, it is *the* thing that resolves the
8th-moment blocker, PROVIDED it can be shown to hold uniformly rather than
at one sampled `(alpha,alpha')` instance. Section 7's entire Sidon/Fourier
apparatus becomes unnecessary once this is established (though it doesn't
retroactively become wrong — it would just no longer be the load-bearing
argument).

**What this document is not claiming**: it is not claiming the uniform
degree bound is already proved. `theData`/`decoupledSystem_isRegularSequence`
currently prove regularity for a *fixed* `sa, sb : SampleTarget` — i.e. a
fixed target `(u0,u1,v0,v1)` pair, with no `alpha` field connecting that
target back to which `(alpha,alpha')` produced it, and no statement yet
about the degree being constant as `(alpha,alpha')` varies. Turning
"regular sequence for one fixed target" into "degree bound uniform across
the (alpha,alpha')-parametrized family of targets" is genuinely new work,
not a relabeling of what's already on file. The rest of this document is
the plan for that work.

## Why the earlier "birationality vs. 8th moment, unrelated" framing was wrong

Advisory-6/7 §6.2's own retraction ("RETRACTED: why this track does NOT
make section 7's variance work moot") argued that `X(Delta)` and the
fiber-degree of `sigma : C^(2) -> J` are counts of different objects over
different domains, with no shown relationship. That argument implicitly
assumed the relevant "fiber" was `sigma`'s fiber over a *fixed target
divisor class* `D`, and objected that summing such fibers over the `~B^2`
choices of `(P1,P2) in F^2` (each producing a different `D`) does not
reduce to one bounded quantity.

That objection is correct *for that specific mental model* — but it is
answering a question `decoupledSystem` does not actually ask. Eq 1's
matching system does not fix `D` and then search for `(P3,P4)`; it fixes
only `alpha,alpha'` and solves for **all four points at once**,
`P1,P2,P3,P4` fully free. `X(Delta)` is therefore literally the
`F^4`-rational-point-count of `decoupledSystem`'s own solution variety at
that `(alpha,alpha')` — not a union of `B^2` separate fiber counts, one
per `(P1,P2)`. There is exactly one variety per `(alpha,alpha')`, and
`X(Delta)` is bounded by its degree directly. The union-of-fibers picture
was a mistranslation of what "0-dimensional" was a claim about, introduced
partway through the discussion that produced the previous version of this
roadmap, and it should be discarded.

(For the record, the earlier "toy counterexample" involving `Delta=0` and
`X(0)=E(T,T)` is not actually a counterexample to the corrected claim
either: `E(T,T) = O(B^2)` is consistent with `decoupledSystem`'s solution
variety at `alpha=alpha'` — i.e. `Delta=0` — being highly *degenerate*, not
0-dimensional at all, since `alpha=alpha'` forces `[P1]+[P2]=[P3]+[P4]`,
which includes the entire diagonal `{P3,P4}={P1,P2}` as solutions for
*every* choice of `P1,P2` — a positive-dimensional family, not a
finite variety. This is expected and unproblematic: `Delta=0` is
*exactly* the kind of special value the uniform bound needs to either
exclude from its range, or handle separately with its own — still
finite, but different — accounting. It is not evidence against
uniform-in-generic-Delta 0-dimensionality; if anything it is a concrete
first example of the "exceptional set" the uniform bound needs to name
explicitly.)

## What's actually in the files (updated this pass — the previous version's
## file-location and sorry-status claims for `DecoupledSystemRegular.lean`
## were stale; see `ROADMAP-regular-sequence.md`'s current-status section
## for the full audit this summarizes)

- **`DataDerivationBasics/Tower/Solve/Mumford.lean`**: builds `theData`,
  i.e. `(uRS, vRS)`, as a tower construction over symbolic anchors, for
  one sample. Curve-and-anchor data only; no `alpha` anywhere.
  `DataDerivationMumford.lean` (the piece of this chain re-audited this
  pass) is essentially complete — `uRS_monic`, the Mumford identity, and
  the `towerToRdec` bridge are all proved, no `sorry`.
- **`DecoupledSystemRegular.lean`**: `Idx` is the 12-variable list.
  `SampleTarget` is `(u0,u1,v0,v1)` with **no `alpha` field, no `P1,P2`
  field** — it is agnostic to how the target arose, exactly as before.
  **`decoupledSystem_isRegularSequence` and `decoupledSystem_zeroDimensional`
  no longer live in this file** — both moved to `AlphaLocusDegreeUniform.lean`
  (see below), cleanly, with a pointer docstring left in their old spot.
  `theData`'s own assembly in this file is fully wired, no `sorry`. There
  is still nothing in this file that quantifies over `alpha,alpha'` — that
  remains exactly the gap this roadmap is about.
- **`AlphaLocusDegreeUniform.lean`** (new since the previous version of
  this roadmap; supersedes the old plan of adding `alpha` machinery
  directly to `DecoupledSystemRegular.lean`): the actual current home of
  `decoupledSystem_isRegularSequence` (fixed-target case — **proved, no
  `sorry`**, a one-line term proof delegating to
  `PeelChainAssembly.lean`'s `regularSeq_of_peel_chain`) and
  `decoupledSystem_zeroDimensional` (fixed-target `IsRegular →
  Module.Finite` corollary — **still `sorry`**, a separate Mathlib-API
  gap unrelated to the regular-sequence content). Also the current home
  of `decoupledSystem_degree_uniform` — the actual target theorem this
  roadmap is about — stated but `sorry`, exactly per Steps 1-2 below not
  having landed yet, and `SampleTargetFromAlpha`, task (A)'s
  `alpha`-parametrized extension of `SampleTarget`, with `isReduction`
  still an assumed `Prop` field rather than a constructed witness (task
  (A) itself, still open — see Step 1).
- **`genus2-index-calculus-advisory-6.md`**: has eq 1, has `alpha,alpha'`,
  has the `D~K_C` locus (§6.2) as the exceptional set for *single-instance*
  finiteness (Question 1), and has Question 3 (§6.3) — uniform degree
  stability across `(alpha,alpha')` — explicitly filed as open but
  downgraded to "detail, not fatal." Per the corrected picture above,
  that downgrade should be reversed: Question 3, correctly proved, IS
  the resolution to Question 4 (§7's entire 8th-moment apparatus). Not
  re-read this pass; status as of the last check.
- **`LCanonicalElementary.lean`**: has `mumfordB`, the concrete two-point
  Mumford reduction — the bridge lemma needed to state eq 1 in terms of
  literal curve points at all, still only for the un-shifted `Q1+Q2`
  case, not the `alpha`-shifted `[P1]+[P2]-alpha*a` case. Not re-read
  this pass.
- **`RiemannRochGenus2.lean`**: has `finrank_L_canonical`/`L_pair`
  machinery, the toolkit `D~K_C` (and any degree-jump-locus argument)
  would be built from. Not re-read this pass.

## The actual target theorem, stated precisely

The object to prove is not "does `decoupledSystem` have a small solution
set for one `(alpha,alpha')`" (already the target of
`decoupledSystem_zeroDimensional`, still `sorry`, but scoped correctly) —
it is the **uniform-in-`(alpha,alpha')` strengthening**:

```
theorem decoupledSystem_degree_uniform :
    ∃ (d : ℕ) (Bad : Set (F ell × F ell)),  -- exceptional locus, TBD what it is
      -- Bad is "small" in a sense to be pinned down (finite? measure zero
      -- in an appropriate sense over F ell? this needs its own definition --
      -- see Step 2 below) AND
      ∀ alpha alpha' : F ell, (alpha, alpha') ∉ Bad →
        <the F_p-rational points of decoupledSystem's variety, built from
         alpha, alpha' via the SampleTarget-from-alpha layer that does not
         yet exist -- see Step 1 below> has cardinality ≤ d
```

Two things are needed before this can even be *stated* in Lean, let alone
proved, matching the two tasks (A) and (B) the previous roadmap version
identified — both still correct, now with the added weight that (A)+(B)
together are the actual resolution to the 8th-moment gap, not a side
quest:

**(A) `SampleTarget` needs an `alpha` field.** Currently `SampleTarget` is
just `(u0,u1,v0,v1)`; there is no way to even ask "as `alpha` ranges over
`F ell`, does the resulting target's system degree stay bounded" because
`alpha` is not a Lean object connected to `SampleTarget` at all. This
needs the `Reduce(alpha*a - P1 - P2)` construction from the previous
roadmap's task (A) — porting whatever Cantor-reduction code the
Julia/Oscar pipeline already runs, not re-deriving it. This is *necessary
infrastructure* for stating the degree-uniformity theorem, not optional
polish.

**(B) The exceptional set `Bad` needs an actual definition and an actual
bound on its size**, not just "codimension 1" or "measure zero" as an
informal gesture — because for the counting argument above to give a
useful density statement, `Bad` needs to be small in a sense that composes
with the `B^4 = sum_Delta X(Delta)` identity: specifically, `Bad` needs to
occupy `o(p^2)` of the `~p^2` possible `Delta` values (or, better, an
explicit small count), not merely "positive-dimensional locus in an
algebraic-geometry sense" — the two notions of "small" are not
automatically the same once you're asking a question over `F_p`-points
rather than over `C`. `D ~ K_C` (§6.2's exceptional locus for Question 1)
is a natural *candidate* for (part of) `Bad`, but as the previous roadmap
version already flagged, whether it's the same set as wherever the degree
actually jumps has not been checked, and now matters more than before:
if `Bad` turns out to be large in the `F_p`-point-count sense (even if
it's "measure zero" over `C`), the counting argument's conclusion weakens
and the 8th-moment problem is not actually closed.

## Proposed roadmap, in order

### Step 0 — DONE, no longer needed as a step

The previous version of this roadmap opened with reconciling two
divergent copies of `DecoupledSystemRegular.lean` (an uploaded one vs. a
stale copy bundled in `bridge.zip`). That concern is now moot: this
session's working files are a single clean import chain
(`DataDerivationMumford` → `DecoupledSystemRegular` →
`PeelChainAssembly` → `AlphaLocusDegreeUniform`, confirmed directly from
each file's own `import` lines this pass) with no duplicate definitions
found anywhere in it. Left here, struck from "to do," rather than
silently deleted, so a future reader doesn't wonder whether the
reconciliation ever happened.

### Step 1: build task (A), the `alpha`-parametrized `SampleTarget`

Add `alpha : F ell`, `P1 P2 : H.Point` (or whatever the curve-point type
is) to `SampleTarget`, plus a field asserting `(u0,u1,v0,v1)` really is
the Mumford reduction of `[P1]+[P2] - alpha • a`. The hard part, as
before, is porting `Reduce` (general Cantor reduction of a divisor class
down to its degree-2 effective Mumford form) from whatever the Julia
pipeline already computes — check `01_elim2_main.jl` / the sample-spec
generation code for the exact algorithm rather than rederiving it.

**Located and read this pass**: `phi_general.zip`
(`07_build_phi_general.jl`, `09_residual_and_modinv.jl`,
`10_root_finding.jl`, `trial3_phi_symbolic_unified.jl`'s
`symbolic_residual`) is exactly this code, general in `K` (not
`elim2`-specific). The recipe: interpolate a cubic
`phi(x,y)=E(x)+y*Y(x)` (normalized `y`-coefficient `1`, matching
`mumfordB`'s existing convention) through the `K` source-divisor points
AND the two "Mumford rows" pinning it to the target `(u0,u1,v0,v1)`
simultaneously (a `(K+2)x(K+2)` linear solve); form
`N(x)=E(x)²-f(x)Y(x)²` (this is `phi(x,y)*phi(x,-y)`, i.e. intersecting
`{phi=0}` with the curve via `y²=f(x)`); divide `N` exactly by the known
anchor factors and by the target's own `u(x)`; the quotient `u_RS(x)`
(degree 2 for `K=2`, root-found via `_solve_quadratic_roots!`) and
`v_RS(x) = -E*Y^{-1} mod u_RS` are `Reduce`'s output. Recorded at this
level of detail in `AlphaLocusDegreeUniform.lean`'s module docstring
("`Reduce`'s actual algorithm, now on file" section) so a porting attempt
has the recipe rather than needing to re-read the Julia source cold.
**Not ported** — this only answers "what does `Reduce` have to compute,"
not "here is the Lean `def`"; the actual port (§4's tower/field-instance/
exact-divisibility work, same shape as `ROADMAP-regular-sequence.md` §4.2's
`theData` port) is unstarted.

This step is now higher-priority than it was in the previous roadmap
version: it used to be filed as "only needed for connecting `theData`
back to the walk/collision-search code... not a blocker for
`decoupledSystem_isRegularSequence` itself." That framing is superseded —
it *is* now a blocker, specifically for stating
`decoupledSystem_degree_uniform` at all, which is the theorem that
actually closes the 8th-moment gap.

### Step 2: pin down what "uniform" and "small exceptional set" mean,
concretely, over `F ell` / `F p` — before attempting the proof

This is new relative to the previous roadmap version, and is the step
most likely to surface a hidden difficulty. Candidates to check, cheaply,
in Julia/Oscar first (same spirit as the previous roadmap's Step 1 "settle
on paper first" — that instinct was right, only the specific question to
settle has changed):

- Generate several independent `(alpha,alpha')` pairs (not just the one
  instance already solved), run the same numerical-irreducible-decomposition
  pipeline (`HomotopyContinuation.jl`) advisory-6/7 §6 already used, and
  record the witness-point count `d` for each. If `d` is exactly the same
  small number every time (as it was for the single instance already run:
  degree-1 components throughout), that's fast, decisive, encouraging
  evidence for uniformity — genuinely worth doing, not as a "stupid"
  detour but as the cheap check that tells you whether Step 3's Lean proof
  is even going after a true statement before investing in it.
- Separately, and however that check comes out: explicitly compute, for a
  grid or sample of `alpha'` (fixing `alpha`, or vice versa), whether
  `D ~ K_C` (§6.2's locus) correlates with a jump in `d` — i.e. actually
  do the check §6.2's own "practical steps" and the previous roadmap's
  Step 1 proposed, but now explicitly in service of bounding `Bad`'s size
  as a subset of `F ell`, not merely settling a curiosity about which
  locus is "correct."
- Count how large the flagged-bad set is *as a fraction of `F ell`*
  (not just "does it have positive dimension over `C`") for the specific
  `ell` in use. This is the number that actually determines whether the
  counting argument in the TL;DR gives a useful bound or a vacuous one.

### Step 3: state and prove `decoupledSystem_degree_uniform` in Lean

Once Steps 1-2 give you (a) the `alpha`-parametrized `SampleTarget` and
(b) a concrete, checked candidate for `Bad` with a known size bound,
state the theorem as in "The actual target theorem" above and attempt
the proof. The proof strategy most consistent with what's already
built: extend `decoupledSystem_isRegularSequence`'s existing
regular-sequence machinery (already proving 0-dimensionality generator-
by-generator for one fixed target) to track how the regular-sequence
witnesses' degrees behave as the target varies over the
`alpha`-parametrized family — likely via showing the relevant resultants/
discriminants in the peel-chain construction (`regularSeq_of_peel_chain`,
`Nondegenerate`, `CrossNondegenerate`, and — new since the previous
version of this roadmap — `PeelChainNondegenerate`, the hypothesis
bundle `regularSeq_of_peel_chain` now also depends on; see
`ROADMAP-peel-chain-assembly.md`) are themselves polynomial in
`alpha,alpha'` of bounded degree, so that "degree jumps" can only happen
on their vanishing locus — which is exactly the kind of set `Bad` needs
to be, and connects back to Step 2's numerical check directly.

### Step 4: revisit `genus2-index-calculus-advisory-6.md` once Step 3 lands

If `decoupledSystem_degree_uniform` goes through with a `Bad` of provably
small size, section 7 of the advisory (Sidon-set Fourier uniformity,
Shkredov's higher-energy dichotomy, the whole `E(S,S)` apparatus) is no
longer the load-bearing argument for the complexity claim — it can be
kept as an independent/backup argument or retired, and the advisory
should be updated to state the counting argument from this roadmap's
TL;DR as the actual proof of (H0), with Step 3's theorem as its citation.

## What NOT to do

Don't treat "generate one more numerical instance and eyeball whether the
degree looks the same" (Step 2's first bullet) as a *substitute* for
Step 3's actual Lean proof — it's a cheap, valuable sanity check that
tells you whether you're chasing a true statement, not a replacement for
proving `Bad` is genuinely small. And don't restart
`DataDerivationBasics.lean`/`DataDerivationTower.lean`/
`DataDerivationSolve.lean`/`DataDerivationMumford.lean`/
`DecoupledSystemRegular.lean` from scratch in favor of a "cleaner"
birationality-only argument: that machinery (the tower construction, the
regular-sequence peel-chain, `Nondegenerate`/`CrossNondegenerate`) is
exactly the toolkit Step 3 needs to extend, not a detour from it. The
single-instance regular-sequence proof and the uniform-in-`alpha`
strengthening are the same proof, one step short of where it needs to go
— not two different approaches where you'd pick one and discard the
other.
