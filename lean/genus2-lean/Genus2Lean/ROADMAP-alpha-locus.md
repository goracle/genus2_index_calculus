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

## Update (this pass): Step 1 ("port `Reduce`") scoped precisely — real
## progress on WHAT to build, held before any Lean editing per Claire's
## explicit instruction this pass

**This pass did no `.lean` editing at all** — `AlphaLocusDegreeUniform.lean`
is byte-for-byte unchanged from the previous pass. What follows is
planning/scoping work only, done specifically so the next pass that
resumes Lean editing has a concrete, checked plan rather than the vague
"port whatever the Julia pipeline computes" instruction Step 1 previously
carried. **Files now on hand for that next pass, not previously
available in-session**: `DataDerivationBasics.lean`,
`DataDerivationSolve.lean`, `DataDerivationTower.lean` (uploaded this
pass, alongside the already-had `DataDerivationMumford.lean`) — these are
the four files `curBeforeMonic`/`Epoly`/`Ypoly`/`Npoly`/`uRS`/`vRS` (the
K=2 symbolic-anchor machinery) actually live across; only `Mumford` was
available in earlier passes, which is why `curBeforeMonic` etc. could
only be discussed at the docstring level, not read directly, until now.
`phi_general.zip` (`07_build_phi_general.jl`, `09_residual_and_modinv.jl`)
was also fetched and read directly this pass (previously only
paraphrased secondhand in the roadmap and in `AlphaLocusDegreeUniform.lean`'s
module docstring) — the recipe below is read off the actual source, not
inferred from an earlier summary of it.

### `alpha • a` is NOT computed by `Reduce` — resolved, changes the shape of task (A)

**Confirmed directly with Claire.** `a` is not a simple curve point — it's
the DLP subgroup generator, itself a genus-2 Mumford divisor with two
support points (i.e. `a` is already a `(u_a, v_a)` Mumford pair, degree 2,
same shape as `SampleTarget`'s own `(u0,u1,v0,v1)`). `alpha • a` (the
scalar multiple in the Jacobian) is computed **offline, by the user**, via
whatever Cantor/group-law doubling code produces the DLP problem
instances in the first place — it is handed to `Reduce` as an input
Mumford pair, not something `Reduce` derives from `alpha : ℤ` and `a`
from scratch. This resolves what looked like a missing piece
(`phi_general.zip` has no Cantor-doubling code anywhere in it, confirmed
by grep this pass) — that code was never supposed to be part of this
port; it lives upstream, outside this project's scope, exactly like the
DLP instance generation itself.

**Consequence for `SampleTargetFromAlpha`'s design** (not yet
implemented, since no `.lean` editing happened this pass, but now
concrete): `Reduce`'s real signature is closer to

    Reduce (u_a v_a : F p) (P1 P2 : F p × F p) : F p × F p × F p × F p

i.e. it takes `alpha•a`'s ALREADY-REDUCED Mumford pair `(u_a,v_a)` plus
two concrete curve points `P1,P2`, and produces the reduced
`(u0,u1,v0,v1)` for `alpha•a - P1 - P2`. It does NOT take `alpha : ℤ` and
`aClass : Jacobian H D` and compute a scalar multiplication internally —
`SampleTargetFromAlpha.reducedClass`'s current `zsmul`-based construction
(`alpha • aClass - ...`) is mathematically fine as a SPECIFICATION of
which divisor class is being reduced, but the actual Lean `def Reduce`
that will someday discharge `isReduction` should be understood as
consuming `(u_a,v_a)` directly, with the connection "`(u_a,v_a)` really is
`alpha•aClass`'s Mumford pair" tracked as ITS OWN separate hypothesis/input
(supplied by whoever calls this file with a concrete `alpha`), not
re-derived. Nothing about `SampleTargetFromAlpha`'s existing field shape
needs to change for this — `alpha : ℤ` and `aClass : Jacobian H D` still
correctly describe WHICH divisor class the target is supposed to reduce,
this note only pins down that `Reduce` the function works from the
Mumford pair, one level down from the abstract Jacobian element.

**Also worth flagging for that exclusion criterion Claire mentioned**:
since `alpha,alpha'` are freely chosen (not sampled/derived), the search
should avoid `alpha`-values whose `alpha•a` support collides with the
factor-base points being drawn from (the "`alpha•a = P1+P2`" degenerate
case, giving a trivial `0=0` solution) — this is a concrete, checkable
exclusion criterion for `Bad` (task (B)) that wasn't on file anywhere
before this pass. It's not the only content `Bad` will need (§6.2's
`D~K_C` locus, already flagged, is a different exceptional condition),
but it's real, mechanical, and worth folding in once `Bad` is actually
defined in Step 2/3.

### The K=4 recipe, read directly off `phi_general.zip`'s actual source (not the earlier paraphrase)

`build_phi_general!` (`07_build_phi_general.jl`) is generic in `K =
length(anchors)`, `nb = K+3` (the `L(K+3•∞)` Riemann-Roch basis size).
For our case: 2 anchor points from `(u_a,v_a)` (`alpha•a`'s pair, handed
in) + `P1,P2` (2 more) = **K=4 anchors**, `nb=7`. The pipeline, confirmed
against the actual Julia source this pass:

1. **Build the RR basis** `rr_basis(7)`, ordered by pole order; locate
   `y_idx` (the position of the `(0,1)` monomial — NOT assumed to be
   `basis[end]`, a bug the Julia source itself flags as the root cause of
   an earlier K=2 failure; the Lean port must locate it the same way,
   not hardcode a position).
2. **One row per anchor** (`K=4` rows; 2 if a repeated/tangent point,
   capped at that — simple points only expected for our case, `P1≠P2`
   generically and `(u_a,v_a)`'s own two roots distinct generically)
   PLUS **exactly 2 "Mumford rows"** encoding `phi(x,v(x)) ≡ 0 mod u(x)`
   for the TARGET pair being reduced against (for a top-level `Reduce`
   this target is the zero divisor / point at infinity, i.e. reducing all
   the way down to `SampleTarget`'s `(u0,u1,v0,v1)` IS the point of the
   whole call — confirm this reading before implementing: `Reduce`'s
   "target" argument in the Julia driver is always the OUTPUT being
   solved for, not a second input divisor, matching `SampleTarget`'s role
   downstream).
3. **`(K+2)×(K+2) = 6×6` linear solve** (Gaussian elimination; `y`'s
   coefficient fixed to `1` by convention, moved to the RHS, hence
   `K+2` unknowns not `K+3`), giving `phi = E(x) + y·Y(x)`.
4. **`N(x) = E(x)² - f(x)·Y(x)²`** (`phi(x,y)·phi(x,-y)`, the norm/
   intersection-with-curve step).
5. **Divide `N` exactly by the 4 known anchor factors** `(x-x_{P1})`,
   `(x-x_{P2})`, and the two roots of `u_a(x)` (or, if `u_a` doesn't split
   over `F p`, by `u_a(x)` itself as a quadratic factor rather than two
   linear ones — **this is a real fork the Julia code's `anchors::NTuple`
   representation glosses over by assuming split anchors; the Lean port
   needs to handle the case `u_a` is irreducible over `F p` explicitly**,
   likely by dividing by `u_a` as a single quadratic factor rather than
   trying to extract two `F p`-points from it — flagged here as NEW, not
   previously identified in any earlier pass of this roadmap).
6. **Divide the result once more by the target `u(x)`** if reducing
   against a nonzero target (per the Mumford-rows step above — for the
   "reduce to `SampleTarget`" top-level call this step may collapse into
   step 5, needs checking once actually implemented).
7. **Quotient is `u_RS`** (degree 2, monic-normalized), **`v_RS := -E·Y⁻¹
   mod u_RS`** — same construction `DataDerivationMumford.lean`'s
   `uRS`/`vRS` already implement, over `K2` (the K=2 symbolic tower); this
   port's job is the SAME arithmetic over plain `F p` for K=4 concrete
   points, not new mathematical content.

### Update (this pass): step 2's "2 if a repeated/tangent point" case —
### CONFIRMED against `phi_general.zip`'s actual reference implementation,
### not designed from scratch. Claire's correction: this is a standard,
### already-solved part of the pipeline, not new mathematics to invent.

**Corrects the previous version of this section.** That version treated
the tangent-anchor row formula and the `m≥3` scoping decision as an open
design question to work out from first principles. It isn't — `06_
monomial_columns.jl`/`07_build_phi_general.jl`/`05_branch_series.jl`
(uploaded and read directly this pass) already implement exactly this,
tested and working, and the port's job is to transcribe that algorithm
faithfully, not invent one. Corrected picture below, read straight off
the source rather than reconstructed from the general theory.

**The reference implementation's actual design, confirmed line-by-line:**

1. **Multiplicity is capped at `m ∈ {1,2}` in the reference code itself**,
   not just as a convenient simplification for this port.
   `build_phi_general!`'s anchor loop asserts
   `occ_count == 1 || occ_count == 2` and errors out explicitly for a
   point occurring 3+ times ("`fill_f_tay!` extended to `f_tay[3..]`... is
   not yet supported"); `_monomial_column!` has the identical cap
   ("only m=1 ... and m=2 ... are implemented; higher-order tangency
   (m>=3) needs ... `F_yy` cross-term handled explicitly"). So the
   triple/quadruple-coincidence question from the previous version of
   this section is already answered by the project's own reference
   pipeline: **not implemented there either**, by explicit design, not
   oversight. This directly confirms (rather than just motivates) this
   roadmap's earlier recommendation to fold `m≥3` into `Bad` rather than
   build third-derivative Hermite conditions — that's what the working
   Julia code that actually runs the DLP walk already does.
2. **Tangency detection**: for anchor `a` in the `K`-tuple, scan
   `anchors[1..a-1]` for an equal RAW point; if found, this occurrence
   gets no row at all (`is_repeat_of_earlier`, `continue`s the loop). The
   FIRST occurrence's own multiplicity `m` is set to
   `occ_count = ` (how many times this point occurs at or after its first
   position) — i.e. one point occurring twice in the tuple produces
   exactly ONE row-block, of size 2, not two separate size-1 row-blocks.
   Translating directly: in `AlphaReduce.lean`'s terms, if `P1 = P2`
   (equal as pairs, not just equal x-coordinate — see point 5 below), the
   anchor list effectively has one fewer occupied "slot," and that slot's
   row-block is the tangent one, not two ordinary evaluation rows (which
   would just make the linear system rank-deficient/singular — exactly
   the bug class `build_phi_general!`'s own header comments describe
   fixing elsewhere in this file for the analogous single-point case).
3. **The `m=2` row-block, exact formula, confirmed from source**:
   - Row 1 (unchanged from `m=1`): the ordinary evaluation row,
     `phi(px,py) = 0`.
   - Row 2 (new): the **first-derivative-along-the-branch** row. For the
     hyperelliptic model `F(x,y) = y² - f(x)`, `fill_f_tay!` computes
     `F_x(px) = -f'(px)` (a plain Horner evaluation of the derivative
     coefficients of `curvePoly`/`f`, no `y`-dependence — confirmed
     directly, `f_tay[2] = -f'(px)` in backend representation). `branch_
     series!` then forms `Fy = 2·py`, `Fy_inv = Fy⁻¹` (so `py ≠ 0` is a
     hard precondition — `build_phi_general!` asserts `py != 0`
     unconditionally for every anchor, not just tangent ones; this is
     exactly the "not a Weierstrass point" nondegeneracy this roadmap
     already flagged as needed and excludable via `Bad`), and computes
     the branch-series derivative `y'(px) = -F_x(px)/F_y(px) =
     f'(px)/(2·py)` — the standard implicit-function-theorem formula for
     `y² = f(x)`, matching exactly what this section's earlier draft
     proposed (`y1' = f'(x1)/(2y1)`), now confirmed rather than derived
     from scratch.
   - Per-column derivative contribution (`fill_monomial_block!`'s m=2
     path, cross-checked in `07_build_phi_general.jl` by an independent
     `i·px^(i-1)` recomputation for every `j=0` column — worth mirroring
     as a Lean-side sanity lemma, see point 6 below): for a pure-`x`
     column `(i,0)`, the derivative-row entry is the ordinary polynomial
     derivative coefficient `i·px^(i-1)` (the `t¹` coefficient of
     `(px+t)^i`'s binomial expansion — no branch-series involvement,
     since this monomial has no `y`). For an `x^i·y` column `(i,1)`, the
     derivative-row entry needs the PRODUCT RULE against the branch
     series: `t¹` coefficient of `(px+t)^i·y(px+t)` is
     `i·px^(i-1)·y(px) + px^i·y'(px)` (both `y(px)=py` and `y'(px)` from
     the branch series above) — this is the genuinely new per-column
     formula relative to the `m=1` case, not a simple reuse of the
     ordinary derivative rule, and it's the piece the previous version of
     this section correctly flagged as needing "the derivative of
     `phi(x,y(x))`," now with the exact product-rule expansion confirmed.
4. **`N(x) = E(x)² - f(x)Y(x)²`'s resulting root structure**: value+
   derivative vanishing of `phi(x,y(x)) = E(x) + y(x)Y(x)` at `x=px`
   (with `y(x)` satisfying the curve relation near `px`) is exactly the
   standard fact that forces `rootMultiplicity px N ≥ 2` — this part of
   the previous version of this section's plan is unchanged and still the
   right target (`Polynomial.rootMultiplicity`,
   `Polynomial.rootMultiplicity_pos`,
   `Polynomial.rootMultiplicity_eq_zero_iff`,
   `Polynomial.prod_multiset_root_eq_finset_root`, confirmed present in
   current Mathlib4 via direct doc search last pass) — nothing in this
   pass's source-reading changes that half of the plan, only confirms the
   row-construction half that feeds it.
5. **One clarification the source reading surfaces that the previous
   version of this section didn't have precisely right**: tangency
   detection in the reference implementation is keyed on the anchor being
   the literal SAME `(px,py)` PAIR (`anchors[prev] == anchors[a]`, a raw
   tuple equality on both coordinates), not merely `P1.1 = P2.1` (same
   x-coordinate). This matters for the hyperelliptic-conjugate case this
   roadmap's `AlphaReduce.lean` status notes flagged earlier
   (`P1`/`P2`'s x-coordinates coinciding but `y`-coordinates being
   `y1 = -y2 ≠ y1`, i.e. the two conjugate points over the same `x`): that
   is NOT tangency in this pipeline's sense at all — it is two perfectly
   ordinary, distinct simple anchors that merely share an x-coordinate,
   still `m=1` each, no derivative row needed. Whatever K=4-specific
   `IsCoprime`-based argument `uRS4_dvd_Npoly4` uses for the "distinct
   points, possibly same x-coordinate" case should already be fine for
   this sub-case (the two points are still distinct as PAIRS, hence still
   coprime in a Mumford/degree-2-factor sense — `(x-x1)` doesn't apply to
   either since neither has multiplicity, and if `u_a`/target `u` are the
   size-2 factors covering conjugate pairs, the existing `MatrixNondegenerate4`-
   style hypotheses likely already cover it structurally); only literal
   pair-equality `P1 = P2` triggers the genuinely new tangent case. Worth
   double-checking against `AlphaReduce.lean`'s actual `h12`/`h13`/etc.
   hypotheses once (i)-(iii) below are underway, but this is a real
   correction to how "duplicate" should be read, not a new complication —
   if anything it narrows the tangent case to exactly the one situation
   the Julia reference code itself treats specially.
6. **A reusable Lean proof-engineering pattern, not just a math fact,
   worth adopting from the reference source**: `build_phi_general!`
   cross-checks the tangent derivative row via an INDEPENDENT
   recomputation (`i·px^(i-1)` derived directly, not by re-running the
   same recurrence) and asserts equality — the same "independent
   re-derivation catches a sign/indexing bug the shared-machinery version
   can't see" discipline this project's own conventions already favor
   (see e.g. `compute_branch_series!`'s own "DEFENSIVE ASSERT" comments
   doing the same thing for `f_tay`). Worth doing the analogous thing in
   Lean once the tangent row-identity lemma exists: prove the derivative-
   row coefficient two independent ways (once via whatever recursive
   construction the Lean port uses, once via a direct closed-form
   `derivative`-based computation) and check they agree, as an extra
   confidence check before relying on it in `uRS4_dvd_Npoly4`'s tangent
   case — not required for correctness (Lean doesn't need runtime
   assertions the way Julia does), but a good sanity pass while writing
   the port, mirroring how this project already used ChatGPT/REPL
   round-trips elsewhere to catch exactly this class of bug early.

**Recommended scope for the next pass, in order (updated, supersedes the
previous version's step list; (i)-(iii) unchanged in substance, now with
the confirmed formulas to implement directly rather than re-derive):**

(i) prove the general `Polynomial (F p)` lemma —
`rootMultiplicity ≥ 2` from value+derivative vanishing — standalone, no
`AlphaReduce`-specific content (search `Mathlib.Algebra.Polynomial.Div`/
`.Roots`/`Mathlib.RingTheory.Polynomial.Basic` for the exact name before
writing anything, per this project's "search first, don't guess Mathlib
API" rule); (ii) port the confirmed `m=2` row formula above verbatim —
`Epoly4Tangent`/`Ypoly4Tangent` (or a case-split single definition) using
the exact `f'(px)/(2·py)` branch-derivative and the exact per-column
product-rule formula from point 3, not a re-derivation; (iii) redo
`uRS4_dvd_Npoly4`'s divisibility for the `P1=P2` literal-pair-equality
case using (i)+(ii); (iv) once (i)-(iii) are solid, generalize to the
other pairwise-coincidence sub-cases (`P1=Q1`, etc.) — likely one lemma
parametrized by which pair, matching how `build_phi_general!`'s own loop
treats every anchor uniformly rather than special-casing which position
tangency occurs at. **`m≥3` (triple/quadruple coincidence) is now
confirmed out of scope, matching the reference implementation's own
explicit limits, not just this roadmap's earlier judgment call** — fold
into `Bad` rather than build the `F_yy` cross-term machinery
`_monomial_column!`'s own comment says would be needed. **Nothing
implemented in `.lean` yet this pass** — `phi_general.zip` was read and
this section corrected/confirmed against it, per Claire's instruction;
`AlphaReduce.lean`'s existing simple-point code is still untouched,
matching this project's "plan before editing a large working proof"
practice.

### Where this leaves `curBeforeMonic`/`Epoly`/`Ypoly`/`Npoly` — now correctly located, not yet read line-by-line

Earlier in this pass, before Claire's files arrived, this roadmap update
was blocked believing `curBeforeMonic`/`Epoly`/`Ypoly`/`Npoly`'s actual
definitions were unavailable anywhere in-session (`DataDerivationSolve.lean`
wasn't uploaded yet, and `bridge.zip`'s `TheDataDerivation/` directory
turned out to be empty). **That gap is now closed** —
`DataDerivationBasics.lean`, `DataDerivationSolve.lean`,
`DataDerivationTower.lean` were uploaded and copied into the working
directory this pass, alongside the already-present `DataDerivationMumford.lean`
— all four files of `TheDataDerivation`'s own split are now on hand.
**Not yet read this pass** (Claire's instruction was to stop at the
roadmap, not continue into design/implementation) — the next pass should
open `DataDerivationSolve.lean` directly for `curBeforeMonic`/`Epoly`/
`Ypoly`/`Npoly`'s actual bodies (§4.0's `rrBasis5`/`coeffsOut`/
`cramerSolution`/`matrixA`, per `DataDerivationMumford.lean`'s own
docstring pointers) before writing anything, both to confirm this
session's reading of the Julia source against how it was already ported
for K=2, and to reuse as much of that K=2 structure as directly
transfers to K=4 (the arithmetic pattern — build `E,Y` from a linear
solve, form `N=E²-fY²`, divide by known factors, monic-normalize,
compute `v_RS` via mod-inverse — is expected to be near-identical; only
the anchor count/basis size and the "does `u_a` split" fork above are
genuinely new relative to what K=2 already had to handle).

### Revised Step 1, concretely (supersedes the vaguer version above)

1. Read `DataDerivationSolve.lean`'s `curBeforeMonic`/`Epoly`/`Ypoly`/
   `Npoly`/`rrBasis5`/`coeffsOut`/`cramerSolution`/`matrixA` in full.
2. Design the K=4 analogues (`rrBasis7`, a `(6×6)` `matrixA`/`cramerSolution`
   generalization, `curBeforeMonicK4`/`EpolyK4`/`YpolyK4`) — expect this to
   be substantially mechanical given K=2's structure, EXCEPT for the
   "does `u_a` split" fork (§ above), which is genuinely new.
3. Decide `Reduce`'s real signature per the "`alpha•a` is precomputed"
   finding above: `Reduce (u_a v_a : F p) (P1 P2 : F p × F p) : F p × F p
   × F p × F p`, not a function of `alpha : ℤ` directly.
4. Restate `SampleTargetFromAlpha.isReduction` as `(u0,u1,v0,v1) = Reduce
   u_a v_a P1 P2` (a `rfl`-provable/computed equation) rather than an
   assumed `Prop` field, once (1)-(3) land.
5. `decoupledSystem_zeroDimensional`'s `sorry` and task (B)'s `Bad`
   definition are UNCHANGED by this pass — still open, still separate
   pieces of work, not addressed here.

**Explicitly not started**: no Lean code for any of the above was written
this pass, per Claire's instruction to hold off until the roadmap itself
was corrected first.

## Status update (this pass): `AlphaReduce.lean` builds clean; `AlphaLocusDegreeUniform.lean`'s errors traced to one missing-file cascade, two real bugs fixed

**`AlphaReduce.lean`: DONE for everything it currently attempts.** Confirmed
against Claire's REPL this pass — 0 errors, `sorry`-free through
`dvd_N_u4`. Three proof-engineering bugs were found and fixed along the
way (all in tactic scripts, not in the underlying math, which was right
throughout):

1. `row01_defining_eq_aux`'s `hEval` step: `ring` was being asked to close
   goals still containing un-reduced `if bj = 0 then _ else 0`/`if bj = 1
   then _ else 0` guards (from `Epoly4`/`Ypoly4`'s `match`-then-`if`
   shape). `split_ifs` initially failed because those `if`s live inside an
   un-reduced `match rrBasis7.getD bidx.val (0,0,0) with | (fst,bi,bj) =>
   ...` rather than a bare `if`; fixed by `simp only [hget]` (substituting
   the concrete `(fst,bi,bj)` triple from the already-established `hget`
   equation) BEFORE attempting to split. Even after that, `split_ifs` was
   splitting three independent `if`s (two from the `Epoly4`/`Ypoly4` eval
   terms, one from `Fsum`'s own `if bj=1 then py else 1`) without
   recognizing they all key off the same `bj`, producing one spurious case
   combination that was unprovable as stated. Final fix: `norm_num` (which
   resolves the literal-numeral disequalities `0=1`/`1=0` via decidability
   directly, rather than introducing independent case hypotheses) followed
   by `<;> ring` (safe whether or not `norm_num` alone already closes the
   goal).
2. `dvd_of_row_identity4`'s `j=1` case: a calc-chain step dropped the
   `C tv1 *`/`C tv0 *` scaling factors that an earlier step in the same
   chain had already established were present — a genuine copy-paste-style
   slip (not a tactic issue), where the claimed intermediate equality was
   false relative to its own context. Fixed by restoring the `C tv1 * (...)`/
   `C tv0 * (...)` wrapping.
3. Same case, next step: `xmodUTable p tu0 tu1 (bi+1)` vs
   `xmodUTable p tu0 tu1 (1+bi)` — syntactically different `Nat`-index
   terms that `ring` treats as opaque, unrelated atoms (it doesn't look
   inside function-application arguments). Fixed with an explicit
   `hcomm : bi+1 = 1+bi` fed into the `simp only` set before `ring`, plus
   `if_neg (one_ne_zero (α := ℕ))` to force `reduceMonomialModU`'s internal
   `if 1 = 0 then ... else ...` into its correct branch (plain `simp only`
   doesn't discharge numeral disequalities on its own).

**Still explicitly not started** in `AlphaReduce.lean` (unchanged from
before this pass — see the file's own module docstring, updated this pass
to record the build confirmation): `uRS4`/`vRS4` (monic-normalization/
root-finding on `curBeforeMonic4`) and the `Reduce` function itself. This
is real, separate work — `AlphaReduce.lean` currently gets you as far as
"the correct quartic/quotient polynomial exists and divides correctly,"
not "here is `Reduce`'s output as a computed `(u0,u1,v0,v1)`."

**`AlphaLocusDegreeUniform.lean`: root cause of the reported errors was a
missing file, not broken code — now resolved, two independent real bugs
found and fixed underneath it.** The build log's `Unknown identifier
'single'`/`single_sub_single_mem_Divisor0`, the `curBeforeMonic`/`Ypoly`/
`uRS` unknown-identifier errors, and the two `heartbeats` timeouts all
trace to ONE cause: `DivisorClassGroup.lean` (imported at this file's top)
was missing from the working tree this pass — Claire's `bridge.zip`
(uploaded mid-pass) has it, at `Genus2Lean/DivisorClassGroup.lean`, and
`single`/`single_sub_single_mem_Divisor0` are both defined there exactly
as `AlphaLocusDegreeUniform.lean` expects (`single : H.Point → Divisor H`,
`single_sub_single_mem_Divisor0 : ∀ P Q, single P - single Q ∈ Divisor0
H`). The `curBeforeMonic`/`Ypoly`/`uRS` errors and the heartbeat timeouts
were downstream cascade damage from that one missing import (Lean's
error-recovery inserts `sorry` for unresolved names and can spend enormous
effort unifying metavariables against `Nondegenerate`'s dependent
signature once its `hcurA`/`hgcdA` arguments are `sorry`), NOT a real
second missing-import problem — the actual definitions are reachable via
`AlphaLocusDegreeUniform → DecoupledSystemRegular →
TheDataDerivation.DataDerivationMumford → TheDataDerivation.
DataDerivationSolve`/`DataDerivationTower`, all present and unchanged.
`bridge.zip`'s full `Genus2Lean/` directory has been copied into the
working tree this pass (36 files, including `DivisorClassGroup.lean` and
everything else it and `AlphaLocusDegreeUniform.lean` transitively need)
so this should no longer reproduce on a clean rebuild.

**Two independent real bugs found and fixed underneath the cascade** (both
plain under-application of `SampleTargetFromAlpha`, which takes FIVE
explicit/implicit arguments — `p H D aClass δ₀` — not four; the missing
`δ₀` made Lean read `SampleTargetFromAlpha p H D aClass` as a still-curried
function `H.Point → Type u_1` rather than a `Type`, hence the "type
expected, got (... : H.Point → Type u_1)" errors at lines 303/374 in the
original log):
1. `alphaPairDelta`'s signature — added `{δ₀ : H.Point}` as an implicit
   argument, threaded into `SampleTargetFromAlpha p H D aClass δ₀`.
2. `decoupledSystem_degree_uniform`'s signature — added `(δ₀ : H.Point)`
   as an explicit argument, same threading.

**Not yet attempted this pass** (no test against Claire's REPL yet for
this file specifically, unlike `AlphaReduce.lean` above): whether these
fixes are sufficient for a clean build, or whether other latent issues
surface once the missing-import cascade is actually cleared. Both
`decoupledSystem_isRegularSequence`/`decoupledSystem_zeroDimensional`
(moved into this file, per the file's own docstring, from
`DecoupledSystemRegular.lean`) and `decoupledSystem_degree_uniform` itself
remain `sorry`'d or unproved as documented elsewhere in this file — this
pass did not attempt any of that proof content, only cleared the
elaboration-blocking errors so the file can actually be typechecked far
enough to see what remains.

**Action still outstanding, per the file's own docstring**: delete
`decoupledSystem_isRegularSequence`/`decoupledSystem_zeroDimensional` from
the end of `DecoupledSystemRegular.lean` now that they're duplicated here
— not done this pass, flagged so it isn't lost.

## Update (this pass): confirmed sorry inventory, answered "what do the two
## sorries actually achieve," drafted a ChatGPT consultation for
## `decoupledSystem_zeroDimensional`

**Full-chain sorry audit, done fresh this pass** (`grep` for actual `sorry`
tactic uses, not docstring mentions, across all four `.lean` files):
`DecoupledSystemRegular.lean`, `PeelChainAssembly.lean`, `AlphaReduce.lean`
are all genuinely 0-`sorry` — every remaining `sorry` in the whole project
lives in `AlphaLocusDegreeUniform.lean`, and there are exactly two:
`decoupledSystem_zeroDimensional` and `decoupledSystem_degree_uniform`.
`decoupledSystem_isRegularSequence` is confirmed proved (one-line
delegation to `regularSeq_of_peel_chain`), matching this file's own
existing claim.

**Answering Claire's question — what does closing each sorry actually
buy**, stated plainly since it wasn't spelled out in one place before:
closing `decoupledSystem_zeroDimensional` is pure Mathlib-API
commutative algebra with ZERO alpha/genus-2 content — it doesn't move
Step 1/2 forward at all, it only upgrades the fixed-target
regular-sequence fact to a fixed-target finiteness fact. Closing
`decoupledSystem_degree_uniform` is not currently possible in Lean at
all — not because of a missing proof idea, but because two prerequisite
pieces of work are still undone and both live OUTSIDE Lean: porting
`Reduce` (Task A, an actual Julia→Lean port of `phi_general.zip`'s
algorithm) and empirically determining what `Bad` even is (Task B, a
numerical Julia/Oscar investigation of whether `D ~ K_C` correlates with
a degree jump, per Step 2). Whether the bad `alpha`'s end up being
literally readable off a formula (e.g. `D ~ K_C`) or something the
computer algebra has to determine per-instance is exactly Step 2's open
question — nobody has run that check yet.

**Attempted `decoupledSystem_zeroDimensional` this pass; not closed —
routed to a ChatGPT consultation instead, per project convention for
hard sorries.** The needed fact — "regular sequence of length
`Fintype.card Idx` (=12) in `MvPolynomial Idx (F p)` implies the quotient
is `Module.Finite (F p)`-finite" — is real commutative algebra (system-
of-parameters / Cohen-Macaulay dimension theory), not a Mathlib one-
liner; confirmed via direct web search that no ready-made Mathlib lemma
states this. Two candidate routes surfaced and written up in
`chatgpt_prompt_zerodim.md` (drafted, not yet sent/answered):
1. **Krull's height theorem**, now genuinely present in current Mathlib
   (`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
   `Mathlib.RingTheory.Ideal.Height` — `Ideal.height`,
   `ringKrullDim`, `Ideal.height_le_ringKrullDim_quotient_add_encard`) —
   this infrastructure did not exist when older passes of this project
   assessed the gap as "a Mathlib-API question not yet surveyed"; it may
   be surveyable now. Missing piece: connecting `rs.length = 12` to
   `ringKrullDim (Rdec p) = 12` (does Mathlib know
   `ringKrullDim (MvPolynomial ι k) = Fintype.card ι` for a field `k`?
   Not confirmed — only found an inequality for the single-variable
   case, `Polynomial.ringKrullDim_le`) and then chaining height/dimension
   facts to get equality (not just inequality) at the quotient, which
   isn't obviously routine.
2. **Noether normalization** (`Mathlib.RingTheory.NoetherNormalization`,
   `exists_integral_inj_algHom_of_quotient`) — for `I ≠ ⊤` an ideal of
   `MvPolynomial (Fin n) k`, gives `MvPolynomial (Fin s) k ↪ (quotient)`
   integral+injective for SOME `s ≤ n`. If `s = 0` can be forced from
   `rs.length = n` and `IsRegular`, `MvPolynomial (Fin 0) k ≃ k` and the
   quotient is finite over `k` directly — this looks like the more
   concrete/tractable route of the two, but nailing `s = 0` is exactly
   where the same underlying dimension-theory content has to enter one
   way or another; flagged as "the crux of the whole sorry" in the
   consultation prompt rather than assumed solvable.

Also recorded in the prompt (in case it's the real answer): the 12
generators' own shape means the honest finiteness argument might not be
a free corollary of `IsRegular`+length-count at all, but might need to
reuse the SAME "final 4-variable elimination certificate" gap that
`ROADMAP-regular-sequence.md` §5 step 4 already flags as needed for
`decoupledSystem_isRegularSequence` itself (the 4 curve-relation
generators pin `wa*,wb*` integrally over `F p[a1,a2,b1,b2]`, and the 8
`Fu`/`Fv` generators pin `U0,U1,V0,V1` linearly over the same subring
given the others — but nothing in `genList` directly bounds
`a1,a2,b1,b2` themselves; that has to come from eliminating everything
else symbolically, which is a genericity/degree computation, not
abstract commutative algebra). If ChatGPT confirms this, the "just
Mathlib API, unrelated to genericity" framing this roadmap and
`ROADMAP-regular-sequence.md` both currently use for this sorry is
optimistic and should be corrected.

**Not sent to ChatGPT yet this pass** — Claire copies prompts over
herself per project convention; `chatgpt_prompt_zerodim.md` is ready to
paste. Nothing in `AlphaLocusDegreeUniform.lean` was edited this pass
(no proof attempt was made without a plan, per "don't write nothing but
also don't guess blind on hard math" — this sorry cleared the bar for
"ask ChatGPT first," not "write a plausible-looking but untested Lean
proof term").
