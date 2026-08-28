import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemRegular
import Genus2Lean.DivisorClassGroup
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.Reduce.GeneralSharedRoot
import Genus2Lean.ZeroD.PeelChainAssembly
import Genus2Lean.ZeroD.RegularSequenceFiniteQuotient
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.ZeroD.SanchorEqAlphaPoints
import Genus2Lean.ZeroD.PrincipalWitnessCAConnection

-- `PrincipalDivisorSubgroup.lean` supplies `toPair`/`divToPair`/`ordAt`/
-- `pointIdeal`, needed below (`ROADMAP-reduce-divisor-correctness.md` Step 2)
-- to state what divisor class a Mumford coordinate pair `(u0,u1,v0,v1)`
-- actually represents, so `reducedClass_eq_of_isReduction'` can be stated
-- (as a `sorry`) against a real right-hand side rather than a placeholder.

-- `Module.Finite.quotient_of_isRegular_of_length_eq_card` (used by
-- `decoupledSystem_zeroDimensional` below) lives in
-- `RegularSequenceFiniteQuotient.lean`, a generic commutative-algebra file
-- with no `Genus2Lean`-specific content — imported directly here since
-- nothing else in this file's import chain pulls it in.

-- `regularSeq_of_peel_chain` (used by `decoupledSystem_isRegularSequence`
-- below, moved verbatim from `DecoupledSystemRegular.lean`) lives in
-- `PeelChainAssembly.lean`, which IMPORTS `DecoupledSystemRegular.lean`
-- (not the reverse) — so importing only `DecoupledSystemRegular` here
-- does not transitively reach it; this file needs its own direct import.
-- `DecoupledSystemRegular.lean` does not import `DivisorClassGroup.lean` (it
-- has never needed `Jacobian`/`toJacobian` before this file), so this file
-- imports it directly. `HyperellipticFunctionField.lean`/`AffinePoints.lean`
-- (for `HyperellipticPolynomial`/`H.Point`) come in transitively through
-- `DivisorClassGroup.lean`.

/-!
# Connecting `SampleTarget`'s `(u0,u1,v0,v1)` to `alpha` and the Jacobian,
# and stating (not yet proving) the uniform-in-`alpha` degree bound

This file is the new home ROADMAP-alpha-locus.md's Step 1/Step 3 asked for:
a place where `SampleTarget` gets an `alpha` field (task (A)), and where
`decoupledSystem_degree_uniform` can actually be *stated* against that
alpha-parametrized data. It imports `DecoupledSystemRegular.lean` rather
than the other way around, and `decoupledSystem_isRegularSequence`/
`decoupledSystem_zeroDimensional` are moved here from that file (see the
note at the bottom of this docstring) — both are the *fixed-target* special
case of the uniform statement this file is organized around, so they
belong with it rather than with the machinery (`Idx`, `Rdec`, the
peel-chain lemmas) that produces them.

## What this file honestly does and does not do

Per ROADMAP-alpha-locus.md, two things are needed before
`decoupledSystem_degree_uniform` can even be **stated**, let alone proved:

- **(A)** `SampleTarget` needs an `alpha` field, connected to `(u0,u1,v0,v1)`
  via `Reduce(alpha • a - P1 - P2)` — i.e. Cantor/Mumford reduction of a
  degree-0 divisor class down to its `(u0,u1,v0,v1)` normal form.
- **(B)** the exceptional set `Bad ⊆ F ell × F ell` needs an actual
  definition and an actual size bound, not just "codimension 1."

Neither exists anywhere in this project yet. In particular, **general
Cantor/Mumford reduction (`Reduce`) is not implemented in Lean** — the only
reduction machinery on file is `mumfordB` (`LCanonicalElementary.lean`),
which builds the two-point Mumford `b`-polynomial for the *un-shifted*
divisor `Q₁ + Q₂` directly from two curve points; it does not reduce an
arbitrary degree-0 divisor class (in particular `alpha • a - P₁ - P₂` for
`alpha ≠ 0`) down to Mumford normal form. Porting that general reduction
from the Julia/Oscar pipeline (`01_elim2_main.jl`) is flagged in the
roadmap as its own piece of work, not attempted here.

So task (A) below is done in the only honest way available right now:
`SampleTargetFromAlpha` packages `alpha`, the two curve points `P1 P2`, and
a **hypothesis field** asserting that `(u0,u1,v0,v1)` is what `Reduce`
*would* produce — stated as a specification, not computed. This mirrors
exactly how `DecoupledGenerators` already handles `Fu_decoupled`/
`Fv_decoupled` (abstract elements satisfying the defining shape, packaged
so downstream statements typecheck, pending the closed-form derivation).
Once `Reduce` exists, the hypothesis field becomes a `rfl`-provable
consequence of a concrete `def` and this indirection collapses, exactly as
that docstring anticipates for `DecoupledGenerators`.

Task (B) is not attempted at all here beyond leaving `Bad` an existential
`Set (F ell × F ell)` with no defining property — Step 2 of the roadmap
(numerically checking, in Julia/Oscar, whether degree stays constant
across several `(alpha,alpha')` instances, and whether `D ~ K_C` correlates
with a degree jump) has to happen first, and is empirical/exploratory work
outside Lean. Pinning `Bad` down without that check would just be
inventing an unjustified definition.

**Consequently `decoupledSystem_degree_uniform` below is `sorry`,
and is expected to remain `sorry` until Steps 1–2 of the roadmap are
substantially further along** — the point of stating it now is so the
target theorem exists as a real Lean statement (matching the "actual
target theorem" box in ROADMAP-alpha-locus.md) that later work can be
checked against, not to claim progress on the proof itself.

## `Reduce`'s actual algorithm, now on file (`phi_general.zip`) — not yet
## ported, but no longer unspecified

The paragraph above says general Cantor/Mumford reduction "is not
implemented in Lean," which is still true, but as of this pass it is no
longer *unknown* — `phi_general.zip` (`07_build_phi_general.jl`,
`09_residual_and_modinv.jl`, `10_root_finding.jl`,
`trial3_phi_symbolic_unified.jl`'s `symbolic_residual`, which
`ROADMAP-regular-sequence.md` §4.0 already documents at the "what it
computes" level) is the actual, general-`K`, working Julia/Oscar
implementation of `Reduce`, and it settles a question this file's earlier
draft left open by construction rather than by proof: **what `Reduce` for
`alpha • a - P1 - P2` (`K=2`, `c=0` in the code's parametrization: two
concrete curve-point anchors, no symbolic ones) actually IS, algorithmically.**
Recorded here so a future porting pass has the recipe rather than having to
reverse-engineer it from the code a second time.

**The construction, at the level that matters for `Reduce`'s Lean
signature (full numerical/scratch-buffer machinery deliberately elided —
see the source files above for that):**

1. **Interpolate a cubic `phi(x,y) = E(x) + y*Y(x)` through the divisor's
   support.** For `K=2`, `P1=(x1,y1)`, `P2=(x2,y2)` are the two curve
   points; `phi` is built (`build_phi_general!`) as the unique (up to the
   irrelevant overall scaling `build_phi_general!` fixes by normalizing
   the coefficient of `y` to `1` — this is exactly `mumfordB`'s existing
   `d=1` convention, see `07_build_phi_general.jl`'s §1b comment) element
   of the Riemann-Roch space `L(3•infty)` (`rr_basis(K+3)`, i.e. `nb=5`
   monomials `{1,x,y,x²,x³}` for `K=2`) vanishing at `P1` and `P2` **and**
   satisfying the two "Mumford" rows that say `phi(x,v(x)) ≡ 0 (mod u(x))`
   for the TARGET `u(x)=x²+u1x+u0, v(x)=v1x+v0` -- i.e. `phi` is
   simultaneously forced to vanish on the divisor being reduced (`P1+P2`)
   AND on the target divisor class's own Mumford representative. This is
   a `(K+2)x(K+2) = 4x4` linear system (`K` anchor rows + 2 Mumford rows,
   `K+2` unknown coefficients since the `y`-coefficient is fixed), solved
   by Cramer's rule / Gaussian elimination (`fp_gauss!`) — matching
   `ROADMAP-regular-sequence.md` §4.0 step 3 exactly, now with the
   geometric "why `K+2` rows/unknowns" reading spelled out: `phi` cuts out
   a degree-`(K+2)`-ish divisor via `L(3•infty)`, and forcing it through
   BOTH the source and target divisors' worth of constraints is what pins
   it down to (projectively) one solution.
2. **Square `phi` and intersect with the curve.** On `C : y²=f(x)`,
   `phi(x,y)*phi(x,-y) = E(x)² - f(x)*Y(x)²` — the user's "solve
   `phi(x,y)^2` for `y²` [via `y²=f(x)`] and set the two `x`-expressions
   equal" is exactly this norm computation, `N(x) := E(x)² - f(x)*Y(x)²`
   (`build_N_inplace!`, `symbolic_residual` step 6). For `K=2`,
   `deg(E) ≤ 3, deg(Y) ≤ 0` (§4.0's basis is `{1,x,y,x²,x³}`, so `Y`'s only
   monomial is the constant-times-`y` term, `y_idx` picks out `(0,1)`) —
   **this is not a new fact discovered by reading the Julia source, it is
   exactly `Npoly_natDegree_le_six`/`Ypoly_natDegree_le_zero` /
   `Epoly_natDegree_le_three`, already proved in
   `DecoupledSystemRegular.lean`** (§ following `curBeforeMonic`), so
   `deg(N) ≤ 6` matches the user's "deg 6 in x" precisely, and the Lean
   file already has the degree bookkeeping this algorithm needs, just not
   (yet) the construction of `phi`/`E`/`Y` themselves from `P1,P2` — those
   are asserted properties of `Epoly`/`Ypoly`/`uRS`/`vRS`
   (`TheDataDerivation`), not yet derived from an interpolation-through-
   `P1,P2` construction the way `phi_general` actually builds them.
3. **Divide out the known factors, leaving the reduced divisor's `u_RS`.**
   `N(x)` is divided exactly (`divexact`/`poly_divmod_linear_inplace!`) by
   `(x-x1)`, `(x-x2)` (the ORIGINAL divisor's support -- these are roots of
   `N` by construction, since `phi` was forced to vanish there) and by the
   TARGET's own `u(x)=x²+u1x+u0` (ditto, by the Mumford rows), then
   normalized monic. What's left, `u_RS(x)`, is degree `deg(N) - 2 - 2 = 2`
   for `K=2` — **the "two additional roots"** the user's message describes,
   found via `_solve_quadratic_roots!` (`10_root_finding.jl`) rather than a
   general root-finder, since the degree is known to be exactly 2 in this
   case (`_find_x_roots_dispatch!` special-cases `deg==2`).
4. **`v_RS(x) := -E(x)*Y(x)^{-1} mod u_RS(x)`**, `y`-coordinates of the two
   roots recovered the same way (`y = -E(x)/Y(x)` at each root,
   `recover_y_from_phi_inplace`/`find_roots_and_points_inplace!`). This
   `(u_RS,v_RS)` pair IS `Reduce(alpha • a - P1 - P2)`'s Mumford-coordinate
   output — i.e. it is `SampleTarget p`'s `(u0,u1,v0,v1)` after `Reduce`,
   NOT before: the target `(u0,u1,v0,v1)` fed into step 1 above is the
   OTHER sample's target (or, for the base case with no prior reduction
   needed, `alpha • a` reduced against the point at infinity) -- `Reduce`
   as a function takes a divisor class and returns Mumford coordinates,
   and this whole 4-step construction is how one candidate representative
   (`P1+P2`, shifted by `-alpha*a` implicitly via which target `(u0,u1,v0,v1)`
   gets fed into step 1) gets turned into another.

**Why the sign/geometry works out to "negation" the way the user's message
states it** (`the two additional roots are the neg group sum of
P1+P2-alpha*a`): `phi`'s divisor of zeros, minus its divisor of poles, is
principal (that's what "cubic interpolating through the four supports"
means -- `phi` vanishes on `P1+P2` and on the target's Mumford pair, and
has a pole of the matching order at infinity); a principal divisor is
`0` in the Jacobian, so `[P1]+[P2] + [target's two points] - [3•infty
worth of poles] = 0`, i.e. `[target] = -([P1]+[P2]) + [3•infty stuff]` --
the "negation" is the group-law fact that a curve's own hyperelliptic
involution `(x,y) -> (x,-y)` combined with Mumford reduction is exactly
how `-D` gets computed for `D` a reduced divisor class of degree ≤ genus,
and squaring `phi` (equivalently, evaluating `phi(x,y)*phi(x,-y)`) is what
makes the involution enter the computation.

**Not ported to Lean.** This section records the algorithm precisely
enough that a future `Reduce : Jacobian H D → (F p × F p × F p × F p)`
definition (or a `Prop`-level spec good enough to discharge
`SampleTargetFromAlpha.isReduction` as a theorem instead of an assumed
field) has the actual recipe to port, rather than nothing -- but no Lean
code changes in this file or `DecoupledSystemRegular.lean` follow from
this pass. `isReduction` below is unchanged: still an assumed `Prop`
field, still the honest placeholder the earlier paragraphs describe.

## Why `alpha` needs a Jacobian to live in, and what's used for that

`alpha • a` (a scalar multiple of a fixed degree-1 divisor `a`, living in
`J = Jac(C)`) needs a group for `alpha : F ell` to act on. `bridge.zip`'s
`DivisorClassGroup.lean` already has the needed objects: `Divisor H`,
`Divisor0 H` (the degree-0 subgroup), `PrincipalDivisorData H`, and
`Jacobian H D := Divisor0 H ⧸ (principal divisors)` for
`D : PrincipalDivisorData H`, plus `toJacobian : Divisor0 H →+ Jacobian H D`
and `s : H.Point → H.Point → Jacobian H D` (a fixed basepoint `δ₀` plus a
point, packaged as a degree-0 class). Below, `alpha • a` is written as a
`ℤ`-action on `Jacobian H D` (via `zsmul`, since `Jacobian H D` is an
additive group) applied to a fixed chosen class `aClass : Jacobian H D`,
rather than reproving group-structure facts already available from
`AddSubgroup`/quotient-group instances Mathlib supplies automatically for
`Divisor0 H ⧸ _`.

`F ell` (`alpha` ranging over a residue field of the group's exponent, per
the roadmap's phrasing) is left as `ℤ` here rather than a bespoke `F ell`
type: nothing in this file's statements needs `alpha` reduced mod the
group order, only that it is an integer scalar, so introducing `F ell` now
would be unmotivated machinery ahead of Step 2 actually needing it.
-/

noncomputable section

-- `Jacobian`, `PrincipalDivisorData`, `toJacobian` live in `namespace
-- HyperellipticPolynomial`; `single`, `Divisor0`,
-- `single_sub_single_mem_Divisor0` live one level deeper, in the nested
-- `namespace Divisor` (`DivisorClassGroup.lean`, closed again before
-- `Jacobian` etc. are defined) — `open HyperellipticPolynomial` alone does
-- NOT reach into that nested namespace, so both opens are needed.
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

-- `curBeforeMonic`, `Ypoly`, `uRS` live in `Genus2Lean.TheDataDerivation`
-- (`DataDerivationSolve.lean`/`DataDerivationMumford.lean`), reached
-- transitively via `DecoupledSystemRegular.lean`'s own import chain — but
-- that file only brings the NAMESPACE in scope for ITSELF (`open
-- TheDataDerivation` at its own line 319); this file needs the same
-- `open` again to use those names unqualified, matching how
-- `DecoupledSystemRegular.lean` does it. (`Nondegenerate`,
-- `CrossNondegenerate`, `genList`, `Rdec`, `regularSeq_of_peel_chain` are
-- NOT in `TheDataDerivation` — they live directly in
-- `Genus2Lean.DecoupledSystem`, i.e. THIS namespace, so no extra `open`
-- is needed for those; `regularSeq_of_peel_chain` specifically needed the
-- `PeelChainAssembly` import above instead, since it's a different file's
-- missing-import problem, not a missing-`open` one.)
open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-! ## Task (A): `SampleTargetFromAlpha`, connecting `alpha` to `SampleTarget` -/

/-- **`SampleTarget`, now carrying the data that says where it came from.**
Extends `DecoupledSystem.SampleTarget p` (unchanged — this is deliberately
additive, not a replacement, so every existing lemma about `SampleTarget p`
still applies to `.toSampleTarget`) with:

- `alpha : ℤ`, the scalar this sample's target divisor class is
  `alpha • a` for (see the module docstring for why `ℤ` rather than a
  bespoke `F ell`);
- `aClass : Jacobian H D`, the fixed degree-1-divisor class `a` lives in,
  shared across both samples of a matching pair (the SAME `a`, per
  advisory-7 §1's `R(alpha; P1,P2) = Reduce(alpha*a - P1 - P2)` — `a` does
  not vary between sample 1 and sample 2, only `alpha` does);
- `P1 P2 : H.Point`, this sample's two curve points;
- `isReduction`, the hypothesis field standing in for the not-yet-ported
  `Reduce` function: it asserts `(u0,u1,v0,v1)` (inherited from
  `.toSampleTarget`) really is the Mumford-coefficient reduction of the
  divisor class `alpha • aClass - toJacobian (single P1 + single P2 -
  [degree-0 correction])`. **Left abstract rather than derived** — see
  module docstring; this is a specification, not a proof that any
  particular `(u0,u1,v0,v1)` satisfies it.

The precise shape of `isReduction` is intentionally the weakest thing that
lets Step 3 below quantify over it: it says "this target came from
reducing `alpha • a - P1 - P2`" without committing to *how* Mumford
reduction computes `(u0,u1,v0,v1)` from a divisor class, since that
computation (`Reduce`) is exactly the missing piece. Once `Reduce : Divisor0
H → (F p × F p × F p × F p)` (or similar) exists, `isReduction` should be
restated as `(u0,u1,v0,v1) = Reduce (alpha • aClass - ...)` and become a
provable field rather than an assumed one — flagged here so that
restatement isn't missed when `Reduce` lands. -/
structure SampleTargetFromAlpha (p : ℕ) [Fact (Nat.Prime p)]
    (H : HyperellipticPolynomial k) (D : PrincipalDivisorData H)
    (aClass : Jacobian H D) (δ₀ : H.Point) where
  toSampleTarget : SampleTarget p
  alpha : ℤ
  P1 : H.Point
  P2 : H.Point
  /-- The divisor class `alpha • aClass - ([P1] + [P2] - 2•[δ₀])` that
  `.toSampleTarget`'s `(u0,u1,v0,v1)` is supposed to be the Mumford
  reduction of. Built from real objects already on file (`toJacobian`,
  `single`, `zsmul`, `single_sub_single_mem_Divisor0` twice to get the
  degree-0 membership proof) rather than left as free-floating prose, so
  the divisor class this structure is FOR is at least pinned down
  precisely — `δ₀` is a fixed basepoint the caller supplies (matching
  `DivisorClassGroup.lean`'s own `s D δ₀ P` pattern), used only to turn
  `[P1]+[P2]` into a degree-0 class the same way `s` does, not claimed to
  be `a` itself. This field computes a real value; it is `isReduction`
  below, not this field, that is the actual placeholder. -/
  reducedClass : Jacobian H D :=
    alpha • aClass -
      toJacobian D ⟨single P1 + single P2 - (2 : ℤ) • single δ₀,
        by
          have h1 := single_sub_single_mem_Divisor0 P1 δ₀
          have h2 := single_sub_single_mem_Divisor0 P2 δ₀
          have : single P1 + single P2 - (2 : ℤ) • single δ₀ =
              (single P1 - single δ₀) + (single P2 - single δ₀) := by
            rw [two_zsmul]; abel
          rw [this]
          exact add_mem h1 h2⟩
  /-- **The actual placeholder for `Reduce`, as a `Prop` field.** Asserts
  that `.toSampleTarget`'s `(u0,u1,v0,v1)` is the Mumford-coefficient
  reduction of `reducedClass` — with NO witness constructed anywhere in
  this project, since `Reduce : Jacobian H D → (F p × F p × F p × F p)`
  (or whatever its precise signature turns out to be once ported) does not
  exist yet. Every instance of `SampleTargetFromAlpha` currently has to
  supply this as its own `sorry` at the call site; the field exists so
  that theorems below can quantify over "some `SampleTargetFromAlpha`
  satisfying `isReduction`" without themselves committing to what `Reduce`
  is. **`Reduce`'s actual algorithm is now recorded** (module docstring,
  "`Reduce`'s actual algorithm, now on file" section, from `phi_general.zip`)
  — interpolate a cubic `phi` through `P1,P2` and the target Mumford pair,
  form `N(x)=E(x)²-f(x)Y(x)²`, divide out the known anchor/target factors,
  the quotient's roots are `reducedClass`'s Mumford data — but that
  algorithm is not ported here, so this field is still exactly as
  unconstructed as before this pass.

  **Update: `Reduce` now exists (`Reduce.AlphaReduce`/`Reduce.GeneralSharedRoot`,
  `ReduceDispatchGeneral` specifically — the `h12`–`h34`-collision-free
  dispatcher), at the level of concrete Mumford/affine coordinates
  `F p × F p × F p × F p`. `isReduction'` below restates this field's
  intent against `ReduceDispatchGeneral` directly, and `isReductionOf`
  (further below, `ROADMAP-reduce-divisor-correctness.md` Step 1) packages
  `isReduction'` plus its witnessing coordinates/hypotheses into a single
  `Prop` with no free parameters beyond `sa` itself — that is what any
  caller instantiating this field should supply from now on, rather than
  an arbitrary unconstrained `Prop`. Kept as a free field (not literally
  replaced by `isReductionOf` in the structure signature) because no
  instance of this structure exists anywhere in the project yet to force
  a choice, and because `isReductionOf` needs `H : HyperellipticPolynomial
  (F p)` specifically while this structure is stated over a generic field
  `k` — pinning that down is exactly the kind of thing best done at an
  actual call site, not preemptively here. -/
  isReduction : Prop

/-- Convenience: read off `alpha`'s companion `alpha'` from a *pair* of
`SampleTargetFromAlpha` values sharing the same `aClass` — matches
advisory-7 §1/§2's two-sample setup (`R(alpha;P1,P2) = R(alpha';P3,P4)`)
directly, so downstream statements can talk about `sa.alpha - sb.alpha`
(`Delta` in the advisory's notation) without re-deriving the pairing each
time. Purely notational; carries no new mathematical content beyond
`SampleTargetFromAlpha` itself. -/
abbrev alphaPairDelta {p : ℕ} [Fact (Nat.Prime p)] {aClass : Jacobian H D}
    {δ₀ : H.Point} (sa sb : SampleTargetFromAlpha p H D aClass δ₀) : ℤ :=
  sa.alpha - sb.alpha

/-! ## Restating `isReduction` against the now-existing `Reduce`

`Reduce`/`ReduceGeneral`/`ReduceDispatchGeneral` (`Reduce.AlphaReduce`,
`Reduce.GeneralSharedRoot`) exist and are `sorry`-free, but they work at
the level of concrete coordinate pairs `F p × F p`, not the abstract
`H.Point`/`Jacobian H D` level `SampleTargetFromAlpha` is stated at. Two
bridges are needed to connect the two levels, and only one of them is
buildable from what's on file in THIS session's upload:

1. **`alpha • aClass`'s own Mumford pair `(ua0,ua1,va0,va1)`.** Per
   `ROADMAP-alpha-locus.md`'s "`alpha • a` is NOT computed by `Reduce`"
   resolution, this is supplied by the caller (whatever Cantor/group-law
   code produced the DLP instance), not derived here — so it is added
   below as an explicit hypothesis bundle, matching that resolution
   exactly, not reopened as a new gap.
2. **`H.Point → F p × F p`, the affine-coordinate projection.** This is
   the one genuinely new gap this restatement surfaces: `Reduce`'s inputs
   `P1 P2 : F p × F p` need to come from `SampleTargetFromAlpha`'s
   `P1 P2 : H.Point` somehow, and nothing in this session's upload defines
   that map — `HyperellipticPolynomial`/`AffinePoints.lean` (which define
   `H.Point` itself) are not part of this upload, only reachable
   transitively via `bridge.zip` per the file's own top-of-file import
   note. Guessing `H.Point`'s field names here (whether it exposes
   `.1`/`.2` directly, is a subtype of `F p × F p`, or something else)
   would risk a proof term that looks plausible but doesn't typecheck
   against the real definition, so this is left as an explicit named
   hypothesis (`toCoords`) rather than invented. Once `H.Point`'s actual
   shape is available, `toCoords` should collapse to a concrete
   projection (likely `fun pt => (pt.x, pt.y)` or similar) and the
   `isReduction'` predicate below should become provable-from-that rather
   than assumed.

**Update: gap 2 is closed.** `AffinePoints.lean` (now available this
pass, from `bridge.zip`) defines `H.Point := {p : k × k // H.Equation
p.1 p.2}` with real, already-proved projections `Point.X`/`Point.Y :
H.Point → k` (`P.X := P.1.1`, `P.Y := P.1.2`) — so the coordinate
extraction is `fun P => (P.X, P.Y) : H.Point → k × k`, a genuine
definition, not a guess. `toCoords` below is accordingly no longer a free
hypothesis; it is fixed to this projection. What remains open is only
what the docstring above already separately flagged: whether this
coordinate pair, for `H : HyperellipticPolynomial (F p)` specifically,
is what `ReduceDispatchGeneral` actually needs to be fed (i.e. `Reduce`'s
own correctness, unrelated to `toCoords`'s definedness). -/

/-- **`isReduction`, restated against `ReduceDispatchGeneral`.** Specializes
`k := F p` (the ambient section variable `k` is otherwise a generic field,
but `Reduce`/`ReduceDispatchGeneral` are stated over `F p = ZMod p`
specifically, so this definition needs a curve `H` fixed over that field,
not left generic — matching how `SampleTarget p`'s own `(u0,u1,v0,v1)`
fields are already `F p`-valued). Given:
- `ua0 ua1 va0 va1 : F p`, `alpha • aClass`'s already-reduced Mumford pair
  (gap 1 from the note above — supplied by the caller, per the roadmap's
  resolution, not computed here);
- `hcur`/`hgcd` (`P1 ≠ P2` branch) and `hcurT`/`hgcdT` (`P1 = P2` branch),
  `ReduceDispatchGeneral`'s own case-split hypotheses, now demanding NO
  pairwise `IsCoprime` facts among `P1,P2,u_a,` target (that's exactly
  what `ReduceGeneral`/`GeneralSharedRoot.lean` bought over the plain
  `Reduce`/`ReduceDispatch`) —

asserts `.toSampleTarget`'s `(u0,u1,v0,v1)` literally equals
`ReduceDispatchGeneral`'s output on `(sa.P1.X, sa.P1.Y)`, `(sa.P2.X,
sa.P2.Y)` and `alpha • a`'s Mumford pair. This is a genuine equation with
a computable RHS (unlike `isReduction` above, which names no witness),
but it is a SEPARATE predicate, not a proof that `isReduction` holds —
connecting the two still needs gap 1's data at any actual call site, and
needs a theorem (not attempted here) that `reducedClass`'s
divisor-class-level description and `ReduceDispatchGeneral`'s
coordinate-level output agree, i.e. that `Reduce`'s algorithm is CORRECT
(computes the Mumford reduction it claims to), which is exactly the open
item `ROADMAP-alpha-locus.md`/`AlphaReduce.lean`'s own docstrings flag as
"`Reduce`'s correctness... a fully open, not-yet-attempted theorem." -/
def isReduction' {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (c0 c1 c2 c3 c4 : F p) (ua0 ua1 va0 va1 : F p)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          ua0 ua1 va0 va1 sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c0 c1 c2 c3 c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4
        sa.P1.X sa.P1.Y ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)) : Prop :=
  (sa.toSampleTarget.u0, sa.toSampleTarget.u1,
   sa.toSampleTarget.v0, sa.toSampleTarget.v1) =
    ReduceDispatchGeneral p c0 c1 c2 c3 c4
      (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
      sa.toSampleTarget.u0 sa.toSampleTarget.u1
      sa.toSampleTarget.v0 sa.toSampleTarget.v1
      hcur hgcd hcurT hgcdT

/-- **`isReduction'` is the real, load-bearing content; `isReduction`
should be understood through it, not as a free-standing `Prop`.**
Per `ROADMAP-reduce-divisor-correctness.md` Step 1: `isReduction` (the
structure field above) was left as an unconstrained `Prop` precisely
because nothing had been built yet to give it real content — that
placeholder status is itself effectively an escape hatch (any `Prop`,
including `True`, typechecks as a witness). `isReduction'` closes that
gap **as a definition**, not merely as a parallel candidate: this
`abbrev` packages "there exist witnessing coordinates/hypotheses making
`isReduction'` hold" as the concrete existential a caller should supply
for `isReduction` from now on. This does not yet prove the two are
provably EQUIVALENT to `reducedClass`'s divisor-class-level statement
(that is `reducedClass_eq_of_isReduction'`, the real target theorem —
Step 2/3 below) — it only stops the file from carrying two unrelated,
confusingly-similar-named notions side by side, per Step 1's own scope
("cheap, mechanical... does not touch the divisor-class gap"). Any
future `isReduction : Prop` argument/field should be instantiated with
this existential rather than left free. -/
abbrev isReductionOf {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀) : Prop :=
  ∃ (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : F p)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          ua0 ua1 va0 va1 sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c0 c1 c2 c3 c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4
        sa.P1.X sa.P1.Y ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)),
    isReduction' sa c0 c1 c2 c3 c4 ua0 ua1 va0 va1 hcur hgcd hcurT hgcdT

-- `X`/`C` below (Step 2's Mumford-pair-as-polynomial encoding) are
-- `Polynomial.X`/`Polynomial.C`; this file otherwise has no need for bare
-- `Polynomial` names, so `open` it only from here on rather than at the top.
open Polynomial

/-! ## `ROADMAP-reduce-divisor-correctness.md` Step 2: stating (not proving)
`reducedClass_eq_of_isReduction'`

Per Step 2's own instructions: get this to TYPECHECK with a `sorry` body and
present it for review before attempting a proof. The three concretely-needed
ingredients, checked against the actual files this pass (not guessed):

1. **The Mumford-pair-to-class map.** `PrincipalDivisorSubgroup.lean` (now
   imported above) has no single lemma "the class a coordinate pair
   `(u0,u1,v0,v1)` represents" — per the roadmap's own flag, this is a real,
   confirmed gap, not an oversight to fix by reading harder. What DOES exist:
   `toPair H A B : CoordinateRing H` for `A B : k[X]` (so `toPair H
   (X^2 + C u1 * X + C u0) (C v1 * X + C v0)` is the actual coordinate-ring
   element `u(x) + v(x)·y` a Mumford pair names), and `divToPair A B S :
   Divisor H := ∑ P ∈ S, ordAt P A B • single P` (`H` implicit — a section
   `variable`, not an explicit argument like `toPair`'s; unlike `toPair`,
   nothing in `A B : k[X]` alone pins `H` down, so call sites below use
   named-argument syntax `divToPair (H := H) A B S` rather than relying on
   unification to find it from context) for an EXPLICIT finite point
   set `S` (`PrincipalDivisorSubgroup.lean`). There is no lemma computing `S`
   from `(A,B)` alone (that would need root-finding/`Polynomial.roots`-type
   machinery over `F p`, specifically the finitely many affine points where
   `u(x)=0 ∧ v(x)=y`, matched against `H.Equation`). So the map is expressed
   here as an existential over the witnessing point set and the fact that it
   really is the coordinate pair's full zero locus (`hsupp`, matching
   `divToPair`'s own precondition pattern) — this is the "flag it as its own
   smaller gap" move Step 2 asks for, not a proof that the map exists as a
   clean function.
2. **`reducedClass`'s definition**, already on file, unchanged (`alpha •
   aClass - toJacobian D (⟨single P1 + single P2 - 2•single δ₀, _⟩)`).
3. **The equality goal**: `reducedClass` equals `toJacobian D` applied to
   `divToPair u v S` (`H` implicit; packaged into `Divisor0 H` via `hmem`), for whichever
   `S` witnesses `isReductionOf`'s underlying `(u0,u1,v0,v1)`.

**Not yet resolved, flagged rather than guessed**: whether `S` should be
required to be exactly `sa.toSampleTarget`'s zero locus (`hsupp` below) or
something weaker — Step 3's proof attempt (residual-intersection /
residual-Mumford / principal-witness, per §3a) will determine which
`hsupp`-shape is actually provable; the one below is the literal reading of
"S is the point set the divToPair is taken over" and may need revision once
Step 3 is attempted. -/

-- **`maxHeartbeats` bump, this pass.** `reducedClass_eq_of_isReduction'`'s
-- signature grew substantially (the final-assembly wiring hypotheses,
-- Step 4 of the roadmap) and its elaboration now times out at the default
-- limit — a `whnf` timeout on the declaration itself, not a tactic-block
-- issue, so this is a signature-elaboration cost, not something
-- "unroll the proof state" (the usual heartbeat fix for tactic blocks)
-- addresses. Placed above the doc comment, per project convention
-- (`set_option`/`omit` go above the `/--`, never between it and the
-- theorem).
set_option maxHeartbeats 800000 in
/-- **Step 2's target theorem, stated as a `sorry` for review — not attempted
here.** Given `sa : SampleTargetFromAlpha` whose Mumford pair satisfies
`isReduction'` (i.e. really is `ReduceDispatchGeneral`'s output on `P1,P2`
and `alpha•aClass`'s reduced pair), and given a finite point set `S`
witnessing that `sa.toSampleTarget`'s `(u0,u1,v0,v1)` names exactly the
coordinate-ring element `toPair H u v` vanishing on `S` (`hsupp`) and that
this lands in `Divisor0 H` (`hmem`, needed to apply `toJacobian`), the claim
is that `sa.reducedClass` (the divisor-class-level specification already on
file) equals `toJacobian D` of that same divisor. This is exactly the
theorem `ROADMAP-reduce-to-zerodim.md` flagged as "not attempted here," now
typechecking; the proof (§3a's three-lemma skeleton: residual-intersection →
residual-Mumford → principal-witness via `ordAt`) is Step 3, deliberately not
attempted in this pass.

**Statement shape, revised this pass to fix a `whnf` heartbeat timeout, then
a follow-up `C`/`X` elaboration error**: the Mumford-pair-as-polynomial
encoding `X^2 + C u1 * X + C u0` / `C v1 * X + C v0` used to appear inline,
spelled out three separate times (`hsupp`, `hmem`, and the goal's anonymous-
constructor argument) — cheap to write but expensive to elaborate, since
each occurrence re-triggers full unification of `X`/`C`'s ring against `H`'s
field and the surrounding `divToPair (H := H)`/`ordAt (H := H)` applications
independently. Named `u v : Polynomial (F p)` as their own explicit
parameters with defining hypotheses `hu`/`hv` instead — this is the same
"thread it through as a hypothesis rather than an inline term" discipline
this codebase already uses elsewhere (e.g. `DecoupledGenerators`'s abstract
fields) — so `hsupp`/`hmem`/the goal now refer to the already-elaborated
`u`/`v` rather than re-elaborating the underlying polynomial expression
three times over. This fixed the heartbeat timeout but surfaced a second,
previously-masked issue: `hu`/`hv`'s own RHS (`X^2 + C ... `) still needs to
know it lives in `Polynomial (F p)`, and Lean's elaboration order for `=`
does not push the LHS's declared type down into an under-constrained RHS
strongly enough for `X`/`C`'s implicit ring argument to resolve on its own
— so both RHSs are ascribed directly, `(... : Polynomial (F p))`, the same
fix already needed at `divToPair`'s call sites in earlier passes.
**Correction after that attempt still failed identically**: ascribing the
*whole sum* (`(X^2 + C u1 * X + C u0 : Polynomial (F p))`) doesn't help
either — `+`'s own elaboration doesn't necessarily push the ascribed result
type down into each summand before `C`'s domain needs to be known, so `C`
still saw an unconstrained metavariable first. Fixed by ascribing `X` and
each `C _` application individually, e.g. `(C sa.toSampleTarget.u1 :
Polynomial (F p))`, which fixes `C`'s domain (`Polynomial.C : R →+* R[X]`,
so ascribing the codomain immediately forces `R := F p`) at the exact point
each one is elaborated, with no dependency on how `+`/`*`/`=` propagate
expected types afterward. Likewise
the goal's `⟨divToPair ..., hmem⟩` anonymous-constructor term (checked
against `toJacobian D`'s expected argument type `↥(Divisor0 H)`, which
unfolds through `AddSubgroup`/`SetLike`/`Subtype` coercions to accept
anonymous-constructor syntax — the likely `whnf` hotspot) was replaced with
an explicit `Subtype.mk (divToPair (H := H) u v S : Divisor H) hmem`, so the
`Divisor H` ascription is settled as its own step before the
subtype-membership coercion is attempted.

**Two more hypotheses added this pass (Step 3 prep, before any proof body
was attempted) — both are gaps in the STATEMENT, not proof difficulty, found
by reading `PrincipalDivisorSubgroup.lean`/`DivisorClassGroup.lean` directly
rather than assuming the Step-2-typechecked signature was already complete:**

1. **`hf : H.f = curvePoly p c0 c1 c2 c3 c4`.** The theorem takes `c0..c4`
   (feeding `curvePoly p c0 c1 c2 c3 c4`, via `Npoly4`/`Epoly4`/`Ypoly4`) but
   also an ambient `H : HyperellipticPolynomial (F p)` with its own `H.f`.
   Nothing previously linked the two — `E,Y,N`'s norm identity
   (`toPair_mul_involution`) is stated against `H.f`, so without `hf` there
   is no way to connect `Npoly4`'s value to anything `ordAt`/`toPair`-level
   can see. Genuinely missing, not previously needed since Step 2's sorry
   never had to unfold that far.
2. **`hdeg`/`hD : principalSubgroup H hdeg ≤ D.P`.** `D : PrincipalDivisorData
   H` is fully generic (`DivisorClassGroup.lean`: any `AddSubgroup (Divisor
   H)` with `P ≤ Divisor0 H`, no connection to `CoordinateRing H` required).
   `toJacobian D (D_old - D_new) = 0` needs `D_old - D_new ∈ D.P`; the
   Step-3 argument only ever produces membership in the GENUINE principal
   divisors, i.e. `HyperellipticPolynomial.principalSubgroup H hdeg`
   (`PrincipalDivisorSubgroup.lean`). For an arbitrary `D` there is no
   reason `D.P` contains that subgroup, so the theorem is false as stated
   without this hypothesis — confirmed by re-reading `PrincipalDivisorData`'s
   definition, which places no constraint on `D.P` beyond `≤ Divisor0 H`.
   `hD` is the weakest honest fix: it doesn't force `D` to be exactly
   `principalDivisorData H hdeg` (any `D` whose `P` is principal-compatible
   still works), matching this file's existing preference for `D` staying
   abstract elsewhere. No downstream call sites exist yet (checked, same as
   prior passes), so widening the hypothesis list breaks nothing.

**Statement bug found and fixed this pass, before any proof body was
attempted — the previous `divToPair (H := H) u v S` call was proving the
wrong thing.** `divToPair A B S := ∑ P ∈ S, ordAt P A B • single P`, and
`ordAt P A B` is the order of `toPair H A B = A + B·y` — NOT some
pair-to-divisor encoding specific to Mumford coordinates. Calling it with
`A := u` (degree 2), `B := v` (degree ≤ 1) computes the divisor of the
coordinate-ring element `u + v·y`, which is a totally different function
from the one a Mumford pair `(u,v)` is supposed to represent. Concretely:
`ordInfOfPair A B = -(max(2 deg A, 2 deg B + 5))`, so `ordInfOfPair u v =
-(max(4,7)) = -7`, hence (via `deg_div_eq_zero_deg5`, `(∑ ordAt) +
ordInfOfPair = 0`) `deg (divToPair u v S) = 7`, not `0` — `divToPair u v S`
can never land in `Divisor0 H` as `hmem` asked, for any `S`. The old
`hmem`/goal were asking for something generically false.

The correct construction (confirmed against the `mumfordB`/
`toPair H (-mumfordB Q₁ Q₂ hne) 1` precedent already in
`LCanonicalElementary.lean`, which is exactly the two-point special case of
this): a Mumford pair `(u,v)` represents the effective divisor `[R₁]+[R₂]`
(the points with `u`-coordinate a root of `u` and `v`-coordinate matching
`v` there) via the function `y - v(x)`, i.e. `toPair H (-v) 1`, NOT via
`toPair H u v = u + v·y`. `u` itself only enters as "the polynomial whose
roots pick out `S`" — it does not appear inside the `divToPair` call at
all. Since `ordInfOfPair (-v) 1 = -(max(2·1, 2·0+5)) = -5` (`B=1` has
degree `0`), `divToPair (-v) 1 S` has degree `5`, still not `0` — a
degree-2 correction is needed to bring it down to the honest
degree-`2 - 2 = 0` representative once `S` really is a 2-point root set.
**Historical note, corrected in a later pass:** an earlier draft of this
paragraph said the correction was `-2•single δ₀`, matching
`reducedClass`'s own structure-default shape. That was superseded once
`PrincipalWitnessStep4.lean`'s (†) showed the only correction this
project's witness construction can actually derive is
`-(single δ₀ + single (Point.iota δ₀))`, NOT `-2•single δ₀` (see this
theorem's own hypothesis-block comments, further down, for the full
`N₂`/`Nι`/`q` derivation). So both `hmem` and the goal subtract
`single δ₀ + single (Point.iota δ₀)` from `divToPair (H := H) (-v) 1 S`
directly, rather than `(2:ℤ) • single δ₀` as this paragraph originally
said. `hu`/`u` are kept as parameters (still
needed to pin down which points populate `S` — Step 3's proof will need
`S` to be exactly `u`'s root set), but no longer feed `divToPair`'s
argument slots. `hsupp` is restated over `ordAt (H := H) P (-v) 1` to match.
No downstream call sites of this theorem exist yet (re-checked), so this
correction is free.

**New hypothesis added this pass, before the proof body: `hAlphaRep`, the
missing semantic bridge from `alpha • aClass` (an abstract `Jacobian H D`
element) to a concrete divisor.** Traced through the actual math needed
(§3a item 3 of the roadmap; confirmed independently while starting Step 3):
the whole principal-witness argument shows `[D_old] = [D_new]` where
`D_old`/`D_new` are BOTH concrete divisors built from Mumford data — but
`sa.reducedClass`'s LHS, `alpha • aClass - ...`, only ever refers to
`aClass` abstractly. Nothing in this file (or `SampleTargetFromAlpha`'s
fields) previously said `alpha • aClass` equals `toJacobian D` of any
particular divisor — `ua0 ua1 va0 va1` were documented in `isReduction'`'s
own docstring as "`alpha • aClass`'s already-reduced Mumford pair," but
that was prose, not a hypothesis; `Jacobian H D`'s quotient-type structure
means `aClass` trivially HAS some representative divisor (it's a quotient
of `Divisor0 H`), but nothing pins that representative down to the
`ua0,ua1,va0,va1` coordinates the rest of the theorem already depends on.
Without this link the theorem cannot be proved: `hr`/`hcur`/`hgcd`/etc. all
talk about `ua0..va1` and `sa.toSampleTarget`'s coordinates, but the goal's
LHS has no route back to those coordinates without it.

Added `hAlphaRep`, matching the anchor divisor to the same `divToPair (-·)
1 · - 2•single δ₀` shape already fixed above for the target divisor (so
the two sides of the eventual principal-witness argument, `D_old` for the
anchor and `D_new` for the target, are stated uniformly): a fresh point set
`Sanchor : Finset H.Point`, `va : Polynomial (F p)` for the anchor's
Mumford `v`-polynomial (`hva`, ascribed exactly like `u`/`v` above for the
same `C`/`X` elaboration-order reasons), `hmemAnchor` for its `Divisor0 H`
membership, and `hAlphaRep` itself asserting `sa.alpha • aClass` literally
equals `toJacobian D` of that anchor divisor. This is not an artificial
weakening of the theorem — it is stating precisely what `isReduction'`'s
own docstring already claims `ua0,ua1,va0,va1` mean, as an actual
hypothesis rather than a comment. No downstream call sites of this theorem
exist yet, so this addition is free; the anchor's own `u_a`-polynomial
(`X^2+C ua1*X+C ua0`) is not needed as a separate parameter since (matching
`u`/`v` above) only `va` feeds `divToPair` directly — `ua0,ua1` remain used
elsewhere in this signature (`hcur`/`hgcd`/`hcurT`/`hgcdT`/`hr`) exactly as
before.

**Gap found and fixed this pass, before any proof attempt: `Sanchor` had
no support hypothesis at all.** `S` (the target support) is properly
constrained by `hsupp : ∀ P, P ∉ S → ordAt P (-v) 1 = 0` — i.e. `S`
can only be as big as `(-v,1)`'s actual zero-divisor support, not an
arbitrary `Finset H.Point`. `Sanchor` had no analogous hypothesis:
nothing in the signature stopped `Sanchor` from being any `Finset` at
all for which `hmemAnchor`'s degree-0 condition merely happened to
hold, disconnected from `va`'s actual roots. That makes `hAlphaRep`
satisfiable by an `Sanchor` that has nothing to do with the real anchor
points, which would let the theorem be proved (or left unprovable) for
reasons unrelated to the genuine Cantor-reduction content it's supposed
to capture. Added `hsuppAnchor : ∀ P, P ∉ Sanchor → ordAt P (-va) 1 = 0`,
the exact mirror of `hsupp`, closing this before Step 3's proof body is
attempted. No downstream call sites exist yet (re-checked), so this is
free.

**Checked this pass, not changed: whether `u` (the INPUT target Mumford
pair fed into the K=4 interpolation) needs its own named support `Finset`,
the way `ROADMAP-principal-witness-assembly.md`'s status-update #5 once
proposed (`Sg := {P1,P2} ∪ Sanchor ∪ Starget`, routed through
`divToPairRatio`/`principalSubgroup` membership).** That plan is
SUPERSEDED, per that same roadmap's later status-update #7/`Principal
WitnessAssembly.lean`'s own trailing note: `ordInfOfPair(Epoly4,Ypoly4) =
-8` vs `ordInfOfPair(uRS4General,0) = -4` do not match, so
`divToPairRatio`'s exact-pole-order-match requirement can never be
satisfied by this witness — `principalSubgroup` membership was never the
right tool here. The confirmed replacement route is a direct
`div_aff(g) - div_aff(uRS4General) = D_old - D_new` identity via
`eq_of_coeffAt_eq` (already on file, `PrincipalWitness.lean`), bypassing
`principalSubgroup` and any `Sg`/`Su`-style support union entirely.
**This identity carries no `δ₀` term at all** — `Divisor H` is
affine-only (`eq_of_coeffAt_eq`'s own docstring is explicit that this
project's model has no `δ₀`-coefficient slot), and the `-8`/`-4`
pole-order gap between `g` and `uRS4General` is a fact about the point at
infinity, not a `δ₀` coefficient; an earlier draft of this note said
`-4•[δ₀]` here, which conflated the two (see
`CHATGPT-LOG-principal-witness-assembly.md`'s "pass #17" entry). No
`Starget`-shaped hypothesis is added here accordingly — it would scaffold
an abandoned plan. **Update, this pass: the proof body below is no
longer `sorry`** — the actual route taken ended up being the concrete
`cAmιTmδmιδ_mem_of_le` assembly (`PrincipalWitnessFinalAssembly.lean`),
composed with `PrincipalWitnessCAConnection.lean`'s `divToPair`-collapse
lemmas and a direct `toJacobian`/`D.P`-membership bridge, NOT the
`eq_of_coeffAt_eq`/`D_old - D_new` route this paragraph originally
anticipated — left here for history, but superseded; see the theorem's
proof body and its inline comments for what was actually used. **Not yet
REPL-tested** — Claire's confirmation is the next step, per project
convention (this file never runs the Lean REPL itself).
 **Pass note: closed the "`S` unlinked to `u`" statement gap flagged
above (line ~682's "kept as parameters... still needed" comment) and its
unflagged anchor-side twin.** This does NOT close the `sorry` — it makes
the theorem actually say what it was meant to say. Before this pass, `S`
could be any `Finset` satisfying `hsupp`/`hmem` with zero connection to
`u`'s roots; the theorem was consequently either unprovable-as-intended
(vacuously true for a `T`-decoupled `S`) or simply not the claim anyone
meant. `hSmem`/`hufree`/`hScard` (and the anchor mirrors) pin `S` down to
be exactly `u`'s root set, stated without ever splitting `u` over `F p`.
This is the concrete, checkable prerequisite that had to exist before
`ROADMAP-principal-witness-assembly.md`'s `f+`/`f-` residual-matching
question is even well-posed: `S` is now the Lean object the roadmap's
prose has been calling `T`, and `Sanchor` is what it calls `C`. Next real
step (not done here): connect `f+`'s residual (`uANew`'s root set) and
`f-`'s residual (`uMinusNew`'s root set) to `S`/`u` via this link, rather
than treating them as free-floating point pairs. -/
theorem reducedClass_eq_of_isReduction' {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    /- The `reducedClass` projection is a defaulted STRUCTURE FIELD, not a
    definitional function of `sa`; an arbitrary `sa` may override the default.
    Therefore the divisor-class formula used below must be supplied explicitly. -/
    (hReducedClass :
      sa.reducedClass =
        sa.alpha • aClass -
          toJacobian D
            (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
              by
                have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
                have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
                have heq2 : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
                    (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
                  rw [two_zsmul]
                  abel
                rw [heq2]
                exact add_mem h1 h2⟩ : Divisor0 H))
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : F p)
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (hdeg : H.f.natDegree = 5)
    (hD : principalSubgroup H hdeg ≤ D.P)
    (hcur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c0 c1 c2 c3 c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          ua0 ua1 va0 va1 sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c0 c1 c2 c3 c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y) ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hcurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c0 c1 c2 c3 c4
        sa.P1.X sa.P1.Y ua0 ua1 va0 va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (hgcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c0 c1 c2 c3 c4
          sa.P1.X sa.P1.Y ua0 ua1 va0 va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (hr : isReduction' sa c0 c1 c2 c3 c4 ua0 ua1 va0 va1 hcur hgcd hcurT hgcdT)
    -- **Added this pass — the two missing Mumford-identity hypotheses
    -- flagged (but not yet added) in an earlier pass's note near line
    -- ~698.** Without these, nothing pins `(ua,va)` down as an actual
    -- Mumford representative of `alpha•aClass` (equivalently, nothing
    -- gives `ordAt Q (-va) 1 = 1` at `Q ∈ Sanchor`, which the assembly
    -- needs to connect `hAlphaRep`'s `divToPair (-va) 1 Sanchor` to
    -- `CAWitness.lean`'s `f`-construction at the point-set level — see
    -- `ROADMAP-principal-witness-assembly.md`'s latest pass note). `alpha`,
    -- `alpha'`, and `a` (`aClass`) are already given to this theorem via
    -- `sa`; these two hypotheses are the same kind of "caller supplies the
    -- real Mumford data" premise `hcur`/`hgcd`/`hr` already are — not a
    -- gap needing a separate proof, just parameters that were missing
    -- from the signature. `hMumfordUa` pins `(ua,va)` to `alpha•aClass`
    -- itself; `hMumfordTarget` pins `(u,v)` (via `sa.toSampleTarget`) to
    -- the reduced target — the `Ypoly4`-shaped analogue already required
    -- by `dvd_N_ua`/`dvd_N_u4` (`Reduce/AlphaReduce.lean`) wherever this
    -- theorem's proof needs to reach into that machinery.
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4
      sa.toSampleTarget.u0 sa.toSampleTarget.u1 sa.toSampleTarget.v0 sa.toSampleTarget.v1)
    (Sanchor S : Finset H.Point) (va u v : Polynomial (F p))
    (hva : va = (Polynomial.C va1 : Polynomial (F p)) * (Polynomial.X : Polynomial (F p))
      + (Polynomial.C va0 : Polynomial (F p)))
    (hu : u = (Polynomial.X : Polynomial (F p)) ^ 2 + (Polynomial.C sa.toSampleTarget.u1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)))
    (hv : v = (Polynomial.C sa.toSampleTarget.v1 : Polynomial (F p)) * (Polynomial.X : Polynomial (F p))
      + (Polynomial.C sa.toSampleTarget.v0 : Polynomial (F p)))
    (hsuppAnchor : ∀ P, P ∉ Sanchor → ordAt (H := H) P (-va) 1 = 0)
    -- **Corrected this pass — `2•[δ₀]` replaced by `[δ₀]+[ιδ₀]`.** The
    -- `2•[δ₀]` correction here was never derived from anything; it was
    -- copied from `sa.reducedClass`'s own `-2•[δ₀]` (which IS honestly
    -- derived, as `s(P1)+s(P2)` applied twice via the `s`-embedding,
    -- `DivisorClassGroup.lean`) by pattern-matching shape alone, with no
    -- actual argument that a Mumford-reduced representative of an
    -- arbitrary `alpha•aClass` needs the SAME normalization `s` happens
    -- to produce. `PrincipalWitnessAssembly.lean`'s own note (search
    -- "unrelated to, and not derived from") already flagged this as
    -- unjustified. The only correction term this project can actually
    -- derive unconditionally (Weierstrass or not) is `[δ₀]+[ιδ₀]`, via
    -- `divToPair_linX_eq` (`HyperellipticClassProof.lean`, 0-`sorry`):
    -- `linX(δ₀.X)`'s own zero divisor is *exactly* `single δ₀ +
    -- single (Point.iota δ₀)`, unconditionally. This is also the
    -- normalization `PrincipalWitnessStep4.lean`'s
    -- `cIotaAmIotaT_mem_principalSubgroup` (†) actually produces — that
    -- theorem was checked (ChatGPT + Claire) to be FALSE if its own
    -- `2•[δ₀]` version is attempted, precisely because `2[δ₀] -
    -- ([δ₀]+[ιδ₀]) = [δ₀]-[ιδ₀]` is a nontrivial extra class for generic
    -- `δ₀` (confirmed independently via a second ChatGPT consultation,
    -- this pass — see the `q := [δ₀]-[ιδ₀]` discussion there). Restating
    -- `hmemAnchor`/`hAlphaRep` here to match removes the mismatch at its
    -- root, rather than trying to bridge `2•[δ₀]` and `[δ₀]+[ιδ₀]` after
    -- the fact (which would need `2[δ₀]-[ιδ₀]` provably principal — false
    -- in general, exactly the discrepancy just described).
    (hmemAnchor : (divToPair (H := H) (-va) 1 Sanchor -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H)
    (hAlphaRep : sa.alpha • aClass =
      toJacobian D (Subtype.mk (divToPair (H := H) (-va) 1 Sanchor -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmemAnchor))
    (hsupp : ∀ P, P ∉ S → ordAt (H := H) P (-v) 1 = 0)
    -- **THE MISSING LINK, added this pass (was flagged in the docstring
    -- above as "still needed" but never actually written).** Without this,
    -- `S` is an arbitrary `Finset` satisfying `hsupp`/`hmem` with no
    -- connection to `u` (equivalently, to `sa.toSampleTarget`'s reduced
    -- Mumford pair) at all — nothing prevents `S` from being some unrelated
    -- point set that happens to make `(-v,1)`'s divisor degree-0. Stated the
    -- only way sound for a possibly-irreducible `u` (no splitting over
    -- `F p` assumed): every `P ∈ S` is a genuine root of the Mumford pair
    -- `(u,v)` (`hSmem`), and conversely `S`'s cardinality already accounts
    -- for all of `u`'s roots with multiplicity — via `u`'s squarefreeness
    -- (`hufree`, from `hgcd`/`hgcdT`'s coprimality, which already rules out
    -- repeated roots at this stage) forcing exactly `u.natDegree` many
    -- points, matching `S.card = u.natDegree` (`hScard`). Mirrors the
    -- analogous unstated gap on the anchor side (`hSanchorMem`/`hufreeAnchor`
    -- /`hSanchorCard`, against the anchor's own quadratic — see the note
    -- below on why the anchor quadratic itself needed naming for the first
    -- time here, it wasn't previously a parameter).
    (hSmem : ∀ P ∈ S, u.eval P.X = 0 ∧ P.Y = v.eval P.X)
    (hufree : Squarefree u)
    (hScard : S.card = u.natDegree)
    -- **Anchor-side mirror.** `ua0,ua1` (already parameters, feeding `hcur`/
    -- `hgcd`/etc.) were never assembled into a polynomial the way `u` is
    -- (`hu`) — `hAlphaRep`'s `va`/`Sanchor` had no linked quadratic at all
    -- before this pass, which is the anchor-side half of the same gap.
    -- Named `ua` here for the first time, mirroring `hu`'s shape exactly.
    (ua : Polynomial (F p))
    (hua : ua = (Polynomial.X : Polynomial (F p)) ^ 2
      + (Polynomial.C ua1 : Polynomial (F p)) * Polynomial.X
      + (Polynomial.C ua0 : Polynomial (F p)))
    (hSanchorMem : ∀ P ∈ Sanchor, ua.eval P.X = 0 ∧ P.Y = va.eval P.X)
    (huafree : Squarefree ua)
    (hSanchorCard : Sanchor.card = ua.natDegree)
    -- **Corrected this pass, matching `hmemAnchor`/`hAlphaRep` above.**
    -- Same `2•[δ₀] → [δ₀]+[ιδ₀]` fix, same reason: this is `S`'s own
    -- Mumford-reduced-representative correction, and `[δ₀]+[ιδ₀]` is the
    -- one this project can actually derive (`divToPair_linX_eq`), not
    -- `2•[δ₀]`.
    (hmem : (divToPair (H := H) (-v) 1 S -
      (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H)
    -- **`q`, the compensating term the goal now genuinely needs.**
    -- `sa.reducedClass := alpha•aClass - N₂({P1}+{P2})` where
    -- `N₂(X) := X - 2•[δ₀]` (`reducedClass`'s own structure-default
    -- field, unchanged by this pass — it is honestly derived from the
    -- `s`-embedding applied twice, `s(P1)+s(P2)`, and stays `N₂`
    -- deliberately: it is NOT the same object as `hAlphaRep`'s anchor
    -- `Sanchor`, so it does not automatically inherit `hAlphaRep`'s
    -- `Nι` normalization just because that field was edited above).
    -- `PrincipalWitnessStep4.lean`'s proved fact (†) is stated in terms
    -- of `Nι(X) := X - ([δ₀]+[ιδ₀])` throughout (its own `C`, `A :=
    -- {P1,P2}`, and `S := ι(T)` are ALL `Nι`-normalized there — §5 of
    -- this pass's ChatGPT consultation confirms `Nι`-differences of
    -- same-normalization divisors are normalization-independent, so (†)
    -- composes cleanly to `Nι(Sanchor) - Nι({P1,P2}) = Nι(S)`, no `q`
    -- needed internally). The ONLY place `q` has to appear is bridging
    -- `reducedClass`'s own `N₂({P1,P2})` term to that `Nι({P1,P2})`.
    -- **Sign correction, this pass**: an earlier draft of this note computed
    -- `N₂(X) - Nι(X) = 2•[δ₀] - ([δ₀]+[ιδ₀]) = [δ₀]-[ιδ₀]` and called that
    -- `q` — but `2•[δ₀] - ([δ₀]+[ιδ₀]) = [δ₀] - [ιδ₀]` is right arithmetic,
    -- the mislabeling was calling it `N₂(X)-Nι(X)` when it is in fact
    -- `Nι(X)-N₂(X)` (`Nι(X) - N₂(X) = -([δ₀]+[ιδ₀]) - (-2•[δ₀]) =
    -- [δ₀]-[ιδ₀]`, whereas `N₂(X)-Nι(X)` is the negative of that,
    -- `[ιδ₀]-[δ₀]`). Re-derived directly rather than trusted: `q` is
    -- defined below as `[ιδ₀]-[δ₀]` (not `[δ₀]-[ιδ₀]`) so that `N₂(X) =
    -- Nι(X) + q` holds as stated (checked: `Nι(X)+q = X-([δ₀]+[ιδ₀]) +
    -- [ιδ₀]-[δ₀] = X - 2[δ₀] = N₂(X)`, correct). This gives
    -- `sa.reducedClass = alpha•aClass - Nι({P1,P2}) - q`. Composed with
    -- `hAlphaRep`/(†)'s `Nι(Sanchor) - Nι({P1,P2}) = Nι(S)`, this gives
    -- `sa.reducedClass = Nι(S) - q`, i.e. `sa.reducedClass + q = Nι(S)`
    -- — matching the sign below, now with `q`'s definition actually
    -- consistent with that derivation (checked by hand this pass, not
    -- carried forward from the earlier mislabeled version). `q = 0`
    -- exactly when `δ₀ - (a fixed point at infinity)` is 2-torsion on the
    -- smooth model — a genuine extra condition on the caller-supplied
    -- `δ₀`, not proved or assumed here. -/
    (q : Jacobian H D)
    (hq : q = toJacobian D (Subtype.mk (single (Point.iota δ₀) - single δ₀ : Divisor H)
      (single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀)) )
    -- **Correction, this pass: the previous pass's `hAnchorRoots`/
    -- `hSanchorEq` (`Sanchor = {sa.P1, sa.P2}`) was WRONG and is removed
    -- here.** Re-reading `CAWitness.lean`'s own module docstring
    -- carefully: `C := [Ra1]+[Ra2] := Sanchor` (the anchor, a
    -- representative of `alpha•aClass` itself) and `A := [P1]+[P2] :=
    -- {sa.P1,sa.P2}` (the SEPARATE pair being subtracted, `C - A`) are
    -- two genuinely different divisors — `Sanchor` is not, and has no
    -- reason to be, `{sa.P1,sa.P2}`. The roadmap's "Gap found and
    -- closed" note (`ROADMAP-principal-witness-assembly.md`) was
    -- similarly re-checked this pass: it only ever asks that `A` (=
    -- `CAWitness.lean`'s `P1,P2` slot) be tied to `sa.P1,sa.P2` — which
    -- the structure default already does for free, no proof needed —
    -- never that `Sanchor` equal `{sa.P1,sa.P2}`. What (†)
    -- (`PrincipalWitnessStep4.lean`'s `cIotaAmIotaT_mem_principalSubgroup`)
    -- actually needs is `Sanchor`'s OWN two named points (its `Ra1,Ra2`
    -- slot), independent of `sa.P1,sa.P2` — supplied here as fresh
    -- points `Ra1 Ra2 : H.Point`, split off `ua` via
    -- `quadratic_eq_mul_X_sub_C` exactly the way `sa.P1,sa.P2` split off
    -- `u` elsewhere in this file (`hcur`/`hgcd`'s fully-split branch).
    -- Fully-split case only (`hRa12Xne`); tangent case for `Sanchor`
    -- left out of scope, mirroring `hcurT`/`hgcdT`'s existing split.
    (Ra1 Ra2 : H.Point)
    (hRa12Xne : Ra1.X ≠ Ra2.X)
    (hRa1Root : ua.IsRoot Ra1.X) (hRa2Root : ua.IsRoot Ra2.X)
    (hRa1Y : Ra1.Y = va.eval Ra1.X) (hRa2Y : Ra2.Y = va.eval Ra2.X)
    -- **`S`'s own split, mirroring `Sanchor`'s.** Same shape as
    -- `Ra1,Ra2` above but against `u`/`v`/`S` instead of `ua`/`va`/
    -- `Sanchor` — named `T1,T2` to match `PrincipalWitnessStep4.lean`'s
    -- own `T1X,T2X` naming for (†)'s residual points.
    (T1 T2 : H.Point)
    (hT12Xne : T1.X ≠ T2.X)
    (hT1Root : u.IsRoot T1.X) (hT2Root : u.IsRoot T2.X)
    (hT1Y : T1.Y = v.eval T1.X) (hT2Y : T2.Y = v.eval T2.X)
    -- **Final assembly wiring, added this pass — closes the `sorry`.**
    -- Everything below is "caller supplies the real Mumford/witness data,"
    -- same category as `hMumfordUa`/`hMumfordTarget`/`hAnchorRoots` above,
    -- not a proof obligation: it instantiates
    -- `PrincipalWitnessCAConnection.lean`'s `divToPair_negVa_one_Sanchor_eq`/
    -- `divToPair_negV_one_S_eq` (collapsing `divToPair (-va) 1 Sanchor` and
    -- `divToPair (-v) 1 S` to `single Ra1 + single Ra2` /
    -- `single T1 + single T2`) and `PrincipalWitnessFinalAssembly.lean`'s
    -- `cAmιTmδmιδ_mem_of_le` (the concrete-coordinate (†), giving `D.P`
    -- membership of exactly the divisor this goal needs).
    [DecidableEq H.Point]
    (hchar : (2 : F p) ≠ 0) (hsf : Squarefree H.f)
    -- Cofactor data for `Sanchor_eq..`'s `ordAt`-at-a-Mumford-point route
    -- (`SanchorMumfordOrdAt.lean`'s own required shape), anchor and target
    -- side. `Uco`/`UcoT` are `pairNorm H (-va) 1`/`pairNorm H (-v) 1`'s
    -- cofactor after dividing out `ua`/`u`.
    (Uco UcoT : Polynomial (F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (F p)) = ua * Uco)
    (hUco_ne : Uco ≠ 0)
    (hUco_evalRa1 : Uco.eval Ra1.X ≠ 0) (hUco_evalRa2 : Uco.eval Ra2.X ≠ 0)
    (hAUT : pairNorm H (-v) (1 : Polynomial (F p)) = u * UcoT)
    (hUcoT_ne : UcoT ≠ 0)
    (hUcoT_evalT1 : UcoT.eval T1.X ≠ 0) (hUcoT_evalT2 : UcoT.eval T2.X ≠ 0)
    (hRa1Y_ne : Ra1.Y ≠ 0) (hRa2Y_ne : Ra2.Y ≠ 0)
    (hT1Y_ne : T1.Y ≠ 0) (hT2Y_ne : T2.Y ≠ 0)
    -- **The `CAWitness` identification** (`ua,va` ARE `uCANew,-bCA` built
    -- from `Ra1,Ra2,sa.P1,sa.P2`), the honest minimal hypothesis per
    -- `PrincipalWitnessCAConnection.lean`'s header — matches this project's
    -- "caller supplies the real Mumford data" convention, not derived.
    (hdet : (caInterpMatrix Ra1.X Ra2.X sa.P1.X sa.P2.X).det ≠ 0)
    (hlead : caCoeff Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y 3 ≠ 0)
    (h1P1 : Ra1.X ≠ sa.P1.X) (h1P2 : Ra1.X ≠ sa.P2.X)
    (h2P1 : Ra2.X ≠ sa.P1.X) (h2P2 : Ra2.X ≠ sa.P2.X) (hPP : sa.P1.X ≠ sa.P2.X)
    (hRa1_curve : Ra1.Y ^ 2 = H.f.eval Ra1.X) (hRa2_curve : Ra2.Y ^ 2 = H.f.eval Ra2.X)
    (hP1_curve : sa.P1.Y ^ 2 = H.f.eval sa.P1.X) (hP2_curve : sa.P2.Y ^ 2 = H.f.eval sa.P2.X)
    (hP1Y_ne : sa.P1.Y ≠ 0) (hP2Y_ne : sa.P2.Y ≠ 0)
    (hU_evalRa1 : (uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).eval Ra1.X ≠ 0)
    (hU_evalRa2 : (uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).eval Ra2.X ≠ 0)
    (hU_evalP1 : (uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).eval sa.P1.X ≠ 0)
    (hU_evalP2 : (uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).eval sa.P2.X ≠ 0)
    (hU_ne0 : uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y ≠ 0)
    -- `PtT1,PtT2`: `uCANew`'s own (unconjugated) residual roots — the
    -- `S := ι(T)` convention means `T1,T2` (this theorem's, roots of `u`)
    -- are their hyperelliptic conjugates.
    (PtT1 PtT2 : H.Point)
    (hPtT1X : PtT1.X ≠ PtT2.X)
    (hPtT1 : (uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).IsRoot PtT1.X)
    (hPtT2 : (uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).IsRoot PtT2.X)
    (Q1 Q2 : Polynomial (F p))
    (hQ1_def : uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y =
      (Polynomial.X - Polynomial.C PtT1.X) * (Polynomial.X - Polynomial.C PtT2.X) * Q1)
    (hQ1T1 : Q1.eval PtT1.X ≠ 0)
    (hQ2_def : uCANew H Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y =
      (Polynomial.X - Polynomial.C PtT2.X) * (Polynomial.X - Polynomial.C PtT1.X) * Q2)
    (hQ2T2 : Q2.eval PtT2.X ≠ 0)
    (hAeval1 : (denomPolyCA Ra1.X Ra2.X sa.P1.X sa.P2.X : Polynomial (F p)).eval PtT1.X ≠ 0)
    (hAeval2 : (denomPolyCA Ra1.X Ra2.X sa.P1.X sa.P2.X : Polynomial (F p)).eval PtT2.X ≠ 0)
    (hPtT1Y : PtT1.Y = (bCA Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).eval PtT1.X)
    (hPtT1Y_ne : PtT1.Y ≠ 0)
    (hPtT2Y : PtT2.Y = (bCA Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y).eval PtT2.X)
    (hPtT2Y_ne : PtT2.Y ≠ 0)
    (h1δ : PtT1.X ≠ δ₀.X) (h2δ : PtT2.X ≠ δ₀.X) (hδY : δ₀.Y ≠ 0)
    (hT1eq : T1 = Point.iota PtT1) (hT2eq : T2 = Point.iota PtT2)
    (hsupp_f : ∀ P, P ∉ ({Ra1, Ra2, Point.iota sa.P1, Point.iota sa.P2, PtT1, PtT2} :
        Finset H.Point) →
      ordAt P (-bCA Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y) (1 : Polynomial (F p)) = 0)
    (hspec_f : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H (-bCA Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y) 1} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({Ra1, Ra2, Point.iota sa.P1, Point.iota sa.P2, PtT1, PtT2} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 (-bCA Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y)
          (1 : Polynomial (F p))).toNat)]
    (hsupp_hT : ∀ P, P ∉ ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} :
        Finset H.Point) →
      ordAt P ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : Polynomial (F p)) = 0)
    (hspec_hT : ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count (Associates.mk (Ideal.span
        ({toPair H ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) 0} :
          Set (CoordinateRing H)))).factors ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P)
    [∀ P : ({PtT1, PtT2, Point.iota PtT1, Point.iota PtT2, δ₀, Point.iota δ₀} : Finset H.Point),
      Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^
        (ordAt P.1 ((linX PtT1.X * linX PtT2.X) * linX δ₀.X) (0 : Polynomial (F p))).toNat)]
    [∀ (a : F p) (Sfin : Finset H.Point),
      ∀ P : Sfin, Module.Finite (F p) (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 (linX a) 0).toNat)]
    (hspec_linX : ∀ (a : F p), ∀ vv : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk vv.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H)))).factors
          ≠ 0 → ∃ P, vv.asIdeal = pointIdeal P) :
    sa.reducedClass + q =
      toJacobian D (Subtype.mk (divToPair (H := H) (-v) 1 S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmem) := by
  classical
  -- **`Sanchor`'s own split, correctly**: `Sanchor = {Ra1, Ra2}`
  -- (`Sanchor`'s own two named points), NOT `{sa.P1, sa.P2}`. Same
  -- `Sanchor_eq_of_anchor_roots` lemma as before, but instantiated at
  -- `Ra1,Ra2` (fresh points naming `Sanchor`'s own roots) instead of
  -- `sa.P1,sa.P2` (a different, independently-existing pair).
  have hRa12ne : Ra1 ≠ Ra2 := fun h => hRa12Xne (by rw [h])
  have hSanchorEq : Sanchor = ({Ra1, Ra2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots ua va hua huafree
      Ra1 Ra2 hRa12ne hRa12Xne ⟨hRa1Root, hRa2Root⟩ hRa1Y hRa2Y Sanchor
      hSanchorMem hSanchorCard
  -- **`S`'s own split**, same lemma applied to `u`/`v`/`S`/`T1`/`T2`.
  have hT12ne : T1 ≠ T2 := fun h => hT12Xne (by rw [h])
  have hSEq : S = ({T1, T2} : Finset H.Point) :=
    Sanchor_eq_of_anchor_roots (ua0 := sa.toSampleTarget.u0) (ua1 := sa.toSampleTarget.u1)
      u v hu hufree
      T1 T2 hT12ne hT12Xne ⟨hT1Root, hT2Root⟩ hT1Y hT2Y S hSmem hScard
  -- **Collapse `divToPair (-va) 1 Sanchor` and `divToPair (-v) 1 S`** to
  -- the concrete two-point sums, via `PrincipalWitnessCAConnection.lean`.
  -- `huafree`/`hufree` have type `Squarefree ua`/`Squarefree u`; the
  -- callees below want `Squarefree (X^2+C ua1*X+C ua0)`/the `u` mirror —
  -- the same polynomial via `hua`/`hu`, but not syntactically, so rewrite
  -- the root hypotheses before passing them to the connection lemmas.
  have huafree' : Squarefree (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X
      + Polynomial.C ua0 : Polynomial (F p)) := hua ▸ huafree
  have hufree' : Squarefree (Polynomial.X ^ 2 +
      Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
      + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) := hu ▸ hufree
  -- `hAU`/`hAUT` are stated against `ua`/`u` (this theorem's own named
  -- polynomials); the callees below want the spelled-out quadratic
  -- `X^2+C ua1*X+C ua0`/the `u` mirror — same object via `hua`/`hu`, not
  -- syntactically, so rewrite here too (same pattern as `huafree'`/`hufree'`
  -- just above).
  have hRa1Root' :
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)).IsRoot Ra1.X := by
    rw [← hua]
    exact hRa1Root
  have hRa2Root' :
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)).IsRoot Ra2.X := by
    rw [← hua]
    exact hRa2Root
  have hT1Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot T1.X := by
    rw [← hu]
    exact hT1Root
  have hT2Root' :
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X +
        Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)).IsRoot T2.X := by
    rw [← hu]
    exact hT2Root
  have hAU' : pairNorm H (-va) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C ua1 * Polynomial.X + Polynomial.C ua0 : Polynomial (F p)) * Uco :=
    hua ▸ hAU
  have hAUT' : pairNorm H (-v) (1 : Polynomial (F p)) =
      (Polynomial.X ^ 2 + Polynomial.C sa.toSampleTarget.u1 * Polynomial.X
        + Polynomial.C sa.toSampleTarget.u0 : Polynomial (F p)) * UcoT :=
    hu ▸ hAUT
  have hSanchorSum : divToPair (H := H) (-va) 1 Sanchor = single Ra1 + single Ra2 :=
    DecoupledSystem.divToPair_negVa_one_Sanchor_eq (H := H) hchar
      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (ua0 := ua0) (ua1 := ua1) (va0 := va0) (va1 := va1)
      hf hMumfordUa huafree' va hva Uco hAU' hUco_ne
      Ra1 Ra2 hRa12ne hRa1Y_ne hRa2Y_ne hRa1Root' hRa2Root' hRa1Y hRa2Y
      hUco_evalRa1 hUco_evalRa2 Sanchor hSanchorEq
  have hSSum : divToPair (H := H) (-v) 1 S = single T1 + single T2 :=
    DecoupledSystem.divToPair_negV_one_S_eq (H := H) hchar
      (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (c4 := c4)
      (u0 := sa.toSampleTarget.u0) (u1 := sa.toSampleTarget.u1)
      (v0 := sa.toSampleTarget.v0) (v1 := sa.toSampleTarget.v1)
      hf hMumfordTarget hufree' v hv UcoT hAUT' hUcoT_ne
      T1 T2 hT12ne hT1Y_ne hT2Y_ne hT1Root' hT2Root' hT1Y hT2Y
      hUcoT_evalT1 hUcoT_evalT2 S hSEq
  -- **The concrete-coordinate assembly (†)**: `C - A - ι(T) + [δ₀] + [ιδ₀]
  -- ∈ D.P`, `C := {Ra1,Ra2}`, `A := {sa.P1,sa.P2}`, instantiated at the
  -- actual named points. `T1cur T2cur := T1 T2` via `hT1eq`/`hT2eq`
  -- (`S := ι(T)` convention). `hspec_linX` is the explicit arg right after
  -- `hD` (the `Module.Finite` bracket before it is instance-implicit,
  -- auto-resolved) — an earlier draft of this call jumped straight to
  -- `Ra1.X` and landed it in `hspec_linX`'s slot; fixed here.
  have hDP := cAmιTmδmιδ_mem_of_le (H := H) hdeg hchar hsf D hD
    hspec_linX
    Ra1.X Ra2.X sa.P1.X sa.P2.X Ra1.Y Ra2.Y sa.P1.Y sa.P2.Y
    hdet hlead hRa12Xne h1P1 h1P2 h2P1 h2P2 hPP
    hRa1_curve hRa2_curve hP1_curve hP2_curve
    hRa1Y_ne hRa2Y_ne hP1Y_ne hP2Y_ne
    Ra1 Ra2 sa.P1 sa.P2 (Point.iota sa.P1) (Point.iota sa.P2)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hU_evalRa1 hU_evalRa2 hU_evalP1 hU_evalP2 hU_ne0
    PtT1.X PtT2.X hPtT1 hPtT2 hPtT1X
    Q1 Q2 hQ1_def hQ1T1 hQ2_def hQ2T2
    PtT1 PtT2 δ₀ hAeval1 hAeval2 rfl hPtT1Y hPtT1Y_ne rfl hPtT2Y hPtT2Y_ne
    h1δ h2δ hδY hsupp_f hspec_f hsupp_hT hspec_hT
    T1 T2 hT1eq hT2eq
  -- **Bridge `D.P` membership to a `toJacobian` equation**, exactly the
  -- `s_add_s_eq_s_add_s_iff` pattern (`DivisorClassGroup.lean`), applied to
  -- the concrete divisor `hDP` supplies rather than re-derived generically.
  -- `sa.reducedClass + q - toJacobian D aTarget`, unfolded all the way to
  -- `Divisor0 H` representatives, is EXACTLY `hDP`'s divisor (checked by
  -- hand, this pass, via a symbolic recomputation after the earlier
  -- `N₂(X)-Nι(X)` sign bug was found and `q`'s definition corrected above
  -- to `[ιδ₀]-[δ₀]`) — so this is a single `abel`-after-unfolding argument,
  -- not a multi-step `set`/`map_sub` composition (an earlier draft of this
  -- proof used the latter and had a mismatched decomposition; this version
  -- is the direct, re-verified one).
  set aAnchor : Divisor0 H := ⟨divToPair (H := H) (-va) 1 Sanchor -
    (single δ₀ + single (Point.iota δ₀)), hmemAnchor⟩ with haAnchor_def
  set aTarget : Divisor0 H := ⟨divToPair (H := H) (-v) 1 S -
    (single δ₀ + single (Point.iota δ₀)), hmem⟩ with haTarget_def
  set aP1P2Nι : Divisor0 H := ⟨single sa.P1 + single sa.P2 -
      (single δ₀ + single (Point.iota δ₀)),
    by
      have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
      have h2 := single_sub_single_mem_Divisor0 sa.P2 (Point.iota δ₀)
      have heq2 : single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀)) =
          (single sa.P1 - single δ₀) + (single sa.P2 - single (Point.iota δ₀)) := by abel
      rw [heq2]; exact add_mem h1 h2⟩ with haP1P2Nι_def
  set aQ : Divisor0 H := ⟨single (Point.iota δ₀) - single δ₀,
    single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀⟩ with haQ_def
  -- `reducedClass`'s `N₂({P1,P2})` term equals `Nι({P1,P2}) + q` at the
  -- `Divisor0 H` level (checked: `Nι(P1P2) + q = (P1+P2-δ₀-ιδ₀) +
  -- (ιδ₀-δ₀) = P1+P2-2δ₀ = N₂(P1P2)`, matching `reducedClass`'s structure
  -- default exactly). **Proved via `Subtype.ext`/`congrArg` on the
  -- underlying divisor value, NOT `show`-matching the whole term** — an
  -- earlier draft tried to `show` the RHS of `sa.reducedClass`'s
  -- definitional unfolding verbatim and failed: the `Subtype.mk` proof
  -- component built inline differs syntactically from `reducedClass`'s
  -- own stored proof term, and `show` needs full syntactic (up to defeq)
  -- reconstruction of BOTH components, not just the value, so it never
  -- matched. Proof irrelevance makes the two proof terms interchangeable
  -- for `Jacobian`-level equality, but reaching that needs `Subtype.ext`
  -- (which only asks the VALUES to agree) rather than a raw `show`.
  have hred : sa.reducedClass = sa.alpha • aClass - (toJacobian D aP1P2Nι + q) := by
    have hN2 :
        (⟨single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀,
          by
            have h1 := single_sub_single_mem_Divisor0 sa.P1 δ₀
            have h2 := single_sub_single_mem_Divisor0 sa.P2 δ₀
            have heq2 : single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
                (single sa.P1 - single δ₀) + (single sa.P2 - single δ₀) := by
              rw [two_zsmul]
              abel
            rw [heq2]
            exact add_mem h1 h2⟩ : Divisor0 H) = aP1P2Nι + aQ := by
      apply Subtype.ext
      show single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
        (aP1P2Nι : Divisor H) + (aQ : Divisor H)
      rw [haP1P2Nι_def, haQ_def]
      show single sa.P1 + single sa.P2 - (2 : ℤ) • single δ₀ =
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) +
          (single (Point.iota δ₀) - single δ₀)
      rw [two_zsmul]
      abel
    rw [hReducedClass, hN2, map_add, hq]
  rw [hred, hAlphaRep]
  -- Goal now: `toJacobian D aAnchor - (toJacobian D aP1P2Nι + q) + q = toJacobian D aTarget`,
  -- which simplifies (the two `q`s cancel) to
  -- `toJacobian D aAnchor - toJacobian D aP1P2Nι = toJacobian D aTarget`,
  -- i.e. `toJacobian D (aAnchor - aP1P2Nι - aTarget) = 0`, i.e.
  -- `aAnchor - aP1P2Nι - aTarget ∈ D.P` (as `Divisor0 H` mod `D.P`) —
  -- exactly `hDP` once `hSanchorSum`/`hSSum` unfold the `divToPair` terms.
  have hcancel : toJacobian D aAnchor - (toJacobian D aP1P2Nι + q) + q =
      toJacobian D aAnchor - toJacobian D aP1P2Nι := by abel
  have hcoe : ((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H) =
      (single Ra1 + single Ra2 - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀) : Divisor H) := by
    show (aAnchor.1 - aP1P2Nι.1) - aTarget.1 =
      single Ra1 + single Ra2 - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
    rw [haAnchor_def, haP1P2Nι_def, haTarget_def]
    show (divToPair (H := H) (-va) 1 Sanchor - (single δ₀ + single (Point.iota δ₀))) -
        (single sa.P1 + single sa.P2 - (single δ₀ + single (Point.iota δ₀))) -
        (divToPair (H := H) (-v) 1 S - (single δ₀ + single (Point.iota δ₀))) =
      single Ra1 + single Ra2 - single sa.P1 - single sa.P2 -
        single T1 - single T2 + single δ₀ + single (Point.iota δ₀)
    rw [hSanchorSum, hSSum]
    abel
  have hmemD : (((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
      ((aTarget : Divisor0 H) : Divisor H)) ∈ D.P := by
    rw [hcoe]; exact hDP
  have hmemD' : (((aAnchor - aP1P2Nι - aTarget : Divisor0 H)) : Divisor H) ∈ D.P := by
    have hval : (((aAnchor - aP1P2Nι - aTarget : Divisor0 H)) : Divisor H) =
        (((aAnchor - aP1P2Nι : Divisor0 H) : Divisor H) -
          ((aTarget : Divisor0 H) : Divisor H)) := by
      show aAnchor.1 - aP1P2Nι.1 - aTarget.1 = (aAnchor.1 - aP1P2Nι.1) - aTarget.1
      rfl
    rw [hval]; exact hmemD
  have hmemAddSub : (aAnchor - aP1P2Nι - aTarget : Divisor0 H) ∈
      D.P.addSubgroupOf (Divisor0 H) := by
    rw [AddSubgroup.mem_addSubgroupOf]; exact hmemD'
  have hJeq := (QuotientAddGroup.eq_iff_sub_mem
    (N := D.P.addSubgroupOf (Divisor0 H))).mpr hmemAddSub
  rw [hcancel, ← map_sub]
  change
    QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H)) (aAnchor - aP1P2Nι) =
      QuotientAddGroup.mk' (D.P.addSubgroupOf (Divisor0 H)) aTarget
  exact hJeq

/-! ## Task (B): the exceptional locus `Bad` (left abstract — see module
docstring; Step 2 of the roadmap has to happen, empirically, before this
can be pinned down to a real definition) -/

/-- **Placeholder for the exceptional set `Bad`.** ROADMAP-alpha-locus.md
Step 2 is explicit that this needs to be checked numerically (does `D ~
K_C` actually correlate with a degree jump? how large is the flagged-bad
set as a fraction of `F ell`?) before it can be *defined*, let alone shown
small. Rather than guess, this is left as an unconstrained parameter of
`decoupledSystem_degree_uniform` below — the theorem statement quantifies
over "some `Bad`, satisfying `IsSmallExceptionalSet`" and leaves both the
set and the proof that any candidate satisfies the smallness predicate as
future work. This is weaker than committing to `D ~ K_C` as the answer
(which the roadmap flags as unverified) and weaker than the roadmap's own
"actual target theorem" sketch, which already presupposes `Bad` is
in hand — intentionally so, since asserting a specific `Bad` here would be
asserting something nobody has checked. -/
def IsSmallExceptionalSet {p : ℕ} (_ell : ℕ) (_Bad : Set (ℤ × ℤ)) : Prop :=
  -- Left `True` deliberately: this is a NAMED gap, not a filled-in
  -- definition. Whatever "small" ends up meaning (finite? o(ell)? an
  -- explicit count, per the roadmap's own preference for "better, an
  -- explicit small count" over a purely qualitative notion?) is exactly
  -- what Step 2's numerical check has to determine before this predicate
  -- can be given real content. Stating it as `True` makes
  -- `decoupledSystem_degree_uniform` below TYPECHECK with the right
  -- shape while making the vacuity impossible to miss (grep `IsSmallExceptionalSet`
  -- shows exactly one definition, immediately visible as a stub).
  True

/-! ## Step 3: the target theorem itself, stated (not proved)

This is `decoupledSystem_degree_uniform` from ROADMAP-alpha-locus.md's "The
actual target theorem" box, now written against `SampleTargetFromAlpha`
(task (A) above) instead of the roadmap's placeholder prose. The
`Fintype`/cardinality bound is stated over the `F_p`-rational points of
`decoupledSystem`'s solution variety, matching the roadmap's own framing of
`X(Delta)` as literally that variety's point count intersected with `F^4` —
here specialized to "the whole variety has ≤ d points" (stronger, and what
the roadmap's two-line counting argument in the TL;DR actually needs: a
bound on `deg(alpha,alpha')` itself, not merely on its `F`-rational
sub-count). -/

/-- **The uniform-in-`(alpha,alpha')` degree bound.** For all but a "small"
(per `IsSmallExceptionalSet`, itself unpinned — see above) set of
`(alpha,alpha')` pairs, `decoupledSystem`'s solution variety at that pair
has at most `d` points, for a SINGLE `d` independent of `p`,
`(alpha,alpha')`. Per the roadmap's TL;DR, this is what actually closes
advisory-6/7's Question 4 (the 8th-moment gap) via
`B^4 = Σ_Delta X(Delta) ≤ d · #{Delta : X(Delta) > 0}`.

Genuinely new content relative to `decoupledSystem_isRegularSequence`/
`decoupledSystem_zeroDimensional` below: those are stated for a SINGLE
fixed `sa sb : SampleTarget p` (equivalently, one fixed `(alpha,alpha')`
once task (A)'s connection is in place) — this theorem is the
uniform-across-the-whole-family strengthening, and per the roadmap's own
"what this document is not claiming" section, that strengthening is
genuinely new work, not a relabeling of what the fixed-target theorems
already give. **Not proved.** The roadmap's proposed strategy (Step 3):
extend `regularSeq_of_peel_chain`'s peel-chain machinery to track how the
regular-sequence witnesses' degrees vary with `alpha,alpha'`, likely via
showing the relevant resultants/discriminants in the peel chain
(`Nondegenerate`, `CrossNondegenerate`) are themselves bounded-degree
polynomials in `alpha,alpha'`, so degree jumps only occur on their
vanishing locus — that locus becoming the concrete candidate for `Bad`.
None of that is attempted here. -/
theorem decoupledSystem_degree_uniform (p : ℕ) [Fact (Nat.Prime p)]
    [Fact (p ≠ 2)] (c0 c1 c2 c3 c4 : F p) (ell : ℕ) (aClass : Jacobian H D)
    (δ₀ : H.Point) :
    ∃ (d : ℕ) (Bad : Set (ℤ × ℤ)), IsSmallExceptionalSet (p := p) ell Bad ∧
      ∀ (sa sb : SampleTargetFromAlpha p H D aClass δ₀),
        (sa.alpha, sb.alpha) ∉ Bad →
        ∀ (hcurA : curBeforeMonic p c0 c1 c2 c3 c4
            sa.toSampleTarget.u0 sa.toSampleTarget.u1
            sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
          (hcurB : curBeforeMonic p c0 c1 c2 c3 c4
            sb.toSampleTarget.u0 sb.toSampleTarget.u1
            sb.toSampleTarget.v0 sb.toSampleTarget.v1 ≠ 0)
          (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4
              sa.toSampleTarget.u0 sa.toSampleTarget.u1
              sa.toSampleTarget.v0 sa.toSampleTarget.v1)
            (uRS p c0 c1 c2 c3 c4 sa.toSampleTarget.u0 sa.toSampleTarget.u1
              sa.toSampleTarget.v0 sa.toSampleTarget.v1))
          (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4
              sb.toSampleTarget.u0 sb.toSampleTarget.u1
              sb.toSampleTarget.v0 sb.toSampleTarget.v1)
            (uRS p c0 c1 c2 c3 c4 sb.toSampleTarget.u0 sb.toSampleTarget.u1
              sb.toSampleTarget.v0 sb.toSampleTarget.v1)),
          Nat.card (Rdec p ⧸
            Ideal.span (↑(genList p c0 c1 c2 c3 c4
              sa.toSampleTarget sb.toSampleTarget hcurA hcurB hgcdA hgcdB).toFinset :
              Set (Rdec p))) ≤ d := by
  sorry

/-! ## Fixed-target special case, moved here from `DecoupledSystemRegular.lean`

Per the request that motivated this file: these two theorems are the
`Bad`-free, single-`(alpha,alpha')` special case of
`decoupledSystem_degree_uniform` above (well, of its `IsRegular`/
`Module.Finite` formulation rather than the `Nat.card ≤ d` one — see the
note after `decoupledSystem_zeroDimensional` below on reconciling the two
statement styles). They are UNCHANGED from `DecoupledSystemRegular.lean` —
same statement, same `sorry`, same proof term where one exists — only
relocated, so that file's `Idx`/`Rdec`/peel-chain apparatus stays scoped to
"machinery for one fixed target" and this file stays scoped to "how the
family varies with `alpha`," matching the module docstring's stated
organizing principle.

**Action required to actually finish this move**: delete
`decoupledSystem_isRegularSequence` and `decoupledSystem_zeroDimensional`
from the end of `DecoupledSystemRegular.lean` once this file compiles
against them here — they are reproduced below, not yet removed from their
old location, since removing them there is a one-line edit to that file
best done alongside compiling this one (see "What's left to do" at the
bottom of this docstring). -/

/-- **The paper's actual claim, fixed-target case.** Moved verbatim from
`DecoupledSystemRegular.lean` (see that file's own docstring for the full
history of `hndA`/`hndB` being added). -/
theorem decoupledSystem_isRegularSequence (p : ℕ) [Fact (Nat.Prime p)]
    [Fact (p ≠ 2)] (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hndA : Nondegenerate p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA)
    (hndB : Nondegenerate p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB)
    (hcross : CrossNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    -- `regularSeq_of_peel_chain`'s current signature (`PeelChainAssembly.lean`,
    -- as actually built against the `ZeroD` folder) takes two more
    -- hypotheses beyond what this theorem previously threaded through:
    -- `hpeel` (`PeelChainNondegenerate`) and `htop_ne_smul` (Gap C, the
    -- 12-generator ideal is proper). Added here as plain pass-through
    -- hypotheses, matching this project's existing convention of exposing
    -- genuinely-open mathematical content as an explicit hypothesis rather
    -- than asserting it — not new content invented at this call site.
    (hpeel : PeelChainNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (htop_ne_smul : (⊤ : Ideal (Rdec p)) ≠
      Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) • ⊤) :
    RingTheory.Sequence.IsRegular (Rdec p)
      (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :=
  regularSeq_of_peel_chain p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB hndA hndB hcross
    hpeel htop_ne_smul

/-- **Standalone bridge lemma**, deliberately generic in `R`/`l` (no
`Genus2Lean`-specific content) so it can be applied to `genList ...`
without Lean ever needing to `whnf`-unfold `genList`'s own definition —
that unfolding is exactly what blew the heartbeat budget when this was
first written inline against the concrete term. `Ideal.ofList l :=
Ideal.span {r | r ∈ l}` (`Mathlib.RingTheory.Regular.RegularSequence`);
`↑l.toFinset = {r | r ∈ l}` as a `Set` is `List.coe_toFinset`. -/
theorem ideal_span_toFinset_eq_ofList {R : Type*} [CommSemiring R] [DecidableEq R]
    (l : List R) :
    Ideal.span (↑l.toFinset : Set R) = Ideal.ofList l := by
  rw [List.coe_toFinset]

/-- **The dimension-0 corollary, fixed-target case.**

**Closed this pass** via `Module.Finite.quotient_of_isRegular_of_length_eq_card`
(`RegularSequenceFiniteQuotient.lean`) — the generic "length-`n` regular
sequence in an `n`-variable `MvPolynomial` over a field gives a
finite-dimensional quotient" lemma the file's own docstring earlier
flagged as a Mathlib-API gap "not yet surveyed." That gap is what
`RegularSequenceFiniteQuotient.lean` closes; this theorem is now a
direct instantiation, not new content.

**Two hypotheses added relative to the previous (`sorry`) signature**:
`hpeel : PeelChainNondegenerate ...` and `htop_ne_smul : ⊤ ≠
Ideal.ofList (genList ...) • ⊤`. These are exactly what
`decoupledSystem_isRegularSequence` above already needs to produce
`IsRegular` in the first place — this theorem's conclusion is strictly
downstream of that one (`Module.Finite` needs `IsRegular` as an input,
it doesn't derive it), so it inherits the same open-mathematical-content
hypotheses rather than hiding them. Not new content invented at this
call site, matching this project's existing convention (see
`decoupledSystem_isRegularSequence`'s own docstring note on `hpeel`/
`htop_ne_smul`).

**Reconciling this with `decoupledSystem_degree_uniform` above**: that
theorem's conclusion is phrased as `Nat.card (Rdec p ⧸ _) ≤ d` rather than
`Module.Finite (F p) (Rdec p ⧸ _)`, because a uniform numeric bound `d` is
what the TL;DR's counting argument actually needs (`Module.Finite` alone
doesn't bound the finite dimension, only assert finiteness) — but
`Nat.card` of a quotient is only meaningful once you know the quotient IS
finite, i.e. once you have THIS theorem's conclusion (or its `alpha`-
parametrized generalization) in hand first. So the intended relationship,
once both are proved, is: `decoupledSystem_zeroDimensional`-for-each-target
gives finiteness pointwise, and `decoupledSystem_degree_uniform` is the
separate, additional claim that the resulting finite cardinalities are
BOUNDED as the target varies — not a formal corollary of finiteness alone.
This reconciliation is recorded here because the two theorems' conclusions
don't obviously compose, and a future pass proving one should not assume
it trivially yields the other. -/
theorem decoupledSystem_zeroDimensional (p : ℕ) [Fact (Nat.Prime p)]
    [Fact (p ≠ 2)] (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hndA : Nondegenerate p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA)
    (hndB : Nondegenerate p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB)
    (hcross : CrossNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (hpeel : PeelChainNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB)
    (htop_ne_smul : (⊤ : Ideal (Rdec p)) ≠
      Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) • ⊤) :
    Module.Finite (F p) (Rdec p ⧸
      Ideal.span (↑(genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).toFinset :
        Set (Rdec p))) := by
  have hreg :
      RingTheory.Sequence.IsRegular (Rdec p)
        (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :=
    decoupledSystem_isRegularSequence p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
      hndA hndB hcross hpeel htop_ne_smul
  -- `Ideal.span ↑l.toFinset = Ideal.ofList l`: both are the ideal generated by
  -- the *set* of the list's elements (`Ideal.ofList l := Ideal.span {r | r ∈ l}`,
  -- `RegularSequence.lean`), and `↑l.toFinset = {r | r ∈ l}` as a `Set` — the
  -- standard `List.coe_toFinset` identification. Proved as a STANDALONE lemma
  -- over a fully generic `l : List R`, deliberately NOT inlined against the
  -- concrete `genList ...` term: unifying/`whnf`-reducing through `genList`'s
  -- actual 12-generator definition (each generator itself built from the
  -- tower/derivation machinery) inside `ext`/`simp` blew the heartbeat budget
  -- in an earlier version of this proof, even though the fact being proved
  -- has nothing to do with what the list's elements actually are. Isolating
  -- it as its own generic lemma means `ext`/`simp` only ever see an opaque
  -- `l : List R`, not `genList`'s expansion.
  have hspan_eq :
      (Ideal.span (↑(genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).toFinset :
          Set (Rdec p))) =
        Ideal.ofList (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :=
    ideal_span_toFinset_eq_ofList _
  rw [hspan_eq]
  -- `genList_length` gives `.length = Fintype.card Idx`;
  -- `Module.Finite.quotient_of_isRegular_of_length_eq_card` wants
  -- `.length = Nat.card Idx`. Bridge via `Nat.card_eq_fintype_card`
  -- (`Nat.card α = Fintype.card α` for `[Fintype α]`, standard Mathlib4).
  have hlen : (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).length =
      Nat.card Idx := by
    rw [Nat.card_eq_fintype_card]
    exact genList_length p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
  exact Module.Finite.quotient_of_isRegular_of_length_eq_card
    (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) hreg hlen

/-! ## What's left to do (honest status, not a completed checklist)

1. ~~**Delete** the two theorems above from the end of
   `DecoupledSystemRegular.lean`~~ **Done** (separate pass, this session):
   `decoupledSystem_isRegularSequence`/`decoupledSystem_zeroDimensional`
   are removed from `DecoupledSystemRegular.lean`'s end and now live only
   here; that file has a pointer docstring in their place instead.
2. **`Reduce`** (general Cantor/Mumford reduction of a divisor class) does
   not exist AS LEAN CODE. `SampleTargetFromAlpha.isReduction` is still an
   assumed `Prop` field with no constructor producing a witness anywhere.
   **What changed this pass**: the ALGORITHM `Reduce` needs to implement is
   no longer unknown — `phi_general.zip`'s `build_phi_general!`/
   `phi_residual_general!`/`find_roots_and_points_inplace!` (Julia/Oscar,
   general `K`) is the actual working implementation, and the module
   docstring's "`Reduce`'s actual algorithm, now on file" section records
   the four-step recipe (interpolate `phi` through `P1,P2` and the target
   Mumford pair; form `N=E²-fY²`; divide out known factors; the quotient's
   roots and `-E/Y` give the reduced `(u_RS,v_RS)`) at the level a Lean
   port would need. Porting it — i.e. writing the actual `def Reduce` and
   proving `isReduction` a consequence rather than an assumption — is still
   unstarted; only the "what has to be ported" question is now answered.
3. **`Bad`/`IsSmallExceptionalSet`** is a stub (`:= True`) pending Step 2's
   numerical investigation, which is empirical work outside Lean
   (`HomotopyContinuation.jl` runs across several `(alpha,alpha')`
   instances, and a check of whether `D ~ K_C` correlates with a degree
   jump) that has not been done.
4. **`decoupledSystem_degree_uniform` is `sorry`** and, per the roadmap,
   should be expected to stay that way until (2) and (3) are substantially
   further along — its value right now is as a real, checkable target
   statement, not as a proof.
4.5. **`ROADMAP-reduce-divisor-correctness.md` Steps 0.5/1/2 done this
   pass**: the sign-convention check (§3c) confirmed `reducedClass`'s
   minus-sign definition is correct as written, no fix needed; `isReduction'`
   is now the load-bearing predicate (`isReductionOf` packages it as the
   existential any future `isReduction` field should be instantiated with);
   and `reducedClass_eq_of_isReduction'` above now TYPECHECKS as a named
   `sorry`, closing the "state it, don't prove it yet" half of Step 2. Two
   things flagged rather than resolved while stating it: (a) there is
   genuinely no Mumford-pair-to-`Divisor H` function in
   `PrincipalDivisorSubgroup.lean` — the statement above takes the
   witnessing finite point set `S` and its `hsupp`/`hmem` facts as
   hypotheses rather than computing them, which is the confirmed gap, not
   an oversight; (b) whether `hsupp`'s exact shape (`S` = the coordinate
   pair's full zero locus) is the right one to demand is left open for
   Step 3 to determine empirically while attempting the proof. Step 3
   itself (the three-lemma skeleton, §3a-§3e) is NOT attempted in this
   pass, per the roadmap's own ordering.
5. ~~**`decoupledSystem_zeroDimensional` is `sorry`**~~ **Closed this
   pass**, wired against `RegularSequenceFiniteQuotient.lean`'s
   `Module.Finite.quotient_of_isRegular_of_length_eq_card` (imported
   above). Two hypotheses (`hpeel`, `htop_ne_smul`) were added to this
   theorem's signature to match what `decoupledSystem_isRegularSequence`
   needs to produce `IsRegular` in the first place — no call sites
   elsewhere in the project reference the old signature, so nothing
   downstream needed updating. **Not yet compiled against Claire's
   REPL** — written and reasoned through carefully (the `Ideal.ofList`/
   `Ideal.span ↑l.toFinset` bridge and the `Nat.card`/`Fintype.card`
   bridge were both checked against Mathlib4 source/docs directly, not
   guessed), but this file's actual sorry-count now depends on Claire
   running `lake build` to confirm the whole chain still typechecks.
-/

end DecoupledSystem
end Genus2Lean
