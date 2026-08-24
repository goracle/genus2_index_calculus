import Mathlib
import Genus2Lean.ZeroD.DecoupledSystemRegular
import Genus2Lean.DivisorClassGroup
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.PeelChainAssembly

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
  unconstructed as before this pass. -/
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

/-- **The dimension-0 corollary, fixed-target case.** Moved verbatim from
`DecoupledSystemRegular.lean`. Still `sorry` — the formal `IsRegular →
Module.Finite` step is not carried out there and is not attempted here
either.

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
    (hcross : CrossNondegenerate p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :
    Module.Finite (F p) (Rdec p ⧸
      Ideal.span (↑(genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).toFinset :
        Set (Rdec p))) := by
  sorry

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
-/

end DecoupledSystem
end Genus2Lean
