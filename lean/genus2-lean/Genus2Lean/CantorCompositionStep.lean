import Mathlib

/-!
# Cantor composition preserves the Mumford identity

**Companion to `CantorReductionStep.lean`.** That file closed the
*reduction* half of `cantor_add` (the `while` loop dividing degree down
after composition) — proved, sorry-free, `cantorReductionStep_preserves_mumford'`.
This file attempts the *composition* half: the step BEFORE the reduction
loop, combining two Mumford pairs `(u1,v1)`, `(u2,v2)` into a single
un-reduced pair `(u,v)` via a Bézout/gcd construction, and showing `(u,v)`
still satisfies the Mumford identity if `(u1,v1)` and `(u2,v2)` did.

**Why this is needed now.** `ROADMAP-alpha-locus.md`'s gauge-shift argument
for `matchCount T Δ ≤ 4` needs to shift `alpha ↦ alpha+c` and re-derive
`(alpha+c)•a`'s Mumford pair, THEN call `Reduce` fresh against the shifted
input (shift-then-reduce, not reduce-then-shift — `Reduce`'s actual
signature, `Reduce/AlphaReduce.lean`, has no output-side operation to
shift, only an input-side precomputed `(ua0,ua1,va0,va1)`). `(alpha+c)•a`'s
pair is `alpha•a`'s pair composed with `c•a`'s pair via Cantor addition —
this file supplies the "composing two valid Mumford pairs gives a valid
Mumford pair" fact that composition step needs, rather than assuming it.

**Caution — this file states the CLASSICAL textbook Cantor composition
formula (Bézout via `IsCoprime`, then the standard `u := u1*u2/d²`,
`v := (...)/d mod u` shape), NOT a formula copied from `00_sample_specs.jl`
directly — that file is not present in this upload, only described
secondhand in `CantorReductionStep.lean`'s docstring ("lines 152-169",
`gcdx`-based). **Diff this against the real Julia source before trusting
it downstream** — if the concrete implementation differs (e.g. in how it
normalizes `d`, or handles the `d² ∣ u1*u2` step), this file's `u`/`v`
formulas need to be re-derived to match, not assumed compatible by
shape-similarity alone. Flagging this explicitly per this project's own
"line-by-line diff against the real target" standing lesson, since a
mechanical port of a formula never seen firsthand is exactly the failure
mode that lesson warns about.

**Simplification taken, stated up front.** The textbook construction
normally also requires showing `d ∣ u1`, `d ∣ u2` and that `u := u1*u2/d²`
is even a polynomial (i.e. `d²` really divides `u1*u2`) — this needs `d`
itself derived from `u1,u2`'s gcd structure, not just an abstract
`IsCoprime`-style witness. Rather than construct `d` from scratch (a
separate, nontrivial polynomial-gcd development not attempted here), this
file takes the EXISTENCE of such a `d` (with `d ∣ u1`, `d ∣ u2`,
`u1 * u2 = d ^ 2 * u`) as a hypothesis (`hd`), and proves the Mumford
identity is preserved GIVEN that `d`/`u` decomposition — i.e. this file
proves the *algebraic content* (Bézout combination preserves `u ∣ v²-f`),
not the *existence* of the gcd decomposition itself. The latter is pure
polynomial-gcd machinery (arguably already implicit in `EuclideanDomain`
instances Mathlib provides for `Polynomial K` over a field `K`) and is
flagged as the next piece needed, not assumed away.

**Not yet checked against the actual Lean toolchain** — same standing
caveat as `CantorReductionStep.lean`: build this before relying on it.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

section CantorCompositionStep

variable {K : Type*} [Field K]

/-- **Cantor composition preserves the Mumford identity, given the gcd
decomposition.**

Setup, matching the classical construction: `u1 ∣ v1²-f`, `u2 ∣ v2²-f`
(both inputs are genuine Mumford pairs). `d` is a common factor of
`u1,u2` with `u1*u2 = d²*u` (`hd` — the gcd/Bézout-normalization step,
taken as hypothesis per the module docstring; not derived here).

**Status: NOT proved — see the module docstring's "What this closes"
section.** Worked the algebra by hand before attempting Lean (per this
project's mindset: attempt first, escalate only once genuinely stuck):
the three-term `hbezout : s1*u1 + s2*u2 + s3*d = 1` as stated is NOT
sufficient on its own. The classical construction's `v` formula only
satisfies `v ≡ v1 (mod u1/d)`, `v ≡ v2 (mod u2/d)` — the compatibility
that makes `v²-f` divisible by the FULL `u = u1*u2/d²` — because `s3`
specifically comes from a SECOND, chained Bézout step solving
`c1*d + c2*(v1+v2) = 1` (not an independent free coefficient satisfying
only the flat 3-term identity above). This is genuine, nontrivial content
connecting `s3` to `v1+v2` that this file's current hypotheses don't
capture; stating it correctly needs either that second Bézout identity
threaded through explicitly, or working directly with an
`EuclideanDomain.gcdA`/`gcdB`-style two-stage construction rather than a
single flat 3-term relation. **Escalated to ChatGPT this pass** rather
than guess a `sorry`-shaped fix or force through an under-hypothesized
statement — see the prompt in this project's chat log for this pass. -/
theorem cantorCompositionStep_preserves_mumford
    {u1 v1 u2 v2 f d u s1 s2 s3 v : Polynomial K}
    (hu1 : u1 ∣ v1 ^ 2 - f)
    (hu2 : u2 ∣ v2 ^ 2 - f)
    (hd1 : d ∣ u1) (hd2 : d ∣ u2)
    (hd : u1 * u2 = d ^ 2 * u)
    (hbezout : s1 * u1 + s2 * u2 + s3 * d = 1)
    (hv : v = s1 * u1 * v2 + s2 * u2 * v1 + s3 * (v1 * v2 + f)) :
    u ∣ v ^ 2 - f := by
  sorry

/-- **Corollary, `u ∣ f - v²` sign convention** (matching
`CantorReductionStep.lean`'s own `_preserves_mumford'` twin, and
`IsMumfordTarget`'s literal shape in `DataDerivationSolve.lean`). -/
theorem cantorCompositionStep_preserves_mumford'
    {u1 v1 u2 v2 f d u s1 s2 s3 v : Polynomial K}
    (hu1 : u1 ∣ f - v1 ^ 2)
    (hu2 : u2 ∣ f - v2 ^ 2)
    (hd1 : d ∣ u1) (hd2 : d ∣ u2)
    (hd : u1 * u2 = d ^ 2 * u)
    (hbezout : s1 * u1 + s2 * u2 + s3 * d = 1)
    (hv : v = s1 * u1 * v2 + s2 * u2 * v1 + s3 * (v1 * v2 + f)) :
    u ∣ f - v ^ 2 := by
  -- Same `⟨witness, by ring⟩` idiom `CantorReductionStep.lean` uses to
  -- flip signs, rather than the unconfirmed `dvd_neg`/`neg_dvd` names.
  have h1 : u1 ∣ v1 ^ 2 - f := by
    obtain ⟨c, hc⟩ := hu1; exact ⟨-c, by rw [show v1 ^ 2 - f = -(f - v1 ^ 2) by ring, hc]; ring⟩
  have h2 : u2 ∣ v2 ^ 2 - f := by
    obtain ⟨c, hc⟩ := hu2; exact ⟨-c, by rw [show v2 ^ 2 - f = -(f - v2 ^ 2) by ring, hc]; ring⟩
  obtain ⟨c, hc⟩ := cantorCompositionStep_preserves_mumford h1 h2 hd1 hd2 hd hbezout hv
  exact ⟨-c, by rw [show f - v ^ 2 = -(v ^ 2 - f) by ring, hc]; ring⟩

end CantorCompositionStep

/-!
## What this closes, and what's still open — honest accounting

**NOT closed by this file.** The main theorem,
`cantorCompositionStep_preserves_mumford`, is stated but its proof is a
`sorry` — the flat 3-term `hbezout` hypothesis this file currently states
is genuinely insufficient (worked by hand, see that theorem's own
docstring): the classical construction's `v` formula is only correct
because its third coefficient `s3` comes from a SECOND, chained Bézout
step (`c1*d + c2*(v1+v2) = 1`), not an independently-free coefficient.
Escalated to ChatGPT this pass for the correct hypothesis shape / two-stage
construction, rather than forcing through a proof against an
under-specified statement or leaving a `sorry` that looks closer to done
than it is.

**Still open regardless of how the escalation resolves** (per
`CantorReductionStep.lean`'s own "still open" list, items 2-3, unchanged
by this pass): the generator's own base-case Mumford identity (a concrete
numerical check, already done outside Lean) and induction over
`cantor_mul`'s double-and-add structure to assemble "composition +
reduction, iterated" into "`alpha•a`'s Mumford pair is valid for every
`alpha`," specialized at `K := K2 p c0 c1 c2 c3 c4`.
-/

end TheDataDerivation
end Genus2Lean
