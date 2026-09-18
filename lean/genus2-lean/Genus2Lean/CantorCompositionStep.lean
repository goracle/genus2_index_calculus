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

**UPDATE — formula now extracted from the actual source** (`elim2.zip`'s
`00_sample_specs.jl`, `cantor_add`/`p_gcdx`, lines 125-190), replacing an
earlier draft's guessed textbook shape which was WRONG on two counts
(flagged and caught before being trusted, per this project's "diff against
the real target" standing lesson — good thing it wasn't skipped). The real
algorithm, transcribed exactly:

```
g1, e1, e2 = p_gcdx(u1, u2)        -- g1 = e1*u1 + e2*u2
g,  c1, c2 = p_gcdx(g1, v1+v2)     -- g  = c1*g1 + c2*(v1+v2)
s1 := c1*e1,  s2 := c1*e2,  s3 := c2
                                    -- ⟹ s1*u1 + s2*u2 + s3*(v1+v2) = g
u := (u1*u2) / g^2                 -- exact (p_divrem, remainder discarded)
num := s1*u1*v2 + s2*u2*v1 + s3*(v1*v2+f)
v_tmp := num / g                   -- exact (p_divrem, remainder discarded)
v := v_tmp mod u
```

**The earlier draft's two errors, now corrected**: (1) the Bézout identity
is `s1*u1 + s2*u2 + s3*(v1+v2) = g` — the third term multiplies `(v1+v2)`,
NOT `d`/`g` as the earlier draft had it; (2) the right-hand side is `g`
(the gcd), NOT `1` — `p_gcdx` returns an actual gcd (monic-normalized),
not a unit, so there is no reason to expect `=1` in general. Both errors
independently confirmed by direct inspection of `p_gcdx`'s contract
(extended-Euclidean, returns `(g,s,t)` with `g = s*a+t*b`) and
`cantor_add`'s literal assignment lines — not re-guessed.

**Genuinely deep, not just unattempted — worked by hand before writing
any Lean.** Tried to derive `u ∣ v²-f` directly from the corrected
relations above via elementary polynomial congruence manipulation (the
same style that closed `CantorReductionStep.lean`'s reduction step, a
straightforward difference-of-squares argument). It does not reduce to
anything that short: tracking `v_tmp ≡ v (mod u)` against `num = g*v_tmp`
only pins `num` modulo `g*u`, not modulo the needed `g²*u = u1*u2`, and
closing that gap needs a further fact (typically supplied by the
ideal/divisor-theoretic reading of Cantor's algorithm — `u` is literally
the ideal `⟨u1,v1-?⟩ + ⟨u2,v2-?⟩`'s own generator via the Chinese-Remainder
structure of the two input ideals — not a fact visible from the bare
polynomial identities alone). This is the actual mathematical content of
Cantor composition's correctness proof (as found in the standard
hyperelliptic-cryptography references), not a shape this file's author
failed to spot. **Escalated to ChatGPT this pass**, now armed with the
verified-correct formula above (a strictly better starting point than the
earlier draft's wrong guess would have given it).

**Not yet checked against the actual Lean toolchain** — same standing
caveat as `CantorReductionStep.lean`: build this before relying on it.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

section CantorCompositionStep

variable {K : Type*} [Field K]

/-- **Cantor composition preserves the Mumford identity, given the gcd
decomposition — hypotheses now matching the REAL `cantor_add` source
exactly** (`00_sample_specs.jl`, transcribed in the module docstring).

`hbezout` is the corrected two-stage Bézout identity
`s1*u1 + s2*u2 + s3*(v1+v2) = g` (the earlier draft's `= 1` /
`s3*d`-instead-of-`s3*(v1+v2)` version was wrong — see module docstring).
`hnum` records that `num/g` is exact (`p_divrem`'s remainder is silently
discarded in the source, exactly as `CantorReductionStep.lean`'s
`u_next`-exactness hypothesis `hexact` already does for the reduction
loop — same convention, not a new one), since `v_tmp` is only genuinely
`num/g` when that division has zero remainder.

**Status: NOT proved.** See module docstring: this is the actual
correctness content of Cantor composition, normally established via the
ideal/divisor-theoretic structure of the construction (not bare
polynomial-ring identities), and resisted a direct hand-derivation
attempt. Escalated to ChatGPT this pass with the now-verified-correct
formula. -/
theorem cantorCompositionStep_preserves_mumford
    {u1 v1 u2 v2 f g u s1 s2 s3 num v_tmp v : Polynomial K}
    (hu1 : u1 ∣ v1 ^ 2 - f)
    (hu2 : u2 ∣ v2 ^ 2 - f)
    (hg1 : g ∣ u1) (hg2 : g ∣ u2)
    (hu : u1 * u2 = g ^ 2 * u)
    (hbezout : s1 * u1 + s2 * u2 + s3 * (v1 + v2) = g)
    (hnumdef : num = s1 * u1 * v2 + s2 * u2 * v1 + s3 * (v1 * v2 + f))
    (hnum : num = g * v_tmp)
    (hv : v = v_tmp %ₘ u) :
    u ∣ v ^ 2 - f := by
  sorry

/-- **Corollary, `u ∣ f - v²` sign convention** (matching
`CantorReductionStep.lean`'s own `_preserves_mumford'` twin, and
`IsMumfordTarget`'s literal shape in `DataDerivationSolve.lean`). -/
theorem cantorCompositionStep_preserves_mumford'
    {u1 v1 u2 v2 f g u s1 s2 s3 num v_tmp v : Polynomial K}
    (hu1 : u1 ∣ f - v1 ^ 2)
    (hu2 : u2 ∣ f - v2 ^ 2)
    (hg1 : g ∣ u1) (hg2 : g ∣ u2)
    (hu : u1 * u2 = g ^ 2 * u)
    (hbezout : s1 * u1 + s2 * u2 + s3 * (v1 + v2) = g)
    (hnumdef : num = s1 * u1 * v2 + s2 * u2 * v1 + s3 * (v1 * v2 + f))
    (hnum : num = g * v_tmp)
    (hv : v = v_tmp %ₘ u) :
    u ∣ f - v ^ 2 := by
  -- Same `⟨witness, by ring⟩` idiom `CantorReductionStep.lean` uses to
  -- flip signs, rather than the unconfirmed `dvd_neg`/`neg_dvd` names.
  have h1 : u1 ∣ v1 ^ 2 - f := by
    obtain ⟨c, hc⟩ := hu1; exact ⟨-c, by rw [show v1 ^ 2 - f = -(f - v1 ^ 2) by ring, hc]; ring⟩
  have h2 : u2 ∣ v2 ^ 2 - f := by
    obtain ⟨c, hc⟩ := hu2; exact ⟨-c, by rw [show v2 ^ 2 - f = -(f - v2 ^ 2) by ring, hc]; ring⟩
  obtain ⟨c, hc⟩ := cantorCompositionStep_preserves_mumford h1 h2 hg1 hg2 hu hbezout
    hnumdef hnum hv
  exact ⟨-c, by rw [show f - v ^ 2 = -(v ^ 2 - f) by ring, hc]; ring⟩

end CantorCompositionStep

/-!
## What this closes, and what's still open — honest accounting

**NOT closed by this file.** `cantorCompositionStep_preserves_mumford` is
stated (now against the VERIFIED-CORRECT formula extracted directly from
`00_sample_specs.jl`, replacing an earlier draft with two real errors —
see module docstring) but its proof is a `sorry`. Worked the algebra by
hand first, per this project's mindset (attempt before escalating): the
gap does not close with elementary polynomial-congruence manipulation the
way `CantorReductionStep.lean`'s reduction-step lemma did — tracking
`v_tmp ≡ v (mod u)` against `num = g·v_tmp` only pins `num` modulo `g·u`,
not the needed `g²·u = u1·u2`. This is the genuine correctness content of
Cantor composition (normally proved via the ideal/divisor-theoretic
structure of the construction, in standard hyperelliptic-curve-crypto
references), not a shape missed for lack of trying. **Escalated to
ChatGPT this pass**, now with the correct formula in hand (a real
improvement over escalating against the earlier wrong draft, which would
have wasted the round).

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
