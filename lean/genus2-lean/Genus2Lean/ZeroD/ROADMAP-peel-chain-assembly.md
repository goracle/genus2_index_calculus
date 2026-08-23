# `regularSeq_of_peel_chain` assembly — status (compressed, rewritten this pass)

**This replaces the previous version**, which predated the
`PeelChainNondegenerate`-hypothesis weakening described below and so
described 4 open proof obligations that, since then, have been *partly*
discharged via that new hypothesis and partly are still bare `sorry`s in
a different, more precise place than before. The old version's "Gap A"/
"Gap B"/"Gap C" diagnosis was correct and is preserved below, but the
wiring has moved. See git history if the pre-weakening reasoning is ever
needed.

## The mechanism in use (unchanged)

`RingTheory.Sequence.IsRegular (Rdec p) genList` unfolds
(`isWeaklyRegular_iff_Fin`) to a flat per-index statement: for each of the
12 indices `i`, `IsSMulRegular (Rdec p ⧸ Ideal.ofList (rs.take i) • ⊤)
rs[i]`, plus one extra `top_ne_smul` field. `genList = [Fu0,Fu1,Fu2,Fu3,
Fv0,Fv1,Fv2,Fv3, curveA1,curveA2,curveB1,curveB2]` (`hgenList`, proved).

## What changed since the last version of this file: Gaps A/B/C weakened to hypotheses

Per this project's stated practice ("we do not use hypotheses to get out
of proving something — we try to prove it first! ... if we find a false
theorem, we weaken it first"), Gap A, Gap B, and Gap C have each been
turned into an explicit hypothesis rather than left as a bare `sorry` on
the main theorem:

- **`PeelChainNondegenerate`** (structure, §3, ~line 1931): bundles Gap A
  and Gap B content as 8 named fields — `hu01`, `hv01` (Gap A, stage 2/6:
  `Fu2`/`Fv2` regular mod the 2-element prefix `[Fu0,Fu1]`/`[Fv0,Fv1]`),
  `hu1_full`, `hv1_full` (Gap A, stage 3/7: `Fu3`/`Fv3` regular mod the
  3-element prefix), and `hcurveA1`/`hcurveA2`/`hcurveB1`/`hcurveB2`
  (Gap B, stages 8–11: the four curve relations regular mod the
  accumulated 8-element `Fu++Fv` prefix).
- **`top_ne_smul` (Gap C)**: weakened directly to a hypothesis
  `htop_ne_smul` on `regularSeq_of_peel_chain`'s own signature, rather
  than bundled into `PeelChainNondegenerate`.

`regularSeq_of_peel_chain` (the public-facing theorem, ~line 2742) is
now **fully proved, no `sorry`**, taking `hpeel : PeelChainNondegenerate
...` and `htop_ne_smul` as hypotheses and delegating to
`regularSeq_of_peel_chain_assembly` (private, ~line 2402) for the actual
12-way case split. `decoupledSystem_isRegularSequence`
(`AlphaLocusDegreeUniform.lean`) is in turn just
`:= regularSeq_of_peel_chain ...` applied — also `sorry`-free, modulo
whatever hypotheses its own callers must eventually discharge.

## The actual remaining gap: `PeelChainNondegenerate` doesn't cover two of the twelve stages

**This is the one concrete, load-bearing finding of this pass.**
Checking `regularSeq_of_peel_chain_assembly`'s 12-way `fin_cases i` body
stage-by-stage against `PeelChainNondegenerate`'s 8 fields:

| stage | generator | mod prefix | discharged by | status |
|---|---|---|---|---|
| 0 | `Fu0` | `[]` | `hFu0_reg` (param, unconditional) | proved |
| 1 | `Fu1` | `[Fu0]` | `hFu1_reg` (param) | proved |
| 2 | `Fu2` | `[Fu0,Fu1]` | `hpeel.hu01` | proved (via hyp) |
| 3 | `Fu3` | `[Fu0,Fu1,Fu2]` | `hpeel.hu1_full` | proved (via hyp) |
| **4** | **`Fv0`** | **`[Fu0,Fu1,Fu2,Fu3]`** | **nothing — no matching field in `PeelChainNondegenerate`** | **bare `sorry`, line ~2596** |
| **5** | **`Fv1`** | **`[Fu0..Fu3,Fv0]`** | **nothing** | **bare `sorry`, line ~2619** |
| **6** | **`Fv2`** | **`[Fu0..Fu3,Fv0,Fv1]`** | **nothing** | **bare `sorry`, line ~2631** |
| **7** | **`Fv3`** | **`[Fu0..Fu3,Fv0..Fv2]`** | **nothing** | **bare `sorry`, line ~2644** |
| 8 | `curveA1` | 8-elt `Fu++Fv` | `hpeel.hcurveA1` | proved (via hyp) |
| 9 | `curveA2` | 9-elt prefix | `hpeel.hcurveA2` | proved (via hyp) |
| 10 | `curveB1` | 10-elt prefix | `hpeel.hcurveB1` | proved (via hyp) |
| 11 | `curveB2` | 11-elt prefix | `hpeel.hcurveB2` | proved (via hyp) |

So the structure that was supposed to bundle "everything Gap A/B needs"
only actually covers the **A-side accounting a second time** (`hu01`/
`hv01`/`hu1_full`/`hv1_full` are all named as if generic, but every one
of their statements, on inspection, happens to be about `Fu2`/`Fu3`'s
regularity mod an all-`Fu` prefix — i.e. only stages 2/3 are covered, not
6/7 as the naming suggested) plus Gap B in full. **Stages 4–7 — `Fv0`
through `Fv3`, each mod a prefix that includes the full 4-element `Fu`
block — have no covering hypothesis at all**, and are still bare
`sorry`s with stale in-place comments diagnosing them as "Gap A, needs a
new hypothesis" (correct diagnosis, just not yet acted on for these four
specifically).

**Why this is real content, not bookkeeping**: `Fv0` unconditionally
regular (`hFv0_reg`, proved, unconditional statement) is a strictly
weaker fact than `Fv0` regular *mod the accumulated `Fu`-prefix* — the
latter is exactly the cross-index coprimality-type content the old
roadmap's Gap A section described (`towerToRdec`-style
denominator-clearing can introduce common factors between `Fv0` and the
A-side generators `Fu0`/`Fu2` that aren't forced by the original
rational function's own coprimality). Stages 5–7 are the same fact one
step further down the same prefix chain.

**Next step**: extend `PeelChainNondegenerate` with 4 more fields
(`hv0_full`-style, covering stages 4–7 the same way `hu01`/`hu1_full`
cover 2–3) using the same "one structural hypothesis per stage,
Gap-A-shaped" pattern already established for the existing 8 fields —
then wire `regularSeq_of_peel_chain_assembly`'s 4 remaining `sorry`s to
the new fields exactly as `hpeel.hu01` etc. already wire stages 2/3.
This is mechanical once the fields exist; no new Lean infrastructure is
needed, matching the pattern already used for every other stage in this
theorem.

## Whether `PeelChainNondegenerate`'s existing 8 fields are themselves provable, or need to stay hypotheses

Not attempted in this project yet, and per the original Gap A/B
diagnosis (below), likely **not** derivable from `Nondegenerate`/
`CrossNondegenerate`/`hgcdA`/`hgcdB` alone — these are genuinely new
nondegeneracy content about the specific `(c0,...,c4,sa,sb)` instance,
expected to hold "for enough" choices but not a formal consequence of
what's already assumed. The same is expected to apply to the 4 new
fields proposed above.

## Original Gap A / Gap B diagnosis (preserved, still the reason `PeelChainNondegenerate`'s fields can't be proved outright)

**Gap A** (repeated-target-variable stages, mod their fuller prefix):
genuinely needs `IsCoprime`-style cross-index coprimality, not derivable
from `hgcdA : IsCoprime (Ypoly ...) (uRS ...)` alone — a
denominator-clearing recursion (`towerToRdec`) can introduce common
factors between coefficients at different indices that aren't forced by
the original rational function's own coprimality. Confirmed via ChatGPT
consultation in an earlier pass. **Caveat, still unverified**: double
check the claimed equivalence "regular mod `⟨Fu0⟩` ⟺ `IsCoprime (u1_num
0) (u1_den 1)`" before leaning on it for the new stage-4–7 fields — it is
NOT true for an arbitrary linear relation `n - U*d` without extra
conditions on `d` (counterexample: `x` is regular mod `(x-2U)` in
`k[x,U]` despite `gcd(x,x) ≠ 1`).

**Gap B** (curve-relation stages, mod the full 8-element `Fu++Fv`
prefix): `Fu0,Fu2,Fv0,Fv2` (A-side generators) can depend on `wa1`
through their numerators (linear, `wa1`-degree ≤ 1 — proved,
`towerToRdec`'s numerator formula is manifestly linear), while denominators
are honestly `wa1`-free (`towerToRdec_den_vars_subset`, proved,
`DataDerivationMumford.lean`). `curveA1 = wa1^2 - quintic(a1)` is monic
of `wa1`-degree exactly 2. Whether "monic quadratic mod an ideal
generated by degree-≤1-in-the-same-variable elements" is provable
outright from the bidegree bound alone, or needs its own resultant-type
hypothesis, was sent to ChatGPT in an earlier pass; **the answer was
never confirmed as received or acted on** — this project's practice is
to weaken to a hypothesis when a fact is genuinely open, which is what
`hcurveA1`–`hcurveB2` do now, so this is moot unless someone wants to
try proving those 4 fields outright later.

## Gap C — `top_ne_smul`

Weakened to `htop_ne_smul`, a hypothesis on `regularSeq_of_peel_chain`
directly (see above) — this project's "weaken first" practice applied.
**Not proved outright anywhere.** Proving it honestly would need
exhibiting an actual `F p`-point solving all 12 defining equations
(giving a surjection `Rdec p ↠ F p` killing the ideal) — real
existence-of-a-point mathematics (does the genus-2 construction have any
valid sample point at all for generic `(c0..c4,sa,sb)`?), not
bookkeeping. Whether this is already implied by
`Nondegenerate`/`CrossNondegenerate`'s existence (if those structures are
only ever instantiated at points where a solution demonstrably exists)
is still an open question worth asking Claire directly rather than
guessing, same as before.

## Final wiring status

`regularSeq_of_peel_chain` itself: **done, no `sorry`** (delegates to
`regularSeq_of_peel_chain_assembly`). `regularSeq_of_peel_chain_assembly`:
**4 bare `sorry`s remaining, stages 4–7 (`Fv0`–`Fv3` mod their
respective prefixes)**, blocked on the missing `PeelChainNondegenerate`
fields described above — not blocked on any remaining Lean bookkeeping
uncertainty. Everything else in the 12-stage assembly (stages 0–3, 8–11)
is wired and closed, either unconditionally or via an explicit,
already-declared hypothesis.
