# `regularSeq_of_peel_chain` assembly — status (compressed, rewritten this pass)

**TL;DR, current as of the very last section below:** 4 live `sorry`s
remain, all in `regularSeq_of_peel_chain_assembly`, stages 4–7
(`Fv0`–`Fv3`). The mathematical content each needs is no longer
missing (`PeelChainNondegenerate.hv0_A`/`hv1_B`/`hv2_A`/`hv3_B`) and
neither is the bridge lemma to extend it to each stage's full goal
(`gapA_disjoint_bridge`, proved, no `sorry`) — what's left is wiring
the two together at each of the 4 call sites, not open mathematics.
See "Update (this pass): the two-sided bridge now EXISTS" near the
end of this file for the concrete remaining steps.

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

## Final wiring status (stale as of this update — see next section)

`regularSeq_of_peel_chain` itself: **done, no `sorry`** (delegates to
`regularSeq_of_peel_chain_assembly`). `regularSeq_of_peel_chain_assembly`:
**4 bare `sorry`s remaining, stages 4–7 (`Fv0`–`Fv3` mod their
respective prefixes)**, blocked on the missing `PeelChainNondegenerate`
fields described above — not blocked on any remaining Lean bookkeeping
uncertainty. Everything else in the 12-stage assembly (stages 0–3, 8–11)
is wired and closed, either unconditionally or via an explicit,
already-declared hypothesis.

## Update (earlier pass): the `PeelChainNondegenerate` fields for stages 4–7 now EXIST, but are not yet wired, and the disjoint-extension route needs a genuinely new lemma

**Superseded by the section below** ("the two-sided bridge now
EXISTS") — the "needs a genuinely new lemma" diagnosis at the end of
this section is no longer accurate; skip ahead if short on time. Kept
here for the accurate parts (the field table, the confirmed
variable-disjointness check) that the later section builds on.

**The missing fields described above are no longer missing.**
`PeelChainNondegenerate` now has `hv0_A`, `hv1_B`, `hv2_A`, `hv3_B`
(added in the session between the previous version of this file and
this one), stated at the minimal SAME-SIDE sub-prefix per stage:

| stage | field | given mod | drop (disjoint) |
|---|---|---|---|
| 4 | `hv0_A` | `[Fu0,Fu2]` | `[Fu1,Fu3]` |
| 5 | `hv1_B` | `[Fu1,Fu3]` | `[Fu0,Fu2]` |
| 6 | `hv2_A` | `[Fu0,Fu2,Fv0]` | `[Fu1,Fu3,Fv1]` |
| 7 | `hv3_B` | `[Fu1,Fu3,Fv1]` | `[Fu0,Fu2,Fv2]` |

**But none of this is wired into `regularSeq_of_peel_chain_assembly`
yet** — its signature still only takes the original ten hypotheses
(`hFu0_reg` through `hCurveB2_reg`), and the caller
`regularSeq_of_peel_chain` never references `hpeel.hv0_A` etc. The 4
`sorry`s are exactly where they were.

**Checked the variable-disjointness claim precisely this pass** (the
in-place comments assert it but don't spell out the `Idx`-level
detail): confirmed correct. `Fu0/Fu2` (roadmap labels; = `u1_num
0/u1_num 1` in `genList` position terms) have vars ⊆
`{wa1,wa2,a1,a2,U0}` / `{wa1,wa2,a1,a2,U1}`. `Fu1/Fu3` (= `u2_num
0/u2_num 1`) have vars ⊆ `{wb1,wb2,b1,b2,U0}` / `{wb1,wb2,b1,b2,U1}`.
`Fv0` has vars ⊆ `{wa1,wa2,a1,a2,V0}`. Despite `Fu0` and `Fu1` BOTH
using the literal variable `U0` (intentional — `U0` is a shared
matching variable, not side-exclusive), `Fv0`'s var set is still
fully disjoint from `Fu1`/`Fu3`'s (`V0 ∉ {U0,U1}`, A-side vars ∉
B-side vars) — so the disjoint-extension claim for stage 4 is
mathematically correct.

**Why `regular_of_disjoint_extension_list` (existing, proved) cannot
be applied directly.** Its hypothesis needs `e` UNCONDITIONALLY
regular in its own home ring `MvPolynomial σ₂ R` — no ambient
quotient. But `hpeel.hv0_A` gives `Fv0` regular only AFTER already
quotienting by `[Fu0,Fu2]` (which lives in the SAME variables as
`Fv0` modulo `V0` vs `U0/U1` — i.e. `Fu0,Fu2,Fv0` all need the
A-side vars `{wa1,wa2,a1,a2}`, so `[Fu0,Fu2]` can't be pushed onto
the disjoint `σ₁` side either — that's exactly Gap A's content, why
`hv0_A` needs to be a hypothesis at all). So closing stage 4 needs a
TWO-SIDED generalization: `e` regular mod its own-side prefix
`gens₂'` survives extending by a disjoint `σ₁` and quotienting by
`gens₁'` there.

## Update (this pass): the two-sided bridge now EXISTS — `gapA_disjoint_bridge`

**The lemma the previous version of this section was drafting a
ChatGPT prompt for has since been written directly, and is proved, no
`sorry`.** `gapA_disjoint_bridge` (`PeelChainAssembly.lean`, ~line
2501, right after `PeelChainNondegenerate`) is an `Idx`/`Rdec
p`-specialized one-sided disjoint-extension bridge:

```
theorem gapA_disjoint_bridge (SA : Finset Idx) (gensA gensB : List (Rdec p))
    {e : Rdec p}
    (hgensA_vars : ∀ g ∈ gensA, (g.vars : Set Idx) ⊆ (↑SA : Set Idx))
    (he_vars : (e.vars : Set Idx) ⊆ (↑SA : Set Idx))
    (hgensB_vars : ∀ g ∈ gensB, ∀ v ∈ g.vars, v ∉ SA)
    (he_reg : IsSMulRegular (Rdec p ⧸ Ideal.ofList gensA)
      (Ideal.Quotient.mk (Ideal.ofList gensA) e)) :
    IsSMulRegular (Rdec p ⧸ Ideal.ofList (gensA ++ gensB))
      (Ideal.Quotient.mk (Ideal.ofList (gensA ++ gensB)) e)
```

i.e. exactly what each of stages 4–7 needs: given `e` regular mod its
own-side prefix `gensA` (`hpeel.hv0_A` etc.), extending by a
variable-disjoint `gensB` (the other side's generators) and
quotienting by both together leaves `e` regular. Built directly at
the `Idx`/`Rdec p` level (via `Equiv.sumCompl`/`Equiv.sumComm` and
`MvPolynomial.sumAlgEquiv`, following the file's own established
`sumAlgEquiv_comp_rename_inl`/`_inr` idiom), rather than through the
general `σ₁ ⊕ σ₂`/two-field abstraction the previous version of this
section proposed — sufficient for this use, simpler to state, and
already done. **The drafted `chatgpt_prompt_two_sided_disjoint_
extension.md` prompt/generic two-field-`R` lemma is accordingly
superseded and does not need to be pursued** unless a future stage
outside this file needs the fully generic version.

**What's still missing is purely wiring, not mathematics.** Checked
this pass: `gapA_disjoint_bridge` has **zero call sites** anywhere in
`PeelChainAssembly.lean`. The remaining steps per stage:

1. Call `gapA_disjoint_bridge` with `SA` := the relevant side's
   `Finset Idx` (e.g. stage 4: `SA = {wa1,wa2,a1,a2,V0,U0,U1}`-ish,
   covering `Fu0,Fu2,Fv0`'s vars), `gensA := [Fu0,Fu2]`, `gensB :=
   [Fu1,Fu3]`, `e := Fv0`, `he_reg := hpeel.hv0_A`. The `hgensA_vars`/
   `he_vars`/`hgensB_vars` side-conditions need the concrete `Idx`
   Finset containment/disjointness facts — already confirmed true by
   hand in the "Checked the variable-disjointness claim precisely
   this pass" note below, just not yet packaged as the `Finset`
   lemmas `gapA_disjoint_bridge`'s hypotheses ask for.
2. The result lands at `Ideal.ofList (gensA ++ gensB)`, i.e.
   `Ideal.ofList [Fu0,Fu2,Fu1,Fu3]` — likely needs a `List.Perm`/
   `Ideal.ofList`-reordering step (`Ideal.span`-of-a-list is
   order-independent, but the raw `List` argument to `Ideal.ofList`
   is not automatically recognized as equal to the `[Fu0,Fu1,Fu2,Fu3]`
   order `regularSeq_of_peel_chain_assembly`'s stage-4 goal is
   literally stated against) before it type-checks against the goal
   `apply hquotient_mk_regular` already sets up at each `sorry` site.
3. Repeat for stages 5–7 with `hpeel.hv1_B`/`hv2_A`/`hv3_B` and the
   matching `gensA`/`gensB` splits (see the per-field docstrings on
   `PeelChainNondegenerate` for the exact split each stage needs —
   already spelled out there).
4. No changes needed to `regularSeq_of_peel_chain_assembly`'s
   signature or to `regularSeq_of_peel_chain`'s call site — `hpeel :
   PeelChainNondegenerate ...` is already threaded through both (its
   `hv0_A`–`hv3_B` fields are simply unused past their own
   definition right now); closing the 4 sorries only touches the
   4 case-split branches themselves.

Rough estimate unchanged from the previous version of this section:
each of the 4 call sites is non-trivial glue (`Finset` containment
arguments plus a possible `Ideal.ofList` reordering), but the
load-bearing mathematical lemma is done — this is now genuinely
mechanical wiring, not open math.

## Update (this pass): the above is WRONG — `gapA_disjoint_bridge` cannot
## close any of stages 4–7 with the `[Fu0,Fu2]`/`[Fu1,Fu3]`-style split

**Re-derived the variable-disjointness claim precisely (the "confirmed
correct" note above only checked `Fv0` vs `Fu1`/`Fu3` pairwise — it
did NOT check `gensA` vs `gensB` as whole lists, which is what
`gapA_disjoint_bridge`'s `hgensB_vars` hypothesis actually demands).**
The real picture, straight from `u1_indep`/`u2_indep`/`v1_indep` (§
`DecoupledSystemRegular.lean` line ~293) and `U0' = X U0` etc.:

- `Fu0 = u1_num0 - U0'*u1_den0` has vars ⊆ `{wa1,wa2,a1,a2,U0}`
- `Fu2 = u1_num1 - U1'*u1_den1` has vars ⊆ `{wa1,wa2,a1,a2,U1}`
- `Fu1 = u2_num0 - U0'*u2_den0` has vars ⊆ `{wb1,wb2,b1,b2,U0}`
- `Fu3 = u2_num1 - U1'*u2_den1` has vars ⊆ `{wb1,wb2,b1,b2,U1}`
- `Fv0 = v1_num0 - V0'*v1_den0` has vars ⊆ `{wa1,wa2,a1,a2,V0}`

`gapA_disjoint_bridge`'s `hgensA_vars`/`he_vars` force `SA ⊇
{wa1,wa2,a1,a2,U0,U1,V0}` (since `Fu0,Fu2,Fv0 ∈ gensA ∪ {e}`, and
`Fu0` alone forces `U0 ∈ SA`, `Fu2` alone forces `U1 ∈ SA`). But then
`hgensB_vars` requires EVERY var of `Fu1` and `Fu3` to avoid `SA` —
and `Fu1` contains `U0`, `Fu3` contains `U1`, both now forced into
`SA`. **Contradiction — `SA` cannot exist.** This isn't a proof
difficulty, it's `gapA_disjoint_bridge` being the wrong lemma for
this call, full stop: `U0`/`U1` are intentionally shared "matching"
variables between the A-side and B-side generators (see
`DecoupledGenerators`'s docstring — "decoupled" means `u1_num`/
`u1_den` alone never touch `U0`/`U1`, but the combination `u1_num -
U0'*u1_den` obviously does), so no partition of `Idx` makes `gensA`
and `gensB` simultaneously factor through disjoint variable subsets.
Same obstruction hits stages 5, 6, 7 (all mirror the same `U0`/`U1`-
or `V0`/`V1`-sharing pattern across the two accumulated sides).

**This is a genuine open mathematical gap, not wiring.** Closing it
needs either (a) a generalization of `gapA_disjoint_bridge` that
tolerates a shared "matching variable" subset between `gensA` and
`gensB` (rather than demanding full disjointness), likely requiring
an extra regularity/coprimality hypothesis on the matching-variable
elimination (e.g. `u1_den0*u2_num0 - u2_den0*u1_num0` being a
nonzerodivisor — a resultant-type condition, since `Fu0=0` and
`Fu1=0` both pin down `U0` and consistency of those two pinned
values is what such a condition would certify), or (b) a different
proof strategy for stages 4–7 entirely. **Sent to ChatGPT this pass**
— prompt at `chatgpt_prompt_gapA_shared_matching_var.md` (same
directory). Do not attempt to force the 4 `sorry`s at stages 4–7 via
`gapA_disjoint_bridge` until this comes back; the lemma's hypotheses
are provably unsatisfiable for these call sites as currently split.

**Nothing in `PeelChainAssembly.lean` was edited this pass beyond
comments** — the 4 `sorry`s themselves are untouched (still exactly
4, same stages); only the stale in-place comments at each `sorry`
site and the file's top-of-file status docstring were corrected to
stop describing `gapA_disjoint_bridge` as not-yet-built.

## Update (later pass): ChatGPT answered — false in general, fixed via new hypotheses, build now GREEN

**ChatGPT confirmed the claim really is false**, not just hard to
derive: it gave a concrete counterexample (`R =
K[x,z,y,U0,U1,V0,V1]`, `Fu0=x-U0`, `Fu2=z-U1`, `Fu1=-U0*y`,
`Fu3=-U1*y`, `Fv0=x-V0*z`) where `Fv0` is regular mod `(Fu0,Fu2)` but
`y*(x-V0*z) = 0` in `R/(Fu0,Fu2,Fu1,Fu3)` with `y ≠ 0` — i.e. a
genuinely new zerodivisor gets created by adjoining the shared-
variable relations, not something any disjoint-extension-style lemma
could ever paper over. The failure mechanism: eliminating the shared
`U0`/`U1` cross-multiplies the two sides' num/den pairs together
(`C0 = d10*n20 - d20*n10` etc.), and *those* cross terms are what can
introduce new torsion — a resultant-type condition, not a variable-
disjointness one.

**Fix applied:** rather than chase a generalized bridge lemma,
`PeelChainNondegenerate` gained four new fields — `hv0_ext`,
`hv1_ext`, `hv2_ext`, `hv3_ext` — stating each stage's literal
full-prefix regularity fact directly as supplied data (same status as
`hu01`/`hv0_A`/etc., genuine hypotheses not derived facts). Wired
straight into `regularSeq_of_peel_chain_assembly`'s signature and the
four `sorry` sites (`exact hvN_ext_reg` where the goal was already
reduced by a preceding `apply hquotient_mk_regular`, stages 4/5; the
fuller `exact hquotient_mk_regular ... hvN_ext_reg` form where it
wasn't, stages 6/7 — got the wrapping wrong on the first pass at
stages 4/5, REPL caught it as a type mismatch, fixed). **Build is now
green — file is `sorry`-free.** `gapA_disjoint_bridge` remains in the
file, proved, but unused (confirmed the wrong tool for this project's
actual variable-sharing pattern).

**What `hv0_ext`–`hv3_ext` still owe us:** they're new *hypotheses*,
not proofs — the underlying math (Tor-independence / the resultant-
type nonzerodivisor condition ChatGPT identified) hasn't actually
been established for this project's real `theData`, just assumed.

**Claire's nondegeneracy note (this pass, ties directly into the
above):** we can safely assume `α ≠ P1+P2` — i.e. `U`/`V` never hit
the zero divisor and never land on a `y=0` point. Any such collision
is a trivial/Weierstrass-point-type solution and would be filtered
out of the search anyway (see `ROADMAP-alpha-locus.md` for how `U,V`
tie back to actual curve points `P1..P4`). This is exactly the kind
of nondegeneracy that would let `hv0_ext`–`hv3_ext` actually be
*proved* rather than assumed: ChatGPT's counterexample's failure mode
was precisely a denominator (`y`) becoming a zerodivisor after
quotienting — a `y=0`/Weierstrass-type degeneracy. Once `hv0_ext` etc.
are re-parametrized in terms of `alpha`/`P1..P4` (the eventual target
noted at the top of `PeelChainAssembly.lean`), this should be the
natural hypothesis to invoke to actually close them. Not attempted
yet — flagged here so it isn't lost.
