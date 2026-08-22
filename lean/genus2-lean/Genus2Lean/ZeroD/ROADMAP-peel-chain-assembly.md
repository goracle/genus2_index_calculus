# `regularSeq_of_peel_chain` assembly — status (compressed)

**This replaces the previous 520-line version**, which documented several
false starts (the `isRegular_cons_iff'`-unrolling route, various
`regular_of_disjoint_extension` misapplications) before landing on the
mechanism actually used in `PeelChainAssembly.lean` §3. Those false
starts are resolved and not reproduced here — see git history / the
prior version of this file if the historical reasoning is ever needed.
This version states only: (1) the mechanism actually in use, (2) exactly
what's proved vs. open right now, (3) what's blocking each open piece.

## The mechanism in use

`RingTheory.Sequence.IsRegular M rs` unfolds (`isWeaklyRegular_iff_Fin`)
to a FLAT per-index statement: `∀ i, IsSMulRegular (M ⧸ Ideal.ofList
(rs.take i) • ⊤) rs[i]`, plus one extra `top_ne_smul` field. No
`QuotSMulTop`/`DoubleQuot` nesting is needed — each of the 12 indices is
checked against a single flat quotient by the literal prefix
`Ideal.ofList (rs.take i)`. `genList = [Fu0,Fu1,Fu2,Fu3,Fv0,Fv1,Fv2,Fv3,
curveA1,curveA2,curveB1,curveB2]` (`hgenList`, proved). §3.0's
`quotSMulTop_equiv_span`/`isSMulRegular_quotSMulTop_of_span` bridge
lemmas (proved) are HARMLESS LEFTOVERS from an earlier, superseded
route — not used by the current flat-index assembly, kept only in case
they're useful later.

## What's proved (no `sorry`), in `regularSeq_of_peel_chain`

- `hFu0_reg`, `hFv0_reg` — plain `IsSMulRegular (Rdec p) Fu0`/`Fv0`
  (first-generator-for-a-fresh-variable shape, via `isSMulRegular_first_gen`,
  itself proved via `regular_of_linear_elim` at empty prefix).
- `hFu1_reg`, `hFu3_reg`, `hFv1_reg`, `hFv3_reg` — regular mod the
  single immediately-preceding same-target generator (`Ideal.span
  {Fu0}` etc.), via the ring identity `d1*Fu1 = resultant + d2*Fu0`
  collapsing mod `⟨Fu0⟩`, closed by `isSMulRegular_of_mul_eq_of_isSMulRegular`
  fed by `hcross.hu0`/`hcross.hu1`/`hcross.hv0`/`hcross.hv1`.
- All of §0–§2's infrastructure (`isSMulRegular_bridge_prefix_gen`,
  `isSMulRegular_C_const_of_isSMulRegular`, `regular_of_second_linear_elim`,
  `isSMulRegular_first_gen`, the `quotSMulTop`/span bridge) — fully proved.
- **New this pass**, in `DataDerivationMumford.lean`:
  `towerToRdec_den_vars_subset` — proves the DENOMINATOR half of
  `towerToRdec`'s output (hence `u1_den i`/`u2_den i`/`v1_den i`/`v2_den i`
  for every `i`) is `⊆ {tGen 0, tGen 1}` only, i.e. **never involves
  either `w`-variable of its own side** (`u1_den`/`v1_den` never involve
  `wa1` OR `wa2`; `u2_den`/`v2_den` never involve `wb1` OR `wb2`) — a
  strictly tighter bound than the existing `towerToRdec_vars_subset`
  (which bounds numerator and denominator together at
  `{tGen0,tGen1,wGen0,wGen1}`). Found while investigating the curve-stage
  gap below; not yet consumed by anything (see "still open" below).

## Still open: two independent gaps, both now diagnosed precisely

### Gap A — `hFu2_reg`, `hFv2_reg`, `hFu3_full_reg`, `hFv3_full_reg`
### (repeated-target-variable stages 2/3/6/7 mod their full prefix)

**Diagnosis (confirmed correct by ChatGPT consultation this pass, see
`chatgpt_prompt_curve_stages_and_coprimality.md`'s Problem 2 answer):**
genuinely needs `IsCoprime (u1_num 0) (u1_den 1)`-style cross-index
coprimality, NOT derivable from `hgcdA : IsCoprime (Ypoly ...) (uRS ...)`
alone — a denominator-clearing recursion (`towerToRdec`) can introduce
common factors between coefficients at different indices that aren't
forced by the original rational function's own coprimality. This is
genuinely new nondegeneracy content, not a Lean gap.

**Recommended packaging (per ChatGPT, not yet acted on):** don't add
four separate ad hoc fields (`coprime_u1_01`, `coprime_u2_01`, etc.) tied
to the specific `Fu2`/`Fu3`/`Fv2`/`Fv3` Lean stages. Instead formulate
ONE structural hypothesis at the coefficient-family level, e.g. `∀ r ∈
{u1,u2,v1,v2}, i < j → IsCoprime (r.num i) (r.den j)` (or whatever
orientation the elimination proof actually consumes — check which
direction/indices are actually needed before finalizing the statement).
**Caveat also flagged by ChatGPT**: double check the claimed equivalence
"regular mod `⟨Fu0⟩` ⟺ `IsCoprime (u1_num 0) (u1_den 1)`" before baking
it into the hypothesis's statement — it is NOT true for an arbitrary
linear relation `n - U*d` without extra conditions on `d` (counterexample:
`x` is regular mod `(x - 2U)` in `k[x,U]` despite `gcd(x,x) ≠ 1`). Verify
this equivalence actually holds in our specific setup (it was derived
via `isSMulRegular_quotient_span_singleton_of_isCoprime`, PeelChainAssembly.lean
§0 — re-check that lemma's hypotheses match what's available here) before
relying on it.

**Next step:** decide the exact new hypothesis's statement (need Claire's
input on whether it's plausible for the real construction), add it
parallel to `Nondegenerate`/`CrossNondegenerate`, then close these 4
stages using the existing `isSMulRegular_den_of_second_peel` machinery
(§1), which is already written to consume exactly this shape of input
(its own `hcross01` parameter) — no new Lean infrastructure needed once
the hypothesis exists, just wiring.

### Gap B — `hCurveA1_reg`, `hCurveA2_reg`, `hCurveB1_reg`, `hCurveB2_reg`
### (curve-relation stages 8-11 mod the full 8-element `Fu++Fv` prefix)

**Original plan was WRONG** (found and corrected this pass): the
in-file docstrings assumed the 8-element prefix, after peeling the
matching `w`-variable (e.g. `wa1` for `curveA1`), collapses to an ideal
"extended from the coefficient ring" (i.e. every prefix generator has
literal `wa1`-degree 0) — false. `Fu0,Fu2,Fv0,Fv2` (the A-side
generators) all genuinely can depend on `wa1` through their NUMERATORS
(`u1_num`/`v1_num`).

**Refined diagnosis this pass** (via `towerToRdec_den_vars_subset`
above, confirmed by direct inspection of `towerToRdecK1`/`towerToRdec`'s
defining formulas): the DENOMINATORS (`u1_den`/`v1_den`) are honestly
`wa1`-free (proved), but the NUMERATORS are `wa1`-degree exactly ≤ 1
(linear, never quadratic) — `towerToRdecK1`'s numerator formula
`n0*den1 + n1*den0*X(wGen 0)` is manifestly linear in `X(wGen 0)` with
`wGen`-free coefficients, and this property is preserved (separately,
for `wa1` and `wa2` independently) one level up in `towerToRdec`. So
each of `Fu0,Fu2,Fv0,Fv2` is `wa1`-degree ≤ 1 (not 0), while `curveA1 =
wa1^2 - quintic(a1)` is monic of `wa1`-degree exactly 2. B-side
generators (`Fu1,Fu3,Fv1,Fv3`) remain honestly variable-disjoint from
`{wa1,wa2,a1,a2}` entirely (unaffected by this).

**Sent back to ChatGPT this pass** (`chatgpt_prompt_followup_wgen_degree.md`,
not yet answered as of this writing): whether "monic quadratic mod an
ideal generated by degree-≤1-in-the-same-variable elements" is provable
outright from the bidegree bound alone, or whether (like Gap A) it
needs its own new resultant/nondegeneracy-type hypothesis. Likely
outcome, per the shape of Gap A's answer: probably needs a new
hypothesis (a resultant of `curveA1` against the up-to-4
degree-≤1-in-`wa1` prefix generators being nonzero/regular) — but not
confirmed yet, don't assume until ChatGPT's answer comes back.

**Next step:** read ChatGPT's answer to `chatgpt_prompt_followup_wgen_degree.md`,
then either (a) write the outright proof if one exists, using
`towerToRdec_den_vars_subset` plus the linear-numerator fact
(not yet stated as its own Lean lemma — would need a
`towerToRdec_num_degree_le_one`-style companion to
`towerToRdec_den_vars_subset`, analogous construction, not yet written),
or (b) add whatever new hypothesis is recommended, packaged uniformly
across all 4 curve stages the same way Gap A's fix should be.

## Gap C — `top_ne_smul`

`IsRegular`'s second field, `⊤ ≠ Ideal.ofList genList • ⊤`. Not
attempted at all yet. Proving it honestly likely needs exhibiting an
actual `F p`-point solving all 12 defining equations (giving a
surjection `Rdec p ↠ F p` killing the ideal, hence properness) — this is
real existence-of-a-point mathematics (does the genus-2 construction
have any valid sample point at all for generic `(c0..c4, sa, sb)`?), not
bookkeeping. Not scoped further this pass; flag to Claire before
attempting, since it may need its own hypothesis or may already be
implied by `Nondegenerate`/`CrossNondegenerate`'s existence in the first
place (if those structures are only ever instantiated at points where a
solution demonstrably exists) — worth asking Claire directly rather than
guessing.

## Final wiring (`sorry` at the very end of `regularSeq_of_peel_chain`)

Purely mechanical once Gaps A/B/C close: 12-way `Fin.cases` (or
equivalent) matching each `regular_mod_prev i` obligation, after
`List.take`/`List.get` unfolding on the literal 12-element list, against
the corresponding `h*_reg` fact above (rewriting `Ideal.ofList (rs.take
i)` to match each fact's stated ideal via `Ideal.ofList_nil`/
`Ideal.ofList_singleton`/`rfl` as needed) — plus `top_ne_smul` (Gap C).
Not attempted yet; blocked on Gaps A/B/C being real theorems to plug in,
not blocked on any remaining Lean bookkeeping uncertainty.
