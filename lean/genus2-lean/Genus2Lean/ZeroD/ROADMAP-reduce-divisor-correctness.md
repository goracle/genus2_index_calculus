# Roadmap: `reducedClass ↔ isReduction'` (Reduce's divisor-class correctness)

## Status as of this pass (supersedes the relevant part of
## `ROADMAP-reduce-to-zerodim.md` step 2, item 2 — that item is what
## this document scopes in detail)

`ROADMAP-reduce-to-zerodim.md` correctly predicted this gap and
correctly said it wasn't scoped yet ("likely deserving its own roadmap
section once someone sits down with `DivisorClassGroup.lean` directly").
That sitting-down happened this pass. Findings:

- `DivisorClassGroup.lean` (237 lines, 0 sorry) is thin — it defines
  `Jacobian H D` abstractly over any `P : PrincipalDivisorData H` and is
  NOT itself where the gap lives.
- `PrincipalDivisorSubgroup.lean` (212 lines, 0 sorry) supplies a real,
  honestly-partial `PrincipalDivisorData` instance for degree-5 `H`
  (`principalSubgroup`, gated on `[IsDedekindDomain (CoordinateRing H)]`
  and friends) — this is NOT a stub; it typechecks and is load-bearing.
- `PrincipalDivisors.lean`/`PrincipalDivisorsDedekind.lean`/
  `PrincipalDivisorsIntegralClosure.lean` are a large (4400+ line)
  function-field/Dedekind-domain development (`ordAt`, CRT, `deg(div g)
  = 0`) that backs the instance above. Comment-stripped, live-tactic
  `sorry` count in `PrincipalDivisors.lean` itself is 0 — the `sorry`
  hits from a raw grep are all inside `/- ... -/` prose describing
  historical/still-conditional status, not open goals. Its main target
  theorem (`deg_div_eq_zero_deg5`-shaped) is proved, but conditioned on
  two hypotheses (`hspec`, a `Module.Finite` instance bundle) that are
  deliberately kept as hypotheses per project convention rather than
  derived — that's fine, matches "weaken first" policy, not a gap to
  chase right now.
- `Reduce/` (`AlphaReduce.lean`, `GeneralSharedRoot.lean`,
  `ReduceDispatchGeneral`) proves **polynomial-level Mumford
  correctness only** (`ReduceGeneral_isMumfordTarget4`: output satisfies
  `v² ≡ f mod u`). It does NOT mention `Jacobian`, `toJacobian`, or
  `Divisor0` anywhere except in prose pointing elsewhere. This is
  confirmed, not a re-open.
- The actual gap is `AlphaLocusDegreeUniform.lean`'s own docstring,
  verbatim: `isReduction'` (coordinate-level, real equation, computable
  RHS) and `reducedClass`/`isReduction` (divisor-class-level, the
  `SampleTargetFromAlpha` field) are two separate things, and **nothing
  proves they coincide**. `isReduction'` has 10 raw `sorry` hits in that
  file (need to re-check comment-stripped count — see Step 0 below,
  don't trust the raw number).

## Step 0 (do this first, before anything else below)

Re-run the comment-stripped sorry scan (the one that correctly flagged
`PrincipalDivisors.lean` as 0 live sorries despite 13 raw hits) against
`AlphaLocusDegreeUniform.lean` and `GeneralSharedRoot.lean`'s single raw
hit. We don't yet know the TRUE live-sorry count in either file — do not
plan Step 1 below off the raw `grep -c sorry` numbers, they're known to
overcount in this codebase. Also confirm both files currently build
clean (per project convention: verify before building on top of
anything, and per the earlier note that `GeneralSharedRoot.lean`'s
build status was "less explicitly confirmed" last time it mattered).

## Step 1 — smallest honest move: make `isReduction'` load-bearing

Nothing here requires new math yet. Per
`ROADMAP-reduce-to-zerodim.md` step 2 item 1: once `hdeg2` is closed
(that's step 1 of the OLD roadmap, may already be done — check), swap
`SampleTargetFromAlpha`'s bare `isReduction : Prop` field for
`isReduction'`'s actual statement, or add
`isReduction'_implies_isReduction` connecting them. This doesn't touch
the divisor-class gap but stops the file from carrying two unrelated
notions under confusingly similar names. Cheap, mechanical, do it
first — eliminates a live sorry (the unconstrained `isReduction : Prop`
field is itself effectively an escape hatch) without needing any new
algebraic-geometry content.

## Step 2 — state the real target theorem (as a named `sorry`, not
## attempted yet)

Write, but do not try to prove, something of the shape:

```
theorem reducedClass_eq_of_isReduction'
    {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : F p)
    (hcur : ...) (hgcd : ...) (hcurT : ...) (hgcdT : ...)
    (hr : isReduction' sa c0 c1 c2 c3 c4 ua0 ua1 va0 va1 hcur hgcd hcurT hgcdT) :
    sa.reducedClass = <the class that sa.toSampleTarget's Mumford pair
      represents, via PrincipalDivisorSubgroup.lean's toJacobian> := by
  sorry
```

Exact signature TBD once Step 0's build check is done — the point of
this step is only to get the statement to typecheck, with a `sorry`
body, and present it for review before spending real effort proving it.
This is the theorem `ROADMAP-reduce-to-zerodim.md` flagged as "not
attempted here."

Concretely this needs, in this order:
1. `toJacobian`/whatever `PrincipalDivisorSubgroup.lean` calls the map
   from a Mumford pair `(u0,u1,v0,v1)` to a class in `Jacobian H D` —
   grep for it, don't assume a name.
2. `reducedClass`'s definition (`AlphaLocusDegreeUniform.lean`, already
   read this pass: `alpha • aClass - ([P1]+[P2]-2•[δ₀])`) restated
   through that map.
3. A genuine equality goal between (2) and "the class represented by
   `sa.toSampleTarget`'s coordinates via (1)".

If any of 1–3 reveals `PrincipalDivisorSubgroup.lean`'s `toJacobian`
(or equivalent) doesn't yet have the API needed to even STATE this
(e.g. no lemma computing which class a coordinate pair represents),
stop and flag that as its own smaller gap rather than guessing an API
that isn't there — same policy as `toCoords` was handled last pass
(named hypothesis until the real definition was confirmed available).

## Step 3 — attempt the proof, easiest sub-piece first

Do not attempt this whole theorem in one pass. Classical structure of
Cantor's reduction algorithm's correctness proof (this is genuinely
"deep classical algebraic geometry," flagged honestly, not polynomial
bookkeeping) — asked ChatGPT (prompt: `CHATGPT-PROMPT-step3-reduce-
correctness.md`), answer summarized below. **The one correction to
our own framing from Step 3's original draft above: `phi` itself is
NOT the principal-divisor witness. The witness is a genuine
function-field element built from `phi`, `N` is only a supporting
computation that locates the residual support.** Read all of §3a
before writing any Lean for this step — the old draft's item 1
("`phi` witnesses a principal divisor") is the mistake this corrects.

### 3a. The math (from ChatGPT, condensed to what's actionable)

**Setup.** `C : y² = f(x)`, deg f = 5, one point at infinity `δ₀`,
`ord_{δ₀}(x) = -2`, `ord_{δ₀}(y) = -5`. A cubic `phi` has pole order 6
at `δ₀`. `N(x) = phi(x)² - f(x)` is the **norm** of `y - phi` down to
`K(x)` (i.e. `(y-phi)(y+phi) = f - phi² = -N`) — this is why `N` lives
purely in `K[x]`: norms forget which side of the hyperelliptic
involution `ι(x,y) = (x,-y)` a point is on.

**Three-lemma skeleton, in order** (this maps directly onto three
separate Lean lemmas — do not collapse them):

1. **Residual-intersection lemma** (algebra only, closest to what's
   already done). `u_old ∣ N` where `u_old` is the known Mumford
   polynomial (the input `u_a`-pair times `(x-x1)(x-x2)` for `P1,P2`,
   in the general-composition case). Write `N = u_old · u_new`;
   `deg N = 6`, `deg u_old = 4` ⟹ `deg u_new = 2`. **This is the
   `hdeg2`/hdeg-shaped computation Step 1 of the OLD roadmap and
   `ReduceGeneral_isMumfordTarget4` already prove** — it's the same
   polynomial-divisibility fact, just now understood as "the x-
   projection of the residual intersection divisor," not merely "a
   degree bound." No new Lean content here, just a new interpretation
   of an existing lemma — confirm this identification before assuming
   any of it needs re-proving.

2. **Residual Mumford lemma.** `v_new ≡ -phi (mod u_new)` — **the minus
   sign is load-bearing, not cosmetic.** `(u_new, v_new)` represents
   the divisor of the hyperelliptic-*conjugate* residual points
   `R̄ᵢ = (rᵢ, -phi(rᵢ))`, not the residual points themselves. Check
   this sign against `GeneralSharedRoot.lean`'s actual `v_new`
   construction before trusting it already matches — this is
   independently exactly the kind of sign bug ChatGPT flags in §6/§13
   below as the single most likely place for a "looks right, proves
   the wrong class" failure.

3. **Principal-witness lemma — the actual theorem to state and prove.**
   Define `h(x,y) = (y - phi(x)) / u_new(x)` as an element of the
   function field / `CoordinateRing`. Then for every closed point `P`
   (i.e. every place `ordAt` can be evaluated at):
   ```
   ordAt(h, P) = coeff_P(D_old) - coeff_P(D_new)
   ```
   equivalently `div(h) = D_old - D_new` globally. **`h`, not `phi`
   and not `N`, is the thing whose `ordAt`-divisor you compute.** This
   is the theorem that actually proves `[D_old] = [D_new]` in
   `Jacobian H D` (a principal divisor is 0 in the quotient) — once
   this is proved, `reducedClass_eq_of_isReduction'` (Step 2) should
   follow close to mechanically via `toJacobian`'s `AddMonoidHom`
   structure and `PrincipalDivisorData.P`'s membership.

   Why `div(h) = D_old - D_new`, sketched (full detail in the raw
   ChatGPT reply, kept below for reference):
   - At each `Rᵢ` (root of `u_new`): `y - phi = 0` there too, so the
     zero of `u_new` and the zero of `y-phi` cancel — no contribution.
   - At each `R̄ᵢ` (conjugate): `y - phi(rᵢ) = -2·phi(rᵢ) ≠ 0`
     generically, while `u_new(rᵢ) = 0` — pole.
   - At `δ₀`: `ord(y-phi) = -6`, `ord(u_new) = -4` (deg 2 poly, and
     `ord_{δ₀}(x)=-2`), so `ord(h) = -6-(-4) = -2` — matches the `2δ₀`
     correction term already built into `reducedClass`'s definition.
   - Zeros at the four known points of `D_old` fall out of `phi`'s
     interpolation conditions directly.

4. **Uniqueness/reducedness lemma — separate from Cantor geometry,
   needed to finish.** §3's argument only gives `[D_old] = [D_new]` in
   the quotient — that the Mumford pair is *the* reduced representative
   of that class (not just *a* representative) needs the existing
   reducedness/uniqueness machinery (deg `u ≤ 2 = g`, already-proved
   Mumford congruence). Check what's already on file for this in
   `DivisorClassGroup.lean`/`PrincipalDivisorsDedekind.lean` before
   assuming it needs new work — likely mostly already available.

### 3b. Case split — confirm against existing Lean structure

Item 2 above (`P1 = P2`) further splits into two, and ChatGPT flags a
sub-case our existing `hcurT`/`hgcdT` split does NOT yet obviously
cover:

- `P1 ≠ P2`: ordinary interpolation, `phi(x1)=y1, phi(x2)=y2`.
- `P1 = P2`, `y(P) ≠ 0`: Hermite/tangent interpolation — need
  `phi(x0)=y0` AND `phi'(x0) = f'(x0)/(2y0)` (order-2 contact).
- `P1 = P2`, `y(P) = 0` (**Weierstrass/ramification point — not
  currently split out anywhere in our code, check `hcurT`/`hgcdT`
  cover this or explicitly exclude it**): the tangent formula divides
  by `y0 = 0` and is undefined; geometrically the tangent is vertical,
  not a graph `y=phi(x)`. Has its own, much simpler witness:
  `div(x - x0) = 2P - 2δ₀` directly, no interpolation needed at all.
  **Action: check whether `H.Point`/the doubling branch already
  excludes `y=0` points by hypothesis somewhere upstream; if not, this
  is a genuine missing case, not just a proof-difficulty issue.**

None of this needs algebraic closure or characteristic 0 anywhere —
confirmed explicitly by ChatGPT (§10-§11 of the raw reply): the
splitting-field language ("let R1,R2 be the roots of u_new") is only
informal intuition. The actual Lean statement should stay in `K[x]`-
divisibility / `ordAt`-at-places language throughout, which is already
how `PrincipalDivisors.lean`'s machinery is built — good sign this
maps cleanly onto existing infrastructure rather than needing a new
closed-field-flavored layer.

### 3c. Sign-convention risk — check this before writing any Lean

**Highest-priority thing to verify against the actual code, per
ChatGPT's own flagging (§6, §13) — do this before Step 3a/3b's Lean
work, it can invalidate the direction of the whole theorem if wrong:**
our target is `D_old = alpha•aClass - [P1] - [P2] + 2[δ₀]` (note the
minus signs on `P1`, `P2`). The elementary interpolation argument
above naturally proves the statement for `alpha•aClass + [P1] + [P2] -
2[δ₀]` (plus signs) — interpolating `phi` through `P1, P2` directly
makes `y - phi` vanish AT `P1, P2`, not at their hyperelliptic
conjugates `ι(P1), ι(P2)`. Since Mumford negation is `(u,v) ↦ (u,-v)`,
subtracting `Pᵢ` means the interpolation should pass through `ι(Pᵢ)`
(i.e. `phi(x(Pᵢ)) = -y(Pᵢ)`), NOT through `Pᵢ` itself — unless
`GeneralSharedRoot.lean`'s actual `E`/`Y`/`va0,va1` construction has
already absorbed this sign somewhere. **Check this first**: does the
existing interpolation code (whatever sets up `phi`/`E`/`Y` from
`sa.P1`, `sa.P2`) pass through the points or their conjugates? This
determines whether Step 3's theorem, as stated in Step 2, is even
provable as written, or needs a sign flip either in `reducedClass`'s
definition or in the interpolation setup.

### 3d. General `E + Y·y` formulation (matches actual code, not just `phi`)

The code doesn't always use literal `y - phi(x)`; the general form is
`g = E(x) + Y(x)·y` with norm `N(x) = E(x)² - f(x)Y(x)²` (matches
`Npoly4`/`Ypoly4`/`Epoly4` naming already in `AlphaReduce.lean`). Same
structure applies: `N` locates zeros/poles of `g` or its conjugate
`ḡ = E - Y·y` but doesn't by itself say which; `g` itself (not `N`)
is the actual function-field element whose divisor matters. The
eventual principal-witness lemma (3a item 3) should likely be phrased
in terms of `g`/`ḡ` directly (or `g` divided by an `x`-only
denominator) to match the existing `E,Y,N` naming already in the
codebase, rather than reintroducing bare `phi` notation.

### 3e. Robustness note — don't over-assume distinctness

Do not build in a blanket "all residual points are distinct from the
old ones" assumption. If `u_old` and `u_new` share a root, valuations
need multiplicity accounting rather than clean cancellation — this is
exactly why Cantor composition ordinarily gcds `u1, u2, v1+v2` first.
State the principal-witness lemma (3a item 3) in terms of `ordAt`
valuations/multiplicities from the start rather than "N distinct
roots," so the distinct-point case is the easy specialization
(`ordAt ∈ {0,1}` everywhere) rather than a separately-proved base case
that the multiplicity version has to redo.

Once 3a–3e are digested, this is exactly the kind of "hard sorry" this
project's convention says to draft a ChatGPT prompt for rather than
grinding alone — once Step 2's statement is nailed down and
typechecks, follow up with ChatGPT (plain, no elaborate md file) for
help turning §3a item 3's `ordAt`-at-each-place argument into an
actual Lean proof against `PrincipalDivisorsDedekind.lean`'s real
`ordAt` API (exact lemma names not yet checked against it this pass).

## Explicit non-goals (per project's own prior correct call in the old
## roadmap, re-affirmed here)

- Do NOT re-derive `hspec`/`Module.Finite` in `PrincipalDivisors.lean` —
  out of scope, already correctly left as hypotheses.
- Do NOT touch `RegularSequenceFiniteQuotient.lean`/
  `PeelChainAssembly.lean` — old roadmap's step 3 already correctly
  identified that connection as free once `isReduction'` is real,
  no new Lean needed there.
- Do NOT attempt closed-field machinery anywhere in this — `F p` only,
  per project ground rule.

## Status update (this pass)

Steps 0.5, 1, and 2 are done. Sign-convention check (§3c) confirmed:
`reducedClass`'s minus-sign definition is correct as written (traced
through `GeneralSharedRoot.lean`'s `hEeq`/`vRS4General := -E·Y⁻¹`,
matching ChatGPT's §2/§4 expectation exactly) — no fix needed to either
`reducedClass` or the interpolation setup. Step 1's `isReductionOf`
(existential packaging `isReduction'`) is in
`AlphaLocusDegreeUniform.lean`. Step 2's `reducedClass_eq_of_isReduction'`
now typechecks there as a named `sorry`, built against
`PrincipalDivisorSubgroup.lean`'s real `toPair`/`divToPair`/`ordAt`
(newly imported into `AlphaLocusDegreeUniform.lean`) — confirmed, per
Step 2's own instruction, that there is no ready-made "Mumford pair to
`Divisor H`" function, so the statement takes the witnessing finite
point set `S` (and its `hsupp`/membership-in-`Divisor0` facts) as
hypotheses rather than computing it. Step 3 (the actual proof, §3a's
three-lemma skeleton) is next and not yet attempted.

## Status update (this pass, 2nd)

Re-confirmed Step 2's sorry count: exactly two live `sorry`s in
`AlphaLocusDegreeUniform.lean` (line 625, `reducedClass_eq_of_isReduction'`
— Step 3's target; line 718, `decoupledSystem_degree_uniform` — unrelated,
out of scope). Confirmed item 1 of §3a's three-lemma skeleton
(residual-intersection: `u_old ∣ N`, `deg u_new = 2`) is **already fully
proved, unconditionally**, in `Reduce/GeneralSharedRoot.lean` —
`uRS4General_dvd_Npoly4` (no `IsCoprime` hypotheses needed) and
`uRS4General_natDegree_eq_two`. No new Lean needed for item 1, matches
the roadmap's own prediction.

Surveyed the real `ordAt` API this file's Step 2 sorry already imports
(`PrincipalDivisorSubgroup.lean` → `PrincipalDivisors.lean`,
`RiemannRochGenus2.lean`, `HyperellipticClassProof.lean`). It's
substantial and genuinely usable, not stub-shaped: `ordAt_toPair_mul_of_ne_zero'`
(additivity under multiplication), `ordAt_linX_eq` (fully assembled
not-root/unramified/ramified case split for a linear factor — the
Weierstrass-point subtlety §3b flagged is *already handled* here, not
missing), `ordAtFrac`/`ordAt_sub_ordAt_eq_of_polePairToFraction_eq`
(fraction-level valuation). Some neighboring lemmas in
`HyperellipticClassProof.lean` (§B sub-branches) are themselves still
`sorry`'d in-progress work — not all of this file's API is finished —
but the specific lemmas listed above are fully proved and directly
reusable. Note: `RiemannRochGenus2.lean` has a file-level
`variable [IsAlgClosed k]`, but every lemma actually used above is
individually `omit [IsAlgClosed k] in`'d, so none of it pulls in
closed-field machinery — confirmed compatible with the `F p`-only rule.

Per project convention (hard sorries → draft a ChatGPT prompt), wrote
`CHATGPT-PROMPT-step3-ordat-translation.md` asking specifically how to
structure the principal-witness lemma's Lean proof against this real
API (fraction representation, the point-by-point case split, `δ₀`
handling since infinity may not have a `pointIdeal`, and how to use
the existing `S`/`hsupp`/`hmem` parameters for the multiplicity-
robustness note rather than assuming distinct roots). Not yet sent —
next step is to copy that prompt to ChatGPT and bring the reply back
before writing any proof body for the Step 2 sorry.

## Status update (this pass, 3rd) — build-error fix, no new math

Fixed the build errors blocking `AlphaLocusDegreeUniform.lean` (errors
first, per project ordering). Root cause: `reducedClass_eq_of_isReduction'`
(Step 2's statement) called `divToPair H A B S`, but `divToPair` in
`PrincipalDivisorSubgroup.lean` takes `H` as an implicit **section**
`variable`, not an explicit argument (unlike `toPair`, which genuinely
does take `H` explicitly) — so `H` was being passed positionally into
`divToPair`'s `A` slot, producing the `HyperellipticPolynomial (F p)` vs
`Polynomial ?m` mismatch, which cascaded into the `Function expected at C`
errors on the following `C`/`X` terms (their expected types collapsed to
metavariables once the surrounding application failed to elaborate).
Fix: dropped the explicit `H` from both `divToPair` call sites (the
`hmem` hypothesis and the final anonymous-constructor term); `H` is
inferred at both from the ambient `Divisor0 H` / `toJacobian D` expected
types. Also corrected the three docstring mentions of `divToPair H A B S`
above the theorem, which described the same (wrong) explicit-`H` calling
convention. No sorry count changed by this pass — still exactly two live
sorries (`reducedClass_eq_of_isReduction'` at Step 2, and the unrelated,
explicitly-out-of-scope `decoupledSystem_degree_uniform`). Not yet
re-verified against a live `lake build` (Claire's repl per project
convention) — flagging as fixed-per-careful-reading, not confirmed-green.

## Status update (this pass, 4th) — build error persisted, real root cause

The 3rd pass's fix was necessary but not sufficient — Claire's rebuild
still failed, now with `failed to synthesize instance of type class
Membership (Divisor ?m.762) (AddSubgroup H.Divisor)` at the `hmem`
line, plus the same cascade of `Function expected at C` errors on the
`X`/`C` terms feeding it. Actual root cause: dropping `H` entirely (3rd
pass's fix) relies on Lean inferring it from context, but nothing in
`divToPair`'s own argument types (`A B : k[X]`, `S : Finset H.Point`)
pins `k`/`H` down *before* `A`/`B` need to be elaborated — `A`/`B` are
built from `X`/`C`, whose own expected type depends on `k`, which
depends on `H`. This is circular under ordinary left-to-right
unification: elaborating `A` needs `H` (for `k[X]`'s `k`), but `H`
isn't resolved until the whole `divToPair` application's result type is
checked against `Divisor0 H`'s ambient type in `hmem`/the goal — too
late for `X`/`C` inside `A`/`B` to already know what ring they live in.
**Fix: named-argument syntax at both call sites**, `divToPair (H := H)
A B S` (and, for the same reason and to avoid asymmetric fragility even
though this particular occurrence built cleanly last time, `ordAt (H :=
H) P A B` in `hsupp` too) — this pins `H` immediately, before `A`/`B`
are elaborated, so `X`/`C`'s expected type (`Polynomial (F p)`, since
`H : HyperellipticPolynomial (F p)`) is known from the start and the
`Function expected at C` cascade cannot occur. Updated the docstring
above the theorem to describe this explicitly (why bare unification
doesn't work here, unlike the more common case where an implicit is
recoverable from a later explicit argument). Not yet re-verified
against a live build — this is the second attempt at the same two
call sites, so treat with slightly more scrutiny than usual on the
next rebuild report.

## Status update (this pass, 5th) — `whnf` heartbeat timeout, statement restructured

Claire's rebuild after the 4th pass's fix got past the type-mismatch/
instance-synthesis errors entirely, but hit a new failure: `(deterministic)
timeout at whnf, maximum number of heartbeats (200000) has been reached`,
pointing at the goal/`hmem` line. Per the project's own heartbeats guidance
("unroll the proof a bit and clear state you don't need, before increasing
heartbeats") — but this is a *statement* elaborating, not a tactic proof (the
body is just `sorry`), so there's no tactic state to unroll; the fix has to
be in the statement's shape instead. Two changes:

1. The Mumford-pair polynomial encoding (`X^2 + C u1 * X + C u0`, `C v1 * X +
   C v0`) was spelled out inline three separate times across `hsupp`, `hmem`,
   and the goal. Each occurrence forces the elaborator to redo the same
   `X`/`C`-against-`(F p)[X]` unification independently, compounded by
   `divToPair (H := H)`/`ordAt (H := H)`'s own unification work at each site.
   Factored `u v : Polynomial (F p)` out as their own named parameters with
   defining equalities `hu`/`hv`, so the polynomial expression is elaborated
   exactly once and every other hypothesis/the goal just refers to `u`/`v`.
2. The goal's `⟨divToPair ..., hmem⟩` anonymous-constructor term was being
   checked against `toJacobian D`'s expected argument type `↥(Divisor0 H)`,
   which requires unfolding through `AddSubgroup`/`SetLike`/`Subtype`
   coercions to accept anonymous-constructor syntax — likely the actual
   `whnf` hotspot. Replaced with an explicit `Subtype.mk (divToPair (H := H)
   u v S : Divisor H) hmem`, so the `Divisor H` ascription is settled as its
   own step before the subtype-membership coercion is attempted.

Updated the docstring immediately above the theorem with this rationale.
Checked for downstream call sites of `reducedClass_eq_of_isReduction'`
(grepped the whole `ZeroD` tree) — none exist yet, so widening its parameter
list (`u v` as new explicit arguments) breaks nothing. Not yet re-verified
against a live build — third attempt at this same theorem's statement, so
if this doesn't clear it, worth considering whether `IsDedekindDomain
(CoordinateRing H)` itself (an instance argument, not searched but still
present in every surrounding type) is contributing unfolding cost, or
whether `set_option maxHeartbeats` at the statement level is the more
honest fix at that point rather than continuing to restructure.

## Status update (this pass, 6th) — heartbeat timeout cleared, one more `C`/`X` fix

Claire's rebuild after the 5th pass got past the `whnf` timeout entirely
(confirming the `u v`/`Subtype.mk` restructuring worked), but hit the same
`Function expected at C` failure as before — now isolated to `hu`/`hv`
themselves rather than cascading from `divToPair`. Root cause: `hu : u = X^2
+ C ... ` relies on `u`'s declared type (`Polynomial (F p)`, two lines up)
flowing across the `=` into the RHS to resolve `X`/`C`'s implicit ring — it
doesn't; Lean's equality elaboration doesn't propagate the LHS's type into
an under-constrained RHS that way. Same root issue as the `divToPair
(H := H)` fix two passes ago, just relocated. Fix: ascribed both RHSs
directly, `hu : u = (X ^ 2 + C ... + C ... : Polynomial (F p))` and
similarly for `hv`. Updated the docstring above the theorem to fold this
into the existing "statement shape, revised this pass" explanation rather
than adding a separate note. Not yet re-verified — fourth attempt at this
theorem's statement; if a build report still shows a `C`/`X` or elaboration
error at this point, stop restructuring inline and instead build `u`/`v`
as their own top-level `def`s (e.g. `mumfordU sa : Polynomial (F p) := ...`)
so the ring is fixed once at the definition site with no `=`/ascription
juggling needed anywhere downstream.

## Status update (this pass, 7th) — same `C`/`X` error persisted, per-term ascription

Claire reported the identical error at the identical column positions after
the 6th pass's fix — confirmed via `md5sum` that the file she built was in
fact the ascribed version, so this ruled out a stale-file mixup and
confirmed the fix itself didn't work as intended. Diagnosis: ascribing the
*whole summed expression* (`(X^2 + C u1 * X + C u0 : Polynomial (F p))`)
still fails, because `+`'s elaboration doesn't necessarily propagate an
outer expected-type ascription down into each individual summand before
that summand's own head symbol (`C`) needs its implicit argument resolved —
so `C` was still being elaborated against an unconstrained metavariable
first, same as with no ascription at all. Real fix: ascribe `X` and each
`C _` application *individually* — `(C sa.toSampleTarget.u1 : Polynomial (F
p))` — which pins `Polynomial.C : R →+* R[X]`'s `R` immediately via the
codomain, with no dependency on how the surrounding `+`/`*`/`=` propagate
types afterward. This is a strictly more robust pattern than ascribing a
compound expression as a whole, worth remembering for future statements in
this file that build `k[X]` terms from `X`/`C` this way. Not yet
re-verified.

## Ordering summary (errors first, then sorries, easiest first)

0. Re-run comment-stripped sorry scan on `AlphaLocusDegreeUniform.lean`
   + `GeneralSharedRoot.lean`; confirm both build clean.
0.5. **New, cheap, do early**: check the sign-convention question in
   §3c against the actual `GeneralSharedRoot.lean` interpolation setup
   (does `phi`/`E,Y` pass through `P1,P2` or their conjugates
   `ι(P1),ι(P2)`?). Answering this doesn't require writing any new
   Lean, just reading existing code — but it determines whether
   `reducedClass`'s definition or the interpolation code needs a sign
   fix before Step 2/3 are worth attempting at all. Do this before
   Step 1, since a sign mismatch could change what Step 1's
   unification should even state.
1. `isReduction`/`isReduction'` unification (mechanical, no new math).
2. State `reducedClass_eq_of_isReduction'` as a `sorry`, present for
   review before proving.
3. Prove it via the three-lemma skeleton in §3a (residual-intersection
   → residual-Mumford → principal-witness via `ordAt(h,P)` → class
   equality), checking §3b's Weierstrass-point case is actually
   excluded or covered, and §3e's multiplicity-robustness note. The
   classical math for this step is now in hand (§3a-§3e above,
   confirmed to need no closed-field or char-0 machinery) — what
   remains is turning §3a item 3's `ordAt`-at-each-place argument into
   Lean against `PrincipalDivisorsDedekind.lean`'s actual API; draft a
   follow-up ChatGPT prompt for that translation once Step 2 typechecks.

## Status update (this pass, 8th) — Step 3 started: two statement gaps
## fixed (errors first), first stack lemma proved

Before writing any proof body, re-checked `reducedClass_eq_of_isReduction'`'s
statement itself against the real `PrincipalDivisorSubgroup.lean`/
`DivisorClassGroup.lean` API (not just against what Step 2 needed to
typecheck) and found two genuine gaps — both fixed now, not deferred:

1. **`D` was fully generic.** `PrincipalDivisorData H` places no constraint
   on `D.P` beyond `≤ Divisor0 H` — nothing ties it to `CoordinateRing H`
   or the genuine principal divisors. The Step-3 argument can only ever
   produce `D_old - D_new ∈ principalSubgroup H hdeg`
   (`PrincipalDivisorSubgroup.lean`), so `toJacobian D (D_old - D_new) = 0`
   is FALSE for an arbitrary `D` without an extra hypothesis. Added
   `hdeg : H.f.natDegree = 5` and `hD : principalSubgroup H hdeg ≤ D.P` —
   the weakest fix that doesn't force `D` to be the concrete
   `principalDivisorData H hdeg` instance, keeping `D` abstract elsewhere
   in the file per its existing convention.
2. **`H.f` was never linked to `curvePoly p c0 c1 c2 c3 c4`.** The norm
   argument (`toPair_mul_involution`, `pairNorm H A B = A²-B²·H.f`) is
   stated against `H.f`; `Npoly4`/`Epoly4`/`Ypoly4` are stated against
   `curvePoly p c0..c4`. Nothing previously connected the two. Added
   `hf : H.f = curvePoly p c0 c1 c2 c3 c4`.

No downstream call sites of `reducedClass_eq_of_isReduction'` exist yet
(re-checked), so widening the hypothesis list breaks nothing. Sorry count
unchanged (still exactly the same two live sorries as the 7th pass) — this
was a statement fix, not proof progress, and is flagged as such rather than
counted as Step 3 work.

**Actual Step 3 work started**: new file
`Genus2Lean/ZeroD/Reduce/PrincipalWitness.lean`, kept deliberately ignorant
of `SampleTargetFromAlpha`/`aClass`/`hr` per the ChatGPT reply's own §16
recommendation (the principal-witness lemma stack should be provable
generically against `E Y : k[X]`/`H : HyperellipticPolynomial k`, with only
the final assembly theorem back in `AlphaLocusDegreeUniform.lean` touching
project-specific names). Contains:

- `toPair_mul_toPair_neg_eq_algebraMap_pairNorm`: the norm identity
  `g·ḡ = N` (ChatGPT §2/§13 step 2), proved — essentially
  `toPair_mul_involution` with `involution H (toPair H E Y)` unfolded to
  the concrete pair `toPair H E (-Y)` via `toPair_involution`, since the
  next lemma in the stack (`ordAt_toPair_mul_of_ne_zero'`) needs a
  concrete `(A', B')` pair, not the abstract `involution` application.
- `pairNorm_eq_of_eq_curvePoly`: bridges `pairNorm H E Y` to the
  `Npoly4`-shaped `E² - Y²·curvePoly p c0..c4` using the new `hf`
  hypothesis, so later lemmas can rewrite `Npoly4 ...` directly into
  `pairNorm`/`toPair` form.

No `sorry` in this new file — both lemmas are complete, small, and close
to definitional unfolding, matching "easiest first." Not yet build-checked
(same caveat as every pass — Claire's REPL is the source of truth).

## Status update (this pass, 9th) — `PrincipalWitness.lean` build errors fixed

Claire's rebuild: `AlphaLocusDegreeUniform.lean` built clean (both sorries
are the expected two, per Step 3/`decoupledSystem_degree_uniform`), but the
new `PrincipalWitness.lean` failed with `Unknown identifier 'curvePoly'` and
`Function expected at F`. Root cause: that file never imported/opened
`Genus2Lean.TheDataDerivation` — `curvePoly`, and `F` itself, are defined
inside `namespace Genus2Lean.TheDataDerivation` (`AlphaReduce.lean`/
`DataDerivationBasics.lean` both live there), and `AlphaLocusDegreeUniform.
lean` only sees them unqualified because it has its own `open
TheDataDerivation` at file scope — a fact I'd read but didn't carry over to
the new file. Fix: added `open Genus2Lean.TheDataDerivation` to
`PrincipalWitness.lean`, and added the missing `[Fact (Nat.Prime p)]`
instance to `pairNorm_eq_of_eq_curvePoly` (`curvePoly`'s own section
`variable`s require it; `H`'s `Field (F p)` instance doesn't necessarily
force Lean to synthesize it automatically at this call site). Also added
`set_option linter.style.header false` to match every other file in this
project (avoids the same copyright-header lint warning the build log
otherwise flags). Not yet re-verified against a live build.

## Status update (this pass, 10th) — confirmed clean; lemmas 2-4 added

Claire confirmed `PrincipalWitness.lean` (9th pass's fix, using fully-
qualified `Genus2Lean.TheDataDerivation.F`/`curvePoly` rather than an
`open`) builds cleanly. Added the next three lemmas in the stack, still
kept generic (no `SampleTargetFromAlpha` dependence):

- `ordAt_eq_zero_of_eval_ne_zero` (lemma 2, ChatGPT §4/§13 step 4): the
  "residue-nonzero ⇒ valuation-zero" lemma ChatGPT flagged as possibly
  missing from the pasted API — it isn't missing, it's `toPair_mem_
  pointIdeal_iff` (`LCanonicalElementary.lean`) composed with `ordAt_eq_
  zero_of_notMem` (`RiemannRochGenus2.lean`), both already proved and
  confirmed `[IsAlgClosed k]`-free.
- `toPair_right_zero`: the `B=0` unfolding of `toPair`, restated as its own
  named lemma (same idiom already used in `LPairFinrankOneOrdAtFrac.lean`)
  since the next lemma needs it by name.
- `toPair_pairNorm_eq_toPair_mul_toPair_neg` (lemma 3, ChatGPT §2/§13 step
  3): the norm identity restated in the `(A,B)`-pair shape
  `ordAt_toPair_mul_of_ne_zero'`'s `hA₃` hypothesis actually needs
  (`toPair H N 0`, not `algebraMap _ _ N`) — trivial composition of lemma 1
  and `toPair_right_zero`.
- `ordAt_eq_ordAt_pairNorm_of_eval_eq_zero` (lemma 4, ChatGPT §3/§5/§13
  step 5): given `g ≠ 0` as a ring element and `ḡ(P) ≠ 0`,
  `ordAt P g = ordAt P N`. **Deliberately does NOT take `g(P) = 0` as a
  hypothesis** — checked and confirmed it isn't needed for this step (only
  motivates why `ḡ(P) ≠ 0` is the case worth supplying), so the lemma stays
  usable at points other than "ordinary zeros of `g`" too (e.g. eventually
  at `δ₀`-adjacent points, if that ever needs a similar move). Also
  deliberately takes `hg_ne : toPair H E Y ≠ 0` as an explicit hypothesis
  rather than trying to derive it from an eval-equals-zero fact — caught
  a genuine error in an earlier draft of this proof (`E=0,Y=0` vacuously
  satisfies "vanishes at one point" but does NOT give `toPair H E Y ≠ 0`;
  fixed before presenting, per §3e's "don't over-assume" discipline applied
  to the lemma's own hypotheses, not just to point-distinctness).

Also caught and fixed, before presenting: an editing mistake left two
adjacent block-comment docstrings (stale draft + final version) directly
above lemma 4 — exactly the "comment block followed by another comment
block" issue this project's conventions warn about. Removed the stale one.

No `sorry` anywhere in the file; all four lemmas fully proved. Updated the
file's own module-docstring status note to list lemmas 1-4 rather than
lemma 1 only. Not yet re-verified against a live build.

**Not yet done, next in the stack** (ChatGPT §13's numbered list, items
6 onward): the root-multiplicity translation for `N`/`u_new` via
`ordAt_eq_rootMultiplicity_unramified`/`_ramified` (§6-§8), the
factorization `N = A·U` at the pair level and the resulting
`ordAt P N = ordAt P A + ordAt P U` (§6/§13 step 7), the pointwise
coefficient identity (§13 step 9), and the `δ₀`-avoidance argument via
`Divisor0`'s degree-zero property (§12) rather than defining an infinity
valuation from scratch. Each should be its own small named lemma per
project convention — do not attempt the `∀ P` theorem in one pass.

## Status update (this pass, 11th) — build error fix: missing imports,
## not a namespace bug

Claire's rebuild failed on three `Unknown identifier` errors
(`ordAt_eq_zero_of_notMem`, `toPair_mem_pointIdeal_iff`,
`ordAt_toPair_mul_of_ne_zero'`) plus a cascading `unsolved goals` at
lemma 4's `:=` (an expected consequence of the third unknown identifier —
`hstep` never got defined, so `omega` had nothing to close the goal with;
not a separate bug). Root cause, confirmed by tracing the actual import
graph rather than re-guessing: all three lemmas genuinely live inside
`namespace HyperellipticPolynomial` (so the earlier "namespace" framing in
this file's own comments was right about *where* they're declared) but
**`PrincipalWitness.lean`'s import chain never reaches the files that
declare them** — `ordAt_eq_zero_of_notMem`/`ordAt_toPair_mul_of_ne_zero'`
are in `RiemannRochGenus2.lean`; `toPair_mem_pointIdeal_iff` is in
`LCanonicalElementary.lean`; neither is imported by
`PrincipalDivisorSubgroup.lean` (whose own chain stops one file short, at
`PrincipalDivisors.lean`) or by any of this file's other imports. This was
checked by existence (`grep` for the theorem name) last pass, not by
reachability (`grep` for the import chain) — the actual gap.

Fix: added `import Genus2Lean.RiemannRochGenus2` and
`import Genus2Lean.LCanonicalElementary` directly. Confirmed cycle-safe
before adding: both of those files already import
`Genus2Lean.PrincipalDivisorSubgroup` themselves (the reverse direction),
and grepped the whole tree to confirm nothing imports
`PrincipalWitness.lean` yet (new file, no consumers).

Claire confirmed this rebuild came back clean.

## Status update (this pass, 12th) — lemma 6 (root-multiplicity
## translation), unramified + ramified

ChatGPT §13 step 6 ("rewrite `ordAt P N` using
`ordAt_eq_rootMultiplicity_unramified`"). Confirmed the exact source
lemmas (`ordAt_eq_rootMultiplicity_unramified`/`_ramified`) already exist,
fully proved, `[IsAlgClosed k]`-free, in `LPairFinrankOneOrdAtFrac.lean` —
not previously imported by `PrincipalWitness.lean`; added that import,
checked cycle-safe first the same way as the 11th pass (that file's own
import list doesn't reach back to this one; nothing in `Genus2Lean`'s
root-level files references `PrincipalWitness`/`AlphaLocusDegreeUniform`
at all).

Added two lemmas, both direct compositions of lemma 4
(`ordAt_eq_ordAt_pairNorm_of_eval_eq_zero`) with the root-multiplicity
lemmas — no new proof technique, just chaining:

- `ordAt_eq_rootMultiplicity_pairNorm_of_eval_eq_zero` (unramified,
  `P.Y ≠ 0`): `ordAt P E Y = (pairNorm H E Y).rootMultiplicity P.X`.
- `ordAt_eq_rootMultiplicity_pairNorm_of_eval_eq_zero_ramified`
  (`P.Y = 0`, needs `Squarefree H.f`): `ordAt P E Y = 2 *
  (pairNorm H E Y).rootMultiplicity P.X`. Flagged in its docstring — not
  yet resolved, just stated for completeness — that per §3b/§14 of the raw
  ChatGPT reply, the Weierstrass case is geometrically different from a
  specialization of this lemma stack (`ḡ(P) = g(P)` there, so
  `hgbar_ne_eval` is a real extra assumption, not automatic from `hg_ne`
  the way it is in the unramified case) and the assembly theorem will
  likely need `div(x-x0) = 2P - 2δ₀` directly instead (§3b item 3), not
  this lemma. Matches the roadmap's own earlier §3b flag that the
  Weierstrass/ramification case isn't yet confirmed covered by the
  existing `hcurT`/`hgcdT` split.

One care point while writing the ramified lemma: matched the source
lemma's RHS shape (`2 * c.rootMultiplicity α : ℤ`, the whole product cast
at once) verbatim rather than writing `(2:ℕ) * (...).rootMultiplicity ...
: ℤ` (product formed at ℕ first, then cast) — the two ascriptions can
elaborate to different terms even though they're propositionally equal,
and matching the source exactly avoids relying on `omega`/`push_cast` to
bridge them inside a one-line `exact`.

Both `pairNorm H E Y ≠ 0` (`hN_ne`) is taken as an explicit hypothesis in
both lemmas rather than derived from `hg_ne`/`hgbar_ne_eval` — same
"don't over-assume" discipline as lemma 4's `hg_ne`; docstring flags that
it *should* be derivable (integral domain, no zero divisors, via lemma 1 +
`algebraMap` injectivity) but that step isn't established in this file yet
and isn't needed for lemma 6's own proof.

No `sorry` anywhere in the file; six lemmas now, all fully proved. Updated
the module-docstring status note. Sanity checks passed (paren/bracket
balance, no adjacent block comments, live-sorry grep clean). Not yet
re-verified against a live build.

**Not yet done, next in the stack** (ChatGPT §13 steps 7-9, per the raw
reply's §6-§9): the factorization `N = A · U` at the `(A,B)`-pair level
(where `U := u_new`/`uRS4General`'s Mumford `u`-polynomial and `A` is the
complementary cofactor) and the resulting `ordAt P N = ordAt P A +
ordAt P U` (§6, "cleanest formal route is probably to factor the whole
divisor computation"); `ordAt P h = ordAt P A` at a residual point (`h :=
g/U`, §13 step 8); the pointwise coefficient identity assembling
`coeff_P(D_old) - coeff_P(D_new) = ordAt P A` (§13 step 9); and the
`δ₀`-avoidance argument. Per §11/§12 of the raw reply: do NOT try to force
`δ₀` into the `ordAt`/`pointIdeal` machinery directly (it's built for
affine points only, confirmed in an earlier pass) — §12 has a
finite-field-safe replacement for reasoning about the point at infinity
that avoids defining an infinity valuation from scratch; read that section
carefully before attempting the `δ₀` piece. The Weierstrass (`P.Y = 0`)
case's own separate argument (§3b item 3 / §14) is also still open.

## Status update (this pass, 13th) — lemma 7 (`N = A·U` factorization at
## the pair level)

Claire's rebuild of the 12th pass's `PrincipalWitness.lean` (lemma 6, root-
multiplicity translation) came back clean. Continuing with ChatGPT §13
step 7 / raw reply §6 ("the cleanest formal route is probably to factor
the whole divisor computation").

Confirmed the concrete factorization this abstracts over already exists in
the codebase: `uRS4General_dvd_Npoly4` (`GeneralSharedRoot.lean`,
unconditionally proved, no new Lean needed there) gives exactly `N = A · U`
with `U := uRS4General` (the residual Mumford `u`-polynomial) — matches the
raw reply's own naming (§6: `N = A·U`, `U` the residual factor) once
translated into this project's variable names. Kept `PrincipalWitness.lean`
itself generic per its stated design (module docstring): lemma 7 below
takes the factorization `N = A * U` as an explicit hypothesis rather than
importing `GeneralSharedRoot.lean`-specific lemmas, so the eventual
assembly theorem in `AlphaLocusDegreeUniform.lean` supplies
`uRS4General_dvd_Npoly4`'s witness at the call site instead.

Added two lemmas:

- `toPair_mul_right_zero'`: the `(A,B)`-pair form of `k[X]`-multiplicativity
  for pure polynomials, `toPair H (A*U) 0 = toPair H A 0 * toPair H U 0` —
  the `B = B' = 0` special case of the existing `toPair_mul`
  (`RiemannRochGenus2.lean`). One care point while writing this: the naive
  `rw [toPair_mul]; simp` doesn't target the right occurrence (the goal's
  LHS is a single `toPair`, not a product, so an un-instantiated
  `toPair_mul` rewrite has nothing obviously to fire on, or could match
  ambiguously) — fixed by giving `toPair_mul` its explicit arguments
  (`toPair_mul A 0 U 0`), which pins the rewrite to the RHS's
  `toPair H A 0 * toPair H U 0` occurrence specifically, turning it into
  `toPair_mul`'s expanded form, which `simp` then collapses back to
  `toPair H (A*U) 0` (`0*0*H.f = 0`, `A*0+U*0 = 0`) to close the goal.
- `ordAt_add_of_pairNorm_eq_mul` (lemma 7, ChatGPT §6/§13 step 7): given
  `N = A * U` and both `toPair H A 0`, `toPair H U 0` nonzero,
  `ordAt P N 0 = ordAt P A 0 + ordAt P U 0`. Direct application of
  `ordAt_toPair_mul_of_ne_zero'` (already used by lemma 4) through
  `toPair_mul_right_zero'`.

No `sorry` anywhere in the file; seven lemmas now (plus the `Npoly4`-bridge
corollary), all fully proved. Updated the module-docstring status note.
Sanity checks passed (paren/bracket/comment balance, live-sorry grep
clean). Not yet re-verified against a live build.

**Not yet done, next in the stack**: `ordAt P h = ordAt P A` at a residual
point (`h := g/U`, ChatGPT §13 step 8) — needs `ordAtFrac`
(`ordAtFrac(P,E,Y,U,0) = ordAt(P,E,Y) - ordAt(P,U,0)` per §13 step 1,
already noted as essentially definitional/`rfl` in an earlier pass) plus
lemma 6/7 above composed together; the pointwise coefficient identity
(§13 step 9); and the `δ₀`-avoidance argument (§11-§12, finite-field-safe
replacement for the point at infinity — read that section before
attempting it, do not build an infinity valuation from scratch). The
Weierstrass (`P.Y = 0`) case's own separate argument (§3b item 3 / §14)
is also still open.

## Status update (this pass, 14th) — build error fix: missing
## `[IsDedekindDomain (CoordinateRing H)]`, plus an `apply`/`rw` fragility

Claire's rebuild of the 13th pass's lemma 7 failed with a cluster of
`failed to synthesize instance of type class IsDedekindDomain
(CoordinateRing H)` errors at `ordAt_add_of_pairNorm_eq_mul`, plus an
`unknown identifier hAU` and unsolved-goals errors cascading from it.
Two genuine bugs, both in that one lemma (`toPair_mul_right_zero'` itself
was fine as *stated*, but its proof needed hardening too — see below):

1. **Missing instance hypothesis.** `ordAt_add_of_pairNorm_eq_mul` calls
   `ordAt_toPair_mul_of_ne_zero'`, which needs
   `[IsDedekindDomain (CoordinateRing H)]` — but unlike that theorem's own
   declaration site (`RiemannRochGenus2.lean`, where an ambient `variable`
   supplies it silently), this file has no such `variable` in scope, and
   every other lemma here that calls into that machinery (2, 4, 6) states
   the instance explicitly. Lemma 7's first draft simply omitted it — a
   plain oversight, not a deeper issue. Fixed by adding
   `[IsDedekindDomain (CoordinateRing H)]` to `ordAt_add_of_pairNorm_eq_mul`'s
   own signature, matching the others.
2. **`apply ... ; rw [...]` didn't survive the instance failure cleanly.**
   Once the instance couldn't synthesize, the `apply` itself failed to
   elaborate, which is why the *next* line's `rw [hAU, ...]` reported
   `hAU` as an unknown identifier — `hAU` genuinely was in scope as a
   hypothesis, but Lean had already abandoned the tactic block's goal
   state by that point, so the error message is a symptom of bug 1, not a
   second independent naming bug. Still, switched the proof to a single
   term-mode expression (`ordAt_toPair_mul_of_ne_zero' P h_bot A 0 U 0 N 0
   hA_ne hU_ne (hAU ▸ toPair_mul_right_zero' A U)`) matching lemma 4's
   already-proven-working term style, rather than re-trying the same
   `apply`+`rw` split now that the instance is fixed — less exposed to the
   same class of cascading failure if anything else is subtly off.

Also hardened `toPair_mul_right_zero'`'s proof (which built successfully
as far as the log shows, but its `rw [toPair_mul]; simp` draft was fragile
by construction — the goal's LHS is a single `toPair` application while
`toPair_mul`'s LHS is a product of two, so an unapplied `rw [toPair_mul]`
has no guaranteed unique match to fire on): rewrote it to fix
`toPair_mul`'s statement concretely first via `have h := toPair_mul
(H := H) A 0 U 0`, simplify `h`'s right-hand side in place with `simp only`
(explicit lemma list: `mul_zero, zero_mul, add_zero, zero_add`, rather than
a bare `simp` that could silently do more or less depending on the
simp-set's future contents), then close with `exact h.symm` — no
ambiguous top-level rewrite involved.

No `sorry` anywhere in the file; seven lemmas, all fully proved (assuming
this fix is confirmed — not yet re-verified against a live build). Updated
both lemmas' docstrings to record the fix and reasoning, per project
convention (errors get fixed and explained, not just silently patched).

## Status update (this pass, 15th) — confirmed clean; lemma 8, the
## `ordAt P h = ordAt P A` theorem the stack was built toward

Claire confirmed the 14th pass's fix builds — with two small further
robustness tweaks beyond what I'd written: `toPair_mul_right_zero'` also
took its own explicit `[IsDedekindDomain (CoordinateRing H)]` (needed once
it's called from a context requiring that instance, even though the
lemma's own statement doesn't otherwise reference `CoordinateRing H`'s
Dedekind-ness), explicit `(0 : k[X])` ascriptions throughout both lemmas
in place of bare `0`, and `hAU.symm ▸ ...` in place of `hAU ▸ ...` (the
`▸`-direction needed flipping — `A*U = N`, not `N = A*U`, to transport
`toPair_mul_right_zero'`'s `A*U`-shaped conclusion into the `N`-shaped one
`ordAt_toPair_mul_of_ne_zero'` needs). Adopted Claire's confirmed-building
version verbatim and corrected this file's own docstring to describe
`hAU.symm ▸` rather than the earlier (wrong) `hAU ▸`.

Added ChatGPT §13 step 8 — "the theorem the whole stack has been building
toward" per the raw reply's own framing (§1: "First normalize every
occurrence of `h` to `ordAt(g) - ordAt(U)`... that gets the rest of the
proof into ordinary valuation arithmetic"):

- `ordAtFrac_eq_ordAt_of_pairNorm_eq_mul` (lemma 8): given `pairNorm H E Y
  = A * U`, both factors' `toPair`-nonvanishing, and lemma 6's conclusion
  (`ordAt P E Y = ordAt P (pairNorm H E Y) 0`, i.e. "`P` is an ordinary
  zero of `g`" already established via lemma 6 at the call site) as an
  explicit hypothesis `hN_eq_mult`, concludes `ordAtFrac P E Y U 0 =
  ordAt P A 0` — i.e. `ordAt P h = ordAt P A` for `h := g/U`, collapsing
  `ordAt P U 0` out entirely. Proof: `unfold ordAtFrac` (per raw reply §1,
  `ordAtFrac`'s definition is literally `ordAt P A B - ordAt P A' B'`, so
  this is the "essentially `rfl`/unfolding" bridge step ChatGPT names),
  then `rw [hN_eq_mult, ordAt_add_of_pairNorm_eq_mul ...]` chains lemma 6
  into lemma 7, and `omega` closes the resulting `(ordAt P A 0 + ordAt P U
  0) - ordAt P U 0 = ordAt P A 0` cancellation (no positivity assumption
  needed — `ordAt` is `ℤ`-valued).

`hN_eq_mult` is taken as a hypothesis rather than re-derived from lemma
6's own (longer) hypothesis list, so lemma 8's signature doesn't need to
carry both lemma 6's full preconditions (`hchar`, `hg_ne`, `hgbar_ne_eval`,
`hN_ne`, `hY`) and lemma 7's (`hAU`, `hA_ne`, `hU_ne`) simultaneously — the
eventual assembly theorem is expected to apply lemma 6 first at its own
call site and pass the result in, keeping each lemma here focused on one
composition step rather than accumulating every upstream precondition.

No `sorry` anywhere in the file; eight numbered lemmas (plus the small
`toPair_right_zero`/`toPair_mul_right_zero'` helpers and the `Npoly4`
bridge corollary — eleven `theorem`s total), all fully proved. Updated the
module-docstring status note. Sanity checks passed (paren/bracket/comment
balance, live-sorry grep clean). Not yet re-verified against a live build.

**Not yet done, next in the stack** (ChatGPT §13 step 9, raw reply §9):
the pointwise coefficient identity — packaging `coeff_P(D_old) -
coeff_P(D_new) = ordAt P A 0` with the project's actual sign convention
(per the roadmap's own §3c sign-check finding: `reducedClass`'s
minus-sign convention is the geometrically correct target, matching
`vRS4General := -E·Y⁻¹`, so this step should mostly be bookkeeping once
the residual-point case (this file's lemmas) and the non-residual/`g(P)≠0`
case (lemma 2 above, already done — `ordAt P g = 0` there) are both in
hand) — then the `δ₀`-avoidance argument (§11-§12, read before attempting;
do not build an infinity valuation from scratch), and the Weierstrass
(`P.Y = 0`) case's own separate argument (§3b item 3 / §14). Once those
land, the final assembly into `div(h) = D_old - D_new` and back to
`reducedClass_eq_of_isReduction'` itself (`AlphaLocusDegreeUniform.lean`)
should, per ChatGPT's own closing line in §13, become "almost entirely
`rw`/`linarith`-style valuation bookkeeping."
