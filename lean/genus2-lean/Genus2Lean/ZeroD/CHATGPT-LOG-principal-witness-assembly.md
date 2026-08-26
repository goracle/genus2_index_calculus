# ChatGPT consultation log — `PrincipalWitnessAssembly.lean` / principal-witness-assembly roadmap

Raw prompts drafted and sent during this work, kept here (not in the
`.lean` file — Lean files are for Lean, not prompt drafts). Companion to
`ROADMAP-principal-witness-assembly.md`, which has the condensed,
actionable takeaways mapped onto this project's actual names; read that
first, come back here only for the exact wording that was sent/is queued.

=====================================================================
CHATGPT PROMPT DRAFT (not part of the Lean file — paste separately)
=====================================================================

I'm formalizing genus-2 hyperelliptic curve divisor arithmetic in Lean 4 /
Mathlib. I need help designing (not necessarily writing full Lean for) a
specific bridge lemma. Context, kept minimal:

Working over a finite field `F p` (`p` prime, `p ≠ 2`). `H.Point :=
{(x,y) : F p × F p // y^2 = H.f.eval x}` is a curve point type. For a
point `P`, `ordAt P A B : ℤ` is the order of vanishing of the
coordinate-ring element `A(x) + B(x)y` at `P` (well-defined once
`pointIdeal P ≠ ⊥`, i.e. `P` isn't a component of `H.f`'s ramification
locus in a degenerate way — in practice this just needs `P` to be a
genuine point).

I have a polynomial
```
npoly4Lcm4 := monic-normalize( lcm( lcm(X - P1.x, X - P2.x), lcm(ua, u_target) ) )
```
where `P1, P2 : F p × F p` are two named affine points, and `ua`,
`u_target` are two monic quadratics (`X^2 + ua1*X + ua0` and
`X^2 + u1*X + u0`). I also have a companion quadratic `uRS4General`
(monic-normalized residual factor) with the exact factorization equation
`Npoly4 = npoly4Lcm4 * uRS4General` (up to a tracked unit), where `Npoly4`
is a degree-8 "norm" polynomial `E^2 - f*Y^2`.

I already have, fully proved and available to call:

1. **Layer 1**: for `a : F p`, `ordAt P (X - C a) 0 = 1` if `P.X = a` (and
   `P.Y ≠ 0`), else `= 0` — proved by case split.
2. **Layer 2**: if `ordAt P L 0 = 1` and `ordAt P Fᵢ 0 = 0` for `i=1,2,3`,
   then `ordAt P (((L*F₁)*F₂)*F₃) 0 = 1` (pure multiplicativity, no roots
   exposed).
3. **Layer 3**: given `P.X = a`, `P.Y ≠ 0`, and three plain
   polynomial-evaluation facts `Fᵢ.eval a ≠ 0` (i=1,2,3), concludes
   `ordAt P (((X-C a)*F₁)*F₂)*F₃) 0 = 1` — i.e. this handles ONE of the
   four linear/quadratic sub-factors being the "designated" order-1
   factor, with the other three plugged in as generic nonvanishing-at-`a`
   facts.

**The gap**: `npoly4Lcm4` is built from `EuclideanDomain.lcm`, nested
pairwise, not literally the flat product
`(X-P1.x)*(X-P2.x)*ua*u_target`. I need to bridge from "`P` is a genuine
simple root of the flat product form" to "`ordAt P npoly4Lcm4 0 = 1`" —
i.e. I need `npoly4Lcm4` and the flat product to actually be associates
(equal up to a unit) whenever the four base factors are pairwise
coprime-or-not in whatever combination actually occurs, so that Layer 3's
flat-product machinery applies to the `lcm`-built object too.

I already have on file, and can cite: `EuclideanDomain.gcd_mul_lcm`
(`gcd a b * lcm a b = a * b` up to associates), and I've used the pattern
"`IsCoprime a b` ⟹ `gcd a b` is a unit ⟹ `lcm a b` is a unit multiple of
`a*b`" successfully already for the two INNER lcms (`lcm(P1,P2)` degree 2,
`lcm(ua,u_target)` degree 4, both via this same technique, already proved
in my codebase). What I still need is the OUTER combination step: given
`lcm(P1,P2)` and `lcm(ua,u_target)` are each already known unit-multiples
of their two-factor products, AND `lcm(P1,P2)` is coprime to
`lcm(ua,u_target)` (i.e. no root shared between `{P1,P2}` and the two
quadratics' root sets), does the SAME technique
(`EuclideanDomain.gcd_mul_lcm` + `IsUnit` of the gcd) give
`npoly4Lcm4 = unit * (X-P1.x)*(X-P2.x)*ua*u_target` directly, by applying
it once more at the outer level? I believe yes but want a second opinion
on whether there's a subtlety (e.g. needing the INNER coprimality facts
again at the outer step, not just the outer coprimality) before I write
the Lean.

Additionally, I have four points/roots to classify at each of which I
need to determine, in the "split" case (both quadratics factor into two
rational roots over `F p`):
- `P = P1` (root of `X - P1.x`)
- `P = P2` (root of `X - P2.x`)
- `P` = each of `ua`'s two roots (call them `Ra1, Ra2`)
- `P` = each of `u_target`'s two roots (call them `R1, R2`)

**Question 1** (see above, restated tightly): under the hypothesis that
all 6 pairs among `{P1.x, P2.x, Ra1, Ra2, R1, R2}` (as points, i.e. as
roots of the 4 base factors, not the base factors themselves) are
pairwise distinct, is `IsCoprime (lcm(P1,P2)) (lcm(ua,u_target))` (the one
remaining outer coprimality fact, beyond the two inner ones I already
have) provable purely from "`ua`/`u_target` have no root in
`{P1.x, P2.x}` AND `ua ≠ u_target` AND `ua`,`u_target` share no root with
each other" — i.e. is the outer coprimality really just "no shared root
across the two 2-element root-sets", with no extra multiplicative
subtlety from the lcm construction itself? (I ask because `lcm` of monic
coprimes should just BE the product for square-free inputs, but want to
confirm there's no hidden double-counting when composing two lcm-of-2
steps into one lcm-of-4.)

**Question 2**: Once I have
`npoly4Lcm4 = unit * (X-P1.x)*(X-P2.x)*ua*u_target`, and separately
`ua = (X - C Ra1)*(X - C Ra2)` (from `Ra1 ≠ Ra2` and both being roots —
is there a clean named Mathlib lemma for "a monic quadratic with two
known distinct roots equals the product of its two linear factors", e.g.
via `Polynomial.roots`/`Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`
or similar, or is it cleaner to just prove
`(X-C Ra1)*(X-C Ra2) = X^2+C ua1*X+C ua0` directly by expanding and
matching coefficients via `Polynomial.ext`/`Polynomial.funext`-style
argument given `Ra1+Ra2 = -ua1` and `Ra1*Ra2 = ua0`?), is there a slicker
way to apply Layer 3 at `P = Ra1` (say) that avoids fully re-deriving and
re-associating the 4-factor flat product into
`((X-C Ra1)*F₁)*F₂)*F₃` shape for each of the 4 cases separately — e.g.
some associativity/commutativity normal form or a generalized
"N-factor, one designated" version of Layer 2/3 that takes the index of
the designated factor as a parameter, rather than 4 separately
hand-written instantiations?

I don't need full Lean code — a clear mathematical roadmap for these two
questions (ideally citing current Mathlib4 lemma names where you know
them) would let me write the Lean myself.
=====================================================================

=====================================================================
CHATGPT PROMPT DRAFT #2 (not part of the Lean file — paste separately,
once #1's reply has been incorporated)
=====================================================================

Follow-up to the previous question, same Lean 4/Mathlib project (genus-2
hyperelliptic divisor arithmetic over a finite field `F p`). I now have,
fully proved:

- `npoly4Lcm4 = C u * ((X-C P1.x)*(X-C P2.x) * (ua * u_target))` for an
  explicit unit `u` (`IsUnit (C u)`, in fact `u` is a nonzero field
  element), in the "split, no shared root" case.
- `Npoly4 = npoly4Lcm4 * uRS4General` exactly (no unit slack).
- Layer 3: given `P.X = a`, `P.Y ≠ 0`, and three polynomials `F1 F2 F3`
  each with `Fi.eval a ≠ 0`, concludes `ordAt P (((X-C a)*F1)*F2)*F3) 0 =
  1` (exact flat product, no unit).

**Question 1**: what's the cleanest Mathlib-idiomatic way to get from
`ordAt P (flat product) 0 = 1` to `ordAt P (C u * flat product) 0 = 1`
for a unit `u`? I believe scaling by an invertible constant shouldn't
change the vanishing order at any point, but I don't know whether this
project's `ordAt`/`toPair` setup has a named "ordAt is invariant under
unit scaling" lemma already, or whether it's cleanest to just unfold via
`ordAt_add_of_pairNorm_eq_mul` (`N = A*U ⟹ ordAt P N = ordAt P A + ordAt
P U`) with `U := C u` and show `ordAt P (C u) 0 = 0` directly (since `C
u` is a nonzero constant, its associated ring element should be a unit
in the coordinate ring, hence order-0 at every point) — is there a
one-line argument for `ordAt P (C u) 0 = 0` given `u ≠ 0`, or does it
need unfolding `ordAt`'s actual valuation-theoretic definition?

**Question 2** (the main assembly): I have 6 named points
(`sa.P1, sa.P2, Ra1, Ra2, R1, R2 : H.Point`) and two `Finset H.Point`s,
`Sold := Sanchor ∪ {sa.P1, sa.P2}` (`Sanchor := {Ra1, Ra2}`) and
`Snew := {R1, R2}`. I need to discharge a hypothesis of the shape
```
∀ P : H.Point,
  (if P ∈ Sold then ordAt P Aold Bold else 0) -
    (if P ∈ Snew then ordAt P Anew Bnew else 0) = 0
```
(this is `divToPair_eq_of_coeffAt_diff_eq_zero`'s literal hypothesis,
already proved and available to call, which concludes the two divisors
are equal once this vanishes everywhere). I know: at each of the 6 named
points, exactly one of `ordAt P Aold Bold`/`ordAt P Anew Bnew` is `1`
(matching my Layer-14/15 lemmas, `ordAtFrac_eq_one_of_old_point`/
`ordAtFrac_neg_eq_one_of_new_point`) and membership in `Sold`/`Snew`
matches which case it is; at every OTHER point `P`, `P ∉ Sold`, `P ∉
Snew`, both `if`s are `0`, and the equation holds trivially.

Given `H.Point` is a subtype (`{p : k × k // H.Equation p.1 p.2}`) with
`DecidableEq H.Point` available, what's the cleanest Lean pattern to
discharge a `∀ P` goal like this over a finite, explicitly-named set of
"interesting" points plus a generic "elsewhere" branch — `rcases`/`by_cases`
chained 6 times against `P = sa.P1 ∨ P = sa.P2 ∨ P = Ra1 ∨ ...`? A
`Finset.mem_insert`/`Finset.mem_union` unfolding into a big disjunction
via `simp`? Or is there a more scalable idiom for "case split on which of
finitely many named elements `P` equals, else fall through to a generic
branch" that avoids 6 nearly-identical proof blocks? I'd like the
resulting Lean to be maintainable if a future pass changes `Sold`'s
construction (e.g. if the K=4 recipe changes to K=6).
=====================================================================

=====================================================================
CHATGPT PROMPT DRAFT #3 (not part of the Lean file — paste separately;
NOT YET SENT as of this pass's end — run this before writing any more
Part-D Lean, since the degree mismatch below breaks the previously-planned
generator shape)
=====================================================================

Same Lean 4/Mathlib genus-2 hyperelliptic project, `F p` a finite field,
`p ≠ 2`, curve `y² = f(x)`, `deg f = 5`. I found a concrete arithmetic
contradiction in my own project's planning notes and need help finding the
correct fix, not just confirming the bug.

Setup: I have an interpolating function `g(x,y) = E(x) + Y(x)·y` (`E`
degree ≤4, `Y` degree ≤1 — NOT the classical K=2 picture's degree
≤3/degree-0 `E`/`Y`; this is a K=4 variant, `E`/`Y` built to satisfy 6
interpolation conditions: 2 "old" affine points, 2 more roots from an
"anchor" quadratic `u_a`, and 2 "Mumford rows" encoding a target quadratic
`u_target`'s own conditions). Let `N(x) := E(x)² - f(x)·Y(x)²` — this has
degree exactly 8 (confirmed: `deg E = 4` dominates, `2·4=8 > 2·1+5=7`).
`N` factors as `N = u_old · u_new` where `u_old` (degree 6) is the LCM of
the 4 "old" linear/quadratic factors (`(x-P1)`, `(x-P2)`, `u_a`,
`u_target` — note `u_target` itself, not just the 2 "new" residual points,
is folded into `u_old` by this recipe's construction) and `u_new` (degree
2) is the genuinely fresh residual quadratic — `u_new`'s 2 roots are the
NEW points the reduction outputs.

I want to express "`g`'s divisor equals `u_old`'s Mumford divisor minus
`u_new`'s Mumford divisor, up to a principal-divisor / linear-equivalence
correction" as an actual `Divisor H` identity provable pointwise (via
`ordAt`/`coeffAt`, which I already have working lemmas for at each
individual point). My `ordInfOfPair` function (pole order at infinity)
gives: `ordInfOfPair(E,Y) = -8` (matches `deg N = 8`, since `g`'s only
affine zeros are `N`'s 8 roots, each simple, by construction) and
`ordInfOfPair(u_new, 0) = -4` (`u_new`'s bare `x`-polynomial pole order,
`-2·deg(u_new)`).

**The problem**: my intended construction was to build a "principal
divisor subgroup" generator as `div(g) - div(u_new)` (a genuine ratio
`g/u_new` in the coordinate ring, i.e. `divToPairRatio` in my Lean, whose
degree-0 membership needs `ordInfOfPair(g) = ordInfOfPair(u_new)` on the
nose — this is my Lean's own generator condition; `principalSubgroup`'s
generators are `div(g₁)-div(g₂)` for `ordInfOfPair`-MATCHING pairs only).
But `-8 ≠ -4` — this pairing is NOT degree-0 as literally built, so it's
not a valid generator of my "divisors of coordinate-ring-element ratios"
subgroup. This directly contradicts what I'd planned (I'd assumed, from an
earlier K=2-flavored note in my own project, that this pairing was
"trivially" degree-matched — it isn't, in this K=4 variant).

**A wrinkle I noticed re-reading my own project's K=2 derivation of the
same construction** (same `h := (y-phi)/u_new` idea, smaller numbers):
there, `ord(y-phi) = -6`, `ord(u_new) = -4`, and my own note says `ord(h)
= -6-(-4) = -2` — NOT claiming `ord(h) = 0`. That `-2` is then said to
"match the `2δ₀` correction term already built into `reducedClass`'s
definition" — i.e. even in K=2, the ratio `h` itself is NOT degree-0 at
infinity; the leftover pole order is absorbed by a SEPARATE `-2•[δ₀]`
correction term that the surrounding Mumford-divisor bookkeeping already
carries elsewhere (my `D_old`/`D_new` are each independently `Divisor -
2•[δ₀]`-shaped, not `div(h)` itself). So it looks like my
`divToPairRatio`/`principalSubgroup` machinery (which demands
`ordInfOfPair` match EXACTLY, giving `div(ratio)` degree 0 outright with
no correction term allowed) may simply be the WRONG tool for this specific
witness — its own natural pole order (`-2` in K=2, `-8-(-4)=-4` in my K=4
variant) is nonzero BY DESIGN and needs absorbing via a correction, not
eliminated by picking a different pairing.

**Question 1**: is my `divToPairRatio`/`principalSubgroup` machinery the
wrong tool here precisely because it forces an exact `ordInfOfPair` match
with no room for a correction term? If so, what's the right Lean-level
fix — proving the needed `Jacobian`-level equality directly via
`eq_of_coeffAt_eq` (bypassing `principalSubgroup` membership's exact-match
requirement) applied to a suitably `δ₀`-corrected pair of divisors, or
widening `principalSubgroup`'s own generating set to allow a
named/bounded correction term (mirroring the `-2•single δ₀` idiom already
used elsewhere in this project for exactly this purpose)? I've already
ruled out "the pairing itself is wrong" as the issue: `g` (a genuine
`y`-dependent curve function, `E+Yy`) has EXACTLY 8 simple affine zeros —
one `y`-lift per root of `N(x) = E²-fY²`, not both lifts — since
`g(x,y)=0` picks out the single point where `y = -E(x)/Y(x)`, unlike a
bare `x`-polynomial. So `g`'s own pole order `-8` is correct as computed,
not a double-counting artifact, and I don't think a different choice of
comparison polynomial removes the mismatch — I think the mismatch is
supposed to be there and absorbed, exactly as in the K=2 case.

**Question 2** (only after Question 1 is resolved): once the correct
`Divisor H`-level identity (with whatever `δ₀`-correction it needs) is
pinned down precisely, what's the right `Sg`/`Su`-style `Finset H.Point`
data for each side, and is there a clean way to state the needed lemma
that reuses `eq_of_coeffAt_eq` directly (which I already have working and
proved) rather than routing through `principalSubgroup` membership at
all — given the end goal is just `toJacobian D (D_old) = toJacobian D
(D_new)` in the quotient, not membership in this specific
`AddSubgroup.closure`-built subgroup for its own sake?

I'd like a careful, from-first-principles resolution here (redo the
degree/pole-order bookkeeping explicitly, don't just pattern-match against
the classical K=2 case), since I already found one silent bug from
assuming a K=2 fact transferred unchanged to K=4 and don't want to repeat
that mistake.
=====================================================================

---

## Reply to Prompt #3 — received, RESOLVES the `ordInfOfPair` mismatch

Full reply, kept verbatim for reference. **Verdict: the `-8` vs `-4`
mismatch is real and expected, not a bug** — `g/u_new`'s principal divisor
is still degree-zero; only this project's `divToPairRatio` (which demands
equal `ordInfOfPair` on both sides, no leftover term) was the wrong tool
for this specific witness. The fix: prove the raw `Divisor H` identity
`div(g) - div(u_new) = D_old - D_new - 4•[δ₀]` directly via
`eq_of_coeffAt_eq` (already on file), bypassing `principalSubgroup`
membership for this one identity, THEN separately check how
`reducedClass`/`toJacobian` absorb the leftover `4•[δ₀]` term. Do NOT
widen `principalSubgroup`. One open sub-question flagged by the reply
itself, not yet resolved: whether `D_new`'s two points should be `R1,R2`
(the roots `u_new` selects together with `g`) or their hyperelliptic
conjugates `ι(R1),ι(R2)` — this depends on this project's actual sign
convention for `v_new`/the Mumford pair and needs checking against
`GeneralSharedRoot.lean`'s real `vRS4General` definition before the
`eq_of_coeffAt_eq` proof is written, not assumed either way.

Full text:

I'm formalizing genus-2 hyperelliptic curve divisor arithmetic in Lean 4 /
Mathlib and found what looks like an arithmetic contradiction in my own
project's planning notes. Please check whether this is a real bug or
whether I'm using the wrong tool for the job.

Setup: `g(x,y) = E(x) + Y(x)y` is an interpolating function (`deg E = 4`,
`deg Y ≤ 1`, over a finite field `F p`, curve `y² = f(x)`, `deg f = 5`).
`N(x) := E(x)² - f(x)Y(x)²` has degree 8 and factors as `N = u_old * u_new`
(`deg u_old = 6`, `deg u_new = 2`). `g`'s own pole order at infinity is
`-8` (dominant term `2·deg E`). `u_new`, used as a bare `x`-polynomial (no
`y`-dependence), has pole order `-2·deg u_new = -4`. I want to express
"`g`'s divisor relates to `u_old`'s and `u_new`'s Mumford divisors" as a
literal coordinate-ring-ratio identity, via a "`divToPairRatio`" construct
in my Lean project that only accepts pairs `(g₁,g₂)` with MATCHING pole
order at infinity (so their ratio's pole order cancels to exactly `0`).
But `-8 ≠ -4`, so this pairing doesn't qualify. Is this a real
contradiction in my construction, or am I using the wrong tool — i.e. is
`g/u_new`'s principal divisor still degree-zero as an honest rational
function, just with the pole order NOT literally cancelling between
numerator and denominator's OWN individual pole orders (since `g` and
`u_new` don't just differ by pole order at infinity — they also differ in
their AFFINE zero/pole structure, since `u_new` as a bare polynomial
vanishes at both hyperelliptic lifts of each root while `g` only vanishes
at one)? If it's the latter, what's the exact `Divisor H` identity I
should be proving instead (including the precise leftover term at
infinity, if any), and should I widen my `principalSubgroup`
construction to accept this witness, or prove the needed
`Jacobian`-quotient equality by some other, more direct route (e.g.
`eq_of_coeffAt_eq` applied to a corrected pair of divisors)?

[Full mathematical response as received — recomputes the K=4 divisor from
first principles, confirms `div(g/u_new) = D_old - D_new - 4•[δ₀]` is
correct and degree-zero as a rational function's own divisor, confirms
`divToPairRatio`'s exact-pole-order-match requirement is a narrower
condition than "principal divisor of any rational function" and is the
wrong interface for this witness, recommends NOT widening
`principalSubgroup`, recommends proving the raw identity via
`eq_of_coeffAt_eq` first and checking `reducedClass`/`toJacobian`'s
absorption of the `4•[δ₀]` term second, and flags the `R_i` vs `ι(R_i)`
orientation question as the one remaining convention-dependent unknown —
kept in full in this project's chat/session record; condensed into the
roadmap's own status-update section rather than duplicated here
verbatim a second time.]
