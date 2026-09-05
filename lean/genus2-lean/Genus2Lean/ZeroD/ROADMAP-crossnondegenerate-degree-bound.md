# Roadmap: the `CrossNondegenerate` degree bound (Obligation 3's first sub-lemma)

## Purpose

Scopes the actual next Lean work per `ROADMAP-degree-uniform-step3.md`'s
rewritten Obligation 2/3 plan: attempt the `CrossNondegenerate`/
`PeelChainNondegenerate` degree bound directly, broken into sub-lemmas.
This document does the scoping (what's actually being bounded, in which
variables, tracing through which files) before any tactic-level proof is
attempted, since the construction spans four files
(`DataDerivationTower.lean` → `DataDerivationMumford.lean` →
`DecoupledSystemRegular.lean`) and getting the target statement wrong is
more costly than getting a `by sorry` wrong. Not run against Claire's
REPL yet — this is a plan, not a proof; per project convention, Claude
scopes and drafts, Claire tests.

## What's actually being bounded — traced through the code, this pass

**`CrossNondegenerate`'s four resultant fields (`hu0/hu1/hv0/hv1`) are
polynomials purely in the 8 sample-local variables
`{wa1,wa2,a1,a2,wb1,wb2,b1,b2}` — no dependence on `U0,U1,V0,V1` (the
target variables) at all.** Confirmed by direct inspection of
`FuList`/`FvList` (`DecoupledSystemRegular.lean`): `Fu0 := d.u1_num 0 -
U0'·d.u1_den 0` is linear in `U0'` with coefficients `u1_num 0`, `u1_den
0` that involve only `{wa1,wa2,a1,a2}` (`DecoupledGenerators.u1_indep`).
The resultant `d1·c2 - d2·c1` (`CrossNondegenerate`'s docstring) is built
entirely from `u1_num/u1_den/u2_num/u2_den` — never multiplies in
`U0',U1',V0',V1'` — so it's a polynomial in the 8 sample-local variables
only. This matches Claire's point directly: `alpha`/`alpha'` (which
parametrize `sa.u0,sa.u1,sa.v0,sa.v1`/`sb.u0,...` — the SampleTarget
coefficients, not `Rdec`'s own 12 variables) don't enter this expression
as ring variables at all; they enter only through which `F p`-values get
substituted for `c0,...,c4,sa.u0,...` when `theData` is instantiated.
The degree bound target is therefore: **a `totalDegree` bound, in the 8
sample-local `Idx` variables, on each of the four `CrossNondegenerate`
resultants — uniform in `(c0,...,c4)` and in `(sa,sb)`, since those never
appear as ring variables of `Rdec p` either (they're `F p`-valued
parameters substituted into constant coefficients via `C`).**

This is consistent with, and sharpens, the "fixed, finite operations"
framing from `ROADMAP-degree-uniform-step3.md`'s rewrite: since neither
`(alpha,alpha')` nor `(c0,...,c4)` are ring variables here, a totalDegree
bound proved once, symbolically, automatically covers every instance —
there is no "sweep more instances" step even in principle for this part
of the argument. The only per-instance content that can vary is the
*nonvanishing* of the resultant (whether it's the zero polynomial, or
whether it stays `IsSMulRegular` after quotienting by `Fu0`), not its
degree, which is what makes this the right layer to attack with a
uniform structural bound.

## Where the degree bound has to come from — the recursion, traced

`u1_num i`, `u1_den i` (etc.) are `(towerToRdec p aSideGens
((uRS ...).coeff i)).1/.2` — i.e. `uRS`'s (a `Polynomial (K2 p ...)`)
`i`-th coefficient (a `K2`-element), pushed through `towerToRdec`'s
three-level recursion down to `Rdec p = MvPolynomial Idx (F p)`:

```
K2  --coeff i-->  K2-element
        |  towerToRdec (AdjoinRoot.modByMonicHom against K2's monic quadratic,
        |               extract .coeff 0/1 : K1, recurse)
        v
K1 × K1  --towerToRdecK1 each-->  (num,den) pairs in MvPolynomial Vars (F p)
        |  (AdjoinRoot.modByMonicHom against K1's monic quadratic,
        |   extract .coeff 0/1 : K0, recurse)
        v
K0 × K0  --baseFracToRing each-->  (num,den) pairs in MvPolynomial Vars (F p)
        |  (IsFractionRing.num/.den, then MvPolynomial.aeval substituting
        |   sg.tGen's images)
        v
base case: K0 = FractionRing (MvPolynomial (Fin 2) (F p))
```

Each level combines its two children `(n0,d0),(n1,d1)` via `num :=
n0*d1 + n1*d0*X(wGen _)`, `den := d0*d1` — **exactly two multiplications
and one addition per level, three levels total**. This is the "fixed,
finite sequence of algebraic operations" Claire is pointing at: given a
totalDegree bound `D` on `(n0,d0,n1,d1)` at one level, the next level's
`(num,den)` satisfy `totalDegree num ≤ 2D + 1`, `totalDegree den ≤ 2D`
(the `+1` from the extra `X(wGen _)` factor) — completely mechanical,
`Polynomial.natDegree_mul_le`/`add_le`-style triangle inequalities, the
same style already used for `Npoly_natDegree_le_six` in
`DecoupledSystemRegular.lean`, just one abstraction level up (`MvPolynomial.totalDegree`
in place of `Polynomial.natDegree`, using `MvPolynomial.totalDegree_mul_le`/
`totalDegree_add_le` in place of `Polynomial.natDegree_mul_le`/`natDegree_add_le` — both exist in Mathlib in the expected shape). Iterating three times from a base-case bound `D0` gives an explicit closed-form bound (not just "some bound exists") — see "Concrete numbers" below.

## The one genuine wrinkle — flagged precisely, not glossed over

**The base case's `num`/`den` are `IsFractionRing.num`/`.den` on a `K0`
element, not a hand-picked representative** (`baseFracToRing`,
`DataDerivationMumford.lean`). `IsFractionRing.num`/`.den`
(`Mathlib.RingTheory.Localization.NumDen`) return a **reduced** fraction
(`IsRelPrime`, per `IsFractionRing.num_den_reduced`/
`exists_reduced_fraction`) via `UniqueFactorizationMonoid` — this is a
choice function, not a syntactic readout of however the `K0`-element was
built, so there is no Mathlib lemma directly saying "if `v = a/b` for
some concrete `(a,b)`, then `totalDegree (IsFractionRing.num v) ≤
totalDegree a`." **This has to be proved as its own small lemma**, not
assumed. The proof route (standard, not a new mathematical difficulty,
just an un-derived Mathlib gap): from `IsFractionRing.mk'_num_den'`
(`(num v) * b = a * (den v)` when `v = a/b`) plus `MvPolynomial
(Fin 2) (F p)` being a UFD/`IsDomain`, `num v` divides `a * (den v)`;
since `IsRelPrime (num v) (den v)` (reducedness), `num v` divides `a`
outright (Euclid's lemma / `IsRelPrime.dvd_of_dvd_mul_right`-style), and
a nonzero divisor in `MvPolynomial (Fin 2) (F p)` has `totalDegree ≤`
the dividend's (needs its own small lemma — not found by name in
Mathlib's `MvPolynomial.Division`/`Basic` API on the pass checked this
session; likely provable via `MvPolynomial.totalDegree_mul` on the
witness `a = num v * k` for the nonzero cofactor `k`, using
`totalDegree_mul_le`'s reverse-direction sibling if one exists, or
directly from `eq_C_of_...`-style leading-term reasoning if not — worth
a Zulip/Mathlib-docs check before assuming it needs to be hand-rolled).
**This is the one place this sub-lemma needs new (but standard, UFD-
level, not curve-geometry) lemma infrastructure**, and it's exactly
where a ChatGPT consultation is worth using if the Mathlib search above
doesn't turn up the exact divisibility-degree lemma quickly — per
project convention, ask rather than block on it.

This wrinkle does NOT change the overall assessment that this is a
tractable, mechanical degree bound — it's a one-time UFD lemma needed
once at the base case, not a source of open mathematical uncertainty
about whether the bound holds.

## Concrete numbers, base case forward (draft, to be checked against real Mathlib names before use)

- **Base case** (`baseFracToRing`, from a `fAtT p c0 c1 c2 c3 c4 i : K0
  p` value, or more generally any `K0`-element built from field
  arithmetic on finitely many `fAtT`-images): `fAtT := curvePoly.eval₂
  (algebraMap ...) (t0 p i)`, and `curvePoly` has `natDegree = 5`
  (`curvePoly_natDegree`, already proved, `DataDerivationBasics.lean`);
  `t0 p i = X i` in `MvPolynomial (Fin 2) (F p)`, `totalDegree 1`. So the
  "obvious" numerator for `fAtT p ... i` (before any `IsFractionRing`
  reduction) is a `totalDegree ≤ 5` polynomial in `MvPolynomial (Fin 2)
  (F p)` with `den = 1`. Via the wrinkle above, `IsFractionRing.num
  (fAtT p ... i)` then also has `totalDegree ≤ 5` (dividing a `≤5`-degree
  numerator), `den` similarly bounded. **Concretely track what `K0`-
  elements actually reach `baseFracToRing`** (not just `fAtT` itself, but
  whatever `EuclideanDomain.gcdA`/field-arithmetic combinations of
  `fAtT`-images `uRS`/`vRS`'s construction produces feeding into `K1`'s
  coefficients) before fixing this base-case number — `uRS`/`vRS`
  themselves are built over `Polynomial (K2 p ...)`, one level up, not
  directly over `K0`, so this base case is reached only via `towerToRdec`'s
  own `.coeff 0/1` extraction at each level, and the actual `K0`-values
  that show up are whatever `K1_poly_monic`'s `AdjoinRoot.modByMonicHom`
  extraction produces — **not yet traced to a concrete degree bound this
  pass**; flagged as the next scoping step rather than guessed.
- **Level 1** (`towerToRdecK1`): given base-case bound `D0`, `num ≤
  2*D0+1`, `den ≤ 2*D0`.
- **Level 2** (`towerToRdec`): given level-1 bound `D1`, `num ≤ 2*D1+1`,
  `den ≤ 2*D1`.
- These are `u1_num i`/`u1_den i` etc. directly (`theData`'s assembly is
  exactly `towerToRdec`'s output, `coeffsToNumDen`).
- **The resultant** `d1*c2 - d2*c1`: `totalDegree ≤ 2*(num-or-den bound
  at level 2)`, one more `MvPolynomial.totalDegree_mul_le`/`add_le` step.

**None of this is claimed final** — the base case's actual value needs
the tracing flagged above, and every Mathlib lemma name here needs
confirming against the real API (some, like `curvePoly_natDegree` and
`Npoly_natDegree_le_six`'s proof style, are already confirmed present
and working in this codebase; `MvPolynomial.totalDegree_mul_le`/
`totalDegree_add_le` are standard and almost certainly present but not
yet grep-confirmed against this specific Mathlib snapshot this pass).

## Proposed next steps, in order

1. **Confirm `MvPolynomial.totalDegree_mul_le`/`totalDegree_add_le`
   exist with those names** (or find the actual names) — five-minute
   Mathlib-docs check, not attempted this pass since no build
   environment is available in this session.
2. **Trace exactly which `K0`-elements reach `baseFracToRing`** — pin
   down the base case's real value (not just `fAtT` alone) by reading
   `K1_poly_monic`/`AdjoinRoot.modByMonicHom`'s coefficient-extraction
   in `towerToRdecK1` concretely, one level at a time from `uRS`/`vRS`'s
   own definitions.
3. **Prove the UFD "divisor's totalDegree ≤ dividend's" lemma** flagged
   above as its own small, reusable lemma — check Mathlib for it by name
   first; if genuinely absent, this is a good candidate for a ChatGPT
   consultation (small, well-defined algebra fact, not curve-specific).
4. **State and prove the three-level totalDegree bound** on
   `u1_num/u1_den/u2_num/u2_den` (and the `v`-side siblings) as an
   explicit theorem in `DecoupledSystemRegular.lean` or a new file,
   `_flat` first (one theorem per level, not bundled), matching this
   project's existing discipline.
5. **Derive `CrossNondegenerate`'s resultant degree bound** as a direct
   corollary (one more `totalDegree_mul_le`/`add_le` step per resultant).
6. **Only after 1-5**: use the resulting explicit bound to identify what
   the resultant's actual *vanishing* condition looks like (the
   "failure mode" question from `ROADMAP-degree-uniform-step3.md`'s
   Obligation 2) — a bounded-degree nonzero polynomial vanishing
   identically forces its coefficients (in `c0,...,c4,sa,sb`) to satisfy
   a specific, checkable algebraic relation, which is the kind of named,
   narrow hypothesis this layer actually needs (replacing
   `CrossNondegenerate`'s current opaque `IsSMulRegular` framing).

## What this document deliberately does NOT do

- Does not write tactic-level Lean — no build environment available this
  session, and per project convention Claire runs all tests. This is
  scoping only.
- Does not claim the base-case number is final (step 2 above is
  unstarted).
- Does not revisit whether numerical sweeping is needed — settled by
  `ROADMAP-degree-uniform-step3.md`'s rewrite: it isn't, for this part
  of the argument, since neither `(alpha,alpha')` nor `(c0,...,c4)` are
  ring variables in the object being bounded.

## Update — step 2 traced one layer further, still open

`DataDerivationTotalDegree.lean` now has steps 1/3/4 (of "Proposed next
steps" above) done and REPL-confirmed: `MvPolynomial.totalDegree_mul`/
`totalDegree_C`/`totalDegree_X_pow`/`totalDegree_finsetSum_le` all
confirmed present (step 1); `towerToRdecK1_totalDegree_le`/
`towerToRdec_totalDegree_le`/`towerToRdec_coeff_totalDegree_le` state and
prove the three-level bound generically, given ANY base-case bound `D`
on `baseFracToRing`'s output (step 4, done as a hypothesis-parametrized
theorem rather than blocked on step 2's concrete number — the generic
form is proved and green regardless of what `D` turns out to be
concretely). `fAtT_eq_mk'_one`/`curvePoly_eval_C_totalDegree_le` handle
the SIMPLEST possible base case (`fAtT` itself, `totalDegree ≤ 5`) but
that is not yet what actually reaches `baseFracToRing` from `uRS`/`vRS`
— see below.

**Traced this pass**: `uRS.coeff j`/`vRS.coeff j` (the actual `K2`-
elements `towerToRdec` is applied to, per `coeffsToNumDen`) are NOT
simple `fAtT`-images. The chain, concretely:

```
uRS := C curBeforeMonic.leadingCoeff⁻¹ * curBeforeMonic      (DataDerivationMumford.lean)
curBeforeMonic := ((Npoly /ₘ (X - C anchor1.1)) /ₘ (X - C anchor2.1)) /ₘ U
  where U := X^2 + C(g u1) X + C(g u0)                        (DataDerivationSolve.lean)
Npoly := Epoly^2 - fAtX * Ypoly^2
```

Every piece here (`Epoly`, `Ypoly`, `fAtX`, `anchor1`, `anchor2`) is
itself a `K2`-valued (or `K2 × K2`-valued) object built from the LINEAR
SYSTEM's solution (§4.2 items 3–5, `DataDerivationSolve.lean`) — i.e.
`w1`/`w2` (the tower's own adjoined roots, not `fAtT`-images at all) and
field-arithmetic combinations of them with `(u0,u1,v0,v1)`-parametrized
coefficients. **`w1`/`w2` are `AdjoinRoot.root` of their respective
minimal polynomials** (`DataDerivationTower.lean`) — their OWN
`towerToRdecK1`/`towerToRdec` image is comparatively simple to bound
directly (a root's `modByMonicHom` normal form is the trivial `X`
itself, i.e. `d0 = 0, d1 = 1` in the `{1,X}` basis — needs checking
against `AdjoinRoot.modByMonicHom_mk`/`AdjoinRoot.root`'s actual
definition, not yet done this pass), but `curBeforeMonic`'s THREE nested
`/ₘ` (polynomial division, not multiplication) steps are the genuine new
difficulty: **Mathlib has no general `totalDegree`-style bound for
`Polynomial.divByMonic`'s coefficients in terms of the dividend's
`MvPolynomial`-coefficient degrees** (division is not a "fixed, finite
sequence of ring operations" in the same sense multiplication/addition
are — a `/ₘ` quotient's coefficients are, in general, complicated
rational functions of the dividend's and divisor's coefficients, even
though here the RESULT is guaranteed polynomial by the `dvd_N_*`
hypotheses). This is a materially different, and likely harder, wrinkle
than the "one UFD lemma" flagged in "The one genuine wrinkle" above
(which is about `IsFractionRing.num/.den`, a DIFFERENT step — the base
case's `K0 → Rdec` step, not this `K2`-level division step upstream of
it).

**Not yet resolved — options, not yet chosen between**:
1. Bound `curBeforeMonic`'s coefficients directly via `Polynomial.
   divByMonic`'s recursive/`natDegree`-recursion definition (Mathlib's
   `divModByMonicAux`) — likely requires induction on `natDegree`, real
   new Lean work, not a quick lemma lookup.
2. Sidestep `/ₘ` entirely: since `dvd_N_anchor1`/`dvd_N_anchor2`/
   `dvd_N_u` (once proved — currently `sorry` upstream, per
   `DataDerivationMumford.lean`'s own header) assert EXACT divisibility,
   `curBeforeMonic * (divisor product) = Npoly` holds as an equation,
   which might let a `totalDegree` bound be derived from `Npoly`'s
   bound via a DIVISOR-side argument (bound `curBeforeMonic` by degree
   subtraction: `natDegree` arithmetic is exact for exact division, and
   `totalDegree` might follow a parallel argument) rather than needing
   division's coefficient formula directly. Not checked whether Mathlib
   has the right lemma for this (something like: exact quotient's
   coefficients are polynomial combinations of dividend/divisor
   coefficients via Cramer's-rule-style resultant formulas — bounded,
   but needs the actual lemma name).
3. Ask ChatGPT for the general "totalDegree of an exact polynomial
   quotient, in terms of totalDegree of dividend and divisor's
   coefficients" fact, if option 2's Mathlib search comes up empty —
   this is exactly the kind of well-defined, non-curve-specific algebra
   fact the project's own convention flags as fair game to consult on.

This is now the concrete blocker for step 2 (not "unstarted" as before,
but not resolved) — `DataDerivationMumford.lean`'s upstream `sorry`s
(`dvd_N_u`, coprimality) also sit in the same file as `curBeforeMonic`
and would need discharging before `uRS`'s divisibility identity is even
available to exploit under option 2 above, so this and that file's own
open work are coupled, not independent.

## Update — option 2 attempted, generic half landed, concrete half blocked

**Landed, REPL-pending**: `eq_mul_divByMonic_of_dvd` (`DataDerivationSolve.
lean`, end of the `ExactDivision` section) — the fully general lemma
option 2 needs: for `g` monic and `g ∣ f`, `f = g * (f /ₘ g)`. Proved
cleanly via `Polynomial.dvd_iff_modByMonic_eq_zero` + `Polynomial.
modByMonic_eq_sub_mul_div` + `sub_eq_zero`, `CommRing R` generic (not
`K2`-specific), so it's the right tool regardless of how the rest of this
plays out. Not yet run against Claire's REPL.

**Blocked, not forced into a `sorry`**: applying this three times to
unwind `curBeforeMonic`'s actual `/ₘ` chain into `Npoly = curBeforeMonic *
((X-t1)(X-t2)*U)` needs propagating `dvd_N_anchor2`'s fact (`(X - C t2) ∣
Npoly`) down to the INTERMEDIATE quotient `Npoly /ₘ (X - C t1)`, which
needs `(X - C t1)`/`(X - C t2)` coprime — for two linear factors, that's
exactly `t1 ≠ t2`. **This is not established anywhere in the codebase.**
`MatrixNondegenerate` is only `A.det ≠ 0`; nothing here derives `t1 ≠ t2`
from it. Attempted this pass, hit the gap, and stopped rather than
papering over it with `sorry` — the abandoned attempt (routing through
`Polynomial.monic_X_sub_C _ |>.coprime_of_ne`, which needs exactly this
fact) is documented in a `/-! -/` note in `DataDerivationSolve.lean`
right after `eq_mul_divByMonic_of_dvd`, not left as dead code in the
file.

**New, smaller concrete next step, sharper than before**: prove `t1 ≠
t2` — i.e. `(anchor1 p ...).1 ≠ (anchor2 p ...).1` — from
`MatrixNondegenerate`, presumably via a Vandermonde-style argument (`t1 =
t2` would make two of `matrixA`'s rows proportional, forcing `det = 0`).
This is now the single sharpest blocker on option 2's path, upstream of
both the `curBeforeMonic`-unwinding step above AND (per `vRS`'s own
docstring) `vRS`'s coprimality hypothesis — so resolving it likely
unblocks more than just this one lemma. Once available, finishing
`Npoly_eq_curBeforeMonic_mul` should be direct: `eq_mul_divByMonic_of_dvd`
three times, `IsCoprime.dvd_of_dvd_mul_left`/`_right` to propagate each
`dvd_N_*` fact through the prior layers' quotients (using `t1 ≠ t2` for
the anchor pair, and a not-yet-checked `(X-t_i)`-vs-`U` coprimality
argument for the third layer, likely from `U`'s roots being genuinely
different target-side values, itself needing its own sourcing check).

Still fully unresolved, independent of the above: bounding `Npoly`'s own
`totalDegree` (traces to `cramerSolution`'s Cramer's-rule structure — see
"Concrete numbers" above, `w1`/`w2` are `AdjoinRoot.root`s not
`fAtT`-images, `Epoly`/`Ypoly`'s coefficients are `cramerSolution`
outputs). Not attempted this pass.
