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
   `dvd_N_u` (`sorry` upstream as of this pass — since proved, see
   `DataDerivationSolve.lean`) assert EXACT divisibility,
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
(`dvd_N_u`, coprimality), as of this pass, also sit in the same file as
`curBeforeMonic` and would need discharging before `uRS`'s divisibility
identity is even available to exploit under option 2 above, so this and
that file's own open work were coupled, not independent. **Since
resolved**: `dvd_N_u` and the relevant coprimality facts are now proved
(see `DataDerivationSolve.lean`/`DataDerivationMumford.lean`, both
`sorry`-free), so this particular coupling is no longer a blocker — the
`t1 ≠ t2` gap identified below is the remaining concrete issue.

## Update — option 2 attempted, generic half landed, concrete half blocked

**Landed, REPL-pending**: `eq_mul_divByMonic_of_dvd` (`DataDerivationSolve.
lean`, end of the `ExactDivision` section) — the fully general lemma
option 2 needs: for `g` monic and `g ∣ f`, `f = g * (f /ₘ g)`. Proved
cleanly via `Polynomial.dvd_iff_modByMonic_eq_zero` + `Polynomial.
modByMonic_eq_sub_mul_div` + `sub_eq_zero`, `CommRing R` generic (not
`K2`-specific), so it's the right tool regardless of how the rest of this
plays out. Not yet run against Claire's REPL.

**Blocked, not forced into a `sorry`, as of this pass** — since resolved,
see the update below: applying this three times to unwind
`curBeforeMonic`'s actual `/ₘ` chain into `Npoly = curBeforeMonic *
((X-t1)(X-t2)*U)` needs propagating `dvd_N_anchor2`'s fact (`(X - C t2) ∣
Npoly`) down to the INTERMEDIATE quotient `Npoly /ₘ (X - C t1)`, which
needs `(X - C t1)`/`(X - C t2)` coprime — for two linear factors, that's
exactly `t1 ≠ t2`. **This was not established anywhere in the codebase
as of this pass.** `MatrixNondegenerate` is only `A.det ≠ 0`; nothing
here derives `t1 ≠ t2` from it. Attempted this pass, hit the gap, and
stopped rather than papering over it with `sorry` — the abandoned
attempt (routing through `Polynomial.monic_X_sub_C _ |>.coprime_of_ne`,
which needs exactly this fact) is documented in a `/-! -/` note in
`DataDerivationSolve.lean` right after `eq_mul_divByMonic_of_dvd`, not
left as dead code in the file. **Resolved, later pass**:
`anchor1_ne_anchor2` (`DataDerivationSolve.lean`) proves `t1 ≠ t2`
unconditionally — no `MatrixNondegenerate` needed at all, since `t1`/`t2`
turn out to be the two free `MvPolynomial` generators pushed through
injective ring maps, not solution-dependent quantities. See that
theorem's own docstring for the full argument.

**Superseded by the resolution above, and fully closed since**: this
section originally proposed proving `t1 ≠ t2` from `MatrixNondegenerate`
via a Vandermonde-style argument, as the sharpest remaining blocker on
option 2's path (upstream of both the `curBeforeMonic`-unwinding step
AND, per `vRS`'s own docstring, `vRS`'s coprimality hypothesis).
`anchor1_ne_anchor2` closes this unconditionally instead, by a simpler
route (the two anchors are free generators, not solution-dependent), so
no `MatrixNondegenerate`-based argument is needed. The remaining pieces
flagged here as open — the third-layer `(X-t_i)`-vs-`U` coprimality
argument (`anchor1_coprime_U`/`anchor2_coprime_U`) and the assembly
itself — are also done: `Npoly_eq_curBeforeMonic_mul`
(`DataDerivationSolve.lean`) is a complete, `sorry`-free term proof
exactly along the lines sketched here (`eq_mul_divByMonic_of_dvd` three
times, `IsCoprime.dvd_of_dvd_mul_left`/`_right` to propagate `dvd_N_*`
through each intermediate quotient, closed by a `calc` block). This
whole `curBeforeMonic`-unwinding obligation is closed; nothing in this
section is still open.

Still fully unresolved, independent of the above: bounding `Npoly`'s own
`totalDegree` (traces to `cramerSolution`'s Cramer's-rule structure — see
"Concrete numbers" above, `w1`/`w2` are `AdjoinRoot.root`s not
`fAtT`-images, `Epoly`/`Ypoly`'s coefficients are `cramerSolution`
outputs). Not attempted this pass.

## Update, later pass — the `matrixA`/`rhsVec` → `coeffsOut` bridge, scoped

**Status check confirms both prerequisites now closed and REPL-green**:
`matrixA_entry_totalDegree_le` (`MatrixEntryTotalDegree.lean`) and
`rhsVec_entry_totalDegree_le` (`RhsVecTotalDegree.lean`) both give, for
every entry, an `IsRdecWitness p ι evalNd (entry) nd` pair with
`nd.1.totalDegree ≤ 24`/`≤7`, `nd.2.totalDegree ≤ 20`/`≤6` respectively
(`ι`/`evalNd` the same ambient field embedding `K2 → FractionRing
(MvPolynomial Vars (F p))` throughout). `cramerRatioDet_num_totalDegree_le`
(`DataDerivationTotalDegree.lean`) is also proved, but is stated for
matrices ALREADY given as literal `a i j / b i j` fractions of
`MvPolynomial Vars (F p)` elements — not for `K2`-valued matrices related
to such fractions only via `IsRdecWitness`'s cross-multiplied equation.
**This is the actual remaining gap** (the "correction note" flagged, but
never resolved, earlier in `DataDerivationTotalDegree.lean` — see that
file's own "The actual `K2`-valued case" section): a bridging theorem
connecting `IsRdecWitness`-per-entry to `IsRdecWitness` (or an
`IsFractionRing.num`/`.den`-shaped bound) on the matrix's `Matrix.cramer`/
`.det`, i.e. on `cramerSolution`/`coeffsOut` themselves.

**The bridge, traced concretely**:
1. `IsRdecWitness p ι evalNd (M i j) (a i j, b i j)` unfolds to `evalNd
   (a i j) = evalNd (b i j) * ι (M i j)` — i.e. `ι (M i j) = evalNd (a i j)
   / evalNd (b i j)` whenever `evalNd (b i j) ≠ 0` (`ι`/`evalNd` land in a
   FIELD, `FractionRing (MvPolynomial Vars (F p))`, so division is always
   defined, just not always the honest inverse when the denominator
   vanishes — matching `cramerSolution`'s own `MatrixNondegenerate`-
   conditional well-definedness).
2. `ι` is a ring hom, so `ι (M.det) = (M.map ι).det` (`RingHom.map_det`,
   confirmed present in Mathlib — exact name to re-confirm against this
   project's snapshot once sent to Claire's REPL, `Mathlib.LinearAlgebra.
   Matrix.Determinant.Basic`-adjacent) — this converts `ι`'s action on the
   `K2`-valued determinant into a determinant of `L`-valued (`L :=
   FractionRing (MvPolynomial Vars (F p))`) entries, each entry now a
   literal `evalNd (a i j) / evalNd (b i j)` fraction by step 1 — EXACTLY
   `cramerRatioDet_num_totalDegree_le`'s hypothesis shape, with `evalNd
   (a i j)`/`evalNd (b i j)` playing the role of that theorem's own `a i
   j`/`b i j` (both already `MvPolynomial`-valued there; here they arrive
   as `evalNd` applied to `MvPolynomial`-valued witnesses, so no type
   mismatch — `evalNd (a i j)` IS an `MvPolynomial Vars (F p)`-indexed
   value only after `evalNd`'s codomain is unfolded... **correction,
   catch this before writing**: `evalNd : MvPolynomial Vars (F p) →+* L`,
   so `evalNd (a i j) : L`, NOT `MvPolynomial Vars (F p)` — `cramerRatioDet_
   num_totalDegree_le`'s own `a`/`b` are `MvPolynomial`-valued, feeding
   INTO `L` only via the `v := IsLocalization.mk' ... a ⟨b,...⟩` hypothesis,
   not via a further homomorphism. **So the right substitution is `a i j`/
   `b i j` themselves (the WITNESS pair, `MvPolynomial`-valued, already
   totalDegree-bounded) directly as that theorem's `a`/`b`**, with `v :=
   ι (M.cramer rhs col) / ι (M.det)` (or the appropriate cramer-ratio
   entry) — NOT `evalNd (a i j)` — and the hypothesis `hv` needs `ι (M.det)
   ⁻¹`-shaped reasoning to connect `Matrix.cramer`'s OWN determinant
   identity (`Matrix.cramer_apply`/`Matrix.det_smul_...`-style) to the
   `a i j * ∏ b i' j` numerator/`∏ b i j` denominator shape
   `cramerRatioDet_num_totalDegree_le` expects — this is genuinely the
   crux of the bridge, not a relabeling, and needs its own small lemma
   (see step 3).
3. **The crux, stated precisely**: given `IsRdecWitness p ι evalNd (M i j)
   (a i j, b i j)` for every `(i,j)`, PLUS `∀ i j, evalNd (b i j) ≠ 0`
   (so `ι (M i j) = evalNd (a i j) / evalNd (b i j)` honestly, not just
   via the zero-denominator convention), show `ι (M.det) = evalNd
   (Matrix.det (Matrix.of fun i j => a i j / b i j))` — i.e. `ι ∘ M.det =
   (M.map (fun x => ...))`... **the cleanest route**: define `A : Matrix n
   n L := Matrix.of fun i j => evalNd (a i j) / evalNd (b i j)`, show `A =
   M.map ι` entrywise (from `IsRdecWitness`'s equation, `evalNd (b i j) ≠
   0` needed to divide), then `ι (M.det) = (M.map ι).det = A.det` via
   `RingHom.map_det`, and `A.det`'s own `IsFractionRing.num`/`.den` bound
   comes from `cramerRatioDet_num_totalDegree_le` applied at `a := (fun i
   j => a i j)`, `b := (fun i j => b i j)` (now genuinely `MvPolynomial`-
   valued as that theorem wants), PROVIDED `A.det`'s value is expressed
   as that theorem's specific `v := IsLocalization.mk' ... (Matrix.det
   (Matrix.of fun i j => a i j * ∏ ...)) ⟨∏∏ b i j, ...⟩` — which is
   `cramerDenom_det_eq`'s own `Δ_A * A.det = C.det` identity, ALREADY
   PROVED, generic over any field `K` (here `K := L`), applied with `a i j
   := evalNd (a i j)`, `b i j := evalNd (b i j)` (i.e. `cramerDenom_det_eq`
   takes FIELD-valued `a`/`b`, so it's `evalNd (a i j)`/`evalNd (b i j)`
   feeding IT, while the totalDegree bound is tracked on the
   `MvPolynomial`-valued `a i j`/`b i j` themselves via
   `cramerRatioDet_num_totalDegree_le`'s separate, `MvPolynomial`-level
   argument list) — so the full chain is `cramerDenom_det_eq` (instantiate
   at `evalNd ∘ a`, `evalNd ∘ b`) to get the `L`-valued identity, combined
   with `cramerRatioDet_num_totalDegree_le` (instantiate at the
   `MvPolynomial`-valued `a`, `b` directly) to get the `totalDegree` bound
   on the RESULT's `IsFractionRing.num`, and these two instantiations
   share the same `a`/`b` names but operate one level apart (`evalNd ∘ a`
   is what `cramerDenom_det_eq` sees; `a` itself is what `cramerRatioDet_
   num_totalDegree_le` bounds) — matching cleanly PROVIDED `v`'s defining
   equation (`hv` in `cramerRatioDet_num_totalDegree_le`'s signature) is
   proved to hold for `v := ι (M.det)` specifically, which is exactly
   `cramerDenom_det_eq` composed with `RingHom.map_det`/`IsLocalization.
   mk'`'s own characterization of division in a field via `mk'`. **This
   composition (not either piece alone) is the new lemma to write** —
   tentatively `IsRdecWitness_det` or `matrixDet_isRdecWitness_of_entries`
   — taking the same `∀ i j, IsRdecWitness ... (M i j) (a i j, b i j)`
   hypothesis this section opened with, `∀ i j, evalNd (b i j) ≠ 0`, and
   producing `IsRdecWitness p ι evalNd (M.det) (C.det, ∏ i j, b i j)`
   directly (`C := Matrix.of fun i j => a i j * ∏ i' ≠ i, b i' j`, exactly
   `cramerDenom_det_eq`'s own `C`) — an `IsRdecWitness` CONCLUSION rather
   than an `IsFractionRing.num`/`.den` one, so it composes with
   `IsRdecWitness`'s OWN downstream degree-bound story
   (`towerToRdec_isRdecWitness`'s sibling, not a detour through
   `IsFractionRing` at all) — cleaner than routing through
   `cramerRatioDet_num_totalDegree_le`'s `IsFractionRing.num`-specific
   statement, since `IsRdecWitness (M.det) (C.det, Δ)` plus `C.det`'s own
   `totalDegree ≤ n²D` (`cramerNumeratorDet_totalDegree_le`, already
   proved) and `Δ`'s own `totalDegree ≤ n²D` (`cramerDeltaA_totalDegree_le`,
   already proved) gives the SAME final bound with no `IsFractionRing`
   machinery needed downstream at all — **this is the corrected plan,
   superseding this file's earlier `cramerRatioDet_num_totalDegree_le`-
   centric framing**: bound the WITNESS PAIR `(C.det, Δ)` directly via
   `IsRdecWitness`, not `A.det`'s `IsFractionRing.num`.
4. **`Matrix.cramer`'s own entries** need the same treatment as `Matrix.
   det`'s — `Matrix.cramer A b i = (A.updateColumn i b).det`
   (`Matrix.cramer_apply`), so `matrixDet_isRdecWitness_of_entries`
   applied to `A.updateColumn i rhsVec` (whose entries are `A`'s own
   `IsRdecWitness` witnesses in every column except `i`, `rhsVec`'s in
   column `i`) gives `cramerSolution i`'s numerator/denominator witness
   directly, by the SAME lemma, no separate cramer-specific version
   needed.

**Next step**: write `matrixDet_isRdecWitness_of_entries` (step 3's crux)
as its own theorem in a new file (`CramerWitnessAssembly.lean`, per this
project's 1500-line-per-file / one-lemma-at-a-time discipline), building
on `cramerDenom_det_eq`, `cramerNumeratorDet_totalDegree_le`,
`cramerDeltaA_totalDegree_le` (all `DataDerivationTotalDegree.lean`,
already proved) plus `RingHom.map_det` (Mathlib, name to confirm against
this snapshot). Then instantiate it twice — once for `matrixA.det`
directly, once for `matrixA.updateColumn i rhsVec).det` (`= Matrix.cramer
matrixA rhsVec i` via `Matrix.cramer_apply`) — to get `IsRdecWitness`
witnesses (with explicit `totalDegree` bounds) for both `cramerSolution`'s
numerator-side and denominator-side pieces. `coeffsOut`'s own bound
follows immediately at the `otherIdx` slots (`cramerSolution` directly)
and trivially at `yIdx` (`coeffsOut yIdx = 1`, `totalDegree` bound `(0,1)`
via `IsRdecWitness`'s own reflexivity-style base case, not yet named as
a lemma but a one-line `map_one`/`mul_one` fact). **Not yet written as
Lean** — this section is scoping only, per this project's convention of
scoping multi-file bridging work before writing tactic-level proofs.

**Closed, REPL-confirmed green (Claire's build)**: `CrossNondegenerateDegreeBound.lean`
(new file, roadmap step 5) states and proves `crossResultant_totalDegree_le`
(u-side, `hu0`/`hu1`'s shape) and `crossResultantV_totalDegree_le` (v-side,
`hv0`/`hv1`'s shape) — each of `CrossNondegenerate`'s four resultants
(`d₁*c₂ - d₂*c₁`) has `totalDegree ≤ 4*D + 2`, given a common base-case bound
`D` on `uRS`/`vRS`'s relevant `towerToRdecK1`-level coefficient data (both
samples, both sides). Both theorems build with no changes needed from the
drafted version — the two risks flagged when they were written (argument
order into `towerToRdec_coeff_totalDegree_le`; whether the `rfl` unfolds
through `coeffsToNumDen`'s `def`) were non-issues in practice.

**What this does NOT close — the actual remaining gap, unchanged from the
"still fully unresolved" note directly above**: both theorems are
conditional on `D` as a hypothesis, not a concrete number. Making `D`
concrete requires bounding `uRS.coeff i`/`vRS.coeff i` themselves, which
traces through `curBeforeMonic`'s three nested `/ₘ` (`Polynomial.divByMonic`)
steps — Mathlib has no general `totalDegree`-transfer lemma for exact
polynomial division's coefficients (see "The one genuine wrinkle" above,
which is a *different*, already-closed gap about `IsFractionRing.num`/`.den`
at the base case, not this one). **This is now the single next step for
Obligation 3** (`ROADMAP-degree-uniform-step3.md`'s framing) — nothing about
`crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le`'s proofs
needs to change once it's closed; `D` just becomes a number instead of a
hypothesis. Candidate routes, per that file's own earlier options list
(unstarted): (1) direct induction on `Polynomial.divByMonic`'s recursive
definition, (2) the exact-quotient-via-multiplication route (`Npoly =
curBeforeMonic * (divisor product)`, already available as an equation via
`Npoly_eq_curBeforeMonic_mul` per that file's own resolved history — bound
`curBeforeMonic` from `Npoly`'s degree and the divisors' degrees, if Mathlib
has the right lemma, or (3) ask ChatGPT for the general "totalDegree of an
exact polynomial quotient" fact if (1)/(2) don't turn up a usable lemma
quickly — this is exactly the well-defined, non-curve-specific algebra fact
this project's convention flags as fair game to consult on.

## Update, latest pass: route (2) was taken and closed `curBeforeMonic.coeff{0,1,2}`'s bound — but exposed a DEEPER, still-open mismatch

`CurBeforeMonicCoeffTotalDegree.lean` (route 2 above) closed the
`curBeforeMonic.coeff{0,1,2} ≤ 315448` bound, and `URSCoeffIsRdecWitness.lean`
bridged that to `uRS.coeff i ≤ 630896` via the `leadingCoeff⁻¹` swap trick —
both REPL-confirmed green. **But both are stated as an `IsRdecWitness`
EXISTENTIAL** (`∃ nd, IsRdecWitness p ι evalNd x nd ∧ nd.1/.2.totalDegree ≤
bound`), proved by composing `IsRdecWitness.add`/`.mul`/`.neg`/`.div`
combinators over `curBeforeMonic.coeff i`'s algebraic sub-expressions —
**NOT a `totalDegree` bound on `towerToRdec p sg (curBeforeMonic.coeff i)`
itself, the SPECIFIC deterministic pair that function computes** (three-
level recursive `def`, `K2 → K1 → K0 → Rdec`, combining sub-results via
`n0*d1 + n1*d0*X(wgen), d0*d1` at each level — see
`TheDataDerivation/DataDerivationMumford.lean`'s `towerToRdec` `def`).

**Why this actually matters, checked directly against `CrossNondegenerate`'s
own definition** (`DecoupledSystemRegular.lean` ~line 1992): `hu0`/`hu1`/
`hv0`/`hv1` state `IsSMulRegular` on `theData`'s LITERAL `u1_num`/`u1_den`/
etc. fields, which are `towerToRdec p sg (uRS.coeff i)`'s literal
`.1`/`.2` — used directly as `MvPolynomial` ring elements inside `Fu0 :=
u1_num i - X_target * u1_den i` and the resultant `u1_den*u2_num -
u2_den*u1_num`, INSIDE `Rdec p ⧸ ⟨Fu0⟩`. `IsRdecWitness`'s existential only
claims `evalNd nd.1 = evalNd nd.2 * ι v` for SOME `(nd.1,nd.2)` under a
chosen `ι`/`evalNd` pair — it does NOT claim `nd = towerToRdec p sg v`
syntactically, and a witness for `v` is not unique (`(n*k,d*k)` also
witnesses `v` for any `k`). So `curBeforeMonic_leadingCoeff_isRdecWitness`/
`uRS_coeff_isRdecWitness`'s existential bounds **cannot be substituted
in place of `towerToRdec`'s own computed pair** in `CrossNondegenerateDegreeBound.lean`'s
hypotheses `hA`/`hB` — confirming, by direct inspection this pass (not
just re-asserting the file's own prior docstring caveat), that this really
is a structural mismatch, not a bookkeeping gap closeable by more Lean
tactics alone.

**Also checked and ruled out this pass**: restating `CrossNondegenerateDegreeBound.
lean`'s conclusion in `IsRdecWitness` form (the file's own earlier
speculative "next step") does NOT sidestep this — `CrossNondegenerate`'s
consumer needs `IsSMulRegular` on the SPECIFIC `theData`-computed resultant
value, a property of that literal ring element, not of an arbitrary
equal-valued-under-some-eval witness; an `IsRdecWitness`-shaped bound on
"some witness for the resultant" doesn't transfer to `IsSMulRegular` on the
actual `theData` value without exactly the same "is this really the
`towerToRdec`-computed pair" identification problem re-appearing one level
up.

**Correct next step, this pass's conclusion**: the degree bound needs to
be proved DIRECTLY on `towerToRdec`'s own recursive formula — i.e. trace
concrete `totalDegree` bounds through the SAME `n0*d1+n1*d0*X(wgen),
d0*d1`-style recursive combination `towerToRdec`/`towerToRdecK1` actually
compute, for the SPECIFIC sub-terms (`t1`, `t2`, `u0`, `u1`, `curBeforeMonic.
coeff{0,1,2}`, etc.) that `curBeforeMonic.coeff i` decomposes into — rather
than routing through `IsRdecWitness`'s abstract existential combinators.
This is plausibly "the same triangle-inequality bookkeeping, one recursion
layer over", since `DataDerivationTotalDegree.lean`'s existing
`towerToRdecK1_totalDegree_le`/`towerToRdec_totalDegree_le` ALREADY prove
exactly this shape (concrete bound on `towerToRdec`'s literal output, given
a bound on its input) — for a SINGLE `K2`-element `v` treated as an opaque
input. What's missing is applying that machinery with `v :=
curBeforeMonic.coeff i` and tracing the `K2`-degree bound `315448` for the
INPUT side (`v` itself, meaning: what does `towerToRdecK1_totalDegree_le`'s
own hypothesis actually need bounded, at the `K1`-internal
`modByMonicHom`-extracted level — likely NOT the same `315448` number, since
that number bounds the WITNESS's degree, not `v`'s own "size" in any
sense `towerToRdecK1_totalDegree_le` consumes) — this substitution has NOT
yet been checked and is genuinely unclear without either (a) re-reading
`towerToRdecK1_totalDegree_le`'s hypothesis shape very carefully against
what's actually available about `curBeforeMonic.coeff i`, or (b) a
ChatGPT consult.

## Update, latest pass: prompt actually written to disk (previous pass's claim was stale — no such file existed)

**`chatgpt_prompt_isrdecwitness_to_concrete_bound.md`** (`Genus2Lean/` top
level) is now actually on disk — a prior pass claimed this was "drafted"
but no file existed anywhere in the repo; written fresh this pass,
grounded directly against the verified current code rather than
re-asserting the prior pass's framing. Confirms, by direct inspection of
`TowerToRdecMul.lean`'s own docstring plus `uRS := C leadingCoeff⁻¹ *
curBeforeMonic` (`DataDerivationMumford.lean`) and `theData.u1_num i :=
(coeffsToNumDen ... (uRS.coeff i)).1` (`DecoupledSystemRegular.lean`),
that the obstruction is specifically MULTIPLICATION of two
independently-obtained `towerToRdec` values — sums and algebraMap-
promotion already have working, REPL-confirmed direct machinery
(`combine_totalDegree_le`, `towerToRdec_algebraMap_totalDegree_le`,
`t0_promoted_totalDegree_le`), and `towerToRdec (a*b) ≠ (product of
witnesses)` in general is itself an already-proved fact, not a bookkeeping
gap. `uRS.coeff i` inherits this exactly because `uRS` is a product of two
independently-obtained `curBeforeMonic`-derived values (`leadingCoeff⁻¹`
and `curBeforeMonic` itself). The prompt asks three concrete questions:
(1) whether `towerToRdec`'s literal output and any `IsRdecWitness` witness
are related by a UNIT in `MvPolynomial Vars (F p)` (hence a nonzero `F p`
scalar, since that's this ring's whole unit group) whenever both arise
from a "reduced" construction — which would make `IsSMulRegular` transfer
for free, since units preserve zero/nonzero and regularity; (2) whether
`uRS.coeff i` can be shown LITERALLY EQUAL (not just IsRdecWitness-
related) to an expression that avoids `curBeforeMonic`'s `/ₘ`-chain
definition and its triangular-coefficient-equation detour entirely, so
the whole chain becomes rewrite-transportable into `CrossNondegenerate`'s
literal `IsSMulRegular (Rdec p ⧸ ⟨Fu0⟩) ...` goal; (3) failing both,
whether computer-algebra/resultant theory (subresultants, content/
primitive-part tracking, pseudo-remainder sequences) has a standard
technique for tracking a boundable "correction factor" between a literal
recursive output and an abstract witness, that this project should
borrow rather than reinvent from scratch.

## Update, latest pass: ChatGPT reply received and cross-checked against this snapshot's actual Mathlib API — concrete, verified plan below

**Reply's headline claim**: for REDUCED witness pairs (`IsRelPrime` numerator/
denominator, not an arbitrary `IsRdecWitness`), two witnesses for the same
value are related by a UNIT of `MvPolynomial Vars (F p)` — and since that
ring's units are exactly the nonzero constants `C c` (`c : F p`), a unit
correction factor has `totalDegree = 0` for free, and `Ideal.span {u*g} =
Ideal.span {g}` for a unit `u`, so `IsSMulRegular` transfers across the
substitution at NO extra bound cost. This would resolve question 1 cleanly
IF `towerToRdec`'s output is provably "reduced" in the relevant sense at
each tower level.

**Checked against this snapshot's real Mathlib docs this pass (not
guessed)** — both key facts the reply leans on are REAL, confirmed via
direct doc lookup: `IsFractionRing.num_den_reduced`/`IsFractionRing.
exists_reduced_fraction` exist in `Mathlib.RingTheory.Localization.NumDen`,
requiring `[UniqueFactorizationMonoid A]` on the base ring; and
`MvPolynomial.uniqueFactorizationMonoid` (`Mathlib.RingTheory.Polynomial.
Basic`) gives exactly that instance for `A := MvPolynomial (Fin 2) (F p)`
(our `K0`'s base ring) since `F p` is a field, hence trivially a UFD. So
`IsFractionRing.num`/`.den`'s BASE-CASE reducedness (the `K0` level, where
`towerToRdec`'s recursion bottoms out via `baseFracToRing`) is real,
available Mathlib content, not a hoped-for fact. **Did NOT find a named
Mathlib lemma for "units of `MvPolynomial σ R` over a field/domain are
exactly `C c`"** — searched directly, no hit under any plausible name.
**Decision: don't depend on that lemma name at all.** In this project's
actual use, the correction-factor unit that would arise IS concretely `C
c` by construction (it comes from `IsFractionRing.num_den_reduced`-style
uniqueness applied to elements of `MvPolynomial (Fin 2) (F p)` — i.e. a
UFD associate relation `a' = c * a` for `c` a constant, not an abstract
`Aˣ` element), so the degree-zero fact needed is just `MvPolynomial.
totalDegree_C` (already used repeatedly elsewhere in this project,
confirmed-safe name) applied directly to that constant — no unit-
characterization lemma needed, no guessed name risk.

**The genuine remaining gap, not yet closed by the reply or this pass**:
the reducedness argument only gives canonicality at the LEVEL where
`IsFractionRing.num_den_reduced` applies directly — the `K0`-level base
case inside `baseFracToRing`. Whether `towerToRdecK1`/`towerToRdec`'s
OWN one-level-up combination (`n0*den1+n1*den0*X(w), den0*den1`) preserves
reducedness, or whether `AdjoinRoot.modByMonicHom`'s remainder extraction
at each tower level could reintroduce a common factor, has NOT been
checked against either this project's code or Mathlib — this is exactly
the "same K2 value → same rational function → cross-multiplied equality →
both pairs reduced → associates → same totalDegree" chain the reply's own
section 1 flags as having a real bottleneck, and that bottleneck is now
the precise open question, not the general existence of the reduced-
witness theory (which IS real Mathlib content, confirmed above).

**Priority order, per the reply's own recommendation and consistent with
what this pass verified**:
1. ~~Try the reply's route 3 FIRST for `uRS` specifically~~ **CORRECTED
   this pass, after checking Mathlib's actual `AdjoinRoot.modByMonicHom`
   API directly**: the reply's point that `uRS.coeff i = curBeforeMonic.
   leadingCoeff⁻¹ * curBeforeMonic.coeff i` is "not the generic bad case"
   because one factor is "a literal K2 scalar" does NOT actually give a
   free ride the way it first looked. `AdjoinRoot.modByMonicHom` (the
   operation `towerToRdec`'s recursion is built from at each tower level)
   is `R`-LINEAR where `R` is the AdjoinRoot's BASE ring — e.g. for
   `K2 := AdjoinRoot (K2_poly_monic ...)`, base ring `K1` — so it commutes
   with scalar multiplication by `K1`-lifted elements (already exploited,
   confirmed, by `towerToRdec_algebraMap_totalDegree_le`'s existing proof)
   but NOT with multiplication by an arbitrary OPAQUE `K2` element like
   `curBeforeMonic.leadingCoeff⁻¹`, which need not be (and has no reason
   to be) a `K1`-lift. So `modByMonicHom (s * v) ≠ s • modByMonicHom v`
   in general for `s : K2` arbitrary — this really is a genuine instance
   of the SAME multiplication-of-two-independent-K2-values obstruction,
   not a free scalar case. **Item 1 is therefore NOT the cheap win it
   looked like; withdrawn as a "does not require route 1" claim.** Left
   here, struck through rather than deleted, since the corrected
   reasoning (why the obvious-looking shortcut fails) is itself useful
   for whoever picks this up next, per this project's "note stale claims
   in place" convention.
2. For `curBeforeMonic.coeff i` itself (genuinely has no closed form —
   confirmed this pass, `curBeforeMonic := (.../ₘ.../ₘ...)/ₘ...` with no
   alternate closed-form expression anywhere in this codebase or the
   Julia reference it was ported from): the reply's route 2 (avoid
   unfolding `/ₘ`, use `Polynomial.divByMonic` uniqueness instead) is
   ALREADY substantially what `eq_mul_divByMonic_of_dvd`/`Npoly_eq_
   curBeforeMonic_mul` do (`DataDerivationSolve.lean`, REPL-confirmed
   green, checked this pass) — but that route bottoms out needing a
   DIRECT (non-existential) bound on `Npoly.coeff k`, which in turn
   requires direct bounds on `Epoly`/`Ypoly.coeff` (`NpolyCoeffTotalDegree.
   lean`), which are built from `coeffsOut`/Cramer-solution entries that
   ARE genuine independent-`towerToRdec`-value products (`matrixA_row0_
   totalDegree_le` etc., `MatrixEntryTotalDegree.lean`, confirmed this
   pass to already be `IsRdecWitness`-based for exactly this reason —
   NOT a route-2-closeable gap, a genuine route-1 (reduced-witness) case).
   So route 2 does NOT fully sidestep route 1 for this specific project —
   it pushes the SAME multiplication obstruction down to `coeffsOut`'s
   own construction, one layer earlier than previously thought.
3. **Corrected conclusion, this pass**: with item 1 withdrawn (see above
   — the "cheap scalar case" doesn't actually avoid the obstruction
   either, since `modByMonicHom`'s linearity is only over the AdjoinRoot's
   OWN base ring, not over arbitrary opaque elements of the tower field
   itself), route 1 (the reduced-witness/unit theorem) is not just the
   fallback but the load-bearing piece needed EVERYWHERE multiplication
   of two independently-obtained `K2` values occurs in this dependency
   chain — `uRS`'s own normalization step included, not exempt from it.
   **Actual next action**: attempt the reduced-witness/unit theorem
   (reply's route 1) specifically for `IsFractionRing.num`/`.den` at the
   `K0` base case first (confirmed-real Mathlib content this pass:
   `IsFractionRing.num_den_reduced`/`exists_reduced_fraction` in
   `Mathlib.RingTheory.Localization.NumDen`, needing `[UniqueFactorization
   Monoid A]` on `A := MvPolynomial (Fin 2) (F p)`, itself available via
   `MvPolynomial.uniqueFactorizationMonoid` since `F p` is a field —
   both confirmed present in this snapshot's Mathlib docs this pass, not
   guessed), THEN check whether `towerToRdecK1`/`towerToRdec`'s own
   one-level-up combination formula (`n0*den1+n1*den0*X(w), den0*den1`)
   preserves reducedness. This is NOT yet checked and is genuinely
   unclear: there's no obvious reason `n0*den1+n1*den0*X(w)` stays
   coprime to `den0*den1` even granting `n0`⊥`den0` and `n1`⊥`den1`
   individually — if reducedness does NOT propagate up the tower, the
   reduced-witness route may only apply at the bare `K0` level and a
   different argument is needed for how far up the tower canonicality
   (or a weaker but still useful invariant) survives. **Not yet analyzed
   — the next thing to check, by hand or via a further ChatGPT
   consultation, before writing any Lean for this route.** Also note:
   `MvPolynomial`'s unit group was NOT confirmed under any named Mathlib
   lemma this pass (searched, no hit) — don't depend on an "units are
   constants" lemma name; the concrete correction factors that arise from
   `IsFractionRing.num_den_reduced`-style UFD-associate reasoning are
   literal `C c` terms by construction, so `MvPolynomial.totalDegree_C`
   (already a confirmed-safe, already-used name in this codebase) is
   sufficient — no new lemma-name risk needed for the degree-zero part
   of this argument.

## Update, latest pass: the flagged open question is RESOLVED — reducedness does NOT propagate, with a concrete counterexample (hand computation, `sympy`-checked, no Lean/Mathlib dependency)

**Answer: no, `towerToRdecK1`'s combination formula does NOT preserve
reducedness in general**, settling the question the previous pass left
open. Concrete counterexample (single-variable case suffices to disprove
the general claim; verified with `sympy`, exact polynomial division, not
approximate): take `n0 = x+5`, `den0 = x*(x-2)`, `n1 = x+7`, `den1 =
x*(x+3)`. Individually, `IsRelPrime n0 den0` and `IsRelPrime n1 den1`
both hold (`gcd(x+5, x(x-2)) = 1`, `gcd(x+7, x(x+3)) = 1`, confirmed).
But the combined pair

```
num := n0*den1 + n1*den0*w = w*x^3+5*w*x^2-14*w*x + x^3+8*x^2+15*x
den := den0*den1           = x^4+x^3-6*x^2
```

(`w` a fresh variable, exactly matching `towerToRdecK1`'s own `X
(sg.wGen 0)` role) has `gcd(num, den) = x`, confirmed by exact polynomial
division both ways (`num/x` and `den/x` are both genuine polynomials, no
remainder). **The mechanism**: nothing in `IsFractionRing.num_den_
reduced`'s guarantee (`IsRelPrime n_i den_i` for EACH `i` separately)
ever forces `den0` and `den1` — denominators of TWO DIFFERENT `K0`
coefficients of the same `v : K1` — to be coprime TO EACH OTHER. Here
both share the factor `x`, and that shared factor survives into the
combined numerator too (since `num = n0*den1 + n1*den0*w`, and `x | den0`,
`x | den1` together force `x | n1*den0*w` trivially and `x | n0*den1`
since `x | den1` — both summands divisible by `x` even though `n0`,`n1`
individually aren't).

**This does NOT kill route 1, but it does kill the naive form of it.**
The fix is straightforward and still well inside real Mathlib content:
apply `UniqueFactorizationMonoid.exists_reduced_factors'` (confirmed
real this pass — searched directly, `Mathlib.RingTheory.
UniqueFactorizationDomain.Basic`: `(a b : R) (hb : b ≠ 0) : ∃ a' b' c',
IsRelPrime a' b' ∧ c'*a' = a ∧ c'*b' = b`) to the COMBINED, possibly-
unreduced pair `(num, den)` AFTER each `towerToRdecK1`/`towerToRdec`
combination step, rather than assuming the recursive construction stays
reduced automatically. This still gives canonicality of the REDUCED
form (`a'`, `b'` are unique up to unit, by the same UFD argument as
before), and still gives what's needed for the `IsSMulRegular` transfer
— the cofactor `c'` extracted this way is a legitimate `MvPolynomial`
element, not necessarily a unit, so IT needs its own `totalDegree` bound
too (unlike the fantasy "unit correction factor" of the naive version),
but that's a much easier ask than the original problem: `c'` divides
BOTH `den0*den1` (known bound) and the combined numerator (known bound),
so `totalDegree c' ≤ totalDegree den` trivially (a divisor's totalDegree
is bounded by the dividend's, for a nonzero dividend in a domain — needs
its own confirmed Mathlib lemma before use, not yet checked this pass).

**Revised route 1, concretely, for the next pass**:
1. At each combination step (`baseFracToRing`'s output combined via
   `towerToRdecK1`, then `towerToRdecK1`'s output combined via
   `towerToRdec`), DON'T assume the combined pair is already reduced.
   Instead apply `exists_reduced_factors'` to `(num, den)` to extract a
   GENUINELY reduced pair `(num', den')` plus cofactor `c'` with `c'*num'
   = num`, `c'*den' = den`.
2. Bound `totalDegree c'` via `c' ∣ den` (or `c' ∣ num` if `den = 0`,
   edge case to handle) and a to-be-confirmed "totalDegree of a divisor
   ≤ totalDegree of dividend" Mathlib lemma (NOT yet searched/confirmed
   this pass — flagged as the next concrete lemma-existence check before
   writing any Lean for this).
3. `totalDegree num' ≤ totalDegree num` and `totalDegree den' ≤
   totalDegree den` then follow the same way (both `num'`, `den'` divide
   `num`, `den` respectively via `c'*num'=num` etc.) — so the REDUCED
   pair's degree bound is dominated by whatever bound was already
   available for the unreduced combined pair. **This means the degree
   bound itself doesn't get WORSE by reducing** — reducing only helps
   the uniqueness/canonicality argument, it doesn't need a separate
   degree analysis.
4. Whether `towerToRdec`'s OWN literal output (the actual recursively-
   computed pair, not this reduced alternate one) equals `(num', den')`
   up to a further unit, or merely `IsRdecWitness`-relates to it via
   ANOTHER cofactor, is the piece that closes the loop back to the
   original goal (bounding `towerToRdec`'s literal output) — not yet
   worked out. This is genuinely the crux: `towerToRdec p sg v`'s literal
   pair `(num,den)` before this reduction step IS the thing we need
   bounded; reducing it to `(num',den')` doesn't help unless we can also
   show `IsSMulRegular` transfers along `(num,den) = c' • (num',den')`-
   style relations (`Ideal.span {c' * g'} ` vs `Ideal.span {g'}` differ
   by the ideal generated by `c'` too, UNLESS `c'` happens to be a unit
   — so this only fully closes the `IsSMulRegular` transfer if `c'` is
   forced to be constant, which is not established and may not be true).
   **Flagged, not resolved**: the reduction step controls the DEGREE
   bound cleanly (step 3 above) but does NOT obviously control the
   `IsSMulRegular`-transfer requirement the way the original naive
   "unit correction factor" idea would have — that transfer needs a
   genuinely separate argument, likely requiring `c' ≠ 0` (probably
   available — `den ≠ 0` should be provable from the construction, though
   not yet checked) plus a fact like "if `g = c*g'` with `c ≠ 0` in a
   domain, then `x` is `IsSMulRegular` mod `⟨g⟩` iff [some related but
   NOT identical condition] mod `⟨g'⟩`" — genuinely unclear whether this
   holds without more structure (e.g. it plausibly fails if `c'` and `x`
   share a factor). **This is a real, currently-unresolved gap, flagged
   honestly rather than assumed away** — a good candidate for the next
   ChatGPT consultation once the degree-bound half (steps 1-3) is
   written up and REPL-tested, since the `IsSMulRegular`-transfer
   question is now sharply and concretely stated (not the vague
   "does canonicality help" framing of earlier passes).

**Small blocking lemma identified this pass, own prompt drafted**: step 2
above needs "in a domain, `c*a' = a`, `a ≠ 0` ⟹ `totalDegree c ≤
totalDegree a`" for `MvPolynomial`. Searched Mathlib docs directly this
pass — `MvPolynomial.totalDegree_mul` (the ≤-only upper-bound direction)
is confirmed and already used throughout this codebase, but no equality
or reverse-direction lemma surfaced under any plausible name. The
underlying math is definitely true (verified by hand via the standard
"top-total-degree homogeneous part is nonzero in a domain" argument, and
spot-checked numerically) — this is a real gap in what's easily findable,
not a false claim. `chatgpt_prompt_totaldegree_of_divisor.md` (`Genus2Lean/`
top level) asks for the exact Mathlib name/route, scoped narrowly (no
project-specific content, pure `MvPolynomial` algebra over a domain) —
**not yet sent/resolved**. If Mathlib has no ready lemma, `MvPolynomial.
IsHomogeneous.totalDegree` (confirmed real — a nonzero homogeneous
component has totalDegree exactly `n`) is the natural route for a from-
scratch proof: take `p`'s totalDegree-`d` homogeneous part `P` and `q`'s
totalDegree-`e` part `Q`; `P*Q` is the totalDegree-`(d+e)` homogeneous
part of `p*q` and is nonzero (domain, `P≠0≠Q`), giving `totalDegree(p*q) =
d+e` exactly — not yet written up as Lean, flagged as the fallback route
if the ChatGPT consult doesn't turn up a direct lemma quickly.

## Update, later pass: the small blocking lemma above is RESOLVED, from scratch, no ChatGPT reply needed

`MvPolynomialTotalDegreeMulEq.lean` (new file) proves both
`MvPolynomial.totalDegree_mul_of_ne_zero` (the `=` strengthening) and
`MvPolynomial.totalDegree_le_of_mul_eq_of_ne_zero` (the direct target
this section asked for) via exactly the "fallback route" sketched above
(`IsHomogeneous.totalDegree` on the top homogeneous components) — no
ready-made Mathlib lemma turned up, so the fallback was needed, but it
was straightforward. **REPL-confirmed green.** `chatgpt_prompt_totaldegree_
of_divisor.md` was never actually sent — this closed without it.

## Update, later pass — the SAME gap resurfaces one level up, genuinely unresolved this time

`crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le`
(`CrossNondegenerateDegreeBound.lean`) are conditional on `hA`/`hB`, a
LITERAL bound on `towerToRdecK1`'s output when fed `uRS.coeff i`'s two
`K1`-extracted children — i.e. exactly `towerToRdec_coeff_totalDegree_le`'s
own hypothesis shape (`DataDerivationTotalDegree.lean`), which bounds
`towerToRdec`'s literal recursive output GIVEN a literal base-case bound.
`uRS_coeff_isRdecWitness`/`curBeforeMonic_leadingCoeff_isRdecWitness`
(`URSCoeffIsRdecWitness.lean`, REPL-confirmed green) give a DIFFERENT kind
of bound — an existential `IsRdecWitness` witness, not necessarily
`towerToRdec`'s own computed pair, since witnesses for the same value
aren't unique. **These two do not connect**: nothing currently derives
`hA`/`hB` (or anything else literal-shaped) from the `IsRdecWitness`
bound in hand. This is the "Revised route 1, step 4" gap this document's
earlier section already flagged as "genuinely the crux, not yet worked
out" — traced precisely this pass (not re-derived from vague memory):
`crossResultant_totalDegree_le`'s proof, checked directly, never goes
through `IsRdecWitness` at all, so there is no obvious rewrite of its
conclusion into `IsRdecWitness` form that would let the witness bound
discharge it — the mismatch is at the HYPOTHESIS level (`hA`/`hB` want a
literal base-case bound), not a form-of-conclusion mismatch. `chatgpt_
prompt_literal_towertordec_bound.md` (`Genus2Lean/` top level) asked
whether route 2's witness bound can be pushed to a literal bound via
`exists_reduced_factors'` (mirroring the earlier-flagged "Revised route
1" plan) or whether this is a genuinely separate obstruction. **Sent and
answered — see the next section, which supersedes this one.** Both
`crossResultant_totalDegree_le`/`crossResultantV_totalDegree_le` remain
conditional on `hA`/`hB` as stated; nothing regresses, this just
documents precisely why they weren't closeable from what was proved as
of this section.

## Update, later pass — ChatGPT reply received, route confirmed to work, AND SIMPLER than expected (verified against real Mathlib docs, not yet written as Lean)

**Bottom line: the gap above closes without `exists_reduced_factors'` at
all.** ChatGPT's proposed route (bound a witness → bound the canonical
`IsFractionRing.num`/`.den` via `exists_reduced_factors'` +
`IsFractionRing.num_den_unique`) is real and its cited lemma names are
all confirmed present in current Mathlib4 (`IsFractionRing.num_den_unique`,
`IsFractionRing.mk'_num_den`, `UniqueFactorizationMonoid.
exists_reduced_factors'` all checked directly against mathlib4_docs this
pass). But tracing it against this project's OWN code turned up a
shortcut: `baseFracToRing` — the base case (`K0` level) of the whole
`towerToRdec` recursion — is defined LITERALLY as `IsFractionRing.num`/
`.den` (via `aeval (X ∘ tGen)`), and `DataDerivationTotalDegree.lean`
ALREADY has `isFractionRing_num_totalDegree_le`/
`isFractionRing_den_totalDegree_le` bounding those directly from a
`v = IsLocalization.mk' (K0 p) a ⟨b,_⟩` witness — via `IsFractionRing.
num_den_reduced` + `dvd_of_dvd_mul_right`/`_left` + `MvPolynomial.
totalDegree_le_of_dvd_of_isDomain`, NO `exists_reduced_factors'`/
`Associated`/`num_den_unique` needed. `baseFracToRing_totalDegree_le`
(same file) already composes this with the `aeval` renaming step
(degree-non-increasing, `aeval_X_comp_totalDegree_le`) to give the
FULL base-case bound in exactly the shape `towerToRdecK1_totalDegree_le`'s
`h` hypothesis wants. **This is already fully proved and REPL-confirmed
— nothing new needed at the base case.**

**The one missing piece, precisely identified this pass**: everything
above needs `v` (a `K0 p` element — e.g. one of `curBeforeMonic`'s two
`K1`-extracted-then-further-extracted `K0` pieces, NOT `uRS.coeff i`
itself, which lives three tower levels higher at `K2`) exhibited as
`v = IsLocalization.mk' (K0 p) a ⟨b,hb⟩` for some EXPLICIT, bounded
`(a,b)`. What `IsRdecWitness`/`uRS_coeff_isRdecWitness` actually supply
is the cross-multiplied equation `evalNd n = evalNd d * ι v` — a
DIFFERENT but equivalent shape. The exact bridging lemma, confirmed
present in Mathlib4 this pass (`Mathlib.RingTheory.Localization.Defs`):
`IsLocalization.mk'_eq_iff_eq_mul {x:R}{y:↥M}{z:S} : mk' S x y = z ↔
algebraMap R S x = z * algebraMap R S ↑y` — symmetrized, this is
LITERALLY `IsRdecWitness`'s defining equation (`evalNd n = evalNd d *
ι v`) with `evalNd = algebraMap`, `ι = id`, at exactly the base level
(`K0`, where `IsRdecWitness`'s generic `ι`/`evalNd` genuinely
specialize to plain `algebraMap`, unlike at `K1`/`K2` where they're the
composite tower embeddings). So: an `IsRdecWitness`-shaped hypothesis on
a `K0`-element, PLUS `b ≠ 0` (needed for the `⟨b,hb⟩ : ↥(nonZeroDivisors
_)` packaging — `mem_nonZeroDivisors_of_ne_zero`, already used by
`numDen_cross_mul` in the same file), converts via
`mk'_eq_iff_eq_mul.mpr` into exactly `baseFracToRing_totalDegree_le`'s
`hv` hypothesis.

**The actual remaining work, concretely scoped**: this bridge only
closes the base case (`K0` level). The `uRS.coeff i`/`vRS.coeff i`
values `crossResultant_totalDegree_le`'s `hA`/`hB` need are `K2`-level,
three tower steps above `K0`, and `URSCoeffIsRdecWitness.lean`'s witness
bound is built via `IsRdecWitness.mul`/`.div` operating at the `K2`
level directly (composing `curBeforeMonic`'s own `K2`-valued
leadingCoeff/coeff witnesses), NOT by recursing back down through
`towerToRdecK1`/`towerToRdec`'s own base-case-forward construction. So
the base-case bridge above, while now fully understood, does NOT by
itself produce `hA`/`hB` — what's actually needed is either (a) tracing
`curBeforeMonic.coeff i`'s OWN `K0`-level sub-pieces (`t1`/`t2`/`gu0`/
`gu1` per `CurBeforeMonicCoeffTotalDegree.lean`'s own composition) and
re-deriving THEIR `IsLocalization.mk'`-witness form directly (bypassing
`IsRdecWitness` for this purpose, going straight to
`baseFracToRing_totalDegree_le`'s hypothesis at each base case, then
propagating up through `towerToRdecK1_totalDegree_le`/
`towerToRdec_totalDegree_le`'s ALREADY-PROVED recursive step — this is
the "obvious" route and avoids `IsRdecWitness` for this particular goal
entirely), or (b) finding/proving an analogous bridge one level up (`K1`,
`K2`) connecting `IsRdecWitness` witnesses to the LITERAL
`towerToRdecK1`/`towerToRdec`-computed pair at those levels specifically
(harder — `towerToRdecK1`/`towerToRdec` are NOT built from `IsFractionRing.
num`/`.den` the way `baseFracToRing` is, so no analogous direct bridge is
known to exist at those levels; this is where `exists_reduced_factors'`
might still be needed, if route (a) turns out to be blocked). **Route (a)
is the one to attempt first** — it reuses proved infrastructure top to
bottom and needs no new Mathlib-level lemma, only re-deriving
`curBeforeMonic.coeff i`'s pieces in `IsLocalization.mk'`-witness form
(which `CurBeforeMonicCoeffTotalDegree.lean`'s own construction already
implicitly has, from `t0_promoted_totalDegree_le`/`Npoly_coeff_
isRdecWitness_uniform` — these were built as `IsRdecWitness` witnesses,
but per the bridge above, an `IsRdecWitness` witness on a `K0`-level
piece converts to an `IsLocalization.mk'` witness for free via
`mk'_eq_iff_eq_mul`, so nothing needs to be RE-PROVED from scratch, only
RESHAPED). **Not yet attempted in Lean** — this is a plan, precisely
scoped against verified Mathlib names and this project's own existing
lemma set, for the next pass to implement directly rather than
re-deriving the trace above from scratch.

## Update, later pass — Route (a)'s premise was WRONG; corrected route found, via ChatGPT, matching this project's own already-proved machinery

**Route (a) above does not apply.** Traced directly this pass: `t1`,
`t2`, `gu0`, `gu1` (`CurBeforeMonicCoeffTotalDegree.lean`'s own
`anchor1`/`anchor2`/`algebraMap (F p) (K2 ...)`-built pieces) are `K2`
p `c0 c1 c2 c3 c4`-VALUED, not `K0`-valued as this document's "Route (a)"
assumed — `baseFracToRing_totalDegree_le` (a `K0`-level lemma) does not
apply to them directly, contrary to what the paragraph above claims.
This was caught by direct inspection of `anchor1`'s return type
(`K2 p c0 c1 c2 c3 c4 × K2 p c0 c1 c2 c3 c4`), not assumed from the
existing prose.

**ChatGPT consultation, this discrepancy specifically.** Confirmed the
above and diagnosed the real obstruction precisely: an existential
`IsRdecWitness` witness for a whole `K2`-element `v` (or `K1`-element)
constrains only the VALUE `v` represents, not its canonical
`AdjoinRoot.modByMonicHom`-coordinates (`v0,v1` with `v = v0 + v1*w`,
`modByMonicHom` not being a ring hom means no generic operation turns a
witness for `v` into witnesses for `v0`/`v1`). Proposed fix: exploit the
QUADRATIC structure explicitly. Given `v = v0 + v1*w` (`w^2 = c` the
extension's defining relation) and a witness `a/b` for `v` in the
surrounding fraction field, clearing denominators mod `w^2-c` gives a
2×2 LINEAR system in `v0,v1` (`a0 = b0*v0 + c*b1*v1`, `a1 = b0*v1 +
b1*v0`, writing `a = a0+a1*w`, `b = b0+b1*w`) — solvable via this
project's own existing Cramer's-rule infrastructure
(`CoeffsOutTotalDegree.lean`'s `matrixDet_totalDegree_le`/
`cramerNumeratorDet_totalDegree_le` etc., already built for an unrelated
4×4 system one level up — same technique, smaller system).

**Independently confirmed this pass, and better than a new lemma is
needed**: `adjoinRoot_quadratic_normal_form` (`DataDerivationMumford.
lean`, already proved, fully generic over any monic quadratic) IS
exactly the canonical-form identity ChatGPT's route needs (`x = algebraMap
... (modByMonicHom x).coeff 0 + algebraMap ... (modByMonicHom x).coeff 1
* root`), and `towerToRdec_spec`'s OWN proof (same file, already proved,
REPL-confirmed) already builds the FULL chain from a hypothesis-supplied
`ι` down through both quadratic levels using exactly this identity
(`hK1repr`/`hK2repr`/`hK1spec` locals inside that proof) to show the
literal `towerToRdec` output's `algebraMap`-image equals `ι v` exactly —
i.e. `towerToRdec_isRdecWitness` (`TowerToRdecMul.lean`) already IS the
witness fact this whole chain was trying to derive from scratch. **The
open gap was never "does a witness exist for the literal pair" — that
was already closed. The gap is a DEGREE bound on that same literal
pair**, which needs `d0`/`d1` (the coeff-0/coeff-1 extractions at each
level) individually exhibited as bounded-degree `mk'`-witnesses, not
merely as *some* value satisfying a cross-multiplied equation together
with the rest of the tower.

**Concrete next step, not yet attempted in Lean**: adapt
`towerToRdec_spec`'s own proof structure (`hK1repr`/`hK2repr`'s
`algebraMap`-decomposition identities, combined with a per-level 2×2
Cramer solve mirroring `CoeffsOutTotalDegree.lean`'s existing 4×4
machinery) into a DEGREE-BOUND-carrying version: given a bounded-degree
witness for `v : K2` (e.g. `curBeforeMonic_coeff_totalDegree_le`'s
existing `≤315448` `IsRdecWitness` fact), derive bounded-degree
`IsLocalization.mk'`-witnesses for `(modByMonicHom v).coeff 0`/`.coeff 1`
(`K1`-valued), then repeat one level down for THEIR `K0`-level
coefficient pairs, finally feeding `isFractionRing_num_totalDegree_le`/
`baseFracToRing_totalDegree_le`/`towerToRdecK1_totalDegree_le`/
`towerToRdec_totalDegree_le` (all already proved) to close `hA`/`hB`.
This is real, nontrivial new Lean work (a per-level linear-system
inversion, not a reshaping of an existing fact) — flagged honestly as
such, not yet attempted.

