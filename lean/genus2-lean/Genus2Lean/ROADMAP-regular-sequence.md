# Roadmap: `decoupledSystem_isRegularSequence` — proving 0-dimensionality of
the `P1+P2-P3-P4=(alpha-alpha')*a` matching system via a regular sequence

## Revision note (this pass)

Two changes to the target, both raising the bar from "transcribe a
computation" to "formalize a construction," requested directly rather than
inferred:

1. **`p` is now symbolic, not `p = 2371157`.** Every previous draft of this
   roadmap (and the current `DecoupledSystemRegular.lean`) fixes
   `curveP : ℕ := 2371157` and works in `F = ZMod curveP` as a *concrete*
   finite field. That numeral is gone. `F` becomes `ZMod p` for an arbitrary
   `p : ℕ` carrying only `[Fact (Nat.Prime p)]` as a hypothesis — no more
   than that is assumed anywhere. This matches how `c0,...,c4` were already
   demoted from numerals (`x^5+x+2`) to symbolic-but-fixed parameters in the
   prior session; `p` gets the identical treatment. The paper/thesis claim
   this is aiming at is genuinely "for the general genus-2 curve over the
   general prime field," not "for this one curve over this one 7-digit
   prime" — the whole point of formalizing rather than just re-running the
   Julia computation at a bigger `p` is that no finite amount of numerical
   testing establishes a `∀ p` statement, whereas an actual Lean proof
   parametric in `p` does.
2. **`theData` is derived, not transcribed.** Every previous draft treats
   `PhiSymbolic.symbolic_residual` as a black box: get Julia/Oscar to print
   the 8 (or, in the intermediate symbolic-`c0..c4` draft, still 8, now with
   symbolic coefficients) polynomials, hand-parse or mechanically transcribe
   them into a Lean `def`. That path is explicitly abandoned in this pass —
   not because it became infeasible, but because it defeats the purpose:
   the goal is a proof that does not depend on trusting the Julia/Oscar
   computation was implemented correctly. `theData` must instead be built by
   Lean definitions and lemmas that carry out the *same sequence of
   algebraic moves* `symbolic_residual` performs — tower construction,
   linear solve, `E²-fY²`, exact division, mod-`u_RS` reduction — so that
   the kernel checks the derivation, not just the output. This is a much
   larger undertaking than transcription and is the bulk of what's new
   below (§4).

These two changes compound: with `p` symbolic, `F = ZMod p` is not even
guaranteed to contain specific elements needed for constructions Julia's
concrete `p = 2371157` run relies on implicitly (e.g. nothing here needs
`p` large in a way that's spelled out, but nothing has *checked* that
either) — see the new "what genericity in `p` actually buys/costs" note in
§4. Everything downstream (§5, the regular-sequence steps) changes shape
too: "regular for generic `(c0,...,c4)`" becomes "regular for generic
`(c0,...,c4)` and all `p` outside a coprimality-type exceptional set,"
which is a mixed characteristic-0/positive-characteristic genericity
statement, not a single Zariski-open condition in one field.

## TL;DR

`DecoupledSystemRegular.lean` sets up `elim2`'s 12-equation decoupled
matching system (`build_decoupled_system`, `01_elim2_main.jl`) as a list of
12 elements `genList : List Rdec` in `Rdec = F[wa1,wa2,wb1,wb2,a2,a1,b2,b1,
U0,U1,V0,V1]` over `F = ZMod p` for an **arbitrary prime `p`** (no longer a
fixed numeral — see revision note above), and states the target theorem
`decoupledSystem_isRegularSequence : RingTheory.Sequence.IsRegular Rdec
genList`, now understood as a statement with free parameters `p` (prime)
and `c0,c1,c2,c3,c4 : F` (the quintic's coefficients, `f(x) = c0+c1x+c2x²+
c3x³+c4x⁴+x⁵`), true for `p` and `(c0,...,c4)` outside an explicit
exceptional locus. This is a genuinely different proof route from
advisory-6 §6.2's already-complete birationality argument (`sigma : C^(2)
-> J` generically injective) — it works directly with the 12 polynomials
rather than the geometry, and for general `p` rather than a
characteristic-0 lift at one numerically-chosen prime, so if it goes
through it closes §6.1's still-open mod-p question in full generality, not
just for one sampled prime.

**Current status (see the final progress note at the bottom for the full
audit): `theData` is fully derived and assembled, not a transcription
target and not a black box — every one of §4's construction steps (tower,
`4×4` Cramer solve, `dvd_N_u`, `uRS`/`vRS`, the Mumford identity) is proved
in `DataDerivationBasics/Tower/Solve/Mumford.lean`, all four of which are
now `sorry`-free.** The only remaining gaps are 6 named `sorry`s, all in
`DecoupledSystemRegular.lean`: four narrow lemmas with proof sketches
already written (`Ypoly`/`Epoly`/`Npoly` degree bounds,
`towerToRdec_den_ne_zero`), plus the two genuinely open structural pieces —
`regularSeq_of_peel_chain` (assembling the now-proved `curveCoeffRegular`/
`denRegular` into the full 12-step regular sequence) and
`decoupledSystem_zeroDimensional` (the formal `IsRegular → Module.Finite`
step). §5 steps 3–4's finite-quotient certificates are correctly left
*unstated* rather than `sorry`-stubbed, since stating them honestly needs
`Fu_cross`/`Fv_cross`'s closed forms, not yet extracted.

## Why a regular sequence, concretely, and why it reduces to polynomial division

For `R = k[x_1,...,x_n]` (k a field) and `f_1,...,f_n ∈ R`, "`(f_1,...,f_n)` is
a regular sequence" unfolds (Mathlib's `RingTheory.Sequence.IsWeaklyRegular`,
extended to `IsRegular` by `R/(f_1,...,f_n) ≠ 0`) to: for every `i`,
multiplication by `f_i` is injective on `R/(f_1,...,f_{i-1})`. Concretely, at
each step `i`, this is exactly the statement

    g * f_i ∈ (f_1,...,f_{i-1})  ⟹  g ∈ (f_1,...,f_{i-1})

for arbitrary `g ∈ R` — a "no new zero divisors" condition. This is where the
"bunch of polynomial divisions" intuition is exactly right: the standard way
to prove this kind of membership statement in Lean, for explicit polynomials,
is to exhibit — for the specific generators on hand — an explicit *reduction*
argument. With `k = F(c0,...,c4)`-generic and now `p`-generic too, "explicit"
means: a division witness whose non-vanishing pivot is an explicit
polynomial/integer expression in `(c0,...,c4)` and `p`, so each step's
validity condition is a concrete, inspectable exceptional set rather than an
appeal to "for all but finitely many primes" left unquantified.

1. Show `f_1,...,f_{12}` cut out a 0-dimensional variety by a **degree/Bezout
   count**: if `f_1,...,f_{12}` were NOT a system of parameters (regular
   sequence of full length `n=12`), the variety `V(f_1,...,f_{12})` would have
   positive dimension somewhere, i.e. some minimal prime of `(f_1,...,f_{12})`
   would have height `< 12`. The cleanest route for THIS system specifically
   is probably not the general Koszul-complex definition directly, but the
   sequential-elimination structure `elim2` already exploits: `Fu_decoupled`'s
   equations are literally **linear** in `U_i` (`num - U_i*den`, degree
   exactly 1 in `U_i`, coefficient `-den[i]`) and `Fv_decoupled` likewise
   linear in `V_j`. A linear (degree-1, nonzero-coefficient) generator in one
   of its variables is automatically a regular element modulo anything not
   already dividing its leading coefficient — eliminating `U_0` via its own
   equation, then `U_1`, `V_0`, `V_1` in turn, reduces the 12-variable regular-
   sequence question to an 8-variable one purely in `(wa1,wa2,wb1,wb2,a1,a2,
   b1,b2)`: **exactly the fiber-product system advisory-6 §6.2 already reduces
   to** ("the system's solution set is in bijection with the locus where
   sample 1's and sample 2's `(u_RS,v_RS)` pairs ... agree identically").
   This step is entirely generic in `p` and `(c0,...,c4)` — see §5 step 1,
   unchanged from before.
2. For the remaining 8-variable system (4 curve relations + 4
   `eliminate(Fu_decoupled/Fv_decoupled, U_i/V_j)` images), the actual content
   is advisory-6 §6.2's birationality fact, restated algebraically. A
   from-scratch regular-sequence proof here checks — generator by generator,
   in the concrete 8-variable ring — that each successive generator is a
   non-zero-divisor mod the ideal of the previous ones, via multivariate
   polynomial division (Mathlib's `MvPolynomial` division is via Gröbner
   bases, `Mathlib.RingTheory.MvPolynomial.Groebner`, or one variable at a
   time via `MvPolynomial.finSuccEquiv`/`Polynomial` induction). With
   `(c0,...,c4)` symbolic-but-fixed and `p` now ALSO symbolic-but-fixed, each
   division witness's pivot is a polynomial expression in the `c_i` — and,
   new this pass, its non-vanishing has to be understood as a condition on
   `p` too (either "pivot ≠ 0 in `ZMod p`" for the specific `p` at hand, i.e.
   `p` does not divide a certain integer coefficient, or — if the pivot
   polynomial's integer coefficients are what's being tracked — a genuine
   `p`-independent identity). This is the part that "shouldn't be too
   heinous" IF the eight polynomials are in hand with manageable
   coefficient/monomial counts, and is also now the part where "in hand"
   means "derived inside Lean" (§4), not "pasted from an Oscar dump."

## §4. `theData`: derivation, not transcription

This section replaces every previous version's "what I need from you" list
(a request to run Julia and paste output). That path is closed — see
revision note. What follows is the plan for building `theData` as an actual
Lean derivation of `symbolic_residual`'s output, ported step-by-step from
`phi_general/src/trial3_phi_symbolic_unified.jl` (uploaded this pass, so
this is no longer guesswork about what the engine does — the full
construction is now visible and summarized below).

### 4.0 What `symbolic_residual` actually does (K=2, c=2 instance)

Read straight from `trial3_phi_symbolic_unified.jl`'s `symbolic_residual`
(lines 324-550) and `_reduce_tower_elem`/`_check_mumford_identity`:

1. **Base field and function field.** `Fp = GF(p)`. Two symbolic anchors
   `t1,t2` (`= a1,a2` resp. `b1,b2` in `elim2`'s naming) live in the
   multivariate rational function field `Fp(t1,t2)` — Oscar's
   `rational_function_field(Fp, ["t1","t2"])`.
2. **Tower construction, one step per anchor.** For `i = 1,2`: form
   `f(t_i) = c0 + c1*t_i + ... + t_i^5` inside the current field `K_curr`,
   adjoin a root `w_i` of `w_i^2 - f(t_i)` via `residue_ring(K_curr[w_i],
   w_i^2 - f(t_i))`, and promote all previously-adjoined `t`/`w` variables
   into the new ring. After both steps, `K_final` is a **rank-4 free module**
   over `Fp(t1,t2)` with basis `{1,w1,w2,w1*w2}` — every element has the
   canonical form `c00 + c01*w2 + c10*w1 + c11*w1*w2` for `c_ij ∈ Fp(t1,t2)`.
3. **The `(K+2)×(K+2)` linear solve.** A Riemann-Roch basis of `K+3` monomials
   `x^i` / `x^i*y` is built (`rr_basis`), one basis element (the specific
   `(0,1)` slot, i.e. the coefficient of `y` itself) is singled out as the
   right-hand side, and a `(K+2)×(K+2)` matrix `A` over `K_final` is
   assembled from two blocks: `K` rows evaluating each remaining basis
   monomial at the `K` anchor points `(t_i, w_i)` (and the fixed numeric
   anchors, if `K > c`), plus 2 rows encoding "reduce mod the target `u(x) =
   x^2+u1*x+u0`" via a fixed lookup table (`build_xmodu_table`/
   `reduce_monomial_mod_u`, itself just iterated polynomial multiplication
   mod `u(x)` — pure integer/`Fp` arithmetic, no `t`/`w` dependence). Solved
   via `solve(A, rhs; side=:right)` — i.e. **Cramer's rule**: the solution's
   entries are `det(A_i)/det(A)` for `A_i` = `A` with column `i` replaced by
   `rhs`.
4. **Form `E(x)` and `Y(x)`.** The `K+2` solved coefficients are the
   non-`y`-coefficient RR-basis coefficients; split by whether each basis
   pair is `(i,0)` (goes into `E(x) = Σ c_i x^i`) or `(i,1)` (goes into
   `Y(x) = Σ c_i x^i`), with the singled-out `y`-coefficient itself fixed to
   `1`.
5. **Form the norm and divide out known factors.**
   `N(x) = E(x)^2 - f(x)*Y(x)^2` (this is where `F_POLY_ASC`, i.e.
   `(c0,...,c4)`, re-enters, now evaluated at the polynomial variable `x`,
   not at `t_i`). Divide `N(x)` exactly by `(x - t_1)`, `(x - t_2)` (and any
   fixed numeric anchors, not present in the `K=c=2` instance), then by the
   fixed target `u(x) = x^2+u1 x+u0`; normalize the quotient to monic — this
   is `u_RS(x)`.
6. **Compute `v_RS(x)`.** `v_RS = -E(x) * Y(x)^{-1} mod u_RS(x)`, where the
   inverse is computed either via a small (`deg ≤ 6`) linear solve
   (`_inv_mod_small`) or, as a fallback, `gcdx` (extended Euclidean
   algorithm) — algebraically the same result either way, `_inv_mod_small`
   is purely a bloat-avoidance optimization Julia-side, not a different
   mathematical object, and can be safely SKIPPED in the Lean port in favor
   of whichever of the two is easier to formalize (they're provably equal
   whenever both are defined, since both compute "the inverse of `Y(x)` mod
   `u_RS(x)`" and inverses mod a fixed polynomial are unique when they
   exist).
7. **Reduce every coefficient to lowest terms** at the base
   `Fp(t1,t2)`-fraction layer (`_reduce_tower_coeffs`/`_reduce_tower_elem`,
   i.e. `gcd`-cancel numerator/denominator of each `c_ij` component,
   recursively through the `w1,w2` tower structure).
8. **Sanity check**: `v_RS(x)^2 ≡ f(x) (mod u_RS(x))` — checked both before
   and after step 7's reduction (`_check_mumford_identity`), since
   independent per-coefficient gcd-cancellation is NOT obviously
   identity-preserving.

The output `theData` needs is exactly steps 1-7's `u_RS_coeffs`/
`v_RS_coeffs` (as elements of the tower `K_final`, restricted to the
`(0,1)`-and-`(1,1)` slots per §5's `N_U_MATCH = 2` convention), specialized
twice (once for sample "a" = `(P1,P2)`, once for sample "b" = `(P3,P4)`) with
different fixed `(u0,u1,v0,v1)` target data but the SAME symbolic `f`,
`p`-generic `Fp`.

### 4.1 Ring stack for the Lean port

Established idiom already used elsewhere in this project
(`HyperellipticFunctionField.lean`'s `CoordinateRing H := AdjoinRoot (X^2 -
C H.f)`) — reuse it here rather than inventing a new representation:

- **Base field, `p` symbolic:** `F := ZMod p` for `p : ℕ` with
  `[hp : Fact (Nat.Prime p)]` — a hypothesis threaded through every
  definition and theorem in this file from here on, replacing the current
  file's `curveP : ℕ := 2371157` / `axiom curveP_prime` numeral entirely.
  Everything downstream (`Rdec`, `theData`, `genList`, the main theorem)
  becomes universally quantified over `p`, not defined for one fixed value.
- **`t1, t2` (i.e. `a1, a2` / `b1, b2`):** live in the fraction field of
  `MvPolynomial (Fin 2) F` — i.e. `FractionRing (MvPolynomial (Fin 2) F)`.
  (Oscar's `rational_function_field(Fp, [t_i])` is exactly this; note this
  is NOT Mathlib's `RatFunc`, which is single-variable — `RatFunc` is
  `FractionRing (Polynomial F)`, one dimension short of what's needed here.
  Call this field `K0`.)
- **Tower steps, `w1` then `w2`:** `K1 := AdjoinRoot (Polynomial.X ^ 2 -
  Polynomial.C (f t1) : Polynomial K0)`, then `K2 := AdjoinRoot (Polynomial.X
  ^ 2 - Polynomial.C (f t2) : Polynomial K1)` — mirroring `residue_ring`'s
  two iterations exactly, `f` the fixed symbolic quintic
  `f(x) = c0+c1x+c2x²+c3x³+c4x⁴+x⁵` with `c0,...,c4 : F` themselves
  universally-quantified parameters (unchanged from the immediately prior
  session's framing — this part does NOT change again this pass). `K2` is
  `theData`'s home field, playing `K_final`'s role; it is a rank-4 `K0`-
  vector space by construction (`AdjoinRoot` of a monic quadratic over a
  field is always rank-2 over the base — `AdjoinRoot.powerBasis'` or the
  hyperelliptic file's own `AdjoinRoot.powerBasisAux'` usage, applied twice).
  **Irreducibility caveat, new this pass:** `AdjoinRoot`'s field/domain
  instances need `X^2 - f(t_i)` irreducible over the field at that tower
  level. For FIXED numeric `p` and `f`, Julia's `residue_ring` call just
  succeeds silently (Oscar doesn't require irreducibility to form a
  residue ring — it forms a ring either way, which is a field only if
  irreducible). For symbolic `p` and symbolic-but-fixed `c0,...,c4`, this
  is genuinely a claim to prove, not inherited for free: `X^2 - f(t_i)` is
  irreducible over `Fp(t1,...,t_{i-1})[t_i]`'s fraction field for GENERIC
  `f` because `f(t_i)` is not a perfect square in that function field
  (a transcendental `t_i` makes `f(t_i)` squarefree-in-`t_i` of odd degree
  5, hence not a square, for ANY `p` and ANY `f` with `f` non-constant —
  this should hold unconditionally, not just generically, and is worth
  proving as a clean standalone lemma early, since steps 1-8 all silently
  assume `K_final` is a field). This should be checked/proved BEFORE relying
  on `AdjoinRoot`'s field instance anywhere below — flag as new work item.
- **Polynomial ring in `x`:** `Polynomial K2`, playing `Kx`/`X`'s role.
- **The `(K+2)×(K+2) = 4×4` linear solve:** `Matrix.det`/`Matrix.adjugate`
  (or `Matrix.cramer`, which is literally named for this) over `K2`, `A :
  Matrix (Fin 4) (Fin 4) K2`. The solution's entries are
  `Matrix.cramer A rhs i / A.det` — **this determinant, as a polynomial
  expression in `c0,...,c4` and (via `Fp`'s characteristic) `p`, is exactly
  the first and most important genericity condition**: `theData` is only
  well-defined (division by a nonzero element) when `A.det ≠ 0` in `K2`,
  which unpacks to a nonvanishing condition on `(c0,...,c4,p)` that should
  be written down explicitly, not left as an unstated side condition —
  this is the natural place the "generic `(c0,...,c4)`, generic `p`"
  exceptional locus FIRST enters the construction, upstream of anything
  regular-sequence-specific in §5.

### 4.2 Suggested build order inside Lean

Unlike the prior "get me a Julia dump" plan, this has no external blocker —
it's a sequence of Lean definitions, each checkable as it's written:

1. **Squarefreeness/irreducibility lemma** (§4.1's caveat): `X^2 - f(t)` is
   irreducible over `Frac(MvPolynomial ι F)[t]`'s relevant subfield for any
   non-constant `f` and any field `F` — prove this ONCE, generically, reuse
   for both tower steps. This is a clean, small, curve-independent lemma,
   startable immediately and with no dependency on anything else here.
2. **`rr_basis`, `build_xmodu_table`, `reduce_monomial_mod_u`** (§4.0 steps 3's
   supporting combinatorics): these are pure `ℕ`/`F`-arithmetic, no tower or
   fraction-field content at all — direct, mechanical ports of the Julia
   functions of the same name, no genericity concerns, no blockers. Do these
   early as warm-up / to get the basis-indexing conventions exactly right
   before the harder matrix step.
3. **The tower, `K0 → K1 → K2`**, plus the irreducibility instance from (1)
   discharging the field instances `AdjoinRoot` needs.
4. **The `4×4` matrix `A` and `rhs`**, built from (2) and (3) exactly as
   §4.0 step 3 describes; state (don't yet prove) `hA : A.det ≠ 0` as an
   explicit hypothesis threaded into everything downstream — this is the
   FIRST piece of the eventual "generic in `(c0,...,c4,p)`" qualifier on the
   main theorem, and should be visible as a named hypothesis from here on
   rather than folded away.
5. **`E(x), Y(x)` from `Matrix.cramer`'s output**, then `N(x) = E² - f·Y²`
   (§4.0 steps 4-5).
6. **The four `divexact` steps** (`x - t1`, `x - t2`, `u(x)`) — these need
   exact divisibility, i.e. proving `(x-t_i)` and `u(x)` actually divide
   `N(x)`, which is a real mathematical fact (not automatic from the
   construction) that Julia's `divexact` just asserts/checks numerically at
   its one concrete `p`; Lean needs an actual divisibility proof here,
   generic in `p` and `(c0,...,c4)`. **This is likely the single hardest new
   step in the whole port** — flagging it now rather than discovering it
   mid-proof. Possible approach: `t_i` and the roots of `u(x)` are
   CONSTRUCTED to be roots of `N(x)` (that's what the linear system in step
   4 solved for — the anchor rows force `E(t_i)^2 = f(t_i) Y(t_i)^2`
   directly, i.e. `N(t_i) = 0` by construction, not by luck), so
   `Polynomial.dvd_iff_isRoot`-style reasoning (`X - C a ∣ p ↔ p.IsRoot a`)
   applied per-factor should turn this into "evaluate the linear system's
   defining equations at each anchor," which is closer to definitional
   unfolding than to a genuinely new computation — worth trying this angle
   before anything more exotic.
7. **`v_RS` via the mod-`u_RS` inverse** (§4.0 step 6) — use whichever of
   `_inv_mod_small`'s linear-solve or `gcdx`'s Euclidean algorithm is easier
   in Mathlib; `EuclideanDomain.gcdA`/`gcdB` exist for `Polynomial K2` (a
   Euclidean domain) and are the direct Mathlib counterpart of `gcdx` if the
   small-linear-solve route proves awkward to state generically.
8. **Reduction to lowest terms** (§4.0 step 7) — likely SKIPPABLE for the
   Lean port specifically: Julia's `_reduce_tower_coeffs` exists purely to
   keep the printed/computed polynomials small enough to be tractable to
   COMPUTE WITH numerically; Lean's kernel doesn't care about term-count
   bloat the way a numerical Gröbner/resultant computation does, so this
   step can likely be dropped from the Lean port entirely, with `theData`'s
   coefficients left as possibly-non-reduced fractions — worth confirming
   this doesn't secretly matter for §5's later steps before fully
   committing to skipping it, but it is NOT part of the mathematical
   content, only a performance optimization on the Julia side.
9. **Mumford identity check** (§4.0 step 8) — this one is NOT skippable: it's
   the actual correctness statement "`(u_RS,v_RS)` really is a point on
   `Jac(C)`'s 2-torsion-free part," i.e. a real theorem to prove
   (`v_RS^2 ≡ f mod u_RS`), following directly from how `v_RS` was
   constructed in step 7 (`_check_mumford_identity`'s Julia-side "pre-
   reduction" check should be near-definitional once step 7 is in Lean;
   skipping step 8 above removes the need for a "post-reduction" copy).

Steps 1-2 have no dependencies and can start immediately. Step 3 depends
only on 1. Steps 4-5 are mechanical once 2-3 are done. Step 6 is no longer
strategy-free: the anchor factors come from the anchor equations, while the
target factor `uT` comes from the mod-`uT` congruence plus the target Mumford
identity (§6.1 below). Steps 7 and 9 depend on 6; step 8 is optional/skippable
per the note above.

### 4.3 What this buys, and what it costs, relative to transcription

**Buys:** the eventual theorem is not contingent on Julia/Oscar's
`symbolic_residual` being bug-free — this was the explicit reason for this
pass's scope change and is worth stating plainly as the payoff. It also
makes the genericity conditions on `(c0,...,c4,p)` EXPLICIT and INSPECTABLE
(step 4's `hA : A.det ≠ 0`, step 6's divisibility facts) rather than
implicit in "well, it worked for `p=2371157` and `f=x^5+x+2`."

**Costs:** step 6 (§4.2) is real new mathematical work with no existing
Julia computation to lean on for confidence — Julia's `divexact` just calls
Oscar's `divexact`, which either succeeds (returning the quotient) or throws
at the one concrete `p` it's run at; it never establishes the general-`p`
divisibility fact this port needs, so there is no "known-true, just needs
transcribing" comfort here the way there arguably was for the rest of the
construction. Budget real time for this step specifically.

## §5. The regular-sequence steps, revised for `p` and `(c0,...,c4)` both symbolic

Steps 1-2 below are the same argument as every previous draft (they were
already generic in the curve/field, just not yet stated that way) — 3-5
are restated to make the mixed genericity (an algebraic condition in
`c0,...,c4` AND a condition on `p`, e.g. `p` avoiding a finite set of primes
dividing some fixed nonzero integer, or `p` large enough) explicit rather
than deferred.

1. **`regular_of_linear_elim`** (new, general-purpose lemma, not
   `elim2`-specific, not curve- or `p`-specific either): if `g = c - t*d` for
   a variable `t` not appearing in `c` or `d`, and `d` is a non-zero-divisor
   mod a given ideal `I` (`t` also not in `I`'s generators), then `g` is
   regular on `R/I`, AND `R/(I,g) ≅ (R minus t)/(I)` under `t ↦ c/d`-
   substitution. This lemma is stated over an ARBITRARY commutative ring
   `R` (no field, no characteristic assumption at all) — genuinely
   unaffected by this pass's changes, and startable immediately, same as
   every previous draft said.
2. Apply step 1 four times (`U0,U1,V0,V1`) to reduce
   `decoupledSystem_isRegularSequence` (12 generators, 12 variables) to an
   8-generator, 8-variable statement in `F[wa1,wa2,wb1,wb2,a1,a2,b1,b2]`
   whose generators are the 4 curve relations plus the 4 "other-sample"
   images `u2_num_d[i]*u1_den_d[i] - u1_num_d[i]*u2_den_d[i]` (and the
   `v`-analogue). Also unaffected by `p`/`(c0,...,c4)` genericity — purely
   structural, same as before.
3. **The 8-variable step**, now understood as: for `p` outside a finite
   exceptional set of primes AND `(c0,...,c4)` outside a Zariski-closed
   exceptional locus (both to be determined concretely as the division
   witnesses in this step are actually constructed — not assumed in advance),
   `[curve_a1,curve_a2,curve_b1,curve_b2, Fu_cross[0],Fu_cross[1],
   Fv_cross[0],Fv_cross[1]]` is regular in `F[wa1,wa2,wb1,wb2,a1,a2,b1,b2]`.
   Eliminate `wa1,wa2,wb1,wb2` next via a Lean port of `norm_eliminate`
   (resultant `Res_w(g, w²-f) = P² - Q²·f` for `g = P+Q·w`) — call this
   lemma `regular_of_norm_eliminate` — reducing to a 4-variable
   `(a1,a2,b1,b2)` statement. **New this pass:** `norm_eliminate`'s own
   validity (that each generator really is degree ≤1 in each `w_i`) is now
   itself a fact about `theData`'s output from §4, not a numerically-checked
   diagnostic (`01_elim2_main.jl`'s own printed check, which only ran at
   `p=2371157`) — this needs to be established as a genuine Lean lemma about
   the derivation in §4 (likely: each tower step only ever contributes
   degree ≤1 in the JUST-adjoined `w_i`, by `AdjoinRoot`'s own normal-form
   guarantee, so this may fall out of §4.1's `AdjoinRoot` representation
   almost for free — worth checking directly once §4 is built, rather than
   assumed).
4. **Final 4-variable step in `F[a1,a2,b1,b2]`.** Do NOT start by
    trying to prove four non-zero-divisor statements directly. First prove
    the geometrically equivalent finite-quotient statement: after adjoining
    the four final generators, the quotient of `F[a1,a2,b1,b2]` is
    finite-dimensional over `F` (equivalently, its Krull dimension is 0).
    The practical certificate should be a triangular polynomial-division
    witness: after a fixed variable order, produce a nonzero polynomial in
    `b2` in the ideal; modulo that polynomial produce a nonzero polynomial
    in `b1`; then similarly eliminate `a2` and `a1`. An even more direct
    certificate is a Gröbner basis whose leading monomials contain a positive
    power of each of `a1,a2,b1,b2`. Either certificate makes the quotient
    finite over `F` and therefore 0-dimensional.

    Once height `4` is established for the ideal generated by the four
    final equations, use that `F[a1,a2,b1,b2]` is a Cohen-Macaulay polynomial
    ring of dimension `4`: an ideal generated by `4` elements with height
    `4` gives a system of parameters, hence those four generators form a
    regular sequence. This is conceptually cleaner than checking the
    non-zero-divisor condition by hand at every intermediate quotient, and
    the only genuinely genus-2 computation is now the finite-quotient
    certificate.

    To keep the genericity bookkeeping concrete, clear all denominators in
    the division certificate once, over the integral coefficient ring
    `Z[c0,c1,c2,c3,c4]`. Record the finitely many coefficient polynomials
    whose nonvanishing is used by the divisions. Specialization to
    `F = ZMod p` is then valid whenever those polynomials remain nonzero;
    integer content factors give the corresponding finite exceptional set
    of primes. This produces exactly the mixed exceptional-locus statement
    promised at the beginning of §5, rather than an unexplained
    "generic" qualifier.
5. **Reassemble**: steps 1-4 give `decoupledSystem_isRegularSequence`, now
   correctly stated as a `∀ p, ∀ c0 c1 c2 c3 c4, <exceptional-locus
   hypotheses> → RingTheory.Sequence.IsRegular Rdec (genList p c0 c1 c2 c3
   c4)`-shaped theorem rather than a single unconditional fact.
   `decoupledSystem_zeroDimensional`'s Krull-dimension-0 corollary follows
   the same way as before, per-`(p,c0,...,c4)` instance satisfying the
   hypotheses.

## §6. Concrete strategies for the remaining named gaps

This section records the proof strategy for the gaps that were previously
described only as `sorry`s or "needs a strategy". None of these are executed
by this roadmap edit; the purpose is to make every remaining theorem have a
specific mathematical certificate to aim for.

### 6.1 `dvd_N_u`: use the target's Mumford congruence, not roots

Introduce a predicate or structure-level field for the target sample saying
that

    `uT ∣ (vT^2 - curvePoly)`

in `Polynomial K2`, where `uT = X^2 + u1*X + u0` and
`vT = C v0 + C v1 * X` (with the exact coefficient convention matching the
existing `Polynomial` definitions).

Separately prove from the last two rows of the `4×4` solve that

    `uT ∣ (E + Y*vT)`.

Then prove the polynomial identity

    `N = (E - Y*vT)*(E + Y*vT) + (vT^2 - curvePoly)*Y^2`.

`dvd_N_u` follows immediately by closure of divisibility under addition and
multiplication. This is preferable to proving separately that the two roots
of `uT` are roots of `N`: it uses exactly the information the matrix was
constructed to encode and works whether `uT` splits over `K2` or not.

The Lean decomposition should be:

    theorem target_mod_u_dvd : uT ∣ E + Y*vT := ...
    theorem target_mumford_dvd : uT ∣ vT^2 - curvePoly := ...
    theorem norm_identity :
      N = (E - Y*vT)*(E + Y*vT) + (vT^2 - curvePoly)*Y^2 := by ring
    theorem dvd_N_u : uT ∣ N := by
      rw [norm_identity]
      exact dvd_add (dvd_mul_of_dvd_right target_mod_u_dvd _)
        (dvd_mul_of_dvd_right target_mumford_dvd _)

The exact `dvd_mul_*` lemma names may differ with the chosen orientation;
the mathematical proof is fixed by the displayed identity.

### 6.2 The four `anchor*_defining_eq` lemmas

Do not unfold all of `Matrix.cramer` at once. Isolate a generic lemma
saying that the Cramer solution satisfies the defining linear system:

    `A.mulVec (Matrix.cramer A rhs) = rhs`

under `A.det ≠ 0`.

Then instantiate its row `0`/`row 1` components for each anchor and simplify
the matrix entries. The resulting equation is exactly

    `E(t_i) + w_i * Y(t_i) = 0`.

This turns `anchor{1,2}_defining_eq` into a matrix-interface lemma plus
normalization of the concrete row, rather than a bespoke calculation about
every coefficient.

### 6.3 `anchor*_curve_relation`

Prove once, for each tower step, the standard `AdjoinRoot` root equation

    `root^2 = f(t_i)`

inside the appropriate tower ring, then transport it through the canonical
algebra maps `K0 → K1 → K2`. In other words, do not reason about the
implementation of the quotient ideal directly after the first theorem.
The desired `K2` equation should be obtained from the `AdjoinRoot` root
specification plus simplification of the algebra maps.

This lemma is independent of the matrix and can be proved before
`anchor*_defining_eq`.

### 6.4 `u1_indep`, `u2_indep`, `v1_indep`, `v2_indep`

Treat these as a support theorem for `towerToRdec`, not as algebraic
independence in the mathematical sense.

For the sample-A output, prove that every coefficient in the numerator and
denominator has `MvPolynomial` support contained in the eight variables
belonging to sample A (and similarly for sample B). The proof should follow
the construction recursively through the tower representation:

- algebra maps preserve the old variable support;
- the newly adjoined `w_i` is eliminated by the `K2` normal form;
- numerator/denominator extraction introduces no new `MvPolynomial` variables;
- the final `uRS`/`vRS` coefficient expressions therefore remain on the
  intended side.

If the current `towerToRdec` definition is written by explicit finite sums,
a structural induction over those sums should be enough. The four theorems
should then be tiny corollaries of one generic `support_towerToRdec` lemma.

### 6.5 `MatrixNondegenerate`

Make `MatrixNondegenerate` an explicit hypothesis of `theData`, `FuList`,
`FvList`, `genList`, and the regular-sequence theorem. Do not hide it inside
a proof of a later formula.

There are then two distinct layers:

1. `MatrixNondegenerate` says the interpolation problem has the intended
   unique solution and therefore the Cramer expressions really represent
   that solution.
2. The regular-sequence theorem studies the resulting explicit generators.

Keeping those hypotheses separate prevents a false implication where
regularity is accidentally used to justify the construction that produced
the generators.

### 6.6 `IsCoprime (Ypoly) (uRS)`

Instead of trying to prove coprimality by an ad hoc case split on common
roots, use the polynomial resultant. For `uRS` of degree `2`, common-root
existence is equivalent to vanishing of the resultant

    `Res(Ypoly, uRS)`.

The coprimality hypothesis can then be recorded as `Res ≠ 0`. After clearing
denominators, the same expression supplies another explicit exceptional
hypersurface in the `(c0,...,c4)` parameters and, after specialization, a
finite set of bad characteristics coming from integer content.

This is the same "named nonvanishing certificate" pattern used for
`MatrixNondegenerate` and the final division certificate; it avoids
inventing a separate geometric argument for each occurrence of `IsCoprime`.

### 6.7 `norm_eliminate` and the four `wa/wb` variables

The correct formal target is not "run a resultant algorithm in Lean."
Prove a reusable quadratic-norm lemma:

    if `g(w) = P + Q*w` and `w^2 = f`,
    then
      `Res_w(g, w^2-f) = P^2 - Q^2*f`.

Then show that every cross-generator produced by `towerToRdec` has the form
`P+Q*w_i` in each newly adjoined variable, by the normal-form theorem for
`AdjoinRoot`. Applying the norm lemma successively eliminates `wa1`, `wa2`,
`wb1`, `wb2`.

For the regular-sequence argument, package the elimination as a quotient map
rather than as a raw equality of resultants: prove that after inverting the
same explicit nonzero norm factors, the quotient by the four quadratic
curve relations is finite/free over the four-variable base. The remaining
four equations can then be studied entirely in `F[a1,a2,b1,b2]`.

### 6.8 Final 4-variable regularity: prove 0-dimensionality first

The most important change from the earlier roadmap is methodological:

    do not prove the final regular sequence by blindly proving four
    successive non-zero-divisor statements.

Instead, build a finite-dimensionality certificate for the quotient by the
four final generators. Concretely, a Gröbner basis or sequential division
certificate should yield powers

    `a1^N1, a2^N2, b1^N3, b2^N4`

in the ideal after reductions, or equivalently leading monomials whose
positive powers involve every variable. This makes the residue ring finite
over the coefficient field, hence 0-dimensional.

Then use the Cohen-Macaulay property of the four-variable polynomial ring:
four generators of an ideal of height four form a regular sequence. This
separates the genuinely computational question ("is the final fiber finite?")
from the commutative-algebra question ("why does finite intersection imply
regular sequence?").

For Lean, this also gives a better debugging boundary. The computational
certificate can be developed first in a small standalone theorem about
`MvPolynomial (Fin 4)`, while the Cohen-Macaulay/height theorem can be
proved or located independently.

### 6.9 Mixed characteristic bookkeeping

All exceptional conditions should be accumulated in one structure rather
than propagated as unrelated hypotheses. A useful eventual interface is a
single predicate, schematically,

    `GoodData p c0 c1 c2 c3 c4 sa sb`

containing:

- `Nat.Prime p`;
- the two `MatrixNondegenerate` hypotheses;
- the two `curBeforeMonic ≠ 0` hypotheses;
- the two target/`Y` coprimality hypotheses;
- every explicit coefficient nonvanishing condition used by division;
- every target Mumford relation needed by §6.1.

Theorems upstream can expose the minimal hypotheses they actually use.
The final theorem can then assume `GoodData` without pretending that all
these nonvanishing conditions are consequences of one another.

When a certificate is computed over an integral coefficient ring, factor
out its integer content. A prime `p` is exceptional only when it kills one
of those finitely many integer factors; the remaining exceptional locus is
a finite collection of explicit polynomial equations in
`(c0,...,c4)`. This is the cleanest way to retain the symbolic-`p` claim
without accidentally assuming "large enough p" where the proof has not
shown it.

### 6.10 Updated dependency graph

With the strategies above, the previously fuzzy dependency chain is:

    target Mumford relation
        └──> target_mod_u_dvd
              └──> dvd_N_u
                    └──> uRS
                          └──> vRS (plus IsCoprime/Y-resultant hypothesis)

    MatrixNondegenerate
        └──> Cramer defining equations
              ├──> anchor divisibility
              └──> target_mod_u_dvd

    tower support theorem
        └──> u/v independence fields
              └──> DecoupledGenerators
                    └──> 8-variable generators

    AdjoinRoot normal form
        └──> norm_eliminate
              └──> 4-variable final system
                    └──> finite-quotient certificate
                          └──> height 4
                                └──> regular sequence
                                      └──> 0-dimensionality

The remaining work is therefore no longer "find a strategy for the whole
thing." It is a sequence of explicit certificates: matrix-row identities,
target Mumford congruence, support containment, resultant nonvanishing, norm
elimination, and finally a finite-quotient/height certificate.

## What is explicitly out of scope for this pass

- Actually discharging any of §4's 9 steps or §5's `sorry`s — this pass is
  the roadmap amendment only, per what was asked for; §4/§5 above are the
  plan, not yet executed.
- A specific choice of "how symbolic is `p`" beyond "arbitrary prime with no
  numeral fixed anywhere" — no attempt is made here to further restrict
  (e.g. "`p ≡ 1 mod something`") beyond what falls out of the exceptional-
  locus conditions §4/§5 actually derive as the construction proceeds.
- `decoupledSystem_zeroDimensional`'s exact final statement — still deferred
  pending the Mathlib API survey noted in prior drafts (Krull-dimension-0
  from a length-`n` regular sequence in an `n`-variable polynomial ring),
  now additionally deferred behind §4/§5 landing first.
- Re-deriving anything about `phi_general`'s combinatorial RR-basis
  selection (`rr_basis`'s specific ordering choice) — treated as a
  black-box combinatorial convention to port literally (§4.2 step 2), not
  re-justified from first principles.

## Files touched / added this pass

- This roadmap, amended in place: revision note added; TL;DR, the "why a
  regular sequence" section, and §5 (formerly the "suggested order of
  attack") revised for symbolic `p`; §4 (`theData`'s derivation plan) is
  entirely new, replacing every previous version's transcription-request
  section, now grounded in the actual `trial3_phi_symbolic_unified.jl`
  construction (uploaded and read in full this pass).
- `DecoupledSystemRegular.lean` itself NOT yet touched this pass — `curveP`/
  `curveP_prime`/`F`'s definitions still reflect the fixed-`p` version and
  need updating to match §4.1 before any of §4's derivation work can begin
  in the file itself; flagged here as the first concrete edit for the next
  session, not made yet since this pass is roadmap-only per what was asked.

## Progress note (later pass): §4.2 items 7–8 drafted, plus one un-numbered gap found

`TheDataDerivation.lean` now has a `sorry`-backed skeleton for every step
§4.2 lists (items 1–8), not just items 1–6:

- **Item 7** (`uRS`, `vRS`): `uRS` is `curBeforeMonic`'s monic
  normalization (`sorry`'d monicity lemma, `uRS_monic`, conditional on a
  `curBeforeMonic ≠ 0` hypothesis `hcur` — a genuine further exceptional-
  locus condition beyond `MatrixNondegenerate`, not yet folded into one
  combined statement). `vRS` is built via `EuclideanDomain.gcdA`/`gcdB`
  (the roadmap's own suggested route, since `_inv_mod_small` is explicitly
  skippable per §4.0 step 6), conditional on an `IsCoprime (Ypoly) (uRS)`
  hypothesis `hgcd` that is not discharged.
- **Item 8** (Mumford identity): stated as `vRS_sq_eq_f_mod_uRS`, a real
  `sorry`'d theorem (not skipped — the roadmap is explicit this one isn't
  skippable, unlike coefficient-reduction). Only the pre-reduction copy is
  stated, matching the decision (below) to drop reduction-to-lowest-terms
  entirely.
- **Reduction to lowest terms** (§4.2 item 8 / §4.0 step 7): confirmed
  droppable, not just assumed — neither `vRS` nor
  `vRS_sq_eq_f_mod_uRS` above depends on coefficients being reduced, so
  this step has no Lean counterpart at all, per the roadmap's own
  prediction.
- **A gap §4.2's numbered list doesn't name**: turning a `K2`-valued
  coefficient into the `(num, den) : Rdec × Rdec` pair `DecoupledGenerators`
  actually wants. This is `elim2.jl`'s `tower_to_ring`/
  `map_coeffs_threaded`, confirmed by reading `01_elim2_main.jl` as a
  separate step from `symbolic_residual` itself, not covered by §4.0's
  8-step numbered list (which stops at `symbolic_residual`'s own output).
  Stubbed as `towerToRdec` in a new `BridgeToRdec` section — fully
  `sorry`'d, flagged as comparable in difficulty to item 6 (a genuine change
  of ring, not an operation internal to one fixed ring). **This section
  also surfaces a live inconsistency**: `towerToRdec`'s codomain uses this
  file's symbolic `F p`, but `DecoupledSystemRegular.lean`'s `Rdec` still
  uses the fixed-`curveP` `F` — the two won't typecheck against each other
  until `DecoupledSystemRegular.lean` gets the symbolic-`p` update this
  roadmap already flagged as outstanding (previous "Files touched" note
  above). Not fixed this pass; recorded at the point it would first bite.
- **Not done this pass**: the actual assembly of a `DecoupledGenerators`
  value / replacement of `DecoupledSystemRegular.lean`'s `theData := by
  sorry`. Every ingredient now has a name and a signature in
  `TheDataDerivation.lean`, but the assembly itself lives in
  `DecoupledSystemRegular.lean` (needs `Idx`/`Rdec` imported the other
  direction) and is documented as the next concrete edit rather than made
  here, per the same "don't block structure on unfinished `sorry`s"
  approach as the rest of this file. `DecoupledSystemRegular.lean`'s
  `curveP`/`F` still need the symbolic-`p` update (previous note, still
  outstanding) before that assembly can even typecheck.
- No Lean toolchain was available to compile-check this pass's additions;
  reviewed by hand for structural/type consistency (section/namespace
  balance, matching argument lists against existing definitions) but not
  kernel-checked. Flagging this explicitly rather than implying it's been
  verified.

## Progress note (later pass): `TheDataDerivation.lean` split into four files; item 6's two anchor divisibility facts proved; `DecoupledSystemRegular.lean` updated to symbolic `p` with `theData` assembled

**File split.** `TheDataDerivation.lean` (929 lines) was split into four
files, in dependency order: `DataDerivationBasics.lean` (symbolic `F`,
`curvePoly`, item 1's irreducibility lemma, item 2's RR-basis
combinatorics), `DataDerivationTower.lean` (item 3, `K0 → K1 → K2`),
`DataDerivationSolve.lean` (items 4–6, the `4×4` solve through exact
division), `DataDerivationMumford.lean` (items 7–8 plus `BridgeToRdec`).
Each carries its own header explaining the split and its place in the
chain; all four share the `Genus2Lean.TheDataDerivation` namespace.
`DecoupledSystemRegular.lean` now imports only the fourth file. Purely
organizational — no mathematical content changed by the split itself.

**Item 6 (§4.2): the two anchor divisibility facts are now proved.**
`dvd_N_anchor1`/`dvd_N_anchor2` (in `DataDerivationSolve.lean`) are no
longer `sorry` — they follow the roadmap's own proposed angle
(`Polynomial.dvd_iff_isRoot` applied to `N(t_i) = 0`, itself following from
squaring the linear system's row-0/row-1 defining equation and substituting
the curve relation `w_i^2 = f(t_i)`) through to an actual proof term. The
argument reduces to two new lemmas per anchor:
- `anchor{1,2}_defining_eq` — the row-0/row-1 equation restated additively
  over all 5 RR-basis slots (`E(t_i) + w_i·Y(t_i) = 0`), **left as `sorry`**:
  needs `Matrix.mulVec_cramer` unfolded against `matrixA`/`rhsVec`/
  `coeffsOut`'s definitions — mechanical but not yet carried out.
- `anchor{1,2}_curve_relation` — `w_i^2 = f(t_i)` promoted into `K2`, **left
  as `sorry`**: needs `AdjoinRoot.root`'s defining property plus
  algebraMap-commutes-with-eval reasoning.

So item 6 is now 2 proved theorems + 4 smaller, individually-tractable
`sorry`s, rather than 3 opaque `sorry`s. `dvd_N_u` (target `u(x)`'s divisibility) is still a `sorry`, but the missing
strategy is now explicit. The mod-`u` rows of the linear system are intended
to establish

    E(x) + Y(x) * vT(x) ≡ 0 mod uT(x),

where `uT(x) = x^2 + u1*x + u0` and `vT(x) = v1*x + v0` are the target
Mumford data. The target specification must also provide the usual Mumford
relation

    vT(x)^2 ≡ f(x) mod uT(x).

Then, in `Polynomial K2`,

    N = E^2 - f*Y^2
      = (E^2 - vT^2*Y^2) + (vT^2 - f)*Y^2
      = (E - Y*vT)*(E + Y*vT) + (vT^2 - f)*Y^2.

The first summand is divisible by `uT` because the mod-`uT` rows give
`uT ∣ E + Y*vT`; the second is divisible by `uT` by the target Mumford
relation. Therefore `uT ∣ N`. This is the whole mathematical argument:
there is no root-by-root argument, no factorization of `N`, and no appeal to
the numerical `divexact` call.

The Lean proof should be split into three small lemmas:
1. `target_mod_u_congruence` : the two mod-`uT` matrix rows imply
   `uT ∣ E + Y*vT`;
2. `target_mumford_relation` : a field-valued target specification carries
   `uT ∣ vT^2 - f` (equivalently the remainder of `vT^2-f` modulo `uT` is
   zero);
3. `dvd_N_u` : combine (1) and (2) with the displayed algebraic identity.

This also clarifies the API boundary: `dvd_N_u` should not manufacture or
prove the target being a valid Mumford pair. That belongs in `SampleTarget`
(or a separate `IsMumfordTarget` predicate) and can be assumed by the
derivation theorem exactly where the target data are introduced. For the
actual generator assembly, those target hypotheses then become ordinary
inputs, just like `hcur` and `hgcd`.

**`DecoupledSystemRegular.lean` updated to symbolic `p`, `theData`
assembled.** Closes the "Progress note" above's two outstanding items:
- `curveP`/`curveP_prime`/fixed `F` replaced by `F (p : ℕ) := ZMod p`,
  `Rdec (p : ℕ) := MvPolynomial Idx (F p)`, threaded explicitly through
  every downstream definition (`variable (p : ℕ)`, explicit — NOT implicit,
  see caveat below). `curveF`/`curveA1..curveB2` likewise generalized from
  the fixed `x^5+x+2` to symbolic `(c0,...,c4 : F p)`, matching
  `TheDataDerivation.curvePoly`.
- `theData` (§4bis, new section) is now assembled from
  `TheDataDerivation.uRS`/`.vRS`/`.towerToRdec` rather than a bare `sorry`.
  Takes `(c0,...,c4)`, both samples' target Mumford data (`SampleTarget`,
  new structure bundling `(u0,u1,v0,v1)`), and four hypotheses `hcurA/B`
  (`curBeforeMonic ≠ 0`, needed for `uRS`) and `hgcdA/B` (the coprimality
  `vRS` needs) — inherited directly from `TheDataDerivation`'s own
  well-definedness conditions on `uRS`/`vRS`. Introduces **four new
  `sorry`s** of its own: `DecoupledGenerators`'s `u1_indep`/`u2_indep`/
  `v1_indep`/`v2_indep` fields (that `towerToRdec`'s output only involves
  the intended 4 variables per side) — plausible from `towerToRdec`'s
  construction but not proved as a lemma anywhere, new work not attempted.
  `FuList`/`FvList`/`genList`/`decoupledSystem_isRegularSequence` are now
  stated for general `(p,c0,...,c4,sa,sb)` satisfying those four hypotheses,
  not unconditionally — `decoupledSystem_isRegularSequence`'s own `sorry`
  is otherwise unchanged in substance.

**A real bug caught and fixed before finalizing**: the first draft of
§4bis declared `p` *implicit* (`variable {p : ℕ}`) while every call site
(`theData p c0 ...`, `genList p c0 ...`, etc.) passed `p` *explicitly* as a
leading argument — inconsistent, would not typecheck. Fixed by making `p`
explicit throughout (`variable (p : ℕ)`, matching `TheDataDerivation`'s own
convention and every call site already in the file). Caught by re-reading
the assembly against its call sites, not by a toolchain — flagging since
this is exactly the kind of error hand-review can miss, and did almost miss
here.

**Not done this pass**:
- `dvd_N_u` remains unproved, but its proof strategy is now explicit in
  §6.1 and no longer depends on factoring `N` or splitting `u`.
- The four new `u1_indep`-etc. `sorry`s in `theData`'s assembly; their
  support-containment strategy is recorded in §6.4.
- `MatrixNondegenerate` is not yet threaded as a hypothesis into
  `decoupledSystem_isRegularSequence`; §6.5 specifies how to make it an
  explicit construction hypothesis.
- Any of item 6/7/8's remaining `sorry`s beyond the two now discharged.
- No Lean toolchain was available this pass either — all of the above is
  hand-reviewed for structural/type consistency (including a systematic
  re-check of every call site against the `variable (p : ℕ)` explicit-vs-
  implicit question after the bug above was found), not kernel-checked.

## Progress note (current pass): status re-audited against the actual files — nearly everything above is now discharged; every remaining `sorry` lives in `DecoupledSystemRegular.lean`, none in `TheDataDerivation`

This pass did not add new mathematics. It re-read all five files against a
literal `grep sorry`, since the roadmap's own prose (including several notes
directly above) had drifted well behind the code — most "left as `sorry`"
and "not yet proved" language above describes gaps that are now closed, and
several sections still frame `theData`'s derivation as unstarted when it has
in fact been fully built out and wired up. Restating the true state plainly:

**`DataDerivationBasics.lean`, `DataDerivationMumford.lean`,
`DataDerivationSolve.lean`, `DataDerivationTower.lean` — zero live `sorry`s
among all four files.** Every occurrence of the word "sorry" left in these
four files (5, 10, 5, and 0 respectively) is prose — a docstring or comment
*reporting* that some nearby theorem is "now fully proved, no `sorry`," or
narrating the history of a gap that has since been closed. None is an actual
`sorry` term/tactic sitting in a proof. Concretely, this means:
- §4.2 items 1–8 (the tower construction, the `4×4` Cramer solve, `Epoly`/
  `Ypoly`/`Npoly`, the two anchor divisibility facts and their two supporting
  lemmas each, `dvd_N_u`'s three-lemma decomposition from §6.1,
  `uRS`/`uRS_monic`, `vRS`, and the Mumford identity `vRS_sq_eq_f_mod_uRS`)
  are now **all proved**, not sketched — including `dvd_N_u` itself, which
  the previous progress note above still lists as unproved.
- The irreducibility caveat flagged in §4.1 (`X² - f(t_i)` irreducible over
  each tower level, needed for `AdjoinRoot`'s field instance) is proved in
  full generality in `DataDerivationBasics.lean`, both the "not a square in
  the multivariate rational function field" half and the single-variable
  `RatFunc`-level half (`fAtT_not_isSquare`).
- `BridgeToRdec`'s `towerToRdec` construction (`DataDerivationMumford.lean`)
  is complete and proved, including the base case and both inductive tower
  steps (`towerToRdecK1`, then the `K1 → K2` step) — the file's own comments
  mark each piece "No `sorry`" explicitly.
- The file split described in the previous progress note (`TheDataDerivation.lean`
  → four files) is done and is exactly the four files now on disk.

The one substantive item still open in this cluster is genuinely a
`DecoupledSystemRegular.lean`-side gap, not a `TheDataDerivation`-side one:
`towerToRdec_den_ne_zero` (item below).

**`DecoupledSystemRegular.lean` — 6 live `sorry`s, all individually named
and none hidden inside a `True`-hypothesis or other disguised assumption.**
This file is also further along than the previous progress note suggests:
`theData` is fully assembled (not a bare `sorry`); `curveCoeffRegular`,
`denRegular`, `regular_of_linear_elim`, `regular_of_norm_eliminate` (and its
one-variable predecessor `regular_of_norm_eliminate_one`), the four
`*SideGens_*Gen_injective` lemmas, `uRS_coeff_ne_zero`/`vRS_coeff_ne_zero`,
and `curBeforeMonic_natDegree_eq_sub`/`_le_two` are all proved. The `Gap 2`
false-theorem episode recorded above (§ "RESOLVED as false-as-a-theorem") is
also handled correctly as designed: the two false claims were replaced by
an explicit `Nondegenerate` hypothesis rather than patched into something
still-false, and `denRegular` is proved conditional on that hypothesis. The
six actual `sorry`s remaining, by line and theorem:

1. `Ypoly_natDegree_le_zero`'s inner `have hsingle` — needs one missing
   combinatorial fact about `rrBasis5` (`rrBasis5_bj_one_unique`: no *other*
   RR-basis index besides `yIdx` has `bj = 1`); a prompt for exactly this
   lemma is already drafted (`chatgpt_prompt_ypoly_epoly.md`), not yet run.
2. `Epoly_natDegree_le_three` — stated, proof not started; the docstring
   above it already gives the intended argument (from `rrBasis5`'s literal
   top `bj = 0` entry).
3. `Npoly_natDegree_le_six` — stated, proof not started; docstring gives the
   intended `natDegree_sub_le`/`natDegree_mul_le`/`natDegree_pow_le`
   assembly from the two lemmas above plus the already-proved
   `curvePoly_natDegree`.
4. `towerToRdec_den_ne_zero` — stated, proof not started; the docstring
   gives the intended three-level induction (base case from
   `IsFractionRing.den`'s nonzero-divisor property, two inductive steps via
   `mul_ne_zero`). This is the one piece of "denominator never vanishes"
   reasoning that still lives on the `DecoupledSystemRegular.lean` side
   rather than already being finished upstream.
5. `regularSeq_of_peel_chain` — the twelve-step variable-peel induction
   assembling `curveCoeffRegular`/`denRegular` (both proved) into the full
   regular-sequence statement. Explicitly **not attempted**, flagged in its
   own docstring as new bookkeeping work rather than a corollary of the two
   proved pieces it would compose.
6. `decoupledSystem_zeroDimensional` — the formal step from `IsRegular` to
   `Module.Finite` (a length-`n` regular sequence in an `n`-variable
   polynomial ring over a field gives a nonzero Artinian quotient). Not
   started; independent of `regularSeq_of_peel_chain`'s own `sorry`.

`decoupledSystem_isRegularSequence` itself carries no `sorry` directly — it
is proved *from* `regularSeq_of_peel_chain`, so item 5 above is its only
dependency-chain gap, made visible in the proof term rather than left as an
opaque `sorry` on the main theorem.

**One item corrected, not just updated:** §5 steps 3–4's old `sorry`-stubs
(`eightVar_finiteQuotient`, `fourVar_finiteQuotient`) were *deleted*, not
filled in — they were built on a `hgens : True` placeholder standing in for
"these really are the generators §5 describes," which is flagged in the
file itself as the same failure mode as an unjustified `sorry`: it made the
statements provable without ever pinning down what they're about. The
honest state, recorded in the file's own §"5 steps 3-4: NOT YET STATEABLE"
section, is that these two steps cannot be stated as real theorems until
`Fu_cross`/`Fv_cross`'s closed forms are extracted concretely from `theData`
— tracked as a prerequisite, not swept into a hypothesis.

**Net count.** Across all five files: **6 live `sorry`s total, all in
`DecoupledSystemRegular.lean`**, versus the double-digit-per-file picture
several passages above (written progressively, pass over pass) still
suggest by only reporting what was newly closed rather than the running
total. Four of the six (1–4) are narrow, single-lemma gaps with an already-
written proof sketch in the surrounding docstring. The remaining two (5, 6)
are the genuinely open structural work: assembling the proved pieces into
the full regular-sequence theorem, and the regular-sequence-to-dimension-0
corollary.

**Still not done, unchanged from before:**
- No Lean toolchain was available this pass either. Every claim above about
  a theorem being "proved" is a literal `grep`-verified absence of a `sorry`
  token in that theorem's body, cross-checked by reading the surrounding
  docstrings' own "no `sorry`"/"fully proved" annotations — not a kernel
  check (`#print axioms` was not run). This is a stronger signal than a
  hand-reviewed structural pass but still short of compilation.
- §5 steps 3–4's finite-quotient certificates remain genuinely unstated
  (not merely unproved), pending `Fu_cross`/`Fv_cross`'s closed forms.
- `MatrixNondegenerate` (§6.5) is still not threaded as an explicit
  hypothesis anywhere in `DecoupledSystemRegular.lean`.

## Progress note (current pass): builds clean, two ChatGPT round-trips on
the assembly architecture, `regular_of_disjoint_extension` corrected from
false to true, one new lemma proved (Layer 2), one remains genuinely open

**The file builds with no errors as of this pass** (previous passes fixed
two elaboration-order/typeclass-unification errors at
`MvPolynomial.isSMulRegular_C_of_isSMulRegular`, unrelated to any `sorry`).
`sorry` count is unchanged at the surface level from the previous note (6),
but the *shape* of the remaining work changed substantially this pass, via
two rounds of ChatGPT consultation on how `regularSeq_of_peel_chain` (item
5 in the previous note) should actually be assembled. Recording the
architecture here so it doesn't need to be re-explained from scratch next
time.

### The two-round consultation, summarized

**Round 1** reviewed an early sketch of the 12-step peel induction and
recommended a four-layer architecture instead of one flat induction:

1. **Layer 1** — a single generic lemma: a polynomial over any `CommRing A`
   with `IsSMulRegular`-regular leading coefficient is itself regular
   (acting on `Polynomial A` by multiplication). Subsumes both the `Monic`
   case (curve relations, leading coeff `1`) and the linear case (`Fu`/`Fv`
   generators, leading coeff `-den`) as one-line corollaries — no
   `NoZeroDivisors`/domain hypothesis needed, and no separate lemma per
   case.
2. **Layer 2** — a quotient-transport lemma: pushes Layer 1's
   `Polynomial A`-level fact down through `MvPolynomial.optionEquivLeft`
   and `Ideal.polynomialQuotientEquivQuotientPolynomial` into the actual
   quotient ring the peel chain lives in. This is the direct
   generalization of this file's own already-proved `regular_of_linear_elim`
   (which only handled the fixed linear shape) to an arbitrary polynomial.
3. **Layer 3** — the "shape" facts: that each generator, after peeling,
   really does look like a monic/linear polynomial in the next variable
   (`quintic`/`quintic_monic` for the curve relations' quintic coefficient
   blob, `curveCoeffRegular` for the anchor-variable instantiation).
4. **Layer 4** — the finite 12-stage assembly over the fixed variable
   order, invoking Layers 1–3 at each stage.

It also flagged `MvPolynomial.finSuccEquiv`/`Fin 12` reindexing as a
cleaner alternative to this file's `{v : Idx // v ≠ x}`-subtype peeling,
but that reindexing was **not attempted** this pass (would touch working
`peelEquiv`/`peelEquivGen` machinery; flagged as a possible future
cleanup, not a blocker).

**Round 2**, after Layers 1–3 above were drafted, corrected two substantive
points in the emerging Layer-4 assembly plan:

- **`curveCoeffRegular` is likely not needed for the literal assembly.**
  Each curve relation (`curveA1` etc.) is *already* monic in its own `w`-
  variable as written — `curveCoeffRegular`'s job (showing the anchor-
  variable coefficient blob is a monic quintic) only matters if the
  intended proof strategy specifically peels the anchor variable too,
  which the literal 12-generator list doesn't require.
- **The genuinely hard gap is the repeated-target-variable problem**, not
  the curve relations. `genList`'s order is `Fu ++ Fv ++ [curveA1..B2]`
  (`Fu`/`Fv` first), and each of `U0`, `U1`, `V0`, `V1` has *two*
  generators (`d.u1_num i - Ui * d.u1_den i` and
  `d.u2_num i - Ui * d.u2_den i`). After imposing the first, the second's
  denominator regularity is needed *in the quotient*, not merely
  `≠ 0` in `Rdec p` — and the two denominators come from disjoint variable
  sets (`{wa1,wa2,a1,a2}` vs. `{wb1,wb2,b1,b2}`), sharing only the target
  variable (`U0` etc.), so this is a genuine flat-base-change situation,
  not something `regular_of_linear_elim`/Layer 2 alone can discharge.

This is exactly `regular_of_disjoint_extension`'s job, drafted the
previous pass and left `sorry`-backed — Round 2 confirmed it is real,
load-bearing work for the assembly, not a redundant lemma to skip.

### What actually got done this pass

- **Layer 2 is now proved**, not just planned: `regular_of_peeled_leadingCoeff`
  (line ~2284), built by generalizing `regular_of_linear_elim`'s own
  working transport argument (same `set I'/A/B/e` skeleton, same
  `hIdealMap`/`hsmul_mk`/`he_apply` helper steps) from the fixed linear
  shape `C c - X·C d` to an arbitrary polynomial `G : Polynomial
  (MvPolynomial τ R)`, using Layer 1 in place of the linear case's bespoke
  argument. `regular_of_linear_elim` itself was *not* rewritten as a
  corollary of this (flagged as a safe future cleanup, not attempted to
  avoid touching a working proof).
- **`regular_of_disjoint_extension` was corrected from false to true.**
  The version drafted the previous pass, over an arbitrary `[CommRing R]`,
  is FALSE — ChatGPT's counterexample (`R := ℤ`, `σ₁ = σ₂ := PUnit`,
  `g := e := 2`) is airtight: `e = 2` is regular in its own home ring, but
  after quotienting by `g = 2` the quotient has characteristic 2 and `e`'s
  image is literally `0`. The obstruction is that `MvPolynomial σ₁ R ⧸ (g)`
  need not be flat over `R` in general (`ℤ ⧸ (2)` isn't `ℤ`-flat), which
  is exactly the base-change step the lemma's proof needs. **Fix:**
  `[CommRing R]` → `[Field R]` (line ~2053). Since every module over a
  field is automatically flat, and the only `R` this file ever instantiates
  the lemma at is `F p := ZMod p` (a field, given `[Fact (Nat.Prime p)]`),
  this loses no generality actually needed here and makes the statement
  true. No call sites existed yet to break from the tightened hypothesis.
  Per project convention (weaken a false theorem rather than delete it):
  the theorem was kept and corrected, not removed.
- `regular_of_disjoint_extension`'s **proof itself is still `sorry`**
  (unchanged) — the tensor-product/base-change assembly needed
  (`MvPolynomial.algebraTensorAlgEquiv`, `IsSMulRegular.of_flat_of_isBaseChange`,
  `TensorProduct.isBaseChange`) involves several nontrivial equivalence
  compositions that were correctly identified as "needs a REPL, don't
  guess blind" per project convention. A fresh, narrowly-scoped ChatGPT
  prompt for exactly this proof (quoting the corrected `[Field R]`
  statement and the specific confirmed Mathlib lemmas to use) was drafted
  and is queued to run next — see "Next concrete step" below.

### Current inventory of `sorry`s in `DecoupledSystemRegular.lean` (7 total,
up from 6 — `regular_of_peeled_leadingCoeff` being newly proved is offset
by `regular_of_disjoint_extension` now being counted as a live, corrected
target rather than an untested draft)

Unchanged from the previous note: items 1–4 (`Ypoly_natDegree_le_zero`'s
`rrBasis5_bj_one_unique` gap, `Epoly_natDegree_le_three`,
`Npoly_natDegree_le_six`, `towerToRdec_den_ne_zero`) and item 6
(`decoupledSystem_zeroDimensional`, the `IsRegular → Module.Finite` step).

Item 5 (`regularSeq_of_peel_chain`) is now better-decomposed rather than a
single monolithic gap:
- **Layer 1** (`Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular`,
  line ~2195) — **proved**.
- **Layer 2** (`regular_of_peeled_leadingCoeff`, line ~2284) — **proved**
  this pass.
- **Layer 3 shape facts** (`quintic`/`quintic_monic`, line ~2365;
  `curveCoeffRegular`, line ~2423) — **proved**, though per Round 2 above,
  `curveCoeffRegular` specifically may turn out to be unneeded for the
  literal 12-generator assembly (kept anyway, harmless if unused).
- **`regular_of_disjoint_extension`** (line ~2053) — statement corrected
  to `[Field R]` this pass (now true), **proof still `sorry`** — the
  concrete next target, see below.
- **Layer 4, the actual 12-stage assembly** (inside
  `regularSeq_of_peel_chain`, line ~2065) — **not started**. Depends on
  `regular_of_disjoint_extension`'s proof being finished first (needed for
  the four repeated-target-variable stages `U0,U0`/`U1,U1`/`V0,V0`/`V1,V1`);
  the four curve-relation stages and the eight `Fu`/`Fv` first-generator
  stages should route through Layer 2 + Layer 1 directly, per Round 2's
  correction that `curveCoeffRegular` isn't needed there.

**Net count, current pass: 7 live `sorry`s** — the same 4 narrow
single-lemma gaps as before (1–4), the same dimension-0 corollary (6, now
listed last), `regular_of_disjoint_extension`'s proof (new: corrected
statement, proof not yet attempted), and the Layer-4 assembly itself
(`regularSeq_of_peel_chain`, unchanged in substance but now much better
scoped — three of its four stage-types have their supporting lemmas fully
proved, only the repeated-target stages are blocked on
`regular_of_disjoint_extension`).

### Next concrete step

Run this prompt (already drafted, copy verbatim) through ChatGPT with REPL
access, to get `regular_of_disjoint_extension`'s actual proof:

> I'm working in Lean 4 / Mathlib. I need to prove this theorem (now
> correctly stated over `[Field R]`, per a prior round-trip that found the
> `[CommRing R]` version false via a `ℤ`/characteristic-2 counterexample):
>
> ```lean
> theorem regular_of_disjoint_extension {R : Type*} [Field R]
>     {σ₁ σ₂ : Type*} [DecidableEq σ₁] [DecidableEq σ₂]
>     (g : MvPolynomial σ₁ R) {e : MvPolynomial σ₂ R}
>     (he : IsSMulRegular (MvPolynomial σ₂ R) e) :
>     IsSMulRegular
>       (MvPolynomial (σ₁ ⊕ σ₂) R ⧸
>         (Ideal.ofList [MvPolynomial.rename Sum.inl g] : Ideal (MvPolynomial (σ₁ ⊕ σ₂) R)))
>       (Ideal.Quotient.mk
>         (Ideal.ofList [MvPolynomial.rename Sum.inl g] : Ideal (MvPolynomial (σ₁ ⊕ σ₂) R))
>         (MvPolynomial.rename Sum.inr e)) := by
>   sorry
> ```
>
> Confirmed to exist in current Mathlib:
> - `MvPolynomial.sumAlgEquiv (R) (S₁) (S₂) : MvPolynomial (S₁ ⊕ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R)`
> - `MvPolynomial.sumAlgEquiv_comp_rename_inl`/`_inr` (their exact
>   coefficient-map/algebraMap composition forms)
> - `MvPolynomial.algebraTensorAlgEquiv R B : TensorProduct R B (MvPolynomial σ₁ R) ≃ₐ[B] MvPolynomial σ₁ B`, sending `b ⊗ₜ p ↦ b • p.map (algebraMap R B)` (`Mathlib.RingTheory.TensorProduct.MvPolynomial`)
> - `IsSMulRegular.of_flat_of_isBaseChange`, `IsSMulRegular.of_flat` (`Mathlib.RingTheory.Flat.Basic`)
> - `TensorProduct.isBaseChange (R) (M) (S) : IsBaseChange S ((TensorProduct.mk R S M) 1)`
> - Since `R` is now a `Field`, every `R`-module (in particular
>   `MvPolynomial σ₁ R ⧸ Ideal.span {g}`) is automatically `Module.Flat R`.
>
> Please give the concrete Lean 4 proof, using `algebraTensorAlgEquiv` (not
> `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`, which was tried in a
> prior round and had its `A`/`B` roles backwards for this situation) to
> identify `MvPolynomial σ₁ B ⧸ Ideal.span {ĝ}` (`ĝ := g.map (algebraMap R
> B)`, `B := MvPolynomial σ₂ R`) with `B ⊗[R] (MvPolynomial σ₁ R ⧸
> Ideal.span {g})`, then apply the flat-base-change regularity lemma.

Once that lands, Layer 4's four `U/V` repeated-target stages become
mechanical applications of `regular_of_disjoint_extension` (with the
disjointness of `{wa1,wa2,a1,a2}` vs. `{wb1,wb2,b1,b2}` already established
by `u1_indep`/`u2_indep`/etc., proved upstream), and the remaining work in
`regularSeq_of_peel_chain` is genuinely mechanical bookkeeping (routing
each of the 12 stages through the now-complete Layer 1/2/3/
`regular_of_disjoint_extension` toolkit) rather than open mathematics.

## Progress note (this pass): `regular_of_disjoint_extension` is now fully
proved, REPL-verified, no `sorry`. Different route than the queued prompt
above actually used.

The prompt drafted above (`algebraTensorAlgEquiv` route) was never run.
Instead, a fresh ChatGPT round-trip identified a materially cleaner route
via **`Algebra.TensorProduct.tensorQuotientEquiv`**
(`Mathlib.RingTheory.TensorProduct.Quotient` — confirmed to exist in
current Mathlib; NOT to be confused with the plain `TensorProduct.
tensorQuotientEquiv` in `Mathlib.LinearAlgebra.TensorProduct.Quotient`,
which is a different, weaker lemma without the algebra structure). This
lemma packages the identification directly as a quotient by an *ideal*
(`Ideal.map includeRight I`), not a `Submodule.range`, which is exactly
what's needed to compose with `Ideal.quotientEquivAlg` -- no
`Submodule.range`-equals-`Ideal.span` bookkeeping lemma was needed, unlike
every earlier draft's plan (including the `AlgebraTensorModule.
tensorQuotientEquiv` route a different ChatGPT round floated in between,
which *would* have needed exactly that bookkeeping lemma and was
correctly abandoned in favor of this one before being attempted).

**Caution for future ChatGPT round-trips on this file:** one intermediate
answer asserted a theorem `Algebra.TensorProduct.tensorQuotientEquiv` with
a signature that turned out, on independent doc verification, to be
subtly wrong in argument meaning (though the name and rough shape were
right) -- always independently verify a cited lemma's *exact* signature
against `leanprover-community.github.io/mathlib4_docs` before wiring it
into a proof; don't trust a citation on name-match alone.

Three REPL round-trips were needed to close the `sorry` once the route was
chosen, none of them mathematical -- all elaboration/direction plumbing:
1. `Algebra.TensorProduct.includeRight g` and `1 ⊗ₜ[R] g` are *defeq* but
   not syntactically `rfl`-matched by `rw`'s own trailing check; needed an
   explicit `simp [Algebra.TensorProduct.includeRight_apply]` after the
   `rw [Ideal.map_span, Set.image_singleton]` chain, not just the `rw`
   alone.
2. `Algebra.TensorProduct.tensorQuotientEquiv`'s implicit base ring `R`
   couldn't be inferred when both scalar-tower arguments (`S`, `A`) were
   instantiated to the same type `MvPolynomial σ₂ R` -- needed `(R := R)`
   supplied explicitly at the call site.
3. Two direction/composition bugs: `rw [hQ_def, ...]` broke `rw`'s motive
   (fixed via `show` with `Q` unfolded to its defeq definition instead of
   rewriting it -- `Q`'s own instances are baked into the surrounding
   `TensorProduct`/`≃ₗ` type, so `rw` can't abstract over it safely);
   `Ideal.quotientEquivAlg`'s hypothesis needed `.symm` on `hIdealMap₂`
   (its actual convention is `hIJ : J = map f I` given `I J`, matching
   this file's *existing* `Ideal.quotientEquiv` call two lines above it,
   which already used `.symm` on the same hypothesis -- a same-file
   precedent that should have been checked before drafting the new call);
   and the final `.trans` needed `hTensor.symm`, not `hTensor` bare, since
   both pieces land on `(... ⧸ J)` as their shared middle term.

**File builds clean.** `sorry` count in `DecoupledSystemRegular.lean`:
**2**, down from the previous pass's headline "7 live sorrys" narrower to
the file's own literal count (this file's own literal `sorry` tokens were
actually 3, not 7 -- the "7" in the previous progress note conflated
theorem-level *gaps* across the whole assembly, several of which had not
yet materialized as `sorry` tokens on disk, with literal remaining
`sorry`s; corrected here to avoid re-propagating the inflated count).
Remaining, both previously identified and unchanged in substance:
1. `regularSeq_of_peel_chain` -- Layer 4, the 12-stage assembly. Now
   genuinely unblocked: `regular_of_disjoint_extension`'s proof is done,
   so the four repeated-target-variable (`U0,U0`/`U1,U1`/`V0,V0`/`V1,V1`)
   stages have their supporting lemma in hand, alongside the already-
   proved Layer 1/2/3 pieces the curve-relation and first-generator
   stages route through. This is the concrete next target.
2. `decoupledSystem_zeroDimensional` -- the `IsRegular → Module.Finite`
   corollary, independent of (1), not started this pass.

## Progress note (this pass): `Nondegenerate` (`hndA`/`hndB`) propagated
through `regularSeq_of_peel_chain`, `decoupledSystem_isRegularSequence`,
`decoupledSystem_zeroDimensional` -- signature-only, no new proofs, file
still builds, `sorry` count unchanged at 2

Before attempting `regularSeq_of_peel_chain`'s actual 12-stage proof, a
blocker surfaced on inspection: `denRegular` (proved, upstream) was
updated in an EARLIER pass to require two further explicit hypotheses,
`hndA hndB : Nondegenerate ...`, beyond `hcurA/B`/`hgcdA/B` -- but that
pass's own docstring explicitly flagged ("not done yet in this pass") that
every theorem downstream of `denRegular` would need the same two
hypotheses threaded through, and that propagation had not actually
happened. Concretely: `regularSeq_of_peel_chain`'s statement, as it stood,
could not possibly discharge `denRegular`'s hypotheses even in principle,
since it had no way to produce a `Nondegenerate` witness from what it was
given -- the *statement*, not just the proof, was blocked.

Fixed this pass, mechanically, in three places:
- `regularSeq_of_peel_chain` gains `hndA`/`hndB` as new explicit arguments
  (proof still `sorry` -- untouched otherwise).
- `decoupledSystem_isRegularSequence` gains the same two arguments and now
  passes them through to its `regularSeq_of_peel_chain` call (this
  theorem's own proof term, previously complete modulo
  `regularSeq_of_peel_chain`'s `sorry`, needed the extra two arguments
  added to that call -- the only actual proof-term edit this pass, purely
  mechanical).
- `decoupledSystem_zeroDimensional` gains the same two arguments for
  signature parity, even though it doesn't yet call either of the other
  two (both still independent `sorry`s) -- done now so a future pass
  proving one of these three doesn't also need a mechanical signature
  edit on top of the real work.

No other call sites existed for any of the three (checked via `grep`), so
nothing else needed updating. `Nondegenerate`'s own definition, `uRS_coeff_
ne_zero`/`vRS_coeff_ne_zero`, and `denRegular` itself are all UNCHANGED --
this pass is pure propagation of an already-decided widening of the
exceptional locus, not new mathematical content.

**Net effect on the paper-facing claim:** `decoupledSystem_isRegularSequence`
and `decoupledSystem_zeroDimensional` now (honestly) require SIX
exceptional-locus conditions per the two samples (`hcurA/B`, `hgcdA/B`,
`hndA/B`), not four -- this is a real (if modest) narrowing of the claimed
generic locus, discovered in the `denRegular` pass and now made visible in
every downstream theorem's statement rather than silently absent from
three of the four theorems that actually need it.

### Next concrete step, still `regularSeq_of_peel_chain`'s 12-stage proof

With the signature now correct, the next pass should attempt the actual
Layer-4 assembly: route the four `Fu`/`Fv` first-generator stages and four
curve-relation stages through Layer 1 (`Polynomial.isSMulRegular_of_
leadingCoeff_isSMulRegular`) + Layer 2 (`regular_of_peeled_leadingCoeff`)
directly, and the four repeated-target-variable stages
(`U0,U0`/`U1,U1`/`V0,V0`/`V1,V1`) through `regular_of_disjoint_extension`
(now proved) using the disjointness facts already established
(`u1_indep`/`u2_indep`/etc.). **One thing to verify before assuming the
curve-relation stages are as simple as Round 2's earlier note claimed**:
`curveCoeffRegular`'s own docstring (search "What this theorem does NOT
yet establish") flags that the identification between the actual
`curveA1`/etc. coefficient blob and the abstract `quintic` shape it proves
`Monic` for is itself NOT yet established -- a short `simp`/`rename`-
unfolding lemma, per that docstring, but not written. If the curve-
relation stages route through `curveCoeffRegular` after all (Round 2's
claim that they don't needs re-checking against the literal 12-generator
list, not just re-assumed), that identification lemma is a prerequisite
worth writing first, since it's small and independently useful either way.

## Progress note (this pass): drafted the ChatGPT prompt for `regularSeq_of_peel_chain`'s actual 12-stage assembly; not attempted blind

Confirmed via re-reading (no Lean toolchain available this pass either):
`decoupledSystem_zeroDimensional`'s own `sorry` (item 2) is independent and
untouched. `regularSeq_of_peel_chain` (item 1) is exactly as scoped by the
previous pass -- Layers 1-3 and `regular_of_disjoint_extension` all proved,
`denRegular`/`Nondegenerate` in hand, only the 12-stage assembly itself
missing.

Per project convention ("if the math gets too deep, ask ChatGPT -- just
ask, don't make an elaborate md file for the ask itself, but a hard sorry
gets a queued prompt"), did NOT attempt this blind. The concrete obstacle,
confirmed by inspection rather than assumed: Layer 2
(`regular_of_peeled_leadingCoeff`) and `regular_of_disjoint_extension` are
both stated over the generic peeling shapes (`Option τ`, `σ₁ ⊕ σ₂`)
`peelEquivGen`'s own construction uses, but `Idx` here is a flat
12-constructor inductive, not syntactically an iterated `Option` or sum
type -- reaching the shape these lemmas want, at each of the 12 stages, in
the right variable-disjointness configuration (`{wa1,wa2,a1,a2}` vs.
`{wb1,wb2,b1,b2}` for the repeated-`U0`/`U1`/`V0`/`V1` stages specifically,
where the two generators sharing a target variable is itself the subtlety
`regular_of_disjoint_extension`'s "disjoint" hypothesis needs care around),
is genuine bookkeeping work this project's own rule flags as REPL-territory,
not something to guess at from a written description of the pieces alone.

Drafted `chatgpt_prompt_peel_chain_assembly.md`: quotes every already-proved
piece the assembly would use verbatim (Layer 1, Layer 2,
`regular_of_linear_elim`, `regular_of_disjoint_extension`, `denRegular`,
the curve relations' monic-in-own-variable shape, `IsRegular.cons`/
`isRegular_cons_iff`/`IsRegular.nil`), states `regularSeq_of_peel_chain`'s
exact target, and asks five specific composition questions: (1) how to
bridge `Idx`'s flat-inductive shape to the `Option`/`⊕` shape Layers 2 and
`regular_of_disjoint_extension` want at each stage, or whether those lemmas
should instead be restated directly in terms of `Ideal.ofList (g :: gs)`-
quotient-of-quotient reasoning to avoid the bridge entirely; (2) the four
"simple" `Fu0`/`Fu2`/`Fv0`/`Fv2` first-generator-per-target stages; (3) the
four "repeated-target" `Fu1`/`Fu3`/`Fv1`/`Fv3` stages and precisely how
`regular_of_disjoint_extension` applies when the shared target variable
(`U0` etc.) is exactly the one variable that ISN'T disjoint between the two
sides; (4) the four curve-relation stages, confirming they're the easiest
(monic degree-2, leading coeff `1`) and flagging the late-stage peel-order
question; (5) the final 12-fold `IsRegular.cons` chain plus the
`Nontrivial (QuotSMulTop ...)` side conditions `IsRegular.nil` needs 12
quotients deep.

**Not run yet.** `regularSeq_of_peel_chain`'s `sorry` is unchanged in
substance; a comment above it in `DecoupledSystemRegular.lean` now points
at the prompt file rather than leaving the "next step" only in this
roadmap. File still builds (comment-only change at the one `sorry` site,
no proof-term edits). `sorry` count unchanged at 2.

### Next concrete step

Run `chatgpt_prompt_peel_chain_assembly.md` (Claire, via her own REPL/
ChatGPT access) and report back the answer for wiring into
`regularSeq_of_peel_chain`. `decoupledSystem_zeroDimensional` remains a
fully independent second target, not started.

## Progress note (this pass): ChatGPT's answer on `regularSeq_of_peel_chain`'s 12-stage assembly is back — found a REAL counterexample, not just an API gap. Paper-level finding, not acted on in the file yet.

Ran `chatgpt_prompt_peel_chain_assembly.md`. Result, confirmed by
independent inspection of the file (not taken on faith):

**8 of 12 stages are routine**, per ChatGPT's guidance (not yet wired in,
but no obstruction found):
- The 4 "first generator per target" stages (`Fu0`, `Fu2`, `Fv0`, `Fv2` —
  i.e. the first of the two generators introduced for each of `U0,U1,V0,V1`
  respectively) go through Layer 1 + Layer 2 directly, using `denRegular`'s
  nonvanishing-in-`Rdec p` fact converted to coefficient-ring regularity via
  domain-ness (`Rdec p` a domain since `F p` is a field).
- The 4 curve-relation stages (`curveA1/A2/B1/B2`) go through Layer 1 + 2
  with leading coefficient `1` (trivially regular) — no repeated-target
  issue reaches them since none of the 8 `Fu`/`Fv` generators contain any
  `w`-variable.
- The `Idx`-vs-`Option τ` bridge these both need doesn't require an
  iterated-`Option` tower or `Idx ≃ Fin 12` — a per-target equivalence
  `Option {j : Idx // j ≠ w} ≃ Idx` suffices, and the final 12-fold
  assembly should use `RingTheory.Sequence.isRegular_append_iff'`/
  `IsRegular.cons'` (native prefix-quotient bookkeeping) rather than manual
  `QuotSMulTop`-vs-`Ideal.ofList` equivalence-chasing.

**The 4 "repeated-target" stages are genuinely NOT provable as currently
hypothesized** (`Fu1`, `Fu3`, `Fv1`, `Fv3` — the SECOND generator for each
of `U0,U1,V0,V1`, e.g. `Fu1 := d.u2_num i - Uk*d.u2_den i` needing to be
regular in the quotient by the already-imposed `Fu0 := d.u1_num i -
Uk*d.u1_den i`). ChatGPT's counterexample, hand-verified: in `k[a,b,U]`,
`Fu0 := a*(1-U)`, `Fu1 := b*(1-U)`. Both "denominators" `a`, `b` are
nonzero and live in disjoint variable sets — exactly matching what
`denRegular` + `u1_indep`/`u2_indep` give us — yet `a*Fu1 = a*b*(1-U) =
b*Fu0` already in the ambient ring, so `a*Fu1 = 0` in the quotient by `Fu0`
while `a ≠ 0` there: `Fu1` is a zero-divisor, not regular.
`regular_of_disjoint_extension` cannot discharge this stage — its
disjointness hypothesis is about `g`'s and `e`'s variable sets, but `Fu0`
and `Fu1` share the SAME target variable `Uk`, which is exactly the
non-disjoint part.

Checked independently (not just trusting ChatGPT): confirmed no resultant/
coprimality identity linking A-side (`u1_num/u1_den`) and B-side
(`u2_num/u2_den`) data exists anywhere in the file — `theData` builds them
via two fully independent `coeffsToNumDen` calls on `sa`/`sb`, related only
by sharing the same symbolic curve `(c0,...,c4)`. So the gap is real, not
an oversight.

**What would close it** (per ChatGPT, not built): the identity `d₁*Fu1 -
d₂*Fu0 = d₁*c₂ - d₂*c₁` reduces "`Fu1` regular mod `Fu0`" to "the
resultant-like combination `d₁*c₂ - d₂*c₁` is regular mod `Fu0`" — which
needs a genuinely NEW hypothesis about the actual Mumford-divisor num/den
data (an exceptional-locus nonvanishing condition), not derivable from
anything currently proved.

**Not acted on in the file this pass.** Per project convention ("if we
find a false theorem, we try to weaken it first, then delete") -- this
theorem is not weakened yet, because whether a resultant-nonvanishing
condition is actually generically true for `elim2`'s real Mumford data is
a question about the paper's own math, not something to guess at in Lean.
`regularSeq_of_peel_chain`'s `sorry`-site comment updated with the full
finding (counterexample included) so this is visible in-file, not just in
this roadmap. `chatgpt_reply_peel_chain_assembly.md` added alongside the
prompt file as a saved summary. File still builds (comment-only change).
`sorry` count unchanged at 2.

### Next concrete step

Not a Lean task: determine (Claire / re-derivation from the paper) whether
a resultant-nonvanishing condition between the A-side and B-side Mumford
data is actually generically true for `elim2`'s real data. If yes, add it
as a new `Nondegenerate`-style hypothesis field (same shape as the earlier
`Nondegenerate` fix) and wire the 8 easy stages + this new stage together.
If it's NOT generically true, `decoupledSystem_isRegularSequence` itself
needs to be weakened or the paper's own claim revisited -- this is above
the Lean formalization's pay grade to resolve alone.
