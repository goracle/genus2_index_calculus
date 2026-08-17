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
exceptional locus. Both the theorem and `theData` (now a *derivation*, not
a transcription target — §4) are `sorry`. This is a genuinely different
proof route from advisory-6 §6.2's already-complete birationality argument
(`sigma : C^(2) -> J` generically injective) — it works directly with the
12 polynomials rather than the geometry, and for general `p` rather than a
characteristic-0 lift at one numerically-chosen prime, so if it goes
through it closes §6.1's still-open mod-p question in full generality, not
just for one sampled prime.

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
only on 1. Steps 4-5 are mechanical once 2-3 are done. Step 6 is the
genuine open problem in this list. Steps 7 and 9 depend on 6; step 8 is
optional/skippable per the note above.

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
4. **Final 4-variable step in `F[a1,a2,b1,b2]`.** This is where genus-2-
   specific content actually has to close the argument, and where the
   `(c0,...,c4)`-genericity conditions from step 3 need to be assembled into
   a single explicit statement — e.g. "regular for all `(c0,...,c4)` outside
   the union of finitely many explicit hypersurfaces `{h_j(c0,...,c4) = 0}`,
   and all primes `p` not dividing any of finitely many explicit nonzero
   integers arising as denominators/discriminants along the way." Concrete
   Gröbner-basis / division-witness computation on the now much smaller
   polynomials, once §4 makes them available as actual Lean terms rather
   than opaque Julia output.
5. **Reassemble**: steps 1-4 give `decoupledSystem_isRegularSequence`, now
   correctly stated as a `∀ p, ∀ c0 c1 c2 c3 c4, <exceptional-locus
   hypotheses> → RingTheory.Sequence.IsRegular Rdec (genList p c0 c1 c2 c3
   c4)`-shaped theorem rather than a single unconditional fact.
   `decoupledSystem_zeroDimensional`'s Krull-dimension-0 corollary follows
   the same way as before, per-`(p,c0,...,c4)` instance satisfying the
   hypotheses.

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
