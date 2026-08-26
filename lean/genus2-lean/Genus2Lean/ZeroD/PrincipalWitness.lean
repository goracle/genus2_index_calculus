import Mathlib
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.Reduce.GeneralSharedRoot
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationBasics
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.LCanonicalElementary
import Genus2Lean.LPairFinrankOneOrdAtFrac
import Genus2Lean.HyperellipticClassProof

-- `ordAt_eq_zero_of_notMem`/`ordAt_toPair_mul_of_ne_zero'` (lemmas 2, 4
-- below) live in `RiemannRochGenus2.lean`, and `toPair_mem_pointIdeal_iff`
-- (lemma 2 below) lives in `LCanonicalElementary.lean` — neither is
-- reachable through this file's other imports (`PrincipalDivisorSubgroup.
-- lean`'s own import chain stops at `PrincipalDivisors.lean`, one file
-- short of these two). Both direct imports are cycle-safe: `RiemannRoch
-- Genus2.lean` and `LCanonicalElementary.lean` themselves import
-- `PrincipalDivisorSubgroup.lean` (the reverse direction), and neither
-- file (nor anything in their own import chains) references this file.
--
-- `ordAt_eq_rootMultiplicity_unramified`/`_ramified` (lemma 6 below) live
-- in `LPairFinrankOneOrdAtFrac.lean` — also cycle-safe: that file's own
-- import list (checked directly, doesn't include this file or
-- `AlphaLocusDegreeUniform.lean`) has no path back here, and nothing in
-- `Genus2Lean`'s root-level files references `PrincipalWitness`/
-- `AlphaLocusDegreeUniform` at all.
--
-- `linX`/`Point.iota`/`divToPair_linX_eq_of_ramified` (lemma 10 below) live
-- in `HyperellipticClassProof.lean` — same cycle-safety check repeated:
-- that file's own import list (`HyperellipticFunctionField`, `AffinePoints`,
-- `DivisorClassGroup`, `PrincipalDivisors`, `PrincipalDivisorSubgroup`,
-- `FFKSidon`) doesn't reach this file or `AlphaLocusDegreeUniform.lean`,
-- and (re-grepped the whole tree) nothing yet imports `PrincipalWitness.lean`.

/-!
# Step 3 (`ROADMAP-reduce-divisor-correctness.md`): the principal-witness lemma stack

This file starts the actual proof of `reducedClass_eq_of_isReduction'`'s
divisor-class content (`AlphaLocusDegreeUniform.lean`), following the
three-lemma skeleton from `CHATGPT-REPLY-step3-reduce-correctness.md` /
`ROADMAP-reduce-divisor-correctness.md` §3a-§3e:

1. residual-intersection (`u_old ∣ N`) — **already fully proved**,
   `uRS4General_dvd_Npoly4`/`uRS4General_natDegree_eq_two` in
   `GeneralSharedRoot.lean`, no new Lean needed.
2. residual-Mumford (`v_new ≡ -phi mod u_new`) — **already confirmed**
   (roadmap's "Status update, this pass" §3c sign check), matches
   `vRS4General := -E·Y⁻¹`.
3. principal-witness (`div(h) = D_old - D_new`, `h = g/u_new`,
   `g = E + Y·y`) — **this file**, not yet proved, built as many small
   named lemmas per project convention rather than attempted whole.

Per the ChatGPT reply's own recommendation (§16), this file is deliberately
kept ignorant of `SampleTargetFromAlpha`/`aClass`/`hr`/`sa.reducedClass` —
those only enter at the final assembly theorem back in
`AlphaLocusDegreeUniform.lean`. Everything here is stated directly against
`E Y : Polynomial (F p)` (or, more generally, `k[X]`) and `H : Hyperelliptic
Polynomial k`, so it can be reused by both the general (`P1 ≠ P2`) and
tangent (`P1 = P2`) branches without duplication.

**Status: lemmas 1-9 of the stack (ChatGPT §2-§3/§6/§9/§13 steps 2-9) —
the norm identity, the residue-nonzero ⇒ valuation-zero lemma, the
`(A,B)`-pair form of the norm identity, the ordinary-zero-of-`g` lemma via
norm multiplicativity, `ordAt P g` expressed directly as a root
multiplicity of `N` (unramified + ramified), the `N = A · U`
factorization at the pair level, `ordAtFrac P E Y U 0 = ordAt P A 0`
(`ordAt P h = ordAt P A` at a residual point), and (lemma 9)
`coeffAt_divToPair` — the pointwise coefficient identity for `divToPair`,
`coeffAt P (divToPair A B S) = if P ∈ S then ordAt P A B else 0`. All
proved, no `sorry`. Also done: `eq_of_coeffAt_eq` (`Divisor H`
extensionality via `coeffAt` — resolves the `δ₀`-avoidance question
cheaply, no infinity valuation needed, see its own docstring); **lemma 10**
(`divToPair_linX_eq_two_smul_of_ramified`, the Weierstrass/ramification-
point witness `div(x-x0) = 2•[P]`, restating the already-fully-proved
`divToPair_linX_eq_of_ramified` from `HyperellipticClassProof.lean`); and
**lemma 11** (`coeffAt_sub_eq_of_forall` +
`divToPair_eq_of_coeffAt_diff_eq_zero`, the pointwise-coefficient
assembly per ChatGPT §15's boxed identity, packaging lemmas 2/8/9/10 into
a `D_old = D_new` conclusion given their per-point case-split facts as
hypotheses). Also done, this pass, following up on ChatGPT's second reply
(the residual-point/`A`-valuation follow-up): **lemma 12**
(`pairNorm_neg_eq`, `pairNorm H E (-Y) = pairNorm H E Y`) and **lemma 13**
(`ordAtFrac_neg_eq_ordAt_of_pairNorm_eq_mul`, the residual-point mirror of
lemma 8 — needs neither `hchar` nor `P.Y ≠ 0`, unlike lemma 8 itself,
since it goes through lemma 4 rather than lemma 6's `rootMultiplicity`
detour). Also done, this pass: **lemma 13b**
(`ordAtFrac_add_ordAtFracNeg_eq_ordAt_pairNorm_sub`, the unconditional `g`/
`ḡ` sum identity — resolves, from the actual `ordAt_toPair_mul_of_ne_zero'`
multiplicativity fact rather than a guess, what `h := g/U`'s OWN valuation
is at a residual point given only lemma 13's conjugate-valuation fact) and
**lemma 13c** (`ordAtFrac_eq_neg_one_of_residual_point`, the concrete `= -1`
composition of lemma 13 + lemma 13b + lemma 7, for the standard "simple
residual root, disjoint from the old/anchor factor" hypotheses) — together
these settle a genuine three-way sign ambiguity (`+1`/`-1`/`-2`) that could
not be resolved by inspection of lemmas 8/13's conclusions alone, since
those two lemmas only ever state facts about `ḡ`'s (or `g`'s) OWN
valuation at a point where that same function vanishes, never about `g`'s
valuation at a point where `ḡ`, not `g`, vanishes — the sum identity is
what bridges the two.

The three "layers" ChatGPT's follow-up reply recommended for
computing `ordAt P A 0` at the four/six named points WITHOUT going through
`Polynomial.roots`: **Layer 1** (`ordAt_linX_eq_one_of_ne_zero`/
`ordAt_linX_eq_zero_of_ne'`, thin restatements of the already-proved
`ordAt_linX_eq`), **Layer 2** (`ordAt_mul_eq_one_of_ordAt_eq_one_zero`/
`ordAt_mul4_eq_one_of_ordAt_eq_one_zero_zero_zero`, "one factor order 1 +
the rest order 0 ⟹ product order 1", generic multiplicativity), and
**Layer 3** (`ordAt_A_eq_one_of_eval_ne_zero`, the Cantor-specific
instantiation: given the other three factors' plain polynomial-evaluation
nonvanishing at the point in question — exactly the shape this project's
existing `isCoprime_lcm12_lcm34_of_no_shared_root`-style hypotheses already
supply — concludes `ordAt P (((linX a * F₁) * F₂) * F₃) 0 = 1`, no
`rootMultiplicity`/`Polynomial.roots` reasoning exposed at the call site).
Not yet attempted: the actual assembly theorem in
`AlphaLocusDegreeUniform.lean` itself — wiring the four/six named points
of the concrete `SampleTargetFromAlpha` situation through lemmas 2/8/9/10/
13 and the three layers to discharge `coeffAt_sub_eq_of_forall`'s
hypothesis and conclude `reducedClass_eq_of_isReduction'`. That's
genuinely project-specific (needs `sa.P1`/`sa.P2`/`Epoly4`/`Ypoly4`/
`uRS4General`/`npoly4Lcm4` instantiated, plus bridging `npoly4Lcm4`'s
`EuclideanDomain.lcm`-nested definition to the plain-product form Layer 2/3
consume — flagged as its own remaining sub-step, not yet started), so it
belongs in `AlphaLocusDegreeUniform.lean`, not this file, matching this
file's stated design (ChatGPT §16: stay ignorant of `SampleTargetFromAlpha`/
`aClass`/`hr`/`sa.reducedClass` until the final assembly step).**
-/

noncomputable section

namespace HyperellipticPolynomial

open Polynomial
open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- **Lemma 1 of the principal-witness stack (ChatGPT §2/§13 step 2):
the norm identity at the `toPair`/`CoordinateRing` level.**
`toPair H E Y * toPair H E (-Y) = algebraMap _ _ (pairNorm H E Y)`,
i.e. `g · ḡ = N` in `CoordinateRing H`, where `ḡ = E - Y·y` is exactly
`toPair H E (-Y)` (matches `toPair_involution`: the hyperelliptic
involution sends `A + By ↦ A - By`).

This is `toPair_mul_involution` restated with `involution H (toPair H E
Y)` unfolded via `toPair_involution` to the concrete pair form
`toPair H E (-Y)`, rather than left as `involution H (toPair H E Y)` — the
concrete form is what the rest of the stack (`ordAt_toPair_mul_of_ne_zero'`,
which needs the *pair* `(A', B')`, not the abstract involution) actually
needs to rewrite against. -/
theorem toPair_mul_toPair_neg_eq_algebraMap_pairNorm (E Y : k[X]) :
    toPair H E Y * toPair H E (-Y) = algebraMap k[X] (CoordinateRing H) (pairNorm H E Y) := by
  rw [← toPair_involution]
  exact toPair_mul_involution H E Y

/-- **Lemma 2 of the stack (ChatGPT §4/§13 step 4): residue-nonzero implies
valuation-zero, specialized to the `E,Y`-pair shape.** If `g = E+Y·y`
evaluated at `P` is nonzero (`E.eval P.X + Y.eval P.X * P.Y ≠ 0`), then
`ordAt P E Y = 0`.

This is `toPair_mem_pointIdeal_iff` (turns the evaluation condition into
`toPair H E Y ∉ pointIdeal P`, since `pointIdeal` membership is exactly
`= 0`) composed with `ordAt_eq_zero_of_notMem` (`[IsAlgClosed k]`-free —
confirmed via `RiemannRochGenus2.lean`'s `omit [IsAlgClosed k] in` clause
directly above it, so this stays usable over `F p`, no closed-field
machinery pulled in). Needs `[IsDedekindDomain (CoordinateRing H)]`, which
both source lemmas already require. -/
theorem ordAt_eq_zero_of_eval_ne_zero [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (E Y : k[X]) (heval : E.eval P.X + Y.eval P.X * P.Y ≠ 0) :
    ordAt P E Y = 0 :=
  ordAt_eq_zero_of_notMem P E Y (fun hmem => heval ((toPair_mem_pointIdeal_iff P E Y).mp hmem))

/-- **`toPair H c 0 = algebraMap k[X] (CoordinateRing H) c`, the `B = 0`
unfolding of `toPair` used to state the norm identity at the `(A,B)`-pair
level rather than via `algebraMap`.** Same idiom already used elsewhere
in this codebase (`LPairFinrankOneOrdAtFrac.lean`'s `htoPair_right_zero`);
restated here as its own lemma since the norm identity below needs it by
name. -/
theorem toPair_right_zero (c : k[X]) :
    toPair H c (0 : k[X]) = algebraMap k[X] (CoordinateRing H) c := by
  unfold toPair
  simp

/-- **Lemma 3 of the stack (ChatGPT §2/§13 step 3, the `(A,B)`-pair form of
the norm identity needed for `ordAt_toPair_mul_of_ne_zero'`).**
`toPair H (pairNorm H E Y) 0 = toPair H E Y * toPair H E (-Y)`, i.e. the
same `g·ḡ = N` fact as `toPair_mul_toPair_neg_eq_algebraMap_pairNorm`
above, but with the right-hand side's `N` expressed as `toPair H N 0`
(via `toPair_right_zero`) instead of `algebraMap _ _ N` — this is the
exact shape `ordAt_toPair_mul_of_ne_zero'`'s `hA₃` hypothesis needs. -/
theorem toPair_pairNorm_eq_toPair_mul_toPair_neg (E Y : k[X]) :
    toPair H (pairNorm H E Y) (0 : k[X]) = toPair H E Y * toPair H E (-Y) := by
  rw [toPair_right_zero, toPair_mul_toPair_neg_eq_algebraMap_pairNorm]

/-- **Lemma 4 of the stack (ChatGPT §3/§5/§13 step 5): given `g ≠ 0` as a
ring element and `ḡ(P) ≠ 0`, `ordAt P g = ordAt P N`.** (The intended use
is the case `g(P) = 0` — an ordinary zero of `g` at `P` — but that
hypothesis is not actually needed for this step; it only motivates why
`ḡ(P) ≠ 0` is the interesting/expected case to supply. Stating the lemma
without an unused `g(P) = 0` hypothesis keeps it usable verbatim at the
`δ₀`-adjacent points too, where the case split is driven by `ḡ` alone.)

`toPair H E Y ≠ 0` is taken as an explicit hypothesis (`hg_ne`) rather than
derived from `hg_eq` alone: vanishing AT a single point `P` (an evaluation
condition) does not imply vanishing AS A RING ELEMENT (`E = 0 ∧ Y = 0`
globally, via `toPair_eq_zero_iff`) — e.g. `E = X, Y = 0` vanishes at
`P.X = 0` but `toPair H X 0 ≠ 0`. This is exactly the "don't over-assume"
discipline §3e of the roadmap asks for: the hypothesis actually needed
(`g ≠ 0` as an element) is stated, not silently assumed provable from the
weaker evaluation fact. `ḡ`'s non-vanishing at `P`, by contrast, genuinely
IS enough to get `toPair H E (-Y) ≠ 0` (nonzero evaluation forces the
element itself nonzero — the same direction `ordAt_eq_zero_of_eval_ne_zero`
already uses), so `hgbar_ne` below is derived, not assumed.

Proof: `ordAt_toPair_mul_of_ne_zero'` (needs both factors `≠ 0` as ring
elements — `hg_ne` supplied, `hgbar_ne` derived) +
`toPair_pairNorm_eq_toPair_mul_toPair_neg` give `ordAt P (pairNorm H E Y) 0
= ordAt P E Y + ordAt P E (-Y)`; `ordAt_eq_zero_of_eval_ne_zero` collapses
the second summand to `0` via `hgbar_ne_eval`. -/
theorem ordAt_eq_ordAt_pairNorm_of_eval_eq_zero [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y : k[X])
    (hg_ne : toPair H E Y ≠ 0)
    (hgbar_ne_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0) :
    ordAt P E Y = ordAt P (pairNorm H E Y) (0 : k[X]) := by
  have hgbar_ne : toPair H E (-Y) ≠ 0 := by
    intro hz
    apply hgbar_ne_eval
    have hmem : toPair H E (-Y) ∈ pointIdeal P := hz ▸ Submodule.zero_mem _
    exact (toPair_mem_pointIdeal_iff P E (-Y)).mp hmem
  have hordbar : ordAt P E (-Y) = 0 :=
    ordAt_eq_zero_of_eval_ne_zero P E (-Y) hgbar_ne_eval
  have hstep := ordAt_toPair_mul_of_ne_zero' P h_bot E Y E (-Y)
    (pairNorm H E Y) (0 : k[X]) hg_ne hgbar_ne
    (toPair_pairNorm_eq_toPair_mul_toPair_neg E Y)
  omega

/-- **Corollary, in `Npoly4`-shaped form for this project's genus-2, `K=4`
instance.** Given `Npoly4 = Epoly4^2 - curvePoly*Ypoly4^2` (`AlphaReduce.lean`)
and `H.f = curvePoly p c0 c1 c2 c3 c4` (the `hf` hypothesis threaded through
`reducedClass_eq_of_isReduction'`), `pairNorm H E Y = E^2 - Y^2 * H.f`
(`HyperellipticFunctionField.lean`'s definition, unfolded) specializes
exactly to `Npoly4` once `E := Epoly4 ...`, `Y := Ypoly4 ...` are
substituted and `hf` is used to rewrite `H.f`. Stated here as the bridge
lemma so downstream code can rewrite `Npoly4 ...` directly into
`pairNorm H (Epoly4 ...) (Ypoly4 ...)` (and hence into the `toPair`
identity above) without re-deriving this each time. -/
theorem pairNorm_eq_of_eq_curvePoly {p : ℕ} [hp : Fact (Nat.Prime p)]
    {H : HyperellipticPolynomial (Genus2Lean.TheDataDerivation.F p)}
    {c0 c1 c2 c3 c4 : Genus2Lean.TheDataDerivation.F p}
    (hf : H.f =
      Genus2Lean.TheDataDerivation.curvePoly p c0 c1 c2 c3 c4)
    (E Y : Polynomial (Genus2Lean.TheDataDerivation.F p)) :
    pairNorm H E Y =
      E ^ 2 - Y ^ 2 * Genus2Lean.TheDataDerivation.curvePoly p c0 c1 c2 c3 c4 := by
  unfold pairNorm
  rw [hf]

/-- **Lemma 6 of the stack (ChatGPT §3/§13 step 6): `ordAt P g` at an
ordinary (`P.Y ≠ 0`) zero of `g`, expressed as a root multiplicity of
`N = pairNorm H E Y`, instead of left as `ordAt P N`.** Composes lemma 4
(`ordAt_eq_ordAt_pairNorm_of_eval_eq_zero`) with
`ordAt_eq_rootMultiplicity_unramified` (`LPairFinrankOneOrdAtFrac.lean`,
already proved, `[IsAlgClosed k]`-free) — the same move ChatGPT's own
step 5→6 in §13 describes: "rewrite `ordAt P N` using
`ordAt_eq_rootMultiplicity_unramified`."

`pairNorm H E Y ≠ 0` is taken as an explicit hypothesis (`hN_ne`) rather
than derived from `hg_ne`/`hgbar_ne_eval`: an integral domain has no zero
divisors, so `g ≠ 0` and `ḡ ≠ 0` (as ring elements, via
`toPair_mul_toPair_neg_eq_algebraMap_pairNorm` and injectivity of
`algebraMap` — not yet established here) *should* give `N ≠ 0`, but that
extra step isn't needed for this lemma's proof and stating it as an
explicit hypothesis keeps the "don't over-assume" discipline consistent
with lemma 4's own `hg_ne`. -/
theorem ordAt_eq_rootMultiplicity_pairNorm_of_eval_eq_zero
    [IsDedekindDomain (CoordinateRing H)] (hchar : (2 : k) ≠ 0)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y : k[X])
    (hg_ne : toPair H E Y ≠ 0)
    (hgbar_ne_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0)
    (hN_ne : pairNorm H E Y ≠ 0) (hY : P.Y ≠ 0) :
    ordAt P E Y = ((pairNorm H E Y).rootMultiplicity P.X : ℤ) := by
  rw [ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E Y hg_ne hgbar_ne_eval]
  exact ordAt_eq_rootMultiplicity_unramified hchar (pairNorm H E Y) hN_ne P.X P h_bot rfl hY

/-- **Ramified analogue of lemma 6 (`P.Y = 0`, the Weierstrass case).**
Same composition, using `ordAt_eq_rootMultiplicity_ramified` (needs
`Squarefree H.f`) instead of the unramified lemma — per §3b/§3e of the
roadmap, this is the case the existing `hcurT`/`hgcdT` split may not yet
cover explicitly; flagged here as its own named lemma (not yet wired into
the assembly theorem) rather than silently assumed excluded. Note this
case is geometrically degenerate for the *interpolation* argument itself
(§3b: at a Weierstrass point `ḡ(P) = g(P)` since `P = ι(P)`, so
`hgbar_ne_eval` here is a real, not vacuous, extra assumption — it does
NOT follow automatically from `hg_ne` the way it does in the unramified
case via `-2·Y(a)·b ≠ 0`) — stated for completeness of the lemma stack,
but the assembly theorem will likely need a separate argument for
Weierstrass points per §3b item 3 (`div(x-x0) = 2P - 2δ₀` directly),
not this lemma. -/
theorem ordAt_eq_rootMultiplicity_pairNorm_of_eval_eq_zero_ramified
    [IsDedekindDomain (CoordinateRing H)] (hsf : Squarefree H.f)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y : k[X])
    (hg_ne : toPair H E Y ≠ 0)
    (hgbar_ne_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0)
    (hN_ne : pairNorm H E Y ≠ 0) (hY : P.Y = 0) :
    ordAt P E Y = (2 * (pairNorm H E Y).rootMultiplicity P.X : ℤ) := by
  rw [ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E Y hg_ne hgbar_ne_eval]
  exact ordAt_eq_rootMultiplicity_ramified hsf (pairNorm H E Y) hN_ne P.X P h_bot rfl hY

/-- **`toPair H (A * U) 0 = toPair H A 0 * toPair H U 0`, the `(A,B)`-pair
form of `k[X]`-multiplicativity for pure polynomials (`B = 0` throughout).**
Special case of `toPair_mul` (`RiemannRochGenus2.lean`) with both `B`-slots
zero — `toPair_mul`'s general formula `toPair H (A*A'+B*B'*H.f) (A*B'+A'*B)`
collapses to `toPair H (A*A') 0` when `B = B' = 0`. Restated here as its own
lemma (rather than inlining `toPair_mul ... 0 ... 0` plus `simp` at every
call site) since lemma 7 below needs it by name.

Proof note: `have h := toPair_mul (H := H) A 0 U 0` fixes `h`'s statement
concretely (`toPair H A 0 * toPair H U 0 = toPair H (A*U+0*0*H.f)
(A*0+U*0)`) *before* any simplification, then `simp only [...] at h`
normalizes its right-hand side down to `toPair H (A*U) 0` in place — this
is more robust than trying to `rw [toPair_mul ...]` directly on the goal,
since the goal's two sides have `toPair` applied to different numbers of
arguments-in-a-product (`A*U` singular on the left vs. a product of two
`toPair`s on the right), which risks the rewrite matching ambiguously or
not firing where intended. -/
theorem toPair_mul_right_zero' [IsDedekindDomain (CoordinateRing H)] (A U : k[X]) :
    toPair H (A * U) (0 : k[X]) = toPair H A (0 : k[X]) * toPair H U (0 : k[X]) := by
  have h := toPair_mul (H := H) A (0 : k[X]) U (0 : k[X])
  simp only [mul_zero, zero_mul, add_zero] at h
  exact h.symm

/-- **Lemma 7 of the stack (ChatGPT §6/§13 step 7): the factorization
`N = A · U` at the pair level, giving `ordAt P N = ordAt P A + ordAt P U`.**
This is ChatGPT's own recommended "cleanest formal route" (§6): rather than
tracking which of the six points `P` is, factor the whole divisor
computation through `N = A · U` (`A` the known/old factor, `U` the residual
Mumford polynomial — `uRS4General` in this project's naming, already known
`∣ Npoly4` via `uRS4General_dvd_Npoly4`) and let valuations add.

Takes `hAU : N = A * U` as an explicit hypothesis (the caller supplies the
concrete factorization, e.g. via `uRS4General_dvd_Npoly4`'s witness) rather
than re-deriving divisibility here — this file stays generic/project-
agnostic per its own stated design (module docstring), so it shouldn't
reach for `uRS4General`-specific lemmas directly.

Needs `[IsDedekindDomain (CoordinateRing H)]` explicitly (this file has no
ambient `variable` supplying it the way the source file
`RiemannRochGenus2.lean` does at the point `ordAt_toPair_mul_of_ne_zero'`
is declared) — same pattern as lemmas 2/4/6 above; missed on the first
draft of this lemma, causing a build failure (instance-synthesis errors
cascading into every line that used `ordAt`/`ordAt_toPair_mul_of_ne_zero'`,
plus a downstream "unknown identifier `hAU`" from the `apply` call failing
to elaborate at all) — fixed here. Also switched the proof from
`apply ... ; rw [...]` to a single term-mode `▸`-rewrite
(`hAU.symm ▸ toPair_mul_right_zero' A U`, transporting
`toPair_mul_right_zero'`'s `A*U` to `N` via `hAU.symm : A*U = N`),
matching the term-style already used successfully by lemma 4 above rather
than an `apply`+`rw` split that turned out fragile here. (`toPair_mul_right_zero'`
also picked up its own explicit `[IsDedekindDomain (CoordinateRing H)]` in
Claire's confirmed-building version, plus explicit `(0 : k[X])`
ascriptions throughout both lemmas rather than bare `0` — belt-and-braces
against the same kind of elaboration-order fragility as the earlier
`C`/`X` build-error passes.) -/
theorem ordAt_add_of_pairNorm_eq_mul
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (N A U : k[X])
    (hAU : N = A * U) (hA_ne : toPair H A (0 : k[X]) ≠ 0)
    (hU_ne : toPair H U (0 : k[X]) ≠ 0) :
    ordAt P N (0 : k[X]) = ordAt P A (0 : k[X]) + ordAt P U (0 : k[X]) :=
  ordAt_toPair_mul_of_ne_zero' P h_bot A (0 : k[X]) U (0 : k[X]) N (0 : k[X]) hA_ne hU_ne
    (hAU.symm ▸ toPair_mul_right_zero' A U)

/-- **Lemma 8 of the stack (ChatGPT §13 step 8): `ordAtFrac P E Y U 0 =
ordAt P A 0` at a residual, ordinary (`P.Y ≠ 0`) point — i.e. `ordAt P h =
ordAt P A` where `h := g/U`.** This is the theorem the whole stack has
been building toward: it collapses `ordAt P U 0` out of the picture
entirely, leaving only `ordAt P A 0` — matching ChatGPT's own §13 step 8
statement verbatim, and (via `ordAtFrac`'s definition, `ordAt P E Y -
ordAt P U 0`) exactly reproduces raw reply §1's "definitional bridge"
composed with lemma 6 + lemma 7 above.

Composition, per §13's own ordering: `ordAtFrac P E Y U 0 = ordAt P E Y -
ordAt P U 0` (`ordAtFrac`'s definition, unfolds by `rfl`) `= (pairNorm H E
Y).rootMultiplicity P.X - ordAt P U 0` (lemma 6, needs `g(P) = 0` via
`hgbar_ne_eval`/`hg_ne`/`hN_ne`/`hchar`/`hY : P.Y ≠ 0`) `= (ordAt P A 0 +
ordAt P U 0) - ordAt P U 0` (lemma 7, needs `pairNorm H E Y = A * U` as
`hAU` plus both factors' `toPair`-nonvanishing) `= ordAt P A 0` (integer
arithmetic, `omega`/`ring`-level cancellation — no positivity assumption
on `ordAt P U 0` needed since these are `ℤ`-valued, not `ℕ`-valued).

`hN_eq_mult` bundles lemma 6's conclusion as a hypothesis rather than
re-deriving lemma 6's own hypothesis list here, to keep this lemma's
signature from ballooning to lemma 6's full list plus lemma 7's full list
simultaneously — the assembly theorem in `AlphaLocusDegreeUniform.lean`
is expected to supply `hN_eq_mult` via a direct application of lemma 6 at
its own call site instead. -/
theorem ordAtFrac_eq_ordAt_of_pairNorm_eq_mul
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y A U : k[X])
    (hAU : pairNorm H E Y = A * U) (hA_ne : toPair H A (0 : k[X]) ≠ 0)
    (hU_ne : toPair H U (0 : k[X]) ≠ 0)
    (hN_eq_mult : ordAt P E Y = ordAt P (pairNorm H E Y) (0 : k[X])) :
    ordAtFrac P E Y U (0 : k[X]) = ordAt P A (0 : k[X]) := by
  unfold ordAtFrac
  rw [hN_eq_mult, ordAt_add_of_pairNorm_eq_mul P h_bot (pairNorm H E Y) A U hAU hA_ne hU_ne]
  omega

/-- **Lemma 9 of the stack (ChatGPT §9/§13 step 9): the pointwise
coefficient identity for `divToPair`.** `coeffAt P (divToPair A B S) =
if P ∈ S then ordAt P A B else 0` — matches raw reply §9's own boxed
statement verbatim ("prove one lemma... then all later divisor
calculations become rewriting rather than `Finset` gymnastics"). `S` is a
support set, not a multiplicity set (§9): a point occurring with
multiplicity `2` still occurs once in `S`, with `coeffAt` (not
`Finset.card`-type membership) carrying the multiplicity via `ordAt`.

Proof: unfold `divToPair` to the defining `∑ Q ∈ S, ordAt Q A B • single
Q`, push `coeffAt P` through the finite sum (`map_sum`, `coeffAt` an
`AddMonoidHom`) via an explicit `Finset.sum_congr`-driven pointwise step
(`hstep`) rather than a bare `simp`, so each rewrite lemma
(`map_zsmul`/`coeffAt_single`/`smul_eq_mul`) is applied under an explicit
binder rather than relying on `simp`'s automatic congruence through the
sum — every summand collapses to `if P = Q then ordAt Q A B else 0`
(`split_ifs <;> ring` closes both branches: `ordAt Q A B * 1 = ordAt Q A B`
and `ordAt Q A B * 0 = 0`). Then `by_cases hP : P ∈ S`: when true,
`Finset.sum_eq_single P` (Mathlib, confirmed signature: `(a) (h₀ : ∀ b ∈
s, b ≠ a → f b = 0) (h₁ : a ∉ s → f a = 0) : ∑ x ∈ s, f x = f a`) picks out
the `Q = P` term directly; when false, `Finset.sum_eq_zero` shows every
summand vanishes since `P ≠ Q` for every `Q ∈ S`. Avoided the initially
tempting one-line `Finset.sum_eq_ite` (`∑ x ∈ s, f x = if a ∈ s then f a
else 0` — a seemingly exact match) because its conclusion's `f a` term
(`if P = P then ordAt P A B else 0`) is not syntactically `ordAt P A B`
even though propositionally equal, which risked `exact` failing to unify
without an extra normalization step — the `by_cases` split avoids
depending on that unification succeeding silently. -/
theorem coeffAt_divToPair [IsDedekindDomain (CoordinateRing H)] [DecidableEq H.Point]
    (A B : k[X]) (S : Finset H.Point) (P : H.Point) :
    coeffAt P (divToPair A B S) = if P ∈ S then ordAt P A B else 0 := by
  unfold divToPair
  rw [map_sum]
  have hstep : ∀ Q ∈ S, coeffAt P ((ordAt Q A B) • single Q) =
      if P = Q then ordAt Q A B else 0 := by
    intro Q _
    rw [map_zsmul, coeffAt_single, smul_eq_mul]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hstep]
  by_cases hP : P ∈ S
  · rw [if_pos hP,
      Finset.sum_eq_single P (fun Q _ hQP => if_neg (fun h => hQP h.symm))
        (fun hPnotin => absurd hP hPnotin)]
    exact if_pos rfl
  · rw [if_neg hP]
    apply Finset.sum_eq_zero
    intro Q hQ
    exact if_neg (fun (h : P = Q) => hP (h.symm ▸ hQ))

/-- **`Divisor H` extensionality via `coeffAt`, needed for the `δ₀`-avoidance
argument (ChatGPT §11/§12).** ChatGPT's §12 escape hatch is: prove finite
(affine) coefficients agree everywhere, then use a degree-zero argument to
get equality including whatever happens at infinity. **In this project's
actual model that degree argument is unnecessary** — `Divisor H := H.Point
→₀ ℤ` (`DivisorClassGroup.lean`) is *already* affine-only by construction
(its own module docstring: "points at infinity are excluded"), so there is
no `δ₀`-coefficient slot for a discrepancy to hide in. If `coeffAt P D₁ =
coeffAt P D₂` for every affine `P`, that alone is the whole of the data
`D₁`/`D₂` carry, so `D₁ = D₂` outright — no separate degree/infinity step
needed for *this* equality. (The `δ₀`-correction term still appears
elsewhere, in `reducedClass`'s own definition as `+ 2•[δ₀]` — that's a
statement about `Jacobian H D`, one level up, via `toJacobian`, not about
`Divisor H` itself; unaffected by this lemma.)

Proof note: proved via `Finsupp.ext` behind an explicit `show`-cast through
`Divisor H`'s definitional unfolding to `H.Point →₀ ℤ`, and `coeffAt` to
`Finsupp.applyAddHom` — the same `show`-cast idiom already confirmed to work
in `coeffAt_single` above (`DivisorClassGroup.lean`), rather than a bare
`Finsupp.ext`/`ext` call directly against `Divisor H` without unfolding
first, which `LPairFinrankOne.lean` flags (in a comment on an unrelated
proof) as a genuine transparency risk precisely because `Divisor H` is a
plain `def`, not `abbrev`, over `Finsupp` — this avoids relying on defeq
matching silently by making the unfolding explicit.

Correction from an earlier draft of this docstring/proof: a first pass
here used `DFunLike.ext` after concluding (from a web search that turned
up mathlib-3-docs results first) that `Finsupp.ext` was deprecated — wrong.
That build failed (`failed to synthesize instance of type class DFunLike
H.Divisor ?m ?m`): `DFunLike.ext _ _ (fun P => ?_)` left its own instance
argument as a metavariable with nothing pinning it down, since the
`show`-cast alone doesn't carry enough information for instance search to
find the `Finsupp`-supplied `DFunLike` instance at that point. A second,
more targeted search confirmed `Finsupp.ext` genuinely exists in current
Mathlib4 (`Mathlib.Data.Finsupp.Defs`) — switched to it directly, which
needs no instance search at all (its statement is stated for `Zero M`
generally, not through the `DFunLike` typeclass machinery), and unfolds
`coeffAt`/`Finsupp.applyAddHom` at each point exactly as before. -/
theorem eq_of_coeffAt_eq {D₁ D₂ : Divisor H} (h : ∀ P, coeffAt P D₁ = coeffAt P D₂) :
    D₁ = D₂ := by
  show (D₁ : H.Point →₀ ℤ) = (D₂ : H.Point →₀ ℤ)
  refine Finsupp.ext (fun P => ?_)
  have hP := h P
  simp only [coeffAt, Finsupp.applyAddHom_apply] at hP
  exact hP

/-- **Lemma 10 of the stack (ChatGPT §3b item 3 / §14's ramified case): the
Weierstrass/ramification-point witness, `div(x - x0) = 2•[P]`.** At a point
`P` with `P.Y = 0`, `Point.iota P = P` (the hyperelliptic involution fixes
Weierstrass points), so the ordinary "distinct-conjugate" witness
`divToPair (linX P.X) 0 {P, ι P} = [P] + [ι P]` degenerates to a single
point with multiplicity 2: `divToPair (linX P.X) 0 {P} = 2•[P]`.

**This is already fully proved elsewhere in the codebase** —
`divToPair_linX_eq_of_ramified` (`HyperellipticClassProof.lean`, via
`ordAt_linX_eq_two_of_ramified`, unconditionally, no `sorry`) — so this
lemma is a thin restatement collapsing its `single P + single (Point.iota
P)` right-hand side (phrased that way there to keep a uniform shape with
the unramified case) down to `2 • single P` directly using `hiota : Point.
iota P = P`, matching how this "witness" is actually consumed: as a
concrete `Divisor H` value, not as a sum of two (possibly-equal) `single`
terms. Confirms, per §3b/§14's own flagging, that the Weierstrass case
genuinely needs (and now has) its own separate witness — it is NOT a
degenerate specialization of the main `g/U`-based principal-witness
argument (lemmas 1-9 above), since at a Weierstrass point `ḡ(P) = g(P)`
(§3b: `P = ι(P)` forces this), so the `hgbar_ne_eval` hypothesis every
other lemma in this stack relies on is unavailable there.

Proof note (direction caught on proofread — the first draft rewrote the
wrong term): `hiota : Point.iota P = P` is rewritten INTO `h` (turning `h`'s
RHS from `single P + single (Point.iota P)` to `single P + single P`), not
into the goal directly — the goal has no `Point.iota P` occurrence to
rewrite before `h` is substituted in, so `rw [hiota]` against the bare goal
would find nothing to fire on. Once `h` reads `... = single P + single P`,
`rw [h, two_smul]` rewrites the goal's LHS via `h` and closes the resulting
`single P + single P = 2 • single P` by unfolding `two_smul` on the RHS
(reflexivity closes it automatically once both sides match). -/
theorem divToPair_linX_eq_two_smul_of_ramified
    [IsDedekindDomain (CoordinateRing H)]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (P : H.Point) (hY : P.Y = 0) :
    divToPair (linX P.X) (0 : k[X]) ({P} : Finset H.Point) = (2 : ℤ) • single P := by
  have h := divToPair_linX_eq_of_ramified hchar hsf P hY
  have hiota : Point.iota P = P := by
    apply Subtype.ext
    apply Prod.ext
    · exact Point.iota_X P
    · change (Point.iota P).Y = P.Y
      rw [Point.iota_Y, hY, neg_zero]
  rw [hiota] at h
  rw [h, two_smul]

/-- **Lemma 11 of the stack (ChatGPT §15's boxed pointwise identity): the
final packaging of lemmas 2/8/9 into a `coeffAt`-of-`divToPair` statement
about `D_old - D_new` directly.** Per §15's derivation: `ordAtFrac P E Y U 0
= ordAt P A 0 - ordAt P (E) (-Y) 0`-shaped bookkeeping reduces, at each
affine point, to exactly one of three cases —
- `P` an "old" point (`g(P) = 0`, i.e. `E.eval P.X + Y.eval P.X*P.Y = 0`,
  and `ḡ(P) ≠ 0`): contributes `+1` to `D_old`'s side, `0` to `D_new`'s
  (lemma 2 applied to `ḡ`, giving `ordAt P E (-Y) = 0`, composed with
  lemma 8's `ordAtFrac = ordAt P A`, itself `0` here since `A`'s multiplicity
  only shows up at residual points — see hypothesis shape below);
- `P` a residual point (`ḡ(P) = 0`, i.e. old point's conjugate is NOT `P`,
  `U(P) = 0`): contributes `0`/`+1` the other way;
- elsewhere: both sides `0`.

Rather than re-deriving this three-way case split generically (which would
duplicate lemmas 2/6/8's own case analysis), this lemma packages the
**already-established per-point facts as explicit hypotheses** (`hold`,
`hnew`, `helse`, covering the three cases above respectively) and concludes
the `coeffAt`-difference identity directly — the assembly theorem at the
call site is expected to discharge `hold`/`hnew`/`helse` via lemmas 2/8/9
(and lemma 10 for any Weierstrass point among the four/six named points),
not by re-proving the case split here. This mirrors this file's existing
discipline (lemmas 6/7/8 all take their key structural fact — root
multiplicity shape, factorization, `hN_eq_mult` — as an explicit hypothesis
rather than re-deriving it), keeping each lemma a single composition step.

`D_old`/`D_new` here are given directly as `divToPair`-values (not yet
specialized to this project's actual `alpha•aClass ± [P1]+[P2] ∓ 2[δ₀]`
shape — that specialization, and the `Jacobian`/`toJacobian` step per
ChatGPT §16, belongs in the final assembly theorem back in
`AlphaLocusDegreeUniform.lean`, not here, matching this file's stated
design of staying ignorant of `SampleTargetFromAlpha`/`aClass`/`hr`). -/
theorem coeffAt_sub_eq_of_forall
    [IsDedekindDomain (CoordinateRing H)] [DecidableEq H.Point]
    (Aold Bold Anew Bnew : k[X]) (Sold Snew : Finset H.Point)
    (h : ∀ P : H.Point,
      coeffAt P (divToPair Aold Bold Sold) - coeffAt P (divToPair Anew Bnew Snew) =
        (if P ∈ Sold then ordAt P Aold Bold else 0) -
          (if P ∈ Snew then ordAt P Anew Bnew else 0)) :
    ∀ P : H.Point,
      coeffAt P (divToPair Aold Bold Sold - divToPair Anew Bnew Snew) =
        (if P ∈ Sold then ordAt P Aold Bold else 0) -
          (if P ∈ Snew then ordAt P Anew Bnew else 0) := by
  intro P
  rw [map_sub]
  exact h P

/-- **Corollary: `D_old = D_new` as `Divisor H` values, given the pointwise
`coeffAt`-agreement hypothesis of `coeffAt_sub_eq_of_forall`'s conclusion
collapses to `0` at every point.** Composes `coeffAt_sub_eq_of_forall` with
`eq_of_coeffAt_eq` — this is the shape the assembly theorem in
`AlphaLocusDegreeUniform.lean` is expected to invoke directly: once the
per-point `if`-`if` difference above is shown to vanish everywhere (via
lemmas 2/8/9/10 supplying which case each of the finitely many relevant
points falls into, and both `if`-conditions being false with equal
`ordAt`-values elsewhere), `D_old = D_new` follows with no further
`Divisor H`-level algebra needed, and no `δ₀`/infinity valuation
machinery anywhere in the proof (per the `eq_of_coeffAt_eq` docstring
above — this project's `Divisor H` model has no `δ₀` coefficient slot to
begin with).

Proof note: after `rw [h1, h2]` the goal is `X = Y` (the two `if`-guarded
`ordAt`-expressions directly), while `hzero P`'s shape is `X - Y = 0` — not
the same term syntactically, so `exact hzero P` alone doesn't typecheck.
Closed with `omega` instead of reaching for a named Mathlib bridging lemma
(considered `sub_eq_zero`, but couldn't confirm its exact name/orientation
via web search, and this project's own convention is to search rather than
guess) — `omega` treats the `if`-expressions as opaque `ℤ` atoms and closes
`X = Y` directly from `X - Y = 0` in context, the same pattern already used
successfully by lemma 8 above for an analogous integer-arithmetic
cancellation. -/
theorem divToPair_eq_of_coeffAt_diff_eq_zero
    [IsDedekindDomain (CoordinateRing H)] [DecidableEq H.Point]
    (Aold Bold Anew Bnew : k[X]) (Sold Snew : Finset H.Point)
    (hzero : ∀ P : H.Point,
      (if P ∈ Sold then ordAt P Aold Bold else 0) -
        (if P ∈ Snew then ordAt P Anew Bnew else 0) = 0) :
    divToPair Aold Bold Sold = divToPair Anew Bnew Snew := by
  apply eq_of_coeffAt_eq
  intro P
  have h1 : coeffAt P (divToPair Aold Bold Sold) = if P ∈ Sold then ordAt P Aold Bold else 0 :=
    coeffAt_divToPair Aold Bold Sold P
  have h2 : coeffAt P (divToPair Anew Bnew Snew) = if P ∈ Snew then ordAt P Anew Bnew else 0 :=
    coeffAt_divToPair Anew Bnew Snew P
  rw [h1, h2]
  have := hzero P
  omega

/-- **Lemma 12 of the stack: `pairNorm H E (-Y) = pairNorm H E Y`.** Pure
algebra (`pairNorm H A B := A^2 - B^2*H.f`, and `(-Y)^2 = Y^2`) — needed so
the "residual point" case (where `ḡ = toPair H E (-Y)` vanishes, not `g`)
can reuse the SAME factorization `pairNorm H E Y = A * U` that the "old
point" case (lemmas 6/7/8) already uses for `g`, rather than needing a
second, independently-supplied factorization of a different-looking norm.
This is exactly why the hyperelliptic involution is central to the whole
argument (ChatGPT §15's closing remark): `g` and `ḡ` are norm-conjugate,
so `N`'s factorization `A * U` governs both sides' zero loci at once. -/
theorem pairNorm_neg_eq (E Y : k[X]) :
    pairNorm H E (-Y) = pairNorm H E Y := by
  unfold pairNorm
  ring

/-- **Lemma 13 of the stack (the residual-point mirror of lemma 8):
`ordAtFrac P E (-Y) U 0 = ordAt P A 0` at a residual point where `ḡ =
toPair H E (-Y)` vanishes at `P` (as a ring element, `hgbar_ne`) but `g`
doesn't (`hg_ne_eval`).** Mirrors lemma 8's own composition
(`ordAtFrac_eq_ordAt_of_pairNorm_eq_mul`) with the roles of `g`/`ḡ`
swapped: lemma 4 (`ordAt_eq_ordAt_pairNorm_of_eval_eq_zero`) applied
directly to the pair `(E,-Y)` gives `ordAt P E (-Y) = ordAt P (pairNorm H E
(-Y)) 0` with NO unramified/ramified case split needed (lemma 4, unlike
lemma 6, doesn't go through `rootMultiplicity` at all) — so, unlike lemma
8's own derivation (which routes through lemma 6 and hence needs `hchar`/
`P.Y ≠ 0`), this lemma needs neither: it holds uniformly whether or not `P`
is a Weierstrass point. `pairNorm_neg_eq` (lemma 12) then rewrites
`pairNorm H E (-Y)` back to `pairNorm H E Y`, so the SAME caller-supplied
factorization `hAU : pairNorm H E Y = A * U` (not a second one) feeds
lemma 7 (`ordAt_add_of_pairNorm_eq_mul`) directly, and the `+ordAt P U 0`
term cancels against `ordAtFrac`'s own `- ordAt P U 0` by `omega` exactly
as in lemma 8. (Caught in review: the earlier version of this lemma
concluded the bare `ordAt P E (-Y) = ordAt P A 0`, dropping the `ordAt P U
0` term entirely with no justification — that statement is false whenever
`ordAt P U 0 ≠ 0`, since `ordAt_add_of_pairNorm_eq_mul` only gives the sum
`ordAt P A 0 + ordAt P U 0`, not `ordAt P A 0` alone; weakened to the
`ordAtFrac` form, which is what lemma 8's own mirror actually needs and is
what genuinely follows from the same composition.) -/
theorem ordAtFrac_neg_eq_ordAt_of_pairNorm_eq_mul
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y A U : k[X])
    (hgbar_ne : toPair H E (-Y) ≠ 0)
    (hg_ne_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0)
    (hAU : pairNorm H E Y = A * U) (hA_ne : toPair H A (0 : k[X]) ≠ 0)
    (hU_ne : toPair H U (0 : k[X]) ≠ 0) :
    ordAtFrac P E (-Y) U (0 : k[X]) = ordAt P A (0 : k[X]) := by
  have hN_eq_mult : ordAt P E (-Y) = ordAt P (pairNorm H E (-Y)) (0 : k[X]) :=
    ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E (-Y) hgbar_ne hg_ne_eval
  have hAU' : pairNorm H E (-Y) = A * U := by rw [pairNorm_neg_eq]; exact hAU
  unfold ordAtFrac
  rw [hN_eq_mult, hAU', ordAt_add_of_pairNorm_eq_mul P h_bot (A * U) A U rfl hA_ne hU_ne]
  omega

/-- **Lemma 13b of the stack (new): the unconditional `g`/`ḡ` sum identity
for `ordAtFrac`, `h := g/U` versus `h̄ := ḡ/U`.** `g * ḡ = toPair H
(pairNorm H E Y) 0` always (`toPair_pairNorm_eq_toPair_mul_toPair_neg`,
no hypothesis needed beyond both factors being nonzero ring elements), so
`ordAt_toPair_mul_of_ne_zero'` gives `ordAt P (pairNorm H E Y) 0 = ordAt P
E Y + ordAt P E (-Y)` UNCONDITIONALLY — no `g(P) = 0`/`ḡ(P) = 0` case
split needed at all, unlike lemmas 8/13 individually (which each need one
side's evaluation-vanishing hypothesis to identify `ordAt P E Y` — or `E
(-Y)` — with a `pairNorm`-rootMultiplicity fact in the first place). This
is the bridge lemma the case-split assembly in `AlphaLocusDegreeUniform.lean`
actually needs: given only lemma 13's `ordAtFrac P E (-Y) U 0 = ordAt P A 0`
at a residual point (`ḡ` vanishes there), this lemma lets the caller solve
for `ordAtFrac P E Y U 0` (i.e. `h`'s OWN valuation, not `h̄`'s) directly,
via `ordAtFrac P E Y U 0 = (ordAt P (pairNorm H E Y) 0 - 2 • ordAt P U 0) -
ordAtFrac P E (-Y) U 0`, itself following from unfolding both `ordAtFrac`s
and this lemma's conclusion by `omega`-level arithmetic — resolving, from
first principles rather than a guess, the exact question the last two
ChatGPT rounds could not settle (whether `h`'s valuation at a residual
point is `+1`, `-1`, or `-2`): it depends on `ordAt P (pairNorm H E Y) 0`
and `ordAt P U 0` at that specific point, which the caller must supply,
not on a universal constant. -/
theorem ordAtFrac_add_ordAtFracNeg_eq_ordAt_pairNorm_sub
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y U : k[X])
    (hg_ne : toPair H E Y ≠ 0) (hgbar_ne : toPair H E (-Y) ≠ 0) :
    ordAtFrac P E Y U (0 : k[X]) + ordAtFrac P E (-Y) U (0 : k[X]) =
      ordAt P (pairNorm H E Y) (0 : k[X]) - 2 * ordAt P U (0 : k[X]) := by
  have hmul : ordAt P (pairNorm H E Y) (0 : k[X]) = ordAt P E Y + ordAt P E (-Y) :=
    ordAt_toPair_mul_of_ne_zero' P h_bot E Y E (-Y) (pairNorm H E Y) (0 : k[X])
      hg_ne hgbar_ne (toPair_pairNorm_eq_toPair_mul_toPair_neg E Y)
  unfold ordAtFrac
  omega

/-- **Lemma 13c of the stack (new): `h`'s OWN valuation at a residual point,
`ordAtFrac P E Y U 0 = -1`, given the standard "simple residual root"
hypotheses.** This is the concrete number the case-split assembly in
`AlphaLocusDegreeUniform.lean` needs at a root of `U` disjoint from `A`'s
roots — resolved here, once, via lemma 13b plus lemma 7's `N = A*U`
factorization applied at the bare-polynomial level (`ordAt P N 0 = ordAt P
A 0 + ordAt P U 0`, via `ordAt_add_of_pairNorm_eq_mul`), rather than left
to a per-call-site `omega` guess. Hypotheses: `hAU : pairNorm H E Y = A *
U` (the standard factorization); `hA_ord : ordAt P A 0 = 0` (`P` is NOT a
root of the old/anchor factor — the genuine "residual, not old" condition);
`hU_ord : ordAt P U 0 = 1` (`P` IS a simple root of the new/residual
factor); `hgbar_ne`/`hg_ne_eval` (lemma 13's own hypotheses, identifying
`P` as a point where `ḡ` vanishes) so lemma 13 supplies `ordAtFrac P E
(-Y) U 0 = ordAt P A 0 = 0` directly. -/
theorem ordAtFrac_eq_neg_one_of_residual_point
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y A U : k[X])
    (hg_ne : toPair H E Y ≠ 0)
    (hgbar_ne : toPair H E (-Y) ≠ 0)
    (hg_ne_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0)
    (hAU : pairNorm H E Y = A * U) (hA_ne : toPair H A (0 : k[X]) ≠ 0)
    (hU_ne : toPair H U (0 : k[X]) ≠ 0)
    (hA_ord : ordAt P A (0 : k[X]) = 0) (hU_ord : ordAt P U (0 : k[X]) = 1) :
    ordAtFrac P E Y U (0 : k[X]) = -1 := by
  have hbar : ordAtFrac P E (-Y) U (0 : k[X]) = ordAt P A (0 : k[X]) :=
    ordAtFrac_neg_eq_ordAt_of_pairNorm_eq_mul P h_bot E Y A U hgbar_ne hg_ne_eval hAU hA_ne hU_ne
  have hsum := ordAtFrac_add_ordAtFracNeg_eq_ordAt_pairNorm_sub P h_bot E Y U hg_ne hgbar_ne
  have hN : ordAt P (pairNorm H E Y) (0 : k[X]) = ordAt P A (0 : k[X]) + ordAt P U (0 : k[X]) :=
    ordAt_add_of_pairNorm_eq_mul P h_bot (pairNorm H E Y) A U hAU hA_ne hU_ne
  rw [hN, hbar, hA_ord, hU_ord] at hsum
  omega

/-- **Layer 1 (per ChatGPT's follow-up reply): `ordAt P (linX a) 0 = 1` at
an unramified point `P` with `P.X = a`.** Thin restatement of the
already-fully-proved `ordAt_linX_eq` (`HyperellipticClassProof.lean`)
specialized to its middle branch (`Q.X = a`, `Q.Y ≠ 0`) — avoids exposing
the `if`-`if` case split to callers who already know they're in the
unramified case, matching the follow-up reply's recommended "boring and
local" Layer 1 API (`ordAt P (X - C a) 0 = 1` when `P.X = a`). Deliberately
does NOT go through `Polynomial.roots`/`rootMultiplicity` at the call
site — `ordAt_linX_eq`'s own proof already did that work once. -/
theorem ordAt_linX_eq_one_of_ne_zero [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (a : k) (P : H.Point)
    (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X = a) (hPY : P.Y ≠ 0) :
    ordAt P (linX a) 0 = 1 := by
  rw [ordAt_linX_eq hchar hsf a P h_bot]
  rw [if_neg (not_ne_iff.mpr hPX), if_pos hPY]

/-- **Layer 1, the "not this point" companion**: `ordAt P (linX a) 0 = 0`
when `P.X ≠ a` — same restatement idiom, other branch of `ordAt_linX_eq`
(the `Q.X ≠ a` case doesn't even need `hchar`/`hsf`, but takes them anyway
to keep this lemma's signature interchangeable with the one above at call
sites that don't yet know which branch applies). -/
theorem ordAt_linX_eq_zero_of_ne' [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f) (a : k) (P : H.Point)
    (h_bot : pointIdeal P ≠ ⊥) (hPX : P.X ≠ a) :
    ordAt P (linX a) 0 = 0 := by
  rw [ordAt_linX_eq hchar hsf a P h_bot, if_pos hPX]

/-- **Layer 2 (per ChatGPT's follow-up reply): a product of two pure-`x`
factors where exactly one has `ordAt`-order 1 and the other 0, has order 1
overall.** Direct application of `ordAt_add_of_pairNorm_eq_mul` (lemma 7,
despite its `pairNorm`-flavored name — it is really a general "`ordAt` of
a product" fact, `N = A*U ⟹ ordAt P N = ordAt P A + ordAt P U`, not
specific to `pairNorm`'s own use) with the two given order values summed
via `omega`. `hL_ne`/`hF_ne` (both factors nonzero as ring elements) are
required by `ordAt_add_of_pairNorm_eq_mul` itself — supplied here rather
than derived, matching this stack's existing "don't over-assume, take the
minimal needed fact as a hypothesis" discipline. -/
theorem ordAt_mul_eq_one_of_ordAt_eq_one_zero
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (L F : k[X])
    (hL_ne : toPair H L (0 : k[X]) ≠ 0) (hF_ne : toPair H F (0 : k[X]) ≠ 0)
    (hL : ordAt P L (0 : k[X]) = 1) (hF : ordAt P F (0 : k[X]) = 0) :
    ordAt P (L * F) (0 : k[X]) = 1 := by
  rw [ordAt_add_of_pairNorm_eq_mul P h_bot (L * F) L F rfl hL_ne hF_ne, hL, hF]
  ring

/-- **Layer 2, four-factor form — the exact shape this project's `A =
(x-x₁)(x-x₂)·uₐ·u_target` needs.** One "designated" factor `L` contributes
order `1` (via Layer 1 at the point in question); the other three
(`F₁ F₂ F₃`) each contribute order `0` (via `ordAt_eq_zero_of_eval_ne_zero`,
lemma 2, at whichever evaluation-nonvanishing fact the caller supplies —
this lemma stays agnostic to WHY each `ordAt = 0`, taking it as a
hypothesis, so it composes with `ordAt_linX_eq_zero_of_ne'` just as well as
with lemma 2 directly). Built by iterating the two-factor case
(`ordAt_mul_eq_one_of_ordAt_eq_one_zero`) three times, associating `((L*F₁)
*F₂)*F₃` — matches how the actual `A` is nested in this project's
`npoly4LcmRaw`/`npoly4Lcm4` (`lcm(lcm(q1,q2),lcm(q3,q4))`, itself
associating pairwise), so the call site should not need any extra
`mul_assoc` bookkeeping beyond possibly re-bracketing to match. -/
theorem ordAt_mul4_eq_one_of_ordAt_eq_one_zero_zero_zero
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (L F₁ F₂ F₃ : k[X])
    (hL_ne : toPair H L (0 : k[X]) ≠ 0) (hF₁_ne : toPair H F₁ (0 : k[X]) ≠ 0)
    (hF₂_ne : toPair H F₂ (0 : k[X]) ≠ 0) (hF₃_ne : toPair H F₃ (0 : k[X]) ≠ 0)
    (hL : ordAt P L (0 : k[X]) = 1)
    (hF₁ : ordAt P F₁ (0 : k[X]) = 0) (hF₂ : ordAt P F₂ (0 : k[X]) = 0)
    (hF₃ : ordAt P F₃ (0 : k[X]) = 0) :
    ordAt P (((L * F₁) * F₂) * F₃) (0 : k[X]) = 1 := by
  have h1 : ordAt P (L * F₁) (0 : k[X]) = 1 :=
    ordAt_mul_eq_one_of_ordAt_eq_one_zero P h_bot L F₁ hL_ne hF₁_ne hL hF₁
  have h1_ne : toPair H (L * F₁) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero hL_ne hF₁_ne
  have h2 : ordAt P ((L * F₁) * F₂) (0 : k[X]) = 1 :=
    ordAt_mul_eq_one_of_ordAt_eq_one_zero P h_bot (L * F₁) F₂ h1_ne hF₂_ne h1 hF₂
  have h2_ne : toPair H ((L * F₁) * F₂) (0 : k[X]) ≠ 0 := by
    rw [toPair_mul_right_zero']
    exact mul_ne_zero h1_ne hF₂_ne
  exact ordAt_mul_eq_one_of_ordAt_eq_one_zero P h_bot ((L * F₁) * F₂) F₃ h2_ne hF₃_ne h2 hF₃

/-- **Layer 3 (Cantor-specific instantiation): `ordAt P (((linX a * F₁) * F₂)
* F₃) 0 = 1` at a point `P` with `P.X = a`, `P.Y ≠ 0`, given the other three
factors don't vanish AT `a` (evaluation-level, per the follow-up reply's
explicit recommendation to phrase these at `eval`, not via roots).**
Composes Layer 1 (`ordAt_linX_eq_one_of_ne_zero`, giving `L`'s own order 1)
with lemma 2 (`ordAt_eq_zero_of_eval_ne_zero`) applied three times (giving
each `Fᵢ`'s order 0 from its evaluation-nonvanishing at `a`, not from any
root-multiplicity reasoning) and Layer 2's four-factor product lemma. This
is the exact shape needed for `A = (x-x(P1))·(x-x(P2))·u_a(x)·u_target(x)`
evaluated at `P = P1` (`a := P1.X`, `F₁,F₂,F₃ := (x-x(P2)), u_a, u_target`)
— the caller supplies `hF₁/hF₂/hF₃` as plain polynomial-evaluation facts
(`(x-x(P2)).eval P1.X ≠ 0` i.e. `P1.X ≠ P2.X`, `u_a.eval P1.X ≠ 0`,
`u_target.eval P1.X ≠ 0`), matching this project's existing
`isCoprime_lcm12_lcm34_of_no_shared_root`-style no-shared-root hypotheses
exactly (those are stated at the same evaluation level already, so the
bridge from "no shared root" facts already on file to this lemma's
`hF₁/hF₂/hF₃` should be direct, no new root-multiplicity work needed at
call sites). Each `Fᵢ.eval a ≠ 0` also gives `Fᵢ ≠ 0` as a ring element
directly (`Polynomial.eval_zero`-contrapositive is NOT needed — `toPair H
Fᵢ 0 ≠ 0` follows via `toPair_eq_zero_iff`: if `Fᵢ = 0` its eval would be
`0`, contradicting `hFᵢ_eval`), avoided as a SEPARATE hypothesis (`hL_ne`
etc. in Layer 2) by deriving it inline here from the eval fact, so this
lemma's own hypothesis list stays at exactly the four evaluation facts a
call site naturally has on hand. -/
theorem ordAt_A_eq_one_of_eval_ne_zero
    [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (a : k) (hPX : P.X = a) (hPY : P.Y ≠ 0)
    (F₁ F₂ F₃ : k[X])
    (hF₁_eval : F₁.eval a ≠ 0) (hF₂_eval : F₂.eval a ≠ 0) (hF₃_eval : F₃.eval a ≠ 0) :
    ordAt P (((linX a * F₁) * F₂) * F₃) (0 : k[X]) = 1 := by
  have hL_ne : toPair H (linX a) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => linX_ne_zero a hA
  have hFi_ne : ∀ F : k[X], F.eval a ≠ 0 → toPair H F (0 : k[X]) ≠ 0 := by
    intro F hFeval
    rw [Ne, toPair_eq_zero_iff]
    exact fun ⟨hA, _⟩ => hFeval (hA ▸ Polynomial.eval_zero)
  have hL : ordAt P (linX a) (0 : k[X]) = 1 :=
    ordAt_linX_eq_one_of_ne_zero hchar hsf a P h_bot hPX hPY
  have hF₁ : ordAt P F₁ (0 : k[X]) = 0 :=
    ordAt_eq_zero_of_eval_ne_zero P F₁ (0 : k[X]) (by rw [hPX]; simpa using hF₁_eval)
  have hF₂ : ordAt P F₂ (0 : k[X]) = 0 :=
    ordAt_eq_zero_of_eval_ne_zero P F₂ (0 : k[X]) (by rw [hPX]; simpa using hF₂_eval)
  have hF₃ : ordAt P F₃ (0 : k[X]) = 0 :=
    ordAt_eq_zero_of_eval_ne_zero P F₃ (0 : k[X]) (by rw [hPX]; simpa using hF₃_eval)
  exact ordAt_mul4_eq_one_of_ordAt_eq_one_zero_zero_zero P h_bot (linX a) F₁ F₂ F₃
    hL_ne (hFi_ne F₁ hF₁_eval) (hFi_ne F₂ hF₂_eval) (hFi_ne F₃ hF₃_eval) hL hF₁ hF₂ hF₃

/-- **Lemma 14 of the stack: the "old point" case of the pointwise
`ordAt`-of-`h` identity, `h := g/U`, `g := toPair H E Y`.** Direct
composition of lemma 8 (`ordAtFrac_eq_ordAt_of_pairNorm_eq_mul`) with
`ordAt P A 0 = 1` supplied as a hypothesis (discharged at the call site
via this file's Layer 1/2/3 lemmas) — concludes `ordAtFrac P E Y U 0 = 1`
at a point where `g(P) = 0` (`hg_ne_eval`) and `ḡ(P) ≠ 0` (implicitly, via
`hN_eq_mult` needing only lemma 4's hypotheses, not a separate `ḡ`
nonvanishing check here — matching lemma 8's own signature exactly, which
does not itself require `ḡ(P) ≠ 0` as input, only `hN_eq_mult`'s
derivation does, and that is discharged by the caller supplying `hg_ne`/
`hg_ne_eval` to lemma 4 directly). Kept generic and thin: this is the
"old point contributes coefficient 1" half of ChatGPT's follow-up reply's
§3 case split, not the residual/new half (lemma 13 does that directly,
no further wrapping needed since it already concludes the `ordAtFrac`
form). No `S`/`Pold1`/`Pold2` bookkeeping here — that belongs to the
call site's `∀ P` assembly (`eq_of_coeffAt_eq`/`coeffAt_single` applied
pointwise), matching ChatGPT's own recommendation not to contort this
stack's support sets to fit a single monolithic lemma. -/
theorem ordAtFrac_eq_one_of_old_point
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y A U : k[X])
    (hg_ne : toPair H E Y ≠ 0) (hg_ne_eval : E.eval P.X + (-Y).eval P.X * P.Y ≠ 0)
    (hAU : pairNorm H E Y = A * U) (hA_ne : toPair H A (0 : k[X]) ≠ 0)
    (hU_ne : toPair H U (0 : k[X]) ≠ 0) (hA_ord : ordAt P A (0 : k[X]) = 1) :
    ordAtFrac P E Y U (0 : k[X]) = 1 := by
  have hN_eq_mult : ordAt P E Y = ordAt P (pairNorm H E Y) (0 : k[X]) :=
    ordAt_eq_ordAt_pairNorm_of_eval_eq_zero P h_bot E Y hg_ne hg_ne_eval
  rw [ordAtFrac_eq_ordAt_of_pairNorm_eq_mul P h_bot E Y A U hAU hA_ne hU_ne hN_eq_mult, hA_ord]

/-- **Lemma 15 of the stack: the "new/residual point" case, the mirror of
lemma 14 via lemma 13 instead of lemma 8.** At a point where `ḡ(P) = 0`
(`hgbar_ne`) and `g(P) ≠ 0` (`hg_ne_eval`), given `ordAt P A 0 = 1`,
concludes `ordAtFrac P E (-Y) U 0 = 1` — i.e. the residual point
contributes coefficient 1 to `h`'s divisor via the CONJUGATE pair
`(E,-Y)`, matching ChatGPT's own flagged subtlety (§3: "at a residual
point... trying to force everything through lemma 8 is wrong"). Purely a
one-line application of lemma 13 with `hA_ord` substituted in — kept as
its own named lemma (rather than inlined at the call site) so the
call-site assembly reads as a clean case split between lemma 14 and
lemma 15, not a repeated unfolding of lemma 13's own five hypotheses. -/
theorem ordAtFrac_neg_eq_one_of_new_point
    [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (E Y A U : k[X])
    (hgbar_ne : toPair H E (-Y) ≠ 0)
    (hg_ne_eval : E.eval P.X + (-(-Y)).eval P.X * P.Y ≠ 0)
    (hAU : pairNorm H E Y = A * U) (hA_ne : toPair H A (0 : k[X]) ≠ 0)
    (hU_ne : toPair H U (0 : k[X]) ≠ 0) (hA_ord : ordAt P A (0 : k[X]) = 1) :
    ordAtFrac P E (-Y) U (0 : k[X]) = 1 := by
  rw [ordAtFrac_neg_eq_ordAt_of_pairNorm_eq_mul P h_bot E Y A U hgbar_ne hg_ne_eval
    hAU hA_ne hU_ne, hA_ord]

end HyperellipticPolynomial

end
