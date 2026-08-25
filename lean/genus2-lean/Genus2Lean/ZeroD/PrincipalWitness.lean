import Mathlib
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.ZeroD.Reduce.AlphaReduce
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationBasics
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.LCanonicalElementary

-- `ordAt_eq_zero_of_notMem`/`ordAt_toPair_mul_of_ne_zero'` (lemmas 2, 4
-- below) live in `RiemannRochGenus2.lean`, and `toPair_mem_pointIdeal_iff`
-- (lemma 2 below) lives in `LCanonicalElementary.lean` — neither is
-- reachable through this file's other imports (`PrincipalDivisorSubgroup.
-- lean`'s own import chain stops at `PrincipalDivisors.lean`, one file
-- short of these two). Both direct imports are cycle-safe: `RiemannRoch
-- Genus2.lean` and `LCanonicalElementary.lean` themselves import
-- `PrincipalDivisorSubgroup.lean` (the reverse direction), and neither
-- file (nor anything in their own import chains) references this file.

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

**Status: lemmas 1-4 of the stack (ChatGPT §2-§5/§13 steps 2-5) —
the norm identity, the residue-nonzero ⇒ valuation-zero lemma, the
`(A,B)`-pair form of the norm identity, and the ordinary-zero-of-`g`
lemma via norm multiplicativity. All proved, no `sorry`. Not yet attempted:
the root-multiplicity translation for `N`/`u_new` (ChatGPT §6-§8), the
factorization `N = A·U` at the pair level (§6/§13 step 7), the pointwise
coefficient identity and `δ₀`-avoidance degree argument (§9/§12/§13 steps
8-9), and the final assembly into `div(h) = D_old - D_new`.**
-/

noncomputable section

namespace HyperellipticPolynomial

open Polynomial

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

end HyperellipticPolynomial

end
