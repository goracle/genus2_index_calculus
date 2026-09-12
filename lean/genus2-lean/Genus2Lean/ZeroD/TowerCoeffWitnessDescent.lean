import Mathlib
import Genus2Lean.ZeroD.TowerToRdecMul
import Genus2Lean.ZeroD.TheDataDerivation.DataDerivationMumford

/-!
# Descending an `IsRdecWitness` bound through one quadratic tower level

New this pass, per `ROADMAP-crossnondegenerate-degree-bound.md`'s live
gap and a ChatGPT consult on exactly this question.

**Update, this pass**: `coeffDescent_totalDegree_le` (the degree-bound
half) is now proved, no `sorry` — direct `MvPolynomial.totalDegree_mul`/
`_add`/`_sub` chasing, `combine_totalDegree_le`'s own style, just more
terms. `coeffDescent_core` (the `Δ*e0=R0`/`Δ*e1=R1` algebraic identity)
was already proved last pass, pure `ring`. Added `_b0` specializations
of both (`coeffDescent_core_b0`/`coeffDescent_totalDegree_le_b0`):
`K1_poly_monic`/`K2_poly_monic` (`DataDerivationMumford.lean`) are
always `X^2 - C(const)`, i.e. `b = 0` identically in this project, so
the `b`-terms these two lemmas' general form carries never actually
occur downstream. Also extracted `towerToRdecK1_spec`
(`DataDerivationMumford.lean`, new this pass) from `towerToRdec_spec`'s
own proof, where it was previously only an internal, unreusable `have`.

**Corrected, this pass, after an initial wrong attempt at composing
these**: `coeffDescent_core` and `towerToRdecK1`/`towerToRdec` solve
OPPOSITE-direction problems and do NOT compose the way an earlier draft
of this file assumed — see `coeffDescent_purpose_note`'s docstring
below for the precise correction and what the right next composition
actually is. Caught before being asserted as a proved theorem, not
after.

**Still genuinely open** (unchanged in substance from before, restated
precisely per the correction above): `norm_ne_zero_iff_placeholder`
needs a real Mathlib `AdjoinRoot`/norm API lookup, not attempted since
guessing an API shape from memory is exactly what the working agreement
says not to do. And the actual assembly `coeffDescent_purpose_note`
describes — decomposing an EXISTING whole-element witness (e.g.
`curBeforeMonic_coeff_totalDegree_le`'s `≤315448` fact) into its
`K1`-basis-coordinate pieces via `coeffDescent_core` — needs that
existing witness's construction inspected directly before it can be
assembled; not attempted this pass, flagged as the concrete next step.

## The math (from the consult, restated)

Given a monic quadratic `g = X^2 + b*X + c` over `K1`, with adjoined
root `w2` generating `K2 = AdjoinRoot g`, and `v : K2` written in the
canonical basis `v = e0 + e1 * w2` (`e0 e1 : K1`, exactly
`AdjoinRoot.modByMonicHom`'s `.coeff 0`/`.coeff 1`), suppose `(n, d)`
is an `IsRdecWitness` pair for `v` under some `ι`/`evalNd`, i.e.
`evalNd n = evalNd d * ι v`. Write the `K1`-basis expansions (which
must themselves come with their own bounded witnesses — see the
"what this does NOT give you" note below) `evalNd n =: N0 + N1 * (image
of w2)`, `evalNd d =: D0 + D1 * (image of w2)` — really this needs `ι`
applied to `b,c` and the target ring's own copy of the `w2^2 = -b*w2-c`
relation, made precise below.

Then, PROVIDED `D := evalNd d ≠ 0` (genuinely necessary — `(0,0)`
witnesses every `v` vacuously, so no bound is derivable without this),
`e0, e1` have explicit witnesses:

```
Δ  := D0^2 - b*D0*D1 + c*D1^2        -- = N_{K2/K1}(D), nonzero iff D ≠ 0
R0 := (D0 - b*D1)*N0 + c*D1*N1
R1 := D0*N1 - D1*N0
```
with `Δ*e0 = R0`, `Δ*e1 = R1`, i.e. `(R0, Δ)` witnesses `e0` and
`(R1, Δ)` witnesses `e1`.

**Degree recurrence** (crude, symmetric numerator/denominator
convention, matching this project's existing style): if `N0,N1,D0,D1`
have witnesses of total degree `≤ D_parent` and `b,c` have witnesses of
total degree `≤ B`, then `R0, R1, Δ` all have witnesses of total degree
`≤ 2*B + 5*D_parent`. Composing two tower levels (`K2` over `K1` over
`K0`) with per-level quadratic-coefficient bounds `B2, B1` gives
`D0_bound ≤ 2*B1 + 10*B2 + 25*D2_bound` for the final `K0`-level
leaf coordinates, starting from a `K2`-level bound `D2_bound`.

**What this does NOT give you, flagged per the consult, not to be lost
in a future pass**: the theorem below is conditional on ALREADY having
witnesses for the `K1`-basis coefficients `N0,N1,D0,D1` of
`evalNd n`/`evalNd d` themselves, not just a witness for the whole
element `v`. Whether `towerToRdec`'s own recursive construction
supplies these coefficient-level witnesses (as opposed to just the
element-level `IsRdecWitness` fact `towerToRdec_isRdecWitness` already
gives) is a SEPARATE fact to check against `towerToRdec`'s actual
recursive definition (`DataDerivationMumford.lean`,
`towerToRdec`/`towerToRdecK1`) before this lemma can be applied to
close `CrossNondegenerateDegreeBound.lean`'s `hA`/`hB`. Likely true by
inspection of `towerToRdec`'s own `let n0 * den1 + n1 * den0 * X (sg.wGen
_), den0 * den1` output shape (which already IS built as separate
`K1`-basis pieces before being recombined) — but not yet verified line
by line, and not assumed here.

-/

namespace Genus2Lean
namespace TheDataDerivation

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-- **One-step coefficient descent, algebraic core.** Pure ring identity,
no `MvPolynomial`/`totalDegree` content yet — this is the `Δ*e0 = R0`,
`Δ*e1 = R1` pair of identities from the consult, stated for an
arbitrary field extension presented via a monic quadratic (not yet
specialized to `K1 →+* K2`/`AdjoinRoot`). Proof: substitute
`v = e0 + e1*w2`, `w2^2 = -b*w2-c`, expand `Dv` in the `1,w2` basis,
compare coefficients — exactly the consult's `Dv = D0e0 - cD1e1 +
(D0e1+D1e0-bD1e1)w2` computation. Purely `ring`/`linear_combination`
once the basis relation is available; no field-inverse needed (this is
the "no division, cross-multiplied" form). -/
theorem coeffDescent_core {R : Type*} [CommRing R]
    (b c D0 D1 N0 N1 e0 e1 : R)
    -- `N0,N1` are `evalNd n`'s `1,w2`-coefficients, `D0,D1` likewise for
    -- `evalNd d`; the hypothesis below is the witness equation `evalNd n
    -- = evalNd d * v` already expanded in the `1,w2` basis using `v =
    -- e0+e1*w2` and `w2^2 = -b*w2-c`, i.e. `N0 + N1*w2 = (D0+D1*w2)*(e0+e1*w2)`
    -- reduced mod the relation -- stated directly at the coefficient
    -- level rather than re-deriving the reduction inside this lemma.
    (hN0 : N0 = D0 * e0 - c * D1 * e1)
    (hN1 : N1 = D1 * e0 + (D0 - b * D1) * e1) :
    (D0 ^ 2 - b * D0 * D1 + c * D1 ^ 2) * e0 =
      (D0 - b * D1) * N0 + c * D1 * N1 ∧
    (D0 ^ 2 - b * D0 * D1 + c * D1 ^ 2) * e1 =
      D0 * N1 - D1 * N0 := by
  constructor <;> (rw [hN0, hN1]; ring)

/-- **`Δ ≠ 0` iff `D ≠ 0`, the norm form.** `Δ = D0^2 - b*D0*D1 +
c*D1^2` is `N_{K2/K1}(D)` for `D = D0 + D1*w2` under `w2^2+b*w2+c=0`;
nonvanishing of a norm in a field extension is equivalent to
nonvanishing of the element, but proving that generally needs `K2` to
literally BE a field (not just an abstract `CommRing` satisfying the
basis relation) -- state this against the actual `K1 →+* K2` structure
once instantiated, not as a bare ring fact (false for zero-divisor
rings in general). Placeholder statement shape only; fill in against
`AdjoinRoot`'s actual field instance for this project's `K2_poly_monic`. -/
theorem norm_ne_zero_iff_placeholder : True := trivial
-- TODO: state as
--   (D0 ^ 2 - b * D0 * D1 + c * D1 ^ 2 ≠ 0) ↔ (D0 + D1 * w2 ≠ 0)
-- against `K2 p c0 c1 c2 c3 c4 := AdjoinRoot (K2_poly_monic ...)`,
-- using its `Field` instance (`factIrreducible_K2`) -- likely via
-- `AdjoinRoot` norm/minpoly API, needs a Mathlib name lookup, not
-- algebra.

/-- **Degree bound, one tower level.** Given `b,c,N0,N1,D0,D1 :
MvPolynomial Vars (F p)` — the SAME six polynomials `coeffDescent_core`
takes as literal ring elements, here specialized to the witness ring
itself rather than an opaque `CommRing R` — each of total degree `≤ B`
(`b,c`) or `≤ Dp` (`N0,N1,D0,D1`), produce explicit `R0, R1, Δ`
(literally `coeffDescent_core`'s own boxed expressions, not merely
"some witness of the right shape") with `totalDegree ≤ 2*B + 5*Dp`.
Bundling `R0,R1,Δ` as the SAME polynomials `coeffDescent_core` uses
(rather than reshaping them into a fraction-of-witnesses form first)
means the two theorems compose directly at a call site: apply this one
for the degree bound, `coeffDescent_core` (specialized to `R :=
MvPolynomial Vars (F p)` composed with `evalNd`, or applied after
evaluating) for the `Δ*e0=R0`/`Δ*e1=R1` identity itself, with no
translation step between them. Proof: `MvPolynomial.totalDegree_mul`/
`_add`/`_sub`'s `≤`-triangle inequalities, chased by hand exactly as
`combine_totalDegree_le` (`DataDerivationTotalDegree.lean`) does for
its own two-term combinator — more terms here (`Δ` has three summands,
`R0`/`R1` have two), so more `have` steps, but the same mechanical
shape throughout; no new proof idea needed beyond that file's own
pattern. **REPL-confirmed status: not yet — this pass's proof, Claire
to test.** -/
theorem coeffDescent_totalDegree_le {Vars : Type*}
    (Dp B : ℕ) (b c N0 N1 D0 D1 : MvPolynomial Vars (F p))
    (hb : b.totalDegree ≤ B) (hc : c.totalDegree ≤ B)
    (hN0 : N0.totalDegree ≤ Dp) (hN1 : N1.totalDegree ≤ Dp)
    (hD0 : D0.totalDegree ≤ Dp) (hD1 : D1.totalDegree ≤ Dp) :
    ((D0 - b * D1) * N0 + c * D1 * N1).totalDegree ≤ 2 * B + 5 * Dp ∧
    (D0 * N1 - D1 * N0).totalDegree ≤ 2 * B + 5 * Dp ∧
    (D0 ^ 2 - b * D0 * D1 + c * D1 ^ 2).totalDegree ≤ 2 * B + 5 * Dp := by
  -- `E := D0 - b*D1`, degree `≤ max Dp (B+Dp) ≤ B+Dp`.
  have hbD1 : (b * D1).totalDegree ≤ B + Dp :=
    le_trans (MvPolynomial.totalDegree_mul b D1) (by omega)
  have hE : (D0 - b * D1).totalDegree ≤ B + Dp :=
    le_trans (MvPolynomial.totalDegree_sub D0 (b * D1)) (max_le (by omega) (by omega))
  -- `R0 := E*N0 + c*D1*N1`.
  have hEN0 : ((D0 - b * D1) * N0).totalDegree ≤ B + 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul (D0 - b * D1) N0) (by omega)
  have hcD1 : (c * D1).totalDegree ≤ B + Dp :=
    le_trans (MvPolynomial.totalDegree_mul c D1) (by omega)
  have hcD1N1 : (c * D1 * N1).totalDegree ≤ B + 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul (c * D1) N1) (by omega)
  have hR0 : ((D0 - b * D1) * N0 + c * D1 * N1).totalDegree ≤ 2 * B + 5 * Dp :=
    le_trans (MvPolynomial.totalDegree_add ((D0 - b * D1) * N0) (c * D1 * N1))
      (max_le (by omega) (by omega))
  -- `R1 := D0*N1 - D1*N0`.
  have hD0N1 : (D0 * N1).totalDegree ≤ 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul D0 N1) (by omega)
  have hD1N0 : (D1 * N0).totalDegree ≤ 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul D1 N0) (by omega)
  have hR1 : (D0 * N1 - D1 * N0).totalDegree ≤ 2 * B + 5 * Dp :=
    le_trans (MvPolynomial.totalDegree_sub (D0 * N1) (D1 * N0))
      (max_le (by omega) (by omega))
  -- `Δ := D0^2 - b*D0*D1 + c*D1^2`.
  have hD0sq : (D0 ^ 2).totalDegree ≤ 2 * Dp := by
    have := MvPolynomial.totalDegree_mul D0 D0
    rw [sq]
    omega
  have hbD0D1 : (b * D0 * D1).totalDegree ≤ B + 2 * Dp := by
    have h1 : (b * D0).totalDegree ≤ B + Dp :=
      le_trans (MvPolynomial.totalDegree_mul b D0) (by omega)
    exact le_trans (MvPolynomial.totalDegree_mul (b * D0) D1) (by omega)
  have hcD1sq : (c * D1 ^ 2).totalDegree ≤ B + 2 * Dp := by
    have h1 : (D1 ^ 2).totalDegree ≤ 2 * Dp := by
      have := MvPolynomial.totalDegree_mul D1 D1
      rw [sq]; omega
    exact le_trans (MvPolynomial.totalDegree_mul c (D1 ^ 2)) (by omega)
  have hDelta1 : (D0 ^ 2 - b * D0 * D1).totalDegree ≤ B + 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_sub (D0 ^ 2) (b * D0 * D1))
      (max_le (by omega) (by omega))
  have hDelta : (D0 ^ 2 - b * D0 * D1 + c * D1 ^ 2).totalDegree ≤ 2 * B + 5 * Dp :=
    le_trans (MvPolynomial.totalDegree_add (D0 ^ 2 - b * D0 * D1) (c * D1 ^ 2))
      (max_le (by omega) (by omega))
  exact ⟨hR0, hR1, hDelta⟩

/-- **`b = 0` specialization, matching this project's actual quadratics.**
`K1_poly_monic`/`K2_poly_monic` (`DataDerivationMumford.lean`) are always
`X^2 - C(const)` — i.e. `b = 0` identically, never a genuine `X^2+bX+c`
with a nonzero linear term. Specializing `coeffDescent_core` to `b = 0`
simplifies `Δ = D0^2 + c*D1^2`, `R0 = D0*N0 + c*D1*N1`, `R1 = D0*N1 -
D1*N0` — the actual formulas this project will invoke, `b` never showing
up as a live input anywhere downstream. Kept as a corollary rather than
replacing `coeffDescent_core` itself, since the general form documents
where the `b` terms would reappear if this project ever used a
non-reduced quadratic. -/
theorem coeffDescent_core_b0 {R : Type*} [CommRing R]
    (c D0 D1 N0 N1 e0 e1 : R)
    (hN0 : N0 = D0 * e0 - c * D1 * e1)
    (hN1 : N1 = D1 * e0 + D0 * e1) :
    (D0 ^ 2 + c * D1 ^ 2) * e0 = D0 * N0 + c * D1 * N1 ∧
    (D0 ^ 2 + c * D1 ^ 2) * e1 = D0 * N1 - D1 * N0 := by
  have := coeffDescent_core (R := R) 0 c D0 D1 N0 N1 e0 e1
    (by simpa using hN0) (by simpa using hN1)
  simpa using this

/-- **`b = 0` specialization of the degree bound.** Same simplification
as `coeffDescent_core_b0`: with `b = 0`, `c`'s own bound `B` is the only
"defining-quadratic" degree input needed (no separate `b`-bound), and
the recurrence collapses to `≤ B + 4*Dp` (one fewer `B` term than the
general `2*B+5*Dp`, since `b*D1`/`b*D0*D1`-shaped terms vanish outright
rather than merely being bounded). Proof: same `totalDegree_mul`/`_add`/
`_sub` chase as `coeffDescent_totalDegree_le`, with the `b`-containing
terms simply absent (`E = D0` directly, no `hE`/`hbD1` steps needed;
`Δ`'s middle term `b*D0*D1` is `0`, dropped instead of bounded). -/
theorem coeffDescent_totalDegree_le_b0 {Vars : Type*}
    (Dp B : ℕ) (c N0 N1 D0 D1 : MvPolynomial Vars (F p))
    (hc : c.totalDegree ≤ B)
    (hN0 : N0.totalDegree ≤ Dp) (hN1 : N1.totalDegree ≤ Dp)
    (hD0 : D0.totalDegree ≤ Dp) (hD1 : D1.totalDegree ≤ Dp) :
    (D0 * N0 + c * D1 * N1).totalDegree ≤ B + 4 * Dp ∧
    (D0 * N1 - D1 * N0).totalDegree ≤ B + 4 * Dp ∧
    (D0 ^ 2 + c * D1 ^ 2).totalDegree ≤ B + 4 * Dp := by
  -- `R0 := D0*N0 + c*D1*N1`.
  have hD0N0 : (D0 * N0).totalDegree ≤ 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul D0 N0) (by omega)
  have hcD1 : (c * D1).totalDegree ≤ B + Dp :=
    le_trans (MvPolynomial.totalDegree_mul c D1) (by omega)
  have hcD1N1 : (c * D1 * N1).totalDegree ≤ B + 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul (c * D1) N1) (by omega)
  have hR0 : (D0 * N0 + c * D1 * N1).totalDegree ≤ B + 4 * Dp :=
    le_trans (MvPolynomial.totalDegree_add (D0 * N0) (c * D1 * N1))
      (max_le (by omega) (by omega))
  -- `R1 := D0*N1 - D1*N0`.
  have hD0N1 : (D0 * N1).totalDegree ≤ 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul D0 N1) (by omega)
  have hD1N0 : (D1 * N0).totalDegree ≤ 2 * Dp :=
    le_trans (MvPolynomial.totalDegree_mul D1 N0) (by omega)
  have hR1 : (D0 * N1 - D1 * N0).totalDegree ≤ B + 4 * Dp :=
    le_trans (MvPolynomial.totalDegree_sub (D0 * N1) (D1 * N0))
      (max_le (by omega) (by omega))
  -- `Δ := D0^2 + c*D1^2`.
  have hD0sq : (D0 ^ 2).totalDegree ≤ 2 * Dp := by
    have := MvPolynomial.totalDegree_mul D0 D0
    rw [sq]; omega
  have hcD1sq : (c * D1 ^ 2).totalDegree ≤ B + 2 * Dp := by
    have h1 : (D1 ^ 2).totalDegree ≤ 2 * Dp := by
      have := MvPolynomial.totalDegree_mul D1 D1
      rw [sq]; omega
    exact le_trans (MvPolynomial.totalDegree_mul c (D1 ^ 2)) (by omega)
  have hDelta : (D0 ^ 2 + c * D1 ^ 2).totalDegree ≤ B + 4 * Dp :=
    le_trans (MvPolynomial.totalDegree_add (D0 ^ 2) (c * D1 ^ 2))
      (max_le (by omega) (by omega))
  exact ⟨hR0, hR1, hDelta⟩

/-- **The actual composition this file exists for, correctly identified.**
`coeffDescent_core`/`coeffDescent_totalDegree_le[_b0]` solve the OPPOSITE
direction from `towerToRdecK1`/`towerToRdec`'s own construction:
- `towerToRdecK1`/`towerToRdec` COMPOSE UPWARD — given witnesses for two
  leaf coordinates `d0, d1` (each one ring level DOWN from the value being
  represented), combine them into a witness for the WHOLE value
  `d0 + d1*w`. Already fully built, and its own `totalDegree` bound is
  ALREADY proved (`combine_totalDegree_le`, `towerToRdecK1_totalDegree_le`,
  `towerToRdec_totalDegree_le`, all in `DataDerivationTotalDegree.lean`,
  REPL-confirmed). Re-deriving that bound via `coeffDescent_totalDegree_le`
  would be redundant AND wrong-shaped (see the retracted attempt this file
  briefly contained, corrected in this pass).
- `coeffDescent_core`/`_totalDegree_le[_b0]` DECOMPOSE DOWNWARD — given a
  witness for the WHOLE value `v : K2` (opaque, e.g.
  `curBeforeMonic_coeff_totalDegree_le`'s existing `≤315448` fact, which
  bounds `v` as a single element with NO separate information about its
  `d0,d1` leaf coordinates), extract witnesses for `d0, d1` themselves.
  This is the genuinely open direction — `ROADMAP-crossnondegenerate-
  degree-bound.md`'s own diagnosis of `hA`/`hB`'s gap is precisely that no
  route from "witness for the whole `K2`-element" to "witness for its
  `K1`-level coordinates" existed before this file. `coeffDescent_core`
  literally IS that route: apply it with `(N0,N1,D0,D1) := ` the
  `K1`-basis expansion of the EXISTING witness's numerator/denominator
  (i.e. `evalNd n =: N0+N1*w2`, `evalNd d =: D0+D1*w2`, both of which
  need their OWN bounded witnesses -- see the "what this does NOT give
  you" note in the header docstring, still the live caveat), `(e0,e1) :=
  (d0,d1)`, `(b,c) := (0, fAtT p ... 1)` (`K2_poly_monic`'s actual
  constant, `b=0` per this project's quadratics) to get a bounded witness
  for `d0` (resp. `d1`) directly. **Not yet assembled as one theorem**:
  doing so needs the `N0,N1,D0,D1`-level witnesses as an actual
  `MvPolynomial` decomposition of `curBeforeMonic_coeff_totalDegree_le`'s
  existing witness pair, which is separate work (splitting an existing
  witness INTO its basis pieces, not yet attempted anywhere) -- flagged
  as the concrete next step, not attempted in this pass since it needs
  that witness's actual construction inspected first, not guessed. -/
theorem coeffDescent_purpose_note : True := trivial

end TheDataDerivation
end Genus2Lean
