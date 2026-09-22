import Mathlib
import Genus2Lean.IndexCalculusComplexity
import Genus2Lean.SidonDichotomyGeneral
set_option linter.style.header false

/-!
# Closing the `hRate` gap for the REAL curve: `~B²` distinct relations,
# unconditionally, from `SidonDichotomyGeneral`

## The gap this file closes

`IndexCalculusComplexity.lean` proves the balance derivation `B⁵ = p² ⟹
B² = p^(4/5)` as pure real-number algebra (`index_calculus_complexity`),
and separately proves an UNCONDITIONAL relation-count lower bound
`matchCount_distinct_hits_ge_unconditional` — but only at the trivial
fiber-cap `M = B³`, which yields just `~B` distinct relations, too weak
to feed the balance argument at its own claimed rate (`N ~ B²` solves at
rate `B⁴/p²` needs `~B²`, not `~B`, distinct hits available in the worst
case for the reachability story to even be plausible). The file's own
docstring flags the sharper `M = 2B²` (Sidon) instantiation as available
in principle but leaves it as "a modeling choice," `hRate` staying an
assumed hypothesis throughout.

**What was missed:** `SidonDichotomyGeneral.lean` already proves, for the
REAL curve over `F_p` (not an abstract group `G`), a `sorry`-free,
unconditional (in `p`) statement of exactly this sharper form —
`hitCount_ge_of_sidonDichotomy_nonInvolution_general`: at least
`T.card²/2` distinct `Δ` are hit, for `T := sidonSet (principalDivisorData
H hdeg) δ₀ F`, needing only `hchar`, `hsf`, `AvoidsInvolutionPairs F`,
`NoWeierstrassPoints F` — no `SidonDichotomy` hypothesis, no fiber-cap
assumption. It was never chained to `IndexCalculusComplexity.lean`'s
balance machinery; nothing outside `SidonDichotomyGeneral.lean` and
`SidonBridge.lean`'s prose even names it.

## What this file adds, precisely

* `hitCount_ge_half_card_sq_real`: restates the existing bound with
  `B := T.card` cast to `ℝ`, matching `IndexCalculusComplexity.lean`'s
  variable naming, for direct use with `balance_forces_fifth_power`-style
  arithmetic.
* `distinct_hits_ge_of_balance_real`: **the actual bridge.** If `B⁵ = p²`
  (the SAME balance equation `index_calculus_complexity` already
  concludes total cost from), the guaranteed distinct-hit count `B²/2` is
  at least `B` — i.e. the worst-case existence guarantee for the real
  curve already MEETS the `~B` relations the balance needs, with room to
  spare (`B²/2 ≥ B` once `B ≥ 2`), confirming `B⁵ = p²` is not merely an
  assumed balance point but one where enough relations demonstrably
  EXIST, unconditionally, for the actual curve.

## What this does NOT close (still honestly open)

This is an EXISTENCE bound: `matchCount T Δ ≠ 0` for `≥ B²/2` values of
`Δ`, over the WHOLE space of `B⁴` quadruples — not a statement about how
many solve ATTEMPTS `N` a sampler needs to actually find them.
`IndexCalculusReachability.lean`'s open item (`SolverReaches`, `|Sol Δ| ≤
d`) is exactly the missing link from "these relations exist" to "a solver
running `N` attempts finds `~B` of them" — per last pass's read, bridging
that needs new model glue (an `H.Point`-level notion of `q : G → ℝ`) that
doesn't exist on file, and is NOT attempted here either. What this file
DOES establish: the `hRate`/`expectedRelations` assumption in
`IndexCalculusComplexity.lean` is now known to be compatible with a real,
unconditional existence fact at the SAME exponent (`~B²`, not just
`~B`) — the balance point `B⁵ = p²` is not vacuous or contradicted by
what can be proved about the real curve; it undersells nothing that is
actually available. `hRate` itself — turning "the relations exist" into
"a solve finds one with the claimed probability" — remains an assumed
sampling heuristic, exactly as flagged, just no longer resting on an
unconnected sharper bound sitting idle in another file.

## Verification status

Drafted without a Lean toolchain, per the working agreement — NOT `lake
build`-checked.
-/

open HyperellipticPolynomial

namespace Genus2Lean
namespace IndexCalculusComplexityRealHitCount

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]
variable [Fintype k] [DecidableEq k]

/-- **The real-curve hit-count bound, restated with `B := T.card : ℝ`** to
match `IndexCalculusComplexity.lean`'s variable-naming convention. Pure
notational restatement of `hitCount_ge_of_sidonDichotomy_nonInvolution_general`
(`SidonDichotomyGeneral.lean`) — no new content. -/
theorem hitCount_ge_half_card_sq_real
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    [Fintype (Jacobian H (principalDivisorData H hdeg))]
    [DecidableEq (Jacobian H (principalDivisorData H hdeg))]
    (δ₀ : H.Point) (F : Finset H.Point)
    (hAvoid : AvoidsInvolutionPairs F) (hNoWeier : NoWeierstrassPoints F)
    (hcard_pos : 0 < (sidonSet (principalDivisorData H hdeg) δ₀ F).card) :
    ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ) ^ 2 / 2 ≤
      ((Finset.univ.filter
        (fun Δ : Jacobian H (principalDivisorData H hdeg) =>
          matchCount (sidonSet (principalDivisorData H hdeg) δ₀ F) Δ ≠ 0)).card : ℝ) :=
  hitCount_ge_of_sidonDichotomy_nonInvolution_general hdeg hchar hsf δ₀ F
    hAvoid hNoWeier hcard_pos

/-- **The bridge: at the complexity balance point `B⁵ = p²`, the real
curve's worst-case existence guarantee (`≥ B²/2` distinct hits) already
covers the `~B` relations the balance derivation needs — with room to
spare (`B²/2 ≥ B` once `B ≥ 2`, true a fortiori once `B ~ p^(2/5)` for any
cryptographically-sized `p`).** This is pure real algebra plumbing (no
new geometric content beyond `hitCount_ge_half_card_sq_real` above): it
does not derive `B⁵ = p²` from anything, it confirms that GIVEN that
balance point, the quantity `IndexCalculusComplexity.lean`'s model calls
`~B` relations is demonstrably available (not just assumed) at the
matching order of magnitude, for the real curve, unconditionally. -/
theorem half_card_sq_ge_card_of_balance
    (B p : ℝ) (hB : 2 ≤ B) (hp : 0 < p) (hbal : B ^ 5 = p ^ 2) :
    B ≤ B ^ 2 / 2 := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith

/-- **Assembled statement.** For the real curve, at the balance point
`B⁵ = p²` (the same hypothesis `total_cost_eq_rpow` needs to conclude
`B² = p^(4/5)`), with a factor base `F` avoiding involution pairs and
Weierstrass points and `B := (sidonSet (principalDivisorData H hdeg) δ₀
F).card` satisfying `2 ≤ B`: the guaranteed distinct-hit count is at
least `B`, i.e. at least as many relations as the balance derivation
needs, UNCONDITIONALLY (no `hRate`/sampling assumption anywhere in this
theorem's own hypotheses — only `hchar`, `hsf`,
`AvoidsInvolutionPairs`/`NoWeierstrassPoints`, and the balance equation
itself), and the total cost is `p^(4/5)`. -/
theorem index_calculus_complexity_real_hitCount
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    [Fintype (Jacobian H (principalDivisorData H hdeg))]
    [DecidableEq (Jacobian H (principalDivisorData H hdeg))]
    (δ₀ : H.Point) (F : Finset H.Point)
    (hAvoid : AvoidsInvolutionPairs F) (hNoWeier : NoWeierstrassPoints F)
    (p : ℝ) (hp : 0 < p)
    (hB : 2 ≤ ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ))
    (hbal : ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ) ^ 5 = p ^ 2) :
    (((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ)) ≤
      ((Finset.univ.filter
        (fun Δ : Jacobian H (principalDivisorData H hdeg) =>
          matchCount (sidonSet (principalDivisorData H hdeg) δ₀ F) Δ ≠ 0)).card : ℝ)
    ∧ ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ) ^ 2 = p ^ ((4 : ℝ) / 5) := by
  have hcard_pos : 0 < (sidonSet (principalDivisorData H hdeg) δ₀ F).card := by
    have : (0:ℝ) < ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ) :=
      lt_of_lt_of_le (by norm_num) hB
    exact_mod_cast this
  have hhit := hitCount_ge_half_card_sq_real hdeg hchar hsf δ₀ F hAvoid hNoWeier hcard_pos
  have hstep := half_card_sq_ge_card_of_balance
    ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ) p hB hp hbal
  refine ⟨le_trans hstep hhit, ?_⟩
  have hBpos : (0:ℝ) < ((sidonSet (principalDivisorData H hdeg) δ₀ F).card : ℝ) :=
    lt_of_lt_of_le (by norm_num) hB
  exact total_cost_eq_rpow _ p hBpos hp hbal

end IndexCalculusComplexityRealHitCount
end Genus2Lean
