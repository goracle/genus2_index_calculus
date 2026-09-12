import Mathlib
import Genus2Lean.ZeroD.QuadraticCoordArith

/-!
# Forward-tracking coordinate-height machinery for a monic-quadratic tower level

New this pass. Per a ChatGPT consult on `ROADMAP-crossnondegenerate-degree-bound.md`'s
last-flagged, still-open gap: turning `curBeforeMonic_coeff_totalDegree_le`'s existing
**whole-value existential** `IsRdecWitness`/`IsLocalization.mk'`-style degree bound (`≤315448`,
already proved) into a **literal, per-coordinate** bound on `uRS`/`vRS`'s `K1`/`K0`-level
`AdjoinRoot.modByMonicHom`-coefficients — needed because `towerToRdec_coeff_totalDegree_le`
(`DataDerivationTotalDegree.lean`) wants exactly such a literal coordinate bound as its
hypothesis, not an existential witness for the whole tower element.

**The consult's diagnosis, confirmed against this project's own three prior ruled-out
attempts** (`QuadraticCoordinateBridge.lean`'s two, `TowerCoeffWitnessDescent.lean`'s
opposite-direction one): there is no general operation recovering a coordinate certificate
from an existential whole-value witness after the fact. The fix is to **stop treating a tower
element as an opaque value and instead carry a degree "budget" on its own `(coeff 0, coeff 1)`
coordinates forward through the same finite sequence of algebraic operations that built it** —
never touching the existential witness machinery at all. This file supplies exactly that
generic machinery for ONE quadratic tower level (`AdjoinRoot (X^2 - C c)` over a base ring
`R`), reusable verbatim at both the `K0 → K1` and `K1 → K2` steps, matching
`QuadraticCoordArith.lean`'s own precedent of proving the coordinate-multiplication identity
generically once rather than twice.

**Design, per the consult's own recommended shape (§8)**: `HasQuadBound c x (a0, a1)` says
`x`'s two `%ₘ (X^2 - C c)`-coordinates (`AdjoinRoot.mk`'s canonical representative, matching
`modByMonicHom` exactly per `AdjoinRoot.modByMonicHom_mk`) are witnessed by base-ring elements
of `totalDegree ≤ a0`/`≤ a1` respectively — i.e. this is the DEGREE-BOUND analogue of
`IsRdecWitness`, but phrased on `x`'s canonical coordinates directly rather than via an
arbitrary cross-multiplied witness pair for `x` as a whole. Proved closed under `zero`, `one`,
`add`, `neg`, `sub`, `mul`, `pow`, matching the consult's crude coordinate-arithmetic bounds
exactly (`(xy)0 ≤ max(a0+b0, dc+a1+b1)`, `(xy)1 ≤ max(a0+b1, a1+b0)`, `dc` a bound on `c`
itself). **Division is NOT included in this pass** — the consult's conjugate/norm-based
`div` rule (§3) needs `c` to be a genuine nonzero-square-obstruction, i.e. field-level
reasoning about `b0² - c*b1² ≠ 0`, which is exactly the kind of per-point nonvanishing
condition this project already threads as an honest named hypothesis elsewhere
(`Nondegenerate`, `CrossNondegenerate`) rather than derives — left for the specific
instantiation site to supply if/when it's needed, rather than baked into this generic file.

**Not yet REPL-confirmed** — drafted this pass; Claire tests via the REPL. Update: first REPL
run surfaced five issues, four now fixed: (1) `hasQuadBound_one`'s `compute_degree!` step left a
stray `↑2 = 2` cast goal — closed with `norm_num`; (2) same stray cast goal inside
`hasQuadBound_mul`'s degree computation — same fix; (3) `hasQuadBound_add` built its `.sub`
argument via an unnecessary double-negation (`-(-y)` then `.neg` of that, landing on a
triple-negated term `assumption` couldn't close) — simplified to negate `hy` once and use
`sub_neg_eq_add` directly; (4) `hasQuadBound_pow`'s argument-order bug (`pow_succ : x^(k+1) =
x^k * x` needs the induction hypothesis first, `hx` second — the original had them backwards).
(5) `hasQuadBound_mul`'s multiplication-identity derivation has now been rewritten TWICE: the
first draft's direct `%ₘ`-level expansion timed out at `whnf`; the second draft (routing through
`mk_mul_coord_eq` via a local `set g := X^2 - C c`) also hung even after Claire raised the
heartbeat limit, traced to a `set`/`unfold HasQuadBound`/`rw [← hgdef]` fold-unfold fight at the
end of the proof. Third draft (current): no local name for `X^2 - C c` anywhere, final goals
closed via `show` instead of `unfold`+`rw`. Still awaiting Claire's re-run to confirm this one
actually terminates.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-! ## The bound predicate -/

/-- **`x`'s canonical quadratic-extension coordinates are degree-bounded.**
`c : R` is the extension's defining constant (`AdjoinRoot (X^2 - C c)`), `x : Polynomial R` is
any representative (typically fed via `AdjoinRoot.mk`), and `(a0, a1)` bound the `totalDegree`
of `x %ₘ (X^2 - C c)`'s two coefficients — which, by `modByMonic_X_sq_sub_C_eq`
(`QuadraticCoordArith.lean`), are exactly `x`'s own canonical `(coeff 0, coeff 1)` normal-form
pair. Phrased directly in terms of `Polynomial.coeff`'s `Nat`-valued `totalDegree` (no
`MvPolynomial`/`IsLocalization` detour at this generic layer) since the actual base ring `R`
varies by instantiation (`K0 p` at the `K0→K1` step, `K1 p ...` at the `K1→K2` step) and each
level's own notion of "degree" is supplied externally via the `dg : R → ℕ` parameter below,
rather than fixed to `MvPolynomial.totalDegree` here — keeping this file's machinery agnostic
to which concrete degree notion the instantiation site uses. -/
def HasQuadBound (dg : R → ℕ) (c : R) (x : Polynomial R) (a0 a1 : ℕ) : Prop :=
  dg ((x %ₘ (X ^ 2 - C c)).coeff 0) ≤ a0 ∧ dg ((x %ₘ (X ^ 2 - C c)).coeff 1) ≤ a1

/-! ## Closure lemmas, matching the consult's forward coordinate-arithmetic exactly

Throughout, `dg : R → ℕ` is an arbitrary "degree" function satisfying only the two structural
facts every reasonable degree notion has (`dg 0 = 0`, and `dg` sub-multiplicative/sub-additive
under `+`/`*`) — stated as explicit hypotheses per lemma rather than a typeclass, since this
file is only ever instantiated twice and a typeclass would be overhead without reuse. -/

/-- **Zero.** The zero polynomial's remainder is zero, so both coordinates are literally `0`,
degree-bounded by `dg 0` (typically `0`, but stated with `dg 0` directly so the caller supplies
whatever their own `dg 0 = 0` fact gives — avoiding baking in an extra hypothesis unused
elsewhere in this section). -/
theorem hasQuadBound_zero (dg : R → ℕ) (c : R) :
    HasQuadBound dg c (0 : Polynomial R) (dg 0) (dg 0) := by
  unfold HasQuadBound
  simp

/-- **One.** `1 %ₘ (X^2 - C c) = 1` (degree `0 < 2`, so the monic-remainder is the polynomial
itself), giving `coeff 0 = 1`, `coeff 1 = 0`. -/
theorem hasQuadBound_one (dg : R → ℕ) (c : R) (hone : dg (1 : R) ≤ 1) (hzero : dg (0 : R) ≤ 1) :
    HasQuadBound dg c (1 : Polynomial R) 1 1 := by
  have hgmonic := monic_X_sq_sub_C (R := R) c
  have hgdeg : (X ^ 2 - C c : Polynomial R).degree = 2 := by
    have hnd : (X ^ 2 - C c : Polynomial R).natDegree = 2 := by compute_degree!
    rw [Polynomial.degree_eq_natDegree hgmonic.ne_zero, hnd]
    norm_num
  have hlt : (1 : Polynomial R).degree < (X ^ 2 - C c : Polynomial R).degree := by
    rw [hgdeg]; simp
  have hmod : (1 : Polynomial R) %ₘ (X ^ 2 - C c) = 1 :=
    Polynomial.modByMonic_eq_self_iff hgmonic |>.mpr hlt
  unfold HasQuadBound
  rw [hmod]
  simp only [Polynomial.coeff_one]
  norm_num
  exact ⟨hone, hzero⟩

/-- **Negation.** `%ₘ` respects negation unconditionally (`Polynomial.neg_modByMonic`, no
`Monic` hypothesis needed — confirmed against current Mathlib4 docs, not assumed from memory);
`dg` is assumed negation-invariant (`dg (-u) = dg u`, true for every degree-style notion this
project uses, e.g. `MvPolynomial.totalDegree_neg`). -/
theorem hasQuadBound_neg (dg : R → ℕ) (c : R)
    (hdg_neg : ∀ u : R, dg (-u) = dg u)
    {x : Polynomial R} {a0 a1 : ℕ} (hx : HasQuadBound dg c x a0 a1) :
    HasQuadBound dg c (-x) a0 a1 := by
  obtain ⟨hx0, hx1⟩ := hx
  unfold HasQuadBound
  rw [Polynomial.neg_modByMonic]
  refine ⟨?_, ?_⟩
  · rw [Polynomial.coeff_neg, hdg_neg]; exact hx0
  · rw [Polynomial.coeff_neg, hdg_neg]; exact hx1

/-- **Subtraction.** `%ₘ` respects subtraction unconditionally
(`Polynomial.sub_modByMonic (p₁ p₂ q) : (p₁ - p₂) %ₘ q = p₁ %ₘ q - p₂ %ₘ q`, confirmed against
current Mathlib4 docs, no `Monic` hypothesis needed), so coordinates subtract coordinatewise —
proved directly (not via `.add`/`.neg`, since `Polynomial.add_modByMonic` was NOT confirmed to
exist under that name in current Mathlib4, while `sub_modByMonic`/`neg_modByMonic` both are). -/
theorem hasQuadBound_sub (dg : R → ℕ) (c : R)
    (hdg_add : ∀ u v : R, dg (u + v) ≤ max (dg u) (dg v))
    (hdg_neg : ∀ u : R, dg (-u) = dg u)
    {x y : Polynomial R} {a0 a1 b0 b1 : ℕ}
    (hx : HasQuadBound dg c x a0 a1) (hy : HasQuadBound dg c y b0 b1) :
    HasQuadBound dg c (x - y) (max a0 b0) (max a1 b1) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  unfold HasQuadBound
  rw [Polynomial.sub_modByMonic]
  constructor
  · calc dg ((x %ₘ (X ^ 2 - C c) - y %ₘ (X ^ 2 - C c)).coeff 0)
        = dg ((x %ₘ (X ^ 2 - C c)).coeff 0 - (y %ₘ (X ^ 2 - C c)).coeff 0) := by
          rw [Polynomial.coeff_sub]
      _ = dg ((x %ₘ (X ^ 2 - C c)).coeff 0 + -(y %ₘ (X ^ 2 - C c)).coeff 0) := by
          rw [sub_eq_add_neg]
      _ ≤ max (dg ((x %ₘ (X ^ 2 - C c)).coeff 0)) (dg (-(y %ₘ (X ^ 2 - C c)).coeff 0)) :=
          hdg_add _ _
      _ = max (dg ((x %ₘ (X ^ 2 - C c)).coeff 0)) (dg ((y %ₘ (X ^ 2 - C c)).coeff 0)) := by
          rw [hdg_neg]
      _ ≤ max a0 b0 := max_le_max hx0 hy0
  · calc dg ((x %ₘ (X ^ 2 - C c) - y %ₘ (X ^ 2 - C c)).coeff 1)
        = dg ((x %ₘ (X ^ 2 - C c)).coeff 1 - (y %ₘ (X ^ 2 - C c)).coeff 1) := by
          rw [Polynomial.coeff_sub]
      _ = dg ((x %ₘ (X ^ 2 - C c)).coeff 1 + -(y %ₘ (X ^ 2 - C c)).coeff 1) := by
          rw [sub_eq_add_neg]
      _ ≤ max (dg ((x %ₘ (X ^ 2 - C c)).coeff 1)) (dg (-(y %ₘ (X ^ 2 - C c)).coeff 1)) :=
          hdg_add _ _
      _ = max (dg ((x %ₘ (X ^ 2 - C c)).coeff 1)) (dg ((y %ₘ (X ^ 2 - C c)).coeff 1)) := by
          rw [hdg_neg]
      _ ≤ max a1 b1 := max_le_max hx1 hy1

/-- **Addition**, as `x - (-y)`, purely a convenience corollary now that `.sub`/`.neg` are both
proved directly from confirmed Mathlib lemmas. -/
theorem hasQuadBound_add (dg : R → ℕ) (c : R)
    (hdg_add : ∀ u v : R, dg (u + v) ≤ max (dg u) (dg v))
    (hdg_neg : ∀ u : R, dg (-u) = dg u)
    {x y : Polynomial R} {a0 a1 b0 b1 : ℕ}
    (hx : HasQuadBound dg c x a0 a1) (hy : HasQuadBound dg c y b0 b1) :
    HasQuadBound dg c (x + y) (max a0 b0) (max a1 b1) := by
  have hny : HasQuadBound dg c (-y) b0 b1 := hasQuadBound_neg dg c hdg_neg hy
  have hxy := hasQuadBound_sub dg c hdg_add hdg_neg hx hny
  rwa [sub_neg_eq_add] at hxy

/-- **Multiplication — the consult's headline forward rule.** Given coordinate bounds
`(a0,a1)`/`(b0,b1)` for `x`/`y` and a bound `dc` on `c` itself, `x*y`'s coordinates are bounded
by `max(a0+b0, dc+a1+b1)` / `max(a0+b1, a1+b0)` — exactly the crude bound the consult states,
now as an actual Lean theorem. **Revised route (twice — the original direct `%ₘ`-level
derivation of the identity timed out at `whnf`, and the first `mk_mul_coord_eq`-based rewrite
also hung even after raising the heartbeat limit, from a `set g := X^2 - C c` /
`unfold HasQuadBound` / `rw [← hgdef]` fold-unfold fight)**: this version never introduces a
local name for `X ^ 2 - C c` at all — every step works with the literal polynomial, and the
final two goals are closed by `show` (stating the unfolded `HasQuadBound` goal directly) rather
than `unfold` + `rw`, so `heq`'s LHS matches the goal syntactically with no defeq search. The
identity itself still comes from `mk_mul_coord_eq` (`QuadraticCoordArith.lean`, already
REPL-confirmed green) via `AdjoinRoot.mk`/`modByMonicHom_mk`. `dg` is assumed sub-multiplicative
(`dg (u*v) ≤ dg u + dg v`) on top of the sub-additivity `.sub`/`.add` already use. -/
theorem hasQuadBound_mul (dg : R → ℕ) (c : R) {dc : ℕ} (hc : dg c ≤ dc)
    (hdg_add : ∀ u v : R, dg (u + v) ≤ max (dg u) (dg v))
    (hdg_mul : ∀ u v : R, dg (u * v) ≤ dg u + dg v)
    {x y : Polynomial R} {a0 a1 b0 b1 : ℕ}
    (hx : HasQuadBound dg c x a0 a1) (hy : HasQuadBound dg c y b0 b1) :
    HasQuadBound dg c (x * y) (max (a0 + b0) (dc + a1 + b1)) (max (a0 + b1) (a1 + b0)) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have hgmonic := monic_X_sq_sub_C (R := R) c
  -- Work entirely with the literal `X ^ 2 - C c` — no local `set` abbreviation for it — so the
  -- final `HasQuadBound` goal (itself stated against the literal polynomial) matches `heq`
  -- syntactically instead of needing a `set`/`unfold` fold-unfold dance, which is what caused
  -- the previous version to hang even after raising the heartbeat limit.
  set x0 := (x %ₘ (X ^ 2 - C c)).coeff 0 with hx0def
  set x1 := (x %ₘ (X ^ 2 - C c)).coeff 1 with hx1def
  set y0 := (y %ₘ (X ^ 2 - C c)).coeff 0 with hy0def
  set y1 := (y %ₘ (X ^ 2 - C c)).coeff 1 with hy1def
  -- Route the identity through `mk_mul_coord_eq` (already REPL-confirmed in
  -- `QuadraticCoordArith.lean`) instead of re-deriving it at the `%ₘ` level directly — the
  -- direct `%ₘ`-level route is what timed out originally.
  have hmk : AdjoinRoot.mk (X ^ 2 - C c) (x * y) =
      AdjoinRoot.mk (X ^ 2 - C c)
        (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X) :=
    mk_mul_coord_eq c x y
  -- `AdjoinRoot.mk g` has kernel exactly the multiples of `g`, and both sides above have
  -- `%ₘ g`-degree `< 2` (the RHS by construction, the LHS's remainder equals it once we
  -- apply `modByMonicHom`), so `mk`-equality gives `%ₘ`-equality via `modByMonicHom_mk`.
  have hgdeg : (X ^ 2 - C c : Polynomial R).natDegree = 2 := by compute_degree!
  have hrhs_natdeg : (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X :
      Polynomial R).natDegree ≤ 1 := by compute_degree
  -- Work purely in `natDegree`/`Nat` terms as long as possible (never `WithBot ℕ`-level
  -- `calc`/`norm_num`), converting to `degree < degree` only at the very end via
  -- `degree_le_of_natDegree_le` (no nonzero side-condition, unlike `natDegree_lt_iff_degree_lt`)
  -- plus `degree_eq_natDegree` on the (nonzero, monic) LHS — this is what avoids the `whnf`
  -- timeout that repeated `WithBot`-level steps were hitting.
  have hrhs_lt : (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X :
      Polynomial R).degree < (X ^ 2 - C c : Polynomial R).degree := by
    have hle : (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X :
        Polynomial R).degree ≤ ((1 : ℕ) : WithBot ℕ) :=
      Polynomial.degree_le_of_natDegree_le hrhs_natdeg
    have hgdeg' : (X ^ 2 - C c : Polynomial R).degree = ((2 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hgmonic.ne_zero, hgdeg]
    calc (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X : Polynomial R).degree
        ≤ ((1 : ℕ) : WithBot ℕ) := hle
      _ < ((2 : ℕ) : WithBot ℕ) := by exact_mod_cast (by norm_num : (1:ℕ) < 2)
      _ = (X ^ 2 - C c : Polynomial R).degree := hgdeg'.symm
  have hrhs_mod : (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X) %ₘ (X ^ 2 - C c) =
      C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X :=
    (Polynomial.modByMonic_eq_self_iff hgmonic).mpr hrhs_lt
  have heq : x * y %ₘ (X ^ 2 - C c) = C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X := by
    have h1 : AdjoinRoot.modByMonicHom hgmonic (AdjoinRoot.mk (X ^ 2 - C c) (x * y)) =
        x * y %ₘ (X ^ 2 - C c) :=
      AdjoinRoot.modByMonicHom_mk hgmonic (x * y)
    have h2 : AdjoinRoot.modByMonicHom hgmonic
        (AdjoinRoot.mk (X ^ 2 - C c)
          (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X)) =
        (C (x0 * y0 + c * x1 * y1) + C (x0 * y1 + x1 * y0) * X) %ₘ (X ^ 2 - C c) :=
      AdjoinRoot.modByMonicHom_mk hgmonic _
    rw [← h1, hmk, h2, hrhs_mod]
  refine ⟨?_, ?_⟩
  · show dg ((x * y %ₘ (X ^ 2 - C c)).coeff 0) ≤ max (a0 + b0) (dc + a1 + b1)
    rw [heq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_zero, mul_zero, add_zero, if_pos rfl]
    calc dg (x0 * y0 + c * x1 * y1)
        ≤ max (dg (x0 * y0)) (dg (c * x1 * y1)) := hdg_add _ _
      _ ≤ max (a0 + b0) (dc + a1 + b1) := by
          apply max_le_max
          · exact (hdg_mul x0 y0).trans (Nat.add_le_add hx0 hy0)
          · calc dg (c * x1 * y1) ≤ dg (c * x1) + dg y1 := hdg_mul _ _
              _ ≤ (dg c + dg x1) + dg y1 := Nat.add_le_add_right (hdg_mul c x1) _
              _ ≤ (dc + a1) + b1 := by
                  have := Nat.add_le_add (Nat.add_le_add hc hx1) hy1
                  omega
              _ = dc + a1 + b1 := by ring
  · show dg ((x * y %ₘ (X ^ 2 - C c)).coeff 1) ≤ max (a0 + b1) (a1 + b0)
    rw [heq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_zero, Polynomial.coeff_X_one, mul_zero, mul_one, add_zero, zero_add,
      if_neg (one_ne_zero)]
    calc dg (x0 * y1 + x1 * y0)
        ≤ max (dg (x0 * y1)) (dg (x1 * y0)) := hdg_add _ _
      _ ≤ max (a0 + b1) (a1 + b0) := max_le_max ((hdg_mul x0 y1).trans (Nat.add_le_add hx0 hy1))
          ((hdg_mul x1 y0).trans (Nat.add_le_add hx1 hy0))

/-- **Powers**, by induction from `.one`/`.mul` — `x^n`'s coordinate bound grows the way
repeated multiplication would, `n`-fold. Stated with the SAME bound `(a0,a1)` used at every
step collapsing via `max`/`n`-scaling exactly the way ordinary `totalDegree_pow`-style bounds
do, rather than tracking a separate bound per exponent. -/
theorem hasQuadBound_pow (dg : R → ℕ) (c : R) {dc : ℕ} (hc : dg c ≤ dc)
    (hone : dg (1 : R) ≤ 1) (hzero : dg (0 : R) ≤ 1)
    (hdg_add : ∀ u v : R, dg (u + v) ≤ max (dg u) (dg v))
    (hdg_mul : ∀ u v : R, dg (u * v) ≤ dg u + dg v)
    {x : Polynomial R} {a0 a1 : ℕ} (hx : HasQuadBound dg c x a0 a1) (n : ℕ) :
    HasQuadBound dg c (x ^ n) (n * (a0 + dc + a1) + 1) (n * (a0 + dc + a1) + 1) := by
  induction n with
  | zero => simpa using hasQuadBound_one dg c hone hzero
  | succ k ih =>
      -- `pow_succ : x ^ (k + 1) = x ^ k * x`, so the multiplication bound needs `ih` (for
      -- `x ^ k`) on the LEFT and `hx` (for `x`) on the RIGHT — the original swapped order
      -- (`hx ih`, matching `x * x^k`) produced an `x^k * x` vs `x * x^k` mismatch downstream.
      have hstep := hasQuadBound_mul dg c hc hdg_add hdg_mul ih hx
      have hle1 : max ((k * (a0 + dc + a1) + 1) + a0) (dc + (k * (a0 + dc + a1) + 1) + a1) ≤
          (k + 1) * (a0 + dc + a1) + 1 := by
        rw [Nat.succ_mul]; omega
      have hle2 : max ((k * (a0 + dc + a1) + 1) + a1) ((k * (a0 + dc + a1) + 1) + a0) ≤
          (k + 1) * (a0 + dc + a1) + 1 := by
        rw [Nat.succ_mul]; omega
      rw [pow_succ]
      exact ⟨hstep.1.trans hle1, hstep.2.trans hle2⟩

end TheDataDerivation
end Genus2Lean
