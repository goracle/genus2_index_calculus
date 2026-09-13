import Mathlib
import Genus2Lean.ZeroD.QuadraticCoordArith
import Genus2Lean.ZeroD.QuadraticCoordinateBridge
import Genus2Lean.ZeroD.HasRdecBound

/-!
# `K2`-native coordinate arithmetic, and `HasCoordBoundK2`

Per two ChatGPT consults on `ROADMAP-crossnondegenerate-degree-bound.md`'s
live gap (closing `CrossNondegenerateDegreeBound.lean`'s `hA`/`hB`): the
robust architecture is to propagate degree bounds FORWARD through the
construction's own coordinate arithmetic, never to extract coordinate
bounds from an opaque whole-value existential witness after the fact (no
general operation does the latter — confirmed by both consults). This
file builds the base layer that recommendation calls for: `K2`'s own
`coord0`/`coord1` extraction, its `.add`/`.neg`/`.mul` identities (as
literal `K1`-level equalities, no degree content), and a matching
`HasCoordBoundK2` predicate with closure lemmas built on `HasRdecBound`
(`HasRdecBound.lean`) as the underlying `K1`-level bound notion.

**Where this sits in the planned chain** (per the second consult):
```
matrix entries in K2 (coordinate-bounded)
        ↓  (this file's .mul/.add, applied entrywise/by Laplace expansion)
coordinate bounds on det(A)/cofactor determinants
        ↓  (Cramer's rule, as a 2×2 K1-linear system — NOT a K2 quotient)
coordinate bounds on E, Y
        ↓  (this file's .mul/.add again)
coordinate bounds on N = E² - f·Y²
        ↓  (Q2/Q3 already clean; this file's .mul/.add against a clean factor)
coordinate bounds on curBeforeMonic.coeff {0,1,2}
```
This file supplies only the first arrow's underlying algebra (`.add`/
`.neg`/`.mul` at the `K2` level) plus the bound-closure lemmas —
determinant/Cramer/`N`/`g` are each a separate, not-yet-attempted next
step, exactly as both consults recommend keeping them (a fold over this
file's `.mul`/`.add`, not a monolithic derivation).

**Convention**: `c : K1 p c0 c1 c2 c3 c4` throughout is `w2`'s defining
constant, `algebraMap (K0 p) (K1 p ...) (fAtT p c0 c1 c2 c3 c4 1)`
(`w2_sq_eq_public`) — always the SAME element project-wide (this tower
has exactly one `K2`, so `c` is never a free parameter at a call site,
unlike `QuadCoordBound.lean`'s deliberately-generic `c : R`).

**Status**: drafted this pass, built directly on already-REPL-confirmed
pieces (`mk_mul_coord_eq`, `AdjoinRoot.modByMonicHom_mk`,
`AdjoinRoot.mk_surjective`, `w2_sq_eq_public`) — not yet REPL-confirmed
itself; Claire tests via the REPL per the working agreement.

**Update (this pass)**: fixed against Claire's second REPL run. That run
surfaced: (1) `coord_mul`'s `hx0eq`/etc. `have`s used `rw [hfa]` where
`rw [← hfa]` was needed (goal has the bare variable `a`, not
`AdjoinRoot.mk _ fa`, after `unfold coord0`) — wrong-direction rewrites
that couldn't find their pattern and cascaded into the `whnf`/`isDefEq`
timeouts and the two "unknown constant `coord_mul`" errors reported
alongside them; (2) `hasCoordBoundK2_add/_neg/_sub` all used
`rw [coord{0,1}_{add,neg,sub}]` directly against a `HasRdecBound` goal,
which fails with "motive is not type correct" — `HasRdecBound` is generic
in an implicit `[CommRing K]`, and `K1 p c0 c1 c2 c3 c4` is reducibly (not
syntactically) an `AdjoinRoot`, so `rw`'s automatic motive-search
generalizes the wrong instance. Fixed by replacing every such `rw` with
an explicit `Eq.mpr (congrArg (fun t => HasRdecBound p ι evalNd t D) heq) proof`,
which supplies the motive by hand instead of asking `rw` to infer it; (3)
`hasCoordBoundK2_mul`'s first branch built `hasRdecBound_mul p hc
(hasRdecBound_mul p ha1 hb1)`, which proves a bound on
`k2Const * (coord1 a * coord1 b)` — but the goal's
`k2Const * coord1 a * coord1 b` is `(k2Const * coord1 a) * coord1 b`
(left-associative `*`), a different (if equal-by-`ring`) term; fixed by
grouping the two `.mul` applications to match:
`hasRdecBound_mul p (hasRdecBound_mul p hc ha1) hb1`. Still awaiting
Claire's next re-run to confirm these three fixes actually close the
file.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]
variable (c0 c1 c2 c3 c4 : F p)

/-- **`w2`'s defining constant, as a plain `K1`-element**, abbreviated so
every statement below can refer to "the" tower constant uniformly instead
of re-writing `algebraMap (K0 p) (K1 p ...) (fAtT p ... 1)` at each call
site. Definitionally `w2_sq_eq_public`'s RHS. -/
noncomputable abbrev k2Const : K1 p c0 c1 c2 c3 c4 :=
  algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)

/-- **`K2`'s defining monic quadratic, as a bare fact**, matching
`k2Const`'s abbreviation — avoids repeating the `X^2 - C (...)` expression
at every call site below. -/
theorem k2_poly_eq :
    (X ^ 2 - C (k2Const p c0 c1 c2 c3 c4) : Polynomial (K1 p c0 c1 c2 c3 c4)) =
      X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :=
  rfl

/-- **`v`'s own canonical `K1`-coordinate 0.** `AdjoinRoot.modByMonicHom`
applied directly to the `K2`-element `v` (no representative needed at the
call site — `modByMonicHom`'s domain literally IS `K2 = AdjoinRoot
(K2_poly_monic ...)`). -/
noncomputable def coord0 (v : K2 p c0 c1 c2 c3 c4) : K1 p c0 c1 c2 c3 c4 :=
  (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 0

/-- **`v`'s own canonical `K1`-coordinate 1.** -/
noncomputable def coord1 (v : K2 p c0 c1 c2 c3 c4) : K1 p c0 c1 c2 c3 c4 :=
  (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 1

/-- **`v` reconstructs from its own coordinates.** Direct restatement of
`adjoinRoot_quadratic_normal_form` in `coord0`/`coord1` notation — the
`w2 = AdjoinRoot.root (K2_poly_monic ...)` identification is definitional
(`w2`'s own definition, `DataDerivationTower.lean`). -/
theorem coord_spec (v : K2 p c0 c1 c2 c3 c4) :
    v = algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (coord0 p c0 c1 c2 c3 c4 v) +
      algebraMap (K1 p c0 c1 c2 c3 c4) (K2 p c0 c1 c2 c3 c4) (coord1 p c0 c1 c2 c3 c4 v) *
        w2 p c0 c1 c2 c3 c4 := by
  have hdeg : (X ^ 2 - C (k2Const p c0 c1 c2 c3 c4) :
      Polynomial (K1 p c0 c1 c2 c3 c4)).natDegree = 2 := by
    compute_degree!
  exact adjoinRoot_quadratic_normal_form (K2_poly_monic p c0 c1 c2 c3 c4) hdeg v

/-! ## Coordinate arithmetic identities -/

/-- **Addition.** `coord0 (a+b) = coord0 a + coord0 b`; immediate from
`AdjoinRoot.modByMonicHom`/`Polynomial.coeff` both being additive. -/
theorem coord0_add (a b : K2 p c0 c1 c2 c3 c4) :
    coord0 p c0 c1 c2 c3 c4 (a + b) =
      coord0 p c0 c1 c2 c3 c4 a + coord0 p c0 c1 c2 c3 c4 b := by
  unfold coord0
  rw [map_add, Polynomial.coeff_add]

theorem coord1_add (a b : K2 p c0 c1 c2 c3 c4) :
    coord1 p c0 c1 c2 c3 c4 (a + b) =
      coord1 p c0 c1 c2 c3 c4 a + coord1 p c0 c1 c2 c3 c4 b := by
  unfold coord1
  rw [map_add, Polynomial.coeff_add]

/-- **Negation.** -/
theorem coord0_neg (a : K2 p c0 c1 c2 c3 c4) :
    coord0 p c0 c1 c2 c3 c4 (-a) = -coord0 p c0 c1 c2 c3 c4 a := by
  unfold coord0
  rw [map_neg, Polynomial.coeff_neg]

theorem coord1_neg (a : K2 p c0 c1 c2 c3 c4) :
    coord1 p c0 c1 c2 c3 c4 (-a) = -coord1 p c0 c1 c2 c3 c4 a := by
  unfold coord1
  rw [map_neg, Polynomial.coeff_neg]

/-- **Subtraction**, packaged directly (`.add`/`.neg` composed) since both
downstream call sites (`Npoly := E²-fY²`'s subtraction, `curBeforeMonic`'s
triangular back-substitution) use it directly rather than via `+ (-·)`. -/
theorem coord0_sub (a b : K2 p c0 c1 c2 c3 c4) :
    coord0 p c0 c1 c2 c3 c4 (a - b) =
      coord0 p c0 c1 c2 c3 c4 a - coord0 p c0 c1 c2 c3 c4 b := by
  unfold coord0
  rw [map_sub, Polynomial.coeff_sub]

theorem coord1_sub (a b : K2 p c0 c1 c2 c3 c4) :
    coord1 p c0 c1 c2 c3 c4 (a - b) =
      coord1 p c0 c1 c2 c3 c4 a - coord1 p c0 c1 c2 c3 c4 b := by
  unfold coord1
  rw [map_sub, Polynomial.coeff_sub]

set_option maxHeartbeats 2000000 in
/-- **Both multiplication coordinates at once** — proved together since
both come from the same `mk_mul_coord_eq` rewrite and the same
degree-`<2`-remainder reduction, mirroring `QuadCoordBound.lean`'s
`hasQuadBound_mul` proof structure exactly (that proof's `heq`/`hrhs_mod`
steps, specialized here to `R := K1 p ...`, `c := k2Const`, and restated
as a `K2`-element equation via `mk_surjective` rather than staying at the
`Polynomial K1`-representative level `HasQuadBound` itself uses). -/
theorem coord_mul (a b : K2 p c0 c1 c2 c3 c4) :
    coord0 p c0 c1 c2 c3 c4 (a * b) =
      coord0 p c0 c1 c2 c3 c4 a * coord0 p c0 c1 c2 c3 c4 b +
        k2Const p c0 c1 c2 c3 c4 * coord1 p c0 c1 c2 c3 c4 a * coord1 p c0 c1 c2 c3 c4 b ∧
    coord1 p c0 c1 c2 c3 c4 (a * b) =
      coord0 p c0 c1 c2 c3 c4 a * coord1 p c0 c1 c2 c3 c4 b +
        coord1 p c0 c1 c2 c3 c4 a * coord0 p c0 c1 c2 c3 c4 b := by
  set c := k2Const p c0 c1 c2 c3 c4 with hcdef
  set x0 := coord0 p c0 c1 c2 c3 c4 a with hx0
  set x1 := coord1 p c0 c1 c2 c3 c4 a with hx1
  set y0 := coord0 p c0 c1 c2 c3 c4 b with hy0
  set y1 := coord1 p c0 c1 c2 c3 c4 b with hy1
  obtain ⟨fa, hfa⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨fb, hfb⟩ := AdjoinRoot.mk_surjective b
  have hgmonic := K2_poly_monic p c0 c1 c2 c3 c4
  -- `x0 = (fa %ₘ g).coeff 0`, etc. `modByMonicHom_mk` is invoked as a
  -- standalone `have`, then transported to the `.coeff` statement via
  -- `congrArg` — never as `rw [AdjoinRoot.modByMonicHom_mk]` directly on
  -- the goal. The previous draft's `rw [← hfa, AdjoinRoot.modByMonicHom_mk]`
  -- inside `coord0`/`coord1` timed out at `whnf`: that `rw` needs to unify
  -- `modByMonicHom_mk`'s LHS pattern against a goal that ALSO has `a`/`b`
  -- (heavy `K2`-level `AdjoinRoot` elements) substituted in from `hfa`/`hfb`
  -- in the same step. Splitting into `rw [← hfa]` (cheap: `a` is an opaque
  -- local hypothesis variable, matched syntactically as an atom, not
  -- unified against) followed by `congrArg` on a separately-elaborated
  -- `have` avoids that combined unification.
  have hx0eq : x0 = (fa %ₘ (X ^ 2 - C c) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0 := by
    have h := AdjoinRoot.modByMonicHom_mk hgmonic fa
    rw [hx0]; unfold coord0; rw [← hfa]; exact congrArg (fun q => Polynomial.coeff q 0) h
  have hx1eq : x1 = (fa %ₘ (X ^ 2 - C c) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1 := by
    have h := AdjoinRoot.modByMonicHom_mk hgmonic fa
    rw [hx1]; unfold coord1; rw [← hfa]; exact congrArg (fun q => Polynomial.coeff q 1) h
  have hy0eq : y0 = (fb %ₘ (X ^ 2 - C c) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 0 := by
    have h := AdjoinRoot.modByMonicHom_mk hgmonic fb
    rw [hy0]; unfold coord0; rw [← hfb]; exact congrArg (fun q => Polynomial.coeff q 0) h
  have hy1eq : y1 = (fb %ₘ (X ^ 2 - C c) : Polynomial (K1 p c0 c1 c2 c3 c4)).coeff 1 := by
    have h := AdjoinRoot.modByMonicHom_mk hgmonic fb
    rw [hy1]; unfold coord1; rw [← hfb]; exact congrArg (fun q => Polynomial.coeff q 1) h
  -- The core multiplication identity, applied directly (term-mode, no
  -- `rw`) — mirrors `QuadCoordBound.lean`'s `hasQuadBound_mul`, whose own
  -- comments record that routing this same fact through a `rw` (rather
  -- than a direct `have := mk_mul_coord_eq ...` application) is what
  -- caused ITS earlier timeout.
  have hmul : AdjoinRoot.mk (X ^ 2 - C c) fa * AdjoinRoot.mk (X ^ 2 - C c) fb =
      AdjoinRoot.mk (X ^ 2 - C c)
        (Polynomial.C ((fa %ₘ (X ^ 2 - C c)).coeff 0 * (fb %ₘ (X ^ 2 - C c)).coeff 0 +
              c * (fa %ₘ (X ^ 2 - C c)).coeff 1 * (fb %ₘ (X ^ 2 - C c)).coeff 1) +
            Polynomial.C ((fa %ₘ (X ^ 2 - C c)).coeff 0 * (fb %ₘ (X ^ 2 - C c)).coeff 1 +
              (fa %ₘ (X ^ 2 - C c)).coeff 1 * (fb %ₘ (X ^ 2 - C c)).coeff 0) * X) :=
    mk_mul_coord_eq c fa fb
  have hmk : a * b = AdjoinRoot.mk (X ^ 2 - C c)
      (Polynomial.C (x0 * y0 + c * x1 * y1) + Polynomial.C (x0 * y1 + x1 * y0) * X) := by
    rw [← hfa, ← hfb, hmul, ← hx0eq, ← hx1eq, ← hy0eq, ← hy1eq]
  -- The RHS's remainder is itself, since it already has `natDegree ≤ 1 < 2`.
  have hrhs_natdeg : (Polynomial.C (x0 * y0 + c * x1 * y1) +
      Polynomial.C (x0 * y1 + x1 * y0) * X : Polynomial (K1 p c0 c1 c2 c3 c4)).natDegree ≤ 1 := by
    compute_degree
  have hgdeg : (X ^ 2 - C c : Polynomial (K1 p c0 c1 c2 c3 c4)).natDegree = 2 := by
    compute_degree!
  have hrhs_lt : (Polynomial.C (x0 * y0 + c * x1 * y1) + Polynomial.C (x0 * y1 + x1 * y0) * X :
      Polynomial (K1 p c0 c1 c2 c3 c4)).degree < (X ^ 2 - C c : Polynomial (K1 p c0 c1 c2 c3 c4)).degree := by
    have hle : (Polynomial.C (x0 * y0 + c * x1 * y1) + Polynomial.C (x0 * y1 + x1 * y0) * X :
        Polynomial (K1 p c0 c1 c2 c3 c4)).degree ≤ ((1 : ℕ) : WithBot ℕ) :=
      Polynomial.degree_le_of_natDegree_le hrhs_natdeg
    have hgdeg' : (X ^ 2 - C c : Polynomial (K1 p c0 c1 c2 c3 c4)).degree = ((2 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hgmonic.ne_zero, hgdeg]
    calc (Polynomial.C (x0 * y0 + c * x1 * y1) + Polynomial.C (x0 * y1 + x1 * y0) * X :
        Polynomial (K1 p c0 c1 c2 c3 c4)).degree
        ≤ ((1 : ℕ) : WithBot ℕ) := hle
      _ < ((2 : ℕ) : WithBot ℕ) := by exact_mod_cast (by norm_num : (1:ℕ) < 2)
      _ = (X ^ 2 - C c : Polynomial (K1 p c0 c1 c2 c3 c4)).degree := hgdeg'.symm
  have hrhs_mod : (Polynomial.C (x0 * y0 + c * x1 * y1) + Polynomial.C (x0 * y1 + x1 * y0) * X :
      Polynomial (K1 p c0 c1 c2 c3 c4)) %ₘ (X ^ 2 - C c) =
      Polynomial.C (x0 * y0 + c * x1 * y1) + Polynomial.C (x0 * y1 + x1 * y0) * X :=
    (Polynomial.modByMonic_eq_self_iff hgmonic).mpr hrhs_lt
  refine ⟨?_, ?_⟩
  · unfold coord0
    rw [hmk, AdjoinRoot.modByMonicHom_mk, hrhs_mod]
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero]
  · unfold coord1
    rw [hmk, AdjoinRoot.modByMonicHom_mk, hrhs_mod]
    simp [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one]

theorem coord0_mul (a b : K2 p c0 c1 c2 c3 c4) :
    coord0 p c0 c1 c2 c3 c4 (a * b) =
      coord0 p c0 c1 c2 c3 c4 a * coord0 p c0 c1 c2 c3 c4 b +
        k2Const p c0 c1 c2 c3 c4 * coord1 p c0 c1 c2 c3 c4 a * coord1 p c0 c1 c2 c3 c4 b :=
  (coord_mul p c0 c1 c2 c3 c4 a b).1

theorem coord1_mul (a b : K2 p c0 c1 c2 c3 c4) :
    coord1 p c0 c1 c2 c3 c4 (a * b) =
      coord0 p c0 c1 c2 c3 c4 a * coord1 p c0 c1 c2 c3 c4 b +
        coord1 p c0 c1 c2 c3 c4 a * coord0 p c0 c1 c2 c3 c4 b :=
  (coord_mul p c0 c1 c2 c3 c4 a b).2

/-! ## `HasCoordBoundK2`: the coordinate-level bound predicate, closed
under `.add`/`.neg`/`.mul` -/

/-- **`v : K2` has coordinate-bounded `IsRdecWitness`s.** The direct
`K2`-specific analogue of `QuadCoordBound.lean`'s `HasQuadCoordBound`,
phrased against `coord0`/`coord1` (this file's `K2`-native extraction, no
representative-choice ambiguity) and `HasRdecBound` (`HasRdecBound.lean`)
as the `K1`-level bound notion. -/
def HasCoordBoundK2 {Vars L : Type*} [CommRing L]
    (ι : K1 p c0 c1 c2 c3 c4 →+* L) (evalNd : MvPolynomial Vars (F p) →+* L)
    (v : K2 p c0 c1 c2 c3 c4) (D0 D1 : ℕ) : Prop :=
  HasRdecBound p ι evalNd (coord0 p c0 c1 c2 c3 c4 v) D0 ∧
  HasRdecBound p ι evalNd (coord1 p c0 c1 c2 c3 c4 v) D1

/-- **Addition.** Immediate from `coord{0,1}_add` plus `HasRdecBound.add`.
Uses `Eq.mpr`/`congrArg` with an explicit motive rather than `rw`, for the
same reason `hasCoordBoundK2_sub` below does: `rw [coord0_add]` here fails
with a "motive is not type correct" error, since the rewritten term's type
`K1 p c0 c1 c2 c3 c4` is reducibly (not syntactically) `AdjoinRoot _`, and
`rw`'s automatic motive lands on a mismatched `CommRing` instance. -/
theorem hasCoordBoundK2_add {Vars L : Type*} [CommRing L]
    {ι : K1 p c0 c1 c2 c3 c4 →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K2 p c0 c1 c2 c3 c4} {A0 A1 B0 B1 : ℕ}
    (ha : HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd a A0 A1)
    (hb : HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd b B0 B1) :
    HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd (a + b) (A0 + B0) (A1 + B1) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  refine ⟨?_, ?_⟩
  · exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t (A0 + B0))
        (coord0_add p c0 c1 c2 c3 c4 a b))
      (hasRdecBound_add p ha0 hb0)
  · exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t (A1 + B1))
        (coord1_add p c0 c1 c2 c3 c4 a b))
      (hasRdecBound_add p ha1 hb1)

/-- **Negation.** Same `Eq.mpr`/`congrArg` pattern as `.add` above, for the
same reason. -/
theorem hasCoordBoundK2_neg {Vars L : Type*} [CommRing L]
    {ι : K1 p c0 c1 c2 c3 c4 →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a : K2 p c0 c1 c2 c3 c4} {A0 A1 : ℕ}
    (ha : HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd a A0 A1) :
    HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd (-a) A0 A1 := by
  obtain ⟨ha0, ha1⟩ := ha
  refine ⟨?_, ?_⟩
  · exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t A0) (coord0_neg p c0 c1 c2 c3 c4 a))
      (hasRdecBound_neg p ha0)
  · exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t A1) (coord1_neg p c0 c1 c2 c3 c4 a))
      (hasRdecBound_neg p ha1)

/-- **Subtraction.** Same pattern once more.-/
theorem hasCoordBoundK2_sub {Vars L : Type*} [CommRing L]
    {ι : K1 p c0 c1 c2 c3 c4 →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K2 p c0 c1 c2 c3 c4} {A0 A1 B0 B1 : ℕ}
    (ha : HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd a A0 A1)
    (hb : HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd b B0 B1) :
    HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd (a - b) (A0 + B0) (A1 + B1) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  -- Plain `rw [coord0_sub]`/`rw [coord1_sub]` here fail with a
  -- "motive is not type correct" error: `coord0 p ... a - coord0 p ... b`
  -- has type `K1 p c0 c1 c2 c3 c4`, which is reducibly (but not
  -- syntactically) `AdjoinRoot _`, so `rw`'s motive-abstraction step
  -- generalizes the ambient `CommRing (K1 ...)` instance along with it,
  -- landing on an ill-typed motive (`HasRdecBound` takes `[CommRing K]`
  -- for an implicit `K`, and the abstracted instance no longer matches).
  -- Side-stepping `rw` entirely — build each `HasRdecBound` proof at its
  -- natural type first, then transport along the (already-proved)
  -- `coord{0,1}_sub` equation via `Eq.mpr`/`▸` used as a plain term,
  -- never asking the tactic framework to abstract a motive over it.
  refine ⟨?_, ?_⟩
  · have hstep : HasRdecBound p ι evalNd
        (coord0 p c0 c1 c2 c3 c4 a - coord0 p c0 c1 c2 c3 c4 b) (A0 + B0) := by
      simpa [sub_eq_add_neg] using hasRdecBound_add p ha0 (hasRdecBound_neg p hb0)
    exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t (A0 + B0))
        (coord0_sub p c0 c1 c2 c3 c4 a b))
      hstep
  · have hstep : HasRdecBound p ι evalNd
        (coord1 p c0 c1 c2 c3 c4 a - coord1 p c0 c1 c2 c3 c4 b) (A1 + B1) := by
      simpa [sub_eq_add_neg] using hasRdecBound_add p ha1 (hasRdecBound_neg p hb1)
    exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t (A1 + B1))
        (coord1_sub p c0 c1 c2 c3 c4 a b))
      hstep

/-- **Multiplication.** Needs a bound `C` on `k2Const` itself (`c` in the
`coord0_mul` formula) — the same genuine extra hypothesis
`QuadCoordBound.lean`'s abstract `hasQuadBound_mul` needs for its `dc`
parameter, since the product's coordinate-0 formula genuinely involves
`c`. `k2Const`'s own bound is a fixed, one-time fact to establish
separately (it's a specific element, not a free parameter varying by
call site) — not attempted in this file. -/
theorem hasCoordBoundK2_mul {Vars L : Type*} [CommRing L]
    {ι : K1 p c0 c1 c2 c3 c4 →+* L} {evalNd : MvPolynomial Vars (F p) →+* L}
    {a b : K2 p c0 c1 c2 c3 c4} {A0 A1 B0 B1 C : ℕ}
    (hc : HasRdecBound p ι evalNd (k2Const p c0 c1 c2 c3 c4) C)
    (ha : HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd a A0 A1)
    (hb : HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd b B0 B1) :
    HasCoordBoundK2 p c0 c1 c2 c3 c4 ι evalNd (a * b)
      (A0 + B0 + (C + A1 + B1)) (A0 + B1 + (A1 + B0)) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  refine ⟨?_, ?_⟩
  · have hstep : HasRdecBound p ι evalNd
        (coord0 p c0 c1 c2 c3 c4 a * coord0 p c0 c1 c2 c3 c4 b +
          k2Const p c0 c1 c2 c3 c4 * coord1 p c0 c1 c2 c3 c4 a * coord1 p c0 c1 c2 c3 c4 b)
        (A0 + B0 + (C + A1 + B1)) :=
      -- `k2Const * coord1 a * coord1 b` parses as `(k2Const * coord1 a) *
      -- coord1 b` (left-associative `*`) — so the two `.mul` applications
      -- must be grouped the same way, not as `k2Const * (coord1 a * coord1 b)`
      -- (the original bug: applying `hasRdecBound_mul p hc` directly to
      -- `hasRdecBound_mul p ha1 hb1` builds the wrong grouping).
      hasRdecBound_add p (hasRdecBound_mul p ha0 hb0)
        (hasRdecBound_mul p (hasRdecBound_mul p hc ha1) hb1)
    exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t (A0 + B0 + (C + A1 + B1)))
        (coord0_mul p c0 c1 c2 c3 c4 a b))
      hstep
  · have hstep : HasRdecBound p ι evalNd
        (coord0 p c0 c1 c2 c3 c4 a * coord1 p c0 c1 c2 c3 c4 b +
          coord1 p c0 c1 c2 c3 c4 a * coord0 p c0 c1 c2 c3 c4 b)
        (A0 + B1 + (A1 + B0)) :=
      hasRdecBound_add p (hasRdecBound_mul p ha0 hb1) (hasRdecBound_mul p ha1 hb0)
    exact Eq.mpr
      (congrArg (fun t => HasRdecBound p ι evalNd t (A0 + B1 + (A1 + B0)))
        (coord1_mul p c0 c1 c2 c3 c4 a b))
      hstep

end TheDataDerivation
end Genus2Lean
