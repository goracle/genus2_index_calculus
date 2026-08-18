import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationBasics

/-!
# `theData` derivation, part 2: the tower `K0 → K1 → K2`

Second of four files — see `DataDerivationBasics.lean`'s header for the full
split rationale and file order. This file builds §4.2 item 3: the fraction
field `K0`, and the two `AdjoinRoot` tower steps `K1`, `K2`, using the
irreducibility lemma (`sq_sub_curve_irreducible`) from
`DataDerivationBasics.lean` to (eventually) discharge the field instances —
those two instances are still `sorry`'d here, blocked on
`sq_sub_curve_irreducible`'s own remaining `sorry` in that file, unchanged
from before the split.

**Import path note**: `import Genus2Lean.TheDataDerivation.DataDerivationBasics`
assumes this project's module root is set up so that path resolves to
`DataDerivationBasics.lean` — adjust to match wherever this file actually
lands in the project's directory layout (this session doesn't have access to
that layout, only the four `.lean` files themselves, so the import line may
need a path adjustment on first build).
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Item 3 (§4.2): the tower `K0 → K1 → K2`

`t1, t2` (`= a1,a2` in `elim2`'s naming, sample-1 side; the `b1,b2` copy is
the identical construction with fresh variables, not re-derived separately
here — `theData`'s `u1_*`/`u2_*` split in `DecoupledSystemRegular.lean`
already keeps the two samples' variable sets disjoint via `Idx`, so this
section builds ONE generic tower and both samples instantiate it with their
own `Idx`-typed variables downstream). -/

/-- `K0`, item-3's base field: the fraction field of `MvPolynomial (Fin 2)
(F p)`, playing `Oscar.rational_function_field(Fp, ["t1","t2"])`'s role.
**Not** Mathlib's `RatFunc`, which is single-variable
(`RatFunc F = FractionRing (Polynomial F)`) — `§4.1` flags this explicitly
as a one-dimension-short trap to avoid. -/
noncomputable def K0 : Type := FractionRing (MvPolynomial (Fin 2) (F p))

noncomputable instance instFieldK0 : Field (K0 p) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin 2) (F p))))

/-- `t1, t2 : K0`, the images of `MvPolynomial`'s two generators under
`algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p)` — the two symbolic anchor
coordinates, playing Oscar's `t_vars` from `rational_function_field`. -/
noncomputable def t0 : Fin 2 → K0 p :=
  fun i => algebraMap (MvPolynomial (Fin 2) (F p)) (K0 p) (MvPolynomial.X i)

/-- `f` evaluated at `t1` (resp. `t2`) inside `K0`, i.e. Julia's `f_ti =
sum(coeff * t_i^(j-1) ...)` (line 351) — the polynomial `curvePoly p c0 c1
c2 c3 c4` mapped through `algebraMap (F p) (K0 p)` and evaluated at `t0 p i`. -/
noncomputable def fAtT (c0 c1 c2 c3 c4 : F p) (i : Fin 2) : K0 p :=
  Polynomial.eval₂ (algebraMap (F p) (K0 p)) (t0 p i) (curvePoly p c0 c1 c2 c3 c4)

/-- Tower step 1: `K1 := AdjoinRoot (X^2 - C (fAtT ... 0) : Polynomial (K0 p))`
— Julia's first `residue_ring(K_curr[w_i], w_i^2 - f_ti)` call, `i=1`,
mirroring `HyperellipticFunctionField.lean`'s `CoordinateRing` idiom
(`AdjoinRoot (X^2 - C H.f)`) exactly, per §4.1's instruction to reuse that
idiom rather than invent a new one. -/
noncomputable def K1 (c0 c1 c2 c3 c4 : F p) : Type :=
  AdjoinRoot (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))

noncomputable instance instCommRingK1 (c0 c1 c2 c3 c4 : F p) : CommRing (K1 p c0 c1 c2 c3 c4) :=
  inferInstanceAs (CommRing (AdjoinRoot _))

/-- `w1 : K1`, the adjoined root, Julia's `gen(K_curr)` after the first
tower step. -/
noncomputable def w1 (c0 c1 c2 c3 c4 : F p) : K1 p c0 c1 c2 c3 c4 :=
  AdjoinRoot.root (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))

/-- `K1` is a field — needs `sq_sub_curve_irreducible` (item 1) instantiated
at `K = K0 p`, `f = fAtT p ... 0` viewed as living over `K0`'s own
polynomial ring in the SECOND variable's role (§4.1's caveat: this is a
genuine claim, not free, for symbolic `p` and symbolic `(c0,...,c4)`).
**Left as `sorry`**, blocked on item 1's own `sorry` above — once
`sq_sub_curve_irreducible` is filled in for the abstract case, this
instantiates it rather than re-proving irreducibility from scratch. -/
noncomputable instance instFieldK1 (c0 c1 c2 c3 c4 : F p) : Field (K1 p c0 c1 c2 c3 c4) := by
  sorry

/-- Tower step 2: `K2 := AdjoinRoot (X^2 - C (fAtT ... 1) : Polynomial
(K1 p ...))` mapped through `K1`'s algebra structure over `K0` — Julia's
second `residue_ring` call, `i=2`. This is `theData`'s home field, `K_final`
in §4.0's naming: a rank-4 `K0`-vector space by construction (`{1, w1, w2,
w1*w2}`), each `AdjoinRoot` step contributing a factor of rank 2. -/
noncomputable def K2 (c0 c1 c2 c3 c4 : F p) : Type :=
  AdjoinRoot
    (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
      Polynomial (K1 p c0 c1 c2 c3 c4))

noncomputable instance instCommRingK2 (c0 c1 c2 c3 c4 : F p) : CommRing (K2 p c0 c1 c2 c3 c4) :=
  inferInstanceAs (CommRing (AdjoinRoot _))

/-- `w2 : K2`, the second adjoined root. -/
noncomputable def w2 (c0 c1 c2 c3 c4 : F p) : K2 p c0 c1 c2 c3 c4 :=
  AdjoinRoot.root
    (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
      Polynomial (K1 p c0 c1 c2 c3 c4))

/-- `K2` is a field — same shape as `instFieldK1`, one level up (needs
`sq_sub_curve_irreducible` instantiated at `K = K1 p c0 c1 c2 c3 c4`
instead). **Left as `sorry`**, same blocker. -/
noncomputable instance instFieldK2 (c0 c1 c2 c3 c4 : F p) : Field (K2 p c0 c1 c2 c3 c4) := by
  sorry


end TheDataDerivation
end Genus2Lean
