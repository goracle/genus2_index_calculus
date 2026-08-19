import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationBasics

set_option linter.style.header false

/-!
# `theData` derivation, part 2: the tower `K0 → K1 → K2`

Second of four files — see `DataDerivationBasics.lean`'s header for the full
split rationale and file order. This file builds §4.2 item 3: the fraction
field `K0`, and the two `AdjoinRoot` tower steps `K1`, `K2`.

**Irreducibility status (this pass): K1 and K2 proved.** Both field
instances previously rested on bare `axiom`s; both are now real theorems
assembled from `DataDerivationBasics.lean`'s item-1 lemmas. `factIrreducible_K1_proved`
uses the odd degree of `curvePoly`, while `factIrreducible_K2_proved` uses
the quadratic-extension square criterion together with the already-proved
non-squareness of `fAtT ... 1` and `fAtT ... 0 * fAtT ... 1` in `K0`.

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

-- `hp2 : Fact (p ≠ 2)` — project-wide "assume odd characteristic" convention,
-- first load-bearing here: `factIrreducible_K2` (the `K2`-is-a-field instance)
-- genuinely needs `char (K0 p) ≠ 2` for its quadratic-extension square
-- criterion (`2xy = 0 ⟹ xy = 0` needs `2` a unit), see that instance's
-- docstring below.
variable (p : ℕ) [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

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
as a one-dimension-short trap to avoid.

**`abbrev`, not `def`**: instance search does not unfold a plain `def`, so
a `def K0 := FractionRing (...)` would need every one of `FractionRing`'s
instances (`Field`, `Algebra (F p) _`, `Algebra (MvPolynomial ...) _`, ...)
manually re-derived and re-stated one at a time — and still risk diamond
mismatches against instances Mathlib derives generically for
`FractionRing`. `abbrev` is reducible, so `K0 p` and
`FractionRing (MvPolynomial (Fin 2) (F p))` are interchangeable for
typeclass resolution and every instance on the RHS is found automatically
for the LHS. Same reasoning applies to `K1`/`K2` below. -/
noncomputable abbrev K0 : Type := FractionRing (MvPolynomial (Fin 2) (F p))

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
idiom rather than invent a new one.

**`abbrev`, not `def`** — same reasoning as `K0` above: `AdjoinRoot`
already carries `CommRing`, and (once irreducibility is known)
`Algebra (K0 p) (K1 p ...)`, `Field`, etc.; wrapping it in a reducible
`abbrev` lets typeclass search see straight through to those instead of
needing each one manually restated (and risking a diamond against the
ones Mathlib derives for `AdjoinRoot` itself — see the note on
`instFieldK1` below for why a manually-stated `CommRing` on top of an
opaque `def` caused exactly that diamond). -/
noncomputable abbrev K1 (c0 c1 c2 c3 c4 : F p) : Type :=
  AdjoinRoot (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))

/-- `w1 : K1`, the adjoined root, Julia's `gen(K_curr)` after the first
tower step. -/
noncomputable def w1 (c0 c1 c2 c3 c4 : F p) : K1 p c0 c1 c2 c3 c4 :=
  AdjoinRoot.root (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))
  

omit hp2 in
/-- **No longer an axiom.** `X^2 - C (fAtT ... 0)` is irreducible over `K0 p`
because `fAtT p ... 0` is not a square in `K0 p` — `DataDerivationBasics.lean`'s
`fAtT_p_not_isSquare` (item 1, §4.2), itself resting only on `curvePoly`
having odd degree (`curvePoly_natDegree_odd`, unconditional in `p`/`c0..c4`)
plus `irreducible_X_sq_sub_C_of_not_isSquare`'s general "not-a-square implies
irreducible" conversion. `fAtT p c0 c1 c2 c3 c4 0` and `fAtT_p_not_isSquare`'s
own statement are definitionally equal (`K0 p`/`t0` are reducible `abbrev`s),
so no separate rewriting step is needed to line the two up. -/
theorem factIrreducible_K1_proved (c0 c1 c2 c3 c4 : F p) :
    Irreducible (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)) :=
  irreducible_X_sq_sub_C_of_not_isSquare (fAtT_p_not_isSquare p c0 c1 c2 c3 c4 0)

omit hp2 in
instance factIrreducible_K1 (c0 c1 c2 c3 c4 : F p) :
    Fact (Irreducible (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p))) :=
  ⟨factIrreducible_K1_proved p c0 c1 c2 c3 c4⟩





/-- `K1` is a field — needs `sq_sub_curve_irreducible` (item 1) instantiated
at `K = K0 p`, `f = fAtT p ... 0` viewed as living over `K0`'s own
polynomial ring in the SECOND variable's role (§4.1's caveat: this is a
genuine claim, not free, for symbolic `p` and symbolic `(c0,...,c4)`).

**Not a hand-proved `Field` instance.** Mathlib already provides
`AdjoinRoot.instField {K} [Field K] {f} [Fact (Irreducible f)] :
Field (AdjoinRoot f)`, built internally via `Ideal.Quotient.field` ON TOP
OF `AdjoinRoot`'s own `CommRing` instance (`Ideal.Quotient.groupWithZero`
composed with the existing ring structure) — so it can never disagree
with `AdjoinRoot`'s `CommRing` the way a from-scratch `Field` term can.
Supplying `[Fact (Irreducible (X^2 - C (fAtT ...)))]` is therefore enough
to make `AdjoinRoot.instField` fire automatically for `K1 p ...`
(`abbrev` makes `K1 p ...` and the underlying `AdjoinRoot _` the same
term to instance search) — no separate `Field (K1 p ...)` instance needs
to be (or should be) declared here at all.

The `Irreducible` fact is a proved theorem (`factIrreducible_K1_proved`)
rather than an axiom. This is also what makes the downstream `Field` and
`Algebra (K0 p) (K1 p ...)` instances available through `AdjoinRoot`.

 Tower step 2: `K2 := AdjoinRoot (X^2 - C (fAtT ... 1) : Polynomial
(K1 p ...))` mapped through `K1`'s algebra structure over `K0` — Julia's
second `residue_ring` call, `i=2`. This is `theData`'s home field, `K_final`
in §4.0's naming: a rank-4 `K0`-vector space by construction (`{1, w1, w2,
w1*w2}`), each `AdjoinRoot` step contributing a factor of rank 2.

**`abbrev`, not `def`** — same reasoning as `K0`/`K1` above. -/
noncomputable abbrev K2 (c0 c1 c2 c3 c4 : F p) : Type :=
  AdjoinRoot
    (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
      Polynomial (K1 p c0 c1 c2 c3 c4))

/-- `w2 : K2`, the second adjoined root. -/
noncomputable def w2 (c0 c1 c2 c3 c4 : F p) : K2 p c0 c1 c2 c3 c4 :=
  AdjoinRoot.root
    (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
      Polynomial (K1 p c0 c1 c2 c3 c4))


/-- K2 irreducibility: the radicand `fAtT ... 1`, viewed in the quadratic
extension `K1 / K0`, is not a square. The proof uses the quadratic-extension
criterion from `DataDerivationBasics.lean`: in odd characteristic, if a base
field element becomes a square in `K0(√d)`, then either it was already a
square in `K0` or its product with `d` was a square in `K0`. Here the two
required base-field non-squareness facts are exactly `fAtT_p_not_isSquare`
for index `1` and `fAtT_prod_not_isSquare` for the product of the two
coordinates. -/
theorem factIrreducible_K2_proved (c0 c1 c2 c3 c4 : F p) :
    Irreducible
      (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
        (fAtT p c0 c1 c2 c3 c4 1)) :
        Polynomial (K1 p c0 c1 c2 c3 c4)) := by
  apply irreducible_X_sq_sub_C_of_not_isSquare
  have hchar : (2 : K0 p) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime
      (R := K0 p) (show Nat.Prime 2 by norm_num) (by
        intro h
        exact hp2.out h)
  have h1 : ¬ IsSquare (fAtT p c0 c1 c2 c3 c4 1) := by
    exact fAtT_p_not_isSquare p c0 c1 c2 c3 c4 1
  have h01 : ¬ IsSquare
      (fAtT p c0 c1 c2 c3 c4 1 * fAtT p c0 c1 c2 c3 c4 0) := by
    have h_prod := fAtT_prod_not_isSquare
      (curvePoly p c0 c1 c2 c3 c4)
      (curvePoly_natDegree_odd p c0 c1 c2 c3 c4)
      (curvePoly_ne_zero p c0 c1 c2 c3 c4)
    have h_eq : fAtT p c0 c1 c2 c3 c4 1 * fAtT p c0 c1 c2 c3 c4 0 =
        (curvePoly p c0 c1 c2 c3 c4).eval₂ (algebraMap (F p) (K0 p)) (t0 p 0) *
        (curvePoly p c0 c1 c2 c3 c4).eval₂ (algebraMap (F p) (K0 p)) (t0 p 1) := by
      rw [mul_comm]
      rfl
    rw [h_eq]
    exact h_prod
  exact quadratic_extension_square_criterion
    (K := K0 p)
    (hchar := hchar)
    (d := fAtT p c0 c1 c2 c3 c4 0)
    (a := fAtT p c0 c1 c2 c3 c4 1)
    h1 h01

/- Keep this instance unconditional in its CONCLUSION (`Fact (Irreducible
...)`); the ambient `hp2 : Fact (p ≠ 2)` supplies the odd-characteristic
hypothesis needed by the quadratic-extension criterion. -/
instance factIrreducible_K2 (c0 c1 c2 c3 c4 : F p) :
    Fact (Irreducible
      (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
        (fAtT p c0 c1 c2 c3 c4 1)) :
        Polynomial (K1 p c0 c1 c2 c3 c4))) :=
  ⟨factIrreducible_K2_proved p c0 c1 c2 c3 c4⟩



/- `K2` is a field via `AdjoinRoot.instField` and the proved
`factIrreducible_K2` instance above. -/

end TheDataDerivation
end Genus2Lean
