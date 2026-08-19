import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationBasics

/-!
# `theData` derivation, part 2: the tower `K0 → K1 → K2`

Second of four files — see `DataDerivationBasics.lean`'s header for the full
split rationale and file order. This file builds §4.2 item 3: the fraction
field `K0`, and the two `AdjoinRoot` tower steps `K1`, `K2`.

**Irreducibility status (this pass): K1 done, K2 still open.** Both field
instances previously rested on bare `axiom`s (`factIrreducible_K1_assumed`/
`factIrreducible_K2_assumed`); both are now real theorems assembled from
`DataDerivationBasics.lean`'s item-1 lemmas, but with different outcomes:
`factIrreducible_K1_proved` is complete, no `sorry`, resting only on
`curvePoly` having odd degree (true unconditionally, no irreducibility of
the quintic itself needed — see that theorem's docstring). `factIrreducible_
K2_proved` is still `sorry`'d, and NOT for the same reason as before: it's a
genuinely different, harder claim (non-squareness has to be shown in `K1`,
a field extension of `K0`, not in `K0` itself) that may depend on
`(c0,...,c4,p)` in a way the K1 case never needed to — see that theorem's
docstring for the full argument and the open question.

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

**Left as `sorry`** at the `Irreducible` fact itself, not at `Field` —
blocked on item 1's `sq_sub_curve_irreducible` in `DataDerivationBasics.lean`,
which this instantiates rather than re-proving irreducibility from
scratch. This is also what fixes the downstream `Algebra (K0 p) (K1 p ...)`
failure: that instance comes from `AdjoinRoot`'s own algebra structure
(`AdjoinRoot.instAlgebra`-style, over the ring `X^2 - C (...)` is a
polynomial in), which was unreachable before because instance search
couldn't get past the earlier `CommRing` diamond to it — with the diamond
gone, it resolves the same way `Field` now does. `factIrreducible_K1`'s
`Irreducible` fact is now a proved theorem (`factIrreducible_K1_proved`
above), not an axiom — see that instance's own docstring.

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


/-- **Genuinely harder than `factIrreducible_K1`, NOT a re-application of the
same lemma.** `factIrreducible_K1` only needed "`fAtT p ... 0` is not a
square IN `K0 p`" (`DataDerivationBasics.fAtT_p_not_isSquare`). This instance
needs "the IMAGE of `fAtT p ... 1` under `algebraMap (K0 p) (K1 p ...)` is
not a square IN `K1 p ...`" — a strictly stronger claim, since `K1` is a
genuine degree-2 field extension of `K0` (`K1 := AdjoinRoot (X^2 - C (fAtT
... 0))`) and a non-square in a base field CAN become a square after
adjoining a square root of something else (a general fact about quadratic
extensions, not something specific to this construction that can be
sidestepped). `fAtT_p_not_isSquare` alone does not give this — it's a
statement about `K0`, not `K1`.

**Proof sketch (not yet formalized as a term, hence still `sorry`):** in the
degree-2 extension `K1/K0`, an element `a ∈ K0` becomes a square in `K1`
iff either (i) `a` is already a square in `K0`, or (ii) `a` and the
adjoined element's radicand (`fAtT p ... 0`, i.e. `w1^2` in `K1`) differ
by a square factor in `K0` — concretely, `a` is a square in `K1 = K0(w1)`
iff `a` or `a * fAtT p ... 0` is a square in `K0` (standard quadratic-
extension fact: `K1`'s elements are `x + y*w1`, and `(x+y*w1)^2 = a` forces
`y = 0` unless `a/fAtT(...,0)` is itself a square in `K0`, by comparing the
`w1`-coefficient). So this reduces to TWO non-square-in-`K0` facts instead
of one: `fAtT p ... 1` not a square in `K0` (have this already, via
`fAtT_p_not_isSquare p c0 c1 c2 c3 c4 1`) AND `fAtT p ... 1 * fAtT p ... 0`
not a square in `K0` either — the SECOND of these is new, not implied by
either factor individually being non-square (product of two non-squares
can be a square). Whether it's true likely depends on `c0,...,c4` and `p`
genuinely (unlike the odd-degree argument, which needed nothing about the
coefficients) — this may be the point where the earlier "should hold
unconditionally" hope from `ROADMAP-regular-sequence.md` §4.1 breaks down
for the SECOND tower step specifically, and where a real genericity
condition on `(c0,...,c4,p)` might need to enter. Flagging this precisely
rather than asserting either way. -/
theorem factIrreducible_K2_proved (c0 c1 c2 c3 c4 : F p) :
    Irreducible
      (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
        (fAtT p c0 c1 c2 c3 c4 1)) :
        Polynomial (K1 p c0 c1 c2 c3 c4)) := by
  sorry -- ChatGPT prompt below; needs the quadratic-extension square criterion
        -- sketched above, not just fAtT_p_not_isSquare re-applied.

/- Keep this instance unconditional: downstream files require `K2` to elaborate as a field. -/
instance factIrreducible_K2 (c0 c1 c2 c3 c4 : F p) :
    Fact (Irreducible
      (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4)
        (fAtT p c0 c1 c2 c3 c4 1)) :
        Polynomial (K1 p c0 c1 c2 c3 c4))) :=
  ⟨factIrreducible_K2_proved p c0 c1 c2 c3 c4⟩



/- `K2` is a field — same shape as `factIrreducible_K1`, one level up, via
`AdjoinRoot.instField` firing off `factIrreducible_K2`'s `Fact (Irreducible
...)` instance above. Unlike `factIrreducible_K1`, `factIrreducible_K2`'s
underlying theorem (`factIrreducible_K2_proved`) is still a genuine `sorry`,
not merely unassembled bookkeeping — see that theorem's docstring for why
this is real open work (a quadratic-extension square criterion, possibly
needing a genericity condition on `(c0,...,c4,p)`), not a restatement of
the same odd-degree argument `factIrreducible_K1` used. -/

end TheDataDerivation
end Genus2Lean
