import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# §4: the Forey–Fresán–Kowalski Sidon dichotomy for `s : C(k) → J`

`DivisorClassGroup.lean` built `J`, the embedding `s`, and reduced the matching
condition `s x₁ + s x₂ = s x₃ + s x₄` to a purely divisor-level statement
(`s_add_s_eq_s_add_s_iff`): it holds iff `(x₁) + (x₂) - (x₃) - (x₄) ∈ D.P`. This
file states the theorem advisory-7 §4 actually needs — the point-level dichotomy —
against that reduction, and closes the direction that is genuine divisor
arithmetic and needs no principal-divisor input at all.

**Status: no `sorry` remains in this file**, but the interesting direction is
still gated on an unproven hypothesis (`SidonDichotomy`, see below) rather
than derived from first principles. The FFK theorem
(Forey–Fresán–Kowalski, "Sidon sets in algebraic geometry", 2023, Theorem 1,
case `g=2`) asserts

    s(x₁) + s(x₂) = s(x₃) + s(x₄)  ⟹  {x₁,x₂} = {x₃,x₄} ∨ (x₂ = ι x₁ ∧ x₄ = ι x₃)

The **backward** direction (dichotomy holds ⟹ the sum equation) is pure divisor
bookkeeping — no genus-2 geometry beyond one containment fact
(`PrincipalDivisorData.HyperellipticClass`, itself genuinely true of the real
principal divisors but not yet derivable from the current abstract `P`) — and
is proved below (`sum_eq_of_dichotomy`), given that fact as a hypothesis. The **forward** direction is where all of FFK's actual
content lives: it says a *nontrivial* linear equivalence
`(x₁)+(x₂)-(x₃)-(x₄) ~ 0` on a genus-2 curve forces one of the two degenerate
shapes, which is a Riemann–Roch-flavoured fact about genus-2 curves specifically
(on higher genus curves nontrivial linear equivalences of degree-0, weight-2
divisors are plentiful — this is precisely where `g = 2` is used). Proving it
here would mean either (a) deriving it from a genuine principal-divisor
subgroup built out of `CoordinateRing H`'s function field (the gap flagged in
`DivisorClassGroup.lean`'s module docstring, not yet built), or (b) taking it as
an additional axiom on `PrincipalDivisorData` beyond `le_Divisor0`. Route (b) is
taken here, packaged as `PrincipalDivisorData.SidonDichotomy` below, so that the
theorem can be *stated* in final form and used downstream (energy bound (6),
advisory-7 §4) while remaining honest that the genus-2-specific content is
still an assumption, not a proof, at this layer.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-! ## The easy direction: dichotomy ⟹ sum equation

No principal-divisor input needed — purely `s`'s additivity/well-definedness
plus `ι`'s point-level involution property, both already on hand. -/

/-- If `{x₁,x₂} = {x₃,x₄}` as an unordered pair of points, `s x₁ + s x₂ =
s x₃ + s x₄`. Split out from `sum_eq_of_dichotomy` since it's the more
elementary of the two disjuncts: unfold the set equality into the two ordered
possibilities (`x₁=x₃ ∧ x₂=x₄`, or `x₁=x₄ ∧ x₂=x₃`) and close with `add_comm` in
the second case.

**Proved below via the manual `Set.ext_iff`/membership-case-bash route** (the
`Set.pair_eq_pair_iff` shortcut was not used, to avoid depending on an
unverified exact name/signature). Derived by hand rather than checked against
a live goal state — no Lean toolchain reachable from this session — so this
proof has NOT been compiled and should be `lake build`-verified before being
relied on. Every `Eq.trans`/`.symm` chain in the two "degenerate" case
branches was traced explicitly in comments below precisely because this is
the kind of proof that reads right but has a real chance of a
`subst`-ordering or wrong-direction-chaining bug (per the
`mk'_cancel_common_factor` lesson from `PrincipalDivisorsDedekind.lean`). -/
theorem sum_eq_of_pair_eq (D : PrincipalDivisorData H) (δ₀ : H.Point)
    {x₁ x₂ x₃ x₄ : H.Point} (h : ({x₁, x₂} : Set H.Point) = {x₃, x₄}) :
    s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄ := by
  -- Reduce the set equality to the fully explicit four-membership-fact form via
  -- `Set.ext_iff` + `simp`, rather than manually chaining `Set.mem_insert`/
  -- `Set.mem_insert_of_mem` (whose argument order is easy to mis-wire without a
  -- live goal state to check against — exactly the risk this theorem was
  -- originally left `sorry`'d over). `simp` with the standard pair/insert/
  -- singleton membership lemmas turns `h` into a single decidable statement
  -- of ordered-equality disjunctions, which `obtain`/`rw` then close directly.
  have h' : (x₁ = x₃ ∧ x₂ = x₄) ∨ (x₁ = x₄ ∧ x₂ = x₃) := by
    have h1 : x₁ ∈ ({x₃, x₄} : Set H.Point) := by rw [← h]; simp
    have h2 : x₂ ∈ ({x₃, x₄} : Set H.Point) := by rw [← h]; simp
    have h3 : x₃ ∈ ({x₁, x₂} : Set H.Point) := by rw [h]; simp
    have h4 : x₄ ∈ ({x₁, x₂} : Set H.Point) := by rw [h]; simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 h3 h4
    -- h1 : x₁ = x₃ ∨ x₁ = x₄, h2 : x₂ = x₃ ∨ x₂ = x₄,
    -- h3 : x₃ = x₁ ∨ x₃ = x₂, h4 : x₄ = x₁ ∨ x₄ = x₂.
    -- Full case split on h1/h2 (4 cases); the two "degenerate" cases
    -- (x₁ = x₂'s target coinciding) are resolved using h3/h4 to still land
    -- in one of the two target disjuncts.
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · -- x₁ = x₃, x₂ = x₃: use h4 (x₄ = x₁ ∨ x₄ = x₂) to still get x₂ = x₄.
        -- (verified by hand: `h1 : x₁ = x₃`, `h2 : x₂ = x₃`, so `x₃ = x₁` via
        -- `h1.symm`; chain with `h4.symm : x₁ = x₄` to get `x₃ = x₄`, then
        -- prepend `h2 : x₂ = x₃`.)
        rcases h4 with h4 | h4
        · exact Or.inl ⟨h1, h2.trans (h1.symm.trans h4.symm)⟩
        · exact Or.inl ⟨h1, h4.symm⟩
      · exact Or.inl ⟨h1, h2⟩
    · rcases h2 with h2 | h2
      · exact Or.inr ⟨h1, h2⟩
      · -- x₁ = x₄, x₂ = x₄: use h3 (x₃ = x₁ ∨ x₃ = x₂) to still get x₂ = x₃.
        -- (verified by hand, symmetric to the case above: chain
        -- `h1.symm : x₄ = x₁` with `h3.symm : x₁ = x₃` to get `x₄ = x₃`, then
        -- prepend `h2 : x₂ = x₄`.)
        rcases h3 with h3 | h3
        · exact Or.inr ⟨h1, h2.trans (h1.symm.trans h3.symm)⟩
        · exact Or.inr ⟨h1, h3.symm⟩
  rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

/-- If `x₂ = ι x₁` and `x₄ = ι x₃`, then `s x₁ + s x₂ = s x₃ + s x₄`. This is
the content of `a0 := s(x) + s(ι x)` being independent of `x` (advisory-7 §4's
"center" of the Sidon set).

**Not provable for an arbitrary `D : PrincipalDivisorData H`.** As the note
above already spells out, this needs `(x₁) + (ι x₁) - (x₃) - (ι x₃) ∈ D.P`,
and `D.P` is only assumed `P ≤ Divisor0 H` — nothing forces it to contain this
specific divisor. (Concretely: `D.P := ⊥` satisfies `le_Divisor0` trivially,
and makes `s D δ₀` injective, so the conclusion below would force
`x₁ = x₃ ∧ Point.iota x₁ = Point.iota x₃` for *every* `x₁, x₃` — false as soon
as the curve has more than one point.) So this is packaged, in the same style
as `SidonDichotomy` below, as an explicit hypothesis on `D`:
`HyperellipticClass` records exactly the fact that the fiber-difference
divisor `(x₁) + (ι x₁) - (x₃) - (ι x₃)` (the divisor of the function cutting
out `{x₁, ι x₁}` divided by the one cutting out `{x₃, ι x₃}`, both fibers of
the degree-2 map `C → P¹` over the shared `x`-coordinate) lies in `D.P`, for
`D` genuinely built from `CoordinateRing H`'s function field. Given that
hypothesis the theorem is immediate divisor bookkeeping via
`s_add_s_eq_s_add_s_iff`. -/
def PrincipalDivisorData.HyperellipticClass (D : PrincipalDivisorData H) : Prop :=
  ∀ x₁ x₃ : H.Point,
    (single x₁ + single (Point.iota x₁) - single x₃ - single (Point.iota x₃) : Divisor H) ∈ D.P

theorem sum_eq_of_involution_swap (D : PrincipalDivisorData H) (hD : D.HyperellipticClass)
    (δ₀ : H.Point) {x₁ x₃ : H.Point} :
    s D δ₀ x₁ + s D δ₀ (Point.iota x₁) = s D δ₀ x₃ + s D δ₀ (Point.iota x₃) := by
  rw [s_add_s_eq_s_add_s_iff]
  exact hD x₁ x₃

/-- **The easy direction of the FFK dichotomy.** No principal-divisor content
beyond `D.HyperellipticClass` (needed only for the involution-swap disjunct):
either disjunct forces the sum equation, by `sum_eq_of_pair_eq` /
`sum_eq_of_involution_swap`. -/
theorem sum_eq_of_dichotomy (D : PrincipalDivisorData H) (hD : D.HyperellipticClass)
    (δ₀ : H.Point)
    {x₁ x₂ x₃ x₄ : H.Point}
    (h : ({x₁, x₂} : Set H.Point) = {x₃, x₄} ∨
      (x₂ = Point.iota x₁ ∧ x₄ = Point.iota x₃)) :
    s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄ := by
  rcases h with h | ⟨h₂, h₄⟩
  · exact sum_eq_of_pair_eq D δ₀ h
  · subst h₂; subst h₄; exact sum_eq_of_involution_swap D hD δ₀

/-! ## The hard direction: packaged as an explicit hypothesis on `D`

Everything above needs at most `D.HyperellipticClass` (itself a genuinely
true fact about the actual principal divisors of a genus-2 curve, just not
yet derivable from the current abstract `P` — see that definition's
docstring). What follows packages the genuinely genus-2-specific content of
the FFK theorem — that these are the *only* ways the sum equation can
hold — as a bundled property `SidonDichotomy` on
`PrincipalDivisorData`, so the final theorem statement below has the shape
advisory-7 §4 needs, with the gap isolated to exactly one place. -/

/-- The forward direction of FFK, packaged as a property a `PrincipalDivisorData`
can satisfy. A `D` satisfying this is, precisely, one whose `P` is small enough
(in the sense that matters) to force the dichotomy — which is what being
*genuinely* the principal divisors of a genus-2 curve (rather than an arbitrary
degree-0-contained subgroup) is supposed to buy. Not yet derived from
`CoordinateRing H`; see the module docstring. -/
def PrincipalDivisorData.SidonDichotomy (D : PrincipalDivisorData H) : Prop :=
  ∀ δ₀ x₁ x₂ x₃ x₄ : H.Point,
    s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄ →
      ({x₁, x₂} : Set H.Point) = {x₃, x₄} ∨
        (x₂ = Point.iota x₁ ∧ x₄ = Point.iota x₃)

/-- **The Forey–Fresán–Kowalski Sidon theorem** (2023, Theorem 1, case `g=2`),
in the form advisory-7 §4 uses it: for `D` satisfying `SidonDichotomy`, `s`
sends `C(k) → J` to a symmetric Sidon set. Immediate from the packaged
hypothesis plus `s_add_s_eq_s_add_s_iff` for the reduction to divisor form and
`sum_eq_of_dichotomy` for the converse (giving the genuine `↔`, matching the
theorem's "iff"-flavoured statement in the advisory: a hit is *equivalent to*
one of the two degenerate shapes, not merely implied by them). Also needs
`D.HyperellipticClass` — a `D` satisfying `SidonDichotomy` should genuinely
satisfy this too (both are facts that hold for `D`'s built from the actual
principal divisors of a genus-2 curve), so it is threaded through as a second
explicit hypothesis rather than derived from `SidonDichotomy` alone. -/
theorem ffk_sidon_dichotomy (D : PrincipalDivisorData H) (hD : D.SidonDichotomy)
    (hDh : D.HyperellipticClass)
    (δ₀ x₁ x₂ x₃ x₄ : H.Point) :
    s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄ ↔
      ({x₁, x₂} : Set H.Point) = {x₃, x₄} ∨
        (x₂ = Point.iota x₁ ∧ x₄ = Point.iota x₃) :=
  ⟨hD δ₀ x₁ x₂ x₃ x₄, sum_eq_of_dichotomy D hDh δ₀⟩

end HyperellipticPolynomial
