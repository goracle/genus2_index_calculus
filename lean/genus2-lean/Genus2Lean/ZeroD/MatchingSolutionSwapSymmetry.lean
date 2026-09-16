import Mathlib
import Genus2Lean.DivisorClassGroup
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.LPairFinrankOneOrdAtFracSpec

/-!
# The FIXED-`(A,B)` solution set has at most 4 elements

## Correction (this pass), per ChatGPT consult — see the record below

This file previously attempted to bound the **difference-only** solution
set `S := {(P1,P2,P3,P4) | s P1 + s P2 - s P3 - s P4 = target}` directly.
That set does **not** have cardinality bounded independently of `p`: only
the *difference* of the two pair-sum classes is fixed, so the set
decomposes as a union, over every possible pair-sum class `A`, of
`{(P1,P2) | s P1 + s P2 = A} × {(P3,P4) | s P3 + s P4 = A - target}`, and
there is no a priori bound on how many classes `A` occur. Working this out
(with ChatGPT, this pass) surfaced that `IsOnlyEffectiveInClass` only
controls the size of ONE such fiber (for a single fixed class), not the
number of classes `A` that occur — so the previous file's two `sorry`s
were symptoms of trying to prove something false as stated, not a gap in
technique.

**The fix**: restate the target as Claire and the roadmap
(`ROADMAP-alpha-locus.md`, "Newest status update") originally intended —
BOTH pair-sums fixed separately (`s P1 + s P2 = A` and `s P3 + s P4 = B`,
for fixed classes `A B : Jacobian H D`), not just their difference. This
is exactly `FixedTargetSolutions` below. `IsOnlyEffectiveInClass` applies
directly and independently to each of the two fixed-class conditions, and
the ≤4 bound (≤2 ordered pairs per class, two classes) is immediate — no
`Δ`, no pairwise-solution comparison, no sorries.

This file's earlier module docstring (see git history / prior version)
recorded a `Δ`-based framing (`swap_of_matching_solutions`) that turned
out to be mis-scoped; it is superseded entirely by `fixedTargetSolutions_
ncard_le_four` below. `swapImages`/`swapImages_ncard_le` are kept (their
proof was already correct and sorry-free) since `pairFiber_ncard_le_two`'s
proof reuses the same swap-image idea for a single pair.

## What this proves, in one line

For fixed classes `A B : Jacobian H D` (typically `A = α • aClass`,
`B = α' • aClass` for the roadmap's fixed `(alpha,alpha')`), the set of
`(P1,P2,P3,P4)` with `s P1 + s P2 = A` and `s P3 + s P4 = B` has at most 4
elements — feeding directly into `StabOfSmallSetTrivial.lean`'s
`delta_eq_zero_of_stabilizes_small_set` (`S.ncard < ell` is immediate from
`4 < ell` for any cryptographically-sized `ell`), once that theorem is
applied to the correct `S` (the fixed-`(A,B)` set here, not the
difference-only set the previous pass mistakenly tried to use).

## Standing hypotheses this file needs and does not discharge

**The `D.P = principalSubgroup H hdeg` bridge, correct direction.**
`IsOnlyEffectiveInClass` (`RiemannRochGenus2.lean`) is stated against
`principalSubgroup H hdeg`, while `s_add_s_eq_s_add_s_iff`
(`DivisorClassGroup.lean`) — the lemma turning a `Jacobian H D` equality
`s D δ₀ x₁ + s D δ₀ x₂ = s D δ₀ x₃ + s D δ₀ x₄` into the divisor-membership
statement `IsOnlyEffectiveInClass` wants — produces `D.P`-membership. The
direction actually needed to compose them is `D.P ≤ principalSubgroup H
hdeg` (the previous pass had this backwards, calling it `hbridge :
principalSubgroup H hdeg ≤ D.P`; corrected here). Taken as an explicit
hypothesis below, in this project's usual honest-hypothesis style — NOT
derived, since the two subgroups' equality is itself unproved
project-wide.

**`IsOnlyEffectiveInClass`'s own proof status**, unchanged from the
previous pass: taken as an explicit hypothesis rather than invoked by
name, so this file is usable regardless of how that audit resolves.

**Verification status: drafted without a live Lean toolchain**, same
caveat as this project's other unverified scaffolding — not yet `lake
build`-checked. -/

open HyperellipticPolynomial
open Divisor

namespace Genus2Lean
namespace MatchingSolutionSwapSymmetry

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable (D : PrincipalDivisorData H)
variable [IsDedekindDomain (CoordinateRing H)]

/-! ## The four-swaps set, as data -/

/-- **The four swap-images of `(P1,P2,P3,P4)`**, as a `Set` of 4-tuples —
the concrete finite carrier this file's main theorem shows the solution
set embeds into. Stated as literal tuple equality (not `Jacobian`
equality) since `IsOnlyEffectiveInClass` gives `{x₃,x₄} = {x₁,x₂}` at
the `H.Point`-pair level directly. -/
def swapImages (P1 P2 P3 P4 : H.Point) :
    Set (H.Point × H.Point × H.Point × H.Point) :=
  {(P1, P2, P3, P4), (P2, P1, P3, P4), (P1, P2, P4, P3), (P2, P1, P4, P3)}

/-- `swapImages` is finite — a literal 4-element (or fewer) set, regardless
of whether `H.Point` itself is a finite type. Needed since `Set.toFinite`
cannot discharge finiteness for an arbitrary subset of `H.Point` (no
`Finite H.Point` instance exists project-wide). Proved via the same
finset-coercion identity used in `swapImages_ncard_le` below, so it only
relies on `Finset.finite_toSet` — a safe, standard name — rather than a
chain of `Set.Finite.insert` calls whose exact signature was not checked
against a live goal state. -/
theorem swapImages_finite [DecidableEq H.Point] (P1 P2 P3 P4 : H.Point) :
    (swapImages P1 P2 P3 P4).Finite := by
  have heq : swapImages P1 P2 P3 P4 =
      (({(P1, P2, P3, P4), (P2, P1, P3, P4), (P1, P2, P4, P3), (P2, P1, P4, P3)} :
          Finset (H.Point × H.Point × H.Point × H.Point)) : Set _) := by
    classical
    rw [swapImages]; push_cast; rfl
  rw [heq]
  exact Finset.finite_toSet _

/-- `swapImages` has at most 4 elements — an upper bound, not asserted as
an equality, since the four listed tuples may coincide (e.g. `P1 = P2`
degenerately, or `P3 = P4`) without that being a problem for the bounds
this file's theorems actually need. -/
theorem swapImages_ncard_le [DecidableEq H.Point] (P1 P2 P3 P4 : H.Point) :
    (swapImages P1 P2 P3 P4).ncard ≤ 4 := by
  classical
  calc (swapImages P1 P2 P3 P4).ncard
      ≤ ({(P1, P2, P3, P4), (P2, P1, P3, P4), (P1, P2, P4, P3), (P2, P1, P4, P3)} :
          Finset (H.Point × H.Point × H.Point × H.Point)).card := by
        rw [swapImages, ← Set.ncard_coe_finset]
        exact le_of_eq (by push_cast; rfl)
    _ ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp

/-! ## Step 1: a single fixed pair-sum class has at most 2 ordered
representations -/

/-- **Unordered-pair-equality case bash, factored out.** If
`{x₁,x₂} = {y₁,y₂}` as sets of points, then either `x₁=y₁ ∧ x₂=y₂` or
`x₁=y₁... ` — precisely, `(x₁=y₁ ∧ x₂=y₂) ∨ (x₁=y₂ ∧ x₂=y₁)`. Factored
into its own lemma since `pairFiber_ncard_le_two` and
`fixedTargetSolutions_ncard_le_four` both need exactly this step (applied
to the `{P1,P2}`/`{P1',P2'}` pair and independently to the
`{P3,P4}`/`{P3',P4'}` pair) — proving it once here avoids duplicating the
error-prone manual case chain. Derived by the manual `Set.ext_iff`/
membership case-bash route, matching `FFKSidon.lean`'s `sum_eq_of_pair_eq`
— `Set.pair_eq_pair_iff` is deliberately not used (see that file's
comment) to avoid depending on an unverified exact name/signature. Every
`.trans`/`.symm` chain in the two degenerate branches was hand-traced
before being written (see the working notes accompanying this pass). -/
theorem pair_eq_pair_cases {x₁ x₂ y₁ y₂ : H.Point}
    (hset : ({x₁, x₂} : Set H.Point) = {y₁, y₂}) :
    (x₁ = y₁ ∧ x₂ = y₂) ∨ (x₁ = y₂ ∧ x₂ = y₁) := by
  have h1 : x₁ ∈ ({y₁, y₂} : Set H.Point) := by rw [← hset]; simp
  have h2 : x₂ ∈ ({y₁, y₂} : Set H.Point) := by rw [← hset]; simp
  have h3 : y₁ ∈ ({x₁, x₂} : Set H.Point) := by rw [hset]; simp
  have h4 : y₂ ∈ ({x₁, x₂} : Set H.Point) := by rw [hset]; simp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 h3 h4
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · -- Degenerate: h1 : x₁ = y₁, h2 : x₂ = y₁ (both equal y₁).
      -- Need x₂ = y₂ too. Use h4 : y₂ = x₁ ∨ y₂ = x₂.
      rcases h4 with h4 | h4
      · -- h4 : y₂ = x₁, with h1 : x₁ = y₁, gives y₂ = y₁;
        -- then x₂ = y₁ (h2) rewritten along (y₂ = y₁).symm gives x₂ = y₂.
        exact Or.inl ⟨h1, h2.trans (h4.trans h1).symm⟩
      · -- h4 : y₂ = x₂, directly gives x₂ = y₂.
        exact Or.inl ⟨h1, h4.symm⟩
    · exact Or.inl ⟨h1, h2⟩
  · rcases h2 with h2 | h2
    · exact Or.inr ⟨h1, h2⟩
    · -- Degenerate: h1 : x₁ = y₂, h2 : x₂ = y₂ (both equal y₂).
      -- Need x₂ = y₁ too. Use h3 : y₁ = x₁ ∨ y₁ = x₂.
      rcases h3 with h3 | h3
      · -- h3 : y₁ = x₁, with h1 : x₁ = y₂, gives y₁ = y₂;
        -- then x₂ = y₂ (h2) rewritten along (y₁ = y₂).symm gives x₂ = y₁.
        exact Or.inr ⟨h1, h2.trans (h3.trans h1).symm⟩
      · -- h3 : y₁ = x₂, directly gives x₂ = y₁.
        exact Or.inr ⟨h1, h3.symm⟩

/-- **`PairFiber δ₀ A`**: the ordered pairs `(P,Q)` whose `s`-image sums
to a FIXED class `A`. This is the object `IsOnlyEffectiveInClass` actually
controls directly (unlike the previous pass's difference-only solution
set, which ranges over infinitely many such classes). -/
def PairFiber (δ₀ : H.Point) (A : Jacobian H D) : Set (H.Point × H.Point) :=
  {q | s D δ₀ q.1 + s D δ₀ q.2 = A}

/-- **A fixed pair-sum class has at most 2 ordered representations.**
If `(P1,P2)` and `(P1',P2')` both sum (under `s`) to the same class `A`,
`IsOnlyEffectiveInClass` (applied to the base pair `(P1,P2)`, given the
bridge hypothesis) forces `{P1',P2'} = {P1,P2}` as an unordered pair of
points, so `(P1',P2')` is one of exactly two ordered tuples: `(P1,P2)`
itself or its swap `(P2,P1)`. -/
theorem pairFiber_ncard_le_two [DecidableEq H.Point]
    {hdeg : H.f.natDegree = 5} {δ₀ : H.Point}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    {P1 P2 : H.Point} (heffective : IsOnlyEffectiveInClass hdeg P1 P2)
    (A : Jacobian H D) (hA : A = s D δ₀ P1 + s D δ₀ P2) :
    (PairFiber D δ₀ A).ncard ≤ 2 := by
  classical
  have hsub : PairFiber D δ₀ A ⊆ ({(P1, P2), (P2, P1)} : Set (H.Point × H.Point)) := by
    rintro ⟨P1', P2'⟩ hmem
    simp only [PairFiber, Set.mem_setOf_eq] at hmem
    have heq : s D δ₀ P1 + s D δ₀ P2 = s D δ₀ P1' + s D δ₀ P2' := by
      rw [← hA, hmem]
    have hiff := (s_add_s_eq_s_add_s_iff D δ₀ P1 P2 P1' P2').mp heq
    have hmemPrin : (single P1 + single P2 - single P1' - single P2' : Divisor H) ∈
        principalSubgroup H hdeg := hbridge hiff
    have hset : ({P1', P2'} : Set H.Point) = {P1, P2} := heffective P1' P2' hmemPrin
    rcases pair_eq_pair_cases hset with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact Prod.ext h1 h2
    · right; exact Prod.ext h1 h2
  calc (PairFiber D δ₀ A).ncard
      ≤ ({(P1, P2), (P2, P1)} : Set (H.Point × H.Point)).ncard := by
        refine Set.ncard_le_ncard hsub ?_
        have heq : ({(P1, P2), (P2, P1)} : Set (H.Point × H.Point)) =
            (({(P1, P2), (P2, P1)} : Finset (H.Point × H.Point)) : Set _) := by
          push_cast; rfl
        rw [heq]; exact Finset.finite_toSet _
    _ ≤ ({(P1, P2), (P2, P1)} : Finset (H.Point × H.Point)).card := by
        rw [← Set.ncard_coe_finset]
        exact le_of_eq (by push_cast; rfl)
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

/-! ## Step 2: the fixed-`(A,B)` solution set, assembled from two
independent pair-fibers -/

/-- **`FixedTargetSolutions δ₀ A B`**: quadruples with BOTH pair-sums
fixed independently — `s P1 + s P2 = A` and `s P3 + s P4 = B` — matching
`ROADMAP-alpha-locus.md`'s original `(alpha,alpha')`-fixed framing
(`A = α • aClass`, `B = α' • aClass` in that roadmap's notation), NOT the
difference-only `s P1 + s P2 - s P3 - s P4 = target` set the previous
pass of this file mistakenly tried to bound (see the corrected module
docstring above for why that set is unbounded independent of `p`). -/
def FixedTargetSolutions (δ₀ : H.Point) (A B : Jacobian H D) :
    Set (H.Point × H.Point × H.Point × H.Point) :=
  {x | s D δ₀ x.1 + s D δ₀ x.2.1 = A ∧ s D δ₀ x.2.2.1 + s D δ₀ x.2.2.2 = B}

/-- **Main theorem.** For fixed classes `A B : Jacobian H D`, given a base
solution `(P1,P2,P3,P4)` (i.e. `s P1+s P2 = A` and `s P3+s P4 = B`) and
`IsOnlyEffectiveInClass` for both `{P1,P2}` and `{P3,P4}`,
`FixedTargetSolutions δ₀ A B` has at most 4 elements: at most 2 choices
for `(P1',P2')` (`pairFiber_ncard_le_two` applied to `A`) times at most 2
for `(P3',P4')` (applied to `B`). This is the bound
`StabOfSmallSetTrivial.lean`'s `delta_eq_zero_of_stabilizes_small_set`
actually needs (`S.ncard < ell`, via `4 < ell` for cryptographic `ell`),
once `S` is correctly taken to be this fixed-`(A,B)` set rather than the
unbounded difference-only set. -/
theorem fixedTargetSolutions_ncard_le_four [DecidableEq H.Point]
    {hdeg : H.f.natDegree = 5} {δ₀ : H.Point}
    (hbridge : D.P ≤ principalSubgroup H hdeg)
    {P1 P2 P3 P4 : H.Point}
    (heffective12 : IsOnlyEffectiveInClass hdeg P1 P2)
    (heffective34 : IsOnlyEffectiveInClass hdeg P3 P4)
    (A B : Jacobian H D)
    (hA : A = s D δ₀ P1 + s D δ₀ P2) (hB : B = s D δ₀ P3 + s D δ₀ P4) :
    (FixedTargetSolutions D δ₀ A B).ncard ≤ 4 := by
  classical
  -- Rather than reaching for a general `Set`-product cardinality lemma
  -- (an unverified name/signature risk, per this project's working
  -- agreement), show `FixedTargetSolutions` is literally a subset of
  -- `swapImages P1 P2 P3 P4` — reusing that already-proved, sorry-free
  -- bound directly: any solution `(P1',P2',P3',P4')` has `(P1',P2')` one
  -- of `(P1,P2)`/`(P2,P1)` (via `pairFiber_ncard_le_two`'s membership
  -- argument, inlined here) and independently `(P3',P4')` one of
  -- `(P3,P4)`/`(P4,P3)`, landing in one of the same four listed tuples.
  have hsub : FixedTargetSolutions D δ₀ A B ⊆ swapImages P1 P2 P3 P4 := by
    rintro ⟨P1', P2', P3', P4'⟩ ⟨h1, h2⟩
    have hA' : s D δ₀ P1' + s D δ₀ P2' = A := h1
    have hB' : s D δ₀ P3' + s D δ₀ P4' = B := h2
    have heq12 : s D δ₀ P1 + s D δ₀ P2 = s D δ₀ P1' + s D δ₀ P2' := hA.symm.trans hA'.symm
    have heq34 : s D δ₀ P3 + s D δ₀ P4 = s D δ₀ P3' + s D δ₀ P4' := hB.symm.trans hB'.symm
    have hiff12 := (s_add_s_eq_s_add_s_iff D δ₀ P1 P2 P1' P2').mp heq12
    have hiff34 := (s_add_s_eq_s_add_s_iff D δ₀ P3 P4 P3' P4').mp heq34
    have hmem12 : (single P1 + single P2 - single P1' - single P2' : Divisor H) ∈
        principalSubgroup H hdeg := hbridge hiff12
    have hmem34 : (single P3 + single P4 - single P3' - single P4' : Divisor H) ∈
        principalSubgroup H hdeg := hbridge hiff34
    have hset12 : ({P1', P2'} : Set H.Point) = {P1, P2} := heffective12 P1' P2' hmem12
    have hset34 : ({P3', P4'} : Set H.Point) = {P3, P4} := heffective34 P3' P4' hmem34
    have hcase12 := pair_eq_pair_cases hset12
    have hcase34 := pair_eq_pair_cases hset34
    simp only [swapImages, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hcase12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hcase34 with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact Or.inl (by rw [e1, e2, e3, e4])
    · exact Or.inr (Or.inr (Or.inl (by rw [e1, e2, e3, e4])))
    · exact Or.inr (Or.inl (by rw [e1, e2, e3, e4]))
    · exact Or.inr (Or.inr (Or.inr (by rw [e1, e2, e3, e4])))
  calc (FixedTargetSolutions D δ₀ A B).ncard
      ≤ (swapImages P1 P2 P3 P4).ncard := Set.ncard_le_ncard hsub (swapImages_finite P1 P2 P3 P4)
    _ ≤ 4 := swapImages_ncard_le P1 P2 P3 P4

end MatchingSolutionSwapSymmetry
end Genus2Lean
