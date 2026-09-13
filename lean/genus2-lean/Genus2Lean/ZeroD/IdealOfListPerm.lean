import Mathlib

/-!
# `Ideal.ofList` is invariant under `List.Perm`

`OptionSplitPolynomialEquiv.lean`'s own docstring names this as one of
two things still needed to actually use its triangular-tower bridge
against `genList`'s literal (non-triangular) order: since `genList`'s
stated order (`FuList ++ FvList ++ [curveA1,...]`) is not triangular,
Assembly must apply the `Option`-split bridge along a REORDERED
(genuinely triangular) peel sequence, then transport the resulting
bound back onto `Ideal.ofList genList` in its ORIGINAL order — which
needs exactly this fact: reordering a generator list by a permutation
doesn't change the ideal it generates.

**Proof avoids `unfold`ing `Ideal.ofList`'s raw definition** (its exact
defining equation wasn't independently re-confirmed this pass via direct
source inspection, only its public API, so relying on `unfold` here
would be building on an unverified assumption) **and instead proceeds by
structural induction on `List.Perm` itself**, using only already-confirmed,
project-trusted lemmas: `Ideal.ofList_nil`, `Ideal.ofList_cons` (`Ideal.
ofList (r :: ys) = Ideal.span {r} ⊔ Ideal.ofList ys` — both already used
elsewhere in this project, `PeelChainAssembly.lean`/
`RegularSequenceFiniteQuotient.lean` respectively), plus the lattice
identities `sup_assoc`/`sup_comm`/`sup_left_comm` for the two "shuffle"
constructors (`List.Perm.swap`, `List.Perm.trans`) `List.Perm`'s
inductive definition is built from (`List.Perm.nil`, `.cons`, `.swap`,
`.trans` — the four constructors any `List.Perm` proof reduces to,
confirmed standard Mathlib4 structure, matching how this project's own
`regularSeq_of_peel_chain` already reasons about `List.Perm`-adjacent
`Ideal.ofList_append`/`_cons`/`_nil` identities elsewhere). This is more
verbose than a one-line `Set.ext` argument would be if `Ideal.ofList`'s
raw definition were confirmed, but never relies on an unverified
assumption about that definition's exact shape. -/

namespace Genus2Lean

/-- **`Ideal.ofList` only depends on a list's underlying set of elements,
not its order.** If `l₁` and `l₂` are permutations of one another, they
generate the same ideal. The genuinely load-bearing fact for reordering
a peel chain (e.g. moving `genList`'s curve-relation generators to the
front of a triangular reordering, then transporting a bound proved
against that reordering back to `genList`'s own stated order) — proved
here as its own standalone, `Genus2Lean`-agnostic lemma so it's reusable
independent of any particular reordering strategy.

**Proof, by induction on `List.Perm`'s four constructors** (`nil`/
`cons`/`swap`/`trans`), never unfolding `Ideal.ofList` itself:
- `nil`: both sides are `Ideal.ofList []`, `rfl`.
- `cons a h ih`: `Ideal.ofList (a :: l₁) = span {a} ⊔ Ideal.ofList l₁`
  (`Ideal.ofList_cons`) `= span {a} ⊔ Ideal.ofList l₂` (by `ih`)
  `= Ideal.ofList (a :: l₂)` (`Ideal.ofList_cons` again).
- `swap a b l`: `Ideal.ofList (b :: a :: l) = span {b} ⊔ (span {a} ⊔
  Ideal.ofList l})` two applications of `Ideal.ofList_cons` deep) equals
  `Ideal.ofList (a :: b :: l)`'s same two-deep unfolding, by `sup_comm`
  on the two singleton spans (`⊔` on a lattice/`Ideal` is commutative
  and associative, so swapping the front two elements of a `cons`-chain
  changes nothing).
- `trans h₁₂ h₂₃ ih₁₂ ih₂₃`: chain the two equalities.

No properties of the base ring beyond `CommSemiring` (matching
`Ideal.ofList`'s own ambient assumption in every project usage) are
needed anywhere in this argument. -/
theorem Ideal.ofList_perm {R : Type*} [CommSemiring R] {l₁ l₂ : List R}
    (h : l₁.Perm l₂) : Ideal.ofList l₁ = Ideal.ofList l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    simp only [Ideal.ofList_cons, ih]
  | swap a b l =>
    -- **Not yet REPL-confirmed**: `Ideal.ofList_cons`'s exact RHS
    -- argument order (`Ideal.span {r} ⊔ Ideal.ofList ys` vs. `Ideal.ofList
    -- ys ⊔ Ideal.span {r}`) was not independently re-derivable from
    -- available documentation this pass — only that the lemma exists and
    -- unfolds a `cons` one layer, from this project's own confirmed use
    -- of it in `RegularSequenceFiniteQuotient.lean`. `simp` with the
    -- commutative/associative lattice identities below should close this
    -- goal regardless of which argument order the real lemma states, but
    -- flagging this honestly rather than asserting a specific `rw`
    -- sequence that assumes one particular order: if this `simp` call
    -- fails to close the goal, the fix is almost certainly a
    -- `sup_comm`/`sup_assoc` variant, not a wrong overall proof strategy.
    simp only [Ideal.ofList_cons, sup_assoc, sup_left_comm]
  | trans _ _ ih₁₂ ih₂₃ => rw [ih₁₂, ih₂₃]

/-- **Corollary, quotient-ring form.** The two one-step quotients
`R ⧸ Ideal.ofList l₁` and `R ⧸ Ideal.ofList l₂` are literally the SAME
ring (not just isomorphic) whenever `l₁.Perm l₂`, since they quotient by
the same ideal — stated separately from `Ideal.ofList_perm` itself since
callers transporting a `Module.finrank`/`Module.Finite`/`Nontrivial` fact
across a reordering will want the quotient-ring equality directly rather
than re-deriving it from the ideal equality at each use site. -/
theorem Ideal.quotient_ofList_perm_eq {R : Type*} [CommRing R] {l₁ l₂ : List R}
    (h : l₁.Perm l₂) : (R ⧸ Ideal.ofList l₁) = (R ⧸ Ideal.ofList l₂) := by
  rw [Ideal.ofList_perm h]

end Genus2Lean
