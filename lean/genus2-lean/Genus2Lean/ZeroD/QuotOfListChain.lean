import Mathlib

/-!
# Assembly, part 1: chaining `Ideal.ofList` quotients one generator at a time

Item 5 of `ROADMAP-monic-annihilator-degree-uniform.md`'s file plan, step
5 of its "Suggested order" — the first of (up to) two Assembly files. This
file supplies the purely ring-theoretic bridging fact the `finrank`-chaining
argument needs; the second file (not yet written) specializes it to
`Rdec p` and the literal 12-element `genList`, applying it once per stage
alongside `FinrankLeOfMonicAnnihilator.lean` / `LinearElimDegreeBound.lean`
/ `LinearElimDegreeBoundExt.lean` / `CurveRelationsDegreeBound.lean`'s
per-stage facts.

**Why this piece is needed, and why it's split out on its own**: every
per-stage `finrank` lemma in this roadmap's earlier files
(`finrank_le_of_monic_annihilator`, `finrank_le_of_linear_elim`,
`finrank_le_of_curve_relation`) is stated for an ABSTRACT `A`-algebra `B`
with a generating element `t`. To CHAIN twelve of these via
`Module.finrank_mul_finrank` (the tower law) into one bound on the
literal `Rdec p ⧸ Ideal.span (genList ...).toFinset`, each stage's `B`
must be identified with `(the previous stage's quotient) ⧸ (the next
single generator's image)` — but the actual target ring
`Rdec p ⧸ Ideal.ofList (gens ++ [g])` is a ONE-STEP quotient of `Rdec p`
by the WHOLE extended list, not literally a quotient-of-a-quotient. This
file proves those two presentations coincide (as a ring isomorphism, with
the quotient maps matching up on the nose), for one appended generator at
a time — the same content `PeelChainAssembly.lean`'s
`hFu1Fu3Fv1Fv3_reg_of`-adjacent regularity-transport proof already uses
internally (`DoubleQuot.quotQuotEquivQuotSup` + `Ideal.ofList_append`),
but extracted here as a small, self-contained, `MvPolynomial`/`τ`-free
lemma over any commutative ring, since that project-specific machinery
was there to transport REGULARITY across the isomorphism — a strictly
harder ask than this file's job, which only needs the isomorphism itself
plus the induced `finrank` equality (an `AlgEquiv`/`RingEquiv` preserves
`finrank` outright, no transport argument needed beyond that).

**Proof strategy**: `Ideal.ofList_append : Ideal.ofList (gens ++ [g]) =
Ideal.ofList gens ⊔ Ideal.ofList [g]` combined with `Ideal.ofList_singleton`
turns the target into `Ideal.ofList gens ⊔ Ideal.span {g}`, and
`DoubleQuot.quotQuotEquivQuotSup` is Mathlib's own ring isomorphism
`(R ⧸ I) ⧸ (J.map (mk I)) ≃+* R ⧸ (I ⊔ J)` for exactly this shape (with
`I := Ideal.ofList gens`, `J := Ideal.span {g}`) — composed with
`Ideal.quotEquivOfEq` to rewrite the `⊔`-shaped ideal into the
`Ideal.ofList (gens ++ [g])`-shaped one the caller actually wants. The
remaining bookkeeping is showing `J.map (mk I) = Ideal.span {mk I g}`
(via `Ideal.map_span`/`Set.image_singleton`), so that the LHS ring is
literally `(R ⧸ Ideal.ofList gens) ⧸ Ideal.span {mk I g}` — i.e.
"quotient by the image of the new generator," the natural `B := A ⧸
Ideal.span {c}`-shaped algebra each per-stage `finrank` lemma's abstract
`B`/`t` gets instantiated against at Assembly time. -/

namespace Genus2Lean

variable {R : Type*} [CommRing R]

/-- **The single-generator quotient-chaining isomorphism.** Extending a
generator list `gens` by one more element `g` and taking the ONE-STEP
quotient `R ⧸ Ideal.ofList (gens ++ [g])` is ring-isomorphic to the
TWO-STEP quotient `(R ⧸ Ideal.ofList gens) ⧸ Ideal.span {image of g}` —
i.e. "quotient by everything at once" agrees with "quotient by the
prefix, then quotient that ring by the new generator's image," matching
each per-stage `finrank` lemma's abstract `B := A ⧸ Ideal.span {c}` shape
to the literal `Rdec p ⧸ Ideal.ofList (prefix ++ [newGen])` Assembly
needs to reach. -/
noncomputable def quotOfListCons_ringEquiv (gens : List R) (g : R) :
    (R ⧸ Ideal.ofList gens) ⧸ Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} :
        Set (R ⧸ Ideal.ofList gens)) ≃+*
      R ⧸ Ideal.ofList (gens ++ [g]) :=
  -- Step 1: rewrite the inner ideal `Ideal.span {mk gens g}` to the
  -- `Ideal.map (mk gens) (Ideal.span {g})` shape `DoubleQuot` expects,
  -- via `Ideal.quotEquivOfEq` (equal ideals ⇒ isomorphic quotient rings)
  -- — a direct ideal-level rewrite, no detour through `Ideal.quotientEquiv`
  -- with an otherwise-unused `RingEquiv.refl` first argument.
  (Ideal.quotEquivOfEq (I := Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} :
      Set (R ⧸ Ideal.ofList gens)))
    (J := Ideal.map (Ideal.Quotient.mk (Ideal.ofList gens)) (Ideal.span ({g} : Set R))) (by
      rw [Ideal.map_span, Set.image_singleton])).trans
  -- Step 2: `DoubleQuot.quotQuotEquivQuotSup` identifies the resulting
  -- two-step quotient with `R ⧸ (Ideal.ofList gens ⊔ Ideal.span {g})`.
  (((DoubleQuot.quotQuotEquivQuotSup (Ideal.ofList gens) (Ideal.span ({g} : Set R))).trans
  -- Step 3: rewrite `Ideal.ofList gens ⊔ Ideal.span {g}` to the target
  -- `Ideal.ofList (gens ++ [g])` via `Ideal.ofList_append` +
  -- `Ideal.ofList_singleton`.
    (Ideal.quotEquivOfEq (by
      rw [← Ideal.ofList_singleton (g : R), ← Ideal.ofList_append]))))

/-- The isomorphism sends the distinguished basepoint `mk (mk gens x)` to
the single-step quotient's `mk (gens ++ [g]) x`, for `x : R` — the fact
needed to transport a proved-abstractly `aeval t (linearElimPoly c d) = 0`
/ `Algebra.adjoin A {t} = ⊤` style hypothesis, stated against the
two-step ring, onto the literal `Rdec p ⧸ Ideal.ofList (prefix ++ [g])`
ring Assembly's final statement is phrased over (or vice versa) — needed
because those hypotheses are about specific ELEMENTS, not just an
abstract ring shape, so the isomorphism alone isn't enough without also
knowing where it sends the point of interest. -/
theorem quotOfListCons_ringEquiv_apply_mk_mk (gens : List R) (g : R) (x : R) :
    quotOfListCons_ringEquiv gens g
      (Ideal.Quotient.mk (Ideal.span ({Ideal.Quotient.mk (Ideal.ofList gens) g} :
          Set (R ⧸ Ideal.ofList gens)))
        (Ideal.Quotient.mk (Ideal.ofList gens) x)) =
      Ideal.Quotient.mk (Ideal.ofList (gens ++ [g])) x := by
  unfold quotOfListCons_ringEquiv
  simp only [RingEquiv.trans_apply]
  rw [Ideal.quotEquivOfEq_mk]
  -- The term produced by `Ideal.quotEquivOfEq_mk` is, up to unfolding, exactly
  -- `DoubleQuot.quotQuotMk (Ideal.ofList gens) (Ideal.span {g}) x`, but `simp`/`rw`
  -- leave it as the raw double-`Ideal.Quotient.mk` application rather than the
  -- `quotQuotMk`-headed term the `_quotQuotMk` simp lemma's LHS pattern expects
  -- syntactically. `show` re-states the goal in the defeq `quotQuotMk`-headed form
  -- so the subsequent `rw` has something to match against.
  show (DoubleQuot.quotQuotEquivQuotSup (Ideal.ofList gens) (Ideal.span ({g} : Set R))).trans
        (Ideal.quotEquivOfEq (by
          rw [← Ideal.ofList_singleton (g : R), ← Ideal.ofList_append]))
      (DoubleQuot.quotQuotMk (Ideal.ofList gens) (Ideal.span ({g} : Set R)) x) =
      Ideal.Quotient.mk (Ideal.ofList (gens ++ [g])) x
  rw [RingEquiv.trans_apply, DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

end Genus2Lean
