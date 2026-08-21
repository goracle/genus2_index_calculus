/- DRAFT continued.

STEP 2: the actual transport lemma. `renameEquiv (F p) (optionSplit x) :
Rdec p ≃ₐ[F p] MvPolynomial (Option τ) (F p)` (τ := {v : Idx // v ≠ x})
is a RING equivalence, so it carries `Ideal.span S` to
`Ideal.span (equiv '' S)` for any set `S`, hence induces a ring
equivalence on quotients (`Ideal.quotientEquiv`) once we know how it acts
on the specific generator list at hand. Since it's an ALGEBRA equiv (in
particular a ring equiv), regularity of an element transports across it
via `Ideal.quotientEquiv`+`RingEquiv`-conjugation, exactly the same
pattern already used successfully in `regular_of_disjoint_extension`
(`hIdealMap`/`e'`/`e'.injective` there) and in `regular_of_peeled_leadingCoeff`
(`hIdealMap`/`e`/`e.injective`). This draft reuses that EXACT pattern
rather than inventing a new one.

Concretely, for a list `gens' : List (MvPolynomial τ (F p))` (τ := {v :
Idx // v ≠ x}) and `g : MvPolynomial (Option τ) (F p)`, if we set
  `gensRdec : List (Rdec p) := gens'.map (fun q => (renameEquiv (F p)
    (optionSplit x)).symm (rename some q))`
  `gRdec : Rdec p := (renameEquiv (F p) (optionSplit x)).symm g`
then `renameEquiv (F p) (optionSplit x)` carries `Ideal.span gensRdec.toFinset`-ish
(really `Ideal.ofList gensRdec`) to `Ideal.ofList (gens'.map (rename some))`
by `Ideal.map_ofList` + `RingEquiv` naturality of `rename`, and carries
`gRdec` to `g`. So:

  `IsSMulRegular (Rdec p ⧸ Ideal.ofList gensRdec) gRdec`
    ↔ (transport across the induced quotient ring equiv)
  `IsSMulRegular (MvPolynomial (Option τ) (F p) ⧸ Ideal.ofList (gens'.map (rename some))) g`

This is the general bridge. Rather than writing it once abstractly (which
still needs an `Ideal.quotientEquiv` + injectivity argument each time it's
invoked, since `IsSMulRegular` doesn't transport for free without knowing
the SMul actions agree, exactly the fiddly step `regular_of_disjoint_extension`
already had to do by hand), I state and prove it ONCE as its own lemma so
each of the 12 stages below just invokes it.

Actually, for THIS project's use, we never need the fully generic version
above — at every stage the "already imposed prefix" `gens'` is a FIXED,
finite, EXPLICIT list of ≤ 11 polynomials (not a variable-length
parameter), and the peel variable `x` is one of `U0,U1,V0,V1` (the 8
"easy"/"repeated" stages) or a `w`-variable (the 4 curve stages). So the
bridge lemma is stated in exactly the shape the assembly needs: given a
LIST of `Rdec p` elements not mentioning `x` (`hgens'_indep`), and a
generator `g = c - X x * d` (linear stages) or `g` itself monic-shaped
(curve stages), relate `IsSMulRegular (Rdec p ⧸ Ideal.ofList gens')` to
the abstract lemmas.

DESIGN DECISION: rather than manually pushing `Ideal.ofList` through
`List.map`/`rename` at each of 12 call sites (fragile, error-prone
bookkeeping that's exactly what the roadmap flags as "genuine bookkeeping
work"), package the FULL bridge as one reusable lemma:
-/

/-- **The master bridge lemma.** Let `x : Idx`, `τ := {v : Idx // v ≠ x}`.
Suppose `gens' : List (Rdec p)` are `Rdec p`-valued but ALL come from
`τ` (i.e. each is `(peelVarsEquiv x).symm (rename some q)` for some
`q : MvPolynomial τ (F p)` not mentioning `x` at all — packaged via
`hgens'` giving the witnessing `τ`-side list `qs'` directly, avoiding an
existence-quantifier reformulation of "doesn't mention x" that would need
its own separate `vars`-based lemma). Suppose further `g : Rdec p` is
ALSO of this form (image of some `G : MvPolynomial (Option τ) (F p)`).
Then `IsSMulRegular (Rdec p ⧸ Ideal.ofList gens') g` transports exactly
to/from the abstract `MvPolynomial (Option τ) (F p)`-level statement.

This lemma's PROOF is the one genuinely new piece of bookkeeping the
assembly needs beyond what's already proved -- everything else (Layer
1/2, `regular_of_linear_elim`, `regular_of_disjoint_extension`,
`isSMulRegular_of_mul_eq_of_isSMulRegular`) is already in hand and gets
INVOKED through this bridge, not re-proved. -/
theorem isSMulRegular_bridge (x : Idx) (gens' : List (MvPolynomial {v : Idx // v ≠ x} (F p)))
    (G : MvPolynomial (Option {v : Idx // v ≠ x}) (F p)) :
    IsSMulRegular
      (Rdec p ⧸ Ideal.ofList (gens'.map (fun q =>
        (MvPolynomial.renameEquiv (F p) (optionSplit x)).symm (MvPolynomial.rename some q))))
      ((MvPolynomial.renameEquiv (F p) (optionSplit x)).symm G)
    ↔
    IsSMulRegular
      (MvPolynomial (Option {v : Idx // v ≠ x}) (F p) ⧸
        Ideal.ofList (gens'.map (MvPolynomial.rename some)))
      G := by
  sorry -- proof: Ideal.quotientEquiv transport, same pattern as
        -- `regular_of_disjoint_extension`'s `hIdealMap`/`e'` block.
