/- DRAFT — bridge lemma design, not yet inserted into the main file.

GOAL: turn `regular_of_linear_elim` / `regular_of_peeled_leadingCoeff` /
`regular_of_disjoint_extension` / `isSMulRegular_of_mul_eq_of_isSMulRegular`
(all stated over the generic `Option τ` / `σ₁ ⊕ σ₂` shapes) into statements
about `Rdec p ⧸ Ideal.span {already-imposed prefix}` at each of the 12
peel stages, WITHOUT re-deriving `Idx ≃ Option τ` by hand each time.

KEY OBSERVATION: `peelEquivGen p x : MvPolynomial σ (F p) ≃ₐ[F p]
Polynomial (MvPolynomial {v // v≠x} (F p))` is BUILT from
`renameEquiv (F p) (e : σ ≃ Option {v // v≠x})` composed with
`optionEquivLeft`. So the `Idx ≃ Option τ` equivalence `peelEquivGen`
uses internally is exactly what I need — I'll pull it out as its own
named `def` so both `peelEquiv` and the bridge lemma below share it
verbatim (avoiding two independently-elaborated copies of the same
equivalence, which risks a defeq-but-not-syntactic mismatch exactly like
several comments in this file already flag as a recurring failure mode).

STEP 1: name the `Idx`-level equivalence explicitly.
-/

/-- The `Option`-splitting equivalence `peelEquivGen`/`peelEquiv` build
internally, pulled out as its own named `def` so the bridge lemma below
and `peelEquiv` provably use the SAME equivalence (avoiding two
independently-elaborated-but-defeq copies, which risks the kind of
syntactic mismatch several existing comments in this file flag as a
recurring failure mode, e.g. `hE₁_inl`'s `simpa` fix in
`regular_of_disjoint_extension`). -/
noncomputable def optionSplit {σ : Type*} [DecidableEq σ] (x : σ) :
    σ ≃ Option {v : σ // v ≠ x} :=
  ((Equiv.optionSubtype x).symm (Equiv.refl {v : σ // v ≠ x})).val.symm

/-- `peelEquivGen` restated literally in terms of `optionSplit`, so the
two are syntactically the same composite (this should be `rfl` against
the existing `peelEquivGen` definition, confirming no divergence). -/
theorem peelEquivGen_eq {σ : Type*} [DecidableEq σ] (x : σ) :
    peelEquivGen p x =
      (MvPolynomial.renameEquiv (F p) (optionSplit x)).trans
        (MvPolynomial.optionEquivLeft (F p) {v : σ // v ≠ x}) := rfl
