/-- **Generic transport lemma**, extracted from the pattern already proved
twice by hand in this file (`regular_of_disjoint_extension`'s tail, from
`intro x y hxy` to `exact hreg_quot hxy''`; `regular_of_peeled_leadingCoeff`'s
tail, from `intro x y hxy` to `exact hreg_poly hxy'`). Both proofs do
EXACTLY this: given a ring equiv `e : R ≃+* S` carrying ideal `I` to `J`
and element `r` to `s`, `IsSMulRegular (R ⧸ I) r` transports to
`IsSMulRegular (S ⧸ J) s` via conjugating the injectivity statement by
the induced quotient equiv `Ideal.quotientEquiv I J e hIJ.symm`. Stated
once here, generically, as a genuine (small, mechanical) new lemma so the
12-stage assembly can invoke it directly instead of re-deriving this
`Ideal.quotientEquiv`/injectivity dance at every one of the 12 stages
(which is exactly the "bookkeeping work" the roadmap flags). -/
theorem isSMulRegular_of_ringEquiv_of_mapsTo {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (hIJ : Ideal.map (e : R →+* S) I = J)
    (r : R) (s : S) (hrs : e r = s) :
    IsSMulRegular (R ⧸ I) (Ideal.Quotient.mk I r) ↔
      IsSMulRegular (S ⧸ J) (Ideal.Quotient.mk J s) := by
  set e' : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hIJ.symm with he'_def
  have he'_apply : e' (Ideal.Quotient.mk I r) = Ideal.Quotient.mk J s := by
    rw [he'_def, Ideal.quotientEquiv_mk, hrs]
  have he'symm_apply : e'.symm (Ideal.Quotient.mk J s) = Ideal.Quotient.mk I r := by
    rw [← he'_apply, e'.symm_apply_apply]
  constructor
  · intro hreg x y hxy
    apply e'.injective
    have hxy' : (Ideal.Quotient.mk I r) • (e'.symm x) = (Ideal.Quotient.mk I r) • (e'.symm y) := by
      have hL : e' ((Ideal.Quotient.mk I r) • (e'.symm x)) =
          (Ideal.Quotient.mk J s) • x := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'_apply, e'.apply_symm_apply]
      have hR : e' ((Ideal.Quotient.mk I r) • (e'.symm y)) =
          (Ideal.Quotient.mk J s) • y := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'_apply, e'.apply_symm_apply]
      apply e'.injective
      rw [hL, hR, hxy]
    have := hreg hxy'
    rw [e'.symm.injective.eq_iff] at this
    exact this
  · intro hreg x y hxy
    apply e'.symm.injective
    have hxy' : (Ideal.Quotient.mk J s) • (e' x) = (Ideal.Quotient.mk J s) • (e' y) := by
      have hL : e'.symm ((Ideal.Quotient.mk J s) • (e' x)) =
          (Ideal.Quotient.mk I r) • x := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'symm_apply, e'.symm_apply_apply]
      have hR : e'.symm ((Ideal.Quotient.mk J s) • (e' y)) =
          (Ideal.Quotient.mk I r) • y := by
        rw [smul_eq_mul, smul_eq_mul, map_mul, he'symm_apply, e'.symm_apply_apply]
      apply e'.symm.injective
      rw [hL, hR, hxy]
    have := hreg hxy'
    rw [e'.injective.eq_iff] at this
    exact this
