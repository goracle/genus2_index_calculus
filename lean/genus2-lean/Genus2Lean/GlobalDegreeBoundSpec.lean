import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.LPairFinrankOne

set_option linter.style.header false

/-!
# The general-`k` global degree bound: `(pairNorm H A' B').natDegree ≤ 2`

This file supplies `ROADMAP-lpaircarrier-nonclosed-field.md`'s step 4, "the genuinely
new mathematical content." It is the `k`-not-necessarily-algebraically-closed
replacement for `LPairFinrankOneOrdAtFrac.lean`'s `natDegree_le_two_of_isCoprimeAtRoots`,
whose proof (`IsAlgClosed.splits c` at that file's line ~952) is exactly the dependency
this project needs to remove.

## The mathematical content (ChatGPT-assisted derivation, transcribed against this
codebase's actual objects)

For `g := toPair H A' B' ≠ 0`, write `c := pairNorm H A' B'`. Two facts, both about the
*same* divisor of `g`, get equated:

1. **(Already proved, unconditionally.)** `natDegree_pairNorm_eq_neg_ordInfOfPair`
   (`PrincipalDivisors.lean:192`): `(c).natDegree = -ordInfOfPair A' B'`. Pure `k[X]`
   degree arithmetic — no closedness, no valuation theory.

2. **(Proved in this file — §1, via the `HeightOneSpectrum`-indexed CRT/associated-graded
   machinery in §1a.)** The residue-degree-weighted sum identity
   ```
   (pairNorm H A' B').natDegree
     = ∑ v ∈ T, residueDeg v * ordAtSpec v A' B'
   ```
   for `T` any finite set of closed points containing the support of `g`'s
   factorization (obtained via the project's existing `hfinite_support` lemma,
   `LPairFinrankOne.lean:263`). This is `sum_ordAt_eq_natDegree_pairNorm`
   (`PrincipalDivisors.lean:1882`)'s shape, generalized: that theorem already proves the
   analogous statement but **only for a `Finset H.Point`-indexed sum**, and it does so
   under an explicit hypothesis (`hspec`) asserting every place with nonzero
   multiplicity is rational — i.e. it is already, silently, the rational-point special
   case of exactly what this file needs to prove in general. Removing that hypothesis
   (equivalently: summing over a `Finset (HeightOneSpectrum ...)` containing the true
   factorization support, weighted by residue degree, rather than assuming the support
   lies in a given `Finset H.Point`) is the actual mathematical content this file adds.

Combining 1 and 2 with `IsPoleBoundedAtPairSpec`'s pointwise clause — which bounds
`ordAtSpec v A' B'` termwise by the indicator `e_v` supported only at
`pointHeightOne' x₁, pointHeightOne' x₂` — gives, after summing,
`(pairNorm H A' B').natDegree ≤ 2`, matching the boxed conclusion of the ChatGPT
derivation this file transcribes. See §2 below for the assembly.

## Why this is the right replacement for `IsAlgClosed.splits`

Over `IsAlgClosed k`, `H.Point` enumerates every closed point (residue degree always
`1`), so summing over `HeightOneSpectrum` with weights collapses to summing over
`H.Point` unweighted, i.e. exactly `LPairFinrankOneOrdAtFrac.lean`'s
`c.roots.card = c.natDegree` argument via `Polynomial.Splits`. The residue-degree sum
is the literal generalization, not a different argument that happens to agree in that
case — `residueDeg v` for a rational point's `pointHeightOne' P` is `1`
(`finrank_quotient_pointIdeal`, `PrincipalDivisors.lean:572`), so §1's identity
specializes to `sum_ordAt_eq_natDegree_pairNorm`'s statement termwise.
-/

noncomputable section

open Classical

open Polynomial IsDedekindDomain

namespace HyperellipticPolynomial

open Divisor
variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-! ## §0. Residue degree of a closed point

`[κ(v) : k]` in the ChatGPT snippet's notation. Defined as the `k`-finrank of the
residue field `CoordinateRing H ⧸ v.asIdeal` — well-defined as a natural number once
that quotient is known to be a finite extension of `k`, which is where
`Module.Finite k (CoordinateRing H ⧸ v.asIdeal)` becomes an unavoidable hypothesis: for
a general Dedekind domain finite over `k[X]` there is no a priori reason every closed
point has *finite* residue degree without a Nullstellensatz-style finiteness input (this
is the direct upstream analogue of `finite_quotient_pointIdeal`,
`PrincipalDivisors.lean:583`, which only handles the rational case). For `CoordinateRing
H` — finite free of rank `2` over `k[X]`, itself of finite type over `k` — this
finiteness should hold for *every* height-one prime, not just `pointIdeal P`'s; recording
it as a clean standalone fact (rather than threading `[Module.Finite k _]` through every
downstream statement as an instance argument, matching this file's existing convention
at `finrank_quotient_prod_eq_sum_finrank`) is a prerequisite proved just below. -/

/-- **Every closed point of `CoordinateRing H` has finite residue degree over `k`.**
Proved via `CoordinateRing H`'s `k[X]`-basis (`AdjoinRoot.powerBasisAux'`, since
`CoordinateRing H` is `AdjoinRoot (X² - C H.f)`), decomposing the quotient by `v.asIdeal`
into a finite product of PID-quotient factors via `Ideal.quotientEquivPiSpan`, each of
which is `k`-finite by Mathlib's own `FiniteDimensional`-over-a-PID-quotient instance. -/
theorem finite_quotient_asIdeal [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    Module.Finite k (CoordinateRing H ⧸ v.asIdeal) := by
  haveI : IsDomain (CoordinateRing H) := IsDedekindDomain.toIsDomain
  -- `CoordinateRing H = AdjoinRoot (X² - C H.f)`, a monic quadratic, so `AdjoinRoot.
  -- powerBasisAux'` gives a `k[X]`-basis indexed by `Fin (X² - C H.f).natDegree`
  -- (same construction `WeierstrassCurve.Affine.CoordinateRing.basis` uses for the
  -- analogous genus-1 case). No reindexing to `Fin 2` needed — `Ideal.quotientEquivPiSpan`
  -- only needs `Finite ι`, which `Fin (X² - C H.f).natDegree` already is.
  have hmonic : (X ^ 2 - C H.f : (k[X])[X]).Monic :=
    Polynomial.monic_X_pow_sub_C H.f two_ne_zero
  set b : Module.Basis (Fin (X ^ 2 - C H.f : (k[X])[X]).natDegree) k[X] (CoordinateRing H) :=
    AdjoinRoot.powerBasisAux' hmonic with hb_def
  -- `Ideal.quotientEquivPiSpan` decomposes the quotient by `v.asIdeal` (nonzero, from
  -- `HeightOneSpectrum`'s own `ne_bot` field) into a finite product of `k[X] ⧸ span
  -- {smithCoeffs ...}` factors.
  have hv_ne : v.asIdeal ≠ ⊥ := v.ne_bot
  set e := Ideal.quotientEquivPiSpan (R := k[X]) (S := CoordinateRing H) v.asIdeal b hv_ne
    with he_def
  -- Each factor is `k`-finite-dimensional: `k[X]` is a PID, so this is exactly Mathlib's
  -- own `instFiniteDimensionalQuotientPolynomialIdealSpanSingletonSetSmithCoeffs`
  -- instance (`FiniteDimensional` is an abbreviation for `Module.Finite` over a field).
  haveI hfactor : ∀ i, Module.Finite k
      (k[X] ⧸ Ideal.span ({Ideal.smithCoeffs b v.asIdeal hv_ne i} : Set k[X])) := by
    intro i
    infer_instance
  haveI hpi : Module.Finite k
      (∀ i : Fin (X ^ 2 - C H.f : (k[X])[X]).natDegree,
        k[X] ⧸ Ideal.span ({Ideal.smithCoeffs b v.asIdeal hv_ne i} : Set k[X])) :=
    Module.Finite.pi
  -- `e` is `k[X]`-linear; `Module.Finite.equiv` needs an equivalence linear over the ring
  -- the finiteness is stated for (`k`), so restrict scalars along `k → k[X]` first — the
  -- same `IsScalarTower.of_algebraMap_eq (fun _ => rfl)` idiom this project already uses
  -- at `RiemannRochGenus2.lean:428` for the same `k`/`k[X]`/`CoordinateRing H` tower.
  haveI hst : IsScalarTower k (k[X]) (CoordinateRing H) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Module.Finite.equiv (LinearEquiv.restrictScalars k e).symm

noncomputable instance instFiniteQuotientAsIdeal [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    Module.Finite k (CoordinateRing H ⧸ v.asIdeal) :=
  finite_quotient_asIdeal v

/-- **Residue degree** `[κ(v) : k]` of a closed point `v`, as a natural number. Reduces
to `1` at rational points (§0.1 below) and is the weight `[κ(v):k]` in the ChatGPT
snippet's norm identity `deg N(g) = ∑_v [κ(v):k] ord_v(g)`. -/
def residueDeg [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) : ℕ :=
  Module.finrank k (CoordinateRing H ⧸ v.asIdeal)

/-- **Residue degree is `1` at every rational point.** Direct consequence of
`finrank_quotient_pointIdeal` (`PrincipalDivisors.lean:572`): `pointHeightOne' P`'s
underlying ideal is `pointIdeal P` by construction, whose quotient is `k`-isomorphic to
`k` itself. This is the fact making §1's identity specialize to
`sum_ordAt_eq_natDegree_pairNorm`'s rational-only statement when every place in the
support happens to be rational, per this file's header discussion. -/
theorem residueDeg_pointHeightOne' [IsDedekindDomain (CoordinateRing H)] (P : H.Point) :
    residueDeg (pointHeightOne' P) = 1 := by
  unfold residueDeg
  exact finrank_quotient_pointIdeal P

/-- **`ordAtSpec` vanishes wherever the `Associates.count` multiplicity is zero.** The
easy direction of `ordAtSpec_eq_count` (never separately stated, since `ordAt_eq_count`'s
`PrincipalDivisors.lean` analogue only handles rational points) — needed to convert
`hfinite_support`'s `count ≠ 0 → v ∈ Tset` into the `hsupp : v ∉ T → ordAtSpec v A B = 0`
shape `natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec` below actually asks for. Same
`intValuation_apply`/`intValuationDef_if_neg` unfolding as `ordAtSpec_nonneg`, specialized
to `n = 0`, where `WithZero.exp (-(0:ℤ)) = 1` makes the valuation a unit, i.e. `ordAtSpec`
is `0` by the same computation as `ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec`'s
`hv1`. -/
theorem ordAtSpec_eq_zero_of_count_eq_zero [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (A B : k[X])
    (hne : toPair H A B ≠ 0)
    (hcount : (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors = 0) :
    ordAtSpec v A B = 0 := by
  unfold ordAtSpec
  rw [if_neg hne]
  have hval : v.intValuation (toPair H A B) = WithZero.exp (-(0 : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_apply,
        IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg _ hne]
    rw [hcount]
    try rfl
  rw [hval]
  have hlog_exp : WithZero.log (WithZero.exp (-(0 : ℤ))) = -(0 : ℤ) :=
    WithZero.exp_injective (WithZero.exp_log WithZero.exp_ne_zero)
  rw [hlog_exp]
  ring

/-- **A finite support `T` for `ordAtSpec`, no rationality restriction.** The
`ordAtSpec`-native analogue of `LPairFinrankOne.lean`'s `exists_finite_support_of_hspec`,
built the same way but without that lemma's `hspec` rationality hypothesis (unneeded here
since `hfinite_support` already ranges over all of `HeightOneSpectrum`, not just points
reachable via `pointIdeal`). Wraps `hfinite_support` plus
`ordAtSpec_eq_zero_of_count_eq_zero`'s contrapositive. -/
theorem exists_finite_support_ordAtSpec [IsDedekindDomain (CoordinateRing H)]
    (A B : k[X]) (hAB : ¬ (A = 0 ∧ B = 0)) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)),
      ∀ v, v ∉ T → ordAtSpec v A B = 0 := by
  have hne : toPair H A B ≠ 0 := by rw [Ne, toPair_eq_zero_iff]; exact hAB
  have hIne : Ideal.span ({toPair H A B} : Set (CoordinateRing H)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hne
  obtain ⟨T, hT⟩ := hfinite_support (H := H)
    (Ideal.span ({toPair H A B} : Set (CoordinateRing H))) hIne
  refine ⟨T, fun v hvT => ?_⟩
  by_contra hne'
  apply hvT
  apply hT
  intro hcount
  exact hne' (ordAtSpec_eq_zero_of_count_eq_zero v A B hne hcount)

/-! ## §1. The residue-degree-weighted norm identity

The genuinely new content this file adds: `sum_ordAt_eq_natDegree_pairNorm`
(`PrincipalDivisors.lean:1882`)'s statement, with the `Finset H.Point`-indexed sum (and
its accompanying rationality hypothesis `hspec`) replaced by a residue-degree-weighted
sum over the *entire* `HeightOneSpectrum`. -/

/-- **`ordAtSpec` is nonnegative for a genuine ring element.** `A, B ∈ k[X]` gives
`toPair H A B ∈ CoordinateRing H` (not a fraction), so this is the `ordAtSpec` analogue
of `ordAt_nonneg` (`PrincipalDivisors.lean:523`, itself proved via `ordAt_eq_count`'s
`Associates.count`-is-a-`ℕ` observation) — needed here to safely convert the `ℤ`-valued
`ordAtSpec` in the norm identity's statement to the `ℕ`-valued multiplicity §1's proof
actually sums (step 3's `finrank k (R/𝔪^n) = residueDeg v * n`, with
`n = (ordAtSpec v A B).toNat`, only makes sense once the cast back from `ℤ` is known
lossless). Same proof shape as `ordAt_nonneg`, transcribed to the unrestricted `v`. -/
-- **Same unconfirmed-against-a-live-goal caveat as `ordAt_eq_count`
-- (`PrincipalDivisors.lean:471–520`)**: the `intValuation_apply`/`intValuationDef_if_neg`
-- unfolding and the `WithZero.exp`/`log` round-trip below are copied verbatim from that
-- theorem's proof, which is itself flagged there as "PLAUSIBLE, not checked against a
-- live goal state." Not re-verified here independently — inherits that theorem's status.
theorem ordAtSpec_nonneg [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (A B : k[X])
    (hne : toPair H A B ≠ 0) :
    0 ≤ ordAtSpec v A B := by
  unfold ordAtSpec
  rw [if_neg hne]
  -- `WithZero.log ∘ intValuation` lands in `-ℕ` (an `Associates.count`, negated by
  -- `ordAtSpec`'s own sign convention) exactly as in `ordAt_eq_count`
  -- (`PrincipalDivisors.lean:485`) — same unfolding, transcribed to a general `v`
  -- instead of `pointHeightOne P h_bot`.
  set n : ℕ := (Associates.mk v.asIdeal).count
    (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors
  have hval : v.intValuation (toPair H A B) = WithZero.exp (-(n : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_apply,
        IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg _ hne]
    try rfl
  rw [hval]
  have hlog_exp : WithZero.log (WithZero.exp (-(n : ℤ))) = -(n : ℤ) :=
    WithZero.exp_injective (WithZero.exp_log WithZero.exp_ne_zero)
  rw [hlog_exp]
  omega

/-- **`ordAtSpec` equals the `Associates.count` multiplicity, at an arbitrary closed point.**
The equality version of `ordAtSpec_nonneg` — same unfolding, stopped one step earlier (before
`omega` discards the equation for the inequality). This is the `HeightOneSpectrum`-native
analogue of `PrincipalDivisors.lean`'s `ordAt_eq_count`, with `pointHeightOne P h_bot` replaced
by a general `v` (no `h_bot` side condition needed, since `HeightOneSpectrum` already carries
`ne_bot`). -/
theorem ordAtSpec_eq_count [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (A B : k[X])
    (hne : toPair H A B ≠ 0) :
    ordAtSpec v A B =
      ((Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors : ℤ) := by
  unfold ordAtSpec
  rw [if_neg hne]
  set n : ℕ := (Associates.mk v.asIdeal).count
    (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors with hn_def
  have hval : v.intValuation (toPair H A B) = WithZero.exp (-(n : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_apply,
        IsDedekindDomain.HeightOneSpectrum.intValuationDef_if_neg _ hne]
    try rfl
  rw [hval]
  have hlog_exp : WithZero.log (WithZero.exp (-(n : ℤ))) = -(n : ℤ) :=
    WithZero.exp_injective (WithZero.exp_log WithZero.exp_ne_zero)
  rw [hlog_exp, neg_neg]

/-! ## §1a. `HeightOneSpectrum`-indexed CRT + associated-graded dimension count

Direct reindexing of `PrincipalDivisors.lean`'s §4.2 scaffold (`pointIdeal_pow_pairwise_coprime`
through `finrank_quotient_pointIdeal_pow_and_finite`, all fully proved there — no `sorry`),
replacing every occurrence of `pointIdeal P` (`P : H.Point`) with `v.asIdeal`
(`v : HeightOneSpectrum (CoordinateRing H)`). None of that argument is rational-point-specific:
`pointIdeal_isMaximal`/`pointIdeal_ne_bot` are used only via the generic `HeightOneSpectrum`
API (`v.isPrime`/`v.ne_bot`, both already fields of the structure, giving maximality via
Dedekind-domain dimension-1), and the associated-graded computation
(`pointIdeal_pow_succ_covBy` through `map_mkQ_pointIdeal_pow_equiv`) only used primality +
`Ideal.eq_prime_pow_of_succ_lt_of_le`-style unique factorization, again generic. The one place
the rational case used something point-specific was §4.3 (`finrank_quotient_pointIdeal = 1`,
via `evalAtPointAlg`'s surjectivity onto `k`) — here that is simply not needed: the induction
below tracks `residueDeg v` instead of the constant `1` throughout, so no residue-field
isomorphism to `k` itself is required. -/

/-- `v.asIdeal` is maximal, for any `v : HeightOneSpectrum (CoordinateRing H)` — a Dedekind
domain has Krull dimension `1`, so every nonzero prime is maximal. Packaged as its own lemma
since `HeightOneSpectrum` only bundles primality + `ne_bot` directly, not maximality.
Mathlib supplies this as the instance `IsDedekindDomain.HeightOneSpectrum.isMaximal`
(confirmed: `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`), so `inferInstance` finds it
directly — more robust than guessing whether `v.isMaximal` dot-notation resolves to the
instance or needs an explicit `haveI`/`@` first. -/
theorem heightOneSpectrum_isMaximal [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    v.asIdeal.IsMaximal :=
  inferInstance

/-- **`HeightOneSpectrum`-indexed analogue of `pointIdeal_pow_pairwise_coprime`.** Distinct
closed points give coprime prime-power ideals. Same proof as the rational case, verbatim,
with `pointIdeal P`/`pointIdeal Q` replaced by `v.asIdeal`/`w.asIdeal` and
`pointIdeal_ne_of_ne` replaced by the direct `HeightOneSpectrum.ext_iff`-contrapositive
(`v ≠ w → v.asIdeal ≠ w.asIdeal`). -/
theorem heightOneSpectrum_pow_pairwise_coprime [IsDedekindDomain (CoordinateRing H)]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))) (A B : k[X]) :
    ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      IsCoprime (v.asIdeal ^ (ordAtSpec v A B).toNat) (w.asIdeal ^ (ordAtSpec w A B).toNat) := by
  intro v _ w _ hvw
  have hne : v.asIdeal ≠ w.asIdeal := fun h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h)
  have hsup : v.asIdeal ⊔ w.asIdeal = ⊤ := by
    by_contra hlt
    have hle : v.asIdeal ≤ v.asIdeal ⊔ w.asIdeal := le_sup_left
    have hne_top : v.asIdeal ⊔ w.asIdeal ≠ ⊤ := hlt
    have heq1 : v.asIdeal = v.asIdeal ⊔ w.asIdeal :=
      (heightOneSpectrum_isMaximal v).eq_of_le hne_top hle
    have hle2 : w.asIdeal ≤ v.asIdeal ⊔ w.asIdeal := le_sup_right
    rw [← heq1] at hle2
    have heq2 : w.asIdeal = v.asIdeal :=
      (heightOneSpectrum_isMaximal w).eq_of_le (heightOneSpectrum_isMaximal v).ne_top hle2
    exact hne heq2.symm
  exact (Ideal.isCoprime_iff_sup_eq.mpr hsup).pow

/-- **`HeightOneSpectrum`-indexed analogue of `crt_equiv_prod_pointIdeal_pow`.** CRT for the
factored ideal `∏ v ∈ S, v.asIdeal ^ nV`, over an arbitrary finite set `S` of closed points
(no rationality restriction). Same construction as the rational case, reindexed. -/
noncomputable def heightOneSpectrum_crt_equiv_prod
    [IsDedekindDomain (CoordinateRing H)]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))) (A B : k[X]) :
    (CoordinateRing H ⧸ ∏ v ∈ S, v.asIdeal ^ (ordAtSpec v A B).toNat) ≃+*
      (Π v : S, CoordinateRing H ⧸ v.1.asIdeal ^ (ordAtSpec v.1 A B).toNat) := by
  let I : S → Ideal (CoordinateRing H) := fun v => v.1.asIdeal ^ (ordAtSpec v.1 A B).toNat
  have hcoprime :
      ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        IsCoprime (v.asIdeal ^ (ordAtSpec v A B).toNat) (w.asIdeal ^ (ordAtSpec w A B).toNat) :=
    heightOneSpectrum_pow_pairwise_coprime S A B
  have h_pairwise : Pairwise (Function.onFun IsCoprime I) := by
    intro v w hvw
    simpa [I, Function.onFun] using
      hcoprime v.1 v.2 w.1 w.2 (by intro h; exact hvw (Subtype.ext h))
  have h_pairwise_univ :
      Set.Pairwise (↑(Finset.univ : Finset S) : Set S) (Function.onFun IsCoprime I) := by
    rw [Finset.coe_univ, Set.pairwise_univ]
    exact h_pairwise
  have heq_sub : (∏ v : S, I v) = ⨅ v : S, I v := by
    simpa using
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := (Finset.univ : Finset S)) (J := I) h_pairwise_univ)
  have heq : (∏ v ∈ S, v.asIdeal ^ (ordAtSpec v A B).toNat) = ⨅ v : S, I v := by
    rw [← Finset.prod_attach]
    simpa [I] using heq_sub
  refine
    (Ideal.quotientEquiv _ _ (RingEquiv.refl _) ?_).trans
      (Ideal.quotientInfRingEquivPiQuotient I h_pairwise)
  · simpa [I] using heq.symm

/-- How `heightOneSpectrum_crt_equiv_prod` acts on classes of the form `Ideal.Quotient.mk _ x`:
componentwise, it is again `Ideal.Quotient.mk _ x` (into the corresponding factor).
`HeightOneSpectrum`-indexed analogue of `crt_equiv_prod_pointIdeal_pow_mk`, same proof. -/
theorem heightOneSpectrum_crt_equiv_prod_mk
    [IsDedekindDomain (CoordinateRing H)]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))) (A B : k[X])
    (x : CoordinateRing H) :
    heightOneSpectrum_crt_equiv_prod S A B (Ideal.Quotient.mk _ x) =
      fun v : S => (Ideal.Quotient.mk (v.1.asIdeal ^ (ordAtSpec v.1 A B).toNat) x :
        CoordinateRing H ⧸ v.1.asIdeal ^ (ordAtSpec v.1 A B).toNat) := by
  unfold heightOneSpectrum_crt_equiv_prod
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk, RingEquiv.refl_apply]
  exact Ideal.quotientInfToPiQuotient_mk _ x

/-- `heightOneSpectrum_crt_equiv_prod`, repackaged as a `k`-`AlgEquiv`, exactly as
`crt_algEquiv_prod_pointIdeal_pow` repackages `crt_equiv_prod_pointIdeal_pow`. Needed because
`LinearEquiv.finrank_eq` requires a `k`-linear map, and a bare `RingEquiv` (`≃+*`) carries no
`k`-linearity data on its own — only `AlgEquiv.toLinearEquiv` supplies that. -/
noncomputable def heightOneSpectrum_crt_algEquiv_prod
    [IsDedekindDomain (CoordinateRing H)]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))) (A B : k[X]) :
    (CoordinateRing H ⧸ ∏ v ∈ S, v.asIdeal ^ (ordAtSpec v A B).toNat) ≃ₐ[k]
      (Π v : S, CoordinateRing H ⧸ v.1.asIdeal ^ (ordAtSpec v.1 A B).toNat) :=
  AlgEquiv.ofRingEquiv (f := heightOneSpectrum_crt_equiv_prod S A B) (fun c => by
    have hlhs : algebraMap k
        (CoordinateRing H ⧸ ∏ v ∈ S, v.asIdeal ^ (ordAtSpec v A B).toNat) c =
        Ideal.Quotient.mk _ (algebraMap k (CoordinateRing H) c) := rfl
    rw [hlhs, heightOneSpectrum_crt_equiv_prod_mk S A B (algebraMap k (CoordinateRing H) c)]
    rfl)

/-- The ideal `v.asIdeal ^ (i + 1)` is covered by `v.asIdeal ^ i`. `HeightOneSpectrum`-indexed
analogue of `pointIdeal_pow_succ_covBy`, same proof. -/
theorem heightOneSpectrum_pow_succ_covBy [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (i : ℕ) :
    v.asIdeal ^ (i + 1) ⋖ v.asIdeal ^ i := by
  haveI : v.asIdeal.IsPrime := v.isPrime
  have hne_bot : v.asIdeal ≠ ⊥ := v.ne_bot
  refine ⟨Ideal.pow_succ_lt_pow hne_bot i, ?_⟩
  intro J hlt1 hlt2
  have hle : J ≤ v.asIdeal ^ i := hlt2.le
  have heq := Ideal.eq_prime_pow_of_succ_lt_of_le hne_bot hlt1 hle
  exact absurd heq hlt2.ne

/-- The associated-graded piece `v.asIdeal ^ i ⧸ v.asIdeal ^ (i+1)` is a simple
`CoordinateRing H`-module. `HeightOneSpectrum`-indexed analogue of
`isSimpleModule_map_mkQ_pointIdeal_pow`, same proof. -/
theorem heightOneSpectrum_isSimpleModule_map_mkQ_pow [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (i : ℕ) :
    IsSimpleModule (CoordinateRing H)
      (Submodule.map (Submodule.mkQ (v.asIdeal ^ (i + 1))) (v.asIdeal ^ i)) := by
  have hle : v.asIdeal ^ (i + 1) ≤ v.asIdeal ^ i := (heightOneSpectrum_pow_succ_covBy v i).le
  set e := Submodule.comapMkQRelIso (R := CoordinateRing H) (v.asIdeal ^ (i + 1)) with he_def
  set N : Submodule (CoordinateRing H) (CoordinateRing H ⧸ v.asIdeal ^ (i + 1)) :=
    Submodule.map (Submodule.mkQ (v.asIdeal ^ (i + 1))) (v.asIdeal ^ i) with hN_def
  have hcorr : e N = ⟨v.asIdeal ^ i, hle⟩ := by
    apply Subtype.ext
    show Submodule.comap (Submodule.mkQ (v.asIdeal ^ (i + 1))) N = v.asIdeal ^ i
    rw [hN_def, Submodule.comap_map_mkQ]
    simpa using sup_eq_left.mpr hle
  rw [isSimpleModule_iff_isAtom]
  have hatom_in_Ici : IsAtom (⟨v.asIdeal ^ i, hle⟩ : Set.Ici (v.asIdeal ^ (i + 1))) := by
    rw [Set.Ici.isAtom_iff]
    exact heightOneSpectrum_pow_succ_covBy v i
  rw [← hcorr] at hatom_in_Ici
  exact (OrderIso.isAtom_iff e N).mp hatom_in_Ici

/-- The annihilator of the associated-graded piece is `v.asIdeal` itself. `HeightOneSpectrum`-
indexed analogue of `annihilator_map_mkQ_pointIdeal_pow`, same proof. -/
theorem heightOneSpectrum_annihilator_map_mkQ_pow [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (i : ℕ) :
    Module.annihilator (CoordinateRing H)
      (Submodule.map (Submodule.mkQ (v.asIdeal ^ (i + 1))) (v.asIdeal ^ i)) = v.asIdeal := by
  set N : Submodule (CoordinateRing H) (CoordinateRing H ⧸ v.asIdeal ^ (i + 1)) :=
    Submodule.map (Submodule.mkQ (v.asIdeal ^ (i + 1))) (v.asIdeal ^ i) with hN_def
  have hle_ann : v.asIdeal ≤ Module.annihilator (CoordinateRing H) N := by
    intro r hr
    rw [Module.mem_annihilator]
    rintro ⟨x, hx⟩
    rw [hN_def, Submodule.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    apply Subtype.ext
    show r • (Submodule.mkQ (v.asIdeal ^ (i + 1))) y = 0
    rw [← map_smul]
    show Submodule.Quotient.mk (r • y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hmem : r • y ∈ v.asIdeal ^ (i + 1) := by
      rw [smul_eq_mul, pow_succ']
      exact Ideal.mul_mem_mul hr hy
    exact hmem
  haveI := heightOneSpectrum_isSimpleModule_map_mkQ_pow v i
  haveI hann_max : (Module.annihilator (CoordinateRing H) N).IsMaximal :=
    IsSimpleModule.annihilator_isMaximal
  exact ((heightOneSpectrum_isMaximal v).eq_of_le hann_max.ne_top hle_ann).symm

/-- The associated-graded piece is `k`-linearly equivalent to the residue field
`CoordinateRing H ⧸ v.asIdeal`. `HeightOneSpectrum`-indexed analogue of
`map_mkQ_pointIdeal_pow_equiv`, same proof — with no collapse to `finrank = 1`, since the
residue field here need not be `k` itself. -/
theorem heightOneSpectrum_map_mkQ_pow_equiv [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (i : ℕ) :
    Nonempty ((Submodule.map (Submodule.mkQ (v.asIdeal ^ (i + 1))) (v.asIdeal ^ i) :
        Submodule (CoordinateRing H) (CoordinateRing H ⧸ v.asIdeal ^ (i + 1))) ≃ₗ[k]
      CoordinateRing H ⧸ v.asIdeal) := by
  haveI := heightOneSpectrum_isSimpleModule_map_mkQ_pow v i
  obtain ⟨J, hJmax, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (heightOneSpectrum_isSimpleModule_map_mkQ_pow v i)
  have hann := heightOneSpectrum_annihilator_map_mkQ_pow v i
  have hJ_eq : J = v.asIdeal := by
    have h1 : Module.annihilator (CoordinateRing H)
        (Submodule.map (Submodule.mkQ (v.asIdeal ^ (i + 1))) (v.asIdeal ^ i)) =
        Module.annihilator (CoordinateRing H) (CoordinateRing H ⧸ J) :=
      LinearEquiv.annihilator_eq e
    rw [hann, Ideal.annihilator_quotient] at h1
    exact h1.symm
  exact ⟨(e.trans (Submodule.quotEquivOfEq J v.asIdeal hJ_eq)).restrictScalars k⟩

/-- **`HeightOneSpectrum`-indexed analogue of `finrank_quotient_pointIdeal_pow_and_finite`.**
`Module.finrank k (CoordinateRing H ⧸ v.asIdeal ^ n) = residueDeg v * n`, together with
finiteness. Same induction as the rational case, with the constant `1` (rational residue
degree) replaced throughout by `residueDeg v`. -/
theorem heightOneSpectrum_finrank_quotient_pow_and_finite
    [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (n : ℕ) :
    Module.finrank k (CoordinateRing H ⧸ v.asIdeal ^ n) = residueDeg v * n ∧
      Module.Finite k (CoordinateRing H ⧸ v.asIdeal ^ n) := by
  induction n with
  | zero =>
    haveI hsub : Subsingleton (CoordinateRing H ⧸ (⊤ : Ideal (CoordinateRing H))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [pow_zero, Ideal.one_eq_top, mul_zero]
    refine ⟨Module.finrank_zero_of_subsingleton, ?_⟩
    infer_instance
  | succ i ih =>
    obtain ⟨ihfin, ihmod⟩ := ih
    haveI := ihmod
    set Mi1 : Ideal (CoordinateRing H) := v.asIdeal ^ (i + 1) with hMi1_def
    set N : Submodule (CoordinateRing H) (CoordinateRing H ⧸ Mi1) :=
      Submodule.map (Submodule.mkQ Mi1) (v.asIdeal ^ i) with hN_def
    set Nk : Submodule k (CoordinateRing H ⧸ Mi1) := N.restrictScalars k with hNk_def
    obtain ⟨eNk⟩ := heightOneSpectrum_map_mkQ_pow_equiv v i
    have heNk : Nk ≃ₗ[k] CoordinateRing H ⧸ v.asIdeal := by
      have hid : Nk ≃ₗ[k] N :=
        { toFun := fun x => ⟨x.1, x.2⟩
          invFun := fun x => ⟨x.1, x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact hid.trans eNk
    have hNk_finrank : Module.finrank k Nk = residueDeg v := by
      rw [LinearEquiv.finrank_eq heNk]; rfl
    haveI hNk_finite : Module.Finite k Nk := Module.Finite.equiv heNk.symm
    have hquot : ((CoordinateRing H ⧸ Mi1) ⧸ Nk) ≃ₗ[k] CoordinateRing H ⧸ v.asIdeal ^ i := by
      have hle : Mi1 ≤ v.asIdeal ^ i := (heightOneSpectrum_pow_succ_covBy v i).le
      have hstep1 : ((CoordinateRing H ⧸ Mi1) ⧸ Nk) ≃ₗ[k] ((CoordinateRing H ⧸ Mi1) ⧸ N) :=
        Submodule.Quotient.restrictScalarsEquiv k N
      have hstep2 : ((CoordinateRing H ⧸ Mi1) ⧸ N) ≃ₗ[k] CoordinateRing H ⧸ v.asIdeal ^ i :=
        (Submodule.quotientQuotientEquivQuotient Mi1 (v.asIdeal ^ i) hle).restrictScalars k
      exact hstep1.trans hstep2
    have hquot_finrank : Module.finrank k ((CoordinateRing H ⧸ Mi1) ⧸ Nk) = residueDeg v * i :=
      (LinearEquiv.finrank_eq hquot).trans ihfin
    haveI hquot_finite : Module.Finite k ((CoordinateRing H ⧸ Mi1) ⧸ Nk) :=
      Module.Finite.equiv hquot.symm
    haveI hMi1_finite : Module.Finite k (CoordinateRing H ⧸ Mi1) :=
      Module.Finite.of_exact (LinearMap.exact_subtype_mkQ Nk) Nk.mkQ_surjective
    refine ⟨?_, hMi1_finite⟩
    have hadd := Submodule.finrank_quotient_add_finrank (R := k) Nk
    rw [hquot_finrank, hNk_finrank] at hadd
    have : residueDeg v * (i + 1) = residueDeg v * i + residueDeg v := by ring
    omega

/-- Thin wrapper: `Module.finrank k (CoordinateRing H ⧸ v.asIdeal ^ n) = residueDeg v * n`. -/
theorem heightOneSpectrum_finrank_quotient_pow [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (n : ℕ) :
    Module.finrank k (CoordinateRing H ⧸ v.asIdeal ^ n) = residueDeg v * n :=
  (heightOneSpectrum_finrank_quotient_pow_and_finite v n).1

instance heightOneSpectrum_finite_quotient_pow [IsDedekindDomain (CoordinateRing H)]
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (n : ℕ) :
    Module.Finite k (CoordinateRing H ⧸ v.asIdeal ^ n) :=
  (heightOneSpectrum_finrank_quotient_pow_and_finite v n).2

/-- **`HeightOneSpectrum`-indexed analogue of `span_toPair_eq_prod_pointIdeal_pow`.** The
factorization `Ideal.span {toPair H A B} = ∏ v ∈ T, v.asIdeal ^ (ordAtSpec v A B).toNat`, for
`T` any finite set containing the true factorization support — no `hspec` rationality
hypothesis needed, since `T` is not assumed a priori to come from `H.Point`. Proof: the same
`Ideal.finprod_heightOneSpectrum_factorization` unique-factorization argument as the rational
case, but simpler — no reindexing through `pointHeightOne'`/`S.image` is needed, since `T`
already ranges directly over `HeightOneSpectrum`. -/
theorem span_toPair_eq_prod_heightOneSpectrum_pow [IsDedekindDomain (CoordinateRing H)]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))) (A B : k[X])
    (hAB : ¬(A = 0 ∧ B = 0)) (hsupp : ∀ v, v ∉ T → ordAtSpec v A B = 0) :
    Ideal.span ({toPair H A B} : Set (CoordinateRing H)) =
      ∏ v ∈ T, v.asIdeal ^ (ordAtSpec v A B).toNat := by
  classical
  set g : CoordinateRing H := toPair H A B with hg_def
  set I : Ideal (CoordinateRing H) := Ideal.span ({g} : Set (CoordinateRing H)) with hI_def
  have hgne : g ≠ 0 := by rw [hg_def, Ne, toPair_eq_zero_iff]; exact hAB
  have hIne : I ≠ 0 := by
    rw [hI_def, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hgne
  have hsub : Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) => v.maxPowDividing I)
      ⊆ (T : Set (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))) := by
    intro v hv
    by_contra hvT
    apply hv
    show v.maxPowDividing I = 1
    have hordv : ordAtSpec v A B = 0 := hsupp v hvT
    have hcount0 : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      have hcount_eq : ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) = 0 := by
        rw [← ordAtSpec_eq_count v A B hgne]; exact hordv
      exact_mod_cast hcount_eq
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, hcount0, pow_zero]
  have hfactor : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      v.maxPowDividing I = I :=
    Ideal.finprod_heightOneSpectrum_factorization hIne
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub] at hfactor
  rw [← hfactor]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  show v.maxPowDividing I = v.asIdeal ^ (ordAtSpec v A B).toNat
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  congr 1
  have hcount_eq : ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) =
      ordAtSpec v A B := (ordAtSpec_eq_count v A B hgne).symm
  omega

/-- **`HeightOneSpectrum`-indexed analogue of `finrank_quotient_prod_eq_sum_finrank`.** CRT
finrank additivity across the factored ideal, weighted by `residueDeg`. Unlike the rational
case, no `Module.Finite` hypothesis needs to be threaded through: `heightOneSpectrum_finite_
quotient_pow` supplies it as an instance directly (this is exactly the simplification the §1
docstring above predicted once `finrank_quotient_pointIdeal_pow`'s generalization was
available). -/
theorem heightOneSpectrum_finrank_quotient_prod_eq_sum
    [IsDedekindDomain (CoordinateRing H)]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H))) (A B : k[X]) :
    Module.finrank k (CoordinateRing H ⧸ ∏ v ∈ S, v.asIdeal ^ (ordAtSpec v A B).toNat) =
      ∑ v : S, residueDeg v.1 * (ordAtSpec v.1 A B).toNat := by
  rw [LinearEquiv.finrank_eq (heightOneSpectrum_crt_algEquiv_prod S A B).toLinearEquiv]
  rw [Module.finrank_pi_fintype k]
  exact Finset.sum_congr rfl (fun v _ => heightOneSpectrum_finrank_quotient_pow v.1 _)

/-- **The residue-degree-weighted norm identity.** `(pairNorm H A B).natDegree` equals
the finite sum, over a `Finset T` of closed points containing the entire support of
`toPair H A B`'s factorization (rational or not), of `residueDeg v * (ordAtSpec v A
B).toNat` — the direct Lean transcription of the ChatGPT derivation's `deg N(g) = ∑_v
[κ(v):k] ord_v(g)`.

**Stated with an explicit `Finset T` and a `hsupp`-style containment hypothesis, mirroring
`sum_ordAt_eq_natDegree_pairNorm`'s existing shape exactly**, rather than with `∑ᶠ`
(finsum) as an earlier draft of this file had it. This is a deliberate correction, not a
stylistic choice: `hfinite_support` (`LPairFinrankOne.lean:263`) already supplies exactly
such a `T` unconditionally (no rationality restriction, no `hspec` needed — it is the
`HeightOneSpectrum`-native finiteness fact, not `exists_finite_support_of_hspec`'s
`H.Point`-translated corollary of it), so every caller of this theorem can obtain `T` for
free via `hfinite_support (Ideal.span {toPair H A B}) hne` rather than being asked to
discharge a `finsum`-support side condition themselves. Matching the codebase's own
established idiom (this is the only place in the project a `Finset`-of-`HeightOneSpectrum`
sum, rather than a `Finset H.Point` one, is needed) also means no new, unverified `finsum`
lemma names (`finsum_le_finsum`, `finsum_mem_finset`, etc. — none confirmed against a live
goal, and this project has no prior use of `finsum` anywhere to crib from) are required
downstream, in `natDegree_le_two_of_isPoleBoundedAtPairSpec`'s summing step.

**Proof, matching `sum_ordAt_eq_natDegree_pairNorm`'s existing template exactly**, with the
rationality restriction on the support dropped, and now fully proved (§1a above supplies the
`HeightOneSpectrum`-indexed CRT/associated-graded machinery this needed):

1. `Ideal.span {toPair H A B} = ∏ v ∈ T, v.asIdeal ^ (ordAtSpec v A B).toNat` for `T` as
   above — `span_toPair_eq_prod_heightOneSpectrum_pow` (§1a), the `HeightOneSpectrum`-indexed
   analogue of `span_toPair_eq_prod_pointIdeal_pow` (`PrincipalDivisors.lean:716`), with
   `pointIdeal P` replaced by the general `v.asIdeal` and no `hspec`-style rationality
   restriction needed, since `T` is any finite set containing the true factorization support
   rather than assumed a priori to land inside a given `Finset H.Point`.
2. CRT gives `CoordinateRing H ⧸ ∏ v ∈ T, v.asIdeal ^ nV ≃+* Π v : T, CoordinateRing H
   ⧸ v.asIdeal ^ nV` — `heightOneSpectrum_crt_equiv_prod` (§1a), the same
   `crt_equiv_prod_pointIdeal_pow` (`PrincipalDivisors.lean:836`) argument, reindexed from
   `S : Finset H.Point` to `T : Finset (HeightOneSpectrum (CoordinateRing H))`; nothing in
   the CRT step used rationality, only pairwise-coprimality of distinct maximal ideals,
   which holds at every pair of distinct height-one primes regardless of residue field.
3. `finrank k (CoordinateRing H ⧸ v.asIdeal ^ n) = residueDeg v * n` for each factor —
   `heightOneSpectrum_finrank_quotient_pow` (§1a), the direct generalization of
   `finrank_quotient_pointIdeal_pow` (`PrincipalDivisors.lean:1067`, itself fully proved,
   no rationality dependence): the associated-graded filtration argument
   `𝔪^i/𝔪^{i+1} ≅ R/𝔪` as `R/𝔪`-modules is agnostic to `R/𝔪`'s `k`-dimension, so summing
   `finrank_k` (rather than `finrank_{R/𝔪}`) across the filtration picks up a factor of
   `residueDeg v = finrank k (R/𝔪)` at each of the `n` graded pieces, giving `n * residueDeg
   v` total instead of the rational case's `n * 1 = n`.
4. Assemble via `finrank_quotient_span_eq_natDegree_pairNorm`
   (`PrincipalDivisors.lean:1836`, already fully proved, no rationality dependence at
   all) exactly as `sum_ordAt_eq_natDegree_pairNorm` does. -/
theorem natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec
    [IsDedekindDomain (CoordinateRing H)] (A B : k[X]) (hAB : ¬(A = 0 ∧ B = 0))
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)))
    (hsupp : ∀ v, v ∉ T → ordAtSpec v A B = 0) :
    ((pairNorm H A B).natDegree : ℤ) =
      ∑ v ∈ T, (residueDeg v : ℤ) * ordAtSpec v A B := by
  -- Step 1 (factorization): `Ideal.span {toPair H A B} = ∏ v ∈ T, v.asIdeal ^ nV`.
  have hne : toPair H A B ≠ 0 := by rw [Ne, toPair_eq_zero_iff]; exact hAB
  have h_span := span_toPair_eq_prod_heightOneSpectrum_pow T A B hAB hsupp
  -- Step 2+3 (CRT + associated-graded, weighted by `residueDeg`):
  -- `finrank k (CoordinateRing H ⧸ span {toPair H A B}) = ∑ v ∈ T, residueDeg v * nV`.
  -- `Finset.sum_attach T f : ∑ v : T, f v.1 = ∑ v ∈ T, f v` — reindexes the subtype sum
  -- `heightOneSpectrum_finrank_quotient_prod_eq_sum` produces back to the `Finset` sum this
  -- theorem's own statement uses, exactly as `finrank_quotient_span_eq_sum_ordAt`
  -- (`PrincipalDivisors.lean:1137`) does for the rational-point case.
  have hfin : Module.finrank k
      (CoordinateRing H ⧸ Ideal.span ({toPair H A B} : Set (CoordinateRing H))) =
      ∑ v ∈ T, residueDeg v * (ordAtSpec v A B).toNat := by
    rw [h_span]
    rw [heightOneSpectrum_finrank_quotient_prod_eq_sum T A B]
    exact Finset.sum_attach T (fun v => residueDeg v * (ordAtSpec v A B).toNat)
  -- Step 4 (§4.4, already unconditionally proved in `PrincipalDivisors.lean`):
  -- `finrank k (CoordinateRing H ⧸ span {toPair H A B}) = (pairNorm H A B).natDegree`.
  have hnorm : Module.finrank k
      (CoordinateRing H ⧸ Ideal.span ({toPair H A B} : Set (CoordinateRing H))) =
      (pairNorm H A B).natDegree :=
    finrank_quotient_span_eq_natDegree_pairNorm A B hAB
  -- Assemble, then cast the `ℕ`-sum to `ℤ`, distributing the cast across the sum and each
  -- product, and rewriting `(ordAtSpec v A B).toNat` back to `ordAtSpec v A B` itself via
  -- `ordAtSpec_nonneg` (nonnegativity, needed since `Int.toNat` only inverts on `≥ 0`).
  have hcast : ((pairNorm H A B).natDegree : ℤ) =
      ∑ v ∈ T, (residueDeg v : ℤ) * (ordAtSpec v A B).toNat := by
    have hstep : ((pairNorm H A B).natDegree : ℤ) =
        ((∑ v ∈ T, residueDeg v * (ordAtSpec v A B).toNat : ℕ) : ℤ) := by
      rw [← hnorm, ← hfin]
    rw [hstep, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun v _ => by push_cast; ring)
  rw [hcast]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 1
  rw [Int.toNat_of_nonneg (ordAtSpec_nonneg v A B hne)]


/-! ## §2. Assembly: the global degree bound

`IsPoleBoundedAtPairSpec`'s pointwise clause, applied at `(A,B) = (1,0)` (so `ordAtSpec
v 1 0 = 0` everywhere, `toPair H 1 0 = 1` a unit — matching the ChatGPT snippet's choice
`f = A + By = 1`, `g = A' + B'y`), termwise-bounds `ordAtSpec v A' B'` by the indicator
`e_v`, then §1 turns that into the natDegree bound after summing. This is the exact
"take degrees" step of the ChatGPT derivation's §2/§5. -/

/-- **`ordAtSpec` is supported only at `pointHeightOne' x₁, pointHeightOne' x₂`, given
pole-boundedness of the reduced pair `(1,0)/(A',B')` at those two points.** The
termwise inequality `ordAtSpec v A' B' ≤ e_v` that the ChatGPT derivation's §1 ("the
entire local argument") establishes, transcribed directly: unfolds
`IsPoleBoundedAtPairSpec`'s pointwise clause at `(A,B) = (1,0)`, using `ordAtSpec v 1 0 =
0` (since `toPair H 1 0 = 1` is a unit, hence in no prime ideal — the same computation as
`RiemannRochGenus2.lean`'s §1c counterexample-exclusion argument, `hv1` around line 490).
-/
theorem ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec
    [IsDedekindDomain (CoordinateRing H)] (x₁ x₂ : H.Point) (A' B' : k[X])
    (h : IsPoleBoundedAtPairSpec x₁ x₂ (1 : k[X]) 0 A' B') :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v A' B' ≤
        (if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0) := by
  obtain ⟨_, _, hpt⟩ := h
  intro v
  -- Same computation as `RiemannRochGenus2.lean`'s
  -- `not_isPoleBoundedAtPairSpec_one_zero_irreducible` (`hv1`, around line 490): reuse
  -- it verbatim rather than re-derive, since it's already a checked, non-`sorry` proof.
  have hv1 : ordAtSpec v (1 : k[X]) 0 = 0 := by
    unfold ordAtSpec
    have hone_ne : toPair H (1 : k[X]) 0 ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      rintro ⟨hone, -⟩
      exact one_ne_zero hone
    rw [if_neg hone_ne]
    have hval : v.intValuation (toPair H (1 : k[X]) 0) = (1 : WithZero (Multiplicative ℤ)) := by
      rw [toPair_one_zero]
      exact v.intValuation.map_one
    rw [hval]
    simp
  have := hpt v
  rw [hv1] at this
  omega

/-- **The global degree bound.** The Lean statement of the ChatGPT derivation's final
boxed conclusion `deg N(g) ≤ 2`, phrased against this codebase's actual objects: if the
reduced pair `(1,0)/(A',B')` is pole-bounded at `x₁, x₂` in the `IsPoleBoundedAtPairSpec`
sense, then `(pairNorm H A' B').natDegree ≤ 2`. This is exactly
`ROADMAP-lpaircarrier-nonclosed-field.md` §4's target theorem
`natDegree_le_two_of_isPoleBoundedAtPairSpec`, and is the intended general-`k`
replacement for `LPairFinrankOneOrdAtFrac.lean`'s `natDegree_le_two_of_isCoprimeAtRoots`
at its one call site (`uniqueDegree2MapToP1_ordAtFrac`, `LPairFinrankOneOrdAtFrac.lean`
§5). -/
theorem natDegree_le_two_of_isPoleBoundedAtPairSpec
    [IsDedekindDomain (CoordinateRing H)] (x₁ x₂ : H.Point) (A' B' : k[X])
    (hA'B' : ¬(A' = 0 ∧ B' = 0))
    (h : IsPoleBoundedAtPairSpec x₁ x₂ (1 : k[X]) 0 A' B') :
    (pairNorm H A' B').natDegree ≤ 2 := by
  have hterm := ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec x₁ x₂ A' B' h
  obtain ⟨T, hsupp⟩ := exists_finite_support_ordAtSpec (H := H) A' B' hA'B'
  -- Enlarge `T` to also contain `pointHeightOne' x₁, pointHeightOne' x₂`, so the sum
  -- below is honestly indexed over a superset of every point where either `ordAtSpec`
  -- or the indicator can be nonzero — `hsupp` (hence `natDegree_pairNorm_eq_sum_
  -- residueDeg_ordAtSpec`) is agnostic to which superset of the true support is used.
  set T' : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :=
    insert (pointHeightOne' x₁) (insert (pointHeightOne' x₂) T) with hT'_def
  have hsupp' : ∀ v, v ∉ T' → ordAtSpec v A' B' = 0 := by
    intro v hv
    apply hsupp
    intro hvT
    apply hv
    rw [hT'_def]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hvT)
  have hnorm := natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec (H := H) A' B' hA'B' T' hsupp'
  -- Sum `hterm` against `residueDeg v ≥ 0`, matching the ChatGPT derivation's
  -- "take degrees" step: `∑ᵥ [κ(v):k] ord_v(g) ≤ ∑ᵥ [κ(v):k] e_v`, and the right side
  -- collapses to `residueDeg (pointHeightOne' x₁) + residueDeg (pointHeightOne' x₂) =
  -- 1 + 1 = 2` via `residueDeg_pointHeightOne'` (§0 above), since `e_v` is zero away
  -- from those two points and both are now guaranteed present in `T'`.
  have hle : ∑ v ∈ T', (residueDeg v : ℤ) * ordAtSpec v A' B' ≤
      ∑ v ∈ T', (residueDeg v : ℤ) *
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (hterm v) (Int.natCast_nonneg _)
  have hx₁mem : pointHeightOne' x₁ ∈ T' := by rw [hT'_def]; exact Finset.mem_insert_self _ _
  have hx₂mem : pointHeightOne' x₂ ∈ T' := by
    rw [hT'_def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  -- Collapse the RHS indicator sum: split off `x₁`'s term (via `Finset.sum_eq_sum_diff_
  -- singleton_add`), then bound what's left by re-summing with `x₂`'s term split off too.
  -- Every other `v` contributes `0` to the indicator, so this is really just picking out
  -- (at most) two nonzero terms, worth `residueDeg (pointHeightOne' xᵢ) = 1` each.
  have hcollapse : ∑ v ∈ T', (residueDeg v : ℤ) *
      ((if v = pointHeightOne' x₁ then 1 else 0) +
        (if v = pointHeightOne' x₂ then 1 else 0)) ≤ 2 := by
    have hterm_le : ∀ v ∈ T', (residueDeg v : ℤ) *
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) ≤
        (if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0) := by
      intro v _
      by_cases hv1 : v = pointHeightOne' x₁
      · subst hv1; rw [residueDeg_pointHeightOne']
        by_cases hv2 : pointHeightOne' x₁ = pointHeightOne' x₂ <;> simp [hv2]
      · by_cases hv2 : v = pointHeightOne' x₂
        · subst hv2; rw [residueDeg_pointHeightOne']; simp [hv1]
        · simp [hv1, hv2]
    calc ∑ v ∈ T', (residueDeg v : ℤ) *
          ((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0))
        ≤ ∑ v ∈ T', ((if v = pointHeightOne' x₁ then (1:ℤ) else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := Finset.sum_le_sum hterm_le
      _ = (∑ v ∈ T', (if v = pointHeightOne' x₁ then (1:ℤ) else 0)) +
            ∑ v ∈ T', (if v = pointHeightOne' x₂ then (1:ℤ) else 0) :=
          Finset.sum_add_distrib
      _ = 1 + 1 := by
            rw [Finset.sum_ite_eq' T' (pointHeightOne' x₁) (fun _ => (1:ℤ)),
                Finset.sum_ite_eq' T' (pointHeightOne' x₂) (fun _ => (1:ℤ)),
                if_pos hx₁mem, if_pos hx₂mem]
      _ = 2 := by norm_num
  have hfinal : ((pairNorm H A' B').natDegree : ℤ) ≤ 2 := by
    rw [hnorm]; exact le_trans hle hcollapse
  exact_mod_cast hfinal

/-! ## §3. General-numerator version

`natDegree_le_two_of_isPoleBoundedAtPairSpec` above fixes the numerator at `(1,0)`,
matching the ChatGPT derivation's choice `f = 1`. `LPairFinrankOneOrdAtFrac.lean`'s
actual call site (`uniqueDegree2MapToP1_ordAtFrac`, step 5 of the roadmap) has a
genuinely non-unit numerator `(a₀,b₀)` at the point it needs this bound (the numerator
is only known coprime-at-roots with the denominator, not reduced to a unit) — so the
`(1,0)`-fixed version doesn't apply there directly. This section restates the same
argument for an arbitrary numerator `(A,B)`, which is really the more natural generality
for the underlying `deg N(g) ≤ deg N(f) + 2` inequality: fixing `f = 1` was a
simplification specific to this file's original assembly, not an inherent restriction of
the argument.

**Honest status re: step 5 wiring.** This section's bound,
`deg N(c₀) ≤ deg N(a₀,b₀) + 2`, does *not* by itself close `LPairFinrankOneOrdAtFrac.
lean`'s `hcdeg : c₀.natDegree ≤ 2` goal the way `natDegree_le_two_of_isPoleBoundedAtPairSpec`
closes the `(1,0)`-numerator case. At the point `hcdeg` is needed, `b₀ = 0` is *not yet
known* — it's derived afterward, from `hcdeg` itself together with `hinf₀`
(`b_eq_zero_of_rationalized_pole_bounded`). So `deg N(a₀,b₀) = deg(a₀² - b₀²·H.f)` isn't
yet pinned to `0`; bounding it needs essentially the same "is `b₀` big" case analysis
`hcdeg`'s existing `IsAlgClosed`-based proof (via `ordInfOfPair`/root-counting) already
performs, just via norms instead of roots. This section's theorem is still useful in its
own right (a clean general-`k` fact matching the roadmap's boxed general inequality), and
`natDegree_le_two_of_isPoleBoundedAtPairSpec` (the `(1,0)`-fixed case, §2) genuinely is
sufficient for the reduced-numerator sub-case once one is reached (e.g. after some other
route establishes `b₀ = 0` independent of `hcdeg`, or the `x₁ = x₂` companion path) — but
completing step 5's rewiring for the general `(a₀,b₀)` case needs one more idea (most
likely: run this section's bound *and* a rearranged form of `hinf₀` together to solve for
both degrees simultaneously, rather than sequentially as the existing `IsAlgClosed`-based
proof does), not attempted here. Flagged as the next concrete gap, not glossed over. -/

/-- **`ordAtSpec`-difference is bounded by the indicator, general numerator.** Direct
requantification of `ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec`, dropping that
theorem's `(A,B) = (1,0)` specialization: `IsPoleBoundedAtPairSpec`'s pointwise clause
already states exactly `ordAtSpec v A B ≥ ordAtSpec v A' B' - e_v` for arbitrary `(A,B)`,
so this is a direct restatement (`sub_le_iff_le_add`-shaped rearrangement), not a new
computation — the `(1,0)`-specific `hv1`-style unit-valuation argument from the original
theorem is exactly the extra fact `ordAtSpec v A B = 0` used to simplify that rearranged
inequality down to `ordAtSpec v A' B' ≤ e_v`, and is simply absent here since `(A,B)` is
no longer assumed a unit. -/
theorem ordAtSpec_sub_le_indicator_of_isPoleBoundedAtPairSpec
    [IsDedekindDomain (CoordinateRing H)] (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (h : IsPoleBoundedAtPairSpec x₁ x₂ A B A' B') :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v A' B' ≤ ordAtSpec v A B +
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) := by
  obtain ⟨_, _, hpt⟩ := h
  intro v
  have := hpt v
  linarith

/-- **The general-numerator global degree bound.** `(pairNorm H A' B').natDegree ≤
(pairNorm H A B).natDegree + 2`, whenever `(A,B,A',B')` is pole-bounded at `x₁,x₂` in
the `IsPoleBoundedAtPairSpec` sense. Specializes to
`natDegree_le_two_of_isPoleBoundedAtPairSpec` at `(A,B) = (1,0)`
(`(pairNorm H 1 0).natDegree = 0`), but is proved independently here (same shape,
summing `ordAtSpec_sub_le_indicator_of_isPoleBoundedAtPairSpec` instead of
`ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec`, against a `T'` enlarged to contain
the support of *both* `(A,B)` and `(A',B')`) rather than derived from it, since deriving
it would need `(pairNorm H A B).natDegree` fed back in as a numerator-side pole bound,
which is exactly circular with what this theorem is proving. -/
theorem natDegree_pairNorm_le_natDegree_pairNorm_add_two_of_isPoleBoundedAtPairSpec
    [IsDedekindDomain (CoordinateRing H)] (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hAB : ¬(A = 0 ∧ B = 0)) (hA'B' : ¬(A' = 0 ∧ B' = 0))
    (h : IsPoleBoundedAtPairSpec x₁ x₂ A B A' B') :
    (pairNorm H A' B').natDegree ≤ (pairNorm H A B).natDegree + 2 := by
  have hterm := ordAtSpec_sub_le_indicator_of_isPoleBoundedAtPairSpec x₁ x₂ A B A' B' h
  obtain ⟨TAB, hsuppAB⟩ := exists_finite_support_ordAtSpec (H := H) A B hAB
  obtain ⟨TA'B', hsuppA'B'⟩ := exists_finite_support_ordAtSpec (H := H) A' B' hA'B'
  set T' : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :=
    insert (pointHeightOne' x₁) (insert (pointHeightOne' x₂) (TAB ∪ TA'B')) with hT'_def
  have hx₁mem : pointHeightOne' x₁ ∈ T' := by rw [hT'_def]; exact Finset.mem_insert_self _ _
  have hx₂mem : pointHeightOne' x₂ ∈ T' := by
    rw [hT'_def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hsuppAB' : ∀ v, v ∉ T' → ordAtSpec v A B = 0 := by
    intro v hv
    apply hsuppAB
    intro hvT
    apply hv
    rw [hT'_def]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hvT))
  have hsuppA'B' : ∀ v, v ∉ T' → ordAtSpec v A' B' = 0 := by
    intro v hv
    apply hsuppA'B'
    intro hvT
    apply hv
    rw [hT'_def]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hvT))
  have hnormAB := natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec (H := H) A B hAB T' hsuppAB'
  have hnormA'B' :=
    natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec (H := H) A' B' hA'B' T' hsuppA'B'
  have hle : ∑ v ∈ T', (residueDeg v : ℤ) * ordAtSpec v A' B' ≤
      ∑ v ∈ T', (residueDeg v : ℤ) *
        (ordAtSpec v A B +
          ((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0))) := by
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (hterm v) (Int.natCast_nonneg _)
  have hexpand : ∑ v ∈ T', (residueDeg v : ℤ) *
      (ordAtSpec v A B +
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0))) =
      (∑ v ∈ T', (residueDeg v : ℤ) * ordAtSpec v A B) +
        ∑ v ∈ T', (residueDeg v : ℤ) *
          ((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    ext v
    ring
  have hcollapse : ∑ v ∈ T', (residueDeg v : ℤ) *
      ((if v = pointHeightOne' x₁ then 1 else 0) +
        (if v = pointHeightOne' x₂ then 1 else 0)) ≤ 2 := by
    have hterm_le : ∀ v ∈ T', (residueDeg v : ℤ) *
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) ≤
        (if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0) := by
      intro v _
      by_cases hv1 : v = pointHeightOne' x₁
      · subst hv1; rw [residueDeg_pointHeightOne']
        by_cases hv2 : pointHeightOne' x₁ = pointHeightOne' x₂ <;> simp [hv2]
      · by_cases hv2 : v = pointHeightOne' x₂
        · subst hv2; rw [residueDeg_pointHeightOne']; simp [hv1]
        · simp [hv1, hv2]
    calc ∑ v ∈ T', (residueDeg v : ℤ) *
          ((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0))
        ≤ ∑ v ∈ T', ((if v = pointHeightOne' x₁ then (1:ℤ) else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := Finset.sum_le_sum hterm_le
      _ = (∑ v ∈ T', (if v = pointHeightOne' x₁ then (1:ℤ) else 0)) +
            ∑ v ∈ T', (if v = pointHeightOne' x₂ then (1:ℤ) else 0) :=
          Finset.sum_add_distrib
      _ = 1 + 1 := by
            rw [Finset.sum_ite_eq' T' (pointHeightOne' x₁) (fun _ => (1:ℤ)),
                Finset.sum_ite_eq' T' (pointHeightOne' x₂) (fun _ => (1:ℤ)),
                if_pos hx₁mem, if_pos hx₂mem]
      _ = 2 := by norm_num
  have hfinal : ((pairNorm H A' B').natDegree : ℤ) ≤ (pairNorm H A B).natDegree + 2 := by
    rw [hnormA'B', hnormAB]
    calc ∑ v ∈ T', (residueDeg v : ℤ) * ordAtSpec v A' B'
        ≤ (∑ v ∈ T', (residueDeg v : ℤ) * ordAtSpec v A B) +
            ∑ v ∈ T', (residueDeg v : ℤ) *
              ((if v = pointHeightOne' x₁ then 1 else 0) +
                (if v = pointHeightOne' x₂ then 1 else 0)) := by rw [← hexpand]; exact hle
      _ ≤ (∑ v ∈ T', (residueDeg v : ℤ) * ordAtSpec v A B) + 2 := by linarith
  exact_mod_cast hfinal

/-! ## §4. The pole-divisor route (ChatGPT-consulted fix for §3's circularity)

**Why §3 alone doesn't finish `LPairFinrankOneOrdAtFrac.lean`'s step 5.** §3's bound
`deg N(A',B') ≤ deg N(A,B) + 2` is circular at the one call site that needs a
non-`(1,0)` numerator (`uniqueDegree2MapToP1_ordAtFrac`'s `hcdeg` goal): `deg N(a₀,b₀)`
is not known to be small at the point `hcdeg` is needed — indeed `b₀ = 0` is derived
*from* `hcdeg`, not before it. Bounding the two norms separately and comparing them
can't break that circularity no matter how the comparison is stated.

**The fix (ChatGPT consultation, ported to this codebase's objects): don't bound the
two norms at all — bound the *pole divisor of the fraction* `z = g/g'` directly.**
`ordAtSpec v A B - ordAtSpec v A' B'` is the `v`-adic order of `z` (numerator order
minus denominator order); its negative part, `max (ordAtSpec v A' B' - ordAtSpec v A B) 0`,
is the actual pole multiplicity of `z` at `v` — zero wherever `z` has no pole there.
`IsPoleBoundedAtPairSpec`'s pointwise clause bounds this negative part termwise by the
indicator `e_v`, exactly as `LPairFinrankOne.lean`'s `isRatioDivisor_shape_of_bounds`
already does for the rational-point-only divisor `divToPairRatio` — this section is the
direct `HeightOneSpectrum`-indexed, residue-degree-weighted generalization of that
theorem, following the exact same case-split-on-`x₁ ∈ T`/`x₂ ∈ T`/`x₁ = x₂` proof shape
(`max_zero_le_add`, `Finset.sum_erase_add`), reindexed from `H.Point`/unweighted
`coeffAt` to `HeightOneSpectrum`/`residueDeg`-weighted `ordAtSpec`-difference. No norm,
no `pairNorm`, no `natDegree` appears anywhere in this section — degree only enters
downstream, via §1's identity applied to whichever polynomial the caller actually wants
a degree bound for (typically the denominator alone, `deg c ≤` this section's pole-mass
bound, once the caller also knows `deg c` equals the *total* — positive and negative —
pole-divisor mass of `c`'s zero locus, which is a separate, `z`-independent fact from
§1, not reproved here). -/

/-- **The residue-degree-weighted pole-mass bound.** `HeightOneSpectrum`-indexed,
`residueDeg`-weighted analogue of `LPairFinrankOne.lean`'s `isRatioDivisor_shape_of_bounds`:
the total weighted *negative* part of `ordAtSpec v A B - ordAtSpec v A' B'` over `T` is
at most `2`. Unlike §2/§3, this needs no `natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec`/
§1 input, and no `ordInfOfPair A B ≥ ordInfOfPair A' B'` clause either — it's pure
pointwise-clause bookkeeping, the same way `isRatioDivisor_shape_of_bounds`'s own
`hdegD`/`hcoeffbound` inputs are pure divisor-arithmetic, no norm identity needed. -/
theorem sum_max_neg_ordAtSpec_diff_le_two
    [IsDedekindDomain (CoordinateRing H)] (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)))
    (hpt : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v A B ≥ ordAtSpec v A' B' -
        ((if v = pointHeightOne' x₁ then 1 else 0) + (if v = pointHeightOne' x₂ then 1 else 0)))
    (hx₁mem : pointHeightOne' x₁ ∈ T) (hx₂mem : pointHeightOne' x₂ ∈ T) :
    ∑ v ∈ T, (residueDeg v : ℤ) *
      max (ordAtSpec v A' B' - ordAtSpec v A B) 0 ≤ 2 := by
  -- Pointwise: `residueDeg v ≥ 0` and (from `hpt`, rearranged) `ordAtSpec v A' B' -
  -- ordAtSpec v A B ≤ e_v`, so `max (that difference) 0 ≤ max e_v 0 = e_v` (`e_v ≥ 0`
  -- always, being a sum of `0/1` indicators) — hence the weighted term is `≤ residueDeg
  -- v * e_v`, and summing collapses to `≤ 2` exactly as in §2/§3's indicator-collapse
  -- step (same `Finset.sum_ite_eq'`/`if_pos hx₁mem`/`if_pos hx₂mem` finish).
  have hterm_le : ∀ v ∈ T,
      (residueDeg v : ℤ) * max (ordAtSpec v A' B' - ordAtSpec v A B) 0 ≤
      (residueDeg v : ℤ) *
        ((if v = pointHeightOne' x₁ then (1:ℤ) else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) := by
    intro v _
    apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _)
    have hev_nonneg : (0:ℤ) ≤
        (if v = pointHeightOne' x₁ then (1:ℤ) else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0) := by
      have h1 : (0:ℤ) ≤ if v = pointHeightOne' x₁ then (1:ℤ) else 0 := by
        by_cases hv1 : v = pointHeightOne' x₁ <;> simp [hv1]
      have h2 : (0:ℤ) ≤ if v = pointHeightOne' x₂ then (1:ℤ) else 0 := by
        by_cases hv2 : v = pointHeightOne' x₂ <;> simp [hv2]
      linarith
    have hdiff_le : ordAtSpec v A' B' - ordAtSpec v A B ≤
        (if v = pointHeightOne' x₁ then (1:ℤ) else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0) := by linarith [hpt v]
    exact max_le hdiff_le hev_nonneg
  calc ∑ v ∈ T, (residueDeg v : ℤ) * max (ordAtSpec v A' B' - ordAtSpec v A B) 0
      ≤ ∑ v ∈ T, (residueDeg v : ℤ) *
          ((if v = pointHeightOne' x₁ then (1:ℤ) else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := Finset.sum_le_sum hterm_le
    _ = (∑ v ∈ T, (residueDeg v : ℤ) * (if v = pointHeightOne' x₁ then (1:ℤ) else 0)) +
          ∑ v ∈ T,
            (residueDeg v : ℤ) * (if v = pointHeightOne' x₂ then (1:ℤ) else 0) := by
        rw [← Finset.sum_add_distrib]; congr 1; ext v; ring
    _ = (∑ v ∈ T, if v = pointHeightOne' x₁ then (residueDeg v : ℤ) else 0) +
          ∑ v ∈ T, if v = pointHeightOne' x₂ then (residueDeg v : ℤ) else 0 := by
        congr 1
        · exact Finset.sum_congr rfl (fun v _ => by
            by_cases hv : v = pointHeightOne' x₁ <;> simp [hv])
        · exact Finset.sum_congr rfl (fun v _ => by
            by_cases hv : v = pointHeightOne' x₂ <;> simp [hv])
    _ = residueDeg (pointHeightOne' x₁) + residueDeg (pointHeightOne' x₂) := by
        rw [Finset.sum_ite_eq' T (pointHeightOne' x₁) (fun v => (residueDeg v : ℤ)),
            Finset.sum_ite_eq' T (pointHeightOne' x₂) (fun v => (residueDeg v : ℤ)),
            if_pos hx₁mem, if_pos hx₂mem]
    _ = 1 + 1 := by
        norm_num [residueDeg_pointHeightOne' (H := H)]
    _ = 2 := by norm_num

end HyperellipticPolynomial
