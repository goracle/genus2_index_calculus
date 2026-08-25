import Mathlib

/-! # A regular sequence of full length forces a finite-dimensional quotient

Generic commutative-algebra lemma, factored out so `decoupledSystem_zeroDimensional`
(`AlphaLocusDegreeUniform.lean`) can be a one-line instantiation of it rather
than a bespoke 12-variable argument. Routed through a ChatGPT consultation
first (per project convention for hard `sorry`s) — see
`chatgpt_prompt_zerodim.md` in this directory for the prompt and its answer.
Every named lemma below was independently checked against the current
Mathlib4 docs (not merely trusted from the consultation) before being used.

## Statement

If `rs : List R` is `IsRegular` on `R = MvPolynomial ι k` (`k` a field,
`ι` finite) and `rs.length = Nat.card ι`, then `R ⧸ Ideal.ofList rs` is a
finite-dimensional `k`-vector space.

## Proof architecture (confirmed against Mathlib4, this pass)

```
IsRegular R rs
    │  (RingTheory.Sequence.IsWeaklyRegular.regular_mod_prev, via IsRegular)
    ├─ each rs[i] is IsSMulRegular on R ⧸ (Ideal.ofList (rs.take i) • ⊤)
    │
    ├─ (isSMulRegular_self_iff_mem_nonZeroDivisors, THE ONE UNCONFIRMED STEP)
    │  rs[i] is a nonzerodivisor on that quotient RING (not just module)
    │
    ├─ (ringKrullDim_succ_le_of_surjective, CONFIRMED real)
    │  quotienting by a nonzerodivisor drops Krull dimension by ≥ 1
    │
    └─ after `rs.length` steps:
           ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length ≤ ringKrullDim R
                                                            = Nat.card ι
             (MvPolynomial.ringKrullDim_of_isNoetherianRing, CONFIRMED real)
         hence ringKrullDim (R ⧸ Ideal.ofList rs) ≤ 0
                         │
                         └─ (Ring.krullDimLE_iff, CONFIRMED real)
                            Ring.KrullDimLE 0 (R ⧸ Ideal.ofList rs)
                                         │
                                         └─ (Module.finite_iff_krullDimLE_zero,
                                             CONFIRMED real — k Artinian +
                                             finite-type algebra)
                                            Module.Finite k (R ⧸ Ideal.ofList rs)
```

Every lemma named CONFIRMED real was checked directly against the current
`leanprover-community.github.io/mathlib4_docs` pages this pass (not just
taken on the consultation's word) — exact signatures recorded in the
docstrings below. The one step not yet independently confirmed is flagged
explicitly at its `sorry`. -/

open RingTheory.Sequence

section RegularSequenceFiniteQuotient

variable {k : Type*} [Field k] {ι : Type*} [Finite ι] [DecidableEq ι]

/-- **The one unconfirmed step.** `IsSMulRegular` is a statement about a
module action (`R` acting on `M`); `ringKrullDim_succ_le_of_surjective`
wants a literal `r ∈ nonZeroDivisors R` fact about the RING `R ⧸ (previous
prefix)` acting on ITSELF. For `M := R` as a module over itself, these
should coincide (`r • x = r * x`, so "regular on the self-module" and
"not a zero divisor in the ring" are the same statement) — but the exact
Mathlib4 bridge lemma name was not confirmed against current docs this
pass (unlike every other step in this file). Flagged rather than guessed,
per project convention ("search first, don't guess Mathlib API" — this is
the one spot that search did not resolve). Send to ChatGPT / grep the
Mathlib4 source (`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean` or
`Mathlib/RingTheory/Regular/RegularSequence.lean`) for the exact name
before attempting to close this — do not guess a plausible-sounding one. -/
theorem isSMulRegular_self_iff_mem_nonZeroDivisors {R : Type*} [CommRing R] {r : R} :
    IsSMulRegular R r ↔ r ∈ nonZeroDivisors R := by
  sorry

/-- **One quotient step drops Krull dimension by at least 1**, given the
next generator is a nonzerodivisor on the current quotient. Direct
application of `ringKrullDim_succ_le_of_surjective` (`Mathlib.RingTheory.
KrullDimension.NonZeroDivisors`, confirmed this pass:
`{R S} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
{r : R} (hr : r ∈ nonZeroDivisors R) (hr' : f r = 0) : ringKrullDim S + 1 ≤
ringKrullDim R`) to the quotient map `R ⧸ I ↠ R ⧸ (I + span {r})` (which
Mathlib presents as `(R ⧸ I) ⧸ Ideal.span {mk r}` via the third isomorphism
theorem, or directly via `Ideal.quotientQuotientEquivQuotient`-style
identifications — the exact ring-iso bookkeeping needed to match `R ⧸
Ideal.ofList (rs.take (i+1))` against `(R ⧸ Ideal.ofList (rs.take i)) ⧸
Ideal.span {image of rs[i]}` one step at a time). -/
theorem ringKrullDim_quotient_ofList_succ_le
    {R : Type*} [CommRing R] (rs : List R) (i : ℕ) (h : i < rs.length)
    (hreg : IsSMulRegular (R ⧸ Ideal.ofList (rs.take i) • (⊤ : Submodule R R)) rs[i]) :
    ringKrullDim (R ⧸ Ideal.ofList (rs.take (i + 1))) + 1 ≤
      ringKrullDim (R ⧸ Ideal.ofList (rs.take i)) := by
  sorry

/-- **The main lemma.** A regular sequence of length equal to the Krull
dimension of `MvPolynomial ι k` (`= Nat.card ι` for a field `k`, finite
`ι`, via `MvPolynomial.ringKrullDim_of_isNoetherianRing`, confirmed this
pass) forces the quotient to be `Module.Finite k`-finite. Iterates
`ringKrullDim_quotient_ofList_succ_le` `rs.length` times, then closes with
`Module.finite_iff_krullDimLE_zero` (confirmed this pass:
`Mathlib.RingTheory.Jacobson.Artinian`, `[Algebra.FiniteType R A]
[IsArtinianRing R] : Module.Finite R A ↔ Ring.KrullDimLE 0 A`, applied
with `R := k` — a field is Artinian — and `A := ` the quotient ring, whose
`Algebra.FiniteType k A` instance comes from `Algebra.FiniteType.quotient`
applied to `MvPolynomial ι k`'s own finite-type-over-`k` instance). -/
theorem Module.Finite.quotient_of_isRegular_of_length_eq_card
    (rs : List (MvPolynomial ι k)) (hrs : IsRegular (MvPolynomial ι k) rs)
    (hlen : rs.length = Nat.card ι) :
    Module.Finite k (MvPolynomial ι k ⧸ Ideal.ofList rs) := by
  sorry

end RegularSequenceFiniteQuotient
