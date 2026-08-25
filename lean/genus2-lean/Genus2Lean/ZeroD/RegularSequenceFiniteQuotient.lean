import Mathlib

set_option linter.style.header false

/-! # A regular sequence of full length forces a finite-dimensional quotient

Generic commutative-algebra lemma, factored out so `decoupledSystem_zeroDimensional`
(`AlphaLocusDegreeUniform.lean`) can be a one-line instantiation of it rather
than a bespoke 12-variable argument.

## Statement

If `rs : List R` is `IsRegular` on `R = MvPolynomial ι k` (`k` a field,
`ι` finite) and `rs.length = Nat.card ι`, then `R ⧸ Ideal.ofList rs` is a
finite-dimensional `k`-vector space.

## Revision note (this pass, #6 — direct ring induction and explicit WithBot cancellation)

**`ringKrullDim_quotient_ofList_le_zero` (as previously stated) is
FALSE**, not merely unproved. Counterexample: `R = k[x,y]`, `rs = [x, x]`.
Then `rs.length = 2 = ringKrullDim R`, but `Ideal.ofList rs =
Ideal.ofList [x, x] = Ideal.span {x}` (`Ideal.ofList` spans the *set* of
list elements, so duplicates collapse), and `R ⧸ Ideal.span {x} ≅ k[y]`
has `ringKrullDim = 1 ≠ 0`. So "`rs.length = ringKrullDim R`" alone never
implies the quotient is `0`-dimensional — Krull's height theorem only
bounds height from *above* by the number of generators; it says nothing
about whether that many generators actually cut dimension down by that
much. The previous proof hole was not a missing-API gap; the statement itself
needed an extra hypothesis. This was caught and
diagnosed via ChatGPT consultation this pass (transcript-derived,
verified below against Mathlib4 source directly, not taken on faith).

The fix is to use the `IsRegular` hypothesis together with the older
`ringKrullDim_quotient_succ_le_of_nonZeroDivisor` theorem and induct on the
regular sequence. Each regular element drops Krull dimension by at least one,
and the successive quotient is canonically the quotient by the full list.

**`ringKrullDim_quotient_ofList_le_zero` is deleted outright this pass**
rather than kept, since its statement was false. Do not resurrect it
verbatim; any replacement needs the `IsRegular`/full-height hypothesis
baked in from the start, per the corrected statement above.

## Proof architecture (current)

R = MvPolynomial ι k, rs : List R, hrs : IsRegular R rs, rs.length = Nat.card ι
│
├─ MvPolynomial.ringKrullDim_of_isNoetherianRing + ringKrullDim_eq_zero_of_field
│  (CONFIRMED real, Mathlib4 source): ringKrullDim R = Nat.card ι = rs.length
│
├─ induction on rs + ringKrullDim_quotient_succ_le_of_nonZeroDivisor
│
├─ ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length ≤ ringKrullDim R
│
├─ hlen forces ringKrullDim (R ⧸ Ideal.ofList rs) = 0
│
└─ Module.finite_iff_krullDimLE_zero
│
└─ Module.Finite k (R ⧸ Ideal.ofList rs)


The proof below deliberately uses only the older regular-sequence and
non-zero-divisor APIs that are already present in the project snapshot. The
induction keeps `rs` in scope via `induction rs generalizing R`, and the final
`Ring.KrullDimLE` goal is converted with `Ring.krullDimLE_iff`. -/

open RingTheory.Sequence
-- `Submodule.pointwiseDistribMulAction` (needed for `r • (N : Submodule S S)`, the scalar
-- `r : S` acting pointwise on a submodule, as opposed to ideal-smul `I • N`) is scoped to the
-- `Pointwise` locale, so it must be opened explicitly.
open scoped Pointwise

section RegularSequenceFiniteQuotient

variable {k : Type*} [Field k] {ι : Type*} [Finite ι]
universe u

/-- **Resolved this pass** (previously flagged as the one unconfirmed step).
`IsSMulRegular` is a statement about a module action (`R` acting on `M`);
what's wanted is a literal `r ∈ nonZeroDivisors R` fact about the RING `R`
acting on ITSELF. The bridge goes through `nonZeroSMulDivisors`, confirmed
against current Mathlib4 docs (`Mathlib.Algebra.GroupWithZero.
NonZeroDivisors`) this pass:
* `isSMulRegular_iff_mem_nonZeroSMulDivisors {M₀ M} [MonoidWithZero M₀]
  [AddGroup M] [DistribMulAction M₀ M] {m₀ : M₀} :
  IsSMulRegular M m₀ ↔ m₀ ∈ nonZeroSMulDivisors M₀ M` — apply with `M := R`.
* `nonZeroDivisorsLeft_eq_nonZeroSMulDivisors {M₀} [MonoidWithZero M₀] :
  nonZeroDivisorsLeft M₀ = nonZeroSMulDivisors M₀ M₀` — identifies the
  self-action non-zero-smul-divisors with `nonZeroDivisorsLeft`.
* `nonZeroDivisorsLeft_eq_nonZeroDivisors {M₀} [CommMonoidWithZero M₀] :
  nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀` — collapses left/right for
  a commutative ring, landing on the plain `nonZeroDivisors`.
Chaining these three (in reverse) gives exactly the claimed iff. -/
theorem isSMulRegular_self_iff_mem_nonZeroDivisors {R : Type*} [CommRing R] {r : R} :
    IsSMulRegular R r ↔ r ∈ nonZeroDivisors R := by
  rw [isSMulRegular_iff_mem_nonZeroSMulDivisors, ← nonZeroDivisorsLeft_eq_nonZeroSMulDivisors,
    nonZeroDivisorsLeft_eq_nonZeroDivisors]

/-- `r • ⊤ = Ideal.span {r}`, as submodules of `S` viewed as a module over itself.
Membership-wise this is `x ∈ I • ⊤ ↔ x ∈ I` for `I = Ideal.span {r}`; proved by
extensionality rather than relying on a specific simp-normal form, since the
exact combinator API for this varies across Mathlib snapshots. -/
theorem smul_top_eq_span_singleton {S : Type u} [CommRing S] (r : S) :
    (r • (⊤ : Submodule S S)) = Ideal.span {r} := by
  apply Submodule.ext
  intro x
  rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, -, ha⟩
    rw [smul_eq_mul] at ha
    exact ⟨a, by rw [smul_eq_mul, mul_comm]; exact ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, Submodule.mem_top, ?_⟩
    rw [smul_eq_mul]
    rw [mul_comm]
    exact ha
    


/-- Transport `IsRegular S (r :: ys)` to `IsRegular (S ⧸ Ideal.span {r})
(ys.map (Ideal.Quotient.mk (Ideal.span {r})))`, the form the main induction's
inductive hypothesis needs.

An earlier draft tried to derive this by hand from the *unprimed*
`isRegular_cons_iff` (`IsRegular (QuotSMulTop r S) ys`, list still over `S`) via
`LinearEquiv.isRegular_congr` along `Submodule.quotEquivOfEq _ _
(smul_top_eq_span_singleton r) : QuotSMulTop r S ≃ₗ[S] S ⧸ Ideal.span {r}`,
followed by a second step converting the `List S` regularity statement into a
`List (S ⧸ Ideal.span {r})` one. That second step needed pushing
`top_ne_smul` through `Ideal.smul_top_eq_map`/`restrictScalars` by hand and was
fiddly enough to be a liability. Mathlib's own *primed* `isRegular_cons_iff'`
already produces exactly this transported statement as the second component of
its `Iff` (going through the same `QuotSMulTop r S ≃ₗ[S] S ⧸ Ideal.span {r}`
identification internally), so we just extract it from `hreg` directly instead
of re-deriving it. -/
theorem quotSMulTop_isRegular_congr {S : Type u} [CommRing S] (r : S) (ys : List S)
    (hreg : RingTheory.Sequence.IsRegular S (r :: ys)) :
    RingTheory.Sequence.IsRegular (S ⧸ Ideal.span {r})
      (ys.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
  have h_reg :=
    ((RingTheory.Sequence.isRegular_cons_iff' S r ys).mp hreg).2

  have hI : (r • (⊤ : Ideal S)) = Ideal.span {r} := by
    exact smul_top_eq_span_singleton r

  let e : QuotSMulTop r S ≃+* (S ⧸ Ideal.span {r}) :=
    Ideal.quotEquivOfEq hI

  have hcompat :
      List.Forall₂
        (fun a b : S ⧸ Ideal.span {r} =>
          ∀ x : QuotSMulTop r S,
            e.toAddEquiv (a • x) = b • e.toAddEquiv x)
        (ys.map (Ideal.Quotient.mk (Ideal.span {r})))
        (ys.map (Ideal.Quotient.mk (Ideal.span {r}))) := by
    apply List.forall₂_same.mpr
    intro a _ x

    refine Submodule.Quotient.induction_on (r • (⊤ : Submodule S S)) x ?_
    intro x'

    refine Submodule.Quotient.induction_on (Ideal.span {r}) a ?_
    intro a'

    rfl

  exact (e.toAddEquiv.isRegular_congr hcompat).mp h_reg


/-- The ring isomorphism identifying the iterated quotient
`(S ⧸ Ideal.span {r}) ⧸ Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span {r})))`
with the single quotient `S ⧸ Ideal.ofList (r :: ys)`. -/
def ringEquiv_quot_cons_ofList {S : Type u} [CommRing S] (r : S) (ys : List S) :
    (S ⧸ Ideal.span {r}) ⧸ Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span {r})))
      ≃+* S ⧸ Ideal.ofList (r :: ys) := by
  set I : Ideal S := Ideal.span {r} with hI
  set J : Ideal S := Ideal.ofList ys with hJ
  have hmap :
      Ideal.ofList (ys.map (Ideal.Quotient.mk I)) = J.map (Ideal.Quotient.mk I) := by
    rw [hJ, ← Ideal.map_ofList]
  exact
    (Ideal.quotEquivOfEq hmap).trans
      ((DoubleQuot.quotQuotEquivQuotSup I J).trans
        (Ideal.quotEquivOfEq (Ideal.ofList_cons r ys).symm))

/-- The successor step of the main induction: given the length-`n` bound for `ys`
(the induction hypothesis `ih`, already instantiated at `S ⧸ Ideal.span {r}` and
`ys.map (Ideal.Quotient.mk (Ideal.span {r}))`), and `r :: ys` regular on `S`,
produce the length-`(n+1)` bound for `r :: ys` on `S`. -/
theorem ringKrullDim_quotient_ofList_cons_add_length_le
    {S : Type u} [CommRing S] [IsNoetherianRing S] (r : S) (ys : List S)
    (hreg : RingTheory.Sequence.IsRegular S (r :: ys))
    (ih' :
      ringKrullDim
          ((S ⧸ Ideal.span {r}) ⧸
            Ideal.ofList (ys.map (Ideal.Quotient.mk (Ideal.span {r})))) +
        (ys.length : ℕ∞) ≤
        ringKrullDim (S ⧸ Ideal.span {r})) :
    ringKrullDim (S ⧸ Ideal.ofList (r :: ys)) + ((r :: ys).length : ℕ∞) ≤
      ringKrullDim S := by
  rcases (RingTheory.Sequence.isRegular_cons_iff S r ys).mp hreg with ⟨hreg_r, _⟩
  have hr : r ∈ nonZeroDivisors S :=
    (isSMulRegular_self_iff_mem_nonZeroDivisors).mp hreg_r
  have hdrop : ringKrullDim (S ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim S :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  have hfinal :
      ringKrullDim (S ⧸ Ideal.ofList (r :: ys)) + (ys.length : ℕ∞) ≤
        ringKrullDim (S ⧸ Ideal.span {r}) := by
    rw [← ringKrullDim_eq_of_ringEquiv (ringEquiv_quot_cons_ofList r ys)]
    exact ih'
  calc
    ringKrullDim (S ⧸ Ideal.ofList (r :: ys)) + ((r :: ys).length : ℕ∞)
        = (ringKrullDim (S ⧸ Ideal.ofList (r :: ys)) + (ys.length : ℕ∞)) + 1 := by
          simp [add_assoc, add_comm, add_left_comm]
    _ ≤ ringKrullDim (S ⧸ Ideal.span {r}) + 1 := by
          simpa [add_assoc, add_comm, add_left_comm] using (add_le_add_right hfinal 1)
    _ ≤ ringKrullDim S := by simpa [add_comm] using hdrop

theorem ringKrullDim_quotient_ofList_add_length_le_of_isRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R] (rs : List R)
    (reg : RingTheory.Sequence.IsRegular R rs) :
    ringKrullDim (R ⧸ Ideal.ofList rs) + (rs.length : ℕ∞) ≤ ringKrullDim R := by
  -- Do induction on the *length* rather than on `rs` directly. This lets
  -- the induction hypothesis quantify over a fresh ring `R`, including the
  -- successive quotient ring.
  suffices h :
      ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsNoetherianRing S]
        (xs : List S), xs.length = n → RingTheory.Sequence.IsRegular S xs →
          ringKrullDim (S ⧸ Ideal.ofList xs) + (xs.length : ℕ∞) ≤ ringKrullDim S by
    exact h rs.length R rs rfl reg
  intro n
  induction n with
  | zero =>
      intro S _ _ xs hlen _
      have hnil : xs = [] := List.length_eq_zero_iff.mp hlen
      subst xs
      rw [Ideal.ofList_nil]
      simpa only [List.length_nil, Nat.cast_zero, WithTop.coe_zero, WithBot.coe_zero,
        add_zero] using (ringKrullDim_quotient_le (⊥ : Ideal S))
  | succ n ih =>
      intro S _ _ xs hlen hreg
      cases xs with
      | nil => simp at hlen
      | cons r ys =>
        have hlen_ys : ys.length = n := by
          have hlen' : ys.length + 1 = n + 1 := by
            simpa only [List.length_cons, Nat.succ_eq_add_one] using hlen
          exact Nat.add_right_cancel hlen'
        rcases (RingTheory.Sequence.isRegular_cons_iff S r ys).mp hreg with
            ⟨_, hreg_ys⟩
        have hreg_ys' := quotSMulTop_isRegular_congr r ys hreg
        have ih' :=
          ih (S ⧸ Ideal.span {r}) (ys.map (Ideal.Quotient.mk (Ideal.span {r})))
            (by simp [hlen_ys]) hreg_ys'
        rw [List.length_map] at ih'
        exact ringKrullDim_quotient_ofList_cons_add_length_le r ys hreg ih'


theorem ringKrullDim_quotient_ofList_eq_zero_of_isRegular
    {R : Type*} [CommRing R] [IsNoetherianRing R] (rs : List R)
    (reg : IsRegular R rs) (hlen : (rs.length : ℕ∞) = ringKrullDim R) :
    Ring.KrullDimLE 0 (R ⧸ Ideal.ofList rs) := by
  have hle := ringKrullDim_quotient_ofList_add_length_le_of_isRegular rs reg
  rw [hlen] at hle
  apply Ring.krullDimLE_iff.mpr
  cases hq : ringKrullDim (R ⧸ Ideal.ofList rs) using WithBot.recBotCoe with
  | bot =>
      simp
  | coe n =>
      have hle' :
          ((n : ℕ∞) : WithBot ℕ∞) +
              ((rs.length : ℕ∞) : WithBot ℕ∞) ≤
            ((rs.length : ℕ∞) : WithBot ℕ∞) := by
        simpa [hq, hlen, WithBot.coe_add] using hle
      have hleTop : (n : ℕ∞) + (rs.length : ℕ∞) ≤ (rs.length : ℕ∞) := by
        exact WithBot.coe_le_coe.mp hle'
      have hn : n = 0 := by
        by_contra hn
        -- `n : ℕ∞` here (from `WithBot.recBotCoe`'s `coe` branch on `ringKrullDim`,
        -- which lands in `WithBot ℕ∞`), so we need the `ℕ∞`-level positivity lemma
        -- rather than `Nat.pos_of_ne_zero` (which is specific to `ℕ`).
        have hpos : (0 : ℕ∞) < n := pos_of_ne_zero hn
        have hlt : (rs.length : ℕ∞) < (n : ℕ∞) + (rs.length : ℕ∞) := by
          have hlt' :
              (0 : ℕ∞) + (rs.length : ℕ∞) <
                (n : ℕ∞) + (rs.length : ℕ∞) := by
            exact
              (ENat.add_lt_add_iff_right (ENat.coe_ne_top rs.length)).2 hpos
          simpa using hlt' 
        exact (not_lt_of_ge hleTop) hlt
      simp [hn]

/-- **The main lemma.** A regular sequence of length equal to the Krull
dimension of `MvPolynomial ι k` (`= Nat.card ι` for a field `k`, finite
`ι`) forces the quotient to be `Module.Finite k`-finite.

**`hlen'` (the `rs.length = ringKrullDim (MvPolynomial ι k)` arithmetic
fact) is CLOSED this pass** — see inline comment.

**Closed this pass** by the explicit regular-sequence dimension-drop induction
above; no newer global regular-sequence Krull-dimension theorem is used. -/
theorem Module.Finite.quotient_of_isRegular_of_length_eq_card
    (rs : List (MvPolynomial ι k)) (hrs : IsRegular (MvPolynomial ι k) rs)
    (hlen : rs.length = Nat.card ι) :
    Module.Finite k (MvPolynomial ι k ⧸ Ideal.ofList rs) := by
  -- `MvPolynomial.ringKrullDim_of_isNoetherianRing {ι} [Finite ι] :
  -- ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι` and
  -- `ringKrullDim_eq_zero_of_field` (`Mathlib.RingTheory.KrullDimension.
  -- {Polynomial,Field}`) confirmed against Mathlib4 source this pass —
  -- CLOSES the arithmetic gap from the previous pass.
  have hlen' : (rs.length : ℕ∞) = ringKrullDim (MvPolynomial ι k) := by
    rw [hlen, MvPolynomial.ringKrullDim_of_isNoetherianRing]
    simp
  have hdim : Ring.KrullDimLE 0 (MvPolynomial ι k ⧸ Ideal.ofList rs) :=
    ringKrullDim_quotient_ofList_eq_zero_of_isRegular rs hrs hlen'
  exact (Module.finite_iff_krullDimLE_zero k (MvPolynomial ι k ⧸ Ideal.ofList rs)).2 hdim

end RegularSequenceFiniteQuotient
