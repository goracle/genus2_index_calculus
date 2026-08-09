import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
import Genus2Lean.PrincipalDivisorSubgroup
import Genus2Lean.FFKSidon
import Genus2Lean.HyperellipticClassProof
import Genus2Lean.RiemannRochGenus2
import Genus2Lean.RatioDivisorCollapse
import Genus2Lean.RiemannRochCrux
set_option linter.style.header false

noncomputable section

open Classical

open Polynomial

/-!
# `uniqueDegree2MapToP1`, scoped down: an elementary route avoiding Riemann–Hurwitz

**Context.** `RiemannRochCrux.lean` reduces `finrank_L_pair` entirely to one
theorem, `uniqueDegree2MapToP1`. `UniqueDegree2MapRiemannHurwitz.lean` attacks
it via a full "degree-2 map to `P¹`" classification (ramification indices,
Riemann–Hurwitz counting, Möbius-transform uniqueness) — genuinely more
machinery than the fact needs, and correspondingly harder (see
`SCOPING-finrank-L-pair.md` in the project root for the full analysis).

**Revision history, kept here because the false start is instructive.** The
first draft of this file tried to show a pole-bounded pair `(A,B,A',B')`
directly forces `B = B' = 0` (reducing `z` to a pure rational function of `x`
alone) by raw `k[X]`-degree counting. **That claim is false**: `A=A'=0,
B=B'=1` gives `z = y/y = 1`, trivially constant and trivially satisfying
`IsPoleBoundedAtPair`, yet `B' ≠ 0` — `IsPoleBoundedAtPair` never asserts a
representation is reduced, so a shared spurious factor (here, all of `y`)
between numerator and denominator can survive undetected. Full counterexample
and the corrected derivation are in `SCOPING-finrank-L-pair.md`.

**Current strategy**: work with the *divisor* `D := divToPairRatio A B T A'
B' T` (`T` a finite support, Lemma 0 below) rather than with `B, B'` as raw
polynomials. `D`'s coefficients automatically cancel any shared,
representation-artifact factor, so bounds on `D` are honest facts about `z`
itself:

* **Lemma 0** (`exists_finite_support_of_hspec`): a finite support `Finset
  H.Point` exists for any nonzero `toPair H A B`, given the standing `hspec`
  hypothesis (same one `deg_div_eq_zero_deg5` already requires everywhere in
  this project).
* **§1** (`deg_divToPairRatio_le_zero`): `deg D ≤ 0`, unconditionally, via
  `deg_div_eq_zero_deg5` applied to each pair separately (no need for
  `ordInfOfPair A B = ordInfOfPair A' B'` — the weaker `≥`
  `IsPoleBoundedAtPair` supplies is enough).
* **§2** (`coeffAt_divToPairRatio_bounds`): `D`'s negative part is confined to
  `{x₁,x₂}` with mass `≤ 2`, directly from `IsPoleBoundedAtPair`'s pointwise
  clause transported to `coeffAt P D` (same transport `RatioDivisorCollapse.
  lean`'s `hcoef` already does for a related divisor).
* **§3** (`constant_or_fiber_of_isPoleBoundedAtPair`, **still open, the actual
  crux**): from §1+§2's bounds (pole confined + mass-bounded, degree ≤ 0
  overall ⟹ zero part also mass-bounded), conclude `z` constant or `x₂ = ι
  x₁`. Not yet reduced to a precise sub-argument; the natural next move is
  reusing `RatioDivisorCollapse.lean`'s `IsRatioDivisor`/
  `mem_LPairCarrier_of_isRatioDivisor` machinery (going the direction that
  file doesn't yet build) rather than re-deriving fiber structure from
  scratch — see `SCOPING-finrank-L-pair.md` for the fuller discussion.

**Status (this session): §1 and §2 are now fully proved** (`deg_divToPairRatio_le_zero`
and `coeffAt_divToPairRatio_bounds` have no `sorry` in their own bodies — §1 by direct
reuse of `deg_div_eq_zero_deg5` applied to each pair separately, matching
`PrincipalDivisorSubgroup.lean`'s `deg_divToPairRatio_eq_zero` idiom exactly, including
its `Module.Finite` instance hypotheses; §2 by direct reuse of `RatioDivisorCollapse.lean`'s
`hcoef`/`hcoeffDivToPair` transport argument, ported verbatim to `divToPairRatio A B T A'
B' T`). **Lemma 0** (`exists_finite_support_of_hspec`) is fully proved *modulo one small,
explicitly isolated sub-lemma*, `hfinite_support`, which is the only remaining `sorry` short
of §3: it needs the fact that `(Associates.mk I).factors` (`I ≠ 0`) unfolds to a genuine
finite `Multiset`, and the precise Mathlib unfolding lemma for that was not checked against
a live goal (see `hfinite_support`'s own docstring for the exact uncertainty and candidate
lemma names) — this is a bookkeeping gap, not a mathematical one, pending `lake build`
verification with a real REPL. **§3 (`constant_or_fiber_of_isPoleBoundedAtPair`) remains
the one genuinely open, hard `sorry`** — the actual crux, not yet reduced to a precise
sub-argument; do not restart from the old three-lemma "B=0" framing if revisiting this file.
Note `uniqueDegree2MapToP1_of_elementary`'s assembly is unaffected by this session's changes
and still depends only on §3.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-! ## Lemma 0 (new, load-bearing infrastructure): finite support from `hspec`

**Added after discovering Lemma 1 as originally stated was FALSE** (see
`SCOPING-finrank-L-pair.md`'s "Correction" section: `A=A'=0, B=B'=1` gives
`z=1` trivially yet satisfies `IsPoleBoundedAtPair` with `B' ≠ 0` — raw
`(A,B)`-pair degree-counting is unsound without knowing the representation is
"efficient", and this project has no coprime-reduction machinery). Rather
than build that (hard, possibly as hard as the original problem — see
`h_coprime` in `UniqueDegree2MapRiemannHurwitz.lean`, the same wall from a
different angle), this lemma sidesteps it: it does *not* reduce a
representation, it directly proves the one fact actually needed downstream —
that the (unreduced, possibly-redundant) support of `ordAt _ A B` is a finite
`Finset H.Point`, given the standing `hspec` hypothesis already used
identically throughout `PrincipalDivisors.lean`/`PrincipalDivisorSubgroup.lean`
(`deg_div_eq_zero_deg5`, `sum_ordAt_eq_natDegree_pairNorm`, etc. all take this
same hypothesis as an honest standing assumption, not something proved
in-project — see `PrincipalDivisors.lean:633`'s note that it was "missing
from the original" and had to be added explicitly; it encodes "no height-one
prime of `CoordinateRing H` corresponds to a point at infinity", a genuine
extra fact about this specific ring, consistent with `AffinePoints.lean`'s
own flagged points-at-infinity gap).

**Proof shape**: `Associates.mk (Ideal.span {toPair H A B})).factors` is a
`Multiset` (finite, by construction of `UniqueFactorizationMonoid` factors) of
associate classes of height-one primes. `hspec` says every one of them, if it
has positive count, equals `pointIdeal P` for some `P` — so composing
`factors.toFinset` with a choice function `v ↦ P` (using `pointIdeal_ne_of_ne`
for injectivity, so the resulting `Finset H.Point` doesn't need any
multiplicity bookkeeping, just the underlying set of *which* points occur)
gives the desired finite point-set. `ordAt_eq_count` (`PrincipalDivisors.lean`)
already identifies `ordAt P A B` with exactly this count, so "outside the
image, count is `0`, hence `ordAt` is `0`" closes the `hsupp`-shaped
conclusion `deg_div_eq_zero_deg5`/`IsRatioDivisor` need. -/
/-- **Confirmed route, using `count_associates_factors_eq` and `Ideal.mem_normalizedFactors_iff`
(`Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`)**: for `I ≠ 0`, `J` prime, `J ≠ ⊥`,
`(Associates.mk J).count (Associates.mk I).factors = Multiset.count J
(UniqueFactorizationMonoid.normalizedFactors I)` — this is the exact bridge from
`Associates.count` (the `FactorSet`/`WithTop`-wrapped API `hspec` is stated in) to
`Multiset.count` on the genuine, honestly-finite `Multiset (Ideal (CoordinateRing H))`
`normalizedFactors I`. Every `v : HeightOneSpectrum (CoordinateRing H)` supplies exactly
such a `J := v.asIdeal` (prime via `v.isPrime`, nonzero via `v.ne_bot`), so nonzero count
for `v` forces `v.asIdeal ∈ normalizedFactors I` (`Multiset.count_ne_zero`), landing `v.asIdeal`
in the finite set `(normalizedFactors I).toFinset`. Conversely, `Ideal.mem_normalizedFactors_iff`
(the Dedekind-domain-specialized membership criterion, giving `p.IsPrime` directly rather than
the monoid-level `Prime`/`Irreducible` predicates) lets every `J` in that finite set be
reassembled into a genuine `HeightOneSpectrum` term via the same anonymous-constructor shape
`pointHeightOne`/`pointHeightOne'` already use elsewhere in this project. The remaining step —
a finite set of `v`s themselves, not just of `v.asIdeal`s — is the image, over
`(normalizedFactors I).toFinset.attach`, of a choice function performing that reassembly. -/
theorem hfinite_support (I : Ideal (CoordinateRing H)) (hIne : I ≠ 0) :
    ∃ Tset : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)),
      ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
        (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 → v ∈ Tset := by
  classical
  -- Every ideal `J ∈ normalizedFactors I` is prime and nonzero, so it assembles into a
  -- genuine `HeightOneSpectrum` term; package that reconstruction as a choice function.
  -- `Ideal.mem_normalizedFactors_iff` (Dedekind-domain-specific, needs `I ≠ ⊥`) gives
  -- `p.IsPrime` directly — the exact field `HeightOneSpectrum` needs — with no detour
  -- through the monoid-level `Prime`/`Irreducible` predicates on `Ideal (CoordinateRing H)`.
  have hbuild : ∀ J ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
      ∃ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H), v.asIdeal = J := by
    intro J hJ
    rw [Multiset.mem_toFinset] at hJ
    have hIbot : I ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact hIne
    have hJprime : J.IsPrime := ((Ideal.mem_normalizedFactors_iff hIbot).mp hJ).1
    -- `J` is a genuine height-one prime: nonzero (else `normalizedFactors I` couldn't
    -- contain it — `UniqueFactorizationMonoid.zero_notMem_normalizedFactors`) and prime.
    have hJne : J ≠ ⊥ := by
      intro hJ0
      rw [hJ0] at hJ
      exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors I hJ
    exact ⟨⟨J, hJprime, hJne⟩, rfl⟩
  set Tset : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :=
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset.attach.image
      (fun J => (hbuild J.1 J.2).choose) with hTset_def
  refine ⟨Tset, fun v hv => ?_⟩
  -- `v.asIdeal ∈ normalizedFactors I` via `Ideal.count_associates_factors_eq` + `count_ne_zero`.
  have hcount_eq : (Associates.mk v.asIdeal).count (Associates.mk I).factors =
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) :=
    Ideal.count_associates_factors_eq hIne v.isPrime v.ne_bot
  rw [hcount_eq] at hv
  have hmemMultiset : v.asIdeal ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.count_ne_zero.mp hv
  have hmemFinset : v.asIdeal ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset :=
    Multiset.mem_toFinset.mpr hmemMultiset
  rw [hTset_def]
  refine Finset.mem_image.mpr ⟨⟨v.asIdeal, hmemFinset⟩, Finset.mem_attach _ _, ?_⟩
  -- `(hbuild v.asIdeal hmemFinset).choose_spec : (choose).asIdeal = v.asIdeal`; combined with
  -- `HeightOneSpectrum.ext`, this gives `choose = v` — the goal's actual orientation.
  have hspec_eq := (hbuild v.asIdeal hmemFinset).choose_spec
  exact IsDedekindDomain.HeightOneSpectrum.ext hspec_eq

theorem exists_finite_support_of_hspec (A B : k[X]) (hAB : ¬ (A = 0 ∧ B = 0))
    (hspec : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P) :
    ∃ S : Finset H.Point, ∀ P, P ∉ S → ordAt P A B = 0 := by
  classical
  set g : CoordinateRing H := toPair H A B with hg_def
  set I : Ideal (CoordinateRing H) := Ideal.span ({g} : Set (CoordinateRing H)) with hI_def
  have hgne : g ≠ 0 := by rw [hg_def, Ne, toPair_eq_zero_iff]; exact hAB
  have hIne : I ≠ 0 := by
    rw [hI_def, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hgne
  obtain ⟨Tset, hsub⟩ := hfinite_support I hIne
  -- Restrict to the sub-`Finset` of `Tset` whose count is genuinely nonzero — a plain
  -- `Finset.filter`, so still finite, and now every element has an honest `hspec`-supplied
  -- witness point (no dummy/placeholder branch needed for the zero-count case, since those
  -- `v`s are filtered out before the choice function is ever applied).
  set Tpos : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :=
    Tset.filter (fun v => (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0)
    with hTpos_def
  have hTpos_spec : ∀ v ∈ Tpos, (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 :=
    fun v hv => (Finset.mem_filter.mp hv).2
  set S : Finset H.Point :=
    Tpos.attach.image (fun v => (hspec v.1 (hTpos_spec v.1 v.2)).choose) with hS_def
  refine ⟨S, fun P hPS => ?_⟩
  by_cases hbot : pointIdeal P = ⊥
  · -- `pointIdeal P = ⊥` makes `ordAt`'s own `dif_pos` branch return `0` directly,
    -- regardless of `g`'s vanishing (we already know `g ≠ 0` from `hgne` above, so the
    -- `if toPair H A B = 0` branch is never taken here).
    unfold ordAt
    rw [if_neg (hg_def ▸ hgne), dif_pos hbot]
  · rw [ordAt_eq_count P A B hgne hbot]
    have hne0 : (Associates.mk (pointHeightOne P hbot).asIdeal).count
        (Associates.mk I).factors = 0 := by
      by_contra hcount
      apply hPS
      rw [hS_def]
      have hvmemT : pointHeightOne P hbot ∈ Tset := hsub (pointHeightOne P hbot) hcount
      have hvmemPos : pointHeightOne P hbot ∈ Tpos := by
        rw [hTpos_def, Finset.mem_filter]
        exact ⟨hvmemT, hcount⟩
      refine Finset.mem_image.mpr
        ⟨⟨pointHeightOne P hbot, hvmemPos⟩, Finset.mem_attach _ _, ?_⟩
      -- `(hspec v hv).choose_spec : v.asIdeal = pointIdeal (choose)`; here
      -- `v.asIdeal = pointIdeal P` definitionally (`pointHeightOne`'s field), so
      -- `pointIdeal P = pointIdeal (choose)`. The witness `choose` is an opaque term
      -- (via `Classical.choice`), so `rw` on an equation mentioning it fails with a
      -- "motive is not type correct" error (the goal `choose = P` depends on the very
      -- term being rewritten) — use `Eq.trans`/`.symm` composition instead of `rw`.
      have hspec_eq := (hspec (pointHeightOne P hbot) (hTpos_spec _ hvmemPos)).choose_spec
      have hPideal : (pointHeightOne P hbot).asIdeal = pointIdeal P := rfl
      have hPeq : pointIdeal P = pointIdeal
          (hspec (pointHeightOne P hbot) (hTpos_spec _ hvmemPos)).choose :=
        hPideal ▸ hspec_eq
      by_contra hne
      exact pointIdeal_ne_of_ne _ P hne hPeq.symm
    exact_mod_cast hne0

/-! ## §1 (corrected, replaces the earlier false "Lemma 1"): the degree bound on `D`

**The earlier draft of this section claimed `B' = 0` is forced directly from
`IsPoleBoundedAtPair` — FALSE, see `SCOPING-finrank-L-pair.md`'s "Correction"
section for the counterexample (`A=A'=0,B=B'=1` gives `z=1` trivially with
`B'≠0`).** The fix: work with the *divisor* `D := divToPairRatio A B T A' B'
T` (`T` a large-enough finite support, via Lemma 0 above) rather than with
`B, B'` as raw polynomials — `D`'s coefficients automatically cancel any
shared, representation-artifact factor between numerator and denominator
(exactly the phenomenon the counterexample exploited), so bounds on `D` are
honest, representation-independent-modulo-`T` facts about `z` itself.

`deg D ≤ 0` **unconditionally** (no need for `ordInfOfPair A B = ordInfOfPair
A' B'`, only the `≥` `IsPoleBoundedAtPair` already supplies): apply
`deg_div_eq_zero_deg5` (`PrincipalDivisors.lean:1844`) to `(A,B)` and to
`(A',B')` *separately* — it needs no matching between the two pairs, giving
`∑_T ordAt(A,B) = -ordInfOfPair(A,B)` and `∑_T ordAt(A',B') =
-ordInfOfPair(A',B')` exactly; subtracting, `deg D = ordInfOfPair(A',B') -
ordInfOfPair(A,B) ≤ 0` directly from `hbound`'s second conjunct. -/
theorem deg_divToPairRatio_le_zero (hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x₁ x₂ A B A' B')
    (hspecAB : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (hspecA'B' : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (T : Finset H.Point)
    (hAB : ¬ (A = 0 ∧ B = 0)) (hA'B' : ¬ (A' = 0 ∧ B' = 0))
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0)
    -- Same standing instance `deg_div_eq_zero_deg5` itself requires (see
    -- `PrincipalDivisorSubgroup.lean`'s `deg_divToPairRatio_eq_zero`, which threads the
    -- identical pair of instance hypotheses through for the same reason: it is not yet
    -- derivable in general, pending `finrank_quotient_pointIdeal_pow`, §4.2 step 4).
    [∀ P : T, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A B).toNat)]
    [∀ P : T, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A' B').toNat)] :
    deg (divToPairRatio A B T A' B' T) ≤ 0 := by
  unfold divToPairRatio
  rw [deg_sub, deg_divToPair, deg_divToPair]
  -- `deg_div_eq_zero_deg5` gives `(∑_T ordAt(A,B)) + ordInfOfPair A B = 0` and likewise for
  -- `(A',B')`; rearranged, `∑_T ordAt(A,B) = -ordInfOfPair A B` and
  -- `∑_T ordAt(A',B') = -ordInfOfPair A' B'`. Subtracting and using `hbound`'s second
  -- conjunct `ordInfOfPair A B ≥ ordInfOfPair A' B'` closes the goal by `omega`.
  have h₁ := deg_div_eq_zero_deg5 H hdeg T A B hAB hsuppAB hspecAB
  have h₂ := deg_div_eq_zero_deg5 H hdeg T A' B' hA'B' hsuppA'B' hspecA'B'
  obtain ⟨_, hmono, _⟩ := hbound
  omega

/-! ## §2 (corrected, replaces the earlier false "Lemma 2"): pole/zero bookkeeping on `D`

`D`'s negative part is confined to `{x₁,x₂}` with total mass `≤ 2` (directly
from `IsPoleBoundedAtPair`'s pointwise clause, transported to `coeffAt P D`
the same way `RatioDivisorCollapse.lean`'s already-proved `hcoef`
(`RatioDivisorCollapse.lean:386`) transports a pointwise `ordAt` bound into a
`coeffAt`-of-a-`divToPairRatio` statement — same argument shape, different
target divisor). Combined with §1's `deg D ≤ 0`, this forces `D`'s *positive*
part (support anywhere in `T`) to also have total mass `≤ 2`. This is the
correct, representation-independent-modulo-`T` replacement for the false
"`B=0`"/"the pole set is exactly `{x₁,x₂}`" claims: it bounds `D` on both
sides by degree `2`, without ever asserting anything about `B, B'`
syntactically. -/
theorem coeffAt_divToPairRatio_bounds (hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x₁ x₂ A B A' B')
    (T : Finset H.Point)
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0) :
    (∀ P, P ≠ x₁ → P ≠ x₂ → 0 ≤ Divisor.coeffAt P (divToPairRatio A B T A' B' T)) ∧
    Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) ≥
      -((if x₁ = x₁ then (1:ℤ) else 0) + (if x₁ = x₂ then 1 else 0)) ∧
    Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) ≥
      -((if x₂ = x₁ then (1:ℤ) else 0) + (if x₂ = x₂ then 1 else 0)) := by
  -- Same `coeffAt`-transport idiom as `RatioDivisorCollapse.lean`'s `hcoef`
  -- (`RatioDivisorCollapse.lean:386`), specialized to `divToPairRatio A B T A' B' T`
  -- rather than a fixed 4-point target divisor: `coeffAt P D = ordAt P A B - ordAt P A' B'`
  -- for every `P`, via the `AddMonoidHom` API (`map_sum`, `map_zsmul`, `coeffAt_single`),
  -- never applying `Divisor H` as a raw function.
  have hcoeffDivToPair : ∀ (a b : k[X]) (S : Finset H.Point),
      (∀ Q ∉ S, ordAt Q a b = 0) → ∀ P,
      Divisor.coeffAt P (divToPair a b S) = ordAt P a b := by
    intro a b S hS P
    unfold divToPair
    rw [map_sum]
    by_cases hPS : P ∈ S
    · rw [Finset.sum_eq_single P
        (fun Q _ hQP => by
          rw [map_zsmul, Divisor.coeffAt_single, if_neg (Ne.symm hQP)]; simp)
        (fun hPS' => absurd hPS hPS')]
      rw [map_zsmul, Divisor.coeffAt_single_self]
      simp
    · rw [Finset.sum_eq_zero (fun Q hQ => by
        have hQP : Q ≠ P := fun h => hPS (h ▸ hQ)
        rw [map_zsmul, Divisor.coeffAt_single, if_neg (Ne.symm hQP)]; simp)]
      rw [hS P hPS]
  have hcoef : ∀ P : H.Point,
      Divisor.coeffAt P (divToPairRatio A B T A' B' T) = ordAt P A B - ordAt P A' B' := by
    intro P
    unfold divToPairRatio
    rw [map_sub, hcoeffDivToPair A B T hsuppAB P, hcoeffDivToPair A' B' T hsuppA'B' P]
  obtain ⟨_, _, hptwise⟩ := hbound
  refine ⟨fun P hPx₁ hPx₂ => ?_, ?_, ?_⟩
  · -- `P ≠ x₁, x₂`: `hptwise P` gives `ordAt P A B ≥ ordAt P A' B' - 0`, i.e.
    -- `ordAt P A B - ordAt P A' B' ≥ 0`, which is `coeffAt P D ≥ 0` via `hcoef`.
    have hp := hptwise P
    rw [if_neg hPx₁, if_neg hPx₂] at hp
    rw [hcoef P]
    omega
  · have hp := hptwise x₁
    rw [hcoef x₁]
    split_ifs at hp ⊢ <;> omega
  · have hp := hptwise x₂
    rw [hcoef x₂]
    split_ifs at hp ⊢ <;> omega

/-! ## §3 (the genuinely new content, still open): a bounded-degree, pole-confined divisor forces the fiber dichotomy

**Not yet reduced to a precise statement.** With §1's `deg D ≤ 0` and §2's
pointwise bounds in hand (`D`'s pole part confined to `{x₁,x₂}`, mass `≤ 2`;
`D`'s zero part therefore also mass `≤ 2`, support anywhere in `T`), the
remaining content is: **either `z` is constant (i.e. `D`'s positive part is
`0` too, once matched against `IsRatioDivisor`-style exactness — see below),
or `z`'s pole set is genuinely `{x₁,x₂}` with `x₂ = ι x₁`.** This is where the
project's existing, *proven* machinery should be reusable rather than
reproving fiber structure from scratch: `RatioDivisorCollapse.lean`'s
`mem_LPairCarrier_of_isRatioDivisor` goes `IsRatioDivisor → LPairCarrier`
membership (with non-constancy) for a specific 4-point target divisor `(x₁)+
(x₂)-(x₃)-(x₄)`; what's needed here is close to its *converse* — `D` (once
its degree is pinned exactly via the discussion above, not just bounded) is
itself `IsRatioDivisor`-shaped for `hdeg`, so `hyperellipticClass_...`-style
fiber facts (`HyperellipticClassProof.lean`) or a direct case analysis via
`ordAt_linX_eq` should apply to it. **Left open — this is the actual crux and
the honest state of the art after this session's corrected analysis.
`SCOPING-finrank-L-pair.md` records the precise math already checked (§1–§2
above); do not restart from the (false) original three-lemma "B=0" framing.** -/
theorem constant_or_fiber_of_isPoleBoundedAtPair (hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁) (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x₁ x₂ A B A' B')
    (hspecAB : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (hspecA'B' : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P) :
    IsConstantFraction (polePairToFraction (H := H) A B A' B') := by
  sorry

/-! ## Assembly -/

/-- **`uniqueDegree2MapToP1`, via the elementary route — assembly, pending §3.**
`hz`'s witness `(A,B,A',B')` needs `hspec` for both halves threaded in
(the same standing hypothesis `deg_div_eq_zero_deg5` already requires
everywhere in this project); once available, `constant_or_fiber_of_isPoleBoundedAtPair`
(§3, still open) closes the goal directly. This is a drop-in replacement for
`RiemannRochCrux.lean`'s `uniqueDegree2MapToP1` *once §3 is closed and its
signature is finalized* — the `hspec` threading below is provisional pending
that. -/
theorem uniqueDegree2MapToP1_of_elementary (hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (z : FractionRing (CoordinateRing H)) (hz : z ∈ LPairCarrier x₁ x₂)
    (hspecAll : ∀ (A B : k[X]), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P) :
    IsConstantFraction z := by
  obtain ⟨A, B, A', B', hbound, hz_eq⟩ := hz
  rw [hz_eq]
  exact constant_or_fiber_of_isPoleBoundedAtPair hdeg x₁ x₂ hne A B A' B' hbound
    (hspecAll A B) (hspecAll A' B')

end HyperellipticPolynomial
