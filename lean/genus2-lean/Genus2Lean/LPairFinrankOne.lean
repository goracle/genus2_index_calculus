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
B' T`). **Lemma 0** (`exists_finite_support_of_hspec`, including its `hfinite_support`
sub-lemma) is now fully proved, no `sorry` — confirmed by a clean `lake build` this session
(the `Ideal.zero_eq_bot ▸` elaboration issue and the `zero_not_mem_normalizedFactors` →
`zero_notMem_normalizedFactors` rename were the only two build errors, both fixed).
**§3 (`constant_or_fiber_of_isPoleBoundedAtPair`) has been broken into a named proof
skeleton** (§3a `isRatioDivisor_shape_of_bounds`, §3d `isConstantFraction_of_divisor_le_zero`,
§3e `posMass_eq_negMass_le_two` — **renamed and weakened from the original
`divisor_eq_fiber_shape_or_constant`, which was found to be FALSE**; see that
lemma's docstring in place for the counterexample and for why Route A
(`SCOPING-finrank-L-pair.md`) should be attempted directly instead of patching
this abstract-divisor-shape decomposition further —, §3f `fiber_eq_of_divisor_shape`,
plus the assembly) rather than left as one opaque `sorry` — §3a/§3d are routine
`deg`/`coeffAt` bookkeeping once stated precisely (§3d is now fully proved, no
`sorry`), §3e is bookkeeping too but proves a materially weaker fact than
originally hoped (see its docstring); **§3f is the one genuinely hard,
still-unformalized `sorry`** — the actual mathematical crux, isolated to its precise
statement (`{x₃,x₄} = {x₁,x₂}` given the exact divisor shape, via `ordAt_linX_eq`, without
circularity through `uniqueDegree2MapToP1`) — **though note §3e no longer supplies
§3f's hypothesis**, so the assembly still cannot wire these pieces together as
originally planned; Route A steps 1–3 (SCOPING doc) are the likely unblock. The
assembly theorem's own body is *also* left `sorry`'d for now (wiring §3a/§3d/§3f
together, obtaining the common finite support via Lemma 0) — not yet attempted,
since §3e's gap blocks it regardless.
Do not restart from the old three-lemma "B=0" framing if revisiting this file.
Note `uniqueDegree2MapToP1_of_elementary`'s assembly is unaffected by this session's changes
and still depends only on §3's top-level theorem.

**Dupe-check against `UniqueDegree2MapRiemannHurwitz.lean` (this session):** no name
collisions (`grep`-verified) and no import relationship either direction, so no cycle
risk. Conceptually this file's §3 deliberately does *not* build any of that file's
`IsDegree2Map`/`IsRamificationPointOf` apparatus — confirmed by inspection that `IsDegree2Map`
requires an *exact* pole-degree-2 witness plus a `Disjoint S S'` pair, strictly more
structure than §3's `deg`/`coeffAt`-only argument needs, matching the scoping doc's
"more machine than the task needs" verdict. **One real, legitimate overlap**: that file's
`isDegree2Map_of_mem_LPairCarrier_of_ne_constant` has its own unproved `h_S_finite`/
`h_S'_finite`/`hspec'` gap — "find a finite support for `(A,B)` given `z ∈ LPairCarrier`" —
which is *the same problem* this file's Lemma 0 (`hfinite_support`/
`exists_finite_support_of_hspec`) already solves, just under an honestly-assumed `hspec`
hypothesis rather than (as that file's `hspec'` sorry attempts) trying to derive
prime-to-point correspondence from nothing. Not merged — different files, different
hypothesis threading, no cycle to justify importing across — but if
`UniqueDegree2MapRiemannHurwitz.lean`
is ever revisited, its `h_S_finite`/`h_S'_finite` sorries should cite this file's Lemma 0
rather than be re-derived independently.
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
/-- **Factored out of `coeffAt_divToPairRatio_bounds`'s proof body** so §3a can cite it
directly instead of re-deriving the same `AddMonoidHom`-transport argument a second time.
`coeffAt P (divToPair a b S) = ordAt P a b` for any `P`, given a support witness `S` for
`(a,b)` — pure bookkeeping via `map_sum`/`map_zsmul`/`coeffAt_single`, never applying
`Divisor H` as a raw function (`Divisor H` is a plain `def`, not `abbrev`, over
`H.Point →₀ ℤ`, so it doesn't unfold to `Finsupp`'s `DFunLike` application at ordinary
transparency — same discipline as `PrincipalDivisorSubgroup.lean`'s `divToPair` docstring
already notes). -/
theorem coeffAt_divToPair_eq_ordAt (a b : k[X]) (S : Finset H.Point)
    (hS : ∀ Q ∉ S, ordAt Q a b = 0) (P : H.Point) :
    Divisor.coeffAt P (divToPair a b S) = ordAt P a b := by
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

/-- **Factored out alongside `coeffAt_divToPair_eq_ordAt`**: the same-support specialization
`coeffAt P (divToPairRatio A B S A' B' S) = ordAt P A B - ordAt P A' B'`, used by both
`coeffAt_divToPairRatio_bounds` and §3a below. -/
theorem coeffAt_divToPairRatio_eq_sub (A B A' B' : k[X]) (T : Finset H.Point)
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0) (P : H.Point) :
    Divisor.coeffAt P (divToPairRatio A B T A' B' T) = ordAt P A B - ordAt P A' B' := by
  unfold divToPairRatio
  rw [map_sub, coeffAt_divToPair_eq_ordAt A B T hsuppAB P,
    coeffAt_divToPair_eq_ordAt A' B' T hsuppA'B' P]

theorem coeffAt_divToPairRatio_bounds (_hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x₁ x₂ A B A' B')
    (T : Finset H.Point)
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0) :
    (∀ P, P ≠ x₁ → P ≠ x₂ → 0 ≤ Divisor.coeffAt P (divToPairRatio A B T A' B' T)) ∧
    Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) ≥
      -((if x₁ = x₁ then (1 : ℤ) else 0) + (if x₁ = x₂ then 1 else 0)) ∧
    Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) ≥
      -((if x₂ = x₁ then (1 : ℤ) else 0) + (if x₂ = x₂ then 1 else 0)) := by
  have hcoef := coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B'
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

/-! ## §3 (the genuinely new content, still open): bounded-degree, pole-confined divisor
forces the fiber dichotomy

**Proof skeleton, drafted this session, not yet `lake build`-checked beyond
what typechecks at the `sorry`s below.** §1 (`deg D ≤ 0`) and §2 (`D`'s
negative part confined to `{x₁,x₂}`, mass `≤ 2`) together pin `D`'s *shape*
tightly enough to make `D` itself `IsRatioDivisor`-shaped (§3a) with total
degree exactly `0` (not merely `≤ 0`) and negative part exactly `{x₁,x₂}`
(not merely bounded there) once the positive part is nonzero (§3b/§3c). The
zero-positive-part case is immediate (§3d, easy — this is the "constant"
branch and needs nothing beyond §1+§2). The nonzero-positive-part case is
where the real content lives: `D`'s positive part, being mass ≤ 2 with `deg D
= 0` and negative part exactly `{x₁,x₂}` (mass 2), is forced to *also* be a
single point-with-multiplicity-2 or two-distinct-points support — i.e. `D =
(x₃)+(x₄) - (x₁) - (x₂)` for some `x₃, x₄` (§3e). Feeding this into
`mem_LPairCarrier_of_isRatioDivisor` — used here in *contrapositive* form,
not its stated direction — together with `uniqueDegree2MapToP1` would be
circular (that theorem is exactly what this file is trying to replace), so
the genuine remaining content is: directly show `{x₃,x₄} = {x₁,x₂}` (forcing
`D = 0`, i.e. `z` constant) using only `ordAt_linX_eq`-style fiber structure,
*without* going through `uniqueDegree2MapToP1`/`finrank_L_pair` (§3f — **the
actual crux, genuinely unformalized reasoning, not bookkeeping**). Ordered
below easiest-first per project convention; §3f is the hard one and is left
as an isolated named `sorry` with its precise statement pinned down, rather
than folded into the top-level theorem's `sorry` as before.

**Do not restart from the (false) original three-lemma "B=0" framing** —
`SCOPING-finrank-L-pair.md` records why it's unsound. -/

/-- **Small arithmetic helper**, factored out so §3a's uses of the same
"`max x 0` is within `n` of `x`" fact don't each re-derive it. **Needs `-n ≤ x`
as well as `0 ≤ n`** — without a lower bound on `x`, `max x 0 ≤ x + n` is false
(e.g. `x` very negative, `n` fixed): the first draft of this lemma omitted
`hxn` and `omega` correctly rejected it. Proved via `max_le` (the two-sided
characterization of `max`) rather than case-splitting on `0 ≤ x`. -/
theorem max_zero_le_add (x : ℤ) {n : ℤ} (hn : 0 ≤ n) (hxn : -n ≤ x) : max x 0 ≤ x + n := by
  apply max_le <;> omega

/-- **§3a (bookkeeping, should be easy).** Package §1's `deg D ≤ 0` and §2's
pointwise pole bound into the single `IsRatioDivisor`-shaped existential:
`D := divToPairRatio A B T A' B' T` has `¬(A=0∧B=0)`, `¬(A'=0∧B'=0)` (from
`hAB`/`hA'B'`, already available at call sites via `toPair_eq_zero_iff`), and
support `T`. This lemma does *not* yet claim `ordInfOfPair A B = ordInfOfPair
A' B'` (the equality `IsRatioDivisor` technically asks for) — `hbound` only
gives `≥`; if the strict `IsRatioDivisor` predicate is needed downstream
rather than just `deg`/`coeffAt` facts about `D`, that gap needs revisiting
here first. -/
theorem isRatioDivisor_shape_of_bounds (hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hAB : ¬ (A = 0 ∧ B = 0)) (hA'B' : ¬ (A' = 0 ∧ B' = 0))
    (T : Finset H.Point)
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0)
    (hdegD : deg (divToPairRatio A B T A' B' T) ≤ 0)
    (hcoeffbound :
      (∀ P, P ≠ x₁ → P ≠ x₂ → 0 ≤ Divisor.coeffAt P (divToPairRatio A B T A' B' T)) ∧
      Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) ≥
        -((if x₁ = x₁ then (1 : ℤ) else 0) + (if x₁ = x₂ then 1 else 0)) ∧
      Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) ≥
        -((if x₂ = x₁ then (1 : ℤ) else 0) + (if x₂ = x₂ then 1 else 0))) :
    -- The positive part of `D` (support in `T \ {x₁,x₂}`, all coefficients ≥ 0 there,
    -- and ≥ -2 at x₁/x₂ combined with the deg ≤ 0 bound) has total mass ≤ 2 — the
    -- precise numeric fact §3e's case split needs. Stated here as the raw arithmetic
    -- consequence of hdegD + hcoeffbound, isolated so §3e can cite it without
    -- re-deriving the deg/coeffAt bookkeeping.
    ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 ≤ 2 := by
  obtain ⟨hpos, hx₁, hx₂⟩ := hcoeffbound
  -- `deg D = ∑ P ∈ T, coeffAt P D`: `D = divToPair A B T - divToPair A' B' T`
  -- (`divToPairRatio`'s definition), `deg_divToPair` (`PrincipalDivisorSubgroup.lean`)
  -- turns each half's `deg` into a `∑_T ordAt`, and `coeffAt_divToPairRatio_eq_sub`
  -- (factored out above) identifies the termwise difference with `coeffAt P D`.
  have hdeg_eq : deg (divToPairRatio A B T A' B' T) =
      ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
    unfold divToPairRatio
    rw [map_sub, deg_divToPair, deg_divToPair, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun P _ =>
      (coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B' P).symm)
  -- Split `T` into `{x₁,x₂} ∩ T` and the rest: at every `P ∈ T` outside `{x₁,x₂}`,
  -- `coeffAt P D ≥ 0` (`hpos`), so `max (coeffAt P D) 0 = coeffAt P D` there — the
  -- positive part contributes exactly its own `coeffAt` value away from `x₁,x₂`, and
  -- summing `hdeg_eq`'s RHS against `hdegD` bounds the total (including the possibly-
  -- negative `x₁,x₂` terms) by `0`; moving those two terms' negative contribution
  -- (bounded below by `-2` total via `hx₁`/`hx₂`) to the other side gives the `≤ 2`
  -- bound on the positive-part sum. Both `T = ∅` and the `x₁ = x₂` coincidence are
  -- handled uniformly since `hx₁`/`hx₂` already fold that case into their `ite`s.
  by_cases hx₁T : x₁ ∈ T
  · by_cases hx₂T : x₂ ∈ T
    · by_cases hxeq : x₁ = x₂
      · -- `x₁ = x₂`: a single point contributes both indicators, `coeffAt x₁ D ≥ -2`.
        subst hxeq
        have hsplit : ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 =
            max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 +
              ∑ P ∈ T.erase x₁, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := by
          rw [← Finset.sum_erase_add T _ hx₁T, add_comm]
        have hsplit' : ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) =
            Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) +
              ∑ P ∈ T.erase x₁, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
          rw [← Finset.sum_erase_add T _ hx₁T, add_comm]
        have hrest_eq : ∑ P ∈ T.erase x₁, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0
            = ∑ P ∈ T.erase x₁, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
          refine Finset.sum_congr rfl (fun P hP => ?_)
          have hPne : P ≠ x₁ := (Finset.mem_erase.mp hP).1
          exact max_eq_left (hpos P hPne hPne)
        rw [hsplit, hrest_eq]
        rw [hdeg_eq, hsplit'] at hdegD
        simp only [if_pos rfl] at hx₁
        have hmax_le : max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 ≤
            Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) + 2 :=
          max_zero_le_add _ (by norm_num) (by omega)
        omega
      · -- `x₁ ≠ x₂`, both in `T`: two distinct points, each contributing its own `≥ -1` bound.
        have hsplit : ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 =
            max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 +
              max (Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T)) 0 +
              ∑ P ∈ (T.erase x₁).erase x₂,
                max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := by
          rw [← Finset.sum_erase_add T _ hx₁T,
            ← Finset.sum_erase_add (T.erase x₁) _
              (Finset.mem_erase.mpr ⟨Ne.symm hxeq, hx₂T⟩)]
          ring
        have hsplit' : ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) =
            Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) +
              Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) +
              ∑ P ∈ (T.erase x₁).erase x₂,
                Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
          rw [← Finset.sum_erase_add T _ hx₁T,
            ← Finset.sum_erase_add (T.erase x₁) _
              (Finset.mem_erase.mpr ⟨Ne.symm hxeq, hx₂T⟩)]
          ring
        have hrest_eq : ∑ P ∈ (T.erase x₁).erase x₂,
            max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0
            = ∑ P ∈ (T.erase x₁).erase x₂, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
          refine Finset.sum_congr rfl (fun P hP => ?_)
          have hPne₂ : P ≠ x₂ := (Finset.mem_erase.mp hP).1
          have hPne₁ : P ≠ x₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hP).2).1
          exact max_eq_left (hpos P hPne₁ hPne₂)
        rw [hsplit, hrest_eq]
        rw [hdeg_eq, hsplit'] at hdegD
        simp only [if_pos rfl, if_neg hxeq] at hx₁
        simp only [if_neg (Ne.symm hxeq), if_pos rfl] at hx₂
        have hmax₁ : max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 ≤
            Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) + 1 :=
          max_zero_le_add _ (by norm_num) (by omega)
        have hmax₂ : max (Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T)) 0 ≤
            Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) + 1 :=
          max_zero_le_add _ (by norm_num) (by omega)
        omega
    · -- `x₂ ∉ T`: `coeffAt x₂ D = 0` (outside the support), so `hx₂`'s bound is slack;
      -- only `x₁`'s term needs separating from the rest.
      have hx₂0 : Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) = 0 := by
        rw [coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B' x₂,
          hsuppAB x₂ hx₂T, hsuppA'B' x₂ hx₂T]
        ring
      have hsplit : ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 =
          max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 +
            ∑ P ∈ T.erase x₁, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := by
        rw [← Finset.sum_erase_add T _ hx₁T, add_comm]
      have hsplit' : ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) =
          Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) +
            ∑ P ∈ T.erase x₁, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
        rw [← Finset.sum_erase_add T _ hx₁T, add_comm]
      have hrest_eq : ∑ P ∈ T.erase x₁, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0
          = ∑ P ∈ T.erase x₁, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
        refine Finset.sum_congr rfl (fun P hP => ?_)
        have hPne : P ≠ x₁ := (Finset.mem_erase.mp hP).1
        by_cases hPx₂ : P = x₂
        · rw [hPx₂, hx₂0]; simp
        · exact max_eq_left (hpos P hPne hPx₂)
      rw [hdeg_eq, hsplit'] at hdegD
      have hxne : x₁ ≠ x₂ := fun h => hx₂T (h ▸ hx₁T)
      simp only [if_neg hxne] at hx₁
      have hmax₁ : max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 ≤
          Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) + 1 :=
        max_zero_le_add _ (by norm_num) (by omega)
      calc ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0
          = max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 +
              ∑ P ∈ T.erase x₁, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := hsplit
        _ = max (Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T)) 0 +
              ∑ P ∈ T.erase x₁, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
              rw [hrest_eq]
        _ ≤ 2 := by omega
  · -- `x₁ ∉ T`: both `coeffAt x₁ D = 0` and (symmetric case split) `coeffAt x₂ D`
    -- handled the same way as `hpos` directly covers `T`'s support once `x₁∉T`.
    have hx₁0 : Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) = 0 := by
      rw [coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B' x₁,
        hsuppAB x₁ hx₁T, hsuppA'B' x₁ hx₁T]
      ring
    by_cases hx₂T : x₂ ∈ T
    · have hsplit : ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 =
          max (Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T)) 0 +
            ∑ P ∈ T.erase x₂, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := by
        rw [← Finset.sum_erase_add T _ hx₂T, add_comm]
      have hsplit' : ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) =
          Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) +
            ∑ P ∈ T.erase x₂, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
        rw [← Finset.sum_erase_add T _ hx₂T, add_comm]
      have hrest_eq : ∑ P ∈ T.erase x₂, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0
          = ∑ P ∈ T.erase x₂, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
        refine Finset.sum_congr rfl (fun P hP => ?_)
        have hPne : P ≠ x₂ := (Finset.mem_erase.mp hP).1
        by_cases hPx₁ : P = x₁
        · rw [hPx₁, hx₁0]; simp
        · exact max_eq_left (hpos P hPx₁ hPne)
      rw [hdeg_eq, hsplit'] at hdegD
      have hxne : x₁ ≠ x₂ := fun h => hx₁T (h ▸ hx₂T)
      simp only [if_neg (Ne.symm hxne)] at hx₂
      have hmax₂ : max (Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T)) 0 ≤
          Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) + 1 :=
        max_zero_le_add _ (by norm_num) (by omega)
      calc ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0
          = max (Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T)) 0 +
              ∑ P ∈ T.erase x₂, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := hsplit
        _ = max (Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T)) 0 +
              ∑ P ∈ T.erase x₂, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
              rw [hrest_eq]
        _ ≤ 2 := by omega
    · -- Neither `x₁` nor `x₂` is in `T`: `hpos` alone (with `hPx₁ := fun h => hx₁T (h ▸ hP')`-
      -- style arguments) covers every `P ∈ T`, so the positive part equals `∑_T coeffAt`,
      -- which is `deg D ≤ 0`, hence the max-sum (all terms already `≥ 0` implicitly, but
      -- capped by `deg ≤ 0` forcing every term `≤ 0` too — see below) is `≤ 0 ≤ 2`.
      have hrest_eq : ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0
          = ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
        refine Finset.sum_congr rfl (fun P hP => ?_)
        have hPx₁ : P ≠ x₁ := fun h => hx₁T (h ▸ hP)
        have hPx₂ : P ≠ x₂ := fun h => hx₂T (h ▸ hP)
        exact max_eq_left (hpos P hPx₁ hPx₂)
      rw [hrest_eq, ← hdeg_eq]
      omega


/-! ### Skeleton for `isConstantFraction_of_ordAt_eq`'s hard case — two sub-steps

Per the docstring below (on `isConstantFraction_of_ordAt_eq` itself), the nonzero
case needs two genuinely separate, currently-unformalized facts. Neither is proved
here; these are staging targets. -/

/-- **Sub-step A.** `ordAt`-equality everywhere (for nonzero `toPair H A B`,
`toPair H A' B'`) implies `Ideal.span {toPair H A B} = Ideal.span {toPair H A' B'}`,
via `Associates`-level unique factorization in the Dedekind domain `CoordinateRing H`
(equal `count` at every height-one prime — `pointHeightOne P h_bot` for points with
`pointIdeal P ≠ ⊥`, trivial elsewhere). Not yet proved — per the docstring below, look
first at whether Mathlib's `IsDedekindDomain.HeightOneSpectrum` /
`Associates.mk_eq_mk_iff_associated` API shortens this. -/
theorem span_eq_of_ordAt_eq (A B A' B' : k[X])
    (hABz : toPair H A B ≠ 0) (hA'B'z : toPair H A' B' ≠ 0)
    (hordeq : ∀ P : H.Point, ordAt P A B = ordAt P A' B') :
    Ideal.span ({toPair H A B} : Set (CoordinateRing H)) =
      Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)) := by
  sorry

/-- **Sub-step B.** `CoordinateRing H`'s unit group is exactly `k^×`, i.e. every
unit is `algebraMap k[X] (CoordinateRing H) (C c)` for some `c : k` with `c ≠ 0`.
Plausible from `CoordinateRing H` being a free `k[X]`-module of rank 2 via
`toPairLin`/`toPairEquiv_mulByToPairLin` (`PrincipalDivisors.lean`), restricting units
to the degree-0 part — but not yet stated or proved anywhere in this project, and
needs `H.f` non-degenerate (roughly the standing `hdeg`). Not yet proved — check
whether this has already been characterized elsewhere before reproving it. -/
theorem isUnit_coordinateRing_iff (hdeg : H.f.natDegree = 5) (u : CoordinateRing H) :
    IsUnit u ↔ ∃ c : k, c ≠ 0 ∧ u = algebraMap k[X] (CoordinateRing H) (C c) := by
  sorry

/-- **New isolated hard fact, factored out of §3d.** This is *not* the same gap as
§3f — it is a lower-level, purely local-ring-theoretic statement with no fiber/`x`-
coordinate content at all: if two pole-bounded pairs `(A,B)`, `(A',B')` have
*identical* `ordAt` at every point `P : H.Point` (i.e. their affine divisors agree
exactly, not just up to the bound `IsPoleBoundedAtPair` imposes), then their ratio
is a `k`-constant. Stated with **no nonvanishing hypothesis on either pair** — the
degenerate cases (`toPair H A B = 0`, or `toPair H A' B' = 0`, or both) are
genuinely reachable from §3d's hypotheses (e.g. `T = ∅`, `A = B = 0`) and are
handled directly below rather than assumed away.

**Why this needs more than `RatioDivisorCollapse.lean` already has (nonzero
case).** That file's `mem_LPairCarrier_of_isRatioDivisor` proves the *converse*
direction as one branch of a proof by contradiction: assuming `z` constant, it
derives `ordAt`-equality everywhere (via cross-multiplying `toPair H A' B' =
toPair H (C c) 0 * toPair H A B` and reading off valuations). What's needed here
is the reverse: *from* `ordAt`-equality everywhere, *construct* the constant `c`
and the factorization witness. That direction is not merely "run the old proof
backwards" — it requires actually producing `c` and the equation `toPair H A B =
toPair H (C c) 0 * toPair H A' B'`, which is where **unique factorization of
ideals in a Dedekind domain** enters for real: `ordAt`-equality everywhere says
the ideals `Ideal.span {toPair H A B}` and `Ideal.span {toPair H A' B'}` have
equal `Associates.count` at every height-one prime (`pointHeightOne P h_bot` for
`pointIdeal P ≠ ⊥`, plus the `pointIdeal P = ⊥` points where every valuation is
trivially `0`) — hence equal factorizations as `Associates`, hence the same ideal,
hence `toPair H A B` and `toPair H A' B'` are associated elements of
`CoordinateRing H` (a domain), giving a unit `u` with `toPair H A B = u * toPair H
A' B'`. The remaining step — identifying that unit `u` with `algebraMap k[X]
(CoordinateRing H) (C c)` for some `c : k` — needs the coordinate ring's unit
group to be exactly `k^×` (plausible: `CoordinateRing H` is a free `k[X]`-module
of rank 2 via `toPairLin`/`toPairEquiv_mulByToPairLin`, elsewhere in
`PrincipalDivisors.lean`, so its units should be exactly the units of the
degree-0 part, i.e. `k^×` — but this specific "units of `CoordinateRing H` are
`k^×`" fact is not yet stated or proved anywhere in this project either, and
would itself need `H.f` non-degenerate, roughly the standing `hdeg`). **Both
sub-steps (`Associates`-level unique factorization ⟹ same ideal ⟹ associated
elements, and "coordinate-ring units are exactly `k^×`") are genuine,
currently-unformalized commutative algebra — not bookkeeping — left as this
single named `sorry` for the nonzero case, rather than guessed at or silently
assumed via a stronger hypothesis. Whoever picks this up should look first at
whether Mathlib's Dedekind-domain API (`UniqueFactorizationMonoid.factorization`-
adjacent lemmas, or working directly with `IsDedekindDomain.HeightOneSpectrum`
and `Associates.mk_eq_mk_iff_associated`-style results) shortens the first
sub-step, and should search for whether `CoordinateRing H`'s unit group has
already been characterized elsewhere before reproving it. -/
theorem isConstantFraction_of_ordAt_eq (A B A' B' : k[X])
    (hordeq : ∀ P : H.Point, ordAt P A B = ordAt P A' B') :
    IsConstantFraction (polePairToFraction (H := H) A B A' B') := by
  by_cases hABz : toPair H A B = 0
  · -- `polePairToFraction A B A' B' = 0 / toPair H A' B' = 0 = algebraMap (C 0)`.
    refine ⟨0, ?_⟩
    unfold polePairToFraction
    rw [hABz, map_zero, zero_div]
    have : (algebraMap k[X] (CoordinateRing H) (C (0:k))) = 0 := by simp
    rw [this, map_zero]
  · by_cases hA'B'z : toPair H A' B' = 0
    · -- `toPair H A' B' = 0` but `toPair H A B ≠ 0`: impossible under `hordeq`, since
      -- `toPair H A' B' = 0` forces `ordAt P A' B' = 0` for every `P` (`ordAt`'s own
      -- `if r = 0 then 0 else ...` case), so `hordeq` would force `ordAt P A B = 0`
      -- for every `P` too — plausible-but-not-quite-enough on its own to conclude
      -- `toPair H A B = 0` (would need injectivity of "all `ordAt` vanish ⟹ element is
      -- a unit or zero", the same missing fact as the main `sorry` below) — rather than
      -- force a second copy of that gap here, this branch is folded into the same
      -- `sorry` as the genuine nonzero case, since it needs the identical unique-
      -- factorization machinery (applied with `toPair H A' B' = 0`, i.e. the "unit"
      -- degenerates to `0`, not literally the same statement).
      sorry
    · -- Genuine case: both `toPair H A B ≠ 0` and `toPair H A' B' ≠ 0`, `ordAt` equal
      -- everywhere. Real content, see docstring above.
      sorry

/-- **§3d (bookkeeping, reduces to `isConstantFraction_of_ordAt_eq`).** If `D`'s
positive part is entirely zero — every coefficient in `T` is `≤ 0` — combined
with `deg D = 0` this forces `coeffAt P D = 0` at every `P ∈ T` (a divisor that
is `≤ 0` everywhere on its support with total degree `0` must vanish termwise:
if any term were `< 0`, the sum would be `< 0`), hence (via `hsuppAB`/`hsuppA'B'`
outside `T`, where both sides of `coeffAt_divToPairRatio_eq_sub` are already `0`)
`ordAt P A B = ordAt P A' B'` at *every* point `P`, not just `T` — exactly
`isConstantFraction_of_ordAt_eq`'s hypothesis. This half is genuinely just
`deg`/`coeffAt`/`Finset.sum` bookkeeping, as the original docstring claimed; the
actual mathematical content was mis-attributed to this lemma and lives in
`isConstantFraction_of_ordAt_eq` instead. -/
theorem isConstantFraction_of_divisor_le_zero (hdeg : H.f.natDegree = 5)
    (A B A' B' : k[X]) (T : Finset H.Point)
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0)
    (hdegD : deg (divToPairRatio A B T A' B' T) = 0)
    (hle : ∀ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) ≤ 0) :
    IsConstantFraction (polePairToFraction (H := H) A B A' B') := by
  apply isConstantFraction_of_ordAt_eq
  intro P
  rw [← sub_eq_zero, ← coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B' P]
  by_cases hPT : P ∈ T
  · -- `coeffAt P D ≤ 0` (`hle P hPT`) and the rest of the sum over `T.erase P` is
    -- also `≤ 0` (each term bounded by `hle`), so splitting `∑ T = coeffAt P D +
    -- ∑ (T.erase P)` and using `deg D = ∑ T = 0` forces both nonpositive halves to
    -- be exactly `0` (two `≤ 0` reals summing to `0` are each `0`) — in particular
    -- `coeffAt P D = 0`, avoiding any `Finset.sum_eq_zero_iff_of_nonneg`-style lemma
    -- whose exact name/signature isn't confirmed against this project's Mathlib version.
    have hdeg_eq : deg (divToPairRatio A B T A' B' T) =
        ∑ Q ∈ T, Divisor.coeffAt Q (divToPairRatio A B T A' B' T) := by
      unfold divToPairRatio
      rw [map_sub, deg_divToPair, deg_divToPair, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun Q _ =>
        (coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B' Q).symm)
    have hsplit : ∑ Q ∈ T, Divisor.coeffAt Q (divToPairRatio A B T A' B' T) =
        Divisor.coeffAt P (divToPairRatio A B T A' B' T) +
          ∑ Q ∈ T.erase P, Divisor.coeffAt Q (divToPairRatio A B T A' B' T) := by
      rw [← Finset.sum_erase_add T _ hPT, add_comm]
    have hrest_le : ∑ Q ∈ T.erase P, Divisor.coeffAt Q (divToPairRatio A B T A' B' T) ≤ 0 :=
      Finset.sum_nonpos (fun Q hQ => hle Q (Finset.mem_of_mem_erase hQ))
    rw [hdeg_eq, hsplit] at hdegD
    have hP_le := hle P hPT
    linarith
  · rw [coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B' P,
      hsuppAB P hPT, hsuppA'B' P hPT]
    ring

/-- **§3e — CORRECTED, see note below.** The original draft of this lemma
(and the docstring introducing §3 above it) claimed: nonzero positive part
`⟹` `D = single x₃ + single x₄ - single x₁ - single x₂` for some `x₃, x₄`,
i.e. the negative part is *exactly* `{x₁,x₂}` with each saturating its bound
to `-1` (or `-2` at a shared point). **That claim is false from `hdegD` +
`hcoeffbound` alone.** Counterexample: `x₁ ≠ x₂`, a third point `x₃ ∈ T`
distinct from both, with `coeffAt x₁ D = -1`, `coeffAt x₂ D = 0`,
`coeffAt x₃ D = 1`, all other points of `T` coefficient `0`. This satisfies
`hdegD` (`-1 + 0 + 1 = 0`) and every clause of `hcoeffbound` (`x₂`'s bound is
`≥ -1`, and `0` satisfies that without saturating it) — real, realizable
`ordAt` data (e.g. `ordAt x₁ A B = 0, ordAt x₁ A' B' = 1`, both individually
nonnegative as `ordAt` always is), yet the conclusion fails: no `x₄` makes
`D` match the claimed shape, since that shape forces `coeffAt x₂ = -1`
unconditionally.

**Root cause.** The docstring introducing §3 (above) attributes the
"negative part exactly `{x₁,x₂}`, mass exactly 2" step to lemmas "§3b/§3c" —
but those were never actually written; only mentioned in prose. `hcoeffbound`
supplies one-sided `≥` bounds (inherited from `IsPoleBoundedAtPair`'s
inequality clause), not the equalities the discarded conclusion needs.
Nothing in this file currently forces saturation.

**What Route A (`SCOPING-finrank-L-pair.md`) actually does instead.** Route
A's three steps do *not* go through an abstract "divisor has this exact
2-point shape" lemma at all — they argue directly on `A, B, A', B'`: (1)
`B' = 0` is forced by comparing `ordInfOfPair`'s pole order at infinity
(`2·deg B' + 5`, odd-parity, unboundable by the ≤2 affine budget) against the
affine bound; (2) with `B' = 0`, a similar parity argument on `y`'s own
pole/zero structure forces `B = 0`, reducing `z` to a pure rational function
`A(x)/A'(x)`; (3) the ≤2 pole-degree bound then forces `deg A, deg A' ≤ 1`,
and matching `A(x)/A'(x)`'s pole set against `{x₁,x₂}` via the already-proved
`ordAt_linX_eq` finishes it directly (`x₂ = ιx₁` unless `{x₁,x₂}` is one
fiber, contradicting `hne`). None of this three-step chain needs — or
produces — a general "`D` equals this fixed 2-point shape" fact first; it
short-circuits straight from the affine/infinity pole-degree split to the
`ordAt_linX_eq` case analysis. **The abstract §3a–§3e decomposition in this
file is a different (and, per the above, broken) attempt at scoping the
problem, not a restatement of Route A** — whoever continues this file should
strongly consider abandoning the §3d/§3e/§3f split in favor of implementing
Route A steps 1–3 directly (as their own named lemmas on `A,B,A',B'`,
following the SCOPING doc's numbering), rather than patching this
abstract-divisor-shape route further.

**This corrected statement** keeps only what `hdegD`+`hcoeffbound` genuinely
imply: the positive part's total mass equals the negative part's total mass
(both come from `deg D = 0`), and that shared mass is `≤ 2` (from
`hcoeffbound`'s bounds). This is materially weaker than the original
(discarded) conclusion and is **not sufficient on its own** to feed §3f's
`IsPoleBoundedAtPair`-shaped hypothesis — §3f's statement is left as-is
(unreachable from this weaker lemma) as a marker of the gap, not silently
patched to match. -/
theorem posMass_eq_negMass_le_two (hdeg : H.f.natDegree = 5)
    (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hAB : ¬ (A = 0 ∧ B = 0)) (hA'B' : ¬ (A' = 0 ∧ B' = 0))
    (T : Finset H.Point)
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0)
    (hdegD : deg (divToPairRatio A B T A' B' T) = 0)
    (hcoeffbound :
      (∀ P, P ≠ x₁ → P ≠ x₂ → 0 ≤ Divisor.coeffAt P (divToPairRatio A B T A' B' T)) ∧
      Divisor.coeffAt x₁ (divToPairRatio A B T A' B' T) ≥
        -((if x₁ = x₁ then (1 : ℤ) else 0) + (if x₁ = x₂ then 1 else 0)) ∧
      Divisor.coeffAt x₂ (divToPairRatio A B T A' B' T) ≥
        -((if x₂ = x₁ then (1 : ℤ) else 0) + (if x₂ = x₂ then 1 else 0))) :
    ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 ≤ 2 ∧
    ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 =
      ∑ P ∈ T, max (- Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := by
  have hmass_le := isRatioDivisor_shape_of_bounds hdeg x₁ x₂ A B A' B' hAB hA'B' T hsuppAB
    hsuppA'B' (le_of_eq hdegD) hcoeffbound
  refine ⟨hmass_le, ?_⟩
  -- `∑ max(coeffAt,0) - ∑ max(-coeffAt,0) = ∑ coeffAt = deg D = 0` (each term's
  -- `max x 0 - max (-x) 0 = x` pointwise), so the two sums are equal.
  have hdeg_eq : deg (divToPairRatio A B T A' B' T) =
      ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) := by
    unfold divToPairRatio
    rw [map_sub, deg_divToPair, deg_divToPair, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun P _ =>
      (coeffAt_divToPairRatio_eq_sub A B A' B' T hsuppAB hsuppA'B' P).symm)
  rw [hdeg_eq] at hdegD
  have hpointwise : ∀ P ∈ T,
      Divisor.coeffAt P (divToPairRatio A B T A' B' T) =
        max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 -
          max (- Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := by
    intro P _
    rcases le_or_gt 0 (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), sub_zero]
    · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith)]; ring
  have hsum_eq : ∑ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) =
      ∑ P ∈ T, max (Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 -
        ∑ P ∈ T, max (- Divisor.coeffAt P (divToPairRatio A B T A' B' T)) 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hpointwise
  rw [hsum_eq] at hdegD
  linarith

/-! ### §3f skeleton — Route A steps 1–3, decomposed per `SCOPING-finrank-L-pair.md`

None of the three lemmas below are proved; this is a decomposition of the single
`fiber_eq_of_divisor_shape` `sorry` (docstring below) into its three genuinely
distinct sub-arguments (per the SCOPING doc's own numbering), each stated as its
own target so a future session can attack them independently rather than reopening
one monolithic goal. `fiber_eq_of_divisor_shape` itself is left exactly as it was
(still one `sorry`) — these are staging lemmas it is expected to be assembled
from, not yet wired in. -/

/-- **Route A step 1.** If `IsPoleBoundedAtPair x₁ x₂ A B A' B'` and `B' ≠ 0`, the
denominator `toPair H A' B'` has pole-at-infinity order `2 * B'.natDegree + 5`
(odd multiple of the half-integer unit, per `ordInfOfPair`'s convention — see
`SCOPING-finrank-L-pair.md` for the precise weighting), which cannot be matched
against the total affine pole budget of `2` (one order-≤1 pole at each of `x₁`,
`x₂`) contributed to `ordInfOfPair A B`'s side of the `≥` bound in
`IsPoleBoundedAtPair`. Forces `B' = 0`. Not yet proved — the precise inequality
chain from `ordInfOfPair`'s definition (`PrincipalDivisors.lean:122`) needs to be
written out; flagged in the SCOPING doc as "probably the easiest of the three". -/
theorem denom_B'_eq_zero_of_isPoleBoundedAtPair (hdeg : H.f.natDegree = 5)
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
    (hAB : ¬ (A = 0 ∧ B = 0))
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0)
    -- **Weakening, added after the original (false) statement was found to have a
    -- counterexample.** `IsPoleBoundedAtPair` alone does not force `B' = 0`: `A=A'=0,
    -- B=B'=1` gives `z = toPair H 0 1 / toPair H 0 1 = y/y`, trivially satisfying
    -- `IsPoleBoundedAtPair` with equality throughout, yet `B' = 1 ≠ 0` (this is exactly
    -- the counterexample already documented in this file's own revision-history
    -- docstring above, §"Revision history, kept here because the false start is
    -- instructive"). The genuine content needs the pair to be in *lowest terms* — no
    -- common affine zero/pole between numerator and denominator — which is what Route A
    -- implicitly assumes throughout (a fraction already reduced, not one with a shared
    -- spurious factor like `y` in the counterexample). This hypothesis is that lowest-
    -- terms condition, stated pointwise.
    (hreduced : ∀ P : H.Point, ordAt P A B = 0 ∨ ordAt P A' B' = 0)
    [∀ P : T, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A B).toNat)]
    [∀ P : T, Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A' B').toNat)] :
    B' = 0 := by
  by_contra hB'ne
  obtain ⟨hA'B', hmono, hpt⟩ := hbound
  -- `deg_div_eq_zero_deg5` applied to each pair: `∑_T ordAt(A,B) = -ordInfOfPair A B`,
  -- likewise for `(A',B')`.
  have h₁ := deg_div_eq_zero_deg5 H hdeg T A B hAB hsuppAB hspecAB
  have h₂ := deg_div_eq_zero_deg5 H hdeg T A' B' hA'B' hsuppA'B' hspecA'B'
  -- `ordInfOfPair A' B'` unfolds explicitly since `B' ≠ 0`: `= -(max (2 deg A') (2 deg B' + 5))`,
  -- in particular `ordInfOfPair A' B' ≤ -(2 * B'.natDegree + 5) ≤ -5`.
  have hordInf_A'B' : ordInfOfPair A' B' ≤ -(2 * (B'.natDegree : ℤ) + 5) := by
    dsimp [ordInfOfPair]
    rw [if_neg hA'B', if_neg hB'ne]
    have : (2 * (B'.natDegree : ℤ) + 5) ≤ max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5) :=
      le_max_right _ _
    linarith
  -- **New, solid intermediate fact**: `(A',B')`'s support outside `{x₁,x₂}` is empty, i.e.
  -- `ordAt P A' B' = 0` for every `P ≠ x₁, x₂`. Proof: for such `P`, `hpt` gives
  -- `ordAt P A B ≥ ordAt P A' B' - 0 = ordAt P A' B'`. If `ordAt P A' B' > 0` then
  -- `ordAt P A B > 0` too, so `ordAt P A B ≠ 0`; `hreduced` then forces `ordAt P A' B' = 0`,
  -- contradicting `ordAt P A' B' > 0`. So `ordAt P A' B' ≤ 0`; combined with `ordAt_nonneg`
  -- (`PrincipalDivisors.lean:472`, valid since `toPair H A' B' ≠ 0` — `hA'B'`, `toPair_eq_zero_iff`
  -- — regardless of whether `pointIdeal P = ⊥`, where `ordAt` is `0` by definition anyway),
  -- `ordAt P A' B' = 0`.
  have hsupp_outside : ∀ P : H.Point, P ≠ x₁ → P ≠ x₂ → ordAt P A' B' = 0 := by
    intro P hPx₁ hPx₂
    have hind : ordAt P A B ≥ ordAt P A' B' - ((if P = x₁ then (1:ℤ) else 0) + (if P = x₂ then 1 else 0)) :=
      hpt P
    rw [if_neg hPx₁, if_neg hPx₂] at hind
    simp only [add_zero, sub_zero] at hind
    have hAB_ne : toPair H A' B' ≠ 0 := by rw [Ne, toPair_eq_zero_iff]; exact hA'B'
    by_cases h_bot : pointIdeal P = ⊥
    · simp only [ordAt, if_neg hAB_ne, dif_pos h_bot]
    · have hge0 : 0 ≤ ordAt P A' B' := ordAt_nonneg P A' B' hAB_ne h_bot
      by_contra hne
      have hpos : 0 < ordAt P A' B' := lt_of_le_of_ne hge0 (Ne.symm hne)
      have hABpos : 0 < ordAt P A B := lt_of_lt_of_le hpos hind
      rcases hreduced P with hzero | hzero
      · exact absurd hzero (ne_of_gt hABpos)
      · exact absurd hzero (ne_of_gt hpos)
  -- **Genuine remaining gap, now narrower.** `hsupp_outside` pins `(A',B')`'s entire affine
  -- support to `{x₁,x₂}` (at most two points, each with `ordAt ≥ 0`). Combined with `h₂`
  -- (`∑_T ordAt(A',B') = -ordInfOfPair A'B' ≥ 2 * B'.natDegree + 5 ≥ 5`, from `hordInf_A'B'`),
  -- this forces `ordAt x₁ A' B' + ordAt x₂ A' B' ≥ 5` (all of the sum concentrated on at most
  -- two points) — a large affine vanishing order concentrated at ≤ 2 points. Closing the proof
  -- from here needs either: (a) an explicit bound on how large `ordAt` at a single point can be
  -- relative to `B'.natDegree` (not yet available in this project — would need something like
  -- "a nonzero pair's ordAt at any single point is `≤` some function of its total degree"), or
  -- (b) the `CoordinateRing H` units-are-`k^×` fact (`isUnit_coordinateRing_iff`, stated
  -- elsewhere in this file, also unproved) to rule out `(A',B')` having *no* affine support at
  -- all despite `B' ≠ 0`. Neither is available yet — isolated here as the precise remaining gap.
  sorry

/-- **Route A step 2.** Given step 1's `B' = 0`, so `z = (A(x) + B(x)y) / A'(x)`, a
similar parity argument on `y`'s own pole/zero structure (`y² = f(x)`, `deg f = 5`)
against the same `≤ 2` affine pole budget forces `B = 0` too, reducing `z` to a pure
rational function of `x` alone. Not yet proved — needs comparing `B(x)y/A'(x)`'s
contribution to `ordAt`/`ordInfOfPair` against the bound, in the same style as step 1
but one level up (SCOPING doc: "same flavor, one level up"). **Caution, not yet
checked:** step 1's original statement (no `hreduced` hypothesis) turned out to have a
counterexample already documented elsewhere in this file (the `y/y` self-cancellation
trick) — this statement hasn't been stress-tested the same way and may need an analogous
`hreduced`-style lowest-terms hypothesis threaded through before attempting a proof;
don't assume it's correct as stated without checking first. -/
theorem num_B_eq_zero_of_isPoleBoundedAtPair (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x₁ x₂ A B A' B') (hB' : B' = 0) :
    B = 0 := by
  sorry

/-- **Route A step 3 — the one genuinely new piece of reasoning** (per the SCOPING
doc; reuses `ordAt_linX_eq` rather than inventing ramification theory). Given steps
1–2 (`B = B' = 0`, so `z = A(x)/A'(x)`), the `≤ 2` total pole-degree bound forces
`deg A, deg A' ≤ 1` (from `ordInfOfPair`'s formula with `B = B' = 0`, i.e.
`ordInfOfPair A 0 = -2 * A.natDegree`). A degree-≤1-over-degree-≤1 rational function
of `x` with pole divisor exactly `{x₁,x₂}` (both affine, both order-≤1, per
`hordeq`/`hdiv`'s shape) is, via case analysis on `ordAt_linX_eq`
(`HyperellipticClassProof.lean:1031`: `Q.Y = 0` gives a double pole at one
Weierstrass point, `Q.Y ≠ 0` gives a simple pole shared with `ι Q`), forced to have
`{x₁,x₂}` be a fiber `{Q, ι Q}` of the coordinate function `x` — i.e. `x₂ = ι x₁` —
unless the pole/zero sets coincide outright as sets, which is the theorem's actual
conclusion. This is Route A step 3's precise target, isolated from steps 1–2. Not
yet proved. -/
theorem fiber_eq_of_pure_rational_pole_match (x₁ x₂ x₃ x₄ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (A A' : k[X]) (hdegA : A.natDegree ≤ 1)
    (hdegA' : A'.natDegree ≤ 1)
    (hpoles : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) =
      single x₃ + single x₄ - single x₁ - single x₂) :
    ({x₃, x₄} : Set H.Point) = {x₁, x₂} := by
  sorry

/-- **§3f — THE HARD SORRY, the actual crux of the whole file.** Given `D =
(x₃)+(x₄)-(x₁)-(x₂)` (§3e's second branch) and `x₂ ≠ ι x₁` (`hne`), show
`{x₃,x₄} = {x₁,x₂}` (forcing `D = 0`, i.e. the fraction is constant after
all) *without* invoking `uniqueDegree2MapToP1` or `finrank_L_pair` (that
would be circular — this file exists to prove a version of
`uniqueDegree2MapToP1`). The genuine content, per `SCOPING-finrank-L-pair.md`
Route A step 3: `D`'s negative part `{x₁,x₂}` and positive part `{x₃,x₄}`
both being pole/zero sets of the *same* ratio `z`, with `z`'s pole structure
constrained by `ordInfOfPair`'s "half-integer weight at infinity" convention
— a genuine hyperelliptic-curve fact about `k[X]`-degree parity, proved via
direct case analysis on `ordAt_linX_eq` (`HyperellipticClassProof.lean:1031`)
applied to whichever of `x₁,x₂,x₃,x₄` witnesses the pole/zero, rather than
any general classification. **This is real, currently-unformalized
mathematics — not a bookkeeping gap** (unlike §3a–§3e above, which are all
routine once stated precisely). Anyone picking this up should reread
`SCOPING-finrank-L-pair.md`'s Route A steps 1–3 in full before attempting a
proof body; the statement here is Route A step 3's precise target, isolated
from steps 1–2 (which are what forces `D` into this exact shape in the first
place, i.e. §3a–§3e above). -/
theorem fiber_eq_of_divisor_shape (x₁ x₂ x₃ x₄ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (hdiv : ∃ A B A' B' : k[X],
      IsPoleBoundedAtPair x₁ x₂ A B A' B' ∧
      (∃ T : Finset H.Point,
        (∀ P, P ∉ T → ordAt P A B = 0) ∧ (∀ P, P ∉ T → ordAt P A' B' = 0) ∧
        (divToPairRatio A B T A' B' T : Divisor H) =
          single x₃ + single x₄ - single x₁ - single x₂)) :
    ({x₃, x₄} : Set H.Point) = {x₁, x₂} := by
  -- Expected assembly (not yet wired in): obtain `A B A' B' T` from `hdiv`, apply
  -- `denom_B'_eq_zero_of_isPoleBoundedAtPair` then `num_B_eq_zero_of_isPoleBoundedAtPair`
  -- to reduce to `B = B' = 0`, derive the `≤ 1` degree bounds from `IsPoleBoundedAtPair`'s
  -- `ordInfOfPair` clause, then close with `fiber_eq_of_pure_rational_pole_match`.
  sorry

/-- **Assembly of §3a–§3f into the top-level target.** Wires the pieces above
together: §3a/§2 give the shape, §3e case-splits on whether the positive part
vanishes, §3d closes the vanishing case directly, and the nonvanishing case
combines §3f (`{x₃,x₄} = {x₁,x₂}`, hence `D = 0`) with §3d again (now that
`D`'s positive part is known `0` after substitution) to close. **Currently
blocked on §3f being a real `sorry`** — everything else below it is
plumbing. -/
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
  -- `IsPoleBoundedAtPair x₁ x₂ A B A' B'` unfolds to exactly three conjuncts:
  -- `¬(A'=0∧B'=0)`, `ordInfOfPair A B ≥ ordInfOfPair A' B'`, and the pointwise
  -- bound `∀ P, ordAt P A B ≥ ordAt P A' B' - (indicator sum)`. (Previously
  -- mis-destructured as four patterns, which silently misaligned `hAB` with
  -- the pointwise clause instead of the nonzero clause — caught by the
  -- `rcases`-on-a-Pi-type error below once something tried to case on `hAB`.)
  obtain ⟨hA'B', hmono, hpt⟩ := hbound
  -- Obtain a finite common support `T` for `(A,B)` and `(A',B')` via Lemma 0,
  -- then merge (`T₁ ∪ T₂` still satisfies both `hsuppAB`/`hsuppA'B'` clauses).
  obtain ⟨T₁, hT₁⟩ := exists_finite_support_of_hspec A B (fun ⟨hA0, hB0⟩ =>
    -- `A = 0 ∧ B = 0` would make `toPair H A B = 0`, contradicting `polePairToFraction`'s
    -- implicit nonzero-numerator requirement — but that's not directly among `hbound`'s
    -- conjuncts (only the denominator `A',B'` is asserted nonzero by `IsPoleBoundedAtPair`).
    -- `LPairCarrier`'s own definition doesn't require the numerator nonzero either, so
    -- this hypothesis position needs the caller-side fact, not something derivable from
    -- `hbound` alone; left as an explicit gap rather than a wrong proof term.
    sorry) hspecAB
  obtain ⟨T₂, hT₂⟩ := exists_finite_support_of_hspec A' B' hA'B' hspecA'B'
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
