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


variable {k : Type*} [Field k] (H : HyperellipticPolynomial k)
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

**Status (latest session): Route A steps 1–2 confirmed already fully proved**
(`denom_B'_eq_zero_of_isPoleBoundedAtPair`, `denom_ordInf_ge_neg_two`,
`num_B_eq_zero_of_isPoleBoundedAtPair` — no `sorry`, this session only touched
one dead `have` inside the first). **One easy sorry closed**:
`natDegree_eq_zero_of_mono` (pure `ordInfOfPair_right_zero` unfolding +
`omega`-shaped arithmetic, no new concepts). **Two sorries diagnosed as
unsound and left explicitly flagged rather than papered over** (per project
convention: false theorems get deleted/documented, not proved by hook or
crook):
- `ordInf_parity_mismatch` — **deleted**. `Odd (ordInfOfPair A' B')` for
  `B' ≠ 0` is false (counterexample: `A'=X^10, B'=1` gives `ordInfOfPair =
  -20`, even). It was also dead code: its output was fetched but never used
  in the one call site's closing `linarith`. `hB'`'s proof is unaffected
  (it already only needed `h_min`, the true weaker upper bound).
- `natDegree_eq_zero_of_ordInf_bound` — **left as `sorry`, now documented
  FALSE as literally stated** (`A'.natDegree = 1` is a genuine
  counterexample, not excluded by the hypotheses given). Traced to the real
  root cause: `constant_or_fiber_of_isPoleBoundedAtPair`'s "Main case" branch
  tries to prove *unconditional* constancy (`A'.natDegree = 0`) using only
  Route A steps 1–2's size bounds, but never invokes its own `hne`
  hypothesis — which is exactly what's needed (via Route A step 3,
  `fiber_eq_of_pure_rational_pole_match`, itself still `sorry`) to rule out
  the genuine `A'.natDegree = 1` fiber case. **This is the real remaining
  wiring gap in the "Main case" branch**, not a missing arithmetic lemma;
  whoever revisits should re-route `h_deg_A'` through Route A step 3 using
  `hne`, not attempt to strengthen `natDegree_eq_zero_of_ordInf_bound` itself
  (see its docstring in place for the full argument). This blocks the "Main
  case" branch the same way §3f already did — two names for adjacent parts
  of the same remaining gap.

**Status (latest session, continued): `h_deg_A'` rewired to actually use `hne`.**
Per a ChatGPT-assisted design pass (transcript on file), the false
`natDegree_eq_zero_of_ordInf_bound` (pure `ordInfOfPair`-size bound, no point
data, provably false — see its old docstring, now removed) has been replaced
by `natDegree_eq_zero_of_isPoleBoundedAtPair`, which takes `hne` and the
pointwise pole bound `hpt` (specialized to `B = B' = 0`) as real hypotheses.
`constant_or_fiber_of_isPoleBoundedAtPair`'s `h_deg_A'` step now calls this
new lemma instead, so `hne` is finally used somewhere in the "Main case"
branch (previously it appeared only in the theorem's signature). **The new
lemma is itself still `sorry`'d — this was a wiring/shape fix, not a proof of
new math.** ChatGPT's diagnosis (confirmed by hand): the natural next tool,
`fiber_eq_of_pure_rational_pole_match`, does NOT directly apply here, because
its hypothesis is an exact divisor *equation* with named witness points
`x₃,x₄`, while this call site only has a pointwise *inequality* plus finite
supports — no witnesses have been constructed. Closing
`natDegree_eq_zero_of_isPoleBoundedAtPair` needs either its own direct
`ordAt_linX_eq` case analysis (applied to the single point `Q'` with `Q'.X =
a'`, likely less work) or a new "pointwise bound ⟹ exact divisor equation"
bridge lemma before `fiber_eq_of_pure_rational_pole_match` can be invoked —
see the new lemma's docstring for the full writeup. **Side effect**:
`constant_or_fiber_of_isPoleBoundedAtPair` and `uniqueDegree2MapToP1_of_
elementary` now both take `hchar : (2:k) ≠ 0` and `hsf : Squarefree H.f` as
extra parameters (threaded through to the new lemma, which needs them for a
future `ordAt_linX_eq` call) — this was already anticipated in this file's
"Downstream callers... will need the same two hypotheses threaded through"
note above.

**Status (latest session, continued further): `fiber_eq_of_pure_rational_pole_match`
found FALSE as originally stated, now weakened.** A second AI (cross-checking the
first's diagnosis of Goals 1–5) found a genuine counterexample: because `divToPair`
sums only over the caller-chosen `Finset` `{x₁,x₂,x₃,x₄}`, setting `x₄ := x₂` (a legal
choice — `Finset` literals dedup) can silently truncate a fiber, letting `hpoles` hold
while the conclusion is false. Independently verified by hand against `divToPair`'s
definition (see the theorem's own docstring for the full counterexample) — this is a
real hole, not a false alarm. **Fix**: added two new hypotheses, `hclosed₁`/`hclosed₃`,
requiring the support set to be ι-closed at whichever root each side witnesses — true at
every anticipated call site, since those call sites already fix `{x₁,x₂,x₃,x₄}` as a
concrete set rather than an arbitrary superset. The mixed-sign/same-root branches
(Goals 1–4 in that session's numbering) don't need this fix at all — the same AI pass
also confirmed they close via the *already-proved* `ordAt_nonneg` (`PrincipalDivisors.
lean:472`, `toPair H A B ≠ 0 → pointIdeal P ≠ ⊥ → 0 ≤ ordAt P A B`), no new lemma
required, contrary to an initial suggestion to add a redundant `ordAt_linX_nonneg`.
Per project convention this was a "weaken first" situation, not a "delete" one — the
five branch `sorry`s are otherwise untouched and still open; only the theorem's
signature changed. `fiber_eq_of_divisor_shape` (still `sorry`, unaffected build-wise
since nothing calls this theorem yet) will need to supply `hclosed₁`/`hclosed₃` once
it's wired up — flagged in its own comment now.

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
`pointIdeal P ≠ ⊥`, trivial elsewhere).

**Corrected statement (ChatGPT-assisted design pass, this session): the original
version omitted the `hspecAB`/`hspecA'B'` hypotheses that every other lemma in this
file needing the same "which height-one primes can appear" fact already carries
(see `deg_divToPairRatio_le_zero`, `exists_finite_support_of_hspec` above, and
`denom_B'_eq_zero_of_isPoleBoundedAtPair` below for the identical pattern).**
`hordeq` alone only pins down agreement at *curve points*; `CoordinateRing H` is a
Dedekind domain with infinitely many height-one primes (it is a rank-2 free
extension of `k[X]`, itself having infinitely many primes), so without ruling out
disagreement at some non-curve prime, the conclusion does not follow from `hordeq`
alone. Adding the two `hspec`-shaped hypotheses (same shape as every sibling lemma)
repairs this: they say every height-one prime with positive multiplicity in either
span *is* some `pointIdeal P`, so comparing at curve points via `hordeq` really does
compare every prime that can possibly matter.

Proof strategy: for a height-one prime `v`, `Ideal.count_associates_factors_eq`
identifies `(Associates.mk v.asIdeal).count (Associates.mk I).factors` with
`Multiset.count v.asIdeal (normalizedFactors I)` (`I` either span); the two counts
agree because either (a) the count is `0` on both sides (no `hspec` witness, so `v`
isn't `pointIdeal P` for any `P`, hence contributes `0` to both — this needs a
*contrapositive* use of `hspec`, not just the forward direction, to rule out `v`
appearing in one factorization but not being covered by `hspec` for the other) or
(b) `v = pointHeightOne P h_bot` for some curve point `P`, where `ordAt_eq_count`
(`PrincipalDivisors.lean`) turns `hordeq P` directly into equal counts. Equal
`Multiset.count` at every element of `normalizedFactors` (both finite multisets,
by `hfinite_support`) gives equal multisets (`Multiset.ext`), hence equal
`Associates.mk`-image ideals (`normalizedFactors` reconstructs the ideal up to
associates for a nonzero ideal in a Dedekind domain), hence — since both ideals
here are already `Associates.mk`-represented via nonzero *principal* ideals in a
domain — the ideals themselves are equal. -/
theorem span_eq_of_ordAt_eq (A B A' B' : k[X])
    (hABz : toPair H A B ≠ 0) (hA'B'z : toPair H A' B' ≠ 0)
    (hspecAB : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (hspecA'B' : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (hordeq : ∀ P : H.Point, ordAt P A B = ordAt P A' B') :
    Ideal.span ({toPair H A B} : Set (CoordinateRing H)) =
      Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)) := by
  classical
  set I : Ideal (CoordinateRing H) := Ideal.span ({toPair H A B} : Set (CoordinateRing H))
    with hI_def
  set I' : Ideal (CoordinateRing H) := Ideal.span ({toPair H A' B'} : Set (CoordinateRing H))
    with hI'_def
  have hIne : I ≠ 0 := by
    rw [hI_def, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hABz
  have hI'ne : I' ≠ 0 := by
    rw [hI'_def, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hA'B'z
  have hIbot : I ≠ ⊥ := by rw [Ideal.zero_eq_bot] at hIne; exact hIne
  have hI'bot : I' ≠ ⊥ := by rw [Ideal.zero_eq_bot] at hI'ne; exact hI'ne
  -- Every `J` appearing in either factorization is prime and nonzero (standard for
  -- `normalizedFactors` of a nonzero ideal), so it packages into a genuine
  -- `HeightOneSpectrum` term, letting `hspecAB`/`hspecA'B'`/`ordAt_eq_count` apply.
  have hcount_eq : ∀ J : Ideal (CoordinateRing H),
      Multiset.count J (UniqueFactorizationMonoid.normalizedFactors I) =
        Multiset.count J (UniqueFactorizationMonoid.normalizedFactors I') := by
    intro J
    by_cases hJmem : J ∈ UniqueFactorizationMonoid.normalizedFactors I ∨
        J ∈ UniqueFactorizationMonoid.normalizedFactors I'
    · -- `J` is prime and nonzero either way (whichever side it's a member from),
      -- so it packages into `v : HeightOneSpectrum (CoordinateRing H)`.
      have hJprime : J.IsPrime ∧ J ≠ ⊥ := by
        rcases hJmem with hJ | hJ
        · exact ⟨((Ideal.mem_normalizedFactors_iff hIbot).mp hJ).1, by
            intro hJ0; rw [hJ0] at hJ
            exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors I hJ⟩
        · exact ⟨((Ideal.mem_normalizedFactors_iff hI'bot).mp hJ).1, by
            intro hJ0; rw [hJ0] at hJ
            exact UniqueFactorizationMonoid.zero_notMem_normalizedFactors I' hJ⟩
      set v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H) :=
        ⟨J, hJprime.1, hJprime.2⟩ with hv_def
      have hvJ : v.asIdeal = J := rfl
      -- `(Associates.mk v.asIdeal).count (Associates.mk I).factors` equals
      -- `Multiset.count v.asIdeal (normalizedFactors I)` on each side
      -- (`Ideal.count_associates_factors_eq`), so it suffices to compare those
      -- `Associates`-level counts, which reduce to `pointIdeal`/`ordAt_eq_count`
      -- comparisons via `hspecAB`/`hspecA'B'` when `v.asIdeal = pointIdeal P` for
      -- some `P`, and to `0 = 0` otherwise (neither `hspec` can witness `v`, so `v`
      -- has count `0` on both sides — contrapositive of `hspecAB`/`hspecA'B'`).
      have hcAB : (Associates.mk v.asIdeal).count (Associates.mk I).factors =
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) :=
        Ideal.count_associates_factors_eq hIne v.isPrime v.ne_bot
      have hcA'B' : (Associates.mk v.asIdeal).count (Associates.mk I').factors =
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I') :=
        Ideal.count_associates_factors_eq hI'ne v.isPrime v.ne_bot
      rw [hvJ] at hcAB hcA'B'
      rw [← hcAB, ← hcA'B']
      by_cases hPex : ∃ P, v.asIdeal = pointIdeal P
      · obtain ⟨P, hP⟩ := hPex
        by_cases h_bot : pointIdeal P = ⊥
        · -- `pointIdeal P = ⊥`: `v.asIdeal = pointIdeal P = ⊥` contradicts `v.ne_bot`.
          exact absurd (hP.trans h_bot) v.ne_bot
        · have hordP : ordAt P A B = ordAt P A' B' := hordeq P
          have hcountAB : ordAt P A B =
              ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) := by
            rw [hP, hI_def]; exact ordAt_eq_count P A B hABz h_bot
          have hcountA'B' : ordAt P A' B' =
              ((Associates.mk v.asIdeal).count (Associates.mk I').factors : ℤ) := by
            rw [hP, hI'_def]; exact ordAt_eq_count P A' B' hA'B'z h_bot
          rw [hcountAB, hcountA'B'] at hordP
          exact_mod_cast hordP
      · -- `v` is witnessed by neither `hspecAB` nor `hspecA'B'` (else `hPex` would
        -- hold), so both counts are forced to `0` by contraposition.
        have hzAB : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
          by_contra hne; exact hPex (hspecAB v hne)
        have hzA'B' : (Associates.mk v.asIdeal).count (Associates.mk I').factors = 0 := by
          by_contra hne; exact hPex (hspecA'B' v hne)
        rw [hzAB, hzA'B']
    · -- `J` is in neither factorization: both counts are `0` by
      -- `Multiset.count_eq_zero`.
      push_neg at hJmem
      rw [Multiset.count_eq_zero.mpr hJmem.1, Multiset.count_eq_zero.mpr hJmem.2]
  have hfactors_eq : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors I' := Multiset.ext'_iff.mpr hcount_eq
  calc I = (UniqueFactorizationMonoid.normalizedFactors I).prod :=
        (Ideal.prod_normalizedFactors_eq_self hIbot).symm
    _ = (UniqueFactorizationMonoid.normalizedFactors I').prod := by rw [hfactors_eq]
    _ = I' := Ideal.prod_normalizedFactors_eq_self hI'bot

/-- **Sub-step B — now proved.** `CoordinateRing H`'s unit group is exactly `k^×`.
**Route actually used** (found after re-reading `RiemannRochGenus2.lean`'s already-proved
`pairNorm_mul_of_toPair_mul`/`algebraMap_coordinateRing_injective`, rather than the free-
module/`toPairLin` route this docstring originally speculated about): if `u` is a unit with
inverse `v`, write both as `toPair`-pairs (`toPair_surjective_local`); `u * v = 1 = toPair H 1
0` (`toPair_one_zero`), so `pairNorm_mul_of_toPair_mul` gives `pairNorm H A B * pairNorm H A' B'
= pairNorm H 1 0 = 1` in `k[X]`, i.e. `pairNorm H A B` is a unit in `k[X]`, hence (`Polynomial.
isUnit_iff`) a nonzero constant `C c`. `natDegree_pairNorm_eq_neg_ordInfOfPair` then reads this
back as `ordInfOfPair A B = 0`, which (unfolding `ordInfOfPair`'s `max`) forces `B = 0` (else
the `2 deg B + 5 ≥ 5` branch would make the `max`, hence `ordInfOfPair`, nonzero) and
`A.natDegree = 0`, i.e. `u = toPair H A 0 = algebraMap (C (A.coeff 0))`; `A.coeff 0 ≠ 0` since
`u ≠ 0` (units are nonzero in a domain) and `toPair_eq_zero_iff`. -/
theorem isUnit_coordinateRing_iff (hdeg : H.f.natDegree = 5) (u : CoordinateRing H) :
    IsUnit u ↔ ∃ c : k, c ≠ 0 ∧ u = algebraMap k[X] (CoordinateRing H) (C c) := by
  constructor
  · intro hu
    obtain ⟨A, B, hAB⟩ := toPair_surjective_local H u
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨A', B', hA'B'⟩ := toPair_surjective_local H v
    have hprod : toPair H 1 0 = toPair H A B * toPair H A' B' := by
      rw [toPair_one_zero, ← hAB, ← hA'B']
      exact hv.symm
    have hnorm : pairNorm H 1 0 = pairNorm H A B * pairNorm H A' B' :=
      pairNorm_mul_of_toPair_mul (H := H) A B A' B' 1 0 hprod
    have hnorm_one : pairNorm H (1 : k[X]) 0 = 1 := by
      simp [pairNorm]
    rw [hnorm_one] at hnorm
    have hpairNorm_unit : IsUnit (pairNorm H A B) :=
      ⟨Units.mkOfMulEqOne _ _ hnorm.symm, rfl⟩
    -- `(A, B) ≠ (0, 0)`: otherwise `toPair H A B = 0`, contradicting `u`'s being a unit
    -- (units are nonzero in a nontrivial ring) via `hAB`.
    have hAB0 : ¬ (A = 0 ∧ B = 0) := by
      intro ⟨hA0, hB0⟩
      apply hu.ne_zero
      rw [hAB, hA0, hB0]
      simp [HyperellipticPolynomial.toPair]
    have hdeg_norm : ((pairNorm H A B).natDegree : ℤ) = - ordInfOfPair A B :=
      natDegree_pairNorm_eq_neg_ordInfOfPair H hdeg A B hAB0
    have hdeg_norm0 : (pairNorm H A B).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit
      hpairNorm_unit
    rw [hdeg_norm0] at hdeg_norm
    -- `hdeg_norm : (0:ℤ) = -ordInfOfPair A B`, i.e. `ordInfOfPair A B = 0`; unfold to pin
    -- down `B = 0` and `A.natDegree = 0`.
    have hordInf0 : ordInfOfPair A B = 0 := by omega
    have hB0 : B = 0 := by
      by_contra hBne
      dsimp [ordInfOfPair] at hordInf0
      rw [if_neg hAB0, if_neg hBne] at hordInf0
      have hle : (2 * (B.natDegree : ℤ) + 5) ≤
          max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5) := le_max_right _ _
      have hBnn : (0:ℤ) ≤ 2 * (B.natDegree : ℤ) := by positivity
      omega
    have hA_deg0 : A.natDegree = 0 := by
      dsimp [ordInfOfPair] at hordInf0
      rw [if_neg hAB0, if_pos hB0] at hordInf0
      have hAnn : (0:ℤ) ≤ 2 * (A.natDegree : ℤ) := by positivity
      rw [max_eq_left hAnn] at hordInf0
      omega
    refine ⟨A.coeff 0, ?_, ?_⟩
    · intro hzero
      apply hu.ne_zero
      rw [hAB, hB0]
      have hcA : A = Polynomial.C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hA_deg0
      rw [hcA, hzero, Polynomial.C_0]
      simp [HyperellipticPolynomial.toPair]
    · rw [hAB, hB0]
      have hcA : A = Polynomial.C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hA_deg0
      rw [hcA]
      simp [HyperellipticPolynomial.toPair]
  · rintro ⟨c, hc, rfl⟩
    have hCc_inv_poly : (C c : k[X]) * C c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    have hCc_inv : algebraMap k[X] (CoordinateRing H) (C c) *
        algebraMap k[X] (CoordinateRing H) (C c⁻¹) = 1 := by
      rw [← map_mul, hCc_inv_poly, map_one]
    exact ⟨Units.mkOfMulEqOne _ _ hCc_inv, rfl⟩

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
theorem isConstantFraction_of_ordAt_eq (hdeg : H.f.natDegree = 5) (A B A' B' : k[X])
    (hspecAB : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (hspecA'B' : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
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
    · -- **Now proved (ChatGPT-assisted, this session): this branch doesn't need
      -- `hordeq` or the unique-factorization machinery at all.** `toPair H A' B' = 0`
      -- makes `polePairToFraction`'s *denominator* vanish, so the whole fraction is
      -- `0` by `FractionRing`'s (in fact any `Field`'s) `x / 0 = 0` convention —
      -- mirrors the `hABz` branch just above verbatim, just on the other side of the
      -- division. No need to derive `toPair H A B = 0` at all (which was the old,
      -- unnecessarily hard route this branch's docstring was stuck on).
      refine ⟨0, ?_⟩
      unfold polePairToFraction
      rw [hA'B'z, map_zero, div_zero]
      have : (algebraMap k[X] (CoordinateRing H) (C (0:k))) = 0 := by simp
      rw [this, map_zero]
    · -- Genuine case: both `toPair H A B ≠ 0` and `toPair H A' B' ≠ 0`, `ordAt` equal
      -- everywhere. Real content, see docstring above.
      -- **Reduced (ChatGPT-assisted, this session) to `span_eq_of_ordAt_eq` +
      -- `isUnit_coordinateRing_iff` — both already available — plus one remaining
      -- fraction-field computation left as its own `sorry` below, not faked.**
      -- `span_eq_of_ordAt_eq` itself is *also* still a `sorry` (its statement is now
      -- believed correct, with the `hspec` hypotheses added; only its assembly proof
      -- remains open — see that theorem's docstring), so this branch does not yet
      -- close either, but the two remaining gaps are now cleanly separated: the
      -- Dedekind-domain factorization fact (`span_eq_of_ordAt_eq`) and a self-contained
      -- fraction-field identity (immediately below) with no more curve-specific content.
      have hspan : Ideal.span ({toPair H A B} : Set (CoordinateRing H)) =
          Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)) :=
        span_eq_of_ordAt_eq (H := H) A B A' B' hABz hA'B'z hspecAB hspecA'B' hordeq
      have hassoc : Associated (toPair H A B) (toPair H A' B') :=
        Ideal.span_singleton_eq_span_singleton.mp hspan
      obtain ⟨u, hu⟩ := hassoc
      -- `hu : toPair H A B * ↑u = toPair H A' B'`.
      have hu_unit : IsUnit (u : CoordinateRing H) := u.isUnit
      obtain ⟨c, hc, hcu⟩ := (isUnit_coordinateRing_iff (H := H) hdeg (u : CoordinateRing H)).mp
        hu_unit
      -- **Now proved.** With `hu : toPair H A B * ↑u = toPair H A' B'` and `hcu : (u :
      -- CoordinateRing H) = algebraMap k[X] (CoordinateRing H) (C c)` (`c ≠ 0`), the
      -- witness constant is `c⁻¹`. Strategy: establish the identity entirely inside
      -- `CoordinateRing H` first (`hring_eq` below — no fraction-field lemma-name
      -- uncertainty at all there), then push through `φ` and finish with `div_eq_iff`,
      -- whose statement (`a / b = c ↔ a = c * b`, for `b ≠ 0`) is used in exactly the
      -- orientation it's applied in below — chosen to match `mul_comm`-safe order
      -- rather than assumed.
      refine ⟨c⁻¹, ?_⟩
      unfold polePairToFraction
      set F := FractionRing (CoordinateRing H)
      set φ : CoordinateRing H →+* F := algebraMap (CoordinateRing H) F with hφ_def
      have hcz : (C c : k[X]) ≠ 0 := fun h => hc (by simpa using congrArg (Polynomial.eval 0) h)
      have hCcpair_ne : toPair H (C c) 0 ≠ 0 := by
        rw [Ne, toPair_eq_zero_iff]; exact fun h => hcz h.1
      have hCc_alg : toPair H (C c) 0 = algebraMap k[X] (CoordinateRing H) (C c) := by
        unfold toPair; simp
      have hCc_ne_ring : (algebraMap k[X] (CoordinateRing H) (C c) : CoordinateRing H) ≠ 0 := by
        rw [← hCc_alg]; exact hCcpair_ne
      have hABz' : φ (toPair H A B) ≠ 0 :=
        fun h => hABz (IsFractionRing.injective (CoordinateRing H) F
          (by rw [hφ_def] at h; rw [h, map_zero]))
      have hCc_ne_frac : φ (algebraMap k[X] (CoordinateRing H) (C c)) ≠ 0 :=
        fun h => hCc_ne_ring (IsFractionRing.injective (CoordinateRing H) F
          (by rw [hφ_def] at h; rw [h, map_zero]))
      -- **Entirely inside `CoordinateRing H`, no fraction-field API needed here at all**:
      -- `toPair H A B = algebraMap (C c⁻¹) * toPair H A' B'`, verified by substituting
      -- `toPair H A' B' = toPair H A B * algebraMap (C c)` (from `hu`/`hcu`) and reducing
      -- to `algebraMap (C c⁻¹) * algebraMap (C c) = algebraMap (C (c⁻¹ * c)) = algebraMap
      -- (C 1) = 1`, a pure `k[X]`/ring-hom identity.
      have hring_eq : toPair H A B =
          algebraMap k[X] (CoordinateRing H) (C c⁻¹) * toPair H A' B' := by
        have h1 : toPair H A' B' = algebraMap k[X] (CoordinateRing H) (C c) * toPair H A B := by
          rw [← hu, hcu, mul_comm]
        rw [h1, ← mul_assoc, ← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hc,
          Polynomial.C_1, map_one, one_mul]
      have hden_ne : φ (toPair H A' B') ≠ 0 := by
        rw [← hu, hcu, map_mul]; exact mul_ne_zero hABz' hCc_ne_frac
      rw [div_eq_iff hden_ne, hring_eq, map_mul]

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
    -- **Added this session, threaded through from `isConstantFraction_of_ordAt_eq`'s
    -- now-corrected signature** (see that theorem's docstring — the original version
    -- omitted these, which made its statement provably too weak). Same `hspec` shape
    -- used throughout this file (`deg_divToPairRatio_le_zero`,
    -- `denom_B'_eq_zero_of_isPoleBoundedAtPair`, etc.).
    (hspecAB : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (hspecA'B' : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    (hsuppAB : ∀ P, P ∉ T → ordAt P A B = 0)
    (hsuppA'B' : ∀ P, P ∉ T → ordAt P A' B' = 0)
    (hdegD : deg (divToPairRatio A B T A' B' T) = 0)
    (hle : ∀ P ∈ T, Divisor.coeffAt P (divToPairRatio A B T A' B' T) ≤ 0) :
    IsConstantFraction (polePairToFraction (H := H) A B A' B') := by
  apply isConstantFraction_of_ordAt_eq hdeg A B A' B' hspecAB hspecA'B'
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
  -- **Closing the gap.** The missing ingredient isn't a degree bound at all — it's an
  -- upper bound on `∑_T ordAt(A',B')` itself, which `hreduced` supplies via `hpt` pointwise.
  -- At any `P`, `hreduced P` gives `ordAt P A B = 0 ∨ ordAt P A' B' = 0`. In the first case,
  -- `hpt P` reads `ordAt P A B ≥ ordAt P A' B' - ind(P)` where `ind(P) := (if P=x₁ then 1
  -- else 0) + (if P=x₂ then 1 else 0)`, i.e. `0 ≥ ordAt P A' B' - ind(P)`, so
  -- `ordAt P A' B' ≤ ind(P)`; in the second case `ordAt P A' B' = 0 ≤ ind(P)` trivially
  -- (`ind(P) ≥ 0` always). So `ordAt P A' B' ≤ ind(P)` at *every* point, unconditionally —
  -- no case split on `x₁ = x₂` needed here (unlike a flat `≤ 1` per-point cap, which is false
  -- when `x₁ = x₂` and both indicators fire together at the single coincident point).
  -- Summed over `T`, `∑_T ind(P) = 2` regardless of whether `x₁ = x₂` (if equal, both
  -- indicators fire together at that one point, contributing `2`; if distinct, each
  -- contributes `1` at its own point), giving `∑_T ordAt(A',B') ≤ 2`.
  have hcap_at : ∀ P : H.Point,
      ordAt P A' B' ≤ (if P = x₁ then (1:ℤ) else 0) + (if P = x₂ then (1:ℤ) else 0) := by
    intro P
    rcases hreduced P with hzero | hzero
    · have hind := hpt P
      rw [hzero] at hind
      omega
    · have hind_nonneg : (0:ℤ) ≤ (if P = x₁ then (1:ℤ) else 0) + (if P = x₂ then (1:ℤ) else 0) := by
        have h1 : (0:ℤ) ≤ if P = x₁ then (1:ℤ) else 0 := by by_cases h : P = x₁ <;> simp [h]
        have h2 : (0:ℤ) ≤ if P = x₂ then (1:ℤ) else 0 := by by_cases h : P = x₂ <;> simp [h]
        linarith
      omega
  -- `∑_T ordAt(A',B')` is bounded by `∑_T ind(P)`, which telescopes to `2`.
  have hsum_le : (∑ P ∈ T, ordAt P A' B') ≤ 2 := by
    calc (∑ P ∈ T, ordAt P A' B')
        ≤ ∑ P ∈ T, ((if P = x₁ then (1:ℤ) else 0) + (if P = x₂ then (1:ℤ) else 0)) :=
          Finset.sum_le_sum (fun P _ => hcap_at P)
      _ = (∑ P ∈ T, (if P = x₁ then (1:ℤ) else 0)) + ∑ P ∈ T, (if P = x₂ then (1:ℤ) else 0) :=
          Finset.sum_add_distrib
      _ ≤ 1 + 1 := by
          have hb1 : (∑ P ∈ T, (if P = x₁ then (1:ℤ) else 0)) ≤ 1 := by
            have heq : (∑ P ∈ T, (if P = x₁ then (1:ℤ) else 0)) =
                ((T.filter (fun P => P = x₁)).card : ℤ) := by
              rw [← Finset.sum_filter]
              simp [Finset.sum_const]
            rw [heq]
            have hsub : T.filter (fun P => P = x₁) ⊆ {x₁} := by
              intro P hP
              simp only [Finset.mem_filter] at hP
              simp [hP.2]
            have hcard : (T.filter (fun P => P = x₁)).card ≤ 1 := by
              have := Finset.card_le_card hsub
              simpa using this
            exact_mod_cast hcard
          have hb2 : (∑ P ∈ T, (if P = x₂ then (1:ℤ) else 0)) ≤ 1 := by
            have heq : (∑ P ∈ T, (if P = x₂ then (1:ℤ) else 0)) =
                ((T.filter (fun P => P = x₂)).card : ℤ) := by
              rw [← Finset.sum_filter]
              simp [Finset.sum_const]
            rw [heq]
            have hsub : T.filter (fun P => P = x₂) ⊆ {x₂} := by
              intro P hP
              simp only [Finset.mem_filter] at hP
              simp [hP.2]
            have hcard : (T.filter (fun P => P = x₂)).card ≤ 1 := by
              have := Finset.card_le_card hsub
              simpa using this
            exact_mod_cast hcard
          linarith
      _ = 2 := by norm_num
  -- Contradiction: `h₂` gives `∑_T ordAt(A',B') = -ordInfOfPair A'B'`, and `hordInf_A'B'`
  -- gives `ordInfOfPair A'B' ≤ -(2 deg B' + 5) ≤ -5`, so `∑_T ordAt(A',B') ≥ 5 > 2 ≥ hsum_le`.
  have hB'deg_nonneg : (0:ℤ) ≤ 2 * (B'.natDegree : ℤ) := by positivity
  omega

/-- 
  The denominator-degree lemma: 
  A reduced denominator of a degree-2 pole-bounded function has -ord_∞ ≤ 2.
  (This encapsulates the summation of affine orders from Step 1).
-/
lemma denom_ordInf_ge_neg_two (A' B' : k[X]) 
    (h_B' : B' = 0) 
    (h_deg_A' : A'.natDegree ≤ 1) : 
    ordInfOfPair A' B' ≥ -2 := by
  dsimp [ordInfOfPair]
  by_cases h_A' : A' = 0
  · have hBoth : A' = 0 ∧ B' = 0 := ⟨h_A', h_B'⟩
    rw [if_pos hBoth]
    linarith
  · have hBoth : ¬ (A' = 0 ∧ B' = 0) := fun h => h_A' h.1
    rw [if_neg hBoth, if_pos h_B']
    have h_deg : (A'.natDegree : ℤ) ≤ 1 := by exact_mod_cast h_deg_A'
    omega


/-- **Route A step 2.** Given step 1's `B' = 0`, so `z = (A(x) + B(x)y) / A'(x)`, a
similar parity argument on `y`'s own pole/zero structure (`y² = f(x)`, `deg f = 5`)
against the same `≤ 2` affine pole budget forces `B = 0` too, reducing `z` to a pure
rational function of `x` alone.

**Not proved — attempted and reverted this session; the "mirror of step 1" idea is
WRONG, documenting why so it isn't retried.** Step 1's argument confined `(A',B')`'s
affine support to `{x₁,x₂}` using `hpt`'s *lower* bound on `ordAt P A B` (the
numerator) together with `hreduced`, contraposed: `ordAt P A B = 0` (from `hreduced`'s
first disjunct) forces `ordAt P A' B' ≤ (indicator)` via `hpt` directly, since `hpt`
reads `ordAt P A B ≥ ordAt P A' B' - indicator`. Trying to run the same argument with
`(A,B)` and `(A',B')` swapped **does not work**: `hpt` only ever bounds the numerator
`ordAt P A B` from *below* by the denominator's data — there is no clause anywhere in
`IsPoleBoundedAtPair` bounding `ordAt P A B` from *above*. So "`(A,B)`'s affine support
is confined to `{x₁,x₂}`" is simply not derivable from `hbound` the way it was for
`(A',B')` — a numerator is free to vanish at as many extra points as it likes; only its
*poles* (via the denominator) are constrained. The whole "confine support, then contradict
degree-5-driven lower bound" strategy therefore does not transfer to step 2 as stated.

**What's actually needed instead** (re-reading `SCOPING-finrank-L-pair.md`'s step 2
description: "comparing `y`'s own pole/zero structure... against the bound"): this is not
about the *affine* divisor of `(A,B)` at all — it's about `y`'s pole structure specifically
*at infinity*, i.e. an argument purely via `ordInfOfPair`/`pairNorm`'s degree formula,
without needing `T`/`hspec`/finite-support machinery at all (unlike what this session's
now-reverted attempt assumed). Sketch: `B' = 0` gives `ordInfOfPair A' 0 = -2 deg A'`
(even). `hmono : ordInfOfPair A B ≥ -2 deg A'`. If `B ≠ 0`, `ordInfOfPair A B =
-(max(2 deg A, 2 deg B + 5))`. The genuinely hard content is presumably in
`pairNorm`/`toPair_mul_involution`: `toPair H A B * involution H (toPair H A B) =
algebraMap (pairNorm H A B)` with `pairNorm H A B = A² - B²f` — and `z = toPair H A B /
algebraMap A'` being pole-bounded by `(x₁)+(x₂)` (mass 2) should force `pairNorm H A B`
(degree `-ordInfOfPair A B` when nonzero, by `natDegree_pairNorm_eq_neg_ordInfOfPair`) to
be small — but making "mass 2 at `{x₁,x₂}`" talk to `pairNorm`'s *global* degree still
seems to need the same `T`/`deg_div_eq_zero_deg5` connection step 1 used, just applied to
a different quantity than "confine `(A,B)`'s support". **Not resolved this session** —
flagging the dead end found (mirroring step 1 verbatim) rather than guessing further;
whoever picks this up next should start from `pairNorm`/`toPair_mul_involution` and the
`y_sq_eq` relation (`HyperellipticFunctionField.lean`) rather than repeating the
affine-support-confinement approach. **One more data point against a quick affine-`ordAt`
route**: checked whether `y`'s own affine vanishing structure (needed for any argument
that goes pointwise through `ordAt P A B` with `B ≠ 0`, rather than staying at the
`pairNorm`/infinity level) is already characterized elsewhere — it is not, fully.
`HyperellipticClassProof.lean`'s `ordAt_linX_eq`-adjacent machinery (§B, around line 187)
is itself mid-scaffold with real unresolved `sorry`s in the ramified/unramified local-
uniformizer case split for `linX`, and doesn't cover `toPair H B 0`-style pairs (`y`
itself, `A=0`) at all — so a pointwise `ordAt`-based route through step 2 would likely
need to redo comparable local-uniformizer work from scratch, not just reuse existing
lemmas. This reinforces that the `pairNorm`-at-infinity route sketched above is the more
promising direction, even though it isn't fully worked out either. 
---
  Step 2: The numerator cannot have a `y` component.
  Relies only on the infinity inequality from `IsPoleBoundedAtPair` 
  and the denominator degree bound from Step 1.
-/
lemma num_B_eq_zero_of_isPoleBoundedAtPair (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (h_bound : IsPoleBoundedAtPair x₁ x₂ A B A' B') 
    (h_denom_ord : ordInfOfPair A' B' ≥ -2) : 
    B = 0 := by
  by_contra h_B_ne_zero
  obtain ⟨_, h_inf_ineq, _⟩ := h_bound
  have h_num_le_neg_five : ordInfOfPair A B ≤ -5 := by
    dsimp [ordInfOfPair]
    have hAB : ¬ (A = 0 ∧ B = 0) := fun h => h_B_ne_zero h.2
    rw [if_neg hAB, if_neg h_B_ne_zero]
    have h_B_deg_nonneg : (0 : ℤ) ≤ 2 * (B.natDegree : ℤ) := by positivity
    have h_max_le : (2 * (B.natDegree : ℤ) + 5) ≤ 
      max (2 * (A.natDegree : ℤ)) (2 * (B.natDegree : ℤ) + 5) := 
      le_max_right _ _
    linarith
  linarith [h_inf_ineq, h_num_le_neg_five, h_denom_ord]


/-! ### Helper lemmas for Route A step 3: scale-invariance and degree-1 normalization

Three small helpers, factored out so `fiber_eq_of_pure_rational_pole_match`'s proof
body can case-split cleanly on `A`'s (resp. `A'`'s) shape rather than re-deriving
each of these facts inline. -/

/-- **`toPair H (C c) 0` is never in any `pointIdeal P`, for `c ≠ 0`.** Same proof
shape as `toPair_one_zero_notMem_pointIdeal` (`RiemannRochGenus2.lean:168`), just for
a general nonzero constant instead of literally `1`: `C c` is a unit in `k[X]`
(inverse `C c⁻¹`), so `toPair H (C c) 0` is a unit in `CoordinateRing H`
(`toPair_mul` applied to `(C c, 0)` and `(C c⁻¹, 0)`, collapsing to `toPair H 1 0 =
1` via `mul_inv_cancel₀`), and no proper ideal (in particular no maximal
`pointIdeal P`) can contain a unit. -/
theorem toPair_C_notMem_pointIdeal (c : k) (hc : c ≠ 0) (P : H.Point) :
    toPair H (Polynomial.C c) (0 : k[X]) ∉ pointIdeal P := by
  intro hmem
  have hunit : IsUnit (toPair H (Polynomial.C c) (0 : k[X])) := by
    have hmul_fwd : toPair H (Polynomial.C c) 0 * toPair H (Polynomial.C c⁻¹) 0 = 1 := by
      have hmul := toPair_mul (H := H) (Polynomial.C c) 0 (Polynomial.C c⁻¹) 0
      simp only [zero_mul, mul_zero, zero_add, add_zero] at hmul
      rw [hmul, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, toPair_one_zero]
    have hmul_bwd : toPair H (Polynomial.C c⁻¹) 0 * toPair H (Polynomial.C c) 0 = 1 := by
      rw [mul_comm]; exact hmul_fwd
    exact ⟨⟨toPair H (Polynomial.C c) 0, toPair H (Polynomial.C c⁻¹) 0, hmul_fwd, hmul_bwd⟩, rfl⟩
  exact (pointIdeal_isMaximal P).ne_top
    (Ideal.eq_top_of_isUnit_mem (pointIdeal P) hmem hunit)

/-- **`ordAt` at a nonzero constant pair is always `0`.** Direct from
`ordAt_eq_zero_of_notMem` + `toPair_C_notMem_pointIdeal`. -/
theorem ordAt_C_zero (c : k) (hc : c ≠ 0) (P : H.Point) :
    ordAt P (Polynomial.C c) (0 : k[X]) = 0 :=
  ordAt_eq_zero_of_notMem P (Polynomial.C c) 0 (toPair_C_notMem_pointIdeal c hc P)

/-- **`ordAt` is invariant under scaling by a nonzero constant.** `A = C c * P` for
`c ≠ 0` has the same `ordAt` (hence the same divisor) as `P` itself, at every point:
`toPair H (C c * P) (C c * Q) = toPair H (C c) 0 * toPair H P Q` (`toPair_mul`
applied to `(C c, 0)` and `(P, Q)`, using `C c * P + 0 * Q * f = C c * P` and
`C c * Q + P * 0 = C c * Q`), and `ordAt _ (C c) 0 = 0` (`ordAt_C_zero`), so
`ordAt_toPair_mul_of_ne_zero'` collapses the sum to `ordAt _ P Q` directly.
Both `hbot` branches of `ordAt`'s own `if`/`dif` are handled uniformly, since
`ordAt_toPair_mul_of_ne_zero'` itself takes an explicit `h_bot` argument — split
once here, at the top, rather than inside a sub-`have`. -/
theorem ordAt_C_mul_eq (c : k) (hc : c ≠ 0) (P Q : k[X]) (hPQ : ¬ (P = 0 ∧ Q = 0))
    (R : H.Point) :
    ordAt R (Polynomial.C c * P) (Polynomial.C c * Q) = ordAt R P Q := by
  have hCcne : toPair H (Polynomial.C c) (0 : k[X]) ≠ 0 := by
    rw [Ne, toPair_eq_zero_iff]
    exact fun h => hc (Polynomial.C_eq_zero.mp h.1)
  have hPQne : toPair H P Q ≠ 0 := by rw [Ne, toPair_eq_zero_iff]; exact hPQ
  have hmul : toPair H (Polynomial.C c * P) (Polynomial.C c * Q) =
      toPair H (Polynomial.C c) (0 : k[X]) * toPair H P Q := by
    have hraw := toPair_mul (H := H) (Polynomial.C c) 0 P Q
    simp only [zero_mul, mul_zero, zero_add, add_zero] at hraw
    exact hraw.symm
  by_cases hbot : pointIdeal R = ⊥
  · -- `ordAt` is `0` by definition at every `⊥`-ideal point, on both sides.
    have hne : toPair H (Polynomial.C c * P) (Polynomial.C c * Q) ≠ 0 := by
      rw [hmul]; exact mul_ne_zero hCcne hPQne
    unfold ordAt
    rw [if_neg hne, if_neg hPQne, dif_pos hbot, dif_pos hbot]
  · have hCc0 : ordAt R (Polynomial.C c) (0 : k[X]) = 0 := ordAt_C_zero c hc R
    have hstep := ordAt_toPair_mul_of_ne_zero' R hbot (Polynomial.C c) 0 P Q _ _
      hCcne hPQne hmul
    rw [hstep, hCc0, zero_add]

/-- **Degree-`≤1` polynomials in `k[X]` are `0`, a nonzero constant, or a nonzero
constant times a monic linear factor.** Standard `k[X]`-degree bookkeeping via
`Polynomial.natDegree_le_iff_coeff_eq_zero` (all coefficients above degree `1`
vanish) plus reconstructing `P` from its `coeff 0`/`coeff 1` via
`Polynomial.ext_iff`/`Polynomial.coeff_add`/`coeff_C`/`coeff_X`. -/
theorem eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one (P : k[X]) (hP : P.natDegree ≤ 1) :
    P = 0 ∨ (∃ c : k, c ≠ 0 ∧ P = Polynomial.C c) ∨
      (∃ c a : k, c ≠ 0 ∧ P = Polynomial.C c * linX a) := by
  by_cases hP1 : P.coeff 1 = 0
  · -- `coeff 1 = 0` and `natDegree ≤ 1` forces `P = C (P.coeff 0)`.
    have hP0 : P.natDegree = 0 ∨ P = 0 := by
      by_cases hz : P = 0
      · right; exact hz
      · left
        by_contra hne
        have hpos : 0 < P.natDegree := Nat.pos_of_ne_zero hne
        have : P.natDegree = 1 := le_antisymm hP (hpos)
        have hcoeff := Polynomial.leadingCoeff_ne_zero.mpr hz
        rw [Polynomial.leadingCoeff, this] at hcoeff
        exact hcoeff hP1
    rcases hP0 with hP0 | hP0
    · have hCeq : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hP0
      by_cases hc0 : P.coeff 0 = 0
      · left; rw [hCeq, hc0, Polynomial.C_0]
      · right; left; exact ⟨P.coeff 0, hc0, hCeq⟩
    · left; exact hP0
  · -- `coeff 1 ≠ 0`: `P = C (coeff 1) * X + C (coeff 0) = C (coeff 1) * (X - C (-coeff 0 / coeff 1))`.
    right; right
    set c := P.coeff 1 with hc_def
    set c₀ := P.coeff 0 with hc₀_def
    refine ⟨c, -(c₀ / c), hP1, ?_⟩
    unfold linX
    have hPeq : P = Polynomial.C c * Polynomial.X + Polynomial.C c₀ := by
      apply Polynomial.ext
      intro n
      match n with
      | 0 => simp [hc₀_def]
      | 1 => simp [hc_def]
      | (m + 2) =>
        have hlt : P.natDegree < m + 2 := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
        simp
    rw [hPeq]
    have hc_ne : c ≠ 0 := hP1
    have hscalar : c * (-(c₀ / c)) = -c₀ := by
      field_simp
    have hlift : Polynomial.C c * Polynomial.C (-(c₀ / c)) = -Polynomial.C c₀ := by
      rw [← Polynomial.C_mul, hscalar, Polynomial.C_neg]
    rw [mul_sub, eq_sub_iff_add_eq, hlift]
    ring

/-- **Helper: a `Divisor H` equation between two pairs of `single`s forces set equality
of the underlying pairs.** Proved by evaluating both sides at each candidate point
(`congrArg (fun D => D P)`) rather than reasoning about `Finsupp.support` directly — robust
to coincidences among `a, b, c, d` (e.g. `a = b`). This is the reusable bookkeeping step that
turns a literal divisor identity into a set-level conclusion; see call sites below. -/
private lemma set_eq_of_two_singletons_eq
    {a b c d : H.Point}
    (h : (single a + single b : Divisor H) = single c + single d) :
    ({a, b} : Set H.Point) = {c, d} := by
  classical
  -- Evaluate `coeffAt` of both sides at every point `x`: gives a single equation of
  -- indicator sums that determines membership in `{a,b}` iff membership in `{c,d}`,
  -- without ever `subst`ing `x` into `a,b,c,d` (which renames the wrong variable and
  -- makes `a,b,c,d` disappear from context).
  have hcoeff : ∀ x : H.Point,
      (if x = a then 1 else 0) + (if x = b then 1 else 0) =
        (if x = c then 1 else 0) + (if x = d then (1 : ℤ) else 0) := by
    intro x
    have h' := congrArg (Divisor.coeffAt x) h
    simpa [map_add, Divisor.coeffAt_single, eq_comm] using h'
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hx := hcoeff x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    by_cases hxc : x = c <;> by_cases hxd : x = d <;>
    (try rw [if_pos hxa] at hx) <;> (try rw [if_neg hxa] at hx) <;>
    (try rw [if_pos hxb] at hx) <;> (try rw [if_neg hxb] at hx) <;>
    (try rw [if_pos hxc] at hx) <;> (try rw [if_neg hxc] at hx) <;>
    (try rw [if_pos hxd] at hx) <;> (try rw [if_neg hxd] at hx) <;>
    first
      | exact absurd hx (by omega)
      | (refine ⟨fun h => ?_, fun h => ?_⟩ <;>
          rcases h with h | h <;>
          first
            | exact Or.inl hxa | exact Or.inr hxb
            | exact Or.inl hxc | exact Or.inr hxd
            | exact absurd h hxa | exact absurd h hxb
            | exact absurd h hxc | exact absurd h hxd)

/-- **`ordAt` at the zero pair is always `0`.** Direct from `ordAt`'s own
`if toPair H A B = 0 then 0 else ...` branch: `toPair H 0 0 = 0` (`toPair`
unfolds to `algebraMap _ _ 0 + algebraMap _ _ 0 * y H = 0`), so the `if`
fires immediately regardless of `P`. -/
theorem ordAt_zero_zero (P : H.Point) : ordAt P (0 : k[X]) (0 : k[X]) = 0 := by
  have hz : toPair H (0 : k[X]) (0 : k[X]) = 0 := by simp [toPair]
  unfold ordAt
  rw [if_pos hz]

/-- **Helper for the "constant" branches of `fiber_eq_of_pure_rational_pole_match`.**
`divToPair (C c) 0 S = 0` for any nonzero constant `c` and any finite support `S`:
`ordAt P (C c) 0 = 0` at every point `P` (`ordAt_C_zero`), so every summand is
`0 • single P = 0`. -/
theorem divToPair_C_eq_zero (c : k) (hc : c ≠ 0) (S : Finset H.Point) :
    (divToPair (Polynomial.C c) 0 S : Divisor H) = 0 := by
  unfold divToPair
  refine Finset.sum_eq_zero (fun P _ => ?_)
  rw [ordAt_C_zero c hc P]
  simp

/-- **Sibling of `divToPair_C_eq_zero` for the literal zero pair.**
`divToPair 0 0 S = 0` for any finite support `S`, via `ordAt_zero_zero`. -/
theorem divToPair_zero_zero_eq_zero (S : Finset H.Point) :
    (divToPair (0 : k[X]) (0 : k[X]) S : Divisor H) = 0 := by
  unfold divToPair
  refine Finset.sum_eq_zero (fun P _ => ?_)
  rw [ordAt_zero_zero P]
  simp

/-- **New helper, closes all four "mixed-sign" branches of
`fiber_eq_of_pure_rational_pole_match` uniformly.** `divToPair A 0 S` always has every
term `ordAt P A 0 ≥ 0` (`ordAt`'s own `if`/`dif` gives `0` in the `toPair = 0` and
`pointIdeal = ⊥` branches, `ordAt_nonneg` gives `≥ 0` in the genuine branch — so `≥ 0`
unconditionally, no case split needed at the call site). If in addition
`∑ P ∈ S, ordAt P A 0 = 0` (i.e. `divToPair A 0 S` has degree `0`, via `deg_divToPair`),
every term must be exactly `0` (`Finset.sum_eq_zero_iff_of_nonneg`), hence
`divToPair A 0 S = 0` termwise. -/
theorem divToPair_right_zero_eq_zero_of_deg_eq_zero (A : k[X]) (S : Finset H.Point)
    (hdeg : deg (divToPair A 0 S) = 0) :
    (divToPair A 0 S : Divisor H) = 0 := by
  have hordnn : ∀ P ∈ S, 0 ≤ ordAt P A 0 := by
    intro P _
    by_cases hz : toPair H A 0 = 0
    · unfold ordAt; rw [if_pos hz]
    · by_cases hbot : pointIdeal P = ⊥
      · unfold ordAt; rw [if_neg hz, dif_pos hbot]
      · exact ordAt_nonneg P A 0 hz hbot
  rw [deg_divToPair] at hdeg
  have hall0 : ∀ P ∈ S, ordAt P A 0 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hordnn).mp hdeg
  unfold divToPair
  refine Finset.sum_eq_zero (fun P hP => ?_)
  rw [hall0 P hP]
  simp

set_option maxHeartbeats 800000 in
-- Route A step 3's degree/pole bookkeeping is long enough to need extra heartbeats
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
conclusion.

**New hypotheses `hchar`/`hsf`, added this session.** `ordAt_linX_eq`
(`HyperellipticClassProof.lean:1031`) — the one fact this proof genuinely needs —
requires `(2:k) ≠ 0` and `Squarefree H.f`, neither of which was in this theorem's
original signature. These are standing assumptions everywhere `ordAt_linX_eq` is
used elsewhere in the project (`HyperellipticClassProof.lean` throughout); adding
them here is the honest fix, not a weakening. **Downstream callers
(`fiber_eq_of_divisor_shape`, `constant_or_fiber_of_isPoleBoundedAtPair`,
`uniqueDegree2MapToP1_of_elementary`) will need the same two hypotheses threaded
through once they're wired to call this** — not yet done in this session, flagged
here so the next pass doesn't rediscover it as a mysterious type error.

**Proof plan (per the ChatGPT-assisted case analysis recorded in this session's
transcript, confirmed by hand against `hpoles`'s exact degree-0 shape):** case on
`(A.natDegree, A'.natDegree) ∈ {0,1}²` via
`eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one`.
- **Both effectively degree `0`** (`A ∈ {0} ∪ {C c}`, `A' ∈ {0} ∪ {C c'}`): the
  divisor `divToPairRatio A 0 _ A' 0 _` is `0` (no roots on either side — `ordAt`
  of a nonzero constant, or of `0` itself, is `0` at every point), forcing
  `hpoles`'s RHS `single x₃+single x₄-single x₁-single x₂ = 0`, i.e.
  `{x₃,x₄}={x₁,x₂}` as an equation of divisors (hence sets) directly.
- **Exactly one side degree `1`** (linear): **impossible by a pure degree count** —
  the nonconstant side contributes a full fiber (`ordAt_C_mul_eq` +
  `divToPair_linX_eq`/`fiberSupport`) of total mass `2`, the constant side
  contributes `0`, giving `deg (divToPairRatio ...) = ±2 ≠ 0`, contradicting that
  `hpoles`'s RHS always has degree `0`.
- **Both degree `1`, same root** (`A = C c * linX a`, `A' = C c' * linX a`, same
  `a`): both sides' divisors are the identical fiber (`ordAt_C_mul_eq` reduces both
  to `divToPair (linX a) 0 (fiberSupport a)`), so the ratio's divisor is `0` —
  same conclusion as the both-constant case.
- **Both degree `1`, different roots `a ≠ a'`:** the zero-side divisor is the
  fiber over `a` (`fiberSupport`-indexed, `{x₃,x₄}`), the pole-side is the fiber
  over `a'` (`{x₁,x₂}`). Matching against `hpoles` forces `{x₁,x₂}` itself to be
  a fiber, i.e. `x₂ = ι x₁` (`fiberSupport`'s two cases: `{Q,ιQ}` when
  unramified, `{Q}` doubled when ramified — either way `x₂ = ι x₁` follows from
  `{x₁,x₂}` being *some* `fiberSupport`-shaped set) — **contradicting `hne`**.
  This is the only case where `hne` is used, matching the ChatGPT-confirmed case
  analysis exactly.

**Update — fully wired into Lean below, no `sorry` remains in this theorem.** The case
split above was right (checked independently), and the `Finset`/`Divisor.coeffAt`
bookkeeping connecting `hpoles`'s literal divisor equation to "the RHS is a
`fiberSupport`-shaped divisor" is now carried out for all branches: the vanishing
branches (`A=A'=0`, mixed-sign, same-root) close via `hclose`/`divToPair_right_zero_eq_
zero_of_deg_eq_zero` as sketched; the different-roots branch closes via a direct
`coeffAt`-at-`Q₁`/`ι Q₁` coefficient bash (see `hbalance2` and below), using disjointness
of the two fibers (Step 4) to isolate `Q₁, ι Q₁ ∈ {x₁,x₂}` and a final case split to force
`x₂ = ι x₁`, contradicting `hne`.

**Statement WEAKENED this session — the original version above (no `S`-containment
hypothesis) is FALSE.** A second AI cross-check (after the ChatGPT pass that diagnosed
Goals 1–4/5's difficulty) found a genuine counterexample to the *unrestricted* claim,
independently confirmed by hand against `divToPair`'s literal definition (`∑ P ∈ S, ordAt
P A B • single P` — `Finset`, no multiplicity):

Take `a ≠ a'`, `x₃` an *unramified* point with `x₃.X = a` (so `ι x₃ ≠ x₃`), `x₁` any point
with `x₁.X = a'`, and — the crux — **`x₄ := x₂`** for some `x₂` with `x₂.X` neither `a` nor
`a'`. Then `{x₁,x₂,x₃,x₄}` as a `Finset` *dedups* to `{x₁,x₂,x₃}` (`x₄ = x₂` literally),
so `divToPair (linX a) 0 {x₁,x₂,x₃,x₄}` only ever sums over `x₃` from the `a`-fiber — `ι
x₃ ∉ {x₁,x₂,x₃}` by construction, so its term is silently dropped, never cancelled. The
resulting LHS collapses to exactly `single x₃ - single x₁`, which equals the RHS
`single x₃+single x₄-single x₁-single x₂` once `x₄=x₂` is substituted (`single x₄` and
`single x₂` then literally cancel) — so `hpoles` holds. `hne` also holds (`x₂.X ∉ {a,a'}`
rules out `x₂ = ι x₁`). But the conclusion `{x₃,x₄}={x₁,x₂}` becomes `{x₃,x₂}={x₁,x₂}`,
false since `x₃ ∉ {x₁,x₂}` by construction. **So the theorem, exactly as stated with a bare
`S = {x₁,x₂,x₃,x₄}` support and no further hypothesis, is false** — the fix is not a matter
of finishing the case split below (which is still the right shape once the hole is patched),
but of ruling out this "truncated, partially-cancelled fiber" loophole first.

**Fix applied**: an `hsupp₃ : fiberSupport ⟨a, _⟩ ⊆ {x₁,x₂,x₃,x₄}`-style containment is
awkward to state directly (`fiberSupport` takes a `H.Point`, not a bare root `a : k`, and
no point with `.X = a` is given by name until deep in the case split). Instead, the
containment is stated the way it is actually *needed and available* at each call site: as a
direct hypothesis that whichever of `x₁,x₂,x₃,x₄` witnesses a root also has its ι-partner in
the support set, i.e. **the two hypotheses below**, which are exactly what's true whenever
this theorem is actually invoked from `constant_or_fiber_of_isPoleBoundedAtPair`/`fiber_eq_
of_divisor_shape` (that call site already knows `{x₁,x₂,x₃,x₄}` is a specific 4-point set,
not an arbitrary superset, so asserting `ι`-closure on it is a real, checkable side
condition there, not a hidden circularity). This is the honest "weaken first" fix per
project convention — deleting the theorem outright was not necessary, since the mixed-sign
and same-root branches below remain true and provable regardless (`ordAt_nonneg`, see next
paragraph, closes them cleanly); only the different-roots branch needed the extra
hypothesis. -/
theorem fiber_eq_of_pure_rational_pole_match (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (x₁ x₂ x₃ x₄ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (A A' : k[X]) (hdegA : A.natDegree ≤ 1)
    (hdegA' : A'.natDegree ≤ 1)
    (hpoles : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) =
      single x₃ + single x₄ - single x₁ - single x₂)
    (hclosed₁ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₁.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point))
    (hclosed₂ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₂.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point))
    (hclosed₃ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₃.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point))
    (hclosed₄ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₄.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point)) :
    ({x₃, x₄} : Set H.Point) = {x₁, x₂} := by
  classical
  -- Shared closing step for every branch where `divToPairRatio A 0 _ A' 0 _ = 0`:
  -- rearrange `hpoles` into `single x₃ + single x₄ = single x₁ + single x₂` and hand
  -- off to `set_eq_of_two_singletons_eq`, exactly as the `A = A' = 0` branch does.
  have hclose : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 →
      ({x₃, x₄} : Set H.Point) = {x₁, x₂} := by
    intro hzero
    have hsum : (single x₃ + single x₄ : Divisor H) = single x₁ + single x₂ := by
      rw [hzero] at hpoles
      have := hpoles.symm
      rwa [sub_sub, sub_eq_zero] at this
    exact set_eq_of_two_singletons_eq hsum
  rcases eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one A hdegA with hA0 | ⟨c, hc, hAc⟩ | ⟨c, a, hc, hAlin⟩
  · rcases eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one A' hdegA' with hA'0 | ⟨c', hc', hA'c⟩ | ⟨c', a', hc', hA'lin⟩
    · -- Both `A`, `A'` effectively zero: `divToPair` of `(0,0)` is `0` on both sides.
      apply hclose
      simp [divToPairRatio, divToPair, hA0, hA'0]
    · -- `A = 0`, `A'` a nonzero constant: `divToPair A 0 _ = 0` (`A = 0`) and
      -- `divToPair A' 0 _ = 0` (`divToPair_C_eq_zero`), so the ratio is again `0`.
      apply hclose
      unfold divToPairRatio
      rw [hA0, hA'c, divToPair_C_eq_zero c' hc', divToPair_zero_zero_eq_zero]
      simp
    · -- `A = 0`, `A' = C c' * linX a'`: `divToPairRatio` reduces to
      -- `- divToPair (linX a') 0 S` (via `ordAt_C_mul_eq` stripping the scalar), and
      -- `hpoles` (degree `0` on the RHS) forces this to have degree `0` too, hence
      -- (`ordAt_nonneg` — no term can be negative) it must vanish termwise
      -- (`divToPair_right_zero_eq_zero_of_deg_eq_zero`).
      apply hclose
      have hstep : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) =
          - divToPair (linX a') 0 {x₁, x₂, x₃, x₄} := by
        unfold divToPairRatio
        rw [hA0, hA'lin, divToPair_zero_zero_eq_zero]
        have hlinXne : linX a' ≠ (0 : k[X]) := by
          rw [linX]; intro h
          have hdeg := Polynomial.natDegree_X_sub_C a'
          rw [h, Polynomial.natDegree_zero] at hdeg
          exact absurd hdeg (by norm_num)
        have hne0 : ¬ (linX a' = (0 : k[X]) ∧ (0 : k[X]) = 0) := fun h => hlinXne h.1
        unfold divToPair
        rw [zero_sub]
        congr 1
        refine Finset.sum_congr rfl (fun P _ => ?_)
        have hordeq : ordAt P (Polynomial.C c' * linX a') (Polynomial.C c' * (0 : k[X])) =
            ordAt P (linX a') 0 := ordAt_C_mul_eq c' hc' (linX a') 0 hne0 P
        rw [mul_zero] at hordeq
        rw [hordeq]
      have hdeg0 : deg (divToPair (linX a') 0 {x₁, x₂, x₃, x₄}) = 0 := by
        have hpoles' := hpoles
        rw [hstep] at hpoles'
        have hdegRHS : deg (single x₃ + single x₄ - single x₁ - single x₂ : Divisor H) = 0 := by
          simp
        rw [← hpoles'] at hdegRHS
        simpa using hdegRHS
      have hzero : (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 :=
        divToPair_right_zero_eq_zero_of_deg_eq_zero (linX a') {x₁, x₂, x₃, x₄} hdeg0
      rw [hstep, hzero]; simp
  · rcases eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one A' hdegA' with hA'0 | ⟨c', hc', hA'c⟩ | ⟨c', a', hc', hA'lin⟩
    · -- `A` a nonzero constant, `A' = 0`: both halves vanish via `divToPair_C_eq_zero`/`A'=0`.
      apply hclose
      unfold divToPairRatio
      rw [hAc, hA'0, divToPair_C_eq_zero c hc, divToPair_zero_zero_eq_zero]
      simp
    · -- Both nonzero constants: both halves vanish via `divToPair_C_eq_zero`.
      apply hclose
      unfold divToPairRatio
      rw [hAc, hA'c, divToPair_C_eq_zero c hc, divToPair_C_eq_zero c' hc']
      simp
    · -- `A` a nonzero constant, `A' = C c' * linX a'`: `divToPair A 0 _ = 0`
      -- (`divToPair_C_eq_zero`), so `divToPairRatio` reduces to `- divToPair (linX a') 0 S`
      -- exactly as in the `A = 0, A' = C c' * linX a'` branch above (the scalar `c` played
      -- no role there either); same `hpoles`-forces-degree-`0`-forces-termwise-`0` route.
      apply hclose
      have hstep : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) =
          - divToPair (linX a') 0 {x₁, x₂, x₃, x₄} := by
        unfold divToPairRatio
        rw [hAc, hA'lin, divToPair_C_eq_zero c hc]
        have hlinXne : linX a' ≠ (0 : k[X]) := by
          rw [linX]; intro h
          have hdeg := Polynomial.natDegree_X_sub_C a'
          rw [h, Polynomial.natDegree_zero] at hdeg
          exact absurd hdeg (by norm_num)
        have hne0 : ¬ (linX a' = (0 : k[X]) ∧ (0 : k[X]) = 0) := fun h => hlinXne h.1
        rw [zero_sub]
        congr 1
        unfold divToPair
        refine Finset.sum_congr rfl (fun P _ => ?_)
        have hordeq : ordAt P (Polynomial.C c' * linX a') (Polynomial.C c' * (0 : k[X])) =
            ordAt P (linX a') 0 := ordAt_C_mul_eq c' hc' (linX a') 0 hne0 P
        rw [mul_zero] at hordeq
        rw [hordeq]
      have hdeg0 : deg (divToPair (linX a') 0 {x₁, x₂, x₃, x₄}) = 0 := by
        have hpoles' := hpoles
        rw [hstep] at hpoles'
        have hdegRHS : deg (single x₃ + single x₄ - single x₁ - single x₂ : Divisor H) = 0 := by
          simp
        rw [← hpoles'] at hdegRHS
        simpa using hdegRHS
      have hzero : (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 :=
        divToPair_right_zero_eq_zero_of_deg_eq_zero (linX a') {x₁, x₂, x₃, x₄} hdeg0
      rw [hstep, hzero]; simp
  · rcases eq_zero_or_C_or_C_mul_linX_of_natDegree_le_one A' hdegA' with hA'0 | ⟨c', hc', hA'c⟩ | ⟨c', a', hc', hA'lin⟩
    · -- `A = C c * linX a`, `A' = 0`: mirror of the `A = 0, A' = C c' * linX a'` branch
      -- with `A`/`A'` swapped — `divToPair A' 0 _ = 0` (`A' = 0`), so `divToPairRatio`
      -- reduces to `+ divToPair (linX a) 0 S` this time (no leading negation), after
      -- stripping the scalar `c` from `divToPair (C c * linX a) 0 S` via `ordAt_C_mul_eq`.
      apply hclose
      have hstep : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) =
          divToPair (linX a) 0 {x₁, x₂, x₃, x₄} := by
        unfold divToPairRatio
        rw [hAlin, hA'0, divToPair_zero_zero_eq_zero]
        have hlinXne : linX a ≠ (0 : k[X]) := by
          rw [linX]; intro h
          have hdeg := Polynomial.natDegree_X_sub_C a
          rw [h, Polynomial.natDegree_zero] at hdeg
          exact absurd hdeg (by norm_num)
        have hne0 : ¬ (linX a = (0 : k[X]) ∧ (0 : k[X]) = 0) := fun h => hlinXne h.1
        rw [sub_zero]
        unfold divToPair
        refine Finset.sum_congr rfl (fun P _ => ?_)
        have hordeq : ordAt P (Polynomial.C c * linX a) (Polynomial.C c * (0 : k[X])) =
            ordAt P (linX a) 0 := ordAt_C_mul_eq c hc (linX a) 0 hne0 P
        rw [mul_zero] at hordeq
        rw [hordeq]
      have hdeg0 : deg (divToPair (linX a) 0 {x₁, x₂, x₃, x₄}) = 0 := by
        have hpoles' := hpoles
        rw [hstep] at hpoles'
        rw [hpoles']
        simp
      have hzero : (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 :=
        divToPair_right_zero_eq_zero_of_deg_eq_zero (linX a) {x₁, x₂, x₃, x₄} hdeg0
      rw [hstep, hzero]
    · -- `A = C c * linX a`, `A'` a nonzero constant: `divToPair A' 0 _ = 0`
      -- (`divToPair_C_eq_zero`), so `divToPairRatio` reduces to `+ divToPair (linX a) 0 S`,
      -- same shape as the previous branch (scalar-stripping on `A`'s side, not `A'`'s).
      apply hclose
      have hstep : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) =
          divToPair (linX a) 0 {x₁, x₂, x₃, x₄} := by
        unfold divToPairRatio
        rw [hAlin, hA'c, divToPair_C_eq_zero c' hc']
        have hlinXne : linX a ≠ (0 : k[X]) := by
          rw [linX]; intro h
          have hdeg := Polynomial.natDegree_X_sub_C a
          rw [h, Polynomial.natDegree_zero] at hdeg
          exact absurd hdeg (by norm_num)
        have hne0 : ¬ (linX a = (0 : k[X]) ∧ (0 : k[X]) = 0) := fun h => hlinXne h.1
        rw [sub_zero]
        unfold divToPair
        refine Finset.sum_congr rfl (fun P _ => ?_)
        have hordeq : ordAt P (Polynomial.C c * linX a) (Polynomial.C c * (0 : k[X])) =
            ordAt P (linX a) 0 := ordAt_C_mul_eq c hc (linX a) 0 hne0 P
        rw [mul_zero] at hordeq
        rw [hordeq]
      have hdeg0 : deg (divToPair (linX a) 0 {x₁, x₂, x₃, x₄}) = 0 := by
        have hpoles' := hpoles
        rw [hstep] at hpoles'
        rw [hpoles']
        simp
      have hzero : (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 :=
        divToPair_right_zero_eq_zero_of_deg_eq_zero (linX a) {x₁, x₂, x₃, x₄} hdeg0
      rw [hstep, hzero]
    · -- Both linear: split on whether the roots coincide.
      by_cases haeq : a = a'
      · -- Same root: `ordAt_C_mul_eq` strips the nonzero-scalar factor from both
        -- sides, leaving `ordAt _ (linX a) 0` on both, so the two `divToPair` sums
        -- are termwise equal over the same support `{x₁,x₂,x₃,x₄}` — no `fiberSupport`

        -- or containment argument needed (per ChatGPT-confirmed proof: the ratio
        -- vanishes purely because both sides compute the same underlying divisor,
        -- scaled by different units).
        apply hclose
        subst haeq
        unfold divToPairRatio
        rw [hAlin, hA'lin, sub_eq_zero]
        unfold divToPair
        refine Finset.sum_congr rfl (fun P _ => ?_)
        have hlinXne : linX a ≠ (0 : k[X]) := by
          rw [linX]
          intro h
          have hdeg := Polynomial.natDegree_X_sub_C a
          rw [h, Polynomial.natDegree_zero] at hdeg
          exact absurd hdeg (by norm_num)
        have hne0 : ¬ (linX a = (0 : k[X]) ∧ (0 : k[X]) = 0) := fun h => hlinXne h.1
        have hc0 : ordAt P (Polynomial.C c * linX a) (Polynomial.C c * (0 : k[X])) =
            ordAt P (linX a) 0 := ordAt_C_mul_eq c hc (linX a) 0 hne0 P
        have hc'0 : ordAt P (Polynomial.C c' * linX a) (Polynomial.C c' * (0 : k[X])) =
            ordAt P (linX a) 0 := ordAt_C_mul_eq c' hc' (linX a) 0 hne0 P
        rw [mul_zero] at hc0 hc'0
        rw [hc0, hc'0]
      · -- Different roots: coefficient-comparison argument (ChatGPT-confirmed shape).
        -- `linX a` and `linX a'` have disjoint zero-fibers (`a ≠ a'`), so `hpoles`'s
        -- `+`/`-` split can't mix contributions from the two fibers — the positive part
        -- must come entirely from the `X = a` fiber and the negative part entirely from
        -- the `X = a'` fiber. `hclosed₃`/`hclosed₁` rule out a "truncated" single-point
        -- fiber (forcing the clean unramified `{Q, ιQ}` shape on each side), and `hne`
        -- rules out the negative fiber collapsing to an `ι`-pair around `x₁` that would
        -- force `x₂ = ι x₁`.
        have hlinXane : linX a ≠ (0 : k[X]) := linX_ne_zero a
        have hlinXa'ne : linX a' ≠ (0 : k[X]) := linX_ne_zero a'
        have hne0a : ¬ (linX a = (0 : k[X]) ∧ (0 : k[X]) = 0) := fun h => hlinXane h.1
        have hne0a' : ¬ (linX a' = (0 : k[X]) ∧ (0 : k[X]) = 0) := fun h => hlinXa'ne h.1
        classical
        -- Coefficient of any `Q ∈ {x₁,x₂,x₃,x₄}` in `divToPair (poly) 0 {x₁,x₂,x₃,x₄}`,
        -- computed directly from the `Finset.sum` definition — no outside-support fact
        -- needed since we only ever evaluate at points inside the support.
        have hcoeffPair : ∀ (P : k[X]) (Q : H.Point), Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point) →
            Divisor.coeffAt Q (divToPair P 0 {x₁, x₂, x₃, x₄}) = ordAt Q P 0 := by
          intro P Q hQ
          unfold divToPair
          rw [map_sum, Finset.sum_eq_single Q
            (fun R _ hRQ => by
              rw [map_zsmul, Divisor.coeffAt_single, if_neg (Ne.symm hRQ)]; simp)
            (fun hQS => absurd hQ hQS)]
          rw [map_zsmul, Divisor.coeffAt_single_self]
          simp
        -- Reduce `hpoles`'s coefficient at any of the four named points to a bare
        -- `ordAt`-difference on `linX a`/`linX a'` (scalars stripped via `ordAt_C_mul_eq`).
        have hcoeff : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point),
            Divisor.coeffAt Q (single x₃ + single x₄ - single x₁ - single x₂ : Divisor H) =
              ordAt Q (linX a) 0 - ordAt Q (linX a') 0 := by
          intro Q hQ
          have hstep : Divisor.coeffAt Q
              (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄}) =
              ordAt Q (linX a) 0 - ordAt Q (linX a') 0 := by
            unfold divToPairRatio
            rw [map_sub, hAlin, hA'lin, hcoeffPair (Polynomial.C c * linX a) Q hQ,
              hcoeffPair (Polynomial.C c' * linX a') Q hQ]
            have hordA := ordAt_C_mul_eq c hc (linX a) 0 hne0a Q
            have hordA' := ordAt_C_mul_eq c' hc' (linX a') 0 hne0a' Q
            rw [mul_zero] at hordA hordA'
            rw [hordA, hordA']
          rw [← hstep, hpoles]
        -- Evaluate `hcoeff` at `x₃`: `coeffAt x₃ (RHS) ≥ 1` (it's `1`, or `2` if `x₃ = x₄`),
        -- in particular positive, so `ordAt x₃ (linX a) 0 ≠ ordAt x₃ (linX a') 0` and the
        -- difference is positive. By `ordAt_linX_eq` (values only ever `0,1,2`, and `a ≠ a'`
        -- means `x₃.X` can't equal both), the only way a nonneg-minus-nonneg difference is
        -- positive is `x₃.X = a` (contributing `≥ 1`) and `x₃.X ≠ a'` (contributing `0`).
        have hordbd : ∀ (r : k) (Q : H.Point), ordAt Q (linX r) 0 = 0 ∨ ordAt Q (linX r) 0 = 1 ∨
            ordAt Q (linX r) 0 = 2 := by
          intro r Q
          rw [ordAt_linX_eq hchar hsf r Q (pointIdeal_ne_bot Q)]
          split_ifs <;> simp
        -- **New this session — all-positive rearrangement, UNVERIFIED (no local Lean, next
        -- session must check in the REPL).** Instead of chasing `hcoeff` at one named point
        -- at a time (the previous attempt's gap: `x₃.X ≠ a` only forces `x₃ ∈ {x₁,x₂}`, not
        -- `False`), rearrange `hcoeff` at *every* point of `H.Point` — not just the four named
        -- ones — into a single divisor identity with every term on the nonneg side:
        -- `D_a + single x₁ + single x₂ = D_a' + single x₃ + single x₄`, where `D_a :=
        -- divToPair (linX a) 0 S`, `D_a' := divToPair (linX a') 0 S`. Both sides are honest
        -- sums of `single`s with nonneg (`ordAt`-valued, or `1`) coefficients, so this is a
        -- genuine mass-balance, not a signed difference — no cancellation ambiguity. Points
        -- *outside* `S` contribute `0` to both `D_a`/`D_a'` (by `divToPair`'s own definition,
        -- a `Finset.sum` over `S`) and `0` to the `single x_i` terms (all four named points are
        -- in `S`), so the identity holds at every point of `H.Point`, i.e. as an equation of
        -- `Divisor H`, not just on `S`.
        -- Proved as whole-`Divisor H` algebra (mirroring the `hstep` idiom used in the
        -- earlier branches of this theorem, e.g. the `A=0,A'=C c'*linX a'` case above),
        -- NOT via `coeffAt`/`Finsupp.ext` — `Divisor H` is a `def` over `H.Point →₀ ℤ`, not
        -- `abbrev` (see `Divisor.coeffAt`'s own docstring), so `Finsupp.ext` may not apply at
        -- ordinary transparency; safer to stay inside the already-working `hstep`/`ring`-on-
        -- `Divisor H`-as-`AddCommGroup` style used throughout this file.
        have hstepD : (divToPairRatio A 0 {x₁, x₂, x₃, x₄} A' 0 {x₁, x₂, x₃, x₄} : Divisor H) =
            (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) -
              divToPair (linX a') 0 {x₁, x₂, x₃, x₄} := by
          unfold divToPairRatio
          rw [hAlin, hA'lin]
          congr 1
          · unfold divToPair
            refine Finset.sum_congr rfl (fun P _ => ?_)
            have hordA := ordAt_C_mul_eq c hc (linX a) 0 hne0a P
            rw [mul_zero] at hordA
            rw [hordA]
          · unfold divToPair
            refine Finset.sum_congr rfl (fun P _ => ?_)
            have hordA' := ordAt_C_mul_eq c' hc' (linX a') 0 hne0a' P
            rw [mul_zero] at hordA'
            rw [hordA']
        have hbalance : (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) + single x₁ + single x₂ =
            (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) + single x₃ + single x₄ := by
          have hpoles' := hpoles
          rw [hstepD] at hpoles'
          -- `hpoles' : D_a - D_a' = single x₃ + single x₄ - single x₁ - single x₂`. Regroup
          -- the RHS's left-to-right subtraction chain into `(single x₃ + single x₄) -
          -- (single x₁ + single x₂)` (`sub_sub`, already used for exactly this purpose at
          -- `hclose`'s definition above), then apply the general `AddCommGroup` rearrangement
          -- `a - b = c - d ↔ a + d = c + b` (`sub_eq_sub_iff_add_eq_add`) with `a := D_a`,
          -- `b := D_a'`, `c := single x₃ + single x₄`, `d := single x₁ + single x₂`, giving
          -- `D_a + (single x₁+single x₂) = (single x₃+single x₄) + D_a'` — then `abel` closes
          -- the remaining associativity/commutativity mismatch against the goal's exact
          -- bracketing (`+ single x₁ + single x₂` vs `+ (single x₁ + single x₂)`, etc.).
          rw [sub_sub] at hpoles'
          have hrearr := sub_eq_sub_iff_add_eq_add.mp hpoles'
          -- `hrearr : D_a + (single x₁ + single x₂) = single x₃ + single x₄ + D_a'`
          have : (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) + single x₁ + single x₂ =
              single x₃ + single x₄ + (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) := by
            rw [add_assoc]; exact hrearr
          rw [this]; abel
        -- **Degree bookkeeping, continuing from `hbalance`.** `deg` is additive
        -- (`AddMonoidHom`), so `deg (D_a + single x₁ + single x₂) = deg D_a + 1 + 1` and
        -- symmetrically for the other side; equating gives `deg D_a = deg D_a'`.
        have hdegeq : deg (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) =
            deg (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) := by
          have h := congrArg deg hbalance
          simp only [map_add, deg_single] at h
          omega
        -- Case split on whether this common degree is `0`.
        by_cases hdeg0 : deg (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0
        · -- **Easy case: both sides vanish.** Exactly the "one/both zero" route sketched
          -- above — `divToPair_right_zero_eq_zero_of_deg_eq_zero` termwise-vanishes both
          -- `D_a` and `D_a'` (using `hdeg0` and `hdegeq.symm.trans hdeg0`/`hdeg0` resp.),
          -- and `hbalance` collapses to `single x₁+single x₂ = single x₃+single x₄`, closed
          -- by `set_eq_of_two_singletons_eq` (symmetrized, since that lemma's conclusion is
          -- stated as `{a,b}={c,d}` from `single a+single b=single c+single d` — here we
          -- have the `x₃,x₄`/`x₁,x₂` roles swapped relative to `hclose`'s usage above, so
          -- take `.symm` on both the hypothesis and the goal).
          have hzeroa : (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 :=
            divToPair_right_zero_eq_zero_of_deg_eq_zero (linX a) {x₁, x₂, x₃, x₄} hdeg0
          have hzeroa' : (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 :=
            divToPair_right_zero_eq_zero_of_deg_eq_zero (linX a') {x₁, x₂, x₃, x₄}
              (hdegeq ▸ hdeg0)
          rw [hzeroa, hzeroa', zero_add, zero_add] at hbalance
          have hsum2 : (single x₃ + single x₄ : Divisor H) = single x₁ + single x₂ :=
            hbalance.symm
          exact set_eq_of_two_singletons_eq hsum2
        · -- **Hard case: `deg D_a = deg D_a' ≠ 0`.** Extract a witness point of `S` with
          -- `X = a` (resp. `X = a'`), pin down `D_a`/`D_a'` as exactly that witness's
          -- fiber (via `hsupp_linX`'s contrapositive + `divToPair_linX_eq`, widened from
          -- `fiberSupport` to all of `S` by `Finset.sum_subset`, mirroring
          -- `RatioDivisorCollapse.lean`'s established idiom for exactly this kind of
          -- support-widening), then close via `hbalance` and `hne`.
          classical
          -- **Step 1: some point of `S` has `X = a`.** Contrapositive of `ordAt_linX_eq`:
          -- if every point of `S` had `X ≠ a`, every term of `D_a`'s defining sum would be
          -- `0` (via `ordAt_linX_eq_zero_of_ne`), forcing `D_a = 0`, hence `deg D_a = 0`,
          -- contradicting `hdeg0`.
          have hexA : ∃ Q₀ ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q₀.X = a := by
            by_contra hcon
            push_neg at hcon
            have hallzero : (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 := by
              unfold divToPair
              refine Finset.sum_eq_zero (fun P hP => ?_)
              rw [ordAt_linX_eq_zero_of_ne a P (pointIdeal_ne_bot P) (hcon P hP)]
              simp
            rw [hallzero] at hdeg0
            exact hdeg0 (by simp)
          have hexA' : ∃ Q₁ ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q₁.X = a' := by
            by_contra hcon
            push_neg at hcon
            have hallzero : (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 := by
              unfold divToPair
              refine Finset.sum_eq_zero (fun P hP => ?_)
              rw [ordAt_linX_eq_zero_of_ne a' P (pointIdeal_ne_bot P) (hcon P hP)]
              simp
            have hdeg0' : deg (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) = 0 := by
              rw [hallzero]; simp
            rw [← hdegeq] at hdeg0'
            exact hdeg0 hdeg0'
          obtain ⟨Q₀, hQ₀mem, hQ₀X⟩ := hexA
          obtain ⟨Q₁, hQ₁mem, hQ₁X⟩ := hexA'
          -- **Step 2: `ι Q₀ ∈ S` and `ι Q₁ ∈ S`.** `Q₀` is literally one of the four named
          -- points, so `Q₀.X = xᵢ.X` (with `xᵢ := Q₀` itself, `rfl`), letting the matching
          -- `hclosed_i` fire with `Q := Q₀`. Same for `Q₁`.
          have hQ₀mem' : Q₀ = x₁ ∨ Q₀ = x₂ ∨ Q₀ = x₃ ∨ Q₀ = x₄ := by
            simpa using hQ₀mem
          have hιQ₀ : Point.iota Q₀ ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point) := by
            rcases hQ₀mem' with h | h | h | h
            · exact h ▸ hclosed₁ Q₀ hQ₀mem (by rw [h])
            · exact h ▸ hclosed₂ Q₀ hQ₀mem (by rw [h])
            · exact h ▸ hclosed₃ Q₀ hQ₀mem (by rw [h])
            · exact h ▸ hclosed₄ Q₀ hQ₀mem (by rw [h])
          have hQ₁mem' : Q₁ = x₁ ∨ Q₁ = x₂ ∨ Q₁ = x₃ ∨ Q₁ = x₄ := by
            simpa using hQ₁mem
          have hιQ₁ : Point.iota Q₁ ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point) := by
            rcases hQ₁mem' with h | h | h | h
            · exact h ▸ hclosed₁ Q₁ hQ₁mem (by rw [h])
            · exact h ▸ hclosed₂ Q₁ hQ₁mem (by rw [h])
            · exact h ▸ hclosed₃ Q₁ hQ₁mem (by rw [h])
            · exact h ▸ hclosed₄ Q₁ hQ₁mem (by rw [h])
          -- **Step 3: `D_a = single Q₀ + single (ι Q₀)`.** `fiberSupport Q₀ ⊆ S`
          -- (`Q₀ ∈ S`, `ι Q₀ ∈ S` from Step 2 — `fiberSupport` is `{Q₀}` or `{Q₀, ι Q₀}`,
          -- both contained once both named members are in `S`), and every point of
          -- `S \ fiberSupport Q₀` contributes `0` to `D_a`'s sum (`hsupp_linX`, using
          -- `linX a = linX Q₀.X` via `hQ₀X`). Widen `divToPair_linX_eq` (computed on the
          -- exact fiber) up to all of `S` via `Finset.sum_subset`.
          have hfiberSubA : fiberSupport Q₀ ⊆ ({x₁, x₂, x₃, x₄} : Finset H.Point) := by
            unfold fiberSupport
            split_ifs with hY
            · simpa using hQ₀mem
            · intro P hP
              simp only [Finset.mem_insert, Finset.mem_singleton] at hP
              rcases hP with h | h
              · rw [h]; exact hQ₀mem
              · rw [h]; exact hιQ₀
          have hDa_eq : (divToPair (linX a) 0 {x₁, x₂, x₃, x₄} : Divisor H) =
              single Q₀ + single (Point.iota Q₀) := by
            rw [← hQ₀X]
            rw [← divToPair_linX_eq hchar hsf Q₀]
            unfold divToPair
            symm
            refine Finset.sum_subset hfiberSubA (fun P hP hPnot => ?_)
            have hzero : ordAt P (linX Q₀.X) 0 = 0 := hsupp_linX hchar hsf Q₀ P hPnot
            rw [hzero]; simp
          have hfiberSubA' : fiberSupport Q₁ ⊆ ({x₁, x₂, x₃, x₄} : Finset H.Point) := by
            unfold fiberSupport
            split_ifs with hY
            · simpa using hQ₁mem
            · intro P hP
              simp only [Finset.mem_insert, Finset.mem_singleton] at hP
              rcases hP with h | h
              · rw [h]; exact hQ₁mem
              · rw [h]; exact hιQ₁
          have hDa'_eq : (divToPair (linX a') 0 {x₁, x₂, x₃, x₄} : Divisor H) =
              single Q₁ + single (Point.iota Q₁) := by
            rw [← hQ₁X]
            rw [← divToPair_linX_eq hchar hsf Q₁]
            unfold divToPair
            symm
            refine Finset.sum_subset hfiberSubA' (fun P hP hPnot => ?_)
            have hzero : ordAt P (linX Q₁.X) 0 = 0 := hsupp_linX hchar hsf Q₁ P hPnot
            rw [hzero]; simp
          -- **Step 4: the two fibers `{Q₀,ιQ₀}`, `{Q₁,ιQ₁}` are pairwise disjoint from each
          -- other**, since `X` is `ι`-invariant (`iota_X`) and `Q₀.X = a ≠ a' = Q₁.X`.
          have hXne : Q₀.X ≠ Q₁.X := by rw [hQ₀X, hQ₁X]; exact haeq
          have hQ0Q1 : Q₀ ≠ Q₁ := fun h => hXne (h ▸ rfl)
          have hQ0iQ1 : Q₀ ≠ Point.iota Q₁ := fun h => hXne (by rw [h, Point.iota_X])
          have hiQ0Q1 : Point.iota Q₀ ≠ Q₁ := fun h => hXne (by rw [← Point.iota_X Q₀, h])
          have hiQ0iQ1 : Point.iota Q₀ ≠ Point.iota Q₁ := fun h => hXne (by
            rw [← Point.iota_X Q₀, ← Point.iota_X Q₁, h])
          -- **Step 5: combine into the balance equation on the concrete fiber points.**
          have hbalance2 : (single Q₀ + single (Point.iota Q₀) : Divisor H) + single x₁ + single x₂ =
              single Q₁ + single (Point.iota Q₁) + single x₃ + single x₄ := by
            rw [← hDa_eq, ← hDa'_eq]; exact hbalance
          -- **Step 6: read off `{x₃,x₄}` and `{x₁,x₂}` via `coeffAt` at each of the four
          -- fiber points, using Step 4's disjointness to kill cross-terms.** At `Q₀`: LHS
          -- coefficient is `1 + [ιQ₀=Q₀] ≥ 1`; RHS's `Q₁,ιQ₁` terms vanish (Step 4), so
          -- `[x₃=Q₀]+[x₄=Q₀] = 1 + [ιQ₀=Q₀] ≥ 1`, i.e. `Q₀ ∈ {x₃,x₄}`. Symmetrically for
          -- `ιQ₀ ∈ {x₃,x₄}`, `Q₁,ιQ₁ ∈ {x₁,x₂}` (from the mirror coefficient at `Q₁`/`ιQ₁`,
          -- where the `Q₀,ιQ₀` terms vanish on the LHS this time). Combined with each pair
          -- having exactly the fiber's `2`-point (or doubled `1`-point) mass, and `{x₃,x₄}`/
          -- `{x₁,x₂}` each having total mass exactly `2`, this pins `{x₃,x₄}={Q₀,ιQ₀}` and
          -- `{x₁,x₂}={Q₁,ιQ₁}` as sets.
          -- **Step 6: read off `{x₃,x₄}` and `{x₁,x₂}` via `coeffAt` at each of the four
          -- fiber points, using Step 4's disjointness to kill cross-terms.**
          -- **Step 6, redone via direct substitution rather than raw `coeffAt`-`if` chasing
          -- (safer: avoids depending on `Divisor.coeffAt_single`'s exact `if` orientation).**
          -- Substitute `hDa_eq`/`hDa'_eq` into `hbalance` to get `hbalance2` (already have,
          -- Step 5): `single Q₀ + single (ι Q₀) + single x₁ + single x₂ = single Q₁ +
          -- single (ι Q₁) + single x₃ + single x₄`. Regroup via `add_assoc`/`add_comm` into
          -- `(single Q₀ + single (ι Q₀)) + (single x₁ + single x₂) = (single Q₁ +
          -- single (ι Q₁)) + (single x₃ + single x₄)`, matching the shape `set_eq_of_two_
          -- singletons_eq`-style reasoning needs, but with 4 summands: instead of reproving
          -- that lemma's machinery from scratch for 4 terms, isolate `{x₁,x₂}` by moving
          -- `single x₃ + single x₄` to the LHS: `(single Q₀+single ιQ₀) - (single Q₁+
          -- single ιQ₁) = (single x₃+single x₄) - (single x₁+single x₂)`, i.e. exactly the
          -- shape `hpoles` already had at the top (`D_a - D_a'` reinterpreted) — so instead
          -- directly derive the **two separate two-point equalities** by using disjointness
          -- (Step 4) to argue `single x₁+single x₂` must absorb *all* of the `Q₁,ιQ₁`-mass
          -- and none of the `Q₀,ιQ₀`-mass. **Finished this session** (coefficient-bash route,
          -- confirmed against a Gemini-assisted derivation): evaluate `hbalance2` via `coeffAt`
          -- at `Q₁` and `ι Q₁` only. Disjointness (Step 4) zeroes the `Q₀,ιQ₀` cross-terms,
          -- forcing `Q₁ ∈ {x₁,x₂}` and `ι Q₁ ∈ {x₁,x₂}` (`omega`, using nonnegativity of the
          -- remaining `if`-terms). A finite case split on which of `x₁,x₂` each of `Q₁,ι Q₁`
          -- equals forces `x₂ = Point.iota x₁` in every branch, contradicting `hne`. No
          -- containment fact about `{x₃,x₄}` is ever needed — the crux only needs `Q₁ ≠ Q₀,
          -- ι Q₀` and `ι Q₁ ≠ Q₀, ι Q₀` (Step 4). Cross-terms are zeroed with explicit
          -- `if_neg`/`if_pos` calls against the disjointness facts; the two remaining
          -- genuinely-unknown terms in each hypothesis are left as opaque `ite`s and
          -- dispatched generically by `split_ifs ... <;> omega`.
          exfalso
          have hcoeffQ₁ := congrArg (Divisor.coeffAt Q₁) hbalance2
          have hcoeffιQ₁ := congrArg (Divisor.coeffAt (Point.iota Q₁)) hbalance2
          -- `simp` already resolves each `if P = P then _ else _` self-term down to
          -- `if True then _ else _` on its own (confirmed by this session's build output),
          -- so add `if_true` to finish collapsing that to a literal `1` before the
          -- disjointness `rw`s below, which target genuine cross-terms only.
          simp only [map_add, Divisor.coeffAt_single, if_true] at hcoeffQ₁ hcoeffιQ₁
          -- Zero out the `Q₀, ι Q₀` cross-terms via Step 4's disjointness — these are the
          -- only two `ite`s each hypothesis has left besides the already-resolved self-term
          -- and the not-yet-known `x₁,x₂` (resp. `x₃,x₄`, `ιQ₁`) terms.
          rw [if_neg hQ0Q1.symm, if_neg hiQ0Q1.symm] at hcoeffQ₁
          rw [if_neg hQ0iQ1.symm, if_neg hiQ0iQ1.symm] at hcoeffιQ₁
          -- Only the `x₁,x₂` (resp. `x₃,x₄`) terms need resolving by contradiction; the
          -- remaining `if [Q₁=ιQ₁] ...` (resp. `if [ιQ₁=Q₁] ...`) terms are left as opaque
          -- `ite`s and dispatched generically by `split_ifs ... <;> omega`, which needs no
          -- information about their truth value (only that each is `0` or `1`).
          have hQ₁mem12 : Q₁ = x₁ ∨ Q₁ = x₂ := by
            by_contra hcon
            push_neg at hcon
            rw [if_neg hcon.1, if_neg hcon.2] at hcoeffQ₁
            split_ifs at hcoeffQ₁ <;> omega
          have hιQ₁mem12 : Point.iota Q₁ = x₁ ∨ Point.iota Q₁ = x₂ := by
            by_contra hcon
            push_neg at hcon
            rw [if_neg hcon.1, if_neg hcon.2] at hcoeffιQ₁
            split_ifs at hcoeffιQ₁ <;> omega
          -- In every case, `x₂ = Point.iota x₁`, contradicting `hne`.
          apply hne
          rcases hQ₁mem12 with hQ₁x1 | hQ₁x2 <;> rcases hιQ₁mem12 with hιQ₁x1 | hιQ₁x2
          · -- `Q₁ = x₁` and `ι Q₁ = x₁`: forces `Q₁ = ι Q₁`. Feed this back into `hcoeffQ₁`
            -- to see the RHS mass at `Q₁` is `≥ 2`, which can only be matched if `x₂` (not
            -- just `x₁`) also equals `Q₁` — then `x₂ = Q₁ = ι Q₁ = ι x₁` via `hιQ₁x1` and
            -- `iota_iota`.
            have hQ₁ιQ₁ : Q₁ = Point.iota Q₁ := hQ₁x1.trans hιQ₁x1.symm
            have hx1x2 : x₁ = x₂ := by
              by_contra hcon
              have hQ₁ne2 : Q₁ ≠ x₂ := by rw [hQ₁x1]; exact hcon
              rw [if_pos hQ₁ιQ₁, if_neg hQ₁ne2, if_pos hQ₁x1] at hcoeffQ₁
              split_ifs at hcoeffQ₁ <;> omega
            -- `x₂ = x₁ = Q₁ = ι Q₁ = ι x₁`.
            exact hx1x2.symm.trans (hQ₁x1.symm.trans (hQ₁ιQ₁.trans (congrArg Point.iota hQ₁x1)))
          · -- `Q₁ = x₁`, `ι Q₁ = x₂`: `x₂ = ι Q₁ = ι x₁` directly.
            rw [← hιQ₁x2, ← hQ₁x1]
          · -- `Q₁ = x₂`, `ι Q₁ = x₁`: apply `iota` to `ι Q₁ = x₁`, use `iota_iota` to get
            -- `Q₁ = ι x₁`, then rewrite via `Q₁ = x₂`.
            have hstep : Point.iota (Point.iota Q₁) = Point.iota x₁ := by rw [hιQ₁x1]
            rw [Point.iota_iota] at hstep
            rw [← hQ₁x2]; exact hstep
          · -- `Q₁ = x₂` and `ι Q₁ = x₂`: mirrors the first subcase (`Q₁ = ι Q₁` again),
            -- forcing `x₁ = x₂` via the RHS mass at `Q₁`, then `x₂ = Q₁ = ι Q₁ = ι x₂ = ι x₁`
            -- (last step using `x₁ = x₂` again).
            have hQ₁ιQ₁ : Q₁ = Point.iota Q₁ := hQ₁x2.trans hιQ₁x2.symm
            have hx1x2 : x₁ = x₂ := by
              by_contra hcon
              have hQ₁ne1 : Q₁ ≠ x₁ := by rw [hQ₁x2]; exact Ne.symm hcon
              rw [if_pos hQ₁ιQ₁, if_neg hQ₁ne1, if_pos hQ₁x2] at hcoeffQ₁
              split_ifs at hcoeffQ₁ <;> omega
            exact hQ₁x2.symm.trans (hQ₁ιQ₁.trans (congrArg Point.iota (hQ₁x2.trans hx1x2.symm)))



set_option maxHeartbeats 800000 in
-- heavy case-bash across the pole-match branches; default heartbeat budget is too tight
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
-- **Hypothesis package strengthened this session (ChatGPT-assisted design pass; every
-- addition below checked by hand against the exact signature of the lemma it feeds —
-- `denom_B'_eq_zero_of_isPoleBoundedAtPair`, `num_B_eq_zero_of_isPoleBoundedAtPair`, and
-- `fiber_eq_of_pure_rational_pole_match` — not just accepted as proposed).** The bare
-- `hdiv` this theorem previously carried is not enough to run the documented assembly.
-- Four independent gaps, none of them a wiring issue:
--
-- (1) `denom_B'_eq_zero_of_isPoleBoundedAtPair` needs `hspecAB`/`hspecA'B'` (every other
--     caller of that lemma threads them; this theorem alone omitted them), plus
--     `hreduced` — a *lowest-terms* condition genuinely not implied by
--     `IsPoleBoundedAtPair` (that lemma's own docstring gives the counterexample
--     `A=A'=0, B=B'=1`, i.e. `z = y/y`, satisfying `IsPoleBoundedAtPair` with `B'≠0`) —
--     plus two `Module.Finite` instance obligations over the support `Finset`, which
--     don't exist as global instances anywhere in this project (checked by search) and
--     so must be threaded in explicitly.
-- (2) `num_B_eq_zero_of_isPoleBoundedAtPair` needs `ordInfOfPair A' B' ≥ -2` directly.
--     **This is exactly `constant_or_fiber_of_isPoleBoundedAtPair`'s own still-open
--     `h_denom_ord` sorry** (identical statement, identical missing content) — carried
--     here as `hdenomOrd`, assumed, not proved. Deriving it from `hbound` alone without a
--     lowest-terms assumption is unresolved; see that theorem's docstring for why the
--     natural route (bounding `∑_T ordAt(A',B')` via `hpt` alone) fails without one.
-- (3) `fiber_eq_of_pure_rational_pole_match` needs the four `hclosed` ι-closure facts,
--     stated over the *literal* `Finset` `{x₁,x₂,x₃,x₄}`, and its own `hpoles` hypothesis
--     is stated with that same literal `Finset` as the support on *both* sides of the
--     ratio. So `T` is fixed to `{x₁,x₂,x₃,x₄}` here rather than left abstract — no
--     support-extension lemma (`divToPair A B T = divToPair A B {x₁,x₂,x₃,x₄}` for
--     `T ⊆ {x₁,x₂,x₃,x₄}`, or similar) exists anywhere in this project to bridge an
--     arbitrary `T` to this shape, and inventing one is out of scope for this pass.
-- (4) `denom_B'_eq_zero_of_isPoleBoundedAtPair` also needs `hAB : ¬(A=0 ∧ B=0)`. This one
--     genuinely *is* free — if `A=0∧B=0` then `toPair H A B = 0` (`toPair_eq_zero_iff`),
--     so `ordAt P A B = 0` at every `P` by `ordAt`'s own `if_pos` branch on that
--     condition — so it is derived in the proof below, not assumed.
--
-- **Honesty note.** `hreduced` and `hdenomOrd` are real, currently-unformalized
-- mathematical content, not bookkeeping. This theorem, once its proof is filled in, will
-- not derive `{x₃,x₄}={x₁,x₂}` from `IsPoleBoundedAtPair` and the divisor equation alone —
-- it derives it *given* a lowest-terms representation and the resulting infinity-order
-- bound. Whoever eventually calls this from `constant_or_fiber_of_isPoleBoundedAtPair`'s
-- §3f site still owes exactly those two facts (already flagged there as `h_denom_ord`'s
-- own open sorry). Strengthening the hypotheses here relocates that gap to an explicit,
-- precisely-named assumption instead of hiding it inside an opaque `sorry` — it does not
-- close it, and the theorem should not be read as "done" until they are.
theorem fiber_eq_of_divisor_shape (x₁ x₂ x₃ x₄ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (hdiv : ∃ A B A' B' : k[X],
      IsPoleBoundedAtPair x₁ x₂ A B A' B' ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
        (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
        ∃ P, v.asIdeal = pointIdeal P) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
        (Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)))).factors ≠ 0 →
        ∃ P, v.asIdeal = pointIdeal P) ∧
      -- lowest-terms condition (§1 above); NOT derivable from `IsPoleBoundedAtPair` alone.
      (∀ P : H.Point, ordAt P A B = 0 ∨ ordAt P A' B' = 0) ∧
      -- infinity-order bound (§2 above); identical content to `constant_or_fiber_of_
      -- isPoleBoundedAtPair`'s still-open `h_denom_ord`.
      ordInfOfPair A' B' ≥ -2 ∧
      (∀ P, P ∉ ({x₁, x₂, x₃, x₄} : Finset H.Point) → ordAt P A B = 0) ∧
      (∀ P, P ∉ ({x₁, x₂, x₃, x₄} : Finset H.Point) → ordAt P A' B' = 0) ∧
      (divToPairRatio A B {x₁, x₂, x₃, x₄} A' B' {x₁, x₂, x₃, x₄} : Divisor H) =
        single x₃ + single x₄ - single x₁ - single x₂ ∧
      -- (§1 above) `Module.Finite` obligations `denom_B'_eq_zero_of_isPoleBoundedAtPair`
      -- needs, over the fixed support `{x₁,x₂,x₃,x₄}`. Packaged inside the existential
      -- (rather than as top-level instance-implicit arguments) because their type
      -- depends on `A, B, A', B'`, which are only bound here.
      (∀ P : ({x₁, x₂, x₃, x₄} : Finset H.Point),
        Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A B).toNat)) ∧
      (∀ P : ({x₁, x₂, x₃, x₄} : Finset H.Point),
        Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A' B').toNat)))
    (hclosed₁ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₁.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point))
    (hclosed₂ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₂.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point))
    (hclosed₃ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₃.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point))
    (hclosed₄ : ∀ Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point), Q.X = x₄.X →
      Point.iota Q ∈ ({x₁, x₂, x₃, x₄} : Finset H.Point)) :
    ({x₃, x₄} : Set H.Point) = {x₁, x₂} := by
  obtain ⟨A, B, A', B', hbound, hspecAB, hspecA'B', hreduced, hdenomOrd,
    hsuppAB, hsuppA'B', hpoles, hfinAB, hfinA'B'⟩ := hdiv
  haveI := hfinAB
  haveI := hfinA'B'
  -- `(A,B) ≠ (0,0)`: free from `toPair_eq_zero_iff` + `ordAt`'s `if_pos` branch (§4 above).
  have hAB : ¬ (A = 0 ∧ B = 0) := by
    intro hz
    obtain ⟨hA0, hB0⟩ := hz
    have hzero : toPair H A B = 0 := (toPair_eq_zero_iff H A B).mpr ⟨hA0, hB0⟩
    -- With `toPair H A B = 0`, `hbound`'s pointwise clause forces `ordAt P A' B' ≤
    -- (indicator)` everywhere via `ordAt`'s `if_pos hzero` branch giving `ordAt P A B = 0`
    -- — this makes `A' B'` itself supported only on `{x₁,x₂}`, which should contradict
    -- `hpoles` (RHS has `single x₃ + single x₄` with positive coefficient) UNLESS
    -- `{x₃,x₄} ⊆ {x₁,x₂}` already — not obviously absurd without more work. Left as a
    -- named gap rather than forced shut with an invalid tactic: see note below.
    sorry
  -- **Remaining assembly — NOT completed this pass.** I was not able to fully verify a
  -- tactic-level proof from here without access to a Lean toolchain (this session's
  -- earlier attempts at this file produced tactic blocks I could not actually check and
  -- had to retract — flagging that explicitly rather than repeating it). The intended
  -- shape, to be verified against a real `lake build` before trusting it:
  --   1. `have hB' : B' = 0 := denom_B'_eq_zero_of_isPoleBoundedAtPair hdeg x₁ x₂ A B A' B'
  --        hbound hspecAB hspecA'B' {x₁,x₂,x₃,x₄} hAB hsuppAB hsuppA'B' hreduced`
  --      (relying on the `haveI`s above for the two instance arguments).
  --   2. `have hB : B = 0 := num_B_eq_zero_of_isPoleBoundedAtPair x₁ x₂ A B A' B' hbound
  --        (hB' ▸ hdenomOrd)` — NOTE: `hdenomOrd : ordInfOfPair A' B' ≥ -2` needs no
  --      rewriting by `hB'` at all (it's already about `(A',B')`, not `(A',0)`); the
  --      `▸` above is likely unnecessary — check whether `hdenomOrd` can be passed as-is.
  --   3. Derive `A.natDegree ≤ 1` and `A'.natDegree ≤ 1` from `ordInfOfPair_right_zero`
  --      (below) + `hbound`'s `ordInfOfPair A B ≥ ordInfOfPair A' B'` clause + `hdenomOrd`,
  --      mirroring `constant_or_fiber_of_isPoleBoundedAtPair`'s existing `h_deg_A'`/
  --      `h_deg_A` derivation (same file, further down) — that derivation is already
  --      proved for an analogous but not identical goal shape, so it is a close model,
  --      not a direct copy-paste.
  --   4. Rewrite `hpoles` by `hB`/`hB'` to match `fiber_eq_of_pure_rational_pole_match`'s
  --      expected `divToPairRatio A 0 {x₁,x₂,x₃,x₄} A' 0 {x₁,x₂,x₃,x₄}` shape (should be
  --      a direct `rw`, since `hpoles` is already stated over that literal `Finset`).
  --   5. `exact fiber_eq_of_pure_rational_pole_match hchar hsf x₁ x₂ x₃ x₄ hne A A'
  --        ‹A.natDegree ≤ 1› ‹A'.natDegree ≤ 1› ‹rewritten hpoles› hclosed₁ hclosed₂
  --        hclosed₃ hclosed₄`.
  sorry
  


/-- **Renamed from the broken `ordInfOfPair_right_zero`.** Was stated as an
equation between two `ordInf` applications of a nonexistent fraction-level
valuation; the honest fact this call site actually needs is `ordInfOfPair`'s
own `B = 0` unfolding, which is `rfl`-close from the definition
(`PrincipalDivisors.lean:122`'s `if B = 0 then 0 else ...` branch collapsing
the `max` to `2 * A.natDegree`). -/
lemma ordInfOfPair_right_zero (A : k[X]) :
    ordInfOfPair A 0 = -2 * (A.natDegree : ℤ) := by
  by_cases hA : A = 0
  · subst hA
    simp [ordInfOfPair]
  · dsimp [ordInfOfPair]
    rw [if_neg (fun h => hA h.1), if_pos rfl]
    have h_nonneg : (0:ℤ) ≤ 2 * (A.natDegree : ℤ) := by positivity
    rw [max_eq_left h_nonneg]
    ring


/-- **Replaces the deleted, FALSE `natDegree_eq_zero_of_ordInf_bound`.**
(Old lemma's counterexample, for the record: `A' = X` has `natDegree = 1`,
`ordInfOfPair A' 0 = -2 ≥ -2`, and nothing false about it — it's the honest
`z = c/(x-a)` witness of the genuine `x₂ = ι x₁` fiber case. A pure
`ordInfOfPair`-size bound can never rule this out, since `A'.natDegree = 1`
*is* a real, satisfiable case; only `hne` together with the actual pointwise
pole data can.)

**Correctly-shaped replacement, per ChatGPT-assisted design pass (session
transcript): this lemma now carries the point data (`x₁, x₂, hne`) and the
pointwise bound `hpt` that the false version omitted**, rather than trying to
squeeze the conclusion out of an integer inequality alone. `hpt` here is
`hbound`'s pointwise clause specialized to `B = B' = 0` (i.e. after `rw [hB,
hB'] at hpt` at the call site — `B`, `B'` are *not* parameters here, the
statement is already specialized to avoid re-threading them uselessly).

**Still an honest `sorry`, not a fabricated proof — this is a genuinely
different difficulty tier from a wiring fix.** Diagnosis (ChatGPT-assisted,
confirmed by hand): the missing step is *not* covered by
`fiber_eq_of_pure_rational_pole_match` directly, because that theorem's
hypothesis `hpoles` is an exact `Divisor H` *equality* `single x₃ + single x₄
- single x₁ - single x₂` with concrete witness points `x₃, x₄`, whereas what
`hpt`/`hT₁`/`hT₂` supply at this call site is only a pointwise *inequality*
plus finite supports — no witness points `x₃, x₄` and no divisor equation
have been constructed yet. Building that bridge ("pointwise pole-bound
inequality + finite support ⟹ exact fiber-shaped divisor equation with
explicit witnesses") is itself unformalized work, comparable in size to
`fiber_eq_of_divisor_shape`'s own gap just above — **not attempted here**,
per the same "document, don't fake" convention as elsewhere in this file.
Whoever closes this should either (a) prove it directly via the same
`ordAt_linX_eq`/`fiberSupport` case analysis `fiber_eq_of_pure_rational_pole_
match` uses, applied to the single point `Q'` with `Q'.X = a'` where `A' = C
c' * linX a'` (using `hdegA'le1` + `eq_zero_or_C_or_C_mul_linX_of_natDegree_
le_one` to get `a'`), or (b) first build the pointwise-inequality-to-exact-
divisor-equation bridge as its own lemma and then call
`fiber_eq_of_pure_rational_pole_match`. Route (a) is likely less work, since
it avoids constructing the bridge lemma at all. -/
lemma natDegree_eq_zero_of_isPoleBoundedAtPair (hchar : (2 : k) ≠ 0)
    (hsf : Squarefree H.f) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (A A' : k[X]) (hdegA'le1 : A'.natDegree ≤ 1)
    (hpt : ∀ P : H.Point, ordAt P A 0 ≥ ordAt P A' 0 -
      ((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0))) :
    A'.natDegree = 0 := by
  sorry


/-- **Renamed from the broken `natDegree_eq_zero_of_mono`.** Was stated as
`IsConstantFraction (polePairToFraction ...)` of already-degree-0 data, which
isn't what the call site (`constant_or_fiber_of_isPoleBoundedAtPair`'s
`h_deg_A` step) needs — that step derives `A.natDegree = 0` *from* `hmono`
together with `A'`'s already-established degree bound and `B = B' = 0`, not a
constant-fraction conclusion. Restated as the actual missing degree fact,
still open. -/
lemma natDegree_eq_zero_of_mono (A A' : k[X])
    (hmono : ordInfOfPair A 0 ≥ ordInfOfPair A' 0)
    (_hB : (0 : k[X]) = 0) (_hB' : (0 : k[X]) = 0)
    (h_deg_A' : A'.natDegree = 0) (h_deg_pos : ¬ A.natDegree = 0) :
    False := by
  -- `ordInfOfPair_right_zero` unfolds both sides: `ordInfOfPair A 0 = -2 * A.natDegree`,
  -- `ordInfOfPair A' 0 = -2 * A'.natDegree = 0` (via `h_deg_A'`). `hmono` then reads
  -- `-2 * A.natDegree ≥ 0`, forcing `A.natDegree = 0` (it's a `ℕ`-cast, so `≥ 0` already),
  -- contradicting `h_deg_pos`.
  have h_ord_A : ordInfOfPair A 0 = -2 * (A.natDegree : ℤ) := ordInfOfPair_right_zero A
  have h_ord_A' : ordInfOfPair A' 0 = -2 * (A'.natDegree : ℤ) := ordInfOfPair_right_zero A'
  rw [h_ord_A, h_ord_A', h_deg_A'] at hmono
  simp only [Nat.cast_zero, mul_zero] at hmono
  have h_deg_nonneg : (0:ℤ) ≤ (A.natDegree : ℤ) := Nat.cast_nonneg _
  have h_deg_zero : (A.natDegree : ℤ) = 0 := by linarith
  exact h_deg_pos (by exact_mod_cast h_deg_zero)


/-- **Assembly of §3a–§3f into the top-level target.** Wires the pieces above
together: §3a/§2 give the shape, §3e case-splits on whether the positive part
vanishes, §3d closes the vanishing case directly, and the nonvanishing case
combines §3f (`{x₃,x₄} = {x₁,x₂}`, hence `D = 0`) with §3d again (now that
`D`'s positive part is known `0` after substitution) to close. **Currently
blocked on §3f being a real `sorry`** — everything else below it is
plumbing. -/
theorem constant_or_fiber_of_isPoleBoundedAtPair (hdeg : H.f.natDegree = 5)
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (x₁ x₂ : H.Point) (hne : x₂ ≠ x₁.iota) (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x₁ x₂ A B A' B')
    (hspecAB : ∀ (v : IsDedekindDomain.HeightOneSpectrum H.CoordinateRing),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {H.toPair A B})).factors ≠ 0 →
        ∃ P, v.asIdeal = pointIdeal P)
    (hspecA'B' : ∀ (v : IsDedekindDomain.HeightOneSpectrum H.CoordinateRing),
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {H.toPair A' B'})).factors ≠ 0 →
        ∃ P, v.asIdeal = pointIdeal P) :
    IsConstantFraction (polePairToFraction (H := H) A B A' B') := by
  by_cases hAB0 : A = 0 ∧ B = 0
  · -- Handle the A = 0 ∧ B = 0 case directly
    have hzero : H.toPair A B = 0 := by
      rw [hAB0.1, hAB0.2]
      simp [HyperellipticPolynomial.toPair]
    -- Unfold IsConstantFraction directly instead of calling missing helper lemmas
    dsimp [IsConstantFraction, polePairToFraction]
    use 0
    rw [hzero]
    simp
  · -- Main case: (A, B) ≠ (0, 0)
    have ⟨hA'B', hmono, hpt⟩ := hbound

    -- 1. Extract finite supports for (A, B) and (A', B') via hspec
    obtain ⟨T₁, hT₁⟩ := exists_finite_support_of_hspec A B hAB0 hspecAB
    obtain ⟨T₂, hT₂⟩ := exists_finite_support_of_hspec A' B' hA'B' hspecA'B'

    -- 2. Deduce B' = 0 and B = 0 (y-components vanish)
    -- **Genuinely open** (SCOPING-finrank-L-pair.md's Route A step 1/2 boundary): the
    -- old code claimed this followed from `hpt` alone via a lemma
    -- (`ordInf_ge_neg_two_of_pole_bounded`) typed against a fraction-level `ordInf` that
    -- doesn't exist anywhere in the project. The real content — bounding
    -- `ordInfOfPair A' B'` below using `hpt`'s pointwise data — needs the same
    -- `T`/`deg_div_eq_zero_deg5` summation
    -- `denom_B'_eq_zero_of_isPoleBoundedAtPair` (§ above) already carries out in full
    -- (using `hT₁`/`hT₂`'s finite supports plus a `hreduced` lowest-terms hypothesis this
    -- theorem does not currently take as a parameter). Left as `sorry`, not a fabricated
    -- proof, until that threading is done; `hT₁`/`hT₂` are already in scope for whoever
    -- closes this.
    have h_denom_ord : ordInfOfPair A' B' ≥ -2 := by
      sorry

    have hB' : B' = 0 := by
      by_contra hB'_ne
      -- `ordInfOfPair A' B' ≤ -(2 deg B' + 5) ≤ -5` (true regardless of which branch of
      -- `ordInfOfPair`'s `max` wins — no parity argument needed, see the deleted
      -- `ordInf_parity_mismatch` note above for why that route was both false and unused).
      have h_min : ordInfOfPair A' B' ≤ -(2 * (B'.natDegree : ℤ) + 5) := by
        dsimp [ordInfOfPair]
        rw [if_neg (fun h => hA'B' h), if_neg hB'_ne]
        have : (2 * (B'.natDegree : ℤ) + 5) ≤
            max (2 * (A'.natDegree : ℤ)) (2 * (B'.natDegree : ℤ) + 5) := le_max_right _ _
        linarith
      have hB'deg_nonneg : (0:ℤ) ≤ 2 * (B'.natDegree : ℤ) := by positivity
      -- This contradicts the bounds from the pole support.
      linarith [h_min, h_denom_ord, hB'deg_nonneg]

    have hB : B = 0 := num_B_eq_zero_of_isPoleBoundedAtPair x₁ x₂ A B A' B' hbound h_denom_ord

    -- 3. Show A' and A are degree 0 (constants)
    -- **Rewired (ChatGPT-assisted design pass) to actually use `hne`** — the previous
    -- version only used the `ordInfOfPair ≥ -2` size bound (giving `natDegree ≤ 1`) and
    -- called a lemma that tried to rule out `natDegree = 1` with no point data at all,
    -- which is false (see `natDegree_eq_zero_of_isPoleBoundedAtPair`'s docstring). The
    -- `≤ 1` bound is still derived the same way (from `h_denom_ord`/`ordInfOfPair_right_
    -- zero`); ruling out the `= 1` case is now delegated to
    -- `natDegree_eq_zero_of_isPoleBoundedAtPair`, which takes `hne` and `hpt` (specialized
    -- to `B = B' = 0`) and is itself still a `sorry` (genuinely open, see its docstring —
    -- not a wiring gap anymore, a real case-analysis gap).
    have h_deg_A' : A'.natDegree = 0 := by
      have h_ord_A' : ordInfOfPair A' 0 = -2 * (A'.natDegree : ℤ) := ordInfOfPair_right_zero A'
      have h_bound_eq : -2 * (A'.natDegree : ℤ) ≥ -2 := by
        calc -2 * (A'.natDegree : ℤ) = ordInfOfPair A' 0 := h_ord_A'.symm
        _ = ordInfOfPair A' B' := by rw [hB']
        _ ≥ -2 := h_denom_ord
      have hdegA'le1 : A'.natDegree ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have : (2 : ℤ) ≤ (A'.natDegree : ℤ) := by exact_mod_cast hgt
        linarith
      have hpt' : ∀ P : H.Point, ordAt P A 0 ≥ ordAt P A' 0 -
          ((if P = x₁ then 1 else 0) + (if P = x₂ then 1 else 0)) := by
        intro P
        have := hpt P
        rwa [hB, hB'] at this
      exact natDegree_eq_zero_of_isPoleBoundedAtPair hchar hsf x₁ x₂ hne A A' hdegA'le1 hpt'

    have h_deg_A : A.natDegree = 0 := by
      by_contra h_deg_pos
      -- By monotonicity (hmono), since A' is bounded to degree 0 and y-components vanish,
      -- A is similarly restricted.
      have hmono' : ordInfOfPair A 0 ≥ ordInfOfPair A' 0 := by rw [hB, hB'] at hmono; exact hmono
      exact natDegree_eq_zero_of_mono A A' hmono' rfl rfl h_deg_A' h_deg_pos

    -- 4. Reconstruct constant fraction in k
    -- `Polynomial.eq_C_of_natDegree_eq_zero` produces an equality `p = C (p.coeff 0)`
    have hcA : A = Polynomial.C (A.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h_deg_A
    have hcA' : A' = Polynomial.C (A'.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h_deg_A'
    -- `A' ≠ 0` (from `hA'B'`, since `B' = 0`), so its constant coefficient is nonzero —
    -- needed so the witness fraction `A.coeff 0 / A'.coeff 0` is an honest quotient in `k`,
    -- and so the denominator `toPair H A' 0` is a nonzero `CoordinateRing H` element.
    have hA'ne : A' ≠ 0 := fun h => hA'B' ⟨h, hB'⟩
    have hA'c0_ne : A'.coeff 0 ≠ 0 := by
      intro hzero
      apply hA'ne
      rw [hcA', hzero, Polynomial.C_0]
    have htoPairA'_ne : toPair H A' 0 ≠ 0 := by
      rw [Ne, toPair_eq_zero_iff]
      exact fun h => hA'ne h.1
    -- `algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))` is injective
    -- (`IsFractionRing.injective`, the codebase's standard route — see
    -- `PrincipalDivisorsIntegralClosure.lean:110` for the same invocation), so a nonzero
    -- `CoordinateRing H` element stays nonzero after mapping into the fraction field.
    have hdenom_ne : algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H))
        (toPair H A' 0) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (CoordinateRing H)
        (FractionRing (CoordinateRing H)))).mpr htoPairA'_ne

    dsimp [IsConstantFraction, polePairToFraction]
    refine ⟨A.coeff 0 / A'.coeff 0, ?_⟩

    -- Clean substitution using exact variable mappings to avoid polynomial namespace collisions
    rw [hcA'] at hdenom_ne
    rw [hcA, hcA', hB, hB']
    -- `toPair H (C a) 0 = algebraMap k[X] (CoordinateRing H) (C a) + algebraMap k[X]
    -- (CoordinateRing H) 0 * y H` (`HyperellipticFunctionField.lean:72-73`); the `B`-term
    -- collapses via `map_zero`/`zero_mul`/`add_zero` on both sides at once. `rw [hcA, hcA']`
    -- above also rewrote the witness's own `A.coeff 0`/`A'.coeff 0` into `(C _).coeff 0`
    -- (since it rewrites every occurrence, including inside the already-substituted witness),
    -- so `Polynomial.coeff_C_zero` collapses those back down first.
    simp only [HyperellipticPolynomial.toPair, map_zero, zero_mul, add_zero,
      Polynomial.coeff_C_zero] at hdenom_ne ⊢
    -- Goal: `algMap (algMap2 (C a)) / algMap (algMap2 (C a')) = algMap (algMap2 (C (a/a')))`.
    -- Clear the division on the LHS against `hdenom_ne`, folding the RHS's `C (a/a')` and the
    -- newly-introduced `algMap (algMap2 (C a'))` factor into one `algMap (algMap2 (C (a/a' *
    -- a')))` term via `map_mul`/`C_mul`, then close with `a = a/a' * a'` at the `k` level.
    rw [div_eq_iff hdenom_ne, ← map_mul, ← map_mul, ← Polynomial.C_mul, div_mul_cancel₀ _ hA'c0_ne]

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
    (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁)
    (z : FractionRing (CoordinateRing H)) (hz : z ∈ LPairCarrier x₁ x₂)
    (hspecAll : ∀ (A B : k[X]), ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A B} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P) :
    IsConstantFraction z := by
  obtain ⟨A, B, A', B', hbound, hz_eq⟩ := hz
  rw [hz_eq]
  exact constant_or_fiber_of_isPoleBoundedAtPair hdeg hchar hsf x₁ x₂ hne A B A' B' hbound
    (hspecAll A B) (hspecAll A' B')

end HyperellipticPolynomial
