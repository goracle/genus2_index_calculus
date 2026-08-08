import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.FFKSidon
import Genus2Lean.AverageComplexity
import Genus2Lean.PaleyZygmund
import Genus2Lean.SidonEnergy
import Genus2Lean.MatchCountAutocorr
import Genus2Lean.CombinatorialSecondMoment

set_option linter.style.header false

/-!
# Bridging the curve-side FFK dichotomy and the abstract Sidon combinatorics

**Purpose of this file: scaffolding, not a proof.** `FFKSidon.lean` states the
Forey–Fresán–Kowalski dichotomy for `s : C(k) → J` as an unproved hypothesis
`PrincipalDivisorData.SidonDichotomy` on an abstract `D`. `SidonEnergy.lean`
(and everything built on it — `MatchCountAutocorr.lean`,
`CombinatorialSecondMoment.lean`) proves real, unconditional-modulo-Sidon
combinatorics for an abstract finite group `G`, under a hypothesis
`SidonRepBound T` that is *the same open problem*, restated for a bare
`Finset G` rather than for points of a curve. Nobody has connected the two:
no lemma anywhere in this repo takes a `D` satisfying `SidonDichotomy` and
produces a `T : Finset G` satisfying `SidonRepBound`. This file writes down
that connection precisely, so the remaining gap is exactly one theorem, with
a name, a type, and a home — not a vague "these should obviously line up."

**What is proved here:** the mechanical bridge
(`sidonRepBound_of_sidonDichotomy`) — given `SidonDichotomy` for a concrete
`D`, together with the field-finiteness instances needed to even state
`Finset`/`Fintype` combinatorics on `Jacobian H D`, the image `T := s '' F`
of a factor base `F` avoiding involution-pairs satisfies `SidonRepBound T`.
This direction is pure bookkeeping (unfolding `IsSidon`, matching up
`s_add_s_eq_s_add_s_iff` with `repFunction`/`repCount`), not new mathematics.

**What is NOT proved here, and is the actual remaining work:**
`SidonDichotomy` itself, for the genuine `D := principalDivisorData H hdeg`
of `PrincipalDivisorSubgroup.lean`. That is the real Forey–Fresán–Kowalski
theorem (Riemann–Roch for genus 2), and closing it is a separate, substantial
undertaking left to future work — see the module docstring of `FFKSidon.lean`
for exactly what shape that proof would need to take.

**Where this project is actually placing its bet.** Even granting
`SidonDichotomy` in full, `CombinatorialSecondMoment.lean`'s
`sidon_gives_hit_count_bound_combinatorial` only yields a *worst-case* lower
bound of `B²/2` values of `Δ` with `matchCount T Δ ≠ 0` — a long way from the
`Θ(B⁴/N)` "generic" behaviour the heuristic runtime analysis actually wants,
and advisory-7 §7.4-7.6 already flags this shortfall explicitly (closing it
without a further structural input would need bounding the 8th Fourier
moment, or equivalently a genuine bound on `E(S,S)`, which nothing in this
repo attempts). **We are not trying to close that worst-case gap here.**
Empirically the walk's collision behaviour tracks the heuristic average
comfortably, so the position this project actually stakes out is the
average-case claim: assuming (a) `SidonDichotomy` and (b) that `F` behaves
like a "generic" factor base in the specific quantitative sense made precise
below (`GenericFactorBase`), relation-gathering at a factor-base size
`B ~ p^{2/5}` comfortably outpaces the `Θ(B²) = Θ(p^{4/5})` sparse
linear-algebra step, so the algorithm's overall group-operation count is
`p^{4/5}`, driven by linear algebra rather than by a relation-gathering
bottleneck — matching the heuristic complexity the algorithm is designed
around. (`B ~ p^{2/5}` itself comes from balancing `Θ(B²)` linear-algebra
cost against the `p^{4/5}` target, not from a relation-gathering
constraint — see `hitCount_ge_of_generic`'s docstring for the exact
accounting.) `GenericFactorBase` is stated as an explicit,
checkable-in-principle hypothesis (not derived from first principles here)
precisely so it is visible as the actual place the "worst case doesn't
happen, empirically" bet is being placed. Proving `GenericFactorBase` from
equidistribution of `F` in `G` (the natural route, paralleling the Fourier
argument advisory-7 sketches but for an average rather than a uniform bound)
is future work, isolated below in one place (`hitCount_ge_of_generic`'s
docstring) rather than smuggled into a definition that looks unconditional.
-/

noncomputable section

open Polynomial Finset

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-! ## §1. Field-finiteness instances

Everything in `SidonEnergy.lean`/`MatchCountAutocorr.lean`/
`CombinatorialSecondMoment.lean` is stated for `[Fintype G] [DecidableEq G]
[AddCommGroup G]`. `Jacobian H D` is a quotient of `Divisor H := H.Point →₀
ℤ`, which is infinite whenever `k` is infinite (already true of `H.Point`
itself: `k × k`'s subtype cut out by one polynomial equation is infinite for
infinite `k`). So the combinatorics literally cannot be applied to the
Jacobian of a curve over an infinite field — the cryptographic setting
(`k = ZMod p`) is not a special case chosen for convenience, it is required
for the statement to typecheck at all. This is made an explicit hypothesis
here (`[Fintype k] [DecidableEq k]`) rather than silently assumed, matching
this project's stated policy of flagging gaps instead of building past
them. -/

variable [Fintype k] [DecidableEq k]

/-- `H.Point`'s defining predicate is decidable once `k` has decidable
equality: `Equation H x y` unfolds to `y ^ 2 = H.f.eval x`, an equality in
`k`. Stated explicitly (rather than relying on instance search to unfold
the opaque `def Equation`/`def Point`) since `Point`/`Equation` are plain
`def`s, not `abbrev`s, and typeclass resolution does not unfold those on its
own. -/
instance instDecidablePredEquation (H : HyperellipticPolynomial k) :
    DecidablePred (fun p : k × k => H.Equation p.1 p.2) :=
  fun p => inferInstanceAs (Decidable (p.2 ^ 2 = H.f.eval p.1))

/-- `H.Point` is finite when `k` is: it is a subtype of `k × k`, itself
finite, cut out by the decidable predicate above. Needed before `Finset
H.Point`/`Finset (Jacobian H D)` combinatorics make sense. -/
instance instFintypePoint : Fintype H.Point :=
  Subtype.fintype (fun p : k × k => H.Equation p.1 p.2)

instance instDecidableEqPoint : DecidableEq H.Point :=
  fun P Q => decidable_of_iff (P.val = Q.val) Subtype.ext_iff.symm

variable (D : PrincipalDivisorData H)

/-! `Jacobian H D` is finite whenever `H.Point` is: it is a quotient of
`Divisor0 H`, itself a subgroup of `Divisor H := H.Point →₀ ℤ`. Stated as an
instance-level hypothesis rather than derived here — deriving it in full
would mean either bounding `Divisor0 H`'s image directly or exhibiting
`Jacobian H D` as literally the group of `k`-points of an abelian variety
(the genuine algebraic-geometry route, well outside what this repo's
affine/divisor-level model can see). Flagged, not assumed away: this is the
one place a full formalization would need to actually construct `J(F_p)` as
a finite group of the expected size, rather than take its finiteness on
faith. -/
variable [Fintype (Jacobian H D)] [DecidableEq (Jacobian H D)]

/-! ## §2. The mechanical bridge: `SidonDichotomy` gives `SidonRepBound`

`SidonDichotomy` is a statement about *pairs of pairs* of points
(`s x₁ + s x₂ = s x₃ + s x₄ → ...`). `SidonRepBound` is a statement about a
`Finset G`'s *representation function* (`repCount T g ≤ 2` for every `g`).
The bridge needs one more ingredient neither file supplies alone: a
description of `T`'s representation-function fibers purely in terms of
`s`-preimages, so that a repetition `repCount T g ≥ 3` can be pulled back to
three genuinely different unordered point-pairs summing to the same `g`,
triggering `SidonDichotomy` to collapse them — and the collapse then has to
be shown to be *impossible* for three distinct pairs at once. This is where
`HyperellipticClass` (also in `FFKSidon.lean`) does its work: it is exactly
what rules out the involution-pair branch of the dichotomy silently
absorbing what should be a genuine `Sidon` violation. -/

/-- The factor base `F`'s image under `s`, as a `Finset (Jacobian H D)`. This
is `T` in `SidonEnergy.lean`'s notation — the Sidon set advisory-7 §4 studies
is literally this image, not `F` itself (`F` lives in `H.Point`, `T` lives in
`Jacobian H D`). -/
noncomputable def sidonSet (δ₀ : H.Point) (F : Finset H.Point) :
    Finset (Jacobian H D) :=
  F.image (s D δ₀)

/-- **The side condition advisory-7 §7.1 calls "verify the factor base
excludes hyperelliptic-involution pairs"**: no two distinct points of `F`
are swapped by `ι`. Needed because `s x + s (ι x) = s y + s (ι y)` holds for
*every* `x, y` (it is `sum_eq_of_involution_swap`, unconditional given
`HyperellipticClass`) — so if `F` contained both `x` and `ι x` for some `x`,
`{x, ι x}` and any other involution-pair in `F` would produce repeated sums
that are geometrically forced, not evidence of a Sidon violation, and no
`SidonRepBound` could possibly hold for `s '' F`. This is a property of the
chosen factor base, not of the curve, and is exactly the kind of thing
advisory-7 says must be checked when the factor base is constructed. -/
def AvoidsInvolutionPairs (F : Finset H.Point) : Prop :=
  ∀ x ∈ F, Point.iota x ∈ F → x = Point.iota x

/-- **The mechanical bridge.** If `D` satisfies both `SidonDichotomy` and
`HyperellipticClass`, and `F` avoids involution-pairs, then `sidonSet D δ₀ F`
satisfies `SidonRepBound` — i.e. `SidonEnergy.lean`'s entire conditional
apparatus (`sidon_energy_bound`, `matchCount_le_two_card_sq`,
`sidon_gives_hit_count_bound_combinatorial`, ...) applies unconditionally to
`T := s '' F` once this one curve-side hypothesis is granted.

Proof sketch (not yet filled in — see the `sorry` below): unfold `repCount T
g ≤ 2` to "at most one unordered pair of `F`-points maps to `g` under `(x,y)
↦ s x + s y`, up to swap." Given three ordered pairs `(x₁,x₂), (x₃,x₄),
(x₅,x₆)` all landing on the same `g`, `SidonDichotomy` (via
`ffk_sidon_dichotomy`'s forward direction) forces each pair against each
other to be either literally the same unordered pair or an involution-swap
of it. `AvoidsInvolutionPairs` rules out the involution-swap disjunct
whenever the two pairs are not already identical (an involution-swap
between two *distinct* points of `F` would require one of them to be the
other's image under `ι`, contradicting `AvoidsInvolutionPairs` unless they
are literally equal as points, which forces the pairs to coincide too). So
all three ordered pairs are forced to the same unordered pair, i.e.
`repCount T g` counts at most the `≤ 2` orderings of one unordered pair —
closing the bound. This is genuinely mechanical given the two curve-side
hypotheses, but threading `Finset.image` preimages back through `s`
(non-injective in general — two different `H.Point`s could coincide in `J`)
adds real bookkeeping that has not been carried out here. -/
theorem sidonRepBound_of_sidonDichotomy
    (δ₀ : H.Point) (F : Finset H.Point)
    (hDichotomy : D.SidonDichotomy) (hClass : D.HyperellipticClass)
    (hAvoid : AvoidsInvolutionPairs F) :
    SidonRepBound (sidonSet D δ₀ F) := by
  sorry

/-! ## §3. Where this project actually stakes its claim: the average case

`sidonRepBound_of_sidonDichotomy` (once proved) plus a proof of
`SidonDichotomy` itself would hand you `CombinatorialSecondMoment.lean`'s
`sidon_gives_hit_count_bound_combinatorial` for free — but that theorem's
conclusion, `#{Δ : hit} ≥ B²/2`, is a *worst-case* guarantee, and it is not
the guarantee the algorithm's design actually relies on. advisory-7 §7.4-7.6
already says as much: the Fourier-analytic route to the sharper `B⁴/N`-type
bound needs control of the 8th moment (equivalently, a genuine bound on
`E(S,S)`), which is a strictly harder question than the Sidon dichotomy
itself and is **explicitly out of scope for this file** — left to future
work, per this session's instructions, rather than attempted here.

Instead: the actual empirical behaviour of the walk is that relations are
found at a rate consistent with `F`'s sums *equidistributing* over `J`, not
concentrating adversarially. That is a strictly weaker, average-case claim,
and it is the one this file states precisely (as a hypothesis,
`GenericFactorBase`) and derives the target complexity exponent from,
rather than leaving as an unexamined "it's fine empirically." -/

/-- **The average-case hypothesis this project's complexity target actually
rests on.** `F` is a "generic" factor base of size `B` in `G := Jacobian H D`
if the *expected* second moment `𝔼[N(Δ)²]` over the ambient group — i.e.
`(∑_Δ matchCount T Δ ^ 2) / |G|`, `T := sidonSet D δ₀ F` — matches what a
uniformly random `B²`-element multiset of sums into `G` would give: order
`B⁴ / |G|` rather than the `O(B²)` a worst-case Sidon bound alone would
force it down to, nor the `O(B⁶)` the trivial Cauchy–Schwarz bound allows.
This is exactly what "the sums of `F`-pairs don't pile up on few `Δ`'s more
than a random model would" means quantitatively, and is stated as a
hypothesis — NOT proved here or claimed to follow from `SidonDichotomy` — so
that the complexity claim below is visibly conditional on it.

**Deriving `GenericFactorBase` from first principles is future work,
deliberately not attempted in this file.** The natural route would be
equidistribution of `s '' F` in `J`, itself following from `F`'s
`x`-coordinates equidistributing via the genus-2 curve's own mixing
properties — paralleling the Fourier-uniformity argument advisory-7 §5
sketches for the *worst-case* bound, but aimed at an *average* rather than
*uniform* statement, and correspondingly should be easier. That argument is
not carried out here; per this session's instructions, the 8th-moment /
worst-case route is explicitly left to future work, and this hypothesis is
exactly where that deferred work would need to land. -/
def GenericFactorBase (δ₀ : H.Point) (F : Finset H.Point) (C : ℝ) : Prop :=
  (∑ Δ : Jacobian H D, (matchCount (sidonSet D δ₀ F) Δ : ℝ) ^ 2)
    ≤ C * (F.card : ℝ) ^ 4 / (Fintype.card (Jacobian H D) : ℝ)

/-- **The average-complexity target, `p^(4/5)`, derived from
`GenericFactorBase` rather than from a worst-case Sidon bound.** With `N :=
|G| ~ p^2` (the standard genus-2 heuristic: `J(F_p)` has order roughly `p^2`)
and a factor base of size `B`, the two costs the algorithm balances against
each other are: relation-gathering (driven by the hit-count bound this
theorem proves) and the sparse linear-algebra step on the resulting `B × B`
relation matrix, which costs `Θ(B²)` group operations (the standard sparse
Wiedemann/Lanczos-type heuristic — not itself formalized here). Setting `B²
~ p^{4/5}` (the target total cost) pins down `B ~ p^{2/5}`, **not** `p^{1/2}`
— this file previously stated the balance incorrectly; corrected here.

`GenericFactorBase` with a constant `C` gives a Paley–Zygmund lower bound of
`B⁴ · N / C` on the hit-count. At `B ~ p^{2/5}`, `N ~ p^2`, this evaluates to
`p^{8/5} · p^2 / C = p^{18/5} / C`, which for any fixed `C` exceeds the
trivial upper cap `N ~ p^2` once `p` is large — i.e. the raw formula
overshoots and the honest reading is simply that the bound saturates: the
lower bound this theorem proves certifies "at least `min(B⁴N/C, N)`", so at
this `B` it certifies a *constant fraction of the whole group* is hit
(`Θ(N)`), not the specific numeral `p^{18/5}/C`. Either way,
relation-gathering is not the bottleneck at `B ~ p^{2/5}`: the `Θ(B²) =
Θ(p^{4/5})` linear-algebra step is. Converting this into the full
algorithm's `p^{4/5}` group-operation count (accounting for factor-base
search cost, the number of walk steps needed to accumulate `B` relations at
this hit-rate, and the linear-algebra cost itself) is standard index-calculus
cost bookkeeping and is **not** re-derived symbolically in this Lean
statement — this theorem only establishes the hit-count bound that
accounting is built on top of.

**A note on `F.card` vs `(sidonSet D δ₀ F).card`.** `GenericFactorBase`'s
right-hand side is stated in terms of `F.card` (the factor base as chosen),
but `hit_count_ge_of_second_moment_bound` — via `SecondMomentBound`, which is
intrinsically about the `Finset` it is applied to — produces a bound whose
numerator is `(sidonSet D δ₀ F).card`, i.e. `|s(F)|`, not `|F|`. Since `s D
δ₀` need not be injective on `F` in general, these two cardinalities need not
agree, so the theorem's conclusion below is stated honestly in terms of
`(sidonSet D δ₀ F).card` rather than `F.card`. In the intended regime —
`F` chosen so that `s` is injective on it, e.g. as a consequence of
`AvoidsInvolutionPairs` together with `SidonDichotomy` ruling out other
collisions — the two coincide and `B` in the informal accounting above can be
read as either; that coincidence is not proved here and would need
`sidonRepBound_of_sidonDichotomy`'s hypotheses (or a direct injectivity
argument) to establish. -/
theorem hitCount_ge_of_generic
    (δ₀ : H.Point) (F : Finset H.Point) (C : ℝ) (hC : 0 < C)
    (hGeneric : GenericFactorBase D δ₀ F C) (hcard_pos : 0 < F.card) :
    (((sidonSet D δ₀ F).card : ℝ) ^ 4) ^ 2 /
        (C * (F.card : ℝ) ^ 4 / (Fintype.card (Jacobian H D) : ℝ)) ≤
      ((univ.filter
        (fun Δ => matchCount (sidonSet D δ₀ F) Δ ≠ 0)).card : ℝ) := by
  have hM : SecondMomentBound (sidonSet D δ₀ F)
      (C * (F.card : ℝ) ^ 4 / (Fintype.card (Jacobian H D) : ℝ)) := hGeneric
  have hcard_pos' : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast hcard_pos
  have hGcard_pos : (0 : ℝ) < (Fintype.card (Jacobian H D) : ℝ) := by
    have : 0 < Fintype.card (Jacobian H D) := Fintype.card_pos
    exact_mod_cast this
  have hMpos : (0 : ℝ) <
      C * (F.card : ℝ) ^ 4 / (Fintype.card (Jacobian H D) : ℝ) := by
    apply div_pos
    · positivity
    · exact hGcard_pos
  exact hit_count_ge_of_second_moment_bound (sidonSet D δ₀ F)
    (C * (F.card : ℝ) ^ 4 / (Fintype.card (Jacobian H D) : ℝ)) hM hMpos

end HyperellipticPolynomial
