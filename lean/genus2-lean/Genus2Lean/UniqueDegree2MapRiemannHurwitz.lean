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
set_option linter.style.header false

noncomputable section

open Classical


open Polynomial

/-!
# A Riemann–Hurwitz proof skeleton for `uniqueDegree2MapToP1`

**This file proves nothing yet — it is a skeleton**, in the same spirit as
`OrdAtExtended.lean`'s diagnosis-before-repair pass: it decomposes
`RiemannRochCrux.lean`'s remaining `sorry`, `uniqueDegree2MapToP1`, into a chain
of individually named, individually cited sub-facts, so that closing it (if it
is ever closed directly rather than by import from elsewhere) is a sequence of
scoped tasks rather than one monolithic gap.

## Why Riemann–Hurwitz, and why it's hard here specifically

`RiemannRochCrux.lean`'s module docstring already identifies the two possible
routes to `uniqueDegree2MapToP1`: Riemann–Hurwitz ramification counting, or the
general classification of `g^1_2` linear systems on a curve. This file commits
to the Riemann–Hurwitz route and spells out what it actually requires, because
none of it is free:

* **No morphism-to-`P¹` type exists in this project.** `H.Point`, `Divisor H`,
  `ordAt`, `ordInfOfPair` give pole/zero bookkeeping for elements of
  `FractionRing (CoordinateRing H)`, but nothing currently packages "a degree-2
  rational map `C → P¹`" as a first-class object with a notion of ramification
  index at a point. §1 below has to build this from the existing pole/zero
  data rather than import it.
* **No ramification-point-counting or genus-formula infrastructure exists.**
  `riemann_roch_dim_identity` (`HyperellipticFunctionField.lean`) encodes
  `g = 2` only implicitly, through the Riemann–Roch dimension formula for
  `L(n P_∞)`; it does not give a general Riemann–Hurwitz formula
  `2g_C - 2 = d(2g_{P¹} - 2) + Σ_P (e_P - 1)` for an arbitrary degree-`d` map.
  §3 below has to state this specialized to `d = 2`, `g_C = 2`, `g_{P¹} = 0`
  directly (giving `Σ(e_P - 1) = 6`, i.e. exactly 6 simple ramification points
  for a degree-2 map on a genus-2 curve) rather than derive it from a general
  formula, since no general formula is formalized here.
* **Points at infinity are a known, separately flagged gap.** `AffinePoints.lean`
  and `PrincipalDivisorSubgroup.lean` both note that `H.Point` only covers
  affine points and that the point(s) at infinity are excluded by design (see
  their module docstrings). The hyperelliptic map's own ramification includes
  the point at infinity whenever `H.f.natDegree` is odd (as `hdeg : H.f.natDegree
  = 5` forces here) — a single ramified point at infinity, alongside the 5
  finite Weierstrass points, giving the 6 total ramification points Riemann–
  Hurwitz predicts. §2's statements below have to either work around this gap
  explicitly (stating the infinity contribution as a separate hypothesis /
  citation) or wait on it being closed elsewhere first; not resolved here.

Given all of this, the sub-facts below are stated as the actual content
required, not as restatements of `uniqueDegree2MapToP1` under new names — each
is a genuine, citable classical fact (Riemann–Hurwitz, or standard hyperelliptic
curve theory, e.g. Liu *Algebraic geometry and arithmetic curves* Ch. 7, or
Hartshorne IV.2), scoped small enough that a future session could plausibly
attack one at a time.

## Assembly, once §1–§4 are closed

`uniqueDegree2MapToP1_of_ramification_uniqueness` at the bottom shows how the
pieces combine into exactly `RiemannRochCrux.lean`'s statement, so that once
§1–§4 are proved, wiring the result back in is mechanical (swap
`RiemannRochCrux.lean`'s `sorry` for a call to that theorem, importing this
file the same way `RatioDivisorCollapse.lean` was wired in).

**Verification status: drafted without a live Lean toolchain — statements only,
no proof attempted at any step; every `sorry` in this file is intentional and
should stay a `sorry` until the corresponding classical fact is actually
formalized, not discharged by `simp`/`decide`/similar.**
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-! ## §1. A degree-2 rational map, as a first-class notion

Nothing in this project currently packages "a rational function `z` exhibits a
degree-2 map `C → P¹`". Rather than inventing a fresh existentially-quantified
pole-degree sum (which would need its own finiteness lemma before it could even
be stated), this reuses `PrincipalDivisorSubgroup.lean`'s existing
`divToPair`/`divToPairRatio` machinery directly: `divToPair A' B' S'` is
already a well-defined `Divisor H` (a finite formal sum, `S'` supplied
explicitly as its support witness, exactly `IsPoleBoundedAtPair`'s and
`LPairCarrier`'s own convention), and `deg_div_eq_zero_deg5` already proves
`∑_{P ∈ S'} ordAt P A' B' = -ordInfOfPair A' B'` given `S'` is a genuine
support (i.e. `ordAt` vanishes outside it) — so "pole degree away from
infinity" doesn't need a fresh `max(_, 0)` sum invented from scratch; it's
read off the same `deg_div_eq_zero_deg5` identity §1 already has available,
no new finiteness sorry required. What §1 still cannot avoid inventing is the
"positive part only" restriction — `deg_div_eq_zero_deg5`'s sum is the full
signed order, whereas "pole degree" wants only the points where `A', B'`
strictly out-vanishes `A, B`. That restriction is captured below by requiring
the two supports `S, S'` be *disjoint* (`hdisj`) rather than filtering with
`max`: at a disjoint pair of supports, `divToPair A B S`'s and `divToPair A'
B' S'`'s nonzero orders never overlap, so their difference's degree already
*is* signed correctly without a `max`. -/

/-- **A rational function has degree-2 pole divisor.** `z = toPair H A B /
toPair H A' B'`, presented via disjoint finite supports `S` (for the
numerator's zeros) and `S'` (for the denominator's zeros, i.e. `z`'s poles),
with matching `ordInfOfPair` (so the total divisor, `divToPairRatio A B S A'
B' S'`, is genuinely `deg`-zero via `deg_divToPairRatio_eq_zero` — the same
condition `PrincipalDivisorSubgroup.lean`'s principal-divisor generators
already require) and pole degree away from infinity, `∑_{P ∈ S'} ordAt P A'
B'`, plus the contribution at infinity, `-ordInfOfPair A' B'`, summing to
exactly `2`. Disjointness of `S, S'` (the `Disjoint S S'` conjunct) is what
makes `∑_{P ∈ S'} ordAt P A' B'` genuinely "the pole degree" rather than a
signed total that could cancel against zeros counted in `S` — at any `P ∈ S'`,
`P ∉ S` forces `ordAt P A B = 0` (nothing to cancel against) whenever `S` is
also a genuine support for `A, B` (the "`∀ P, P ∉ S → ordAt P A B = 0`"
conjunct), so the sum is a pure pole count. -/
def IsDegree2Map (z : FractionRing (CoordinateRing H)) : Prop :=
  ∃ A B A' B' : k[X], ∃ S S' : Finset H.Point,
    ¬ (A' = 0 ∧ B' = 0) ∧
    z = algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A B) /
        algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A' B') ∧
    Disjoint S S' ∧
    (∀ P, P ∉ S → ordAt P A B = 0) ∧
    (∀ P, P ∉ S' → ordAt P A' B' = 0) ∧
    (∑ P ∈ S', ordAt P A' B') + (- ordInfOfPair A' B') = 2

/-! ## §2. Ramification of a degree-2 map

A point `P` is a ramification point of the degree-2 map exhibited by `z` iff
the map is 2-to-1 there in the scheme-theoretic sense: `z - z(P)` (or, if `P`
is itself a pole of `z`, the appropriate uniformizer-normalized statement) has
a double zero at `P` rather than two simple zeros at `P` and some `P' ≠ P`.
Concretely, for the hyperelliptic map `x` itself: `P` is ramified iff
`P = ι P`, i.e. `P.Y = 0` (a Weierstrass point) — this is the case
`HyperellipticClassProof.lean`'s `ordAt_linX_eq_two_of_ramified` sorry already
names and is working on, independently of this file.

**Made precise below via `evalAtPoint`** (`PrincipalDivisors.lean`):
`evalAtPoint P : CoordinateRing H →+* k` is the ring hom "evaluate at `P`",
with `pointIdeal P = ker (evalAtPoint P)` — so `evalAtPoint P (toPair H A B) =
0` exactly captures `toPair H A B ∈ pointIdeal P`, i.e. `ordAt P A B > 0`. This
gives "the value of `z = toPair H A B / toPair H A' B'` at `P`" whenever `P`
isn't a pole (`evalAtPoint P (toPair H A' B') ≠ 0`): the field element
`evalAtPoint P (toPair H A B) / evalAtPoint P (toPair H A' B')`, and
ramification there is `ordAt P` of the value-shifted numerator equaling `2`
rather than `1`. When `P` *is* a pole, ramification is instead read directly
off the pole order, `ordAt P A' B' = 2`. -/

/-- **A point is a ramification point of the degree-2 map exhibited by `z`.**
Existentially quantifies over a representation `A, B, A', B'` of `z` (any valid
one gives the same answer, since ramification is a property of `z` itself, not
of how it happens to be written — that representation-independence is not
proved here, only assumed implicit in the `Prop`'s well-definedness, same as
`IsConstantFraction`/`IsDegree2Map` already assume `toPair`-representations of
a fixed `z` behave consistently). Two cases: `P` is a pole of `z` (`A' B'`'s
value at `P` is `0`), where ramification means a double pole, `ordAt P A' B' =
2`; or `P` isn't a pole, where ramification means the value-shifted numerator
`toPair H A B - c • toPair H A' B'` (`c` being `z`'s actual value at `P`) has a
double zero, `ordAt P (A - c • A') (B - c • B') = 2` — phrased at the
polynomial-pair level via scalar multiplication on `k[X]`, matching how every
other pair-level statement in this project (`IsPoleBoundedAtPair`, `toPair`
itself) stays at the `A, B : k[X]` level rather than lifting to
`CoordinateRing H` combinations. -/
def IsRamificationPointOf (z : FractionRing (CoordinateRing H)) (P : H.Point) : Prop :=
  ∃ A B A' B' : k[X], ¬ (A' = 0 ∧ B' = 0) ∧
    z = algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A B) /
        algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H A' B') ∧
    (if evalAtPoint P (toPair H A' B') = 0 then
      ordAt P A' B' = 2
    else
      ordAt P (A - C (evalAtPoint P (toPair H A B) / evalAtPoint P (toPair H A' B')) * A')
               (B - C (evalAtPoint P (toPair H A B) / evalAtPoint P (toPair H A' B')) * B') = 2)

/-- **The hyperelliptic map's ramification is exactly the Weierstrass points.**
For the specific degree-2 map exhibited by `z = x` (i.e. `toPair H X 0` over
`toPair H 1 0`, the coordinate function itself), `P` ramifies iff `P.Y = 0`.

**Update: no longer an opaque `sorry`.** Tracing what `IsRamificationPointOf`
unfolds to for this specific `z` shows the "genuinely hard" content this
docstring originally described (citing `HyperellipticClassProof.lean`'s
`ordAt_linX_eq_two_of_ramified`/`pointIdeal_linX_not_sq_dvd` as in-progress) was
already fully discharged there by the time this file was drafted, via the
combined case-split lemma `ordAt_linX_eq` — this theorem is a direct corollary
of it, not independent hard work. Two gaps remain, both *bookkeeping*, not
mathematics, and both isolated below as named `have`s rather than left buried:

1. **Extra hypotheses needed.** `ordAt_linX_eq` needs `hchar : (2:k) ≠ 0` and
   `hsf : Squarefree H.f` (Dedekind-domain char-2/squarefreeness side
   conditions — see `NonsingularData` in `PrincipalDivisors.lean`, and the
   note in `HyperellipticFunctionField.lean` that `Squarefree H.f` is a
   genuine, non-derivable hypothesis, not a consequence of `hdeg` alone).
   `RiemannRochCrux.lean`'s `uniqueDegree2MapToP1` (this file's ultimate
   target) does not currently thread these through either — whoever wires
   this file's results back in needs to add them to the signature chain, not
   just here.
2. **`z`'s denominator is always nonvanishing.** `toPair H 1 0 = 1`
   (`toPair_one_zero`), so `IsRamificationPointOf`'s `if` always takes the
   "not a pole" branch for this specific `z`; the shifted numerator collapses
   to exactly `linX P.X` after evaluating `toPair H X 0` at `P`. -/
theorem hyperelliptic_ramification_eq_weierstrass
    (hdeg : H.f.natDegree = 5) (hchar : (2 : k) ≠ 0) (hsf : Squarefree H.f)
    (P : H.Point) :
    IsRamificationPointOf
      (algebraMap (CoordinateRing H) (FractionRing (CoordinateRing H)) (toPair H X 0))
      P ↔ P.Y = 0 := by
  classical
  -- Step 1: `evalAtPoint P (toPair H X 0) = P.X` — evaluating the coordinate
  -- function `x` at `P` reads off `P`'s own `X`-coordinate. Same computation
  -- as `pointIdeal_ne_of_ne`'s `hXeval` in `PrincipalDivisors.lean`, just
  -- for `toPair H X 0` (`= algebraMap k[X] (CoordinateRing H) X`, the `B = 0`
  -- term of `toPair` vanishing) rather than a difference of two such terms.
  have hXeval : evalAtPoint P (toPair H X 0) = P.X := by
    have hg : toPair H X 0 = algebraMap k[X] (CoordinateRing H) X := by
      unfold toPair; simp
    rw [hg]
    change Polynomial.eval₂ (Polynomial.evalRingHom P.val.1) P.val.2 (C X) = P.X
    simp [Point.X]
  -- Step 2: `evalAtPoint P (toPair H 1 0) = 1` — the denominator is the unit
  -- `1`, so it never vanishes and `IsRamificationPointOf`'s pole branch never
  -- fires for this `z`.
  have hDeval : evalAtPoint P (toPair H (1 : k[X]) 0) = 1 := by
    rw [toPair_one_zero]; exact map_one _
  -- Step 3: `ordAt_linX_eq` specialized to `a := P.X`, `Q := P` — the `if`'s
  -- guard `P.X ≠ P.X` is `False` by `rfl`, collapsing it to the two-way split
  -- on `P.Y ≠ 0` that matches this theorem's target `↔` almost verbatim.
  have hordAt : ordAt P (linX P.X) 0 = if P.Y ≠ 0 then 1 else 2 := by
    have h := ordAt_linX_eq hchar hsf P.X P (pointIdeal_ne_bot P)
    rwa [if_neg (fun hcontra => hcontra rfl)] at h
  -- Step 4: repackage step 3 as the exact "not a pole" branch of
  -- `IsRamificationPointOf` for this `z`'s canonical representation
  -- `A = X, B = 0, A' = 1, B' = 0`: the shifted pair `(X - C(.../1)) * A', ...)`
  -- collapses to `(linX P.X, 0)` via steps 1–2, once `evalAtPoint P (toPair H
  -- X 0)`/`evalAtPoint P (toPair H 1 0)` are rewritten via `hXeval`/`hDeval`
  -- (folded directly into the final `rw` chains below, rather than
  -- pre-packaged as standalone `have`s, since `rw [hDeval]` alone already
  -- rewrites every occurrence of the denominator term in one pass — a
  -- separate `hshiftA`/`hshiftB` stated against the *pre*-`hDeval` shape
  -- stops matching as soon as `hDeval` fires earlier in the same chain).
  constructor
  · rintro ⟨A, B, A', B', hA'B', hzeq, hram⟩
    -- **Genuine gap, not bookkeeping: representation-independence.**
    -- `IsRamificationPointOf`'s definition existentially quantifies over
    -- *some* `(A,B,A',B')` representing `z`; the hypothesis obtained here is
    -- about whichever representation the existential handed back, not
    -- necessarily the canonical `(X,0,1,0)` steps 1–4 above were computed
    -- for. Closing this needs exactly the fact this file's own docstring
    -- above already flags as assumed-but-unproved: that `IsRamificationPointOf`
    -- gives the same verdict regardless of which valid `(A,B,A',B')`
    -- represents a fixed `z` (two representations of the same `z` differ by
    -- a common unit factor in `CoordinateRing H`, so their `ordAt`s agree —
    -- an argument in the same style as `mem_LPairCarrier_of_isRatioDivisor`'s
    -- `hordeq` step in `RatioDivisorCollapse.lean`, but for a *ramification*
    -- statement rather than a divisor-equality one, so not a direct reuse).
    -- Once that representation-independence lemma exists, this direction is:
    -- specialize it to the canonical representation, then rewrite via
    -- `hXeval`/`hDeval`/`hordAt` (same chain as the `mpr` case below) to turn
    -- `hram` (or its specialized image) directly into
    -- `if P.Y ≠ 0 then 1 else 2 = 2`, and `by_contra` + `split_ifs` finishes
    -- (`P.Y ≠ 0` would force `1 = 2`, absurd).
    sorry
  · intro hY
    -- `P.Y = 0`: exhibit the canonical representation directly (no
    -- representation-independence needed, since we get to *choose* the
    -- witness here rather than receive an arbitrary one) and discharge via
    -- steps 1–3, rewriting `evalAtPoint`'s two values in one pass so the
    -- `if`'s guard and body both land in the post-rewrite shape together.
    refine ⟨X, 0, 1, 0, by simp, ?_, ?_⟩
    · rw [toPair_one_zero, map_one, div_one]
    · rw [hXeval, hDeval, if_neg one_ne_zero, div_one, mul_one, mul_zero, sub_zero,
        show X - C P.X = linX P.X from rfl, hordAt, if_neg (by simp [hY])]

/-! ## §3. Riemann–Hurwitz, specialized to this case

The general Riemann–Hurwitz formula for a degree-`d` separable map `φ : C → C'`
between smooth projective curves over an algebraically closed field (or, with
care, a perfect field) of characteristic `0` or `> 2d - 1`:

  `2 g_C - 2 = d (2 g_{C'} - 2) + Σ_{P ∈ C} (e_P - 1)`

specializes, for `C' = P¹` (`g_{C'} = 0`), `d = 2`, `g_C = 2` (this project's
standing genus-2 hypothesis, encoded throughout via `H.f.natDegree = 5`), and
every ramification index `e_P ∈ {1, 2}` for a degree-2 map (so `e_P - 1 ∈
{0, 1}`, i.e. the sum counts ramification points with multiplicity `1` each),
to: **a degree-2 map `C → P¹` has exactly 6 ramification points, counted
without multiplicity** (`2·2 - 2 = 2` gives `Σ(e_P - 1) = 2 + 2 = ... `; the
precise arithmetic — `2g - 2 = -2d + Σ(e_P - 1)`, i.e. `Σ(e_P-1) = 2g-2+2d =
2+4 = 6` for `g=2, d=2` — is elementary once the formula itself is granted, and
is NOT re-derived here, only the count `6` is asserted as the citable
consequence). Citation: Liu, *Algebraic geometry and arithmetic curves*, Thm
7.4.16 (Riemann–Hurwitz); Hartshorne, *Algebraic Geometry*, Cor. IV.2.4. -/

/-- **Riemann–Hurwitz, specialized**: any `z` with `IsDegree2Map z` has exactly
6 points `P : H.Point` (plus, depending on how the points-at-infinity gap
above is ultimately resolved, possibly the point at infinity itself) with
`IsRamificationPointOf z P`. Stated here via a `Finset` cardinality rather than
an abstract sum over `e_P - 1`, since every ramification index is `2` for a
degree-2 map (no room for higher ramification), collapsing the general sum to
a plain count. **This is the genuinely hard external input** — it is exactly
Riemann–Hurwitz, cited above, not a consequence of anything else in this
project. -/
theorem card_ramification_eq_six
    (hdeg : H.f.natDegree = 5) (z : FractionRing (CoordinateRing H))
    (hz : IsDegree2Map z) :
    ∃ S : Finset H.Point, S.card = 6 ∧ ∀ P, P ∈ S ↔ IsRamificationPointOf z P := by
  sorry

/-! ## §4. Two degree-2 maps with the same ramification differ by a Möbius map

The last classical ingredient: a degree-2 map `C → P¹` is determined, up to
post-composition by an automorphism of `P¹` (a Möbius transformation), by its
ramification divisor alone. This is the actual uniqueness statement — a
degree-2 map is *the* hyperelliptic map (composed with a Möbius transform)
because genus-2 curves have a *unique* degree-2 map to `P¹` up to this
equivalence (this is the fact `RiemannRochCrux.lean` cites directly: Forey–
Fresán–Kowalski citing Liu, Remark 7.4.30). Concretely: since §3 forces both
maps' ramification to be the same 6-point set (both must equal the
Weierstrass points, via §2, since — by this very uniqueness — there is only
one hyperelliptic structure on `C`), any second nonconstant `z ∈ LPairCarrier
x₁ x₂` with `x₂ ≠ ι x₁` cannot itself be a degree-2 map with the "right"
ramification (its pole set `{x₁, x₂}` is not a fiber of the hyperelliptic
map unless `x₂ = ι x₁`, contradicting `hne`), forcing `z` to be constant —
`IsConstantFraction`. -/

/-- **Non-fiber pole pairs cannot come from a degree-2 map with Weierstrass
ramification.** If `z ∈ LPairCarrier x₁ x₂` is a degree-2 map (`IsDegree2Map`)
whose ramification is exactly the Weierstrass points (i.e. `z` is, up to a
Möbius transform, the hyperelliptic map itself — the content §4's docstring
above describes), then its pole set `{x₁, x₂}` must be a hyperelliptic fiber,
i.e. `x₂ = ι x₁`. Stated as the direct contrapositive of what
`uniqueDegree2MapToP1` needs. -/
theorem pole_pair_eq_fiber_of_degree2_weierstrass_ramified
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (z : FractionRing (CoordinateRing H)) (hz : z ∈ LPairCarrier x₁ x₂)
    (hdeg2 : IsDegree2Map z)
    (hram : ∀ P, IsRamificationPointOf z P ↔ P.Y = 0) :
    x₂ = Point.iota x₁ := by
  sorry

/-- **Every nonconstant element of `LPairCarrier x₁ x₂` is a degree-2 map.**
The converse direction §4 also needs: `LPairCarrier`'s definition
(`IsPoleBoundedAtPair`) already bounds poles by at most `1` at each of `x₁,
x₂`, i.e. total pole degree at most `2`; a *nonconstant* such `z` has pole
degree *exactly* `2` (not `0` or `1`, since degree `0` means constant and
degree `1` is impossible — a degree-1 map `C → P¹` would exhibit `C ≅ P¹`,
impossible for `g = 2 ≠ 0`, citing the standard fact that a curve admitting a
degree-1 map to `P¹` has genus `0`).

**Skeletonized, not proved: decomposed into named sub-facts below rather than
left as one opaque `sorry`, per this session's convention of naming the actual
blocker instead of hiding it in a single tactic block.** None of these
sub-facts is a restatement of the theorem under a new name — each is real,
separable content:

* **`isDegree2Map_of_isPoleBoundedAtPair_of_supportWitness`** (stated below,
  not proved): the *mechanical-modulo-two-gaps* direction. Even granted an
  explicit finite support `S'` for `A', B'` (see next bullet) and matching
  `hspec'`/`Module.Finite` side data, `IsPoleBoundedAtPair`'s
  `ordInfOfPair A B ≥ ordInfOfPair A' B'` is only an *inequality* — it does
  not itself pin `ordInfOfPair A' B' = -1`, which `IsDegree2Map`'s pole-count
  conjunct needs to combine with `deg_div_eq_zero_deg5`'s
  `(∑_{S'} ordAt) + ordInfOfPair A' B' = 0` to get the required
  `∑_{S'} ordAt + (-ordInfOfPair A' B') = 2`. So even this "easy" direction
  is not pure bookkeeping; it silently needs a genus/degree bound (pole order
  at infinity is bounded by the pair's polynomial degrees via `ordInfOfPair`'s
  own formula, so ruling out anything other than exactly `-1` for a pair
  drawn from a `LPairCarrier x₁ x₂` witness — as opposed to some other pole
  order — is itself unformalized content, not attempted here).
* **The `S'` witness itself is not constructible** from what
  `IsPoleBoundedAtPair`/`LPairCarrier` alone supply — the same Dedekind-domain
  "a nonzero element of `CoordinateRing H` has finitely many zero/pole
  points" gap flagged in this file's earlier session notes (traced to
  Mathlib's `UniqueFactorizationMonoid`/`Associates.factors` machinery
  supplying finiteness only at the level of height-one primes of
  `CoordinateRing H`, not yet connected to a `Finset H.Point` via a
  prime-to-point correspondence this codebase hasn't built).
* **Degree-`0` exclusion** (needed to use `hnc`): pole degree `0 ↔
  IsConstantFraction z` — would need "an element of `FractionRing
  (CoordinateRing H)` with no poles anywhere is a `k`-constant", a
  nontrivial fact about the coordinate ring's global sections, not present
  in this project.
* **Degree-`1` exclusion**: as the docstring above already notes, ruling out
  pole degree exactly `1` needs "a degree-1 map `C → P¹` forces genus `0`" —
  checked via `grep` this session: not formalized anywhere in this codebase,
  only asserted in prose here. A genuinely separate classical citation from
  Riemann–Hurwitz itself (it's closer to "a curve with a degree-1 map to
  `P¹` is `P¹`" / Lüroth-type territory), so not attempted here either. 

 **Skeleton sub-lemma, `sorry`-free but not directly usable, for the same
reason as its parent, stated explicitly so the missing witness is visible in
the signature rather than buried in a tactic block.** Given
`IsPoleBoundedAtPair x₁ x₂ A B A' B'` data, an explicit finite support `S'`
for the denominator pair with the same `hspec'`/`Module.Finite` side
conditions `deg_div_eq_zero_deg5` needs elsewhere in this project, and the
extra pin `ordInfOfPair A' B' = -1` (see the module docstring above for why
`IsPoleBoundedAtPair`'s inequality alone doesn't give this — note this is
`-1`, not the more intuitive-looking `-2`: `deg_div_eq_zero_deg5` gives
`affine_sum = -ordInfOfPair A' B'`, and `IsDegree2Map`'s own pole-count
conjunct is `affine_sum + (-ordInfOfPair A' B') = 2`, i.e.
`-2 · ordInfOfPair A' B' = 2`, forcing `ordInfOfPair A' B' = -1` exactly —
this was gotten wrong in an earlier draft of this lemma, which asserted `-2`
by analogy with `ordInfOfPair_linX` and only caught the sign/arithmetic error
by running `omega` against both equations together and finding them
inconsistent), the pole-count conjunct `IsDegree2Map` needs follows from
`deg_div_eq_zero_deg5` applied to `S', A', B'` by `omega`. **This lemma's own
proof is complete and bookkeeping-only; its *use* still needs the
`S'`/`hspec'`/`Module.Finite`/`ordInf = -1` hypotheses supplied by a caller,
none of which this project can currently derive for a general element of
`LPairCarrier x₁ x₂`.** -/
theorem isDegree2Map_of_isPoleBoundedAtPair_of_supportWitness
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) (A B A' B' : k[X])
    (hbound : IsPoleBoundedAtPair x₁ x₂ A B A' B')
    (S S' : Finset H.Point) (hdisj : Disjoint S S')
    (hsupp : ∀ P, P ∉ S → ordAt P A B = 0)
    (hsupp' : ∀ P, P ∉ S' → ordAt P A' B' = 0)
    (hspec' : ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span ({toPair H A' B'} : Set (CoordinateRing H)))).factors ≠ 0 →
      ∃ P, v.asIdeal = pointIdeal P)
    [∀ P : S', Module.Finite k (CoordinateRing H ⧸ pointIdeal P.1 ^ (ordAt P.1 A' B').toNat)]
    (hinf : ordInfOfPair A' B' = -1) :
    IsDegree2Map (polePairToFraction (H := H) A B A' B') := by
  obtain ⟨hA'B', _, _⟩ := hbound
  refine ⟨A, B, A', B', S, S', hA'B', rfl, hdisj, hsupp, hsupp', ?_⟩
  have h := deg_div_eq_zero_deg5 (H := H) hdeg S' A' B' hA'B' hsupp' hspec'
  omega

theorem isDegree2Map_of_mem_LPairCarrier_of_ne_constant
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (z : FractionRing (CoordinateRing H)) (hz : z ∈ LPairCarrier x₁ x₂)
    (hnc : ¬ IsConstantFraction z) :
    IsDegree2Map z := by
  sorry

/-- **Every degree-2 map's ramification is the Weierstrass points.** The
uniqueness half of the FFK/Liu citation: since a genus-2 curve has a *unique*
degree-2 map to `P¹` up to Möbius transform, and the hyperelliptic map `x`
is one such map with ramification exactly the Weierstrass points
(`hyperelliptic_ramification_eq_weierstrass`), *every* degree-2 map shares
that same ramification set (Möbius transforms of `P¹` don't change which
points of `C` are ramified, only how the target coordinate is labeled). This
is where the actual "uniqueness" content of the citation enters, distinct from
the ramification-counting content of §3 (`card_ramification_eq_six`, which
only pins the *count*, not *which* points). -/
theorem ramification_eq_weierstrass_of_isDegree2Map
    (hdeg : H.f.natDegree = 5) (z : FractionRing (CoordinateRing H))
    (hz : IsDegree2Map z) (P : H.Point) :
    IsRamificationPointOf z P ↔ P.Y = 0 := by
  sorry

/-! ## Assembly -/

/-- **`uniqueDegree2MapToP1`, assembled from §1–§4.** Matches
`RiemannRochCrux.lean`'s statement exactly; once §1–§4 above are proved, swap
that file's `sorry` for a call to this theorem (importing this file the same
way `RatioDivisorCollapse.lean` was wired into `RiemannRochCrux.lean`). -/
theorem uniqueDegree2MapToP1_of_ramification_uniqueness
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (z : FractionRing (CoordinateRing H))
    (hz : z ∈ LPairCarrier x₁ x₂) : IsConstantFraction z := by
  by_contra hnc
  have hdeg2 : IsDegree2Map z :=
    isDegree2Map_of_mem_LPairCarrier_of_ne_constant hdeg x₁ x₂ z hz hnc
  have hram : ∀ P, IsRamificationPointOf z P ↔ P.Y = 0 :=
    ramification_eq_weierstrass_of_isDegree2Map hdeg z hdeg2
  exact hne (pole_pair_eq_fiber_of_degree2_weierstrass_ramified hdeg x₁ x₂ z hz hdeg2 hram)

end HyperellipticPolynomial
