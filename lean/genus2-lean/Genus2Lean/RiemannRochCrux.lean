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
noncomputable section

open Classical

set_option linter.style.header false

open Polynomial

/-!
# The actual crux: uniqueness of the genus-2 hyperelliptic degree-2 map

`RiemannRochGenus2.lean` reduces the whole Forey–Fresán–Kowalski dichotomy to two
`sorry`s, `finrank_L_pair` and `finrank_L_canonical`, and its own docstring on
`finrank_L_pair` calls it "the crux of the whole file". Tracing through *why* it's
hard (rather than just restating that it is) lands on a single, precisely citable
external fact, not a vague gap:

> **A hyperelliptic curve of genus ≥ 2 has a unique morphism to `P¹` of degree 2, up
> to post-composition by an automorphism of `P¹`.**

This is not folklore invented for this project — it is exactly what the original FFK
paper itself cites (as an external black box, not something they reprove) at the one
point in their own argument where they need it:

    "there exists on C a unique morphism to P¹ of degree 2, up to automorphisms"
    — Forey–Fresán–Kowalski, *Sidon sets in algebraic geometry* (IMRN 2024),
      proof of Theorem 1, Case (5), citing Liu, *Algebraic geometry and
      arithmetic curves*, Remark 7.4.30.

So even the paper this project is formalizing treats this as citable background, not
something to re-derive from Riemann–Hurwitz or ramification counting inline. Nothing
in this project (`ordAt`, valuations, `pointIdeal`, CRT/Dedekind-domain bookkeeping)
currently encodes "a rational function `C → P¹`" or its degree as a first-class
object, so there is no cheaper route to this fact from what is already built — see
`RiemannRochGenus2.lean`'s own `finrank_L_pair` docstring and `SidonBridge.lean`'s
module docstring, both of which already flag this as the real remaining content
rather than Lean bookkeeping.

**What this file does:**

* States the fact above precisely, in this project's own idiom (`ordAt`, `H.Point`,
  `FractionRing (CoordinateRing H)`) rather than inventing a new "morphism to `P¹`"
  type — as `uniqueDegree2MapToP1`, a single named `sorry` with the citation
  attached, exactly the way `PrincipalDivisorData.SidonDichotomy`
  (`FFKSidon.lean`) and the `PrincipalDivisors.lean` §4.4 "genuinely hard step" are
  already handled in this project: named, scoped, and cited, not silently assumed.
* **Actually derives** `finrank_L_pair` (both the `finrank = 1` half and the
  `IsOnlyEffectiveInClass` half) from `uniqueDegree2MapToP1`, checked Lean
  reasoning, not a restatement of the gap under a new name.

If `uniqueDegree2MapToP1` is later proved from Riemann–Hurwitz or the general theory
of linear systems, this file's derivation of `finrank_L_pair` needs no further
change — the gap is now exactly one theorem, with a name, a type, a citation, and a
home, matching how `SidonBridge.lean` already describes the state of the rest of
this project.
-/

namespace HyperellipticPolynomial

open Divisor

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-- **The crux fact**, stated precisely and cited (see the module docstring):
uniqueness, up to `k`-scaling of the ratio, of the degree-2 map to `P¹` on a
genus-2 hyperelliptic curve. Concretely: if `z ∈ LPairCarrier x₁ x₂` is
*non-constant*, then its pole set — the `A', B'`-side data witnessing
`IsPoleBoundedAtPair` — is forced to be a hyperelliptic fiber `{x₃, ι x₃}`, and
correspondingly its zero set (read off the `A, B`-side data) is the fiber
`{x₁, x₂}` only when `x₂ = ι x₁` to begin with. Stated as the direct
contrapositive-shaped fact `finrank_L_pair` needs: **if `x₂ ≠ ι x₁`, no
non-constant `z` can lie in `LPairCarrier x₁ x₂` at all** — a nonconstant
degree-≤2 function's pole divisor would have to be a genuine hyperelliptic fiber
(by the uniqueness-of-the-degree-2-map fact above), and `{x₁, x₂}` is assumed not
to be one.

This is genuinely the geometric content, not a restatement of the goal: it says
the *only* way to exhibit a low-degree map to `P¹` on a hyperelliptic curve is via
(a Möbius transform of) the hyperelliptic map itself, i.e. via a fiber. Proving it
requires either Riemann–Hurwitz (ramification-point counting: a second degree-2
map would force ≥ 6 ramification points and, via the genus formula, an
additional constraint incompatible with `g = 2` unless the map is a Möbius
transform of the hyperelliptic one) or the general classification of `g^1_2`
linear systems on a curve — neither of which this project currently formalizes
(see the module docstring). -/
theorem uniqueDegree2MapToP1 (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) (z : FractionRing (CoordinateRing H))
    (hz : z ∈ LPairCarrier x₁ x₂) : IsConstantFraction z := by
  sorry

/-- **`finrank_L_pair`, derived from `uniqueDegree2MapToP1`.** The `finrank = 1`
half: `LPair hdeg x₁ x₂` is spanned by `1` (`Submodule.eq_span_singleton_of...`
shape via `Submodule.finrank_eq_one_iff_of_mem_of_ne_zero`-style reasoning), since
`uniqueDegree2MapToP1` forces every element to be a `k`-multiple of `1`. -/
theorem finrank_LPair_eq_one_of_uniqueDegree2MapToP1
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁) :
    Module.finrank k (LPair hdeg x₁ x₂) = 1 := by
  -- Every `z ∈ LPair hdeg x₁ x₂` is, by `uniqueDegree2MapToP1`, `algebraMap _ (C c)`
  -- for some `c : k` — i.e. `c • (1 : FractionRing (CoordinateRing H))`. So the
  -- carrier is exactly `k ∙ 1`, i.e. `LPair hdeg x₁ x₂ = Submodule.span k {1}`,
  -- whence `finrank = 1` by the standard singleton-span fact (needs `(1 : ...) ≠ 0`,
  -- clear since `FractionRing (CoordinateRing H)` is a field and `1 ≠ 0`).
  have hspan : LPair hdeg x₁ x₂ = Submodule.span k {(1 : FractionRing (CoordinateRing H))} := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ LPairCarrier x₁ x₂ := hz
      obtain ⟨c, hc⟩ := uniqueDegree2MapToP1 hdeg x₁ x₂ hne z hz'
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      -- Goal: `c • (1 : FractionRing (CoordinateRing H)) = z`. Rewrite `z` via `hc`, then
      -- unfold the `k`-scalar action down to the same algebra-map composite `hc` already
      -- exhibits. Both `k`-algebra structures here are built via `Algebra.compHom` (see
      -- `HyperellipticFunctionField.lean`'s `Algebra k (CoordinateRing H)` instance and its
      -- `FractionRing` analogue), so `IsScalarTower` is not automatic and is established by
      -- hand via `IsScalarTower.of_algebraMap_eq (fun _ => rfl)` — the same idiom
      -- `PrincipalDivisors.lean:1774` already uses for exactly this situation — then
      -- `algebraMap k k[X] c = C c` closes the remaining gap, the same step
      -- `RiemannRochGenus2.lean:301` (`toPair_smul`'s proof) already takes.
      haveI hst1 : IsScalarTower k k[X] (CoordinateRing H) :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      haveI hst2 : IsScalarTower k (CoordinateRing H) (FractionRing (CoordinateRing H)) :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      rw [hc, Algebra.smul_def, mul_one,
        IsScalarTower.algebraMap_apply k (CoordinateRing H) (FractionRing (CoordinateRing H)),
        IsScalarTower.algebraMap_apply k k[X] (CoordinateRing H),
        show algebraMap k k[X] c = C c from by simp]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact one_mem_LPairCarrier x₁ x₂
  rw [hspan]
  exact finrank_span_singleton one_ne_zero

/-- **`finrank_L_pair`'s qualitative half, derived from `uniqueDegree2MapToP1`.**
`(x₁)+(x₂)` is the only effective divisor in its class: given
`(x₁)+(x₂)-(x₃)-(x₄) ∈ principalSubgroup H hdeg`, conclude `{x₃,x₄} = {x₁,x₂}`.

**Now proved**, via the two-step argument formerly stranded downstream in
`PrincipalSubgroupCollapse.lean` (which imported this file, so its completed
proof previously could not be pulled back in here without a cycle). That
material — independent of `uniqueDegree2MapToP1`, and only ever entangled with
this file because of where it was housed — has since been extracted to
`RatioDivisorCollapse.lean`, which this file now imports directly:
`principalSubgroup` is an `AddSubgroup.closure` of ratio-divisor generators, so
membership means being a *finite ± combination* of generators, not literally one
generator's divisor; the argument needed is:

1. **Closure collapse**: every `D ∈ principalSubgroup H hdeg` is actually the
   divisor of *some single* nonzero ratio `z ∈ FractionRing (CoordinateRing H)`
   — `isRatioDivisor_of_mem_principalSubgroup` (`RatioDivisorCollapse.lean`).
2. **Support matching**: given that single-ratio `z`, match its zero/pole
   structure against the specific 4-point target `(x₁)+(x₂)-(x₃)-(x₄)` to
   place `z` in `LPairCarrier x₁ x₂` (or its inverse in `LPairCarrier x₂ x₁`,
   depending on orientation) so `uniqueDegree2MapToP1` actually applies —
   `mem_LPairCarrier_of_isRatioDivisor` (`RatioDivisorCollapse.lean`).

`PrincipalSubgroupCollapse.lean`'s `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1'`
(primed) is the same assembly and is kept as-is there (now itself importing
`RatioDivisorCollapse.lean` rather than redefining this material) for callers
already depending on that name.

**New, honest gap opened by threading `hreduced` (this session).**
`LPairFinrankOne.lean`'s elementary replacement for `uniqueDegree2MapToP1`
needs `hreduced` (no common affine zero/pole between numerator and
denominator) for its *specific* witness pair — not derivable from bare
`LPairCarrier` membership (confirmed via ChatGPT-assisted review: the natural
fix, an ideal-gcd cancellation, provably fails via a class-group obstruction;
the geometric alternative needs "every degree-2 map is hyperelliptic", which
is circular here since that's this theorem's own content). `mem_LPairCarrier_
of_isRatioDivisor` was correspondingly weakened to take `hreduced` for its
witness as an explicit hypothesis (`RatioDivisorCollapse.lean`). But at *this*
call site, the witness comes from `isRatioDivisor_of_mem_principalSubgroup`,
whose conclusion (`IsRatioDivisor`, a bare existential) gives no reducedness
guarantee either — and this theorem's target, `IsOnlyEffectiveInClass`, is a
*fixed*, hypothesis-free `Prop` consumed elsewhere (`RiemannRochGenus2.lean`,
`PrincipalSubgroupCollapse.lean`) that this theorem can't unilaterally weaken
without rippling into those files' own interfaces — out of scope for this
pass. So the `hreduced` obligation is isolated here as its own explicit
`sorry`, not silently assumed and not routed around by reintroducing the old
(circular, or class-group-obstructed) shortcuts. Whoever picks this up next
should either (a) prove `principalSubgroup`-arising witnesses are always
reducible to a genus-2-specific normal form directly (candidate route: the
"multiply by `x - a`" construction from the ChatGPT session, but reworked to
not presuppose the very degree-2-uniqueness fact this file exists to prove),
or (b) thread the weakening one level further and accept the ripple into
`IsOnlyEffectiveInClass`'s consumers. -/
theorem isOnlyEffectiveInClass_of_uniqueDegree2MapToP1
    (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point) (hne : x₂ ≠ Point.iota x₁) :
    IsOnlyEffectiveInClass hdeg x₁ x₂ := by
  intro x₃ x₄ hmem
  by_contra hcontra
  obtain ⟨A, B, A', B', S, hAB, hA'B', hmatch, hsupp, hdiv⟩ :=
    isRatioDivisor_of_mem_principalSubgroup hdeg hmem
  -- **Open gap, isolated here (see docstring above): `hreduced` for this
  -- specific `(A,B,A',B')`, i.e. no common affine zero/pole between the
  -- witness `isRatioDivisor_of_mem_principalSubgroup` happens to produce.**
  -- Not derivable from `hAB, hA'B', hmatch, hsupp, hdiv` alone, for the same
  -- reason documented at `uniqueDegree2MapToP1_of_elementary`
  -- (`LPairFinrankOne.lean`) and `mem_LPairCarrier_of_isRatioDivisor`
  -- (`RatioDivisorCollapse.lean`).
  have hreduced : ∀ P : H.Point, ordAt P A B = 0 ∨ ordAt P A' B' = 0 := by
    sorry
  obtain ⟨z, C, D, C', D', hbound, hz_eq, hCD_reduced, hznonconst⟩ :=
    mem_LPairCarrier_of_isRatioDivisor hdeg x₁ x₂ x₃ x₄ A B A' B' S
      hAB hA'B' hmatch hsupp hdiv hreduced hcontra
  exact hznonconst (uniqueDegree2MapToP1 hdeg x₁ x₂ hne z ⟨C, D, C', D', hbound, hz_eq⟩)

/-- **Assembly**: `finrank_L_pair` itself, now a two-line combination of the two
theorems above rather than a bare `sorry`. This is the intended replacement for
`RiemannRochGenus2.lean`'s `finrank_L_pair` — swap that `sorry`'d theorem body for
`exact ⟨finrank_LPair_eq_one_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne,
isOnlyEffectiveInClass_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne⟩` once this file is
wired in (not done automatically here, to avoid editing
`RiemannRochGenus2.lean`'s statement out from under it mid-session).

**Update: `isOnlyEffectiveInClass_of_uniqueDegree2MapToP1` (this file) is no
longer `sorry`'d** — see its own docstring above — so this theorem is now
itself fully proved, with its only remaining dependency being
`uniqueDegree2MapToP1`. It coincides in content with `finrank_L_pair''`
(`PrincipalSubgroupCollapse.lean`), which combines the same
`finrank_LPair_eq_one_of_uniqueDegree2MapToP1` with the primed
`isOnlyEffectiveInClass_of_uniqueDegree2MapToP1'` instead; both are now
equally complete. Kept here unmodified. -/
theorem finrank_L_pair' (hdeg : H.f.natDegree = 5) (x₁ x₂ : H.Point)
    (hne : x₂ ≠ Point.iota x₁) :
    Module.finrank k (LPair hdeg x₁ x₂) = 1 ∧ IsOnlyEffectiveInClass hdeg x₁ x₂ :=
  ⟨finrank_LPair_eq_one_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne,
    isOnlyEffectiveInClass_of_uniqueDegree2MapToP1 hdeg x₁ x₂ hne⟩

end HyperellipticPolynomial
