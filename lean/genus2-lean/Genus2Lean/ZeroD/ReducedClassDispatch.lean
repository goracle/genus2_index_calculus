import Mathlib
import Genus2Lean.ZeroD.ReducedClassBundles
import Genus2Lean.ZeroD.ReducedClassBundlesCross1
import Genus2Lean.ZeroD.ReducedClassBundlesCross2
import Genus2Lean.ZeroD.ReducedClassBundlesCross3
import Genus2Lean.ZeroD.ReducedClassBundlesCross4
import Genus2Lean.ZeroD.AlphaLocusDegreeUniformTangentTarget

/-! # `reducedClassDispatch` — the top-level router over all seven
`reducedClass_eq_of_isReduction'` variants

`ROADMAP-reducedClass-dispatcher.md`, "Suggested order" steps 1 and 2.
Step 3's bundling is done — `ReducedClassBundles.lean`,
`ReducedClassBundlesCross{1,2,3,4}.lean`, and the two pre-existing
tangent-axis bundle pairs in `AlphaLocusDegreeUniformTangent.lean`/
`AlphaLocusDegreeUniformTangentTarget.lean` — confirmed by direct read
this pass, no further bundling work needed to write this file.

## Shape, per the roadmap's "Proposed shape" section

Two-level dispatch:

1. **Outer — decidable, on `X`-coordinates only:** `if Ra1.X = Ra2.X
   then ... else if sa.P1.X = sa.P2.X then ... else ...` — tangent-anchor
   / tangent-target / both-split.
2. **Inner (only in the "both split" branch) — NOT decidable, taken as
   caller-supplied data**: `CrossCase`, a five-constructor sum type
   (`generic` plus one `some`-style constructor per `Cross{1,2,3,4}`
   theorem), matching each theorem's own `hP1eq`/`hP2eq`-shaped
   hypothesis (confirmed by direct read of all four
   `ReducedClassBundlesCross{1,2,3,4}.lean` files, this pass — `cross1`/
   `cross3` name `hP1eq : sa.P1 = Point.iota (anchor point)`, `cross2`/
   `cross4` name `hP2eq : sa.P2 = Point.iota (anchor point)`, exactly the
   four `H.Point`-level identities the roadmap's original `CrossCase`
   sketch anticipated).

Per the roadmap's "Uncovered residual case" section, option (a):
simultaneous anchor+target tangency is not covered by any of the seven
theorems, so the dispatcher takes an explicit `hRaT : Ra1.X ≠ Ra2.X ∨
sa.P1.X ≠ sa.P2.X` hypothesis ruling that case out, rather than papering
over it with a `sorry`-guarded fourth branch.

## Resolving the `q`/conclusion-shape question

The roadmap flagged the seven variants' `as_q` fields as a possible
source of a non-uniform conclusion. **Checked directly this pass: all
seven bundles' `as_q`/`hq` fields are textually identical** —
`hq : as_q = toJacobian D ⟨single (Point.iota δ₀) - single δ₀, ...⟩`,
a term depending only on `δ₀` (shared by every branch via `sa`), not on
any branch-specific data. So `as_q` is not a genuine per-branch unknown;
every branch's `d.as_q` equals the SAME value. This lets the dispatcher
fix one `q : Jacobian H D` up front (defined by that shared formula) and
have every branch's own `hq` discharge `d.as_q = q` by `rfl`/direct
rewrite, rather than needing an existential or seven-way sum return
type. Likewise `d.as_v`/`d.as_S`/`d.hmem` differ across branches only in
which concrete polynomial/finset the caller instantiates them with —
the dispatcher takes the target `v S hmem` as parameters and requires
each branch's own bundle fields to match them, so the final conclusion
is one fixed `sa.reducedClass + q = toJacobian D ⟨divToPair (-v) 1 S -
..., hmem⟩` statement regardless of which branch fires.

**REPL round-trip (Claire, this pass) surfaced a real proof-technique
bug, fixed below**: the original draft called the bundled theorem FIRST
(`have hthm := ...`) and then tried `rw [d.hq, dV, dS] at hthm` to align
its conclusion with the dispatcher's caller-fixed `v`/`S`/`hmem`. This
fails — "motive is not type correct" — because `d.hmem`'s own TYPE
mentions `d.as_v`/`d.as_S` dependently (`divToPair (-d.as_v) 1 d.as_S -
... ∈ Divisor0 H`), so `rw` cannot abstract `as_v`/`as_S` out of
`hthm`'s statement without also transporting `d.hmem` itself, which
`rw`'s motive-construction can't do automatically. **Fix**: `subst` the
branch's `dV : d.as_v = v` / `dS : d.as_S = S` equalities BEFORE calling
the theorem, not after — this replaces `v`/`S` throughout the ambient
goal AND the caller-supplied `hmem`'s type with `d.as_v`/`d.as_S`
(the direction `subst` runs, since `v`/`S` are free dispatcher-bound
variables and `d.as_v`/`d.as_S` are not), so `hthm`'s conclusion and the
goal already agree on the data component once stated; the two are then
`Subtype.mk`-different only in their `Divisor0`-membership PROOF
component, which `convert ... using 2` discharges via proof
irrelevance (the `using 2` depth targets exactly the `Subtype.mk` proof
argument, one level in from `using 3`'s original guess — confirmed
against the actual goal shape this pass, not assumed). -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor

namespace Genus2Lean
namespace DecoupledSystem

open TheDataDerivation

variable {k : Type*} [Field k] {H : HyperellipticPolynomial k}
variable {D : PrincipalDivisorData H}

/-- **Which (if any) cross-pair identification holds**, once anchor and
target are each confirmed split (`Ra1.X ≠ Ra2.X`, `sa.P1.X ≠ sa.P2.X`).
`generic` is the fully-split case (all four `h1P1,h1P2,h2P1,h2P2` cross
inequalities hold, matching `SplitAssemblyData`'s own field names,
checked directly against that structure rather than assumed); each
`some`-style constructor names the one `H.Point`-level identity the
corresponding `Cross{N}AssemblyData` bundle's own `hP1eq`/`hP2eq` field
needs. Deliberately NOT decidable from `X`-coordinates alone — per the
roadmap's "undecidable step" finding, `Ra = ι(P)` needs the row-level
`Y`-fact the bare `X`-equality doesn't determine, so this is data the
caller supplies (matching the project's existing convention of caller-
supplied Mumford/witness data for `hdet`, `hMumfordUa`, etc.), not
something the dispatcher can compute. -/
inductive CrossCase {p : ℕ} [Fact (Nat.Prime p)] {H : HyperellipticPolynomial (F p)}
    (Ra1 Ra2 P1 P2 : H.Point) : Type
  | generic (h1P1 : Ra1.X ≠ P1.X) (h1P2 : Ra1.X ≠ P2.X)
            (h2P1 : Ra2.X ≠ P1.X) (h2P2 : Ra2.X ≠ P2.X) : CrossCase Ra1 Ra2 P1 P2
  | cross1  (h : P1 = Point.iota Ra1) : CrossCase Ra1 Ra2 P1 P2
  | cross2  (h : P2 = Point.iota Ra1) : CrossCase Ra1 Ra2 P1 P2
  | cross3  (h : P1 = Point.iota Ra2) : CrossCase Ra1 Ra2 P1 P2
  | cross4  (h : P2 = Point.iota Ra2) : CrossCase Ra1 Ra2 P1 P2

/-- **Top-level dispatcher.** Routes to whichever of the seven
`reducedClass_eq_of_isReduction'` variants matches `sa`'s actual
anchor/target configuration, given `Ra1 Ra2 : H.Point` as the candidate
anchor pair, and concludes the SHARED target statement
`sa.reducedClass + q = toJacobian D ⟨divToPair (-v) 1 S - ..., hmem⟩`
for a caller-fixed `v S hmem` (see module docstring for why `q` itself
needs no such parameter — it is pinned by `δ₀` alone, identically across
all seven branches).

Per "Uncovered residual case" in the roadmap, `hRaT` rules out the
not-yet-built simultaneous-tangency case; `cc` supplies the `CrossCase`
data only once anchor and target are both confirmed split.

Each of the seven branches takes its OWN bundle-pair (`base`/`d`) plus
its own `hcoeff`, per the roadmap's "Bundling, not flattening"
conclusion — flattening seven bundle-pairs directly into the signature,
not inventing a shared mega-bundle, since a caller only ever has the ONE
bundle-pair matching their actual case in hand; the other six arguments
are simply unused by whichever branch fires. Each branch additionally
supplies `hv`/`hS` tying its own `d.as_v`/`d.as_S` to the caller-fixed
`v`/`S`, and `hqhmem` witnessing the resulting membership matches the
caller-fixed `hmem` (via `Subtype.ext`, since `Divisor0` membership
proofs are propositions and any two are equal by proof irrelevance —
the real content is `d.as_v = v` and `d.as_S = S`). -/
def reducedClassDispatch {p : ℕ} [Fact (Nat.Prime p)] [Fact (p ≠ 2)]
    {H : HyperellipticPolynomial (F p)} [IsDedekindDomain (CoordinateRing H)]
    [DecidableEq H.Point]
    {D : PrincipalDivisorData H}
    {aClass : Jacobian H D} {δ₀ : H.Point}
    (sa : SampleTargetFromAlpha p H D aClass δ₀)
    (Ra1 Ra2 : H.Point)
    (v : Polynomial (F p)) (S : Finset H.Point)
    (hmem : (divToPair (H := H) (-v) 1 S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) ∈ Divisor0 H)
    (hRaT : Ra1.X ≠ Ra2.X ∨ sa.P1.X ≠ sa.P2.X)
    (cc : Ra1.X ≠ Ra2.X → sa.P1.X ≠ sa.P2.X →
      CrossCase Ra1 Ra2 sa.P1 sa.P2)
    -- Tangent-anchor branch (`Ra1.X = Ra2.X`).
    (tanBase : TangentReductionData sa) (tanD : TangentAssemblyData sa)
    (tanCoeff : tanD.as_coeffs = tanBase.coeffs)
    (tanV : tanD.as_v = v) (tanS : tanD.as_S = S)
    -- Tangent-target branch (`sa.P1.X = sa.P2.X`).
    (ttBase : TangentTargetReductionData sa) (ttD : TangentTargetAssemblyData sa)
    (ttCoeff : ttD.as_coeffs = ttBase.coeffs)
    (ttV : ttD.as_v = v) (ttS : ttD.as_S = S)
    -- Fully-split, generic-cross branch.
    (gBase : ReductionData sa) (gD : SplitAssemblyData sa)
    (gCoeff : gD.as_coeffs = gBase.coeffs)
    (gCur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p gD.as_coeffs.coeff_c0 gD.as_coeffs.coeff_c1 gD.as_coeffs.coeff_c2
        gD.as_coeffs.coeff_c3 gD.as_coeffs.coeff_c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        gD.as_coeffs.coeff_ua0 gD.as_coeffs.coeff_ua1 gD.as_coeffs.coeff_va0 gD.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (gGcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          gD.as_coeffs.coeff_ua0 gD.as_coeffs.coeff_ua1 gD.as_coeffs.coeff_va0 gD.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p gD.as_coeffs.coeff_c0 gD.as_coeffs.coeff_c1 gD.as_coeffs.coeff_c2
          gD.as_coeffs.coeff_c3 gD.as_coeffs.coeff_c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          gD.as_coeffs.coeff_ua0 gD.as_coeffs.coeff_ua1 gD.as_coeffs.coeff_va0 gD.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (gCurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p gD.as_coeffs.coeff_c0 gD.as_coeffs.coeff_c1 gD.as_coeffs.coeff_c2
        gD.as_coeffs.coeff_c3 gD.as_coeffs.coeff_c4
        sa.P1.X sa.P1.Y
        gD.as_coeffs.coeff_ua0 gD.as_coeffs.coeff_ua1 gD.as_coeffs.coeff_va0 gD.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (gGcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p gD.as_coeffs.coeff_c0 gD.as_coeffs.coeff_c1 gD.as_coeffs.coeff_c2
          gD.as_coeffs.coeff_c3 gD.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          gD.as_coeffs.coeff_ua0 gD.as_coeffs.coeff_ua1 gD.as_coeffs.coeff_va0 gD.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p gD.as_coeffs.coeff_c0 gD.as_coeffs.coeff_c1 gD.as_coeffs.coeff_c2
          gD.as_coeffs.coeff_c3 gD.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          gD.as_coeffs.coeff_ua0 gD.as_coeffs.coeff_ua1 gD.as_coeffs.coeff_va0 gD.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (gR : isReduction' sa gD.as_coeffs.coeff_c0 gD.as_coeffs.coeff_c1 gD.as_coeffs.coeff_c2
      gD.as_coeffs.coeff_c3 gD.as_coeffs.coeff_c4
      gD.as_coeffs.coeff_ua0 gD.as_coeffs.coeff_ua1 gD.as_coeffs.coeff_va0 gD.as_coeffs.coeff_va1
      gCur gGcd gCurT gGcdT)
    (gDeg : H.f.natDegree = 5)
    (gDvd : principalSubgroup H gDeg ≤ D.P)
    (gV : gD.as_v = v) (gS : gD.as_S = S)
    -- Cross1 branch (`sa.P1 = ι(Ra1)`). Same `hcur/hgcd/hcurT/hgcdT/hr/
    -- hdeg/hD` tail as the split branch above — confirmed by direct read,
    -- this pass, that all four `_cross{N}` theorems carry this tail
    -- verbatim (stated against their OWN bundle's `as_coeffs`), not just
    -- `sa base d hcoeff` as an earlier draft of this file assumed.
    (c1Base : ReductionData sa) (c1D : Cross1AssemblyData sa)
    (c1Coeff : c1D.as_coeffs = c1Base.coeffs)
    (c1Cur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c1D.as_coeffs.coeff_c0 c1D.as_coeffs.coeff_c1 c1D.as_coeffs.coeff_c2
        c1D.as_coeffs.coeff_c3 c1D.as_coeffs.coeff_c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        c1D.as_coeffs.coeff_ua0 c1D.as_coeffs.coeff_ua1 c1D.as_coeffs.coeff_va0
        c1D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c1Gcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c1D.as_coeffs.coeff_ua0 c1D.as_coeffs.coeff_ua1 c1D.as_coeffs.coeff_va0
          c1D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c1D.as_coeffs.coeff_c0 c1D.as_coeffs.coeff_c1 c1D.as_coeffs.coeff_c2
          c1D.as_coeffs.coeff_c3 c1D.as_coeffs.coeff_c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c1D.as_coeffs.coeff_ua0 c1D.as_coeffs.coeff_ua1 c1D.as_coeffs.coeff_va0
          c1D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c1CurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c1D.as_coeffs.coeff_c0 c1D.as_coeffs.coeff_c1 c1D.as_coeffs.coeff_c2
        c1D.as_coeffs.coeff_c3 c1D.as_coeffs.coeff_c4
        sa.P1.X sa.P1.Y
        c1D.as_coeffs.coeff_ua0 c1D.as_coeffs.coeff_ua1 c1D.as_coeffs.coeff_va0
        c1D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c1GcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c1D.as_coeffs.coeff_c0 c1D.as_coeffs.coeff_c1
          c1D.as_coeffs.coeff_c2 c1D.as_coeffs.coeff_c3 c1D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c1D.as_coeffs.coeff_ua0 c1D.as_coeffs.coeff_ua1 c1D.as_coeffs.coeff_va0
          c1D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c1D.as_coeffs.coeff_c0 c1D.as_coeffs.coeff_c1 c1D.as_coeffs.coeff_c2
          c1D.as_coeffs.coeff_c3 c1D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c1D.as_coeffs.coeff_ua0 c1D.as_coeffs.coeff_ua1 c1D.as_coeffs.coeff_va0
          c1D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c1R : isReduction' sa c1D.as_coeffs.coeff_c0 c1D.as_coeffs.coeff_c1 c1D.as_coeffs.coeff_c2
      c1D.as_coeffs.coeff_c3 c1D.as_coeffs.coeff_c4
      c1D.as_coeffs.coeff_ua0 c1D.as_coeffs.coeff_ua1 c1D.as_coeffs.coeff_va0
      c1D.as_coeffs.coeff_va1
      c1Cur c1Gcd c1CurT c1GcdT)
    (c1Deg : H.f.natDegree = 5)
    (c1Dvd : principalSubgroup H c1Deg ≤ D.P)
    (c1V : c1D.as_v = v) (c1S : c1D.as_S = S)
    -- Cross2 branch (`sa.P2 = ι(Ra1)`).
    (c2Base : ReductionData sa) (c2D : Cross2AssemblyData sa)
    (c2Coeff : c2D.as_coeffs = c2Base.coeffs)
    (c2Cur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c2D.as_coeffs.coeff_c0 c2D.as_coeffs.coeff_c1 c2D.as_coeffs.coeff_c2
        c2D.as_coeffs.coeff_c3 c2D.as_coeffs.coeff_c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        c2D.as_coeffs.coeff_ua0 c2D.as_coeffs.coeff_ua1 c2D.as_coeffs.coeff_va0
        c2D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c2Gcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c2D.as_coeffs.coeff_ua0 c2D.as_coeffs.coeff_ua1 c2D.as_coeffs.coeff_va0
          c2D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c2D.as_coeffs.coeff_c0 c2D.as_coeffs.coeff_c1 c2D.as_coeffs.coeff_c2
          c2D.as_coeffs.coeff_c3 c2D.as_coeffs.coeff_c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c2D.as_coeffs.coeff_ua0 c2D.as_coeffs.coeff_ua1 c2D.as_coeffs.coeff_va0
          c2D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c2CurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c2D.as_coeffs.coeff_c0 c2D.as_coeffs.coeff_c1 c2D.as_coeffs.coeff_c2
        c2D.as_coeffs.coeff_c3 c2D.as_coeffs.coeff_c4
        sa.P1.X sa.P1.Y
        c2D.as_coeffs.coeff_ua0 c2D.as_coeffs.coeff_ua1 c2D.as_coeffs.coeff_va0
        c2D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c2GcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c2D.as_coeffs.coeff_c0 c2D.as_coeffs.coeff_c1
          c2D.as_coeffs.coeff_c2 c2D.as_coeffs.coeff_c3 c2D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c2D.as_coeffs.coeff_ua0 c2D.as_coeffs.coeff_ua1 c2D.as_coeffs.coeff_va0
          c2D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c2D.as_coeffs.coeff_c0 c2D.as_coeffs.coeff_c1 c2D.as_coeffs.coeff_c2
          c2D.as_coeffs.coeff_c3 c2D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c2D.as_coeffs.coeff_ua0 c2D.as_coeffs.coeff_ua1 c2D.as_coeffs.coeff_va0
          c2D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c2R : isReduction' sa c2D.as_coeffs.coeff_c0 c2D.as_coeffs.coeff_c1 c2D.as_coeffs.coeff_c2
      c2D.as_coeffs.coeff_c3 c2D.as_coeffs.coeff_c4
      c2D.as_coeffs.coeff_ua0 c2D.as_coeffs.coeff_ua1 c2D.as_coeffs.coeff_va0
      c2D.as_coeffs.coeff_va1
      c2Cur c2Gcd c2CurT c2GcdT)
    (c2Deg : H.f.natDegree = 5)
    (c2Dvd : principalSubgroup H c2Deg ≤ D.P)
    (c2V : c2D.as_v = v) (c2S : c2D.as_S = S)
    -- Cross3 branch (`sa.P1 = ι(Ra2)`).
    (c3Base : ReductionData sa) (c3D : Cross3AssemblyData sa)
    (c3Coeff : c3D.as_coeffs = c3Base.coeffs)
    (c3Cur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c3D.as_coeffs.coeff_c0 c3D.as_coeffs.coeff_c1 c3D.as_coeffs.coeff_c2
        c3D.as_coeffs.coeff_c3 c3D.as_coeffs.coeff_c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        c3D.as_coeffs.coeff_ua0 c3D.as_coeffs.coeff_ua1 c3D.as_coeffs.coeff_va0
        c3D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c3Gcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c3D.as_coeffs.coeff_ua0 c3D.as_coeffs.coeff_ua1 c3D.as_coeffs.coeff_va0
          c3D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c3D.as_coeffs.coeff_c0 c3D.as_coeffs.coeff_c1 c3D.as_coeffs.coeff_c2
          c3D.as_coeffs.coeff_c3 c3D.as_coeffs.coeff_c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c3D.as_coeffs.coeff_ua0 c3D.as_coeffs.coeff_ua1 c3D.as_coeffs.coeff_va0
          c3D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c3CurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c3D.as_coeffs.coeff_c0 c3D.as_coeffs.coeff_c1 c3D.as_coeffs.coeff_c2
        c3D.as_coeffs.coeff_c3 c3D.as_coeffs.coeff_c4
        sa.P1.X sa.P1.Y
        c3D.as_coeffs.coeff_ua0 c3D.as_coeffs.coeff_ua1 c3D.as_coeffs.coeff_va0
        c3D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c3GcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c3D.as_coeffs.coeff_c0 c3D.as_coeffs.coeff_c1
          c3D.as_coeffs.coeff_c2 c3D.as_coeffs.coeff_c3 c3D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c3D.as_coeffs.coeff_ua0 c3D.as_coeffs.coeff_ua1 c3D.as_coeffs.coeff_va0
          c3D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c3D.as_coeffs.coeff_c0 c3D.as_coeffs.coeff_c1 c3D.as_coeffs.coeff_c2
          c3D.as_coeffs.coeff_c3 c3D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c3D.as_coeffs.coeff_ua0 c3D.as_coeffs.coeff_ua1 c3D.as_coeffs.coeff_va0
          c3D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c3R : isReduction' sa c3D.as_coeffs.coeff_c0 c3D.as_coeffs.coeff_c1 c3D.as_coeffs.coeff_c2
      c3D.as_coeffs.coeff_c3 c3D.as_coeffs.coeff_c4
      c3D.as_coeffs.coeff_ua0 c3D.as_coeffs.coeff_ua1 c3D.as_coeffs.coeff_va0
      c3D.as_coeffs.coeff_va1
      c3Cur c3Gcd c3CurT c3GcdT)
    (c3Deg : H.f.natDegree = 5)
    (c3Dvd : principalSubgroup H c3Deg ≤ D.P)
    (c3V : c3D.as_v = v) (c3S : c3D.as_S = S)
    -- Cross4 branch (`sa.P2 = ι(Ra2)`).
    (c4Base : ReductionData sa) (c4D : Cross4AssemblyData sa)
    (c4Coeff : c4D.as_coeffs = c4Base.coeffs)
    (c4Cur : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4General p c4D.as_coeffs.coeff_c0 c4D.as_coeffs.coeff_c1 c4D.as_coeffs.coeff_c2
        c4D.as_coeffs.coeff_c3 c4D.as_coeffs.coeff_c4
        (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
        c4D.as_coeffs.coeff_ua0 c4D.as_coeffs.coeff_ua1 c4D.as_coeffs.coeff_va0
        c4D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c4Gcd : (sa.P1.X, sa.P1.Y) ≠ (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4 p (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c4D.as_coeffs.coeff_ua0 c4D.as_coeffs.coeff_ua1 c4D.as_coeffs.coeff_va0
          c4D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4General p c4D.as_coeffs.coeff_c0 c4D.as_coeffs.coeff_c1 c4D.as_coeffs.coeff_c2
          c4D.as_coeffs.coeff_c3 c4D.as_coeffs.coeff_c4
          (sa.P1.X, sa.P1.Y) (sa.P2.X, sa.P2.Y)
          c4D.as_coeffs.coeff_ua0 c4D.as_coeffs.coeff_ua1 c4D.as_coeffs.coeff_va0
          c4D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c4CurT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      curBeforeMonic4Tangent p c4D.as_coeffs.coeff_c0 c4D.as_coeffs.coeff_c1 c4D.as_coeffs.coeff_c2
        c4D.as_coeffs.coeff_c3 c4D.as_coeffs.coeff_c4
        sa.P1.X sa.P1.Y
        c4D.as_coeffs.coeff_ua0 c4D.as_coeffs.coeff_ua1 c4D.as_coeffs.coeff_va0
        c4D.as_coeffs.coeff_va1
        sa.toSampleTarget.u0 sa.toSampleTarget.u1
        sa.toSampleTarget.v0 sa.toSampleTarget.v1 ≠ 0)
    (c4GcdT : (sa.P1.X, sa.P1.Y) = (sa.P2.X, sa.P2.Y) →
      IsCoprime (Ypoly4Tangent p c4D.as_coeffs.coeff_c0 c4D.as_coeffs.coeff_c1
          c4D.as_coeffs.coeff_c2 c4D.as_coeffs.coeff_c3 c4D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c4D.as_coeffs.coeff_ua0 c4D.as_coeffs.coeff_ua1 c4D.as_coeffs.coeff_va0
          c4D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1)
        (uRS4Tangent p c4D.as_coeffs.coeff_c0 c4D.as_coeffs.coeff_c1 c4D.as_coeffs.coeff_c2
          c4D.as_coeffs.coeff_c3 c4D.as_coeffs.coeff_c4
          sa.P1.X sa.P1.Y
          c4D.as_coeffs.coeff_ua0 c4D.as_coeffs.coeff_ua1 c4D.as_coeffs.coeff_va0
          c4D.as_coeffs.coeff_va1
          sa.toSampleTarget.u0 sa.toSampleTarget.u1
          sa.toSampleTarget.v0 sa.toSampleTarget.v1))
    (c4R : isReduction' sa c4D.as_coeffs.coeff_c0 c4D.as_coeffs.coeff_c1 c4D.as_coeffs.coeff_c2
      c4D.as_coeffs.coeff_c3 c4D.as_coeffs.coeff_c4
      c4D.as_coeffs.coeff_ua0 c4D.as_coeffs.coeff_ua1 c4D.as_coeffs.coeff_va0
      c4D.as_coeffs.coeff_va1
      c4Cur c4Gcd c4CurT c4GcdT)
    (c4Deg : H.f.natDegree = 5)
    (c4Dvd : principalSubgroup H c4Deg ≤ D.P)
    (c4V : c4D.as_v = v) (c4S : c4D.as_S = S) :
    sa.reducedClass +
      toJacobian D (Subtype.mk (single (Point.iota δ₀) - single δ₀ : Divisor H)
        (single_sub_single_mem_Divisor0 (Point.iota δ₀) δ₀)) =
      toJacobian D (Subtype.mk (divToPair (H := H) (-v) 1 S -
        (single δ₀ + single (Point.iota δ₀)) : Divisor H) hmem) := by
  by_cases hRa : Ra1.X = Ra2.X
  · -- `subst` the branch's `as_v = v`/`as_S = S` facts FIRST, before invoking
    -- the theorem — rewriting `hthm` AFTER the fact fails ("motive is not
    -- type correct"), since `tanD.hmem`'s own type mentions `tanD.as_v`
    -- dependently, so `rw` can't abstract `as_v` out of it. Substituting
    -- `v := tanD.as_v` (using `tanV.symm`) BEFORE calling the theorem
    -- avoids ever needing to transport a dependent proof term.
    subst tanV; subst tanS
    have hthm := reducedClass_eq_of_isReduction'_tangent sa tanBase tanD tanCoeff
    rw [tanD.hq] at hthm
    convert hthm using 2
  · by_cases hT : sa.P1.X = sa.P2.X
    · subst ttV; subst ttS
      have hthm := reducedClass_eq_of_isReduction'_tangent_target sa ttBase ttD ttCoeff
      rw [ttD.hq] at hthm
      convert hthm using 2
    · match cc hRa hT with
      | .generic h1P1 h1P2 h2P1 h2P2 =>
          subst gV; subst gS
          have hthm := reducedClass_eq_of_isReduction' sa gBase gD gCoeff gCur gGcd gCurT gGcdT
            gR gDeg gDvd
          rw [gD.hq] at hthm
          convert hthm using 2
      | .cross1 _h =>
          subst c1V; subst c1S
          have hthm := reducedClass_eq_of_isReduction'_cross1 sa c1Base c1D c1Coeff
            c1Cur c1Gcd c1CurT c1GcdT c1R c1Deg c1Dvd
          rw [c1D.hq] at hthm
          convert hthm using 2
      | .cross2 _h =>
          subst c2V; subst c2S
          have hthm := reducedClass_eq_of_isReduction'_cross2 sa c2Base c2D c2Coeff
            c2Cur c2Gcd c2CurT c2GcdT c2R c2Deg c2Dvd
          rw [c2D.hq] at hthm
          convert hthm using 2
      | .cross3 _h =>
          subst c3V; subst c3S
          have hthm := reducedClass_eq_of_isReduction'_cross3 sa c3Base c3D c3Coeff
            c3Cur c3Gcd c3CurT c3GcdT c3R c3Deg c3Dvd
          rw [c3D.hq] at hthm
          convert hthm using 2
      | .cross4 _h =>
          subst c4V; subst c4S
          have hthm := reducedClass_eq_of_isReduction'_cross4 sa c4Base c4D c4Coeff
            c4Cur c4Gcd c4CurT c4GcdT c4R c4Deg c4Dvd
          rw [c4D.hq] at hthm
          convert hthm using 2

end DecoupledSystem
end Genus2Lean
