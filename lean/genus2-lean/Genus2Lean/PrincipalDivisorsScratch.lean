import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.DivisorClassGroup
import Genus2Lean.PrincipalDivisors
noncomputable section

set_option linter.style.header false

open Polynomial

/-!
# SCRATCH: attempted derivation of `IsDedekindDomain (CoordinateRing H)`

**This file is NOT wired into the build or into anything downstream.** It is a
speculative, in-progress draft of the §3 Dedekind-domain proof flagged (and left
as `sorry`) in `PrincipalDivisors.lean`. Every step below is written blind — no
Lean toolchain was available while drafting this — and confidence varies wildly
step to step; each `have`/`sorry` below is annotated with how confident it is:

- **CONFIRMED**: the Mathlib lemma/instance name and signature were checked
  against current Mathlib documentation before use.
- **PLAUSIBLE**: mathematically the right fact, but the exact Mathlib name,
  argument order, or side-conditions were not checked and may be wrong.
- **GUESS**: genuinely uncertain this is even the right approach, let alone the
  right name.

The overall strategy: `k[X]` is a Dedekind domain (PID). `CoordinateRing H` is a
degree-2 extension. If it's the integral closure of `k[X]` in its own fraction
field (which needs `squarefree_f`), Mathlib's
`integralClosure.isDedekindDomain_fractionRing` (or the more general
`IsIntegralClosure.isDedekindDomain`) hands us `IsDedekindDomain` on that integral
closure, which we then need to transport onto `CoordinateRing H` itself.
-/

namespace HyperellipticPolynomial

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}

/-- **CONFIRMED name, PLAUSIBLE it just works**: `k[X]` is a Dedekind domain.
`k` a field ⟹ `k[X]` a Euclidean domain ⟹ PID ⟹ Dedekind. Mathlib should have
some instance chain producing this automatically via `infer_instance`/
`inferInstance`, since PID-implies-Dedekind is a standard instance, but the
exact instance path (`IsPrincipalIdealRing.isDedekindDomain`? something in
`Mathlib.RingTheory.DedekindDomain.Basic` reached via `EuclideanDomain k[X]`?)
was not individually confirmed — only that the *fact* is true and *should* be
wired up as instances given how central "polynomial ring over a field is a
PID" is to Mathlib's algebra hierarchy. -/
example : IsDedekindDomain (k[X]) := by infer_instance

/-- **PLAUSIBLE**: `X^2 - C H.f` is separable when `char k ≠ 2`. The standard
route: a polynomial over a field is separable iff it's coprime to its own
derivative (`Polynomial.separable_iff_derivative_ne_zero`-shaped, or via
`IsCoprime`). Derivative of `X² - C H.f` (as a polynomial in the *outer* `X`
over base ring `k[X]`, i.e. thinking of `H.f` as a constant) is `C 2 * X`,
nonzero exactly when `(2 : k[X]) ≠ 0`, which holds whenever `char k ≠ 2`.
Exact lemma name not confirmed — candidates: `Polynomial.separable_of_...`,
or bespoke via `Polynomial.Separable` unfolded to a Bezout-identity `∃ u v,
u * f + v * f.derivative = 1` constructed by hand (since `f = X² - c` has
derivative `2X`, and `X² - c` and `2X` are coprime in a PID iff they share no
common root, true when `c ≠ 0` isn't even needed — `2X` and `X² - c` are
coprime whenever `2 ≠ 0`, regardless of `c`, since `gcd` divides
`X * (2X) - 2*(X² - c) = 2c`, a nonzero constant when `c ≠ 0`... but c = H.f
here is a *polynomial*, not a scalar, complicating this "constant" framing;
this whole paragraph needs re-deriving carefully in a live goal state, flagged
as GUESS-tier despite the label above the code). -/
theorem defining_poly_separable (nd : NonsingularData H) :
    ((X : (k[X])[X]) ^ 2 - C H.f).Separable := by
  sorry

/-- **GUESS**: `CoordinateRing H` is a free `k[X]`-module of rank 2, hence
`FiniteDimensional (FractionRing k[X]) (FractionRing (CoordinateRing H))` with
`finrank = 2`. Should follow from `AdjoinRoot.powerBasis` (confirmed to exist:
`AdjoinRoot.powerBasis {K} [Field K] {f : K[X]} (hf : f ≠ 0) : PowerBasis K
(AdjoinRoot f)` — but note this signature has `[Field K]` as the *base*, and our
base `k[X]` is not a field, only a domain, so `AdjoinRoot.powerBasis` as stated
may not directly apply to `CoordinateRing H` over `k[X]`; it would need to be
applied one level up, to `FractionRing (CoordinateRing H)` over
`FractionRing (k[X])` after already localizing — meaning this step likely needs
`IsFractionRing`/localization-compatibility lemmas for `AdjoinRoot` that were
not located at all in this session). This is the least-confident step in the
whole chain and the one most likely to need real Lean-environment exploration
(`exact?`/`apply?`/`loogle`) rather than blind API guessing. -/
theorem finiteDimensional_fractionRing (nd : NonsingularData H) :
    True := by  -- placeholder Prop; real statement needs FractionRing/Algebra
                -- instances established first, which are themselves unbuilt
  sorry

/-- **GUESS, likely wrong shape**: `CoordinateRing H` is integrally closed in its
own fraction field, using `squarefree_f`. This is genuinely the mathematical
heart of §3 and the part most likely to require an actual argument (e.g. via
`IsIntegrallyClosed` unfolded to "every root in the fraction field of a monic
poly over `CoordinateRing H` already lies in `CoordinateRing H`", proved using
that `X² - C H.f` having no repeated roots means the ring `k[X][y]/(y²-f)` has
no nilpotents/non-normal points — this is standard in the theory of
hyperelliptic curves but was not attempted as an actual proof here, only
asserted as the target). -/
theorem coordinateRing_isIntegrallyClosed (nd : NonsingularData H) :
    True := by  -- same placeholder caveat as above
  sorry

/- Final assembly — **NOT ATTEMPTED**, since it depends on all three steps
above, none of which actually compile yet. Left unstated (not even a `sorry`d
`theorem` with the real signature) because getting the real signature right
depends on how the `FractionRing`/`IsIntegralClosure` plumbing from the steps
above actually shakes out, and guessing that signature now would likely just
be wrong in a way that wastes a rebuild cycle rather than saves one. -/

end HyperellipticPolynomial
