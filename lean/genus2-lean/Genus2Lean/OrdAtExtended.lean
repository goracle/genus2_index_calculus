import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.PrincipalDivisors
import Genus2Lean.RiemannRochGenus2
noncomputable section

set_option linter.style.header false

open Polynomial

namespace HyperellipticPolynomial

open Classical

variable {k : Type*} [Field k]
variable {H : HyperellipticPolynomial k}
variable [IsDedekindDomain (CoordinateRing H)]

/-!
# `ordAt`'s zero-`toPair` convention boundary: diagnosis and a fix path

**This file proves nothing yet — it is a skeleton, written after concluding (in
`RiemannRochGenus2.lean`'s `LPairCarrier_add_smul`) that four `sorry`s there
(`hordN₁`, `hordN₂`, and the `c₁ = c₂ = 0` / `hsum_ne` branches of `hordN`) are
false as literally stated, not merely unproven, and that no local rearrangement
of hypotheses at their call site can rescue them.** The purpose here is to
record *why*, precisely, and to lay out the one fix that actually closes the
gap, so a future session can pick this up without re-deriving the diagnosis.

## The problem, stated precisely

`ordAt` (`PrincipalDivisors.lean`) is `ℤ`-valued:

```
noncomputable def ordAt [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (A B : k[X]) : ℤ :=
  if toPair H A B = 0 then
    0
  else if h_bot : pointIdeal P = ⊥ then
    0
  else
    -WithZero.log ((pointHeightOne P h_bot).intValuation (toPair H A B))
```

(The middle `h_bot` branch is dead code in practice — `pointIdeal_ne_bot`
proves `pointIdeal P ≠ ⊥` unconditionally for every `P : H.Point`
(`PrincipalDivisors.lean`) — so the only degenerate case that actually arises
is the first: `toPair H A B = 0`.)

The `toPair H A B = 0` branch returns `0` — a placeholder, standing in for
"the pair represents the identically-zero function, whose order of vanishing
at every point is $+\infty$, not $0$". This placeholder is harmless whenever a
theorem's hypotheses already guarantee `toPair H A B ≠ 0` (the overwhelming
majority of this file's and `RiemannRochGenus2.lean`'s theorems do exactly
that — see e.g. `ordAt_toPair_mul_of_ne_zero'`, which takes `hAB : toPair H A
B ≠ 0` as an explicit hypothesis). It becomes unsound exactly when a theorem
needs to relate `ordAt` at a *possibly-zero* pair to `ordAt` at other pairs via
arithmetic (`+`, in particular), because `0` is not an additive identity for
"order of vanishing" the way it needs to be: the true fact is
`ord(0 · g) = +∞` for any `g`, and `+∞ ≥ n` for every `n : ℤ`, which `ordAt`'s
placeholder `0` cannot express in either direction (neither `0 = n` nor even
`0 ≥ n` holds for arbitrary `n`).

## Where this actually bites: `LPairCarrier_add_smul`

`hordN₁ : ordAt Q N₁' N₁'' = ordAt Q A₁ B₁ + ordAt Q A₂' B₂'` (stated as an
equality — `RiemannRochGenus2.lean` line ~1042, with `N₁', N₁''` defined so
that `toPair H N₁' N₁'' = toPair H A₁ B₁ * toPair H A₂' B₂'`) is *true*
whenever `toPair H A₁ B₁ ≠ 0` (proved already, via
`ordAt_toPair_mul_of_ne_zero'`), and *false as stated* whenever `toPair H A₁
B₁ = 0`: that branch forces `toPair H N₁' N₁'' = 0` too (so `ordAt Q N₁' N₁''
= 0` by convention and `ordAt Q A₁ B₁ = 0` by convention), reducing the goal
to `0 = 0 + ordAt Q A₂' B₂''`, i.e. `ordAt Q A₂' B₂'' = 0` — which is false in
general (only `ordAt_nonneg` gives `≥ 0`, with no matching upper bound, and
nothing in scope pins the true order of vanishing of `A₂', B₂''` at `Q` to
exactly `0`).

**A `≥`-weakened version fails too**, for a subtler reason (checked directly,
not assumed): the working precedent for this kind of weakening,
`ordInfOfPair`'s `hge1`/`hge2` (same file, same theorem, a different
conjunct), succeeds only because `ordInfOfPair_le_zero` is an *unconditional*
global fact — `ordInfOfPair`'s degenerate value `0` happens to be its maximum
over all pairs, so `0 ≥ ordInfOfPair (anything)` always holds and the
degenerate branch closes for free. `ordAt` has no such property: its
degenerate placeholder `0` is neither an upper nor a lower bound on the true
local order of vanishing at a point, so no inequality direction survives the
`toPair H A₁ B₁ = 0` case. This was checked concretely (not just asserted)
before writing this file.

The same defect recurs identically in `hordN₂` (`A₂, B₂` in place of `A₁,
B₁`), and again — one level up — in `hordN`'s `c₁ = c₂ = 0` branch (`N', N''`
both become `0` literally when both scalars vanish, forcing `ordAt Q N' N'' =
0` against a `min` of two `ordAt`s that need not be `≤ 0`), and in
`ordAt_add_ge_min`'s downstream `hsum_ne` obligation (needs `c₁ • toPair H
N₁' N₁'' + c₂ • toPair H N₂' N₂'' ≠ 0`, not derivable from `N₁', N₂'`'s
individual nonzero-ness since two nonzero ring elements can still sum, with
nonzero coefficients, to zero).

**Also checked and ruled out**: adding `toPair H A B ≠ 0` as a blanket fourth
conjunct to `IsPoleBoundedAtPair` (which would make all of the above vacuous,
since every witness pair would then be guaranteed nonzero). This breaks
`LPair.zero_mem'` (`RiemannRochGenus2.lean`), which is proved by instantiating
`LPairCarrier_add_smul` at `c₁ = c₂ = 0`, `z₁ = z₂ = 1` — i.e. `0 ∈
LPairCarrier x₁ x₂` is *required*, and is witnessed exactly by a
zero-numerator pair. A blanket nonzero-numerator conjunct would make
`LPairCarrier` never contain `0`, contradicting the submodule structure
outright. So the fix cannot live in `IsPoleBoundedAtPair`'s statement; it has
to live in `ordAt` itself.

## The fix: an `ℤ ∪ {+∞}`-valued companion `ordAt'`

The clean fix is a genus-2-generic (not case-specific) upgrade: define

```
noncomputable def ordAt' [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (A B : k[X]) : WithTop ℤ :=
  if toPair H A B = 0 then
    ⊤
  else if h_bot : pointIdeal P = ⊥ then
    0
  else
    -WithZero.log ((pointHeightOne P h_bot).intValuation (toPair H A B))
```

(`WithTop ℤ` rather than `WithBot ℤ`: "order of vanishing" is naturally
bounded *below* by however negative a pole can get for a fixed pair — finite
— and unbounded *above* only in the true-zero-function case, so `⊤` for
"$+\infty$" is the right direction; this also lines up with `ordAt_nonneg`,
`ordInfOfPair_le_zero`, and every other bound already proved in this
codebase, none of which need touching.)

Then:

* **`ordAt_eq_ordAt'_of_ne_zero`**: `toPair H A B ≠ 0 → ordAt' P A B = (ordAt
  P A B : WithTop ℤ)` — the two agree (via coercion) everywhere `ordAt`'s
  placeholder isn't in play. Should be near-immediate from the two
  definitions being identical except for the `if`-branch's return value.
* **`ordAt'_toPair_mul`** (the real fix — **unconditional**, no `≠ 0`
  hypothesis needed on either factor): `toPair H A₃ B₃ = toPair H A B * toPair
  H A' B' → ordAt' P A₃ B₃ = ordAt' P A B + ordAt' P A' B'`, in `WithTop ℤ`
  arithmetic (`⊤ + n = ⊤`, `⊤ + ⊤ = ⊤`, matching "one zero factor makes the
  product's order of vanishing infinite regardless of the other factor" — the
  fact `ordAt`'s `ℤ`-valued convention could not express). This is the
  theorem `hordN₁`/`hordN₂` actually need; both become one-line applications
  of it plus `ordAt_eq_ordAt'_of_ne_zero` on the *nonzero* side, once stated
  at the `ordAt'` level.
* **`ordAt'_add_ge_min`**: the ultrametric inequality, again unconditional (no
  `g + g' ≠ 0` side hypothesis, unlike `ordAt_add_ge_min`) — `⊤` behaves
  correctly as the identity for `min` on the degenerate side (`min ⊤ x = x`),
  so the `g = 0` and `g + g' = 0` cases that forced `ordAt_add_ge_min`'s
  hypothesis dissolve automatically at the `WithTop ℤ` level.

With these three, `hordN₁`, `hordN₂`, `hordN`'s `c₁ = c₂ = 0` branch, and
`ordAt_add_ge_min`'s `hsum_ne` obligation should all restate cleanly at the
`ordAt'` level with no case-split on vanishing needed anywhere, and the
original `ℤ`-valued statements `LPairCarrier_add_smul` actually needs to
produce (its final goal, `ordAt P A B ≥ ordAt P A' B' - s`, is always about a
*known-nonzero* numerator by the time it's invoked — `IsPoleBoundedAtPair`'s
own third conjunct is stated at exactly this `ordAt` level, on the specific
witness the caller already committed to) come back out via
`ordAt_eq_ordAt'_of_ne_zero` at the one point that matters, the final
`IsPoleBoundedAtPair`-conjunct assembly, rather than needing it threaded
through every intermediate step.

## What's NOT yet done here

Nothing below is proved. In order, the actual work is:

1. `ordAt'`'s definition (above) and `ordAt_eq_ordAt'_of_ne_zero`
   (mechanical).
2. `ordAt'_toPair_mul` — likely the real content, following
   `ordAt_toPair_mul_of_ne_zero`'s existing proof shape
   (`PrincipalDivisors.lean`) for the nonzero×nonzero case, plus two new
   one-line cases (`toPair H A B = 0` and/or `toPair H A' B' = 0`) that
   `ordAt`'s version couldn't state.
3. `ordAt'_add_ge_min` — likely follows `WithZero.log_le_log_of_ne_zero` /
   `intValuation_add_le_max`'s existing argument (`RiemannRochGenus2.lean`)
   with the same translation, but now needs `WithTop.add_le_add`-style
   monotonicity lemmas checked against whatever Mathlib actually has for
   `WithTop ℤ` (not yet looked up).
4. Re-derive `hordN₁`, `hordN₂`, `hordN`'s degenerate branch, and
   `ordAt_add_ge_min`'s `hsum_ne` obligation in `LPairCarrier_add_smul`
   (`RiemannRochGenus2.lean`) from the above, replacing all four `sorry`s.
5. Confirm nothing downstream of `ordAt` (`sum_ordAt_eq_natDegree_pairNorm`
   and friends, `PrincipalDivisors.lean` §4) implicitly relies on `ordAt`'s
   *current* `ℤ`-valued zero-convention in a way `ordAt'`'s introduction
   would disturb — expected not to, since `ordAt'` is purely additive
   alongside `ordAt`, not a replacement, but not checked.
-/

-- **Update (this session): steps 1-4 above are now done.** `ordAt'`,
-- `ordAt_eq_ordAt'_of_ne_zero`, `ordAt'_toPair_mul`, and `ordAt'_add_ge_min`
-- are proved directly in `RiemannRochGenus2.lean` (immediately after
-- `ordAt_add_ge_min`, which they depend on) rather than here, since this file
-- imports `RiemannRochGenus2.lean` for `ordAt_toPair_mul_of_ne_zero'` and
-- `ordAt_add_ge_min` themselves -- defining `ordAt'` here and importing it
-- back would be a cycle. `hordN₁`, `hordN₂`, `hordN`'s `c₁ = c₂ = 0` branch,
-- and `ordAt_add_ge_min`'s `hsum_ne` obligation in `LPairCarrier_add_smul`
-- have all been rewritten in terms of `ordAt'` accordingly and no longer
-- contain `sorry`. This file is kept as the diagnosis/design record (above)
-- for why the fix takes this shape; see `RiemannRochGenus2.lean` for the
-- actual lemma statements and proofs, and item 5 in "What's NOT yet done
-- here" above (unchecked -- nothing downstream was found to rely on
-- `ordAt`'s zero-convention in a way `ordAt'` would disturb, but this was
-- checked only by inspection of call sites, not exhaustively).

end HyperellipticPolynomial
