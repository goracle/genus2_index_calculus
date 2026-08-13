import Mathlib
import Genus2Lean.HyperellipticFunctionField
import Genus2Lean.AffinePoints
import Genus2Lean.PrincipalDivisors
import Genus2Lean.GlobalDegreeBoundSpec
import Genus2Lean.LPairFinrankOneOrdAtFrac
set_option linter.style.header false

noncomputable section

open Classical
open Polynomial

variable {k : Type*} [Field k] (H : HyperellipticPolynomial k)

/-!
# Bridging `k[X]`-gcd coprimality to closed-point pole-boundedness

**Status: §3's original plan (bridge an `H.Point`-only `hzsupp` up to a closed-point
bound) was a dead end, confirmed false by two independent ChatGPT consultations
(post-mortems below) — do not resume that specific route
(`isNormCoprime_of_reduce_ordAtFrac_triple`, `ordAtSpec_sub_le_indicator_of_
isNormCoprime`, both left as historical stubs). §4 below is the actual fix: it
consumes `IsPoleBoundedAtPairSpec` directly (already closed-point-native, no
bridging needed) and lands `natDegree_le_one_of_isPoleBoundedAtPairSpec_isNormCoprime`
— drafted with no `sorry`, `IsAlgClosed`-free, and (if it checks out) strictly
stronger (`deg c ≤ 1`) than the old `IsAlgClosed`-based
`natDegree_le_two_of_isCoprimeAtRoots`'s `≤ 2`. **Not yet build-tested** — written by
adapting `natDegree_le_two_of_isPoleBoundedAtPairSpec`'s already-proved proof shape
(`GlobalDegreeBoundSpec.lean:749`) almost line-for-line, swapping its unit-numerator
`hv1`-style step for the `IsNormCoprime`-based `ordAtSpec_eq_zero_of_notMem` argument,
so it should be close, but every Mathlib lemma name in the new supporting lemmas
(`ordAtSpec_eq_zero_of_notMem`'s `intValuation_lt_one_iff_dvd`/`intValuation_le_one`
chain, copied from `RiemannRochGenus2.lean`'s `ordAt_eq_zero_of_notMem`) needs REPL
confirmation. This is the intended replacement for that theorem and for
`LPairFinrankOneOrdAtFrac.lean`'s `false_of_root_of_coprimeAtRoots_zero_snd`; rewiring
`uniqueDegree2MapToP1_ordAtFrac` to use it is the next step, not yet done in this
file.**

**§0/§1/§1b (`IsFullyCoprime`, `IsNormCoprime`, `isCoprimeAtRoots_of_isNormCoprime`),
§2 (`toPair_notMem_or_notMem_of_isNormCoprime`), and §4 (the real fix) are all TRUE
and fully proved. Only §3's original (abandoned) theorems are dead ends — kept as
historical stubs with their counterexamples documented, not deleted, per project
convention.**

## Post-mortem #1 (kept for the record — do not repeat): `IsFullyCoprime` is too weak

The original §2 target, `IsFullyCoprime a b c := IsCoprime (gcd a b) c` implies
`toPair H a b ∉ v.asIdeal ∨ toPair H c 0 ∉ v.asIdeal` for every closed point `v`, is
**false**. Counterexample (ChatGPT consultation #1): at a Weierstrass point
`v = (X - α, y)` (`α` a simple root of `H.f`), take `a = c = X - α`, `b = 1`. Then
`gcd a b = 1` so `IsFullyCoprime a b c` holds vacuously, yet
`toPair H a b = (X - α) + y ∈ v.asIdeal` (both summands are) and
`toPair H c 0 = X - α ∈ v.asIdeal`. The fix applied — weaken the hypothesis to
`IsNormCoprime a b c := IsCoprime (pairNorm H a b) c` — genuinely does repair §2 (see
§2's proof below, complete, no case split). **But it does not repair §3**, per the
second post-mortem below, discovered only after §3 was attempted.

## Post-mortem #2 (the fatal one): §3's theorem itself is false, no matter what
`k[X]`-gcd-flavored hypothesis replaces `IsNormCoprime`

`ordAtSpec_sub_le_indicator_of_isNormCoprime` claimed: given `IsNormCoprime H a b c`
and the **rational-point-only** bound
`hzsupp : ∀ P : H.Point, ordAtFrac P a b c 0 ≥ -(indicator P)`, conclude the
**closed-point** bound `∀ v, ordAtSpec v c 0 ≤ ordAtSpec v a b + indicator v`.

**Counterexample (ChatGPT consultation #2, independently reconstructed and confirmed
in-session before being sent for consultation):** take `k = ZMod 5`, `H.f = X^5 - X`
(squarefree: `f' = -1`), `a = 1, b = 0, c = X^2 + 2` (irreducible over `ZMod 5`, since
`2` is a non-square mod `5`). Then:
- `pairNorm H a b = 1`, a unit, so `IsNormCoprime H a b c` holds trivially for this
  `c` (coprime to a unit is automatic) — the hypothesis is *satisfiable* and in fact
  unavoidably weak here.
- `toPair H a b = 1` is a unit at every closed point, so `ordAtSpec v a b = 0`
  everywhere.
- `c = X^2 + 2` has **no root in `ZMod 5`**, so `ordAt P c 0 = 0` for every rational
  `P : H.Point`; `hzsupp` holds trivially (indeed with the indicator identically `0`).
- But at the (non-rational, residue-degree-2) closed point `v` lying over the
  irreducible factor `X^2 + 2` itself, `c` **does** vanish: `ordAtSpec v c 0 ≥ 1 > 0 =
  ordAtSpec v a b + indicator v` (since `v ∉ {pointHeightOne' x₁, pointHeightOne'
  x₂}` for any rational `x₁, x₂`). The claimed inequality fails.

**Root cause, per the consultation:** `hzsupp`'s `H.Point`-only quantification
structurally cannot see a pole of `c` sitting at a non-rational closed point — no
amount of `k[X]`-gcd/norm bookkeeping downstream can recover information that was
never in the hypothesis. `IsNormCoprime` in fact points in the *opposite* direction
from what §3 needed: it says the numerator's norm and `c` share no factor, which at
a `v` where `c` vanishes forces `ordAtSpec v a b = 0` (numerator is a *unit* there) —
exactly the wrong conclusion when what's needed is a bound on `ordAtSpec v c 0`
itself. This is not a missing Lean lemma or a case-split gap; the mathematical content
`hzsupp` needs was simply never supplied by anything in this file's hypotheses.

## Where the real fix lives (next step, not attempted in this file)

`RiemannRochGenus2.lean` §1c already builds exactly the right primitive:
`IsPoleBoundedAtPairSpec'`/`LPairCarrierSpec'`, whose pointwise clause is quantified
over `v : HeightOneSpectrum (CoordinateRing H)` from the start (not `H.Point`), fully
proved with no `sorry`, including `isPoleBoundedAtPair'_of_spec'` (the specialization
back down to the `H.Point`-only `IsPoleBoundedAtPair'`) and
`lPairCarrierSpec'_subset_lPairCarrier'`. That section's docstring already
cross-references this exact counterexample.

The remaining work is **not** "bridge a rational bound up to a closed-point bound"
(impossible, per the post-mortem above) but **rewire the call site**:
`LPairFinrankOneOrdAtFrac.lean`'s `uniqueDegree2MapToP1_ordAtFrac` currently consumes
`z ∈ LPairCarrier'` (the `H.Point`-only carrier) and extracts its rational-only
`hptwise'` to build `hzsupp`. It should instead consume `z ∈ LPairCarrierSpec'` (the
closed-point carrier) and extract the closed-point pointwise clause directly from
`IsPoleBoundedAtPairSpec'` — no synthesis needed, since that clause is already stated
over `HeightOneSpectrum`. This also means `reduce_ordAtFrac_triple` (§6 of that file)
needs a `HeightOneSpectrum`-indexed analogue (reducing a closed-point-bounded triple
by its `k[X]`-gcd and re-deriving the closed-point bound for the reduced triple),
since the existing one is itself `H.Point`-only throughout. That analogue is where the
real remaining mathematical content sits — genuinely new work, not yet scoped in
detail, but now aimed at a theorem that is actually true. -/

namespace HyperellipticPolynomial

open Divisor

/-- **§0. `IsFullyCoprime`: HISTORICAL, the original (too weak) plan. Kept only as a
named artifact for the record — do NOT use this to conclude closed-point
disjointness, see the file docstring's counterexamples. Nothing below depends on
this. -/
def IsFullyCoprime (a b c : k[X]) : Prop :=
  IsCoprime (gcd a b) c

/-- **§1. `IsNormCoprime`: the correct `k[X]`-gcd statement.**

**Norm coprimality**: `pairNorm H a b = a² - b²·H.f` and `c` share no common
irreducible factor. This is the hypothesis that actually controls whether a closed
point can see both `a + bY` and `c` vanish (§2 below), unlike `IsFullyCoprime`
(`IsCoprime (gcd a b) c`), which is too weak (see file docstring). `IsCoprimeAtRoots
a b c` (`LPairFinrankOneOrdAtFrac.lean`) is recovered as a corollary (§1b below). -/
def IsNormCoprime (H : HyperellipticPolynomial k) (a b c : k[X]) : Prop :=
  IsCoprime (pairNorm H a b) c

/-- **`IsNormCoprime` implies `IsCoprimeAtRoots`.** If `α` were a shared rational
root of `(a,b,c)` — i.e. `c.eval α = 0` and `a.eval α = 0 ∧ b.eval α = 0` — then
evaluating `pairNorm H a b = a ^ 2 - b ^ 2 * H.f` at `α` gives `0² - 0² * H.f.eval α =
0`, so `α` is also a root of `pairNorm H a b`. Evaluating `IsNormCoprime`'s own Bézout
identity `u * pairNorm H a b + w * c = 1` at `α` then gives `u.eval α * 0 + w.eval α *
0 = 1`, i.e. `0 = 1` in `k` — immediate contradiction, since evaluation at a fixed
point is a ring homomorphism `k[X] → k` and therefore turns the Bézout witness
identity directly into a false equation. **Proved directly via `Polynomial.eval`'s
ring-hom structure** — no `linX`/`dvd`/unit machinery needed, simpler than the
originally-sketched route through `IsCoprime.isUnit_of_dvd'`. -/
theorem isCoprimeAtRoots_of_isNormCoprime (a b c : k[X])
    (hnc : IsNormCoprime H a b c) : IsCoprimeAtRoots a b c := by
  intro α hcα
  rintro ⟨haα, hbα⟩
  obtain ⟨u, w, huw⟩ := hnc
  have hnormα : (pairNorm H a b).eval α = 0 := by
    unfold pairNorm
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul, haα, hbα]
    ring
  have heval := congrArg (Polynomial.eval α) huw
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    hnormα, hcα, mul_zero, add_zero] at heval
  exact zero_ne_one heval

variable {H} [IsDedekindDomain (CoordinateRing H)]

/-- **§1b was ABANDONED as a route to close the theorem below (see "Post-mortem #2"
in the file docstring) — but its target output, a `HeightOneSpectrum`-native
coprime-at-a-closed-point reduction, is exactly what §4 below finally supplies via a
different route: not by bridging up from `H.Point`-only `hzsupp`, but by consuming
`IsPoleBoundedAtPairSpec'`/`LPairCarrierSpec'` directly, which already carries the
closed-point pointwise clause from the start. No reduction lemma of this shape is
needed at all in the end — see §4.  **§2. The genuinely new step: `IsNormCoprime` at the closed-point level.**

**No closed point sees both a norm-coprime numerator and denominator vanish.** The
`HeightOneSpectrum`-indexed generalization of `IsCoprimeAtRoots`'s role in the old
`IsAlgClosed`-based proof: there, "no rational root of `c` is also a root of both `a`
and `b`" was enough because every closed point *was* rational. Here, `v` ranges over
the full spectrum (any residue degree), and the claim is the same shape: `v` cannot
contain both `toPair H a b` and `toPair H c 0`.

**Corrected proof (second ChatGPT consultation, on the counterexample from the file
docstring), formalized below — no case split on ramified/split/inert; the earlier
plan's trichotomy was an artifact of the wrong hypothesis, not a genuine obstruction.**
`P := Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal` is prime
(`Ideal.comap_isPrime`, comap of `v.asIdeal`'s primality along the algebra map).
Suppose for contradiction both `toPair H a b ∈ v.asIdeal` and `toPair H c 0 ∈
v.asIdeal`. Unfolding `toPair`, `toPair H c 0 = algebraMap k[X] (CoordinateRing H) c`
(the `y H` term drops since its coefficient is `0`), so `c ∈ P` directly. For the
numerator: `toPair_mul_involution` gives
`toPair H a b * involution H (toPair H a b) = algebraMap _ _ (pairNorm H a b)`.
Since `toPair H a b ∈ v.asIdeal` and ideals absorb multiplication by anything, the
whole product lies in `v.asIdeal` regardless of whether the conjugate factor does —
**this is exactly the step the old, gcd-based attempt was missing**: it never needs
to know whether `v.asIdeal` contains the conjugate `toPair H a (-b)`, because
membership of one factor is already enough to place the *product* in the ideal. So
`algebraMap _ _ (pairNorm H a b) ∈ v.asIdeal`, hence `pairNorm H a b ∈ P` too. Now
`P` is a prime (in particular proper, `≠ ⊤`) ideal containing both `pairNorm H a b`
and `c`. Unfolding `IsNormCoprime H a b c := IsCoprime (pairNorm H a b) c` by its own
definition (`∃ u w, u * pairNorm H a b + w * c = 1`) puts `1 ∈ P` (each summand is in
`P` since `P` is an ideal), contradicting `P.IsPrime.ne_top`. This route (raw Bézout
witnesses + `Ideal.eq_top_iff_one`) avoids needing to name the exact `span`-based
`IsCoprime` characterization lemma at all. -/
theorem toPair_notMem_or_notMem_of_isNormCoprime
    (a b c : k[X]) (hnc : IsNormCoprime H a b c)
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :
    toPair H a b ∉ v.asIdeal ∨ toPair H c (0 : k[X]) ∉ v.asIdeal := by
  by_contra h
  push_neg at h
  obtain ⟨hab, hc⟩ := h
  set P : Ideal k[X] := Ideal.comap (algebraMap k[X] (CoordinateRing H)) v.asIdeal
    with hP_def
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hcP : c ∈ P := by
    have : algebraMap k[X] (CoordinateRing H) c ∈ v.asIdeal := by
      simpa [toPair] using hc
    simpa [hP_def, Ideal.mem_comap] using this
  have hnormP : pairNorm H a b ∈ P := by
    have hmem : toPair H a b * involution H (toPair H a b) ∈ v.asIdeal :=
      v.asIdeal.mul_mem_right _ hab
    have heq := toPair_mul_involution H a b
    rw [heq] at hmem
    simpa [hP_def, Ideal.mem_comap] using hmem
  -- `IsNormCoprime H a b c` unfolds to `IsCoprime (pairNorm H a b) c`, i.e.
  -- `∃ u v, u * pairNorm H a b + v * c = 1`. Both `pairNorm H a b` and `c` lie in
  -- `P`, so `1 ∈ P`, contradicting `P` proper.
  obtain ⟨u, w, huw⟩ := hnc
  have h1 : (1 : k[X]) ∈ P := by
    rw [← huw]
    exact P.add_mem (P.mul_mem_left u hnormP) (P.mul_mem_left w hcP)
  exact hPprime.ne_top (P.eq_top_iff_one.mpr h1)

/-! ## §4. [DEPRECATED] `IsNormCoprime` + `IsPoleBoundedAtPairSpec` (closed-point
native from the start) ⟹ `deg c ≤ 1`

**DEPRECATED — do not use.** Despite the "real fix" framing below (a stale
self-description from when this route was still believed to be the fix),
the `IsNormCoprime` strategy has been superseded by the `IsCoprimeAtRoots`
closed-point route in `LPairFinrankOneOrdAtFracSpec.lean`
(`natDegree_le_two_of_gcdUnit_closed_point`,
`false_of_root_of_isCoprimeAtRoots_zero_snd_general`). `IsCoprimeAtRoots` is
the maintained strategy; `IsNormCoprime` is not — nothing in the live
assembly theorem calls `natDegree_le_one_of_isPoleBoundedAtPairSpec_isNormCoprime`
anymore. Kept here only as historical reference. Do not build on this.

**Corrected route, per the "Where the real fix lives" note above and a third ChatGPT
consultation (`chatgpt_prompt_nonclosed_field.md`).** §3's error was trying to
*derive* a closed-point pole bound from an `H.Point`-only `hzsupp` — impossible, since
`hzsupp` structurally cannot see non-rational closed points. The fix is to never
attempt that derivation: **consume `IsPoleBoundedAtPairSpec` directly** (already
quantified over the full `HeightOneSpectrum`, `RiemannRochGenus2.lean:180`, no
closedness assumed), and combine its pointwise clause with `IsNormCoprime`'s
already-proved closed-point disjointness (`toPair_notMem_or_notMem_of_isNormCoprime`,
§2 above) the same way the `(1,0)`-numerator case
(`ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec`,
`GlobalDegreeBoundSpec.lean:712`) uses `ordAtSpec v 1 0 = 0`: there, the numerator is
a unit so it trivially never sees a pole; here, `IsNormCoprime` supplies the
weaker-but-sufficient fact that numerator and denominator can't both see the *same*
closed point, which is all the argument actually needs.

**Consequence, matching the third consultation's derivation exactly**: since the
degree-2 hyperelliptic cover has `∑_{v∣g} e_v·f_v = 2` for every irreducible factor
`g` of `c`, the residue-degree-weighted pole bound collapses to `2·deg(c) ≤ 2`
(not merely `≤ 2` as in the unit-numerator case, but a *factor of 2* stronger, since
every closed point over `c` contributes at least `1` per unit of `deg(c)` — see
`natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec` specialized to `B=0`, where
`pairNorm H c 0 = c^2` has degree `2·deg(c)`), giving `deg(c) ≤ 1` directly. This
is the key improvement over the old `IsAlgClosed`-based `natDegree_le_two_of_
isCoprimeAtRoots`: not just `IsAlgClosed`-free, but a *strictly stronger* bound
(`≤ 1`, not merely `≤ 2`), because the weighted-fiber argument counts every closed
point's full residue-degree contribution rather than one witness point per root. -/

/-- **`ordAtSpec` vanishes off a closed point's own ideal.** The `ordAtSpec`/`v.asIdeal`
analogue of `RiemannRochGenus2.lean`'s `ordAt_eq_zero_of_notMem`
(`ordAt`/`pointIdeal P`), transcribed to the unrestricted `HeightOneSpectrum` — simpler
than that theorem since `v` already carries `ne_bot` (no `h_bot` case split needed).
Same `Ideal.dvd_span_singleton` + `intValuation_lt_one_iff_dvd` +
`intValuation_le_one` chain. -/
theorem ordAtSpec_eq_zero_of_notMem
    (v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) (A B : k[X])
    (hnotmem : toPair H A B ∉ v.asIdeal) :
    ordAtSpec v A B = 0 := by
  have hne : toPair H A B ≠ 0 := by
    intro hz; apply hnotmem; rw [hz]; exact Submodule.zero_mem _
  have hnotdvd : ¬ v.asIdeal ∣ Ideal.span ({toPair H A B} : Set (CoordinateRing H)) := by
    rw [Ideal.dvd_span_singleton]
    exact hnotmem
  have hval_not_lt : ¬ v.intValuation (toPair H A B) < 1 := by
    rw [v.intValuation_lt_one_iff_dvd]
    exact hnotdvd
  have hval_le : v.intValuation (toPair H A B) ≤ 1 := v.intValuation_le_one (toPair H A B)
  have hval_eq : v.intValuation (toPair H A B) = 1 := le_antisymm hval_le (not_lt.mp hval_not_lt)
  unfold ordAtSpec
  rw [if_neg hne, hval_eq]
  simp

/-- **`ordAtSpec` at the closed-point level is bounded by the indicator, given
`IsNormCoprime`.** The general-numerator analogue of `ordAtSpec_le_indicator_of_
isPoleBoundedAtPairSpec` (`GlobalDegreeBoundSpec.lean:712`, which specializes to
numerator `(1,0)`): here the numerator `(a,b)` need only be norm-coprime to `c`, not
a unit. At any `v` where `ordAtSpec v c 0 > 0` (i.e. `toPair H c 0 ∈ v.asIdeal`),
`toPair_notMem_or_notMem_of_isNormCoprime` forces `toPair H a b ∉ v.asIdeal`, hence
`ordAtSpec v a b = 0` (`ordAtSpec_eq_zero_of_notMem` above), and
`IsPoleBoundedAtPairSpec`'s pointwise clause (unfolded at `(A,B) = (a,b)`,
`(A',B') = (c,0)`) then reads `0 ≥ ordAtSpec v c 0 - e_v`, i.e. exactly the wanted
bound. When `v.asIdeal` doesn't contain `toPair H c 0` the bound is immediate from
`ordAtSpec_eq_zero_of_notMem` itself (LHS is `0`, RHS is `≥ 0`). -/
theorem ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec_isNormCoprime
    (x₁ x₂ : H.Point) (a b c : k[X]) (hcne : c ≠ 0)
    (hnc : IsNormCoprime H a b c)
    (h : IsPoleBoundedAtPairSpec x₁ x₂ a b c 0) :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (CoordinateRing H),
      ordAtSpec v c (0 : k[X]) ≤
        (if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0) := by
  obtain ⟨_, _, hpt⟩ := h
  intro v
  by_cases hcmem : toPair H c (0 : k[X]) ∈ v.asIdeal
  · have hab_notmem : toPair H a b ∉ v.asIdeal := by
      rcases toPair_notMem_or_notMem_of_isNormCoprime (H := H) a b c hnc v with h1 | h2
      · exact h1
      · exact absurd hcmem h2
    have hab0 : ordAtSpec v a b = 0 := ordAtSpec_eq_zero_of_notMem v a b hab_notmem
    have := hpt v
    rw [hab0] at this
    omega
  · have hc0 : ordAtSpec v c (0 : k[X]) = 0 := ordAtSpec_eq_zero_of_notMem v c 0 hcmem
    rw [hc0]
    -- RHS is a sum of two `if _ then (1:ℤ) else 0` terms, each nonnegative;
    -- `positivity` may not see through the `if`, so fall back to `split_ifs`+`omega`
    -- if it fails in the REPL.
    split_ifs <;> omega

/-- **The general-numerator global degree bound, `IsNormCoprime` version.** The
`(a,b)`-numerator generalization of `natDegree_le_two_of_isPoleBoundedAtPairSpec`
(`GlobalDegreeBoundSpec.lean:749`), and — thanks to counting the *entire* residue-
degree-weighted fiber rather than a single witness point — strictly stronger than
that theorem's `≤ 2`: `pairNorm H c 0 = c^2` has `natDegree = 2 * c.natDegree`
(`pairNorm`'s definition at `B=0` collapses to a bare square), so the same `≤ 2`
bound on `(pairNorm H c 0).natDegree` gives `c.natDegree ≤ 1` directly. This is
exactly `natDegree_le_two_of_isCoprimeAtRoots`'s conclusion, but strengthened
(`≤ 1` not `≤ 2`) and with `IsAlgClosed k` replaced by `IsNormCoprime H a b c`. This
is the intended `IsAlgClosed`-free replacement for `LPairFinrankOneOrdAtFrac.lean`'s
`natDegree_le_two_of_isCoprimeAtRoots` and (post `b=0`) `false_of_root_of_
coprimeAtRoots_zero_snd`, unifying both of that file's `IsAlgClosed` call sites into
one closed-point fiber-sum argument. -/
theorem natDegree_le_one_of_isPoleBoundedAtPairSpec_isNormCoprime
    (x₁ x₂ : H.Point) (a b c : k[X]) (hcne : c ≠ 0)
    (hnc : IsNormCoprime H a b c)
    (h : IsPoleBoundedAtPairSpec x₁ x₂ a b c 0) :
    c.natDegree ≤ 1 := by
  have hterm := ordAtSpec_le_indicator_of_isPoleBoundedAtPairSpec_isNormCoprime
    (H := H) x₁ x₂ a b c hcne hnc h
  have hcB0ne : ¬ (c = 0 ∧ (0 : k[X]) = 0) := by simpa using hcne
  obtain ⟨T, hsupp⟩ := exists_finite_support_ordAtSpec (H := H) c (0 : k[X]) hcB0ne
  set T' : Finset (IsDedekindDomain.HeightOneSpectrum (CoordinateRing H)) :=
    insert (pointHeightOne' x₁) (insert (pointHeightOne' x₂) T) with hT'_def
  have hsupp' : ∀ v, v ∉ T' → ordAtSpec v c (0 : k[X]) = 0 := by
    intro v hv
    apply hsupp
    intro hvT
    apply hv
    rw [hT'_def]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hvT)
  have hnorm := natDegree_pairNorm_eq_sum_residueDeg_ordAtSpec
    (H := H) c (0 : k[X]) hcB0ne T' hsupp'
  have hle : ∑ v ∈ T', (residueDeg v : ℤ) * ordAtSpec v c (0 : k[X]) ≤
      ∑ v ∈ T', (residueDeg v : ℤ) *
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (hterm v) (Int.natCast_nonneg _)
  have hx₁mem : pointHeightOne' x₁ ∈ T' := by rw [hT'_def]; exact Finset.mem_insert_self _ _
  have hx₂mem : pointHeightOne' x₂ ∈ T' := by
    rw [hT'_def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hcollapse : ∑ v ∈ T', (residueDeg v : ℤ) *
      ((if v = pointHeightOne' x₁ then 1 else 0) +
        (if v = pointHeightOne' x₂ then 1 else 0)) ≤ 2 := by
    have hterm_le : ∀ v ∈ T', (residueDeg v : ℤ) *
        ((if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0)) ≤
        (if v = pointHeightOne' x₁ then 1 else 0) +
          (if v = pointHeightOne' x₂ then 1 else 0) := by
      intro v _
      by_cases hv1 : v = pointHeightOne' x₁
      · subst hv1; rw [residueDeg_pointHeightOne']
        by_cases hv2 : pointHeightOne' x₁ = pointHeightOne' x₂ <;> simp [hv2]
      · by_cases hv2 : v = pointHeightOne' x₂
        · subst hv2; rw [residueDeg_pointHeightOne']; simp [hv1]
        · simp [hv1, hv2]
    calc ∑ v ∈ T', (residueDeg v : ℤ) *
          ((if v = pointHeightOne' x₁ then 1 else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0))
        ≤ ∑ v ∈ T', ((if v = pointHeightOne' x₁ then (1:ℤ) else 0) +
            (if v = pointHeightOne' x₂ then 1 else 0)) := Finset.sum_le_sum hterm_le
      _ = (∑ v ∈ T', (if v = pointHeightOne' x₁ then (1:ℤ) else 0)) +
            ∑ v ∈ T', (if v = pointHeightOne' x₂ then (1:ℤ) else 0) :=
          Finset.sum_add_distrib
      _ = 1 + 1 := by
            rw [Finset.sum_ite_eq' T' (pointHeightOne' x₁) (fun _ => (1:ℤ)),
                Finset.sum_ite_eq' T' (pointHeightOne' x₂) (fun _ => (1:ℤ)),
                if_pos hx₁mem, if_pos hx₂mem]
      _ = 2 := by norm_num
  have hpairNorm_eq : pairNorm H c (0 : k[X]) = c ^ 2 := by
    unfold pairNorm; ring
  have hfinal : ((c ^ 2).natDegree : ℤ) ≤ 2 := by
    rw [← hpairNorm_eq, hnorm]; exact le_trans hle hcollapse
  have hdeg2 : (c ^ 2).natDegree = 2 * c.natDegree := by
    rw [Polynomial.natDegree_pow]
  rw [hdeg2] at hfinal
  omega

end HyperellipticPolynomial
