import Mathlib

/-!
# Cantor reduction preserves the Mumford identity

**Why this file exists.** `DataDerivationSolve.lean`'s `IsMumfordTarget`
(`u ∣ v² - f`, the condition `(u,v)` is a genuine Mumford representative
for the *target* `(u0,u1,v0,v1)`) is currently carried as a bare,
undischarged hypothesis — see that file's own docstring: "Not derived
from anything else in this file — it is a hypothesis on the sample data
... supplied by whatever upstream construction produces a genuine
Mumford pair." That upstream construction is `00_sample_specs.jl`'s
`cantor_add`, specifically its reduction loop:

```julia
while length(u) - 1 > 2
    v2_poly = p_mul(v, v, p)
    num_next = p_sub(f, v2_poly, p)        -- f - v²
    u_next, _ = p_divrem(num_next, u, p)   -- u_next := (f - v²) / u, remainder DISCARDED
    ...
    neg_v = p_scale(v, -1, p)
    _, v_next = p_divrem(neg_v, u_next, p) -- v_next := (-v) mod u_next
    u, v = u_next, v_next
end
```

Julia's `p_divrem` discards the remainder of `(f - v²) / u` on the
assumption that the division is exact, i.e. that `u ∣ f - v²` — the
Mumford identity — holds *before* the step. This file proves that if it
holds before the step, it holds *after* the step too: reduction preserves
the Mumford identity. Combined with a base case (the generator
`(u_G, v_G)` satisfies the identity — a single concrete, checkable fact,
not proved in this file) and induction over `cantor_add`'s composition +
reduction structure, this discharges `IsMumfordTarget` from Cantor's own
correctness rather than carrying it as an assumption on the sample data.

**Scope of this file.** Only the reduction step (`(u,v) → (u_next,
v_next)` inside the `while` loop) is proved generically here. `cantor_add`
also has a *composition* half (building `(u,v)` from two inputs via
`gcdx`, before the reduction loop even starts) — showing composition
*also* preserves the Mumford identity is a separate, not-yet-attempted
lemma; see the module docstring note at the bottom of this file for
exactly what remains.

This is deliberately proved over a **generic field** `K` (not `K2 p
c0..c4` specifically), matching `sq_mod_eq_of_dvd`'s style in
`DataDerivationMumford.lean` — the reduction step is pure polynomial
algebra, independent of this project's particular tower construction, so
proving it generically means it can be instantiated wherever a Mumford
pair over any field shows up, not just this one target.

**Not yet checked against the actual Lean toolchain.** No REPL was
available this pass (same limitation this project's other recent passes
have flagged). Every `ring`-closed identity below was checked by hand,
and every named Mathlib lemma used (`Polynomial.dvd_modByMonic_sub`,
`dvd_mul_of_dvd_right`, `dvd_add`) is one this project has *already*
confirmed against the live toolchain elsewhere (see the per-lemma
comments below for exactly where) rather than a newly-guessed name — but
"matches lemmas verified elsewhere" is not the same as "this file itself
has been built." Confirm with `lake build` before relying on this file
downstream, per this project's own standing practice.

**One hypothesis is carried but unused**: `hu_next_monic` is not
consumed by either proof below — `Polynomial.dvd_modByMonic_sub` doesn't
need it (confirmed unconditional, see `DataDerivationMumford.lean`'s own
note on this exact lemma), and nothing else in this argument needs
`u_next`'s monicity either. Kept in the signature anyway, matching
`DataDerivationMumford.lean`'s `vRS` precedent (`uRS_monic`'s hypothesis
`hcur` is threaded similarly): the CALLER's `v_next := (-v) %ₘ u_next`
is only the mathematically correct residual once `u_next` really is
monic (`%ₘ`'s *defining property* — degree `<` divisor's degree — needs
it even though this file's own algebra doesn't), so requiring it here
keeps this theorem's use honest rather than silently relying on a
`%ₘ`-by-a-non-monic-polynomial value that isn't the intended remainder.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

section CantorReductionStep

variable {K : Type*} [Field K]

/-- **One step of Cantor reduction preserves the Mumford identity.**

Given `u ∣ f - v²` (the Mumford identity holds for `(u,v)`), and
`u_next` an EXACT quotient of `f - v²` by `u` (`f - v² = u * u_next`,
matching Julia's `p_divrem` with a verified-zero remainder — see
`hexact` below), and `v_next := (-v) %ₘ u_next` (matching Julia's
`neg_v mod u_next`, using Mathlib's monic-divisor remainder `%ₘ`), then
`u_next ∣ f - v_next²`: the Mumford identity holds for `(u_next,
v_next)` too.

**Proof idea**, matching `sq_mod_eq_of_dvd`'s structure one file over:
`v_next ≡ -v (mod u_next)`, so `v_next² ≡ v² (mod u_next)` (difference of
squares, `sq_mod_eq_of_dvd_step3`/`step4`-style). Combined with `f - v² =
u * u_next` (so `f - v² ≡ 0 mod u_next` — `u_next` obviously divides its
own multiple `u * u_next`), this gives `f - v_next² ≡ f - v² ≡ 0 (mod
u_next)`, i.e. exactly the claim. -/
theorem cantorReductionStep_preserves_mumford
    {u v f u_next v_next : Polynomial K}
    (hu_next_monic : u_next.Monic)
    (hexact : f - v ^ 2 = u * u_next)
    (hv_next : v_next = (-v) %ₘ u_next) :
    u_next ∣ f - v_next ^ 2 := by
  -- Step 1: `u_next ∣ (v_next %ₘ-remainder-shifted) ... ` — concretely,
  -- `u_next ∣ (v_next) - (-v)`, the division-algorithm remainder fact.
  have hrem : u_next ∣ v_next - (-v) := by
    rw [hv_next]
    have := Polynomial.dvd_modByMonic_sub (-v) u_next
    simpa using this
  -- Step 2: difference of squares, `u_next ∣ v_next² - v²`.
  have hvsq : u_next ∣ v_next ^ 2 - v ^ 2 := by
    have hsq : v_next ^ 2 - v ^ 2 = (v_next - v) * (v_next - (-v)) := by ring
    rw [hsq]
    exact dvd_mul_of_dvd_right hrem (v_next - v)
  -- Step 3: `u_next ∣ f - v²` (since `f - v² = u * u_next`, an obvious
  -- multiple of `u_next`).
  have hfv : u_next ∣ f - v ^ 2 := ⟨u, by rw [hexact]; ring⟩
  -- Step 4: combine via `dvd_add` (matching this project's established
  -- pattern, e.g. `sq_mod_eq_of_dvd_step2`/`_step4` in
  -- `DataDerivationMumford.lean`, which use `dvd_add` + a `ring`-checked
  -- rewrite rather than an unconfirmed `dvd_sub` name): negate `hvsq` to
  -- get `u_next ∣ v² - v_next²` via the same `⟨witness, by ring⟩` idiom
  -- as `hfv` above, then add it to `hfv`.
  obtain ⟨cv, hcv⟩ := hvsq
  have hvsq' : u_next ∣ v ^ 2 - v_next ^ 2 := ⟨-cv, by rw [show v ^ 2 - v_next ^ 2 = -(v_next ^ 2 - v ^ 2) by ring, hcv]; ring⟩
  have hid : f - v_next ^ 2 = (f - v ^ 2) + (v ^ 2 - v_next ^ 2) := by ring
  rw [hid]
  exact dvd_add hfv hvsq'

/-- Corollary stated with the sign flipped to `u ∣ v² - f`, matching
`IsMumfordTarget`'s actual literal shape in `DataDerivationSolve.lean`
(that file's `hMumford`/`IsMumfordTarget` are stated as `u ∣ v^2 - f`,
not `u ∣ f - v^2`) — avoided leaning on a `dvd_neg`/`neg_dvd` Mathlib
name here (not independently confirmed against this project's toolchain
the way `dvd_modByMonic_sub` was), and instead just re-derives the
divisibility directly against the negated target via the same
`⟨witness, by ring⟩` idiom `hfv` already uses above, which only needs
`Dvd.dvd`'s definition (`a ∣ b ↔ ∃ c, b = a * c`), not any named lemma. -/
theorem cantorReductionStep_preserves_mumford'
    {u v f u_next v_next : Polynomial K}
    (hu_next_monic : u_next.Monic)
    (hexact : f - v ^ 2 = u * u_next)
    (hv_next : v_next = (-v) %ₘ u_next) :
    u_next ∣ v_next ^ 2 - f := by
  obtain ⟨c, hc⟩ := cantorReductionStep_preserves_mumford hu_next_monic hexact hv_next
  exact ⟨-c, by rw [show v_next ^ 2 - f = -(f - v_next ^ 2) by ring, hc]; ring⟩

end CantorReductionStep

/-!
## What this closes, and what's still open

**Closed by this file**: the reduction step itself (`(u,v) → (u_next,
v_next)` inside `cantor_add`'s `while` loop) is now a proved theorem,
`cantorReductionStep_preserves_mumford'`, not an assumption — given the
Mumford identity held before the step and the quotient really is exact,
it holds after.

**Still open, and precisely scoped** (not attempted in this file):

1. **`cantor_add`'s composition half** (building `(u,v)` from two inputs
   `(u1,v1),(u2,v2)` via `gcdx`, lines 152-169 of
   `00_sample_specs.jl`, BEFORE the reduction loop starts) also needs a
   "preserves the Mumford identity" lemma — different algebra (Bézout
   combination, not a single division step), not covered here.
2. **The base case**: the generator `(u_G, v_G)` genuinely satisfies
   `v_G² ≡ f (mod u_G)` for this project's concrete curve. This is a
   finite check on concrete numbers (`f = x^5+x+2`, `u_G, v_G` as given
   in `00_sample_specs.jl`), not a theorem needing K-generic algebra.
   **Verified numerically outside Lean this pass** (Python reimplementation
   of `p_divrem`/`p_mul`/`p_sub`, run against `p=2371157`,
   `u_G=[2307335,2061398,1]`, `v_G=[1348746,397106]`: `(v_G² - f) %ₘ u_G
   = 0` exactly, quotient `q = [1803655, 537259, 2061398, 2371156]`) —
   and, going further, the SAME zero-remainder check was run across 18
   independent `(sample slot, alpha)` combinations spanning the full
   `cantor_mul` double-and-add path (not just the base case), all exact.
   This is strong evidence the whole chain is sound, but is a numerical
   check outside Lean, not a kernel-checked proof — the actual `decide`/
   `native_decide` instantiation over `ZMod p` inside Lean is still not
   attempted here, since this file stays curve-and-instance-agnostic.
3. **Wiring**: composing (1) + (2) + this file's reduction-step lemma
   via induction over `cantor_mul`'s double-and-add structure, then
   specializing the generic `K` here to `K2 p c0 c1 c2 c3 c4`
   (`DataDerivationTower.lean`) to actually discharge
   `IsMumfordTarget` in `DataDerivationSolve.lean` for a *symbolic*
   target — this is the actual endpoint but needs (1)-(2) first, and
   needs deciding whether `IsMumfordTarget` is proved for the
   PRODUCTION concrete instance only (route (a), matching
   `ROADMAP-reduce-to-zerodim.md`'s Step 4 recommendation to try
   concrete-instance discharge before generic) or generically over
   symbolic `alpha` (much harder, same shape of difficulty as that
   roadmap's task (B)/`Bad`-locus work) — recommend route (a) first,
   for the same reasons that roadmap gives.
-/

end TheDataDerivation
end Genus2Lean
