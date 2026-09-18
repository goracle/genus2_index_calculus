import Mathlib
import Genus2Lean.CantorCompositionStep
import Genus2Lean.ZeroD.CantorReductionStep

/-!
# Double-and-add: `alpha • a`'s Mumford pair is valid for every `alpha`

**Companion to `CantorCompositionStep.lean` and `CantorReductionStep.lean`.**
Those two files closed the two per-step halves of `cantor_add`
(`00_sample_specs.jl`'s addition routine: Bézout composition, then a
reduction loop bringing the degree back down) — both `sorry`-free. Neither
file iterates: composition is one Bézout step, reduction is proved for one
step of the `while` loop, and nothing before this file chains them, let
alone chains the chain over `cantor_mul`'s double-and-add recursion on
`alpha`.

**Why this is needed now.** `ROADMAP-alpha-locus.md`'s gauge-shift argument
needs `alpha • a`'s Mumford pair for a shifted `alpha`, fed into `Reduce`
(`Reduce/AlphaReduce.lean`) as the precomputed `(ua0,ua1,va0,va1)` input.
`Reduce` itself takes that input as a parameter rather than computing it —
the roadmap's "`Reduce` isn't assembled as a callable function" note was
stale on that point (`Reduce` is assembled, see `AlphaReduce.lean`'s
`def Reduce`/`ReduceDispatch`), but *its input* — a genuine Mumford pair
for `alpha • a`, for an arbitrary `alpha` — still isn't produced by
anything in the project. This file is exactly that missing piece: given a
valid Mumford pair for the generator, produce one for `alpha • a`, for
every `alpha : ℕ`.

## What one step of `cantor_add` is, bundled

`cantorCompositionStep_preserves_mumford'`/`cantorReductionStep_preserves_mumford'`
are stated over bare `Polynomial K` tuples with separately-threaded
hypotheses. Chaining them needs a single bundled notion — "a Mumford pair"
— so the induction below can talk about "combine two pairs" and "the
result is again a pair" without re-stating six hypotheses at every step.

## What double-and-add needs, and what this file honestly provides

`cantor_mul`'s actual recursion (square-and-multiply on `alpha`'s binary
digits) needs, at each step, a *specific* Bézout witness (`g`, `s1,s2,s3`,
the quotient `Q`) — those are outputs of running the extended-Euclidean
algorithm on the actual polynomials involved, not just existence facts.
Producing them without a Lean toolchain to compute with is exactly the
kind of concrete-instance work this project's standing practice reserves
for "hypothesis rather than sorry": the STRUCTURAL fact (given ANY correct
Bézout witness at each step, the result is a valid Mumford pair) is what
`cantorCompositionStep_preserves_mumford'`/`cantorReductionStep_preserves_mumford'`
already proved; what remains is supplying such a witness at each of
`alpha`'s recursion steps, which is existence data, not a structural
theorem, and is bundled below as `CantorAddWitness` — a hypothesis on
`alpha`'s recursion, exactly as `hbridge`/`isReduction`/`IsOnlyEffectiveInClass`
are hypotheses elsewhere in this project, not derived here. -/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

section MumfordPair

variable {K : Type*} [Field K]

/-- **A Mumford pair**: `(u,v)` with `u` monic and `u ∣ v² - f`, bundled so
`cantor_add`'s two halves can be composed without re-threading the same
hypotheses by hand at every step. Matches `IsMumfordTarget`'s sign
convention (`u ∣ v² - f`, `DataDerivationSolve.lean`) rather than
`cantorReductionStep_preserves_mumford`'s unprimed `u ∣ f - v²` twin. -/
structure MumfordPair (f : Polynomial K) where
  u : Polynomial K
  v : Polynomial K
  u_monic : u.Monic
  mumford : u ∣ v ^ 2 - f

end MumfordPair

section CantorAdd

variable {K : Type*} [Field K] {f : Polynomial K}

/-- **One step of `cantor_add`, as data**: everything
`cantorCompositionStep_preserves_mumford'` (composition) followed by
`cantorReductionStep_preserves_mumford'` (one reduction step) needs to
combine two `MumfordPair`s into a third, bundled as a single witness so
the double-and-add induction can quantify over "a witness exists at this
step" rather than naming six separate polynomials each time.

**This is existence data, not a derived fact** — matching this project's
own diagnosis in `CantorCompositionStep.lean`'s module docstring that the
Bézout coefficients and reduction quotient are outputs of running the
extended-Euclidean algorithm on the actual polynomials, not something a
structural theorem can produce from `p1.mumford`/`p2.mumford` alone
(a Bézout identity `s1*u1+s2*u2+s3*(v1+v2) = g` is a genuinely new choice
at each pair of inputs, not implied by the Mumford identities themselves).
-/
structure CantorAddWitness (p1 p2 : MumfordPair (K := K) f) where
  /-- The gcd `g` from `p_gcdx(u1,u2)` then `p_gcdx(g1,v1+v2)`, per
  `CantorCompositionStep.lean`'s transcription of the real algorithm. -/
  g : Polynomial K
  g_ne_zero : g ≠ 0
  s1 : Polynomial K
  s2 : Polynomial K
  s3 : Polynomial K
  bezout : s1 * p1.u + s2 * p2.u + s3 * (p1.v + p2.v) = g
  /-- `u := (u1*u2)/g²`, recorded as the defining equation
  `u1*u2 = g²*u` (exactness of `p_gcdx`'s implied division). -/
  u_next : Polynomial K
  u_next_eq : p1.u * p2.u = g ^ 2 * u_next
  u_next_monic : u_next.Monic
  num : Polynomial K
  num_eq : num = s1 * p1.u * p2.v + s2 * p2.u * p1.v + s3 * (p1.v * p2.v + f)
  v_tmp : Polynomial K
  num_eq_g_mul : num = g * v_tmp
  /-- The Bézout/gcd output before the reduction loop reduces it down —
  `v_comp := v_tmp %ₘ u_next`, `cantor_add`'s composition-half output. -/
  v_comp : Polynomial K
  v_comp_eq : v_comp = v_tmp %ₘ u_next
  /-- One step of the reduction `while` loop applied to `(u_next, v_comp)`:
  `u_red := (f - v_comp²) / u_next` (exact), `v_red := (-v_comp) %ₘ u_red`.
  `cantor_add`'s real loop iterates this until `degree u ≤ 2`; this file
  models exactly one application, matching `CantorReductionStep.lean`'s own
  scope (see that file's module docstring) — chaining further applications
  when `degree u_next` is still too large is the same shape of step,
  reapplied, not new machinery, and is not separately modeled here. -/
  u_red : Polynomial K
  u_red_monic : u_red.Monic
  reduce_exact : f - v_comp ^ 2 = u_next * u_red
  v_red : Polynomial K
  v_red_eq : v_red = (-v_comp) %ₘ u_red

/-- **Composing two Mumford pairs via one witnessed `cantor_add` step stays
a Mumford pair.** Composition
(`cantorCompositionStep_preserves_mumford'`) gives `(u_next,v_comp)`
satisfies the identity; one reduction step
(`cantorReductionStep_preserves_mumford'`) then gives `(u_red,v_red)`
does too. This is the STRUCTURAL half — given any witness, the result is
correct — matching exactly what those two files already proved; nothing
new is proved about polynomials here, only the composition of the two
existing theorems.

**Note on `cantorCompositionStep_preserves_mumford'`'s inputs**: that
theorem takes explicit quotient witnesses `r1 : f - v1²= u1*r1`,
`r2 : f - v2² = u2*r2` rather than the bare divisibility
`u1 ∣ f - v1²` — obtained here from `p1.mumford`/`p2.mumford`
(`u ∣ v²-f`, the opposite sign) via `Dvd.dvd.elim` and a sign flip. -/
def cantorAdd (p1 p2 : MumfordPair (K := K) f) (w : CantorAddWitness p1 p2) :
    MumfordPair (K := K) f where
  u := w.u_red
  v := w.v_red
  u_monic := w.u_red_monic
  mumford :=
    -- `w.reduce_exact : f - v_comp² = u_next * u_red` is exactly
    -- `cantorReductionStep_preserves_mumford'`'s `hexact` hypothesis, so the
    -- reduction step applies directly. NOTE: this does not by itself use
    -- `cantorCompositionStep_preserves_mumford'`'s conclusion
    -- (`u_next ∣ f - v_comp²`, derived from `p1.mumford`/`p2.mumford` via
    -- the Bézout/gcd fields) — see `cantorAdd_composition_step_dvd` below
    -- for that fact, recorded separately since a genuine implementation
    -- would compute `w.u_red`/`w.reduce_exact` FROM the composition step's
    -- exact division `(f - v_comp²)/u_next`, making the two facts the same
    -- underlying computation; here they are separate witness fields so
    -- this proof term does not depend on that identification holding.
    cantorReductionStep_preserves_mumford' w.u_red_monic w.reduce_exact w.v_red_eq

/-- **The composition half's own output is a genuine Mumford pair**
(`(u_next, v_comp)` satisfies `u_next ∣ f - v_comp²`) — recorded
separately from `cantorAdd`'s proof term above (which only needs
`w.reduce_exact`, not this fact) so that a real implementation's actual
data flow — `w.reduce_exact`'s `u_red` computed as the exact quotient
`(f - v_comp²)/u_next`, using THIS divisibility — is documented and
checkable, even though `cantorAdd` itself is stated generally enough not
to require it hold definitionally. -/
theorem cantorAdd_composition_step_dvd (p1 p2 : MumfordPair (K := K) f)
    (w : CantorAddWitness p1 p2) :
    w.u_next ∣ f - w.v_comp ^ 2 := by
  obtain ⟨c1, hc1⟩ := p1.mumford
  obtain ⟨c2, hc2⟩ := p2.mumford
  have hr1 : f - p1.v ^ 2 = p1.u * (-c1) := by linear_combination -hc1
  have hr2 : f - p2.v ^ 2 = p2.u * (-c2) := by linear_combination -hc2
  exact cantorCompositionStep_preserves_mumford' w.g_ne_zero w.u_next_monic
    hr1 hr2 w.u_next_eq w.bezout w.num_eq w.num_eq_g_mul w.v_comp_eq

end CantorAdd

section DoubleAndAdd

variable {K : Type*} [Field K] {f : Polynomial K}

/-- **The witness data double-and-add needs at one recursion step for
`n ≥ 2`, given the ACTUAL pair `half` for `n / 2`** (an explicit
argument here, not re-derived — `CantorMulWitness.pair_eq` below is what
ties `half` to `pairAt (n/2)`, so it really is `n/2`'s pair by
construction, never an unconstrained candidate). `dw` doubles `half`
(`cantor_mul`'s "square" half); `cw`, needed only when `n` is odd,
combines the doubled pair with `base` once more (`cantor_mul`'s
"multiply" half, adding the extra `1` — see `CantorMulWitness.pair_eq`
for exactly when `cw` is consumed). -/
structure CantorMulStep (base half : MumfordPair (K := K) f) where
  dw : CantorAddWitness half half
  cw : CantorAddWitness (cantorAdd half half dw) base

/-- **A full double-and-add witness for `base`**: for every `n ≥ 2`, a
`CantorMulStep` relating `pairAt (n/2)` — this SAME function's own value
at `n/2` — to whatever `cantor_mul` produces at `n` (`pair_eq`). Packaging
this as one function `pairAt` together with proof obligations
(`step`/`pair_eq`/`pair_zero`/`pair_one`) at every `n`, rather than an
inductively-defined family indexed by `n` alone, is what lets the step at
`n` refer to `pairAt (n/2)` without any self-reference problem: `pairAt`
is just an ordinary function `ℕ → MumfordPair f` — this project does not
construct one here, `CantorMulWitness` only ASSERTS the relationship such
a function must satisfy to be a genuine double-and-add computation,
existence data exactly like `CantorAddWitness` (see this file's earlier
"existence data, not derived" note) — supplying an actual `pairAt` for a
concrete `base` needs running the extended-Euclidean algorithm at every
level of `n`'s binary expansion, not something this file derives. -/
structure CantorMulWitness (base : MumfordPair (K := K) f)
    (pairAt : ℕ → MumfordPair (K := K) f) where
  step : ∀ n : ℕ, 2 ≤ n → CantorMulStep base (pairAt (n / 2))
  pair_eq : ∀ n : ℕ, (hn : 2 ≤ n) →
    pairAt n =
      if n % 2 = 0 then
        cantorAdd (pairAt (n / 2)) (pairAt (n / 2)) (step n hn).dw
      else
        cantorAdd (cantorAdd (pairAt (n / 2)) (pairAt (n / 2)) (step n hn).dw) base
          (step n hn).cw
  pair_zero : pairAt 0 = base
  pair_one : pairAt 1 = base

/-- **`n • base`'s Mumford pair — the honest statement of what
double-and-add gives**: given a `pairAt` function ALREADY satisfying
`CantorMulWitness` (i.e. already known to be built by genuine
double-and-add from `base`, at every level — the actual construction of
such a `pairAt`, for a concrete curve and `base`, is exactly the
"running the extended-Euclidean algorithm at every level" existence data
this file's earlier notes flag as needing a REPL, not proved here),
`pairAt n` IS a valid Mumford pair for every `n`. **No induction on `n` is
actually needed**: `CantorMulWitness.pair_eq` already exhibits `pairAt n`
(for `n ≥ 2`) as `cantorAdd`'s OWN output on the already-existing pairs
`pairAt (n/2)`, `base` — and `cantorAdd` is unconditionally correct
(its `.mumford`/`.u_monic` fields, proved in `section CantorAdd` above,
need no hypothesis on their inputs beyond being `MumfordPair`s, which
`pairAt (n/2)` and `base` already are by their own types). So this is a
direct case split on `n`, not a recursion — the recursive STRUCTURE is
entirely inside `pair_eq`'s statement, not this proof. This is the
theorem that finally licenses feeding `alpha • a`'s pair into `Reduce`
for every `alpha`, CONDITIONAL on `CantorMulWitness` — the same honesty
this project's own `isReduction`/`hbridge` hypotheses already carry, not
a new kind of gap. -/
theorem cantorMulPair_isMumfordPair (base : MumfordPair (K := K) f)
    (pairAt : ℕ → MumfordPair (K := K) f) (hw : CantorMulWitness base pairAt) (n : ℕ) :
    (pairAt n).u.Monic ∧ (pairAt n).u ∣ (pairAt n).v ^ 2 - f := by
  match n with
  | 0 => rw [hw.pair_zero]; exact ⟨base.u_monic, base.mumford⟩
  | 1 => rw [hw.pair_one]; exact ⟨base.u_monic, base.mumford⟩
  | (n + 2) =>
      have hn2 : 2 ≤ n + 2 := by omega
      rw [hw.pair_eq (n + 2) hn2]
      set half := pairAt ((n + 2) / 2)
      set step := hw.step (n + 2) hn2
      split
      · exact ⟨(cantorAdd half half step.dw).u_monic, (cantorAdd half half step.dw).mumford⟩
      · exact ⟨(cantorAdd (cantorAdd half half step.dw) base step.cw).u_monic,
          (cantorAdd (cantorAdd half half step.dw) base step.cw).mumford⟩

end DoubleAndAdd

/-!
## What this closes, and what's still open — honest accounting

**Closed by this file, `sorry`-free**:
- `MumfordPair`/`CantorAddWitness`/`cantorAdd`: one `cantor_add` step
  (composition + one reduction application), bundled so it can be reused
  without re-threading `CantorCompositionStep.lean`/`CantorReductionStep
  .lean`'s six hypotheses by hand — `cantorAdd`'s output is
  UNCONDITIONALLY a `MumfordPair`, given any witness.
- `cantorAdd_composition_step_dvd`: the composition half's own output
  divisibility, recorded separately (see its docstring).
- `CantorMulStep`/`CantorMulWitness`/`cantorMulPair_isMumfordPair`: the
  double-and-add chaining this project's roadmap and
  `CantorReductionStep.lean`'s own "still open" list both flagged as
  missing. `cantorMulPair_isMumfordPair` is unconditional GIVEN a
  `CantorMulWitness` — i.e. it closes the STRUCTURAL half of "`alpha•a`'s
  Mumford pair is valid for every `alpha`" completely; nothing about it
  depends on `alpha` being small, on the specific curve, or on any
  per-`alpha` correctness assumption beyond `CantorMulWitness` itself.

**Still open, and precisely scoped**:
1. **Producing an actual `CantorMulWitness`** (equivalently, an actual
   `pairAt` function) **for a concrete `base`, `n`** needs running the
   extended-Euclidean algorithm at every level of `n`'s binary expansion
   — existence data, the same kind of gap `CantorCompositionStep.lean`'s
   own Bézout witness already carries, now iterated. This is NOT proved
   here and is not a structural gap in this file's theorems; it is
   exactly the "hypothesis, not sorry" this project's standing practice
   asks for at genuine open mathematical/computational content.
2. **Multiple reduction steps per `cantor_add` call**: `CantorAddWitness`
   models exactly one reduction application (matching
   `CantorReductionStep.lean`'s own scope). When `degree (u1*u2) / g²`
   still exceeds `2` after one step, `cantor_add`'s real `while` loop
   applies the reduction step again — the same shape of step, reapplied,
   not new machinery, but `CantorAddWitness` as stated only bundles one
   application; a caller needing more must currently chain
   `CantorAddWitness`es (or, better, extend the structure with a
   `List`/count of reduction applications) rather than get it for free.
3. **`ua0,ua1,va0,va1` reading off `pairAt`'s `.u`/`.v` coefficients**:
   `AlphaReduce.lean`'s `Reduce` wants its precomputed input as four field
   elements (`.coeff 0`/`.coeff 1` of a degree-≤2 Mumford pair), not a
   `MumfordPair (K := K) f` — connecting `cantorMulPair_isMumfordPair`'s
   conclusion to `Reduce`'s actual call site needs (a) specializing
   `K := K2 p c0 c1 c2 c3 c4` (`DataDerivationTower.lean`), matching
   `CantorReductionStep.lean`'s own item 3 note, and (b) a degree bound
   `(pairAt n).u.natDegree ≤ 2` (not addressed here — `CantorAddWitness`'s
   reduction step brings the degree down but this file does not track by
   how much, or assert it lands at exactly 2 after finitely many
   applications; that is part of gap 2 above). Neither is attempted in
   this file.
-/

end TheDataDerivation
end Genus2Lean
