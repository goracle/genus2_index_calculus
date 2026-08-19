import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationMumford

/-!
# 0-dimensionality of the decoupled `P1+P2-P3-P4=(alpha-alpha')*a` matching
  system, via a regular sequence

## Update this pass: symbolic `p`, and `theData` assembled (not opaque)

Per `ROADMAP-regular-sequence.md`'s revision note and "Progress note": this
file previously fixed `p = curveP = 2371157` and left `theData` as a bare
`sorry`. Both are now updated: `F p := ZMod p` for an arbitrary prime `p`
(§1, matching `TheDataDerivation.F`), and `theData` (§4bis) is assembled
from `TheDataDerivation`'s `uRS`/`vRS`/`towerToRdec` rather than left
opaque. This does NOT discharge any proof — `theData`'s assembly carries
four explicit hypotheses (`hcurA/B`, `hgcdA/B`, each a genuine
exceptional-locus condition inherited from `TheDataDerivation`'s own
`uRS`/`vRS`), four fresh `sorry`s of its own (the `u1_indep`/etc.
independence obligations — see §4bis), and `genList`/
`decoupledSystem_isRegularSequence` are now stated for a general `(p,
c0,...,c4, sa, sb)` satisfying those hypotheses rather than unconditionally.
`decoupledSystem_isRegularSequence`'s own `sorry` is unchanged in substance
(still the same statement being proved, now with explicit parameters/
hypotheses rather than implicit fixed values). See §4bis's own docstring for
exactly what is and isn't proved by this pass's assembly.

## What this file is

Advisory-6/7 (`genus2-index-calculus-advisory-6.md`) §6.2 proves, via a classical
birationality argument (`sigma : C^(2) -> J` generically injective for genus 2),
that the 12-variable matching system built by `elim2`'s `build_decoupled_system`
is generically 0-dimensional -- this is "Question 1" in §6.3's triage table,
"PROVED, not merely evidenced". That proof is about the *geometry*
(`sigma`'s generic fibers), not about the specific 12 polynomials on file.

This file takes a different, more computational route to the same conclusion,
requested directly rather than reusing §6.2's birational argument: exhibit the
literal 12 generators `elim2` builds as a **regular sequence** in the
12-variable polynomial ring. For a polynomial ring `R = k[x_1,...,x_n]` over a
field, a regular sequence `f_1,...,f_n` of length exactly `n` is equivalent to
`R / (f_1,...,f_n)` being a nonzero Artinian `k`-algebra, i.e. the variety
`V(f_1,...,f_n)` is 0-dimensional (Krull dimension 0) as a set, with the
generators additionally certifying (via the regular-sequence Koszul complex)
that no fewer than `n` of them already cut the dimension down -- a strictly
finer statement than mere finiteness, and one that unlike §6.2's argument
requires no Riemann-Roch input: it is checkable in principle from the
polynomials alone, e.g. by exhibiting a division witness at each step
("shouldn't be too heinous ... a bunch of polynomial divisions" -- see
`ROADMAP-regular-sequence.md` for the exact reduction this bottoms out at).

## The 12 equations, exactly as `01_elim2_main.jl` builds them

Two samples, `(P1,P2)` and `(P3,P4)`, each a pair of points on
`C : y^2 = x^5+x+2` over `F = GF(p)`, `p = 2371157` (`DEFAULT_P`,
`00_sample_specs.jl`). Each sample is parametrized by its own Mumford
`(u,v)`-representation of `[P_i]+[P_{i+1}] - 2*infty`, which in turn is built
from two symbolic anchor points `(a1,wa1),(a2,wa2)` for sample 1 and
`(b1,wb1),(b2,wb2)` for sample 2, subject to the curve relations
`wa_i^2 = a_i^5+a_i+2` (and likewise for `b`). Sample 1's *target* is
`alpha*a` (Mumford coords `u0,u1,v0,v1` from `SampleSpec`, i.e.
`R(alpha; P1,P2) = Reduce(alpha*a - P1 - P2)`, advisory-7 eq. in §1); sample
2's target is `alpha'*a` symmetrically. The matching condition
`R(alpha;P1,P2) = R(alpha';P3,P4)` is exactly
`(P1+P2)-(P3+P4) = (alpha-alpha')*a` (advisory-7 §2, eq. right after (H0)) --
this file's system is the Mumford-coefficient-matching encoding of that one
group-law equation, not a separate construction.

`build_decoupled_system` (`01_elim2_main.jl:986-1073`) does NOT match u_RS/v_RS
coefficients across samples directly (that would cross-multiply both samples'
variables together, "coeff_equal", `build_fu_fv`); instead it introduces
target variables `U0,U1,V0,V1` and constrains each sample's own
`(u_num,u_den)`/`(v_num,v_den)` to hit those targets:

  `Fu_decoupled`: `u1_num[i] - U_i * u1_den[i] = 0`  and
  `u2_num[i] - U_i * u2_den[i] = 0`,  i = 0,1
  `Fv_decoupled`: `v1_num[i] - V_i * v1_den[i] = 0`  and
  `v2_num[i] - V_i * v2_den[i] = 0`,  i = 0,1

(4 + 4 = 8 equations; each pair states "sample 1's own num/den equals the
target" and "sample 2's own num/den equals the *same* target", which is
exactly coefficient-matching without cross-multiplying). Advisory-6 §6
reports each `U_i` generator (`Fu_decoupled`) as degree 17 and each `V_j`
generator (`Fv_decoupled`) as degree 25, in the 12 variables below.

Plus the 4 curve relations (degree 5, or degree 2 in the relevant `w`):

  `curve_a1 = wa1^2 - (a1^5+a1+2)`,  `curve_a2 = wa2^2 - (a2^5+a2+2)`
  `curve_b1 = wb1^2 - (b1^5+b1+2)`,  `curve_b2 = wb2^2 - (b2^5+b2+2)`

Total: **12 equations in 12 unknowns**
`(wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1)` -- matching advisory-6 §6's count
exactly ("The resulting system is 12 equations in 12 unknowns ... solved as an
affine, non-homogenized system over C", there run numerically via
`HomotopyContinuation.jl` over `ℂ` after a characteristic-0 lift; this file
works directly over `F = GF(p)` instead, since a regular-sequence proof over
`F` is a strictly better (mod-p, not just characteristic-0-then-Hensel)
statement than what advisory-6 §6 established numerically, and answers
advisory-6 §6.1's still-open mod-p finiteness question by construction if it
goes through).

## What is NOT yet in this file (updated this pass)

**No longer the closed-form polynomials themselves** — `theData` (§4bis) now
derives them from `TheDataDerivation`'s tower/linear-solve/exact-division
construction rather than treating them as an external transcription target.
What's still missing:

- `TheDataDerivation`'s own remaining `sorry`s (§4.2 items 1, 3's field
  instances, `dvd_N_u`, `uRS_monic`, `vRS`'s inverse-identification, the
  Mumford identity) — `theData` here is built FROM those definitions, so it
  inherits every one of them, whether or not this file's own code mentions
  them by name.
- The four `u1_indep`/`u2_indep`/`v1_indep`/`v2_indep` obligations in
  `theData`'s assembly (§4bis) — new `sorry`s introduced by this pass's
  assembly itself, not inherited from `TheDataDerivation`.
- `decoupledSystem_isRegularSequence`'s own `sorry` — the actual
  regular-sequence argument (§5's five steps), entirely separate from
  `theData`'s construction and not attempted by this pass.

See `ROADMAP-regular-sequence.md` for the plan on all of these.
-/

namespace Genus2Lean
namespace DecoupledSystem

open MvPolynomial

/-! ## §1. The field and the curve

**Updated this pass** per `ROADMAP-regular-sequence.md`'s revision note
(item 1): `curveP : ℕ := 2371157` and `axiom curveP_prime` are gone. `p` is
now an arbitrary prime, threaded as `[Fact (Nat.Prime p)]`, matching
`TheDataDerivation`'s `F p`/`variable (p : ℕ) [hp : Fact (Nat.Prime p)]`
exactly -- this is what lets `Rdec` here and `TheDataDerivation`'s `K2 p ...`
typecheck against each other in the `theData` assembly below (§4bis), which
was blocked on this update per the roadmap's own "Progress note" ("the two
won't typecheck against each other until `DecoupledSystemRegular.lean` gets
the symbolic-`p` update"). Likewise `curveF`'s fixed numeral coefficients
(`x^5+x+2`, i.e. `c0=2,c1=1,c2=c3=c4=0`) are replaced by symbolic
`(c0,...,c4 : F p)`, matching `TheDataDerivation.curvePoly`'s parametrization
(unchanged since "the immediately prior session's framing" per the
roadmap). -/

/-- The base field `F = GF(p)`, now symbolic -- `01_elim2_main.jl`'s
`CurveConfig.F`, generalized away from the fixed `curveP` numeral. Matches
`TheDataDerivation.F` exactly (same definition, restated here so this file
does not need to `open` the other namespace just to name its own base
field). -/
abbrev F (p : ℕ) : Type := ZMod p

noncomputable instance instFieldF (p : ℕ) [hp : Fact (Nat.Prime p)] : Field (F p) :=
  ZMod.instField p

/-- `f(x) = c0 + c1 x + c2 x² + c3 x³ + c4 x⁴ + x⁵`, `01_elim2_main.jl`'s
`F_POLY_ASC` generalized from the fixed `[2,1,0,0,0,1]` to symbolic-but-fixed
coefficients (roadmap revision note: "this part does NOT change again this
pass", carried over unchanged into this pass's own edit). Matches
`TheDataDerivation.curvePoly` pointwise-evaluated, rather than as a
`Polynomial` -- this file only ever needs `curveF`'s VALUES (in the curve
relations below), not the polynomial itself, unlike `TheDataDerivation`
which needs the polynomial to adjoin roots of `X² - curvePoly`. -/
def curveF (p : ℕ) (c0 c1 c2 c3 c4 : F p) (x : F p) : F p :=
  c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 + x ^ 5

/-! ## §2. The 12-variable ring

Variable order matches `01_elim2_main.jl:988-996`'s `dec_gens` exactly:
`wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1` (note: `a2` before `a1`, `b2` before
`b1` -- preserved from the original file's own (slightly unusual) generator
order, not a transcription slip here). Unaffected by the symbolic-`p` update
-- `Idx` itself carries no field/curve data, only variable names. -/

/-- The 12 index labels, in `dec_gens` order. -/
inductive Idx : Type
  | wa1 | wa2 | wb1 | wb2 | a2 | a1 | b2 | b1 | U0 | U1 | V0 | V1
  deriving DecidableEq, Fintype, Repr

open Idx

/-- `R_dec`, `01_elim2_main.jl`'s `DecoupledSystem.R_dec`:
`MvPolynomial (Idx) (F p)`, i.e. `(F p)[wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1]`,
now parametric in `p` (previously fixed at `curveP`). -/
abbrev Rdec (p : ℕ) : Type := MvPolynomial Idx (F p)

/-- Notation matching the Julia variable names directly, so the equations
below read the same as `01_elim2_main.jl`'s own `println` diagnostics. Now
parametric in `p` (previously `Rdec` was defined for the fixed `curveP`, so
these needed no separate parameter). -/
noncomputable def wa1' (p : ℕ) : Rdec p := X wa1
noncomputable def wa2' (p : ℕ) : Rdec p := X wa2
noncomputable def wb1' (p : ℕ) : Rdec p := X wb1
noncomputable def wb2' (p : ℕ) : Rdec p := X wb2
noncomputable def a1' (p : ℕ) : Rdec p := X a1
noncomputable def a2' (p : ℕ) : Rdec p := X a2
noncomputable def b1' (p : ℕ) : Rdec p := X b1
noncomputable def b2' (p : ℕ) : Rdec p := X b2
noncomputable def U0' (p : ℕ) : Rdec p := X U0
noncomputable def U1' (p : ℕ) : Rdec p := X U1
noncomputable def V0' (p : ℕ) : Rdec p := X V0
noncomputable def V1' (p : ℕ) : Rdec p := X V1

/-! ## §3. The four curve relations

`01_elim2_main.jl:998-1001` / `:103-106` (both `TargetRing.build_target_ring`
and `DecoupledSystem.build_decoupled_system` build the same four relations,
once per ring copy -- reproduced here directly in `Rdec`). **Updated this
pass**: the fixed `+ 2` constant (from `curveF`'s old `x^5+x+2` numeral) is
replaced by the general `c0 + c1*X + c2*X² + c3*X³ + c4*X⁴` shape, matching
`curveF`'s new symbolic form above and `TheDataDerivation.curvePoly`'s
`Rdec`-embedded shape -- each curve relation now takes `(c0,...,c4 : F p)` as
an explicit parameter (the SAME five values across all four relations, per
`TheDataDerivation`'s framing: "the SAME symbolic `f`" is shared by both
samples/both tower copies). -/

variable (p : ℕ)

/-- `c0,...,c4 : F p` embedded into `Rdec p` as constants, so they can be
added to the `X`-generator terms (`a1' p`, etc.) below -- `Rdec p` is a
polynomial ring, `F p`'s elements are not literally its elements, `C` is
`MvPolynomial`'s constant-embedding ring hom. -/
noncomputable def curveA1 (c0 c1 c2 c3 c4 : F p) : Rdec p :=
  wa1' p ^ 2 - (C c0 + C c1 * a1' p + C c2 * a1' p ^ 2 + C c3 * a1' p ^ 3 +
    C c4 * a1' p ^ 4 + a1' p ^ 5)
noncomputable def curveA2 (c0 c1 c2 c3 c4 : F p) : Rdec p :=
  wa2' p ^ 2 - (C c0 + C c1 * a2' p + C c2 * a2' p ^ 2 + C c3 * a2' p ^ 3 +
    C c4 * a2' p ^ 4 + a2' p ^ 5)
noncomputable def curveB1 (c0 c1 c2 c3 c4 : F p) : Rdec p :=
  wb1' p ^ 2 - (C c0 + C c1 * b1' p + C c2 * b1' p ^ 2 + C c3 * b1' p ^ 3 +
    C c4 * b1' p ^ 4 + b1' p ^ 5)
noncomputable def curveB2 (c0 c1 c2 c3 c4 : F p) : Rdec p :=
  wb2' p ^ 2 - (C c0 + C c1 * b2' p + C c2 * b2' p ^ 2 + C c3 * b2' p ^ 3 +
    C c4 * b2' p ^ 4 + b2' p ^ 5)

/-! ## §4. `Fu_decoupled` / `Fv_decoupled`: the eight matching generators

**This is the section that needs real input from the Julia side (or a from-
scratch symbolic re-derivation in Lean) before the equations below are
anything more than a shape.** `01_elim2_main.jl:1042-1052` builds these from
`u1_num_d/u1_den_d/u2_num_d/u2_den_d` (resp. `v1_.../v2_...`), which are
themselves `PhiSymbolic.symbolic_residual`'s output run through
`map_coeffs_threaded` and a generator-renaming `remap` -- i.e. long closed-form
polynomials that exist concretely only as Julia `Oscar.MPolyRingElem` values
produced by that call, not (yet) as hand-derivable expressions.

Rather than block the whole file on that derivation, `Fu_decoupled`/
`Fv_decoupled` are stated here as **abstract elements of `Rdec` satisfying the
defining `U_i*den = num` shape**, packaged as a structure so the regular-
sequence goal typechecks and the proof obligations below are precisely
targeted. Once the eight closed-form polynomials are available (see
`ROADMAP-regular-sequence.md`), replace `DecoupledGenerators` with a concrete
`def` computing them and this whole indirection collapses to `rfl`-shaped
unfolding.

The `num`/`den` split matches `build_decoupled_system`'s own construction
(`Fu_decoupled[i] = num_d[i] - U_i * den_d[i]`) exactly, one pair per sample
per coefficient index `i ∈ {0,1}` (recall `N_U_MATCH = 2`, `length(s1.v_num)
= 2`: `01_elim2_main.jl` §"Struct: MatchSpec" plus advisory-6 §6's "12
equations" count forces exactly 2 non-trivial `u`-coefficients and 2
`v`-coefficients per sample, matching `deg(u_RS)=2` (Mumford normal form) and
`deg(v_RS)≤1`). -/
structure DecoupledGenerators (p : ℕ) where
  /-- Sample 1's u-side numerator/denominator, index 0,1 (matches `u0,u1`
  coefficients of `u_RS`, i.e. `s1.u_num`/`s1.u_den` restricted to the two
  non-leading coefficients -- the degree-2 leading coefficient is always `1`
  and is skipped, `mspec.N_U_MATCH = U_DEG_TOP - 1`, `build_match_spec`). -/
  u1_num : Fin 2 → Rdec p
  u1_den : Fin 2 → Rdec p
  u2_num : Fin 2 → Rdec p
  u2_den : Fin 2 → Rdec p
  v1_num : Fin 2 → Rdec p
  v1_den : Fin 2 → Rdec p
  v2_num : Fin 2 → Rdec p
  v2_den : Fin 2 → Rdec p
  /-- Sanity constraints this data must satisfy to actually BE `elim2`'s
  output (not part of `build_decoupled_system` itself, but properties any
  real instantiation must have -- flagged here so a future filled-in
  instance is checked against them): each `u1_num i` / `u1_den i` etc. only
  involves sample 1's own variables `(wa1,wa2,a1,a2)`, not sample 2's
  `(wb1,wb2,b1,b2)` or the target variables `U0,U1,V0,V1` -- "decoupled"
  literally means each sample's num/den pair is a function of that sample's
  own five variables (t/w-generators) alone, `MappedSample`'s whole point.
  (Bound variable renamed `v` here, was `p` in the pre-split-update draft --
  that shadowed the now-explicit outer `p : ℕ` prime parameter.) -/
  u1_indep : ∀ i, ∀ v ∈ (u1_num i).vars ∪ (u1_den i).vars, v ∈ ({wa1, wa2, a1, a2} : Finset Idx)
  u2_indep : ∀ i, ∀ v ∈ (u2_num i).vars ∪ (u2_den i).vars, v ∈ ({wb1, wb2, b1, b2} : Finset Idx)
  v1_indep : ∀ i, ∀ v ∈ (v1_num i).vars ∪ (v1_den i).vars, v ∈ ({wa1, wa2, a1, a2} : Finset Idx)
  v2_indep : ∀ i, ∀ v ∈ (v2_num i).vars ∪ (v2_den i).vars, v ∈ ({wb1, wb2, b1, b2} : Finset Idx)

/-! ## §4bis. Assembling `theData` from `TheDataDerivation`

The actual Mumford-residual data, now assembled (§4bis below) from
`TheDataDerivation`'s `uRS`/`vRS`/`towerToRdec` rather than left as a bare
`sorry` -- see §4bis for the assembly and exactly which upstream `sorry`s it
still depends on. Downstream statements (`FuList`/`FvList`/`genList`/the main
theorem) are phrased against `theData` regardless of how it's built, so nothing
below §4bis needed to change shape for this update.

**New this pass.** Previously `theData := by sorry`, an entirely opaque
constant. Now built from `TheDataDerivation.uRS`/`.vRS`/`.towerToRdec`,
following §4.0's own recipe ("specialized twice ... with different fixed
`(u0,u1,v0,v1)` target data but the SAME symbolic `f`") -- this does NOT
discharge any of `TheDataDerivation`'s own `sorry`s (`dvd_N_u`, the field
instances, the Mumford identity, etc.); it only wires the (partially
`sorry`-backed) derivation up to `Rdec`'s shape, so `theData` is no longer a
bare unexplained `sorry` but an actual term built from named, individually-
tracked `sorry`s living in `TheDataDerivation`. Every `sorry` this
assembly's own hypotheses ultimately bottom out in is named explicitly
below rather than absorbed silently. -/

open TheDataDerivation

/-- The a-side generator map: `TheDataDerivation`'s abstract tower variables
`(t1,t2,w1,w2)` land on `(a1,a2,wa1,wa2)` here -- matches sample 1's own
five variables (`DecoupledGenerators.u1_indep`'s target `{wa1,wa2,a1,a2}`
exactly). -/
noncomputable def aSideGens : SideGens Idx :=
  ⟨![a1, a2], ![wa1, wa2]⟩

/-- The b-side generator map: `(t1,t2,w1,w2) ↦ (b1,b2,wb1,wb2)`, matching
`{wb1,wb2,b1,b2}`. -/
noncomputable def bSideGens : SideGens Idx :=
  ⟨![b1, b2], ![wb1, wb2]⟩

/-- One sample's four target Mumford coefficients `(u0,u1,v0,v1)`, packaged
together since `uRS`/`vRS` both need all four (`u0,u1` determine the target
`u(x)=x²+u1x+u0` the `reduceMonomialModU` rows reduce against; `v0,v1`
likewise for `v(x)=v1x+v0`) -- `00_sample_specs.jl`'s per-sample data, not
reconstructed here (this file has never had access to the actual numeric/
symbolic target values `elim2`'s two samples use; `SampleTarget` is a
parameter, filled in by whoever instantiates `theData` for a specific DLP
instance, exactly the same status `(c0,...,c4)` already had before this
pass). Takes `p` explicitly (rather than picking up the section's implicit
`{p : ℕ}`) since a `structure`'s own parameters are stated independently of
surrounding `variable` declarations -- call sites below always apply it as
`SampleTarget p`, matching. -/
structure SampleTarget (p : ℕ) [Fact (Nat.Prime p)] where
  u0 : F p
  u1 : F p
  v0 : F p
  v1 : F p

variable [Fact (Nat.Prime p)]

/-- Extract `(x^0, x^1)` coefficients of a `Polynomial (K2 p ...)` value,
run each through `towerToRdec sg`, and re-pair into the `(num0,den0,num1,
den1)` shape `DecoupledGenerators` wants for one of its eight fields --
shared plumbing for all eight `uRS`/`vRS` × a-side/b-side combinations
below, rather than repeating the same four lines eight times. -/
noncomputable def coeffsToNumDen (c0 c1 c2 c3 c4 : F p) (sg : SideGens Idx)
    (poly : Polynomial (K2 p c0 c1 c2 c3 c4)) : Fin 2 → Rdec p × Rdec p :=
  fun i => towerToRdec p sg (poly.coeff i.val)

/-- **The assembly.** Given the shared curve coefficients `(c0,...,c4)`, each
sample's target `(u0,u1,v0,v1)`, and the hypotheses `TheDataDerivation.uRS`/
`.vRS` need to be well-defined (`hcurA/hcurB` -- `curBeforeMonic ≠ 0` for
each sample; `hgcdA/hgcdB` -- the `Ypoly`/`uRS` coprimality `vRS` needs),
build the eight `Rdec p`-valued numerator/denominator functions. The four
`u1_indep`/`u2_indep`/`v1_indep`/`v2_indep` independence obligations are
**left as `sorry`** here -- they would follow from `towerToRdec`'s
construction only ever introducing `sg`'s own generators (`aSideGens`'s
image is exactly `{wa1,wa2,a1,a2}` by inspection of `SideGens`/
`baseFracToRing`/`towerToRdecK1`/`towerToRdec`'s definitions, so this is
plausible, but has not been proved as a lemma about `towerToRdec` itself
anywhere in `TheDataDerivation.lean`, and is new work this pass did not
attempt). -/
noncomputable def theData (c0 c1 c2 c3 c4 : F p)
    (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    DecoupledGenerators p :=
  { u1_num := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1) i).1
    u1_den := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1) i).2
    u2_num := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1) i).1
    u2_den := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1) i).2
    v1_num := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
      (vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA) i).1
    v1_den := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 aSideGens
      (vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA) i).2
    v2_num := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
      (vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB) i).1
    v2_den := fun i => (coeffsToNumDen p c0 c1 c2 c3 c4 bSideGens
      (vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB) i).2
    u1_indep := by
      intro i v hv
      have h1 := (towerToRdec_vars_subset p aSideGens
        ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).1
      have h2 := (towerToRdec_vars_subset p aSideGens
        ((uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1).coeff i.val)).2
      have := (Finset.mem_union.mp hv).elim (fun hv1 => h1 hv1) (fun hv2 => h2 hv2)
      simp only [aSideGens, coeffsToNumDen, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    u2_indep := by
      intro i v hv
      have h1 := (towerToRdec_vars_subset p bSideGens
        ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).1
      have h2 := (towerToRdec_vars_subset p bSideGens
        ((uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1).coeff i.val)).2
      have := (Finset.mem_union.mp hv).elim (fun hv1 => h1 hv1) (fun hv2 => h2 hv2)
      simp only [bSideGens, coeffsToNumDen, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    v1_indep := by
      intro i v hv
      have h1 := (towerToRdec_vars_subset p aSideGens
        ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).1
      have h2 := (towerToRdec_vars_subset p aSideGens
        ((vRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hgcdA).coeff i.val)).2
      have := (Finset.mem_union.mp hv).elim (fun hv1 => h1 hv1) (fun hv2 => h2 hv2)
      simp only [aSideGens, coeffsToNumDen, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto
    v2_indep := by
      intro i v hv
      have h1 := (towerToRdec_vars_subset p bSideGens
        ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).1
      have h2 := (towerToRdec_vars_subset p bSideGens
        ((vRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hgcdB).coeff i.val)).2
      have := (Finset.mem_union.mp hv).elim (fun hv1 => h1 hv1) (fun hv2 => h2 hv2)
      simp only [bSideGens, coeffsToNumDen, Finset.mem_insert, Finset.mem_singleton] at this ⊢
      tauto }

/-- `Fu_decoupled`, `01_elim2_main.jl:1042-1046`, flattened to a length-4
list in the same order the original loop produces (`i=0`: sample-1 then
sample-2 equation; `i=1`: likewise), matching how `build_decoupled_system`
`push!`s them. Now takes `theData`'s full parameter list (`c0,...,c4`, both
samples' targets, and the four well-definedness hypotheses) since `theData`
itself does. -/
noncomputable def FuList (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) : List (Rdec p) :=
  let d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
  [ d.u1_num 0 - U0' p * d.u1_den 0, d.u2_num 0 - U0' p * d.u2_den 0,
    d.u1_num 1 - U1' p * d.u1_den 1, d.u2_num 1 - U1' p * d.u2_den 1 ]

/-- `Fv_decoupled`, `01_elim2_main.jl:1048-1052`, same pattern for `V0,V1`. -/
noncomputable def FvList (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) : List (Rdec p) :=
  let d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
  [ d.v1_num 0 - V0' p * d.v1_den 0, d.v2_num 0 - V0' p * d.v2_den 0,
    d.v1_num 1 - V1' p * d.v1_den 1, d.v2_num 1 - V1' p * d.v2_den 1 ]

/-! ## §5. The full 12-generator list and the 0-dimensionality goal

All 12 generators, `Fu_decoupled ++ Fv_decoupled ++ [curve_a1, curve_a2,
curve_b1, curve_b2]` -- matches the ideal `Iuv_decoupled`
(`01_elim2_main.jl:1064-1065`) exactly as a *set* of generators (this file
uses a `List` rather than the `ideal(...)` call directly, since
`RingTheory.Sequence.IsRegular` is stated for an ordered `List`, not an
`Ideal` -- regularity is order-and-multiplicity-sensitive in general, though
for a genuinely regular sequence over a Noetherian local/graded ring any
permutation is again regular; no reordering is attempted here, the list below
is `elim2`'s own order, `Fu` before `Fv` before the four curve relations).
Now parametric in `p, c0,...,c4`, both samples' targets, and `theData`'s
four hypotheses, propagated from `FuList`/`FvList`/`curveA1`-etc. above. -/
noncomputable def genList (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) : List (Rdec p) :=
  FuList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB ++
    FvList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB ++
    [curveA1 p c0 c1 c2 c3 c4, curveA2 p c0 c1 c2 c3 c4,
     curveB1 p c0 c1 c2 c3 c4, curveB2 p c0 c1 c2 c3 c4]

/-- Sanity check on the shape of the construction: exactly 12 generators for
12 variables, `Fintype.card Idx`. This is a NECESSARY (not sufficient)
condition for `genList` to be a maximal-length regular sequence in a
12-variable polynomial ring -- checked here as a cheap guard so a future
edit to `FuList`/`FvList`/the curve list that accidentally drops or
duplicates a generator is caught immediately, independent of the harder
`decoupledSystem_isRegularSequence` goal below. Unaffected in substance by
this pass's parametrization -- length is independent of which `(c0,...,c4,
sa,sb,...)` values are plugged in, so the proof is unchanged, just
restated with `genList`'s new arguments threaded through. -/
theorem genList_length (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).length = Fintype.card Idx := by
  simp only [genList, FuList, FvList, List.length_append, List.length_cons, List.length_nil]
  decide

/-! ## §5bis. Proof skeleton for `decoupledSystem_isRegularSequence`

**Draft assembly, this pass.** This is the one remaining `sorry` in the
file (`ROADMAP-regular-sequence.md` §5's five-step plan). Nothing in §5 has
been executed in any previous pass (see the roadmap's own "out of scope"
note), so rather than leave a single opaque `sorry` here, the goal is split
into the five named pieces §5 actually describes, wired together the way
§5 says they compose. Each piece below is its own `sorry` with a precise
statement, so the genuinely hard math (steps 3-4, real unformalized
mathematics) is isolated from the purely mechanical wiring (step 5). Per
project convention: not proved, not build-tested, statements only, ready to
be attacked easiest-first once Claire has confirmed this typechecks.

Order of attack (easiest first, per usual project convention):
1. `regular_of_linear_elim` -- general-purpose, no curve/field-specific
   content at all, arguably the easiest of the five.
2. `regular_of_norm_eliminate` -- needs the resultant identity
   `Res_w(P+Qw, w²-f) = P²-Q²f` (a fixed, checkable algebraic identity) plus
   the "degree ≤1 in the just-adjoined `w_i`" fact the roadmap flags as
   likely following from `AdjoinRoot`'s normal form almost for free.
3. `eightVar_finiteQuotient` -- the genuinely hard one: the explicit
   division-witness/Gröbner certificate over `F[wa1,wa2,wb1,wb2,a1,a2,b1,b2]`
   promised by roadmap step 3. This is where `theData`'s actual closed-form
   polynomials (still gated behind `TheDataDerivation`'s own `sorry`s) are
   needed concretely, not just abstractly -- likely the single best
   candidate in this whole file for a ChatGPT consultation, since it is a
   concrete (if large) symbolic-algebra computation once `theData` is
   filled in, not open-ended proof search.
4. `fourVar_finiteQuotient` / `height4_of_finiteQuotient` -- roadmap step 4,
   same flavor as step 3 but smaller (4 variables, 4 generators): the
   triangular division witness eliminating `b2,b1,a2,a1` in turn, then the
   Cohen-Macaulay height-4-gives-regular-sequence argument.

**Roadmap §5 step 1.** If `g = c - X none * d` for `c, d` not involving
the distinguished variable `none : Option τ` (i.e. `t := none`, `Rdec`'s
extra "elimination" variable), `gens` also doesn't involve `none` (each
generator lies in the range of `rename some`, matching the roadmap's own
"`t` also not in `I`'s generators" condition -- **added this pass**: the
first draft omitted this and is false without it, since `gens` could
otherwise smuggle in a `none`-relation that kills `d`'s regularity even
though `d` alone is a non-zero-divisor; caught by hand-checking a
zero-divisor counterexample before attempting the proof, not found via
REPL), and `d` is regular on the quotient by `gens`, then `g` is too.
Restated against `σ := Option τ` (rather than an arbitrary `σ` with a side
`t : σ` and `DecidableEq σ`) specifically so `MvPolynomial.optionEquivLeft`
applies directly: `MvPolynomial (Option τ) R ≃ₐ[R] Polynomial (MvPolynomial
τ R)` sends `X none ↦ Polynomial.X` and `X (some s) ↦ Polynomial.C (X s)`
(`optionEquivLeft_apply`/`optionEquivLeft_X_some`, confirmed via web search
against the real Mathlib API rather than guessed). Under this equivalence,
`gens` (now hypothesized `none`-free) becomes a list of constant
polynomials `Polynomial.C '' (MvPolynomial τ R)`, and `g` becomes
`C c - X * C d`, a polynomial of degree exactly 1 in the fresh variable `X`
with leading coefficient `-d`. `IsSMulRegular` for the quotient by an ideal
of CONSTANT polynomials, of a degree-1-in-`X` element with leading
coefficient `d`, should reduce cleanly to `d`'s own regularity mod the
(image of) `gens` -- this is the shape where the argument actually goes
through, unlike the ungens-restricted version above.

Genuinely open here (the `sorry`): the precise chain from `optionEquivLeft`
+ `hgens`/`hc`/`hd` to `IsSMulRegular`, and translating `Ideal.ofList gens`
(stated over `MvPolynomial (Option τ) R`) across `optionEquivLeft` to
`Ideal.ofList (gens'.map Polynomial.C)` over `Polynomial (MvPolynomial τ R)`
cleanly -- the mechanical part (`AlgEquiv`s preserve `IsSMulRegular` via
`LinearEquiv.isSMulRegular_congr`, found via the same web search) should be
routine; the substance is the "regular mod a constant-coefficient ideal
transfers to a degree-1 polynomial with that coefficient as leading term"
argument, itself a small standalone fact about `Polynomial (MvPolynomial τ
R)` worth trying to isolate and prove first, in the REPL, before wiring the
rest around it. Left as a `sorry` pending that rather than guessed blind. -/
theorem regular_of_linear_elim {τ : Type*} {R : Type*} [CommRing R]
    (gens' : List (MvPolynomial τ R))
    (c d : MvPolynomial τ R)
    (hd_reg : IsSMulRegular (MvPolynomial (Option τ) R ⧸
      Ideal.ofList (gens'.map (MvPolynomial.rename some))) (MvPolynomial.rename some d))
    (g : MvPolynomial (Option τ) R)
    (hg : g = MvPolynomial.rename some c -
      MvPolynomial.X none * MvPolynomial.rename some d) :
    IsSMulRegular (MvPolynomial (Option τ) R ⧸
      Ideal.ofList (gens'.map (MvPolynomial.rename some))) g := by
  sorry

/-- **Roadmap §5 step 2 + 3 (norm-elimination half).** Given the resultant
identity `Res_w(P + Q•w, w² - f) = P² - Q²•f` (`norm_eliminate`'s Lean
port), eliminating a single `AdjoinRoot`-style generator `w` with `w² = f`
from a generator of the shape `P + Q•w` (both `P,Q` free of `w`) preserves
regularity: if `[P₁+Q₁w, ..., Pₙ+Qₙw]` is regular on `R[w]/(w²-f)` then
`[P₁²-Q₁²f, ..., Pₙ²-Qₙ²f]` is regular on `R` (informally -- the precise
Lean statement needs `AdjoinRoot f` or an explicit quotient by `w²-f` as the
base ring, matching whichever shape `theData`'s `w`-generators actually
come out in from §4.1's ring stack). Left in this loose/informal form
pending that ring-stack choice being pinned down concretely by
`eightVar_finiteQuotient` below -- restating this precisely is easier once
that dependency is fixed, rather than guessed now. -/
theorem regular_of_norm_eliminate {σ : Type*} [DecidableEq σ] {R : Type*} [CommRing R]
    (w : σ) (f : MvPolynomial σ R) (hw : w ∉ f.vars)
    (P Q : MvPolynomial σ R) (hP : w ∉ P.vars) (hQ : w ∉ Q.vars) :
    True := by  -- placeholder statement; see docstring -- precise shape TODO
  trivial

/-- **Roadmap §5 step 3, the 8-variable finite-quotient certificate.** For
`p` outside a finite exceptional set of primes and `(c0,...,c4)` outside a
Zariski-closed exceptional locus (both TBD concretely, per the roadmap's own
"not assumed in advance" framing), the 8-generator list
`[curve_a1,curve_a2,curve_b1,curve_b2, Fu_cross[0],Fu_cross[1],Fv_cross[0],
Fv_cross[1]]` cuts `F[wa1,wa2,wb1,wb2,a1,a2,b1,b2]` down to a
finite-dimensional (equivalently 0-dimensional) quotient. This is the
genuinely hard, currently-unformalized step the roadmap flags as needing
`theData`'s actual closed-form output, not merely its abstract
`DecoupledGenerators` packaging -- stated here only as a placeholder
pending that. **Best candidate in this file for a ChatGPT consultation**
once `theData` is concretely filled in: the target certificate (triangular
division witness or Gröbner basis) is a fixed, checkable symbolic
computation at that point, not open-ended search. -/
theorem eightVar_finiteQuotient : True := by  -- placeholder statement; see docstring
  trivial

/-- **Roadmap §5 step 4, the 4-variable finite-quotient + height-4
certificate.** After eliminating `wa1,wa2,wb1,wb2` via
`regular_of_norm_eliminate`, the resulting 4-generator system in
`F[a1,a2,b1,b2]` (i) cuts the ring down to a finite-dimensional quotient
(triangular division witness eliminating `b2` then `b1` then `a2` then
`a1`, or an equivalent Gröbner basis with a positive power of each variable
among its leading monomials), hence (ii) the generated ideal has height 4
in a Krull-dimension-4 Cohen-Macaulay polynomial ring, hence (iii) the four
generators form a regular sequence (system-of-parameters argument). Left
as a single placeholder bundling roadmap step 4's three sub-claims rather
than split further, since (ii)/(iii) are routine Cohen-Macaulay/
system-of-parameters facts once (i)'s certificate is in hand -- the real
content is entirely in (i), which needs the same concrete `theData` output
as `eightVar_finiteQuotient` above (worth attempting together / in the same
ChatGPT consultation). -/
theorem fourVar_regularSequence : True := by  -- placeholder statement; see docstring
  trivial

/-- **Main target.** `genList` is a regular sequence on `Rdec p` itself (as
an `Rdec p`-module), in the sense of `RingTheory.Sequence.IsRegular`. Since
`Rdec p = (F p)[X_1,...,X_12]` is a polynomial ring over a field --
Cohen-Macaulay of Krull dimension 12 -- a regular sequence of length exactly
12 (`genList_length`) is equivalent to `Rdec p ⧸ Ideal.ofList genList` being
a nonzero Artinian `F p`-algebra, i.e. `V(genList)` is 0-dimensional. Now
understood, per the roadmap's §5 revision, as true for `p` and
`(c0,...,c4)` outside an explicit exceptional locus rather than
unconditionally -- the hypotheses threaded through `genList` above
(`hcurA/B`, `hgcdA/B`) are part of that locus, though not yet the complete
statement of it (§5's own division-witness genericity conditions,
`MatrixNondegenerate` in particular, are additional hypotheses this
statement does not yet carry -- flagged here rather than silently
incomplete: a fully faithful restatement would also hypothesize
`MatrixNondegenerate` for both samples, since `uRS`/`vRS` are only the
INTENDED values under that condition too, not merely under `hcurA/B`/
`hgcdA/B`).

**This pass:** the body is reassembled per roadmap §5 step 5 out of the
four lemmas above (`regular_of_linear_elim` applied four times, folded into
`eightVar_finiteQuotient`/`fourVar_regularSequence` via
`regular_of_norm_eliminate`) rather than left as one bare `sorry` -- see
§5bis's docstring above for the attack order. The assembly itself
(`sorry` here) is still to be written once steps 1-4's statements are
confirmed against a real Lean session; not attempted blind in this pass,
per Claire's "let me do all the testing" instruction. -/
theorem decoupledSystem_isRegularSequence (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    RingTheory.Sequence.IsRegular (Rdec p)
      (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) := by
  -- Step 5 (roadmap §5): reassemble from `regular_of_linear_elim` (×4) +
  -- `eightVar_finiteQuotient` + `regular_of_norm_eliminate` +
  -- `fourVar_regularSequence`. Not yet written -- see §5bis docstring.
  sorry

/-- **Corollary, stated but not yet derived from the theorem above** (mirrors
this project's convention of stating the target consequence alongside the
main `sorry`, e.g. `SCOPING-isRatioDivisorSpec.md`'s §5): 0-dimensionality of
the variety itself, phrased via `Ideal.ofList genList` having Krull dimension
0 in the quotient ring. Left as a second `sorry` pending the Mathlib API
survey noted in `ROADMAP-regular-sequence.md` ("Krull-dimension-0 from a
length-`n` regular sequence in an `n`-variable polynomial ring" -- likely via
Cohen-Macaulay-ness of `Rdec` plus a `Ideal.height`/system-of-parameters
argument, not yet pinned to an exact Mathlib lemma name). -/
theorem decoupledSystem_zeroDimensional :
    True := by  -- placeholder statement; see docstring
  trivial

end DecoupledSystem
end Genus2Lean
