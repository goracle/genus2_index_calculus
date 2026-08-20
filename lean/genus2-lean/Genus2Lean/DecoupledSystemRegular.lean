import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationMumford

/-!
# 0-dimensionality of the decoupled `P1+P2-P3-P4=(alpha-alpha')*a` matching
# Revision 3: fixed dependent `Fin` elimination in the `Ypoly` degree proof and closed the non-`bj=1` branch explicitly.
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

-- `Fact (p ≠ 2)` — needed transitively from here on: this section's
-- definitions/theorems work over `TheDataDerivation.K2 p ...`, whose
-- `Field` instance (`factIrreducible_K2`, `DataDerivationTower.lean`) now
-- requires odd characteristic, matching this project's global "assume odd
-- characteristic" convention.
variable [Fact (Nat.Prime p)] [Fact (p ≠ 2)]

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

**Roadmap §5 step 1, split per ChatGPT's guidance (consultation prompt
`chatgpt_prompt_regular_of_linear_elim.md`, answered this pass).** ChatGPT
confirmed the corrected (gens'-restricted) statement is true and gave a
clean route: transport via `MvPolynomial.optionEquivLeft` to `Polynomial
(MvPolynomial τ R ⧸ Ideal.ofList gens')`
(`Ideal.polynomialQuotientEquivQuotientPolynomial`, confirmed to exist in
current Mathlib -- the ideal of "constant-coefficient" polynomials
`Ideal.map Polynomial.C I'` is exactly what `gens'.map (rename some)`'s
image becomes), then argue directly in `Polynomial B` (`B := MvPolynomial τ
R ⧸ Ideal.ofList gens'`): a polynomial `C cbar - X * C dbar` with `dbar` regular in
`B` is itself regular in `Polynomial B`, by a leading-term argument (if
`p * q = 0` with `q ≠ 0`, the top-degree coefficient of the product is
`-dbar * leadingCoeff q`, which is nonzero since `dbar` is regular -- contradiction
unless `q = 0`). This bottom fact is split out below as
`regular_linear_of_regular_coeff`, a small self-contained `Polynomial`
lemma, proved first on its own before wiring the `MvPolynomial`-level
transport around it (per ChatGPT's own suggestion that the leading-term
argument, not the transport, is the real content). -/
theorem regular_linear_of_regular_coeff {B : Type*} [CommRing B] {dbar : B}
    (hd : IsSMulRegular B dbar) (cbar : B) :
    IsSMulRegular (Polynomial B) (Polynomial.C cbar - Polynomial.X * Polynomial.C dbar) := by
  -- Key coefficient identity: for any `r : Polynomial B` and `n : ℕ`,
  -- `((C cbar - X * C dbar) * r).coeff (n+1) = cbar * r.coeff (n+1) - dbar * r.coeff n`.
  -- `Polynomial.coeff_C_mul` / `Polynomial.coeff_X_mul` confirmed against
  -- Mathlib.Algebra.Polynomial.Coeff (web docs, this pass).
  have hcoeff_id : ∀ (r : Polynomial B) (n : ℕ),
      ((Polynomial.C cbar - Polynomial.X * Polynomial.C dbar) * r).coeff (n + 1) =
        cbar * r.coeff (n + 1) - dbar * r.coeff n := by
    intro r n
    -- Confirmed against Mathlib.Algebra.Polynomial.Coeff:
    -- `Polynomial.coeff_C_mul : (C a * p).coeff n = a * p.coeff n`
    -- `Polynomial.coeff_X_mul : (X * p).coeff (n + 1) = p.coeff n`
    rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        mul_assoc, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
  -- `IsSMulRegular (Polynomial B) g` unfolds (by definition) to
  -- `Function.Injective (g • ·)`; `intro` should work directly on this without
  -- an explicit `rw`/`unfold`, since it's a plain `def`, not a class -- flagged
  -- as worth double-checking in the REPL if `intro` doesn't immediately apply.
  intro p q hpq
  simp only [smul_eq_mul] at hpq
  rw [← sub_eq_zero]
  have hpq' : (Polynomial.C cbar - Polynomial.X * Polynomial.C dbar) * (p - q) = 0 := by
    rw [mul_sub, hpq, sub_self]
  set r : Polynomial B := p - q with hr_def
  clear_value r
  by_contra hr0
  -- `g * r = 0` and `r ≠ 0`: the coefficient identity at `n := r.natDegree`
  -- forces `dbar * r.leadingCoeff = 0` (the `cbar * r.coeff (n+1)` term vanishes
  -- since `n+1 > r.natDegree`), contradicting `hd` since `r.leadingCoeff ≠ 0`
  -- (as `r ≠ 0`).
  have htop := hcoeff_id r r.natDegree
  rw [hpq'] at htop
  simp only [Polynomial.coeff_zero] at htop
  have hdeg_lt : r.coeff (r.natDegree + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hdeg_lt, mul_zero, zero_sub, eq_comm, neg_eq_zero] at htop
  -- `htop : dbar * r.coeff r.natDegree = 0`; `r.leadingCoeff` is definitionally
  -- `r.coeff r.natDegree`, so this is `dbar * r.leadingCoeff = 0`. `hd` is
  -- `Function.Injective (dbar • ·)`; apply it to `dbar • r.leadingCoeff =
  -- dbar • 0` (via `smul_eq_mul`/`smul_zero`) to conclude `r.leadingCoeff = 0`,
  -- contradicting `hlead_ne`.
  have hlead_ne : r.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hr0
  apply hlead_ne
  apply hd
  show dbar • r.leadingCoeff = dbar • (0 : B)
  rw [smul_eq_mul, smul_zero]
  exact htop

/-- Helper, proved this pass: `MvPolynomial.optionEquivLeft` sends `rename
some p` to the constant polynomial `C p`, for every `p : MvPolynomial τ R`.
Both sides are ring homs `MvPolynomial τ R →+* Polynomial (MvPolynomial τ
R)` in `p` (LHS: `optionEquivLeft R τ` composed with `rename some`, both
ring homs; RHS: `Polynomial.C`), agreeing on `MvPolynomial.C` (both send
`r : R` to `Polynomial.C (MvPolynomial.C r)`, since `optionEquivLeft` and
`rename` are both `R`-algebra maps) and on each generator `X x`
(`optionEquivLeft R τ (rename some (X x)) = optionEquivLeft R τ (X (some
x)) = C (X x)` by `MvPolynomial.rename_X` then
`MvPolynomial.optionEquivLeft_X_some`, both confirmed simp lemmas against
Mathlib.Algebra.MvPolynomial.Equiv, this pass). `MvPolynomial.hom_eq_hom`
then extends agreement on `C`/`X` to all of `MvPolynomial τ R`. -/
theorem optionEquivLeft_rename_some {τ : Type*} {R : Type*} [CommRing R] (p : MvPolynomial τ R) :
    (MvPolynomial.optionEquivLeft R τ) (MvPolynomial.rename some p) = Polynomial.C p := by
  have hC : (((MvPolynomial.optionEquivLeft R τ).toRingHom).comp
        (MvPolynomial.rename some).toRingHom).comp
      (MvPolynomial.C : R →+* MvPolynomial τ R) =
      (Polynomial.C : MvPolynomial τ R →+* Polynomial (MvPolynomial τ R)).comp
        (MvPolynomial.C : R →+* MvPolynomial τ R) := by
    ext r
    simp [MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_apply]
  have hX : ∀ x : τ,
      (((MvPolynomial.optionEquivLeft R τ).toRingHom).comp
          (MvPolynomial.rename some).toRingHom) (MvPolynomial.X x) =
      (Polynomial.C : MvPolynomial τ R →+* Polynomial (MvPolynomial τ R)) (MvPolynomial.X x) := by
    intro x
    show (MvPolynomial.optionEquivLeft R τ) (MvPolynomial.rename some (MvPolynomial.X x)) = _
    rw [MvPolynomial.rename_X, MvPolynomial.optionEquivLeft_X_some]
  have := MvPolynomial.hom_eq_hom
    (((MvPolynomial.optionEquivLeft R τ).toRingHom).comp (MvPolynomial.rename some).toRingHom)
    (Polynomial.C : MvPolynomial τ R →+* Polynomial (MvPolynomial τ R))
    hC hX p
  simpa using this

/-- **Roadmap §5 step 1, the `MvPolynomial` transport half.** Wires
`regular_linear_of_regular_coeff` (over `B := MvPolynomial τ R ⧸
Ideal.ofList gens'`) back through `MvPolynomial.optionEquivLeft` and
`Ideal.polynomialQuotientEquivQuotientPolynomial` to conclude the original
`MvPolynomial (Option τ) R`-level statement. `gens` doesn't involve `none`
(each generator lies in the range of `rename some`, matching the roadmap's
own "`t` also not in `I`'s generators" condition -- **added this pass**:
the first draft omitted this and is false without it, since `gens` could
otherwise smuggle in a `none`-relation that kills `d`'s regularity even
though `d` alone is a non-zero-divisor; caught by hand-checking a
zero-divisor counterexample before attempting the proof, not found via
REPL, and independently confirmed by the ChatGPT consultation).

**Update this pass:** `optionEquivLeft_rename_some` above is now a proved
lemma (not a flagged assumption), which unblocks the ideal-matching fact
`Ideal.map Polynomial.C I' = Ideal.map (optionEquivLeft R τ) (Ideal.ofList
(gens'.map (rename some)))` used below -- still left as its own local
`sorry`, since it needs `Ideal.map`/`Ideal.ofList` pushed through a list
`map`, which is routine but not yet spelled out. -/
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
  -- Notation matching the docstring: `I' := Ideal.ofList gens'` in
  -- `MvPolynomial τ R`, `B := MvPolynomial τ R ⧸ I'`, and the target quotient
  -- `A := MvPolynomial (Option τ) R ⧸ Ideal.ofList (gens'.map (rename some))`.
  set I' : Ideal (MvPolynomial τ R) := Ideal.ofList gens' with hI'_def
  set A : Ideal (MvPolynomial (Option τ) R) :=
    Ideal.ofList (gens'.map (MvPolynomial.rename some)) with hA_def
  set B : Type _ := MvPolynomial τ R ⧸ I' with hB_def
  -- `dbar`/`cbar` are the images of `d`/`c` in `B`, matching
  -- `regular_linear_of_regular_coeff`'s hypotheses exactly.
  set dbar : B := Ideal.Quotient.mk I' d with hdbar_def
  set cbar : B := Ideal.Quotient.mk I' c with hcbar_def
  -- `Ideal.map_ofList (f : R →+* S) (rs : List R) : Ideal.map f (Ideal.ofList rs) =
  -- Ideal.ofList (rs.map f)` -- confirmed this pass. Applying it to both sides
  -- (once to push `optionEquivLeft` through `A := Ideal.ofList (...)`, once in
  -- reverse to fold `gens'.map Polynomial.C` back into `Ideal.map Polynomial.C
  -- I'`), with `optionEquivLeft_rename_some` collapsing the composed list map
  -- `(gens'.map (rename some)).map (optionEquivLeft R τ)` down to
  -- `gens'.map Polynomial.C` via `List.map_map`.
  have hIdealMap : Ideal.map ((MvPolynomial.optionEquivLeft R τ).toRingEquiv : MvPolynomial (Option τ) R →+* Polynomial (MvPolynomial τ R)) A =
      Ideal.map Polynomial.C I' := by
    rw [hA_def, hI'_def, Ideal.map_ofList, Ideal.map_ofList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    show (MvPolynomial.optionEquivLeft R τ) (MvPolynomial.rename some p) = Polynomial.C p
    exact optionEquivLeft_rename_some p
  -- Build `e : (MvPolynomial (Option τ) R ⧸ A) ≃+* Polynomial B` by composing
  -- `optionEquivLeft R τ` (as a genuine `RingEquiv`, via `.toRingEquiv`) with
  -- `I'.polynomialQuotientEquivQuotientPolynomial.symm`, using
  -- `Ideal.quotientEquiv (I : Ideal R) (J : Ideal S) (f : R ≃+* S) (hIJ : J =
  -- Ideal.map (↑f) I) : R ⧸ I ≃+* S ⧸ J` -- confirmed this pass, note the
  -- hypothesis direction is `J = map f I`, i.e. `hIdealMap.symm` here.
  set e : (MvPolynomial (Option τ) R ⧸ A) ≃+* Polynomial B :=
    (Ideal.quotientEquiv A (Ideal.map Polynomial.C I')
      (MvPolynomial.optionEquivLeft R τ).toRingEquiv hIdealMap.symm).trans
      I'.polynomialQuotientEquivQuotientPolynomial.symm with he_def
  -- `e` sends `Ideal.Quotient.mk A (rename some p)` to `Polynomial.C
  -- (Ideal.Quotient.mk I' p)` for `p ∈ {c, d}` (chasing through both pieces of
  -- `e` on a class represented by `rename some p`: `Ideal.quotientEquiv` acts
  -- as `optionEquivLeft` on representatives, landing on `C p` in `Polynomial
  -- (MvPolynomial τ R)` by `optionEquivLeft_rename_some`, then
  -- `polynomialQuotientEquivQuotientPolynomial.symm` maps `Ideal.Quotient.mk
  -- (map C I') (C p)` to `C (Ideal.Quotient.mk I' p)` by mapping `C`
  -- coefficientwise -- this uses `Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk`
  -- with `f := Polynomial.C p`, whose `Polynomial.map (Quotient.mk I')`
  -- collapses to the single-coefficient case via `Polynomial.map_C`).
  -- `g • x = Ideal.Quotient.mk A g * x` for `x : MvPolynomial (Option τ) R ⧸ A`:
  -- this is the defining property of the `R`-module structure on `R ⧸ A`
  -- (scalar action by the ambient ring factors through the quotient ring's own
  -- multiplication). Proved directly via `Quotient.inductionOn'` rather than
  -- relying on `smul_eq_mul`, which is stated for a ring acting on itself, not
  -- for this cross-type action of `R` on `R ⧸ A`. Needed both for `hd_reg'`
  -- (to transport the `•`-action through `e`) and for the final step.
  have hsmul_mk : ∀ (r : MvPolynomial (Option τ) R) (x : MvPolynomial (Option τ) R ⧸ A),
      r • x = Ideal.Quotient.mk A r * x := by
    intro r x
    refine Quotient.inductionOn' x ?_
    intro x'
    show Ideal.Quotient.mk A (r * x') = Ideal.Quotient.mk A r * Ideal.Quotient.mk A x'
    rw [map_mul]
  -- `e`'s value as a `RingEquiv.trans`, restated as an applied-form lemma
  -- (via `RingEquiv.trans_apply`, a genuine simp lemma) rather than relied on
  -- through `show`'s defeq check, since `e` is `set`-bound and opaque to
  -- defeq unfolding once introduced as a local hypothesis.
  have he_apply : ∀ x : MvPolynomial (Option τ) R ⧸ A,
      e x = I'.polynomialQuotientEquivQuotientPolynomial.symm
        ((Ideal.quotientEquiv A (Ideal.map Polynomial.C I')
          (MvPolynomial.optionEquivLeft R τ).toRingEquiv hIdealMap.symm) x) := by
    intro x
    rw [he_def, RingEquiv.trans_apply]
  have he_C : ∀ p : MvPolynomial τ R,
      e (Ideal.Quotient.mk A (MvPolynomial.rename some p)) =
        Polynomial.C (Ideal.Quotient.mk I' p) := by
    intro p
    rw [he_apply, Ideal.quotientEquiv_mk]
    have hstep : (MvPolynomial.optionEquivLeft R τ).toRingEquiv (MvPolynomial.rename some p) =
        Polynomial.C p := optionEquivLeft_rename_some p
    rw [hstep, Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk]
    simp
  -- `dbar` is regular in `B`: transport `hd_reg` through `e`. `e` is a ring
  -- isomorphism, hence bijective and multiplicative, so `Function.Injective
  -- (g' • ·)` on the source transports to `Function.Injective (e g' • ·)` on
  -- the target for any `g'`; apply with `g' := Ideal.Quotient.mk A (rename
  -- some d)`, giving `IsSMulRegular (Polynomial B) (e (mk A (rename some d)))
  -- = IsSMulRegular (Polynomial B) (C dbar)` by `he_C`. `regular_linear_of_
  -- regular_coeff` wants `IsSMulRegular B dbar` (before promoting to
  -- `Polynomial B`), which is a strictly weaker fact than `IsSMulRegular
  -- (Polynomial B) (C dbar)` -- getting from one to the other needs
  -- `Polynomial.C`'s injectivity plus a coefficient-extraction argument, not
  -- yet spelled out.
  have hd_reg' : IsSMulRegular B dbar := by
    have hd_reg_poly : IsSMulRegular (Polynomial B) (Polynomial.C dbar) := by
      rw [← he_C d]
      have hcongr : ∀ x : MvPolynomial (Option τ) R ⧸ A,
          e ((MvPolynomial.rename some d : MvPolynomial (Option τ) R) • x) =
            e (Ideal.Quotient.mk A (MvPolynomial.rename some d)) • e x := by
        intro x
        rw [hsmul_mk, map_mul, smul_eq_mul]
      exact (Equiv.isSMulRegular_congr (e := e.toEquiv) hcongr).mp hd_reg
    intro x y hxy
    apply Polynomial.C_injective
    apply hd_reg_poly
    simpa [smul_eq_mul] using
      congrArg (Polynomial.C : B →+* Polynomial B) hxy
  -- Main step: `e` sends `g` to `C cbar - X * C dbar` (by `hg`'s shape and
  -- `he_C` applied to `c` and `d`, plus `e`'s ring-hom-ness distributing over
  -- `-`/`*`), so `regular_linear_of_regular_coeff hd_reg' cbar` gives
  -- `IsSMulRegular (Polynomial B) (e g)`, which transports back through `e`
  -- (a bijection intertwining the two `•`-actions, since `e` is a ring hom:
  -- `e (g * x) = e g * e x`) to `IsSMulRegular (MvPolynomial (Option τ) R ⧸
  -- A) g`.
  -- `e (mk A (X none)) = Polynomial.X`: the other half of `optionEquivLeft`'s
  -- action on generators, via the named lemma `optionEquivLeft_X_none`
  -- (mirrors `he_C`'s derivation exactly, swapping `optionEquivLeft_rename_some`
  -- for `optionEquivLeft_X_none`).
  have he_X : e (Ideal.Quotient.mk A (MvPolynomial.X none)) = Polynomial.X := by
    rw [he_apply, Ideal.quotientEquiv_mk]
    have hstep : (MvPolynomial.optionEquivLeft R τ).toRingEquiv (MvPolynomial.X none) =
        Polynomial.X := MvPolynomial.optionEquivLeft_X_none R τ
    rw [hstep]
    show Polynomial.map (Ideal.Quotient.mk I') Polynomial.X = Polynomial.X
    simp
  have hg_e : e (Ideal.Quotient.mk A g) =
      Polynomial.C cbar - Polynomial.X * Polynomial.C dbar := by
    rw [hg]
    show e (Ideal.Quotient.mk A (MvPolynomial.rename some c -
        MvPolynomial.X none * MvPolynomial.rename some d)) = _
    have hstep : (Ideal.Quotient.mk A : MvPolynomial (Option τ) R → MvPolynomial (Option τ) R ⧸ A)
        (MvPolynomial.rename some c - MvPolynomial.X none * MvPolynomial.rename some d) =
        Ideal.Quotient.mk A (MvPolynomial.rename some c) -
          Ideal.Quotient.mk A (MvPolynomial.X none) * Ideal.Quotient.mk A (MvPolynomial.rename some d) := by
      rw [map_sub, map_mul]
    rw [hstep, map_sub, map_mul, he_C, he_C, he_X]
  have hreg_poly : IsSMulRegular (Polynomial B)
      (Polynomial.C cbar - Polynomial.X * Polynomial.C dbar) :=
    regular_linear_of_regular_coeff hd_reg' cbar
  intro x y hxy
  change g • x = g • y at hxy
  rw [hsmul_mk g x, hsmul_mk g y] at hxy
  apply e.injective
  have : e (Ideal.Quotient.mk A g * x) = e (Ideal.Quotient.mk A g * y) := by rw [hxy]
  rw [map_mul, map_mul, hg_e] at this
  have hxy' : (Polynomial.C cbar - Polynomial.X * Polynomial.C dbar) • e x =
      (Polynomial.C cbar - Polynomial.X * Polynomial.C dbar) • e y := by
    simpa [smul_eq_mul] using this
  exact hreg_poly hxy'

/-- **Roadmap §5 step 2 (norm-elimination half), now an actual `sorry`-backed
statement instead of loose prose.** Previously this section only described
the resultant identity `Res_w(P + Q•w, w² - f) = P² - Q²•f` informally and
declined to state a Lean theorem "pending the ring-stack choice being
pinned down." That choice is no longer open: `§4.1`/`DataDerivationTower.lean`
already commit to `AdjoinRoot (X^2 - C f)` as the ring `w` lives in, so
there is no obstruction to writing the statement down — only to proving it,
which is not attempted here.

Statement: for `R` a commutative ring, `f : R`, `w : AdjoinRoot (X^2 - C f :
Polynomial R)` the adjoined root, and `P Q : R` such that `g := C P + C Q *
X` maps to `C P + C Q • w`'s class — if the list `gens` (each of the shape
`Pᵢ + Qᵢ • w`, i.e. each `AdjoinRoot.mk`-image of a degree-≤1-in-`X`
polynomial) is a regular sequence on `AdjoinRoot (X^2 - C f)`, then the
list of "norms" `[P₁^2 - Q₁^2*f, ..., Pₙ^2 - Qₙ^2*f]` is a regular sequence
on `R` itself. This is the precise claim `eightVar_finiteQuotient` and
`fourVar_finiteQuotient` below both need, stated generically over one
`AdjoinRoot` layer at a time (the two-layer `wa1,wa2`/`wb1,wb2` towers, one
per sample, are meant to invoke this twice per sample -- once per adjoined
`w_i` -- not covered by a single application). Genuinely new work: neither
the resultant identity nor its regular-sequence-transport consequence is
proved anywhere in this project. 
 
**Core case of `regular_of_norm_eliminate`, split out and attempted this
pass.** The general-`n` statement below reduces, at each step of its
induction, to this single-generator fact: `AdjoinRoot (X^2 - C f)` is a free
`R`-module of rank 2 with basis `{1, w}` (`w := AdjoinRoot.root`), so
multiplication by `g := P + Q•w` is an `R`-linear endomorphism of `R × R`
(via that basis) with matrix `M := !![P, Q*f; Q, P]` — its images of `1`
and `w` are `P + Q•w ↦ (P,Q)` and `w•(P+Q•w) = Q•f + P•w ↦ (Q*f, P)`
respectively. `M.det = P^2 - Q^2*f`, exactly the norm/target quantity.

**Proof strategy (verified by hand, NOT yet carried out in Lean — this
`sorry` is a genuine attempt-and-defer, not a restatement of the header
theorem):**
- *Injectivity half* (`N` is `IsSMulRegular` on `R`): suppose `N * r = 0`
  for `r : R`. Let `v := M.adjugate.mulVec ![r, 0] = (P*r, -Q*r)` (an
  explicit 2-vector, computed from `M.adjugate = !![P, -Q*f; -Q, P]`).
  `M.mulVec v = M.mulVec (M.adjugate.mulVec ![r,0]) = (M * M.adjugate).mulVec
  ![r,0] = (N • 1).mulVec ![r,0] = N*r • ![r,0] = 0` (`Matrix.mul_adjugate`
  gives `M * M.adjugate = M.det • 1`). Translating `v = (P*r, -Q*r)` back
  through the `{1,w}` basis to the element `P*r - Q*r•w : AdjoinRoot(...)`,
  `M.mulVec v = 0` says `g • (P*r - Q*r•w) = 0`. Two sub-cases: (a) if
  `P*r - Q*r•w ≠ 0` in `AdjoinRoot(...)`, this directly contradicts `g`
  being `IsSMulRegular` (from `hreg`'s length-1 case, or the first step of
  the general induction); (b) if `P*r = Q*r = 0` in `R`, then `r•1 = 0` in
  `AdjoinRoot(...)` too (since `{1,w}` is an `R`-basis, `r•1 ↦ (r,0)` and
  `(r,0)=(0,0)` in `R×R` iff `r=0` UNLESS... careful: `P*r=Q*r=0` does NOT
  immediately give `r=0` unless `P,Q` themselves satisfy some regularity —
  but it DOES give `g • (r•1) = P*r + Q*r•w = 0•1+0•w = 0` directly, i.e.
  `r•1` is annihilated by `g`; if `r ≠ 0` then `r•1 ≠ 0` in `AdjoinRoot(...)`
  (basis-freeness), again contradicting `g`'s regularity). Either sub-case
  forces `r = 0`, giving injectivity of `N`.
- *Nonzero-quotient half* (`R ⧸ (N) ≠ 0`, i.e. `N` not a unit): if `N` were
  a unit, `M.adjugate * N⁻¹` would be a two-sided inverse for `M`
  (`Matrix.mul_adjugate`/`Matrix.adjugate_mul` plus `N` a unit), making
  multiplication-by-`g` bijective on `AdjoinRoot(...)`, in particular
  surjective, so `g` is a unit there, contradicting `hreg`'s "quotient by
  `g` is nonzero" clause (a unit generates the whole ring).

This is a concrete, closed argument (same flavor as `regular_linear_of_regular_coeff`
above — a leading-coefficient/determinant computation, not open-ended search)
but needs `AdjoinRoot`'s `{1,w}` basis made explicit in Lean
(`AdjoinRoot.powerBasisAux'` for `Monic (X^2 - C f)`, or direct
`AdjoinRoot.modByMonicHom`/`.coeff 0`/`.coeff 1` unfolding as
`towerToRdec_vars_subset` above already does for a similar purpose) and the
matrix/adjugate identities (`Matrix.mul_adjugate`, `Matrix.mulVec_mulVec`)
threaded through -- superseded by the direct factorization argument below.

**Attempted this pass via a factorization/conjugation argument.** Write
`S := AdjoinRoot (X^2 - C f)`, `w := AdjoinRoot.root (X^2 - C f)`, `g := P +
Q•w`, `g' := P - Q•w`. Since `w^2 = f` in `S`, `g * g' = algebraMap R S (P^2
- Q^2*f)`. Not-a-unit half: if `n` were a unit, `algebraMap R S n = g*g'`
would be, forcing `g` to be a unit, contradicting `hreg`. Regular half: the
`R`-algebra involution `w ↦ -w` on `S` sends `g ↦ g'`, transporting `g`'s
regularity to `g'`; then `n*a=n*b` in `R` maps to `g*(g'*algebraMap a) =
g*(g'*algebraMap b)`, cancel both factors, get `algebraMap a = algebraMap
b`, hence `a=b` (needs `Nontrivial R`; `Subsingleton R` case is trivial).
NOTE: written without REPL access -- names and a few tactic steps
(flagged inline) are not independently verified and may need adjustment. -/
theorem regular_of_norm_eliminate_one {R : Type*} [CommRing R] (f P Q : R)
    (hreg : RingTheory.Sequence.IsRegular
      (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R))
      [AdjoinRoot.mk (Polynomial.X ^ 2 - Polynomial.C f)
        (Polynomial.C P + Polynomial.C Q * Polynomial.X)]) :
    RingTheory.Sequence.IsRegular R [P ^ 2 - Q ^ 2 * f] := by
  classical
  by_cases hR : Nontrivial R
  swap
  · haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    haveI : Subsingleton (Polynomial R) := by
      constructor
      intro p q
      ext i
      exact Subsingleton.elim _ _
    have hp_zero : (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R) = 0 :=
      Subsingleton.elim _ _
    letI : Subsingleton (AdjoinRoot
        (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R)) :=
      Function.Surjective.subsingleton
        (Ideal.Quotient.mk_surjective
          (I := Ideal.span ({(Polynomial.X ^ 2 - Polynomial.C f : Polynomial R)} : Set (Polynomial R))))
    exact False.elim ((not_nontrivial_iff_subsingleton.mpr inferInstance)
      hreg.nontrivial)
  letI : Nontrivial R := hR
  let p : Polynomial R := Polynomial.X ^ 2 - Polynomial.C f
  have hp_monic : p.Monic := by
    dsimp [p]
    exact Polynomial.monic_X_pow_sub_C f (by norm_num)
  have hp_deg : p.degree = (2 : WithBot ℕ) := by
    dsimp [p]
    exact Polynomial.degree_X_pow_sub_C (R := R) (n := 2) (by norm_num) f
  have hp_pos : 0 < p.degree := by
    rw [hp_deg]
    norm_num
  have hreg' : RingTheory.Sequence.IsRegular (AdjoinRoot p)
      [AdjoinRoot.mk p (Polynomial.C P + Polynomial.C Q * Polynomial.X)] := by
    simpa [p] using hreg
  let w : AdjoinRoot p := AdjoinRoot.root p
  let g : AdjoinRoot p :=
    AdjoinRoot.mk p (Polynomial.C P + Polynomial.C Q * Polynomial.X)
  let g' : AdjoinRoot p :=
    AdjoinRoot.mk p (Polynomial.C P - Polynomial.C Q * Polynomial.X)
  let n : R := P ^ 2 - Q ^ 2 * f
  have hw2 : w ^ 2 = algebraMap R (AdjoinRoot p) f := by
    have hroot := AdjoinRoot.eval₂_root p
    have hroot' : w ^ 2 - algebraMap R (AdjoinRoot p) f = 0 := by
      simpa [w, p, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C,
        AdjoinRoot.algebraMap_eq] using hroot
    exact sub_eq_zero.mp hroot'
  have hfactor : g * g' = algebraMap R (AdjoinRoot p) n := by
    have hexpand :
        (Polynomial.C P + Polynomial.C Q * Polynomial.X) *
          (Polynomial.C P - Polynomial.C Q * Polynomial.X) =
          Polynomial.C (P ^ 2) - Polynomial.C (Q ^ 2) * Polynomial.X ^ 2 := by
      simp only [map_pow]
      ring
    calc
      g * g' = AdjoinRoot.mk p
          ((Polynomial.C P + Polynomial.C Q * Polynomial.X) *
            (Polynomial.C P - Polynomial.C Q * Polynomial.X)) := by
        simp [g, g', map_mul]
      _ = AdjoinRoot.mk p
          (Polynomial.C (P ^ 2) - Polynomial.C (Q ^ 2) * Polynomial.X ^ 2) := by
        rw [hexpand]
      _ = (AdjoinRoot.of p) (P ^ 2) -
          (AdjoinRoot.of p) (Q ^ 2) * w ^ 2 := by
        simp [w, map_sub, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      _ = algebraMap R (AdjoinRoot p) (P ^ 2 - Q ^ 2 * f) := by
        rw [hw2]
        simp [AdjoinRoot.algebraMap_eq, map_sub, map_mul, map_pow]
      _ = algebraMap R (AdjoinRoot p) n := by
        rfl
  have hx : IsSMulRegular (AdjoinRoot p) g := by
    rw [RingTheory.Sequence.isRegular_cons_iff] at hreg'
    exact hreg'.1
  have hg_not_unit : ¬ IsUnit g := by
    intro hg
    have htop : Ideal.span ({g} : Set (AdjoinRoot p)) = ⊤ :=
      (Ideal.span_singleton_eq_top).2 hg
    apply hreg'.top_ne_smul
    rw [Ideal.ofList_singleton, htop]
    simp
  have heval : Polynomial.eval₂ (algebraMap R (AdjoinRoot p))
      (-w) p = 0 := by
    have hexpand : Polynomial.eval₂ (algebraMap R (AdjoinRoot p)) (-w) p
        = (-w) ^ 2 - algebraMap R (AdjoinRoot p) f := by
      simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
    have hpow : (-w) ^ 2 = w ^ 2 := by
      ring
    rw [hexpand, hpow, hw2, sub_self]
  let σ : AdjoinRoot p →ₐ[R] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId R (AdjoinRoot p)) (-w) heval
  have hσ_root : σ w = -w := by
    simpa only [σ, w] using
      (AdjoinRoot.liftAlgHom_root p (Algebra.ofId R (AdjoinRoot p)) (-w) heval)
  have hσ_invol : σ.comp σ = AlgHom.id R (AdjoinRoot p) := by
    apply AdjoinRoot.algHom_ext
    change σ (σ (AdjoinRoot.root p)) = AdjoinRoot.root p
    change σ (σ w) = w
    rw [hσ_root, map_neg, hσ_root, neg_neg]
  have hinv : Function.Involutive σ := by
    intro z
    have hz := congrArg (fun φ : AdjoinRoot p →ₐ[R] AdjoinRoot p => φ z) hσ_invol
    simpa using hz
  have hσ_g : σ g = g' := by
    simp [σ, g, g', Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, AdjoinRoot.mk_C,
      AdjoinRoot.mk_X, map_sub, map_mul, AdjoinRoot.algebraMap_eq] <;> ring
  have hσ_g' : σ g' = g := by
    calc
      σ g' = σ (σ g) := by rw [hσ_g]
      _ = g := hinv g
  have hσ_inj : Function.Injective σ := by
    intro a b hab
    calc
      a = σ (σ a) := (hinv a).symm
      _ = σ (σ b) := congrArg σ hab
      _ = b := hinv b
  have hx' : IsSMulRegular (AdjoinRoot p) g' := by
    intro a b hab
    have hh := congrArg σ hab
    have hc : g * σ a = g * σ b := by
      simpa [map_mul, hσ_g'] using hh
    have hc' : σ a = σ b := hx (by simpa [smul_eq_mul] using hc)
    exact hσ_inj hc'
  have hnorm : IsSMulRegular R n := by
    intro a b hab
    have step1 : algebraMap R (AdjoinRoot p) n *
        algebraMap R (AdjoinRoot p) a =
        algebraMap R (AdjoinRoot p) n *
          algebraMap R (AdjoinRoot p) b := by
      simpa [smul_eq_mul, map_mul] using congrArg
        (algebraMap R (AdjoinRoot p)) hab
    rw [← hfactor] at step1
    have step2 : g' * algebraMap R (AdjoinRoot p) a =
        g' * algebraMap R (AdjoinRoot p) b := by
      apply hx
      simpa [smul_eq_mul, mul_assoc] using step1
    have step3 : algebraMap R (AdjoinRoot p) a =
        algebraMap R (AdjoinRoot p) b := by
      apply hx'
      simpa [smul_eq_mul] using step2
    have hof : (AdjoinRoot.of p) a = (AdjoinRoot.of p) b := by
      simpa [AdjoinRoot.algebraMap_eq] using step3
    by_contra hab
    have hpoly_ne : Polynomial.C a - Polynomial.C b ≠ 0 := by
      intro hz
      apply hab
      apply Polynomial.C_injective
      exact sub_eq_zero.mp hz
    have hpoly_deg : (Polynomial.C a - Polynomial.C b).degree < p.degree := by
      have hle : (Polynomial.C a - Polynomial.C b).degree ≤ (0 : WithBot ℕ) := by
        calc
          (Polynomial.C a - Polynomial.C b).degree ≤
              max (Polynomial.C a).degree (Polynomial.C b).degree :=
            Polynomial.degree_sub_le (Polynomial.C a) (Polynomial.C b)
          _ ≤ (0 : WithBot ℕ) := max_le Polynomial.degree_C_le Polynomial.degree_C_le
      exact lt_of_le_of_lt hle hp_pos
    have hmk : (AdjoinRoot.mk p) (Polynomial.C a - Polynomial.C b) ≠ 0 :=
      AdjoinRoot.mk_ne_zero_of_degree_lt hp_monic hpoly_ne hpoly_deg
    apply hmk
    change (AdjoinRoot.mk p) (Polynomial.C a - Polynomial.C b) = 0
    simpa [map_sub] using (sub_eq_zero.mpr hof)
  have hn_not_unit : ¬ IsUnit n := by
    intro hn
    have hmap : IsUnit (algebraMap R (AdjoinRoot p) n) := hn.map _
    have hgg : IsUnit (g * g') := by
      rw [hfactor]
      exact hmap
    exact hg_not_unit ((IsUnit.mul_iff.mp hgg).1)
  refine RingTheory.Sequence.IsRegular.cons hnorm ?_
  letI : Nontrivial (QuotSMulTop n R) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    intro htop
    apply hn_not_unit
    obtain ⟨b, hb, hnb⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists (1 : R) n (⊤ : Submodule R R)).mp
        (htop.symm ▸ Submodule.mem_top)
    exact IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hnb)
  exact RingTheory.Sequence.IsRegular.nil R (QuotSMulTop n R)
theorem regular_of_norm_eliminate {R : Type*} [CommRing R] (f : R)
    (n : ℕ) (Pv Qv : Fin n → R)
    (gens : Fin n → AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R))
    (hgens : ∀ i, gens i = AdjoinRoot.mk (Polynomial.X ^ 2 - Polynomial.C f)
      (Polynomial.C (Pv i) + Polynomial.C (Qv i) * Polynomial.X))
    (hcop : ∀ i : Fin n, IsCoprime (Pv i) (Qv i))
    (hcompat : ∀ (m : ℕ) (Pm Qm : Fin (m + 1) → R),
      (∀ i : Fin (m + 1), IsCoprime (Pm i) (Qm i)) →
      RingTheory.Sequence.IsRegular
        (QuotSMulTop ((Pm 0) ^ 2 - (Qm 0) ^ 2 * f) R)
        (List.ofFn (fun i : Fin m => (Pm i.succ) ^ 2 - (Qm i.succ) ^ 2 * f)))
    (hreg : RingTheory.Sequence.IsRegular
      (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R))
      (List.ofFn gens)) :
    RingTheory.Sequence.IsRegular R
      (List.ofFn (fun i => (Pv i) ^ 2 - (Qv i) ^ 2 * f)) := by
  induction n with
  | zero =>
      have hR : Nontrivial R := by
        by_contra hR
        haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
        haveI : Subsingleton (Polynomial R) := by
          constructor
          intro p q
          ext i
          exact Subsingleton.elim _ _
        letI : Subsingleton (AdjoinRoot
            (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R)) :=
          Function.Surjective.subsingleton
            (Ideal.Quotient.mk_surjective
              (I := Ideal.span ({(Polynomial.X ^ 2 - Polynomial.C f : Polynomial R)} :
                Set (Polynomial R))))
        exact not_nontrivial_iff_subsingleton.mpr inferInstance hreg.nontrivial
      letI : Nontrivial R := hR
      simpa only [List.ofFn_zero] using
        (RingTheory.Sequence.IsRegular.nil R R)
  | succ n ih =>
      let A := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R)
      let i0 : Fin (Nat.succ n) := ⟨0, Nat.succ_pos n⟩
      let g0 : A := gens i0
      let n0 : R := (Pv i0) ^ 2 - (Qv i0) ^ 2 * f
      have hi0 : i0 = (0 : Fin (Nat.succ n)) := by
        simp [i0, Fin.ext_iff]
      have hreg_cons : RingTheory.Sequence.IsRegular A
          (g0 :: List.ofFn (fun i : Fin n => gens i.succ)) := by
        show RingTheory.Sequence.IsRegular A
          (gens i0 :: List.ofFn (fun i : Fin n => gens i.succ))
        rw [hi0]
        simpa [A, List.ofFn_succ] using hreg
      have hhead : IsSMulRegular A g0 := by
        rw [RingTheory.Sequence.isRegular_cons_iff] at hreg_cons
        exact hreg_cons.1
      have hreg_one : RingTheory.Sequence.IsRegular A [g0] := by
        refine RingTheory.Sequence.IsRegular.cons hhead ?_
        have htail_reg : RingTheory.Sequence.IsRegular (QuotSMulTop g0 A)
            (List.ofFn (fun i : Fin n => gens i.succ)) := by
          exact ((RingTheory.Sequence.isRegular_cons_iff A g0
            (List.ofFn (fun i : Fin n => gens i.succ))).mp hreg_cons).2
        haveI : Nontrivial (QuotSMulTop g0 A) := htail_reg.nontrivial
        exact RingTheory.Sequence.IsRegular.nil _ _
      have hreg_one' : RingTheory.Sequence.IsRegular
          (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f : Polynomial R))
          [AdjoinRoot.mk (Polynomial.X ^ 2 - Polynomial.C f)
            (Polynomial.C (Pv i0) + Polynomial.C (Qv i0) * Polynomial.X)] := by
        simpa [A, g0, hgens i0] using hreg_one
      have hnorm_one : RingTheory.Sequence.IsRegular R [n0] := by
        simpa [n0] using
          (regular_of_norm_eliminate_one f (Pv i0) (Qv i0) hreg_one')
      have hfirst_norm : IsSMulRegular R n0 := by
        rw [RingTheory.Sequence.isRegular_cons_iff] at hnorm_one
        exact hnorm_one.1
      rw [List.ofFn_succ]
      refine RingTheory.Sequence.IsRegular.cons hfirst_norm ?_
      show RingTheory.Sequence.IsRegular (QuotSMulTop n0 R)
        (List.ofFn (fun i : Fin n => (Pv i.succ) ^ 2 - (Qv i.succ) ^ 2 * f))
      have hn0 : n0 = Pv (0 : Fin (Nat.succ n)) ^ 2 - Qv (0 : Fin (Nat.succ n)) ^ 2 * f := by
        show (Pv i0) ^ 2 - (Qv i0) ^ 2 * f = Pv (0 : Fin (Nat.succ n)) ^ 2 - Qv (0 : Fin (Nat.succ n)) ^ 2 * f
        rw [hi0]
      rw [hn0]
      exact hcompat n Pv Qv hcop

/-! ## §5 steps 3-4: NOT YET STATEABLE, deliberately not stubbed

Roadmap §5 steps 3 ("8-variable finite-quotient certificate") and 4
("4-variable finite-quotient certificate, then Cohen-Macaulay upgrade to
regular sequence") used to have `sorry`-backed theorem stubs here
(`eightVar_finiteQuotient`, `fourVar_finiteQuotient`). Both were deleted
this pass, per project convention "we do not use hypotheses to get out of
proving something": their generator lists (`eightGens`/`fourGens`) were
taken as bare hypothesis-parameters with a `hgens : True` placeholder
standing in for "these really are the generators §5 describes" — that
placeholder made both statements provable by never actually pinning down
which polynomials they're about, which is the same failure mode as an
unjustified `sorry`-avoidance, just dressed as a hypothesis instead.

The honest state: these two steps cannot be stated as real theorems yet,
because the object they'd quantify over — `theData`'s output restricted to
the 8-variable subring after eliminating `U0,U1,V0,V1` (step 3), and that
result's further restriction to 4 variables after eliminating
`wa1,wa2,wb1,wb2` (step 4) — is not constructed anywhere in this file or in
`TheDataDerivation`. Restating them correctly requires building that
restriction map first (not just asserting its existence), which is new
work, not a proof-search gap. Left as a documented TODO rather than a fake
`sorry` or a vacuous hypothesis.

## §5bis-0a. Scaffold: the gcd/leading-coefficient route for steps 3-4

**This pass (per Claire's request): scaffold the "big kahuna" sorry.**
Steps 3-4 above are correctly flagged as "not yet stateable" in full
generality (no restriction map to the 8-variable or 4-variable subring
exists yet).
What follows is a DIFFERENT, more concrete route to the same two
obligations, avoiding the need to construct that restriction map at all:
peel variables one at a time (`peelEquiv` below already does this for one
variable) and show each generator becomes MONIC, or has REGULAR leading
coefficient, in the just-peeled variable, given everything peeled before
it. This is exactly `regular_of_linear_elim`'s
"already-imposed-ideal-is-extended-from-the-coefficient-ring" hypothesis
iterated twelve times, one variable at a time, using `Polynomial.Monic`'s
"regular over ANY ring" fact (`Polynomial.Monic.isRegular`, no domain
hypothesis needed -- this is why `uRS_monic` above, already fully proved
with NO `sorry`, is load-bearing here and not just background flavor).

Deliberately abstract / "on paper" per instructions -- this section is
scaffolding, not a finished proof. Each `sorry` below names precisely the
gcd- or leading-coefficient fact it needs, so a later pass (or a ChatGPT
consultation, this is flagged as the best candidate for one) can fill
them in one at a time, easiest first, without re-deriving the overall
architecture.

### The peeling order, and why the curve relations go first

`genList`'s 12 generators, in `Idx` order `wa1,wa2,wb1,wb2,a2,a1,b2,b1,
U0,U1,V0,V1`:
- The four curve relations `curveA1/A2/B1/B2` are each, BY INSPECTION
  (§3 above), MONIC of degree 2 in exactly one variable
  (`wa1`/`wa2`/`wb1`/`wb2` respectively) with coefficients not mentioning
  that variable at all -- `wa1' p ^ 2 - (...)` where the `(...)` is a
  polynomial in `a1` alone. So these four are the natural FIRST four
  variables to peel: `curveA1` is monic in `wa1` over the (`wa1`-free)
  coefficient ring, `regular_of_linear_elim`'s hypothesis is satisfied
  trivially (the "already-imposed ideal" before peeling `wa1` is the
  ZERO ideal, so vacuously extended from the coefficient ring), and
  `Polynomial.Monic.isRegular` finishes it in one step per curve relation.
  This part needs NO gcd argument at all -- flagged as the easiest fully-
  concrete piece of steps 3-4, likely provable outright rather than left
  `sorry`, once someone sits down with the REPL.
- The eight `Fu_decoupled`/`Fv_decoupled` generators are each of the shape
  `num - U_i * den` (or `V_i`), i.e. LINEAR in the target variable
  (`U0`/`U1`/`V0`/`V1`) with coefficient `-den` -- exactly
  `regular_of_linear_elim`'s shape (`c - X * d`), NOT
  `regular_of_norm_eliminate`'s (that machinery is for the `wa1`-type
  quadratic adjunctions, already spent on the curve relations above; the
  target variables are genuinely linear, no square-root structure). So
  peeling `U0,U1,V0,V1` needs `regular_of_linear_elim` applied with
  `d := den` (`u1_den`/`u2_den`/`v1_den`/`v2_den`), and the load-bearing
  fact is `den`'s REGULARITY (in particular nonzero-ness, since `Rdec p`
  is a domain -- `MvPolynomial` over a field is an integral domain, so
  "regular" and "nonzero" coincide here) in the quotient by everything
  peeled so far. This is where `hgcdA`/`hgcdB`'s `IsCoprime (Ypoly ...)
  (uRS ...)` hypothesis is expected to enter: `vRS`'s definition (`vRS =
  (-Epoly * gcdA Ypoly uRS) %ₘ uRS`, `DataDerivationMumford.lean`) shows
  `v1_den`/`v2_den` trace back to `uRS`'s coefficients, and `uRS` is
  MONIC (`uRS_monic`, already fully proved) -- a monic polynomial's
  coefficients are not simultaneously zero, giving SOME nonvanishing
  fact, though pinning down exactly which coefficient of `uRS`
  contributes to which of `u1_den`/`u2_den`'s two slots (`Fin 2`) is not
  worked out here. This is the genuinely hard gcd-tracking half of the
  scaffold; see `denRegular` below for where it is isolated as its own
  named `sorry` rather than buried inside a larger proof.
- After all twelve variables are peeled (four curve variables, four `a`/`b`
  anchor variables `a1,a2,b1,b2` -- these do NOT appear as a LEADING
  variable of any generator on their own, they only ever appear inside
  the `wa1' p ^ 2 - (...)` coefficient blob and inside `theData`'s
  `num`/`den` polynomials, so peeling them needs its own argument, not
  covered by `regular_of_linear_elim`/`regular_of_norm_eliminate` as
  stated -- flagged below as `curveCoeffRegular`, the other genuinely new
  piece), and finally the four target variables `U0,U1,V0,V1`), the
  quotient ring is `Rdec p ⧸ (genList ...)`, and twelve applications of
  "regular element extends a regular sequence by one" is exactly
  `RingTheory.Sequence.IsRegular` for the whole list -- this is the
  content of `decoupledSystem_isRegularSequence` itself, assembled at the
  very end from the pieces below via `regularSeq_of_peel_chain`.

### The two genuinely new named gaps

Everything above reduces to two facts not yet proved anywhere in this
project (beyond `uRS_monic`, already done, and `regular_of_linear_elim`/
`regular_of_norm_eliminate`, already scaffolded above): -/

-- Real statement and proof moved below `peelEquivGen`/`peelEquiv` and
-- Layer 1 (`Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular`), §5bis-0/
-- §5bis-0a, since the correct statement needs both: `curveCoeffRegular` is
-- defined right after Layer 1 below, no longer a `True`-stub here.

set_option maxHeartbeats 1000000 in
/-- **Gap 2 (the actual gcd/leading-coefficient tracking, the heart of the
"big kahuna").** `theData`'s eight `num`/`den` polynomials
(`u1_num/den`, `u2_num/den`, `v1_num/den`, `v2_num/den`, each `Fin 2 →
Rdec p`) are built (§4bis, `coeffsToNumDen`) by running `uRS`/`vRS`'s
`Polynomial (K2 p ...)` coefficients through `towerToRdec`, i.e.
`u1_den i = (towerToRdec p aSideGens ((uRS ...).coeff i.val)).2` and
likewise for `v1_den` via `vRS`. `uRS` is MONIC (`uRS_monic`, proved, no
`sorry`) of degree exactly 2 (`curBeforeMonic`'s degree, inherited
unchanged by the monic-normalization in `uRS`'s definition -- **not
independently confirmed here**, flagged as a small additional check
worth confirming in the REPL rather than assumed silently), so its TWO
non-leading coefficients (`.coeff 0`, `.coeff 1` -- exactly `Fin 2`'s
range, matching `u1_den`'s indexing) are not BOTH forced to vanish
identically as elements of `K2 p ...` (only their SIMULTANEOUS vanishing
would make `uRS` degree-0, contradicting `uRS_monic`'s degree-2 claim) --
but "not both zero" is far weaker than "each individually nonzero after
`towerToRdec`'s denominator-clearing", which is the actual fact needed
for `regular_of_linear_elim`'s `d`-regularity hypothesis on EACH of the
four `Fu`/`Fv` peels. This gap is exactly where `hgcdA`/`hgcdB`'s
`IsCoprime (Ypoly ...) (uRS ...)` hypothesis is expected to do its work
(coprimality with `Ypoly` is what makes `vRS`'s construction well-defined
at all, per `vRS`'s own docstring in `DataDerivationMumford.lean` --
tracking exactly how that coprimality propagates to `v1_den`/`v2_den`'s
nonvanishing, as opposed to merely `vRS`'s well-definedness, is new work
not attempted anywhere in this project). Left maximally abstract here
(`hden` as a bare hypothesis-shaped `sorry` target) rather than guessed at
in more detail, per the instruction to keep this pass "on paper" -- this
is the single best candidate in the whole file for a ChatGPT
consultation, since pinning it down needs the actual `rrBasis5`/
`cramerSolution`/Euclidean-algorithm machinery in
`DataDerivationSolve.lean`/`DataDerivationMumford.lean` traced through in
full, not proof search.

**This pass (per Claire's request): `denRegular` split into its real pieces.**
The single flat `sorry` above hid two genuinely different obligations that
were being conflated. Unbundling them:

**Piece A — `towerToRdec`'s denominator-clearing recursion is
zero-preserving.** Chasing `towerToRdec`'s definition (`DataDerivationMumford.lean`,
`towerToRdec`/`towerToRdecK1`/`baseFracToRing`) shows its denominator output
at every level is a PRODUCT of two things: (i) an `aeval`/`rename`-transported
copy of `IsFractionRing.den`, which is a genuine nonzero-divisor of
`MvPolynomial (Fin 2) (F p)` by the `IsFractionRing` API alone (see
`towerToRdec_spec`'s own `hdK` step, already proved, for exactly this fact
one level down), and (ii) the SAME kind of denominator one recursion level
up. Since `aSideGens`/`bSideGens`'s `tGen`/`wGen` maps are injective
(`![a1,a2]`/`![wa1,wa2]` etc., distinct `Idx` constructors), the `aeval`
substitution step is really just a RENAMING (injective variable map), which
sends nonzero `MvPolynomial (Fin 2) (F p)` elements to nonzero `Rdec p`
elements. So `(towerToRdec p sg v).2 ≠ 0` should follow from `v ≠ 0`
(`v : K2 p ...`) alone, for `sg` with injective generators — this is pure
bookkeeping over an already-fully-proved recursion (`towerToRdec`/
`towerToRdecK1`/`baseFracToRing` all have **no `sorry`**), not new math, but
was never assembled into its own lemma. Isolated below as
`towerToRdec_den_ne_zero`, **left `sorry`** since the three-level induction
(base case via `IsFractionRing`, then twice through `towerToRdecK1`/
`towerToRdec`'s `den0*den1` combination step) is real work, just mechanical
rather than mathematical.

**Piece B — the actual `K2`-level coefficient nonvanishing, UPDATE: this is
NOT a consequence of `hcurA/B`/`hgcdA/B` at all — resolved, not just
proved.** Given Piece A, `denRegular` reduces to: is `uRS.coeff i ≠ 0`
(`i : Fin 2`) and `vRS.coeff i ≠ 0`? The ChatGPT consultation this section
originally flagged as needed (`chatgpt-prompt-denRegular.md`, sent and
answered this pass) came back with a clean counterexample: `uRS = X^2+1`,
`Ypoly = 1` satisfies `hcur`/`hgcd` fully yet has `uRS.coeff 1 = 0`, and can
force `vRS.coeff 0 = vRS.coeff 1 = 0` outright if the numerator happens to
land divisible by `uRS`. So per this project's own rule ("if we find a
false theorem, we try to weaken it first"), `uRS_coeff_ne_zero`/
`vRS_coeff_ne_zero` below no longer attempt a proof from `hcurA/B`/
`hgcdA/B` alone — they take a new explicit hypothesis, `Nondegenerate`
(below `curBeforeMonic_natDegree_eq_two`), bundling the four individual
nonvanishing facts as a genuine further exceptional-locus condition on the
specific symbolic Mumford divisor, analogous in status to `hcurA/B`/
`hgcdA/B` themselves rather than derived from them. 

 **Gap 2a — RESOLVED, weakened rather than proved as originally stated.**
`curBeforeMonic` needs its own degree fact before `uRS_monic`'s "monic
degree 2" claim pins down WHICH two coefficient slots (`Fin 2`) `u1_den`/
`u2_den` are reading. Investigated this pass, per this project's own rule
("if we find a false theorem, we try to weaken it first"): the ORIGINAL
target, `curBeforeMonic.natDegree = 2` from `hcur` alone, is not provable
as stated, for the same flavor of reason `uRS_coeff_ne_zero`/
`vRS_coeff_ne_zero` weren't -- exact degree needs data-dependent
nonvanishing that `hcur` doesn't supply.

**What's actually free (no hypothesis beyond monicity of the three
divisors, all immediate by inspection):** `Polynomial.natDegree_divByMonic`
(`Mathlib.Algebra.Polynomial.Div`, confirmed) is UNCONDITIONAL --
`(f /ₘ g).natDegree = f.natDegree - g.natDegree` (truncated `ℕ`
subtraction) for ANY `g.Monic`, with no exactness/root condition needed,
unlike what the earlier "not yet confirmed" note above worried about. So
`curBeforeMonic.natDegree = Npoly.natDegree - 1 - 1 - 2` holds
UNCONDITIONALLY, given only that `X - C (anchor1 ...).1`, `X - C (anchor2
...).1`, and `X^2 + C u1 * X + C u0` are each `Monic` (all three immediate:
`Polynomial.monic_X_sub_C`-style for the first two, `Polynomial.monic_X_pow_add`-
or direct-computation-style for the quadratic since its `X^2` coefficient is
literally `1` with no scaling). This is `curBeforeMonic_natDegree_eq_sub`
below, proved outright, **no `sorry`**.

**What is NOT free, and why `= 2` specifically was the wrong target:**
`Npoly.natDegree` itself is only boundable, not pinned, without tracing
through the full Cramer's-rule solve (`coeffsOut`/`cramerSolution`/
`matrixA`, `DataDerivationSolve.lean`). Since `rrBasis5 =
[(0,0,0),(2,1,0),(4,2,0),(5,0,1),(6,3,0)]` (computed directly, not
estimated -- `rrBasisCandidates 20` sorted by first component and the first
5 taken), `Ypoly` is built from the SINGLE `bj=1` entry `(5,0,1)`, i.e.
`Ypoly = C (coeffsOut ... 3)` is a genuine CONSTANT (`natDegree ≤ 0`, exactly
0 iff that one coefficient is nonzero, else the zero polynomial) -- NOT the
"degree ≤ 8-ish" this section used to guess, correcting that estimate.
`Epoly`'s top term is the `bj=0` entry `(6,3,0)`, so `Epoly.natDegree ≤ 3`.
With `fAtX.natDegree = 5` (from `curvePoly_natDegree`, already proved,
`natDegree` preserved under `Polynomial.map` by an injective ring hom into
a field extension), `Npoly = Epoly^2 - fAtX * Ypoly^2` has
`Npoly.natDegree ≤ max (2*3) (5 + 2*0) = 6` by the standard
`natDegree_sub_le`/`natDegree_mul_le`/`natDegree_pow_le` triangle-inequality
chain (`≤`, not `=` -- cancellation in the leading term, or `Epoly`/`Ypoly`'s
actual leading coefficients from `coeffsOut` vanishing, are both live
possibilities not ruled out by anything proved so far). So the honest
bound this pass can certify is `curBeforeMonic.natDegree ≤ 6 - 1 - 1 - 2 = 2`
UNCONDITIONALLY (truncated subtraction only helps here, never hurts an
upper bound) -- which happens to already match the target's "≤ 2" half
for free, with "= 2" (equivalently `≥ 2`, equivalently `curBeforeMonic ≠ 0`
persisting all the way to degree exactly 2 rather than collapsing lower)
still needing the same class of `MatrixNondegenerate`-adjacent genericity
`dvd_N_anchor1`/`dvd_N_anchor2`/`dvd_N_u` already carry as hypotheses
elsewhere in `DataDerivationSolve.lean`, not yet threaded into this
specific claim. Left as `curBeforeMonic_natDegree_le_two` (proved, `≤`
only) plus a **flagged, NOT restated as a fresh `sorry`** open question for
whoever next touches this: does `hcur` (`≠ 0`) alone upgrade `≤ 2` to `= 2`,
or does that also need `MatrixNondegenerate`-style input? Not resolved this
pass -- deliberately left unclaimed rather than guessed, since the
`uRS_coeff_ne_zero`/`vRS_coeff_ne_zero` precedent above suggests caution is
warranted before asserting more than what's proved. -/
theorem curBeforeMonic_natDegree_eq_sub (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree =
      (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree - 1 - 1 - 2 := by
  -- **Proved outright this pass** -- the truly mechanical half of the
  -- original Gap 2a target, needing no hypothesis at all. Three monicity
  -- side facts feed `Polynomial.natDegree_divByMonic` three times; the
  -- quadratic's own monicity+degree is closed by `monicity!`/`compute_degree!`
  -- (`Mathlib.Tactic.ComputeDegree`), the standard automation for exactly
  -- this kind of "read off Monic/natDegree from a polynomial's literal
  -- `C`/`X`/`+`/`*` shape" goal, rather than assembled from `degree_add_le`/
  -- `max_lt`/etc. by hand as an earlier draft of this proof attempted (that
  -- draft got stuck needing `Polynomial.Monic.natDegree_eq`-shaped reasoning
  -- whose exact name wasn't confirmed; `compute_degree!` sidesteps needing
  -- that lemma by name at all).
  --
  -- **Heartbeat note**: `K2 p c0 c1 c2 c3 c4` is a reducible `abbrev`
  -- unfolding through two `AdjoinRoot` layers down to `FractionRing
  -- (MvPolynomial (Fin 2) (F p))` (see `DataDerivationTower.lean`).
  -- `monicity!`/`compute_degree!` normalize via `simp`/`norm_num`, which can
  -- get dragged into unfolding that whole tower even though the quadratic's
  -- monicity/degree only needs the AMBIENT ring to be a commutative ring --
  -- the leading coefficient literally is `1`, nothing about `K2`'s specific
  -- construction matters. `generalize` first, so these two tactics run over
  -- a fully opaque `CommRing`/`Field` variable instead of the concrete
  -- tower, then transport the result back along the generalizing equations.
  have hmonic3 : (Polynomial.X ^ 2 +
      Polynomial.C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * Polynomial.X +
      Polynomial.C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) :
      Polynomial (K2 p c0 c1 c2 c3 c4)).Monic := by
    generalize algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1 = a1
    generalize algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0 = a0
    monicity!
  have hdeg3 : (Polynomial.X ^ 2 +
      Polynomial.C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1) * Polynomial.X +
      Polynomial.C (algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0) :
      Polynomial (K2 p c0 c1 c2 c3 c4)).natDegree = 2 := by
    generalize algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u1 = a1
    generalize algebraMap (F p) (K2 p c0 c1 c2 c3 c4) u0 = a0
    compute_degree!
  have hmonic1 : (Polynomial.X - Polynomial.C (anchor1 p c0 c1 c2 c3 c4).1 :
      Polynomial (K2 p c0 c1 c2 c3 c4)).Monic := Polynomial.monic_X_sub_C _
  have hmonic2 : (Polynomial.X - Polynomial.C (anchor2 p c0 c1 c2 c3 c4).1 :
      Polynomial (K2 p c0 c1 c2 c3 c4)).Monic := Polynomial.monic_X_sub_C _
  simp only [curBeforeMonic]
  rw [Polynomial.natDegree_divByMonic _ hmonic3,
      Polynomial.natDegree_divByMonic _ hmonic2,
      Polynomial.natDegree_divByMonic _ hmonic1,
      Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_sub_C, hdeg3]

/-- `Ypoly`'s exact shape, computed directly from `rrBasis5`'s concrete
value: the single `bj = 1` entry is `rrBasis5[3] = (5,0,1)`, so `Ypoly` is
literally the constant `C (coeffsOut ... 3)` (`Fin.mk 3 (by norm_num)`,
`bidx.val = 3` the unique index with `bj = 1`), all other summands `0` by
the `if bj = 1 then ... else 0` guard. Immediate from unfolding `Ypoly`,
`Fin.sum_univ_five`, and `rrBasis5`'s literal value (`rfl`/`decide`-checkable
once `rrBasis5` itself reduces, though `mergeSort` not kernel-reducing --
see `rrBasis5_flag`'s docstring above -- may make this need the same
`List.mem_of_mem_take`/`mergeSort` Prop-level lemmas rather than `decide`
outright). Genuinely new fact, not previously stated anywhere in this
project despite being immediate once `rrBasis5`'s value is written out --
flagged since it corrects the file's own earlier "`Epoly`/`Ypoly`... degree
`≤ 8`-ish" guess (`Ypoly` is degree `≤ 0`, not comparable in size to
`Epoly` at all). -/
theorem Ypoly_natDegree_le_zero (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree ≤ 0 := by
  have hlen : rrBasis5.length = 5 := by
    simp [rrBasis5, rrBasisCandidates, List.length_flatMap]
  have hylt : yIdx < rrBasis5.length := hlen ▸ yIdx_lt_five
  -- `hyidx` is derived BEFORE `set` introduces `yidx5`, so `interval_cases`
  -- can freely case-split and substitute into `yIdx`'s occurrences without
  -- fighting a dependent local definition (`yidx5 := ⟨yIdx, yIdx_lt_five⟩`)
  -- whose own type/proof term mentions `yIdx` -- that ordering is what
  -- caused `generalize`'s "result is not type correct" failure previously:
  -- once `set` folds `⟨yIdx, yIdx_lt_five⟩` into `yidx5` everywhere,
  -- `interval_cases`'s internal `generalize` on bare `yIdx` no longer
  -- type-checks against the now-`yidx5`-mentioning context.
  have hyidx : yIdx = 3 := by
    have hylt5 : yIdx < 5 := hylt.trans_eq hlen
    have hyidxeq := rrBasis5_yIdx_eq
    interval_cases yIdx <;> revert hyidxeq <;> native_decide
  set yidx5 : Fin 5 := ⟨yIdx, yIdx_lt_five⟩ with hyidx5_def
  have hyidx5_three : yidx5 = (⟨3, by norm_num⟩ : Fin 5) := by
    apply Fin.ext
    simpa [yidx5] using hyidx
  -- The sum collapses to the single `bidx = 3` term: every other index
  -- has `bj = 0`. NOT yet available as a standalone upstream fact --
  -- `rrBasis5_yIdx_eq` only pins `rrBasis5`'s VALUE at `yIdx`, not that no
  -- OTHER index also has `bj = 1`. That needs `rrBasis5.countP (bj=1) = 1`
  -- (structurally true -- `bj=1` candidates have order `2i+5 ≥ 5`, and only
  -- one, `(5,0,1)`, has order `≤ 6`, the largest order appearing in
  -- `rrBasis5`'s first-5 window -- but not yet proved in this project; see
  -- `chatgpt_prompt_ypoly_epoly.md`, drafted this pass, for a prompt asking
  -- for this specific missing lemma, named `rrBasis5_bj_one_unique` there).
  -- Left as a named `sorry` bottoming out in that one missing fact, rather
  -- than absorbed silently.
  have hsingle : ∀ bidx : Fin 5, bidx ≠ yidx5 →
      (let (_, _bi, bj) := rrBasis5.getD bidx.val (0, 0, 0)
       if bj = 1 then Polynomial.C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 bidx) *
         (Polynomial.X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ _bi else 0) = 0 := by
    intro bidx hne
    have hcases3 : bidx = (⟨3, by norm_num⟩ : Fin 5) ∨
        (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 1 := by
      fin_cases bidx <;> native_decide
    have hcases : bidx = yidx5 ∨
        (rrBasis5.getD bidx.val (0, 0, 0)).2.2 ≠ 1 := by
      rcases hcases3 with h | h
      · left
        simpa [hyidx5_three] using h
      · exact Or.inr h
    rcases hcases with h | hbj
    · exact False.elim (hne h)
    · dsimp
      rw [if_neg hbj]
  have hcollapse : Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 =
      (let (_, bi, bj) := rrBasis5.getD yidx5.val (0, 0, 0)
       if bj = 1 then Polynomial.C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 yidx5) *
         (Polynomial.X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ bi else 0) := by
    unfold Ypoly
    exact Finset.sum_eq_single yidx5 (fun bidx _ hne => hsingle bidx hne) (fun h => absurd (Finset.mem_univ _) h)
  rw [hcollapse]
  have hval : rrBasis5.getD yidx5.val (0, 0, 0) = (5, 0, 1) := rrBasis5_yIdx_eq
  rw [hval]
  show (Polynomial.C (coeffsOut p c0 c1 c2 c3 c4 u0 u1 v0 v1 yidx5) *
      (Polynomial.X : Polynomial (K2 p c0 c1 c2 c3 c4)) ^ (0 : ℕ)).natDegree ≤ 0
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)







/-- `Epoly`'s degree bound, same style, from `rrBasis5`'s top `bj = 0` entry
`rrBasis5[4] = (6,3,0)`. Unlike `Ypoly_natDegree_le_zero`, `Epoly` does NOT
collapse to a single surviving summand -- all FOUR `bj = 0` indices
(`rrBasis5 = [(0,0,0),(2,1,0),(4,2,0),(5,0,1),(6,3,0)]`, so indices
`0,1,2,4` survive with `bi ∈ {0,1,2,3}`) contribute. The bound instead comes
from `Polynomial.natDegree_sum_le` (`(∑ i ∈ s, f i).natDegree ≤ s.sup (fun i
=> (f i).natDegree)`): each individual summand, whether it's the `bj = 1`
term (killed to `0`, degree `0`) or one of the four `bj = 0` terms
(`C _ * X ^ bi` with `bi ≤ 3`, by the same concrete `rrBasis5` lookup style
as `Ypoly`'s `hsingle`/`hcases3`), has `natDegree ≤ 3` -- so the whole
`Finset.univ.sup` over `Fin 5` is `≤ 3`. No single-survivor lemma
(`rrBasis5_bj_one_unique`) needed at all: bounding every term by the same
constant sidesteps the uniqueness question `Ypoly`'s proof needed. -/
theorem Epoly_natDegree_le_three (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree ≤ 3 := by
  unfold Epoly
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  refine Finset.sup_le (fun bidx _ => ?_)
  simp only [Function.comp_apply]
  have hbi3 : (rrBasis5.getD bidx.val (0, 0, 0)).2.1 ≤ 3 := by
    fin_cases bidx <;> native_decide
  -- `generalize` replaces every occurrence of the (now beta-reduced) term
  -- `rrBasis5.getD bidx.val (0,0,0)` in the goal with a fresh triple `t`,
  -- carrying `hbi3` along via `rw` first so it's stated about the same
  -- fresh variable once destructured -- unlike a bare `obtain` on the raw
  -- term (which introduces `a bi bj` disconnected from the goal, since the
  -- goal's occurrences sit under an unreduced `Function.comp`/lambda).
  revert hbi3
  generalize rrBasis5.getD bidx.val (0, 0, 0) = t
  obtain ⟨a, bi, bj⟩ := t
  intro hbi3
  dsimp only at hbi3 ⊢
  split
  · -- goal: `(C (coeffsOut ... bidx) * X ^ bi).natDegree ≤ 3`, with `hbi3 :
    -- bi ≤ 3` in context. `compute_degree!` handles the `C _ * X ^ bi`
    -- shape generically (same tactic already used for `curBeforeMonic`'s
    -- quadratic above) and discharges the resulting side goal `bi ≤ 3`
    -- from `hbi3` itself.
    compute_degree!
  · simp

/-- `Npoly`'s degree bound, assembled from `Epoly_natDegree_le_three`/
`Ypoly_natDegree_le_zero`/`curvePoly_natDegree` (the last, already fully
proved upstream in `DataDerivationBasics.lean`, transported through
`fAtX := curvePoly.map (algebraMap ...)` via `Polynomial.natDegree_map`-style
reasoning for an injective/field-extension `algebraMap`) via the standard
`natDegree_sub_le`/`natDegree_mul_le`/`natDegree_pow_le` triangle
inequalities -- `Npoly.natDegree ≤ max (2*3) (5 + 2*0) = 6`. -/
theorem Npoly_natDegree_le_six (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    (Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree ≤ 6 := by
  unfold Npoly
  have hE3 := Epoly_natDegree_le_three p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hY0 := Ypoly_natDegree_le_zero p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hf5 : (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree ≤ 5 := by
    unfold fAtX
    exact le_trans Polynomial.natDegree_map_le (le_of_eq (curvePoly_natDegree p c0 c1 c2 c3 c4))
  have hE2 : (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2).natDegree ≤ 6 :=
    le_trans (Polynomial.natDegree_pow_le_of_le 2 hE3) (by norm_num)
  have hY2 : (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2).natDegree ≤ 0 :=
    le_trans (Polynomial.natDegree_pow_le_of_le 2 hY0) (by norm_num)
  have hfY2 : (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
      Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2).natDegree ≤ 6 := by
    -- `natDegree_mul_le : (p * q).natDegree ≤ p.natDegree + q.natDegree`
    -- (standard triangle-inequality form, unconditional -- no `≠ 0`
    -- hypothesis needed since it only claims `≤`, unlike the equality
    -- version `natDegree_mul` which does need nonzero factors).
    have hstep := Polynomial.natDegree_mul_le (p := fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1)
      (q := Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2)
    omega
  exact le_trans
    (Polynomial.natDegree_sub_le (Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2)
      (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1 * Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 ^ 2))
    (max_le hE2 hfY2)

/-- **Assembly.** The honest, unconditional half of the original target:
`curBeforeMonic.natDegree ≤ 2`, no hypothesis needed at all (not even
`hcur`) -- combines `curBeforeMonic_natDegree_eq_sub` (unconditional
equality with `Npoly.natDegree - 4`) and `Npoly_natDegree_le_six` (which
forces `Npoly.natDegree - 1 - 1 - 2 ≤ 6 - 1 - 1 - 2 = 2` since truncated `ℕ`
subtraction is monotone in its first argument). This is as far as this pass
takes Gap 2a; upgrading to equality needs the further genericity condition
flagged above, not attempted here. -/
theorem curBeforeMonic_natDegree_le_two (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p) :
    (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).natDegree ≤ 2 := by
  rw [curBeforeMonic_natDegree_eq_sub]
  have h6 := Npoly_natDegree_le_six p c0 c1 c2 c3 c4 u0 u1 v0 v1
  omega

/-- **Helper for Piece A.** `MvPolynomial.aeval` against a purely-`X`-valued,
injective substitution never kills a nonzero polynomial -- i.e. an injective
renaming (here landing in `Rdec p = MvPolynomial Idx (F p)` rather than
another `MvPolynomial`, matching exactly the shape `baseFracToRing` uses)
is injective on nonzero elements. Proved directly via a left-inverse
`RingHom` built from `Function.invFun tGen`, the same "build a retraction,
apply `MvPolynomial.ringHom_ext`" technique `towerToRdec_spec`'s own
`hcomp` step above already uses (confirmed present, `RingHom`-valued, in
this codebase), rather than an unconfirmed named `rename`/`aeval`
interchange lemma: `Function.invFun tGen` left-inverts `tGen` since `tGen`
is injective, so the composite retraction fixes every `X i` and hence (by
`ringHom_ext`) is the identity on all of `MvPolynomial (Fin 2) (F p)`; a
map that is injective after composing with a retraction is itself
injective, and an injective ring hom out of a nontrivial ring never sends a
nonzero element to `0`. -/
theorem aeval_X_comp_injective_ne_zero {Vars : Type*}
    (tGen : Fin 2 → Vars) (htGen : Function.Injective tGen)
    (q : MvPolynomial (Fin 2) (F p)) (hq : q ≠ 0) :
    MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.X (tGen i) : Fin 2 → MvPolynomial Vars (F p)) q
      ≠ 0 := by
  intro hzero
  apply hq
  let fwd : MvPolynomial (Fin 2) (F p) →+* MvPolynomial Vars (F p) :=
    (MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.X (tGen i) :
      Fin 2 → MvPolynomial Vars (F p))).toRingHom
  let back : MvPolynomial Vars (F p) →+* MvPolynomial (Fin 2) (F p) :=
    (MvPolynomial.aeval (fun j : Vars => MvPolynomial.X (Function.invFun tGen j) :
      Vars → MvPolynomial (Fin 2) (F p))).toRingHom
  have hcomp : back.comp fwd = RingHom.id (MvPolynomial (Fin 2) (F p)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, fwd, back, RingHom.id_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      simp only [MvPolynomial.aeval_C]
      simp
    · intro i
      simp only [RingHom.comp_apply, fwd, back, RingHom.id_apply,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
      rw [Function.leftInverse_invFun htGen i]
  have := congrArg (fun φ => φ q) hcomp
  simp only [RingHom.comp_apply, RingHom.id_apply] at this
  rw [show fwd q = MvPolynomial.aeval
        (fun i : Fin 2 => MvPolynomial.X (tGen i) : Fin 2 → MvPolynomial Vars (F p)) q from rfl,
      hzero] at this
  simpa using this.symm

/-- **Piece A.** `towerToRdec`'s output denominator is nonzero whenever the
input `K2` element is nonzero, for any `SideGens` with INJECTIVE `tGen`/
`wGen` (`aSideGens`/`bSideGens` both qualify, `![a1,a2]`/`![wa1,wa2]` etc.
being visibly injective on the two-element domain `Fin 2`). Pure
denominator-tracking through an already-`sorry`-free recursion -- see the
docstring above `curBeforeMonic_natDegree_eq_two` for the three-level
induction shape (base case: `IsFractionRing.den`'s nonzero-divisor property,
transported by the injective-renaming `aeval`; inductive step, twice:
`den0 * den1 ≠ 0` in a domain from each factor nonzero, `mul_ne_zero`).
The denominator, tracing `towerToRdec`/`towerToRdecK1`/`baseFracToRing`'s
definitions, never actually depends on `wGen` or on `v ≠ 0` -- only the
NUMERATOR does (via the extra `* X (wGen i)` term at each level) -- so
`hwGen`/`hv` are carried as hypotheses (matching this theorem's existing
call sites and interface) but not needed by this particular proof. -/
theorem towerToRdec_den_ne_zero {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars) (htGen : Function.Injective sg.tGen)
    (hwGen : Function.Injective sg.wGen)
    (c0 c1 c2 c3 c4 : F p) (v : K2 p c0 c1 c2 c3 c4) (hv : v ≠ 0) :
    (towerToRdec p sg v).2 ≠ 0 := by
  -- Base case: `baseFracToRing`'s denominator is `aeval (X ∘ tGen)` applied
  -- to `IsFractionRing.den`, which is always a nonzero-divisor (hence
  -- nonzero, `MvPolynomial (Fin 2) (F p)` being a domain), regardless of
  -- which `K0 p` element it came from.
  have hbase_den_ne_zero : ∀ w : K0 p, (baseFracToRing p sg w).2 ≠ 0 := by
    intro w
    have hd_ne_zero : ((IsFractionRing.den (MvPolynomial (Fin 2) (F p)) w : MvPolynomial (Fin 2) (F p)))
        ≠ 0 := by
      have hmem := (IsFractionRing.den (MvPolynomial (Fin 2) (F p)) w).property
      exact nonZeroDivisors.ne_zero hmem
    simpa only [baseFracToRing] using
      aeval_X_comp_injective_ne_zero p sg.tGen htGen _ hd_ne_zero
  -- First inductive step: `towerToRdecK1`'s denominator is `den0 * den1`,
  -- each factor a `baseFracToRing` denominator (living in `MvPolynomial
  -- Vars (F p)`, not `K1`/`K2` -- the multiplication below never leaves
  -- that ring), hence nonzero by the base case; `MvPolynomial Vars (F p)`
  -- has no zero divisors (`F p = ZMod p` is a field for prime `p`), so the
  -- product of two nonzero elements is nonzero.
  have hK1_den_ne_zero : ∀ x : K1 p c0 c1 c2 c3 c4, (towerToRdecK1 p sg x).2 ≠ 0 := by
    intro x
    unfold towerToRdecK1
    dsimp only
    exact mul_ne_zero
      (hbase_den_ne_zero _)
      (hbase_den_ne_zero _)
  -- Second inductive step: `towerToRdec`'s own denominator is `den0 * den1`
  -- from two `towerToRdecK1` calls, nonzero by the same argument one level up.
  unfold towerToRdec
  dsimp only
  exact mul_ne_zero
    (hK1_den_ne_zero _)
    (hK1_den_ne_zero _)

/-- **Gap 2, RESOLVED as false-as-a-theorem — corrected per ChatGPT
consultation (`chatgpt-prompt-denRegular.md`).** The two `theorem`s that
used to sit here (`uRS_coeff_ne_zero`, `vRS_coeff_ne_zero`, claiming each
coefficient is individually nonzero as a CONSEQUENCE of `hcur`/`hgcd`) were
**false as stated** -- per this project's own rule ("if we find a false
theorem, we try to weaken it first"), they are replaced below by an
explicit nondegeneracy HYPOTHESIS rather than an attempted proof.

**The counterexample** (confirmed by ChatGPT, not re-derived independently
here, but the algebra is elementary enough to trust): `uRS := X^2 + 1` is
monic of degree 2 and `Ypoly := 1` gives `IsCoprime Ypoly uRS` trivially
(`1` is a unit), yet `uRS.coeff 1 = 0` -- `hcur`/`hgcd`-shaped hypotheses
say nothing about symmetric-looking or origin-touching Mumford divisors,
which are perfectly legitimate degree-2 divisors. Worse for `vRS`: if the
numerator `-Epoly * gcdA Ypoly uRS` happens to be divisible by `uRS` for
such a `uRS`, `vRS %ₘ uRS = 0` outright, killing BOTH of `vRS`'s
coefficients at once. So no argument from `hcur`/`hgcd` alone -- however
clever -- can close the original statement; it needs a genuinely separate
genericity input about the specific symbolic Mumford divisor `theData`
constructs, not implied by the two well-definedness conditions already in
hand.

**What each individual coefficient actually MEANS**, per ChatGPT, worth
keeping in mind for whoever eventually discharges `Nondegenerate` at a
concrete instantiation: `uRS.coeff 0 = 0 ↔ X ∣ uRS` (`Polynomial.X_dvd_iff`)
-- i.e. one Mumford point sits at `x = 0`; `uRS.coeff 1 = 0` means the
divisor's two `x`-coordinates are negatives of one another. Both are
genuine special loci a generic sample should avoid, not artifacts of a
missing Lean argument.

**Downstream note, per ChatGPT's own suggestion, NOT acted on this pass**:
the four-way `Nondegenerate` bundled below is almost certainly stronger
than what `denRegular`'s actual downstream use (regularity of `Fu`/`Fv` as
generators, `regular_of_linear_elim`'s `d ≠ 0` hypothesis) needs -- e.g. it
may be that only `vRS.natDegree = 1` (equivalent to `vRS.coeff 1 ≠ 0`
alone) is load-bearing and `vRS.coeff 0 ≠ 0` is never used, or that `x ∤
uRS`/`x ∤ vRS` phrased via `X_dvd_iff` is the more natural downstream
hypothesis than raw coefficient-nonvanishing. Left as future-pass work
("inspect exactly what later proof needs the four inequalities") rather
than guessed at now, per instructions to keep this scaffold on paper. -/
structure Nondegenerate (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
      (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1)) : Prop where
  uRS_coeff0_ne_zero : (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 0 ≠ 0
  uRS_coeff1_ne_zero : (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff 1 ≠ 0
  vRS_coeff0_ne_zero : (vRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 hgcd).coeff 0 ≠ 0
  vRS_coeff1_ne_zero : (vRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 hgcd).coeff 1 ≠ 0

/-- Repackaging `Nondegenerate`'s four fields as the `Fin 2`-indexed
statements `uRS_coeff_ne_zero`/`vRS_coeff_ne_zero` used to claim outright
-- same shape `denRegular`'s assembly below wants to consume, now
correctly ASSUMED rather than proved. Trivial `Fin.cases` unfolding, kept
separate from `Nondegenerate` itself so the exceptional-locus CONTENT
(the four named fields, each independently meaningful per the docstring
above) stays legible rather than buried behind a `Fin 2`-quantifier. -/
theorem uRS_coeff_ne_zero (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
      (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1))
    (hnd : Nondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1 hcur hgcd)
    (i : Fin 2) :
    (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).coeff i.val ≠ 0 := by
  fin_cases i
  · exact hnd.uRS_coeff0_ne_zero
  · exact hnd.uRS_coeff1_ne_zero

theorem vRS_coeff_ne_zero (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)
    (hcur : curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 ≠ 0)
    (hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
      (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1))
    (hnd : Nondegenerate p c0 c1 c2 c3 c4 u0 u1 v0 v1 hcur hgcd)
    (i : Fin 2) :
    (vRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 hgcd).coeff i.val ≠ 0 := by
  fin_cases i
  · exact hnd.vRS_coeff0_ne_zero
  · exact hnd.vRS_coeff1_ne_zero

/-- `aSideGens`'s generators are injective — small side fact
`towerToRdec_den_ne_zero`'s hypotheses need, split out so it's a one-line
`decide`/`Fin.cases` discharge rather than repeated inline at each call
site. **This pass: proved outright, per the file's own assessment that
these were "likely provable outright."** `Function.Injective f` for
`f : Fin 2 → Idx` is `∀ a b, f a = f b → a = b` — since `Fin 2` is a
`Fintype` and `Idx` has `DecidableEq` (`deriving DecidableEq`), this whole
statement has a `Decidable` instance (nested `Fintype.decidableForallFintype`)
and `decide` should discharge it by brute enumeration over the 4
`(a,b) : Fin 2 × Fin 2` pairs, reducing on the diagonal (`a = b`, trivial)
and off-diagonal (`a1 ≠ a2` for `tGen`, `wa1 ≠ wb1`-style for `wGen`, each
`decide`-able from distinct `Idx` constructors). **Not independently
verified in a REPL this pass** — `decide` is the right tactic in principle,
but if it times out (unlikely for `Fintype.card = 2`, but `Idx` has 12
constructors so `DecidableEq Idx`'s derived instance does a 12-way case
split per equality test) the mechanical fallback is `intro a b hab;
fin_cases a <;> fin_cases b <;> simp_all` (fully unfolds both `Fin 2`
cases, then `simp`/`Idx`'s injective-constructor lemmas close each of the
4 resulting goals). -/
theorem aSideGens_tGen_injective : Function.Injective (aSideGens).tGen := by
  decide

theorem aSideGens_wGen_injective : Function.Injective (aSideGens).wGen := by
  decide

theorem bSideGens_tGen_injective : Function.Injective (bSideGens).tGen := by
  decide

theorem bSideGens_wGen_injective : Function.Injective (bSideGens).wGen := by
  decide

/-- **Assembly, UPDATED per ChatGPT consultation.** `denRegular` itself,
built from Pieces A and B, now taking TWO further hypotheses
(`hndA`/`hndB : Nondegenerate ...`) that were previously (wrongly) claimed
provable from `hcurA/B`/`hgcdA/B` alone -- see `Nondegenerate`'s docstring
above for the counterexample showing why. `denRegular`'s own conclusion is
UNCHANGED (still "all eight denominators nonzero"), but it is no longer
unconditional given only well-definedness of `theData`: it now genuinely
needs a further exceptional-locus condition per sample, exactly matching
how `hcurA/B`/`hgcdA/B` themselves already work. Every theorem downstream
of `denRegular` (`regularSeq_of_peel_chain`, `decoupledSystem_isRegularSequence`,
`decoupledSystem_zeroDimensional`) will need `hndA`/`hndB` threaded through
too, once this propagates -- **not done yet in this pass**, flagged as the
immediate next step rather than attempted here, since it touches several
signatures and instructions were to keep this pass scoped to `denRegular`
itself. -/
theorem denRegular (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1))
    (hndA : Nondegenerate p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA)
    (hndB : Nondegenerate p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB) :
    let d := theData p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB
    (∀ i, d.u1_den i ≠ 0) ∧ (∀ i, d.u2_den i ≠ 0) ∧
    (∀ i, d.v1_den i ≠ 0) ∧ (∀ i, d.v2_den i ≠ 0) := by
  -- NOTE (unverified, no REPL this pass): `simp only [theData, coeffsToNumDen]`
  -- is used here to unfold `d.u1_den`/etc. down to `towerToRdec`'s raw
  -- `.2` projection, matching the shape `u1_indep`'s already-working proof
  -- above uses (`simp only [aSideGens, coeffsToNumDen, ...]`) rather than a
  -- bare `show`, since `show` needs the two sides syntactically defeq up to
  -- reducible unfolding and `theData`'s record-literal projections may not
  -- reduce that transparently without help. If `simp only` leaves a residual
  -- goal shape mismatch against `towerToRdec_den_ne_zero`'s conclusion,
  -- try `dsimp only [theData, coeffsToNumDen]` instead (definitional-only,
  -- no simp-set surprises) before falling back to `show` + `rfl`-adjacent
  -- massaging.
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · simp only [theData, coeffsToNumDen]
    exact towerToRdec_den_ne_zero p aSideGens aSideGens_tGen_injective
      aSideGens_wGen_injective c0 c1 c2 c3 c4 _
      (uRS_coeff_ne_zero p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA hndA i)
  · simp only [theData, coeffsToNumDen]
    exact towerToRdec_den_ne_zero p bSideGens bSideGens_tGen_injective
      bSideGens_wGen_injective c0 c1 c2 c3 c4 _
      (uRS_coeff_ne_zero p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB hndB i)
  · simp only [theData, coeffsToNumDen]
    exact towerToRdec_den_ne_zero p aSideGens aSideGens_tGen_injective
      aSideGens_wGen_injective c0 c1 c2 c3 c4 _
      (vRS_coeff_ne_zero p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 hcurA hgcdA hndA i)
  · simp only [theData, coeffsToNumDen]
    exact towerToRdec_den_ne_zero p bSideGens bSideGens_tGen_injective
      bSideGens_wGen_injective c0 c1 c2 c3 c4 _
      (vRS_coeff_ne_zero p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 hcurB hgcdB hndB i)

/-- **Assembly placeholder.** Once `curveCoeffRegular`/`denRegular` (and the
still-not-written-down "peel the remaining anchor/target variables in
order, applying `regular_of_linear_elim`/`Polynomial.Monic.isRegular` at
each step" induction they feed into) are filled in, this is where they
compose into the full 12-step peel chain proving
`decoupledSystem_isRegularSequence`. Not attempted this pass -- the
twelve-step induction itself (which variable order, how each step's
"already-imposed ideal is extended from the coefficient ring" hypothesis
is re-verified after the PREVIOUS peel changes the ambient ring) is new
bookkeeping work, not just a corollary of `curveCoeffRegular`/
`denRegular`, and is exactly the "genuinely hard one" §5bis's own ordering
note (step 3) already flags. Deliberately left as a named `sorry` rather
than either attempted in full or silently absorbed into
`decoupledSystem_isRegularSequence` directly, so it is visible as its own
unit of future work. -/
theorem regularSeq_of_peel_chain (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    RingTheory.Sequence.IsRegular (Rdec p)
      (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) := by
  sorry

/-! ## §5bis-0. Variable-peeling infrastructure for the "leading coefficient"
argument

Per ChatGPT consultation (see `chatgpt-prompt-regularsequence.md` and its
reply): the robust version of "monic/nonzero-leading-coefficient in one
variable implies regular element" is NOT "generators of strictly lower
degree in `x`" but the sharper and actually-true statement: if the
already-imposed ideal `I` is *extended from the coefficient ring* (i.e.
`I = Ideal.map C J` for `J` an ideal not involving `x` at all — in our
case, `I`'s generators literally don't mention `x`), then
`MvPolynomial σ R ⧸ I ≃ Polynomial ((MvPolynomial {v // v≠x} R) ⧸ J)`, and
the leading-coefficient argument for `Polynomial.Monic.isRegular` (which
holds over ANY ring, not just domains — Mathlib) applies directly inside
that quotient. This section builds the peeling equivalence and the two
transport lemmas (`isRegular_of_monic_peel` for the monic/curve-relation
case, `isRegular_of_leadingCoeff_regular_peel` for the more general
regular-leading-coefficient case) needed for both the curve relations and
(later, once the closed-form `Fu_cross`/`Fv_cross` polynomials are
available concretely) the cross-generators.

 **Generic version of `peelEquiv`, over any `DecidableEq` variable type
`σ`** (not just `Idx`), so the same peeling construction can be applied a
SECOND time to the coefficient ring `MvPolynomial {v : Idx // v ≠ x} (F p)`
`peelEquiv` itself produces -- needed by `curveCoeffRegular` below, which
peels an anchor variable `a_i` out of that once-already-peeled ring. Same
construction as `peelEquiv`, just with `Idx` generalized to `σ`. -/
noncomputable def peelEquivGen {σ : Type*} [DecidableEq σ] (x : σ) :
    MvPolynomial σ (F p) ≃ₐ[F p] Polynomial (MvPolynomial {v : σ // v ≠ x} (F p)) :=
  (MvPolynomial.renameEquiv (F p)
      (((Equiv.optionSubtype x).symm
          (Equiv.refl {v : σ // v ≠ x})).val.symm : σ ≃ Option {v : σ // v ≠ x})).trans
    (MvPolynomial.optionEquivLeft (F p) {v : σ // v ≠ x})

/-- Peel variable `x : Idx` out of `Rdec p`, landing on
`Polynomial (MvPolynomial {v : Idx // v ≠ x} (F p))` -- the `Idx`-specific
analogue of `MvPolynomial.finSuccEquiv`, built directly from
`MvPolynomial.renameEquiv` (with a hand-built `Idx ≃ Option {v // v ≠ x}`)
composed with `MvPolynomial.optionEquivLeft` (the same combinator already
used successfully in `regular_of_linear_elim` above, applied here to a
concrete finite `σ := Idx` rather than a generic `Option τ`). Now a trivial
specialization of `peelEquivGen` at `σ := Idx` (kept as its own `def`,
rather than inlined at call sites, since `Rdec p` is definitionally
`MvPolynomial Idx (F p)` and callers below already refer to `peelEquiv`
by name). **Does not re-declare `p` in its OWN explicit binder list**
(no literal `(p : ℕ)` written here) -- but since its type mentions `p`
(`Rdec p`, `F p`), Lean auto-includes the ambient section variable `p`
(and its `Fact (Nat.Prime p)`/`Fact (p ≠ 2)` instances, in scope via
`variable` above) as this `def`'s own first explicit argument anyway,
exactly the same mechanism `theData`/`genList` above already rely on
(their own signatures don't write `(p : ℕ)` either, yet every call site
passes `theData p ...`/`genList p ...` explicitly). So the correct call
form is `peelEquiv p x`, matching that convention -- NOT `peelEquiv x`.
An earlier draft mistakenly added a REDUNDANT local `(p : ℕ)` binder
here, which SHADOWED the auto-included section variable with a fresh
`p` carrying no `Fact` instances, causing a "failed to synthesize
instance" error one level down at `peelEquivGen`'s own `F p`; the fix
was removing that redundant binder, not adding one. -/
noncomputable def peelEquiv (x : Idx) :
    Rdec p ≃ₐ[F p] Polynomial (MvPolynomial {v : Idx // v ≠ x} (F p)) :=
  peelEquivGen p x

/-! ### §5bis-0a. The leading-coefficient regularity lemma (Layer 1)

Per ChatGPT consultation (`chatgpt_prompt_regularseq_peel_chain.md`): the
right primitive for turning "regular after peeling" into "regular before
peeling" is NOT two separate lemmas (one for `Monic`, one for the linear
`c - X*d` shape) but a single generic fact about `Polynomial A` for an
arbitrary `CommRing A` (no domain hypothesis) -- `Polynomial.Monic.isRegular`
and the linear case both become one-line corollaries.

ChatGPT's own sketch used `Polynomial.leadingCoeff_mul` (`(p*q).leadingCoeff
= p.leadingCoeff * q.leadingCoeff`) directly, but that lemma needs
`[NoZeroDivisors R]` in Mathlib (confirmed by search: mathlib3/4's
`leadingCoeff_mul` docstring requires it) -- exactly the hypothesis NOT
available for our intermediate quotient rings `A` (a coefficient ring
after peeling some but not all variables need not be a domain, even though
`Rdec p` itself is). So the proof below goes through the definition of
`IsSMulRegular` (injectivity of `c • ·`) and `Polynomial.natDegree_smul_of_smul_regular`/
`Polynomial.leadingCoeff_smul_of_smul_regular` instead, which only need
`IsSMulRegular`, matching exactly what we have to work with.

Proof idea (`f.leadingCoeff` regular ⟹ `f` regular, as an `IsSMulRegular
(Polynomial A) f` statement acting on `Polynomial A` itself via
multiplication): suppose `f * g = 0`. Looking at the top coefficient of
this product, `(f*g).coeff (f.natDegree + g.natDegree) = f.leadingCoeff *
g.coeff g.natDegree = f.leadingCoeff * g.leadingCoeff` (`Polynomial.coeff_mul_degree_add_degree`-
style top-coefficient fact, valid unconditionally, no domain hypothesis --
this is the one piece of `leadingCoeff_mul`-style reasoning that IS true
without `NoZeroDivisors`, since it's about a single specific coefficient of
the product rather than claiming the product's OWN leadingCoeff/natDegree
behaves multiplicatively). So `f.leadingCoeff * g.leadingCoeff = 0`,
and `f.leadingCoeff` regular forces `g.leadingCoeff = 0`. That alone
doesn't yet give `g = 0` (a polynomial can have nilpotent-free zero leading
coefficient and yet be nonzero if its `natDegree` bound understates its
support) -- but combined with induction on `g.natDegree` (peel off the
top term and repeat against the ONE-LOWER-DEGREE remainder, which still
multiplies to `0` against `f` since `f * (g - C g.leadingCoeff * X^g.natDegree)
= f*g - f.leadingCoeff*g.leadingCoeff • X^g.natDegree = 0 - 0 = 0`) this
closes by strong induction on `g.natDegree`. -/

/-- The one coefficient-level fact from `leadingCoeff_mul` that survives
without `NoZeroDivisors`: the TOP coefficient of a product is the product
of the two top coefficients, unconditionally. Standard Mathlib fact
(`Polynomial.coeff_mul_degree_add_degree`), restated here in `natDegree`
form matching how the induction below consumes it. -/
private theorem coeff_natDegree_add_natDegree_mul {A : Type*} [CommRing A]
    (f g : Polynomial A) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.leadingCoeff * g.leadingCoeff :=
  Polynomial.coeff_mul_degree_add_degree f g

/-- **Layer 1, the key transport lemma.** A polynomial with `IsSMulRegular`
leading coefficient is itself `IsSMulRegular` as an element of `Polynomial
A` acting on itself by multiplication -- no domain/`NoZeroDivisors`
hypothesis on `A` needed. Subsumes both the curve relations' `Monic` case
(leading coefficient `1`, trivially regular) and the `Fu`/`Fv` generators'
linear case (leading coefficient `-den`, regular exactly when `den` is,
i.e. `denRegular`'s conclusion) -- a single lemma, matching what ChatGPT's
consultation recommended instead of two separate `isRegular_of_monic_peel`/
`isRegular_of_leadingCoeff_regular_peel` lemmas. -/
theorem Polynomial.isSMulRegular_of_leadingCoeff_isSMulRegular
    {A : Type*} [CommRing A] {f : Polynomial A}
    (hf : IsSMulRegular A f.leadingCoeff) :
    IsSMulRegular (Polynomial A) f := by
  -- `IsSMulRegular (Polynomial A) f` unfolds to injectivity of `f • ·` on
  -- `Polynomial A`; since the action here is by the ring's own
  -- multiplication, this is `Function.Injective (f * ·)`, i.e. `g ↦ f * g`.
  -- No induction needed in the end: `f.leadingCoeff` regular directly
  -- forces `g.leadingCoeff = 0`, and for `g ≠ 0` that alone already
  -- contradicts `g.natDegree ∉ g.eraseLead.support` once `eraseLead g = g`
  -- (which `g.leadingCoeff = 0` gives via `self_sub_C_mul_X_pow`) -- no
  -- degree-peeling recursion is actually required.
  have hmul : ∀ g : Polynomial A, f * g = 0 → g = 0 := by
    intro g hfg
    by_contra hg0
    -- Top coefficient of `f * g` is `f.leadingCoeff * g.leadingCoeff`,
    -- and `f * g = 0` forces it to vanish.
    have htop : f.leadingCoeff * g.leadingCoeff = 0 := by
      have hc := coeff_natDegree_add_natDegree_mul f g
      rw [hfg, Polynomial.coeff_zero] at hc
      exact hc.symm
    -- `f.leadingCoeff` regular ⟹ `g.leadingCoeff = 0`. `IsSMulRegular A c`
    -- unfolds to injectivity of `c • ·`; rephrase `htop` in `•` form (via
    -- `smul_eq_mul`) before applying `hf`, then convert the conclusion
    -- back to `= 0` form.
    have hglc : g.leadingCoeff = 0 := by
      have hsmul : f.leadingCoeff • g.leadingCoeff = f.leadingCoeff • (0 : A) := by
        rw [smul_eq_mul, smul_eq_mul, mul_zero]
        exact htop
      exact hf hsmul
    -- `g.leadingCoeff = 0` forces `g.eraseLead = g` (the peeled-off term
    -- `C g.leadingCoeff * X^g.natDegree` is itself `0`).
    have herase : g.eraseLead = g := by
      have hsub := Polynomial.self_sub_C_mul_X_pow g
      rw [hglc, Polynomial.C_0, zero_mul, sub_zero] at hsub
      exact hsub.symm
    -- But `g.natDegree ∉ g.eraseLead.support` always holds, and combined
    -- with `herase` this says `g.natDegree ∉ g.support`, contradicting
    -- `g ≠ 0` (whose leading coefficient, hence `g.natDegree`-th
    -- coefficient, is nonzero).
    have hmem : g.natDegree ∉ g.eraseLead.support :=
      Polynomial.natDegree_notMem_eraseLead_support
    rw [herase] at hmem
    exact hmem (Polynomial.mem_support_iff.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hg0))
  intro g₁ g₂ hgg
  -- `hgg : f • g₁ = f • g₂`; rewrite `•` as `*`, move to `f * (g₁ - g₂) = 0`,
  -- apply `hmul`, then conclude `g₁ = g₂` from `g₁ - g₂ = 0`.
  have hmul_eq : f * g₁ = f * g₂ := by
    rw [← smul_eq_mul, ← smul_eq_mul]; exact hgg
  have hsub : f * (g₁ - g₂) = 0 := by
    rw [mul_sub, hmul_eq, sub_self]
  have hzero : g₁ - g₂ = 0 := hmul (g₁ - g₂) hsub
  exact sub_eq_zero.mp hzero


/-! ### §5bis-0b. Gap 1: the anchor-variable quintic coefficient is monic

**Real statement, replacing the old `True`-stub.** Each curve relation's
coefficient polynomial (the thing subtracted from `wa_i^2`/`wb_i^2` in
`curveA1`/`curveA2`/`curveB1`/`curveB2`, §3) is, syntactically,
`C c0 + C c1 * X_ai + C c2 * X_ai^2 + C c3 * X_ai^3 + C c4 * X_ai^4 +
X_ai^5` for `X_ai` the anchor variable (`a1`/`a2`/`b1`/`b2` respectively)
-- literally monic of degree 5 in that variable, `c0,...,c4` never
appearing at any power ≥ 5. Stated here as a generic fact about the
abstract quintic shape (`quintic` below), independent of `Idx`/`Rdec`
specifics, then instantiated per anchor variable at call sites. -/

/-- The abstract "quintic with monic top term" shape shared by every curve
relation's coefficient polynomial, over any `CommRing A` -- no domain
hypothesis needed, matching Layer 1's own generality. -/
noncomputable def quintic {A : Type*} [CommRing A] (c0 c1 c2 c3 c4 : A) :
    Polynomial A :=
  Polynomial.C c0 + Polynomial.C c1 * Polynomial.X + Polynomial.C c2 * Polynomial.X ^ 2 +
    Polynomial.C c3 * Polynomial.X ^ 3 + Polynomial.C c4 * Polynomial.X ^ 4 + Polynomial.X ^ 5

/-- `quintic` is `Monic`, over ANY `CommRing A` (no `Nontrivial`/domain
hypothesis needed for `Monic` itself -- unlike pinning down its exact
`natDegree`, which genuinely does need `[Nontrivial A]` since over a
trivial ring `quintic` is the zero polynomial with `natDegree = 0`; `Monic`
alone doesn't need that, it only claims the COEFFICIENT at the tactic's own
computed degree bound is `1`, which holds vacuously/trivially either way).
`monicity!` (`Mathlib.Tactic.ComputeDegree`) is exactly the tactic built for
this shape of goal: converts `Monic f` to `natDegree f ≤ 5` and
`f.coeff 5 = 1`, discharging both automatically from `quintic`'s literal
`C`/`X`/`+`/`^` structure -- the same tactic, on a structurally identical
(quadratic, not quintic) `C`/`X`/`+`/`^` goal, already succeeds elsewhere
in this file (`curBeforeMonic_natDegree_eq_sub`'s `hmonic3`/`hdeg3`, via
`monicity!`/`compute_degree!`), so this is not a blind first use of the
tactic in this codebase. **Not independently re-verified in a REPL this
specific instance (5 terms instead of 3)** -- if `monicity!` alone doesn't
close it, the flagged fallback is `Polynomial.monic_X_pow_add` applied to
`quintic`'s rewritten form `X^5 + (C c0 + C c1*X + C c2*X^2 + C c3*X^3 +
C c4*X^4)` (`add_comm`-rewritten so `X^5` is on the left, matching
`monic_X_pow_add`'s expected shape), discharging its `degree (...) < 5`
side goal via `compute_degree!`/`Polynomial.degree_add_le` chains, same
style as `Epoly_natDegree_le_three` above. -/
theorem quintic_monic {A : Type*} [CommRing A] (c0 c1 c2 c3 c4 : A) :
    (quintic c0 c1 c2 c3 c4).Monic := by
  unfold quintic
  monicity!

omit [Fact (p ≠ 2)] in
/-- **Gap 1, the "shape" half -- proved outright, no `sorry`.** After
peeling `x : Idx` (a `w`-variable, one of `wa1,wa2,wb1,wb2`) via
`peelEquiv p x`, then peeling `anchor` (the MATCHING anchor variable,
`a1/a2/b1/b2` respectively, itself an element of `{v : Idx // v ≠ x}` via
`hne : anchor ≠ x`) out of that coefficient ring via `peelEquivGen`, the
constants `c0,...,c4 : F p` embed into the twice-peeled ring `A` via
`MvPolynomial.C`, and the resulting `quintic` instance
`C c0 + C c1*X + ... + X^5 : Polynomial A` is `Monic` -- immediate from
`quintic_monic` (`A`-generic, no domain hypothesis). This is the
mathematical content Gap 1 needs.

**What this theorem does NOT yet establish** (separate, still-open
obligation, not conflated with the fact above): that `curveA1`/etc.'s
ACTUAL coefficient blob (`C c0 + C c1 * a_i' + C c2 * a_i'^2 + C c3 *
a_i'^3 + C c4 * a_i'^4 + a_i'^5 : Rdec p`, §3's literal definition), pushed
through `(peelEquivGen p (⟨anchor,hne⟩ : {v : Idx // v ≠ x})).toRingEquiv`
composed with `peelEquiv p x`, is DEFINITIONALLY/PROPOSITIONALLY EQUAL to
this `quintic` instance -- i.e. that peeling really does turn the concrete
curve-relation coefficient blob into exactly this shape, rather than some
other rearrangement. That identification is expected to be a short
`simp`/`rename`-unfolding lemma once someone has a REPL (`peelEquivGen`
sends `X (anchor)` to `Polynomial.X` and `C r`/other-variable `X j` to
`Polynomial.C (C_or_X_in_the_smaller_ring)`, matching `optionEquivLeft`'s
known behavior, §5bis-0a's `optionEquivLeft_rename_some`/
`_X_none`-style lemmas above), but is NOT attempted here -- flagged as the
next concrete step, not silently assumed. -/
theorem curveCoeffRegular (x anchor : Idx) (hne : anchor ≠ x)
    (c0 c1 c2 c3 c4 : F p) :
    let B := {v : Idx // v ≠ x}
    let A := MvPolynomial {v : B // v ≠ (⟨anchor, hne⟩ : B)} (F p)
    (quintic (MvPolynomial.C c0 : A) (MvPolynomial.C c1 : A) (MvPolynomial.C c2 : A)
      (MvPolynomial.C c3 : A) (MvPolynomial.C c4 : A)).Monic := by
  -- The goal is headed by two `let`s (`B`, `A`) before the actual `Monic`
  -- statement; `show`/`dsimp only []` (beta/zeta-reducing the `let`s) or
  -- `intro`-style unfolding is needed before `quintic_monic` applies --
  -- `dsimp only` alone should zeta-reduce both `let`s here since they're
  -- not dependent on any bound variable introduced later in the goal.
  dsimp only
  exact quintic_monic _ _ _ _ _

/-! ## §6. The actual target theorems

**These did not exist anywhere in the file before this pass — flagged in
review as the single most important gap: the paper's claim ("this variety
has dimension 0") was never stated as a Lean theorem at all, so it could
not have a `sorry`, `True`-stub, or any other marker of incompleteness.
Both statements below are added now, `sorry`-backed, precisely so that an
audit (`#print axioms`, or just `grep sorry`) reports the true state of the
file instead of reporting a false "complete" signal by omission.

Neither proof is attempted here. The dependency chain each one would
actually need, if attacked, is:
`regular_of_linear_elim` (proved) + `regular_of_norm_eliminate` (`sorry`
above) + `eightVar_finiteQuotient` (`sorry` above) +
`fourVar_finiteQuotient` (`sorry` above) + the wiring roadmap §5 step 5
describes (not attempted, not even stubbed as its own lemma) +
every upstream `sorry` in `TheDataDerivation` that `theData` transitively
depends on (`dvd_N_u`'s hypotheses, `towerToRdec_spec`, the four
`u1_indep`-style fields' correctness — note `u1_indep` etc. themselves ARE
proved, but only establish variable-support, not that `theData`'s numerators/
denominators are the numbers they claim to be). -/

/-- **The paper's actual claim.** `elim2`'s 12-equation decoupled matching
system is a regular sequence of length 12 in the 12-variable ring `Rdec p`,
for `p` and `(c0,...,c4)` satisfying `theData`'s own well-definedness
hypotheses (`hcurA/B`, `hgcdA/B`) — i.e. outside the exceptional locus those
four conditions carve out, with no further exceptional-locus condition
identified or assumed beyond them (roadmap §5 steps 3-4 are exactly where
additional such conditions would need to be discovered and threaded in,
were this theorem actually proved; none has been, since none of the
dependency chain above has been executed). Not proved. -/
theorem decoupledSystem_isRegularSequence (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    RingTheory.Sequence.IsRegular (Rdec p)
      (genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB) :=
  -- Routed through the §5bis-0a scaffold (`regularSeq_of_peel_chain`) rather
  -- than left as its own bare `sorry`, so the dependency on the two named
  -- gaps (`curveCoeffRegular`, `denRegular`) is visible in the proof term
  -- itself, not just in prose. `regularSeq_of_peel_chain` is itself still
  -- `sorry`-backed (the twelve-step peel induction is new bookkeeping not
  -- attempted this pass) -- this wiring changes nothing about what is
  -- proved, only makes the dependency structure explicit.
  regularSeq_of_peel_chain p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB

/-- **The dimension-0 corollary the roadmap's TL;DR promises**, also never
previously stated. Follows formally from
`decoupledSystem_isRegularSequence` once that is proved (a length-`n`
regular sequence in an `n`-variable polynomial ring over a field makes the
quotient a nonzero Artinian, i.e. finite-dimensional, `F p`-algebra) — the
formal step from `IsRegular` to `Module.Finite` is itself not carried out
here either, so this is a second, independent `sorry` on top of the first,
not merely a restatement of it. -/
theorem decoupledSystem_zeroDimensional (c0 c1 c2 c3 c4 : F p) (sa sb : SampleTarget p)
    (hcurA : curBeforeMonic p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1 ≠ 0)
    (hcurB : curBeforeMonic p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1 ≠ 0)
    (hgcdA : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1)
      (uRS p c0 c1 c2 c3 c4 sa.u0 sa.u1 sa.v0 sa.v1))
    (hgcdB : IsCoprime (Ypoly p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)
      (uRS p c0 c1 c2 c3 c4 sb.u0 sb.u1 sb.v0 sb.v1)) :
    Module.Finite (F p) (Rdec p ⧸
      Ideal.span (↑(genList p c0 c1 c2 c3 c4 sa sb hcurA hcurB hgcdA hgcdB).toFinset :
        Set (Rdec p))) := by
  sorry

end DecoupledSystem
end Genus2Lean

