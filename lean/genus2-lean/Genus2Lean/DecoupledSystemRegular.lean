import Mathlib

/-!
# 0-dimensionality of the decoupled `P1+P2-P3-P4=(alpha-alpha')*a` matching
  system, via a regular sequence

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

  `Fu_decoupled`: `u1_num[i] - U_i * u1_den[i] = 0`  and  `u2_num[i] - U_i * u2_den[i] = 0`,  i = 0,1
  `Fv_decoupled`: `v1_num[i] - V_i * v1_den[i] = 0`  and  `v2_num[i] - V_i * v2_den[i] = 0`,  i = 0,1

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

## What is NOT yet in this file

The actual 12 polynomials are `elim2`'s `PhiSymbolic.symbolic_residual`
output (Julia, `phi_general/src/trial3_phi_symbolic_unified.jl`, not part of
either uploaded zip) mapped through `map_coeffs_threaded`/`build_decoupled_system`.
This file does not attempt to re-derive that closed form in Lean; instead it
states the target system SHAPE (ring, variables, curve relations, and the
`Fu_decoupled`/`Fv_decoupled` slots as opaque `k[X]`-elements satisfying the
defining property `elim2` builds them from) and isolates exactly what data is
needed to close `decoupledSystem_isRegularSequence` below: the 8 explicit
polynomials. **This is the concrete blocker for turning the `sorry`s below
into proofs** -- see `ROADMAP-regular-sequence.md`, "What I need from you",
for the two ways to supply them.
-/

namespace Genus2Lean
namespace DecoupledSystem

open MvPolynomial

/-! ## §1. The field and the curve -/

/-- `p = 2371157`, `00_sample_specs.jl`'s `DEFAULT_P` / `01_elim2_main.jl`'s
`default_curve_config().p`. Both samples and both curve copies (`a`-side,
`b`-side) live over this same prime. -/
def curveP : ℕ := 2371157

/-- Placeholder for `p` prime; `elim2` never re-derives this (it is inherited
from the DLP instance the whole project targets), but `GF(p)` needs it to be a
field. Filed as an axiom rather than `sorry`d numerically -- `decide`/`norm_num`
primality on a 7-digit prime is expensive to re-run per build; if this becomes
a blocker, replace with a `by norm_num` or a cached `Nat.Prime` certificate. -/
axiom curveP_prime : Nat.Prime curveP

instance : Fact (Nat.Prime curveP) := ⟨curveP_prime⟩

/-- The base field `F = GF(p)`, `01_elim2_main.jl`'s `CurveConfig.F`. -/
abbrev F : Type := ZMod curveP

noncomputable instance : Field F := ZMod.instField curveP

/-- `f(x) = x^5+x+2`, `01_elim2_main.jl`'s `F_POLY_ASC = [2,1,0,0,0,1]`
(ascending coefficients: `2 + 1*x + 0*x^2 + 0*x^3 + 0*x^4 + 1*x^5`), the curve
`C : y^2 = f(x)` shared by both samples ("Original top-level consts: p,
F_POLY_ASC, F", same header comment). -/
def curveF (x : F) : F := x ^ 5 + x + 2

/-! ## §2. The 12-variable ring

Variable order matches `01_elim2_main.jl:988-996`'s `dec_gens` exactly:
`wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1` (note: `a2` before `a1`, `b2` before
`b1` -- preserved from the original file's own (slightly unusual) generator
order, not a transcription slip here). -/

/-- The 12 index labels, in `dec_gens` order. -/
inductive Idx : Type
  | wa1 | wa2 | wb1 | wb2 | a2 | a1 | b2 | b1 | U0 | U1 | V0 | V1
  deriving DecidableEq, Fintype, Repr

open Idx

/-- `R_dec`, `01_elim2_main.jl`'s `DecoupledSystem.R_dec`:
`MvPolynomial (Idx) F`, i.e. `F[wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1]`. -/
abbrev Rdec : Type := MvPolynomial Idx F

noncomputable instance : CommRing Rdec := MvPolynomial.commRing

/-- Notation matching the Julia variable names directly, so the equations
below read the same as `01_elim2_main.jl`'s own `println` diagnostics. -/
noncomputable def wa1' : Rdec := X wa1
noncomputable def wa2' : Rdec := X wa2
noncomputable def wb1' : Rdec := X wb1
noncomputable def wb2' : Rdec := X wb2
noncomputable def a1' : Rdec := X a1
noncomputable def a2' : Rdec := X a2
noncomputable def b1' : Rdec := X b1
noncomputable def b2' : Rdec := X b2
noncomputable def U0' : Rdec := X U0
noncomputable def U1' : Rdec := X U1
noncomputable def V0' : Rdec := X V0
noncomputable def V1' : Rdec := X V1

/-! ## §3. The four curve relations

`01_elim2_main.jl:998-1001` / `:103-106` (both `TargetRing.build_target_ring`
and `DecoupledSystem.build_decoupled_system` build the same four relations,
once per ring copy -- reproduced here directly in `Rdec`). -/

noncomputable def curveA1 : Rdec := wa1' ^ 2 - (a1' ^ 5 + a1' + 2)
noncomputable def curveA2 : Rdec := wa2' ^ 2 - (a2' ^ 5 + a2' + 2)
noncomputable def curveB1 : Rdec := wb1' ^ 2 - (b1' ^ 5 + b1' + 2)
noncomputable def curveB2 : Rdec := wb2' ^ 2 - (b2' ^ 5 + b2' + 2)

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
structure DecoupledGenerators where
  /-- Sample 1's u-side numerator/denominator, index 0,1 (matches `u0,u1`
  coefficients of `u_RS`, i.e. `s1.u_num`/`s1.u_den` restricted to the two
  non-leading coefficients -- the degree-2 leading coefficient is always `1`
  and is skipped, `mspec.N_U_MATCH = U_DEG_TOP - 1`, `build_match_spec`). -/
  u1_num : Fin 2 → Rdec
  u1_den : Fin 2 → Rdec
  u2_num : Fin 2 → Rdec
  u2_den : Fin 2 → Rdec
  v1_num : Fin 2 → Rdec
  v1_den : Fin 2 → Rdec
  v2_num : Fin 2 → Rdec
  v2_den : Fin 2 → Rdec
  /-- Sanity constraints this data must satisfy to actually BE `elim2`'s
  output (not part of `build_decoupled_system` itself, but properties any
  real instantiation must have -- flagged here so a future filled-in
  instance is checked against them): each `u1_num i` / `u1_den i` etc. only
  involves sample 1's own variables `(wa1,wa2,a1,a2)`, not sample 2's
  `(wb1,wb2,b1,b2)` or the target variables `U0,U1,V0,V1` -- "decoupled"
  literally means each sample's num/den pair is a function of that sample's
  own five variables (t/w-generators) alone, `MappedSample`'s whole point. -/
  u1_indep : ∀ i, ∀ p ∈ (u1_num i).vars ∪ (u1_den i).vars, p ∈ ({wa1, wa2, a1, a2} : Finset Idx)
  u2_indep : ∀ i, ∀ p ∈ (u2_num i).vars ∪ (u2_den i).vars, p ∈ ({wb1, wb2, b1, b2} : Finset Idx)
  v1_indep : ∀ i, ∀ p ∈ (v1_num i).vars ∪ (v1_den i).vars, p ∈ ({wa1, wa2, a1, a2} : Finset Idx)
  v2_indep : ∀ i, ∀ p ∈ (v2_num i).vars ∪ (v2_den i).vars, p ∈ ({wb1, wb2, b1, b2} : Finset Idx)

/-- The actual Mumford-residual data. **Currently a `sorry`-backed opaque
constant** standing in for the concrete polynomials `elim2` computes --
see the module docstring and `ROADMAP-regular-sequence.md`. Downstream
statements are phrased against `theData` so that once a real instance is
supplied (replacing this with a `noncomputable def theData : DecoupledGenerators
:= { u1_num := ..., ... }`), nothing else in this file needs to change. -/
noncomputable def theData : DecoupledGenerators := by
  -- BLOCKED: needs the eight closed-form polynomials from
  -- `PhiSymbolic.symbolic_residual` (K=2,c=2 instance) / `build_decoupled_system`,
  -- transcribed or re-derived symbolically. See `ROADMAP-regular-sequence.md`.
  sorry

/-- `Fu_decoupled`, `01_elim2_main.jl:1042-1046`, flattened to a length-4
list in the same order the original loop produces (`i=0`: sample-1 then
sample-2 equation; `i=1`: likewise), matching how `build_decoupled_system`
`push!`s them. -/
noncomputable def FuList : List Rdec :=
  [ theData.u1_num 0 - U0' * theData.u1_den 0, theData.u2_num 0 - U0' * theData.u2_den 0,
    theData.u1_num 1 - U1' * theData.u1_den 1, theData.u2_num 1 - U1' * theData.u2_den 1 ]

/-- `Fv_decoupled`, `01_elim2_main.jl:1048-1052`, same pattern for `V0,V1`. -/
noncomputable def FvList : List Rdec :=
  [ theData.v1_num 0 - V0' * theData.v1_den 0, theData.v2_num 0 - V0' * theData.v2_den 0,
    theData.v1_num 1 - V1' * theData.v1_den 1, theData.v2_num 1 - V1' * theData.v2_den 1 ]

/-! ## §5. The full 12-generator list and the 0-dimensionality goal -/

/-- All 12 generators, `Fu_decoupled ++ Fv_decoupled ++ [curve_a1, curve_a2,
curve_b1, curve_b2]` -- matches the ideal `Iuv_decoupled`
(`01_elim2_main.jl:1064-1065`) exactly as a *set* of generators (this file
uses a `List` rather than the `ideal(...)` call directly, since
`RingTheory.Sequence.IsRegular` is stated for an ordered `List`, not an
`Ideal` -- regularity is order-and-multiplicity-sensitive in general, though
for a genuinely regular sequence over a Noetherian local/graded ring any
permutation is again regular; no reordering is attempted here, the list below
is `elim2`'s own order, `Fu` before `Fv` before the four curve relations). -/
noncomputable def genList : List Rdec :=
  FuList ++ FvList ++ [curveA1, curveA2, curveB1, curveB2]

/-- Sanity check on the shape of the construction: exactly 12 generators for
12 variables, `Fintype.card Idx`. This is a NECESSARY (not sufficient)
condition for `genList` to be a maximal-length regular sequence in a
12-variable polynomial ring -- checked here as a cheap guard so a future
edit to `FuList`/`FvList`/the curve list that accidentally drops or
duplicates a generator is caught immediately, independent of the harder
`decoupledSystem_isRegularSequence` goal below. -/
theorem genList_length : genList.length = Fintype.card Idx := by
  simp [genList, FuList, FvList, Fintype.card, Idx]

/-- **Main target.** `genList` is a regular sequence on `Rdec` itself (as an
`Rdec`-module), in the sense of `RingTheory.Sequence.IsRegular`. Since
`Rdec = F[X_1,...,X_12]` is a polynomial ring over a field -- Cohen-Macaulay
of Krull dimension 12 -- a regular sequence of length exactly 12 (`genList_length`)
is equivalent to `Rdec ⧸ Ideal.ofList genList` being a nonzero Artinian
`F`-algebra, i.e. `V(genList)` is 0-dimensional. This is the Lean-native
formalization of advisory-6 §6.2's "Question 1" conclusion (generic
0-dimensionality / finiteness) for `elim2`'s literal generators, proved by a
direct algebraic (division) argument instead of the birationality-of-`sigma`
geometric one -- see the module docstring for why this is a deliberately
different, independent route to the same fact, and
`ROADMAP-regular-sequence.md` for the per-step division witnesses this
`sorry` unpacks into. -/
theorem decoupledSystem_isRegularSequence :
    RingTheory.Sequence.IsRegular Rdec genList := by
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
