import Mathlib
import Genus2Lean.ZeroD.SanchorMumfordOrdAt
import Genus2Lean.ZeroD.PrincipalWitnessFinalAssembly

/-! # Connecting `(ua,va)`/`(u,v)` to `CAWitness.lean`'s `uCANew`/`bCA`

**ChatGPT consultation this pass (`CHATGPT-PROMPT-cawitness-uRS4General-bridge.md`
/ its reply): do NOT try to prove `uCANew = uRS4General`.** The two
constructions solve genuinely different interpolation problems (plain
4-point Vandermonde vs. a 7-dim Riemann–Roch/Cramer basis with extra
`ua`/`u` data baked into the LCM denominator) and are not expected to
agree in general — forcing that equality risks proving something false.
`uRS4General`/`curBeforeMonic4General`/`Npoly4` (`Reduce/GeneralSharedRoot.
lean`) are abandoned for the purpose of this theorem, per that
consultation's explicit recommendation (§8: "the safer and cleaner
canonical construction" is `CAWitness.lean`'s single-witness route).

**What this file does instead**: rather than derive the connection from
`hcur`/`hgcd`/`uRS4General`, it takes the identification as a NEW
caller-supplied hypothesis — `ua`/`va` (resp. `u`/`v`, via `sa.
toSampleTarget`) ARE `CAWitness.lean`'s `uCANew`/`-bCA`, built from
`Ra1,Ra2` and `sa.P1,sa.P2`. This is the exact same category of premise
`hMumfordUa`/`hMumfordTarget`/`hAnchorRoots` already are in this
project's convention ("caller supplies the real Mumford data," not a
proof obligation) — ChatGPT's §5/§6 sufficient-condition writeup
(`Y = c ∈ kˣ`, `E = ±c·bCA`) is exactly this shape of hypothesis, just
specialized to `Y = 1`/`c = 1` (`CAWitness.lean`'s `f := y - bCA(x)`
already fixes `Y := 1`), so stating the identification directly as
`ua = uCANew ...` is the honest, minimal version of that sufficient
condition — no separate `E`/`Y`-general argument needed since this
project's construction already lives in the `Y = 1` specialization.

Uses `SanchorMumfordOrdAt.lean`'s `ordAt`-at-a-Mumford-point machinery
(built purely from `IsMumfordUa`/`IsMumfordTarget4`, with NO dependence on
`uCANew`/`bCA` at all) to collapse `divToPair (-va) 1 Sanchor` and
`divToPair (-v) 1 S` down to explicit `single Ra1 + single Ra2` /
`single T1cur + single T2cur` sums — the shape `cAmιTmδmιδ_mem_of_le`
(`PrincipalWitnessFinalAssembly.lean`) needs directly. The `uCANew`/`bCA`
identification described above is what the CALL SITE (this project's next
step: threading `Ra1,Ra2,sa.P1,sa.P2` through `cAmιTmδmιδ_mem_of_le`'s own
`Ra1X,...,P2Y`/`hdet`/`hlead`/etc. parameters) needs to supply — this file
itself only needs `IsMumfordUa`/`IsMumfordTarget4`, not the interpolation
construction directly.

**All nonvanishing/cofactor data below (`Uco`, `hAU`, `hUco_ne`,
`hUco_eval`) is taken as a caller-supplied hypothesis, matching
`ordAt_negVa_one_eq_one_of_mem_Sanchor`'s own signature exactly** — this
file does not attempt to re-derive those from `huafree`/`hf` alone (that
would need `H.f`'s own degree/squarefreeness threaded through in a way
this file does not have on hand); it only composes what
`SanchorMumfordOrdAt.lean` already requires. -/

noncomputable section

open Polynomial
open HyperellipticPolynomial
open HyperellipticPolynomial.Divisor
open Genus2Lean.TheDataDerivation

namespace Genus2Lean
namespace DecoupledSystem

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {H : HyperellipticPolynomial (Genus2Lean.TheDataDerivation.F p)}
  [IsDedekindDomain (CoordinateRing H)]

/-- **Anchor side: `divToPair (-va) 1 Sanchor = single Ra1 + single Ra2`**,
given `Sanchor = {Ra1,Ra2}` (`hSanchorEq`, from `SanchorEqAlphaPoints.lean`'s
`Sanchor_eq_of_anchor_roots`, applied at the call site) and each point's
`ordAt = 1` (`ordAt_negVa_one_eq_one_of_mem_Sanchor`,
`SanchorMumfordOrdAt.lean`). Pure bookkeeping: rewrite `Sanchor` to
`{Ra1,Ra2}`, unfold `divToPair` over the pair (`Finset.sum_pair`), and
discharge each `ordAt` via the cited lemma applied at `Ra1`/`Ra2` in turn. -/
theorem divToPair_negVa_one_Sanchor_eq
    [DecidableEq H.Point]
    (hchar : (2 : Genus2Lean.TheDataDerivation.F p) ≠ 0)
    {c0 c1 c2 c3 c4 ua0 ua1 va0 va1 : Genus2Lean.TheDataDerivation.F p}
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (hMumfordUa : IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1 va0 va1)
    (huafree : Squarefree
      (X ^ 2 + C ua1 * X + C ua0 : Polynomial (Genus2Lean.TheDataDerivation.F p)))
    (va : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hva : va = (C va1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) * X + C va0)
    (Uco : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hAU : pairNorm H (-va) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) =
      (X ^ 2 + C ua1 * X + C ua0) * Uco)
    (hUco_ne : Uco ≠ 0)
    (Ra1 Ra2 : H.Point) (hRa12ne : Ra1 ≠ Ra2)
    (hRa1Y_ne : Ra1.Y ≠ 0) (hRa2Y_ne : Ra2.Y ≠ 0)
    (hRa1Root : (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).IsRoot Ra1.X)
    (hRa2Root : (X ^ 2 + C ua1 * X + C ua0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).IsRoot Ra2.X)
    (hRa1Y : Ra1.Y = va.eval Ra1.X) (hRa2Y : Ra2.Y = va.eval Ra2.X)
    (hUco_evalRa1 : Uco.eval Ra1.X ≠ 0) (hUco_evalRa2 : Uco.eval Ra2.X ≠ 0)
    (Sanchor : Finset H.Point)
    (hSanchorEq : Sanchor = ({Ra1, Ra2} : Finset H.Point)) :
    divToPair (H := H) (-va) 1 Sanchor = single Ra1 + single Ra2 := by
  classical
  have hordRa1 := ordAt_negVa_one_eq_one_of_mem_Sanchor (H := H) hchar hf hMumfordUa huafree
    va hva Uco hAU hUco_ne Ra1 (pointIdeal_ne_bot Ra1) hRa1Y hRa1Y_ne hRa1Root hUco_evalRa1
  have hordRa2 := ordAt_negVa_one_eq_one_of_mem_Sanchor (H := H) hchar hf hMumfordUa huafree
    va hva Uco hAU hUco_ne Ra2 (pointIdeal_ne_bot Ra2) hRa2Y hRa2Y_ne hRa2Root hUco_evalRa2
  rw [hSanchorEq]
  unfold divToPair
  rw [Finset.sum_pair hRa12ne, hordRa1, hordRa2, one_smul, one_smul]

/-- **Target side: `divToPair (-v) 1 S = single T1cur + single T2cur`**,
the `S`-analogue of `divToPair_negVa_one_Sanchor_eq` above. **No separate
lemma needed**: `IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1` unfolds to
literally the same `Prop` shape as `IsMumfordUa p c0 c1 c2 c3 c4 ua0 ua1
va0 va1` (`Reduce/AlphaReduce.lean`, both `(X^2+C_1 X+C_0) ∣ ((C_1'X+C_0')^2
- curvePoly ...)`, differing only in which named variables fill the slots)
— so `ua_dvd_pairNorm_negVa_one`/`ordAt_negVa_one_eq_one_of_mem_Sanchor`
apply verbatim with `ua0 ua1 va0 va1 := u0 u1 v0 v1`, `ua va := u v`,
`hMumfordUa := hMumfordTarget`. This is the same "unfold to the same `Prop`"
move `SanchorEqAlphaPoints.lean`'s own `hSEq` derivation already relies on
(applying `Sanchor_eq_of_anchor_roots` — an anchor-named lemma — directly
to `u`/`v`/`S`/`T1`/`T2` with no target-specific twin). -/
theorem divToPair_negV_one_S_eq
    [DecidableEq H.Point]
    (hchar : (2 : Genus2Lean.TheDataDerivation.F p) ≠ 0)
    {c0 c1 c2 c3 c4 u0 u1 v0 v1 : Genus2Lean.TheDataDerivation.F p}
    (hf : H.f = curvePoly p c0 c1 c2 c3 c4)
    (hMumfordTarget : IsMumfordTarget4 p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (ufree : Squarefree
      (X ^ 2 + C u1 * X + C u0 : Polynomial (Genus2Lean.TheDataDerivation.F p)))
    (v : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hv : v = (C v1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) * X + C v0)
    (Uco : Polynomial (Genus2Lean.TheDataDerivation.F p))
    (hAU : pairNorm H (-v) (1 : Polynomial (Genus2Lean.TheDataDerivation.F p)) =
      (X ^ 2 + C u1 * X + C u0) * Uco)
    (hUco_ne : Uco ≠ 0)
    (T1cur T2cur : H.Point) (hT12ne : T1cur ≠ T2cur)
    (hT1Y_ne : T1cur.Y ≠ 0) (hT2Y_ne : T2cur.Y ≠ 0)
    (hT1Root : (X ^ 2 + C u1 * X + C u0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).IsRoot T1cur.X)
    (hT2Root : (X ^ 2 + C u1 * X + C u0 :
      Polynomial (Genus2Lean.TheDataDerivation.F p)).IsRoot T2cur.X)
    (hT1Y : T1cur.Y = v.eval T1cur.X) (hT2Y : T2cur.Y = v.eval T2cur.X)
    (hUco_evalT1 : Uco.eval T1cur.X ≠ 0) (hUco_evalT2 : Uco.eval T2cur.X ≠ 0)
    (S : Finset H.Point)
    (hSEq : S = ({T1cur, T2cur} : Finset H.Point)) :
    divToPair (H := H) (-v) 1 S = single T1cur + single T2cur := by
  classical
  have hMumfordUa' : IsMumfordUa p c0 c1 c2 c3 c4 u0 u1 v0 v1 := hMumfordTarget
  have hordT1 := ordAt_negVa_one_eq_one_of_mem_Sanchor (H := H) hchar hf hMumfordUa' ufree
    v hv Uco hAU hUco_ne T1cur (pointIdeal_ne_bot T1cur) hT1Y hT1Y_ne hT1Root hUco_evalT1
  have hordT2 := ordAt_negVa_one_eq_one_of_mem_Sanchor (H := H) hchar hf hMumfordUa' ufree
    v hv Uco hAU hUco_ne T2cur (pointIdeal_ne_bot T2cur) hT2Y hT2Y_ne hT2Root hUco_evalT2
  rw [hSEq]
  unfold divToPair
  rw [Finset.sum_pair hT12ne, hordT1, hordT2, one_smul, one_smul]

end DecoupledSystem
end Genus2Lean
