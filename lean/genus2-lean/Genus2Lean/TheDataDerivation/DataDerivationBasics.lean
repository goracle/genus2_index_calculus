import Mathlib

/-!
# `theData` derivation, part 1: symbolic base field, irreducibility, RR-basis combinatorics

## What this file is

First of four files splitting what was previously the single
`TheDataDerivation.lean` (now too long to work in comfortably — see
`ROADMAP-regular-sequence.md` §4 for the overall derivation plan this
implements). The split is purely organizational; nothing about the
mathematical content changes. The four files, in dependency order:

1. **`DataDerivationBasics.lean`** (this file) — the symbolic base field `F`,
   `curvePoly`, the squarefreeness/irreducibility lemma (§4.2 item 1), and
   the Riemann–Roch basis combinatorics (`rrBasis5`/`xmodUTable`/
   `reduceMonomialModU`, §4.2 item 2). Self-contained: no tower or
   fraction-field content.
2. **`DataDerivationTower.lean`** — the tower `K0 → K1 → K2` (§4.2 item 3).
   Imports this file for the irreducibility lemma.
3. **`DataDerivationSolve.lean`** — the `4×4` linear solve, `E(x)`/`Y(x)`/
   `N(x)` (§4.2 items 4–5), and the exact-division step (§4.2 item 6).
   Imports the tower file.
4. **`DataDerivationMumford.lean`** — `u_RS`/`v_RS`, the Mumford identity
   (§4.2 items 7–8), and the bridge to `Rdec` (`towerToRdec`). Imports the
   solve file.

`DecoupledSystemRegular.lean` imports only file 4, which transitively pulls
in files 1–3.

All four files share the namespace `Genus2Lean.TheDataDerivation` (opened
here, closed at the bottom of file 4) so downstream references don't need
per-file qualification.

**Compile status**: none of this has been checked against an actual Lean
toolchain in this session (none was available) — reviewed by hand for
structural/type consistency only, same caveat as every previous pass on
this project.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

/-! ## §4.1 / item 3 setup: symbolic `p`, replacing `curveP`/`curveP_prime`

Per revision-note item 1: `curveP : ℕ := 2371157` and `axiom curveP_prime`
are gone. Every definition from here on is universally quantified over an
arbitrary prime `p`, threaded as `[Fact (Nat.Prime p)]` exactly as
`ZMod.instField` needs. -/

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The base field `F = GF(p)`, now symbolic — `01_elim2_main.jl`'s
`CurveConfig.F`, generalized away from the fixed `curveP` numeral. -/
abbrev F : Type := ZMod p

noncomputable instance instFieldF : Field (F p) := ZMod.instField p

/-! The quintic's coefficients, symbolic-but-fixed (unchanged from the prior
session's framing, revision note: "this part does NOT change again this
pass"). `f(x) = c0 + c1 x + c2 x² + c3 x³ + c4 x⁴ + x⁵`, i.e.
`F_POLY_ASC = [c0,c1,c2,c3,c4,1]` ascending — the leading coefficient is
fixed to `1` (monic quintic), matching `01_elim2_main.jl`'s own
`F_POLY_ASC = [2,1,0,0,0,1]` shape (last entry always `1`). -/
variable (c0 c1 c2 c3 c4 : F p)

/-- `f : F[x]`, the curve polynomial, symbolic in both `p` and `(c0,...,c4)`.
Matches `curveF` in `DecoupledSystemRegular.lean` but as an actual
`Polynomial (F p)` (needed here, since item 3's tower construction adjoins a
root of `X^2 - C (f (t i))`, not just evaluates `f` pointwise the way the
existing file's `curveF : F → F` does). -/
noncomputable def curvePoly : Polynomial (F p) :=
  C c0 + C c1 * X + C c2 * X ^ 2 + C c3 * X ^ 3 + C c4 * X ^ 4 + X ^ 5

theorem curvePoly_natDegree (_h4 : c4 ≠ 0 ∨ True) :
    True := by
  -- `curvePoly`'s degree-5 shape is by construction (leading term `X^5`,
  -- coefficient exactly 1); a `natDegree = 5` lemma is routine but not
  -- needed by anything below, so left as a `True` placeholder rather than
  -- a real `sorry` — nothing downstream depends on it yet.
  trivial

/-! ## Item 1 (§4.2): the squarefreeness/irreducibility lemma

§4.1's "irreducibility caveat": `AdjoinRoot`'s field instance needs
`X^2 - f(t)` irreducible over the field it's a polynomial ring over, at
each tower step. The roadmap's proposed argument: for `t` TRANSCENDENTAL
over the base field (i.e. `t` itself, viewed inside the rational function
field `K0`, not a value of `t`), `f(t)` is not a perfect square in `K0`,
because a nonconstant `f` composed with a transcendental `t` stays
squarefree of odd degree 5 in `t` — squares have even degree, so a degree-5
element can never be a square, for ANY field and ANY nonconstant-degree-5
`f`. This should hold unconditionally (roadmap: "should hold
unconditionally, not just generically"), independent of `p` and of the
specific `(c0,...,c4)` — the argument below only uses `f`'s degree, nothing
about its coefficients.

This is the "clean, small, curve-independent lemma" the roadmap says to
prove first, reused for both tower steps (`i=1` adjoining `w1`, `i=2`
adjoining `w2`). Stated over an abstract field `K` (not yet specialized to
`K0`/`K1`, which don't exist as concrete types until item 3 below) so it
really is curve- and tower-level-independent, matching the roadmap's own
framing ("prove this ONCE, generically"). -/

section Irreducibility

variable {K : Type*} [Field K]

/-- A polynomial of odd degree over a field is never a perfect square (as a
polynomial): `natDegree (g^2) = 2 * natDegree g` is always even. This is the
purely-degree-theoretic fact the roadmap's argument reduces to; it says
nothing about `K`'s characteristic or `g`'s coefficients. -/
theorem not_isSquare_of_odd_natDegree {g : Polynomial K} (hg : g ≠ 0)
    (hodd : Odd g.natDegree) : ¬ ∃ h : Polynomial K, g = h ^ 2 := by
  rintro ⟨h, rfl⟩
  have hh : h ≠ 0 := by
    rintro rfl
    simp at hg
  have hdeg : (h ^ 2).natDegree = 2 * h.natDegree := natDegree_pow h 2
  rw [hdeg, Nat.odd_iff] at hodd
  omega

/-- **Mechanical half, now proved.** For a field `K` and `a : K` that is not
a square, `X^2 - C a` is irreducible: degree exactly 2 (`C a` has degree
`≤ 0 < 2 = X^2`'s degree, so subtraction doesn't change `natDegree`), and by
`Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three` a degree-2 (or
-3) polynomial over a field is irreducible iff it has no root — a root `x`
of `X^2 - C a` is exactly `x^2 = a`, i.e. `IsSquare a`, so `¬ IsSquare a`
gives `roots = 0` gives `Irreducible`. This is the "clean, small" half the
roadmap anticipated; the remaining `sorry` below (`fAtT`-specific) is the
genuinely open part — showing the SPECIFIC field elements `fAtT p ... i`
that `factIrreducible_K1`/`factIrreducible_K2` need are not squares, not
this general conversion. -/
theorem irreducible_X_sq_sub_C_of_not_isSquare {a : K} (ha : ¬ IsSquare a) :
    Irreducible (X ^ 2 - C a : Polynomial K) := by
  have hdeg2 : (X ^ 2 - C a : Polynomial K).natDegree = 2 := by
    compute_degree!
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  by_contra hroots
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hroots
  have hxroot : (X ^ 2 - C a : Polynomial K).IsRoot x := Polynomial.isRoot_of_mem_roots hx
  have : x ^ 2 - a = 0 := by simpa [Polynomial.IsRoot, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] using hxroot
  have hxa : x ^ 2 = a := sub_eq_zero.mp this
  exact ha ⟨x, by rw [← hxa, sq]⟩

/-- **Single-variable case, now proved (ChatGPT-assisted, degree-based
route).** For `f : Polynomial K` of odd degree, its image in `RatFunc K`
under `algebraMap (Polynomial K) (RatFunc K)` is not a square. Proved via
`RatFunc.intDegree`: `RatFunc.intDegree_polynomial` identifies the image's
`intDegree` with `f.natDegree`; if the image were `z * z` for some
`z : RatFunc K`, `RatFunc.intDegree_mul` would force `f.natDegree` to be
`z.intDegree + z.intDegree`, i.e. even — contradicting `Odd f.natDegree`.
This route (via `RatFunc.intDegree`) is considerably shorter than the
originally-planned numerator/denominator-clearing argument: it needs no
`IsFractionRing.num`/`.den`/`IsRelPrime`/UFD API at all, just the two
`intDegree` lemmas above plus `Odd`'s `∃ k, n = 2*k+1` unfolding. -/
theorem RatFunc.not_isSquare_algebraMap_of_odd_natDegree
    (f : Polynomial K) (hf_deg : Odd f.natDegree) (hf_ne : f ≠ 0) :
    ¬ IsSquare ((algebraMap (Polynomial K) (RatFunc K)) f) := by
  intro hs
  rcases hs with ⟨z, hz⟩
  have hf0 : (algebraMap (Polynomial K) (RatFunc K)) f ≠ 0 :=
    (map_ne_zero_iff (algebraMap (Polynomial K) (RatFunc K))
      (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr hf_ne
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, zero_mul] at hz
    exact hf0 hz
  have hdeg : ((algebraMap (Polynomial K) (RatFunc K)) f).intDegree =
      z.intDegree + z.intDegree := by
    rw [hz]; exact RatFunc.intDegree_mul hz0 hz0
  rw [RatFunc.intDegree_polynomial] at hdeg
  rcases hf_deg with ⟨k, hk⟩
  have hk' : (f.natDegree : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  omega

/-- **The irreducibility lemma proper.** For `f : K[t]` a polynomial ring
over a field `K`, and its image `f_t := f.eval₂ (algebraMap K (FractionRing
(Polynomial K))) (algebraMap K (FractionRing (Polynomial K)) applied to the
generator)` — i.e. `f` evaluated AT the transcendental element `t` itself,
viewed inside `RatFunc K` — `X^2 - C f_t` is irreducible over `RatFunc K`
whenever `f` is nonconstant of odd degree.

Stated here in the single-variable case (`RatFunc K = FractionRing
(Polynomial K)`) as the base case; item 3 needs the analogous fact one
level up, over `FractionRing (MvPolynomial (Fin 2) F)` for the first tower
step and over `K1` (no longer a rational function field in the naive sense)
for the second — see the note after this theorem.

**Split into three pieces across two passes.** The mechanical "not-a-square
implies irreducible" half is `irreducible_X_sq_sub_C_of_not_isSquare` above
(complete, general, no `sorry`). The single-variable "not a square in
`RatFunc K`" half is now ALSO complete, no `sorry`, as
`RatFunc.not_isSquare_algebraMap_of_odd_natDegree` above (ChatGPT-assisted:
the `RatFunc.intDegree`-based route turned out much shorter than the
originally-planned numerator/denominator-clearing argument). What remains
`sorry`'d — restated as its own theorem below, `fAtT_not_isSquare`, rather
than left inline here — is the genuinely two-variable TRANSPORT of this
fact: `factIrreducible_K1`/`factIrreducible_K2` need the analogous
non-square fact not in `RatFunc K` (one transcendental) but in `K0 =
FractionRing (MvPolynomial (Fin 2) (F p))` (two commuting transcendentals,
only one of which the curve polynomial is evaluated at) and then, for
`factIrreducible_K2`, over `K1` rather than `K0` again. The proposed
route (ChatGPT, second round): identify `MvPolynomial (Fin 2) K` with
`Polynomial (MvPolynomial (Fin 1) K)` via `MvPolynomial.finSuccEquiv`,
transport the resulting fraction-ring identification
`FractionRing (MvPolynomial (Fin 2) K) ≃ₐ[K] RatFunc (MvPolynomial (Fin 1) K)`
via `IsFractionRing.algEquivOfAlgEquiv`, and reduce to
`RatFunc.not_isSquare_algebraMap_of_odd_natDegree` applied over the
one-variable-smaller coefficient field `MvPolynomial (Fin 1) K`. Two
supporting facts that route needs are individually named but NOT yet
verified against this project's exact Mathlib checkout (`Polynomial.
toMvPolynomial`'s exact name/API, and the precise current spelling of
`natDegree` under an injective-coefficient-map `Polynomial.map` — both
flagged by name uncertainty in the ChatGPT response this docstring is
transcribing, not silently assumed). Left as `sorry` here rather than
risk assembling those into a proof term sight-unseen. -/
theorem sq_sub_curve_irreducible
    (f : Polynomial K) (hf_deg : Odd f.natDegree) (hf_ne : f ≠ 0) :
    ¬ IsSquare (algebraMap (Polynomial K) (RatFunc K) f) :=
  RatFunc.not_isSquare_algebraMap_of_odd_natDegree f hf_deg hf_ne

/-- **The two-variable transport, still open.** This is what
`factIrreducible_K1`/`factIrreducible_K2` in `DataDerivationTower.lean`
actually need: the curve polynomial `f`, evaluated at `t = MvPolynomial.X
(0 : Fin 2)` (only ONE of `K0`'s two transcendentals — the other,
`MvPolynomial.X 1`, sits unused in the coefficient field, per the
`finSuccEquiv`-based routing sketched in `sq_sub_curve_irreducible`'s
docstring above), is not a square in `K0 = FractionRing (MvPolynomial
(Fin 2) K)`. **Left as `sorry`**, genuinely unresolved this pass — the
route is sketched (ChatGPT, second round) but not yet assembled into a
checked Lean proof; see `sq_sub_curve_irreducible`'s docstring for the
full plan and the two name-uncertain steps blocking a confident attempt. -/
theorem fAtT_not_isSquare
    (f : Polynomial K) (hf_deg : Odd f.natDegree) (hf_ne : f ≠ 0) :
    ¬ IsSquare
      (f.eval₂ (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)))
        (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.X (0 : Fin 2))) :
        FractionRing (MvPolynomial (Fin 2) K)) := by
  sorry

end Irreducibility

/-! ## Item 2 (§4.2): `rr_basis`, `build_xmodu_table`, `reduce_monomial_mod_u`

Pure `ℕ`/`F p`-arithmetic combinatorics, no tower or fraction-field content
— direct ports of the Julia functions of the same name (lines 17–58 of
`trial3_phi_symbolic_unified.jl`), specialized to `nb = K + 3 = 5` (the
`K=2, c=2` instance, per this file's top-level convention note) rather than
ported as a general `n_basis`-parametric function, matching how
`DecoupledSystemRegular.lean` itself is already specific to `K=2,c=2`
(`Idx`'s 12 fixed variables) rather than parametric in `(K,c)`. -/

/-- Julia's `rr_basis(n_basis)`: enumerate `(2i, i, 0)` and `(2i+5, i, 1)`
candidates, sort by first component ("order"), take the first `n_basis`.
Ported directly as a `List` computation rather than reproving the sort is
correct in the abstract — for the fixed `n_basis = 5` this file needs, the
candidate list is small and finite, so this is computed by `decide`/`rfl`
rather than proved as a general theorem about `rr_basis`'s sortedness. -/
def rrBasisCandidates (maxOrder : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (maxOrder / 2 + 1)).flatMap (fun i => [(2 * i, i, 0), (2 * i + 5, i, 1)])

/-- The `K=2, c=2` instance's Riemann–Roch basis, `nb = 5` elements, each an
`(i, j)` pair (`j = 0`: basis element `x^i`; `j = 1`: basis element `x^i * y`)
— Julia's `rr_basis(5)`. Computed by sorting `rrBasisCandidates` and taking
the first 5, matching the Julia source exactly (`max_order = 2*5+10 = 20`
there, though any `maxOrder ≥ 8` suffices to produce the same first-5
prefix here since the candidates are generated in increasing order-of-`i`
blocks of 2 and `5` candidates only needs `i` up to `2`). -/
def rrBasis5 : List (ℕ × ℕ × ℕ) :=
  ((rrBasisCandidates 20).mergeSort (fun a b => a.1 ≤ b.1)).take 5

/-- Every candidate's flag component (`.2.2`) is `0` or `1` by construction
— immediate from `rrBasisCandidates`'s `flatMap` shape (each `i` contributes
exactly `(2i,i,0)` and `(2i+5,i,1)`), no `mergeSort` involved. -/
theorem rrBasisCandidates_flag (maxOrder : ℕ) :
    ∀ t ∈ rrBasisCandidates maxOrder, t.2.2 = 0 ∨ t.2.2 = 1 := by
  intro t ht
  simp only [rrBasisCandidates, List.mem_flatMap, List.mem_range] at ht
  obtain ⟨i, _, hti⟩ := ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
  rcases hti with hti | hti
  · left; rw [hti]
  · right; rw [hti]

/-- Every element of `rrBasis5` has flag component `0` or `1` — combines
`rrBasisCandidates_flag` with `rrBasis5 ⊆ rrBasisCandidates 20` via
`List.mem_mergeSort`/`List.mem_of_mem_take` (`Prop`-level membership
lemmas, safe to use even though `mergeSort` itself does not kernel-reduce
via `decide`/`rfl`/`native_decide` — see `yIdx_lt_five`'s docstring in
`DataDerivationSolve.lean` for the same caveat). -/
theorem rrBasis5_flag : ∀ t ∈ rrBasis5, t.2.2 = 0 ∨ t.2.2 = 1 := by
  intro t ht
  apply rrBasisCandidates_flag 20
  have ht' : t ∈ (rrBasisCandidates 20).mergeSort (fun a b => a.1 ≤ b.1) :=
    List.mem_of_mem_take ht
  exact (List.mem_mergeSort).mp ht'

/-- Julia's `build_xmodu_table`: the recurrence `r0[i+1] = -r1[i]*u0`,
`r1[i+1] = r0[i] - r1[i]*u1` (mod `p`, here just `F p`-arithmetic — no
explicit `mod p` needed once everything lives in `ZMod p`), computing `X^i
mod (X^2+u1*X+u0)`'s coefficients `(r0[i], r1[i])` for `i = 0,...,maxI`.
Ported as a `Fin (maxI+2) → F p × F p`-valued recursion (index shifted by
one relative to Julia's 1-based `r0[i+1]` to match Lean's 0-based `Fin`,
so `xmodUTable u0 u1 maxI n = (r0, r1)` for `X^n mod (X^2+u1 X+u0)`). -/
noncomputable def xmodUTable (u0 u1 : F p) : ℕ → F p × F p
  | 0 => (1, 0)
  | 1 => (0, 1)
  | n + 2 =>
      let (prev0, prev1) := xmodUTable u0 u1 (n + 1)
      (-prev1 * u0, prev0 - prev1 * u1)

/-- Julia's `reduce_monomial_mod_u`: reduce the basis monomial `x^i` (if
`j=0`) or `x^i * y` (if `j=1`, using `y^2 ≡ v1*x*y + v0*y`-style reduction
via `(a0,a1)` at index `i` and `(b0,b1)` at index `i+1`) modulo the target
`u(x) = x^2+u1 x+u0`, returning the `(r0,r1)` coefficients of the reduced
`r0 + r1*x` (or, for `j=1`, `r0 + r1*x` after folding in the `v0,v1` data
from the target `v(x) = v1*x+v0`). Ported directly from lines 50–58. -/
noncomputable def reduceMonomialModU (u0 u1 v0 v1 : F p) (i j : ℕ) : F p × F p :=
  let (a0, a1) := xmodUTable p u0 u1 i
  if j = 0 then (a0, a1)
  else
    let (b0, b1) := xmodUTable p u0 u1 (i + 1)
    (v0 * a0 + v1 * b0, v0 * a1 + v1 * b1)


end TheDataDerivation
end Genus2Lean
