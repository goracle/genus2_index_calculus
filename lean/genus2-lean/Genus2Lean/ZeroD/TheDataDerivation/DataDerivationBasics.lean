import Mathlib

set_option linter.style.header false

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

/-- `curvePoly` has `natDegree = 5` unconditionally: the `X^5` term has
coefficient exactly `1` (not symbolic), so its degree can't be cancelled by
any choice of `c0,...,c4` — no leading-coefficient hypothesis needed at all,
unlike a general quintic. This is what the irreducibility argument below
actually needs (`Odd natDegree`), replacing the earlier `True` placeholder
now that item 1's non-square lemma is wired up and depends on it. -/
theorem curvePoly_natDegree : (curvePoly p c0 c1 c2 c3 c4).natDegree = 5 := by
  unfold curvePoly
  compute_degree!

/-- `curvePoly` is nonzero — immediate from `natDegree_natDegree` since a
degree-5 polynomial can't be the zero polynomial (`natDegree 0 = 0 ≠ 5`). -/
theorem curvePoly_ne_zero : curvePoly p c0 c1 c2 c3 c4 ≠ 0 := by
  intro h
  have := curvePoly_natDegree p c0 c1 c2 c3 c4
  rw [h, Polynomial.natDegree_zero] at this
  omega

/-- `curvePoly` has odd degree — the one fact `fAtT_not_isSquare` actually
consumes; stated separately from `curvePoly_natDegree` so call sites don't
need to unfold `Odd` themselves. -/
theorem curvePoly_natDegree_odd : Odd (curvePoly p c0 c1 c2 c3 c4).natDegree := by
  rw [curvePoly_natDegree]
  decide

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

set_option maxHeartbeats 1000000 in
/-- **The two-variable transport, `i = 0` case.** This is what
`factIrreducible_K1` in `DataDerivationTower.lean` actually needs: the
curve polynomial `f`, evaluated at `t = MvPolynomial.X (0 : Fin 2)` (only
ONE of `K0`'s two transcendentals — the other, `MvPolynomial.X 1`, sits
unused, living inside the coefficient ring `A := MvPolynomial (Fin 1) K`
after the `finSuccEquiv`-style identification below), is not a square in
`K0 = FractionRing (MvPolynomial (Fin 2) K)`.

**Route (ChatGPT-assisted, injective-map version, not a full `AlgEquiv`):**
`MvPolynomial.finSuccEquiv K 1 : MvPolynomial (Fin 2) K ≃ₐ[K]
Polynomial (MvPolynomial (Fin 1) K)` sends `X 0 ↦ Polynomial.X` and
`X 1 ↦ Polynomial.C (MvPolynomial.X 0)` (via the confirmed general
unfolding lemma `MvPolynomial.finSuccEquiv_apply`, not the more specific
`_X_zero`/`_X_succ` names, which weren't independently verified against
this checkout). Composing with `Polynomial.map (algebraMap A (FractionRing
A))` and then `algebraMap (Polynomial (FractionRing A)) (RatFunc (FractionRing A))`
gives an INJECTIVE ring hom `φ : MvPolynomial (Fin 2) K →+* RatFunc
(FractionRing A)` (injective as a composite of injective maps: `finSuccEquiv`
is an equiv, `Polynomial.map` of an injective coefficient map is injective
via `Polynomial.map_injective`, and `algebraMap _ (RatFunc _)` is injective
since `FractionRing A` is a domain). `IsLocalization.map` extends `φ` along
`K0 = FractionRing (MvPolynomial (Fin 2) K)` to `Φ : K0 →+* RatFunc
(FractionRing A)`, and `Φ` is injective by
`IsLocalization.injective`-style reasoning applied to the localization at
`nonZeroDivisors`, since `φ` sends `nonZeroDivisors (MvPolynomial (Fin 2) K)`
into `nonZeroDivisors (RatFunc (FractionRing A))` (everything nonzero, as
`RatFunc _` is a field and `φ` is injective, hence maps nonzero to
nonzero). Since `Φ` is injective, `IsSquare` reflects along it: if
`fAtT_0`'s image in `K0` were a square, `Φ` of it would be a square in
`RatFunc (FractionRing A)`; but `Φ (fAtT_0)` computes (via
`Polynomial.eval₂_map` and `finSuccEquiv_apply`'s `X 0 ↦ Polynomial.X`
clause) to exactly `algebraMap (Polynomial (FractionRing A)) (RatFunc
(FractionRing A)) (f.map (algebraMap K (FractionRing A)))` — precisely the
shape `RatFunc.not_isSquare_algebraMap_of_odd_natDegree` rules out, since
mapping `f` along the FIELD homomorphism `algebraMap K (FractionRing A)`
preserves `natDegree` (`Polynomial.natDegree_map_eq_of_injective` — a
field map into a nonzero ring is always injective) and hence oddness. -/
theorem fAtT_not_isSquare
    (f : Polynomial K) (hf_deg : Odd f.natDegree) (hf_ne : f ≠ 0) :
    ¬ IsSquare
      (f.eval₂ (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)))
        (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.X (0 : Fin 2))) :
        FractionRing (MvPolynomial (Fin 2) K)) := by
  let A := MvPolynomial (Fin 1) K
  let K' := FractionRing A
  let T := RatFunc K'
  let B := MvPolynomial (Fin 2) K
  let K0 := FractionRing B

  let e : B ≃ₐ[K] Polynomial A := MvPolynomial.finSuccEquiv K 1
  let cmap : A →+* K' := algebraMap A K'
  have hcmap_inj : Function.Injective cmap := IsFractionRing.injective A K'

  let polyToT : Polynomial A →+* T :=
    (algebraMap (Polynomial K') T).comp (Polynomial.mapRingHom cmap)
  let φ : B →+* T := polyToT.comp e.toRingEquiv.toRingHom
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply e.injective
    apply Polynomial.map_injective cmap hcmap_inj
    apply IsFractionRing.injective (Polynomial K') T
    exact hxy
  let Φ : K0 →+* T := IsFractionRing.lift hφ_inj
  have hΦ_alg : ∀ b : B, Φ (algebraMap B K0 b) = φ b := by
    intro b
    exact IsFractionRing.lift_algebraMap hφ_inj b

  have hΦ_fAtT0 :
      Φ (algebraMap B K0
          (f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2)))) =
      algebraMap (Polynomial K') T (f.map (algebraMap K K')) := by
    rw [hΦ_alg]
    have he_hom :
        e.toRingEquiv.toRingHom.comp
            (Polynomial.eval₂RingHom (algebraMap K B) (MvPolynomial.X (0 : Fin 2))) =
          Polynomial.mapRingHom (algebraMap K A) := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          Polynomial.coe_mapRingHom, Polynomial.map_C]
        exact AlgEquiv.commutes e a
      · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
          RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
          Polynomial.coe_mapRingHom, Polynomial.map_X]
        change (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X 0) = Polynomial.X
        simp [MvPolynomial.finSuccEquiv_apply]
    have he_eval : ∀ g : Polynomial K,
        e (g.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2))) =
          g.map (algebraMap K A) := by
      intro g
      have h := congrArg (fun q => q g) he_hom
      simpa [Polynomial.coe_eval₂RingHom] using h
    have he_eval_f := he_eval f

    show φ (f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2))) = _
    change ((algebraMap (Polynomial K') T).comp (Polynomial.mapRingHom cmap)) (e _) = _
    rw [he_eval_f]
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom]
    rw [Polynomial.map_map]
    have h_comp : cmap.comp (algebraMap K A) = algebraMap K K' := by
      ext x
      exact IsScalarTower.algebraMap_apply K A K' x
    rw [h_comp]

  letI : Field K' := IsFractionRing.toField A
  have h_inj : Function.Injective (algebraMap K K') := RingHom.injective _
  have hf_map_deg : Odd (f.map (algebraMap K K')).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective h_inj]
    exact hf_deg
  have hf_map_ne : f.map (algebraMap K K') ≠ 0 :=
    (Polynomial.map_ne_zero_iff h_inj).mpr hf_ne
  have hnot : ¬ IsSquare (algebraMap (Polynomial K') T (f.map (algebraMap K K'))) :=
    RatFunc.not_isSquare_algebraMap_of_odd_natDegree
      (f.map (algebraMap K K')) hf_map_deg hf_map_ne

  intro hs
  obtain ⟨z, hz⟩ := hs
  apply hnot
  refine ⟨Φ z, ?_⟩
  
  have hz' :
      algebraMap B K0
          (f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2))) =
        z * z := by
    rw [Polynomial.hom_eval₂]
    have h_comp : RingHom.comp (algebraMap B K0) (algebraMap K B) = algebraMap K K0 := by
      ext x
      exact IsScalarTower.algebraMap_apply K B K0 x
    rw [h_comp]
    exact hz

  have hzΦ := congrArg Φ hz'
  rw [map_mul] at hzΦ
  rw [hΦ_fAtT0] at hzΦ
  exact hzΦ

/-- **Generalizing `fAtT_not_isSquare` from `i = 0` to arbitrary `i : Fin 2`.**
`factIrreducible_K1` (Tower file) only needs `i = 0` and gets it directly from
`fAtT_not_isSquare` above with no further work. `factIrreducible_K2` needs
`i = 1` instead (`fAtT p ... 1`, the SECOND tower step's radicand) — this
theorem covers both by swapping the two `MvPolynomial (Fin 2) K` coordinates
via `MvPolynomial.renameEquiv K (Equiv.swap 0 1)`, an ALGEBRA AUTOMORPHISM of
`B := MvPolynomial (Fin 2) K` sending `X 0 ↦ X 1` and `X 1 ↦ X 0`
(`MvPolynomial.rename_X`-style unfolding — swapping which coordinate is
"the polynomial variable" doesn't change whether `f` composed with it is a
square, since the swap is invertible).

**Assembled this pass (renameEquiv-swap route), NOT independently
verified against a toolchain.** The `X 0 ↔ X 1` swap automorphism
`e := MvPolynomial.renameEquiv K (Equiv.swap 0 1) : B ≃ₐ[K] B`
(`B := MvPolynomial (Fin 2) K`) is extended to the fraction field
`K0 := FractionRing B` via `IsFractionRing.fieldEquivOfAlgEquiv`, giving
`E : K0 ≃ₐ[K] K0` with `E ∘ algebraMap B K0 = algebraMap B K0 ∘ e`
(`fieldEquivOfAlgEquiv_algebraMap`). Since `e (X 1) = X 0`
(`MvPolynomial.rename_X` plus `Equiv.swap_apply_right`) and `e` fixes `K`
(it's a `K`-algebra map), `e` carries `f` evaluated at `X 1` to `f`
evaluated at `X 0`; pushing through `algebraMap B K0` and using `E`'s
naturality reduces "`f` at `X 1` is a square in `K0`" to "`f` at `X 0` is
a square in `K0`" (via `E z` witnessing the square on the other side),
closed by the already-proved `fAtT_not_isSquare`. **Flagging explicitly:**
`IsFractionRing.fieldEquivOfAlgEquiv`/`_algebraMap`'s exact implicit-argument
convention (which of its type parameters is the shared base ring vs. the two
sides being compared, and which explicit `Type` arguments are the three
fraction fields) was reconstructed from search-engine doc snippets, not a
live toolchain — this is exactly the kind of routine-but-fiddly
`IsLocalization`/`AlgEquiv` bookkeeping this project's workflow flags for a
ChatGPT-assisted pass if the argument wiring below doesn't elaborate as
written; see `ROADMAP-regular-sequence.md`'s note pointing at this theorem,
and the prompt drafted alongside this pass's notes for exactly this
possibility. -/
theorem fAtT_i_not_isSquare
    (f : Polynomial K) (hf_deg : Odd f.natDegree) (hf_ne : f ≠ 0) (i : Fin 2) :
    ¬ IsSquare
      (f.eval₂ (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)))
        (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.X i)) :
        FractionRing (MvPolynomial (Fin 2) K)) := by
  fin_cases i
  · exact fAtT_not_isSquare f hf_deg hf_ne
  · -- `i = 1` case: transport the `i = 0` case along the `X 0 ↔ X 1` swap
    -- automorphism of `B := MvPolynomial (Fin 2) K`, extended to its
    -- fraction field `K0`. `e` fixes `K` (it's a `K`-algebra automorphism)
    -- and sends `X 1 ↦ X 0`, so it carries `f` evaluated at `X 1` to `f`
    -- evaluated at `X 0` — reducing to the already-proved case via
    -- `IsSquare`'s transport along a ring equivalence (both directions,
    -- since `e`'s extension `E` is its own kind of equivalence).
    -- `fin_cases` leaves the index as a defeq-but-not-syntactically-equal
    -- term (`(fun i ↦ i) ⟨1, ⋯⟩`); `show` first to normalize it to the
    -- literal `(1 : Fin 2)` so the `rw`s below actually find their pattern.
    show ¬ IsSquare
      (f.eval₂ (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)))
        (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.X (1 : Fin 2))) :
        FractionRing (MvPolynomial (Fin 2) K))
    set B := MvPolynomial (Fin 2) K
    set K0 := FractionRing B
    let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
    let e : B ≃ₐ[K] B := MvPolynomial.renameEquiv K swap
    let E : K0 ≃ₐ[K] K0 :=
      IsFractionRing.fieldEquivOfAlgEquiv (A := K) (B := B) (C := B) K K0 K0 e
    have hE_alg : ∀ b : B, E (algebraMap B K0 b) = algebraMap B K0 (e b) :=
      fun b => IsFractionRing.fieldEquivOfAlgEquiv_algebraMap
        (A := K) (B := B) (C := B) K K0 K0 e b
    have he_swap : e (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X (0 : Fin 2) := by
      show MvPolynomial.rename swap (MvPolynomial.X (1 : Fin 2)) = MvPolynomial.X (0 : Fin 2)
      rw [MvPolynomial.rename_X]
      have : swap (1 : Fin 2) = 0 := Equiv.swap_apply_right (0 : Fin 2) (1 : Fin 2)
      rw [this]
    have hEval_e : e (f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2))) =
        f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2)) := by
      have h1 : f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2)) =
          Polynomial.aeval (MvPolynomial.X (1 : Fin 2)) f :=
        (Polynomial.aeval_def (MvPolynomial.X (1 : Fin 2)) f).symm
      have h0 : f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2)) =
          Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) f :=
        (Polynomial.aeval_def (MvPolynomial.X (0 : Fin 2)) f).symm
      rw [h1, h0]
      -- `e.toAlgHom.comp (aeval (X 1))` and `aeval (X 0)` are both algebra
      -- homs `Polynomial K →ₐ[K] B`; they agree at `X` (both send it to
      -- `e (X 1) = X 0` by `he_swap`), so they're equal by
      -- `Polynomial.algHom_ext`. Apply that equality to `f`.
      have hhom : e.toAlgHom.comp (Polynomial.aeval (MvPolynomial.X (1 : Fin 2))) =
          Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) := by
        apply Polynomial.algHom_ext
        show e (Polynomial.aeval (MvPolynomial.X (1 : Fin 2)) Polynomial.X) =
          Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) Polynomial.X
        rw [Polynomial.aeval_X, Polynomial.aeval_X, he_swap]
      have := congrArg (fun φ => φ f) hhom
      simpa using this
    have hE_key :
        E (algebraMap B K0 (f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2)))) =
        algebraMap B K0 (f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2))) := by
      rw [hE_alg, hEval_e]
    have hcast : ∀ (x : B),
        f.eval₂ (algebraMap K K0) (algebraMap B K0 x) =
          algebraMap B K0 (f.eval₂ (algebraMap K B) x) := by
      intro x
      rw [Polynomial.hom_eval₂]
      have h_comp : RingHom.comp (algebraMap B K0) (algebraMap K B) = algebraMap K K0 := by
        ext y
        exact IsScalarTower.algebraMap_apply K B K0 y
      rw [h_comp]
    intro hs
    obtain ⟨z, hz⟩ := hs
    apply fAtT_not_isSquare f hf_deg hf_ne
    refine ⟨E z, ?_⟩
    have hgoal0 : f.eval₂ (algebraMap K K0) (algebraMap B K0 (MvPolynomial.X (0 : Fin 2))) =
        E (f.eval₂ (algebraMap K K0) (algebraMap B K0 (MvPolynomial.X (1 : Fin 2)))) := by
      rw [hcast, hcast, ← hE_key]
    rw [hgoal0, hz, map_mul]

set_option maxHeartbeats 1000000 in
/-- **Product non-square, the fact `factIrreducible_K2` needs.** `f`
evaluated at BOTH transcendentals `X 0` and `X 1` at once — i.e. `fAtT_0 *
fAtT_1` — is not a square in `K0 = FractionRing (MvPolynomial (Fin 2) K)`,
for `f` of odd degree, no further hypothesis on `f`'s coefficients needed
(same unconditional-in-the-coefficients flavor as `fAtT_not_isSquare`
itself). This is the "genuinely two-variable" fact flagged as open in
`factIrreducible_K2_proved`'s docstring in `DataDerivationTower.lean`
(ChatGPT-assisted, second round).

**Route.** Reuses `fAtT_not_isSquare`'s exact transport machinery
(`e := MvPolynomial.finSuccEquiv K 1`, `φ`, `Φ`), but this time tracks
BOTH `e (f.eval₂ ... (X 0))` (`↦ f.map (algebraMap K A)`, as before) and
`e (f.eval₂ ... (X 1))` (`↦ Polynomial.C (f.eval₂ (algebraMap K A) (X 0))`
— since `finSuccEquiv` sends `X 1 ↦ Polynomial.C (X 0 : A)`, evaluating `f`
AT `X 1` becomes evaluating `f` at the CONSTANT `Polynomial.C (X 0 : A)`,
landing entirely inside the coefficient ring `A`, not touching `Polynomial
A`'s own variable). Composing with `Φ`, the product `Φ(fAtT_0) * Φ(fAtT_1)`
becomes `algebraMap (Polynomial A') T (f.map (algebraMap K A'))` times the
CONSTANT `algebraMap A' T (f.eval₂ (algebraMap K A) (X 0) |> algebraMap A A')`
(`A' := FractionRing A`) — a polynomial of odd `natDegree` (`f.map`, by the
same `natDegree_map_eq_of_injective` argument as `fAtT_not_isSquare`) times
a NONZERO constant. `RatFunc.intDegree` is additive under `*` and a nonzero
constant has `intDegree = 0` (`RatFunc.intDegree_C`), so the product still
has ODD `intDegree` — hence still not a square, by the same
`RatFunc.intDegree`-parity argument as the single-transcendental case,
just with an extra even (`= 0`) contribution folded in. The constant
factor's nonvanishing comes from `fAtT_i_not_isSquare` itself (`i = 1`):
if `Φ(fAtT_1)`, i.e. that constant, were `0`, `Φ`'s injectivity would force
`fAtT_1 = 0`, which is trivially a square (`0 = 0^2`), contradicting
`fAtT_i_not_isSquare f hf_deg hf_ne 1`. -/
theorem fAtT_prod_not_isSquare
    (f : Polynomial K) (hf_deg : Odd f.natDegree) (hf_ne : f ≠ 0) :
    ¬ IsSquare
      ((f.eval₂ (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)))
          (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (MvPolynomial.X (0 : Fin 2)))) *
        (f.eval₂ (algebraMap K (FractionRing (MvPolynomial (Fin 2) K)))
          (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (MvPolynomial.X (1 : Fin 2)))) :
        FractionRing (MvPolynomial (Fin 2) K)) := by
  let A := MvPolynomial (Fin 1) K
  let A' := FractionRing A
  let T := RatFunc A'
  let B := MvPolynomial (Fin 2) K
  let K0 := FractionRing B

  let e : B ≃ₐ[K] Polynomial A := MvPolynomial.finSuccEquiv K 1
  let cmap : A →+* A' := algebraMap A A'
  have hcmap_inj : Function.Injective cmap := IsFractionRing.injective A A'

  let polyToT : Polynomial A' →+* T := algebraMap (Polynomial A') T
  let φ : B →+* T := polyToT.comp ((Polynomial.mapRingHom cmap).comp e.toRingEquiv.toRingHom)
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply e.injective
    apply Polynomial.map_injective cmap hcmap_inj
    apply IsFractionRing.injective (Polynomial A') T
    exact hxy
  let Φ : K0 →+* T := IsFractionRing.lift hφ_inj
  have hΦ_alg : ∀ b : B, Φ (algebraMap B K0 b) = φ b := fun b =>
    IsFractionRing.lift_algebraMap hφ_inj b
  -- We only need injectivity of the base map `φ`; `IsFractionRing.lift` is
  -- used below through its defining algebraMap compatibility.
  -- `e (X 0) = X`, `e (X 1) = C (X 0 : A)`.
  have he_X0 : e (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
    simpa only [e] using (MvPolynomial.finSuccEquiv_X_zero (R := K) (n := 1))
  have he_X1 : e (MvPolynomial.X (Fin.succ (0 : Fin 1))) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa only [e] using
      (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1) (j := (0 : Fin 1)))
  have he_X1' : e (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    simpa using he_X1

  have he_eval0 : e (f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2))) =
      f.map (algebraMap K A) := by
    have hhom : e.toAlgHom.comp (Polynomial.aeval (MvPolynomial.X (0 : Fin 2))) =
        Polynomial.aeval (R := K) (A := Polynomial A) Polynomial.X := by
      apply Polynomial.algHom_ext
      show e (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) Polynomial.X) = _
      rw [Polynomial.aeval_X, he_X0, Polynomial.aeval_X]
    have h0 : f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2)) =
        Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) f := (Polynomial.aeval_def _ f).symm
    rw [h0]
    have h := congrArg (fun q => q f) hhom
    calc
      e (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) f) =
          Polynomial.aeval Polynomial.X f := by
            simpa [AlgHom.comp_apply] using h
      _ = f.map (algebraMap K A) := by
        exact Polynomial.aeval_X_left_eq_map f

  have he_eval1 : e (f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2))) =
      Polynomial.C (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))) := by
    have hhom : e.toAlgHom.comp (Polynomial.aeval (MvPolynomial.X (1 : Fin 2))) =
        Polynomial.aeval (Polynomial.C (MvPolynomial.X (0 : Fin 1)) : Polynomial A) := by
      apply Polynomial.algHom_ext
      show e (Polynomial.aeval (MvPolynomial.X (1 : Fin 2)) Polynomial.X) = _
      rw [Polynomial.aeval_X, he_X1', Polynomial.aeval_X]
    have h1 : f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2)) =
        Polynomial.aeval (MvPolynomial.X (1 : Fin 2)) f := (Polynomial.aeval_def _ f).symm
    rw [h1]
    have heq := congrArg (fun q => q f) hhom
    calc
      e (Polynomial.aeval (MvPolynomial.X (1 : Fin 2)) f) =
          Polynomial.aeval (Polynomial.C (MvPolynomial.X (0 : Fin 1)) : Polynomial A) f := by
            simpa [AlgHom.comp_apply] using heq
      _ = Polynomial.C (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))) := by
        rw [Polynomial.aeval_def]
        have hC : (Polynomial.C : A →+* Polynomial A).comp (algebraMap K A) =
            algebraMap K (Polynomial A) := by
          ext x
          simpa using (IsScalarTower.algebraMap_apply K A (Polynomial A) x)
        symm
        rw [Polynomial.hom_eval₂, hC]

  set fAtT0 : K0 :=
      algebraMap B K0 (f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2))) with hfAtT0_def
  set fAtT1 : K0 :=
      algebraMap B K0 (f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2))) with hfAtT1_def

  have hΦ_fAtT0 : Φ fAtT0 = algebraMap (Polynomial A') T (f.map (algebraMap K A')) := by
    rw [hfAtT0_def, hΦ_alg]
    show polyToT (Polynomial.mapRingHom cmap
        (e (f.eval₂ (algebraMap K B) (MvPolynomial.X (0 : Fin 2))))) = _
    rw [he_eval0]
    show algebraMap (Polynomial A') T (Polynomial.map cmap (f.map (algebraMap K A))) = _
    rw [Polynomial.map_map]
    have h_comp : cmap.comp (algebraMap K A) = algebraMap K A' := by
      ext x; exact IsScalarTower.algebraMap_apply K A A' x
    rw [h_comp]

  have hΦ_fAtT1 : Φ fAtT1 =
      algebraMap (Polynomial A') T
        (Polynomial.C (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))))) := by
    rw [hfAtT1_def, hΦ_alg]
    show polyToT (Polynomial.mapRingHom cmap
        (e (f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2))))) = _
    rw [he_eval1]
    show algebraMap (Polynomial A') T
        (Polynomial.map cmap (Polynomial.C (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))))) = _
    rw [Polynomial.map_C]

  letI : Field A' := IsFractionRing.toField A
  have h_inj_KA' : Function.Injective (algebraMap K A') := RingHom.injective _
  have hf_map_deg : Odd (f.map (algebraMap K A')).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective h_inj_KA']
    exact hf_deg
  have hf_map_ne : f.map (algebraMap K A') ≠ 0 :=
    (Polynomial.map_ne_zero_iff h_inj_KA').mpr hf_ne

  have hfAtT1_ne : fAtT1 ≠ 0 := by
    intro h
    have h_eval_zero : f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2)) = 0 := by
      apply IsFractionRing.injective B K0
      simpa [hfAtT1_def] using h
    have h_eval_zero_K0 :
        f.eval₂ (algebraMap K K0)
          (algebraMap B K0 (MvPolynomial.X (1 : Fin 2))) = 0 := by
      have himage :
          algebraMap B K0
              (f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2))) = 0 := by
        simpa using congrArg (algebraMap B K0) h_eval_zero
      have htransport :
          algebraMap B K0
              (f.eval₂ (algebraMap K B) (MvPolynomial.X (1 : Fin 2))) =
            f.eval₂ (algebraMap K K0)
              (algebraMap B K0 (MvPolynomial.X (1 : Fin 2))) := by
        have hcomp :
            (algebraMap B K0).comp (algebraMap K B) = algebraMap K K0 := by
          ext x
          exact IsScalarTower.algebraMap_apply K B K0 x
        have h := Polynomial.hom_eval₂ f (algebraMap K B) (algebraMap B K0)
          (MvPolynomial.X (1 : Fin 2))
        simpa [hcomp] using h
      exact htransport.symm.trans himage
    have hnot := fAtT_i_not_isSquare f hf_deg hf_ne (1 : Fin 2)
    apply hnot
    refine ⟨0, ?_⟩
    simpa [h_eval_zero_K0]

  have hΦfAtT1_ne : Φ fAtT1 ≠ 0 := by
    intro h
    apply hfAtT1_ne
    apply RingHom.injective Φ
    simpa using h

  have hconst_ne : algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))) ≠ 0 := by
    intro h
    apply hΦfAtT1_ne
    calc
      Φ fAtT1 = algebraMap (Polynomial A') T
          (Polynomial.C (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))))) := hΦ_fAtT1
      _ = 0 := by simp [h]

  have hnot_f_map : ¬ IsSquare (algebraMap (Polynomial A') T (f.map (algebraMap K A'))) :=
    RatFunc.not_isSquare_algebraMap_of_odd_natDegree
      (f.map (algebraMap K A')) hf_map_deg hf_map_ne

  have hprod_not : ¬ IsSquare (Φ fAtT0 * Φ fAtT1) := by
    rw [hΦ_fAtT0, hΦ_fAtT1]
    intro hs
    obtain ⟨z, hz⟩ := hs

    have hF_ne :
        algebraMap (Polynomial A') T (f.map (algebraMap K A')) ≠ 0 := by
      exact RatFunc.algebraMap_ne_zero hf_map_ne

    have hC_poly_ne :
        Polynomial.C
          (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1)))) ≠ 0 :=
      (Polynomial.C_ne_zero.mpr hconst_ne)

    have hC_ne :
        algebraMap (Polynomial A') T
            (Polynomial.C
              (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))))) ≠ 0 := by
      exact RatFunc.algebraMap_ne_zero hC_poly_ne

    have hz0 : z ≠ 0 := by
      intro hz'
      rw [hz', zero_mul] at hz
      rcases mul_eq_zero.mp hz with hF | hC
      · exact hnot_f_map ⟨0, by simpa [hF]⟩
      · exact hC_ne hC

    have hdeg :
        ((f.map (algebraMap K A')).natDegree : ℤ) = z.intDegree + z.intDegree := by
      calc
        ((f.map (algebraMap K A')).natDegree : ℤ) =
            (algebraMap (Polynomial A') T (f.map (algebraMap K A'))).intDegree := by
              symm
              exact RatFunc.intDegree_polynomial
        _ = (algebraMap (Polynomial A') T
              (Polynomial.C
                (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))))) *
            algebraMap (Polynomial A') T (f.map (algebraMap K A'))).intDegree := by
              have hCdeg :
                  (algebraMap (Polynomial A') T
                    (Polynomial.C
                      (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1)))))).intDegree = 0 := by
                rw [RatFunc.intDegree_polynomial]
                simp [hconst_ne]
              rw [RatFunc.intDegree_mul hC_ne hF_ne, hCdeg, zero_add]
        _ = (algebraMap (Polynomial A') T (f.map (algebraMap K A')) *
              algebraMap (Polynomial A') T
                (Polynomial.C
                  (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1)))))).intDegree := by
              rw [mul_comm]
        _ = (z * z).intDegree := by
              rw [show
                algebraMap (Polynomial A') T (f.map (algebraMap K A')) *
                    algebraMap (Polynomial A') T
                      (Polynomial.C
                        (algebraMap A A' (f.eval₂ (algebraMap K A) (MvPolynomial.X (0 : Fin 1))))) =
                    z * z by simpa [mul_comm] using hz]
        _ = z.intDegree + z.intDegree := RatFunc.intDegree_mul hz0 hz0

    rcases hf_map_deg with ⟨k, hk⟩
    have hk' : ((f.map (algebraMap K A')).natDegree : ℤ) =
        2 * (k : ℤ) + 1 := by
      exact_mod_cast hk
    omega


  intro hs
  apply hprod_not
  obtain ⟨w, hw⟩ := hs
  refine ⟨Φ w, ?_⟩
  have h_eval0_K0 :
      f.eval₂ (algebraMap K K0)
          (algebraMap B K0 (MvPolynomial.X (0 : Fin 2))) =
        fAtT0 := by
    rw [hfAtT0_def]
    symm
    have htransport := Polynomial.hom_eval₂ f (algebraMap K B)
      (algebraMap B K0) (MvPolynomial.X (0 : Fin 2))
    have hcomp : (algebraMap B K0).comp (algebraMap K B) = algebraMap K K0 := by
      ext x
      exact IsScalarTower.algebraMap_apply K B K0 x
    rw [hcomp] at htransport
    exact htransport
  have h_eval1_K0 :
      f.eval₂ (algebraMap K K0)
          (algebraMap B K0 (MvPolynomial.X (1 : Fin 2))) =
        fAtT1 := by
    rw [hfAtT1_def]
    symm
    have htransport := Polynomial.hom_eval₂ f (algebraMap K B)
      (algebraMap B K0) (MvPolynomial.X (1 : Fin 2))
    have hcomp : (algebraMap B K0).comp (algebraMap K B) = algebraMap K K0 := by
      ext x
      exact IsScalarTower.algebraMap_apply K B K0 x
    rw [hcomp] at htransport
    exact htransport
  have hw' : fAtT0 * fAtT1 = w * w := by
    rw [← h_eval0_K0, ← h_eval1_K0]
    exact hw
  calc Φ fAtT0 * Φ fAtT1 = Φ (fAtT0 * fAtT1) := (map_mul Φ fAtT0 fAtT1).symm
    _ = Φ (w * w) := by rw [hw']
    _ = Φ w * Φ w := map_mul Φ w w

/-- **Quadratic-extension square criterion (ChatGPT-assisted, degree-1-
normal-form route).** For a field `K` of characteristic ≠ 2 and `d : K` a
non-square, `L := AdjoinRoot (X^2 - C d)` is a genuine degree-2 extension
of `K`; this is the standard fact that an element `a : K` becomes a square
in `L` only if `a` or `a*d` was already a square in `K`. Contrapositive
form (the one actually used downstream): if neither `a` nor `a*d` is a
square in `K`, then `algebraMap K L a` is not a square in `L`.

**Proof idea.** Every `z : L` is `AdjoinRoot.mk _ g` for some `g : K[X]`
(`AdjoinRoot.mk_surjective`); replacing `g` by `g %ₘ (X^2 - C d)` doesn't
change `mk _ g` (`AdjoinRoot.mk_eq_mk` plus `modByMonic_add_div`), and the
remainder has `natDegree ≤ 1` (`natDegree_modByMonic_lt`), so by
`Polynomial.exists_eq_X_add_C_of_natDegree_le_one` it has the shape
`C y * X + C x` for some `x y : K` — i.e. every `z : L` is `of x + y • root`
in the more familiar `x + y*w` notation, with `w := AdjoinRoot.root`
satisfying `w^2 = d` (`AdjoinRoot.mk_eq_zero`/`X^2 - C d` vanishing at
`root`). Squaring `x + y*w` and comparing `w`-coefficients (`2xy`, using
`(2:K) ≠ 0` from `hchar`) forces `x = 0 ∨ y = 0`: the `y = 0` case gives
`a = x^2` (contradicting `ha`), the `x = 0` case gives `a = d*y^2`, i.e.
`a*d = (d*y)^2` (contradicting `hda`). Either way, contradiction — so
`algebraMap K L a` cannot be a square. -/
theorem quadratic_extension_square_criterion {K : Type*} [Field K]
    (hchar : (2 : K) ≠ 0) {d a : K} (ha : ¬ IsSquare a) (hda : ¬ IsSquare (a * d)) :
    ¬ IsSquare (algebraMap K (AdjoinRoot (X ^ 2 - C d : Polynomial K)) a) := by
  set L := AdjoinRoot (X ^ 2 - C d : Polynomial K)
  set U : Polynomial K := X ^ 2 - C d with hU_def
  have hU_monic : U.Monic := by
    rw [hU_def]
    have hdeg : (- C d : Polynomial K).degree < (2 : ℕ) := by compute_degree!
    have := Polynomial.monic_X_pow_add (R := K) (n := 2) hdeg
    simpa [sub_eq_add_neg] using this
  have hU_ne_one : U ≠ 1 := by
    intro h
    have hdeg1 : U.natDegree = 0 := by rw [h]; simp
    have hdeg2 : U.natDegree = 2 := by rw [hU_def]; compute_degree!
    omega
  rintro ⟨z, hz⟩
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
  set r := g %ₘ U with hr_def
  have hmk_eq : AdjoinRoot.mk U g = AdjoinRoot.mk U r := by
    symm
    simpa [r, hr_def] using
      (AdjoinRoot.mk_leftInverse hU_monic (AdjoinRoot.mk U g))
  have hr_deg : r.natDegree < 2 := by
    have h := Polynomial.natDegree_modByMonic_lt g hU_monic hU_ne_one
    simpa [r, hU_def] using h
    -- (`hU_def`'s `natDegree` matches the `2` computed by `compute_degree!` above)
  have hr_natDegree_le_one : r.natDegree ≤ 1 := by omega
  obtain ⟨y, x, hxy⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hr_natDegree_le_one
  -- `AdjoinRoot.mk U r = of x + y • root U` in the `C y * X + C x` shape `hxy` gives.
  have hroot_sq : (AdjoinRoot.root U) ^ 2 = AdjoinRoot.of U d := by
    have h0 : AdjoinRoot.mk U U = 0 := AdjoinRoot.mk_self
    have hUexp : U = X ^ 2 - C d := hU_def
    rw [hUexp, map_sub, map_pow] at h0
    have : (AdjoinRoot.mk U X) ^ 2 = AdjoinRoot.mk U (C d) := by
      have := sub_eq_zero.mp h0
      simpa using this
    simpa [AdjoinRoot.mk_X, AdjoinRoot.mk_C] using this
  have hz' : AdjoinRoot.mk U g = AdjoinRoot.of U x + AdjoinRoot.of U y * AdjoinRoot.root U := by
    rw [hmk_eq, hxy]
    show AdjoinRoot.mk U (C y * X + C x) = _
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    ring
  rw [hz'] at hz
  have hexpand :
      (AdjoinRoot.of U x + AdjoinRoot.of U y * AdjoinRoot.root U) *
        (AdjoinRoot.of U x + AdjoinRoot.of U y * AdjoinRoot.root U) =
      AdjoinRoot.of U (x * x + y * y * d) +
        AdjoinRoot.of U (2 * x * y) * AdjoinRoot.root U := by
    have h0 :
        (AdjoinRoot.of U x + AdjoinRoot.of U y * AdjoinRoot.root U) *
          (AdjoinRoot.of U x + AdjoinRoot.of U y * AdjoinRoot.root U) =
        AdjoinRoot.of U x * AdjoinRoot.of U x +
          AdjoinRoot.of U x * AdjoinRoot.of U y * AdjoinRoot.root U +
          AdjoinRoot.of U y * AdjoinRoot.of U x * AdjoinRoot.root U +
          AdjoinRoot.of U y * AdjoinRoot.of U y * (AdjoinRoot.root U) ^ 2 := by
      ring
    rw [h0, hroot_sq]
    have hxx : AdjoinRoot.of U x * AdjoinRoot.of U x = AdjoinRoot.of U (x * x) := by
      simpa using (map_mul (AdjoinRoot.of U) x x).symm
    have hyy :
        AdjoinRoot.of U y * AdjoinRoot.of U y * AdjoinRoot.of U d =
          AdjoinRoot.of U (y * y * d) := by
      calc
        AdjoinRoot.of U y * AdjoinRoot.of U y * AdjoinRoot.of U d =
            AdjoinRoot.of U (y * y) * AdjoinRoot.of U d := by
              rw [← map_mul]
        _ = AdjoinRoot.of U (y * y * d) := by
              rw [← map_mul]
    have hxy' :
        AdjoinRoot.of U x * AdjoinRoot.of U y +
            AdjoinRoot.of U y * AdjoinRoot.of U x =
          AdjoinRoot.of U (2 * x * y) := by
      calc
        AdjoinRoot.of U x * AdjoinRoot.of U y +
            AdjoinRoot.of U y * AdjoinRoot.of U x =
            AdjoinRoot.of U (x * y) + AdjoinRoot.of U (y * x) := by
              rw [map_mul, map_mul]
        _ = AdjoinRoot.of U (x * y + y * x) := by
              rw [map_add]
        _ = AdjoinRoot.of U (2 * x * y) := by
              congr 1
              ring
    rw [hxx, hyy]
    calc
      AdjoinRoot.of U (x * x) +
          AdjoinRoot.of U x * AdjoinRoot.of U y * AdjoinRoot.root U +
          AdjoinRoot.of U y * AdjoinRoot.of U x * AdjoinRoot.root U +
          AdjoinRoot.of U (y * y * d) =
          AdjoinRoot.of U (x * x) +
            (AdjoinRoot.of U x * AdjoinRoot.of U y +
              AdjoinRoot.of U y * AdjoinRoot.of U x) * AdjoinRoot.root U +
            AdjoinRoot.of U (y * y * d) := by ring
      _ = AdjoinRoot.of U (x * x) +
            AdjoinRoot.of U (2 * x * y) * AdjoinRoot.root U +
            AdjoinRoot.of U (y * y * d) := by rw [hxy']
      _ = (AdjoinRoot.of U (x * x) + AdjoinRoot.of U (y * y * d)) +
            AdjoinRoot.of U (2 * x * y) * AdjoinRoot.root U := by ring
      _ = AdjoinRoot.of U (x * x + y * y * d) +
            AdjoinRoot.of U (2 * x * y) * AdjoinRoot.root U := by
            rw [map_add]
  rw [hexpand] at hz
  -- `algebraMap K L a = AdjoinRoot.of U a` (`AdjoinRoot.algebraMap_eq`).
  have haL : algebraMap K L a = AdjoinRoot.of U a := by
    rw [show (algebraMap K L : K →+* L) = AdjoinRoot.of U from AdjoinRoot.algebraMap_eq U]
  rw [haL] at hz
  -- Compare `{1, root U}`-coordinates: `of` is injective (`U` monic, `natDegree ≥ 1`), and
  -- `1, root U` are `K`-linearly independent, so `hz` forces `a = x*x + y*y*d` (the `1`
  -- coefficient) AND `2*x*y = 0` (the `root`-coefficient) simultaneously. Rather than build
  -- general linear-independence machinery, extract both facts directly via `AdjoinRoot.mk`'s
  -- degree-≤1 normal form: apply `AdjoinRoot.mk_eq_mk`-style reasoning to `hz` restated as an
  -- equality of `mk U` images of two degree-≤1 polynomials.
  have hz_mk : AdjoinRoot.mk U (C a) =
      AdjoinRoot.mk U (C (x * x + y * y * d) + C (2 * x * y) * X) := by
    have hLHS : AdjoinRoot.of U a = AdjoinRoot.mk U (C a) := AdjoinRoot.mk_C a
    have hRHS : AdjoinRoot.of U (x * x + y * y * d) +
        AdjoinRoot.of U (2 * x * y) * AdjoinRoot.root U =
        AdjoinRoot.mk U (C (x * x + y * y * d) + C (2 * x * y) * X) := by
      calc
        AdjoinRoot.of U (x * x + y * y * d) +
            AdjoinRoot.of U (2 * x * y) * AdjoinRoot.root U =
            AdjoinRoot.mk U (C (x * x + y * y * d)) +
              AdjoinRoot.mk U (C (2 * x * y)) * AdjoinRoot.mk U X := by
                rw [AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk U (C (x * x + y * y * d) + C (2 * x * y) * X) := by
              calc
                AdjoinRoot.mk U (C (x * x + y * y * d)) +
                    AdjoinRoot.mk U (C (2 * x * y)) * AdjoinRoot.mk U X =
                    AdjoinRoot.mk U (C (x * x + y * y * d)) +
                      AdjoinRoot.mk U (C (2 * x * y) * X) := by rw [← map_mul]
                _ = AdjoinRoot.mk U
                    (C (x * x + y * y * d) + C (2 * x * y) * X) := by
                    rw [← map_add]
    rw [← hLHS, ← hRHS]
    exact hz
  rw [AdjoinRoot.mk_eq_mk] at hz_mk
  -- `U ∣ (C a - (C (x*x+y*y*d) + C (2xy) * X))`; the divisor has `natDegree < 2 = U.natDegree`
  -- unless it's zero (`Monic.not_dvd_of_natDegree_lt`), so it must be `0`, giving both
  -- coefficient equalities by `Polynomial.ext_iff` at degrees `0` and `1`.
  have hcoeff_diff_zero :
      (C a - (C (x * x + y * y * d) + C (2 * x * y) * X) : Polynomial K) = 0 := by
    by_contra hne
    have hdeg_lt : (C a - (C (x * x + y * y * d) + C (2 * x * y) * X) :
        Polynomial K).natDegree < U.natDegree := by
      have hb : (C a - (C (x * x + y * y * d) + C (2 * x * y) * X) :
          Polynomial K).natDegree ≤ 1 := by compute_degree!
      have hUd2 : U.natDegree = 2 := by rw [hU_def]; compute_degree!
      omega
    exact (hU_monic.not_dvd_of_natDegree_lt hne hdeg_lt) hz_mk
  have hcoeff0 : a = x * x + y * y * d := by
    have h0 := congrArg (fun p => Polynomial.coeff p 0) hcoeff_diff_zero
    exact sub_eq_zero.mp (by simpa using h0)
  have hcoeff1 : (2 : K) * x * y = 0 := by
    have h1 := congrArg (fun p => Polynomial.coeff p 1) hcoeff_diff_zero
    simpa using h1
  have hxy0 : x = 0 ∨ y = 0 := by
    rcases mul_eq_zero.mp hcoeff1 with h | h
    · rcases mul_eq_zero.mp h with h2 | hx
      · exact absurd h2 hchar
      · left; exact hx
    · right; exact h
  rcases hxy0 with hx0 | hy0
  · apply hda
    refine ⟨d * y, ?_⟩
    rw [hcoeff0, hx0]
    ring
  · apply ha
    refine ⟨x, ?_⟩
    rw [hcoeff0, hy0]
    ring

end Irreducibility

/-- **Bridge from `fAtT_i_not_isSquare`'s statement shape to `curvePoly`'s
own `eval₂`.** `fAtT_i_not_isSquare` is stated for an abstract `f : Polynomial
K` composed with `eval₂ (algebraMap K _) (algebraMap _ _ (X i))` — i.e.
`eval₂` straight into the base field `K`, then pushed into `FractionRing
(MvPolynomial (Fin 2) K)` by `algebraMap`. Tower.lean's actual `fAtT` (in
`DataDerivationTower.lean`) is `Polynomial.eval₂ (algebraMap (F p) (K0 p))
(t0 p i) (curvePoly ...)` — `eval₂` directly into `K0 p`, using `t0 p i`
(already an element of `K0 p`, defined as `algebraMap (MvPolynomial (Fin 2)
(F p)) (K0 p) (MvPolynomial.X i)`) as the evaluation point, not as a
two-step composition. This lemma shows the two are literally the same
element, via `Polynomial.eval₂_at_apply`-style naturality: evaluating first
into the small ring then mapping equals mapping the base ring hom through
and evaluating directly, whenever the evaluation point itself factors as
`(map) ∘ (generator)` — which `t0 p i`'s own definition already is. Purely
mechanical (`Polynomial.hom_eval₂` plus unfolding `t0`), no new mathematics,
same style as `hΦ_fAtT0` above. -/
theorem curvePoly_eval_eq_fAtT_shape (i : Fin 2) :
    (curvePoly p c0 c1 c2 c3 c4).eval₂
        (algebraMap (F p) (FractionRing (MvPolynomial (Fin 2) (F p))))
        (algebraMap (MvPolynomial (Fin 2) (F p))
          (FractionRing (MvPolynomial (Fin 2) (F p))) (MvPolynomial.X i)) =
      Polynomial.eval₂ (algebraMap (F p) (FractionRing (MvPolynomial (Fin 2) (F p))))
        (algebraMap (MvPolynomial (Fin 2) (F p)) (FractionRing (MvPolynomial (Fin 2) (F p)))
          (MvPolynomial.X i))
        (curvePoly p c0 c1 c2 c3 c4) := rfl

/-- **The instance Tower.lean actually needs**: `curvePoly` evaluated at
`t0 p i` inside `K0 p` is not a square, for either `i`. Assembles
`fAtT_i_not_isSquare` (`K := F p`, `f := curvePoly p ...`) with
`curvePoly_natDegree_odd`/`curvePoly_ne_zero` above. This is the theorem
`factIrreducible_K1`/`factIrreducible_K2` in `DataDerivationTower.lean`
should invoke instead of their current bare `axiom`s — see that file. -/
theorem fAtT_p_not_isSquare (i : Fin 2) :
    ¬ IsSquare
      ((curvePoly p c0 c1 c2 c3 c4).eval₂
        (algebraMap (F p) (FractionRing (MvPolynomial (Fin 2) (F p))))
        (algebraMap (MvPolynomial (Fin 2) (F p))
          (FractionRing (MvPolynomial (Fin 2) (F p))) (MvPolynomial.X i))) :=
  fAtT_i_not_isSquare (curvePoly p c0 c1 c2 c3 c4)
    (curvePoly_natDegree_odd p c0 c1 c2 c3 c4) (curvePoly_ne_zero p c0 c1 c2 c3 c4) i

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

/-! ## `xmodUTable` correctness

`xmodUTable` is *intended* to compute the coefficients of `X^n mod
(X^2+u1*X+u0)`. This was never proved anywhere — `dvd_N_u` (item 6's last
remaining gap, `DataDerivationSolve.lean`) needs it. Proved here, over
`F p` directly (not yet promoted into any tower field `K2`; that promotion,
via `Polynomial.map` and `Monic.map`, happens where it's actually needed
downstream). -/

section XModUCorrect

variable (u0 u1 : F p)

/-- The divisor `X^2 + C u1 * X + C u0` is monic — via `Polynomial.
monic_X_pow_add` (`(X^n + q).Monic` from `q.degree < n`), applied with
`n = 2`, `q = C u1 * X + C u0`. The degree bound itself is closed by the
`compute_degree!` tactic (`Mathlib.Tactic.ComputeDegree`), which is built
exactly for `degree f ≤/< d` goals and avoids hand-picking individual
`degree_add_le`/`degree_mul_le`/`degree_C_le`/`degree_X_le`-style lemma
names. -/
theorem uPoly_monic : (X ^ 2 + C u1 * X + C u0 : Polynomial (F p)).Monic := by
  have hdeg : (C u1 * X + C u0 : Polynomial (F p)).degree < (2 : ℕ) := by
    compute_degree!
  have := Polynomial.monic_X_pow_add (R := F p) (n := 2) hdeg
  simpa [add_assoc] using this

/-- `xmodUTable u0 u1 n`'s two components are exactly the coefficients of
`X^n mod (X^2+u1*X+u0)` — the correctness fact `dvd_N_u` needs.

Proved by strong induction on `n` in steps of `2` (matching `xmodUTable`'s
own recursive shape): the `n+2` case reduces `X^(n+2) %ₘ U` to `X *
(X^(n+1) %ₘ U) %ₘ U` via `modByMonic_eq_of_dvd_sub` (since their difference
`X^(n+2) - X*(X^(n+1)%ₘU) = X*(X^(n+1) - X^(n+1)%ₘU)` is `X` times a
multiple of `U`, by `modByMonic_add_div`), then substitutes the IH and
reduces the resulting degree-≤1 polynomial `X*(C a+C b*X)` against `U`
directly (its remainder, after subtracting `C b * U`, is again degree ≤ 1
so equals its own `%ₘ U` by `modByMonic_eq_self_iff`). All degree bounds
below are closed by `compute_degree!`. -/
theorem xmodUTable_correct (n : ℕ) :
    (X ^ n : Polynomial (F p)) %ₘ (X ^ 2 + C u1 * X + C u0) =
      C (xmodUTable p u0 u1 n).1 + C (xmodUTable p u0 u1 n).2 * X := by
  set U : Polynomial (F p) := X ^ 2 + C u1 * X + C u0 with hU_def
  have hU : U.Monic := uPoly_monic p u0 u1
  have hUdeg : U.degree = (2 : ℕ) := by
    rw [hU_def]; compute_degree!
  -- Base cases `n = 0, 1`: `X^0 = 1`, `X^1 = X`, both already degree < 2.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      have h0 : (X ^ 0 : Polynomial (F p)).degree < U.degree := by
        rw [hUdeg]; compute_degree!
      rw [(Polynomial.modByMonic_eq_self_iff hU).mpr h0]
      simp [xmodUTable]
    | 1 =>
      have h1 : (X ^ 1 : Polynomial (F p)).degree < U.degree := by
        rw [hUdeg]; compute_degree!
      rw [(Polynomial.modByMonic_eq_self_iff hU).mpr h1]
      simp [xmodUTable]
    | (m + 2) =>
      have ihm : (X ^ (m + 1) : Polynomial (F p)) %ₘ U =
          C (xmodUTable p u0 u1 (m + 1)).1 + C (xmodUTable p u0 u1 (m + 1)).2 * X :=
        ih (m + 1) (by omega)
      set a := (xmodUTable p u0 u1 (m + 1)).1
      set b := (xmodUTable p u0 u1 (m + 1)).2
      -- `X^(m+2) - X * (X^(m+1) %ₘ U) = X * (X^(m+1) - X^(m+1) %ₘ U)`,
      -- and `X^(m+1) - X^(m+1) %ₘ U = U * (X^(m+1) /ₘ U)` by `modByMonic_add_div`.
      have hsub : U ∣ (X ^ (m + 2) : Polynomial (F p)) - X * (X ^ (m + 1) %ₘ U) := by
        have hdiv : X ^ (m + 1) - X ^ (m + 1) %ₘ U = U * (X ^ (m + 1) /ₘ U) := by
          have h := Polynomial.modByMonic_add_div (X ^ (m + 1) : Polynomial (F p)) U
          linear_combination -h
        have heq : (X ^ (m + 2) : Polynomial (F p)) - X * (X ^ (m + 1) %ₘ U) =
            X * (U * (X ^ (m + 1) /ₘ U)) := by
          rw [← hdiv]; ring
        rw [heq]
        exact ⟨X * (X ^ (m + 1) /ₘ U), by ring⟩
      have hstep : (X ^ (m + 2) : Polynomial (F p)) %ₘ U =
          (X * (X ^ (m + 1) %ₘ U)) %ₘ U :=
        Polynomial.modByMonic_eq_of_dvd_sub hU hsub
      rw [hstep, ihm]
      -- Now reduce `X * (C a + C b * X) %ₘ U = (-b*u0) + (a - b*u1)*X`,
      -- via `X*(C a+C b*X) - (C(-b*u0)+C(a-b*u1)*X) = C b * U` (a `ring`
      -- identity), so `modByMonic_eq_of_dvd_sub` reduces to that degree-≤1
      -- polynomial's own `%ₘ U`, which equals itself by `modByMonic_eq_self_iff`.
      have hcong : X * (C a + C b * X) - (C (-b * u0) + C (a - b * u1) * X) = C b * U := by
        rw [hU_def]
        simp only [map_mul, map_sub, map_neg]
        ring
      have hdvd2 : U ∣ X * (C a + C b * X) - (C (-b * u0) + C (a - b * u1) * X) :=
        ⟨C b, by rw [hcong]; ring⟩
      have hmod2 : (X * (C a + C b * X)) %ₘ U =
          (C (-b * u0) + C (a - b * u1) * X) %ₘ U :=
        Polynomial.modByMonic_eq_of_dvd_sub hU hdvd2
      have hlindeg : (C (-b * u0) + C (a - b * u1) * X : Polynomial (F p)).degree
          < U.degree := by
        rw [hUdeg]; compute_degree!
      rw [hmod2, (Polynomial.modByMonic_eq_self_iff hU).mpr hlindeg]
      -- Goal: `C(xmodUTable p u0 u1 (m+2)).1 + C(xmodUTable p u0 u1 (m+2)).2 * X`
      -- vs `C(-b*u0) + C(a-b*u1)*X`. `xmodUTable`'s `n+2` clause makes the LHS
      -- tuple *definitionally* `(-b*u0, a-b*u1)` (`a,b` are literally
      -- `xmodUTable p u0 u1 (m+1)`'s two components via `set`), so `rfl`
      -- should close it directly via the equation compiler's unfolding.
      -- If `rfl` doesn't fire (equation-compiler unfolding can be picky
      -- through `set`), replace this line with `simp [xmodUTable]`.
      rfl

end XModUCorrect

end TheDataDerivation
end Genus2Lean
