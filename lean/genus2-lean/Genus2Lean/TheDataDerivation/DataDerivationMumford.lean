import Mathlib
import Genus2Lean.TheDataDerivation.DataDerivationSolve

/-!
# `theData` derivation, part 4: `u_RS`/`v_RS`, the Mumford identity, and the bridge to `Rdec`

Fourth and last of four files — see `DataDerivationBasics.lean`'s header for
the full split rationale and file order. This file builds §4.2 items 7–8
(`u_RS`, `v_RS` via the mod-`u_RS` inverse, and the Mumford identity
`v_RS² ≡ f mod u_RS`) and the un-numbered "bridge to `Rdec`" section
(`towerToRdec`, denominator-clearing from `K2` down to `Rdec`).

**This pass**: `uRS_monic` is now fully proved (no `sorry`) — the roadmap's
own "worth a five-minute Mathlib search" hunch about
`Polynomial.monic_mul_leadingCoeff_inv`-style reasoning was directionally
right; the actual lemma used is
`Polynomial.natDegree_C_mul_eq_of_mul_eq_one` (degree preserved under
multiplication by a witnessed unit) plus `Polynomial.coeff_C_mul` and
`mul_inv_cancel₀`/`inv_mul_cancel₀`, all confirmed against `mathlib4`'s
actual source this pass rather than guessed. `vRS`'s coprimality/inverse-
identification gaps and the Mumford identity itself (`vRS_sq_eq_f_mod_uRS`)
remain `sorry`, still downstream of `DataDerivationSolve.lean`'s `dvd_N_u`
in particular (the Mumford identity's proof depends on all three of item
6's divisibility facts, not just the two proved so far).

`DecoupledSystemRegular.lean` imports this file (which transitively pulls
in the other three) and builds the actual `theData : DecoupledGenerators`
assembly against `towerToRdec`/`uRS`/`vRS` — see that file for the current
state of that assembly.
-/

namespace Genus2Lean
namespace TheDataDerivation

open Polynomial

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Item 7 (§4.2 / §4.0 step 6): `u_RS`, then `v_RS` via the mod-`u_RS` inverse

`curBeforeMonic` (item 6) only equals the true quotient `cur` under the
three `dvd_N_*` facts; `uRS` below is its monic normalization exactly as
Julia's line 469 (`u_RS = cur * inv(leading_coefficient(cur))`), which
additionally needs `curBeforeMonic ≠ 0` (Julia's `iszero(cur)` early-return,
line 464 — the `SymbolicResidualResult(...,Any[],Any[],...)` degenerate
case) to make sense as a normalization at all: dividing by the leading
coefficient of the zero polynomial is `0/0`. That non-degeneracy, like
`MatrixNondegenerate`, is recorded as an explicit hypothesis rather than
proved or assumed globally — a genuine further exceptional-locus condition
on `(p,c0,...,c4,u0,u1,v0,v1)`, additional to `MatrixNondegenerate`, not
yet folded into a single combined statement anywhere in this file. -/

section VRS

variable (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)

/-- `u_RS(x)`, monic-normalized `curBeforeMonic` — Julia line 469. Uses
`Polynomial.leadingCoeff` and its inverse in the field `K2`; well-defined
(as the correct monic associate of `cur`) only once `curBeforeMonic ≠ 0`,
recorded as the hypothesis `hcur` threaded through this section rather than
proved here (upstream of item 6's own three `sorry`s, so nothing below
could discharge it yet regardless). -/
noncomputable def uRS : Polynomial (K2 p c0 c1 c2 c3 c4) :=
  C (curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1).leadingCoeff⁻¹ *
    curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1

/-- `uRS` really is monic, given `curBeforeMonic ≠ 0`. **Now proved** (the
roadmap's own five-minute-search hunch was right, and the lemma is now
pinned down): `Polynomial.natDegree_C_mul_eq_of_mul_eq_one` (Mathlib,
`Mathlib.Algebra.Polynomial.Degree.Lemmas`) gives `(C a * p).natDegree =
p.natDegree` from a witnessed inverse `ai * a = 1` — here `a :=
leadingCoeff⁻¹`, `ai := leadingCoeff`, and `leadingCoeff * leadingCoeff⁻¹ =
1` is `mul_inv_cancel₀` (field, since `leadingCoeff ≠ 0` follows from `hcur`
via `Polynomial.leadingCoeff_ne_zero`). With the degree preserved, the new
leading coefficient is, by `Polynomial.coeff_C_mul` at the (unchanged)
top degree, `leadingCoeff⁻¹ * leadingCoeff = 1` (`inv_mul_cancel₀`) — exactly
`Monic`'s definition (`leadingCoeff = 1`). -/
theorem uRS_monic (hcur : curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 ≠ 0) :
    (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1).Monic := by
  simp only [uRS]
  set q := curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 with hq
  -- Goal now: `(C q.leadingCoeff⁻¹ * q).Monic`.
  have hlc : q.leadingCoeff ≠ 0 := (not_congr Polynomial.leadingCoeff_eq_zero).mpr hcur
  have hau : q.leadingCoeff * q.leadingCoeff⁻¹ = 1 := mul_inv_cancel₀ hlc
  have hdeg : (C q.leadingCoeff⁻¹ * q).natDegree = q.natDegree :=
    Polynomial.natDegree_C_mul_eq_of_mul_eq_one hau
  rw [Polynomial.Monic.def]
  change (C q.leadingCoeff⁻¹ * q).coeff (C q.leadingCoeff⁻¹ * q).natDegree = 1
  rw [hdeg, Polynomial.coeff_C_mul]
  exact inv_mul_cancel₀ hlc

/-- **`v_RS(x) = -E(x) * Y(x)⁻¹ mod u_RS(x)`** (§4.0 step 6, Julia line 486),
computed via the Euclidean-algorithm route the roadmap names as the direct
Mathlib counterpart of Julia's `gcdx` fallback (`_inv_mod_small` is flagged
by the roadmap itself as "purely a bloat-avoidance optimization ... can be
safely SKIPPED in the Lean port", so only the `gcdx`/Euclidean route is
ported here, per the roadmap's own recommendation to prefer "whichever of
the two is easier to formalize").

`Polynomial (K2 p ...)` is a Euclidean domain (a polynomial ring over a
field always is — `Polynomial.instEuclideanDomain` or equivalent), so
`EuclideanDomain.gcdA`/`gcdB` are available: `gcdA a b * a + gcdB a b * b =
gcd a b`. Taking `a := Ypoly`, `b := uRS`, and `gcd = 1` (needs
`IsCoprime`/`gcd = 1`, itself a further hypothesis — Julia's `gcdx` just
returns whatever `gcd` it computes and the caller trusts it is `1` because
the construction guarantees `Y_poly` is a unit mod `u_RS`; this is NOT
proved here, recorded as `hgcd` below), `gcdA Ypoly uRS` is exactly `Y⁻¹ mod
u_RS` up to the sign/normalization `EuclideanDomain.gcdA` happens to use
(Mathlib's Bézout coefficients are not always normalized the same way a
hand-rolled extended-Euclidean routine like Julia's `gcdx` would produce —
this is worth checking concretely, e.g. against Julia's ACTUAL sign
convention for `gcdx`, once both sides are computable, rather than assumed
to match `Y_inv_mod` on the nose; flagged rather than silently assumed).

**Left as `sorry`**: both the coprimality hypothesis's discharge (would
follow from item 6's divisibility facts plus the linear system's own
non-degeneracy, but not derived here) and the actual identification of
`gcdA Ypoly uRS` with "the" inverse are real remaining work, downstream of
item 6.

**Note on `%ₘ`:** Mathlib's `modByMonic` (`%ₘ`) is total — it typechecks
for ANY divisor, not just monic ones — but its defining property
(`a %ₘ b` has degree `< b.natDegree`, and is the "true" remainder) only
holds when the divisor is genuinely monic. `vRS` below is stated against
`uRS` directly rather than threading `uRS_monic`'s hypothesis `hcur`
through as well, so as written this compiles but is only the CORRECT
`v_RS` once `hcur` also holds alongside `hgcd` — both hypotheses belong
together on any theorem actually USING `vRS`'s value (e.g.
`vRS_sq_eq_f_mod_uRS` below), even though `vRS`'s bare definition only
needs `hgcd` to typecheck. -/
noncomputable def vRS
    (_hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1) (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1)) :
    Polynomial (K2 p c0 c1 c2 c3 c4) :=
  (-(Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1) *
      EuclideanDomain.gcdA (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
        (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1)) %ₘ
    uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1

end VRS

/-! ## Item 8 (§4.0 step 8): the Mumford identity — NOT skippable

Per the roadmap: "this one is NOT skippable: it's the actual correctness
statement `(u_RS,v_RS)` really is a point on `Jac(C)`'s 2-torsion-free
part". This is `_check_mumford_identity`'s "pre-reduction" check (the
"post-reduction" copy has no counterpart here since item 8 in §4.2's build
order — coefficient reduction to lowest terms — is separately flagged as
skippable and is NOT ported below; see the note after this theorem). The
roadmap's own assessment: "should be near-definitional once step 7 is in
Lean", since `vRS` was constructed FROM `uRS` via the mod-`u_RS` inverse
specifically so this identity holds by that construction, not as an
independent fact requiring new algebra. -/

section GenericRemainderLemma
-- **Deliberately its own section, above `MumfordIdentity`'s variables.**
-- `sq_mod_eq_of_dvd` below mentions none of `p`, `c0..v1`, `hcur`, `hgcd` —
-- but those are declared as ambient `variable`s in `section MumfordIdentity`
-- (needed by `vRS_sq_eq_f_mod_uRS` right after it), and living inside that
-- section was bloating this lemma's local context enough to timeout `whnf`
-- during elaboration even though the statement never uses them. Elaborating
-- it here, before any of those variables exist, gives it the smallest
-- possible local context.

set_option maxHeartbeats 4000000 in
/-- **Heartbeats raised**: even this fully generic, abstract statement hit
the default ceiling during elaboration (cause not yet isolated — see the
`sq_mod_eq_of_dvd` docstring below for the splitting rationale).

Step 1 of `sq_mod_eq_of_dvd`: `U ∣ (Y*G)^2 - 1` from `U ∣ Y*G - 1`. -/
theorem sq_mod_eq_of_dvd_step1
    {R : Type*} [CommRing R] {U Y G : Polynomial R}
    (hInv : U ∣ Y * G - 1) :
    U ∣ (Y * G) ^ 2 - 1 := by
  have hsq1 : (Y * G) ^ 2 - 1 = (Y * G - 1) * (Y * G + 1) := by ring
  rw [hsq1]
  exact dvd_mul_of_dvd_left hInv (Y * G + 1)

set_option maxHeartbeats 4000000 in
/-- **Heartbeats raised** (see `sq_mod_eq_of_dvd_step1`'s docstring — same
situation). Step 2 of `sq_mod_eq_of_dvd`: `U ∣ (E*G)^2 - f`, combining the
`N` divisibility with step 1's inverse-squared divisibility. -/
theorem sq_mod_eq_of_dvd_step2
    {R : Type*} [CommRing R] {U E Y G f : Polynomial R}
    (hN : U ∣ E ^ 2 - f * Y ^ 2)
    (hInvSq : U ∣ (Y * G) ^ 2 - 1) :
    U ∣ (E * G) ^ 2 - f := by
  have hNscaled : U ∣ (E ^ 2 - f * Y ^ 2) * G ^ 2 :=
    dvd_mul_of_dvd_left hN (G ^ 2)
  have hInvscaled : U ∣ f * ((Y * G) ^ 2 - 1) :=
    dvd_mul_of_dvd_right hInvSq f
  have hid1 :
      (E ^ 2 - f * Y ^ 2) * G ^ 2 + f * ((Y * G) ^ 2 - 1) = (E * G) ^ 2 - f := by
    ring
  rw [← hid1]
  exact dvd_add hNscaled hInvscaled

set_option maxHeartbeats 4000000 in
/-- **Heartbeats raised** (see `sq_mod_eq_of_dvd_step1`'s docstring — same
situation). Step 3 of `sq_mod_eq_of_dvd`: the division-algorithm remainder
identity `U ∣ (X %ₘ U) - X`, stated for a general dividend `X`. -/
theorem sq_mod_eq_of_dvd_step3
    {R : Type*} [CommRing R] (U X : Polynomial R) :
    U ∣ (X %ₘ U) - X := by
  -- The file's earlier searches for `Polynomial.dvd_modByMonic_sub` turned
  -- up an out-of-date (pre-refactor) signature that required an explicit
  -- derivation via `modByMonic_eq_sub_mul_div` and a `Monic` hypothesis.
  -- In this checkout, `Polynomial.dvd_modByMonic_sub (p q : Polynomial R)
  -- : q ∣ p %ₘ q - p` already exists directly and unconditionally (no
  -- `Monic` needed — confirmed against the live mathlib4 docs this pass),
  -- so no `hU` parameter is needed here at all.
  exact Polynomial.dvd_modByMonic_sub X U

set_option maxHeartbeats 4000000 in
/-- **Heartbeats raised** (see `sq_mod_eq_of_dvd_step1`'s docstring — same
situation). Step 4 of `sq_mod_eq_of_dvd`: `U ∣ (X %ₘ U)^2 - X^2` for any
`X`, via difference of squares against step 3's remainder divisibility. -/
theorem sq_mod_eq_of_dvd_step4
    {R : Type*} [CommRing R] {U : Polynomial R} (X : Polynomial R)
    (hrem : U ∣ (X %ₘ U) - X) :
    U ∣ (X %ₘ U) ^ 2 - X ^ 2 := by
  have hsq2 : (X %ₘ U) ^ 2 - X ^ 2 = ((X %ₘ U) + X) * ((X %ₘ U) - X) := by ring
  rw [hsq2]
  exact dvd_mul_of_dvd_right hrem ((X %ₘ U) + X)

set_option maxHeartbeats 4000000 in
/-- **Heartbeats raised**: even this fully generic, abstract statement hit
the default ceiling during elaboration.

**Generic remainder lemma used by the Mumford identity.**
This isolates all polynomial algebra from the very large concrete expressions
for `uRS`, `Epoly`, `Ypoly`, and `fAtX`, so elaboration does not repeatedly
unfold those definitions while proving the identity.

Assembled from `sq_mod_eq_of_dvd_step{1,2,3,4}` above (split out because the
single monolithic proof was hitting the `maxHeartbeats` ceiling even at 4M —
splitting isolates which step, if any, is actually the expensive one instead
of hiding it inside one large `by` block). -/
theorem sq_mod_eq_of_dvd
    {R : Type*} [CommRing R]
    {U E Y G f : Polynomial R}
    (hU : U.Monic)
    (hN : U ∣ E ^ 2 - f * Y ^ 2)
    (hInv : U ∣ Y * G - 1) :
    ((-E * G) %ₘ U) ^ 2 %ₘ U = f %ₘ U := by
  have hInvSq := sq_mod_eq_of_dvd_step1 hInv
  have hEGf := sq_mod_eq_of_dvd_step2 hN hInvSq
  have hrem := sq_mod_eq_of_dvd_step3 U (-E * G)
  have hvrem := sq_mod_eq_of_dvd_step4 (-E * G) hrem
  -- `hvrem : U ∣ ((-E*G) %ₘ U)^2 - (-E*G)^2`; bridge `(-E*G)^2 = (E*G)^2`
  -- to match `hEGf`'s `(E*G)^2` before combining (not syntactically equal,
  -- just `ring`-equal, so the two `have`s don't unify on the nose).
  have hnegsq : (-E * G) ^ 2 = (E * G) ^ 2 := by ring
  rw [hnegsq] at hvrem
  have hid2 :
      ((-E * G) %ₘ U) ^ 2 - (E * G) ^ 2 + ((E * G) ^ 2 - f) =
        ((-E * G) %ₘ U) ^ 2 - f := by
    ring
  have hvf : U ∣ ((-E * G) %ₘ U) ^ 2 - f := by
    rw [← hid2]; exact dvd_add hvrem hEGf
  exact Polynomial.modByMonic_eq_of_dvd_sub hU hvf

end GenericRemainderLemma

section MumfordIdentity

variable (c0 c1 c2 c3 c4 u0 u1 v0 v1 : F p)
variable (hcur : curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 ≠ 0)
variable (hgcd : IsCoprime (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1) (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1))

/-- **The Mumford identity**: `v_RS(x)^2 ≡ f(x) (mod u_RS(x))`.

**Review note on `hInv` vs `hgcd`, checked this pass**: `hInv` looks at
first glance like it should be a free consequence of `hgcd : IsCoprime Y
U` via `EuclideanDomain.gcd_eq_gcd_ab` (`gcd Y U = Y*gcdA Y U + U*gcdB Y
U`) — but it is NOT, and keeping it as a separate hypothesis here is the
correct choice, not redundant caution. `EuclideanDomain.gcd_isUnit_iff`
confirms `hgcd` only gives `IsUnit (EuclideanDomain.gcd Y U)`, i.e.
`gcd Y U = c` for SOME unit `c` (a nonzero constant), not `gcd Y U = 1`
on the nose — `EuclideanDomain.gcd` (unlike `GCDMonoid.gcd`) carries no
built-in normalization convention forcing the unit to be exactly `1`.
Turning `hgcd` into `hInv` therefore needs an extra step: scaling
`gcdA Y U` by `c⁻¹` to correct for whatever unit `gcd Y U` actually turned
out to be. That scaling step is not carried out anywhere in this file, so
`hInv` is real remaining content, not a restatement of `hgcd` — flagged
explicitly rather than left for a future reader to (wrongly) assume one
hypothesis subsumes the other. -/
theorem vRS_sq_eq_f_mod_uRS
    (hcur :
      curBeforeMonic p c0 c1 c2 c3 c4 u0 u1 v0 v1 ≠ 0)
    (hNu :
      uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 ∣
        Npoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
    (hInv :
      uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 ∣
        Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1 *
            EuclideanDomain.gcdA
              (Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1)
              (uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1) - 1) :
    (vRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 hgcd) ^ 2 %ₘ
        uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 =
      (fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1) %ₘ
        uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1 := by
  let U := uRS p c0 c1 c2 c3 c4 u0 u1 v0 v1
  let E := Epoly p c0 c1 c2 c3 c4 u0 u1 v0 v1
  let Y := Ypoly p c0 c1 c2 c3 c4 u0 u1 v0 v1
  let G := EuclideanDomain.gcdA Y U
  let f := fAtX p c0 c1 c2 c3 c4 u0 u1 v0 v1
  have hU : U.Monic :=
    uRS_monic p c0 c1 c2 c3 c4 u0 u1 v0 v1 hcur
  have hInv' : U ∣ Y * G - 1 := by
    exact hInv
  have hNu' : U ∣ E ^ 2 - f * Y ^ 2 := by
    exact hNu
  have hmod := sq_mod_eq_of_dvd hU hNu' hInv'
  simpa only [vRS, U, E, Y, G, f] using hmod

end MumfordIdentity

/-! ## Reduction to lowest terms (§4.2 item 8 / §4.0 step 7) — intentionally NOT ported

Per the roadmap (§4.2 item 8): `_reduce_tower_coeffs` exists purely to keep
Julia's NUMERICAL computation tractable (term-count bloat), and "Lean's
kernel doesn't care about term-count bloat the way a numerical
Gröbner/resultant computation does" — this step is deliberately dropped
here, confirmed rather than merely assumed (nothing in items 7's `vRS` or
item 8's Mumford-identity statement above depends on coefficients being in
lowest terms; both are stated directly against `uRS`/`vRS` as elements of
`K2`, unreduced). `theData`'s coefficients (below) are therefore
possibly-non-reduced fractions throughout — this is a deliberate scope
decision per the roadmap, not an oversight. -/

/-! ## New item (implicit in §4.0, not separately numbered in §4.2):
denominator-clearing, `K2` → `Rdec` — the bridge to `DecoupledGenerators`

§4.0's own summary states the target crisply: "The output `theData` needs
is exactly steps 1-7's `u_RS_coeffs`/`v_RS_coeffs` ... specialized twice
... with different fixed `(u0,u1,v0,v1)` target data". What §4.0/§4.2
leaves implicit is HOW a `K2`-valued coefficient becomes an `Rdec` element
at all: `K2` is built over the ABSTRACT field `K0 = Frac(MvPolynomial (Fin
2) F)`, with `t0 p 0`/`t0 p 1` as its two free generators, whereas
`DecoupledSystemRegular.lean`'s `Rdec = MvPolynomial Idx F` has its OWN
twelve named generators (`wa1,wa2,...`), and `DecoupledGenerators` wants
each coefficient as an explicit `(num, den) : Rdec × Rdec` PAIR, not a
single `K2`/fraction-field element — `Rdec` itself has no division. This is
exactly `elim2.jl`'s `tower_to_ring`/`map_coeffs_threaded` step (confirmed
by reading `01_elim2_main.jl` directly: `tower_to_ring` is called once per
`u_RS`/`v_RS` coefficient, separately from `symbolic_residual`), and is
genuinely a SEPARATE step from anything `symbolic_residual` itself does —
worth naming explicitly here since §4.2's build order does not give it its
own numbered item, but `theData`'s assembly below cannot be stated without
it.

**Left as `sorry`** throughout this section: a full port needs (a) a
concrete ring isomorphism/embedding identifying `K2`'s rank-4-over-`K0`
structure with the sub-`F`-algebra of `Rdec` generated by
`{wa1,wa2,a1,a2}` (resp. `{wb1,wb2,b1,b2}` for the b-side copy) subject to
the two curve relations — i.e. `K2 ≃ Rdec ⧸ (curve relations)`'s fraction
field, restricted to the 4-generator subring — and (b) clearing each
coefficient's denominator down to a genuine `Rdec` numerator/denominator
pair (`tower_to_ring`'s own per-coefficient `_reduce_frac`, itself skipped
per the note above, but the denominator-clearing ITSELF, as opposed to
GCD-reducing it afterward, is not skippable — `Rdec` has no fractions at
all, so SOME clearing step is mandatory even though further reduction to
lowest terms is not). Neither (a) nor (b) is attempted here beyond stating
the target type signature; this is flagged as likely comparable in
difficulty to item 6, not a formality, since it is a genuine change of ring
(fraction field of a quotient of a 2-variable polynomial ring, embedded
into a 12-variable one) rather than an operation internal to a single fixed
ring. -/

section BridgeToRdec

/-- Which 4-variable copy of `Rdec`'s generators `towerToRdec` targets —
matches `DecoupledGenerators.u1_indep`/`.u2_indep`'s two `Finset Idx`
targets in `DecoupledSystemRegular.lean` exactly (`{wa1,wa2,a1,a2}` vs.
`{wb1,wb2,b1,b2}`). Kept as a named type (rather than just inlining the two
`SideGens` records at each call site) purely for documentation value at the
call site in `DecoupledSystemRegular.lean`. -/
inductive Side | aSide | bSide
  deriving DecidableEq

/-- Per-copy target generators: `wGen 0, wGen 1` are the images of the
tower's `w1, w2` (Julia's `w_gens`, i.e. `[wa1,wa2]` or `[wb1,wb2]`),
`tGen 0, tGen 1` are the images of `t1, t2` (Julia's `t_gens`, i.e.
`[a1,a2]` or `[b1,b2]`). A record of two `Fin 2 → Vars` functions rather
than a bare string list (the earlier draft's `sideVars`), so `towerToRdec`
below can build `MvPolynomial.X` terms directly. The call site in
`DecoupledSystemRegular.lean` instantiates `Vars := Idx` with e.g.
`⟨![a1, a2], ![wa1, wa2]⟩` for `Side.aSide`. -/
structure SideGens (Vars : Type*) where
  tGen : Fin 2 → Vars
  wGen : Fin 2 → Vars

/-! **§4.0's denominator-clearing step, ported directly from
`01_elim2_main.jl`'s `_tower_to_ring`/`_reduce_frac`/`_base_frac_to_ring`**
(read in full this pass — `elim2.zip`, lines 120–203 — so this is no
longer a guess about what `tower_to_ring` does, closing the gap the
roadmap's "New item" note above flagged as un-numbered in §4.2).

The Julia recursion: an element of `K_final = K2` is stored, at the outer
`AdjoinRoot` layer, as a degree-`≤1` polynomial in `w2` over `K1` —
`data(val) = c0 + c1*w2` — and `c0, c1 : K1` are themselves degree-`≤1` in
`w1` over `K0` — `c0 = d0 + d1*w1`, etc. — bottoming out at
`K0 = FractionRing (MvPolynomial (Fin 2) F)`, where a value is literally a
`num/den` fraction of 2-variable polynomials, cleared by substituting
`SideGens.tGen`'s images (`_base_frac_to_ring`'s `evaluate(num, t_gens)`).
Each recursive step combines its two children's `(num,den)` pairs via
`num = n0*d1 + n1*d0*w`, `den = d0*d1` (cross-multiplication — `Rdec` has
no division) — Julia additionally GCD-reduces at every step
(`_reduce_frac`), which is dropped here, extending §4.2 item 8's finding
("reduction to lowest terms ... likely SKIPPABLE ... Lean's kernel doesn't
care about term-count bloat") from the earlier single-variable `Polynomial`
case to this multivariate one, for the identical reason:
`_reduce_frac`'s sole purpose is keeping Julia's NUMERICAL computation
tractable, and dropping it changes no mathematical content — `num/den`
still equals the same field element whether or not `num,den` share a
common factor, and nothing downstream (`FuList`/`FvList` in
`DecoupledSystemRegular.lean`, or this file) needs lowest-terms form.
Flagged explicitly since this is a NEW instance of that skip (a genuinely
multivariate one, where `MvPolynomial` also lacks the convenient
`EuclideanDomain`/`gcd` API `Polynomial` has, giving a second, independent
reason to drop it here beyond the term-count argument alone). -/

/-- **Base case** (`level = 0`, Julia's `_base_frac_to_ring`): clear a `K0`
element's denominator by substituting `sg.tGen`'s images for `K0`'s two
`MvPolynomial (Fin 2) (F p)` generators. `K0 = FractionRing (MvPolynomial
(Fin 2) (F p))`, so any `v : K0 p` has genuine numerator/denominator
polynomials via `IsFractionRing.num`/`.den`; `MvPolynomial.aeval` with the
variable map `fun i => X (sg.tGen i)` performs Julia's
`evaluate(num, t_gens)` exactly. **No `sorry`**: this base case is
constructive given the `IsFractionRing` API alone. -/
noncomputable def baseFracToRing {Vars : Type*}
    (sg : SideGens Vars) (v : K0 p) :
    MvPolynomial Vars (F p) × MvPolynomial Vars (F p) :=
  ( MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.X (sg.tGen i))
      (IsFractionRing.num (MvPolynomial (Fin 2) (F p)) v),
    MvPolynomial.aeval (fun i : Fin 2 => MvPolynomial.X (sg.tGen i))
      (↑(IsFractionRing.den (MvPolynomial (Fin 2) (F p)) v) : MvPolynomial (Fin 2) (F p)) )

/-- The defining quadratic for `K1`, monic (leading coefficient `1` by
construction — `X^2 - C (fAtT ...)` always has `X^2`'s coefficient `1`),
named separately so `towerToRdecK1`/its correctness lemmas can cite
`Monic` without re-unfolding `K1`'s definition each time. **No `sorry`**:
monicity of `X^2 - C a` is immediate from `Polynomial.monic_X_pow_sub_C`-
style reasoning (`X^2` has leading coefficient `1`, subtracting a constant
doesn't change the degree-2 coefficient). -/
theorem K1_poly_monic (c0 c1 c2 c3 c4 : F p) :
    (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)).Monic := by
  have : (X ^ 2 - C (fAtT p c0 c1 c2 c3 c4 0) : Polynomial (K0 p)) =
      X ^ 2 + C (-fAtT p c0 c1 c2 c3 c4 0) := by
    rw [Polynomial.C_neg, sub_eq_add_neg]
  rw [this]
  exact (monic_X_pow 2).add_of_left (by
    simpa using (degree_C_le (a := -fAtT p c0 c1 c2 c3 c4 0)).trans_lt
      (by simp : (0 : WithBot ℕ) < 2))

/-- **The resolved blocker.** `AdjoinRoot.modByMonicHom` (Mathlib,
`Mathlib.RingTheory.AdjoinRoot`) is exactly the API the roadmap's
"candidates" note was looking for: for `hg : g.Monic`, it is the
(linear, well-defined) map `AdjoinRoot g →ₗ[R] Polynomial R` sending
`AdjoinRoot.mk g f ↦ f %ₘ g` — i.e. THE canonical degree-`<deg g`
representative of a class in `AdjoinRoot g`, which for `g` a monic
quadratic is exactly the `d1*w+d0` normal form `_tower_to_ring` reads off
via Julia's `data(val)`/`coeff(val_poly, 0/1)`. `AdjoinRoot.modByMonicHom_mk`
is its defining computation lemma (`modByMonicHom hg (mk g f) = f %ₘ g`),
and `.coeff 0` / `.coeff 1` on the resulting `Polynomial (K0 p)` extract
`d0`/`d1` respectively — Julia's `coeff(val_poly, 0)` / `coeff(val_poly, 1)`
verbatim. This closes the roadmap's own "not yet pinned down" note, so
`towerToRdecK1` below is now a genuine construction, not a `sorry`. -/
noncomputable def towerToRdecK1 {Vars : Type*}
    (sg : SideGens Vars) (v : K1 p c0 c1 c2 c3 c4) :
    MvPolynomial Vars (F p) × MvPolynomial Vars (F p) :=
  let valPoly : Polynomial (K0 p) :=
    AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) v
  let d0 : K0 p := valPoly.coeff 0
  let d1 : K0 p := valPoly.coeff 1
  let (n0, den0) := baseFracToRing p sg d0
  let (n1, den1) := baseFracToRing p sg d1
  ( n0 * den1 + n1 * den0 * MvPolynomial.X (sg.wGen 0),
    den0 * den1 )

/-- `K2`'s defining quadratic, monic over `K1` — same shape/proof as
`K1_poly_monic`, one level up. **No `sorry`**. -/
theorem K2_poly_monic (c0 c1 c2 c3 c4 : F p) :
    (X ^ 2 - C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
        Polynomial (K1 p c0 c1 c2 c3 c4)).Monic := by
  have : (X ^ 2 -
      C (algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)) :
        Polynomial (K1 p c0 c1 c2 c3 c4)) =
      X ^ 2 + C (-(algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1))) := by
    -- `rw [Polynomial.C_neg, sub_eq_add_neg]` here hits "motive is not type
    -- correct": `K1 p ...` is a reducible `abbrev` over `AdjoinRoot`, and its
    -- own `Field`/`Irreducible` instance search is entangled with this exact
    -- polynomial term, so `rw` can't safely abstract it. `simp only` handles
    -- such dependencies (per its own diagnostic message), same fix as the
    -- earlier `w2_sq_eq` timeout.
    simp only [Polynomial.C_neg, sub_eq_add_neg]
  rw [this]
  exact (monic_X_pow 2).add_of_left (by
    simpa using (degree_C_le
        (a := -(algebraMap (K0 p) (K1 p c0 c1 c2 c3 c4) (fAtT p c0 c1 c2 c3 c4 1)))).trans_lt
      (by simp : (0 : WithBot ℕ) < 2))

/-- `level = 2` step (Julia's `_tower_to_ring` with `level=2`, i.e.
`tower_to_ring`'s own entry point) — **this is `towerToRdec` itself**, the
top-level denominator-clearing map §4.0's summary and
`DecoupledSystemRegular.lean`'s `theData` assembly both need. Given
`v : K2 p c0 c1 c2 c3 c4`, extract its `(c0,c1) : K1 p ... × K1 p ...`
coefficient pair the same way `towerToRdecK1` does one level down (via
`AdjoinRoot.modByMonicHom (K2_poly_monic ...)` instead of `K1_poly_monic`),
recurse via `towerToRdecK1` on each, then combine using `sg.wGen 1`
(`wa2`/`wb2`) as the image of `w2` — Julia's `num = n0*d1+n1*d0*wv`,
`den = d0*d1` formula, identical shape to `towerToRdecK1`'s own combination
step, now with the recursive call one level down being `towerToRdecK1`
rather than `baseFracToRing`. Supersedes the earlier fully-abstract stub of
the same name (which took an opaque `Side` and no `SideGens`); the
`Side`/`sideVars` split from that draft is kept above only as
documentation, with `SideGens` doing the actual work, since the assembly
step needs concrete `Idx`-valued functions, not strings, to build
`MvPolynomial.X` terms. **No `sorry`**: this and `towerToRdecK1` together
close the roadmap's un-numbered "bridge to `Rdec`" gap in full — the
denominator-clearing recursion itself (as opposed to the `_reduce_frac`
GCD-cancellation step, deliberately dropped per the note above and in
§4.2 item 8) is now a complete Lean construction, not a stub. -/
noncomputable def towerToRdec {Vars : Type*}
    (sg : SideGens Vars) (v : K2 p c0 c1 c2 c3 c4) :
    MvPolynomial Vars (F p) × MvPolynomial Vars (F p) :=
  let valPoly : Polynomial (K1 p c0 c1 c2 c3 c4) :=
    AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v
  let d0 : K1 p c0 c1 c2 c3 c4 := valPoly.coeff 0
  let d1 : K1 p c0 c1 c2 c3 c4 := valPoly.coeff 1
  let (n0, den0) := towerToRdecK1 p sg d0
  let (n1, den1) := towerToRdecK1 p sg d1
  ( n0 * den1 + n1 * den0 * MvPolynomial.X (sg.wGen 1),
    den0 * den1 )

/-- **Shared generator-containment bound.** The four independence
obligations `DecoupledGenerators.u1_indep`/`.u2_indep`/`.v1_indep`/
`.v2_indep` in `DecoupledSystemRegular.lean` all reduce to this one fact
about `towerToRdec`'s output: since every `MvPolynomial.X` term either
function ever introduces is one of `sg.tGen 0`, `sg.tGen 1`, `sg.wGen 0`,
`sg.wGen 1` (`baseFracToRing` only substitutes `sg.tGen`, `towerToRdecK1`
additionally multiplies in `X (sg.wGen 0)`, `towerToRdec` additionally
multiplies in `X (sg.wGen 1)` — no other generator is ever mentioned by
name anywhere in the recursion), both the numerator and denominator stay
within that 4-element set regardless of `v`. Proved by chasing `vars`
through the recursion with `MvPolynomial.vars_add_subset`/`vars_mul`/
`vars_X`/`vars_bind₁` (via `aeval_eq_bind₁`, for `baseFracToRing`'s call),
rather than by induction on `v` itself — `towerToRdec`/`towerToRdecK1`/
`baseFracToRing` are each a single non-recursive `let`-chain, not a
recursive definition on `v`, so ordinary equational unfolding plus these
four `vars` lemmas suffices; no separate induction principle is needed. -/
theorem towerToRdec_vars_subset {Vars : Type*} [DecidableEq Vars]
    (sg : SideGens Vars) (v : K2 p c0 c1 c2 c3 c4) :
    (towerToRdec p sg v).1.vars ⊆ {sg.tGen 0, sg.tGen 1, sg.wGen 0, sg.wGen 1} ∧
    (towerToRdec p sg v).2.vars ⊆ {sg.tGen 0, sg.tGen 1, sg.wGen 0, sg.wGen 1} := by
  classical
  -- Step 0: `baseFracToRing`'s output only involves `sg.tGen 0, sg.tGen 1`.
  have hbase : ∀ w : K0 p, (baseFracToRing p sg w).1.vars ⊆ {sg.tGen 0, sg.tGen 1} ∧
      (baseFracToRing p sg w).2.vars ⊆ {sg.tGen 0, sg.tGen 1} := by
    intro w
    unfold baseFracToRing
    dsimp only
    have hgen : ∀ i : Fin 2, (MvPolynomial.X (sg.tGen i) : MvPolynomial Vars (F p)).vars ⊆
        ({sg.tGen 0, sg.tGen 1} : Finset Vars) := by
      intro i
      have : (MvPolynomial.X (sg.tGen i) : MvPolynomial Vars (F p)).vars ⊆ {sg.tGen i} := by
        rw [MvPolynomial.vars_X]
      refine this.trans ?_
      fin_cases i <;> simp
    constructor <;>
      · rw [MvPolynomial.aeval_eq_bind₁]
        exact (MvPolynomial.vars_bind₁ _ _).trans (Finset.biUnion_subset.mpr (fun i _ => hgen i))
  -- Step 1: `towerToRdecK1`'s output additionally allows `sg.wGen 0`.
  have hK1 : ∀ w : K1 p c0 c1 c2 c3 c4,
      (towerToRdecK1 p sg w).1.vars ⊆ {sg.tGen 0, sg.tGen 1, sg.wGen 0} ∧
      (towerToRdecK1 p sg w).2.vars ⊆ {sg.tGen 0, sg.tGen 1, sg.wGen 0} := by
    intro w
    unfold towerToRdecK1
    dsimp only
    set d0 := (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) w).coeff 0
    set d1 := (AdjoinRoot.modByMonicHom (K1_poly_monic p c0 c1 c2 c3 c4) w).coeff 1
    obtain ⟨hn0, hd0⟩ := hbase d0
    obtain ⟨hn1, hd1⟩ := hbase d1
    have hsub3 : ({sg.tGen 0, sg.tGen 1} : Finset Vars) ⊆
        {sg.tGen 0, sg.tGen 1, sg.wGen 0} := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto
    refine ⟨?_, ?_⟩
    · refine (MvPolynomial.vars_add_subset _ _).trans ?_
      apply Finset.union_subset
      · exact (MvPolynomial.vars_mul _ _).trans
          (Finset.union_subset (hn0.trans hsub3) (hd1.trans hsub3))
      · refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset
          ((MvPolynomial.vars_mul _ _).trans
            (Finset.union_subset (hn1.trans hsub3) (hd0.trans hsub3)))
          ?_)
        have : (MvPolynomial.X (sg.wGen 0) : MvPolynomial Vars (F p)).vars ⊆ {sg.wGen 0} := by
          rw [MvPolynomial.vars_X]
        exact this.trans (by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; simp)
    · exact (MvPolynomial.vars_mul _ _).trans
        (Finset.union_subset (hd0.trans hsub3) (hd1.trans hsub3))
  -- Step 2: `towerToRdec` itself additionally allows `sg.wGen 1`.
  unfold towerToRdec
  dsimp only
  set d0 := (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 0
  set d1 := (AdjoinRoot.modByMonicHom (K2_poly_monic p c0 c1 c2 c3 c4) v).coeff 1
  obtain ⟨hn0, hd0⟩ := hK1 d0
  obtain ⟨hn1, hd1⟩ := hK1 d1
  have hsub4 : ({sg.tGen 0, sg.tGen 1, sg.wGen 0} : Finset Vars) ⊆
      {sg.tGen 0, sg.tGen 1, sg.wGen 0, sg.wGen 1} := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto
  refine ⟨?_, ?_⟩
  · refine (MvPolynomial.vars_add_subset _ _).trans ?_
    apply Finset.union_subset
    · exact (MvPolynomial.vars_mul _ _).trans
        (Finset.union_subset (hn0.trans hsub4) (hd1.trans hsub4))
    · refine (MvPolynomial.vars_mul _ _).trans (Finset.union_subset
        ((MvPolynomial.vars_mul _ _).trans
          (Finset.union_subset (hn1.trans hsub4) (hd0.trans hsub4)))
        ?_)
      have : (MvPolynomial.X (sg.wGen 1) : MvPolynomial Vars (F p)).vars ⊆ {sg.wGen 1} := by
        rw [MvPolynomial.vars_X]
      exact this.trans (by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; simp)
  · exact (MvPolynomial.vars_mul _ _).trans
      (Finset.union_subset (hd0.trans hsub4) (hd1.trans hsub4))

/-- **Correctness spec `towerToRdec` is intended to satisfy**, recorded in
prose (not yet a checkable Lean statement — see below for why): under the
embedding identifying `K2 p c0 c1 c2 c3 c4` with the sub-`F p`-algebra of
`FractionRing (MvPolynomial Vars (F p))` generated by `sg.tGen`/`sg.wGen`'s
images subject to the two curve relations `wGen i ^ 2 = f (tGen i)` — call
this embedding `ι : K2 p c0 c1 c2 c3 c4 →+* FractionRing (MvPolynomial Vars
(F p))`, itself NOT constructed anywhere in this file — `towerToRdec sg v`
should satisfy `(towerToRdec sg v).1 = (towerToRdec sg v).2 • ι v` (as
elements of `FractionRing (MvPolynomial Vars (F p))`, after mapping the
`Rdec`-valued pair through `algebraMap`), i.e. "clearing the denominator
correctly." Left unstated as an actual `theorem` here because `ι` itself
has no Lean definition yet — constructing it is flagged in the surrounding
docstrings as comparable in difficulty to item 6, a genuine change of ring
rather than plumbing — so there is nothing yet to quantify over. Recorded
as prose so the embedding construction, whenever attempted, has a named
target to prove rather than `towerToRdec` floating free of any spec. -/
theorem towerToRdec_spec_TODO : True := trivial

end BridgeToRdec

/-! ## Assembling `theData`

§4.0's own summary states the target crisply: "The output `theData` needs
is exactly steps 1-7's `u_RS_coeffs`/`v_RS_coeffs` ... specialized twice
... with different fixed `(u0,u1,v0,v1)` target data". The recipe: apply
`uRS`/`vRS` above once with sample a's target data `(ua0,ua1,va0,va1)`, once
with sample b's `(ub0,ub1,vb0,vb1)`, both against the SAME `(c0,...,c4)`,
then run `towerToRdec` (with the a-side/b-side `SideGens` respectively) on
each of `uRS`/`vRS`'s two relevant coefficients (`N_U_MATCH = 2`, skipping
`u_RS`'s always-`1` leading `x^2` coefficient). The actual assembly into a
`DecoupledGenerators` value lives in `DecoupledSystemRegular.lean` itself,
which imports this file and instantiates `SideGens Idx` for both sides —
see that file for the current, up-to-date state of that assembly. -/

end TheDataDerivation
end Genus2Lean
