# Notes: a shift-graph attack on the E(S,S) bottleneck

Status: exploratory, unproven, written up to preserve the thread — not
a claim that this closes advisory-7's open item. Companion to
`genus2-index-calculus-advisory-6.md` (labeled revision 7 internally),
specifically sections 3-7 and item 8(c).

## 1. The open problem this targets

Advisory-7 section 7.4-7.5 pins the entire remaining gap in the
complexity heuristic (H0) on one quantity:

    E(S,S) = additive energy of S = T+T,  T = s(F) subset of J(F_p)

Known: E(S,S) << B^8/|J| would suffice (Paley-Zygmund, eq. 13).
Known unconditionally: E(S,S) < 2 B^6 * |J| via Sidon-ness alone
(section 7.5, eq. 16), short of the target by a factor of exactly
B^2, and this shortfall is proven extremal given only (a) T Sidon,
(b) the trivial pointwise Fourier bound |T-hat(chi)| <= B. Every
other route tried (Ortega-Prendiville Fourier uniformity, a fresh
Lang-torsor/Weil-II sup-norm bound, FFKW's 2026 Jacobian-graph 4th
moment) tops out at the same 4th-moment / Gowers U^2 level; none
reach the 8th-moment / U^3 level E(S,S) actually lives at. Section
7.6 explains structurally why: U^2 data (pairwise sums, i.e. an
O(B^2) histogram) cannot certify U^3 facts by a theorem of Shkredov
(higher energy E_k(A) <= |A|^(k+eps) unless A has coset/small-doubling
structure — pairwise flattening pushes toward the *generic* branch,
not the structured branch where a better bound could live).

## 2. The proposed new angle: a "shift graph" on Delta

Idea (from conversation, not in the advisory): build a graph on
witnesses of the matching condition

    (P1+P2) - (P3+P4) = Delta*a

using a group-translation move: for delta in (a bounded subset of)
<a>, absorb delta*a into the P-side instead of the Delta-side:

    (P1+P2) + delta*a  -->  Cantor-reduce  -->  (u_delta, v_delta)

If u_delta splits over F_p (i.e. has two F_p-rational roots), this
produces a genuine new witness pair (P1', P2') with
(P1'+P2') - (P3+P4) = (Delta+delta)*a, i.e. a witness for
N(Delta+delta) built from a witness of N(Delta). This map is exactly
invertible (shift back by -delta*a) whenever both sides split, so
conditional on splitting it is a genuine bijection on that subset of
witnesses -- not just a heuristic correspondence.

Whether u_delta splits is governed by a discriminant/QR condition:
a "random" monic quadratic over F_p splits with probability exactly
1/2 (standard fact: quadratic factors over F_p iff its discriminant
is a square, true for exactly half of all monic quadratics). Hence
"up to the 1/2 splitting" -- the correspondence is only defined,
witness-by-witness, on (heuristically) half the witnesses at a time.

Goal: if this shift structure can be shown to *spread out* -- i.e.
mixes the witnesses of a lumpy/hot Delta out across many other
Delta's -- it would give leverage on E(S,S) that doesn't reduce to
any of the four already-exhausted routes above, because it's an
orbit/expansion argument rather than a Fourier sup-norm or aggregate
Cauchy-Schwarz argument.

## 3. Reduction to a Cayley graph / character sum

Since <a> is cyclic (order n = ord(a)), any translation-invariant
graph on it is a circulant / abelian Cayley graph, whose spectrum is
exactly given by character sums over the generating (shift) set S:

    lambda(chi) = sum_{delta in S} chi(delta)

for chi ranging over the n characters of Z/nZ. This is a clean,
standard fact for abelian Cayley graphs (no representation-theoretic
complications as in the nonabelian case) -- see e.g. Liu, "Eigenvalues
of Cayley Graphs" (arXiv, circulant case, eq 2.1), or the classical
Paley graph computation (generating set = quadratic residues mod p),
which is the closest known relative: QR-generated circulants get
their spectral gap from classical Gauss-sum square-root cancellation
on the Legendre symbol.

Here the generating/shift set is NOT literally "QR mod n" -- it's
"delta such that disc(u_delta) is a QR mod p", where u_delta is
itself a nonlinear (curve-arithmetic) function of delta. So the
relevant object is a MIXED exponential sum:

    sum_{delta in target range} chi(delta) * Legendre(disc(u_delta) / p)

for chi a nontrivial additive character of Z/nZ. This is exactly the
genre of sum advisory-7 section 7.1 already built a Weil-II/Lang-torsor
bound for (characters of J(F_p) on s(C(F_p))) -- and section 7.2 shows
that bound is quantitatively too weak for uniform equidistribution at
the actual factor-base scale. Open question flagged mid-thread: does
this shift-graph route reduce to that same insufficient bound, or is
it a genuinely different sum with better constants? Not yet resolved.

## 4. Scope of what's actually needed (important simplification)

Established in conversation: we do NOT need a global spectral gap on
all of <a> (size n ~ p^2). We only need uniform mixing restricted to
a target set of Delta's of size B ~ p^(4/5)/p^2 relative to <a> -- i.e.
local/small-set mixing on the actual O(B) or O(p^(4/5)) set of Delta's
the algorithm cares about, not worst-case-over-all-characters
equidistribution. This is a materially weaker ask than what section
7.1-7.2 ruled out (which was specifically sup-norm / every-character
uniformity). Caveat flagged: this may not be a genuinely new route so
much as a new way to *compute or bound* E(S,S) itself, since
small-set mixing between two size-B-ish sets is itself an
E(S,S)-flavored second-moment quantity. Real progress either way, but
worth being honest that the hard content could resurface here in a
different guise (bounding variance of edge-counts between small
subsets) rather than actually being dodged.

Also established: delta does NOT need to range over all of <a> --
a bounded/limited subset suffices, per the O(B)-scale target above.
The exact size of that subset is NOT YET DETERMINED (open item, see
section 6 below).

## 5. The addition-law mechanism: closed-form, bounded-degree, verified in code

Question raised: is disc(u_delta), as a function of delta, an honest
bounded-degree rational function (Weil-bound-amenable), or does it
inherit case-branching from Cantor's algorithm (gcd steps), which
would break a clean exponential-sum argument?

Resolved (partially) by inspecting the actual codebase
(`trial3_phi.jl`, the phi-function / residual-intersection machinery
already used in the Julia pipeline):

  - `build_phi_mumford`: constructs phi(x,y) = a*x^2 + b*x + c + d*y
    (d=1 normalized) vanishing at one anchor point P0 and at the
    2-point support of a Mumford divisor D=(u,v). This is 3 linear
    conditions on (a,b,c), solved by direct substitution/division --
    a genuine rational function of the inputs (px, py, u0, u1, v0, v1),
    NO gcd/branching. Confirms the intersection-theoretic addition law
    (interpolate a low-degree function through known points, intersect
    with the curve, read off the residual) is implemented exactly this
    way already, not via Cantor's algorithm.

  - `phi_residual_mumford`: computes N(x) = phi(x,y)^2 - f(x) (degree
    5, since f has degree 5 => F_POLY has 6 coefficients), strips the
    known root at px (synthetic division, Step 1) and the known
    degree-2 factor u(x) (polynomial division, Step 2), leaving a
    monic residual quadratic s(x) = u_RS(x) via one field inversion
    (inv_s2_const, precomputed/cached per curve). This residual
    quadratic's coefficients (c1_rs, c0_rs) are rational functions of
    the inputs of SMALL FIXED DEGREE -- exactly the closed form needed
    to feed a Weil-bound estimate on the discriminant character sum.

  - The actual split/discriminant check matches the "1/2 event"
    exactly: `disc = c1_rs^2 - 4*c0_rs`; `sq = sqrt_fp_fast(disc)`;
    if `sq === nothing` the residual pair is a Galois-conjugate
    (non-split) pair (SENTINEL_PT branch); otherwise xR, xS are
    computed directly from the QR square root. This is a literal,
    already-instrumented Legendre-symbol check on a concretely
    computable value -- good, this is real ground truth to build the
    character sum on, not a hypothetical.

IMPORTANT CAVEAT / discrepancy noted but not yet resolved: this code
path (`phi_residual_mumford`, the "k=1 fast path" per its own
comments) is a 1-ANCHOR-POINT + 2-POINT-DIVISOR -> 2-POINT-RESIDUAL
construction (phi is degree 2 in x, degree-5 N(x), strips 1+2=3 known
roots leaving a degree-2 residual). The verbally-described construction
in this conversation (a CUBIC through 4 points: P1, P2, and the
2-point support of delta*a) is a different, higher-degree relative --
degree-3 in x, N(x) degree 6, strips 4 known roots leaving a degree-2
residual. Both are legitimate genus-2 addition-law realizations (this
is the general k=1 vs k>=2 distinction the code comments reference),
but they are NOT the same primitive. Open question raised at the end
of the last exchange, not yet answered: does the delta-shift
construction want to reuse the k=1 phi machinery directly (treating
delta*a as playing the anchor-point role), or does it need the
general k>=2 / cubic-through-4-points construction (treating delta*a
as a 2-point divisor being absorbed alongside P1, P2)? The original
verbal description (delta*a absorbed alongside P1+P2, both feeding a
cubic) points at the second, but the fast/already-tested code path is
the first. This needs to be pinned down before the degree bookkeeping
in the Weil-sum estimate can be trusted.

## 6. Open items / next steps

1. **Which primitive?** Resolve the k=1-anchor vs k>=2/cubic
   discrepancy in section 5 above. Determines the actual degree
   bookkeeping for everything downstream.

2. **Degree of disc(u_delta) as a function of delta itself.** Section
   5 establishes bounded degree in the *input point coordinates*
   (px, py, u0, u1, v0, v1, etc.) for a FIXED such input. But delta
   itself parametrizes which point delta*a is, i.e. the actual
   dependence on delta goes through the scalar-multiplication /
   division-polynomial step (jac_mul / jac_mul_raw in the codebase),
   whose degree in delta is expected to grow like O(delta^2) (genus-2
   analogue of elliptic division polynomials). This is the term that
   has to be weighed against the Weil-bound error O(d * sqrt(p)) where
   d = deg_delta(disc(u_delta)). NOT YET COMPUTED: what's the actual
   degree growth of jac_mul/jac_mul_raw in this codebase, as a
   function of the scalar argument? Needed to know how large a range
   of delta the Weil bound can tolerate before the error term
   swamps the O(B)-scale count is needed.

3. **How large a delta-range is actually needed?** Established that
   it need not be all of <a> (order n ~ p^2), and that the target
   scale is tied to B ~ p^(4/5) / p^2 ... exact relationship between
   (size of delta-range) and (small-set mixing strength needed to
   beat the B^2 shortfall of section 7.5) is NOT YET derived. This is
   probably the single most important missing calculation -- it's
   what would tell us whether the Weil-bound-tolerable delta-range
   (from item 2) is anywhere near sufficient.

4. **Does the mixed character sum reduce to the already-insufficient
   section 7.1 bound, or is it a genuinely different quantity with
   better constants?** Flagged as open in section 3 above, not
   investigated further yet.

5. **Reframe check:** is small-set mixing between two B-ish subsets
   of Delta-space actually a materially different quantity from
   E(S,S) itself, or just E(S,S) computed a different way? If the
   latter, this line of inquiry may still be worth it (a new
   *computational/estimation* angle, per item 8(c)'s spirit) even if
   it doesn't produce a new *proof* route.

## 7. Honest assessment

This is a genuinely different angle from the four already-exhausted
in the advisory (Sidon/Cauchy-Schwarz, Ortega-Prendiville Fourier,
Lang-torsor Weil bound, FFKW 4th moment) in that it's an orbit/mixing
argument rather than a direct Fourier or energy argument, and the
weakened target (local mixing on a size-B set, not global sup-norm
equidistribution) is a real and correct simplification given what the
complexity claim actually needs. But it is NOT yet a bound: the
degree-in-delta growth of scalar multiplication (item 2), the
required delta-range vs mixing-strength relationship (item 3), and
the risk of silently reducing to the same insufficient Weil bound
(item 4) are all open and could each independently kill this
approach. Worth continuing to chase, but should not be treated as
more than a plausible unexplored direction until at least item 3 is
pinned down numerically.

## 8. Update: closest literature analogue found, resolves item 2, sharpens item 3

Correction to section 5/item 2's framing: the degree-in-input-point-
coordinates bound is uniform regardless of which delta*a is plugged
in (confirmed correct -- there is no "symbolic in delta" object
needed; each delta gives a concrete group element computed once, and
the closed-form-rational-function argument applies identically no
matter how that element was reached). Item 2 as originally posed was
a wrong question, conflating this with elliptic-curve-style DIVISION
POLYNOMIALS (a single object psi_n(x), polynomial in x, whose DEGREE
IN n grows like n^2 -- this is the right analogue, but it enters
differently than originally framed: see below.

Farashahi & Shparlinski, "Pseudorandom Bits From Points on Elliptic
Curves" (2010, arXiv:1005.4771) is the closest published analogue
found. They bound exactly this shape of sum for elliptic curves:

    sum_{Q in H, Q != O} psi( sum_i c_i * x(d_i * Q) )  = O(s D^2 sqrt(q))

(their Lemma 5, quoting Lange-Shparlinski 2005) for H an arbitrary
SUBGROUP of E(F_q), D = max(d_i) the largest multiplier used. Two
structurally important features:

  (a) The bound has NO dependence on the subgroup order t = |H| at
      all -- only on D (how far you multiply by). Mechanism: fold the
      group-sum into a FIELD-sum via u = x(Q), using that each field
      element is hit by x() either 0 or 2 times (weighted by
      1 + chi(u^3+au+b)), then apply the ordinary Weil bound to the
      resulting rational function Phi_{m,n}(X) = f_m(X)f_n(X) /
      (g_m(X)g_n(X)), built from division polynomials
      (deg f_n = n^2, deg g_n <= n^2-1). This DIRECTLY CONFIRMS the
      thing flagged in conversation ("the degree bound is the same
      regardless of which delta*a you pick") is not a coincidence --
      this whole genre of bound is subgroup-size-independent by
      construction, it only cares about multiplier range.

  (b) Non-degeneracy (needed so the Weil bound isn't vacuous) is
      Lemma 4: Phi_{m,n} is never a perfect square of a rational
      function, for m != n and b != 0 -- a clean algebraic condition,
      not a smallness condition on the group.

Translation to this project's genus-2 setting: delta plays the role
of their n (or d_i); disc(u_delta) being a QR plays the role of their
chi(x(mP)x(nP)). The genus-2 analogue of their Phi_{m,n} would need
the genus-2 addition-law formulas already found in the codebase
(build_phi_mumford / phi_residual_mumford in trial3_phi.jl) recast as
explicit rational functions of delta via a genus-2 division-polynomial-
type object (giving u_delta, v_delta as rational functions of delta
for a fixed base divisor) -- this object is the concrete missing
ingredient, not yet written down, but not conceptually novel: genus-2
explicit addition formulas (Cantor / Flon-Oyono-Prouff / Uchida-style,
or Kummer-surface/theta-coordinate formulations) are known in the
literature and should supply it.

Sharpened balance calculation (answers item 3, at least at the
single-character/worst-case level): if genus-2 division-polynomial
degree growth is O(delta^2) as in the elliptic case, summing delta in
{1,...,D} gives Weil error O(D^2 sqrt(p)) against a main term ~ D/2
(half the delta's split). Naive single-sum cancellation needs
D/2 >> D^2 sqrt(p), i.e. D << 1/sqrt(p) -- impossible (D >= 1
required). SAME SHAPE OF FAILURE as advisory section 7.2's threshold.
This is a real negative data point for the naive/worst-case version
of this approach.

HOWEVER: this negative calculation is for a SINGLE character / single
worst-case sum, mirroring exactly the sup-norm framing already ruled
out in section 7.1-7.2. What's actually wanted (per section 4 above,
and the local-mixing / small-set framing established in conversation)
is the AGGREGATE / fourth-moment behavior averaged across many
points/characters at once -- which is exactly what Farashahi-
Shparlinski's own Theorem 6/7 do (average U(N) or V_k over ALL
P, Q in E(F_q) or R in H, getting savings like O(D^4 sqrt(q)) against
a trivial bound of O(D^2 q^2), i.e. a genuine improvement for
D <= q^(1/4-eps), via Cauchy-Schwarz / second-moment technique,
INSTEAD OF needing single-sum square-root cancellation). This
matches the local/small-set mixing target from section 4 much more
closely than a single-character estimate does, and is the natural
next thing to translate to the genus-2 setting.

Updated open items:
  - Item 2 (original framing) is resolved/moot: no symbolic-in-delta
    degree blowup at the level originally worried about; the real
    degree-in-delta object is the genus-2 division-polynomial-type
    map, analogous to their f_n/g_n, degree ~ delta^2 expected but
    NOT YET DERIVED explicitly for genus 2.
  - Item 3 (delta-range vs mixing strength) is now sharpened: the
    naive single-character/worst-case version FAILS for the same
    reason section 7.2 already failed (needs D << 1/sqrt(p),
    impossible). The aggregate/4th-moment version (Farashahi-
    Shparlinski Theorem 6/7 style) is the version actually worth
    pursuing, and has NOT yet been translated to genus 2 or checked
    for whether its threshold (their D <= q^(1/4-eps) analogue) lands
    anywhere near the B ~ p^(2/5) scale this project needs.
  - New concrete next step: write down the genus-2 division-polynomial-
    type formula (u_delta, v_delta as explicit rational functions of
    delta for fixed base divisor), using the existing
    build_phi_mumford / phi_residual_mumford machinery as the starting
    point, then attempt the Farashahi-Shparlinski-style SECOND-MOMENT
    (not single-sum) argument, averaging over many delta AND many base
    divisors simultaneously, to see whether a nontrivial threshold
    exists at the actual B ~ p^(2/5) scale.
