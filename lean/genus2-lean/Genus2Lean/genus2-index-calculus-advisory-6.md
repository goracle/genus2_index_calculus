Security Advisory: Heuristic Complexity of a Genus-2 Index Calculus Attack
(Revision 7 — mod-p reduction, factor-base classification, a
symmetry-quotient correction, and a resolution of the 7(b)(i)
exponential-sum question)

Summary
-------

This revises advisory-6. That document reported a positive
characteristic-0 empirical result for assumption (a) (generic
finiteness of the specialized 4-equation Mumford-coefficient-matching
system): 2475 witness points, all dimension 0 and degree 1, for one
tested (K=2, c=2) instance, with mod-p behavior explicitly left open
pending the Hensel-lifting step.

This revision reports that follow-up. The strict near-integer
Hensel check failed for all 2457 witness points on file (a design
mismatch with what a1/a2/b1/b2 actually are, not a finiteness
failure — see section 6.1). Reclassifying against two empirically
discovered, and independently verified, minimal polynomials instead
gives a concrete mod-p factor-base count: 313 raw d1-type and 63 raw
d2-type witness points, reducing to 36 and 9 distinct values
respectively once correctly quotiented by the confirmed a1<->a2 /
b1<->b2 swap symmetry (a bug in an earlier quotient attempt, which
tested only the combined swap instead of the full order-4 group, is
also documented and corrected here). Assumption (a)'s remaining open
items — mod-p-specific finiteness as a theorem rather than an
empirical count, and cross-instance/cross-p consistency — are
unchanged from revision 6.

This revision also settles item 7(b)(i) as posed in advisory-6: it
was an open question whether a genuine, fully uniform (all character
orders, no exceptional set) Weil-type exponential-sum bound exists
for characters of J(F_p) evaluated on s(C(F_p)), as an alternative to
the Ortega-Prendiville bulk/Fourier route. Such a bound is
constructed below (section 7.1) via Lang-torsor character sheaves on
J and Deligne's Weil II, and is provably stronger in scope than
Ortega-Prendiville (no exceptional set). However, it is then shown,
by direct computation, that this bound is quantitatively insufficient
to establish equidistribution of N(Delta) for any factor base of size
o(p) -- not merely at the actual scale B ~ p^(2/5) -- because
square-root cancellation per character, raised to the fourth moment
and summed over |J| ~ p^2 characters, structurally cannot beat B^4
unless B is a positive proportion of the full curve. This closes
7(b)(i) negatively: no bound of this general type, however sharp,
can resolve assumption (b) via the sup-norm route. Section 7.2
reframes the remaining problem correctly, following an external
observation: the expectation E[N(Delta)] over uniformly random Delta
is an exact identity requiring no Sidon input, no Fourier bounds, and
no pseudorandomness assumption, obtained by pure double-counting.
The open content of assumption (b) is not the expectation but the
hit probability Pr[N(Delta) > 0], which by Paley-Zygmund reduces
exactly to a second-moment / additive-energy bound. Section 7.2
shows this reduction is tight: the required second-moment bound is
algebraically equivalent to the same energy quantity E(S,S) that
Steps 2-3 (sections 3-5) were already built around, so the
reframing correctly identifies the minimal remaining target rather
than supplying a new route around it.

This revision does not revisit assumption (a) further, and sections
1-5 below are carried forward unchanged from revision 6.

1. Restating the heuristic to be justified
-------------------------------------------

As in advisory-5, fix a genus-2 curve C over F_p, J = Jac(C), a
factor base F subset of C(F_p) of size B = #F, and consider the
matching condition

R(alpha; P1,P2) = R(alpha'; P3,P4),  P1,...,P4 in F

where R(alpha; P1,P2) = Reduce(alpha*a - P1 - P2) is the Cantor-reduced
Mumford representative. The original heuristic (advisory-5, section 5)
asserted directly:

    Pr(hit) ~ B^4 / p^2                                          (H0)

on the grounds that the B^4 factor-base tuples map "close to
equidistributed" into J. This revision derives (H0) from more
primitive assumptions.

2. Step 1: reduction to a sumset problem
-----------------------------------------

Let S = F + F = { P1 + P2 : P1, P2 in F } subset of J (all sums taken
in the Jacobian group law, after Cantor reduction). The matching
condition R(alpha; P1,P2) = R(alpha'; P3,P4) is equivalent to

    (P1 + P2) - (P3 + P4) = (alpha - alpha') * a   in J.

Writing Delta = alpha - alpha', a hit occurs iff Delta * a lands in the
difference set S - S. This reduces the density question to a concrete
combinatorial one: how large is S - S, and how uniformly is it
populated?

By Cauchy-Schwarz,

    |S - S| >= |S|^4 / E(S, S)                                   (1)

where E(S,S) = #{(s1,s2,s3,s4) in S^4 : s1 - s2 = s3 - s4} is the
additive energy of S. This step is exact; no assumption is used here.

3. Step 2: what quasi-randomness of F+F would give
----------------------------------------------------

If F does not possess strong additive structure, the standard
expectation is that S = F+F is close to maximal size (|S| ~ B^2/2,
since S is symmetric under P1 <-> P2) and that its additive energy is
close to the minimum possible for a set of that size:

    E(S,S) ~ |S|^4 / |J| ~ (B^2/2)^4 / p^2 = B^8 / (16 p^2)        (2)

Substituting (2) into (1):

    |S - S| >= p^2 (up to constants)                               (3)

If, further, S - S is not merely large but roughly uniformly
distributed over its support in J, then

    Pr(hit) = Pr_{Delta}[Delta*a in S-S] = |S-S|/|J| ~ B^4/(4p^2)   (4)

recovering (H0). This derivation is a genuine improvement over
asserting (H0) directly: it isolates the load-bearing hypothesis as a
single, named, standard object in additive combinatorics — the
additive energy of F+F — rather than a direct claim about the
distribution of the matching condition itself. But it is still
conditional on that hypothesis, which we now examine rather than
assume.

4. Step 3: is F+F actually quasi-random? A structural result for genus 2
---------------------------------------------------------------------------

The naive way to justify the hypothesis in Step 2 — "F was not chosen
with any deliberate additive structure, therefore F+F is quasi-random"
— is not a valid inference. Absence of a specified structure is not
evidence of pseudorandomness; sets built from unremarkable-looking
enumeration procedures (arithmetic progressions, coordinate-ordered
lists, coset-biased samples) routinely fail to be quasi-random, and
some of these failure modes are specific to curves of small genus
(automorphisms, torsion structure). This was the actual gap in the
original heuristic, and revision 5 did not close it.

It can be closed, for genus 2 specifically, using a recent structural
theorem about generalized Jacobians of curves.

Theorem (Forey, Fresan, Kowalski, "Sidon sets in algebraic geometry",
2023; Theorem 1, case g=2). Let C be a smooth genus-2 curve over a
field k, let delta be a k-rational divisor of degree 1 on C, and let
s: C -> J be the map x |-> (x) - delta into the Jacobian. Then s(C(k))
is a symmetric Sidon set in J(k): every solution of

    s(x1) + s(x2) = s(x3) + s(x4),   xi in C(k)

satisfies either {x1,x2} = {x3,x4}, or x2 = iota(x1) and x4 = iota(x3),
where iota is the hyperelliptic involution on C (every genus-2 curve
is hyperelliptic). The "center" of the symmetric Sidon set is the
constant value a0 := s(x) + s(iota(x)), independent of x.

Consequence for F+F. Write T := s(F) subset of J for the image of the
factor base itself (|T| = B) — distinct from S := F+F = T+T (|S| ~
B^2/2), which is the object Steps 1-2 above are about. Keeping T and S
separate matters here: the Sidon property is a statement about T, and
the energy computation below is about how T's collision structure
constrains S.

If the factor base F is constructed so that it does not contain
hyperelliptic-involution pairs — i.e., for each x-coordinate used, at
most one of the two points {(x,y), (x,-y)} on the affine model is
included — then T contains no symmetric solutions, and T is a genuine
(non-symmetric) Sidon set: every sum P1+P2 with P1,P2 in T is achieved
by exactly one unordered pair {P1,P2}, with no exceptions.

This gives, essentially by definition of the Sidon property, that the
representation function of T (not of S) satisfies

    r_{T,T}(g) in {0, 1, 2}  for every g in J                     (5)

(the value 2 accounts for the two orderings (P1,P2) and (P2,P1) of a
given unordered pair). This is close to the strongest possible
non-degeneracy statement available for a set of this size — stronger,
in fact, than the generic quasi-random heuristic in Step 3 assumed,
since (5) pins down the representation function pointwise rather than
only on average. Consequently, the additive energy of T itself is

    E(T,T) = sum_g r_{T,T}(g)^2 <= 4 * #T <= 4 * C(B,2) ~ 2B^2      (6)

Note (6) is a much stronger (smaller) bound than the quasi-random
estimate (2) would give for a set of size B — a Sidon set has energy
linear in B^2, not the scaling a generic quasi-random set of the same
size would have. This is expected: Sidon sets are the extremal
low-collision case. It is E(T,T), via (6), that feeds into the Fourier
analysis of T in the next section — the object being shown Fourier-flat
there is T = s(F), and the sumset S = T+T inherits equidistribution
properties from T's flatness, not the other way around.

5. Step 4: Fourier uniformity of Sidon sets — what it gives, and where it runs out
---------------------------------------------------------------------------------------

The Cauchy-Schwarz route from Step 2 (equation (1)) is the wrong tool
once F is known to be Sidon rather than merely low-energy: Cauchy-Schwarz
is tight precisely when energy is *concentrated*, the opposite of the
Sidon regime, and applying it to a Sidon set's energy bound (6) gives
only a weak lower bound on |S-S| (of order B^6, far short of what a
density argument needs). The natural alternative is to use the Sidon
property to get Fourier uniformity of T = s(F) directly.

Theorem (Ortega-Prendiville, "Extremal Sidon sets are Fourier uniform",
2021, Theorem 1.2). For a Sidon subset of [N] subset of Z of size comparable to the
extremal size N^(1/2), the Fourier transform of its indicator function
is uniformly close to that of a random set of the same density, with
an explicit error term that is small precisely at that extremal size.

The proof (van der Corput differencing, their Lemma 2.1-2.2) uses only
the Sidon property and a bound on the intersection of the Sidon set
with a small set; the mechanism generalizes to a finite abelian group G
by replacing intervals with subgroups (or Bohr sets). In fact the key
sub-step — that a Sidon set restricted to any subgroup H is still
small — is *easier* to establish in a group than in Z: since any
subset of a Sidon set is Sidon, and any Sidon set
in a finite abelian group of order M has size O(sqrt(M)) (Babai-Sos,
the direct generalization of the Erdos-Turan bound used implicitly by
Ortega-Prendiville), the intersection of a Sidon set with any subgroup
H is O(sqrt(|H|)) for free, with no additional input needed.

We carried out this generalization ourselves; it is an adapted
calculation, not a result stated in or directly implied by
Ortega-Prendiville's paper (which proves Theorem 1.2 only for subsets
of [N] subset of Z). Nothing below this point should be attributed to
the cited theorem itself — it is our own re-derivation of their
argument's structure with G = J(F_p) in place of Z, and should be
checked independently before being relied on. With that label attached:
we redid the van der Corput computation with G = J(F_p) (N := |G| ~
p^2) and T = s(F) (|T| = B), rather than importing Ortega-Prendiville's
stated bound (which is calibrated for a Sidon set of size ~N^(1/2) and
does not by itself say anything about groups other than Z). Two of the three
cross-terms in their computation are actually cleaner in a group than
in Z (no boundary/edge loss under translation, since translating a
group by any element gives the group back exactly, unlike translating
a sub-interval of Z). The substantive term is the Sidon-collision term,
controlled via the group analogue of their Lemma 2.2, which transfers
essentially verbatim. Optimizing the resulting bound

    |f-hat(chi)|^2  <<  N + H - B^2 + BN/H + B

over the averaging-kernel scale H gives H = sqrt(BN) and

    |f-hat(chi)|^2  <<  N - B^2 + 2*sqrt(BN) + B.

For B comparable to N^(1/2) (the extremal regime the cited theorem
targets) this reproduces their result. For B << N^(1/2) — which is the
actual regime here, since B ~ p^(2/5) while N^(1/2) ~ p — the -B^2 term
is negligible and the bound degrades to

    |f-hat(chi)|^2  <<  N  (up to lower-order terms),

i.e. |f-hat(chi)| = O(sqrt(N)), which is no better than the trivial
bound (indeed worse than the trivial bound |T-hat(chi)| <= B, since
B << sqrt(N) in this regime). This is not a bookkeeping artifact: it is
the genuine content of the word "extremal" in the theorem's title. The
van der Corput method, honestly optimized, does not produce nontrivial
sup-norm Fourier uniformity at the factor-base scale B ~ p^(2/5). A
different technique, or extra arithmetic input specific to J(F_p)
(e.g. a genuine exponential-sum/Weil-type bound for characters
evaluated along the curve, of the kind gestured at earlier in this
project's discussion but never derived), would be needed to get a
uniform bound at this scale, and we do not have one.

What the Sidon property does still give, unconditionally, at any scale
of B, is the *aggregate* (Markov/Chebyshev-type) statement obtained
directly from the energy bound (6), without going through a sup-norm
argument: since Sigma_{chi != 1} |T-hat(chi)|^4 <= N * E(T,T) <= 2*B^2*N,
the number of nontrivial characters with |T-hat(chi)| > t is at most
2*B^2*N/t^4. Taking t = C*sqrt(B*log N) gives that all but an
O(N/(C^4 (log N)^2))-sized exceptional set of characters satisfies the
desired bound. This is, precisely, a statement about the distribution
of Fourier coefficients of T, not directly a statement about
(alpha, alpha') pairs; going from "most characters are small" to "most
pairs see quasi-random behavior" requires an additional standard but
non-trivial step (bounding how the exceptional characters could bias
Pr_{Delta}[Delta*a in S-S] for a typical Delta, e.g. via a second
Erdos-Turan-type inequality or a further averaging argument), which we
have not carried out here. The defensible claim at this point is
narrower than "most pairs behave quasi-randomly": it is that the
obstruction to quasi-randomness, if any, is concentrated on a small,
explicitly bounded set of frequencies — a necessary but not yet
sufficient condition for the pairwise statement.

Revised status of hypothesis (H1). Full equidistribution of S-S over
J — needed for the density estimate (H0)/(4) to hold for *every*
candidate pair — remains open at the factor-base scale actually in
use. What is established is narrower than a bulk pairwise statement:
the Fourier coefficients of S are proven to be small outside a small,
explicitly bounded exceptional set of frequencies (a necessary
condition for S-S to be well-spread). Converting this into a direct
statement about typical (alpha, alpha') pairs is a further step that
has not been carried out. This is a materially better-grounded
position than either the original heuristic or the Cauchy-Schwarz-
based revision, but it should not be overstated in either direction:
it is a partial, frequency-level result, not yet even a typical-case
pairwise one, and closing the remaining gaps looks like it needs
either the additional averaging step noted above or input beyond
generic additive-combinatorial machinery.

6. Empirical result on assumption (a): generic finiteness, characteristic 0
--------------------------------------------------------------------------

Advisory-5's assumption (a) — generic finiteness of the specialized
matching system, with an O(1) root count independent of p — has now
been tested directly for one instance (K=2, c=2 sample) via numerical
irreducible decomposition (HomotopyContinuation.jl).

Setup actually solved. The matching condition was reformulated using
the confirmed a1<->a2 / b1<->b2 swap symmetry (verified numerically
before proceeding — u and v coefficients from both samples are exactly
invariant under the swap) into elementary-symmetric-style target
variables, then decoupled via iterated norm elimination: every
Fu/Fv generator was verified to be degree <=1 in each of the four
square-root generators (wa1,wa2,wb1,wb2), which is exactly the
precondition needed for exact (not approximate) elimination of those
variables via A^2 - B^2*f(t_i). The resulting system is 12 equations
in 12 unknowns (wa1,wa2,wb1,wb2,a2,a1,b2,b1,U0,U1,V0,V1), lifted from
GF(p) to Z (canonical representative lift) and solved as an affine,
non-homogenized system over C.

Result. The numerical irreducible decomposition finished (~26900s)
with 2475 witness points, all of dimension 0, and — critically — every
one of the 2475 components has degree exactly 1. There is no
component of dimension >= 1.

What this establishes, precisely. Zero-dimensionality with all-degree-1
components means: for this specialized instance, the lifted
(characteristic-0) system has finitely many solutions, all simple
roots — no positive-dimensional solution locus, and no non-reduced
(multiple) roots beyond whatever multiplicity is already accounted for
by the swap symmetry used in the decoupled construction. This is
direct evidence for generic finiteness (assumption (a)), for the
specific instance tested, in characteristic 0.

What this does not establish. The run's own printed verdict is worth
repeating verbatim as the correct scope of the result: this is
evidence that the mod-p system is finite too, not a proof for the
mod-p system specifically — reduction mod p can both create and
destroy positive-dimensional behavior relative to a characteristic-0
lift. Whether this specific finiteness result survives reduction mod
the actual prime p in use is a separate question, addressed by the
Hensel-lifting step (see the operational note following this
advisory). Additionally, the run logged repeated warnings that some
homotopy paths in the u-regeneration intersection step failed,
localized specifically to elimination of the U0/U1 target variables
(degree-17 generators) rather than the V0/V1 (degree-25) or curve
generators; these warnings were confirmed to originate only from
intermediate stages of the decomposition, with the final witness set
reported as complete (status "done" for both the witness-set
computation and the decomposition step). This should still be treated
as a single-instance result: it has not yet been confirmed to
reproduce under a different random monodromy seed, and it covers one
(K=2, c=2) sample, not a survey across instances or across p.

Practical consequence for the O(p^(4/5)) complexity claim. Advisory-5's
balancing equation assumed O(1) roots per hit, independent of p; this
result is consistent with that assumption (root count = 1, the
smallest possible O(1) value, for the instance tested) but does not
yet establish independence from p, since only one instance has been
solved. It substantially de-risks assumption (a) relative to where
revision 5 left it, without yet closing it.

6.1 Follow-up: mod-p reduction, classification, and the true d1/d2 factor-base size
-------------------------------------------------------------------------------------

The Hensel-lifting step flagged as the next open item above has now
been run and followed through to a concrete mod-p result. Summary of
what changed since the 2475-witness-point characteristic-0 result:

Hensel verification, as originally run. Reducing each of the 2457
saved witness points mod p (a strict tol=1e-6 near-integer check, per
the operational note's own reduce_mod_p) failed for all of them:
0/2457 passed. This does NOT mean the characteristic-0 result is
wrong, or that the mod-p system is not finite — a1/a2/b1/b2 (and
wa1/wa2/wb1/wb2, U0/U1/V0/V1) were never expected to be near-integers
in the first place; reduce_mod_p's near-integer assumption is a
design mismatch with this system, not a finding about the system
itself (see below).

Reclassification via known minimal polynomials. Separately, guess()
(Nemo's algebraic-number recognition routine) identified two minimal
polynomials recurring across a1, a2, b1, b2 at many witness points:
x^2+x+1 (roots the primitive cube roots of unity, irreducible over
F_p at this p since p mod 3 = 2 — these roots live in F_p^2) and
x^3-x^2+1 (three roots, all in F_p at this p). Classifying every
witness point's (a1,a2,b1,b2) against these two polynomials (rather
than against reduce_mod_p's near-integer assumption) gave:

  - d1 (all four of a1,a2,b1,b2 of cubic_type, i.e. in F_p): 313 raw
    witness points
  - d2 (all four of omega_type, i.e. in F_p^2 \ F_p): 63 raw witness
    points
  - 0 points with an unrecognized coordinate (at MATCH_TOL=5e-4)

Because guess() relies on a heuristic enclosure radius rather than a
rigorous error bound, this reclassification was independently
verified two further ways before being trusted: (i) the ~30
borderline coordinate instances sitting closest to MATCH_TOL were
each certified via HomotopyContinuation.jl's certify() (Smale
alpha-theory) as genuine isolated simple roots of the full 12-variable
system, and their certified locations sit 2e-8 to 1.6e-5 from the
relevant known root — comfortably resolved, not an artifact of a loose
match tolerance; (ii) independently of guess() entirely, the
distance from every one of the 2457*4 = 9828 (a1,a2,b1,b2) coordinate
instances to the nearer of the two polynomials' exact symbolic roots
(computed once via Nemo's roots(), no heuristic radius) was measured
directly: the distribution has a hard wall at ~2.8e-4 with nothing
beyond it (median 2.4e-7, 97.4% under 1e-5), rather than the roughly
uniform spread up to the classification tolerance that an
accidental-fit artifact would produce. Both checks support the same
conclusion: a1/a2/b1/b2 genuinely satisfy these two low-degree
polynomials across the tested witness set, and the classification
above is not a guess()-radius false positive.

The swap-symmetry quotient, and a bug found and fixed in it. The
confirmed a1<->a2 / b1<->b2 swap symmetry (section 6 above; also
independently re-confirmed by 01_elim2_main.jl's run_symmetry_checks
output during this follow-up work) means the true symmetry group
acting on (a1,a2,b1,b2) labels has order 4 (id, swap_a alone,
swap_b alone, both together) — the two swaps are INDEPENDENT
generators, not one combined operation. An initial dedup pass tested
only the combined-swap element and undercounted the quotient (156
"distinct" d1 points from 313 raw candidates). Quotienting correctly
by the full order-4 group gives:

    d1: 36 distinct (a1,a2,b1,b2) values, mod symmetry
    d2: 9 distinct (a1,a2,b1,b2) values, mod symmetry

Both counts saturate their combinatorial ceiling exactly: d1 draws
(a1,a2) and (b1,b2) independently, each an unordered pair from the
3-element root set of x^3-x^2+1, giving C(3+1,2)^2 = 6x6 = 36 with
every combination realized; d2 does the same over the 2-element root
set of x^2+x+1 in F_p^2, giving C(2+1,2)^2 = 3x3 = 9, again fully
realized. No gaps in either case.

Status. This settles, for the tested instance, the concrete question
of how many distinct d1- and d2-type factor-base labels the
characteristic-0 witness set actually contains after correcting for
the known symmetry: 36 and 9 respectively. It does not by itself
close assumption (a)'s remaining open items (mod-p-specific
finiteness proof, cross-instance/cross-p consistency, reproducibility
under a different monodromy seed) — those are unchanged from the
status above.

Resolution of the label-vs-full-fiber question. A distinct question
surfaced during this work: each (a1,a2,b1,b2) label corresponds to
multiple distinct full 12-coordinate witness points — checked directly
against this run's 2457-point output (witness_points.csv), grouping by
(a1,a2,b1,b2) canonicalized under the confirmed order-4 swap group.
Result: 240 distinct labels across this run's full witness set (this
count is taken over all witness points together, before splitting by
d1/d2 type as sections 6/6.1 do above — how it decomposes against the
36 d1-type and 9 d2-type label counts, e.g. whether 240 = 36 + 9 +
mixed/off-target cases, has not been checked and should not be assumed;
flagged here rather than asserted), with a non-constant per-label multiplicity ranging
from 2 to 16 full witness points per label (mean multiplicity ~10.2;
distribution: 1 label at mult 2, 3 at mult 3, 40 at mult 4, 1 at mult
6, 9 at mult 7, 88 at mult 8, 12 at mult 12, 1 at mult 14, 5 at mult
15, 80 at mult 16). All 2457 full 12-coordinate points are pairwise
distinct at the pipeline's own match tolerance (1e-4) and remain so at
a looser 1e-3 — this is not near-duplicate numerical noise collapsing
onto a small solution set; the multiplicity is real.

The mechanism, traced directly against build_decoupled_system (section
6.2 above) rather than assumed: Fu_decoupled's 4 equations (2 per U_i)
constrain U_0, U_1 given (wa1,wa2,a1,a2) — but (wa1,wa2,a1,a2) is only
pinned to 4 values by the 2 curve relations wa_i^2=f(a_i) (2 sign
choices per point); nothing in Fu_decoupled or the curve relations
alone forces a1, a2 down to the label's 2 specific values without also
bringing in Fv_decoupled's b-side and the cross-sample matching
(build_match_spec) — i.e. the (a1,a2,b1,b2) label genuinely
under-determines a solution point; the remaining freedom (confirmed
against the actual data: distinct wa1 values beyond a simple +/-
pair, e.g. one label's 16 points exhibit 4 genuinely different
(wa1,wa2) pairs, each further combined with 4 different (wb1,wb2)
pairs) is resolved only once U_i, V_j are pinned down consistently
with the full system. This rules out the alternative explanation
(spurious multiplicity from the elimination/solving path rather than
the geometry itself): norm_eliminate (section 6.2) and the
norm-elimination diagnostic in 02_norm_elim_diag.jl operate downstream
of and independently from this fiber — the multiplicity is present
already in what System(...) in nid_fiber_system.jl is built from
(the 4 curve relations plus the 12 Fu_decoupled/Fv_decoupled equations
directly, no intermediate elimination step), so it is a property of
the variety being solved, not an artifact of how it was solved.

Consequently: the 240-label count (36/9 restricted to d1/d2 type) is
the degree of the coarser projection onto (a1,a2,b1,b2) alone: a
projection this document does not otherwise use downstream. The
2457-point full-fiber count is the degree of the actual system solved
and certified (section 6's Smale certification, section 6.2's
generic-finiteness argument) — the right notion of "factor base size"
for consistency with the sections 1-5 theory, since T = s(F) is built
from full solution points (a Mumford representation, i.e. the full
12-coordinate data), not from x-coordinate labels alone. Treat the
2457-scale count, not 36/9, as the operative factor-base-size figure
downstream; 36/9 remains correct as a count of distinct x-coordinate
labels but is not itself the factor-base size.

6.2 An analytic argument for generic finiteness (assumption (a)),
    replacing the single-instance numerical witness count with a
    classical theorem
--------------------------------------------------------------------------

Section 6 establishes finiteness for one specialized instance,
numerically. This subsection gives an argument for generic
finiteness -- true for all but a codimension-1 (measure-zero) set of
parameter choices, not just the one instance solved -- from a
classical fact about genus-2 curves, rather than from a witness-point
count.

Reduction to a fiber-product question. Fu_decoupled/Fv_decoupled (see
build_decoupled_system) constrain the target variables U_i, V_j by two
linear equations each:

    num_1[i] - U_i * den_1[i] = 0        num_2[i] - U_i * den_2[i] = 0

(and likewise V_j against v_1, v_2). Since U_i, V_j appear only
linearly -- coefficient exactly -den[i] in each equation -- eliminating
them is exact and lossless (this is precisely what norm_eliminate
already does downstream): the system's solution set is in bijection
with the locus where sample 1's and sample 2's (u_RS, v_RS) pairs, as
rational functions of (wa1,wa2,a1,a2) and (wb1,wb2,b1,b2)
respectively, agree identically. Writing sigma: C x C -> Mumford-space
for the map (P,Q) |-> (u_RS, v_RS) of the reduced Mumford
representation of [P]+[Q], generic finiteness of the 12-variable
system is exactly generic finiteness of the fiber

    sigma^{-1}( sigma(sample 2's point) )

over sample 1's variables (a1,a2,wa1,wa2) -- i.e., whether the
sum-of-two-points map to Mumford space has 0-dimensional fibers over a
generic point of its image.

The classical fact this reduces to. For a genus-2 curve C, the map

    sigma: C^(2) -> J,   {P,Q} |-> [P]+[Q] - 2*[infinity]

(C^(2) the second symmetric power) is birational onto its image. This
is the standard Riemann-Roch consequence that makes genus-2 index
calculus work at all: a generic effective divisor D of degree 2 = g on
C has h^0(D) = 1, so D is the *unique* effective representative of its
own linear equivalence class -- equivalently, sigma is generically
injective on C^(2), hence generically injective on C x C up to the
{P,Q} <-> {Q,P} swap already accounted for by the confirmed a1<->a2 /
b1<->b2 symmetry (section 6's decoupled construction). Generic
finiteness of the 12-variable system follows directly: for a generic
point in the image of sigma, its fiber under sigma is a single point
(up to the swap), so the fiber-product system above has finitely many
solutions -- in fact exactly the (small, swap-accounted-for) multiplicity
already observed numerically, generically.

The exceptional locus, explicitly. Birationality of sigma fails exactly
where h^0(D) > 1 for D = sample 2's divisor class, i.e. exactly on the
locus D ~ K_C (D linearly equivalent to the canonical divisor of C) --
a single divisor class, hence a single point of J, hence codimension 2
in C x C and measure zero in the relevant parameter space. This is an
explicit, checkable condition: generic finiteness of the system for a
given pair of samples holds unless sample 2's target divisor class is
canonical. This can and should be checked directly against the actual
sample data (compare sample 2's divisor class to K_C, computable from
F_POLY_ASC) rather than merely assumed generic.

What this argument establishes, and what it still leaves open. This
gives generic 0-dimensionality of the system as a set (the reduced
fiber product), from a citable classical theorem, rather than from a
single numerical instance -- a materially stronger form of evidence for
assumption (a) than section 6's witness count alone, and one that
extends across parameter choices rather than being tied to the one
(K=2, c=2) instance solved. It does not by itself establish two things
section 6's numerical run checked directly: (i) scheme-theoretic
reducedness -- the theorem gives finiteness of the underlying set, not
that every point is a simple (multiplicity-1) root, which is what the
2475-witness-points-all-degree-1 result confirmed empirically for that
instance; and (ii) that the tower's cleared denominators (mspec's
CLEARED_DENOMS, saturated against in Iu_decoupled/Iuv_decoupled) don't
vanish identically on the relevant fiber, which is a construction-
specific bookkeeping fact this argument does not address. Both remain
appropriately checked per-instance (as section 6 already does via
Hensel/mod-p verification) rather than treated as consequences of the
generic argument here.

RETRACTED: why this track does NOT make section 7's variance work moot
(the paragraph below, as it stood, asserted a bridge that does not
hold -- corrected here rather than silently removed, since the
error is instructive about what X(Delta) actually is).

The original claim was that a constant fiber-degree bound d for the
projection pi: (this section's 0-dimensional variety) -> J would give
X(Delta) <= d as a deterministic pointwise bound, making section 7's
second-moment machinery unnecessary. This does not follow, because pi
and X(Delta) are counts of two different objects over two different
domains, and there is no derivation anywhere in this document
connecting them -- working it through explicitly shows they cannot be
connected this way:

  - d (section 6/6.2's object) bounds the fiber of sigma: C^(2) -> J,
    i.e. how many pairs {P,Q} of curve points map to the SAME point of
    J. It is a statement about collisions in sigma's own fibers, for a
    FIXED target point alpha in J.

  - X(Delta) (section 7's object, eq. 9) is #{(P1,P2,P3,P4) in F^4 :
    (P1+P2)-(P3+P4) = Delta} -- a count over 4-tuples drawn from the
    factor base F, as Delta ranges over J. Unwinding this via T := s(F)
    (section 4's Sidon set) and r_{T,T}, the pairwise-sum
    representation function of T, gives exactly

        X(Delta) = sum_{g in J} r_{T,T}(g) * r_{T,T}(g - Delta)

    i.e. X(Delta) is the AUTOCORRELATION of r_{T,T} with itself at
    Delta -- not a fiber count of sigma at all. Section 4 already
    proves (eq. 5, unconditionally, via Forey-Fresan-Kowalski) that
    r_{T,T}(g) in {0,1,2} pointwise for every g. Plugging this pointwise
    bound directly into the autocorrelation sum gives only
    X(Delta) <= 4 * |{g : r_{T,T}(g) != 0 and r_{T,T}(g-Delta) != 0}|,
    which can be as large as O(|S|) = O(B^2) for an unlucky Delta --
    not O(1), and not O(d) for any small d. This is exactly consistent
    with (not an improvement on) section 7.5's E(S,S) analysis: Sidon-
    ness is a U^2-level (pairwise/4th-moment) fact, and it controls
    X(Delta) only in aggregate (via E(S,S) = sum_Delta X(Delta)^2),
    never pointwise for a single adversarial Delta. There is no
    additional input in this document -- and, as far as this
    derivation goes, no available one -- that converts "sigma has
    bounded fiber degree d over a fixed alpha" into "X(Delta) is
    bounded by something small for every Delta." These are simply
    different maps (sigma: C^(2) -> J vs. the pairwise-difference map
    on T+T) with no shown relationship between their fiber structures.

Consequence: Question 3 (constant-degree stability of pi, section 6.3)
remains a legitimate open question in its own right -- it is still
needed to convert section 6's single-instance finiteness result into a
generic one, and it is still the right thing to check via a second,
independently generated (alpha,alpha') instance (see "practical steps"
below). What it is NOT is a shortcut around section 7's B^2 gap. That
gap is real, independent of Question 3, and resolving Question 3
favorably would not close it. Section 6.3's summary table should be
read with this correction: Question 3 remains open and worth
resolving for its own sake (it completes assumption (a)'s reduction
from single-instance to generic), but it is no longer FATAL in the
specific sense of substituting for section 7 -- the actual fatal,
still-open item for the O(p^(4/5)) complexity claim is section 7.5's
B^2 shortfall in E(S,S), which needs U^3-level (higher-energy)
control that Sidon-ness alone cannot supply (section 7.6's Shkredov
dichotomy), not a fiber-degree bound from section 6.

Practical steps for Question 3, unaffected by the above (still worth
doing, just not as a substitute for section 7):

It is not yet available for two concrete reasons, not merely
unproven-in-general the way (H0) is. First, the degree d is currently
known at exactly one instance (this run's (alpha,alpha'): 2457, the
full-fiber count established above) -- no second, independently
generated instance has been checked, so there is no evidence yet, one
way or the other, that this count is even approximately stable across
different (alpha,alpha') choices, let alone provably constant.
Second, even granting stability, the exceptional set where the degree
could jump has not been identified or shown to coincide with (or be
contained in) the D~K_C exceptional locus already found above --
these could be the same closed set or a strictly larger one, and
which it is has not been checked. Both are concrete, tractable,
next steps (generate one more instance and compare its fiber count;
identify the degree-jump locus explicitly) rather than open-ended
research questions, but neither is done, and this section's finiteness
result should not be read as already implying a bound on X(Delta) --
it never did, and (per the correction above) no version of it would.



6.3 Triage addendum: what is FATAL to the O(p^(4/5)) claim vs. what is
    an open DETAIL — disentangling finiteness, birationality, and degree
--------------------------------------------------------------------------

Sections 6/6.1/6.2 answer three genuinely different questions, and
prior discussion of this document (per conversation) blurred them
together in a way that made a resolved point look unresolved. This
addendum separates them explicitly.

QUESTION 1 -- Is the system finite at all (0-dimensional), for a
generic instance? -- PROVED, not merely evidenced.
Section 6.2's birationality argument is a real proof, not a numerical
observation: sigma: C^(2) -> J is birational onto its image (standard
Riemann-Roch consequence of g=2, h^0(D)=1 for generic degree-2 D),
therefore sigma is generically injective, therefore the fiber-product
system's generic fiber is a single point (up to the already-quotiented
swap), therefore the system has finitely many solutions for all
(alpha,alpha') outside a codimension-2 (measure-zero) exceptional
locus -- explicitly identified as D ~ K_C. This is a classical theorem
applied to this construction, not an inference from the 2475/2457/
2458-point counts. The witness-point runs are *confirmation* of this
proof at specific instances (and additionally confirm scheme-theoretic
reducedness -- see Question 2 below, which the theorem alone does not
give) -- they are not what makes finiteness true. Nothing in this
document actually disputes this; the "finiteness not proved" framing
that has circulated in conversation about this document conflates
Question 1 with Question 3 below, which is the actual open item.

QUESTION 2 -- Is every root simple (multiplicity 1), not just the set
finite? -- PROVED per-instance (empirically, three-for-three), NOT
covered by the Question 1 theorem, and not needed for O(p^(4/5)) as
currently derived.
The birational-map theorem gives finiteness of the *underlying set*
only; it says nothing about scheme-theoretic reducedness. That every
witness point independently came back degree 1 across all three runs
(2475/2457/2458) is doing separate, non-redundant work: it is exactly
the "O(1) roots per hit, independent of p" input the balancing
equation behind O(p^(4/5)) actually assumes (section 6, "Practical
consequence"). This is currently established only empirically,
instance-by-instance -- there is no theorem on file (or claimed) that
forces reducedness in general. This is a DETAIL, not a FATAL gap: if a
future run ever produced a genuine degree>1 component, that would not
break finiteness (Question 1 stays proved regardless), it would only
mean the "O(1)" constant in the complexity heuristic is not 1 for that
instance -- a quantitative correction, not a collapse of the argument.
The varying witness counts themselves (2475/2457/2458) are consistent
with numerical/path-tracking variance across monodromy seeds on a
fixed true count, NOT with the true count itself being unstable or
undefined -- Question 1's finiteness does not depend on which of these
three integers is exactly right.

QUESTION 3 -- Is the fiber-product projection's degree d CONSTANT
across (alpha,alpha') (not just finite at each instance), and where
exactly is the jump locus? -- OPEN, but DOWNGRADED from fatal to
detail (see correction in section 6.2: "RETRACTED: why this track does
NOT make section 7's variance work moot").
Section 6.2's closing paragraphs are explicit that this is a distinct,
harder question from Questions 1-2, for two concrete reasons: (i) d is
currently known at exactly one full instance (2457, or whichever count
is trusted after the current retry work) -- no second independently
generated instance has been checked for whether d is even
approximately the same value, let alone provably constant; (ii) even
granting stability, the locus where d could jump has not been shown to
coincide with (or sit inside) the D~K_C exceptional locus that
Question 1's proof already identifies -- these could be the same
closed set or a strictly larger one, unchecked either way. This was
previously classified FATAL on the claim that a bound on d would give
X(Delta) <= d directly, substituting for section 7's second-moment
argument. That claim does not hold: working through the definitions,
X(Delta) is the autocorrelation of T = s(F)'s own pairwise-sum
representation function, not a fiber count of sigma at all, and no
relationship between the two has been shown (see section 6.2's
correction for the full derivation). Question 3 is therefore a
legitimate open item worth resolving -- it is still needed to promote
assumption (a) from a single verified instance to a generic statement
-- but resolving it, in either direction, does not change whether the
O(p^(4/5)) claim goes through. It is reclassified as a DETAIL: tractable
and concretely scoped (generate one more instance and compare its
fiber count; identify the degree-jump locus explicitly, per section
6.2), and worth doing to complete assumption (a), but no longer the
fatal-vs-detail hinge for the complexity claim as a whole.

QUESTION 4 -- Is E(S,S) (the additive energy of S = F+F) small enough
to close the B^2 shortfall in section 7.5? -- OPEN, and this is the
actual FATAL item, independent of anything in section 6.
This is the item Question 3 was previously (incorrectly) thought to be
able to substitute for. It cannot be reached through Questions 1-3 at
all: section 7.5 proves the shortfall is extremal given only Sidon-ness
(a U^2/4th-moment fact about T, already proven unconditionally via
Forey-Fresan-Kowalski) and the trivial pointwise bound -- no sharper
deduction from those two inputs alone can do better. Section 7.6
further shows, via Shkredov's higher-energy dichotomy, that no
pairwise-only (U^2-level) selection strategy for F can supply the
missing U^3-level control either, regardless of how cleverly F is
chosen from a bounded budget. What remains open, concretely: (i) a
genuinely different per-character bound beyond the one candidate
already checked and found vacuous at this scale (Ortega-Prendiville,
section 5/7.2); (ii) selecting F to deliberately land in Shkredov's
structured branch (a genuine algebraic Sidon construction such as
quadratic-residue-type or Bose-Chowla-type sets, restricted to the
curve's actual d1-point set) -- not ruled out, but requires showing
such structure exists among this curve's d1 points, which is an open
existence question in its own right; (iii) the empirical route of item
8(c), which does not resolve the proof but gives a practical,
self-certifying substitute (a batch returning Theta(B) relations is
usable without first proving which regime produced it).

Summary table for this addendum:

| Question                                    | Status    | Fatal or detail? |
|----------------------------------------------|-----------|----------------------------------------------|
| 1. Generic 0-dimensionality (finiteness)      | PROVED    | N/A -- already closed, not at risk            |
| 2. Generic-instance reducedness (degree 1)    | Empirical, 3/3 instances | DETAIL -- affects the O(1) constant, not whether O(p^(4/5)) has a shape at all |
| 3. Constant degree d + exceptional-locus match | OPEN      | DETAIL (downgraded) -- worth resolving to complete assumption (a) generically, but does not bear on the complexity claim's actual bottleneck |
| 4. E(S,S) / B^2 shortfall in section 7.5      | OPEN      | FATAL -- this is the real bottleneck; nothing in section 6 (finiteness, reducedness, or degree-stability) touches it |

Practical read for the retry/convergence work in progress: since
Question 1 is a theorem, the witness-point count varying run to run
(2475/2457/2458) is not evidence against finiteness and does not need
to "converge" to validate finiteness -- it already is valid. What
repeated runs actually buy is progress on Question 2 (does degree-1
keep holding) and, if a second *distinct* (alpha,alpha') instance is
ever run, a first data point on Question 3 (is d stable) -- worthwhile
for completeness, but not on the critical path to resolving the
complexity claim. A third run at the SAME instance, however many more
are done, cannot by itself touch Question 3 -- that specifically
requires a different (alpha,alpha') choice, not just a different
monodromy seed on the same one. The critical-path item, Question 4, is
untouched by any of this retry work; it lives entirely in section 7's
additive-combinatorics analysis of the factor base F, not in section
6's elimination-system geometry.

7. Resolution of item 7(b)(i): a uniform Weil bound exists, but the
   sup-norm route is provably too weak; the correct remaining target
   is a second moment
------------------------------------------------------------------------

7.1 A fully uniform exponential-sum bound for characters of J(F_p)
--------------------------------------------------------------------

Advisory-6, item 7(b)(i), left open whether a genuine exponential-sum
/ Weil-type bound exists for characters of J(F_p) evaluated on
s(C(F_p)), as opposed to the bulk/typical-case statement obtained
from Ortega-Prendiville. Such a bound can be constructed as follows.

Since J is defined over F_p, Frobenius pi acts on J, and phi := pi - 1
is an isogeny J -> J. Its differential at the origin is -id (since
d(pi) = 0), so phi is etale everywhere -- with no coprimality
condition on p needed, unlike a fixed-integer multiplication isogeny
[n]. Its kernel is exactly J(F_p), by definition of rational points,
and translation by any gamma in J(F_p) preserves the fibers of phi
(since pi(gamma) = gamma), so phi is a finite etale J(F_p)-Galois
covering of J. This is the abelian-variety analogue of the Lang
torsor used to construct Artin-Schreier sheaves on the additive group
and Kummer sheaves on the multiplicative group.

Decomposing phi_* Qbar_l into isotypic pieces for the deck group
J(F_p) gives, for every character chi of J(F_p) (any order, up to
|J(F_p)| ~ p^2), a rank-1 lisse sheaf L_chi on J with
tr(Frob_y | L_chi) = chi(y) for y in J(F_p). Pushforward along the
finite (proper) map phi preserves weight-0 purity, so L_chi is pure
of weight 0; and because phi is etale everywhere on J, L_chi is
unramified everywhere. The rank is 1 regardless of the order of chi
-- this is the feature that removes the "small-subgroup" restriction
that limited the Ortega-Prendiville route to a bulk statement.

Pulling back via the closed immersion s: C -> J gives a rank-1 lisse
sheaf s*L_chi on C, pure of weight 0, unramified everywhere on C.
Since s(C(Fbar_p)) generates J as a group (standard for Abel-Jacobi
images at genus >= 1) and chi is nontrivial, s*L_chi is geometrically
nontrivial, so H^0 = H^2 = 0 and Grothendieck-Ogg-Shafarevich (with no
ramification term, since s*L_chi is unramified) gives
dim H^1_c(C, s*L_chi) = 2*g_C - 2 = 2. Deligne's Weil II bounds every
Frobenius eigenvalue on H^1 by sqrt(p) in absolute value. By
Grothendieck-Lefschetz:

    |S(chi)| <= (2 g_C - 2) sqrt(p) = 2 sqrt(p)                    (6)

for the complete sum S(chi) = sum_{x in C(F_p)} chi(s(x)), uniformly
over every nontrivial character chi -- no exceptional set, unlike
Ortega-Prendiville. Completing to the actual interval-restricted
factor base F (via the standard Polya-Vinogradov-type completion
technique, twisting by an Artin-Schreier sheaf pulled back along the
degree-2 map to the x-line, which adds a bounded ramification term at
the poles of that map) gives

    |S_F(chi)| << sqrt(p) log(p)                                    (7)

uniformly in chi != 1 and in the interval defining F. This affirmatively
answers the literal question in 7(b)(i): a fully uniform Weil-type
bound does exist. [Caveat: this construction -- character sheaves on
an abelian variety via the Frobenius-minus-one Lang isogeny -- is
standard in spirit (the natural generalization of Artin-Schreier/
Kummer sheaves, in the manner of Katz's and Kowalski-Michel-Sawin's
trace-function formalism) but a pinpoint literature reference for
this exact construction was not located during this work; it should
be checked independently before being relied upon.]

7.2 Why (6)-(7) do not close assumption (b): an explicit threshold
--------------------------------------------------------------------

Bound (7) does not, however, give a useful equidistribution statement
for N(Delta), and the failure is quantifiable and turns out to be
scale-independent in a strong sense. Write G = J(F_p), |G| ~ p^2, and
f = 1_{s(F)} on G. Fourier inversion on G gives, for the same N(Delta)
of section 2,

    N(Delta) - B^4/|G| = (1/|G|) sum_{chi != 1} |f-hat(chi)|^4 chi(Delta)

so with K := sup_{chi != 1} |S_F(chi)|,

    |N(Delta) - B^4/|G|| <= K^4.                                    (8)

Nontrivial equidistribution needs K^4 << B^4/|G|. With K ~ sqrt(p)
(dropping logs) and |G| ~ p^2, this requires p^2 << B^4/p^2, i.e.
B >> p. But B <= |C(F_p)| ~ p always, since F is a subset of the
curve -- so the condition needed for (7) to certify equidistribution
degenerates to "F is a positive proportion of the entire curve,"
which is vacuous for any genuine sub-sampled factor base, and in
particular fails at the actual scale B ~ p^(2/5).

This is a stronger statement than "the bound is too weak at
B ~ p^(2/5)": since sqrt(p) is (by the Riemann Hypothesis for curves)
essentially the best possible bound for a single nontrivial character,
no exponential-sum bound of Weil/Deligne type -- however the
character sheaf is constructed -- can certify uniform equidistribution
of N(Delta) for a factor base of size o(p). The obstruction is
intrinsic to the sup-norm approach, not a defect of Ortega-Prendiville
specifically or of the construction in 7.1: two structurally
unrelated methods (additive combinatorics via Sidon sets, and
sheaf-theoretic character sums) hit the identical B ~ p threshold,
which is evidence the wall is real rather than technique-specific.
Item 7(b)(i) is accordingly closed in the negative: a uniform
exponential-sum bound of the type asked for exists (section 7.1), but
resolving assumption (b) does not lie down this route at any relevant
factor-base scale, and further effort should not be spent searching
for a sharper per-character bound.

7.3 The correct reframing: the expectation is exact, and the real
    target is a second moment
--------------------------------------------------------------------

The preceding two subsections concern pointwise (every-Delta)
equidistribution, which is more than assumption (b) strictly requires
for the complexity claim. The complexity argument only needs the
expectation of N(Delta) over a uniformly random Delta (or,
equivalently, a positive hit probability). This suggests a materially
easier target, which resolves cleanly:

    sum_{Delta in J(F_p)} N(Delta) = B^4                             (9)

exactly, because every quadruple (P1,P2,P3,P4) in F^4 contributes to
exactly one value of Delta = (P1+P2)-(P3+P4). Hence

    E_Delta[N(Delta)] = (1/|J(F_p)|) sum_Delta N(Delta) = B^4/|J(F_p)| (10)

exactly, for uniformly random Delta, with no Sidon input, no Fourier
bound, and no pseudorandomness assumption of any kind. This is a
genuine simplification relative to sections 1-5 and to 7.1-7.2 above:
it establishes the heuristic (H0) as an exact statement about the
mean of N(Delta), unconditionally on the structure of F.

It does not, however, resolve assumption (b). What the complexity
argument actually needs is a positive hit probability, Pr[N(Delta) >
0] for the actual (non-random, adversarially-fixed-by-the-attack)
Delta of interest, or at least for a typical Delta arising during the
algorithm's run. The mean alone does not give this when mu :=
E[N(Delta)] = B^4/|J| is small (the relevant regime here, since
B ~ p^(2/5) and |J| ~ p^2 give mu ~ p^{-2/5} << 1): a small mean is
consistent with N(Delta) being exactly 0 for almost all Delta and
concentrated on a sparse set, in which case a randomly or
adversarially encountered Delta would almost never hit. Converting
the mean into a probability statement requires a second-moment bound,
via Paley-Zygmund:

    Pr[N(Delta) > 0] >= E[N(Delta)]^2 / E[N(Delta)^2].              (11)

If E[N(Delta)^2] << E[N(Delta)] + E[N(Delta)]^2, this gives
Pr[N(Delta) > 0] >> mu ~ B^4/|J| ~ B^4/p^2, recovering (H0) as a
genuine hit-probability statement in the sparse regime. This is the
mathematically correct minimal target, in place of the pointwise
equidistribution pursued in sections 3-5 and 7.1-7.2.

7.4 The second moment reduces to the same energy quantity already
    identified in section 3 -- the reframing is correct but does not
    bypass the open problem
--------------------------------------------------------------------

Writing X(Delta) := N(Delta) and T := s(F) (so |T| = B), expand

    E[X^2] = (1/|J|) sum_Delta N(Delta)^2
           = (1/|J|) #{(P1,...,P4,P1',...,P4') in F^8 :
                       (P1+P2)-(P3+P4) = (P1'+P2')-(P3'+P4')}.

This counts solutions in T to a+b+c'+d' = c+d+a'+b' (an 8-term
additive relation). Splitting by whether {a,b,c,d} equals
{a',b',c',d'} as a multiset:

  - Solutions with {a,b,c,d} = {a',b',c',d'}: a bounded number of
    coincidence patterns, each contributing O(B^4) using only that T
    is Sidon (i.e. that section 4's theorem applies to 2-fold sums in
    T, which is unconditional here). This contributes O(B^4) to the
    sum, i.e. O(E[X]) to E[X^2] after dividing by |J|. This part of
    the target bound in (boxed display below) is therefore already
    established, unconditionally, by the Sidon property alone.

  - Solutions with {a,b,c,d} != {a',b',c',d'}: this is precisely
    E(S,S), the additive energy of S = F+F = T+T, as already defined
    in section 3, equation (1)-(2). Concretely,

        E[X^2] = O(E[X]) + E(S,S)/|J|.                              (12)

The Paley-Zygmund target E[X^2] << E[X] + E[X]^2 is therefore
algebraically equivalent to

    E(S,S) << |J| * E[X]^2 = B^8 / |J|,                             (13)

which is exactly the quasi-random energy bound of equation (2) in
section 3 -- the load-bearing hypothesis that sections 3-5 already
identified as the actual open problem, and which the Sidon-set
machinery of section 4 gives only a bulk/typical-case version of
(section 5), not the full bound.

Status: the Paley-Zygmund reframing is a correct and useful
simplification of the target -- it establishes that the expectation
(10) needs nothing further, that the only missing ingredient for a
positive hit-probability statement is the second moment (11), and
that a bounded, easily-dispatched part of that second moment ((12),
first bullet) is already free from the Sidon property alone. But it
does not supply a new route around the hard part: the surviving
term is literally E(S,S), the same quantity flagged as open in
section 3, so the reframing correctly narrows assumption (b) to its
minimal necessary content rather than resolving it. The remaining
open task is unchanged in substance from item 8(c) below (the
proposed direct empirical measurement of the spread of s(F)+s(F))
and from the discussion in the closing paragraph of section 9: what
is needed is a genuine bound on E(S,S), of second-moment type, not a
sup-norm/Weil-type bound of the kind ruled out in section 7.2.

7.5 Carrying the second moment through explicitly: a precise,
    provably tight shortfall of B^2
--------------------------------------------------------------------

Section 7.4 identified E(S,S) as the surviving unknown. It is worth
carrying the computation through with only the tools already
established (Sidon-ness plus the trivial pointwise bound) to see
exactly how far they get, since the shortfall turns out to be both
precise and provably not closable by better bookkeeping of the same
inputs.

Work directly with T = s(F) rather than S = T+T. Let N = |G| =
|J(F_p)|, f = 1_T on G, and X(Delta) = #{(a,b,c,d) in T^4 :
a+b-c-d=Delta}, so E[X] = B^4/N exactly (section 7.3) and, by
Parseval applied twice,

    E[X^2] = (1/N^2) sum_chi |f-hat(chi)|^8.                        (14)

The Sidon bound controls only the 4th moment. For g != 0, Sidon-ness
gives r_{T-T}(g) <= 1 (this is what "T is Sidon" means, applied to
differences rather than sums, and the two are equivalent since
a-b=c-d iff a+d=c+b), so

    E(T,T) = r(0)^2 + sum_{g!=0} r(g)^2
           <= B^2 + sum_{g!=0} r(g) = B^2 + (B^2-B) < 2B^2,          (15)

hence sum_chi |f-hat(chi)|^4 = N*E(T,T) < 2 B^2 N. (Note: this
corrects an intermediate slip -- an earlier pass at this computation
stated the bound as 2BN; the Sidon energy of a B-element set cannot
be smaller than B^2, since the diagonal term r(0)^2=B^2 alone already
achieves that, so the correct bound is 2B^2N. The final numbers below
are unaffected, since they were already computed consistently with
2B^2N.)

Using only this plus the trivial bound |f-hat(chi)| <= B for every
chi:

    sum_chi |f-hat(chi)|^8 <= B^4 * sum_chi |f-hat(chi)|^4 < 2 B^6 N, (16)

so E[X^2] < 2 B^6/N, and Paley-Zygmund gives

    Pr(X>0) >= E[X]^2/E[X^2] > (B^8/N^2)/(2B^6/N) = B^2/(2N).        (17)

This is short of the target Pr(X>0) ~ B^4/N by exactly a factor of
B^2 -- Sidon-ness (a statement about 2-fold collisions, i.e. the 4th
moment of f-hat) buys real ground over the trivial bound, but not
enough, and the shortfall is precisely quantified rather than merely
qualitative.

This shortfall is not an artifact of a loose inequality: it is
extremal given the stated inputs. Given only sum_chi |f-hat(chi)|^4 =
M_4 (<= 2B^2N) and the pointwise cap |f-hat(chi)| <= B, the bound (16)
is the worst case consistent with that data -- maximizing sum
|f-hat(chi)|^8 subject to a fixed 4th-moment budget and a pointwise
cap concentrates the budget onto as few characters as possible, each
sitting at the cap B, which reproduces (16) up to constants. In other
words: no sharper deduction from "T is Sidon" and "trivial bound"
alone can improve on B^2/(2N); the gap is a genuine information
deficit, not a slack step in the derivation.

Closing the remaining B^2 therefore requires a third, independent
input beyond these two -- most plausibly a nontrivial bound on
|f-hat(chi)| itself (not just its 4th moment) for most chi, which is
exactly what the Ortega-Prendiville bulk statement of section 5 was
positioned to supply. But section 5 already established that this
bulk bound is vacuous (no better than the trivial B) at the actual
scale B ~ p^(2/5). So the one existing candidate for the missing
input has already been checked and found wanting -- this is the same
obstruction encountered in sections 5, 7.2, and now 7.5, arrived at
by three structurally different routes (additive combinatorics,
sheaf-theoretic character sums, and this direct second-moment
computation), which is strong evidence that the B^2 shortfall is a
real feature of the problem at this factor-base scale, not an
accident of any one method. Item 8(c)'s proposed empirical
measurement is, at this point, the only avenue in the document that
does not reduce to one of these three already-exhausted routes.

7.6 A relaxed O(B^2) selection budget does not reopen the gap
--------------------------------------------------------------------

Section 7.5 treated F as an arbitrary d1-point subset, constrained
only by the Sidon property that holds automatically (Forey-Fresan-
Kowalski) regardless of how F is chosen. A natural objection: what if
F is not arbitrary but *selected*, using up to O(B^2) group
operations, so long as every element remains a genuine d1 point on C?
O(B^2) is exactly the cost of computing the full pairwise-sum table
of a candidate pool F_0 with |F_0| = O(B), i.e. exact knowledge of
r_{T+T}(g) for every g -- the full multiplicity histogram of S = T+T,
not merely its aggregate energy (which Sidon-ness already pins down
for free). This is strictly more information than section 7.5 used,
so it is worth asking whether it closes the B^2 shortfall.

It does not, and the reason is structural rather than a failure of
any one proposed construction. The quantity that must be suppressed,
sum_chi |f-hat(chi)|^8, equals (up to normalization) the "higher
energy" E_4(T) -- solutions to t1+t2+t3+t4 = t1'+t2'+t3'+t4' over T --
which controls the Gowers U^3 norm of 1_T. Exact pairwise-sum data
(the object O(B^2) buys) is exactly the U^2-norm information: it
pins down E(T,T) exactly, which is already captured by the Sidon
bound alone. It is a standard fact in additive combinatorics that
U^2 control does not imply U^3 control -- a set can have perfectly
flat pairwise sums while still correlating with a quadratic phase
function, which is precisely what inflates the 8th moment. (The
canonical witnesses are quadratic-residue-type sets: flat at 2nd
order, biased at 3rd order.) So no selection rule that only reads
off pairwise-sum data -- however cleverly it uses that data -- can
certify the 3rd-order-level fact section 7.5 actually needs.

This is not merely a heuristic gap; it matches the shape of the
relevant theorem. Shkredov (arXiv:2103.14670, Theorem 2) shows that
for any finite set A, the higher energy E_k(A) is at most |A|^(k+eps)
UNLESS A carries a very specific coset/small-doubling structure. This
is precisely the dichotomy at stake here: the "generic" branch of
that theorem already reproduces the bound section 7.5 obtained from
Sidon-ness alone, and the only way to do better is to land in the
structured exceptional branch -- which requires genuine algebraic
structure (a coset-like witness H), not a pairwise-flatness
certificate. A greedy selection rule that flattens the pairwise-sum
histogram is explicitly trying to make F look *unstructured*, which
is the wrong direction: it pushes F toward the generic branch (where
the bound is already what section 7.5 has), not toward the
structured branch (where a better bound could in principle live).

This also matches the empirical record for Sidon-type constructions.
Eberhard (Electron. J. Combin. 30 (2023)) observes that every known
near-maximal dense Sidon set relies on genuine algebraic structure
(finite-field/prime-related constructions such as Singer difference
sets or Bose-Chowla), while randomly or greedily constructed Sidon
sets are reliably smaller/weaker than the structured ones -- greedy
methods do not discover the structure that would be needed. A 2025
result on greedy Sidon sets for linear forms (Y. C. Cheng, J. Number
Theory 266) shows greedy constructions can still yield specific
sequence-level improvements over particular prior bounds, but these
are constant-factor wins internal to the greedy process, not a route
to a better exponent, and they do not transfer here since they are
not phrased as pairwise-certificate selection rules at all.

The remaining alternative -- selecting F to explicitly match a known
algebraic near-extremal Sidon construction (quadratic-residue-type or
Bose-Chowla-type sets) -- is not ruled out in principle, since these
are exactly the constructions that occupy Shkredov's structured
branch. But it does not fit the O(B^2)-selection framing at all: such
constructions are global algebraic objects, not subsets selected from
an arbitrary pool by any local (pairwise or otherwise) certificate,
and F is additionally constrained to be d1 points of the specific
curve C -- there is no existing argument that C's d1-point set
contains, or approximates, such a structure. Establishing that would
be a separate and likely harder existence question, not a corollary
of the O(B^2) budget.

A note on a tempting but incorrect shortcut. It is natural to ask
whether E(S,S) itself can simply be read off the O(B^2) pairwise-sum
histogram r_{T+T}(g) = #{(a,b) in T^2 : a+b=g} by the same
sum-of-squares step used for E(T,T), i.e. whether
E(S,S) = sum_g r_{T+T}(g)^2. This is false, and worth stating
precisely since the two quantities are easy to conflate.
sum_g r_{T+T}(g)^2 is exactly E(T,T) -- already pinned to O(B^2) by
Sidon-ness alone and carrying no new information. E(S,S), by
contrast, is the energy of S = T+T itself: E(S,S) = sum_Delta
r_{S-S}(Delta)^2, where r_{S-S}(Delta) = #{s1,s2 in S : s1-s2=Delta}
= sum_g r_{T+T}(g) r_{T+T}(g-Delta) -- the *autocorrelation* of the
pairwise-sum histogram with itself, not its self-sum-of-squares. (A
quick check confirms these cannot coincide: Sidon-ness pins
E(T,T) = Theta(B^2), but |S| = Theta(B^2) already, so a generic set
of that size has E(S,S) = Theta(|S|^4/N) = Theta(B^8/N), which for
B ~ p^(2/5) is enormous compared to B^2 -- the two quantities live at
completely different scales.) Equivalently, by Parseval,
sum_chi|f-hat(chi)|^8 = N * E(S,S), confirming E(S,S) is genuinely
the 8th-moment object, not the 4th-moment one. The pairwise histogram
does determine E(S,S) in the sense that E(S,S) is a fixed functional
of it (its autocorrelation), but computing that autocorrelation
directly still costs O(B^4) in general (the histogram's support has
size Theta(B^2), and autocorrelating a size-m support against itself
costs O(m^2) absent further structure) -- so this observation
sharpens the open question without closing it. Fourier-transforming
the histogram over the ambient group J(F_p) does not help either: an
FFT-based route costs O(|J| log|J|) = O(p^2 log p), which at
B ~ p^(2/5) is larger than the direct O(B^4) = O(p^(8/5)) computation
it would replace.

What the O(B^2) histogram does support, honestly, is a Monte Carlo
*estimate* of E(S,S) rather than an exact value or a proof: sample M
pairs of support points (g1,g2) from the exact histogram r_{T+T}
already in hand, weighted by r_{T+T}(g1) r_{T+T}(g2), and use the
resulting empirical distribution of Delta = g1-g2 to estimate
r_{S-S}(Delta) and hence E(S,S), at cost O(M) rather than O(B^4),
reusing data already computed rather than resampling raw curve
points. This has standard error shrinking like 1/sqrt(M) around the
*true* E(S,S) for uniform sampling, but is only reliable if E(S,S) is
not dominated by rare, heavy outliers in r_{S-S}: if a small number
of Delta values carry a disproportionate share of the energy (the
"lumpy" failure mode this whole section is about), uniform sampling
of histogram pairs will systematically *underestimate* E(S,S) with
high probability, the same way naive Monte Carlo underestimates a
heavy-tailed variance. A trustworthy estimate in that regime needs
importance sampling weighted toward the high-r_{T+T}(g) bins of the
histogram, not uniform sampling over it. This estimator is developed
as item 8(c) below.

Conclusion: the O(B^2) selection budget, however it is used, cannot
*certify* the 8th-moment suppression section 7.5 needs via a
pairwise-only argument, because it only ever supplies U^2-level
(pairwise) information about T, while the needed fact is U^3-level.
It can, however, *estimate* E(S,S) directly and cheaply from data
already computed, with the reliability caveat above. This leaves the
B^2 shortfall exactly as characterized in section 7.5 as a matter of
proof, while giving item 8(c) a concrete, efficient instrument rather
than only a qualitative empirical check.

7.7 Literature check: Forey-Fresan-Kowalski-Wigderson, "Jacobian
graphs" (2026), does not close the gap
--------------------------------------------------------------------

A literature search was carried out to check whether the 8th-moment
/ U^3 gap identified in sections 7.5-7.6 has since been closed. It
has not, but a genuinely relevant new paper was found and is worth
recording.

Forey, Fresan, Kowalski, and Wigderson, "Jacobian graphs"
(arXiv:2603.13198, March 2026 -- confirmed to exist and checked
directly against its text; this postdates the working literature
base of this document), studies graphs built from the same
generalized-jacobian Sidon-set construction underlying this whole
project (Forey-Fresan-Kowalski, "Sidon sets in algebraic geometry").
Their Theorem 4.1/4.2 establishes that for a genus-2 curve C with
J = Jac(C), the normalized character sums

    U_n(chi) = |k_n|^{-1/2} sum_{x in S(k_n)} chi(x)

(S = the symmetric Sidon set image of C(k_n) in J(k_n)) become
equidistributed, as n -> infinity, according to the trace of Haar
measure on a compact group K^a subset of SU_2(C), and that for
g = 2 (their Theorem 4.2(i), unconditionally, via [FFK
"Arithmetic Fourier transforms", Th. 11.1]) K^a = SU_2(C), giving
semicircle-law equidistribution of the associated graph spectrum.
The key quantitative input is their fourth moment

    M_4 = integral over K^a of |Tr(x)|^4 = 2

(not the naive 3 a generic quasi-random set would suggest; the
discrepancy is explained by the trivial-character contribution),
which via Larsen's alternative forces K^a to be either all of
SU_2(C) or one of three specific finite subgroups, the finite cases
being ruled out for g=2.

This is a real and directly relevant result, but it operates one
moment level below what section 7.5's gap needs. M_4 = 2 is a
statement about the *fourth* moment of character sums over S itself
(equivalently, U^2-level information about S, in the terminology of
section 7.6) -- it reproves, via much heavier sheaf-theoretic
machinery (Deligne's Weil II, Lang torsors, Larsen's alternative),
essentially the same order of fact already available for free from
the elementary Sidon property used throughout sections 3-7 above. It
is not a statement about the 8th moment of S+S needed to bound
E(S,S) via Paley-Zygmund (section 7.3-7.5), and nothing in the
Larsen's-alternative argument structure -- which identifies K^a from
the 4th moment and gets everything else "for free" once K^a is
pinned down as SU_2(C) -- extends to control 8th moments without a
fundamentally different input. The paper itself gives no indication
of addressing this higher level; its object of study (spectral
statistics of the induced graph) does not require it.

Net effect on this document: no change to the status of the gap
characterized in sections 7.5-7.6. This is now a fourth independent
confirmation (alongside Ortega-Prendiville, the Lang-torsor bound of
section 7.1, and the direct second-moment computation of section
7.5) that the 4th-moment/U^2 level of this problem is solid and
well-covered by multiple techniques, which correspondingly sharpens
the sense that the *remaining* gap is specifically at the 8th-moment
/ U^3 level, where this literature search still finds nothing
addressing the construction here. Worth periodically re-checking,
since Kowalski's group is actively working in exactly this area.

8. Practical, immediately checkable consequences
----------------------------------------------------

Three concrete action items follow directly from this analysis, all
cheaper than the current 0-dimensional symbolic solve:

(a) Verify the factor base excludes hyperelliptic-involution pairs.
    This is required for the clean (non-symmetric) Sidon bound in
    Step 3; if F does contain such pairs, the correction is exactly
    characterized by the theorem (solutions pin to the center
    a0 = s(x)+s(iota(x))) and can be explicitly removed or accounted
    for, rather than treated as an unknown source of error.

(b) [Done, see section 5; (i) now also settled, negatively, see
    section 7.] The Ortega-Prendiville sup-norm bound was worked out
    explicitly at the actual scale B ~ p^(2/5) and found to be vacuous
    there (no better than trivial) — the extremal-regime calibration
    in the cited theorem does not transfer usefully to this
    factor-base size. Sub-item (i), finding a genuine exponential-sum/
    Weil-type bound for characters of J(F_p) evaluated on the image of
    C(F_p), has since been carried out (section 7.1, via Lang-torsor
    character sheaves) and shown, by direct computation, to be
    provably insufficient for uniform equidistribution at any factor-
    base scale o(p), not merely at B ~ p^(2/5) (section 7.2) — closing
    this sub-item negatively rather than leaving it open. Sub-item
    (ii), accepting the bulk/typical-case statement as sufficient, has
    also been superseded: section 7.3-7.4 shows the actually-needed
    target is not pointwise equidistribution at all but a second
    moment bound, E(S,S) << B^8/|J|, equivalent by Paley-Zygmund to a
    positive hit probability in the sparse regime. This is the
    correct remaining open task — see section 7.4 and item (c) below.

(c) Estimate E(S,S) directly from the O(B^2) pairwise-sum histogram
    already computed for the Sidon/factor-base bookkeeping, rather
    than only performing a qualitative spread check. Concretely:
    from the exact histogram r_{T+T}(g) (already in hand at O(B^2)
    cost), draw M pairs of support points (g1,g2), weighted by
    r_{T+T}(g1) r_{T+T}(g2), form Delta = g1-g2, and use the
    resulting empirical distribution to estimate r_{S-S}(Delta) and
    hence E(S,S) = sum_Delta r_{S-S}(Delta)^2 -- see section 7.6 for
    the derivation and the identity E(S,S) = sum_Delta [sum_g
    r_{T+T}(g) r_{T+T}(g-Delta)]^2, i.e. the *autocorrelation* of the
    pairwise histogram, not its sum of squares (which is only
    E(T,T), already known from Sidon-ness and uninformative here).
    This costs O(M), reusing the O(B^2) histogram already computed,
    versus O(B^4) for an exact brute-force autocorrelation, and gives
    a genuine point estimate of the quantity 7.5 could not bound
    tightly, with standard error shrinking like 1/sqrt(M). Caveat:
    uniform sampling of histogram pairs will systematically
    *underestimate* E(S,S) if the true energy is dominated by a few
    heavy Delta values (the lumpy failure mode itself) -- a
    trustworthy estimate in that regime requires importance sampling
    weighted toward the high-r_{T+T}(g) bins, not uniform sampling.

    Separately, and more directly diagnostic: run the sampling
    procedure at its designed scale, N^2 ~ p^2/B^3 pairs (alpha,
    alpha'), for which E[total hits] = N^2 * B^4/p^2 = O(B) by
    construction (section 1's restated heuristic, applied at the
    sampling-budget level). Whether this batch actually returns
    Theta(B) hits, spread over roughly that many distinct Delta
    values, is a direct empirical read on whether the SE discussed in
    section 7.6 is small (H0 holds, as needed) or large (lumpy
    failure mode). The all-or-nothing version of this test is sharp:
    under a rare-event/Poisson model for hits across the N^2 sampled
    pairs, if the true hit process matches (H0) -- i.e. the mean
    E[total hits] = O(B) is not an artifact of a few Delta values
    absorbing almost all the mass -- then the probability of
    observing *zero* hits in the full N^2-sized batch is
    exp(-Theta(B)), which is already astronomically small for any B
    of practical size (e.g. ~1e-5 at B=10, ~1e-22 at B=50, ~1e-44 at
    B=100, and ~1e-136 at the B=313 factor-base size found in section
    6.1). So a full-scale run that returns zero hits is not a fluke
    under (H0) -- it would be strong evidence *against* (H0),
    pointing at exactly the lumpy/concentrated-elsewhere scenario
    this section is worried about (the "murdered by a few bad Delta
    values" case: the mass exists, per the exact expectation
    identity of section 7.3, but missed this particular sample of
    Delta values entirely). Conversely, observing Theta(B) hits
    spread across Theta(B) distinct Delta values in a full-scale run
    is correspondingly strong practical confirmation of (H0) for the
    actual curve and p in use, independent of closing the theoretical
    B^2 gap.

    A third, cheaper diagnostic sits between these two, and its
    reach needs to be stated precisely so it is not overinterpreted:
    take B^2 tuples (a,b,c,d) in T^4 (a size-B^2 slice of the full
    B^4 population, cheap relative to either test above), compute
    Delta = a+b-c-d for each, and check for repeats -- a birthday-
    style collision test on the sample itself, distinct from both
    the E(S,S) estimator and the full N^2-scale hit-rate test.

    What this bounds, precisely, on the SE of the O(B) relation
    count: under (H0) (Delta uniform over J, |J| ~ p^2), the expected
    number of same-Delta collisions in a sample of size B^2 is, by
    the standard birthday calculation, ~ (B^2)^2/(2p^2) = B^4/(2p^2),
    which at B ~ p^(2/5) is ~ (1/2) p^(-2/5) -- already less than 1
    and shrinking. So under (H0) itself, seeing *zero* collisions in
    this size of sample is the expected, unremarkable outcome, not
    evidence of anything -- the sample is simply too small relative
    to |J| for collisions to be likely even in the best (flattest)
    case. This test therefore cannot, by itself, confirm that the SE
    is small.

    What it can do is bound how bad the worst undetected case is
    allowed to be. If a small number of Delta values were carrying k
    times the flat average multiplicity B^4/p^2, a size-B^2 sample
    would be expected to land >=2 tuples on such a hot Delta once
    k >~ p^2/B^2 (at B ~ p^(2/5), k >~ p^(6/5)). So a clean
    (zero-collision) result at this sample size rules out any
    concentration factor at or above k ~ p^(6/5) -- it excludes the
    most catastrophic lumpiness, where E(S,S) would be inflated by
    hot spots that large, but says nothing about moderate lumpiness
    below that threshold (e.g. many Delta's each carrying a factor of
    k ~ p, or even k ~ p^(6/5-eps), would pass this test undetected
    and could still leave E(S,S) far above the flat value B^8/p^2 --
    potentially still near the pessimistic 2B^6*N bound section 7.5
    could not improve on). Concretely, in terms of the SE on the O(B)
    relation count: this test only rules out an SE consistent with
    catastrophic concentration; it does not tighten the proven upper
    bound on the SE at all, and should not be read as confirming a
    small SE. Detecting moderate lumpiness (concentration factors
    down to O(1), i.e. an actual near-flat confirmation) requires a
    birthday-test sample size m with m^2/p^2 non-negligible, i.e.
    m >~ p -- far more than B^2 ~ p^(4/5), though still far cheaper
    than the O(B^4) exact computation.

    In short: the E(S,S) estimator above measures the SE's magnitude
    directly (with the stated importance-sampling caveat); the
    full-N^2-scale test gives a sharp pass/fail read at the actual
    operating scale; this B^2-sample birthday test is the cheapest of
    the three but only rules out extreme lumpiness and should not be
    used on its own to claim a bound on the SE. This sharpens the
    previous, more qualitative version of this item (a coarse
    partition/chi-squared spread check, or correlation with known
    proper subgroups of J(F_p)), which remains a reasonable
    complementary check but is less immediately actionable than the
    three tests above.

    A fourth point, orthogonal to the three tests above: none of them
    need to be run as a prerequisite to using the algorithm, because
    the relation-finding step is self-certifying. Run the N^2-scale
    batch; if it returns Theta(B) relations, use them -- success does
    not require having first proven, or even estimated, which regime
    (flat vs. lumpy) produced it. If a batch instead falls well short
    of Theta(B), that outcome is itself diagnostic: under the hoped-
    for light-tailed/near-(H0) behavior it is already astronomically
    unlikely (the exp(-Theta(B)) calculation above), so a shortfall is
    strong evidence against that regime, and the correct response is
    simply to restart with an independent batch. This is a genuine
    Las Vegas structure -- expected restarts to succeed is O(1)
    *provided the process ever succeeds cleanly at all* -- and it is
    worth recording explicitly because a superficially similar but
    invalid shortcut is easy to propose: attempting to derive the
    O(1)-restart guarantee analytically via Chebyshev's inequality
    from Var(X) alone, without running anything. That does not work.
    Chebyshev gives P(X < mu - delta*B) <= Var(X)/(delta*B)^2; with
    the *proven* bound Var(X) < 2B^6/p^2 (section 7.5, eq. 16-17),
    this ratio is Theta(p^(6/5)) at B ~ p^(2/5) -- far above 1, hence
    vacuous, not "a constant epsilon bounded away from 0" as a naive
    reading might suggest. Concluding that restarts give O(1) expected
    reruns *from Chebyshev and the proven variance bound alone* is
    circular: it assumes the same near-flatness (a small, bounded
    failure probability per restart) that the B^2 gap leaves open in
    the first place, merely restated in terms of restart counts rather
    than hit probabilities. The number of restarts needed to instead
    empirically *distinguish* light-tailed from heavy-tailed behavior
    scales with the reciprocal of the outlier probability, which in
    the worst case allowed by the proven bound is Theta(B^2) restarts
    -- as expensive as the O(B^4) computation this whole approach was
    meant to avoid. The resolution is therefore not to estimate the
    tail behavior in the abstract, but to rely on the self-certifying
    property above: a handful of restarts either produces usable
    relations directly, or produces a cheap, legible failure signal
    (not an expensive one) well before Theta(B^2) restarts would be
    needed to characterize the tail analytically.

    A fifth point, closing a specific alternative to the Chebyshev
    shortcut just rejected. It is natural to ask whether applying
    Chebyshev to the *aggregated* batch total, rather than to X(Delta)
    for fixed Delta, escapes the vacuity above -- since the aggregate's
    mean, E[X_agg] = Theta(B), is not tiny the way E[X(Delta)] =
    B^4/p^2 is. It does not escape it. Writing X_agg = sum_{i=1}^{M}
    X(Delta_i) for M ~ p^2/B^3 independently sampled Delta_i (this
    independence is a property of the sampling design, not an appeal
    to (H0)), variance is additive regardless of whether (H0)'s
    flatness holds:

        Var(X_agg) = M * Var(X(Delta)) < (p^2/B^3) * (2B^6/p^2)
                   = 2B^3,

    using the same proven bound Var(X(Delta)) < 2B^6/p^2 as above. Since
    E[X_agg] = Theta(B), Chebyshev gives
    q <= Var(X_agg)/(delta*B)^2 = O(B), which diverges rather than
    vanishing -- not merely non-vanishing, but uninformative more
    severely than the per-Delta case. B^3 ~ p^(6/5) at B ~ p^(2/5), the
    same exponent already identified as the signature of this
    obstruction. The aggregate framing therefore does not supply an
    escape from the B^2 gap; it reproduces the identical obstruction
    from a different angle, confirming that no Chebyshev-type argument
    from the currently proven second-moment bounds closes it under
    either framing.

(d) Calibrate restart/reroll success probability empirically via full
    re-randomization of F, using Beta-Binomial updating.

    Points (c)-4 and (c)-5 above rule out any current analytic
    derivation of Pr(success), per-restart or per-reroll, from the
    proven bounds. That does not make the quantity uncharacterizable --
    only not derivable from what is currently proven. It can be
    estimated empirically, rigorously, provided reroll is applied to
    the factor base itself and not merely to the batch of Delta's
    sampled against a fixed F.

    The distinction matters because restarts against a *fixed* F are
    not independent trials in the relevant sense: two restarts on the
    same F share the same unknown energy E(S,S), so a "bad" draw of F
    (S-S lumpy/concentrated) disadvantages every restart on it equally
    -- the restarts are correlated through that shared unknown, and no
    amount of restarting on one F converts outcomes into independent
    evidence about the underlying success rate. Full reroll -- drawing
    an entirely fresh random size-B subset F_i of the d1 points for
    each attempt i, together with a fresh batch of Delta's on it --
    removes this correlation. Writing

        theta := Pr_F[a full-scale batch on a random F returns
                      Theta(B) relations],

    each attempt is then a genuine i.i.d. Bernoulli trial with success
    probability theta, the randomness now taken over both the choice of
    F and the sampled batch. theta is exactly E_F[Pr(success | F)] --
    the average-case quantity absent from the fixed-F bounds of section
    7.5. Full reroll does not supply a new proof of theta; it supplies
    the correct statistical setting in which theta can be learned from
    repeated trials rather than derived.

    Recipe: use Beta-Binomial updating rather than raw Laplace
    succession, since it reports a calibrated interval rather than only
    a point estimate. Start from a weakly informative prior
    theta ~ Beta(a0, b0) (a0 = b0 = 1 for a flat prior; a0 = b0 = 1/2,
    the Jeffreys prior, if theta is expected a priori to sit close to 0
    or 1 rather than near 1/2). After n full-reroll attempts with s
    successes and f = n - s failures, the posterior is exactly

        theta | data ~ Beta(a0 + s, b0 + f),

    with posterior mean (a0+s)/(a0+b0+n) and a closed-form credible
    interval from the Beta quantile function. This is the direct
    generalization of Laplace's rule of succession (the a0=b0=1
    posterior mean, (s+1)/(n+2)) to also report the uncertainty around
    that estimate -- essential at the attempt counts actually affordable
    here, since each attempt costs a full M ~ p^2/B^3 batch and n will
    typically be small enough that the interval, not just the point
    estimate, is the honest quantity to report.

    Two things this recipe is not. It is not a substitute for closing
    the B^2 gap analytically -- a posterior interval, however tight, is
    an empirical estimate of theta, not a proof about it. And it is not
    valid under partial reroll: restarting the batch without redrawing
    F reintroduces the correlation this procedure exists to remove, and
    the resulting outcomes are not exchangeable trials in theta. Any
    reported success rate from this procedure should state explicitly
    that F was redrawn on every attempt, not only the batch.

9. Summary of assumption status
-----------------------------------

| Assumption in advisory-5 §7          | Status after this revision                                          |
|---------------------------------------|-----------------------------------------------------------------------|
| Generic finiteness of 4x4 system      | De-risked, not closed. Characteristic-0 numerical irreducible        |
|                                        | decomposition confirms 0-dimensionality with all-degree-1 (simple)   |
|                                        | roots for one tested instance (section 6): 2475 witness points, no   |
|                                        | positive-dimensional component. Follow-up (section 6.1): mod-p       |
|                                        | reduction via strict Hensel check failed for all points (expected —  |
|                                        | design mismatch, not a finiteness failure); reclassification against |
|                                        | two verified minimal polynomials instead gives 313 raw d1 / 63 raw   |
|                                        | d2 witness points, correctly quotienting (after fixing an            |
|                                        | undercounting bug) to 36 / 9 distinct factor-base labels. Mod-p      |
|                                        | finiteness as a theorem (vs. this empirical count) and               |
|                                        | cross-instance/cross-p consistency remain open — see the             |
|                                        | Hensel-lifting step next. NOTE: "finiteness" here bundles four       |
|                                        | separable questions — see section 6.3's triage table (updated,       |
|                                        | includes a correction to an earlier bridge claim). Generic           |
|                                        | 0-dimensionality is PROVED (birationality of sigma: C^(2)->J,        |
|                                        | section 6.2), not open. Constant-degree stability across instances   |
|                                        | (section 6.3, Q3) remains open but is a DETAIL, not fatal — a        |
|                                        | claimed bridge from it to a pointwise bound on X(Delta) was checked  |
|                                        | and does not hold (section 6.2's correction). The actual FATAL open  |
|                                        | item (section 6.3, Q4) is the B^2 shortfall in E(S,S), which lives   |
|                                        | entirely in section 7 and is untouched by anything in section 6.    |
| Equidistribution / density of matching| Reframed and precisely quantified. The expectation E_Delta[N(Delta)]  |
| condition                              | = B^4/|J| is an *exact* identity (section 7.3), by pure double-      |
|                                        | counting, requiring no Sidon input, no Fourier bound, and no         |
|                                        | pseudorandomness assumption whatsoever. Pointwise/uniform            |
|                                        | equidistribution of N(Delta) is a strictly stronger and unnecessary  |
|                                        | target: item 7(b)(i) (existence of a uniform Weil-type exponential-  |
|                                        | sum bound for characters of J(F_p) on s(C(F_p))) is answered         |
|                                        | affirmatively in existence (section 7.1) but negatively in           |
|                                        | usefulness (section 7.2). The correct minimal target, via            |
|                                        | Paley-Zygmund, is a second moment / additive-energy bound (section   |
|                                        | 7.3-7.4). Carried through explicitly (section 7.5) using only        |
|                                        | Sidon-ness plus the trivial pointwise bound, this gives a *provably  |
|                                        | tight* Pr(N(Delta)>0) >~ B^2/(2p^2) -- short of the target B^4/p^2   |
|                                        | by exactly a factor of B^2, and demonstrably not improvable from     |
|                                        | these two inputs alone. The one candidate for the missing third      |
|                                        | input (a genuine per-character bound from Ortega-Prendiville) has    |
|                                        | already been shown vacuous at this scale (section 5). Three          |
|                                        | independent methods -- additive combinatorics, sheaf-theoretic       |
|                                        | character sums, and this direct second-moment computation -- now     |
|                                        | converge on the same obstruction, which is correspondingly strong    |
|                                        | evidence that it is intrinsic to the B ~ p^(2/5) regime rather than  |
|                                        | an artifact of any one technique. A further relaxation -- allowing   |
|                                        | up to O(B^2) work to *select* F rather than treating it as           |
|                                        | arbitrary -- was checked (section 7.6) and closes negatively as a    |
|                                        | proof strategy: the needed 8th-moment suppression is U^3-level       |
|                                        | (Shkredov's higher-energy dichotomy), while O(B^2) pairwise-sum data |
|                                        | is only ever U^2-level, so no selection certificate built from it    |
|                                        | can prove the target regardless of the selection rule used. However, |
|                                        | that same O(B^2) histogram does support a cheap Monte Carlo          |
|                                        | *estimate* of E(S,S) (section 7.6, item 8(c)), reusing data already  |
|                                        | computed rather than resampling from scratch, with the caveat that   |
|                                        | uniform sampling underestimates a heavy-tailed/lumpy true value.     |
|                                        | Item 8(c) also gives a sharp empirical diagnostic: a full-scale run  |
|                                        | of N^2 ~ p^2/B^3 sampled pairs should return Theta(B) hits under     |
|                                        | (H0), and returning zero would be strong evidence against (H0) (its  |
|                                        | probability under (H0) is exp(-Theta(B)), astronomically small for   |
|                                        | any practical B), not a benign fluke. Item 8(c), now concretized     |
|                                        | this way, is the only remaining avenue that does not reduce to one   |
|                                        | of the three exhausted theoretical routes. Crucially, the relation-  |
|                                        | finding step is self-certifying in practice (item 8(c)): a batch     |
|                                        | that returns Theta(B) relations is simply usable, with no need to    |
|                                        | first prove which regime produced it, and a batch that falls well    |
|                                        | short is itself a cheap diagnostic (astronomically unlikely under    |
|                                        | (H0)), pointing to restart rather than requiring a resolved variance |
|                                        | bound. A tempting shortcut -- deriving an O(1)-expected-restarts     |
|                                        | guarantee analytically via Chebyshev's inequality from the proven    |
|                                        | Var(X) bound alone, without running anything -- was checked and does |
|                                        | not work: at B ~ p^(2/5) the relevant ratio is Theta(p^(6/5)), not a |
|                                        | constant bounded away from 0, making the Chebyshev bound vacuous;    |
|                                        | this is the same B^2 gap restated in terms of restart counts, not a  |
|                                        | way around it.                                                        |

The complexity claim O(p^(4/5)) should still be treated as heuristic
until assumption (a) is fully resolved (mod-p and cross-instance
confirmation, per section 6, beyond the single characteristic-0
instance already tested) and item 8(c) is carried
out. What has changed relative to revision 5 is substantial but should
be stated precisely rather than oversold. On the finiteness side,
nothing new. On the density side: the mean of N(Delta) is now known
exactly and unconditionally (section 7.3); the sup-norm/Weil-bound
route to a stronger, pointwise statement has been shown, via three
independent methods, to hit an identical and apparently intrinsic
obstruction at this factor-base scale -- Ortega-Prendiville's additive
combinatorics (section 5), the Lang-torsor sheaf-theoretic bound
(section 7.1-7.2), and the direct second-moment/Paley-Zygmund
computation (section 7.5), which pins the shortfall at a precise
factor of B^2 and shows it is not an artifact of a loose inequality.
The gap that remains is real, not cosmetic, and is now stated as
precisely as this project has been able to state it: closing the
factor of B^2 requires a genuinely new input beyond Sidon-ness, most
plausibly either a non-vacuous per-character bound at this scale (not
currently known) or the empirical measurement of item 8(c), which is
now the most direct remaining source of evidence on the question. A
relaxed computational budget for constructing F (up to O(B^2), rather
than treating F as arbitrary) was also checked and does not provide
an escape (section 7.6): the shortfall sits at a strictly higher
order (U^3 / 8th-moment) than what O(B^2) pairwise-sum data can
certify (U^2 / 4th-moment), a mismatch that holds for any selection
rule built from that data, not just the specific greedy construction
considered.

10. Empirical status summary (this project's implementation, post-revision-7)
--------------------------------------------------------------------

This section records what has actually been measured/implemented
against the theory above, as a durable reference distinct from the
theoretical content of sections 1-8. Everything here is empirical or
implementation-level; it does not change any proof above, but it
does tell you where the implementation currently sits relative to
what sections 7.5-7.6 predict, and flags one open question those
sections do not address.

10.1 Empirical growth-exponent measurements (strategy_comparison.jl)
--------------------------------------------------------------------

The M8 ratio (empirical M8 / flat-value B^8/N, via Monte Carlo
character sampling) was fit as ratio ~ C*N^gamma across N in
{10007, 100003, 1000003, 10000019}, B ~ N^0.4 (i.e. the real
factor-base constraint after accounting for N ~ p^2), for several
construction strategies:

  strategy                          fitted gamma   R^2
  greedy (baseline)                 0.4607         0.9989
  greedy_low_energy (tiebreak)      0.4793         0.9970
  Singer (native scale)             0.0083         0.8298
  embedded Singer @ q_exp=0.2 (REAL)1.5724         0.9985

The reference points from section 7.5/7.6 are gamma~0 (flat/(H0)-
consistent, best case) and gamma~1.2 (section 7.5's pessimistic
worst-case bound derived from Sidon-ness + trivial pointwise bound
alone). Two results are worth stating plainly:

  (i) Plain greedy sits at gamma~0.46, comfortably BETTER than the
      1.2 worst-case reference, across four decades of N, with a
      tight fit (R^2>0.998). greedy_low_energy (an O(B^2)-budget
      pairwise-flattening tiebreak, in the spirit of the selection
      rule considered and rejected in section 7.6) does NOT improve
      on plain greedy -- gamma is marginally worse (0.479 vs 0.461),
      within the noise of a single-seed comparison. This is
      consistent with 7.6's argument that pairwise-flattening pushes
      F toward the *generic* Shkredov branch (where the bound is
      already what greedy achieves), not toward the *structured*
      branch where genuine improvement would need to come from.

 (ii) Singer difference sets, which ARE genuine algebraic structure
      (Shkredov's "structured branch" candidate per section 7.6),
      perform excellently at their OWN native scale (Nq = q^2+q+1,
      B=q+1, gamma~0.008 -- essentially flat) but catastrophically
      once embedded/compressed into the real target N at the real
      constraint B~N^0.2 (gamma~1.57, WORSE than greedy and at or
      beyond the 1.2 pessimistic reference). An exponent sweep
      (target_q_exponent from 0.2 up to 0.45) confirms this is a
      genuine embedding-compression effect, not a measurement
      artifact: gamma improves monotonically as the exponent (and
      hence Nq/N) increases toward the point where embedding stops
      being lossy, but the REAL constraint is fixed at 0.2 by
      B ~ p^(2/5), so this improvement is not accessible in practice.
      Section 7.6 anticipated exactly this kind of gap: "there is no
      existing argument that C's d1-point set contains, or
      approximates, [a Singer-like] structure" at the actual scale
      needed. This has now been checked directly and the algebraic-
      structure escape route, at least via this embedding approach,
      does not work.

Reading (i) and (ii) together against sections 7.5-7.6: the
theoretically-predicted escape from the generic-branch bound
(genuine algebraic structure) is available in principle but fails in
the one place it has actually been tried at the real problem scale,
and the theoretically-blocked route (pairwise-only selection, however
clever) is, as predicted, not distinguishable from baseline greedy.
No construction tried to date beats the generic-branch gamma~0.46
regime. Per section 7.5's exact accounting, gamma=0 corresponds to
closing the full B^2 shortfall; the measured gamma~0.46, while well
short of the gamma~1.2 pessimistic bound, is not itself evidence of
convergence toward gamma=0 -- section 7.6's argument is that generic
(unstructured) constructions are theoretically capped near the
generic-branch value regardless of how much larger N gets, and the
flat, tight fit across four decades of N here is consistent with
that cap already having been reached rather than being a transient
partway point on a trajectory toward gamma=0.

10.2 Cheap-proxy search (new_invariants.jl) -- an empirical test of
    whether O(B^2) selection can be MADE to work in practice, even
    though section 7.6 already rules it out as a certifiable proof
    strategy
--------------------------------------------------------------------

Section 7.6 proves that no O(B^2)-cost selection rule can CERTIFY
8th-moment suppression (U^2 data cannot imply U^3 control). It leaves
open whether some cheap, empirically-validated O(B^2) SCORE might
still correlate well enough with the true 8th moment to be useful as
a practical, uncertified tiebreak. Five candidate scores were
implemented and tested retroactively against the one confirmed
ground truth available (greedy: known-good, gamma~0.46; embedded
Singer @ q_exp=0.2: known-bad, gamma~1.57), checking only whether
each score separates the two in the correct direction:

  proposal                            result
  1. Gauss/multiplicative-char corr.  no consistent separation across N
  2. AP-discrepancy (L^2)             separates CONSISTENTLY but
                                       BACKWARDS -- lower discrepancy
                                       (more structured) tracks the
                                       WORSE (Singer) strategy at every
                                       N tested. Plausible read: this
                                       score detects algebraic
                                       structure in general, not 8th-
                                       moment suppression specifically,
                                       and those two are anti-
                                       correlated in this problem (per
                                       9.1(ii), the one structured
                                       construction tried is also the
                                       one with bad 8th-moment
                                       behavior at the real scale) --
                                       this is a real, useful negative
                                       result, not just a null one.
  3. Structured (AP) vs iid Fourier   no trend across N (ratio bounces
     sketch                           0.41-2.13); no evidence the
                                       structured sketch is tighter.
  4. Difference-of-differences energy CONFIRMED CONSTANT (=1) for every
     (diff_set_energy)                Sidon set by construction --
                                       zero degrees of freedom, dead on
                                       arrival, same failure mode as
                                       the originally-discarded pair-
                                       sum-energy idea one level up.
  5. Sampled R(t)-variance            initial run showed apparent
     (autocorrelation of pairwise-    separation in the correct
     sum histogram; GPT-proposed,     direction, but on inspection
     this session)                   most of Singer's data points
                                       (B=6..24, so mu=B^4/N is tiny)
                                       landed in a degenerate regime
                                       where R(t)=0 for nearly every
                                       sampled shift purely because
                                       R's O(B^4) total mass is spread
                                       across N >> B^4 possible shift
                                       values -- producing
                                       Rvar_hat/mu^2 -> 1 as a trivial
                                       sparsity artifact, independent
                                       of any real 8th-moment
                                       structure. NOT YET a validated
                                       proxy; needs normalization
                                       against a random-set null
                                       (analogous to the gauss_T/B fix
                                       applied to proposal 1) before
                                       it can be trusted, and needs
                                       re-running post-fix before any
                                       conclusion is drawn.

Current bottom line: of five cheap-proxy attempts, none has yet
produced a validated, correctly-directed, non-degenerate 8th-moment
predictor. This is the expected outcome given section 7.6's proof
that no such proxy can be certified to work in general -- what was
open was only whether one might work well ENOUGH in practice to be
useful without a certificate, and the evidence so far (one dead-on-
arrival, one backwards, two null, one unresolved/likely-artifactual)
does not support that either. Proposal 2's inverted-but-consistent
result is the most informative outcome of the five and is worth
further investigation in its own right (see caveat above), separate
from whether it can serve as a usable score.

10.3 Restart accounting: relation accumulation without re-rolling F
--------------------------------------------------------------------

A question came up in this project's discussion of restart counts:
does treating F as fixed (built once, not re-rolled per attempt) and
accumulating relations from independent Delta draws against that same
F -- rather than a single-hit framing -- change the B^2 shortfall?

This is already answered, more precisely than an initial pass at it
here managed, by item 8(d) above: accumulating relations against a
FIXED F does not convert restarts into independent evidence about the
underlying success rate, because every restart on the same F shares
the same unknown E(S,S) -- a "bad" F disadvantages every attempt on
it equally, correlated through that shared unknown. This is a
distinct point from the per-Delta magnitude question (which is a
property of E(S,S) alone and does not depend on attempt ordering):
the B^2 shortfall in section 7.5's bound is unaffected by how many
Delta's you draw against one F, but the fixed-F correlation means
those draws cannot be used to empirically ESTIMATE the true success
rate the way independent trials could -- for that, item 8(d)'s
full-reroll-of-F Beta-Binomial recipe is the correct instrument, not
batch accumulation on a fixed F.

One thing item 8(d) does not cover, since it is about ESTIMATING
theta rather than the underlying combinatorial bound itself: if
failed attempts against a fixed F leave behind reusable partial state
(e.g. near-miss Mumford-coefficient matches short of a full hit) that
correlates outcomes across successive Delta draws on that SAME F in a
way that changes the per-Delta hit probability itself (not merely the
statistical independence of the estimate), the Paley-Zygmund argument
underlying section 7.5's bound would need to be re-derived for
whatever correlated-trial process is actually implemented -- this is
a question about the bound, not about estimating it, and is not
analyzed anywhere in this document. Flagged here as open and distinct
from item 8(d), not as a resolution of the existing gap.



- P. Gaudry, E. Thome, N. Theriault, C. Diem, "A double large prime
  variation for small genus hyperelliptic index calculus" (2005).
- C. Diem, "Index calculus with double large prime variation for
  curves of small genus with cyclic class group", arXiv:math/0606607.
- C. Diem, "Index Calculus in Class Groups of Plane Curves of Small
  Degree" (slides / ANTS VII).
- A. Forey, J. Fresan, E. Kowalski, "Sidon sets in algebraic
  geometry", arXiv:2301.12878 (2023), Theorem 1.
- M. Ortega, S. Prendiville, "Extremal Sidon sets are Fourier uniform,
  with applications to partition regularity", arXiv:2110.13447 (2021),
  Theorem 1.2.
- I. D. Shkredov, "On an application of higher energies to Sidon
  sets", arXiv:2103.14670, Theorem 2, for the higher-energy
  dichotomy used in section 7.6.
- S. Eberhard, "The apparent structure of dense Sidon sets", Electron.
  J. Combin. 30 (2023), for the observation that near-maximal dense
  Sidon sets rely on algebraic structure rather than greedy/random
  construction, used in section 7.6.
- Y. C. Cheng, "Greedy Sidon sets for linear forms", J. Number Theory
  266 (2025), 225-248, for the scope and limits of greedy Sidon
  constructions cited in section 7.6.
- A. Forey, J. Fresan, E. Kowalski, Y. Wigderson, "Jacobian graphs",
  arXiv:2603.13198 (2026), for the fourth-moment/semicircle-law
  equidistribution result checked against the gap in section 7.7
  (does not close it -- see that section).
- Advisory-5 (this project), for the original heuristic and open
  assumptions.
- Advisory-6 (this project), for the rigorous Sidon/Fourier-uniformity
  grounding of assumption (b) and the initial characteristic-0
  finiteness result for assumption (a), carried forward unchanged in
  sections 1-6 above.
- P. Deligne, "La conjecture de Weil II", Publ. Math. IHES 52 (1980),
  for the purity/Weil-II input used in section 7.1.
- S. Lang, "Algebraic groups over finite fields", Amer. J. Math. 78
  (1956), for the Lang isogeny used to construct the character sheaves
  of section 7.1. NOTE: the specific application to abelian varieties
  via phi = Frobenius - 1, as a source of rank-1 character sheaves on
  J indexed by all of J(F_p) (rather than a fixed small-order
  subgroup), is standard in spirit — the natural generalization of
  Artin-Schreier/Kummer sheaves, in the manner of Katz's and
  Kowalski-Michel-Sawin's trace-function formalism — but a pinpoint
  reference carrying out exactly this construction was not located
  during this work (see section 7.1) and should be independently
  verified before section 7's results are relied upon further.


11. Preliminary Findings: 2D Translation Symmetry, Log Minimality, and Table-Based SmoothnessRecent theoretical developments have clarified the geometry of the matching equation, providing a concrete mechanism to quotient out its positive-dimensional behavior. While the final geometric proof remains open, the conjectural basis is now robust enough to define the next phase of the attack.11.1 2D Translation Symmetry and the Square SystemWe have identified that the core matching condition $P_1 + P_2 - P_3 - P_4 = (\alpha - \alpha')a$ is genuinely 2-dimensional. Specifically, for any solution pair $A = P_1 + P_2$ and $B' = P_3 + P_4$ (temporarily overloading $B$ to denote the sum rather than the factor base size), the tuple $A+T, B'+T$ is also a valid solution for some Jacobian translation operator $T$.Despite this 2D symmetry, the 12-equation system derived from this condition is confirmed to be square.11.2 Log Minimality of the Returned SolutionCrucially, the solution returned by this square system is log minimal. This relies on the discrete logarithm property $\log(A) \le \log(A+T) \le \log(A) + \log(T)$.This minimality can be demonstrated via contradiction:Suppose the returned solution $A, B'$ is not log minimal. Then there exists a smaller solution $A', B''$ such that $A' + T = A$ and $B'' + T = B'$ for some positive translation $T$. Substituting these into the core matching equation causes the $T$ operators to cancel out algebraically. This leaves a solve over $A', B''$ as variables, which yields the exact same 0-dimensional solution as previously found (identical up to the primes). This forms a contradiction, proving the system inherently isolates the log-minimal solution.11.3 Quotienting the 2Dness via $\mathcal{O}(B^2)$ Table LookupTo exploit this log minimality, we adapt the factor base (size $B$) to consist of the first $\sim B$ prime multiples of the subgroup generator $a$. This allows us to decompose any matching logs we find.Because we have an $\mathcal{O}(B^2)$ precomputation budget available, we can construct a lookup table of the first $B^2$ discrete logs. Consequently, checking a returned solution for smoothness is now strictly equivalent to checking for a log match within this table.By pushing the smoothness check into this log-lookup phase, we effectively quotient out the 2D translation symmetry, allowing the algorithmic pipeline to proceed cleanly.11.4 Remaining Open TaskThe algorithmic pathway is now clear, but the underlying geometry requires formal closure: we must still rigorously prove that the system of equations is strictly 0-dimensional up to the translation operator $T$. This replaces the generic finiteness questions of Section 6 with a highly specific geometric target for future verification.

12. The Bad-Curve Locus: What Degenerates the 12-Equation System, and What Doesn't

Prompted by the question "what is the exceptional set Bad the O(B^4) <= d . #{Delta : X(Delta)>0} counting argument (section 11, and ROADMAP-alpha-locus.md) needs to be small" -- this section characterizes, as precisely as the current Lean formalization supports, where the 12-equation decoupled system (section 11.1, `DecoupledSystemRegular.lean`/`AlphaLocusDegreeUniform.lean`) actually degenerates. Two structurally different loci were found; they should not be conflated.

12.1 The interpolation-matrix locus (MatrixNondegenerate): fully characterized, small, and already case-split in Lean

Each sample's own Cantor reduction solves a 4x4 linear system (Cramer's rule) built from two anchor points t1,t2 (Riemann-Roch interpolation nodes) and the target Mumford divisor u(x)=x^2+u1*x+u0. The system's determinant was computed symbolically this pass and factors completely:

  det(A) = -(t1 - t2) * u(t1) * u(t2)

i.e. the interpolation degenerates exactly when (a) the two anchor points coincide (t1=t2, a tangency on the anchor side), or (b) one of the anchor points lies on the target divisor's own zero locus (u(t1)=0 or u(t2)=0, an anchor/target collision). Point (b) further splits, via the curve equation y^2=f(x), into "same point" (excluded by an existing anchor/target-disjointness convention, not a new case) and "iota-conjugate point" (a genuine tangency, four symmetric sub-variants depending on which anchor point collides with which target point).

Every one of these cases already has its own complete, REPL-confirmed, 0-`sorry` top-level theorem in the codebase (`AlphaLocusDegreeUniformTangent.lean`, `AlphaLocusDegreeUniformTangentTarget.lean`, and the four `CAWitnessCrossTangent*`/`AlphaLocusDegreeUniformCross{1,2,3,4}.lean` files), and `ReducedClassDispatch.lean`'s `reducedClassDispatch` already routes between all of them via a real case split (`by_cases` on the two X-coordinate equalities, then a `match` on a 5-constructor `CrossCase`). The only unhandled residual is simultaneous anchor-and-target tangency (both collisions at once), explicitly excluded via a named hypothesis (`hRaT`) rather than silently assumed away, and deferred because no caller has needed it yet. Conclusion: this locus is codimension >=1, geometrically meaningful (classical Cantor-reduction degeneracies), and its Bad-relevant content is essentially already closed.

12.2 The cross-sample resultant locus (CrossNondegenerate / PeelChainNondegenerate): a materially different, open, and NOT necessarily small, problem

The 12-equation system additionally requires, for each of the four repeated target variables U0,U1,V0,V1, that a resultant-type expression comparing sample A's and sample B's independently-computed Cantor-reduction coefficients (e.g. `hu0`'s `u1_den(0)*u2_num(0) - u2_den(0)*u1_num(0)`) be a non-zero-divisor (not merely nonzero -- `IsSMulRegular`, per a corrected proof gap recorded in `DecoupledSystemRegular.lean`) in the quotient by the already-imposed prefix relation.

Unlike section 12.1's locus, this resultant compares two constructions living in genuinely disjoint variable sets (sample A's own {a1,a2,wa1,wa2} vs sample B's own {b1,b2,wb1,wb2}, tied together only through the shared curve coefficients c0..c4 and the shared target variable). There is no algebraic reason for this to factor the way det(A) did -- section 12.1's factorization came from comparing a construction against itself; this compares two independent evaluations, and the codebase's own documented counterexample (`Fu0=a(1-U), Fu1=b(1-U)`, identically dependent for ALL a,b,U) shows this shape of degeneracy can in principle hold on the WHOLE space, not just a thin sublocus, for unlucky choices of the ambient curve. `DecoupledSystemRegular.lean`'s own docstring already states this plainly: `CrossNondegenerate` is "expected to be FALSE for at least some, quite possibly most, choices of (c0,...,c4)" and is recorded as an open, per-instance hypothesis, not a theorem.

This means Bad, as currently scoped in `AlphaLocusDegreeUniform.lean` (a locus in (alpha,alpha')-space for a FIXED curve), may be understating the problem: if `CrossNondegenerate` fails identically for some curves, the correct statement needs an additional "the curve itself is good" hypothesis or a Bad that also varies over (c0,...,c4), not only over (alpha,alpha'). This has not been resolved on paper and no attempt was made to hand-derive the resultant's closed form (a direct symbolic expansion was attempted and produced an unenlightening, non-factoring multivariate polynomial in t1,t2,u0,u1,v0,v1,w1,w2 -- consistent with there being no clean geometric collapse to find here, not with an error in the computation).

12.3 A concrete, curve-agnostic runnable check for section 12.2

No closed form is available, but the check itself is cheap and mechanical -- exactly the kind of screen that should run before trusting a specific curve/sample pair:

  1. Run Cantor reduction on sample A's data (P1,P2 against the anchor), obtaining its reduced (u,v) coefficients as num/den pairs (no GCD reduction needed).
  2. Run Cantor reduction on sample B's data (P3,P4 against the same target U0,U1,V0,V1) the same way.
  3. For each of the four repeated-target slots (U0,U1,V0,V1), cross-multiply: R = denB*numA - denA*numB.
  4. Check R != 0 mod p, for all four R's.

A curve/sample pair failing this check at step 4 is a candidate for the CrossNondegenerate-failure locus and should not be assumed to give a well-posed 0-dimensional system without further, currently-unwritten, argument. This is the practical analogue of section 11's numerical 0-dimensionality check (HomotopyContinuation.jl), scoped specifically to this one algebraic hypothesis rather than the system's dimension as a whole, and is a natural next thing to sweep over (multiple curves, not just multiple (alpha,alpha') on one curve) to determine whether section 12.2's worst case is realized in practice or is a pessimistic-but-rare corner, mirroring section 10's cheap-proxy-search methodology.
