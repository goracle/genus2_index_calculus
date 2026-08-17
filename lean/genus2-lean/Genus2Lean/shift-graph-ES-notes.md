# Notes: a shift-graph attack on the E(S,S) bottleneck (v2, pruned)

Status: **closed as a proof strategy**, unconditionally (not just
heuristically). Companion to `genus2-index-calculus-advisory-6.md`
(revision 7), sections 3-7 and item 8(c). This supersedes the v1 notes:
same conclusion, but the v1 file recorded several dead-end passes
(a degree-growth scare that turned out not to apply to genus 2, and
one real in-session error — see §5) before landing here. Pruned to the
load-bearing chain; the abandoned material is summarized in §7.

## 1. The open problem

Advisory-7 §7.4-7.5 pins the whole remaining gap in the complexity
heuristic on one quantity: E(S,S), the additive energy of S = T+T,
T = s(F) ⊂ J(F_p). Target: E(S,S) ≪ B^8/|J| (eq. 13). Known
unconditionally: E(S,S) < 2B^6·|J| from Sidon-ness alone (§7.5, eq.
16) — short of the target by exactly a factor B². Four independent
routes (Sidon/Cauchy-Schwarz, Ortega-Prendiville Fourier, a Lang-torsor
Weil-II bound, FFKW's 4th-moment paper) all cap out at this same B²
shortfall. §7.6 explains why structurally: these are all U²-level
(pairwise-sum) arguments, and E(S,S) is a U³-level (8th-moment)
quantity — a theorem of Shkredov says U² data can't certify U³ facts
without extra structure.

## 2. The construction: shifting witnesses between Δ's

A witness of Δ is a pair (P1,P2),(P3,P4) with (P1+P2)-(P3+P4) = Δ·a.
The shift move: absorb δ·a (δ in a bounded range, or all of ⟨a⟩) into
the P-side instead of the Δ-side, i.e. Cantor-reduce (P1+P2)+δ·a to a
Mumford pair (u_δ, v_δ). If u_δ splits over F_p (two rational roots),
this yields a genuine new witness pair (P1',P2') with
(P1'+P2')-(P3+P4) = (Δ+δ)·a — a witness of N(Δ+δ) built from a witness
of N(Δ). The move is exactly invertible (shift by -δ·a) whenever both
sides split, so *conditional on splitting* it's a real bijection, not
a heuristic correspondence.

Splitting is governed by a discriminant/QR condition on u_δ. A random
monic quadratic over F_p splits with probability exactly 1/2, so the
correspondence is witness-by-witness defined on (heuristically) half
of the witnesses at a time.

Goal: if this spreads a lumpy Δ's witnesses out across many other Δ's,
it gives leverage on E(S,S) that's an orbit/expansion argument rather
than Fourier/Cauchy-Schwarz — a genuinely different route from the
four already exhausted.

## 3. Scope actually needed

We do not need a global spectral gap on all of ⟨a⟩ (size n ~ p²).
Only local mixing on the target set of Δ's (size B ~ p^(4/5)/p²
relative to ⟨a⟩) is needed — materially weaker than the sup-norm
uniformity §7.1-7.2 of the advisory already ruled out. Caveat: local
mixing between two size-B sets is itself an E(S,S)-flavored
second-moment quantity, so this may be a new way to *compute* E(S,S)
rather than a way around it. That caveat turns out to be exactly
right — see §6.

## 4. The double-counting bound

Fix Δ₀ with witness count M = N(Δ₀). For every δ ∈ ⟨a⟩ (a symmetry
statement, not a search budget — the correspondence is defined for
every δ whether or not any run computes it), the shift gives a
bijection between Δ₀'s split-witnesses and a subset of Δ₀+δ's
witnesses. Write s(Δ₀,δ) for the fraction of Δ₀'s M witnesses with
u_δ split. Summing over δ ∈ ⟨a⟩ and comparing against the exact
identity Σ_Δ N(Δ) = B^4 (advisory §7.3):

    M · Σ_δ s(Δ₀,δ)  ≤  B^4.                                    (18)

If s(Δ₀,δ) ≈ 1/2 uniformly (not just on average) over δ:

    M  ≤  O(B^4/n).                                              (19)

This would pin E(S,S) at its flattest possible value and close the B²
gap by a wide margin — far more than advisory-7 actually needs. So the
entire gap reduces to one clean hypothesis: uniform splitting of the
shift-graph's residual quadratic across the full δ-orbit. No Fourier
analysis, no Weil bound, no sheaf theory required to *state* it.

Two proposed shortcuts to (19), both checked and rejected:

- **Hardness-reduction argument** (Zhang/Boneh-Shparlinski-style
  hardcore-bit theorems): doesn't apply. Those theorems are about
  predicting a bit of a *secret* scalar multiple without computing it.
  Here δ is a public integer the algorithm itself iterates over, and
  δ·a is directly, deterministically computable — there's no oracle
  being asked to predict something it can't just compute. The
  surrounding project being a DLP attack doesn't transfer hardness
  onto an auxiliary quantity that's trivially computable from public
  data.
- **"Bijectivity alone spreads the mass" argument**: this just *is*
  (18)-(19), not a free pass to it. Bijectivity only guarantees the
  mass lands somewhere (first moment); it doesn't guarantee the
  landing is flat (second moment) unless s(Δ₀,δ) is close to 1/2
  *uniformly*, not just on average. A permutation can conserve total
  mass while redistributing it arbitrarily unevenly — that unevenness
  is precisely the "lumpy Δ" failure mode this whole document is
  about.

## 5. The splitting-uniformity hypothesis: actually proved, unconditionally

Literature search found nothing establishing δ-orbit uniformity for
disc(u_δ) as a *dynamical/ordered* statement, as opposed to a static
aggregate density over the group — worth flagging because the two are
easy to conflate (an earlier pass in this project did conflate them).
But it doesn't need a literature source: it follows directly from two
facts already in hand.

**(a) δ·a is a bijection ⟨a⟩ ↔ ⟨a⟩** (δ ↦ δ·a, by definition of a as a
generator). So the "sequence" disc(u_{δ·a}) for δ = 0,...,n-1 is just a
relabeling of the fixed, static split/inert type of every element of
⟨a⟩, each hit exactly once — there's no separate generative process
whose δ-dependent bias needs checking.

**(b)** The curve's own point count (#C(F_p) = p+1-t, Weil's bound on
t) pins the aggregate split/inert density over all of J(F_p) at
1/2 + O(1/√p). Since ⟨a⟩ has index O(1) in J(F_p) (the standard
cryptographic-subgroup assumption — a small or index-heavy ⟨a⟩ would
itself be a weak-curve red flag), this density transfers to ⟨a⟩
directly:

    #{δ ∈ ⟨a⟩ : disc(u_{δ·a}) splits} / |⟨a⟩| = 1/2 + O(1/√p).   (20)

**Sharper: this holds per-witness, not just on average.** Fix one
witness's value sol₀ = P1+P2. By construction, u_δ *is*, by
definition, the Mumford-u of the group element δ·a + sol₀ — not a
separate quantity needing its own transfer argument. Since δ ↦ δ·a is
a bijection and translation by sol₀ is a bijection on any group, the
composite δ ↦ δ·a + sol₀ is a bijection ⟨a⟩ ↔ ⟨a⟩. Applying (20)'s
density to this composite:

    #{δ ∈ ⟨a⟩ : u_δ splits, fixed sol₀} / |⟨a⟩| = 1/2 + O(1/√p). (21)

unconditionally, for *every* individual witness of *every* Δ₀, lumpy
or not. Averaging (21) over Δ₀'s M witnesses gives s(Δ₀,δ) averaged
over δ = 1/2 + O(1/√p) directly — (21) already *is* the conditional
statistic (18) needs, not a weaker marginal fact requiring a transfer
step. So (18)-(19) is unconditional: M ≤ O(B^4/n) for every Δ, no open
hypothesis, no character-sum estimate, no empirical check needed.

**This should have been the closing argument. It is treated with
suspicion below because it is too strong** — an elementary
bijection-plus-Weil-bound argument closing a gap that four independent
heavy-machinery routes all failed to close, on a problem the advisory
proves (§7.5) is extremal given Sidon-ness + the trivial pointwise
bound alone. (This argument doesn't use either of those two inputs, so
it isn't directly contradicted by that extremality proof — but a
result this clean warrants checking hard before relying on it, not
accepting at face value.) The check finds a real gap: §6.

## 6. The actual gap: splitting ≠ witness. F-membership is the missing factor.

(18)-(21) establish that "u_δ splits" happens with density 1/2 along
the δ-orbit. But splitting only produces a pair of rational points
(Q1(δ), Q2(δ)) on C(F_p) — a genuine *witness* additionally requires
Q1, Q2 to land in the factor base F itself (|F| = B, and B ≪ p =
|C(F_p)|). This condition was silently absent from §4-5 entirely, and
it's not a minor correction: folding it in changes the answer.

Genus-2 reduced divisors correspond generically 1-1 with unordered
pairs of distinct points of C(F_p) (consistent with |⟨a⟩| = n ~ p²
matching |Sym²(C(F_p))| ~ p²/2). So the split half H of the bijection
in §5 identifies with close to half of *all possible pairs* of
C(F_p)-points. Take F as a uniformly random size-B subset of C(F_p)'s
~p points. For a fixed pair (Q1,Q2) ∈ H, P(Q1,Q2 both ∈ F) = (B/p)²
independent of which pair. So:

    E_F[ #{(Q1,Q2) ∈ H : Q1,Q2 ∈ F} ]  ~  (n/2)·(B/p)²  ~  B²/2.  (22)

Correcting (18)'s per-δ rate from "splits" (density 1/2, eq. 21) to
"splits AND lands in F×F" (density (1/2)(B/p)²) and re-deriving:

    M · n · (B/p)²  ≲  B^4   (in expectation over F)
    =>  M  ≲  B² · p²/n  =  Θ(B²)          [n = Θ(p²)]

**Θ(B²) is exactly the trivial pointwise cap** that holds for every Δ
with zero machinery: N(Δ) counts pairs (s,s') ∈ S² with s-s' = Δ·a, so
s determines s' up to |S| ~ B²/2. So all of the near-bijection
machinery, once corrected, reproduces information that was already
free — it cannot discriminate a flat Δ₀ from a maximally lumpy one.

**This is the actual resolution of the "seems fishy" intuition.** The
counting/bijection property is completely real (§5, eqs. 20-21) — it's
not a trivial or hand-wavy bound at the level of the raw group ⟨a⟩.
But it lives on ⟨a⟩ (size ~p²), and the factor-base restriction (an
independent-looking (B/p)² dilution) is exactly what erases the gain
before it reaches N(Δ). A near-bijection on a big set, sub-sampled down
to a small target set, does not in general beat what you'd get from
the small set's size alone — that's not a bug in this argument, it's
generic behavior, and here it happens to land exactly on the trivial
bound rather than above or below it.

**Two independent checks that this isn't recoverable:**

- **Aggregating over Δ₀'s own M witnesses** doesn't help: at fixed δ
  the M shifted images are pairwise distinct (translation is
  injective); across different δ, two witness-orbits collide at
  exactly one δ per pair of witnesses. Total collision budget O(M²)
  against M·n total (witness,δ) pairs; since M ≤ B² ~ p^(4/5) ≪ √n ~
  p, collisions are negligible. But this is bookkeeping of a *rate*,
  and rates don't compound under a linear sum over M — aggregating M
  copies of a per-witness rate just multiplies by M, which is exactly
  the unknown the bound is solving for. It cancels out. Same bound.
- **A second application of the shift move** ("diffuse further")
  fails for a structural reason, not a quantitative one: composing two
  shifts (δ then δ') is translation by δ+δ' — abelian, no exception.
  Round 1 already summed δ over the *full* group ⟨a⟩, so every value
  of δ+δ' was already reached in round 1. There's no unexplored
  territory for a second step to reach; this differs fundamentally
  from a sparse-generating-set Cayley graph, where a second step
  genuinely finds new vertices. (An alternative "sum the mass across
  every Δ it spreads to" reading also just reproduces Θ(B^6) via
  Cauchy-Schwarz on the same trivial per-Δ cap — same wall, different
  route to it.)

A structurally different move — shifting *both* sides of the matching
equation by the same δ (a self-map on Δ₀'s own witness set, rather
than moving between Δ's) — was checked under an independence
assumption on the two splitting events and found self-consistent with
flatness (i.e. it doesn't secretly re-lumpify an unlumpy Δ₀), but
depends on an unproven joint-correlation claim that is exactly as open
as everything else here, and doesn't produce a bound either way.

## 7. Final status (superseded — see §8-9)

The shift-graph route (full-sum shift, §2-6) is **closed as a proof
strategy** for advisory-7's B² gap. Not "reduces to the same wall"
vaguely — shown concretely to cap out at exactly the trivial bound via
two structurally different aggregations (§6), with the near-bijection
step itself fully unconditional (§5, eqs. 20-21) and Lean-formalizable
as an isolated fact. It just answers a uniformity question at the
wrong scale (density over the full group ⟨a⟩, order n ~ p², rather
than density restricted to F×F, order B ~ p^(2/5)) for the gap that
needs closing.

This closure stands for the *full-sum* shift of §2. §8 opens a distinct
single-leg variant that briefly (and, on two separate occasions,
incorrectly) appeared to beat it; §8 records both wrong turns and the
corrected conclusion. §9 corrects the target itself. The bottom line
(post §8-9): the single-leg construction does **not** beat the trivial
bound either — worse, it's slightly weaker than trivial once quotiented
correctly (§8.9) — but it exposes a τ-symmetry expansion structure
worth pursuing as an L² statement rather than an L^∞ one, and the
target it should be checked against is `E(S,S) ≍ B^4 + B^8/n`, not
`B^8/n` alone.

## 8. Single-leg shift: two false "beats the trivial bound" claims,
   corrected

Same setup as §2, but shift only one point of the 4-tuple (say P1)
rather than the sum P1+P2: Cantor-reduce `P1+δa`, and if it splits into
`(R1,R2)`, this gives `R2+P2-P3-P4 = (Δ₀+δ)a`. This is a genuine 2-vs-2
witness of a new Δ' — *if* the leftover `R1` can be legally absorbed
into the Δ-side, which requires `R1 ∈ H := ⟨a⟩`, i.e. `R1=τa` for some
integer τ, giving `Δ'=Δ₀+δ-τ`.

**8.1-8.3 (the naive count).** Splitting density 1/2 (unconditional,
same argument as (20)-(21), translate-by-P1 instead of
translate-by-(P1+P2)). Landing density for R2 alone: (B/p) (R2 is a
genuinely new point, same reasoning as §6). `R1∈H`: since H has index
O(1) in J(F_p) *and* the curve's embedding into J has no structural
reason to align with H's cosets, `|H∩C(F_p)| ~ p`, so `P(R1∈H) ~ Θ(1)`
— not the (B/p) dilution R2 pays, since R1 only needs curve-membership
via H, not factor-base membership. Naive per-(witness,δ) hit rate:
`~(1/2)·Θ(1)·(B/p)`, summed over M witnesses and n~p² values of δ
against the budget `Σ_Δ N(Δ)=B^4`:

    M·n·(B/p) ≲ B^4  ⟹  M ≲ B^4·p/(nB) = B^3 p/n ~ B^3/p            (34, first pass)

giving `M ≲ p^{1/5}` at `B=p^{2/5}` — apparently *beating* the trivial
`M≲B²=p^{4/5}` bound by a wide margin. **This was wrong**, and wrong
twice, in two different ways, before landing on the correct count.

**8.4 (first, incorrect fix attempt).** An initial worry: for fixed
output `(R2,P2,P3,P4)`, how many `(δ,τ)` pairs produce it? A first
guess used `|H∩C|~p` directly as a stabilizer size (conflating "how
many curve points could R1 land on" — a density fact, §8.9-8.10's real
content below — with "how many δ give this *specific* output" — a
fiber-size fact). That guess is invalid: `δ↦(R1(δ),R2(δ))` is
injective (translation by δa is injective), so for *fixed* output the
naive stabilizer is actually 1, not p — this was checked and rejected
in-thread (it wrongly implied `M≲B³`, the vacuous bound, for the wrong
reason).

**8.5 (second, also-incorrect fix attempt).** A second pass argued the
opposite: since `R1` alone (not the pair) is a map from a
δ-domain of size ~p² into a curve of size ~p, pigeonhole forces an
average fiber of size ~p on `R1` alone — and (wrongly) treated this as
forcing `Δ'=Δ₀+δ-τ` to collapse across that fiber. This is also wrong:
within a fixed-R1 fiber, τ is constant (it's R1's own fixed discrete
log), so `Δ'` varies *injectively* with δ across that fiber — no
collapse there. Both 8.4 and 8.5 located the redundancy in the wrong
place before the correct count was worked out.

**8.6 (the correct count).** For a *fixed output* `(R2,Δ')` (not fixed
R1), how many `(δ,τ)` pairs produce it? From `R2=P1+δa-τa` and
`δ-τ=Δ'-Δ₀` (fixed once Δ' is fixed), solving for `P1` gives

    P1 = R2 - (Δ'-Δ₀)a,                                              (35)

**independent of τ** — meaning every one of the up-to-`|T|~p` values of
τ consistent with this output (`T:=H∩C(F_p)`, `|T|~p`) correspond to
the *same* P1, i.e. the *same* single fact ("this P1 is in F"), not p
independent constraints. So a fixed output witness has ≤ O(p)
preimages in the (witness,δ) count, and the correct comparison is

    M·n·(B/p) ≲ p·B^4   ⟹   M ≲ p²B³/n ~ B³   (n~p²).                (36)

At `B=p^{2/5}`: `M ≲ p^{6/5}` — **weaker than the trivial `M≲B²=p^{4/5}`
bound**, not stronger. So the single-leg construction, correctly
quotiented, does not beat §6 either; the apparent `p^{1/5}` win in
8.1-8.3 was an artifact of not quotienting by this τ-symmetry at all,
and both intermediate attempts to fix it (8.4, 8.5) misidentified where
the multiplicity actually lives before (35)-(36) pinned it down.

**8.7 What's salvageable.** Two things survive this correction and are
worth pursuing separately from the (closed) worst-case-M question:

- `|H∩C(F_p)| = |C(F_p)|/m + O(√p)` for index-m H, via the m characters
  of `J(F_p)/H` restricted to the Abel-Jacobi curve — a real,
  checkable Weil-type lemma (same family as (20)-(21)), not just the
  "generic position" heuristic used above it.
- The L² reformulation: since each lumpy witness produces `~n(B/p)~pB`
  raw successful shifts against only an O(p) τ-multiplicity, each
  witness contributes `~pB/p = B` essentially-distinct output
  incidences after quotienting — i.e. one lumpy Δ₀ is forced to spray
  mass across many Δ' at a nontrivial rate. This is a candidate
  *collision/energy*-level statement (bounding how N(Δ₀) constrains
  `Σ_{Δ'} N(Δ')`-type sums), not a worst-case bound on M alone — and it
  plugs directly into `E(S,S)=ΣN(Δ)²` rather than going through a
  lossy pointwise cap first. Not yet carried through; this is the next
  thing to attack, checked against the corrected target of §9.

## 9. Corrected target: `E(S,S) ≍ B^4 + B^8/n`, not `B^8/n` alone

Advisory-7 eq. (13) and this document's §1 both compared against a
target of `E(S,S) ≲ B^8/n`. This is not the right flat benchmark at
the actual parameters. `Σ_Δ N(Δ)=B^4` (exact) plus `N(Δ)²≥N(Δ)`
(trivial) already gives

    E(S,S) = Σ_Δ N(Δ)² ≥ Σ_Δ N(Δ) = B^4                              (37)

unconditionally — and at `B=p^{2/5}`, `B^4=p^{8/5}`, while
`B^8/n~B^8/p²=p^{6/5}`. Since `p^{8/5}>p^{6/5}`, the diagonal/coincidence
term `B^4` **dominates** `B^8/n` at this scale, so the correct flat
benchmark is

    E(S,S) ≍ B^4 + B^8/n,                                             (38)

matching a direct dimension-count of the defining 8-tuple variety
`P1+P2-P3-P4=P5+P6-P7-P8`: generic stratum has dimension 8-2=6, giving
`~p^6(B/p)^8=B^8/p²`, and the diagonal/symmetry strata (where
`{P1..P4}={P5..P8}` as multisets, a bounded number of coincidence
patterns) contribute `O(B^4)` — recovering (38) directly, without
going through a worst-case bound on any single Δ.

**Consequence:** the real target is not "make E(S,S) small in absolute
terms" but bound the *excess* collision energy

    Σ_Δ N(Δ)(N(Δ)-1) = O(B^4)   [or O(B^4+B^8/n)],                    (39)

i.e. show collisions beyond the unavoidable diagonal don't add more
than a constant factor to what's already forced. §8's L² idea (spray
one lumpy Δ₀'s mass across many Δ' via the τ-quotiented shift) should
be checked against (39), not against `B^8/n` alone as §1 originally
framed it. The 8-tuple-variety route above is also a candidate
standalone strategy for (38)-(39) directly, independent of whether the
shift-graph construction of §2-8 goes anywhere further.

What was tried and abandoned along the way, briefly, for the record:

- An initial worry that disc(u_δ) has degree growing like δ² in δ
  (the elliptic-curve division-polynomial analogue) turned out not to
  apply: genus-2 Riemann-Roch fixes the residual polynomial's degree
  at a small constant (K+1, independent of δ's magnitude) by
  construction, confirmed directly against the codebase
  (`build_phi_mumford`/`phi_residual_mumford`/`phi_general.jl` in
  `trial3_phi.jl`). This made the degree bookkeeping a non-issue —
  it just wasn't the actual obstruction (§6 is).
- A framing of the reduction as a mixed exponential/Cayley-graph
  character sum (§3 of v1) is subsumed by the direct bijection
  argument in §5 above and isn't needed once (20)-(21) are in hand.

**Two concrete, cheap, computational checks remain open** (diagnostic
only, not load-bearing for any closing argument):
1. Directly count, on the actual codebase, how many δ·a+sol₀ shifts
   for a real hot Δ₀ land on distinct new Δ's with split u_δ, and
   compare against the B^4/n and Θ(B²) predictions — verification of
   §5-6's unconditional claims, not exploration of an open heuristic.
2. Whether (22), upgraded from expectation to a concentration result
   over F's randomness, is even worth doing given it was already shown
   (§6) to only reproduce the trivial cap — probably not, unless a
   different use for the concentration result surfaces later.

## 10. The 8-tuple-variety route (§9): checked, and it collapses to
    the original open problem, restated

§9 proposed bounding `E(S,S)` directly via the defining 8-tuple
`P1+P2+P7+P8=P3+P4+P5+P6` (equivalent to `(P1+P2)-(P3+P4)=(P5+P6)-(P7+P8)`,
i.e. (40) below), splitting into a diagonal case (multiset coincidence)
and a generic case, with the generic case estimated by a `p^6(B/p)^8`
fiber count. This needed checking on two fronts: whether the fiber
count (10.6 below) is actually derivable rather than asserted, and
whether the resulting strategy is independent of the original E(S,S)
hypothesis or secretly the same one. Both were checked.

**10.1-10.5 (diagonal, fully rigorous).** Write

    E(S,S) = #{(P1,...,P8)∈F^8 : P1+P2+P7+P8=P3+P4+P5+P6}.          (40)

Split by whether `{P1,P2,P7,P8}` coincides with `{P3,P4,P5,P6}` as a
multiset. Coincidence case: given the LHS quadruple freely
(`B^4` choices), the number of coincidence-respecting assignments to
the RHS quadruple is a bounded constant (≤24, likely fewer given the
all-`+` sign pattern here — no `+/+/-/-` sign asymmetry the way the
advisory's `E[X²]` split had). This contributes `O(B^4)` to E(S,S),
**unconditionally**, using only Sidon-ness (to rule out coincidences
beyond the multiset-match itself contributing more than O(1) per
choice) — this piece of the corrected target (§9, eq. 38-39) is now
fully established, not merely asserted.

**10.6-10.7 (off-diagonal, the `p^6(B/p)^8` count, derived not
assumed).** Fixing 7 of the 8 points in `C(F_p)` freely (`~p^7`
choices) pins the 8th via the group equation to a specific element
`g∈J(F_p)`; `g` must additionally land on the curve, `P(g∈C(F_p))~p/p²
=1/p` (a density-of-a-curve-in-an-abelian-surface fact, not a
splitting/Cantor-reduction question — simpler in kind than §5's
splitting density). This gives `~p^7·(1/p)=p^6` valid `C(F_p)^8`-tuples,
confirming the exponent via direct fiber-counting rather than citing a
Lang-Weil dimension heuristic. Restricting all 8 points to F
(independent `(B/p)` each) gives the off-diagonal contribution
`~p^6(B/p)^8 = B^8/n`, confirming (38)'s second term the same way.

**10.8-10.12 (the actual finding: this is not a second, independent
route).** Checked directly: the off-diagonal count in (40) *is*, by
construction, precisely `E(S,S)`'s own non-diagonal part — (40) is not
an alternative derivation converging on the same scale, it is E(S,S)'s
defining sum, split into diagonal (now rigorous, §10.5) and
off-diagonal (everything else, by definition). The `(B/p)^8`-per-tuple
sampling assumption used to get (42) — that F samples the fiber locus
of 10.6 at the generic/expected rate — is not a new or weaker
hypothesis than advisory §3's "F+F is quasi-random" (eq. 2 there): it
is that same hypothesis, restated as "F samples this particular
codimension-1 algebraic locus generically" instead of "F+F is
quasi-random as a subset of J." Both are 8th-order (U³-level)
statements about F; neither is implied by Sidon-ness (a 2nd-order/U²
statement), for the same reason §6 already gives.

**Status: closed as an independent route.** Net result of working this
through: the diagonal term of (38)-(39), `O(B^4)`, is now a fully
proved, unconditional fact (real progress — previously stated but not
separately nailed down). The off-diagonal term is confirmed to be
exactly as open as it always was, under a different name. §10 should
not be cited as a second strategy alongside the shift-graph route; it
is a (useful) rigorization of half of the same target the shift-graph
route was already aimed at, plus a demonstration that the other half
resists an easy re-derivation via fiber-counting the same way it
resisted the Fourier and shift-graph attempts.

## 11. Open, going forward

- §8.7's τ-quotiented L² reformulation (spray one lumpy Δ₀'s mass
  across many Δ' at rate `~B` per witness after quotienting) is, unlike
  §10, built from the shift-graph's own structure rather than from
  re-expanding E(S,S)'s definition — genuinely worth checking on its
  own terms against the corrected target (39), rather than assumed
  independent without checking (the mistake §10 came close to making).
  Not yet carried through.
- The `|H∩C(F_p)|=|C(F_p)|/m+O(√p)` character-sum lemma (§8.7) remains
  a clean, likely-provable side result regardless of what happens to
  the L² idea.
