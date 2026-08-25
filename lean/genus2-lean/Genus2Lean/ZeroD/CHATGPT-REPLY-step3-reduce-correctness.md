# Raw ChatGPT reply — Step 3 math (Reduce's divisor-class correctness)

This is the full, unedited answer to `CHATGPT-PROMPT-step3-reduce-
correctness.md`, kept verbatim for reference. The condensed,
actionable version (mapped onto our actual Lean names/files) is in
`ROADMAP-reduce-divisor-correctness.md` §3a–3e — read that first;
come back here only for the full derivations/justifications it
summarizes.

---

Yes. There is a very clean way to organize the proof, and I think it will map unusually well onto your existing `ordAt` machinery.

The one conceptual correction I would make at the outset is:

> The polynomial phi(x) itself is not generally the principal-divisor witness.
> The natural witness is a function of the form
> h(x,y) = (y - phi(x)) / u_new(x)
> (up to an overall nonzero scalar and sign conventions).
>
> Your N = phi^2 - f is the norm of the numerator (y - phi), and its quotient by the known factors tells you which residual x-coordinates occur.

That is exactly the geometry behind the Cantor reduction step. Cantor's algorithm is explicitly split into composition and reduction, with the reduction step replacing (u,v) by ((f-v^2)/u, -v mod u) in the h=0, odd-characteristic case.

## 1. Start with the geometric picture

Let C: y^2 = f(x), deg f = 5, over K = F_p, p ≠ 2, with f squarefree.

There is one point at infinity, call it δ₀, and ord_{δ₀}(x) = -2, ord_{δ₀}(y) = -5.

So a cubic polynomial phi(x) has pole order 6 at infinity.

Therefore y - phi(x) has pole order 6 at δ₀, generically because the cubic term dominates y:

div(y - phi) = Z(y-phi) - 6δ₀.

The affine zeros of y - phi are exactly the intersection points of the curve y^2=f(x) with the graph y=phi(x).

Now eliminate y: (y-phi)(y+phi) = f - phi^2.

Thus the x-coordinates of those intersection points are the roots of N(x) = phi(x)^2 - f(x) (up to sign).

Since deg phi = 3, deg N = 6. So Bezout here is literally visible as polynomial degree: there are six intersections counting multiplicity.

That is the fundamental fact your Lean proof should exploit.

## 2. The standard genus-2 Cantor reduction identity

Suppose you have a semireduced divisor D_old = P1+P2+Q1+Q2-4δ₀ with Mumford representation (u_old, v_old), where u_old = prod(x-xi) in the completely split picture, and v_old(xi) = yi.

Choose phi satisfying phi(xi) = yi at all four points.

Then u_old | phi^2 - f. Write phi^2 - f = u_old · u_new. Since the left side has degree 6 and u_old has degree 4, deg u_new = 2.

Let its roots be r1,r2, with corresponding curve points Ri = (ri, phi(ri)).

Then div(y - phi) = P1+P2+Q1+Q2+R1+R2 - 6δ₀.

Now define v_new ≡ -phi (mod u_new). The minus sign is crucial.

The Mumford divisor associated to (u_new, v_new) is D_new = R̄1 + R̄2 - 2δ₀, where R̄i = (ri, -phi(ri)) is the hyperelliptic conjugate.

And now comes the beautiful trick: (y - phi(x)) / u_new(x) has:
- zeros at the original four points (Pi, Qi),
- poles at the conjugate residual points (R̄1, R̄2),
- pole of order 2 at infinity.

Why?

At Ri: y - phi(x) = 0 there too, and u_new(x) = 0, so the two zeros cancel.

At R̄i: y = -phi(ri), so y - phi(ri) = -2phi(ri), which is generally nonzero, while u_new(ri) = 0. Hence there is a pole.

At infinity: ord_{δ₀}(y-phi) = -6 and ord_{δ₀}(u_new) = -4, so ord_{δ₀}((y-phi)/u_new) = -6-(-4) = -2.

Therefore: div((y-phi)/u_new) = D_old - D_new.

That is the entire correctness proof of the reduction step.

So, class-theoretically, D_old ~ D_new.

This is the geometric content of Cantor reduction. The standard algorithm consequently returns the unique reduced divisor in the same class.

## 3. This also tells you exactly what ordAt should be applied to

For your Lean development, I would conceptualize the eventual theorem as:

ordAt((y-phi(x))/u_new(x), P) = coeff_P(D_old) - coeff_P(D_new)

for every closed point P.

Or globally: div(h) = D_old - D_new, h = (y-phi)/u_new.

That is much better as the conceptual target than trying to prove directly that the two Mumford pairs represent the same Jacobian point.

You then get equality in Pic^0 immediately because a principal divisor represents zero.

So I would structure the eventual formal proof around three separate facts:

1. u_old | (phi^2 - f).
2. u_new = (phi^2-f)/u_old describes the residual intersection divisor.
3. The rational function h = (y-phi)/u_new has divisor D_old - D_new.

The third is the actual class-preservation theorem.

## 4. Why N = phi^2-f is the right computational object

This is where your N calculation fits beautifully.

The hyperelliptic involution is ι(x,y) = (x,-y).

For g = y - phi(x), its conjugate is ι(g) = -y - phi(x).

Their product is g·ι(g) = phi(x)^2 - y^2 = phi(x)^2 - f(x) = N(x).

So N is exactly the norm N_{K(C)/K(x)}(g).

This explains an otherwise slightly mysterious feature of Cantor arithmetic: N lives in the x-polynomial ring because norms forget whether an intersection point is P or ι(P).

If the known divisor contributes the factor u_old, then N = u_old·u_new.

The remaining factor is exactly the x-projection of the residual intersection divisor.

That is why the quotient polynomial gives you the new u.

And then the sign v_new ≡ -phi (mod u_new) switches the residual points to their hyperelliptic conjugates, which is exactly what turns the geometric relation from D_old + R - 6δ₀ into D_old - D_new.

This is also exactly what the usual Cantor step says: after forming u' = (f-v^2)/u, replace v by -v mod u'.

## 5. Your more general E+Yy formulation

This is particularly relevant to the code you've described.

You apparently aren't always using the literal y-phi(x); instead you have something like g = E(x) + Y(x)y, with norm N(x) = E(x)^2 - f(x)Y(x)^2.

That is completely natural.

The involution sends g = E+Yy to ḡ = E-Yy, so g·ḡ = E^2 - Y^2 y^2 = E^2 - fY^2 = N.

Thus N is again the norm of the actual curve function.

This gives you a very useful slogan for the formalization: N tells you where g or ḡ vanishes; g itself tells you which side of the involution the divisor lives on.

So I would not make the eventual principal-divisor theorem about N itself.

It should be about an element of the function field represented by something of the form E+Yy, possibly divided by an x-only denominator.

The norm calculation is then a supporting lemma that tells you the x-divisor of that function.

## 6. The exact sign issue for your D_old

This is the place where I think you should be particularly careful in translating your actual implementation.

You wrote that your target divisor is D_old = alpha·aClass - [P1] - [P2] + 2[δ₀].

But the elementary Cantor interpolation argument above for phi through P1,P2 proves the corresponding statement for alpha·aClass + [P1] + [P2] - 2[δ₀] unless your implementation has already encoded negation somewhere else.

To subtract Pi, you should ordinarily add its inverse -Pi = [ι(Pi) - δ₀].

On Mumford coordinates, negation is (u,v) ↦ (u,-v).

So if your old divisor really is D_a - [P1] - [P2] + 2δ₀, the interpolation function for the composition stage should geometrically pass through ι(P1), ι(P2), not P1,P2, unless your definitions of E, Y, or the target v_a have already absorbed those signs.

This is probably the single most important thing to check against your current code.

If your phi literally satisfies phi(x(Pi)) = y(Pi), then y-phi has zeros at Pi, not at ι(Pi).

If instead phi(x(Pi)) = -y(Pi), then y-phi vanishes at ι(Pi), which is what subtraction needs.

So the correct informal statement for your code is: determine which points are zeros of the actual curve function g = E+Yy, rather than reading the sign solely from the x-polynomial N.

That's exactly where the E+Yy formulation is preferable to talking only about phi.

## 7. Distinct points P1 ≠ P2

For the distinct-point case, the interpolation condition is simply phi(x1)=y1, phi(x2)=y2, together with the corresponding conditions coming from u_a,v_a.

Geometrically these are ordinary intersection conditions.

If P1≠P2 and both are ordinary affine points, each contributes intersection multiplicity 1 unless the cubic happens to be tangent there.

So you get four prescribed intersection points and two residual intersections.

The resulting divisor calculation is exactly the one above.

The subtle cases are not really about P1≠P2 versus P1=P2 by themselves; they are about intersection multiplicity. Your case split is convenient because doubling forces you to encode multiplicity 2 explicitly.

## 8. Doubling: P1=P2=P

Now suppose the same point occurs twice.

You need the cubic to intersect the curve with multiplicity 2 at P.

For an ordinary affine point P=(x0,y0) with y0≠0, differentiate y^2=f(x).

Locally, 2y·dy/dx = f'(x), so the tangent slope is dy/dx = f'(x0)/(2y0).

Therefore the Hermite interpolation conditions are phi(x0)=y0, and phi'(x0) = f'(x0)/(2y0).

Then y-phi(x) vanishes to order at least 2 at P.

That is the exact geometric meaning of your doubling branch.

So in divisor language you get ord_P(y-phi) ≥ 2, and, provided the second-order contact is exactly two, ord_P(y-phi) = 2.

This is the divisor analogue of the tangent-line construction on an elliptic curve.

## 9. But there is an additional exceptional case: y(P)=0

This is worth calling out explicitly for your Lean development.

If y0=0, then P is a ramification point of the hyperelliptic map.

The formula f'(x0)/(2y0) doesn't make sense.

That isn't a finite-field issue. It's geometric: the tangent at a branch point is vertical, so it is not the graph of a function y=phi(x).

For a squarefree f, f'(x0)≠0, and using a local parameter t=y, one has x-x0 ~ c·t^2.

Hence x-x0 has order 2 at the branch point.

In fact, div(x-x0) = 2P - 2δ₀.

So if your doubling branch permits a Weierstrass point, that case has an especially simple principal-divisor witness: x-x0.

Its divisor immediately proves 2[P]-2[δ₀]=0 in the Jacobian.

So for a completely robust theorem, I would expect three geometric subcases eventually:

1. P1≠P2;
2. P1=P2 and y(P)≠0, Hermite/tangent interpolation;
3. P1=P2 and y(P)=0, ramification/vertical-tangent case.

Your existing P1=P2 split is the right major split, but the second branch may eventually need that internal exceptional case.

## 10. Why nothing here requires an algebraically closed field

This is actually good news for your formalization.

The geometry is often explained over K̄ by saying u(x)=prod(x-xi), and talking about individual points.

But that is only a visualization.

The actual Cantor algorithm is defined over the original field K, using polynomial gcds and quotients. Standard treatments formulate Mumford representations over an arbitrary base field with the appropriate rationality conditions; the finite-field setting is completely standard.

For K=F_p, you can avoid algebraic closure entirely.

Instead of saying "Let R1,R2 be the roots of u_new," say "Let V(u_new, y+phi) be the residual effective divisor cut out by the two functions u_new(x) and y+phi(x)."

Or, in your Dedekind-domain language, work with the prime ideals / places occurring in the factorization.

Then the identity phi^2-f = u_old·u_new is entirely over K[x], and the divisor relation is also defined over K.

The algebraic-closure picture can be used only as intuition.

## 11. What finite-field assumptions are actually being used?

For your K=F_p, you have everything you need.

The important assumptions are: p≠2, and f squarefree, and deg f = 5.

Those give you: the model y^2=f(x) with the usual separable hyperelliptic behavior; the involution y↦-y; a unique point at infinity; genus 2; the usual Mumford representation.

Characteristic 0 is not needed.

Algebraic closure is not needed.

The fact that K is finite is not an obstacle at all.

The only place where the finite-field nature potentially changes the presentation is factorization: u(x) need not split over F_p. But that is a representational issue, not a mathematical obstruction.

## 12. The finite-field-safe replacement for "six intersection points"

This is probably the form you'll eventually want Lean to formalize.

Rather than phi^2-f = c·prod(x-xi) for i=1..6, use the divisor-theoretic statement div_0(y-phi) and the identity of its pushforward to the x-line.

The norm gives N_{K(C)/K(x)}(y-phi) = phi^2-f.

The divisor of this norm on K(x) records the pushforward of the divisor upstairs under π: C→P^1, (x,y)↦x.

That statement is valid over the base field without splitting anything.

So the logical order can be:

phi^2-f = u_old·u_new
⟹ the known divisor is part of the zero divisor of y-phi
⟹ the quotient corresponds to the residual intersection divisor
⟹ changing +phi to -phi in v_new applies the hyperelliptic involution
⟹ h = (y-phi)/u_new has divisor D_old - D_new.

That's the entire reduction proof in a form that doesn't mention a single algebraic closure.

## 13. Where your u_a, P1, P2, and N fit

Suppose the semi-reduced divisor you're trying to reduce is D_old = D_a + Q1+Q2 - 4δ₀, where D_a is represented by (u_a,v_a).

Then the interpolation conditions are schematically phi ≡ v_a (mod u_a), plus phi(x(Q1))=y(Q1), phi(x(Q2))=y(Q2).

Hence u_a(x)·(x-x1)(x-x2) | phi(x)^2-f(x).

Call the known factor A(x) = u_a(x)(x-x1)(x-x2).

Then N(x) = phi^2-f = A(x)·u(x) for the new quadratic u.

This is precisely the algebra your code is doing.

But the crucial divisor witness is not N. It is h = (y-phi)/u.

Then div(h) = D_old - D_new provided the sign conventions for Qi and v_a are aligned as above.

So I would strongly recommend treating N=A·u as the residual-intersection lemma, and div(h)=D_old-D_new as the class-preservation lemma.

That separation will make the Lean proof much less tangled.

## 14. One more subtlety: overlapping supports

There is one place where the pleasant "divide by u_new, and everything cancels nicely" story can silently fail if stated too naively.

If the residual divisor shares support with the old divisor, then u_old and u_new are not coprime, and you have to account for multiplicities in the valuations.

That is exactly why general Cantor composition uses gcds before the reduction step. The standard algorithm first computes gcd information among u1,u2 and v1+v2, forms the semireduced composition, and only then performs the repeated reduction step.

So for your proof, I would not build in a blanket assumption "all six points are distinct."

Instead prove statements with valuation multiplicities. Then the distinct-point situation becomes the easy special case where every relevant valuation is 0 or 1.

This is particularly valuable for Lean because it keeps the theorem correct in exactly the degenerate cases that tend to explode later.

## 15. The proof skeleton I'd use

Conceptually, I think your eventual formalization wants these lemmas, in this order:

**Intersection/norm lemma**: For the chosen interpolation data, N = phi^2-f is divisible by the known x-factor A.

**Residual polynomial lemma**: Define u = N/A. Then u is the x-polynomial of the residual intersection divisor.

**Residual Mumford lemma**: Define v ≡ -phi (mod u). Then (u,v) represents the conjugate residual divisor.

**Principal witness lemma**: Define h = (y-phi)/u. Then for every point/place P, ord_P(h) = coeff_P(D_old) - coeff_P(D_new). Hence div(h) = D_old - D_new.

**Class-preservation lemma**: Therefore [D_old]=[D_new] in Pic^0(C).

**Uniqueness/reducedness lemma**: Since deg u ≤ 2 = g and the pair is reduced, it is the unique reduced representative of that class.

That last step is separate from the Cantor geometry itself. Your already-proved Mumford congruence gives you part of it; you still need the reducedness/uniqueness machinery to conclude "this is the representative," rather than merely "this represents an equal class."

## The punchline

phi^2 - f = N = u_old · u_new (known divisor × residual x-projection)

h = (y-phi)/u_new

div(h) = D_old - D_new.

Your N computation is therefore not itself the proof of equality of Jacobian classes. It is the elimination step that identifies the residual support. The actual equality of classes comes from the divisor of h.

And for your specific target alpha·aClass - [P1] - [P2] + 2[δ₀], the thing I would check first against your implementation is the sign convention: the interpolation function must vanish at the points representing the summands you are actually adding, so subtraction of Pi normally means interpolating through ι(Pi), or equivalently arranging your E+Yy so that its zero is at ι(Pi). That is the most likely place for a formally valid-looking N-calculation to end up proving the wrong divisor class.

Cantor's original paper is the 1987 "Computing in the Jacobian of a hyperelliptic curve"; modern treatments explicitly describe the same composition/reduction structure.

The really nice part is that this meshes almost perfectly with the existing ordAt setup: the central theorem you ultimately want is not "the Mumford pairs are equal," but "there exists this very explicit function-field element h whose ordAt divisor is exactly the old-minus-new divisor." Once that is proved, the Jacobian equality is basically bookkeeping.


claude:I'm formalizing Cantor reduction correctness for genus-2 hyperelliptic
curves in Lean 4 / Mathlib4, over a finite field F\_p (p ≠ 2), no
algebraic closure anywhere. You previously helped me work out the math
(three-lemma skeleton: residual-intersection, residual-Mumford,
principal-witness). I've now confirmed the first lemma is already
proved in my codebase. I need help turning the third lemma (the actual
class-preservation argument) into a real Lean proof against my actual
`ordAt` API, which I'll paste below.

**Goal.** Prove `div(h) = D_old - D_new` where `h = (y - phi(x)) / u_new(x)`, by showing, for every point `P : H.Point`,
`ordAt P h = coeff_P(D_old) - coeff_P(D_new)`, then assembling that
into class equality in the Jacobian via a principal divisor being 0 in
the quotient.

**My actual** **`ordAt`** **API (already proved, from** **`PrincipalDivisors.lean`****
/** **`RiemannRochGenus2.lean`** **/** **`HyperellipticClassProof.lean`****):**

```
noncomputable def ordAt [IsDedekindDomain (CoordinateRing H)]
    (P : H.Point) (A B : k[X]) : ℤ := ...
-- ordAt P A B is the valuation, at the place P, of the CoordinateRing
-- element represented by the pair (A, B) (i.e. A(x) + B(x)·y).

theorem ordAt_toPair_mul_of_ne_zero'
    (P : H.Point) (h_bot : pointIdeal P ≠ ⊥) (A B A' B' A₃ B₃ : k[X])
    (hAB : toPair H A B ≠ 0) (hA'B' : toPair H A' B' ≠ 0)
    (hA₃ : toPair H A₃ B₃ = toPair H A B * toPair H A' B') :
    ordAt P A₃ B₃ = ordAt P A B + ordAt P A' B'
-- additivity of ordAt under multiplication, stated at the (A,B)-pair level

theorem ordAt_linX_eq_zero_of_ne [IsDedekindDomain (CoordinateRing H)]
    (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) (hne : Q.X ≠ a) :
    ordAt Q (linX a) 0 = 0
-- ordAt of (X - a) at a point Q not lying over a is 0

theorem ordAt_linX_eq_one_of_unramified_dvd [IsDedekindDomain (CoordinateRing H)]
    (a : k) (Q : H.Point) (heq : Q.X = a) :
    pointIdeal Q ∣ Ideal.span ({toPair H (linX a) 0} : Set (CoordinateRing H))
-- Q lies over a ⟹ pointIdeal Q divides the ideal generated by (X - a)

theorem ordAt_linX_eq [IsDedekindDomain (CoordinateRing H)] [DecidableEq k]
    (a : k) (Q : H.Point) (h_bot : pointIdeal Q ≠ ⊥) :
    ordAt Q (linX a) 0 = if Q.X = a then (if Q.Y = 0 then 2 else 1) else 0
-- the fully assembled case split: ordAt of (X - a) at Q, covering
-- not-a-root / unramified-root / ramified(Weierstrass)-root

theorem ordAt_sub_ordAt_eq_of_polePairToFraction_eq (P : H.Point)
    (A B A' B' : k[X]) (... ) : ...
-- relates ordAt of two pairs representing the same function-field
-- fraction; exact hypotheses in the file, can paste more if needed

theorem ordAt_add_ge_min ... 
-- valuation inequality for sums, standard ultrametric-style bound

def ordAtFrac (P : H.Point) (A B A' B' : k[X]) : ℤ := ...
-- ordAt of a fraction A+By over A'+B'y, i.e. ordAt(num) - ordAt(denom)

theorem ordAt_eq_rootMultiplicity_unramified (hchar : (2 : k) ≠ 0)
    (a : k) (Q : H.Point) (...) : ...
theorem ordAt_eq_rootMultiplicity_ramified (hsf : Squarefree H.f)
    (a : k) (Q : H.Point) (...) : ...
-- ordAt of a general polynomial-in-x factor at Q, in terms of that
-- polynomial's root multiplicity at Q.X, split unramified/ramified

```

`H.Point` is `{X Y : k // Y^2 = H.f.eval X}`-shaped (curve point).
`toPair H A B` builds the `CoordinateRing H` element `A(x) + B(x)·y`.
`pointIdeal P` is the maximal ideal at `P`. `divToPair H A B S` builds
a `Divisor H` (formal sum) supported on the finite point set `S`, using
`ordAt · A B` as the coefficient function. `Divisor0 H` is the
degree-0 divisors. `toJacobian : Divisor0 H →+ Jacobian H D` is the
quotient map (an `AddMonoidHom`, so a principal divisor — anything in
`AddMonoidHom.range` of the map from principal divisors — maps to 0
automatically once membership is shown).

My target theorem's statement (already typechecks with a `sorry` body,
this is what I need to prove):

```
theorem reducedClass_eq_of_isReduction'
    ... (sa : SampleTargetFromAlpha p H D aClass δ₀) ...
    (hr : isReduction' sa c0 c1 c2 c3 c4 ua0 ua1 va0 va1 hcur hgcd hcurT hgcdT)
    (S : Finset H.Point)
    (hsupp : ∀ P, P ∉ S → ordAt P
      (X ^ 2 + C sa.toSampleTarget.u1 * X + C sa.toSampleTarget.u0)
      (C sa.toSampleTarget.v1 * X + C sa.toSampleTarget.v0) = 0)
    (hmem : divToPair H
      (X ^ 2 + C sa.toSampleTarget.u1 * X + C sa.toSampleTarget.u0)
      (C sa.toSampleTarget.v1 * X + C sa.toSampleTarget.v0) S ∈ Divisor0 H) :
    sa.reducedClass = toJacobian D
      ⟨divToPair H
        (X ^ 2 + C sa.toSampleTarget.u1 * X + C sa.toSampleTarget.u0)
        (C sa.toSampleTarget.v1 * X + C sa.toSampleTarget.v0) S, hmem⟩ := by
  sorry

```

**What I need from you.** Not the whole proof at once — walk me
through how to structure the Lean proof of the principal-witness
lemma (`ordAt P h = coeff_P(D_old) - coeff_P(D_new)` for all `P`,
where `h`'s numerator/denominator are represented as `(A,B)` pairs via
`toPair`/`divToPair` as above) using this specific API:

1. How do I represent `h = (y - phi(x)) / u_new(x)` — or more precisely `g/u_new` where `g = E(x) + Y(x)·y` — as a fraction in terms of `ordAtFrac` or via `ordAt_sub_ordAt_eq_of_polePairToFraction_eq`, given I only have `ordAt` defined on `(A,B)` pairs representing numerators, not a native "divide two CoordinateRing elements" operation?
2. For the case-split at each point P (P is one of the four known points / a residual root / a conjugate residual root / δ₀ / none of the above), which combination of `ordAt_linX_eq`, `ordAt_toPair_mul_of_ne_zero'`, and `ordAt_eq_rootMultiplicity_*` actually computes the needed valuation, and in what order should I chain them?
3. Is there a cleaner way to avoid re-deriving the point-at-infinity (`δ₀`) pole-order bookkeeping from scratch, given my `ordAt` is defined via `pointIdeal`/`IsDedekindDomain.HeightOneSpectrum` at finite points — does `δ₀` even have a `pointIdeal` in this setup, or does infinity need separate handling (e.g. via `natDegree` directly rather than `ordAt`)?
4. Given the "don't assume distinct roots" robustness note from before — should the Lean proof case-split on `Finset` membership / multiplicity directly, or is there a cleaner way using the `S` parameter (the explicit finite point set) already threaded through my theorem statement above?

I'd like this broken into the smallest provable chunks possible, since
my convention is many small named lemmas rather than one large proof
attempt.

gpt:

Yes — and looking at the API you pasted changes the proof strategy in a useful way. I would **not** attack the final `∀ P, ...` theorem by immediately splitting into five geometric cases. Your API is actually set up to let you factor the argument into about 6–10 tiny valuation lemmas, with the only genuinely geometric lemma being “what is the valuation of the interpolation numerator (g) at one of its zeroes?”

There is also one important structural issue I want to flag up front: your `S : Finset H.Point` representation only sees (F_p)-rational affine points. A general degree-2 Mumford polynomial (u_{\rm new}) can be irreducible over (F_p), in which case its residual divisor is a degree-2 closed point, not two elements of `H.Point`. If your current theorem assumes the support splits over (F_p), that's fine; otherwise the eventual fully general theorem needs to be phrased in terms of height-one primes/closed points rather than `H.Point`. More on that below.

## 1. First: represent (h) with `ordAtFrac`

For your specific denominator,

[
u_{\rm new}(x)=x^2+c_1x+c_0,
]

the numerator is

[
g(x,y)=E(x)+Y(x)y.
]

So the clean representation is simply

```text
ordAtFrac P E Y u_new 0
```

because this means

[
\operatorname{ordAtFrac}*P(g/u*{\rm new})
=========================================

## \operatorname{ordAt}_P(E,Y)

\operatorname{ordAt}*P(u*{\rm new},0).
]

So your first tiny lemma should just be the definitional bridge:

[
\boxed{
\operatorname{ordAtFrac}(P,E,Y,U,0)
===================================

\operatorname{ordAt}(P,E,Y)-\operatorname{ordAt}(P,U,0).
}
]

If `ordAtFrac` is literally defined this way, this should be essentially `rfl`/unfolding.

That is preferable to `ordAt_sub_ordAt_eq_of_polePairToFraction_eq` as the primary route.

I would use the latter only when you need to prove that two *different pairs* represent the same fraction. For example, if your actual code constructs (g/U) in a less direct pair form and you want to replace it by `(E,Y,U,0)`, then use the fraction-equality lemma as the bridge.

So conceptually:

[
\boxed{\text{First normalize every occurrence of }h\text{ to }\operatorname{ordAt}(g)-\operatorname{ordAt}(U).}
]

That gets the rest of the proof into ordinary valuation arithmetic.

---

# 2. Don't compute `ordAt g` from scratch point-by-point if you can avoid it

This is the biggest simplification I'd make.

Let

[
\bar g=E-Yy
]

be the hyperelliptic conjugate of (g=E+Yy). Then in the coordinate ring,

[
g\bar g
=======

# E^2-fY^2

N.
]

So prove the little algebra lemma

[
\boxed{
\operatorname{toPair}(H,E,Y)
\cdot
\operatorname{toPair}(H,E,-Y)
=============================

\operatorname{toPair}(H,N,0).
}
]

Then your already-proved theorem

```text
ordAt_toPair_mul_of_ne_zero'
```

gives

[
\boxed{
\operatorname{ordAt}_P(g)
+
\operatorname{ordAt}_P(\bar g)
==============================

\operatorname{ordAt}_P(N,0).
}
]

That turns the valuation of the non-polynomial-in-(x) object (g) into the valuation of the ordinary polynomial (N(x)), which is exactly what your `ordAt_eq_rootMultiplicity_*` lemmas understand.

This is the central trick I would exploit in Lean.

---

# 3. The local lemma you actually need for the numerator

At an ordinary point (P=(a,b)) with (b\neq0), there are two points above (x=a):

[
P=(a,b),\qquad \iota(P)=(a,-b).
]

Suppose (g(P)=0).

Then automatically

[
\bar g(P)\neq0
]

provided (b\neq0) and you aren't in a degenerate situation where both (g) and (\bar g) vanish.

Indeed,

[
g(P)=E(a)+Y(a)b=0,
]

whereas

[
\bar g(P)=E(a)-Y(a)b=-2Y(a)b.
]

So if (Y(a)\neq0),

[
\bar g(P)\neq0
]

because (2b\neq0).

That means the conjugate factor has valuation zero:

[
\operatorname{ordAt}_P(\bar g)=0.
]

Then norm multiplicativity gives

[
\boxed{
\operatorname{ordAt}_P(g)
=========================

\operatorname{ordAt}_P(N,0).
}
]

Now your existing

```text
ordAt_eq_rootMultiplicity_unramified
```

can compute the right-hand side.

So I would create this as a named lemma, something like conceptually:

```text
ordAt_g_of_g_eval_eq_zero_of_unramified
```

whose proof is:

1. prove `g * gbar = N`;
2. apply `ordAt_toPair_mul_of_ne_zero'`;
3. prove `ordAt P gbar = 0` from `gbar(P) ≠ 0`;
4. conclude `ordAt P g = ordAt P N`;
5. rewrite `ordAt P N` using `ordAt_eq_rootMultiplicity_unramified`.

That is much cleaner than trying to reason directly about the local expansion of (E+Yy).

---

# 4. You will probably want one tiny “nonzero residue ⇒ valuation zero” lemma

Your listed API doesn't explicitly include one.

I suspect you either already have one under a different name, or it is buried in the proof of `ordAt`.

You want something morally like:

[
g(P)\neq0
\quad\Longrightarrow\quad
\operatorname{ordAt}_P(g)=0.
]

More algebraically, if the image of the coordinate-ring element in the residue field

[
\kappa(P)
=========

R/\operatorname{pointIdeal}(P)
]

is nonzero, then that element is a unit in the local DVR, hence valuation zero.

For Lean, this is worth extracting as a tiny reusable lemma. It will immediately give you:

[
g(P)\neq0\implies\operatorname{ordAt}_P g=0,
]

and similarly for (\bar g).

I would expect to use it constantly.

---

# 5. Then the numerator/denominator calculation becomes almost mechanical

Set

[
U=u_{\rm new}.
]

Your target is

[
\operatorname{ordAt}(h)
=======================

\operatorname{ordAt}(g)-\operatorname{ordAt}(U).
]

Suppose we're at a residual point (R) where (g(R)=0) and (U(R)=0).

Then:

[
\operatorname{ordAt}(g)
=======================

\operatorname{ordAt}(N),
]

and from

[
N=A,U
]

where (A) is your known anchor factor,

[
\operatorname{ordAt}(N)
=======================

\operatorname{ordAt}(A)
+
\operatorname{ordAt}(U).
]

Therefore

[
\operatorname{ordAt}(h)
=======================

\operatorname{ordAt}(A).
]

That's exactly the cancellation you want.

Notice what happened: **you didn't need to directly determine the order of (g) and subtract 1.**

You use the factorization

[
N=A,U
]

to make the denominator valuation cancel automatically.

This is very attractive for Lean.

---

# 6. In fact, the cleanest formal route is probably to factor the whole divisor computation

Suppose

[
A(x)=u_a(x)(x-x_1)(x-x_2)
]

is the known factor, and

[
N=A,U.
]

Suppose the prescribed interpolation makes (g) vanish along the old effective divisor (D_{\rm old}^{+}) and the residual effective divisor (R).

Then conceptually you have

[
\operatorname{div}(g)
=====================

D_{\rm old}^{+}+R-6\delta_0
]

and

[
\operatorname{div}(U)
=====================

R+\iota(R)-4\delta_0.
]

Subtracting gives

[
\operatorname{div}(g/U)
=======================

D_{\rm old}^{+}-\iota(R)-2\delta_0.
]

The right-hand side is exactly

[
D_{\rm old}-D_{\rm new}
]

once the sign convention for the Mumford (v_{\rm new}) is fixed.

So the proof doesn't fundamentally need to know whether a point is “one of the six points” at every stage. It needs the two divisor identities.

That suggests a useful hierarchy:

```text
local valuation of g at an ordinary zero
        ↓
valuation of N = A * U
        ↓
valuation of g/U
        ↓
pointwise coefficient identity
        ↓
divisor equality
        ↓
principal divisor / Jacobian equality
```

---

# 7. How `ordAt_linX_eq` fits in

For the denominator

[
U=(X-r_1)(X-r_2)
]

when it splits, `ordAt_linX_eq` is perfect.

For each (P),

[
\operatorname{ordAt}_P(X-r)
===========================

\begin{cases}
0,&P.X\neq r,\
1,&P.X=r,\ P.Y\neq0,\
2,&P.X=r,\ P.Y=0.
\end{cases}
]

Then multiplicativity gives

[
\operatorname{ordAt}_P(U)
=========================

\operatorname{ordAt}_P(X-r_1)
+
\operatorname{ordAt}_P(X-r_2).
]

So if you *are* working in the split-over-(F_p) situation, this is the easiest way to prove the denominator coefficient formula.

But if (U) is not split over (F_p), don't factor it into linear terms. Use your

```text
ordAt_eq_rootMultiplicity_unramified
ordAt_eq_rootMultiplicity_ramified
```

directly on (U).

That gives you a much more robust theorem:

[
\boxed{
\operatorname{ordAt}_P(U,0)
===========================

\text{root multiplicity of }U\text{ at }P.X,
}
]

with the ramified factor of (2) automatically handled.

So I'd actually make the root-multiplicity lemma the *main* denominator theorem, and make `ordAt_linX_eq` a corollary useful in the split case.

---

# 8. Don't case-split on “is (P) a residual root?” if root multiplicity can do it for you

This answers your second question pretty strongly.

I would avoid a giant proof like:

```text
by_cases P = P1
by_cases P = P2
by_cases P = R1
by_cases P = R2
...
```

That will become horrible when points collide.

Instead, case-split on the **valuation source**, not on geometric identity.

For an ordinary point (P), the useful logical cases are:

1. (g(P)\neq0);
2. (g(P)=0).

Inside case 2, distinguish whether (P) is ramified.

Then the norm identity converts case 2 into a root-multiplicity calculation for (N).

Likewise the denominator is handled entirely by the root-multiplicity theorem for (U).

This means collisions are absorbed automatically into multiplicities.

That's exactly what you want.

---

# 9. The `S` parameter is useful, but don't use it to encode multiplicity

Your `divToPair ... S` construction is actually a nice abstraction.

You want `S` to be a **support set**, not a multiplicity set.

The coefficient at (P) is already

[
\operatorname{ordAt}_P(u,v),
]

so if a point occurs with multiplicity (2), it should still occur just once in `S`; its coefficient will be (2).

Therefore the clean support theorem is:

[
P\notin S
\implies
\operatorname{ordAt}_P(u,v)=0.
]

That's exactly what your

```text
hsupp :
  ∀ P, P ∉ S →
    ordAt P ... ... = 0
```

already says.

So I would prove your final equality by using:

[
P\notin S
\Rightarrow
\operatorname{coeff}*P(D*{\rm new})=0.
]

And inside (S), calculate the coefficient from `ordAt`.

But here's an even cleaner option: if your definition of `divToPair` lets you characterize the coefficient directly, prove one lemma of the form

[
\boxed{
\operatorname{coeff}_P(\operatorname{divToPair}(A,B,S))
=======================================================

\begin{cases}
\operatorname{ordAt}_P(A,B),&P\in S,\
0,&P\notin S.
\end{cases}}
]

Then all later divisor calculations become rewriting rather than Finset gymnastics.

---

# 10. There is an important issue with `S : Finset H.Point`

This deserves special emphasis because you're deliberately avoiding algebraic closure.

A quadratic (U\in F_p[x]) can be irreducible.

For example,

[
U(x)=x^2+1
]

may have no root in (F_p).

But it still corresponds to a degree-2 effective divisor on (C).

There are then no two `H.Point`s (R_1,R_2) you can put into `S`.

So a theorem whose entire new divisor is

```text
divToPair ... S
```

with `S : Finset H.Point`
is not a representation of arbitrary genus-2 Mumford reduction over (F_p).

It represents the split/rational-support special case.

That's not necessarily a problem. But it needs to be explicit.

For the fully general finite-field theorem, the natural support object is something like height-one primes of the coordinate ring, exactly the machinery your `ordAt` was built from.

And this is actually mathematically nicer for the proof you're working toward: an irreducible (u_{\rm new}) is just a prime divisor of degree (2), and `ordAt` is fundamentally a valuation at a prime ideal anyway.

---

# 11. Infinity: I would not try to force `δ₀` into this `ordAt`

This is the other major architectural point.

Your

```text
P : H.Point
pointIdeal P
```

is clearly describing an affine rational point.

The unique point at infinity is not an element of the affine coordinate ring, so it does **not** have a corresponding maximal ideal of the same form.

Therefore I would expect infinity to require a separate valuation:

[
\operatorname{ord}_{\delta_0}.
]

And I would absolutely make that separate rather than trying to fake it through `pointIdeal`.

For your model (\deg f=5),

[
\operatorname{ord}*{\delta_0}(x)=-2,
\qquad
\operatorname{ord}*{\delta_0}(y)=-5.
]

For a polynomial (A(x)),

[
\operatorname{ord}_{\delta_0}(A(x))
===================================

-2\deg A
]

provided (A\neq0).

For

[
g=E(x)+Y(x)y,
]

you can compute the pole order from

[
\max(2\deg E,;2\deg Y+5)
]

provided the leading terms don't cancel.

In your actual cubic-interpolation situation, (E) and (Y) will presumably have controlled degrees, so this should be a finite collection of degree lemmas.

But there is an even nicer escape hatch for the *final* divisor equality.

---

# 12. You may be able to avoid proving the infinity coefficient directly

Suppose you prove

[
\operatorname{coeff}*P(D*{\rm old}-D_{\rm new})=0
]

for every finite affine point (P).

Then the difference is supported entirely at infinity.

If you also know

[
\deg(D_{\rm old}-D_{\rm new})=0,
]

the only divisor supported at a single point and having degree zero is zero.

So:

[
\boxed{
\text{finite coefficients agree}
+
\text{degree zero}
\Longrightarrow
D_{\rm old}=D_{\rm new}.
}
]

That could save you a *lot* of Lean pain.

You still need some theorem that says the degree of the difference is zero, but you may already have this in `Divisor0`.

Then the entire principal-witness theorem can be proved entirely with affine `ordAt`, followed by one degree argument for infinity.

I would strongly prefer this over introducing an infinity valuation into this particular theorem unless you actually need infinity valuations elsewhere.

---

# 13. The smallest useful lemma stack

If I were building this file, I'd aim for roughly this sequence.

First:

[
\operatorname{ordAtFrac}(P,E,Y,U,0)
===================================

\operatorname{ordAt}(P,E,Y)-\operatorname{ordAt}(P,U,0).
]

Second, the norm identity:

[
(E+Yy)(E-Yy)=E^2-fY^2.
]

Third:

[
\operatorname{ordAt}_P(g)+\operatorname{ordAt}_P(\bar g)
========================================================

\operatorname{ordAt}_P(N).
]

Fourth, residue-nonzero implies valuation zero:

[
g(P)\neq0\Rightarrow\operatorname{ordAt}_P(g)=0.
]

Fifth, ordinary zero of (g):

[
P.Y\neq0,\quad g(P)=0
\Rightarrow
\operatorname{ordAt}_P(g)=\operatorname{ordAt}_P(N).
]

Sixth, convert `ordAt N` to root multiplicity using your existing theorem.

Seventh, prove the factorization

[
N=A,U
]

at the pair level and derive

[
\operatorname{ordAt}_P(N)
=========================

\operatorname{ordAt}_P(A)
+
\operatorname{ordAt}_P(U).
]

Eighth:

[
\operatorname{ordAt}_P(h)
=========================

\operatorname{ordAt}_P(A)
]

at a residual point.

Ninth, package the old/new coefficients and show

[
\operatorname{coeff}*P(D*{\rm old})-\operatorname{coeff}*P(D*{\rm new})
=======================================================================

\operatorname{ordAt}_P(A)
]

with whatever your exact sign convention is.

Then the `∀ P` theorem becomes almost entirely `rw`/`linarith`-style valuation bookkeeping.

---

# 14. The one place where doubling really needs a different lemma

For (P_1\neq P_2), the argument above works with ordinary simple zeros.

For (P_1=P_2=P), you want

[
\operatorname{ord}_P(g)=2
]

in the usual unramified tangent case.

The norm route is actually still excellent:

if (g(P)=0) and (\bar g(P)\neq0), then

[
\operatorname{ord}_P(g)
=======================

\operatorname{ord}_P(N).
]

Hermite interpolation gives

[
N=(x-x(P))^2\cdot(\text{something nonzero at }P)
]

in the unramified case, so your root-multiplicity lemma gives

[
\operatorname{ord}_P(N)=2.
]

Therefore

[
\operatorname{ord}_P(g)=2.
]

So you do **not** need a bespoke local-parameter proof of “tangency implies order two” inside the principal-witness theorem. The existing root-multiplicity machinery can carry it.

That's a very nice fit with your existing API.

The ramified (Y=0) case is different because (P=\iota(P)), so you lose the argument that (\bar g(P)\neq0). That case needs its own tiny lemma. I would isolate it rather than contaminate the main proof.

---

# 15. So the actual pointwise proof should look like this conceptually

For finite (P):

[
\begin{aligned}
\operatorname{ordAtFrac}(P,E,Y,U,0)
&=
\operatorname{ordAt}_P(g)-\operatorname{ordAt}_P(U)\
&=
\bigl(\operatorname{ordAt}_P(N)-\operatorname{ordAt}_P(\bar g)\bigr)
-\operatorname{ordAt}_P(U)\
&=
\operatorname{ordAt}_P(A)
+\operatorname{ordAt}_P(U)
-\operatorname{ordAt}_P(\bar g)
-\operatorname{ordAt}_P(U).
\end{aligned}
]

So

[
\boxed{
\operatorname{ordAtFrac}(P,g/U)
===============================

## \operatorname{ordAt}_P(A)

\operatorname{ordAt}_P(\bar g).
}
]

Now the geometry says:

* at an old point, (g) vanishes and (\bar g) doesn't, so this gives the old coefficient;
* at the “opposite” residual point, (\bar g) vanishes instead, so this gives the negative new coefficient;
* elsewhere neither contributes.

That is a much cleaner pointwise identity than trying to separately compute numerator and denominator at five classes of points.

And it explains why the hyperelliptic involution is so central to the reduction proof.

---

# 16. The final Jacobian step should be downstream, not mixed into this

Once you've got

[
\operatorname{div}(h)=D_{\rm old}-D_{\rm new},
]

don't immediately start wrestling with `toJacobian`.

Make a separate theorem:

[
D_{\rm old}-D_{\rm new}\in\operatorname{PrincipalDivisors}(H)
]

using (h).

Then separately:

[
\operatorname{toJacobian}(D_{\rm old}-D_{\rm new})=0.
]

Then because `toJacobian` is additive,

[
[D_{\rm old}]=[D_{\rm new}].
]

That separation will make the eventual `reducedClass_eq_of_isReduction'` theorem vastly easier to read.

In other words, I would make the main principal-divisor theorem completely ignorant of `aClass`, `SampleTargetFromAlpha`, `hr`, `sa.reducedClass`, etc. Those should only appear in the final assembly theorem.

---

## One thing I'd check before writing any Lean

The next useful piece of your codebase to inspect is the exact definition/theorems around `divToPair`, especially:

```text
coeff_P (divToPair H A B S)
```

and the definition of `Divisor H` itself.

That will determine whether we can make the pointwise theorem almost literally:

[
\operatorname{coeff}*P(D*{\rm old})
-----------------------------------

# \operatorname{coeff}*P(D*{\rm new})

\operatorname{ordAtFrac}(P,E,Y,U,0),
]

or whether there is one intermediate `if P ∈ S then ... else ...` rewrite we need.

And I'd also want to see the exact hypotheses of `ordAt_eq_rootMultiplicity_unramified` and `..._ramified`; those two lemmas are probably the workhorses that let us avoid a huge amount of local algebra.
