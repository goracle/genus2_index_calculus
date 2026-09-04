# Raw ChatGPT reply — response to CHATGPT-PROMPT-step3-C-A-T-principal.md

Yes. With the facts exactly as you state them, there is a genuine mathematical gap, and I think we can say rather precisely what it is.

The important point is that the desired divisor class is the class of a **subtraction**,

$$
(C-2\delta_0)-(A-2\delta_0),
$$

whereas your proved identity

$$
\operatorname{div}_{\rm aff}(g)=A+C+T
$$

is an interpolation identity with \(A\) and \(C\) entering with the **same sign**. A finite sum of pole-matched ratios cannot magically change that class.

There is also a more serious warning: under the standard projective function-field interpretation, your stated affine divisor and stated infinity order for \(g\) cannot simultaneously be the complete divisor data of a nonzero rational function. I will come back to that, because it is actually a useful diagnostic.

### 1. What the pole-matched generators can and cannot do

A generator has the form

$$
\operatorname{div}_{\rm aff}(h_1)-\operatorname{div}_{\rm aff}(h_2),
\qquad
\operatorname{ord}_\infty(h_1)=\operatorname{ord}_\infty(h_2).
$$

Globally, its infinity contribution cancels, so it is an honest degree-zero principal divisor whose affine part is exactly the recorded difference.

Finite sums therefore give divisors of the form

$$
\sum_i\bigl(\operatorname{div}_{\rm aff}(h_i)-\operatorname{div}_{\rm aff}(k_i)\bigr)
$$

with matching pole orders termwise. In particular, `PrincSub` is a subgroup of genuinely principal divisor classes, but only those principal divisors whose infinity contribution can be represented by this balanced decomposition.

The linear-factor trick

$$
\frac{x-a}{x-b}
$$

is especially limited. Both numerator and denominator have pole order \(2\) at infinity, and its affine divisor is

$$
\bigl([P_a]+[\iota P_a]\bigr)
-
\bigl([P_b]+[\iota P_b]\bigr).
$$

But in the Jacobian every hyperelliptic fiber satisfies

$$
[P_a]+[\iota P_a]-2[\infty]\sim0.
$$

So these linear bridges generate only relations between fibers that are already Jacobian-trivial. They cannot manufacture a nontrivial relation such as

$$
[C-2\infty]-[A-2\infty]-[T-2\infty].
$$

That is exactly why trying to "repair" the sign pattern using a pile of \(x-a\) ratios is doomed unless the target relation is already true for some additional reason.

So the answer to your question (1) is:

**There is no generic finite collection of linear-factor bridges that will turn the known `A+C+T` relation into `C-A-T+2δ₀`.** Those bridges live in the hyperelliptic-fiber subgroup, which is trivial in the Jacobian.

More generally, a decomposition into matched-pole ratios exists only if the target divisor is already known to be the affine part of a principal divisor in your restricted sense. The existence of such a decomposition is not a formal consequence of `div_aff(g)=A+C+T`.

### 2. The exact extra fact you need

Your target

$$
C-A-T+2[\delta_0]\in\mathrm{PrincSub}
$$

is equivalent, at the Jacobian level, to

$$
[C-2[\delta_0]]
=
[A-2[\delta_0]]
+
[T-2[\delta_0]].
$$

That is precisely the Cantor-correctness assertion for the operation encoded by the theorem.

The natural function-field witness for that statement is **not** your currently known \(g\). It should be a function whose zero divisor encodes

$$
C + (-A) + (\text{output})
$$

rather than

$$
C + A + T.
$$

Here \(-A\) means the hyperelliptic inverse of the two-point divisor \(A\):

$$
-A=[\iota P_1]+[\iota P_2]-2[\infty].
$$

For the K=4→K=2 Cantor step, the classical interpolation function is constructed so that, schematically,

$$
\operatorname{div}(h)
=
C+\iota(A)+D_{\rm res}-6[\infty],
$$

where \(D_{\rm res}\) is the degree-2 residual divisor. Then

$$
[C-2\infty]-[A-2\infty]
=
-[D_{\rm res}-2\infty].
$$

If your final Mumford representative \(T\) is the inverse of that residual divisor,

$$
T=-D_{\rm res},
$$

then this becomes exactly

$$
[C-2\infty]-[A-2\infty]
=
[T-2\infty].
$$

Equivalently,

$$
C-A-T+2[\infty]\sim0.
$$

That is exactly your target.

So the missing theorem should have roughly this mathematical content:

> The polynomial/function produced by the subtraction version of the Cantor interpolation construction has divisor \(C+\iota(A)-D_T-6\infty\), where \(D_T\) is the residual degree-2 divisor, and \(T=-D_T\).

Once you have that, the Jacobian identity is immediate.

And this is importantly different from proving another consequence of your existing `g`.

### 3. In fact, your current `g` appears to have the wrong orientation for the theorem

The standard Cantor interpolation picture is worth writing explicitly.

Suppose \(D_1,D_2\) are degree-2 Mumford divisors. Construct \(v\) satisfying

$$
v\equiv v_1\pmod{u_1},
\qquad
v\equiv v_2\pmod{u_2},
$$

and let

$$
u_3=\frac{f-v^2}{u_1u_2}.
$$

Then the function

$$
h=y-v(x)
$$

vanishes at the two points of \(D_1\), the two points of \(D_2\), and the two residual points \(D_3\). Thus, globally,

$$
\operatorname{div}(h)
=
D_1+D_2+D_3-6[\infty].
$$

Consequently,

$$
[D_1-2\infty]+[D_2-2\infty]
=
-[D_3-2\infty].
$$

The reduced Mumford output is represented by \(-D_3\), i.e. by changing \(v\) to \(-v\) modulo \(u_3\).

That is the fundamental correctness identity.

For your theorem, however, the desired operation is

$$
C-A.
$$

So you need to feed **\(-A\)** into the Cantor addition, not \(A\):

$$
C+(-A).
$$

The corresponding interpolation divisor is therefore of the shape

$$
C+\iota(A)+D_3-6\infty,
$$

and the final output \(T=-D_3\) gives exactly

$$
C-A=T
$$

in the normalized Jacobian.

This makes me think the biggest issue is not "how do we decompose `C-A-T+2δ₀` into clever ratios?" It is:

**your present `g` witnesses an addition relation involving \(A+C\), while the theorem requires the subtraction relation \(C-A\).**

That is a genuine orientation mismatch, unless `A` or `T` has already been conjugated somewhere in the definitions you haven't exposed in the question.

### 4. The infinity-order issue is worth checking immediately

There is one thing in your stated hypotheses that I would treat as a mathematical red flag.

You say:

$$
\operatorname{div}_{\rm aff}(g)=A+C+T
$$

with each of \(A,C,T\) degree \(2\), so the affine divisor has degree \(6\).

You also say

$$
\operatorname{ord}_\infty(g)=-8.
$$

For a genuine nonzero rational function on a genus-2 hyperelliptic curve with a single point at infinity, the global principal divisor has degree \(0\). So if \(g\) has a pole of order \(8\) at infinity, its total zero divisor has degree \(8\), not \(6\).

Therefore these three statements cannot all mean the usual thing:

$$
\deg(\operatorname{div}_{\rm aff}(g))=6,
\qquad
\operatorname{ord}_\infty(g)=-8,
\qquad
g\neq0.
$$

There must be another contribution somewhere, or one of your project-local notions is deliberately not the global divisor/valuation. That may be completely intentional in your formalization, but it needs to be identified before using global divisor arguments.

This also explains why the old attempt to compare `g` and `u_new` by infinity order produced confusion: the formal `Divisor H` is explicitly only an affine bookkeeping object, whereas `ordInfOfPair` is measuring information that `Divisor H` deliberately does not record.

So I would **not** attempt to prove anything about `C-A-T+2δ₀` from the two affine equalities alone until this infinity bookkeeping is reconciled.

### 5. The clean K=4→K=2 correctness proof you actually want

For your exact setting, the classical proof is very short once stated at the right level.

Start with the divisor class you want to reduce:

$$
D=(C-2\infty)+(-A).
$$

Represent \(C\) by \((u_C,v_C)\) and \(-A\) by \((u_A,-v_A)\).

Construct the unique interpolation polynomial \(v(x)\) of degree at most \(3\) satisfying

$$
v\equiv v_C\pmod{u_C},
\qquad
v\equiv -v_A\pmod{u_A}.
$$

Then

$$
u_Cu_A\mid f-v^2.
$$

Set

$$
u_3=\frac{f-v^2}{u_Cu_A}.
$$

Because \(\deg f=5\), \(\deg u_Cu_A=4\), and \(\deg v\le3\), \(u_3\) has degree \(2\) after normalization.

Now

$$
h=y-v
$$

has zeros at the four points comprising \(C+(-A)\) and at the two residual points \(D_3\) determined by \(u_3\). Hence

$$
\operatorname{div}(h)
=
C+\iota(A)+D_3-6\infty
$$

with the appropriate \(y\)-sign convention.

Therefore

$$
[C-2\infty]-[A-2\infty]
=
-[D_3-2\infty].
$$

The Mumford output is by definition

$$
T=-D_3,
$$

so

$$
[C-2\infty]-[A-2\infty]
=
[T-2\infty].
$$

Rearranging gives

$$
C-A-T+2\infty\sim0.
$$

That is the exact theorem you need.

Notice what the proof does **not** use:

It does not use algebraic closure. The coefficients are obtained by solving the interpolation equations over \(F_p\), and the residual \(u_3\) is a degree-2 polynomial over \(F_p\). Its roots need not be individually \(F_p\)-rational for the divisor-class statement. In your formalization, the cleanest route may therefore be to formulate the residual divisor initially at the polynomial/Mumford level rather than immediately splitting it into `R1,R2`.

### Bottom line

I would classify the situation this way.

Your two proved affine identities are **not sufficient** to prove

```lean
C - A - T + 2 • [δ₀] ∈ PrincSub
```

and there is no generic "sum of `x-a` bridges" that fixes this. The `x-a` bridges only express differences of hyperelliptic fibers.

The missing mathematical theorem is **Cantor correctness for the subtraction step**:

$$
[C-2\infty]-[A-2\infty]
=
[T-2\infty].
$$

The right function-field witness is a new interpolation function for \(C+(-A)\), equivalently an explicit divisor identity with the hyperelliptic conjugates of \(A\) appearing. That is the genuinely missing content.

Moreover, before porting that theorem, I would audit the claimed combination

$$
\operatorname{div}_{\rm aff}(g)=A+C+T,
\qquad
\operatorname{ord}_\infty(g)=-8,
$$

because for a genuine global principal divisor those numbers do not balance. That may reveal that one of the current labels (`A`, `C`, `T`) is already carrying a conjugation/sign convention that would make the final theorem easier than it currently appears.

---

## Claire's follow-up check on this reply (logged in ROADMAP-principal-witness-assembly.md)

§4's diagnostic (the 6-vs-8 degree mismatch) is confirmed correct, but for
a different underlying reason than a multiple-points-at-infinity model:
`Step1`'s own Lean theorem never claimed `A+C+T` was `g`'s COMPLETE affine
divisor (it's `divToPair` restricted to a named 6-point Finset) — the
project's own roadmap prose had been overclaiming completeness. The two
missing zeros were found directly: they are `ι ρ1, ι ρ2` (conjugates of
`u_new`'s own two roots), via `g(ι P) = ḡ(P)` and the already-proved
`ḡ(ρ_i)=0` fact. See the roadmap's own dated status section for the full
derivation. §1-3's orientation-mismatch diagnosis is UNAFFECTED by this
correction and still stands as the primary open item.
