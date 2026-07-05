"""
Sanity check for trial3_phi_symbolic.jl's mathematical construction, done
independently in Python over a concrete F_p (not symbolic F_p(t) -- this
just checks the *algorithm* is right by comparing against a brute-force
reimplementation of the whole build_phi_general!/phi_residual_general!
pipeline for a concrete last anchor, then separately (in symbolic_port.py)
checking that plugging a concrete t into the *symbolic* construction's
formulas gives the same answer as running the concrete pipeline directly
with that same t as anchor K's px.

FIX vs the first version: u0,u1,v0,v1 must be an actual valid *reduced
Mumford divisor* of the curve -- i.e. v(x)^2 == f(x) mod u(x) -- not just
four random field elements. The rows K+1,K+2 of the linear system encode
"phi vanishes along the divisor (u,v)"; that only forces N(x) divisible by
u(x) if (u,v) really is a divisor supported on the curve (v interpolates
the correct y-coordinates at the roots of u). Random (u0,u1,v0,v1) fails
this with overwhelming probability, which is exactly why the first version
of this script threw "u(x) remainder nonzero" for every K. Fixed here by
building (u,v) as the Mumford representation of P1+P2 for two random
concrete curve points P1,P2 (u = (x-x1)(x-x2), v = line through the two
points) -- valid by construction since v(x1)=y1, v(x2)=y2 and yi^2=f(xi).
"""
import random

p = 10007  # prime

def fp(x): return x % p
def inv(a): return pow(a, p-2, p)

def strip(a):
    a = a[:]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def padd(a,b):
    n = max(len(a),len(b)); c=[0]*n
    for i,x in enumerate(a): c[i]=fp(c[i]+x)
    for i,x in enumerate(b): c[i]=fp(c[i]+x)
    return strip(c)
def psub(a,b):
    n = max(len(a),len(b)); c=[0]*n
    for i,x in enumerate(a): c[i]=fp(c[i]+x)
    for i,x in enumerate(b): c[i]=fp(c[i]-x)
    return strip(c)
def pmul(a,b):
    if a==[0] or b==[0]: return [0]
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x==0: continue
        for j,y in enumerate(b):
            c[i+j]=fp(c[i+j]+x*y)
    return strip(c)

def rr_basis(n_basis):
    basis=[]
    max_order = 2*n_basis+10
    cands=[]
    for i in range(max_order//2+1):
        cands.append((2*i,i,0))
        cands.append((2*i+5,i,1))
    cands.sort(key=lambda x:x[0])
    for (_,i,j) in cands:
        basis.append((i,j))
        if len(basis)==n_basis: break
    return basis

def eval_monomial(px,py,i,j):
    v = pow(px,i,p)
    if j==1: v = fp(v*py)
    return v

def build_xmodu_table(max_i,u0,u1):
    r0=[0]*(max_i+2); r1=[0]*(max_i+2)
    r0[0]=1; r1[0]=0
    if max_i+1>=1:
        r0[1]=0; r1[1]=1
    for i in range(2,max_i+2):
        prev0,prev1=r0[i-1],r1[i-1]
        r0[i]=fp(-prev1*u0)
        r1[i]=fp(prev0-prev1*u1)
    return r0,r1

def reduce_monomial(i,j,u0,u1,v0,v1,r0tab,r1tab):
    a0,a1=r0tab[i],r1tab[i]
    if j==0: return a0,a1
    b0,b1=r0tab[i+1],r1tab[i+1]
    return fp(v0*a0+v1*b0), fp(v0*a1+v1*b1)

def build_phi_and_residual(K, anchors, u0,u1,v0,v1, f_asc):
    """anchors: list of (px,py), length K.  f_asc ascending coeffs of f(x)."""
    nb = K+3
    basis = rr_basis(nb)
    y_idx = [idx for idx,b in enumerate(basis) if b==(0,1)][0]
    other_idx = [idx for idx in range(nb) if idx != y_idx]
    n_unk = K+2
    assert len(other_idx)==n_unk

    A = [[0]*n_unk for _ in range(n_unk)]
    rhs = [0]*n_unk

    for a in range(K):
        px,py = anchors[a]
        for col,bidx in enumerate(other_idx):
            bi,bj = basis[bidx]
            A[a][col] = eval_monomial(px,py,bi,bj)
        bi_n,bj_n = basis[y_idx]
        rhs[a] = fp(-eval_monomial(px,py,bi_n,bj_n))

    max_basis_i = max(bi for bi,_ in basis)
    r0tab,r1tab = build_xmodu_table(max_basis_i+1,u0,u1)
    row0,row1 = K, K+1
    for col,bidx in enumerate(other_idx):
        bi,bj = basis[bidx]
        rr0,rr1 = reduce_monomial(bi,bj,u0,u1,v0,v1,r0tab,r1tab)
        A[row0][col]=rr0; A[row1][col]=rr1
    bi_n,bj_n = basis[y_idx]
    rn0,rn1 = reduce_monomial(bi_n,bj_n,u0,u1,v0,v1,r0tab,r1tab)
    rhs[row0]=fp(-rn0); rhs[row1]=fp(-rn1)

    # gaussian elimination over F_p
    n = n_unk
    M = [row[:] for row in A]; b = rhs[:]
    for col in range(n):
        piv=None
        for r in range(col,n):
            if M[r][col]!=0: piv=r; break
        assert piv is not None, "singular"
        M[col],M[piv]=M[piv],M[col]; b[col],b[piv]=b[piv],b[col]
        pinv = inv(M[col][col])
        for r in range(col+1,n):
            if M[r][col]==0: continue
            factor = fp(M[r][col]*pinv)
            for c in range(col,n):
                M[r][c] = fp(M[r][c]-factor*M[col][c])
            b[r]=fp(b[r]-factor*b[col])
    x=[0]*n
    for row in range(n-1,-1,-1):
        acc=b[row]
        for c in range(row+1,n):
            acc=fp(acc-M[row][c]*x[c])
        x[row]=fp(acc*inv(M[row][row]))

    coeffs=[0]*nb
    for col,bidx in enumerate(other_idx):
        coeffs[bidx]=x[col]
    coeffs[y_idx]=1

    max_i_E = max((bi for bi,bj in basis if bj==0), default=0)
    max_i_Y = max((bi for bi,bj in basis if bj==1), default=-1)
    E=[0]*(max_i_E+1)
    Y=[0]*(max_i_Y+1) if max_i_Y>=0 else []
    for bidx in range(nb):
        bi,bj=basis[bidx]
        if bj==0: E[bi]=fp(E[bi]+coeffs[bidx])
        else: Y[bi]=fp(Y[bi]+coeffs[bidx])

    Esq = pmul(E,E)
    Ysq = pmul(Y,Y) if Y else [0]
    fY2 = pmul(Ysq, f_asc)
    N = psub(Esq, fY2)

    # divide out anchors[0..K-1]'s (x-px) factors
    cur = N
    for a in range(K):
        px,_ = anchors[a]
        n_ = len(cur)
        if n_==1:
            rem=cur[0]; q=[0]
        else:
            q=[0]*(n_-1)
            acc=cur[-1]
            for i in range(n_-2,-1,-1):
                q[i]=acc
                acc=fp(cur[i]+px*acc)
            rem=acc
        assert rem==0, f"remainder nonzero dividing out anchor {a}: {rem}"
        cur = strip(q)

    # divide out u(x)=x^2+u1 x+u0
    n_ = len(cur)
    buf = cur[:]
    for i in range(n_-1,1,-1):
        c = buf[i]
        if c==0: continue
        buf[i-1]=fp(buf[i-1]-c*u1)
        buf[i-2]=fp(buf[i-2]-c*u0)
    r0f,r1f = buf[0],buf[1]
    assert r0f==0 and r1f==0, f"u(x) remainder nonzero: {r0f},{r1f}"
    cur = strip(buf[2:]) if n_>2 else [0]

    lc = cur[-1]
    if lc!=1:
        il = inv(lc)
        cur = [fp(c*il) for c in cur]
    u_RS = cur

    # v_RS = -E * Yinv mod u_RS
    negE = [fp(-c) for c in E]
    def pmod(a,m):
        a = a[:]
        dm = len(m)-1
        lc_inv = inv(m[-1])
        while len(a)-1>=dm and not (len(a)==1 and a[0]==0):
            if a[-1]==0:
                a.pop(); continue
            c = fp(a[-1]*lc_inv)
            shift = len(a)-1-dm
            for i in range(dm+1):
                a[shift+i]=fp(a[shift+i]-c*m[i])
            while len(a)>1 and a[-1]==0: a.pop()
        return a
    def pdivrem(a,b):
        a=a[:]; b=strip(b)
        db=len(b)-1
        lb_inv=inv(b[-1])
        q=[0]*max(len(a)-db,1)
        while not (len(a)==1 and a[0]==0) and len(a)-1>=db:
            dr=len(a)-1
            c=fp(a[-1]*lb_inv)
            shift=dr-db
            q[shift]=fp(q[shift]+c)
            for i in range(db+1):
                a[shift+i]=fp(a[shift+i]-c*b[i])
            a=strip(a)
        return strip(q),a
    def invmod(a,m):
        old_r,r=m[:],a[:]
        old_s,s=[0],[1]
        while not (len(r)==1 and r[0]==0):
            q,rem = pdivrem(old_r,r)
            old_r,r = r,rem
            qs = pmul(q,s)
            n2 = max(len(old_s),len(qs))
            os_ = old_s+[0]*(n2-len(old_s))
            new_s = psub(os_, qs)
            old_s,s = s,strip(new_s)
        assert len(old_r)==1
        ginv = inv(old_r[0])
        return strip([fp(c*ginv) for c in old_s])

    negE_mod = pmod(negE,u_RS)
    Y_mod = pmod(Y,u_RS)
    Y_inv_mod = invmod(Y_mod,u_RS)
    v_RS = pmod(pmul(negE_mod,Y_inv_mod), u_RS)

    return u_RS, v_RS, len(E)-1, (len(Y)-1 if Y else -1)


# --- test curve: y^2=f(x), degree 5, monic, over F_p ---
random.seed(42)
f_asc = [fp(random.randint(1,p-1)) for _ in range(5)] + [1]  # monic degree 5

def is_qr(a):
    return pow(a, (p-1)//2, p) == 1

def curve_fx(x):
    fx = 0
    for i,c in enumerate(f_asc):
        fx = fp(fx + c*pow(x,i,p))
    return fx

def find_point(exclude_x=set()):
    while True:
        x = random.randint(1,p-1)
        if x in exclude_x: continue
        fx = curve_fx(x)
        if fx==0: continue
        if is_qr(fx):
            y = pow(fx,(p+1)//4,p) if p%4==3 else None
            if y is None:
                continue
            if fp(y*y)==fx:
                return x,y

def make_valid_mumford_divisor(exclude_x=set()):
    """
    Build a genuine reduced Mumford divisor D=(u,v) of weight 2 by taking
    two distinct random curve points P1=(x1,y1), P2=(x2,y2) and setting
        u(x) = (x-x1)(x-x2)
        v(x) = the (degree <= 1) line through P1,P2
    This satisfies v(x)^2 == f(x) mod u(x) by construction (v matches the
    real y-coordinate at both roots of u), unlike four independently random
    field elements.
    Returns (u0,u1,v0,v1,P1,P2) with u(x)=x^2+u1*x+u0, v(x)=v1*x+v0.
    """
    x1,y1 = find_point(exclude_x)
    x2,y2 = find_point(exclude_x | {x1})
    u1_ = fp(-(x1+x2))
    u0_ = fp(x1*x2)
    v1_ = fp((y2-y1)*inv(x2-x1))
    v0_ = fp(y1 - v1_*x1)
    return u0_,u1_,v0_,v1_,(x1,y1),(x2,y2)


if __name__ == "__main__":
    for K in [1,2,3]:
        anchors=[]
        xs=set()
        for _ in range(K):
            x,y = find_point(xs)
            xs.add(x)
            anchors.append((x,y))
        u0,u1,v0,v1,P1,P2 = make_valid_mumford_divisor(xs)
        try:
            u_RS,v_RS,degE,degY = build_phi_and_residual(K, anchors, u0,u1,v0,v1, f_asc)
            print(f"K={K}: OK  deg_E={degE} deg_Y={degY}  u_RS={u_RS}  v_RS={v_RS}  (deg u_RS = {len(u_RS)-1})")
        except AssertionError as e:
            print(f"K={K}: FAILED ({e})  anchors={anchors} divisor points={P1},{P2} u0,u1={u0,u1} v0,v1={v0,v1}")
