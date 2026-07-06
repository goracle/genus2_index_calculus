"""
Python port of trial3_phi_symbolic.jl's math, for cross-checking against
sanity_check.py's concrete pipeline. Mirrors the Julia file's RFun/Ft2
structures directly (same algorithms), just in Python so it's runnable here.
"""
import sanity_check as sc
p = sc.p

def fp(x): return x % p
def fpinv(a):
    a = fp(a)
    assert a != 0
    return pow(a, p-2, p)

def strip(a):
    a = a[:]
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def is_zero_poly(a): return len(a)==1 and a[0]==0
def deg(a): return -1 if is_zero_poly(a) else len(a)-1

def padd(a,b):
    n=max(len(a),len(b)); c=[0]*n
    for i,x in enumerate(a): c[i]=fp(c[i]+x)
    for i,x in enumerate(b): c[i]=fp(c[i]+x)
    return strip(c)
def psub(a,b):
    n=max(len(a),len(b)); c=[0]*n
    for i,x in enumerate(a): c[i]=fp(c[i]+x)
    for i,x in enumerate(b): c[i]=fp(c[i]-x)
    return strip(c)
def pmul(a,b):
    if is_zero_poly(a) or is_zero_poly(b): return [0]
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x==0: continue
        for j,y in enumerate(b):
            c[i+j]=fp(c[i+j]+x*y)
    return strip(c)
def pdivrem(a,b):
    a=a[:]; b=strip(b)
    db=deg(b); lb_inv=fpinv(b[-1])
    q=[0]*max(deg(a)-db+1,1)
    while not is_zero_poly(a) and deg(a)>=db:
        dr=deg(a); c=fp(a[-1]*lb_inv); shift=dr-db
        q[shift]=fp(q[shift]+c)
        for i in range(db+1):
            a[shift+i]=fp(a[shift+i]-c*b[i])
        a=strip(a)
    return strip(q),a
def pgcd(a,b):
    a=strip(a); b=strip(b)
    while not is_zero_poly(b):
        _,r = pdivrem(a,b); a,b = b,r
    if not is_zero_poly(a) and a[-1]!=1:
        il=fpinv(a[-1]); a=[fp(c*il) for c in a]
    return a

class RFun:
    __slots__=('num','den')
    def __init__(self,num,den):
        self.num=num; self.den=den
    @staticmethod
    def const(a): return RFun([fp(a)],[1])
    @staticmethod
    def zero(): return RFun([0],[1])
    @staticmethod
    def one(): return RFun([1],[1])
    @staticmethod
    def t(): return RFun([0,1],[1])
    @staticmethod
    def from_poly(c): return rfun_norm(c[:], [1])

def rfun_norm(num,den):
    num=strip(num); den=strip(den)
    assert not is_zero_poly(den)
    if is_zero_poly(num): return RFun([0],[1])
    g = pgcd(num,den)
    if not (deg(g)==0 and g[0]==1):
        num,_=pdivrem(num,g); den,_=pdivrem(den,g)
    if den[-1]!=1:
        il=fpinv(den[-1]); num=[fp(c*il) for c in num]; den=[fp(c*il) for c in den]
    return RFun(num,den)

def rf_add(a,b): return rfun_norm(padd(pmul(a.num,b.den),pmul(b.num,a.den)), pmul(a.den,b.den))
def rf_sub(a,b): return rfun_norm(psub(pmul(a.num,b.den),pmul(b.num,a.den)), pmul(a.den,b.den))
def rf_neg(a): return RFun([fp(-c) for c in a.num], a.den)
def rf_mul(a,b): return rfun_norm(pmul(a.num,b.num), pmul(a.den,b.den))
def rf_is_zero(a): return is_zero_poly(a.num)
def rf_inv(a):
    assert not rf_is_zero(a)
    return rfun_norm(a.den[:], a.num[:])
def rf_eq(a,b): return a.num==b.num and a.den==b.den
def rf_eval(a, tval):
    num = 0
    for i,c in enumerate(a.num): num = fp(num + c*pow(tval,i,p))
    den = 0
    for i,c in enumerate(a.den): den = fp(den + c*pow(tval,i,p))
    return fp(num * fpinv(den))

class Ft2:
    __slots__=('a','b','fT')
    def __init__(self,a,b,fT): self.a=a; self.b=b; self.fT=fT
def ft2c(a,fT): return Ft2(a, RFun.zero(), fT)
def ft2w(fT): return Ft2(RFun.zero(), RFun.one(), fT)
def ft2_add(x,y): return Ft2(rf_add(x.a,y.a), rf_add(x.b,y.b), x.fT)
def ft2_sub(x,y): return Ft2(rf_sub(x.a,y.a), rf_sub(x.b,y.b), x.fT)
def ft2_neg(x): return Ft2(rf_neg(x.a), rf_neg(x.b), x.fT)
def ft2_mul(x,y):
    newa = rf_add(rf_mul(x.a,y.a), rf_mul(rf_mul(x.b,y.b), x.fT))
    newb = rf_add(rf_mul(x.a,y.b), rf_mul(x.b,y.a))
    return Ft2(newa,newb,x.fT)
def ft2_is_zero(x): return rf_is_zero(x.a) and rf_is_zero(x.b)
def ft2_inv(x):
    norm = rf_sub(rf_mul(x.a,x.a), rf_mul(rf_mul(x.b,x.b), x.fT))
    assert not rf_is_zero(norm)
    ninv = rf_inv(norm)
    return Ft2(rf_mul(x.a,ninv), rf_mul(rf_neg(x.b),ninv), x.fT)

def rr_basis(n_basis):
    basis=[]; max_order=2*n_basis+10; cands=[]
    for i in range(max_order//2+1):
        cands.append((2*i,i,0)); cands.append((2*i+5,i,1))
    cands.sort(key=lambda z:z[0])
    for (_,i,j) in cands:
        basis.append((i,j))
        if len(basis)==n_basis: break
    return basis

def build_xmodu_table(max_i,u0,u1):
    r0=[0]*(max_i+2); r1=[0]*(max_i+2)
    r0[0]=1; r1[0]=0
    if max_i+1>=1: r0[1]=0; r1[1]=1
    for i in range(2,max_i+2):
        prev0,prev1=r0[i-1],r1[i-1]
        r0[i]=fp(-prev1*u0); r1[i]=fp(prev0-prev1*u1)
    return r0,r1
def reduce_monomial(i,j,u0,u1,v0,v1,r0tab,r1tab):
    a0,a1=r0tab[i],r1tab[i]
    if j==0: return a0,a1
    b0,b1=r0tab[i+1],r1tab[i+1]
    return fp(v0*a0+v1*b0), fp(v0*a1+v1*b1)

def gauss_solve_ft2(A,rhs):
    n=len(rhs)
    M=[row[:] for row in A]; b=rhs[:]
    for col in range(n):
        piv=None
        for r in range(col,n):
            if not ft2_is_zero(M[r][col]): piv=r; break
        assert piv is not None, "singular"
        M[col],M[piv]=M[piv],M[col]; b[col],b[piv]=b[piv],b[col]
        pinv = ft2_inv(M[col][col])
        for r in range(col+1,n):
            if ft2_is_zero(M[r][col]): continue
            factor = ft2_mul(M[r][col],pinv)
            for c in range(col,n):
                M[r][c] = ft2_sub(M[r][c], ft2_mul(factor,M[col][c]))
            b[r] = ft2_sub(b[r], ft2_mul(factor,b[col]))
    x=[None]*n
    for row in range(n-1,-1,-1):
        acc=b[row]
        for c in range(row+1,n):
            acc = ft2_sub(acc, ft2_mul(M[row][c], x[c]))
        x[row] = ft2_mul(acc, ft2_inv(M[row][row]))
    return x

def eval_monomial_ft2(px,py,i,j):
    v = ft2c(RFun.one(), px.fT)
    for _ in range(i): v = ft2_mul(v,px)
    if j==1: v = ft2_mul(v,py)
    return v

def symbolic_residual_ft2(K, fixed_anchors, u0,u1,v0,v1, f_asc):
    """
    Raw (non-collapsing) version: returns u_RS, v_RS as lists of Ft2
    (a(t) + b(t)*w pairs), with NO assertion that b(t)==0. This is the
    honest object -- see symbolic_residual() below for the correct way
    to use it with a real anchor.
    """
    nb=K+3
    basis=rr_basis(nb)
    y_idx=[idx for idx,bb in enumerate(basis) if bb==(0,1)][0]
    fT = RFun.from_poly(f_asc)
    t = ft2c(RFun.t(), fT)
    w = ft2w(fT)

    n_unk=K+2
    other_idx=[idx for idx in range(nb) if idx!=y_idx]
    A=[[None]*n_unk for _ in range(n_unk)]
    rhs=[None]*n_unk

    anchor_pts=[None]*K
    for a in range(K-1):
        px_raw,py_raw = fixed_anchors[a]
        anchor_pts[a] = (ft2c(RFun.const(px_raw),fT), ft2c(RFun.const(py_raw),fT))
    anchor_pts[K-1] = (t,w)

    for a in range(K):
        px,py = anchor_pts[a]
        for col,bidx in enumerate(other_idx):
            bi,bj = basis[bidx]
            A[a][col] = eval_monomial_ft2(px,py,bi,bj)
        bi_n,bj_n = basis[y_idx]
        rhs[a] = ft2_neg(eval_monomial_ft2(px,py,bi_n,bj_n))

    max_basis_i = max(bi for bi,_ in basis)
    r0tab,r1tab = build_xmodu_table(max_basis_i+1,u0,u1)
    row0,row1 = K,K+1
    for col,bidx in enumerate(other_idx):
        bi,bj = basis[bidx]
        rr0,rr1 = reduce_monomial(bi,bj,u0,u1,v0,v1,r0tab,r1tab)
        A[row0][col]=ft2c(RFun.const(rr0),fT)
        A[row1][col]=ft2c(RFun.const(rr1),fT)
    bi_n,bj_n = basis[y_idx]
    rn0,rn1 = reduce_monomial(bi_n,bj_n,u0,u1,v0,v1,r0tab,r1tab)
    rhs[row0]=ft2c(RFun.const(fp(-rn0)),fT)
    rhs[row1]=ft2c(RFun.const(fp(-rn1)),fT)

    c = gauss_solve_ft2(A,rhs)
    coeffs=[None]*nb
    for col,bidx in enumerate(other_idx): coeffs[bidx]=c[col]
    coeffs[y_idx]=ft2c(RFun.one(),fT)

    max_i_E = max((bi for bi,bj in basis if bj==0), default=0)
    max_i_Y = max((bi for bi,bj in basis if bj==1), default=-1)
    E=[ft2c(RFun.zero(),fT) for _ in range(max_i_E+1)]
    Y=[ft2c(RFun.zero(),fT) for _ in range(max_i_Y+1)] if max_i_Y>=0 else []
    for bidx in range(nb):
        bi,bj = basis[bidx]
        if bj==0: E[bi]=ft2_add(E[bi],coeffs[bidx])
        else: Y[bi]=ft2_add(Y[bi],coeffs[bidx])

    def ft2_pmul(a,b):
        c=[ft2c(RFun.zero(),fT) for _ in range(len(a)+len(b)-1)]
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                c[i+j]=ft2_add(c[i+j], ft2_mul(x,y))
        return c
    def ft2_psub(a,b):
        n=max(len(a),len(b))
        c=[ft2c(RFun.zero(),fT) for _ in range(n)]
        for i,x in enumerate(a): c[i]=ft2_add(c[i],x)
        for i,x in enumerate(b): c[i]=ft2_sub(c[i],x)
        return c

    Esq = ft2_pmul(E,E)
    Ysq = ft2_pmul(Y,Y) if Y else [ft2c(RFun.zero(),fT)]
    f_ft2 = [ft2c(RFun.const(cc),fT) for cc in f_asc]
    fY2 = ft2_pmul(Ysq, f_ft2)
    Nx = ft2_psub(Esq, fY2)

    # NOTE (fixed per Claire, 2026-07-05): N(x) does NOT generally collapse
    # to pure F_p(t) (w-part == 0). That was verified false numerically:
    # w -> -w sends each phi-coefficient (a,b) -> (a,-b) exactly (real
    # Galois conjugation of the anchor's field), but N(x) formed from the
    # w-negated (E,Y) is not the w-negated N(x) -- its b-part is a
    # different nonzero rational function, not the negative of the
    # original. N(x) IS guaranteed polynomial in x (that's the y -> -y
    # norm baked into E(x)^2-f(x)Y(x)^2 regardless of E,Y) -- it is simply
    # not guaranteed to descend to the subfield F_p(t). So N(x), and hence
    # u_RS, v_RS below, are carried as genuine Ft2 objects throughout; only
    # symbolic_residual() (evaluating at a concrete t0,y0) collapses to F_p.
    N_ft2 = Nx
    while len(N_ft2)>1 and ft2_is_zero(N_ft2[-1]): N_ft2.pop()

    # Divide out ALL K anchor factors, not just the K-1 fixed ones: the
    # concrete pipeline (build_phi_and_residual) divides out every anchor
    # including the last (see its `for a in range(K)` loop over ALL
    # anchors) because every anchor -- symbolic or not -- is a root of
    # phi, hence of N(x) = phi(x,y)*phi(x,-y). The symbolic K-th anchor's
    # factor is (x - t), i.e. divide by the Ft2 constant `t` itself.
    # Missing this step was a real bug: it left N(x) one degree too high
    # after division (confirmed by comparing deg(u_RS) against the
    # concrete pipeline's build_phi_and_residual for the same K,u,v,f).
    cur = N_ft2
    anchor_factors = [ft2c(RFun.const(px_raw), fT) for px_raw,_ in fixed_anchors] + [t]
    for a, r in enumerate(anchor_factors):
        n_=len(cur)
        if n_==1:
            rem=cur[0]; q=[ft2c(RFun.zero(),fT)]
        else:
            q=[None]*(n_-1); acc=cur[-1]
            for i in range(n_-2,-1,-1):
                q[i]=acc
                acc=ft2_add(cur[i], ft2_mul(r,acc))
            rem=acc
        assert ft2_is_zero(rem), f"remainder dividing out anchor {a}"
        cur=q
        while len(cur)>1 and ft2_is_zero(cur[-1]): cur.pop()

    n_=len(cur)
    U1=ft2c(RFun.const(u1),fT); U0=ft2c(RFun.const(u0),fT)
    buf=cur[:]
    for i in range(n_-1,1,-1):
        cc=buf[i]
        if ft2_is_zero(cc): continue
        buf[i-1]=ft2_sub(buf[i-1], ft2_mul(cc,U1))
        buf[i-2]=ft2_sub(buf[i-2], ft2_mul(cc,U0))
    r0f,r1f = buf[0],buf[1]
    assert ft2_is_zero(r0f) and ft2_is_zero(r1f), f"u(x) remainder nonzero"
    cur = buf[2:] if n_>2 else [ft2c(RFun.zero(),fT)]
    while len(cur)>1 and ft2_is_zero(cur[-1]): cur.pop()

    lc = cur[-1]
    is_monic_already = (lc.a.num==[1] and lc.a.den==[1] and rf_is_zero(lc.b))
    if not is_monic_already:
        il = ft2_inv(lc)
        cur = [ft2_mul(cc,il) for cc in cur]
    u_RS = cur

    # v_RS = -E * Yinv mod u_RS, ALL over Ft2 (u_RS/modulus is Ft2-valued now,
    # not RFun-valued -- see the branch-dependence note above).
    def ft2_pmod_ft2mod(a, m_ft2):
        dm=len(m_ft2)-1
        a=a[:]
        lc_inv = ft2_inv(m_ft2[-1])
        while len(a)-1>=dm and not (len(a)==1 and ft2_is_zero(a[0])):
            if ft2_is_zero(a[-1]):
                a.pop(); continue
            c = ft2_mul(a[-1], lc_inv)
            shift = len(a)-1-dm
            for i in range(dm+1):
                a[shift+i] = ft2_sub(a[shift+i], ft2_mul(c,m_ft2[i]))
            while len(a)>1 and ft2_is_zero(a[-1]): a.pop()
        return a
    def ft2_pdivrem(a,b):
        a=a[:]
        while len(b)>1 and ft2_is_zero(b[-1]): b=b[:-1]
        db=len(b)-1
        lb_inv=ft2_inv(b[-1])
        q=[ft2c(RFun.zero(),fT) for _ in range(max(len(a)-db,1))]
        while not (len(a)==1 and ft2_is_zero(a[0])) and len(a)-1>=db:
            dr=len(a)-1; c=ft2_mul(a[-1],lb_inv); shift=dr-db
            q[shift]=ft2_add(q[shift],c)
            for i in range(db+1):
                a[shift+i]=ft2_sub(a[shift+i], ft2_mul(c,b[i]))
            while len(a)>1 and ft2_is_zero(a[-1]): a.pop()
        while len(q)>1 and ft2_is_zero(q[-1]): q.pop()
        return q,a
    def ft2_invmod_ft2mod(a,m_ft2):
        zero1=ft2c(RFun.zero(),fT); one1=ft2c(RFun.one(),fT)
        old_r,r = m_ft2[:], a[:]
        old_s,s = [zero1],[one1]
        while not (len(r)==1 and ft2_is_zero(r[0])):
            q,rem = ft2_pdivrem(old_r,r)
            old_r,r = r,rem
            cprod=[ft2c(RFun.zero(),fT) for _ in range(len(q)+len(s)-1)]
            for i,x in enumerate(q):
                for j,y in enumerate(s):
                    cprod[i+j]=ft2_add(cprod[i+j], ft2_mul(x,y))
            qs=cprod
            n2=max(len(old_s),len(qs))
            os_ = old_s+[ft2c(RFun.zero(),fT)]*(n2-len(old_s))
            qs_ = qs+[ft2c(RFun.zero(),fT)]*(n2-len(qs))
            new_s = [ft2_sub(os_[i],qs_[i]) for i in range(n2)]
            while len(new_s)>1 and ft2_is_zero(new_s[-1]): new_s.pop()
            old_s,s = s,new_s
        ginv = ft2_inv(old_r[0])
        return [ft2_mul(cc,ginv) for cc in old_s]

    negE = [ft2_neg(cc) for cc in E]
    negE_mod = ft2_pmod_ft2mod(negE, u_RS)
    Y_mod = ft2_pmod_ft2mod(Y, u_RS)
    Y_inv_mod = ft2_invmod_ft2mod(Y_mod, u_RS)
    cprod=[ft2c(RFun.zero(),fT) for _ in range(len(negE_mod)+len(Y_inv_mod)-1)]
    for i,x in enumerate(negE_mod):
        for j,y in enumerate(Y_inv_mod):
            cprod[i+j]=ft2_add(cprod[i+j], ft2_mul(x,y))
    v_RS_ft2 = ft2_pmod_ft2mod(cprod, u_RS)
    while len(v_RS_ft2)>1 and ft2_is_zero(v_RS_ft2[-1]): v_RS_ft2.pop()

    # u_RS, v_RS are genuine Ft2 objects (a(t)+b(t)*w pairs) -- see the note
    # above symbolic_residual_ft2's N(x) construction. No collapse here;
    # only symbolic_residual() below (evaluating at a concrete t0,y0)
    # produces a plain F_p result.
    return u_RS, v_RS_ft2


def symbolic_residual(K, fixed_anchors, u0, u1, v0, v1, f_asc, t0, y0):
    """
    Correct way to use the symbolic construction for a REAL anchor point
    (t0, y0) with y0^2 == f(t0) mod p: evaluate the raw a(t),b(t) rational
    functions from symbolic_residual_ft2 at t0, then recombine with the
    KNOWN y0 -- a(t0) + b(t0)*y0. For a genuine affine F_p point this lands
    back in F_p automatically (real + real*real = real); b(t) itself is NOT
    required to be identically zero (and generically isn't) -- that would be
    a much stronger claim (branch-independence), which is false in general:
    using the "wrong" root -y0 instead of y0 corresponds to a genuinely
    different point of the Jacobian and generically gives a different
    (still real) residual.
    """
    u_RS_ft2, v_RS_ft2 = symbolic_residual_ft2(K, fixed_anchors, u0, u1, v0, v1, f_asc)

    def combine(coeffs):
        out = []
        for c in coeffs:
            a_val = rf_eval(c.a, t0)
            b_val = rf_eval(c.b, t0)
            out.append(fp((a_val + b_val * y0)))
        # strip trailing zeros like sanity_check.strip
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        return out

    return combine(u_RS_ft2), combine(v_RS_ft2)
