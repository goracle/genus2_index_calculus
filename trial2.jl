#!/usr/bin/env julia
# =============================================================================
#  trial2.jl  --  Index calculus via Markov-walk / phi-function relations
#
#  Same curve/field/subgroup as trial1.jl.  Instead of the Gaudry-Harley
#  random-pair strategy we use the Diem plane-model variant:
#
#  Walk step  (current point P0 = (px, py)):
#    1. Pick random (alpha, beta), form D = alpha*G + beta*T  (degree-2 Mumford).
#       Extract the two affine support points Q1=(x1,y1), Q2=(x2,y2) of D.
#    2. Build phi = a*x^2 + b*x + c + d*y  vanishing at P0, Q1, Q2.
#       (4 coefficients, 1 overall scale => 3 free parameters, 3 conditions
#        => unique phi up to scale.)
#    3. div(phi) on C has degree 5 (C is a plane quintic):
#         div(phi) = [P0] + [Q1] + [Q2] + [R] + [S] - 5*[inf]
#       Recover R, S by forming N(x) = (a*x^2+b*x+c)^2 - d^2*f(x) (degree 5),
#       then dividing out the three known roots px, x1, x2.
#    4. Principal-divisor relation in Cl^0:
#         atom(P0) + atom(R) + atom(S) = -(alpha*G + beta*T)
#       where atom(P) = [P] - [inf].
#       When P0, R, S are all in the factor base F, record this relation.
#    5. Set P_next = R;  add P0, R, S to F during the build phase.
#
#  Phase 1: walk until |F| >= fb_target.
#  Phase 2: continue walk, recording relations whenever P0,R,S in F.
#           Stop after |F|+20 relations; left-kernel => k.
# =============================================================================

include("trial1.jl")   # all Fp/poly/Jacobian/curve utilities

# ---------------------------------------------------------------------------
#  phi construction
#
#  phi(x,y) = a*x^2 + b*x + c + d*y
#
#  Vanishing conditions (mod p):
#    a*px^2 + b*px + c + d*py = 0
#    a*x1^2 + b*x1 + c + d*y1 = 0
#    a*x2^2 + b*x2 + c + d*y2 = 0
#
#  Fix d=1 and solve the 3x3 system in (a,b,c).  If singular, fix a=1 and
#  solve for (b,c,d).  Returns (a,b,c,d) or nothing.
# ---------------------------------------------------------------------------
function build_phi(px::Int, py::Int,
                   x1::Int, y1::Int,
                   x2::Int, y2::Int)::Union{NTuple{4,Int}, Nothing}

    M = [fp(px*px)  px  1  py;
         fp(x1*x1)  x1  1  y1;
         fp(x2*x2)  x2  1  y2]

    # 3x3 Gaussian elimination over Fp.  A is 3x3, rhs is length-3.
    function solve3(A::Matrix{Int}, rhs::Vector{Int})::Union{Vector{Int}, Nothing}
        Aug = hcat(mod.(A, p), mod.(rhs, p))
        for col in 1:3
            piv = findfirst(r -> Aug[r, col] != 0, col:3)
            piv === nothing && return nothing
            piv += col - 1
            Aug[[col, piv], :] = Aug[[piv, col], :]
            inv_lc = powermod(Int(Aug[col, col]), p - 2, p)
            Aug[col, :] = mod.(Aug[col, :] .* inv_lc, p)
            for r in 1:3
                r == col && continue
                f = Aug[r, col]
                f == 0 && continue
                Aug[r, :] = mod.(Aug[r, :] .- f .* Aug[col, :], p)
            end
        end
        Aug[:, 4]
    end

    # Try d = 1: solve M[:,1:3] * [a,b,c]' = -M[:,4]
    rhs1 = [fp(-py), fp(-y1), fp(-y2)]
    sol1 = solve3(M[:, 1:3], rhs1)
    if sol1 !== nothing
        a, b, c = sol1
        return (fp(a), fp(b), fp(c), 1)
    end

    # Fallback: a = 1, solve M[:,2:4] * [b,c,d]' = -M[:,1]
    rhs2 = [fp(-fp(px*px)), fp(-fp(x1*x1)), fp(-fp(x2*x2))]
    sol2 = solve3(M[:, 2:4], rhs2)
    sol2 === nothing && return nothing
    b2, c2, d2 = sol2
    return (1, fp(b2), fp(c2), fp(d2))
end

# ---------------------------------------------------------------------------
#  Residual intersection points R, S
#
#  phi(x,y) = 0 on C: substitute y = -(a*x^2+b*x+c)/d into y^2=f(x):
#    N(x) = (a*x^2+b*x+c)^2 - d^2*f(x)   (degree 5, leading coeff -d^2)
#
#  Three roots px, x1, x2 are known.  Divide them out -> degree-2 residual.
#  Returns vector of (x,y) pairs with correct y-sign (length 0, 1, or 2).
# ---------------------------------------------------------------------------
function phi_residual_points(a::Int, b::Int, c::Int, d::Int,
                              px::Int, x1::Int, x2::Int)::Vector{NTuple{2,Int}}
    d == 0 && return NTuple{2,Int}[]

    # N(x) = (a*x^2+b*x+c)^2 - d^2*f(x)
    apoly = Int[c, b, a]                    # ascending-coeff representation
    sq    = pmul(apoly, apoly)              # degree 4
    fd2   = pscale(F_POLY, fp(d * d))      # d^2*f(x), degree 5 (len 6)
    nlen  = max(length(sq), length(fd2))
    N     = ptrim(mod.(
                vcat(sq,  zeros(Int, nlen - length(sq))) .-
                vcat(fd2, zeros(Int, nlen - length(fd2))),
                p))

    # Divide out a known root r => divide by (x - r) = [-r, 1]
    function divide_out(poly::Vector{Int}, r::Int)::Union{Vector{Int}, Nothing}
        q, rem = pdivrem(poly, Int[fp(-r), 1])
        pzero(rem) ? q : nothing
    end

    q = divide_out(N,  px);  q === nothing && return NTuple{2,Int}[]
    q = divide_out(q,  x1);  q === nothing && return NTuple{2,Int}[]
    q = divide_out(q,  x2);  q === nothing && return NTuple{2,Int}[]
    q = ptrim(q)

    # Given x-coordinate, find correct y using phi(x,y) = 0
    function y_for_x(xr::Int)::Union{NTuple{2,Int}, Nothing}
        yr = sqrt_fp(eval_f(xr));  yr === nothing && return nothing
        base = fp(a * fp(xr * xr) + b * xr + c)
        fp(base + d * yr) == 0 && return (xr, yr)
        fp(base - d * yr) == 0 && return (xr, fp(-yr))
        return nothing
    end

    pts = NTuple{2,Int}[]
    dq  = pdeg(q)

    if dq == 1
        xr = fp(-q[1] * fpinv(q[2]))
        pt = y_for_x(xr);  pt !== nothing && push!(pts, pt)

    elseif dq == 2
        q_monic = pscale(q, fpinv(q[end]))   # normalise to monic for u2_roots
        rs = u2_roots(q_monic);  rs === nothing && return NTuple{2,Int}[]
        for xr in rs
            pt = y_for_x(xr);  pt !== nothing && push!(pts, pt)
        end
    end

    pts
end


# ---------------------------------------------------------------------------
#  index_calculus_walk
#
#  Strategy: run the Markov walk for `walk_steps` steps, recording EVERY
#  valid phi-step as a raw relation over all 5 atoms {P0,Q1,Q2,R,S}.
#  Then choose the factor base F = the `fb_size` most-frequent atoms.
#  Extract the submatrix of relations where all 5 atoms are in F.
#  Solve via left-kernel => k.
#
#  jac_mul is called only ONCE per walk step (to update the running
#  Jacobian accumulator by one G-step), not twice with large scalars.
#  Concretely: we maintain D_cur = alpha_cur*G + beta_cur*T by doing
#  D_cur += G each step and tracking alpha_cur mod ell.  For the beta
#  coefficient we fold T in randomly every few steps.  Actually the
#  simplest correct approach: just add a random small multiple of G and T
#  each step using jac_add (single doubling-and-add with tiny scalar).
#
#  Faster: precompute all (alpha,beta,x1,y1,x2,y2) by iterating the
#  curve points directly — D doesn't need to come from G,T during the
#  walk; we just need *any* degree-2 split divisor.  We recover (alpha,beta)
#  at the end by solving the discrete log of each factor-base atom.
#
#  BUT: we need the relation to be in terms of G and T, so we need
#  (alpha,beta) for each step.  Cheapest: keep a running D and update
#  it with a single jac_add(D, G) or jac_add(D, T) per step (O(1) field ops).
# ---------------------------------------------------------------------------

"""
    index_calculus_walk(G, T; fb_size, walk_steps, verbose) -> k or nothing

Walk strategy:
  1. Run `walk_steps` phi-steps.  At each step the running divisor
     D = alpha*G + beta*T is updated by adding G once (alpha += 1),
     keeping computation cheap.  Record every step as a raw relation.
  2. Build factor base from the `fb_size` most-visited curve points.
  3. Extract relations whose 5 atoms all lie in F.
  4. Left-kernel => k.
"""
function index_calculus_walk(G::Div2, T::Div2;
                             fb_size::Int    = 300,
                             walk_steps::Int = 200_000,
                             verbose::Bool   = true)

    all_pts = curve_points()
    t0      = time()

    # ------------------------------------------------------------------
    # Walk: collect raw relations and atom frequencies
    # ------------------------------------------------------------------
    # Each raw relation is stored as:
    #   (alpha, beta, p0, q1, q2, r, s)
    # where the points are NTuple{2,Int} and alpha,beta are Int (mod ell).
    #
    # Running state: D_cur = alpha_cur * G + beta_cur * T
    # We update D by adding G each step (so alpha increments by 1).
    # Periodically we also add T (beta increments by 1).
    # This keeps every update O(1) field ops instead of O(log ell).

    atom_count = Dict{NTuple{2,Int}, Int}()   # frequency counter
    raw_rels   = Vector{Any}()             # (alpha,beta,p0,q1,q2,r,s)

    cur_pt   = all_pts[rand(1:length(all_pts))]
    alpha_cur = rand(1:ell-1)
    beta_cur  = rand(0:ell-1)
    D_cur     = jac_add(jac_mul(G, alpha_cur), jac_mul(T, beta_cur))

    verbose && @printf("Walking %d steps...\n", walk_steps)

    hits = 0
    for step in 1:walk_steps

        # Update D by adding G (cheap: one jac_add, not jac_mul)
        D_cur     = jac_add(D_cur, G)
        alpha_cur = mod(alpha_cur + 1, ell)

        # Every ~sqrt(p) steps, also add T to keep beta non-trivial
        if step % 128 == 0
            D_cur    = jac_add(D_cur, T)
            beta_cur = mod(beta_cur + 1, ell)
        end

        # D must be degree-2 and split over Fp
        pdeg(D_cur.u) != 2 && continue
        rs_D = u2_roots(D_cur.u)
        rs_D === nothing && continue
        x1, x2 = rs_D

        px, py = cur_pt
        (px == x1 || px == x2 || x1 == x2) && continue

        y1 = peval(D_cur.v, x1)
        y2 = peval(D_cur.v, x2)
        eval_f(x1) == fp(y1 * y1) || continue
        eval_f(x2) == fp(y2 * y2) || continue

        phi_c = build_phi(px, py, x1, y1, x2, y2)
        phi_c === nothing && continue
        a, b, c, d = phi_c

        res = phi_residual_points(a, b, c, d, px, x1, x2)
        length(res) < 2 && continue
        R, S = res[1], res[2]

        eval_f(R[1]) == fp(R[2] * R[2]) || continue
        eval_f(S[1]) == fp(S[2] * S[2]) || continue

        hits += 1
        Q1 = (x1, y1);  Q2 = (x2, y2)

        # Count atom frequencies
        for pt in (cur_pt, Q1, Q2, R, S)
            atom_count[pt] = get(atom_count, pt, 0) + 1
        end

        # Store raw relation (alpha_cur and beta_cur at time of this step)
        push!(raw_rels, (alpha_cur, beta_cur, cur_pt, Q1, Q2, R, S))

        # Advance walk: next P0 = R
        cur_pt = R
    end

    verbose && @printf("Walk done: %d valid steps out of %d (%.1fs)\n",
                       hits, walk_steps, time()-t0)
    hits == 0 && error("No valid phi-steps found. Something is wrong.")

    # ------------------------------------------------------------------
    # Build factor base: top fb_size atoms by frequency
    # ------------------------------------------------------------------
    sorted_atoms = sort(collect(atom_count), by=x->-x[2])
    nF           = min(fb_size, length(sorted_atoms))
    fb           = [sorted_atoms[i][1] for i in 1:nF]
    pt2idx       = Dict(pt => i for (i,pt) in enumerate(fb))
    verbose && @printf("Factor base: %d atoms (top freq %d, min freq %d)\n",
                       nF, sorted_atoms[1][2],
                       sorted_atoms[min(nF,end)][2])

    # ------------------------------------------------------------------
    # Extract relations: all 5 atoms must be in F
    # ------------------------------------------------------------------
    # Relation: atom(P0)+atom(Q1)+atom(Q2)+atom(R)+atom(S) = 0  in Cl^0
    # and  atom(Q1)+atom(Q2) = alpha*G + beta*T  (D = alpha*G+beta*T)
    # so   atom(P0)+atom(R)+atom(S) = -alpha*G - beta*T
    # Store alpha_stored=-alpha, beta_stored=-beta, +1 at {P0,R,S} cols.
    #
    # Actually we can use all 5 atoms and set the rhs to 0:
    #   +1 at {P0,Q1,Q2,R,S}, alpha_stored=alpha, beta_stored=beta
    #   and the relation encodes: sum_of_atoms - D = 0
    #   => sum_of_atoms = alpha*G + beta*T
    # Use the 5-atom form so more relations survive the FB filter.

    alpha_vec   = Int[]
    beta_vec    = Int[]
    rel_entries = Vector{Tuple{Int,Int}}[]

    for (al, be, p0, q1, q2, r, s) in raw_rels
        i0 = get(pt2idx, p0, 0);  iq1 = get(pt2idx, q1, 0)
        iq2 = get(pt2idx, q2, 0); ir  = get(pt2idx, r,  0)
        is_ = get(pt2idx, s,  0)
        (i0==0 || iq1==0 || iq2==0 || ir==0 || is_==0) && continue

        # Relation: [P0]+[Q1]+[Q2]+[R]+[S] ~ 5[inf]
        # => atom(P0)+atom(Q1)+atom(Q2)+atom(R)+atom(S) = alpha*G+beta*T
        # (since [Q1]+[Q2] reduced = D = alpha*G+beta*T,
        #  and atom(P0)+atom(R)+atom(S) = -D,
        #  but let's record all 5 atoms explicitly with their signs.)
        #
        # In the matrix: row has +1 at {P0,Q1,Q2,R,S},
        # rhs = alpha*G + beta*T.  The left-kernel γ with γ^T R=0 gives
        # Σγ_i*(alpha_i*G+beta_i*T) = 0  => (Σγ_i*alpha_i)*G = -(Σγ_i*beta_i)*T
        # => k = -(Σγ_i*alpha_i)/(Σγ_i*beta_i).

        push!(alpha_vec, Int(al))
        push!(beta_vec,  Int(be))
        # accumulate coefficients (a point may appear multiple times in one row)
        row = Dict{Int,Int}()
        for idx in (i0, iq1, iq2, ir, is_)
            row[idx] = get(row, idx, 0) + 1
        end
        push!(rel_entries, [(idx2,v) for (idx2,v) in row])
    end

    nrel = length(alpha_vec)
    verbose && @printf("Relations with all atoms in FB: %d / %d\n",
                       nrel, length(raw_rels))
    nrel < nF + 1 && error("Too few relations ($nrel) for FB size $nF. " *
                            "Increase walk_steps or decrease fb_size.")

    # ------------------------------------------------------------------
    # Dense matrix and left kernel
    # ------------------------------------------------------------------
    Rmat = zeros(Int, nrel, nF)
    for i in 1:nrel, (j, v) in rel_entries[i]
        j <= nF && (Rmat[i, j] = mod(Rmat[i, j] + v, ell))
    end

    verbose && println("Left-kernel search over GF($ell)...")
    gamma = left_kernel(Rmat)
    gamma === nothing && error("Kernel not found -- collect more relations")

    Sa = mod(sum(Int128(gamma[i]) * alpha_vec[i] for i in 1:nrel), ell)
    Sb = mod(sum(Int128(gamma[i]) * beta_vec[i]  for i in 1:nrel), ell)
    Sb == 0 && error("beta sum = 0 in kernel vector; retry")

    k  = mod(-Int(Sa) * powermod(Int(Sb), ell - 2, ell), ell)
    ok = jac_mul(G, k) == T

    if verbose
        ok ? println("  check  k = $k   (k*G == T)") :
             println("  FAIL   k = $k")
    end
    ok ? k : nothing
end

# ---------------------------------------------------------------------------
function main2()
    println("="^62)
    println("  trial2: Markov-walk phi-relation index calculus")
    println("  y^2 = x^5+3x^3+2x^2+5x+4  /F_$p,  ell=$ell")
    println("="^62, "\n")

    pts = curve_points()

    println("Finding G of order ell...")
    G = find_ell_generator(pts)
    @printf("G.u = %s\nG.v = %s\n", G.u, G.v)
    @assert jac_isid(jac_mul_raw(G, ell))  "G does not have order ell"
    println("Confirmed: ell*G = identity\n")

    k_true = rand(2:ell-1)
    T      = jac_mul(G, k_true)
    @printf("Secret k = %d\n\n", k_true)

    k_rec = index_calculus_walk(G, T; fb_size=300, walk_steps=200_000, verbose=true)

    println()
    if k_rec !== nothing
        @printf("Recovered k = %-8d  true k = %-8d  match = %s\n",
                k_rec, k_true, k_rec == k_true)
    else
        println("DLP not recovered.")
    end
end

main2()
