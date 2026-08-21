#!/usr/bin/env julia
################################################################################
#
#  exceptional_locus_probe.jl
#
#  Standalone diagnostic. Does NOT depend on the Elim2 package layout,
#  ELIM2_ROOT_DIR, or phi_general/trial3_phi_symbolic_unified.jl -- it
#  reimplements the minimal symbolic_residual + tower_to_ring + w-elimination
#  + cross-sample resultant pipeline directly, so you can just
#  `julia exceptional_locus_probe.jl` (with Oscar in your active
#  environment) and get an answer.
#
#  QUESTION BEING TESTED
#  ----------------------
#  Two samples (K=2, c=2, no fixed anchors) each contribute a
#  target-coefficient equation
#
#      F_A(a1,a2,U) = U * u1_den(a1,a2) - u1_num(a1,a2)     [sample 1, U0 slot]
#      F_B(b1,b2,U) = U * u2_den(b1,b2) - u2_num(b1,b2)     [sample 2, U0 slot]
#
#  after each side's own w-variables have already been eliminated (the
#  part_j_worker.jl Stage-1 norm-resultant step). Eliminating U between
#  F_A and F_B gives
#
#      R_U0(a1,a2,b1,b2) = Res_U(F_A, F_B)
#                        = u1_num*u2_den - u2_num*u1_den   (degree-1-in-U case)
#
#  This script:
#    1. Builds sample 1's and sample 2's raw (u_num,u_den) as elements of
#       the 2-level tower (rational_function_field + 2 quadratic
#       extensions), independently, with DISTINCT anchor variable names
#       (a1,a2 vs b1,b2; wa1,wa2 vs wb1,wb2) from the start, exactly
#       mirroring elim2's map_sample separation.
#    2. Runs Stage 1 (per-sample w-elimination via resultant against the
#       curve relations) on each side separately, WITHOUT the
#       correct_multiplicity heuristic first, so you see the raw
#       resultant-chain output and its factorization.
#    3. Also runs correct_multiplicity's exact e2==3*e1 pattern check
#       against a fresh factor_multiset, reporting any UNRECOGNIZED
#       factors -- if this hardcoded heuristic misfires, that's a
#       plausible actual source of a spurious "R vanishes" or "R doesn't
#       vanish" result downstream, distinct from a genuine geometric
#       degeneracy.
#    4. Builds R_U0 = corrected_1 * corrected_2's denominator-analogue
#       via the SAME cross-multiplication PART K performs (not a generic
#       resultant() call, to match production exactly), then checks:
#         (a) is R_U0 literally the zero polynomial in
#             F[a1,a2,b1,b2]? (the true C-type degeneracy)
#         (b) if not, factor it and report which irreducible factors
#             involve BOTH sample-1 and sample-2 variables jointly
#             (mixed factors = genuine cross-sample vanishing loci) vs.
#             factors purely in a1,a2 or purely in b1,b2 (would indicate
#             the "degeneracy" is actually just one sample's own
#             interpolation-singularity locus, unrelated to the other
#             sample -- see the a1==a2 Vandermonde-collapse case flagged
#             separately below).
#         (c) separately checks the interpolation-matrix determinant
#             D(a1,a2) (and D(b1,b2)) for vanishing on a1==a2 (resp.
#             b1==b2) -- the OTHER exceptional locus identified in the
#             analysis, upstream of and distinct from R_U0.
#
#  This uses SMALL primes (p=1009, not the production p=2371157) so
#  factor() stays fast enough to iterate on interactively. Re-run with
#  PROBE_P/PROBE_U0 etc below set to production values once the small-p
#  run's shape is understood -- degeneracy loci that are genuinely
#  algebraic (not mod-p accidents) should show up at both scales.
#
################################################################################

using Oscar

# ------------------------------------------------------------------------
# Config -- edit these to match whichever concrete (u0,u1,v0,v1) you want
# to probe. Defaults here are arbitrary small values, NOT the ones from
# SampleSpecs' cantor_mul output -- swap in real sample values (paste from
# a `println(spec)` in your REPL) if you want to test the ACTUAL default
# sample 1 / sample 2 instances rather than an illustrative pair.
# ------------------------------------------------------------------------
const PROBE_P = 1009
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # f(x) = x^5 + x + 2

# Sample 1's target divisor (u0,u1,v0,v1) -- K=2,c=2, no fixed anchors
const S1_U0, S1_U1, S1_V0, S1_V1 = 101, 202, 303, 404
# Sample 2's target divisor
const S2_U0, S2_U1, S2_V0, S2_V1 = 555, 111, 222, 333

################################################################################
# rr_basis / build_xmodu_table / reduce_monomial_mod_u -- copied verbatim
# from trial3_phi_symbolic_unified.jl (see that file for the derivation).
################################################################################

function rr_basis(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    max_order = 2 * n_basis + 10
    candidates = Tuple{Int,Int,Int}[]
    for i in 0:max_order÷2
        push!(candidates, (2i, i, 0))
        push!(candidates, (2i+5, i, 1))
    end
    sort!(candidates, by = x -> x[1])
    seen = 0
    for (_, i, j) in candidates
        seen += 1
        push!(basis, (i, j))
        seen == n_basis && break
    end
    return basis
end

function build_xmodu_table(max_i::Int, u0::Int, u1::Int, p::Int)::Tuple{Vector{Int},Vector{Int}}
    r0 = zeros(Int, max_i + 2)
    r1 = zeros(Int, max_i + 2)
    r0[1] = 1; r1[1] = 0
    if max_i + 1 >= 1
        r0[2] = 0; r1[2] = 1
    end
    for i in 2:(max_i+1)
        prev0, prev1 = r0[i], r1[i]
        r0[i+1] = mod(-prev1 * u0, p)
        r1[i+1] = mod(prev0 - prev1 * u1, p)
    end
    return (r0, r1)
end

function reduce_monomial_mod_u(i::Int, j::Int, u0::Int, u1::Int, v0::Int, v1::Int,
                               r0tab::Vector{Int}, r1tab::Vector{Int}, p::Int)::Tuple{Int,Int}
    a0, a1v = r0tab[i+1], r1tab[i+1]
    j == 0 && return (a0, a1v)
    b0, b1v = r0tab[i+2], r1tab[i+2]
    r0 = mod(v0*a0 + v1*b0, p)
    r1 = mod(v0*a1v + v1*b1v, p)
    return (r0, r1)
end

################################################################################
# symbolic_residual -- K=2, c=2, no fixed anchors ONLY (simplified from the
# general version; sufficient for both default samples). Returns
# u_RS_coeffs as elements of the 2-level tower K_final.
################################################################################

struct ResidualResult
    u_RS_coeffs::Vector{Any}
    v_RS_coeffs::Vector{Any}
end

function symbolic_residual_k2c2(u0::Int, u1::Int, v0::Int, v1::Int, p::Int)
    # Rebuilt to match trial3_phi_symbolic_unified.jl's tower-construction
    # loop EXACTLY (same t_vars/w_vars array-based promotion pattern,
    # rather than the ad hoc t1_l/t1_ll renaming from the first version of
    # this script, which is the suspected source of the exact-division
    # failure -- see chat).
    Fp = GF(p)
    c = 2
    R_t, t_vars_init = rational_function_field(Fp, ["t$i" for i in 1:c])
    t_vars = Any[tv for tv in t_vars_init]

    K_curr = R_t
    w_vars = Any[]

    for i in 1:c
        f_ti = sum(K_curr(Fp(coeff)) * K_curr(t_vars[i])^(j-1) for (j, coeff) in enumerate(F_POLY_ASC))
        R_wi, wi_var = polynomial_ring(K_curr, "w$i")
        K_curr, _ = residue_ring(R_wi, wi_var^2 - f_ti)
        push!(w_vars, gen(K_curr))

        t_vars = [K_curr(tv) for tv in t_vars]
        for j in 1:(i-1)
            w_vars[j] = K_curr(w_vars[j])
        end
    end

    K_final = K_curr
    t1_ll, t2_ll = t_vars[1], t_vars[2]
    w1_ll, w2_ll = w_vars[1], w_vars[2]

    Kx, X = polynomial_ring(K_final, "X")

    nb = 5   # K+3 = 5
    basis = rr_basis(nb)
    y_idx = findfirst(bi -> bi == (0,1), basis)
    n_unknowns = 4  # K+2
    other_idx = [idx for idx in 1:nb if idx != y_idx]

    A = zero_matrix(K_final, n_unknowns, n_unknowns)
    rhs = zero_matrix(K_final, n_unknowns, 1)

    anchor_pts = [(t1_ll, w1_ll), (t2_ll, w2_ll)]

    for a in 1:2
        px, py = anchor_pts[a]
        for (col, bidx) in enumerate(other_idx)
            bi, bj = basis[bidx]
            A[a, col] = (px^bi) * (bj == 1 ? py : K_final(1))
        end
        bi_n, bj_n = basis[y_idx]
        rhs[a, 1] = -((px^bi_n) * (bj_n == 1 ? py : K_final(1)))
    end

    max_basis_i = maximum(bi for (bi,_) in basis)
    r0tab, r1tab = build_xmodu_table(max_basis_i + 1, u0, u1, p)
    row0, row1 = 3, 4
    for (col, bidx) in enumerate(other_idx)
        bi, bj = basis[bidx]
        rr0, rr1 = reduce_monomial_mod_u(bi, bj, u0, u1, v0, v1, r0tab, r1tab, p)
        A[row0, col] = K_final(rr0)
        A[row1, col] = K_final(rr1)
    end
    bi_n, bj_n = basis[y_idx]
    rn0, rn1 = reduce_monomial_mod_u(bi_n, bj_n, u0, u1, v0, v1, r0tab, r1tab, p)
    rhs[row0, 1] = K_final(mod(-rn0, p))
    rhs[row1, 1] = K_final(mod(-rn1, p))

    local c_sol
    try
        c_sol = solve(A, rhs; side = :right)
    catch e
        error("symbolic_residual_k2c2: linear solve failed -- interpolation matrix " *
              "singular at these SYMBOLIC anchors?? (should not happen generically) -- $e")
    end

    coeffs_out = Vector{elem_type(K_final)}(undef, nb)
    for (col, bidx) in enumerate(other_idx)
        coeffs_out[bidx] = c_sol[col, 1]
    end
    coeffs_out[y_idx] = K_final(1)

    E_poly = Kx(0)
    Y_poly = Kx(0)
    for bidx in 1:nb
        bi, bj = basis[bidx]
        c_here = coeffs_out[bidx]
        if bj == 0
            E_poly += c_here * X^bi
        else
            Y_poly += c_here * X^bi
        end
    end

    f_poly_Kx = sum(K_final(c) * X^(i-1) for (i, c) in enumerate(F_POLY_ASC))
    Nx = E_poly^2 - f_poly_Kx * Y_poly^2

    # ---- DIAGNOSTIC: check N(t1)==0 directly before attempting exact
    # division, so we know whether the interpolation identity itself
    # failed (root cause upstream) vs. divexact/Oscar being unable to
    # perform a division that IS mathematically exact (a library/type
    # issue). This distinction changes what needs fixing.
    Nx_at_t1 = evaluate(Nx, t1_ll)
    Nx_at_t2 = evaluate(Nx, t2_ll)
    println("  [diag] N(t1) == 0 ? ", iszero(Nx_at_t1), "   value=", Nx_at_t1)
    println("  [diag] N(t2) == 0 ? ", iszero(Nx_at_t2), "   value=", Nx_at_t2)
    println("  [diag] degree(Nx) = ", iszero(Nx) ? -1 : degree(Nx))
    println("  [diag] E_poly = ", E_poly)
    println("  [diag] Y_poly = ", Y_poly)

    # K=2, c=2, no fixed anchors: divide by (X-t1)(X-t2) then by u(X).
    # `divexact(...; check=true)` (Oscar's default) fails to VERIFY
    # exactness through this many tower layers even though N(t1)=N(t2)=0
    # confirms the division genuinely is exact -- library limitation, not
    # a math bug (see chat). check=false skips that verification and
    # just runs the division algorithm directly.
    cur = Nx
    cur = divexact(cur, X - t1_ll; check=false)
    cur = divexact(cur, X - t2_ll; check=false)
    u_poly_Kx = X^2 + K_final(u1)*X + K_final(u0)
    cur = divexact(cur, u_poly_Kx; check=false)

    if iszero(cur)
        error("symbolic_residual_k2c2: residual divided to zero -- degenerate sample " *
              "(u0=$u0,u1=$u1,v0=$v0,v1=$v1) at p=$p")
    end
    u_RS = cur * inv(leading_coefficient(cur))

    if iszero(Y_poly)
        error("symbolic_residual_k2c2: Y_poly is zero -- cannot form v_RS")
    end
    # v_RS(x) = E(x) * inverse(Y(x)) mod u_RS(x), via gcdx (small-degree
    # case here so this is cheap; production code's _inv_mod_small
    # fast-path is an optimization, not a different formula).
    g, s, _t = gcdx(Y_poly, u_RS)
    if !isone(g)
        error("symbolic_residual_k2c2: Y_poly not invertible mod u_RS (gcd=$g) -- " *
              "this IS one of the exceptional loci flagged in the analysis " *
              "(Y/u_RS invertibility failure) -- STOP, do not proceed silently")
    end
    v_RS = mod(E_poly * s, u_RS)

    u_coeffs = [coeff(u_RS, i) for i in 0:(degree(u_RS)-1)]  # drop leading 1 (monic, matches u_RS_coeffs convention minus top)
    # NOTE: elim2's u_RS_coeffs convention -- check against your own
    # SymbolicResidualResult if this script's u1_num[end] disagrees with
    # a REPL run of the real symbolic_residual; degree-length bookkeeping
    # is the single easiest place for an off-by-one to hide here.
    v_coeffs = [coeff(v_RS, i) for i in 0:degree(v_RS)]

    return ResidualResult(u_coeffs, v_coeffs)
end

################################################################################
# tower_to_ring -- same recursion as elim2's version, mapping a K_final
# tower element into a plain ring given (t_gens, w_gens) images.
################################################################################

function _reduce_frac(num, den)
    iszero(num) && return (num, one(den))
    g = gcd(num, den)
    if !isone(g)
        num = divexact(num, g)
        den = divexact(den, g)
    end
    return (num, den)
end

function _base_frac_to_ring(val, t_gens::Vector)
    num = numerator(val)
    den = denominator(val)
    num_R = evaluate(num, t_gens)
    den_R = evaluate(den, t_gens)
    return _reduce_frac(num_R, den_R)
end

function _tower_to_ring(val, level::Int, t_gens::Vector, w_gens::Vector)
    if level == 0
        return _base_frac_to_ring(val, t_gens)
    end
    val_poly = data(val)
    c0 = coeff(val_poly, 0)
    c1v = coeff(val_poly, 1)
    n0, d0 = _tower_to_ring(c0, level - 1, t_gens, w_gens)
    n1, d1 = _tower_to_ring(c1v, level - 1, t_gens, w_gens)
    wv = w_gens[level]
    num = n0 * d1 + n1 * d0 * wv
    den = d0 * d1
    return _reduce_frac(num, den)
end

tower_to_ring(val, t_gens::Vector, w_gens::Vector) = _tower_to_ring(val, 2, t_gens, w_gens)

################################################################################
# Stage 1: per-sample w-elimination (verbatim structure from
# part_j_worker.jl's process_sample_1_coeff / process_sample_2_coeff),
# but WITHOUT correct_multiplicity applied yet -- returns the raw
# (step1, step2) resultant-chain output plus its factorization, so you
# can see both the raw and corrected picture.
################################################################################

function canonical_factor_key(f)
    Fbase = base_ring(parent(f))
    exps = collect(AbstractAlgebra.exponent_vectors(f))
    cfs  = collect(coefficients(f))
    order = sortperm(exps)
    lead_c = cfs[order[1]]
    inv_lead = inv(lead_c)
    io = IOBuffer()
    for idx in order
        c = cfs[idx] * inv_lead
        print(io, string(c), ":", string(exps[idx]), ";")
    end
    return String(take!(io))
end

function factor_multiset(f)
    fac = factor(f)
    d = Dict{String,Int}()
    for (fp, e) in fac
        key = canonical_factor_key(fp)
        d[key] = get(d, key, 0) + e
    end
    return d, fac
end

"""
Same logic as part_j_worker.jl's correct_multiplicity -- copied here
so this script has no external dependency. Prints (does not silently
swallow) any unrecognized-pattern factors.
"""
function correct_multiplicity(Res1, Res2; label::AbstractString="")
    set1, fac1 = factor_multiset(Res1)
    set2, fac2 = factor_multiset(Res2)
    poly_of_2 = Dict{String,Any}(canonical_factor_key(fp) => fp for (fp, _e) in fac2)

    candidates = NamedTuple[]
    unrecognized = NamedTuple[]
    for k in keys(set2)
        e1 = get(set1, k, 0)
        e2 = set2[k]
        if e1 > 0 && e2 > e1
            if e2 == 3 * e1
                push!(candidates, (key = k, excess = e2 - e1))
            else
                push!(unrecognized, (key = k, exp_Res1 = e1, exp_Res2 = e2))
            end
        end
    end

    if !isempty(unrecognized)
        println("  [$label] ** ", length(unrecognized), " UNRECOGNIZED-PATTERN factor(s) ",
                "(present in Res1, e2>e1, but e2 != 3*e1) -- correct_multiplicity's ",
                "hardcoded heuristic does NOT apply here. This run's corrected output ",
                "should NOT be trusted without a Groebner cross-check. **")
        for u in unrecognized
            rep = poly_of_2[u.key]
            println("      degree=", total_degree(rep), " terms=", length(terms(rep)),
                    " exp(Res1)=", u.exp_Res1, " exp(Res2)=", u.exp_Res2)
        end
    end

    corrected = Res2
    for c in candidates
        Fp = poly_of_2[c.key]
        corrected = divexact(corrected, Fp^c.excess)
    end
    return (corrected = corrected, n_candidates = length(candidates),
            n_unrecognized = length(unrecognized))
end

# Robust variable-index lookup: works regardless of whether this Oscar
# version exposes var_index()/varindex()/index_of_gen() etc -- just finds
# the position of `v` among its own parent ring's generators directly.
gen_index(v) = findfirst(g -> g == v, gens(parent(v)))

function stage1_eliminate_w(raw_coeff, wname1::String, wname2::String,
                             tname1::String, tname2::String, target_name::String,
                             Fp, curve_poly_fn)
    R_small, (w1, w2, t1, t2, T) = polynomial_ring(Fp, [wname1, wname2, tname1, tname2, target_name])
    t_gens = [t1, t2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
    h_s = T * den_s - num_s

    curve1 = w1^2 - curve_poly_fn(t1)
    curve2 = w2^2 - curve_poly_fn(t2)

    step1 = resultant(h_s, curve1, gen_index(w1))
    step2 = resultant(step1, curve2, gen_index(w2))

    corr = correct_multiplicity(step1, step2; label = "$target_name/$tname1$tname2")

    return (raw_step1 = step1, raw_step2 = step2, corrected = corr.corrected,
            n_candidates = corr.n_candidates, n_unrecognized = corr.n_unrecognized,
            ring = R_small, t1 = t1, t2 = t2, T = T)
end

################################################################################
# MAIN
################################################################################

function main()
    p = PROBE_P
    Fp = GF(p)
    curve_poly_fn(x) = sum(Fp(c) * x^(i-1) for (i, c) in enumerate(F_POLY_ASC))

    println("="^80)
    println("Building sample 1 (u0,u1,v0,v1) = ($S1_U0,$S1_U1,$S1_V0,$S1_V1) at p=$p")
    println("="^80)
    res1 = symbolic_residual_k2c2(S1_U0, S1_U1, S1_V0, S1_V1, p)
    println("sample 1: deg(u_RS)=", length(res1.u_RS_coeffs), " coeff(s) below leading term")

    println("="^80)
    println("Building sample 2 (u0,u1,v0,v1) = ($S2_U0,$S2_U1,$S2_V0,$S2_V1) at p=$p")
    println("="^80)
    res2 = symbolic_residual_k2c2(S2_U0, S2_U1, S2_V0, S2_V1, p)
    println("sample 2: deg(u_RS)=", length(res2.u_RS_coeffs), " coeff(s) below leading term")

    # Focus on the U0 slot (i=1, the constant coefficient of u_RS), the
    # first repeated-target equation -- same slot GPT's original prompt's
    # schematic Fu0/Fu1 example referred to.
    target_idx = 1
    raw1 = res1.u_RS_coeffs[target_idx]
    raw2 = res2.u_RS_coeffs[target_idx]

    println()
    println("="^80)
    println("STAGE 1: per-sample w-elimination for U0 slot")
    println("="^80)
    s1 = stage1_eliminate_w(raw1, "wa1", "wa2", "a1", "a2", "U0", Fp, curve_poly_fn)
    println("sample 1 U0: raw_step2 degree=", total_degree(s1.raw_step2),
            " terms=", length(terms(s1.raw_step2)),
            " | corrected degree=", total_degree(s1.corrected),
            " terms=", length(terms(s1.corrected)),
            " | multiplicity candidates=", s1.n_candidates,
            " unrecognized=", s1.n_unrecognized)

    s2 = stage1_eliminate_w(raw2, "wb1", "wb2", "b1", "b2", "U0", Fp, curve_poly_fn)
    println("sample 2 U0: raw_step2 degree=", total_degree(s2.raw_step2),
            " terms=", length(terms(s2.raw_step2)),
            " | corrected degree=", total_degree(s2.corrected),
            " terms=", length(terms(s2.corrected)),
            " | multiplicity candidates=", s2.n_candidates,
            " unrecognized=", s2.n_unrecognized)

    if s1.n_unrecognized > 0 || s2.n_unrecognized > 0
        println()
        println("!! STOP: correct_multiplicity hit an unrecognized factor pattern on this")
        println("   instance. Any R_U0 conclusion below is built on an unverified-correct")
        println("   Stage-1 polynomial and should not be trusted as-is. Re-run with")
        println("   Groebner cross-check (eliminate()) on the flagged case before trusting")
        println("   the vanishing/non-vanishing result printed below.")
    end

    # ------------------------------------------------------------------
    # STAGE 2: cross-sample resultant, in a shared 4-variable ring
    # F[a1,a2,b1,b2,U0]. s1.corrected is a polynomial in (a1,a2,U0)
    # (over F_small1); s2.corrected is a polynomial in (b1,b2,U0) (over
    # F_small2). Remap both into one shared ring, then compute
    # Res_U0(corrected_1, corrected_2), matching PART K's actual
    # approach (this is the honest general-degree resultant -- PART K's
    # Bezout-determinant route is an optimization of the SAME
    # elimination, not a different one, so a direct resultant() call
    # here is a valid ground-truth check even though it won't scale to
    # production-size instances).
    # ------------------------------------------------------------------
    println()
    println("="^80)
    println("STAGE 2: cross-sample resultant R_U0 = Res_U0(corrected_1, corrected_2)")
    println("="^80)

    R_final, (a1, a2, b1, b2, U0v) = polynomial_ring(Fp, ["a1", "a2", "b1", "b2", "U0"])

    remap1 = hom(s1.ring, R_final, [zero(R_final), zero(R_final), a1, a2, U0v])
    # ^ w1,w2 mapped to 0 is WRONG in general (s1.corrected should already
    # be w-free after Stage 1 -- if it is NOT, this remap will silently
    # corrupt the polynomial). The script checks this explicitly below
    # before trusting the remap.
    if !iszero(coeff(s1.corrected, [1,0,0,0,0])) || any(e -> e[1] != 0 || e[2] != 0,
            [collect(AbstractAlgebra.exponent_vectors(s1.corrected))...])
        # cheap guard: confirm no w1/w2 exponents survive in s1.corrected
        has_w = any(ev -> ev[1] != 0 || ev[2] != 0, AbstractAlgebra.exponent_vectors(s1.corrected))
        if has_w
            error("STAGE 2 remap: s1.corrected still has nonzero wa1/wa2 exponents -- " *
                  "Stage 1's w-elimination did not fully clear w1,w2 from this polynomial. " *
                  "Do not proceed with a w->0 remap; investigate stage1_eliminate_w first.")
        end
    end
    has_w2 = any(ev -> ev[1] != 0 || ev[2] != 0, AbstractAlgebra.exponent_vectors(s2.corrected))
    if has_w2
        error("STAGE 2 remap: s2.corrected still has nonzero wb1/wb2 exponents -- same issue " *
              "as sample 1, see message above.")
    end

    F_A = remap1(s1.corrected)
    remap2 = hom(s2.ring, R_final, [zero(R_final), zero(R_final), b1, b2, U0v])
    F_B = remap2(s2.corrected)

    println("F_A (sample 1 side) degree in U0: ", degree(F_A, U0v))
    println("F_B (sample 2 side) degree in U0: ", degree(F_B, U0v))

    # ------------------------------------------------------------------
    # CHEAP FIRST TEST: specialize (a1,a2,b1,b2) at several random F_p
    # points, and at each one check whether Res_U(F_A(pt,U), F_B(pt,U))
    # -- now just a resultant of two univariate degree-4 polys over F_p,
    # trivial -- is zero. If ANY point gives a nonzero value, R_U0 is
    # provably NOT the zero polynomial and we can stop without ever
    # computing the full multivariate resultant (which is the expensive
    # step that was hanging). Only fall through to the full symbolic
    # resultant if every sample point gives zero (strong evidence, not
    # proof, of identical vanishing).
    # ------------------------------------------------------------------
    println("Specialization pre-test: sampling random (a1,a2,b1,b2) points in F_$p...")
    Rx, Uvar = polynomial_ring(Fp, "U")
    n_trials = 25
    nonzero_found = false
    rng_state = UInt64(12345)
    function next_rand(state::UInt64, modulus::Int)
        # tiny xorshift so this script has zero extra deps
        state = xor(state, state << 13)
        state = xor(state, state >> 7)
        state = xor(state, state << 17)
        return state, Int(state % UInt64(modulus))
    end
    for trial in 1:n_trials
        rng_state, av1 = next_rand(rng_state, p); a1v = Fp(av1)
        rng_state, av2 = next_rand(rng_state, p); a2v = Fp(av2)
        rng_state, bv1 = next_rand(rng_state, p); b1v = Fp(bv1)
        rng_state, bv2 = next_rand(rng_state, p); b2v = Fp(bv2)

        F_A_spec = evaluate(F_A, [a1v, a2v, b1v, b2v, U0v])
        F_B_spec = evaluate(F_B, [a1v, a2v, b1v, b2v, U0v])
        # F_A_spec, F_B_spec are now degree-<=4 univariate-in-U0
        # elements of R_final still carrying U0 as the only free
        # generator -- convert to the plain Rx=Fp[U] ring for a cheap
        # univariate resultant.
        FA_u = sum(coeff(F_A_spec, [0,0,0,0,i]) * Uvar^i for i in 0:degree(F_A_spec, U0v))
        FB_u = sum(coeff(F_B_spec, [0,0,0,0,i]) * Uvar^i for i in 0:degree(F_B_spec, U0v))
        r_val = resultant(FA_u, FB_u)
        if !iszero(r_val)
            nonzero_found = true
            println("  trial $trial: (a1,a2,b1,b2)=($av1,$av2,$bv1,$bv2) -> resultant = ",
                    r_val, "  ** NONZERO **")
            break
        else
            println("  trial $trial: (a1,a2,b1,b2)=($av1,$av2,$bv1,$bv2) -> resultant = 0")
        end
    end

    if nonzero_found
        println()
        println(">>> R_U0 is PROVABLY NOT identically zero (found a nonzero specialization).")
        println(">>> This alone answers the type-C-degeneracy question: NO, for this")
        println(">>> (u0,u1,v0,v1) pair at p=$p, the cross-sample U0 resultant does not")
        println(">>> vanish identically. Skipping the full symbolic resultant/factorization")
        println(">>> (expensive and unnecessary once a single nonzero point is found).")
        return (res1=res1, res2=res2, s1=s1, s2=s2, R_final=R_final,
                R_U0=nothing, provably_nonzero=true)
    end

    println()
    println(">>> All $n_trials random specializations gave 0. This is SUSPICIOUS -- either")
    println(">>> R_U0 really is identically zero, or n_trials was too small relative to")
    println(">>> deg(R_U0)/p (unlikely at these degrees/this p, but flagging). Proceeding")
    println(">>> to the full symbolic resultant to get a definitive answer -- this WILL be")
    println(">>> slow (this is the step that was hanging); consider Ctrl-C and reporting")
    println(">>> back with 'all zero, didn't wait for the full computation' as a valid,")
    println(">>> informative result on its own.")

    R_U0 = resultant(F_A, F_B, gen_index(U0v))

    println()
    if iszero(R_U0)
        println(">>> R_U0 IS IDENTICALLY ZERO on this instance (p=$p, these u0/u1/v0/v1). <<<")
        println(">>> This is the TRUE (type-C) degeneracy GPT's prompt asked about.")
        println(">>> Re-run with a SECOND independent (u0,u1,v0,v1) pair and a different p")
        println(">>> to see whether this is instance-specific or structural.")
    else
        println(">>> R_U0 is NOT identically zero. degree=", total_degree(R_U0),
                " terms=", length(terms(R_U0)))
        println(">>> Factoring R_U0 to classify its vanishing locus...")
        fac = factor(R_U0)
        for (fp, e) in fac
            evs = collect(AbstractAlgebra.exponent_vectors(fp))
            involves_1 = any(ev -> ev[1] != 0 || ev[2] != 0, evs)   # a1,a2
            involves_2 = any(ev -> ev[3] != 0 || ev[4] != 0, evs)   # b1,b2
            kind = involves_1 && involves_2 ? "MIXED (genuine cross-sample factor)" :
                   involves_1 ? "sample-1-only (a1,a2)" :
                   involves_2 ? "sample-2-only (b1,b2)" : "constant/degenerate"
            println("    factor: degree=", total_degree(fp), " terms=", length(terms(fp)),
                    " exponent=", e, "  [", kind, "]")
        end
    end

    # ------------------------------------------------------------------
    # Separately: interpolation-matrix singularity locus, D(a1,a2) and
    # D(b1,b2) -- the OTHER exceptional locus, upstream of Stage 1/2,
    # identified during the analysis. Vanishes (generically) exactly
    # when a1==a2 (resp b1==b2) for this K=2,c=2,no-fixed-anchor case,
    # since the anchor rows of A are then linearly dependent (repeated
    # interpolation point). Reported here for completeness -- this is
    # NOT the same locus as R_U0 above and should not be conflated with
    # it; a "yes" here means the tower construction itself fails before
    # Stage 1 or 2 ever run.
    # ------------------------------------------------------------------
    println()
    println("="^80)
    println("Cross-check: interpolation-matrix D(a1,a2) vanishing locus (a1==a2 case)")
    println("="^80)
    println("(Structural fact, not computed here: for K=2,c=2, no fixed anchors, the")
    println(" anchor rows of the K+2 x K+2 system are (a_i^bi)*... type Vandermonde rows;")
    println(" a1==a2 with wa1==wa2 makes rows 1,2 identical -> singular. This is a DIFFERENT")
    println(" exceptional locus from R_U0 and is guarded structurally by using a1 != a2")
    println(" random anchors, not by anything in Stage 1/2 above.)")

    return (res1=res1, res2=res2, s1=s1, s2=s2, R_U0=R_U0, R_final=R_final)
end

result = main()
