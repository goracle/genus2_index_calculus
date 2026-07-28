################################################################################
#
#  00_sample_specs.jl -- part of the Elim2 package (src/Elim2.jl includes
#  this file FIRST, before any other submodule -- see src/Elim2.jl for the
#  package-level overview and full include order).
#
#  Module: SampleSpecs
#
#  Single source of truth for K, c, fixed anchors, and u0/u1/v0/v1 for
#  BOTH samples. Every other file that needs these values -- Elim2Main
#  (01_elim2_main.jl), NormElimDiag (02_norm_elim_diag.jl), and the
#  standalone part_j_worker.jl subprocess -- imports SampleSpec /
#  default_sample1 / default_sample2 from here instead of keeping its own
#  copy.
#
#  Deliberately has ZERO non-stdlib dependencies (no `using Oscar`, nothing)
#  so that part_j_worker.jl -- which must NOT pull in Oscar before it needs
#  to -- can `include()` this file directly and cheaply.
#
################################################################################
module SampleSpecs

using Random

export SampleSpec, default_sample1, default_sample2, generate_sample_spec

const DEFAULT_SEED = 2026
const DEFAULT_P = 2371157

################################################################################
# Struct: SampleSpec -- K, c, fixed anchors, and u0/u1/v0/v1 for one sample.
################################################################################
struct SampleSpec
    K::Int
    c::Int
    fixed::Vector{Tuple{Int,Int}}
    u0::Int
    u1::Int
    v0::Int
    v1::Int
end

# -----------------------------------------------------------------------------
# Pure Julia F_p[x] polynomial and Cantor arithmetic helpers
# -----------------------------------------------------------------------------

function p_trim(a::Vector{Int})
    d = length(a)
    while d > 1 && a[d] == 0
        d -= 1
    end
    return a[1:d]
end

function p_add(a::Vector{Int}, b::Vector{Int}, p::Int)
    n = max(length(a), length(b))
    res = zeros(Int, n)
    for i in 1:n
        va = i <= length(a) ? a[i] : 0
        vb = i <= length(b) ? b[i] : 0
        res[i] = mod(va + vb, p)
    end
    return p_trim(res)
end

function p_sub(a::Vector{Int}, b::Vector{Int}, p::Int)
    n = max(length(a), length(b))
    res = zeros(Int, n)
    for i in 1:n
        va = i <= length(a) ? a[i] : 0
        vb = i <= length(b) ? b[i] : 0
        res[i] = mod(va - vb, p)
    end
    return p_trim(res)
end

function p_mul(a::Vector{Int}, b::Vector{Int}, p::Int)
    if (length(a) == 1 && a[1] == 0) || (length(b) == 1 && b[1] == 0)
        return Int[0]
    end
    res = zeros(Int, length(a) + length(b) - 1)
    for i in 1:length(a), j in 1:length(b)
        res[i+j-1] = mod(res[i+j-1] + a[i] * b[j], p)
    end
    return p_trim(res)
end

function p_scale(a::Vector{Int}, c::Int, p::Int)
    c_mod = mod(c, p)
    if c_mod == 0
        return Int[0]
    end
    return p_trim(Int[mod(x * c_mod, p) for x in a])
end

function p_divrem(a::Vector{Int}, b::Vector{Int}, p::Int)
    a = p_trim(a)
    b = p_trim(b)
    if length(b) == 1 && b[1] == 0
        throw(DivideError())
    end
    deg_a = length(a) - 1
    deg_b = length(b) - 1
    if deg_a < deg_b
        return Int[0], a
    end

    rem_p = copy(a)
    q = zeros(Int, deg_a - deg_b + 1)
    inv_b_lead = invmod(b[end], p)

    for i in (deg_a - deg_b):-1:0
        cur_deg = i + deg_b
        coeff_val = mod(rem_p[cur_deg + 1] * inv_b_lead, p)
        q[i + 1] = coeff_val
        if coeff_val != 0
            for j in 0:deg_b
                rem_p[i + j + 1] = mod(rem_p[i + j + 1] - coeff_val * b[j + 1], p)
            end
        end
    end
    return p_trim(q), p_trim(rem_p)
end

function p_gcdx(a::Vector{Int}, b::Vector{Int}, p::Int)
    a = p_trim(a)
    b = p_trim(b)
    r0, r1 = a, b
    s0, s1 = Int[1], Int[0]
    t0, t1 = Int[0], Int[1]

    while !(length(r1) == 1 && r1[1] == 0)
        q, r2 = p_divrem(r0, r1, p)
        s2 = p_sub(s0, p_mul(q, s1, p), p)
        t2 = p_sub(t0, p_mul(q, t1, p), p)
        r0, r1 = r1, r2
        s0, s1 = s1, s2
        t0, t1 = t1, t2
    end

    lead = r0[end]
    if lead != 0 && lead != 1
        inv_lead = invmod(lead, p)
        r0 = p_scale(r0, inv_lead, p)
        s0 = p_scale(s0, inv_lead, p)
        t0 = p_scale(t0, inv_lead, p)
    end
    return r0, s0, t0
end

function cantor_add(u1::Vector{Int}, v1::Vector{Int}, u2::Vector{Int}, v2::Vector{Int}, f::Vector{Int}, p::Int)
    g1, e1, e2 = p_gcdx(u1, u2, p)
    v_sum = p_add(v1, v2, p)
    g, c1, c2 = p_gcdx(g1, v_sum, p)

    s1 = p_mul(c1, e1, p)
    s2 = p_mul(c1, e2, p)
    s3 = c2

    u1u2 = p_mul(u1, u2, p)
    g2 = p_mul(g, g, p)
    u, _ = p_divrem(u1u2, g2, p)

    term1 = p_mul(p_mul(s1, u1, p), v2, p)
    term2 = p_mul(p_mul(s2, u2, p), v1, p)
    term3 = p_mul(s3, p_add(p_mul(v1, v2, p), f, p), p)
    num = p_add(p_add(term1, term2, p), term3, p)
    v_tmp, _ = p_divrem(num, g, p)
    _, v = p_divrem(v_tmp, u, p)

    while length(u) - 1 > 2
        v2_poly = p_mul(v, v, p)
        num_next = p_sub(f, v2_poly, p)
        u_next, _ = p_divrem(num_next, u, p)

        if length(u_next) == 1 && u_next[1] == 0
            throw(ErrorException("Cantor reduction produced zero polynomial u_next"))
        end

        inv_lead = invmod(u_next[end], p)
        u_next = p_scale(u_next, inv_lead, p)

        neg_v = p_scale(v, -1, p)
        _, v_next = p_divrem(neg_v, u_next, p)

        u, v = u_next, v_next
    end

    return u, v
end

function cantor_mul(u::Vector{Int}, v::Vector{Int}, n::Int, f::Vector{Int}, p::Int)
    if n <= 0
        throw(DomainError(n, "Scalar n must be a positive integer"))
    end

    curr_u, curr_v = u, v
    res_u, res_v = Int[], Int[]
    for b in reverse(digits(n, base=2))
        if !isempty(res_u)
            res_u, res_v = cantor_add(res_u, res_v, res_u, res_v, f, p)
        end
        if b == 1
            if isempty(res_u)
                res_u, res_v = curr_u, curr_v
            else
                res_u, res_v = cantor_add(res_u, res_v, curr_u, curr_v, f, p)
            end
        end
    end
    return res_u, res_v
end

function extract_coords(u::Vector{Int}, v::Vector{Int})
    if length(u) - 1 != 2
        throw(ErrorException("Divisor u(x) degree is $(length(u)-1), expected degree 2"))
    end
    u0 = u[1]
    u1 = u[2]
    v0 = length(v) >= 1 ? v[1] : 0
    v1 = length(v) >= 2 ? v[2] : 0
    return u0, u1, v0, v1
end

# -----------------------------------------------------------------------------
# Anchor Generator Function
# -----------------------------------------------------------------------------

"""
    generate_sample_spec(sample_idx::Int; seed::Int=DEFAULT_SEED, p::Int=DEFAULT_P)

Generates a valid `SampleSpec` for \$K=2, c=2\$ on \$y^2 = x^5 + x + 2 \\pmod p\$
by computing \\alpha \\cdot G using standard scalar multiplication.
"""
function generate_sample_spec(sample_idx::Int; seed::Int = DEFAULT_SEED, p::Int = DEFAULT_P)
    f = Int[2, 1, 0, 0, 0, 1]              # f(x) = x^5 + x + 2
    u_G = Int[2307335, 2061398, 1]         # Generator G u-poly
    v_G = Int[1348746, 397106]             # Generator G v-poly

    rng = Random.MersenneTwister(seed + sample_idx * 1000)
    alpha = rand(rng, 2:100000)

    u_s, v_s = cantor_mul(u_G, v_G, alpha, f, p)
    u0, u1, v0, v1 = extract_coords(u_s, v_s)

    return SampleSpec(2, 2, Tuple{Int,Int}[], u0, u1, v0, v1)
end

"""
    default_sample1(; seed::Int=DEFAULT_SEED)

Sample 1: K=2, c=2, automatically generated for a fixed seed.
"""
function default_sample1(; seed::Int = DEFAULT_SEED)
    spec = generate_sample_spec(1; seed = seed)
    @assert spec.K == 2 && spec.c == 2 "default_sample1(): expected K=2,c=2, got K=$(spec.K),c=$(spec.c)"
    return spec
end

"""
    default_sample2(; seed::Int=DEFAULT_SEED)

Sample 2: K=2, c=2, automatically generated for a fixed seed.
"""
function default_sample2(; seed::Int = DEFAULT_SEED)
    spec = generate_sample_spec(2; seed = seed)
    @assert spec.K == 2 && spec.c == 2 "default_sample2(): expected K=2,c=2, got K=$(spec.K),c=$(spec.c)"
    return spec
end

end # module SampleSpecs
