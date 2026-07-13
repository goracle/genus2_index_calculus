#!/usr/bin/env julia
################################################################################
#  part_j_worker.jl  --  ONE Part J sandbox (one sample x one target coeff),
#  run as its own OS process.
#
#  Why a subprocess and not a Threads.@spawn task: elim2.jl's own Part H
#  notes already document that two eliminate()/Singular calls running
#  concurrently *in the same process* raced on Singular's global omalloc
#  allocator and crashed (omInsertBinPage/omAllocBinFromFullPage). Julia's
#  Threads.@spawn cannot preempt or truly isolate a blocking Singular C
#  call, so parallel eliminate() calls are only safe as separate OS
#  processes, each with its own address space / allocator state. This
#  script is that isolated unit of work.
#
#  Usage:
#      julia part_j_worker.jl <sample:1|2> <target:U0|U1|V0|V1> <outfile>
#
#  Recomputes symbolic_residual for the requested sample (cheap relative
#  to eliminate()) rather than trying to serialize a live Oscar tower
#  ring element across the process boundary, extracts the one raw
#  coefficient it needs, builds the 5-variable sandbox, runs eliminate(),
#  and saves the resulting polynomial to `outfile` with Oscar's save().
################################################################################

using Oscar

const PHI_GENERAL_SRC = joinpath(@__DIR__, "phi_general", "src")
include(joinpath(PHI_GENERAL_SRC, "trial3_phi_symbolic_unified.jl"))
using .PhiSymbolic

const p = 2371157
const F_POLY_ASC = [2, 1, 0, 0, 0, 1]   # y^2 = x^5 + x + 2, ascending coeffs
F = GF(p)

################################################################################
# CLI args
################################################################################

if length(ARGS) != 3
    error("usage: julia part_j_worker.jl <sample:1|2> <target:U0|U1|V0|V1> <outfile>")
end

sample = parse(Int, ARGS[1])
target = ARGS[2]
outfile = ARGS[3]

sample in (1, 2) || error("sample must be 1 or 2, got $sample")
occursin(r"^[UV][0-9]+$", target) || error("target must look like U0/U1/V0/V1, got $target")

kind = target[1]              # 'U' or 'V'
idx  = parse(Int, target[2:end]) + 1   # 1-based index into u_RS_coeffs / v_RS_coeffs

################################################################################
# Same tower -> ring machinery as elim2.jl (kept verbatim so results match).
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
# Recompute only the sample this worker needs.
################################################################################

if sample == 1
    const_K, const_c = 2, 2
    fixed = Tuple{Int,Int}[]
    u0, u1, v0, v1 = 468873, 956582, 2168176, 2288437
else
    const_K, const_c = 3, 2
    fixed = [(196, 793353)]
    u0, u1, v0, v1 = 2112189, 375309, 801778, 2048138
end

println("[worker sample=$sample target=$target] calling symbolic_residual...")
res = PhiSymbolic.symbolic_residual(const_K, const_c, fixed, u0, u1, v0, v1, F_POLY_ASC, p)

coeffs = kind == 'U' ? res.u_RS_coeffs : res.v_RS_coeffs
idx <= length(coeffs) || error("target $target out of range for sample $sample (have $(length(coeffs)) coeffs)")
raw_coeff = coeffs[idx]

################################################################################
# Build the 5-variable sandbox and eliminate -- identical logic to
# process_sample_1_coeff / process_sample_2_coeff in elim2.jl.
################################################################################

if sample == 1
    R_small, (w1, w2, a1, a2, T) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2", target])
    t_gens = [a1, a2]
    w_gens = [w1, w2]
    curve1 = w1^2 - (a1^5 + a1 + 2)
    curve2 = w2^2 - (a2^5 + a2 + 2)
else
    R_small, (w1, w2, b1, b2, T) = polynomial_ring(F, ["wb1", "wb2", "b1", "b2", target])
    t_gens = [b1, b2]
    w_gens = [w1, w2]
    curve1 = w1^2 - (b1^5 + b1 + 2)
    curve2 = w2^2 - (b2^5 + b2 + 2)
end

num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
h_s = T * den_s - num_s

println("[worker sample=$sample target=$target] running eliminate()...")
t_start = time()
I_small = ideal(R_small, [h_s, curve1, curve2])
eliminated_ideal = eliminate(I_small, [w1, w2])
result = gens(eliminated_ideal)[1]
elapsed = time() - t_start
println("[worker sample=$sample target=$target] eliminate() done in $(round(elapsed, digits=3))s, ",
        "degree=", total_degree(result), " terms=", length(terms(result)))

save(outfile, result)
println("[worker sample=$sample target=$target] saved -> $outfile")
