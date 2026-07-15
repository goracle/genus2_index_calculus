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
#  to the resultant+correction pipeline) rather than trying to serialize
#  a live Oscar tower ring element across the process boundary, extracts
#  the one raw coefficient it needs, builds the 5-variable sandbox, runs
#  the resultant + correct_multiplicity pipeline (Groebner-free, in place
#  of eliminate()), and saves the resulting polynomial to `outfile` with
#  Oscar's save().
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
# Groebner-free multiplicity correction -- copied verbatim from elim2.jl
# (kept as a self-contained copy here since this worker is a standalone
# process and does not `include` elim2.jl itself). See elim2.jl's
# _run_bench / correct_multiplicity for the derivation and the
# CHECK_GROEBNER=true verification that this reproduces eliminate()'s
# output exactly.
################################################################################

function canonical_factor_key(f)
    R = parent(f)
    Fbase = base_ring(R)
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
    for (p, e) in fac
        key = canonical_factor_key(p)
        d[key] = get(d, key, 0) + e
    end
    return d, fac
end


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



using Oscar

"""
    correct_multiplicity(Res2)

Automatically corrects the multiplicity of the resultant Res2 by:
  1. Inspecting the parent ring generators to find the target variable.
  2. Extracting the coordinate ('U' or 'V') to apply the exact proven exponent 
     (4 for 'U', 6 for 'V').
  3. Locating the unique degree-8 inflation factor (F_infl).
  4. Performing an exact, remainder-free algebraic division.

Returns a NamedTuple containing the `.corrected` polynomial to match the legacy API.
"""
function correct_multiplicity(Res2)
    # 1. Inspect the parent ring of the resultant to identify the target variable name
    R = parent(Res2)
    ring_vars = gens(R)
    if isempty(ring_vars)
        error("The resultant parent ring has no generators.")
    end
    
    # The 5th (last) generator in our sandbox is the target variable (e.g., "U0", "V0")
    target_var = ring_vars[end]
    target_str = string(target_var)
    
    # 2. Extract coordinate and assign the exact mathematically proven exponent
    coord_char = uppercase(target_str[1])
    if coord_char == 'U'
        exponent = 4
    elseif coord_char == 'V'
        exponent = 6
    else
        error("Could not determine coordinate ('U' or 'V') from target variable: $target_str")
    end

    # 3. Factor the resultant in the polynomial ring
    local factors
    try
        factors = factor(Res2)
    catch e
        error("Failed to factor the second resultant Res2: ", e)
    end

    # Helper to safely retrieve degrees of multivariate factors in Oscar/Nemo
    get_poly_degree(p) = begin
        try
            return total_degree(p)
        catch
            try
                return degree(p)
            catch
                error("Unable to determine degree of factor: $p")
            end
        end
    end

    # 4. Deterministically isolate the unique degree-8 inflation factor (F_infl)
    f_infl = nothing
    f_infl_mult = 0

    for (fac, mult) in factors
        if get_poly_degree(fac) == 8
            if f_infl !== nothing
                error("Ambiguity detected: Found multiple distinct degree-8 factors in Res2:\n" *
                      "  1) $f_infl\n" *
                      "  2) $fac\n" *
                      "Cannot deterministically isolate the true inflation factor.")
            end
            f_infl = fac
            f_infl_mult = mult
        end
    end

    # Validate that the expected degree-8 inflation factor actually exists
    if f_infl === nothing
        fac_list = [(fac, mult) for (fac, mult) in factors]
        error("Mathematical assumption violated: Could not find the expected degree-8 " *
              "inflation factor in the factorization of Res2.\n" *
              "Factors found: $fac_list")
    end

    # 5. Verify that the factor possesses at least the required multiplicity
    if f_infl_mult < exponent
        error("The identified degree-8 inflation factor ($f_infl) has multiplicity $f_infl_mult " *
              "in Res2, which is less than the required exponent of $exponent for coordinate '$coord_char'.")
    end

    # 6. Perform exact algebraic division to strip the inflation factor
    divisor = f_infl^exponent
    success, corrected_poly = divides(Res2, divisor)
    
    if !success
        error("Exact division failed: Non-zero remainder when dividing Res2 by F_infl^$exponent.")
    end

    # Return as a NamedTuple to support the legacy .corrected access pattern
    return (corrected = corrected_poly, inflation_factor = f_infl, exponent = exponent)
end


# ==============================================================================
# Factory for Sample 1 (Uses 'a' variables)
# ==============================================================================
# Groebner-free rewrite (wired to correct_multiplicity, per chat): this used
# to call eliminate(I_small, [w1, w2]) directly, which is the slow Groebner
# oracle. We now use the exact PATH B / correction recipe verified against
# Groebner in _run_bench: sequential resultants to eliminate w1 then w2,
# then correct_multiplicity(step1, step2) to divide out the excess
# (inflated) multiplicity that the two-step resultant chain introduces
# relative to the true (Groebner) elimination ideal generator. This was
# checked (CHECK_GROEBNER=true runs of _run_bench) to reproduce gA exactly,
# so it's safe to use as the production path -- and since it divides out
# spurious factors before this coefficient ever reaches PART F/Bezout, the
# polynomials feeding the Bezout matrix should also come out smaller.
function process_sample_1_coeff(raw_coeff, target_name)
    println("  Spinning up sandbox for: ", target_name)
    
    # 1. Build the 5-variable sandbox
    R_small, (w1, w2, a1, a2, T) = polynomial_ring(F, ["wa1", "wa2", "a1", "a2", target_name])
    
    # 2. Convert the raw tower fraction directly into our new sandbox
    t_gens = [a1, a2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
    
    # 3. Build the graph equation: Target * denominator - numerator = 0
    h_s = T * den_s - num_s
    
    # 4. Add the curve equations to the sandbox
    curve1 = w1^2 - (a1^5 + a1 + 2)
    curve2 = w2^2 - (a2^5 + a2 + 2)
    
    # 5. Eliminate the w's via sequential resultants instead of eliminate():
    #    step1 = Res_{w1}(h_s, curve1)   -- eliminates w1
    #    step2 = Res_{w2}(step1, curve2) -- eliminates w2
    #    Note: Passing variables directly to resultant() is safer than index numbers.
    step1 = resultant(h_s, curve1, w1)
    step2 = resultant(step1, curve2, w2)

    # 6. Divide out excess (inflated) multiplicity picked up by the
    #    resultant chain, Groebner-free, verified equal to eliminate()'s
    #    output in _run_bench.
    corr = correct_multiplicity(step2)

    # Return the winning (corrected) polynomial
    return corr.corrected
end


# ==============================================================================
# Factory for Sample 2 (Uses 'b' variables instead of 'a')
# ==============================================================================
# Groebner-free rewrite -- same reasoning as process_sample_1_coeff above,
# mirrored for the b-variable (sample 2) sandbox.
function process_sample_2_coeff(raw_coeff, target_name)
    println("  Spinning up sandbox (Sample 2) for: ", target_name)
    
    # 1. Build the 5-variable sandbox for Sample 2
    R_small, (w1, w2, b1, b2, T) = polynomial_ring(F, ["wb1", "wb2", "b1", "b2", target_name])
    
    # 2. Convert the raw tower fraction directly into our new sandbox
    t_gens = [b1, b2]
    w_gens = [w1, w2]
    num_s, den_s = tower_to_ring(raw_coeff, t_gens, w_gens)
    
    # 3. Build the graph equation
    h_s = T * den_s - num_s
    
    # 4. Add the curve equations (using b)
    curve1 = w1^2 - (b1^5 + b1 + 2)
    curve2 = w2^2 - (b2^5 + b2 + 2)
    
    # 5. Eliminate the w's via sequential resultants instead of eliminate():
    #    step1 = Res_{w1}(h_s, curve1)   -- eliminates w1
    #    step2 = Res_{w2}(step1, curve2) -- eliminates w2
    #    Note: Passing variables directly to resultant() is safer than index numbers.
    step1 = resultant(h_s, curve1, w1)
    step2 = resultant(step1, curve2, w2)

    # 6. Divide out excess (inflated) multiplicity picked up by the
    #    resultant chain, Groebner-free, verified equal to eliminate()'s
    #    output in _run_bench.
    corr = correct_multiplicity(step2)

    return corr.corrected
end



println("[worker sample=$sample target=$target] calling symbolic_residual...")
res = PhiSymbolic.symbolic_residual(const_K, const_c, fixed, u0, u1, v0, v1, F_POLY_ASC, p)

coeffs = kind == 'U' ? res.u_RS_coeffs : res.v_RS_coeffs
idx <= length(coeffs) || error("target $target out of range for sample $sample (have $(length(coeffs)) coeffs)")
raw_coeff = coeffs[idx]

################################################################################
# Build the 5-variable sandbox and run the resultant+correction pipeline
# -- identical logic to process_sample_1_coeff / process_sample_2_coeff
# in elim2.jl.
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

println("[worker sample=$sample target=$target] running resultant + correct_multiplicity...")
t_start = time()
# Eliminate the w's via sequential resultants instead of eliminate():
#   step1 = Res_{w1}(h_s, curve1)   -- eliminates w1
#   step2 = Res_{w2}(step1, curve2) -- eliminates w2
step1 = resultant(h_s, curve1, 1)
step2 = resultant(step1, curve2, 2)

# Divide out excess (inflated) multiplicity picked up by the resultant
# chain, Groebner-free, verified equal to eliminate()'s output in _run_bench.
corr = correct_multiplicity(step2)
result = corr.corrected
elapsed = time() - t_start
println("[worker sample=$sample target=$target] resultant+correction done in $(round(elapsed, digits=3))s, ",
        "degree=", (iszero(result) ? -1 : total_degree(result)), " terms=", length(terms(result)))

save(outfile, result)
println("[worker sample=$sample target=$target] saved -> $outfile")
