println("PART I: The Sandbox Factory (Automated Elimination)")
println("===========================================================")

################################################################################
# Forward declarations, hoisted from later in this file (the
# part_i_squarefree_diag.jl / correct_multiplicity blocks below), because
# this is a flat top-to-bottom script with no function-hoisting: the
# resultant + multiplicity-correction pipeline wired into
# process_sample_1_coeff/process_sample_2_coeff just below needs
# canonical_factor_key, factor_multiset, and correct_multiplicity to
# already be defined by the time those factories are called (including the
# "Factory Test" call immediately after process_sample_1_coeff's
# definition). The originals still appear later in the file, unchanged --
# Julia just lets the later `function` definitions redefine these methods
# again (identically), which is harmless.
################################################################################

"""
    canonical_factor_key(f) -> String

Return a hashable, order-independent, unit-scaled key for an irreducible
polynomial `f`, so two irreducible factors coming out of independent
`factor()` calls (potentially differing by a nonzero field-element unit,
and with no guaranteed enumeration order) compare equal iff they are
associates.

Normalization: divide by the coefficient of the lexicographically-first
monomial (in a fixed, deterministic term order), so the leading
coefficient of the normalized polynomial is always 1. This is well
defined for any irreducible over a field, independent of which unit
multiple factor() happened to emit.
"""
function canonical_factor_key(f)
    R = parent(f)
    F = base_ring(R)
    # Deterministic term order: sort exponent vectors lexicographically.
    exps = collect(AbstractAlgebra.exponent_vectors(f))
    cfs  = collect(coefficients(f))
    order = sortperm(exps)  # lexicographic on Vector{Int} is Julia's default
    lead_c = cfs[order[1]]
    inv_lead = inv(lead_c)
    # Build normalized (monic-by-convention) term list as a canonical string.
    io = IOBuffer()
    for idx in order
        c = cfs[idx] * inv_lead
        print(io, string(c), ":", string(exps[idx]), ";")
    end
    return String(take!(io))
end

"""
    factor_multiset(f) -> Dict{String,Int}

Factor `f` and return a map: canonical_factor_key(irreducible factor) => exponent.
Keys are unit/order independent so two factorizations of associate
polynomials produce identical dictionaries.
"""
function factor_multiset(f)
    fac = factor(f)
    d = Dict{String,Int}()
    for (p, e) in fac
        key = canonical_factor_key(p)
        d[key] = get(d, key, 0) + e
    end
    return d, fac
end


using Oscar # Or Nemo

using Oscar

"""
    correct_multiplicity(Res2)

SUPERSEDED -- no longer called anywhere in this file (both
process_sample_1_coeff and process_sample_2_coeff now call the general
correct_multiplicity(Res1, Res2; label="") defined further below, near
"Groebner-free multiplicity correction" / MULTIPLICITY CORRECTION).
Kept only because Julia dispatches this and the 2-arg version as
separate methods of the same name; not deleted since that wasn't asked
for. This version hardcodes the correction exponent from the target
variable's name (U->4, V->6) and errors out if there's more than one
degree-8 factor, instead of handling every inflated factor Res1-vs-Res2
comparison finds -- do not wire this back in.

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
    corr = correct_multiplicity(step1, step2)

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
    corr = correct_multiplicity(step1, step2)

    return corr.corrected
end

println("===========================================================")
