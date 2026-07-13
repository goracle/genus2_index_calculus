#!/usr/bin/env julia
################################################################################
#  part_k_monomial_gcd_check.jl  --  cheapest possible structure check on the
#  Leibniz summand term files: does EVERY term of a given summand share a
#  common monomial factor (i.e. is min exponent > 0 for some variable, taken
#  across all terms)?
#
#  This is NOT a real polynomial GCD -- it's just, for each variable, the
#  minimum exponent that variable has across every term of the polynomial.
#  If that minimum is > 0 for some variable, that variable (to that power)
#  divides every term, so it can be factored out for free -- O(terms) work,
#  no GCD algorithm involved. If a summand is "dense" in the sense that some
#  term has a zero exponent in every variable (i.e. a pure constant-times-
#  monomial-in-other-vars term touches exponent 0 somewhere for each var),
#  this will correctly report "no common monomial factor" and there's
#  nothing more to squeeze out at this level.
#
#  Usage:
#      julia part_k_monomial_gcd_check.jl <term_file_1> [<term_file_2> ...]
#
#  Defaults to checking U0_summand_1.stats.term.oscar and
#  U0_summand_2.stats.term.oscar if no arguments given.
################################################################################

using Oscar

const PART_K_RESULTS_DIR = joinpath(@__DIR__, "part_k_results")

term_files = if !isempty(ARGS)
    ARGS
else
    [joinpath(PART_K_RESULTS_DIR, "U0_summand_1.stats.term.oscar"),
     joinpath(PART_K_RESULTS_DIR, "U0_summand_2.stats.term.oscar")]
end

function common_monomial_factor(p)
    R = parent(p)
    nvars_R = nvars(R)
    min_exp = fill(typemax(Int), nvars_R)
    for t in terms(p)
        e = first(exponents(t))  # single term -> single exponent vector
        for i in 1:nvars_R
            min_exp[i] = min(min_exp[i], e[i])
        end
        # Early exit: once every entry is already 0, no common factor is
        # possible and we don't need to scan the remaining terms.
        all(iszero, min_exp) && break
    end
    return min_exp
end

for f in term_files
    isfile(f) || error("term file not found: $f")
    println("loading ", f, " ...")
    t0 = time()
    p = load(f)
    println("  loaded in ", round(time() - t0, digits=3), "s: ",
            "degree=", total_degree(p), " terms=", length(terms(p)))

    println("  scanning for common monomial factor (min exponent per variable)...")
    t0 = time()
    min_exp = common_monomial_factor(p)
    elapsed = time() - t0
    R = parent(p)
    var_names = symbols(R)

    nontrivial = [(var_names[i], min_exp[i]) for i in 1:length(min_exp) if min_exp[i] > 0]

    if isempty(nontrivial)
        println("  [", basename(f), "] no common monomial factor ",
                "(some term has exponent 0 in every variable) -- ",
                round(elapsed, digits=3), "s")
    else
        factor_str = join(["$(v)^$(e)" for (v, e) in nontrivial], " * ")
        println("  [", basename(f), "] COMMON MONOMIAL FACTOR FOUND: ", factor_str,
                "  (", round(elapsed, digits=3), "s)")
    end
    println()
end
