println("PART K DIAGNOSTIC: quartic-in-T structure probe")
println("="^70)

@assert (@isdefined syl_c1) && (@isdefined syl_c2) """
    syl_c1/syl_c2 not found. Run elim2.jl at least through the
    'computing resultant via subresultant PRS' print (i.e. through the
    poly_coeffs_in(g1_fp,...)/poly_coeffs_in(g2_fp,...) calls) before
    loading this diagnostic.
    """

# ------------------------------------------------------------------------
# Section A: per-coefficient size report (term counts / degrees), so we
# can see exactly which T^k slice(s) are driving the PRS cost.
# ------------------------------------------------------------------------
println("\n--- Section A: coefficient-of-T^k size report ---")
println("side 1 (g1_fp, degree-in-T=", d1T, "):")
for (k, c) in enumerate(syl_c1)
    kk = k - 1
    println("  [a1,a2,b1,b2]-coeff of T^$kk : total_degree=", total_degree(c),
            "  terms=", length(terms(c)))
end
println("side 2 (g2_fp, degree-in-T=", d2T, "):")
for (k, c) in enumerate(syl_c2)
    kk = k - 1
    println("  [a1,a2,b1,b2]-coeff of T^$kk : total_degree=", total_degree(c),
            "  terms=", length(terms(c)))
end

# ------------------------------------------------------------------------
# Section B: does g1_fp / g2_fp factor over its own ring, treated as a
# univariate-in-T polynomial with those large coefficients? Cheapest
# possible test first: leading/trailing coefficient GCD (a necessary
# condition for a nontrivial factorization T^4+...  = (T^2+AT+B)(T^2+CT+D)
# is that no single irreducible factor of the coefficient ring divides
# every T^k-coefficient in a way that's inconsistent with such a split;
# full factorization of a degree-4 univariate poly over a fraction field
# is what we actually want, so try factor() directly and time-box it).
# ------------------------------------------------------------------------
println("\n--- Section B: factorization of g1_T / g2_T over Kcoef(T) ---")

function try_factor_with_timeout(label, g, limit_secs)
    # Reuse elim2.jl's own run_with_timeout (~line 1403) rather than a
    # hand-rolled @async wrapper. NOTE the same caveat elim2.jl documents
    # for that helper: it uses Threads.@spawn, so a genuinely hung/
    # non-yielding Singular call inside factor() won't actually be
    # killed -- run_with_timeout will correctly report :timeout at the
    # wall-clock deadline and let the REST of this diagnostic proceed,
    # but the abandoned factor() call keeps running in the background
    # (same tradeoff elim2.jl already accepted for its own PART B sweep,
    # and the same reason elim2.jl's comments say a true kill needs an
    # OS-level `timeout N julia ...` wrapper around the whole process).
    if isdefined(Main, :run_with_timeout)
        val, status, elapsed = Main.run_with_timeout(() -> factor(g), limit_secs)
        if status != :ok
            println("  $label: factor() did not complete (status=$status, ",
                    round(elapsed, digits=1), "s elapsed) -- skipping. ",
                    "Background task may still be running; a fresh REPL ",
                    "is the only way to fully reclaim it.")
            return nothing
        end
        fac = val
    else
        println("  $label: run_with_timeout not found in Main (load elim2.jl ",
                "first) -- running factor() with NO timeout. This may hang ",
                "for a long time if the polynomial is large; interrupt ",
                "(Ctrl-C) if needed.")
        fac = factor(g)
    end
    n = length(fac)
    println("  $label: ", n, " irreducible factor(s):")
    for (f, e) in fac
        Tgen = gens(parent(f))[end]
        println("    degree-in-T=", degree(f, Tgen),
                " (exponent ", e, "), total_degree=", total_degree(f),
                " terms=", length(terms(f)))
    end
    return fac
end

if isdefined(Main, :g1_T) && isdefined(Main, :g2_T)
    fac1 = try_factor_with_timeout("g1_T", Main.g1_T, 60.0)
    fac2 = try_factor_with_timeout("g2_T", Main.g2_T, 60.0)
else
    println("  g1_T/g2_T not yet built in this session (Part K hasn't ",
            "reached that line) -- skipping live factorization test. ",
            "Rebuilding just enough to test factor() on g1_fp/g2_fp as ",
            "plain multivariate polys instead (factor(), not resultant()):")
    fac1 = try_factor_with_timeout("g1_fp", Main.g1_fp, 60.0)
    fac2 = try_factor_with_timeout("g2_fp", Main.g2_fp, 60.0)
end

# ------------------------------------------------------------------------
# Section C: do the T^k coefficients across k=0..4 share a common
# multivariate factor? If gcd(syl_c1...) is nontrivial, it can be pulled
# out of g1_fp entirely before the PRS ever runs, shrinking every pseudo-
# division step proportionally. Same check for side 2.
# ------------------------------------------------------------------------
println("\n--- Section C: common-factor (GCD) check across T^k coefficients ---")

function gcd_report(label, coeffs)
    nz = filter(!iszero, coeffs)
    if length(nz) < 2
        println("  $label: fewer than 2 nonzero coefficients, nothing to GCD.")
        return
    end
    g = nz[1]
    for c in nz[2:end]
        g = gcd(g, c)
    end
    if is_unit(g)
        println("  $label: gcd across all T^k coefficients is a unit -- ",
                "no common factor to pull out.")
    else
        println("  $label: NONTRIVIAL common factor found! degree=",
                total_degree(g), " terms=", length(terms(g)),
                " -- pulling this out before building g*_T could shrink ",
                "every coefficient the PRS touches.")
    end
end

gcd_report("side 1 (syl_c1)", syl_c1)
gcd_report("side 2 (syl_c2)", syl_c2)

# ------------------------------------------------------------------------
# Section D: structural symmetry checks on g1_fp / g2_fp as polynomials
# in T -- is it quadratic-in-T^2 (only even powers present), palindromic/
# reciprocal (c_k == c_{d-k} up to a unit), or otherwise reducible in a
# way that would let us solve two quadratics instead of one quartic?
# ------------------------------------------------------------------------
println("\n--- Section D: symmetry checks (even-power-only / palindromic) ---")

function symmetry_report(label, coeffs, d)
    # coeffs[k+1] = coefficient of T^k, k = 0..d
    odd_nonzero = any(!iszero(coeffs[k+1]) for k in 1:2:d)
    println("  $label: only even powers of T present? ", !odd_nonzero,
            odd_nonzero ? "" : "  --> reduces to a QUADRATIC in T^2, " *
            "halving the effective degree for root-finding / factoring.")

    if d >= 1
        is_palindromic = true
        for k in 0:d
            ck = coeffs[k+1]
            cdk = coeffs[d-k+1]
            # palindromic up to scalar: c_k == lambda * c_{d-k} for fixed lambda
            if iszero(ck) != iszero(cdk)
                is_palindromic = false
                break
            end
        end
        println("  $label: leading/trailing coefficient zero-pattern is ",
                is_palindromic ? "consistent with" : "NOT consistent with",
                " a palindromic (reciprocal) polynomial.")
    end
end

symmetry_report("side 1 (syl_c1)", syl_c1, d1T)
symmetry_report("side 2 (syl_c2)", syl_c2, d2T)

# ------------------------------------------------------------------------
# Section E: numeric substitution test. Plug in a handful of random
# GF(p)-rational values for (a1,a2,b1,b2) (respecting the curve
# constraints if F is exposed as such -- here we just use random field
# elements, which is fine for a *size* diagnostic even if not every
# substitution lands on the actual curve) and see how much the term
# count of g1_fp/g2_fp collapses. This tells us whether "1445 terms" is
# inherent to the degree-36 geometry, or mostly bookkeeping overhead from
# carrying 4 symbolic anchor variables through the tower this late.
# ------------------------------------------------------------------------
println("\n--- Section E: random specialization size test ---")

function specialize_and_report(label, g, gens_to_kill)
    # Uses the same evaluate(f, full_image_list) pattern already used
    # throughout elim2.jl (e.g. `remap(f) = evaluate(f, [...])` at line
    # 645 / 1208). g1_fp/g2_fp are only 5-variable, so this full-ring
    # evaluate() is cheap and safe here -- it's the large final-universe
    # objects elsewhere in elim2.jl where evaluate() was the problem
    # (the ring-remapping bug already fixed upstream via
    # MPolyBuildCtx/push_term!/finish, i.e. remap_to_final).
    Rg = parent(g)
    all_gens = gens(Rg)
    images = Vector{Any}(undef, length(all_gens))
    for (i, v) in enumerate(all_gens)
        if v in gens_to_kill
            images[i] = rand(F)
        else
            images[i] = v   # leave T (and any other free generator) symbolic
        end
    end
    g_spec = evaluate(g, images)
    Tpos = findfirst(v -> !(v in gens_to_kill), all_gens)
    println("  $label: before terms=", length(terms(g)),
            "  after random (a*,b*) specialization terms=",
            length(terms(g_spec)), "  degree-in-T unchanged=",
            degree(g_spec, all_gens[Tpos]))
end

specialize_and_report("g1_fp", g1_fp, [a1_fp, a2_fp])
specialize_and_report("g2_fp", g2_fp, [b1_fp, b2_fp])

println("\n" * "="^70)
