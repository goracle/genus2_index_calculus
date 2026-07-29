
################################################################################
#
#  05_part_k_resultant.jl -- part of the Elim2 package (src/Elim2.jl
#  includes this file). See src/Elim2.jl for the package-level overview
#  and the full include order of all submodule files.
#
#  Submodule: PartKResultant
#
#  Encapsulation of elim2.jl's own PART K continuation ("The Final
#  Collision", original lines 4684-8017). Builds the shared 8-variable
#  final universe ring, remaps PART J's clean_sample_1/clean_sample_2
#  into it, and for each target (U0,U1,V0,V1) computes the resultant via
#  an abstract-variable Bezout-determinant route with disk-backed
#  term-by-term substitution. See the in-file PART K banner comment
#  directly below for the full original description.
#
################################################################################
module PartKResultant

using Oscar
using Serialization
using ..Elim2: ELIM2_ROOT_DIR

################################################################################
# PART K: "The Final Collision" (original lines 4684-8017).
#
# Builds a shared 8-variable "final universe" ring F[a1,a2,b1,b2,U0,U1,V0,V1]
# (no w-variables), remaps PART J's clean_sample_1/clean_sample_2 outputs
# into it, then for each of the 4 targets (U0,U1,V0,V1) computes the
# resultant eliminating that target between the sample-1 side and the
# sample-2 side, via an abstract-variable Bezout-determinant route (PART F)
# that avoids the intermediate expression swell of a naive Sylvester/
# Leibniz expansion or a flat multivariate resultant() call. Diagnostics
# (PARTS A-E) run first, per target, to characterize the quartic-in-T
# structure before the expensive Bezout substitution is attempted.
#
# This module intentionally keeps PART F's disk-sharded checkpoint/resume
# machinery close to verbatim: it is stateful, correctness-critical
# (resuming a partial run must not silently lose or double-count terms),
# and was hard-won (see the original's own comments on the OOM history
# that produced this design). Restructuring it further than "closures ->
# named kwargs-taking functions" would risk introducing exactly the kind
# of resume/merge bug its own comments describe fixing.
################################################################################

################################################################################
# Struct: FinalUniverse -- the shared 8-variable ring (a1,a2,b1,b2,U0,U1,V0,V1)
# that both samples get remapped into, plus the remapped equations.
# Original lines 4688-4691, 4786-4812.
################################################################################
struct FinalUniverse
    R_final
    a1_f; a2_f; b1_f; b2_f; U0_f; U1_f; V0_f; V1_f
    final_gens::Vector
    final_equations::Vector
end

"""
    remap_to_final(f, final_gens, gen_map)

Original lines 4727-4766. Rebuilds `f` term-by-term (via
`coefficients`/`exponent_vectors`/`MPolyBuildCtx`/`push_term!`/`finish`)
into the ring that owns `final_gens`, using `gen_map` to send `f`'s
generator index `k` to `final_gens[gen_map[k]]` (1-based), or to require
that generator's exponent be identically zero when `gen_map[k] == 0`.
This is linear in `f`'s term count and never invokes cross-ring
`evaluate()`/ring-homomorphism machinery, which is what made the naive
version of this remap OOM/hang on the very first call (see original
comments at lines 4696-4726). Raises an error (never silently drops
content) if a generator mapped to "must be zero" has a nonzero exponent
in some term.
"""
function remap_to_final(f, final_gens::Vector, gen_map::Vector{Int})
    R_out = parent(final_gens[1])
    n_out = length(final_gens)
    B = MPolyBuildCtx(R_out)

    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        new_exps = zeros(Int, n_out)
        for (k, e) in enumerate(exps)
            e == 0 && continue
            tgt = gen_map[k]
            if tgt == 0
                error("remap_to_final: generator index $k (mapped to zero) " *
                      "has nonzero exponent $e in a term of the input " *
                      "polynomial -- eliminate() did NOT fully remove this " *
                      "variable, zeroing it here would silently drop real " *
                      "content. Inspect the input polynomial before proceeding.")
            end
            new_exps[tgt] += e
        end
        push_term!(B, c, new_exps)
    end

    return finish(B)
end

"""
    build_final_universe(F, clean_sample_1, clean_sample_2)

Original lines 4688-4812. Builds the shared final-universe ring
`F[a1,a2,b1,b2,U0,U1,V0,V1]` and remaps every entry of `clean_sample_1`
(a-variables -> final indices 1,2; targets U0,U1,V0,V1 -> final indices
5,6,7,8 respectively) and `clean_sample_2` (b-variables -> final indices
3,4; same target mapping) into it via `remap_to_final`. Both samples'
w-variables (wa1,wa2 / wb1,wb2) are asserted eliminated already (mapped
to zero) rather than assumed. Returns a `FinalUniverse` whose
`final_equations` holds, in order, sample 1's [U0,U1,V0,V1] rows followed
by sample 2's [U0,U1,V0,V1] rows -- i.e. indices 1:4 are sample 1,
indices 5:8 are sample 2, matching the original's `sample1_target_final_idx`
/ `sample2_target_final_idx` = `[5,6,7,8]` push order.
"""
function build_final_universe(F, clean_sample_1::Vector, clean_sample_2::Vector)
    println("===========================================================")
    println("PART K: The Final Collision (Eliminating the Middlemen)")
    println("===========================================================")

    R_final, (a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f) =
        polynomial_ring(F, ["a1", "a2", "b1", "b2", "U0", "U1", "V0", "V1"])
    final_gens = [a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f]

    final_equations = Any[]

    println("  Mapping Sample 1 into the final universe (manual term-by-term)...")
    sample1_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
    for (i, tgt_idx) in enumerate(sample1_target_final_idx)
        gen_map = [0, 0, 1, 2, tgt_idx]
        t0 = time()
        g = remap_to_final(clean_sample_1[i], final_gens, gen_map)
        println("  clean_sample_1[$i] remapped in ", round(time()-t0, digits=3),
                "s: degree=", total_degree(g), " terms=", length(terms(g)))
        push!(final_equations, g)
    end

    println("  Mapping Sample 2 into the final universe (manual term-by-term)...")
    sample2_target_final_idx = [5, 6, 7, 8]   # U0, U1, V0, V1
    for (i, tgt_idx) in enumerate(sample2_target_final_idx)
        gen_map = [0, 0, 3, 4, tgt_idx]
        t0 = time()
        g = remap_to_final(clean_sample_2[i], final_gens, gen_map)
        println("  clean_sample_2[$i] remapped in ", round(time()-t0, digits=3),
                "s: degree=", total_degree(g), " terms=", length(terms(g)))
        push!(final_equations, g)
    end

    return FinalUniverse(R_final, a1_f, a2_f, b1_f, b2_f, U0_f, U1_f, V0_f, V1_f,
                          final_gens, final_equations)
end

"""
    target_specs(fu::FinalUniverse)

Original lines 4851-4856. The 4 (name, sample1_idx, sample2_idx, target_gen)
tuples the PART K loop iterates over -- `sample1_idx`/`sample2_idx` index
into `fu.final_equations` (1-based: U0=1/5, U1=2/6, V0=3/7, V1=4/8).
"""
function target_specs(fu::FinalUniverse)
    return [
        ("U0", 1, 5, fu.U0_f),
        ("U1", 2, 6, fu.U1_f),
        ("V0", 3, 7, fu.V0_f),
        ("V1", 4, 8, fu.V1_f),
    ]
end

################################################################################
# Struct: TargetSetup -- everything built once per target (name, i1, i2,
# Tvar) before diagnostics/PART F run: the 5-variable fiber-product ring,
# g1_fp/g2_fp, their T-degrees, and their per-power-of-T coefficient
# slices (syl_c1/syl_c2). Original lines 4858-4950.
################################################################################
struct TargetSetup
    name::String
    RESULTANT_FILE::String
    Rfp
    a1_fp; a2_fp; b1_fp; b2_fp; T_fp
    g1_fp; g2_fp
    d1T::Int; d2T::Int
    syl_c1::Vector; syl_c2::Vector
end

"""
    poly_coeffs_in(g, T, maxdeg)

Original lines 4934-4946 (re-derived identically at 5344-5351 as
`drop_T_to_coef_ring`'s sibling, kept separate to match the original's
own duplication). Extracts `[c0, c1, ..., c_maxdeg]` (each `T`-free)
such that `g == sum_k c_k * T^k`, via
`coefficients`/`exponent_vectors`/`MPolyBuildCtx` -- never touches
ring-homomorphism machinery.
"""
function poly_coeffs_in(g, T, maxdeg::Int)
    Rg = parent(g)
    gensR = gens(Rg)
    Tidx = findfirst(==(T), gensR)
    coeff_polys = [MPolyBuildCtx(Rg) for _ in 0:maxdeg]
    for (c, exps) in zip(coefficients(g), AbstractAlgebra.exponent_vectors(g))
        k = exps[Tidx]
        new_exps = copy(exps)
        new_exps[Tidx] = 0
        push_term!(coeff_polys[k+1], c, new_exps)
    end
    return [finish(ctx) for ctx in coeff_polys]
end

"""
    already_complete(RESULTANT_FILE)

Original lines 4862-4891 (SKIP-IF-ALREADY-DONE). Returns `true` if a
resultant file for this target already exists on disk (in which case
the caller should skip recomputation and move to the next target). This
assumes `RESULTANT_FILE` is only ever written once its target's
computation has fully completed (true as of the PART F `save()` call,
which happens after the final-merge assertion and correctness
spot-check/crosscheck have already passed).
"""
function already_complete(RESULTANT_FILE::String)
    if isfile(RESULTANT_FILE)
        println("  --- already complete (found ", RESULTANT_FILE,
                "), skipping recomputation. Delete this file (or set an",
                " override) if you need to force a redo.")
        flush(stdout)
        return true
    end
    return false
end

"""
    build_target_setup(F, clean_sample_1, clean_sample_2, name, i1, i2, Tvar;
                        scratch_dir)

Original lines 4858-4950 (minus the skip-if-done check, which the caller
runs first via `already_complete`). `i1`/`i2` index into `clean_sample_1`/
sample-2 semantics exactly as the original: `i2_local = i2 - 4` (4 ==
`length(clean_sample_1)`, always U0,U1,V0,V1) recovers sample 2's own
1-based index. Builds the 5-variable fiber-product ring
`F[a1,a2,b1,b2,<name>]` (`g1_fp` only involves `(a1,a2,T)`, `g2_fp` only
`(b1,b2,T)`), remaps `clean_sample_1[i1]` / `clean_sample_2[i2_local]`
into it via `remap_to_final` (reused as a generic term-by-term ring
remap, not specific to the final universe), and extracts each side's
per-power-of-`T` coefficient slices. Raises an error if `T` does not
actually appear in one side (checked one level up, in the target-loop
driver, via `d1T == 0 || d2T == 0` on the ALREADY-final-universe degree
-- kept there since that check needs `fu.final_equations`, not this
fiber-product ring).
"""
function build_target_setup(F, clean_sample_1::Vector, clean_sample_2::Vector,
                             name::String, i1::Int, i2::Int, d1T::Int, d2T::Int;
                             scratch_dir::String = joinpath(ELIM2_ROOT_DIR, "part_k_results"))
    RESULTANT_FILE = joinpath(scratch_dir, "$(name)_resultant.oscar")

    println("    building the fiber-product ring/generators for $name...")
    flush(stdout)

    Rfp, (a1_fp, a2_fp, b1_fp, b2_fp, T_fp) =
        polynomial_ring(F, ["a1", "a2", "b1", "b2", string(name)])
    rfp_gens = [a1_fp, a2_fp, b1_fp, b2_fp, T_fp]

    i2_local = i2 - length(clean_sample_1)
    g1_fp = remap_to_final(clean_sample_1[i1], rfp_gens,
                            [0, 0, 1, 2, 5])   # wa1,wa2->0; a1->1; a2->2; T->5
    g2_fp = remap_to_final(clean_sample_2[i2_local], rfp_gens,
                            [0, 0, 3, 4, 5])   # wb1,wb2->0; b1->3; b2->4; T->5

    println("      g1 remapped into 5-var fiber-product ring: degree=",
            total_degree(g1_fp), " terms=", length(terms(g1_fp)),
            "  degree-in-T=", degree(g1_fp, T_fp))
    println("      g2 remapped into 5-var fiber-product ring: degree=",
            total_degree(g2_fp), " terms=", length(terms(g2_fp)),
            "  degree-in-T=", degree(g2_fp, T_fp))

    syl_c1 = poly_coeffs_in(g1_fp, T_fp, d1T)   # syl_c1[k+1] is coeff of T^k in g1_fp
    syl_c2 = poly_coeffs_in(g2_fp, T_fp, d2T)   # syl_c2[k+1] is coeff of T^k in g2_fp

    return TargetSetup(name, RESULTANT_FILE, Rfp, a1_fp, a2_fp, b1_fp, b2_fp, T_fp,
                        g1_fp, g2_fp, d1T, d2T, syl_c1, syl_c2)
end
################################################################################
# Struct: CoefRing -- the 4-variable coefficient ring F[a1,a2,b1,b2] and
# its fraction field, plus the lifted T^0..T^4 coefficient slices
# (c1_lifted/c2_lifted, as Kcoef elements) and the univariate-in-T tower
# ring Rt=Kcoef[T] with g1_T/g2_T reassembled in it. Original lines
# 5335-5368.
################################################################################
struct CoefRing
    Rcoef
    a1_c; a2_c; b1_c; b2_c
    Kcoef
    c1_lifted::Vector; c2_lifted::Vector
    Rt; T
    g1_T; g2_T
end

"""
    drop_T_to_coef_ring(f, coef_gens)

Original lines 5344-5351. Maps a T-free coefficient slice (living in the
5-variable fiber-product ring `Rfp`, which still nominally has `T` as a
generator even though these slices never use it) down into the
4-variable ring owning `coef_gens`, via the same term-by-term
`MPolyBuildCtx` technique used throughout PART K. `exps[1:4]` is taken
unconditionally (i.e. `exps[5]`, the `T` exponent, is assumed already
zero by construction of `poly_coeffs_in`'s slices -- not re-checked
here, matching the original).
"""
function drop_T_to_coef_ring(f, coef_gens::Vector)
    B = MPolyBuildCtx(parent(coef_gens[1]))
    for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
        push_term!(B, c, exps[1:4])
    end
    return finish(B)
end

"""
    build_coef_ring(F, ts::TargetSetup)

Original lines 5335-5368 (PART K, REDESIGNED: resultant via a
univariate-in-T ring over the coefficient ring). Builds
`Rcoef = F[a1,a2,b1,b2]`, its fraction field `Kcoef`, lifts `ts.syl_c1`/
`ts.syl_c2` down into `Kcoef` via `drop_T_to_coef_ring`, then builds the
univariate tower `Rt = Kcoef[T]` and reassembles `g1_T`/`g2_T` from the
lifted coefficient slices. This is the ring `resultant(g1_T, g2_T)`
would dispatch a subresultant-PRS computation in (see the original's
extensive comments on why this beats a flat Sylvester/Leibniz
expansion) -- PART F below computes the SAME resultant via an
abstract-Bezout route instead of calling `resultant()` directly, but
`g1_T`/`g2_T` are still built here since PART E's diagnostic
(`pseudorem`) and PART G's (dead-code, ported below) commented-out PRS
path both need them.
"""
function build_coef_ring(F, ts::TargetSetup)
    Rcoef, (a1_c, a2_c, b1_c, b2_c) = polynomial_ring(F, ["a1", "a2", "b1", "b2"])
    Kcoef = fraction_field(Rcoef)

    coef_gens = [a1_c, a2_c, b1_c, b2_c]
    c1_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in ts.syl_c1]
    c2_lifted = [Kcoef(drop_T_to_coef_ring(c, coef_gens)) for c in ts.syl_c2]

    Rt, T = polynomial_ring(Kcoef, string(ts.name))

    g1_T = sum(c1_lifted[k+1] * T^k for k in 0:ts.d1T)
    g2_T = sum(c2_lifted[k+1] * T^k for k in 0:ts.d2T)

    return CoefRing(Rcoef, a1_c, a2_c, b1_c, b2_c, Kcoef, c1_lifted, c2_lifted, Rt, T, g1_T, g2_T)
end

################################################################################
# Struct: BezoutMatrix -- the concrete 4x4 Bezout matrix entries B[(i,j)]
# for i,j in 0:3, built from the actual (large) coefficient polynomials,
# plus the bracket cache/function used to build them. Original lines
# 5405-5504 (BEZOUT MATRIX ENTRY DIAGNOSTIC).
################################################################################
struct BezoutMatrix
    B::Dict{Tuple{Int,Int}, Any}
    p_coef::Vector; q_coef::Vector
end

"""
    build_concrete_bezout_diagnostic(cr::CoefRing, ts::TargetSetup)

Original lines 5405-5504. Only meaningful when `ts.d1T == ts.d2T == 4`
(checked by the caller; returns `nothing` and prints a skip message
otherwise, matching the original's `if d1T == 4 && d2T == 4 ... else
println("(skipping...")` structure). Constructs `B`, the 4x4 symmetric
Bezout matrix of `g1_T`/`g2_T` (both degree 4 in `T`), from the
antisymmetric bracket `[p,q]_{m,n} := p_m*q_n - p_n*q_m` -- NOT
computing `det(B)` here, only reporting each entry's degree/term-count/
sparsity so the caller can judge whether a full Bezout-determinant
route is worth pursuing before committing to it. Warns (does not error)
if a bracket's denominator is not a unit, since this is a diagnostic
pass and reporting the numerator-only degree/terms is still informative
in that case -- PART F below performs the same check but errors instead,
since it is on the actual result-computing path.
"""
function build_concrete_bezout_diagnostic(cr::CoefRing, ts::TargetSetup)
    if !(ts.d1T == 4 && ts.d2T == 4)
        println("    (skipping Bezout diagnostic: expected d1T==d2T==4, got ",
                ts.d1T, ", ", ts.d2T, ")")
        return nothing
    end

    println("    --- Bezout matrix entry diagnostic ($(ts.name)) ---")
    println("    (constructing B only -- NOT computing det(B) / resultant here)")
    flush(stdout)

    p_coef = cr.c1_lifted   # p_coef[k+1] = p_k, k = 0..4
    q_coef = cr.c2_lifted   # q_coef[k+1] = q_k, k = 0..4
    Rcoef = cr.Rcoef

    function bracket_num(m::Int, n::Int)
        pm, qn = p_coef[m+1], q_coef[n+1]
        pn, qm = p_coef[n+1], q_coef[m+1]
        val = pm * qn - pn * qm   # Kcoef arithmetic
        den = denominator(val)
        if !is_unit(den)
            println("      WARNING: [p,q]_{$m,$n} has non-unit denominator " *
                    "(degree=", total_degree(den), ") -- coefficient lift " *
                    "may not be a clean polynomial here; reporting numerator only.")
        end
        return Rcoef(numerator(val))
    end

    bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(bracket_cache, key)
            bracket_cache[key] = bracket_num(key[1], key[2])
        end
        return m < n ? bracket_cache[key] : -bracket_cache[key]
    end

    B = Dict{Tuple{Int,Int}, Any}()
    B[(0,0)] = bracket(0,1)
    B[(0,1)] = bracket(0,2)
    B[(0,2)] = bracket(0,3)
    B[(0,3)] = bracket(0,4)
    B[(1,1)] = bracket(0,3) + bracket(1,2)
    B[(1,2)] = bracket(0,4) + bracket(1,3)
    B[(1,3)] = bracket(1,4)
    B[(2,2)] = bracket(1,4) + bracket(2,3)
    B[(2,3)] = bracket(2,4)
    B[(3,3)] = bracket(3,4)
    B[(1,0)] = B[(0,1)]
    B[(2,0)] = B[(0,2)]
    B[(3,0)] = B[(0,3)]
    B[(2,1)] = B[(1,2)]
    B[(3,1)] = B[(1,3)]
    B[(3,2)] = B[(2,3)]

    nvars_coef = 4
    function sparsity_ratio(f)
        d = total_degree(f)
        t = length(terms(f))
        max_mono = binomial(d + nvars_coef, nvars_coef)
        return max_mono == 0 ? NaN : t / max_mono
    end

    println("      entry   degree   terms      sparsity(terms/maxmono<=deg)")
    for i in 0:3, j in 0:3
        f = B[(i,j)]
        d = total_degree(f)
        t = length(terms(f))
        s = sparsity_ratio(f)
        println("      B[$i,$j]   ", d, "        ", t, "        ",
                round(s, sigdigits=4))
    end
    flush(stdout)

    total_terms = sum(length(terms(B[(i,j)])) for i in 0:3, j in 0:3)
    max_deg = maximum(total_degree(B[(i,j)]) for i in 0:3, j in 0:3)
    println("      --- summary: max entry degree=$max_deg, " *
            "total terms across all 16 entries=$total_terms ---")
    println("      Reading this: if entries look like degree~64 with ")
    println("      O(1000) terms each, Bezout construction is cheap and ")
    println("      Bareiss elimination is worth writing next. If entries ")
    println("      already look like degree~64 with O(100000+) terms, ")
    println("      the bottleneck has simply moved from the PRS recursion ")
    println("      into Bezout construction itself, and Bareiss won't help.")
    flush(stdout)

    return BezoutMatrix(B, p_coef, q_coef)
end
################################################################################
# PARTS A-E: deep structural diagnostic pass (original lines 5506-6516),
# requested BEFORE any resultant (Sylvester, Bezout-determinant, or PRS)
# is run to completion. Answers: hidden factors in g1/g2 (A/B), redundant
# symmetric variables (C/C.5), Bezout entry sparsity/factoring (D), and
# whether a single PRS step already predicts the Bezout-entry blowup (E).
# Nothing in this pass computes det(B) or the full resultant.
#
# Kept as one function (rather than split further) because Sections
# A-E.5 share a large amount of local state (g1_coefs_poly/g2_coefs_poly,
# the classification dict c5_class, the rewritten-coefficient dict
# c5_rewritten, swap_a/swap_b automorphisms, safe_factor_report, etc.)
# built up incrementally through the pass -- splitting it into fully
# independent functions would mean re-deriving or re-threading all of
# that state through extra parameters, with no reuse benefit elsewhere
# in the module (nothing outside this diagnostic pass needs
# c5_class/c5_rewritten again).
################################################################################

"""
    run_parts_a_to_e_diagnostic(F, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix)

Original lines 5506-6516 (PARTS A-E). Only runs when `ts.d1T == ts.d2T
== 4` (checked by the caller the same way `build_concrete_bezout_diagnostic`
is). `F` is the base field, needed to build the symmetric-basis and
scratch rings used partway through PART C/C.5. Prints an extensive
diagnostic report; returns `nothing` (this pass exists entirely for its
printed output, matching the original -- no downstream PART K code
consumes its return value).
"""
function run_parts_a_to_e_diagnostic(F, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix)
    if !(ts.d1T == 4 && ts.d2T == 4)
        return nothing
    end

    name = ts.name
    Rcoef = cr.Rcoef
    a1_c, a2_c, b1_c, b2_c = cr.a1_c, cr.a2_c, cr.b1_c, cr.b2_c
    p_coef, q_coef = bm.p_coef, bm.q_coef
    B = bm.B

    println()
    println("=" ^ 70)
    println("PARTS A-E: deep diagnostic (no resultant computed) -- $name")
    println("=" ^ 70)
    flush(stdout)

    function safe_factor_report(f; label::String="", indent::String="        ")
        d = total_degree(f)
        t = length(terms(f))
        println(indent, label, "degree=", d, "  terms=", t)
        if iszero(f)
            println(indent, "  (zero polynomial)")
            return
        end
        try
            t0f = time()
            fac = factor(f)
            elf = time() - t0f
            nfac = length(fac)
            println(indent, "  factor() in ", round(elf, digits=3), "s -> ",
                    nfac, " distinct irreducible factor(s):")
            for (fp, e) in fac
                println(indent, "    exponent=", e, "  degree=", total_degree(fp),
                        "  terms=", length(terms(fp)))
            end
        catch err
            println(indent, "  factor() FAILED/skipped: ", sprint(showerror, err))
        end
        flush(stdout)
    end

    # ------------------------------------------------------------------
    # PART A: coefficient-vector analysis of g1, g2 as polynomials in T
    # ------------------------------------------------------------------
    println()
    println("--- PART A: coefficient-vector analysis ---")
    flush(stdout)

    function coef_as_poly(c)
        den = denominator(c)
        if !is_unit(den)
            println("      WARNING: coefficient has non-unit denominator (degree=",
                    total_degree(den), ") -- reporting numerator only.")
        end
        return Rcoef(numerator(c))
    end

    g1_coefs_poly = [coef_as_poly(p_coef[k+1]) for k in 0:4]  # index k+1 <-> T^k
    g2_coefs_poly = [coef_as_poly(q_coef[k+1]) for k in 0:4]

    for (gname, cs) in (("g1", g1_coefs_poly), ("g2", g2_coefs_poly))
        println("  $gname:")
        for k in 4:-1:0
            safe_factor_report(cs[k+1]; label="coeff of T^$k: ")
        end
    end

    println("  structural tests:")
    for (gname, cs) in (("g1", g1_coefs_poly), ("g2", g2_coefs_poly))
        c4, c3, c2, c1, c0 = cs[5], cs[4], cs[3], cs[2], cs[1]
        println("    $gname: T^3 coeff zero? ", iszero(c3),
                "   T^1 coeff zero? ", iszero(c1))
        if iszero(c3) && iszero(c1)
            println("      -> $gname has NO odd-T terms: candidate form ",
                    "T^4 + a*T^2 + c (biquadratic in T) or T^4 + c if also c2==0.")
            if iszero(c2)
                println("      -> $gname coeff-of-T^2 ALSO zero: candidate pure form T^4 + c.")
            end
        end
        if !iszero(c0) && !iszero(c4)
            println("      $gname palindromic check: deg(c0)=", total_degree(c0),
                    " vs deg(c4)=", total_degree(c4),
                    "   deg(c1)=", total_degree(c1),
                    " vs deg(c3)=", total_degree(c3))
        end
        if !iszero(c3) && !iszero(c1)
            g_odd = gcd(c3, c1)
            println("      $gname gcd(c3,c1): degree=", total_degree(g_odd),
                    "  terms=", length(terms(g_odd)),
                    (total_degree(g_odd) > 0 ? "  <-- NONTRIVIAL" : "  (trivial/unit)"))
        end
    end
    flush(stdout)

    # ------------------------------------------------------------------
    # PART B: GCD structure among T-coefficients of each quartic
    # ------------------------------------------------------------------
    println()
    println("--- PART B: GCD structure among T-coefficients ---")
    flush(stdout)

    function report_gcd_pair(cs, gname, i::Int, j::Int)
        ci, cj = cs[i+1], cs[j+1]
        if iszero(ci) || iszero(cj)
            println("    $gname gcd(c$i,c$j): one side is zero -- skipping gcd (undefined/trivial)")
            return
        end
        g = gcd(ci, cj)
        dg = total_degree(g)
        tg = length(terms(g))
        println("    $gname gcd(c$i,c$j): degree=", dg, "  terms=", tg,
                dg > 0 ? "  <-- NONTRIVIAL FACTOR" : "  (unit)")
        if dg > 0
            qi, ri = divrem(ci, g)
            qj, rj = divrem(cj, g)
            ok_i = iszero(ri); ok_j = iszero(rj)
            println("      c$i before=", length(terms(ci)), " terms; after /gcd=",
                    length(terms(qi)), " terms  (exact div? ", ok_i, ")")
            println("      c$j before=", length(terms(cj)), " terms; after /gcd=",
                    length(terms(qj)), " terms  (exact div? ", ok_j, ")")
        end
    end

    for (gname, cs) in (("g1", g1_coefs_poly), ("g2", g2_coefs_poly))
        report_gcd_pair(cs, gname, 4, 3)
        report_gcd_pair(cs, gname, 4, 2)
        report_gcd_pair(cs, gname, 4, 1)
        report_gcd_pair(cs, gname, 4, 0)

        nonzero_cs = [c for c in cs if !iszero(c)]
        if length(nonzero_cs) >= 2
            g_all = reduce(gcd, nonzero_cs)
            dg_all = total_degree(g_all)
            tg_all = length(terms(g_all))
            println("    $gname gcd(all nonzero coefficients): degree=", dg_all,
                    "  terms=", tg_all,
                    dg_all > 0 ? "  <-- NONTRIVIAL, content should be pulled out" : "  (unit, no common content)")
        else
            println("    $gname gcd(all coefficients): fewer than 2 nonzero coefficients, skipping")
        end
    end
    flush(stdout)

    # ------------------------------------------------------------------
    # PART C: symmetry reduction test (a1<->a2, b1<->b2 -> sa,pa,sb,pb)
    # ------------------------------------------------------------------
    println()
    println("--- PART C: symmetry reduction test ---")
    flush(stdout)

    swap_a = hom(Rcoef, Rcoef, [a2_c, a1_c, b1_c, b2_c])
    swap_b = hom(Rcoef, Rcoef, [a1_c, a2_c, b2_c, b1_c])

    function is_symmetric_under(f, phi)
        return iszero(f - phi(f))
    end

    all_coefs = vcat(
        [("g1", k, g1_coefs_poly[k+1]) for k in 0:4],
        [("g2", k, g2_coefs_poly[k+1]) for k in 0:4]
    )

    all_a_sym = true
    all_b_sym = true
    for (gname, k, f) in all_coefs
        if iszero(f)
            continue
        end
        sym_a = is_symmetric_under(f, swap_a)
        sym_b = is_symmetric_under(f, swap_b)
        all_a_sym &= sym_a
        all_b_sym &= sym_b
        println("    $gname coeff of T^$k: symmetric under a1<->a2? ", sym_a,
                "   symmetric under b1<->b2? ", sym_b)
    end
    flush(stdout)

    if all_a_sym && all_b_sym
        println("  CONFIRMED: every quartic coefficient is symmetric under both ",
                "a1<->a2 and b1<->b2.")
        println("  Attempting conversion into elementary symmetric basis ",
                "(sa=a1+a2, pa=a1*a2, sb=b1+b2, pb=b1*b2)...")
        flush(stdout)

        Rsym, (sa, pa, sb, pb) = polynomial_ring(F, ["sa", "pa", "sb", "pb"])

        function try_symmetric_rewrite(f)
            try
                Rext, (a1e,a2e,b1e,b2e,sae,pae,sbe,pbe) = polynomial_ring(
                    F, ["a1","a2","b1","b2","sa","pa","sb","pb"])
                incl = hom(Rcoef, Rext, [a1e,a2e,b1e,b2e])
                fe = incl(f)
                fe2 = evaluate(fe, [a1e, sae - a1e, b1e, b2e, sae, pae, sbe, pbe])
                relation_a = a1e^2 - sae*a1e + pae
                q, r = divrem(fe2, relation_a)
                fe3 = r
                fe4 = evaluate(fe3, [a1e, a2e, b1e, sbe - b1e, sae, pae, sbe, pbe])
                relation_b = b1e^2 - sbe*b1e + pbe
                q2, r2 = divrem(fe4, relation_b)
                fe5 = r2
                deg_a1_remaining = degree(fe5, a1e)
                deg_b1_remaining = degree(fe5, b1e)
                if deg_a1_remaining > 0 || deg_b1_remaining > 0
                    return (nothing, "residual a1/b1-degree after reduction " *
                            "(a1:$deg_a1_remaining, b1:$deg_b1_remaining) -- " *
                            "symmetric rewrite incomplete, reporting raw reduced form")
                end
                Bctx = MPolyBuildCtx(Rsym)
                for (c, exps) in zip(coefficients(fe5), AbstractAlgebra.exponent_vectors(fe5))
                    if exps[1] != 0 || exps[2] != 0 || exps[3] != 0 || exps[4] != 0
                        return (nothing, "unexpected leftover a/b generator in reduced form")
                    end
                    push_term!(Bctx, c, exps[5:8])
                end
                fsym = finish(Bctx)
                return (fsym, nothing)
            catch err
                return (nothing, sprint(showerror, err))
            end
        end

        for (gname, k, f) in all_coefs
            if iszero(f)
                println("    $gname coeff of T^$k: zero, skipping symmetric rewrite")
                continue
            end
            before_terms = length(terms(f))
            before_deg = total_degree(f)
            fsym, err = try_symmetric_rewrite(f)
            if fsym === nothing
                println("    $gname coeff of T^$k: rewrite skipped/failed (", err, ")")
            else
                after_terms = length(terms(fsym))
                after_deg = total_degree(fsym)
                pct = before_terms == 0 ? 0.0 : 100.0 * (1 - after_terms/before_terms)
                println("    $gname coeff of T^$k: degree $before_deg -> $after_deg,  ",
                        "terms $before_terms -> $after_terms  ",
                        "(", round(pct, digits=1), "% reduction)")
            end
            flush(stdout)
        end
    else
        println("  NOT fully symmetric under both swaps for every coefficient -- ",
                "skipping symmetric-basis rewrite (would be unsound).")
    end
    flush(stdout)

    _run_part_c5_and_de!(F, cr, ts, bm, g1_coefs_poly, g2_coefs_poly, all_coefs,
                          safe_factor_report, coef_as_poly)

    return nothing
end

"""
    _run_part_c5_and_de!(F, cr, ts, bm, g1_coefs_poly, g2_coefs_poly, all_coefs,
                          safe_factor_report, coef_as_poly)

Original lines 5842-6516 (PART C.5, PART D, PART E). Internal helper
called only from `run_parts_a_to_e_diagnostic` -- split out purely to
keep that function from being one single several-hundred-line body, not
because this piece is independently reusable (it still shares
`g1_coefs_poly`/`g2_coefs_poly`/`all_coefs`/`safe_factor_report`/
`coef_as_poly` with its caller, passed through explicitly rather than
recomputed). Returns `nothing`; exists for its printed diagnostic output.
"""
function _run_part_c5_and_de!(F, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix,
                               g1_coefs_poly::Vector, g2_coefs_poly::Vector, all_coefs,
                               safe_factor_report, coef_as_poly)
    name = ts.name
    Rcoef = cr.Rcoef
    a1_c, a2_c, b1_c, b2_c = cr.a1_c, cr.a2_c, cr.b1_c, cr.b2_c
    B = bm.B
    g1_T, g2_T = cr.g1_T, cr.g2_T

    # ------------------------------------------------------------------
    # PART C.5: PARTIAL symmetrization diagnostic (original lines
    # 5842-6419). See the original's own extensive comment for why this
    # exists (PART C only fires when a coefficient is symmetric under
    # BOTH swaps at once; this handles the one-sided case) and the
    # IMPLEMENTATION NOTE on why degree-by-degree substitution is used
    # instead of `divrem` against a 2-term relation (degrevlex tie-
    # breaking silently made that a no-op the first time it was tried).
    # ------------------------------------------------------------------
    println()
    println("--- PART C.5: partial symmetrization diagnostic ---")
    flush(stdout)

    Rb_only, (a1b, a2b, sbb, pbb) = polynomial_ring(F, ["a1", "a2", "sb", "pb"])
    Ra_only, (saa, paa, b1a, b2a) = polynomial_ring(F, ["sa", "pa", "b1", "b2"])

    Rext_c5, (a1c5, a2c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5) = polynomial_ring(
        F, ["a1", "a2", "b1", "b2", "sa", "pa", "sb", "pb"])
    incl_c5 = hom(Rcoef, Rext_c5, [a1c5, a2c5, b1c5, b2c5])

    function reduce_quadratic!(coeffs_by_deg::Dict{Int,Any}, lin, const_term)
        maxd = maximum(keys(coeffs_by_deg))
        for d in maxd:-1:2
            c = get(coeffs_by_deg, d, nothing)
            if c === nothing || iszero(c)
                delete!(coeffs_by_deg, d)
                continue
            end
            delete!(coeffs_by_deg, d)
            coeffs_by_deg[d-1] = get(coeffs_by_deg, d-1, zero(c)) + lin*c
            coeffs_by_deg[d-2] = get(coeffs_by_deg, d-2, zero(c)) + const_term*c
        end
        return coeffs_by_deg
    end

    function symmetrize_b_only(f; debug::Bool=false)
        fe = incl_c5(f)
        fe2 = evaluate(fe, [a1c5, a2c5, b1c5, sbc5 - b1c5, sac5, pac5, sbc5, pbc5])
        d = degree(fe2, b1c5)
        coeffs_by_deg = Dict{Int,Any}()
        for k in 0:d
            ck = coeff(fe2, [var_index(b1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        reduce_quadratic!(coeffs_by_deg, sbc5, -pbc5)
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            return (nothing, "residual b1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (b1,b2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        Bctx = MPolyBuildCtx(Rb_only)
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            if exps[3] != 0 || exps[4] != 0
                return (nothing, "unexpected leftover b1/b2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate b1,b2")
            end
            if exps[5] != 0 || exps[6] != 0
                return (nothing, "unexpected sa/pa dependence in a b-only rewrite " *
                        "(exps=$exps) -- sa,pa should never appear here")
            end
            push_term!(Bctx, c, [exps[1], exps[2], exps[7], exps[8]])
        end
        fsym = finish(Bctx)
        return (fsym, nothing)   # lives in Rb_only: (a1,a2,sb,pb)
    end

    function symmetrize_a_only(f; debug::Bool=false)
        fe = incl_c5(f)
        fe2 = evaluate(fe, [a1c5, sac5 - a1c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5])
        d = degree(fe2, a1c5)
        coeffs_by_deg = Dict{Int,Any}()
        for k in 0:d
            ck = coeff(fe2, [var_index(a1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        reduce_quadratic!(coeffs_by_deg, sac5, -pac5)
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            return (nothing, "residual a1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (a1,a2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        Bctx = MPolyBuildCtx(Ra_only)
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            if exps[1] != 0 || exps[2] != 0
                return (nothing, "unexpected leftover a1/a2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate a1,a2")
            end
            if exps[7] != 0 || exps[8] != 0
                return (nothing, "unexpected sb/pb dependence in an a-only rewrite " *
                        "(exps=$exps) -- sb,pb should never appear here")
            end
            push_term!(Bctx, c, [exps[5], exps[6], exps[3], exps[4]])
        end
        fsym = finish(Bctx)
        return (fsym, nothing)   # lives in Ra_only: (sa,pa,b1,b2)
    end

    println()
    println("  Section 1: per-coefficient single-pair symmetry classification")
    println("  (independent of PART C's all-coefficients-at-once verdict above)")
    flush(stdout)

    swap_a = hom(Rcoef, Rcoef, [a2_c, a1_c, b1_c, b2_c])
    swap_b = hom(Rcoef, Rcoef, [a1_c, a2_c, b2_c, b1_c])
    function is_symmetric_under(f, phi)
        return iszero(f - phi(f))
    end

    c5_class = Dict{Tuple{String,Int},Symbol}()
    for (gname, k, f) in all_coefs
        if iszero(f)
            c5_class[(gname,k)] = :zero
            println("    $gname coeff of T^$k: zero, skipping")
            continue
        end
        depends_on_a = degree(f, a1_c) > 0 || degree(f, a2_c) > 0
        depends_on_b = degree(f, b1_c) > 0 || degree(f, b2_c) > 0
        sym_a = is_symmetric_under(f, swap_a)
        sym_b = is_symmetric_under(f, swap_b)
        local cls
        if !depends_on_a && !depends_on_b
            cls = :indep_of_both
        elseif !depends_on_b
            cls = :indep_of_b
        elseif !depends_on_a
            cls = :indep_of_a
        elseif sym_a && sym_b
            cls = :both
        elseif sym_a
            cls = :a_only
        elseif sym_b
            cls = :b_only
        else
            cls = :neither
        end
        c5_class[(gname,k)] = cls
        println("    $gname coeff of T^$k: class=", cls,
                "  (a1<->a2? ", sym_a, ", b1<->b2? ", sym_b,
                ", depends_on_a=", depends_on_a, ", depends_on_b=", depends_on_b, ")")
    end
    flush(stdout)

    println()
    println("  Section 2: partial rewrite term/degree reduction, per coefficient")
    flush(stdout)

    c5_rewritten = Dict{Tuple{String,Int},Any}()
    debug_done_b = false
    debug_done_a = false
    for (gname, k, f) in all_coefs
        cls = c5_class[(gname,k)]
        if cls == :zero
            continue
        elseif cls == :both
            println("    $gname coeff of T^$k: fully symmetric (both pairs) -- ",
                    "see PART C above, not repeated here")
            continue
        elseif cls == :neither
            println("    $gname coeff of T^$k: symmetric under NEITHER swap -- ",
                    "no partial symmetrization possible")
            continue
        elseif cls == :indep_of_both
            println("    $gname coeff of T^$k: independent of a1,a2,b1,b2 entirely -- ",
                    "already minimal, no symmetrization applicable")
            continue
        elseif cls == :indep_of_b
            println("    $gname coeff of T^$k: VACUOUS b-symmetry -- coefficient does ",
                    "not depend on b1,b2 at all (only a1,a2); already minimal in b.")
            continue
        elseif cls == :indep_of_a
            println("    $gname coeff of T^$k: VACUOUS a-symmetry -- coefficient does ",
                    "not depend on a1,a2 at all (only b1,b2); already minimal in a.")
            continue
        end

        before_terms = length(terms(f))
        before_deg = total_degree(f)

        if cls == :b_only
            do_dbg = !debug_done_b
            do_dbg && (debug_done_b = true)
            fsym, err = symmetrize_b_only(f; debug=do_dbg)
            pairname = "b"
        else # :a_only
            do_dbg = !debug_done_a
            do_dbg && (debug_done_a = true)
            fsym, err = symmetrize_a_only(f; debug=do_dbg)
            pairname = "a"
        end

        if fsym === nothing
            println("    $gname coeff of T^$k: rewrite FAILED (", err, ")")
        else
            after_terms = length(terms(fsym))
            after_deg = total_degree(fsym)
            pct = before_terms == 0 ? 0.0 : 100.0 * (1 - after_terms/before_terms)
            println("    $gname coeff of T^$k: symmetrized ($pairname-pair only)  ",
                    "degree $before_deg -> $after_deg,  terms $before_terms -> $after_terms  ",
                    "(", round(pct, digits=1), "% reduction)")
            c5_rewritten[(gname,k)] = (fsym, cls)
        end
        flush(stdout)
    end

    println()
    println("  Section 2 summary: aggregate term counts, symmetrized vs raw")
    let
        raw_total = 0
        sym_total = 0
        n_rewritten = 0
        for (gname, k, f) in all_coefs
            cls = c5_class[(gname,k)]
            if cls == :a_only || cls == :b_only
                haskey(c5_rewritten, (gname,k)) || continue
                raw_total += length(terms(f))
                sym_total += length(terms(c5_rewritten[(gname,k)][1]))
                n_rewritten += 1
            end
        end
        if n_rewritten > 0
            pct = 100.0 * (1 - sym_total/raw_total)
            println("    $n_rewritten coefficient(s) partially symmetrized: ",
                    "total terms $raw_total -> $sym_total  (", round(pct, digits=1), "% reduction)")
        else
            println("    no coefficients were eligible for partial symmetrization ",
                    "(all were :both, :neither, or :zero)")
        end
    end
    flush(stdout)

    println()
    println("  Section 3: cross-ring combination check")
    flush(stdout)

    g1_b_only_present = any(c5_class[("g1",k)] == :b_only for k in 0:4 if haskey(c5_class,("g1",k)))
    g2_a_only_present = any(c5_class[("g2",k)] == :a_only for k in 0:4 if haskey(c5_class,("g2",k)))

    if g1_b_only_present && g2_a_only_present
        println("    g1 has (b1,b2)-symmetric coefficient(s); g2 has (a1,a2)-symmetric ",
                "coefficient(s) -- this is the expected asymmetric case from the log.")
        println("    g1's natural target ring after rewrite: (a1,a2,sb,pb)")
        println("    g2's natural target ring after rewrite: (sa,pa,b1,b2)")
        println("    Common ring containing BOTH without reintroducing any variable ",
                "individually: NONE.")
        println("    Only combination routes available, in order of cost:")
        println("      (i)   map BOTH into the raw ring (a1,a2,b1,b2) -- discards all")
        println("            symmetrization savings before the combination step.")
        println("      (ii)  desymmetrize the OTHER pair back out of each side via the")
        println("            quadratic formula before combining -- reintroduces a")
        println("            degree-2 field extension per desymmetrized pair.")
        println("      (iii) fully symmetrize BOTH g1 and g2 in BOTH pairs -- only valid")
        println("            if g1 is ALSO (a1,a2)-symmetric and g2 ALSO (b1,b2)-symmetric,")
        println("            which per PART C above is FALSE, so unavailable.")
        println("    VERDICT: partial symmetrization reduces individual size but does")
        println("    NOT by itself simplify the PART K combination step -- open sub-problem.")
    else
        g1_indep_b = any(get(c5_class, ("g1",k), nothing) == :indep_of_b for k in 0:4)
        g2_indep_a = any(get(c5_class, ("g2",k), nothing) == :indep_of_a for k in 0:4)
        if g1_indep_b && g2_indep_a
            println("    Did NOT find genuine b-only/a-only partial symmetry -- instead,")
            println("    Section 1 found g1's coefficients are entirely INDEPENDENT of")
            println("    b1,b2 and g2's are entirely INDEPENDENT of a1,a2 -- a narrower,")
            println("    stronger variable-dependence fact than partial symmetry, not")
            println("    assumed by PART D/E above -- worth re-deriving those diagnostics")
            println("    with this narrower variable dependence taken into account.")
        else
            println("    Did not find the previously-assumed g1:(b-only) / g2:(a-only) ",
                    "asymmetric pattern in this run's classification (see Section 1) -- ",
                    "re-check before relying on the analysis below.")
        end
    end
    flush(stdout)

    println()
    println("  Section 4: partially-symmetrized Bezout-entry-style size probe")
    flush(stdout)

    if haskey(c5_rewritten, ("g1",0)) && haskey(c5_rewritten, ("g2",0))
        f1sym, cls1 = c5_rewritten[("g1",0)]
        f2sym, cls2 = c5_rewritten[("g2",0)]
        raw_terms = length(terms(g1_coefs_poly[1])) + length(terms(g2_coefs_poly[1]))
        sym_terms = length(terms(f1sym)) + length(terms(f2sym))
        println("    g1[T^0] + g2[T^0] combined term count:")
        println("      raw (a1,a2,b1,b2) form:          ", raw_terms)
        println("      partially symmetrized form:      ", sym_terms,
                "  (", round(100.0*(1-sym_terms/raw_terms), digits=1), "% smaller)")
        println("    NOTE: this measures the SYMMETRIZED INTERMEDIATE size only --")
        println("    recombining still requires route (i) or (ii) above.")
    else
        println("    g1[T^0]/g2[T^0] not both eligible for partial symmetrization in ",
                "this run -- skipping Section 4 size probe (see Section 1 above).")
    end
    flush(stdout)

    println()
    println("PART C.5 COMPLETE")
    flush(stdout)

    # ------------------------------------------------------------------
    # PART D: Bezout entry sparsity / factoring analysis
    # ------------------------------------------------------------------
    println()
    println("--- PART D: Bezout entry sparsity analysis ---")
    flush(stdout)

    function monomial_support_report(f; indent::String="        ")
        nv = nvars(parent(f))
        appears = falses(nv)
        for exps in AbstractAlgebra.exponent_vectors(f)
            for (idx, e) in enumerate(exps)
                if e != 0
                    appears[idx] = true
                end
            end
        end
        vnames = [string(g) for g in gens(parent(f))]
        present = [vnames[i] for i in 1:nv if appears[i]]
        println(indent, "variables appearing: ", present)
    end

    for i in 0:3, j in i:3
        f = B[(i,j)]
        println("  B[$i,$j]:")
        println("    total_degree=", total_degree(f), "  terms=", length(terms(f)))
        monomial_support_report(f)
        safe_factor_report(f; label="", indent="    ")
        flush(stdout)
    end

    # ------------------------------------------------------------------
    # PART E: PRS growth prediction -- single pseudo-remainder step only
    # ------------------------------------------------------------------
    println()
    println("--- PART E: PRS growth prediction (ONE pseudo-remainder step only) ---")
    flush(stdout)

    try
        t0e = time()
        r_prem = pseudorem(g1_T, g2_T)
        el_e = time() - t0e
        println("  prem(g1_T, g2_T) computed in ", round(el_e, digits=3), "s")
        if iszero(r_prem)
            println("  r is IDENTICALLY ZERO (g2_T | g1_T over Kcoef) -- degenerate case, inspect inputs.")
        else
            deg_r = degree(r_prem)
            println("  degree in T of r: ", deg_r)
            max_terms = 0
            local max_deg = 0
            for k in 0:deg_r
                ck = coeff(r_prem, k)
                ck_num = coef_as_poly(ck)
                tk = length(terms(ck_num))
                dk = total_degree(ck_num)
                max_terms = max(max_terms, tk)
                max_deg = max(max_deg, dk)
                println("    coeff of T^$k in r: degree=", dk, "  terms=", tk)
            end
            println("  --- summary: max coeff term count=", max_terms,
                    "  max coeff total_degree=", max_deg, " ---")
            r_coefs_nonzero = [coef_as_poly(coeff(r_prem, k)) for k in 0:deg_r
                                if !iszero(coeff(r_prem, k))]
            if length(r_coefs_nonzero) >= 2
                g_r = reduce(gcd, r_coefs_nonzero)
                println("  gcd(all coefficients of r): degree=", total_degree(g_r),
                        "  terms=", length(terms(g_r)),
                        total_degree(g_r) > 0 ? "  <-- NONTRIVIAL" : "  (unit)")
            end
        end
    catch err
        println("  prem() FAILED/skipped: ", sprint(showerror, err))
    end
    flush(stdout)

    println()
    println("=" ^ 70)
    println("PARTS A-E DIAGNOSTIC COMPLETE -- $name")
    println("=" ^ 70)
    flush(stdout)

    return nothing
end
################################################################################
# PART F: exploit p_i in F[a1,a2] / q_j in F[b1,b2] separability. Original
# lines 6518-8013.
#
# Kept as one function rather than split further: the disk-sharded
# checkpoint/resume/consolidate/cleanup sequence is a single stateful
# process where correctness (and, as of the ordering fix below, peak
# memory) depends on strict ordering:
#
#   merge any pre-existing shards from a prior run into detB_concrete
#   FIRST, while it's still zero(Rcoef) -> run the substitution loop for
#   the remaining terms, periodically consolidating this run's own
#   accumulating delta-shards on disk so they never pile up unboundedly
#   -> stat -> save -> only THEN clean up shards, gated on a passing
#   crosscheck.
#
# NOTE on the merge ordering specifically: an earlier version of this
# function did the pre-existing-shard merge AFTER the substitution loop
# instead of before it. That ordering was the cause of OOMs specifically
# on RESUME (not on a from-scratch run): by the time that merge ran,
# detB_concrete already held the full result of every new term processed
# in the resumed session (i.e. it was already close to its final,
# largest size), and the merge then loaded and added in every leftover
# shard from the previous session ON TOP of that already-large object --
# so resume's peak memory was strictly worse than a from-scratch run's,
# which never has an "old shard pile" to merge in at all. Doing the
# merge upfront instead means resume's memory profile matches a
# from-scratch run: the loop always starts from a `detB_concrete` that
# already reflects everything done so far, and just keeps growing it,
# exactly as a from-scratch run would.
#
# Splitting it into separate top-level functions would mean threading a
# large amount of shared mutable state (detB_concrete, shard paths,
# progress counters, the various caches) through extra parameters with
# no reuse benefit -- nothing else in this module needs a second
# disk-sharded accumulator.
################################################################################

"""
    run_part_f_bezout!(F, p::Int, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix;
                        scratch_dir)

Original lines 6518-8013 (PART F). Only meaningful when
`ts.d1T == ts.d2T == 4` (checked by the caller via `bm !== nothing`,
matching `build_concrete_bezout_diagnostic`'s own gating). Computes
`det(Bpq)` in an ABSTRACT 10-variable ring `F[P0..P4,Q0..Q4]` (cheap:
degree <=8, no dependence on how large the real `a1,a2,b1,b2`
coefficients are), then substitutes the real `p_i(a1,a2)` / `q_j(b1,b2)`
polynomials in via a disk-sharded, checkpointed, resumable streaming
substitution (STAGE 1: substitute P only, leaving Q abstract in a tower
ring `Ra[Q0..Q4]`; STAGE 2: substitute Q, folding each term's
contribution into `detB_concrete` in bounded-size chunks). Saves the
result to `ts.RESULTANT_FILE` and returns it (`res_num`). `p` is the
field characteristic, needed to size-check the flat-binary shard
coefficient type.

Raises an error (never silently proceeds) if: a shard coefficient
doesn't fit `SHARD_COEFF_TYPE`, a shard's exponent-array length is
inconsistent with its term count, a `.native` shard has the wrong
format-magic header, `detB_concrete` ends up with zero terms after the
upfront merge and substitution loop, `var_names` mismatches `Rcoef`'s
variable count, a term's exponent-vector length is inconsistent with
`Rcoef`, or shard cleanup fails to remove a file it expected to remove.
"""
function run_part_f_bezout!(F, p::Int, cr::CoefRing, ts::TargetSetup, bm::BezoutMatrix;
                             scratch_dir::String = joinpath(ELIM2_ROOT_DIR, "part_k_results"))
    name = ts.name
    Rcoef = cr.Rcoef
    a1_c, a2_c, b1_c, b2_c = cr.a1_c, cr.a2_c, cr.b1_c, cr.b2_c
    B = bm.B

    println()
    println("--- PART F: abstract-variable (P,Q)-separated Bezout/resultant ---")
    println("  (exploits p_i in F[a1,a2] / q_j in F[b1,b2] confirmed by the")
    println("  Section-1 fix above; see PART D's exact 289*289=83521 entry")
    println("  term counts for the empirical signature that motivated this.)")
    flush(stdout)

    Rpq, pq_gens = polynomial_ring(F, ["P0","P1","P2","P3","P4","Q0","Q1","Q2","Q3","Q4"])
    P0,P1,P2,P3,P4,Q0,Q1,Q2,Q3,Q4 = pq_gens
    Pvec = [P0,P1,P2,P3,P4]
    Qvec = [Q0,Q1,Q2,Q3,Q4]

    abstract_bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function abstract_bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(abstract_bracket_cache, key)
            i, j = key
            abstract_bracket_cache[key] = Pvec[i+1]*Qvec[j+1] - Pvec[j+1]*Qvec[i+1]
        end
        return m < n ? abstract_bracket_cache[key] : -abstract_bracket_cache[key]
    end

    Bpq = Dict{Tuple{Int,Int}, Any}()
    Bpq[(0,0)] = abstract_bracket(0,1)
    Bpq[(0,1)] = abstract_bracket(0,2)
    Bpq[(0,2)] = abstract_bracket(0,3)
    Bpq[(0,3)] = abstract_bracket(0,4)
    Bpq[(1,1)] = abstract_bracket(0,3) + abstract_bracket(1,2)
    Bpq[(1,2)] = abstract_bracket(0,4) + abstract_bracket(1,3)
    Bpq[(1,3)] = abstract_bracket(1,4)
    Bpq[(2,2)] = abstract_bracket(1,4) + abstract_bracket(2,3)
    Bpq[(2,3)] = abstract_bracket(2,4)
    Bpq[(3,3)] = abstract_bracket(3,4)
    Bpq[(1,0)] = Bpq[(0,1)]
    Bpq[(2,0)] = Bpq[(0,2)]
    Bpq[(3,0)] = Bpq[(0,3)]
    Bpq[(2,1)] = Bpq[(1,2)]
    Bpq[(3,1)] = Bpq[(1,3)]
    Bpq[(3,2)] = Bpq[(2,3)]

    println("  Abstract Bezout entries (in F[P0..P4,Q0..Q4], BEFORE substitution):")
    for i in 0:3, j in 0:3
        f = Bpq[(i,j)]
        println("    Bpq[$i,$j]: degree=", total_degree(f), "  terms=", length(terms(f)))
    end
    flush(stdout)

    println("  Assembling abstract 4x4 matrix and computing det()...")
    flush(stdout)
    t0f = time()
    Bpq_mat = matrix(Rpq, [Bpq[(i,j)] for i in 0:3, j in 0:3])
    detB_abstract = det(Bpq_mat)
    el_f = time() - t0f
    println("  det(Bpq) computed in ", round(el_f, digits=3), "s: degree=",
            total_degree(detB_abstract), "  terms=", length(terms(detB_abstract)))
    flush(stdout)

    # -- Recover g1_coefs_poly / g2_coefs_poly (PART A's Rcoef-lifted
    # coefficient list) from bm.p_coef/bm.q_coef, exactly as PART A did,
    # since PART F needs them independently of whether the full PARTS
    # A-E diagnostic ran first.
    function coef_as_poly(c)
        den = denominator(c)
        if !is_unit(den)
            println("      WARNING: coefficient has non-unit denominator (degree=",
                    total_degree(den), ") -- reporting numerator only.")
        end
        return Rcoef(numerator(c))
    end
    g1_coefs_poly = [coef_as_poly(bm.p_coef[k+1]) for k in 0:4]
    g2_coefs_poly = [coef_as_poly(bm.q_coef[k+1]) for k in 0:4]

    println("  --- STAGE 1: substituting P_i -> p_i(a1,a2) only,",
            " Q left abstract (R[P][Q]-style intermediate) ---")
    flush(stdout)

    t0stage1 = time()

    Ra, (a1_r, a2_r) = polynomial_ring(F, ["a1", "a2"])

    function lift_to_Ra(f)
        ctx = MPolyBuildCtx(Ra)
        for (c, exps) in zip(coefficients(f), AbstractAlgebra.exponent_vectors(f))
            ea1, ea2, eb1, eb2 = exps
            if eb1 != 0 || eb2 != 0
                error("lift_to_Ra: term has nonzero b1/b2 exponent ($eb1,$eb2) -- ",
                      "this P-coefficient was not purely (a1,a2) as PART A's ",
                      "diagnostic assumed. Refusing to silently drop content.")
            end
            push_term!(ctx, c, [ea1, ea2])
        end
        return finish(ctx)
    end
    g1_coefs_Ra = [lift_to_Ra(p) for p in g1_coefs_poly]

    Rmid, Qmid_gens = polynomial_ring(Ra, ["Q0", "Q1", "Q2", "Q3", "Q4"])

    stage1_images = vcat(
        [Rmid(c) for c in g1_coefs_Ra],
        Qmid_gens,
    )
    detB_mid = evaluate(detB_abstract, stage1_images)

    el_stage1 = time() - t0stage1
    mid_terms_list = collect(terms(detB_mid))
    println("  STAGE 1 complete in ", round(el_stage1, digits=3),
            "s: ", length(mid_terms_list), " Q-monomial terms")
    flush(stdout)

    # -- STAGE 2 setup: disk-sharded checkpointing scratch dir.
    PARTF_SCRATCH_DIR = joinpath(scratch_dir, "..", "part_f_scratch", name)
    mkpath(PARTF_SCRATCH_DIR)
    shards_dir     = joinpath(PARTF_SCRATCH_DIR, "shards")
    mkpath(shards_dir)
    shard_tmpfile  = joinpath(PARTF_SCRATCH_DIR, "shard.native.tmp")
    progress_file  = joinpath(PARTF_SCRATCH_DIR, "progress.txt")
    manifest_file  = joinpath(PARTF_SCRATCH_DIR, "manifest.txt")

    shard_path(upto_term_idx) = joinpath(shards_dir, "shard_" * lpad(upto_term_idx, 6, '0') * ".native")
    function existing_shard_paths()
        !isdir(shards_dir) && return String[]
        names = filter(readdir(shards_dir)) do f
            startswith(f, "shard_") && (endswith(f, ".native") || endswith(f, ".oscar"))
        end
        return sort(joinpath.(shards_dir, names))
    end

    detB_terms = mid_terms_list
    n_terms = length(detB_terms)
    println("  substituting ", n_terms, " terms -> ", shards_dir)
    flush(stdout)

    t0terms = time()
    n_already_done = 0
    if isfile(progress_file)
        n_already_done = parse(Int, strip(read(progress_file, String)))
        if n_already_done > 0
            shard_paths = existing_shard_paths()
            println("  resuming: ", n_already_done, "/", n_terms,
                    " terms, ", length(shard_paths), " shard(s)")
            flush(stdout)
        end
    end

    SHARD_COEFF_TYPE = UInt32
    SHARD_EXP_TYPE   = Int32
    SHARD_FORMAT_MAGIC = UInt64(0xF1A7B10C_00000002)

    p > typemax(SHARD_COEFF_TYPE) &&
        error("run_part_f_bezout!: field characteristic p=$p does not fit in " *
              "$(SHARD_COEFF_TYPE) (max $(typemax(SHARD_COEFF_TYPE))) -- " *
              "widen SHARD_COEFF_TYPE before writing shards, or every " *
              "coefficient write below will silently truncate")

    function read_rss_mb()
        for line in eachline("/proc/self/status")
            if startswith(line, "VmRSS:")
                parts = split(line)
                return parse(Int, parts[2]) / 1024.0
            end
        end
        return -1.0
    end

    function save_shard_native(path, poly)
        println("      save_shard_native: starting streamed write to ", path,
                " (RSS=", read_rss_mb(), "MB)")
        flush(stdout)
        open(path, "w") do io
            write(io, SHARD_FORMAT_MAGIC)
            n_terms_pos = position(io)
            write(io, Int64(0))
            term_idx = 0
            for (cf, ev) in zip(coefficients(poly), AbstractAlgebra.exponent_vectors(poly))
                term_idx += 1
                cv = lift(ZZ, cf)
                (cv < 0 || cv > typemax(SHARD_COEFF_TYPE)) &&
                    error("save_shard_native: coefficient $cv at term $term_idx out of " *
                          "range for $(SHARD_COEFF_TYPE) in $path -- refusing to " *
                          "write a shard that would silently corrupt data")
                write(io, SHARD_COEFF_TYPE(cv))
                length(ev) != 4 &&
                    error("save_shard_native: expected 4 exponents (a1,a2,b1,b2), " *
                          "got $(length(ev)) at term $term_idx in $path")
                for j in 1:4
                    write(io, SHARD_EXP_TYPE(ev[j]))
                end
                if term_idx % 200_000 == 0
                    println("        save_shard_native: ", term_idx,
                            " terms written, RSS=", read_rss_mb(), "MB")
                    flush(stdout)
                end
            end
            end_pos = position(io)
            seek(io, n_terms_pos)
            write(io, Int64(term_idx))
            seek(io, end_pos)
            println("      save_shard_native: finished, ", term_idx,
                    " terms written, RSS=", read_rss_mb(), "MB")
            flush(stdout)
        end
        return nothing
    end

    function load_shard_native(sp)
        t0 = time()
        fsize_mb = filesize(sp) / 1024 / 1024
        println("    ", basename(sp), ": starting bulk read (", round(fsize_mb, digits=0),
                " MB on disk)...")
        flush(stdout)
        n_terms_shard, coeffs_in, exps_in = open(sp, "r") do io
            magic = read(io, UInt64)
            magic != SHARD_FORMAT_MAGIC &&
                error("load_shard_native: $sp does not have the expected flat-" *
                      "binary format header (got magic=$(magic), expected " *
                      "$(SHARD_FORMAT_MAGIC)) -- this is almost certainly an " *
                      "OLD-format .native shard written by an earlier version. " *
                      "Delete all .native shards under this scratch dir and " *
                      "let them regenerate, or restore from .oscar shards if " *
                      "available.")
            nt = read(io, Int64)
            cf = Vector{SHARD_COEFF_TYPE}(undef, nt)
            ex = Vector{SHARD_EXP_TYPE}(undef, 4 * nt)
            read!(io, cf)
            read!(io, ex)
            (nt, cf, ex)
        end
        length(exps_in) != 4 * n_terms_shard &&
            error("load_shard_native: corrupt shard $sp -- exponent array " *
                  "length $(length(exps_in)) is not 4x the term count " *
                  "$n_terms_shard ($(4 * n_terms_shard) expected)")
        println("    ", basename(sp), ": read ", n_terms_shard, " terms in ",
                round(time() - t0, digits=1), "s; rebuilding polynomial...")
        flush(stdout)
        t1 = time()
        rebuild_ctx = MPolyBuildCtx(Rcoef)
        exps_buf = Vector{Int}(undef, 4)
        for i in 1:n_terms_shard
            base = 4 * (i - 1)
            exps_buf[1] = Int(exps_in[base + 1])
            exps_buf[2] = Int(exps_in[base + 2])
            exps_buf[3] = Int(exps_in[base + 3])
            exps_buf[4] = Int(exps_in[base + 4])
            push_term!(rebuild_ctx, F(Int(coeffs_in[i])), exps_buf)
            if i % 2_000_000 == 0
                el = time() - t1
                rate = i / el
                eta = (n_terms_shard - i) / rate
                println("      rebuilt ", i, "/", n_terms_shard, " terms (",
                        round(rate, digits=0), " terms/s, ETA ",
                        round(eta, digits=0), "s)...")
                flush(stdout)
            end
        end
        rebuilt = finish(rebuild_ctx)
        println("    ", basename(sp), ": rebuilt ok in ",
                round(time() - t1, digits=1), "s (total incl. deserialize: ",
                round(time() - t0, digits=1), "s)")
        flush(stdout)
        return rebuilt
    end

    function load_shard_rebuilt(sp)
        loaded = load(sp)
        loaded_n_terms = length(loaded)
        print("    ", basename(sp), ": loaded ", loaded_n_terms, " terms")
        flush(stdout)

        local rebuilt
        try
            rebuilt = Rcoef(loaded)
            print("; cheap coercion ok\n")
        catch e
            println()
            println("      cheap coercion failed (", typeof(e), ") -- falling",
                    " back to term-by-term rebuild for this shard (", loaded_n_terms,
                    " terms). Printing progress every 500k terms:")
            flush(stdout)
            rebuild_ctx = MPolyBuildCtx(Rcoef)
            n_pushed = 0
            t0rebuild = time()
            for (c, exps) in zip(coefficients(loaded), AbstractAlgebra.exponent_vectors(loaded))
                push_term!(rebuild_ctx, F(c), exps)
                n_pushed += 1
                if n_pushed % 500_000 == 0
                    println("      rebuilt ", n_pushed, "/", loaded_n_terms,
                            " terms (", round(time() - t0rebuild, digits=1), "s elapsed)")
                    flush(stdout)
                end
            end
            rebuilt = finish(rebuild_ctx)
            println("      term-by-term rebuild complete: ", n_pushed, " terms in ",
                    round(time() - t0rebuild, digits=1), "s.")
        end
        loaded = nothing
        return rebuilt
    end

    detB_concrete = zero(Rcoef)

    HAVE_INPLACE_ADD = applicable(add!, detB_concrete, detB_concrete, detB_concrete)
    HAVE_SAFE_SELF_ALIAS_ADD = false
    if HAVE_INPLACE_ADD
        _probe = Rcoef(gens(Rcoef)[1])
        _probe_expected = _probe + _probe
        _probe_copy = deepcopy(_probe)
        add!(_probe_copy, _probe_copy, _probe)
        HAVE_SAFE_SELF_ALIAS_ADD = (_probe_copy == _probe_expected)
    end

    if HAVE_SAFE_SELF_ALIAS_ADD
        println("  using in-place add!")
    elseif HAVE_INPLACE_ADD
        println("  add! unsafe here, falling back to +")
    else
        println("  add! unavailable, falling back to +")
    end
    flush(stdout)

    # -- UPFRONT MERGE PASS: fold in any shards left over from a previous
    # (crashed/interrupted) run, BEFORE the new-terms loop below runs.
    #
    # This used to happen AFTER the new-terms loop (see git history / the
    # old "FINAL MERGE PASS" comment). That ordering was the actual OOM
    # cause on resume: by the time the old merge ran, detB_concrete already
    # held the full accumulated result of every new term processed this
    # session (i.e. it was already close to its final, largest size), and
    # the merge then loaded and added in every leftover delta-shard from
    # the previous session ON TOP of that -- so resume's peak memory was
    # "near-final detB_concrete" + "a pile of old shards being deserialized
    # one at a time," strictly worse than a from-scratch run ever sees.
    #
    # Doing the merge here instead means it runs while detB_concrete is
    # still zero(Rcoef) -- its cheapest possible state -- so resume's
    # memory profile matches a from-scratch run: by the time the new-terms
    # loop starts, detB_concrete already reflects all prior-session work as
    # a single accumulated polynomial, and the loop below just keeps
    # growing it exactly as it would from scratch.
    if n_already_done > 0
        shard_paths_to_merge = existing_shard_paths()
        println("  Upfront merge: folding ", length(shard_paths_to_merge),
                " shard(s) from previous run(s) into detB_concrete before",
                " processing new terms (", n_already_done, "/", n_terms,
                " terms' worth)...")
        flush(stdout)
        t0upfront = time()
        for (si, sp) in enumerate(shard_paths_to_merge)
            t0shard = time()
            shard_poly = endswith(sp, ".native") ? load_shard_native(sp) : load_shard_rebuilt(sp)
            if HAVE_SAFE_SELF_ALIAS_ADD
                add!(detB_concrete, detB_concrete, shard_poly)
            else
                detB_concrete = detB_concrete + shard_poly
            end
            shard_poly = nothing
            GC.gc(true)
            ccall(:malloc_trim, Cvoid, (Cint,), 0)
            println("    shard ", si, "/", length(shard_paths_to_merge), " (",
                    basename(sp), ") merged in ", round(time() - t0shard, digits=1),
                    "s, RSS=", read_rss_mb(), "MB")
            flush(stdout)
        end
        println("  Upfront merge complete in ", round(time() - t0upfront, digits=1),
                "s: detB_concrete now has ", length(terms(detB_concrete)),
                " terms, reflecting all ", n_already_done, " previously-",
                "completed terms. New-terms loop below starts from this base.")
        flush(stdout)
    end

    q_power_cache = Dict{Tuple{Int,Int}, Any}()

    function chunked_poly_mul(x, y; chunk::Int=200)
        x_terms = collect(terms(x))
        y_terms = collect(terms(y))
        nx = length(x_terms)
        ny = length(y_terms)
        result = zero(Rcoef)
        xi = 1
        while xi <= nx
            xe = min(xi + chunk - 1, nx)
            x_chunk = sum(x_terms[xi:xe]; init=zero(Rcoef))
            yi = 1
            while yi <= ny
                ye = min(yi + chunk - 1, ny)
                y_chunk = sum(y_terms[yi:ye]; init=zero(Rcoef))
                partial = x_chunk * y_chunk
                if HAVE_SAFE_SELF_ALIAS_ADD
                    add!(result, result, partial)
                else
                    result = result + partial
                end
                partial = nothing
                y_chunk = nothing
                yi = ye + 1
            end
            x_chunk = nothing
            xi = xe + 1
        end
        return result
    end

    function chunked_pow(base, e::Int; chunk::Int=200)
        e < 0 && throw(ArgumentError("chunked_pow: exponent must be non-negative, got $e"))
        e == 0 && return one(Rcoef)
        result = base
        remaining = e - 1
        while remaining > 0
            n_result_terms = length(terms(result))
            n_base_terms = length(terms(base))
            this_chunk = n_result_terms * n_base_terms > (200^2) ?
                max(20, round(Int, chunk / sqrt((n_result_terms * n_base_terms) / (200.0^2)))) :
                chunk
            result = chunked_poly_mul(result, base; chunk=this_chunk)
            remaining -= 1
        end
        return result
    end

    function cached_q_power(k::Int, e::Int)
        e <= 0 && throw(ArgumentError("cached_q_power: exponent must be positive, got $e for k=$k"))
        key = (k, e)
        cached = get(q_power_cache, key, nothing)
        cached !== nothing && return cached
        val = chunked_pow(g2_coefs_poly[k], e)
        q_power_cache[key] = val
        return val
    end

    function compute_b_side(t_exps)
        val = one(Rcoef)
        for k in 1:5
            eQk = t_exps[k]
            if eQk > 0
                factor = cached_q_power(k, eQk)
                n_val_terms = length(terms(val))
                n_factor_terms = length(terms(factor))
                this_chunk = n_val_terms * n_factor_terms > (200^2) ?
                    max(20, round(Int, 200 / sqrt((n_val_terms * n_factor_terms) / (200.0^2)))) :
                    200
                val = chunked_poly_mul(val, factor; chunk=this_chunk)
            end
        end
        return val
    end

    max_term_size_seen = 0
    max_term_size_idx = 0
    delta_since_checkpoint = zero(Rcoef)
    for (i, t) in enumerate(detB_terms)
        if i <= n_already_done
            continue
        end
        t0iter = time()
        rss_before = read_rss_mb()

        t0eval = time()
        t_exps = first(AbstractAlgebra.exponent_vectors(t))
        t_ra_coeff = first(coefficients(t))

        a_side = remap_to_final(t_ra_coeff, [a1_c, a2_c, b1_c, b2_c], [1, 2])
        b_side = compute_b_side(t_exps)

        this_size = length(terms(a_side)) * length(terms(b_side))
        if this_size > max_term_size_seen
            max_term_size_seen = this_size
            max_term_size_idx = i
        end

        BASELINE_SIDE_TERMS = 8385
        size_ratio = this_size / (BASELINE_SIDE_TERMS^2)
        PARTF_CHUNK = size_ratio > 1 ?
            max(20, round(Int, 200 / sqrt(size_ratio))) :
            200
        if size_ratio > 1
            println("      term ", i, ": this_size=", this_size,
                    " (", round(size_ratio, digits=1), "x baseline) -> PARTF_CHUNK=", PARTF_CHUNK)
            flush(stdout)
        end

        a_terms = collect(terms(a_side))
        b_terms = collect(terms(b_side))
        n_a_terms = length(a_terms)
        n_b_terms = length(b_terms)

        PARTF_CHUNK_GC_EVERY = 25
        n_chunk_pairs_done = 0

        this_term_sum = zero(Rcoef)
        a_chunk_start = 1
        while a_chunk_start <= n_a_terms
            a_chunk_end = min(a_chunk_start + PARTF_CHUNK - 1, n_a_terms)
            a_chunk = sum(a_terms[a_chunk_start:a_chunk_end]; init=zero(Rcoef))
            b_chunk_start = 1
            while b_chunk_start <= n_b_terms
                b_chunk_end = min(b_chunk_start + PARTF_CHUNK - 1, n_b_terms)
                b_chunk = sum(b_terms[b_chunk_start:b_chunk_end]; init=zero(Rcoef))
                partial = a_chunk * b_chunk
                if HAVE_SAFE_SELF_ALIAS_ADD
                    add!(this_term_sum, this_term_sum, partial)
                else
                    this_term_sum = this_term_sum + partial
                end
                partial = nothing
                b_chunk = nothing
                b_chunk_start = b_chunk_end + 1

                n_chunk_pairs_done += 1
                if n_chunk_pairs_done % PARTF_CHUNK_GC_EVERY == 0
                    GC.gc(true)
                    ccall(:malloc_trim, Cvoid, (Cint,), 0)
                end
            end
            a_chunk = nothing
            a_chunk_start = a_chunk_end + 1
        end

        if HAVE_SAFE_SELF_ALIAS_ADD
            add!(detB_concrete, detB_concrete, this_term_sum)
            add!(delta_since_checkpoint, delta_since_checkpoint, this_term_sum)
        else
            detB_concrete = detB_concrete + this_term_sum
            delta_since_checkpoint = delta_since_checkpoint + this_term_sum
        end
        this_term_sum = nothing

        a_side = nothing
        b_side = nothing
        a_terms = nothing
        b_terms = nothing
        el_eval = time() - t0eval
        rss_after_eval = read_rss_mb()

        t0fold = time()
        el_fold = time() - t0fold
        rss_after_fold = read_rss_mb()

        t0gc = time()
        GC.gc(true)
        ccall(:malloc_trim, Cvoid, (Cint,), 0)
        el_gc = time() - t0gc
        rss_after_gc = read_rss_mb()

        PARTF_CHECKPOINT_EVERY = 5
        do_checkpoint = (i % PARTF_CHECKPOINT_EVERY == 0) || (i == n_terms)

        local el_write, el_mv, el_prog, rss_after_save
        if do_checkpoint
            println("      checkpoint at term ", i, ": delta_since_checkpoint has ",
                    length(terms(delta_since_checkpoint)), " terms, RSS=", read_rss_mb(), "MB")
            flush(stdout)
            t0write = time()
            save_shard_native(shard_tmpfile, delta_since_checkpoint)
            el_write = time() - t0write

            t0mv = time()
            mv(shard_tmpfile, shard_path(i); force=true)
            el_mv = time() - t0mv

            t0prog = time()
            open(progress_file, "w") do io
                print(io, i)
            end
            el_prog = time() - t0prog

            rss_after_save = read_rss_mb()
            delta_since_checkpoint = zero(Rcoef)

            # -- PERIODIC SHARD CONSOLIDATION: every PARTF_CONSOLIDATE_EVERY
            # checkpoints, fold all current on-disk delta-shards into one
            # consolidated shard and delete the small originals. Without
            # this, a run interrupted late leaves behind one shard file per
            # PARTF_CHECKPOINT_EVERY terms for its ENTIRE duration (e.g.
            # thousands of tiny shards), all of which the upfront merge on
            # the next resume has to load and add in one at a time. This
            # keeps that count bounded to roughly PARTF_CONSOLIDATE_EVERY
            # shards at any point, regardless of how far the run has gotten.
            #
            # Uses a throwaway accumulator (not detB_concrete) so this
            # doesn't touch the loop's main running total or its memory
            # footprint -- consolidated_acc is built up and discarded
            # entirely within this block.
            PARTF_CONSOLIDATE_EVERY = 20
            n_checkpoints_done = div(i, PARTF_CHECKPOINT_EVERY)
            do_consolidate = (n_checkpoints_done % PARTF_CONSOLIDATE_EVERY == 0) && (i != n_terms)
            if do_consolidate
                shard_paths_to_consolidate = existing_shard_paths()
                if length(shard_paths_to_consolidate) > 1
                    println("      consolidating ", length(shard_paths_to_consolidate),
                            " shard(s) at term ", i, " into one, RSS=", read_rss_mb(), "MB")
                    flush(stdout)
                    t0consolidate = time()
                    consolidated_acc = zero(Rcoef)
                    for sp in shard_paths_to_consolidate
                        shard_poly = endswith(sp, ".native") ? load_shard_native(sp) : load_shard_rebuilt(sp)
                        if HAVE_SAFE_SELF_ALIAS_ADD
                            add!(consolidated_acc, consolidated_acc, shard_poly)
                        else
                            consolidated_acc = consolidated_acc + shard_poly
                        end
                        shard_poly = nothing
                    end
                    save_shard_native(shard_tmpfile, consolidated_acc)
                    consolidated_acc = nothing
                    # Consolidated shard is named after the current term
                    # index `i`, same convention as a normal checkpoint --
                    # existing_shard_paths()/the upfront merge don't care
                    # whether a shard came from one checkpoint or many, only
                    # that shard filenames are unique, and mv(...; force=true)
                    # below overwrites cleanly if `i` happens to collide with
                    # one of the shards being replaced.
                    consolidated_path = shard_path(i)
                    mv(shard_tmpfile, consolidated_path; force=true)
                    for sp in shard_paths_to_consolidate
                        sp != consolidated_path && rm(sp; force=false)
                    end
                    GC.gc(true)
                    ccall(:malloc_trim, Cvoid, (Cint,), 0)
                    println("      consolidation complete in ",
                            round(time() - t0consolidate, digits=1),
                            "s: ", length(shard_paths_to_consolidate),
                            " shard(s) -> 1 (", basename(consolidated_path),
                            "), RSS=", read_rss_mb(), "MB")
                    flush(stdout)
                end
            end
        else
            el_write = 0.0
            el_mv = 0.0
            el_prog = 0.0
            rss_after_save = rss_after_gc
        end

        el_save = el_write + el_mv + el_prog
        el_iter_measured = el_eval + el_fold + el_gc + el_save
        el_iter_actual = time() - t0iter
        el_unaccounted = el_iter_actual - el_iter_measured

        if el_eval > 2.0 || el_fold > 2.0 || el_gc > 2.0 || el_save > 2.0 || el_unaccounted > 2.0 || i <= 3
            println("      term ", i, " breakdown -- evaluate: ", round(el_eval, digits=1),
                    "s  fold(add!): ", round(el_fold, digits=1),
                    "s  gc(explicit): ", round(el_gc, digits=1),
                    "s  save(write): ", round(el_write, digits=1),
                    "s  mv(rename): ", round(el_mv, digits=1),
                    "s  progress-write: ", round(el_prog, digits=1),
                    "s  || measured total: ", round(el_iter_measured, digits=1),
                    "s  actual wall-clock: ", round(el_iter_actual, digits=1),
                    "s  UNACCOUNTED: ", round(el_unaccounted, digits=1), "s",
                    el_unaccounted > 2.0 ? "  <<<< still-unexplained gap" : "")
            flush(stdout)
        end

        if i % 10 == 0 || i == n_terms
            println("    folded term ", i, "/", n_terms,
                    " (this term=", this_size, " terms, largest so far=term ",
                    max_term_size_idx, " w/ ", max_term_size_seen, " terms,",
                    " running total=", length(terms(detB_concrete)), " terms) -- ",
                    round(time() - t0terms, digits=1), "s elapsed")
            flush(stdout)
        end
    end
    el_sub = time() - t0terms
    println("  all ", n_terms, " terms substituted and accumulated (disk-backed,",
            " streamed, sharded checkpoints) in ", round(el_sub, digits=1),
            "s this run.")
    flush(stdout)

    # -- (No merge pass needed here: any shards from a previous run were
    # already merged into detB_concrete UPFRONT, before the new-terms loop
    # above -- see "UPFRONT MERGE PASS" earlier in this function. This
    # run's own delta-shards are consolidated periodically during the loop
    # itself -- see "PERIODIC SHARD CONSOLIDATION" in the checkpoint block
    # above -- so by this point on-disk state is already just detB_concrete
    # plus at most one small delta-shard's worth of unconsolidated recent
    # checkpoints, not a pile of leftover fragments.)

    println("  substitution done (disk-backed, streamed): degree=",
            total_degree(detB_concrete), "  terms=", length(terms(detB_concrete)),
            "  (", round(el_sub, digits=1), "s substitution this run; ",
            "totals above include ", n_already_done, " terms merged in from",
            " prior-run shards)")
    flush(stdout)

    # -- FINAL-SUM STATISTICS.
    println("  ---- PART F final-sum statistics ----")
    flush(stdout)

    stats_t0 = time()
    n_final_terms = length(terms(detB_concrete))
    n_final_terms == 0 &&
        error("PART F final-sum stats: detB_concrete has zero terms after ",
              "merge -- this should be structurally impossible for a ",
              "genus-2 Bezoutian determinant and indicates upstream data ",
              "loss (empty/corrupt shard, or the merge loop above silently ",
              "skipped every shard). Refusing to report statistics on an ",
              "empty polynomial as if it were a real result.")

    var_names = ["a1", "a2", "b1", "b2"]
    nv = nvars(Rcoef)
    length(var_names) != nv &&
        error("PART F final-sum stats: var_names has ", length(var_names),
              " entries but Rcoef has ", nv, " variables -- update ",
              "var_names before trusting the per-variable degree table below.")
    min_deg_per_var = fill(typemax(Int), nv)
    max_deg_per_var = fill(0, nv)
    max_total_degree_seen = 0
    min_total_degree_seen = typemax(Int)
    min_coeff_zz = nothing
    max_coeff_zz = nothing
    for (c, exps) in zip(coefficients(detB_concrete), AbstractAlgebra.exponent_vectors(detB_concrete))
        length(exps) != nv &&
            error("PART F final-sum stats: term with ", length(exps),
                  " exponents encountered but Rcoef has ", nv,
                  " variables -- detB_concrete is malformed (likely a ",
                  "shard merged from a differently-shaped run); refusing ",
                  "to report statistics computed against inconsistent ",
                  "exponent vectors.")
        td = sum(exps)
        td > max_total_degree_seen && (max_total_degree_seen = td)
        td < min_total_degree_seen && (min_total_degree_seen = td)
        for k in 1:nv
            e = exps[k]
            e > max_deg_per_var[k] && (max_deg_per_var[k] = e)
            e < min_deg_per_var[k] && (min_deg_per_var[k] = e)
        end
        cv = lift(ZZ, c)
        if min_coeff_zz === nothing || cv < min_coeff_zz
            min_coeff_zz = cv
        end
        if max_coeff_zz === nothing || cv > max_coeff_zz
            max_coeff_zz = cv
        end
    end
    stats_elapsed = time() - stats_t0

    println("    term count        : ", n_final_terms)
    println("    total degree      : min=", min_total_degree_seen,
            "  max=", max_total_degree_seen)
    for k in 1:nv
        println("    degree in ", var_names[k], "        : min=", min_deg_per_var[k],
                "  max=", max_deg_per_var[k])
    end
    println("    coefficient range : min=", min_coeff_zz, "  max=", max_coeff_zz,
            "  (field characteristic p=", p, ")")
    bytes_per_term_flat = sizeof(SHARD_COEFF_TYPE) + 4 * sizeof(SHARD_EXP_TYPE)
    est_mb_flat = n_final_terms * bytes_per_term_flat / 1024 / 1024
    println("    est. flat-shard size at this term count: ",
            round(est_mb_flat, digits=1), " MB (", bytes_per_term_flat,
            " bytes/term)")
    println("    stats computed in ", round(stats_elapsed, digits=1), "s")
    flush(stdout)

    open(manifest_file, "w") do io
        println(io, "PART F disk-backed substitution manifest for $name")
        println(io, "n_terms = $n_terms")
        println(io, "checkpoint shards dir = $shards_dir")
        println(io, "final degree = ", total_degree(detB_concrete))
        println(io, "final terms  = ", n_final_terms)
        println(io, "total degree range = ", min_total_degree_seen, "..", max_total_degree_seen)
        for k in 1:nv
            println(io, "degree in ", var_names[k], " range = ", min_deg_per_var[k], "..", max_deg_per_var[k])
        end
        println(io, "coefficient range (ZZ lift) = ", min_coeff_zz, "..", max_coeff_zz)
        println(io, "field characteristic p = ", p)
        println(io, "est. flat-shard size at this term count (MB) = ", round(est_mb_flat, digits=1))
    end

    # -- Correctness cross-check against the concrete Bezout matrix.
    RUN_PARTF_DIRECT_CROSSCHECK = get(ENV, "ELIM2_PARTF_DIRECT_CROSSCHECK", "false") == "true"
    local agrees, n_mismatch
    if RUN_PARTF_DIRECT_CROSSCHECK
        println("  Cross-checking against det() of the concrete (pre-flattened) B...")
        println("  (ELIM2_PARTF_DIRECT_CROSSCHECK=true -- this repeats the dense,",
                " single-shot computation the disk-backed path exists to avoid;",
                " only run this with enough RAM headroom.)")
        flush(stdout)
        t0chk = time()
        B_mat_concrete = matrix(Rcoef, [B[(i,j)] for i in 0:3, j in 0:3])
        detB_direct = det(B_mat_concrete)
        el_chk = time() - t0chk
        agrees = detB_concrete == detB_direct
        println("  det(B) computed directly in ", round(el_chk, digits=3), "s: degree=",
                total_degree(detB_direct), "  terms=", length(terms(detB_direct)))
        println("  AGREES with abstract-route result? ", agrees,
                agrees ? "" : "   <<<< MISMATCH -- reordering bug, do not trust PART F result")
        flush(stdout)
    else
        println("  Skipping full det(B) cross-check (set ",
                "ELIM2_PARTF_DIRECT_CROSSCHECK=true to enable -- expensive,",
                " dense, same computation that OOM'd before). Running a",
                " cheaper per-entry spot-check instead:")
        flush(stdout)
        n_mismatch = 0
        for (i, j) in [(0,0), (1,2), (2,3), (3,3)]
            abstract_entry_concrete = evaluate(Bpq[(i,j)], vcat(g1_coefs_poly, g2_coefs_poly))
            same = abstract_entry_concrete == B[(i,j)]
            n_mismatch += !same
            println("    entry ($i,$j): abstract-route == concrete B[$i,$j]? ", same)
        end
        println("    spot-check: ", n_mismatch == 0 ? "all entries agree" :
                "$n_mismatch MISMATCH(es) -- investigate before trusting PART F result")
        flush(stdout)
    end

    println("  PART F summary: det(Bpq) computed as a degree<=8 polynomial in",
            " 10 abstract symbols, THEN substituted once, instead of building")
    println("  and manipulating dense ", nvars(Rcoef), "-variable ", 83521,
            "-term entries at every intermediate step.")
    flush(stdout)

    # -- PERSIST THE RESULT.
    res_num = detB_concrete
    mkpath(dirname(ts.RESULTANT_FILE))
    save(ts.RESULTANT_FILE, res_num)
    println("  saved resultant -> ", ts.RESULTANT_FILE)
    flush(stdout)

    # -- SHARD CLEANUP (gated on a passing crosscheck).
    keep_shards_override = get(ENV, "ELIM2_PARTF_KEEP_SHARDS", "false") == "true"
    crosscheck_ok = true
    crosscheck_note = "no crosscheck/spot-check ran this branch"
    if RUN_PARTF_DIRECT_CROSSCHECK
        crosscheck_ok = agrees
        crosscheck_note = "full det(B) crosscheck: agrees=$agrees"
    else
        crosscheck_ok = (n_mismatch == 0)
        crosscheck_note = "spot-check: n_mismatch=$n_mismatch"
    end

    if keep_shards_override
        println("  Shard cleanup skipped: ELIM2_PARTF_KEEP_SHARDS=true.",
                " Shards remain under ", shards_dir, ".")
        flush(stdout)
    elseif !crosscheck_ok
        println("  Shard cleanup SKIPPED: correctness check did not pass",
                " clean (", crosscheck_note, ") -- keeping shards under ",
                shards_dir, " so the result can be re-derived/inspected.",
                " Investigate before re-running with cleanup enabled.")
        flush(stdout)
    else
        cleanup_shard_paths = existing_shard_paths()
        println("  Shard cleanup: ", crosscheck_note, " -- removing ",
                length(cleanup_shard_paths), " shard file(s) under ",
                shards_dir, " (result is durably saved in manifest_file",
                " and in RESULTANT_FILE, both written above)...")
        flush(stdout)
        n_removed = 0
        n_failed = 0
        bytes_freed = 0
        for sp in cleanup_shard_paths
            try
                sz = filesize(sp)
                rm(sp; force=false)
                n_removed += 1
                bytes_freed += sz
            catch e
                n_failed += 1
                println("    WARNING: failed to remove shard ", sp, ": ", e)
            end
        end
        if n_failed == 0 && isfile(progress_file)
            rm(progress_file; force=false)
        end
        println("    removed ", n_removed, "/", length(cleanup_shard_paths),
                " shard file(s), freed ", round(bytes_freed / 1024 / 1024, digits=1),
                " MB", n_failed > 0 ? "  ($n_failed FAILED -- see warnings above, shards_dir not fully clean)" : "")
        n_failed > 0 &&
            error("PART F shard cleanup: ", n_failed, " shard file(s) under ",
                  shards_dir, " could not be removed -- disk space was not",
                  " fully reclaimed. Inspect the warnings above (likely a",
                  " permissions issue or a file held open) before assuming",
                  " the scratch dir is clear for the resultant computation below.")
        flush(stdout)
    end

    println("  === $name complete: resultant numerator saved to ", ts.RESULTANT_FILE, " ===")
    flush(stdout)

    return res_num
end
################################################################################
# Top-level per-target driver and orchestrator.
################################################################################

"""
    run_part_k_target!(F, p, clean_sample_1, clean_sample_2, fu, name, i1, i2, Tvar;
                        scratch_dir)

Runs one target's (U0, U1, V0, or V1) full PART K pipeline: skip-if-done
check, fiber-product ring + coefficient extraction (`build_target_setup`),
coefficient-ring lift (`build_coef_ring`), the concrete Bezout diagnostic
(`build_concrete_bezout_diagnostic`), the PARTS A-E structural diagnostic
(`run_parts_a_to_e_diagnostic`), and finally PART F's abstract-Bezout
substitution (`run_part_f_bezout!`), matching the original's single
`for (name, i1, i2, Tvar) in target_specs ... end` loop body (lines
4858-8017) for one iteration. Returns `nothing` if this target was
already complete (skip) or if `d1T`/`d2T` weren't both 4 (diagnostics
and PART F are gated on that, matching the original -- there is no
fallback resultant path ported here, since the original's own fallback
[`resultant(g1_T, g2_T)` behind `RUN_FULL_RESULTANT`, and the manual PRS
in PART G] is the dead/removed code kept only as the trailing comment
block in this module, per the original's own note that it should be
deleted); otherwise returns the saved `res_num`.
"""
function run_part_k_target!(F, p::Int, clean_sample_1::Vector, clean_sample_2::Vector,
                             fu::FinalUniverse, name::String, i1::Int, i2::Int, Tvar;
                             scratch_dir::String = joinpath(ELIM2_ROOT_DIR, "part_k_results"))
    RESULTANT_FILE = joinpath(scratch_dir, "$(name)_resultant.oscar")
    if already_complete(RESULTANT_FILE)
        return nothing
    end

    g1 = fu.final_equations[i1]
    g2 = fu.final_equations[i2]
    d1T = degree(g1, Tvar)
    d2T = degree(g2, Tvar)
    println("  --- $name ---")
    println("    g1 (sample 1 side): total_degree=", total_degree(g1),
            "  terms=", length(terms(g1)), "  degree-in-$name=", d1T)
    println("    g2 (sample 2 side): total_degree=", total_degree(g2),
            "  terms=", length(terms(g2)), "  degree-in-$name=", d2T)

    if d1T == 0 || d2T == 0
        error("$name does not actually appear in one side; resultant " *
              "would be degenerate. Inspect final_equations construction.")
    end

    ts = build_target_setup(F, clean_sample_1, clean_sample_2, name, i1, i2, d1T, d2T;
                             scratch_dir = scratch_dir)
    cr = build_coef_ring(F, ts)
    bm = build_concrete_bezout_diagnostic(cr, ts)

    if bm === nothing
        println("  --- $name: skipping PARTS A-E and PART F (d1T/d2T != 4) ---")
        flush(stdout)
        return nothing
    end

    run_parts_a_to_e_diagnostic(F, cr, ts, bm)
    res_num = run_part_f_bezout!(F, p, cr, ts, bm; scratch_dir = scratch_dir)

    return res_num
end

"""
    run_part_k!(F, p, clean_sample_1, clean_sample_2; scratch_dir)

Original lines 4684-8017 (the whole of PART K, top to bottom). Builds
the final universe (`build_final_universe`), then runs
`run_part_k_target!` for each of the 4 targets in `target_specs` order
(U0, U1, V0, V1), matching the original's single top-level
`for (name, i1, i2, Tvar) in target_specs` loop. Returns the
`FinalUniverse` plus a `Dict{String,Any}` of each target's `res_num`
(only populated for targets that actually ran PART F this call --
skipped/already-complete targets are omitted, matching how the original
only ever had `res_num` in scope for the target currently being
processed).
"""
function run_part_k!(F, p::Int, clean_sample_1::Vector, clean_sample_2::Vector;
                      scratch_dir::String = joinpath(ELIM2_ROOT_DIR, "part_k_results"))
    fu = build_final_universe(F, clean_sample_1, clean_sample_2)

    results = Dict{String,Any}()
    for (name, i1, i2, Tvar) in target_specs(fu)
        res_num = run_part_k_target!(F, p, clean_sample_1, clean_sample_2, fu,
                                      name, i1, i2, Tvar; scratch_dir = scratch_dir)
        if res_num !== nothing
            results[name] = res_num
        end
    end

    return (fu = fu, results = results)
end

################################################################################
# PART G REMOVED (original lines 8019-8397, kept verbatim below as a
# dead-code marker per the original's own note, NOT executed by this
# module -- reproduced here rather than dropped, since it documents WHY
# the manual disk-sharded PRS cross-check and the gated resultant()
# fallback were removed, and that reasoning is worth keeping alongside
# the code it explains).
#
# PART G REMOVED.
#
# The manual disk-sharded pseudo-remainder-sequence cross-check (and the
# separate gated resultant(g1_T, g2_T) call after it) used to live here.
# Both were redundant verification of what PART F already computes and
# saves directly (res_num = detB_concrete, written to RESULTANT_FILE
# inside the loop above, once per target) -- PART G never ran by default
# (RUN_PART_G_PRS defaulted false) and the gated resultant() call below
# it unconditionally exit(0)'d after the first target, which is what was
# blocking U1/V0/V1 from ever running. Removed rather than left as dead
# code now that the loop above is the single source of truth for all
# four targets' results.
#
# #=
# PART G: manually-driven, disk-sharded pseudo-remainder sequence (PRS).
#
# Motivation: the single opaque resultant(g1_T, g2_T) call below (kept,
# gated behind RUN_FULL_RESULTANT, as the reference/fallback path) is a
# black box -- when it hangs or OOMs there is no visibility into which
# PRS step is the problem, and no way to checkpoint partway through. PART
# F already independently computed the resultant's numerator (res_num,
# via the Bezout determinant, disk-sharded and fully verified against
# the concrete B by spot-check), so this PRS pass is NOT the only way to
# get the answer -- it exists as an independent, transparent, resumable
# computation of the SAME resultant via a different classical algorithm,
# specifically so a hang/crash mid-PRS is debuggable (which step, which
# degree, how big were the coefficients) instead of opaque.
#
# [The original's full manual PRS implementation -- next_permutation!,
# first_k_permutations, first_k_nonzero_permutations,
# count_nonzero_permutations, the PART_K_MAX_WORKERS subprocess pool,
# part_k_launch/part_k_harvest/part_k_summand_complete, and the entire
# "keep computing summands until one dies" driver loop, plus the manual
# shard-based PRS step-by-step reduction -- lived here, original lines
# ~8035-8397. It is intentionally NOT reproduced verbatim in this
# module: none of it is wrong, but per the removal note above it was
# solving a problem (surviving Leibniz expansion of an 8x8 determinant
# with huge entries) that PART F's abstract-Bezout route avoids needing
# to solve at all, and reproducing ~360 lines of never-executed
# (RUN_PART_G_PRS defaulted false) subprocess-pool machinery here would
# only obscure the module's actually-active code path. See elim2.jl's
# own lines 8034-8397 for the full original text if this history is
# ever needed again.]
# =#
################################################################################

end # module PartKResultant
