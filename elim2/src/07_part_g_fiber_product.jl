println("PART G: fiber-product decomposition (eliminate each side ")
println("independently, then combine via shared U-variable)")
println("===========================================================")
println()

# Fu_decoupled was built as [u1_x^0(U0), u2_x^0(U0), u1_x^1(U1), u2_x^1(U1)]
# -- confirm that pairing explicitly rather than assuming it silently.
fiber_pairs = [
    ("U0", Fu_decoupled[1], Fu_decoupled[2], U_vars[1]),
    ("U1", Fu_decoupled[3], Fu_decoupled[4], U_vars[2]),
]

if false # this section segfaults
for (uname, ga, gb, Uvar) in fiber_pairs
    println("--- fiber pair over $uname ---")
    println("  side A vars: ", vars(ga), "   side B vars: ", vars(gb))
    shared = intersect(Set(vars(ga)), Set(vars(gb)))
    println("  shared variables: ", collect(shared),
            shared == Set([Uvar]) ? "  (confirmed: only $uname shared)" :
            "  *** WARNING: shared set is not just {$uname} -- fiber-product ***" *
            "  *** decomposition below is NOT valid for this pair, skipping ***")
    if shared != Set([Uvar])
        println()
        continue
    end

    # Build side A's SELF-CONTAINED ring: only the variables ga actually
    # uses (its own w's, its own a/b's, and Uvar), remapped into a small
    # fresh ring so Singular only ever sees this side's variables.
    a_vars_sorted = sort(vars(ga); by = string)  # deterministic order
    Ra, ra_gens = polynomial_ring(F, string.(a_vars_sorted))
    a_remap = Dict(zip(a_vars_sorted, ra_gens))
    remap_to_Ra(f) = evaluate(f, [get(a_remap, v, zero(Ra)) for v in a_vars_sorted])
    # NOTE: evaluate(f, images) requires images indexed the same way f's
    # OWN parent ring's generators are, not a_vars_sorted -- since ga
    # lives in R_dec, we must map over ALL of R_dec's generators, sending
    # the ones ga doesn't use to 0 (they don't appear in ga's monomials
    # so this is exact, not an approximation).
    full_remap_a = [v in a_vars_sorted ? a_remap[v] : zero(Ra) for v in gens(R_dec)]
    ga_small = evaluate(ga, full_remap_a)

    # curve equations relevant to side A: whichever of curve_a*_d/curve_b*_d
    # share variables with ga.
    curve_gens_d_local = [curve_a1_d, curve_a2_d, curve_b1_d, curve_b2_d]
    curves_a = [c for c in curve_gens_d_local if !isempty(intersect(Set(vars(c)), Set(a_vars_sorted)))]
    curves_a_small = [evaluate(c, full_remap_a) for c in curves_a]

    Ia_small = ideal(Ra, vcat([ga_small], curves_a_small))
    w_vars_a = [v for v in ra_gens if string(v) in ("wa1","wa2","wb1","wb2")]

    println("  side A: independent ring with ", ngens(Ra), " vars, eliminating ", w_vars_a)
    resultA, statusA, elapsedA = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Ia_small, w_vars_a)
    end
    if statusA == :ok
        gA = gens(resultA)
        println("    status=OK  elapsed=", round(elapsedA, digits=3), "s  ",
                "generators=", length(gA), "  degrees=", total_degree.(gA),
                "  terms=", length.(terms.(gA)))
    else
        println("    status=$statusA after ", round(elapsedA, digits=3), "s")
    end

    # Side B, same procedure.
    b_vars_sorted = sort(vars(gb); by = string)
    Rb, rb_gens = polynomial_ring(F, string.(b_vars_sorted))
    b_remap = Dict(zip(b_vars_sorted, rb_gens))
    full_remap_b = [v in b_vars_sorted ? b_remap[v] : zero(Rb) for v in gens(R_dec)]
    gb_small = evaluate(gb, full_remap_b)
    curves_b = [c for c in curve_gens_d_local if !isempty(intersect(Set(vars(c)), Set(b_vars_sorted)))]
    curves_b_small = [evaluate(c, full_remap_b) for c in curves_b]
    Ib_small = ideal(Rb, vcat([gb_small], curves_b_small))
    w_vars_b = [v for v in rb_gens if string(v) in ("wa1","wa2","wb1","wb2")]

    println("  side B: independent ring with ", ngens(Rb), " vars, eliminating ", w_vars_b)
    resultB, statusB, elapsedB = run_with_timeout(SUBIDEAL_TIMEOUT_SECS) do
        eliminate(Ib_small, w_vars_b)
    end
    if statusB == :ok
        gB = gens(resultB)
        println("    status=OK  elapsed=", round(elapsedB, digits=3), "s  ",
                "generators=", length(gB), "  degrees=", total_degree.(gB),
                "  terms=", length.(terms.(gB)))
    else
        println("    status=$statusB after ", round(elapsedB, digits=3), "s")
    end

    if statusA == :ok && statusB == :ok
        println("  BOTH sides eliminated independently -- combined result would be")
        println("  elim_A(Ia) + elim_B(Ib) in k[a1,a2,b1,b2,$uname], WITHOUT Singular")
        println("  ever seeing the joint 6+ generator system that hung/segfaulted")
        println("  in Part B. Total combined generator count = ",
                length(gens(resultA)) + length(gens(resultB)), ".")
        println("  (Not re-embedding into R_dec here -- these live in Ra/Rb, two")
        println("  DIFFERENT small rings, both sharing the variable name \"$uname\"")
        println("  but as distinct ring objects; embedding both into one common")
        println("  k[a1,a2,b1,b2,$uname] ring for actual downstream use is a")
        println("  mechanical remap, omitted here since the point of this pass is")
        println("  the elimination-cost comparison, not the final variety.)")
    end
    println()
end

end # end segfault section

################################################################################
# PART H: FULLY INDEPENDENT small-ring reconstruction (not a restriction
# of Part G).
#
# Part G took Fu_decoupled[1]/[2] (already elements of the 12-variable
# R_dec) and remapped/evaluated them into smaller rings -- a restriction,
# not an independent build. This part is stricter, per direct request:
# it builds u1_num[1]/u1_den[1] (sample 1's ORIGINAL numerator/
# denominator pair, still living in the ORIGINAL 8-variable ring R from
# much earlier in this file, never touched by the R_dec construction at
# all) into a brand-new 5-variable ring from scratch, with NO reference
# to R_dec, Iu_decoupled, or Fu_decoupled anywhere in this construction.
# If this succeeds quickly where Part C's single-variable elimination on
# the full Iu_decoupled did not, that's strong evidence the pathology is
# an artifact of the 12-variable ambient ring (or of something Oscar/
# Singular does when constructing/preparing an ideal in that ring -- see
# the dim() segfault discussion below) rather than being intrinsic to
# the elimination mathematics itself.
#
# NEW EVIDENCE motivating this part: in the actual run, eliminating just
# wa1_d ALONE from the full Iu_decoupled timed out (Part C), and then
# dim() on the CURVE-ONLY ideal (4 generators, degree 5 each -- about as
# simple as an ideal in this ring gets) segfaulted. A single-variable
# elimination hanging, and dim() crashing on a tiny ideal, are both hard
# to explain by "the elimination math is genuinely hard" -- eliminating
# ONE variable from a system where every generator is individually cheap
# should not be expensive if the joint structure is actually as
# decomposable as Part G's math argument says it is. This points at
# something about how Oscar/Singular is handling the 12-variable R_dec
# ring itself (ring/ideal object construction, internal GB caching
# triggered by dim()'s call path -- see PART D's comment on
# singular_groebner_generators -- or possibly a resource/threading issue
# specific to this Oscar/Singular build) rather than at the elimination
# problem. This part tests that directly by never constructing anything
# in R_dec at all.
################################################################################

println()
println("===========================================================")
