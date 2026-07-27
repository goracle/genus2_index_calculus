global all_b_sym = true

if d1T == 4 && d2T == 4
    println()
    println("=" ^ 70)
    println("PARTS A-E: deep diagnostic (no resultant computed) -- $name")
    println("=" ^ 70)
    flush(stdout)

    # ------------------------------------------------------------------
    # shared helper: try factor(), fall back gracefully if it errors or
    # times out conceptually (Oscar's factor() has no built-in timeout,
    # so we just wrap in try/catch -- if factor() itself hangs, that is
    # itself diagnostic information worth seeing separately, but we do
    # not want a factor() hang to mask the rest of this report).
    # ------------------------------------------------------------------
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

    # p_coef, q_coef, bracket_num already defined above (Bezout block);
    # reuse p_coef[k+1]=p_k, q_coef[k+1]=q_k directly -- these are Kcoef
    # elements, take numerator (denominator already unit-checked at
    # construction time via bracket_num's pattern; check again here per
    # coefficient since these are used standalone, not just in brackets).
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

    # structural tests
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
        # palindromic test: c0 vs c4, c1 vs c3 (up to a possible overall
        # scalar/unit factor -- report the ratio's structure rather than
        # assuming it must be exactly 1)
        if !iszero(c0) && !iszero(c4)
            println("      $gname palindromic check: deg(c0)=", total_degree(c0),
                    " vs deg(c4)=", total_degree(c4),
                    "   deg(c1)=", total_degree(c1),
                    " vs deg(c3)=", total_degree(c3))
        end
        # common factor among "odd slot" coefficients c3, c1 (both should
        # be zero or share a factor if there's hidden even/odd splitting)
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

    # Build the swap automorphisms of Rcoef directly from its own
    # generators (a1_c,a2_c,b1_c,b2_c already in scope from Step 1
    # above) -- swap a1<->a2 only, and swap b1<->b2 only.
    swap_a = hom(Rcoef, Rcoef, [a2_c, a1_c, b1_c, b2_c])
    swap_b = hom(Rcoef, Rcoef, [a1_c, a2_c, b2_c, b1_c])

    function is_symmetric_under(f, phi)
        return iszero(f - phi(f))
    end

    all_coefs = vcat(
        [("g1", k, g1_coefs_poly[k+1]) for k in 0:4],
        [("g2", k, g2_coefs_poly[k+1]) for k in 0:4]
    )

    global all_a_sym = true
    global all_b_sym = true
    for (gname, k, f) in all_coefs
        if iszero(f)
            continue
        end
        global all_a_sym
        global all_b_sym
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

        # Symmetric-basis ring
        Rsym, (sa, pa, sb, pb) = polynomial_ring(F, ["sa", "pa", "sb", "pb"])

        # Rewrite f(a1,a2,b1,b2), known symmetric in (a1,a2) and (b1,b2)
        # separately, in terms of (sa,pa,sb,pb) via Newton's identities /
        # direct substitution: express as a polynomial in a1 with
        # coefficients depending on a2 is not what we want -- instead
        # use the standard trick of representing symmetric functions of
        # (a1,a2) via a1=  (sa + d)/2, a2 = (sa-d)/2 is unnecessary; the
        # clean way in a CAS is: build the map by matching monomials.
        # Given full symmetry is already confirmed, every monomial
        # a1^i*a2^j*b1^k*b2^l appears paired with a1^j*a2^i*b1^l*b2^k
        # with equal coefficient (for i!=j or k!=l); we rewrite via
        # repeated elimination: a1^2 -> sa*a1 - pa (since a1,a2 are
        # roots of X^2 - sa*X + pa), reducing every monomial's a-degree
        # in a1,a2 down to at most degree 1 in each of a1,a2 individually
        # then expressing the surviving symmetric combination in sa,pa.
        # For a DIAGNOSTIC term-count measurement (not a full rewrite),
        # we instead use Oscar's msolve/symmetric-function machinery if
        # available, and fall back to a direct evaluate-and-interpolate
        # sanity count if not. Wrapped in try/catch since this is
        # explicitly a "measure savings, don't fully commit" step.
        function try_symmetric_rewrite(f)
            # Fallback strategy: since f is symmetric in (a1,a2) and
            # (b1,b2) separately, and total_degree/term-count are the
            # quantities we actually want, estimate the reduced term
            # count via the standard bound: a symmetric polynomial in
            # (a1,a2) of degree d has a symmetric-basis representation
            # with at most ~ (number of monomials sa^i pa^j with
            # 2j+i <= d_a) terms per "half" -- rather than guess, do the
            # actual rewrite using elimination substitution a1^2 ->
            # sa*a1 - pa repeatedly via divrem in a fresh ring where sa,
            # pa are already available as extra generators, then confirm
            # the a1-degree has dropped to <=1 and a2 no longer appears
            # (by construction) before reading off a monomial count in
            # (sa,pa,b-analog).
            try
                # Extended ring carrying both original and symmetric
                # generators simultaneously so we can do the elimination
                # substitution as ordinary polynomial arithmetic.
                Rext, (a1e,a2e,b1e,b2e,sae,pae,sbe,pbe) = polynomial_ring(
                    F, ["a1","a2","b1","b2","sa","pa","sb","pb"])
                incl = hom(Rcoef, Rext, [a1e,a2e,b1e,b2e])
                fe = incl(f)
                # Reduce a2-degree to 0 using a2 = sa - a1 (exact,
                # since a1+a2=sa), then reduce resulting a1-degree using
                # a1^2 = sae*a1e - pae (from a1,a2 roots of X^2-sa X+pa).
                # Substitute a2e -> (sae - a1e) directly via evaluate.
                fe2 = evaluate(fe, [a1e, sae - a1e, b1e, b2e, sae, pae, sbe, pbe])
                # Now repeatedly knock down a1e powers >=2 using
                # a1e^2 == sae*a1e - pae, via divrem against that
                # relation treated as a univariate reduction in a1e.
                Runiv, a1u = polynomial_ring(fraction_field(Rext), "a1u")
                # This nested-ring gymnastics is more machinery than a
                # pure diagnostic needs; instead do plain polynomial
                # division of fe2 (as element of Rext) by the relation
                # a1e^2 - sae*a1e + pae, using Oscar's built-in divrem
                # in the multivariate ring directly (works because the
                # relation is monic in a1e).
                relation_a = a1e^2 - sae*a1e + pae
                q, r = divrem(fe2, relation_a)
                fe3 = r   # r should now have a1e-degree <= 1
                # Same treatment for b1e/b2e -> sb,pb
                fe4 = evaluate(fe3, [a1e, a2e, b1e, sbe - b1e, sae, pae, sbe, pbe])
                relation_b = b1e^2 - sbe*b1e + pbe
                q2, r2 = divrem(fe4, relation_b)
                fe5 = r2
                # fe5 should now be expressible with a1e,b1e-degree <=1;
                # since f was confirmed FULLY symmetric (not just
                # individually in each pair), the surviving a1e,b1e
                # degree-1 terms must actually cancel to degree 0 -- if
                # they don't, symmetry detection or the reduction has a
                # bug, and we report that rather than silently trusting it.
                deg_a1_remaining = degree(fe5, a1e)
                deg_b1_remaining = degree(fe5, b1e)
                if deg_a1_remaining > 0 || deg_b1_remaining > 0
                    return (nothing, "residual a1/b1-degree after reduction " *
                            "(a1:$deg_a1_remaining, b1:$deg_b1_remaining) -- " *
                            "symmetric rewrite incomplete, reporting raw reduced form")
                end
                # Project down to Rsym by dropping a1e,a2e,b1e,b2e
                # (they should not appear at all at this point).
                Bctx = MPolyBuildCtx(Rsym)
                for (c, exps) in zip(coefficients(fe5), AbstractAlgebra.exponent_vectors(fe5))
                    # exps = [e_a1,e_a2,e_b1,e_b2,e_sa,e_pa,e_sb,e_pb]
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

    # ------------------------------------------------------------------
    # PART C.5: PARTIAL symmetrization diagnostic.
    #
    # Motivation: PART C above only acts when a coefficient is symmetric
    # under BOTH a1<->a2 AND b1<->b2 simultaneously. In practice g1 is
    # typically symmetric only in (b1,b2) and g2 only in (a1,a2) (see
    # the per-coefficient printout above) -- PART C correctly refuses to
    # touch these ("NOT fully symmetric... skipping"), but that leaves a
    # real, one-sided reduction on the table: a coefficient symmetric in
    # (b1,b2) alone can still be rewritten in (a1,a2,sb,pb), dropping b1,b2
    # individually without touching a1,a2. This block does exactly that
    # rewrite, per coefficient, for whichever single pair is symmetric,
    # and separately stress-tests the "combine g1 and g2 afterwards"
    # step, since g1 and g2 end up partially symmetrized in DIFFERENT
    # variable pairs and are not obviously combinable without further
    # work (see PART C.5 SECTION 3 below).
    #
    # IMPLEMENTATION NOTE (important, learned the hard way): the first
    # version of this diagnostic used `divrem(f, b1^2 - sb*b1 + pb)` in
    # the ambient multivariate ring to perform the b1-degree reduction.
    # That is WRONG in general: multivariate divrem reduces against the
    # divisor's leading term under the ring's *global* monomial order
    # (degrevlex here), not against "the b1^2 term specifically" -- and
    # since sb*b1 and b1^2 are the same total degree, degrevlex's
    # tie-break (on variable position) can pick sb*b1 as the leading
    # term instead of b1^2, so the "reduction" silently does nothing.
    # That bug produced a suspicious flat 0.0% reduction on every
    # coefficient, which is what exposed it.
    #
    # Fixed approach: extract f's coefficients EXPLICITLY as a
    # polynomial in the single variable being eliminated (via coeff(f,
    # [var], [d]) for each degree d present -- ordering-independent,
    # already used elsewhere in this file, e.g. leading_coeff_in), then
    # perform the b1^2 -> sb*b1 - pb (or a1^2 -> sa*a1 - pa) reduction
    # by explicit degree-by-degree substitution, which has no
    # dependence on any monomial order at all.
    # ------------------------------------------------------------------
    println()
    println("--- PART C.5: partial symmetrization diagnostic ---")
    flush(stdout)

    # Target rings for the two partial-rewrite directions.
    Rb_only, (a1b, a2b, sbb, pbb) = polynomial_ring(F, ["a1", "a2", "sb", "pb"])
    Ra_only, (saa, paa, b1a, b2a) = polynomial_ring(F, ["sa", "pa", "b1", "b2"])

    # Scratch ring: original vars plus both symmetric-pair substitutes,
    # used only as a common home for intermediate coefficient-polynomial
    # arithmetic (additions/multiplications of coefficient-of-b1^k
    # pieces, which themselves still depend on a1,a2 and, after
    # reduction, on sb,pb). No divrem against a 2-term relation is done
    # in this ring -- see note above.
    Rext_c5, (a1c5, a2c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5) = polynomial_ring(
        F, ["a1", "a2", "b1", "b2", "sa", "pa", "sb", "pb"])
    incl_c5 = hom(Rcoef, Rext_c5, [a1c5, a2c5, b1c5, b2c5])

    # Ordering-independent reduction of a univariate-in-`var` polynomial
    # (given as a Dict degree => coefficient-polynomial, coefficients
    # living in Rext_c5) modulo relation var^2 = lin*var + const, i.e.
    # standard "reduce a degree-d polynomial in a quadratic-algebraic
    # element down to degree <=1" via repeated top-down substitution:
    # var^k = lin*var^(k-1) + const*var^(k-2) for k>=2, applied
    # degree-by-degree starting from the top so every step only ever
    # touches two adjacent coefficient slots.
    function reduce_quadratic!(coeffs_by_deg::Dict{Int,Any}, lin, const_term)
        maxd = maximum(keys(coeffs_by_deg))
        for d in maxd:-1:2
            c = get(coeffs_by_deg, d, nothing)
            if c === nothing || iszero(c)
                delete!(coeffs_by_deg, d)
                continue
            end
            delete!(coeffs_by_deg, d)
            # var^d = var^(d-2) * (lin*var + const)
            #       = lin*var^(d-1) + const*var^(d-2)
            coeffs_by_deg[d-1] = get(coeffs_by_deg, d-1, zero(c)) + lin*c
            coeffs_by_deg[d-2] = get(coeffs_by_deg, d-2, zero(c)) + const_term*c
        end
        return coeffs_by_deg   # now only keys 0 and/or 1 remain
    end

    # Rewrite f, KNOWN symmetric in (b1,b2) only, into (a1,a2,sb,pb):
    # substitute b2 -> sb - b1 (exact, since b1+b2=sb), extract the
    # resulting polynomial's coefficients in b1 explicitly via coeff(),
    # reduce those degree-by-degree via reduce_quadratic! using
    # b1^2 = sb*b1 - pb, and verify the degree-1-in-b1 slot vanishes
    # (as it must, since f depends on b1,b2 ONLY through symmetric
    # combinations -- this is the standard elementary-symmetric-
    # polynomial fact, and is checked rather than assumed).
    function symmetrize_b_only(f; debug::Bool=false)
        debug && println("      [DBG b_only] input f: terms=", length(terms(f)),
                          "  degree=", total_degree(f))
        # --- NEW DIAGNOSTIC: check raw f's dependence on b1_c/b2_c BEFORE
        # any ring games, using both element-form and index-form degree(),
        # so any divergence between the two call conventions is exposed
        # directly instead of silently producing a wrong (possibly always
        # 0) answer downstream.
        if debug
            println("      [DBG b_only] === RAW f DIAGNOSTIC (in Rcoef) ===")
            println("      [DBG b_only] degree(f, b1_c)              = ", degree(f, b1_c))
            println("      [DBG b_only] degree(f, b2_c)              = ", degree(f, b2_c))
            println("      [DBG b_only] var_index(b1_c)              = ", var_index(b1_c))
            println("      [DBG b_only] var_index(b2_c)              = ", var_index(b2_c))
            println("      [DBG b_only] degree(f, var_index(b1_c))   = ", degree(f, var_index(b1_c)))
            println("      [DBG b_only] vars(f) (generators actually appearing) = ", vars(f))
        end
        fe = incl_c5(f)
        debug && println("      [DBG b_only] after incl_c5: terms=", length(terms(fe)))
        if debug
            println("      [DBG b_only] === fe DIAGNOSTIC (in Rext_c5, pre-substitution) ===")
            println("      [DBG b_only] degree(fe, b1c5)             = ", degree(fe, b1c5))
            println("      [DBG b_only] degree(fe, b2c5)             = ", degree(fe, b2c5))
            println("      [DBG b_only] var_index(b1c5)              = ", var_index(b1c5))
            println("      [DBG b_only] var_index(b2c5)              = ", var_index(b2c5))
            println("      [DBG b_only] vars(fe) (generators appearing) = ", vars(fe))
        end
        fe2 = evaluate(fe, [a1c5, a2c5, b1c5, sbc5 - b1c5, sac5, pac5, sbc5, pbc5])
        debug && println("      [DBG b_only] after b2->sb-b1 substitution: terms=",
                          length(terms(fe2)), "  degree=", total_degree(fe2))
        d = degree(fe2, b1c5)
        debug && println("      [DBG b_only] degree(fe2, b1c5) [element-form] = ", d)
        if debug
            d_idx = degree(fe2, var_index(b1c5))
            println("      [DBG b_only] degree(fe2, var_index(b1c5)) [index-form] = ", d_idx,
                    d_idx != d ? "   <<<< MISMATCH between element-form and index-form degree()!" : "   (match)")
            println("      [DBG b_only] vars(fe2) (generators appearing after substitution) = ", vars(fe2))
            println("      [DBG b_only] degree(fe2, sbc5) [should be >0 if sb actually entered] = ", degree(fe2, sbc5))
            # Direct algebraic sanity check: fe2 should NOT equal fe if the
            # substitution actually did anything (unless f happens to be
            # independent of b2c5, which contradicts Section-1 classification).
            println("      [DBG b_only] fe2 == fe (substitution was a no-op)? ", fe2 == fe)
        end
        coeffs_by_deg = Dict{Int,Any}()
        # --- NEW: cross-check element-form coeff(f, [var_element], [exp])
        # against the documented index-form coeff(f, vars::Vector{Int},
        # exps::Vector{Int}) API for every degree 0:d, so a call-convention
        # bug is caught mechanically rather than assumed away.
        if debug
            b1_idx = var_index(b1c5)
            for k in 0:d
                ck_elem = coeff(fe2, [b1c5], [k])
                ck_idx  = coeff(fe2, [b1_idx], [k])
                same = ck_elem == ck_idx
                println("      [DBG b_only] k=$k: coeff(fe2,[b1c5],[k]) terms=",
                        length(terms(ck_elem)), "   coeff(fe2,[b1_idx=$b1_idx],[k]) terms=",
                        length(terms(ck_idx)),
                        same ? "   (match)" : "   <<<< MISMATCH between element-form and index-form coeff()!")
            end
        end
        for k in 0:d
            ck = coeff(fe2, [var_index(b1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
                debug && println("      [DBG b_only] coeff of b1^", k, ": terms=",
                                  length(terms(ck)))
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        debug && println("      [DBG b_only] sum of per-degree term counts BEFORE reduce = ",
                          sum(length(terms(v)) for v in values(coeffs_by_deg)),
                          "  (compare to fe2's ", length(terms(fe2)), " -- should roughly match",
                          " if coeff() extraction is complete and non-overlapping)")
        reduce_quadratic!(coeffs_by_deg, sbc5, -pbc5)
        debug && println("      [DBG b_only] AFTER reduce_quadratic!: remaining keys=",
                          sort(collect(keys(coeffs_by_deg))),
                          "  term counts=", Dict(k=>length(terms(v)) for (k,v) in coeffs_by_deg))
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            debug && println("      [DBG b_only] FAILED: nonzero b1^1 residual, terms=",
                              length(terms(coeffs_by_deg[1])))
            return (nothing, "residual b1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (b1,b2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        debug && println("      [DBG b_only] r (post-reduction, pre-projection): terms=",
                          length(terms(r)), "  degree=", total_degree(r))
        Bctx = MPolyBuildCtx(Rb_only)
        n_pushed = 0
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            # exps = [e_a1,e_a2,e_b1,e_b2,e_sa,e_pa,e_sb,e_pb]
            if exps[3] != 0 || exps[4] != 0
                debug && println("      [DBG b_only] FAILED at projection: leftover b1/b2 exps=", exps)
                return (nothing, "unexpected leftover b1/b2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate b1,b2")
            end
            if exps[5] != 0 || exps[6] != 0
                debug && println("      [DBG b_only] FAILED at projection: leftover sa/pa exps=", exps)
                return (nothing, "unexpected sa/pa dependence in a b-only rewrite " *
                        "(exps=$exps) -- sa,pa should never appear here")
            end
            push_term!(Bctx, c, [exps[1], exps[2], exps[7], exps[8]])
            n_pushed += 1
        end
        fsym = finish(Bctx)
        debug && println("      [DBG b_only] pushed ", n_pushed, " terms into Bctx; ",
                          "finish(Bctx) reports terms=", length(terms(fsym)),
                          "  degree=", total_degree(fsym))
        return (fsym, nothing)   # lives in Rb_only: (a1,a2,sb,pb)
    end

    # Mirror image: f known symmetric in (a1,a2) only, rewritten into
    # (sa,pa,b1,b2), leaving b1,b2 untouched.
    function symmetrize_a_only(f; debug::Bool=false)
        debug && println("      [DBG a_only] input f: terms=", length(terms(f)),
                          "  degree=", total_degree(f))
        if debug
            println("      [DBG a_only] === RAW f DIAGNOSTIC (in Rcoef) ===")
            println("      [DBG a_only] degree(f, a1_c)              = ", degree(f, a1_c))
            println("      [DBG a_only] degree(f, a2_c)              = ", degree(f, a2_c))
            println("      [DBG a_only] var_index(a1_c)              = ", var_index(a1_c))
            println("      [DBG a_only] vars(f) (generators actually appearing) = ", vars(f))
        end
        fe = incl_c5(f)
        if debug
            println("      [DBG a_only] === fe DIAGNOSTIC (in Rext_c5, pre-substitution) ===")
            println("      [DBG a_only] degree(fe, a1c5)             = ", degree(fe, a1c5))
            println("      [DBG a_only] degree(fe, a2c5)             = ", degree(fe, a2c5))
            println("      [DBG a_only] vars(fe) (generators appearing) = ", vars(fe))
        end
        fe2 = evaluate(fe, [a1c5, sac5 - a1c5, b1c5, b2c5, sac5, pac5, sbc5, pbc5])
        debug && println("      [DBG a_only] after a2->sa-a1 substitution: terms=",
                          length(terms(fe2)), "  degree=", total_degree(fe2))
        d = degree(fe2, a1c5)
        debug && println("      [DBG a_only] degree(fe2, a1c5) [element-form] = ", d)
        if debug
            d_idx = degree(fe2, var_index(a1c5))
            println("      [DBG a_only] degree(fe2, var_index(a1c5)) [index-form] = ", d_idx,
                    d_idx != d ? "   <<<< MISMATCH between element-form and index-form degree()!" : "   (match)")
            println("      [DBG a_only] vars(fe2) (generators appearing after substitution) = ", vars(fe2))
            println("      [DBG a_only] degree(fe2, sac5) [should be >0 if sa actually entered] = ", degree(fe2, sac5))
            println("      [DBG a_only] fe2 == fe (substitution was a no-op)? ", fe2 == fe)
        end
        coeffs_by_deg = Dict{Int,Any}()
        if debug
            a1_idx = var_index(a1c5)
            for k in 0:d
                ck_elem = coeff(fe2, [a1c5], [k])
                ck_idx  = coeff(fe2, [a1_idx], [k])
                same = ck_elem == ck_idx
                println("      [DBG a_only] k=$k: coeff(fe2,[a1c5],[k]) terms=",
                        length(terms(ck_elem)), "   coeff(fe2,[a1_idx=$a1_idx],[k]) terms=",
                        length(terms(ck_idx)),
                        same ? "   (match)" : "   <<<< MISMATCH between element-form and index-form coeff()!")
            end
        end
        for k in 0:d
            ck = coeff(fe2, [var_index(a1c5)], [k])
            if !iszero(ck)
                coeffs_by_deg[k] = ck
                debug && println("      [DBG a_only] coeff of a1^", k, ": terms=",
                                  length(terms(ck)))
            end
        end
        if isempty(coeffs_by_deg)
            coeffs_by_deg[0] = zero(fe2)
        end
        debug && println("      [DBG a_only] sum of per-degree term counts BEFORE reduce = ",
                          sum(length(terms(v)) for v in values(coeffs_by_deg)))
        reduce_quadratic!(coeffs_by_deg, sac5, -pac5)
        debug && println("      [DBG a_only] AFTER reduce_quadratic!: remaining keys=",
                          sort(collect(keys(coeffs_by_deg))),
                          "  term counts=", Dict(k=>length(terms(v)) for (k,v) in coeffs_by_deg))
        if haskey(coeffs_by_deg, 1) && !iszero(coeffs_by_deg[1])
            debug && println("      [DBG a_only] FAILED: nonzero a1^1 residual, terms=",
                              length(terms(coeffs_by_deg[1])))
            return (nothing, "residual a1-degree=1 term did not vanish after " *
                    "reduction -- f was not actually (a1,a2)-symmetric, or " *
                    "reduction bug")
        end
        r = get(coeffs_by_deg, 0, zero(fe2))
        debug && println("      [DBG a_only] r (post-reduction, pre-projection): terms=",
                          length(terms(r)), "  degree=", total_degree(r))
        Bctx = MPolyBuildCtx(Ra_only)
        n_pushed = 0
        for (c, exps) in zip(coefficients(r), AbstractAlgebra.exponent_vectors(r))
            # exps = [e_a1,e_a2,e_b1,e_b2,e_sa,e_pa,e_sb,e_pb]
            if exps[1] != 0 || exps[2] != 0
                debug && println("      [DBG a_only] FAILED at projection: leftover a1/a2 exps=", exps)
                return (nothing, "unexpected leftover a1/a2 exponent after reduction " *
                        "(exps=$exps) -- reduction did not fully eliminate a1,a2")
            end
            if exps[7] != 0 || exps[8] != 0
                debug && println("      [DBG a_only] FAILED at projection: leftover sb/pb exps=", exps)
                return (nothing, "unexpected sb/pb dependence in an a-only rewrite " *
                        "(exps=$exps) -- sb,pb should never appear here")
            end
            push_term!(Bctx, c, [exps[5], exps[6], exps[3], exps[4]])
            n_pushed += 1
        end
        fsym = finish(Bctx)
        debug && println("      [DBG a_only] pushed ", n_pushed, " terms into Bctx; ",
                          "finish(Bctx) reports terms=", length(terms(fsym)),
                          "  degree=", total_degree(fsym))
        return (fsym, nothing)   # lives in Ra_only: (sa,pa,b1,b2)
    end

    println()
    println("  Section 1: per-coefficient single-pair symmetry classification")
    println("  (independent of PART C's all-coefficients-at-once verdict above)")
    flush(stdout)

    # classification[gname][k] in {:both, :a_only, :b_only, :neither, :zero,
    #                               :indep_of_both, :indep_of_a, :indep_of_b}
    #
    # IMPORTANT: is_symmetric_under(f, swap_a) is VACUOUSLY true whenever f
    # does not depend on a1,a2 at all (swapping variables that don't appear
    # is a no-op) -- and likewise for swap_b. Section 2's "symmetrize"
    # rewrite then has nothing real to reduce, which is exactly why it was
    # reporting a flat 0.0% reduction on every coefficient: g1's
    # coefficients are genuinely independent of b1,b2 (not merely
    # b-symmetric), and g2's are genuinely independent of a1,a2. So
    # dependence is checked explicitly via degree() BEFORE trusting the
    # swap-symmetry test, and the vacuous cases are given their own labels
    # so Section 2 can skip them (there is nothing to symmetrize) instead
    # of "succeeding" at a no-op.
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
            cls = :indep_of_both   # constant in all four -- shouldn't happen given degree=32, but handle it
        elseif !depends_on_b
            cls = :indep_of_b      # vacuously b-symmetric; genuinely a1,a2-only, not reducible via b-swap
        elseif !depends_on_a
            cls = :indep_of_a      # vacuously a-symmetric; genuinely b1,b2-only, not reducible via a-swap
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
    println("  (only attempted where Section 1 found GENUINE a1-only or b1-only")
    println("  symmetry -- i.e. the coefficient actually depends on both members")
    println("  of that pair, and is truly symmetric under swapping them. 'both'")
    println("  coefficients are handled by PART C above and skipped here to avoid")
    println("  double-reporting. 'neither' cannot be partially symmetrized at all.")
    println("  'indep_of_a'/'indep_of_b' are the VACUOUS case caught by the")
    println("  Section-1 fix: the coefficient simply does not depend on that pair")
    println("  at all, so is_symmetric_under() was trivially true and there is")
    println("  nothing to symmetrize -- reported honestly instead of run through")
    println("  the rewrite as a no-op, which is what previously produced the flat")
    println("  0.0% reduction on every coefficient.)")
    flush(stdout)

    c5_rewritten = Dict{Tuple{String,Int},Any}()   # stores (poly, which_pair)
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
                    "not depend on b1,b2 at all (only a1,a2); swap-symmetry was trivially ",
                    "true and there is nothing to symmetrize. Already minimal in b.")
            continue
        elseif cls == :indep_of_a
            println("    $gname coeff of T^$k: VACUOUS a-symmetry -- coefficient does ",
                    "not depend on a1,a2 at all (only b1,b2); swap-symmetry was trivially ",
                    "true and there is nothing to symmetrize. Already minimal in a.")
            continue
        end
        # From here on, cls is genuinely :a_only or :b_only -- the
        # coefficient really depends on both members of that pair AND is
        # really symmetric under swapping them, so the rewrite has actual
        # work to do.

        before_terms = length(terms(f))
        before_deg = total_degree(f)

        # Full stage-by-stage trace on just the FIRST coefficient we hit
        # for each rewrite direction (b_only / a_only) -- enough to
        # diagnose where the pipeline diverges without flooding output
        # for all ten coefficients.
        global _c5_debug_done_b = @isdefined(_c5_debug_done_b) ? _c5_debug_done_b : false
        global _c5_debug_done_a = @isdefined(_c5_debug_done_a) ? _c5_debug_done_a : false

        if cls == :b_only
            do_dbg = !_c5_debug_done_b
            if do_dbg
                println("    [entering full debug trace for $gname coeff of T^$k, class=b_only]")
                global _c5_debug_done_b = true
            end
            fsym, err = symmetrize_b_only(f; debug=do_dbg)
            pairname = "b"
        else # :a_only
            do_dbg = !_c5_debug_done_a
            if do_dbg
                println("    [entering full debug trace for $gname coeff of T^$k, class=a_only]")
                global _c5_debug_done_a = true
            end
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
    println("  (the actual hazard flagged for Task 2: g1 is typically rewritten")
    println("  in (a1,a2,sb,pb) and g2 in (sa,pa,b1,b2) -- these are DIFFERENT")
    println("  rings and cannot be combined [resultant/GCD/matching] directly.")
    println("  This section checks, computationally, whether that combination")
    println("  requires reintroducing the eliminated pair, i.e. whether the")
    println("  partial rewrite is a dead end for the downstream matching step")
    println("  as currently structured.)")
    flush(stdout)

    g1_b_only_present = any(c5_class[("g1",k)] == :b_only for k in 0:4 if haskey(c5_class,("g1",k)))
    g2_a_only_present = any(c5_class[("g2",k)] == :a_only for k in 0:4 if haskey(c5_class,("g2",k)))

    if g1_b_only_present && g2_a_only_present
        println("    g1 has (b1,b2)-symmetric coefficient(s); g2 has (a1,a2)-symmetric ",
                "coefficient(s) -- this is the expected asymmetric case from the log.")
        println("    g1's natural target ring after rewrite: (a1,a2,sb,pb)")
        println("    g2's natural target ring after rewrite: (sa,pa,b1,b2)")
        println("    Common ring containing BOTH without reintroducing any variable ",
                "individually: NONE -- (a1,a2,sb,pb) has a1,a2 unreduced while ",
                "(sa,pa,b1,b2) has b1,b2 unreduced, and neither is a subring of the other.")
        println("    Only combination routes available, in order of cost:")
        println("      (i)   map BOTH into the raw ring (a1,a2,b1,b2) -- discards all")
        println("            symmetrization savings before the combination step, i.e.")
        println("            the win from Section 2 does not survive into PART K's")
        println("            final collision step as currently structured.")
        println("      (ii)  desymmetrize the OTHER pair back out of each side via the")
        println("            quadratic formula (b1,b2 = (sb +/- sqrt(sb^2-4pb))/2, and")
        println("            symmetrically for a1,a2) before combining -- reintroduces")
        println("            a degree-2 field extension per desymmetrized pair, so this")
        println("            is not free either, and needs explicit sign-branch handling.")
        println("      (iii) fully symmetrize BOTH g1 and g2 in BOTH pairs -- only valid")
        println("            if g1 is ALSO (a1,a2)-symmetric and g2 ALSO (b1,b2)-symmetric,")
        println("            which PART C above already tests; per the log this is FALSE,")
        println("            so route (iii) is not available for this construction.")
        println("    VERDICT: partial symmetrization, as currently scoped, reduces the")
        println("    SIZE of g1 and g2 individually (Section 2 numbers above are real)")
        println("    but does NOT by itself simplify the PART K combination step -- that")
        println("    step still needs route (i) or (ii). This should be treated as an")
        println("    open sub-problem, not assumed solved by Section 2's reduction.")
    else
        g1_indep_b = any(get(c5_class, ("g1",k), nothing) == :indep_of_b for k in 0:4)
        g2_indep_a = any(get(c5_class, ("g2",k), nothing) == :indep_of_a for k in 0:4)
        if g1_indep_b && g2_indep_a
            println("    Did NOT find genuine b-only/a-only partial symmetry -- instead,")
            println("    Section 1 found g1's coefficients are entirely INDEPENDENT of")
            println("    b1,b2 (they only ever involved a1,a2 to begin with), and g2's")
            println("    coefficients are entirely INDEPENDENT of a1,a2 (only b1,b2).")
            println("    This is a stronger, better situation than partial symmetrization:")
            println("    g1 already lives in the smaller ring (a1,a2) and g2 already lives")
            println("    in (b1,b2) -- no rewrite, no quadratic-relation reduction, and no")
            println("    sqrt-desymmetrization is needed to get there, because they were")
            println("    never coupled to the other pair in the first place. The routes")
            println("    (i)/(ii)/(iii) discussion above does not apply to this case: the")
            println("    combination step should instead be analyzed directly as a")
            println("    resultant/Bezout construction between a genuinely-(a1,a2)-only")
            println("    polynomial and a genuinely-(b1,b2)-only polynomial, which may be")
            println("    a materially easier structure than the general 4-variable case")
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
    println("  (compares the combined term count of g1[T^0]+g2[T^0] in raw form")
    println("  against their partially symmetrized intermediate form, so the")
    println("  effect of Section 2's reduction can be read off directly before")
    println("  any remapping-back-to-raw-ring cost from Section 3 is paid.)")
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
        println("    per Section 3, recombining these into one Bezout-style entry")
        println("    still requires mapping back to the raw ring (route (i)) or a")
        println("    sqrt-desymmetrization (route (ii)), so this number bounds the")
        println("    best case, not the as-implemented case, until Section 3's open")
        println("    sub-problem is resolved.")
    else
        println("    g1[T^0]/g2[T^0] not both eligible for partial symmetrization in ",
                "this run -- skipping Section 4 size probe (see Section 1 above).")
    end
    flush(stdout)

    println()
    println("PART C.5 COMPLETE")
    println("Answering (per Task 2 questions):")
    println("  - meaningful term-count reduction from partial symmetrization?")
    println("    -> see Section 2 summary (aggregate) and per-coefficient lines.")
    println("  - hidden pitfalls combining partially-symmetrized rings?")
    println("    -> see Section 3 (this is a real, currently-open blocker, not")
    println("       merely a theoretical concern -- routes (i)/(ii)/(iii) are the")
    println("       only options and none is free).")
    println("  - does it help the actual Bezout/PRS combination step, not just")
    println("    the standalone coefficient size?")
    println("    -> see Section 4 (currently: reduces intermediate size only;")
    println("       benefit at the combination step is NOT yet demonstrated).")
    flush(stdout)

    # ------------------------------------------------------------------
    # PART D: Bezout entry sparsity / factoring analysis
    # ------------------------------------------------------------------
    println()
    println("--- PART D: Bezout entry sparsity analysis ---")
    flush(stdout)

    function monomial_support_report(f; indent::String="        ")
        # variables actually appearing (nonzero exponent in at least one term)
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

    for i in 0:3, j in i:3   # symmetric, only report each distinct entry once
        f = B[(i,j)]
        println("  B[$i,$j]:")
        println("    total_degree=", total_degree(f), "  terms=", length(terms(f)))
        monomial_support_report(f)
        # common-factor check: gcd across the polynomial's own terms is
        # not directly a builtin op (terms don't individually gcd against
        # each other in the usual sense) -- what's meaningful here is
        # whether factor() finds this entry has a nontrivial factorization
        # (i.e. gcd of its irreducible factors' multiplicities > trivial),
        # which safe_factor_report already reports. Run it once per
        # entry as requested.
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
            # gcd across r's coefficients, same content check as Part B
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
    println("Answering:")
    println("  1. Hidden factors in g1/g2?      -> see PART A/B factor() and gcd reports")
    println("  2. Redundant symmetric variables? -> see PART C term-count reduction %")
    println("  3. PRS cheaper than Bezout?       -> compare PART E single-step sizes")
    println("     against the PART D Bezout entry sizes above (~83k terms/entry)")
    println("  4. Representation change feasible? -> see PART C (symmetric basis) and")
    println("     PART B (content extraction) results together")
    println("=" ^ 70)
    flush(stdout)

    ############################################################################
    # PART F: exploit p_i in F[a1,a2] / q_j in F[b1,b2] separability.
    #
    # Section 1's fix established that g1's T-coefficients (p_0..p_4) are
    # PURELY (a1,a2)-polynomials and g2's T-coefficients (q_0..q_4) are
    # PURELY (b1,b2)-polynomials -- they were never coupled to the other
    # pair to begin with. PART D's Bezout entries came back at EXACTLY
    # 289*289 = 83521 terms, which is not incidental: since p_m and q_n
    # share no variables, p_m*q_n as a flattened polynomial has exactly
    # (#terms of p_m)*(#terms of q_n) terms with zero possible collisions
    # -- i.e. every Bezout entry [p,q]_{m,n} = p_m*q_n - p_n*q_m is really
    # a RANK-<=2 object (a difference of two outer products of coefficient
    # vectors), not a dense 4-variable polynomial. Flattening it into
    # Rcoef immediately (as bracket_num does) throws that structure away
    # and forces every downstream factor()/gcd()/prem() call to pay the
    # dense 4-variable cost.
    #
    # The fix: introduce an ABSTRACT 10-variable ring F[P0..P4,Q0..Q4]
    # (one symbol per T-coefficient of g1 and g2), build the SAME 4x4
    # Bezout matrix entirely in terms of these abstract symbols (a cheap,
    # low-degree computation -- each entry is degree 2 in the P's/Q's
    # jointly, det(B) is degree <=8 total), and substitute the real
    # (a1,a2)-polynomials for P_i / (b1,b2)-polynomials for Q_j only ONCE,
    # at the very end, via a single ring homomorphism evaluate() call.
    # This defers the expensive flattening to the last possible step
    # instead of paying it at every intermediate Bezout/PRS stage.
    ############################################################################
    println()
    println("--- PART F: abstract-variable (P,Q)-separated Bezout/resultant ---")
    println("  (exploits p_i in F[a1,a2] / q_j in F[b1,b2] confirmed by the")
    println("  Section-1 fix above; see PART D's exact 289*289=83521 entry")
    println("  term counts for the empirical signature that motivated this.)")
    flush(stdout)

    # Abstract ring: one symbol per T-coefficient of g1 (P0..P4) and g2
    # (Q0..Q4). Total degree stays tiny here (det(B) is degree <=8) no
    # matter how large the eventual a1,a2,b1,b2-substitutions are.
    Rpq, pq_gens = polynomial_ring(F, ["P0","P1","P2","P3","P4","Q0","Q1","Q2","Q3","Q4"])
    P0,P1,P2,P3,P4,Q0,Q1,Q2,Q3,Q4 = pq_gens
    Pvec = [P0,P1,P2,P3,P4]
    Qvec = [Q0,Q1,Q2,Q3,Q4]

    # Abstract bracket: [P,Q]_{m,n} := P_m*Q_n - P_n*Q_m, cheap (degree 2,
    # <=4 terms) since it's built from single symbols, not the actual
    # 289-term a/b-polynomials.
    abstract_bracket_cache = Dict{Tuple{Int,Int}, Any}()
    function abstract_bracket(m::Int, n::Int)
        key = m < n ? (m, n) : (n, m)
        if !haskey(abstract_bracket_cache, key)
            i, j = key
            abstract_bracket_cache[key] = Pvec[i+1]*Qvec[j+1] - Pvec[j+1]*Qvec[i+1]
        end
        return m < n ? abstract_bracket_cache[key] : -abstract_bracket_cache[key]
    end

    # Same 10 distinct symmetric entries as the concrete Bezout block
    # above, but now built from the cheap abstract brackets.
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

    # Assemble the abstract 4x4 matrix and compute its determinant --
    # this is the entire "resultant via Bezout" computation, but done
    # while every entry is still degree <=2 in 10 variables, so det()
    # only ever has to expand a determinant of small-degree polynomials,
    # never the 83521-term flattened entries.
    println("  Assembling abstract 4x4 matrix and computing det()...")
    flush(stdout)
    t0f = time()
    Bpq_mat = matrix(Rpq, [Bpq[(i,j)] for i in 0:3, j in 0:3])
    detB_abstract = det(Bpq_mat)
    el_f = time() - t0f
    println("  det(Bpq) computed in ", round(el_f, digits=3), "s: degree=",
            total_degree(detB_abstract), "  terms=", length(terms(detB_abstract)))
    flush(stdout)

    # Substitution homomorphism: P_i -> actual (a1,a2)-polynomial
    # g1_coefs_poly[i+1], Q_j -> actual (b1,b2)-polynomial
    # g2_coefs_poly[j+1]. This is the ONE place the real, large
    # coefficients ever enter the computation -- everything above this
    # line was cheap regardless of how large g1_coefs_poly/g2_coefs_poly
    # are, because it only ever manipulated the 10 abstract placeholders.
    # ------------------------------------------------------------------
    # Substitution strategy: DISK-BACKED, term-by-term.
    #
    # The single evaluate(detB_abstract, subst_vals) call OOM'd: even
    # though det(Bpq) is only 219 terms in the abstract (P,Q) symbols,
    # each term substitutes in as a product of up to 4 of the 289-term
    # p_i's (all living in the SAME 2-variable ring F[a1,a2], degree<=32
    # each) times up to 4 of the 289-term q_j's (same, in F[b1,b2]).
    # Because the p_i's share variables with each other, their product
    # doesn't blow up combinatorially the way cross-ring products do --
    # a product of 4 degree-32-in-2-variables polynomials is still only
    # a degree-<=128-in-2-variables polynomial, capped at C(128+2,2) =
    # 8385 monomials -- but the (a1,a2)-part times the (b1,b2)-part IS a
    # cross-ring product (disjoint variables, no collisions), so a single
    # substituted det() term can still have up to ~8385*8385 ~= 70
    # million monomials before any further collection. evaluate() was
    # trying to build and sum all 219 such terms simultaneously in one
    # in-memory polynomial, which is what actually exhausted RAM.
    # ------------------------------------------------------------------
    println("  Substituting real (a1,a2)/(b1,b2) coefficients into det(Bpq),",
            " term-by-term with disk-backed accumulation",
            " (single in-memory evaluate() OOM'd here previously)...")
    flush(stdout)

    subst_vals = vcat(
        g1_coefs_poly,   # P0..P4 -> p_0..p_4, already Rcoef elements (pure F[a1,a2])
        g2_coefs_poly,   # Q0..Q4 -> q_0..q_4, already Rcoef elements (pure F[b1,b2])
    )

    # ------------------------------------------------------------------
    # SHARDED checkpointing (fixes the OOM from resuming a monolithic
    # accumulator file).
    #
    # The previous design kept ONE running-sum file (accum.oscar) that
    # was overwritten -- serialized WHOLE -- every PARTF_CHECKPOINT_EVERY
    # terms, growing every checkpoint. That bounded RAM during the
    # substitution loop itself, but load(accum_file) on resume still has
    # to deserialize that entire, ever-larger polynomial as ONE object in
    # ONE call. There is no incremental/streaming load in Oscar's
    # save()/load(). By 200/219 terms the accumulator is (per the
    # existing "multi-million-term", "multi-GB polynomial" comments
    # below) large enough that THIS load is what actually exhausted RAM
    # -- the run's own log ends immediately after printing "resuming:
    # 200/219 terms...", i.e. it died inside/around load(accum_file),
    # before even the next line ("loaded checkpoint has N terms...")
    # could be printed. Checkpointing more often or less often doesn't
    # help: it only changes the SIZE of the one thing load() has to
    # deserialize, not whether load() has to deserialize the whole
    # thing at once.
    #
    # Fix: instead of one growing accum file, each checkpoint writes a
    # new, separately-numbered SHARD file containing only the DELTA
    # folded since the previous shard (i.e. the partial sum of just the
    # terms processed since the last checkpoint) -- bounded in size by
    # PARTF_CHECKPOINT_EVERY terms' worth of substitution, not by how
    # far through the 219 terms we are. On resume, shards are summed
    # back together ONE AT A TIME (load shard -> add! into running total
    # -> drop shard from memory -> load next shard), so peak resident
    # memory during resume is one shard's worth plus the running total
    # under construction, not the entire final accumulator deserialized
    # in a single call.
    PARTF_SCRATCH_DIR = joinpath(ELIM2_ROOT_DIR, "part_f_scratch", name)
    mkpath(PARTF_SCRATCH_DIR)
    shards_dir     = joinpath(PARTF_SCRATCH_DIR, "shards")
    mkpath(shards_dir)
    shard_tmpfile  = joinpath(PARTF_SCRATCH_DIR, "shard.oscar.tmp")
    progress_file  = joinpath(PARTF_SCRATCH_DIR, "progress.txt")
    manifest_file  = joinpath(PARTF_SCRATCH_DIR, "manifest.txt")

    # Shard filenames are zero-padded and named by the LAST term index
    # they include, so sorting filenames = chronological order.
    shard_path(upto_term_idx) = joinpath(shards_dir, "shard_" * lpad(upto_term_idx, 6, '0') * ".oscar")
    function existing_shard_paths()
        !isdir(shards_dir) && return String[]
        names = filter(f -> startswith(f, "shard_") && endswith(f, ".oscar"), readdir(shards_dir))
        return sort(joinpath.(shards_dir, names))   # filename padding keeps this chronological
    end

    detB_terms = collect(terms(detB_abstract))
    n_terms = length(detB_terms)
    println("  det(Bpq) has ", n_terms, " monomials to substitute; streaming each",
            " into per-checkpoint SHARD files (each holding only the delta",
            " folded since the previous shard) under ", shards_dir,
            " -- resuming sums shards back in one at a time, so peak resume",
            " memory is one shard plus the running total, not the whole",
            " final accumulator deserialized in a single load().")
    flush(stdout)

    # Streamed substitute-and-accumulate: for each monomial of
    # detB_abstract, substitute it (bounded RAM: worst case ~289^4
    # monomials before collection for a single term, same as before) and
    # immediately fold it into a running-sum polynomial IN MEMORY. Every
    # PARTF_CHECKPOINT_EVERY terms, the terms accumulated so far THIS RUN
    # (the delta, not the grand total) are written out as a new shard
    # file, so disk usage grows with the number of checkpoints taken, not
    # with n_terms, and no single shard is bigger than one checkpoint
    # interval's worth of folded terms.
    #
    # Resumability: progress_file records how many of the n_terms
    # monomials (in the fixed order given by detB_terms) are already
    # folded into some shard on disk. On restart, every existing shard is
    # loaded and add!-ed into the in-memory accumulator ONE SHARD AT A
    # TIME (drop each shard from memory before loading the next), then
    # substitution resumes at n_already_done+1 -- rather than either
    # re-substituting everything or deserializing one giant merged file.
    t0terms = time()
    n_already_done = 0
    detB_concrete = zero(Rcoef)   # preallocated accumulator -- never replaced by
                                   # a fresh object after this; add! mutates it
                                   # in place every iteration instead of + allocating
                                   # a brand-new ~17.8M-term polynomial each time.
    if isfile(progress_file)
        n_already_done = parse(Int, strip(read(progress_file, String)))
        if n_already_done > 0
            shard_paths = existing_shard_paths()
            println("  resuming: ", n_already_done, "/", n_terms,
                    " terms already folded, spread across ", length(shard_paths),
                    " shard file(s) from a previous run.")
            flush(stdout)
            t0resume = time()

            for (shard_i, sp) in enumerate(shard_paths)
                t0shard = time()
                loaded = load(sp)
                loaded_n_terms = length(loaded)
                print("    shard ", shard_i, "/", length(shard_paths),
                      " (", basename(sp), "): loaded ", loaded_n_terms, " terms")
                flush(stdout)

                # Try the cheap path first: Rcoef(loaded) is a single C-level
                # FLINT call and is FAST if the parent rings happen to be
                # compatible this time (this is not guaranteed to fail --
                # it's environment/version dependent, see comment below).
                # Only fall back to the slow, one-term-at-a-time Julia loop
                # (which was silently costing MINUTES for a large shard with
                # zero progress output, and looked exactly like a hang) if
                # the fast coercion actually throws.
                local rebuilt
                try
                    rebuilt = Rcoef(loaded)
                    print("; cheap coercion ok (", round(time() - t0shard, digits=1), "s)")
                catch e
                    println()
                    println("      cheap coercion failed (", typeof(e), ") -- falling",
                            " back to term-by-term rebuild for this shard. This is the",
                            " SLOW path: one push_term! call per term (", loaded_n_terms,
                            " total here), each a separate FFI call into FLINT with no",
                            " batching -- for a large shard this can legitimately take",
                            " minutes with NO progress output, which is exactly what",
                            " looked like a hang before this message was added.",
                            " Printing progress every 500k terms so it's visible",
                            " instead of silent:")
                    flush(stdout)
                    # save()/load() does not guarantee returning a polynomial in
                    # the IDENTICAL Rcoef parent object (even though it's the
                    # same ring mathematically) -- Nemo's coercion, R(other_poly),
                    # is stricter than that and can throw "Unable to coerce
                    # polynomial". Sidestep coercion entirely: rebuild the
                    # loaded polynomial term-by-term straight into Rcoef's own
                    # generators, the same MPolyBuildCtx/push_term!/finish
                    # pattern used by remap_to_final elsewhere in this file.
                    # Generator order is identity here (both rings are Rcoef's
                    # own [a1,a2,b1,b2] declared order), so no gen_map is needed.
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

                # Fold this shard into the running accumulator, then drop
                # the shard's own objects before loading the next one --
                # never more than one shard resident at a time.
                global detB_concrete = detB_concrete + rebuilt
                loaded = nothing
                rebuilt = nothing
                GC.gc(false)
                println("  -- folded (", round(time() - t0shard, digits=1), "s,",
                        " running total now ", length(terms(detB_concrete)), " terms)")
                flush(stdout)
            end
            println("  resume: all shards folded in ", round(time() - t0resume, digits=1), "s.")
        end
    end

    # Detect once, outside the hot loop, whether this Nemo/AbstractAlgebra
    # install actually supports in-place add! on Rcoef elements (some
    # versions/ring types silently fall back to allocating regardless, in
    # which case applicable() below will just be false and we use plain +
    # -- correctness never depends on this, only speed).
    #
    # Separately verify SELF-ALIASED add!(a, a, c) actually produces the
    # right numeric result, not just that the method exists -- some
    # AbstractAlgebra in-place implementations only support add!(a, b, c)
    # for a distinct from b/c, and silently misbehave (not error) if a
    # aliases one of its inputs. This is checked ONCE with tiny throwaway
    # values, never against the real 17.8M-term accumulator, so it's
    # cheap and safe to always run.
    HAVE_INPLACE_ADD = applicable(add!, detB_concrete, detB_concrete, detB_concrete)
    HAVE_SAFE_SELF_ALIAS_ADD = false
    if HAVE_INPLACE_ADD
        _probe = Rcoef(gens(Rcoef)[1])          # tiny throwaway: just "a1"
        _probe_expected = _probe + _probe        # == 2*a1, via plain +
        _probe_copy = deepcopy(_probe)
        add!(_probe_copy, _probe_copy, _probe)
        HAVE_SAFE_SELF_ALIAS_ADD = (_probe_copy == _probe_expected)
    end

    if HAVE_SAFE_SELF_ALIAS_ADD
        println("  in-place add! (self-aliased) verified correct for Rcoef",
                " elements -- accumulator will be mutated in place each",
                " term (no full reallocation).")
    elseif HAVE_INPLACE_ADD
        println("  add! exists but self-aliased add!(a,a,c) did NOT match",
                " plain + on a probe value -- NOT safe to use here.",
                " Falling back to + (correct, but each fold reallocates",
                " the full accumulator).")
    else
        println("  in-place add! NOT available for Rcoef elements on this",
                " Nemo/AbstractAlgebra version -- falling back to +",
                " (correct, but each fold reallocates the full accumulator).")
    end
    flush(stdout)

    # NOTE on GC instrumentation: Base.gc_num() was tried here first and
    # proved UNRELIABLE for this workload -- it reported NEGATIVE bytes
    # allocated in a live run (-0.52 GB, -0.35 GB), which happens because
    # FLINT/Nemo mpoly data lives in C-allocated memory that Julia's GC
    # does not track at all; gc_num() only sees the thin Julia-side
    # wrapper, not the actual multi-GB polynomial backing storage. Since
    # GC time was also negligible (0.3-1.2s) while ~40s/iteration stayed
    # unaccounted, GC is RULED OUT. Replaced with direct RSS (resident
    # set size) sampling from /proc/self/status, which reflects actual
    # process memory regardless of which allocator (Julia GC or FLINT's
    # own malloc) is responsible -- this will show whether the missing
    # time correlates with memory growth (consistent with FLINT
    # allocating/copying large buffers) or not (pointing elsewhere, e.g.
    # disk cache eviction pressure from the save() calls).
    function read_rss_mb()
        for line in eachline("/proc/self/status")
            if startswith(line, "VmRSS:")
                # format: "VmRSS:	 1234567 kB"
                parts = split(line)
                return parse(Int, parts[2]) / 1024.0   # kB -> MB
            end
        end
        return -1.0
    end

    max_term_size_seen = 0
    max_term_size_idx = 0
    # Tracks only what's been folded since the last shard was written to
    # disk -- this, not detB_concrete, is what gets serialized into each
    # shard file, so shard size is bounded by one checkpoint interval's
    # worth of terms instead of growing with the grand total.
    global delta_since_checkpoint = zero(Rcoef)
    for (i, t) in enumerate(detB_terms)
        if i <= n_already_done
            continue   # already folded into detB_concrete in a previous run
        end
        t0iter = time()
        rss_before = read_rss_mb()

        t0eval = time()
        # ------------------------------------------------------------
        # CHUNKED substitution (fixes the OOM from evaluate(t, subst_vals)).
        #
        # A single term t of detB_abstract is a monomial in P0..P4,Q0..Q4,
        # e.g. coeff * P_i1*P_i2 * Q_j1*Q_j2 (up to 4 P's and 4 Q's,
        # since det(Bpq) is degree <=8 total and each abstract_bracket
        # entry mixes P's and Q's). Substituting P_k -> p_k (a
        # ~289-term poly in F[a1,a2]) and Q_k -> q_k (a ~289-term poly
        # in F[b1,b2]) and calling evaluate() on the WHOLE monomial at
        # once forces Nemo to build the FULL cross product -- up to
        # ~8385*8385 ~= 70 million monomials -- as one single
        # intermediate polynomial before any collection/addition
        # happens. That intermediate is what exhausted RAM; it was
        # never kept, only the (smaller) sum, but building it even
        # transiently requires having all 70M terms live in memory
        # simultaneously.
        #
        # Fix: exploit exactly the disjoint-variable structure the
        # PART F comment above already identified. Split the term's
        # exponent vector into its P-part and Q-part, compute:
        #   a_side = product of the p_k's raised to their P-exponents
        #            (pure F[a1,a2] arithmetic, capped at ~8385 terms)
        #   b_side = product of the q_k's raised to their Q-exponents
        #            (pure F[b1,b2] arithmetic, capped at ~8385 terms)
        # separately -- each of these is cheap and bounded. Then fold
        # coeff * a_side * b_side into the accumulator NOT as one
        # multiply, but by walking a_side in small term-batches
        # (PARTF_CHUNK terms at a time), multiplying each batch by the
        # full b_side (a batch of <=PARTF_CHUNK terms times an
        # <=8385-term poly is at most PARTF_CHUNK*8385 monomials, not
        # 8385*8385), and add!-ing each partial product straight into
        # detB_concrete before moving to the next batch. At no point
        # do we hold more than one chunk's worth of the cross product
        # in memory -- the full a_side*b_side product is never
        # materialized as a single object.
        # ------------------------------------------------------------
        t_exps = first(AbstractAlgebra.exponent_vectors(t))
        t_coeff = first(coefficients(t))

        a_side = one(Rcoef)
        b_side = one(Rcoef)
        for k in 1:5
            ePk = t_exps[k]        # exponent of P_{k-1} in this monomial
            eQk = t_exps[5 + k]    # exponent of Q_{k-1} in this monomial
            if ePk > 0
                a_side = a_side * (g1_coefs_poly[k]^ePk)
            end
            if eQk > 0
                b_side = b_side * (g2_coefs_poly[k]^eQk)
            end
        end
        a_side = t_coeff * a_side   # fold the term's scalar coefficient into the (smaller) a-side

        this_size = length(terms(a_side)) * length(terms(b_side))   # worst-case bound, for reporting only
        if this_size > max_term_size_seen
            global max_term_size_seen = this_size
            global max_term_size_idx = i
        end

        # PARTF_CHUNK terms per batch, on BOTH sides. Previously only
        # a_side was chunked (PARTF_CHUNK terms) while b_side was kept
        # whole (up to ~8385 terms) and multiplied against each a-chunk
        # in full -- so each partial product could still be up to
        # PARTF_CHUNK*8385 (~1.7M) monomials before collection, and with
        # a_side/b_side each capable of reaching that ~8385-term bound
        # independently (not just in the worst case Claire's original
        # comment sized for), that was the actual OOM source, not just
        # the single-shot evaluate() this loop already replaced. Nesting
        # the chunking on both sides bounds every single cross-product
        # batch to at most PARTF_CHUNK*PARTF_CHUNK monomials, independent
        # of how large a_side/b_side get.
        PARTF_CHUNK = 200   # terms per batch per side; tune down further if RSS still climbs
        a_terms = collect(terms(a_side))
        b_terms = collect(terms(b_side))
        n_a_terms = length(a_terms)
        n_b_terms = length(b_terms)
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
                    add!(detB_concrete, detB_concrete, partial)
                    add!(delta_since_checkpoint, delta_since_checkpoint, partial)
                else
                    global detB_concrete = detB_concrete + partial
                    global delta_since_checkpoint = delta_since_checkpoint + partial
                end
                partial = nothing
                b_chunk = nothing
                b_chunk_start = b_chunk_end + 1
            end
            a_chunk = nothing
            a_chunk_start = a_chunk_end + 1
        end
        a_side = nothing
        b_side = nothing
        a_terms = nothing   # drop references explicitly before the timed GC sweep below
        b_terms = nothing
        el_eval = time() - t0eval
        rss_after_eval = read_rss_mb()

        t0fold = time()
        # Folding now happens inside the chunk loop above (one add! per
        # chunk rather than one add! for the whole term), so this stage
        # is a no-op left in place only so the existing timing/RSS
        # instrumentation below still has a well-defined (zero-length)
        # "fold" phase to report -- the real fold cost is now counted
        # inside el_eval, which is the honest place for it to live given
        # it's now interleaved with the substitution.
        el_fold = time() - t0fold
        rss_after_fold = read_rss_mb()

        # Force one full collection here, now that this term's a_side/
        # b_side/a_terms/each chunk's partial product are all
        # unreachable (each chunk is already dropped inside the loop
        # above, but a_side/b_side/a_terms themselves are only freed
        # once the whole term is done). This turns what would otherwise
        # be unpredictable incremental GC pauses scattered through the
        # NEXT term's chunk loop into one accounted-for sweep here,
        # timed separately so it shows up explicitly instead of as
        # "unaccounted" wall-clock.
        t0gc = time()
        GC.gc(false)   # false = not full/aggressive; just reclaim what's already dead
        el_gc = time() - t0gc
        rss_after_gc = read_rss_mb()

        # Checkpoint: write ONLY this interval's delta (delta_since_checkpoint)
        # to a new, uniquely-named shard file (via a temp file + atomic
        # rename so a crash mid-write never leaves a half-written shard
        # that progress_file claims is complete), then update the
        # progress counter and reset the delta accumulator to zero.
        #
        # Unlike the previous single-accum-file design, a shard's size is
        # bounded by PARTF_CHECKPOINT_EVERY terms' worth of substitution
        # -- it does NOT grow as the loop progresses, since it never
        # holds anything from before the last checkpoint. This is what
        # fixes the resume-time OOM: load() on any one shard only ever
        # has to deserialize one checkpoint interval's worth of data,
        # never the full accumulator (see the resume block above, which
        # sums shards back in one at a time instead of doing one
        # load(accum_file) on a single ever-growing file).
        #
        # Each sub-step timed separately -- in particular mv() is only a
        # fast atomic rename if shard_tmpfile and the shard's final path
        # are on the SAME filesystem; if PARTF_SCRATCH_DIR straddles a
        # filesystem boundary (e.g. tmp on one mount, scratch dir on
        # another), Julia silently falls back to a full copy+delete for
        # mv(), which would otherwise show up as unexplained missing time.
        PARTF_CHECKPOINT_EVERY = 5   # terms between checkpoints; lower if a crash near the end of a run is costing too much re-work, raise if save() itself is still RAM-heavy at this cadence
        do_checkpoint = (i % PARTF_CHECKPOINT_EVERY == 0) || (i == n_terms)

        local el_write, el_mv, el_prog, rss_after_save
        if do_checkpoint
            t0write = time()
            save(shard_tmpfile, delta_since_checkpoint)
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

            # Reset the delta accumulator now that its contents are
            # safely on disk in this shard -- the NEXT shard should only
            # contain terms folded after this point.
            global delta_since_checkpoint = zero(Rcoef)
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
            println("        RSS (resident memory, MB) -- before iter: ", round(rss_before, digits=0),
                    "  after evaluate: ", round(rss_after_eval, digits=0),
                    " (Δ", round(rss_after_eval - rss_before, digits=0), ")",
                    "  after fold: ", round(rss_after_fold, digits=0),
                    " (Δ", round(rss_after_fold - rss_after_eval, digits=0), ")",
                    "  after gc: ", round(rss_after_gc, digits=0),
                    " (Δ", round(rss_after_gc - rss_after_fold, digits=0), ")",
                    "  after save: ", round(rss_after_save, digits=0),
                    " (Δ", round(rss_after_save - rss_after_gc, digits=0), ")")
            println("        (Note: Base.gc_num()-based instrumentation was tried",
                    " and abandoned -- it reported NEGATIVE bytes allocated for",
                    " this workload because FLINT/Nemo mpoly data lives in",
                    " C-allocated memory outside Julia's GC accounting. RSS",
                    " above reflects the OS's view of actual process memory",
                    " regardless of which allocator is responsible, and is the",
                    " ground truth for where the unaccounted time correlates",
                    " with memory growth.)")
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

    println("  substitution done (disk-backed, streamed): degree=",
            total_degree(detB_concrete), "  terms=", length(terms(detB_concrete)),
            "  (", round(el_sub, digits=1), "s total this run)")
    flush(stdout)

    # Record the manifest so a subsequent run (or a human) can tell at a
    # glance that this result came from the disk-backed path and where
    # the checkpoint file lives, without needing to re-derive it.
    open(manifest_file, "w") do io
        println(io, "PART F disk-backed substitution manifest for $name")
        println(io, "n_terms = $n_terms")
        println(io, "checkpoint shards dir = $shards_dir")
        println(io, "final degree = ", total_degree(detB_concrete))
        println(io, "final terms  = ", length(terms(detB_concrete)))
    end

    # Cross-check against the concrete (already-flattened) Bezout matrix
    # built above: det(B) via the abstract route should agree exactly
    # with det() computed directly on the concrete B, since it's the
    # same matrix. HOWEVER: det(B_mat_concrete) is exactly the dense,
    # single-shot computation that OOM'd in the first place (it has to
    # internally build and sum the same huge products the disk-backed
    # path above was written to avoid) -- so it is NOT run by default.
    # Gate it behind an explicit opt-in, same pattern as
    # RUN_FULL_RESULTANT below, so re-confirming correctness on a
    # machine with enough RAM is a deliberate choice, not something that
    # silently reproduces the crash every run.
    RUN_PARTF_DIRECT_CROSSCHECK = get(ENV, "ELIM2_PARTF_DIRECT_CROSSCHECK", "false") == "true"
    if @isdefined(B) && RUN_PARTF_DIRECT_CROSSCHECK
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
    elseif @isdefined(B)
        # Cheap partial correctness signal instead: re-derive a handful
        # of individual concrete Bezout entries (already computed as B[..]
        # above, at ~83521 terms each -- NOT re-flattening the whole
        # determinant) via the abstract-bracket substitution route, and
        # confirm they agree entry-by-entry. This is orders of magnitude
        # cheaper than det() on the full matrix (it's just re-checking
        # the entries, which were already built and paid for above),
        # while still directly testing whether evaluate() on a single
        # abstract bracket matches the concrete bracket_num() path.
        println("  Skipping full det(B) cross-check (set ",
                "ELIM2_PARTF_DIRECT_CROSSCHECK=true to enable -- expensive,",
                " dense, same computation that OOM'd before). Running a",
                " cheaper per-entry spot-check instead:")
        flush(stdout)
        n_mismatch = 0
        for (i, j) in [(0,0), (1,2), (2,3), (3,3)]
            abstract_entry_concrete = evaluate(Bpq[(i,j)], subst_vals)
            same = abstract_entry_concrete == B[(i,j)]
            global n_mismatch += !same
            println("    entry ($i,$j): abstract-route == concrete B[$i,$j]? ", same)
        end
        println("    spot-check: ", n_mismatch == 0 ? "all entries agree" :
                "$n_mismatch MISMATCH(es) -- investigate before trusting PART F result")
        flush(stdout)
    else
        println("  (concrete B not available for cross-check in this branch)")
    end

    println("  PART F summary: det(Bpq) computed as a degree<=8 polynomial in",
            " 10 abstract symbols, THEN substituted once, instead of building")
    println("  and manipulating dense ", nvars(Rcoef), "-variable ", 83521,
            "-term entries at every intermediate step.")
    flush(stdout)
    ############################################################################
    # END PART F
    ############################################################################
end
