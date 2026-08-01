using Serialization
using Oscar

wpts_nt = deserialize("witness_points.jls")
pts = wpts_nt.points
gen_names = wpts_nt.gen_names
p = 2371157   # NOTE: confirmed against hensel_verification.jls earlier in
              # this session -- re-check if you've since changed p.

x_var_names = [:a1, :a2, :b1, :b2]
x_idx = [findfirst(==(v), gen_names) for v in x_var_names]
any(isnothing, x_idx) &&
    error("Could not find one of ", x_var_names, " in gen_names=", gen_names)

Fp, _ = finite_field(p)
Fpx, xp = polynomial_ring(Fp, "x")

# The two minimal polynomials actually observed across a1,a2,b1,b2 in this
# run (confirmed via guess() on 15 sample points -- NOT assumed to be
# exhaustive; see the fallback branch below for anything that doesn't match
# either). Factored once, here, rather than per-coordinate -- cheap and
# avoids repeating the same factorization 2457*4 times.
f_omega = xp^2 + xp + 1        # roots: primitive cube roots of unity
f_cubic = xp^3 - xp^2 + 1      # the other observed minimal polynomial

fac_omega = factor(f_omega)
fac_cubic = factor(f_cubic)

omega_roots_Fp = [-coeff(g, 0) for (g, _) in fac_omega if degree(g) == 1]
cubic_roots_Fp = [-coeff(g, 0) for (g, _) in fac_cubic if degree(g) == 1]

println("x^2+x+1 mod p: ", fac_omega, " -- ",
        isempty(omega_roots_Fp) ? "NO root in F_p (needs an extension)" :
        "root(s) in F_p: $omega_roots_Fp")
println("x^3-x^2+1 mod p: ", fac_cubic, " -- ",
        length(cubic_roots_Fp), " root(s) in F_p: ", cubic_roots_Fp)
println()

# ---------------------------------------------------------------------------
# Closed-form recognition instead of guess(): omega = -1/2 + i*sqrt(3)/2 (or
# its conjugate) has an exact algebraic form, so we can check a coordinate
# against it directly via a numeric comparison at working precision, rather
# than running guess()'s general search. Same idea for the cubic's three
# real roots (all three factors are linear over Q here in the sense that the
# minimal polynomial x^3-x^2+1 has three REAL roots numerically -- confirmed
# by the a1/b1-type points having |im|~1e-7, i.e. genuinely real, in the
# earlier diagnostic run). We match against the polynomial's actual roots
# computed once via Nemo (exact, not re-derived from HC.jl's noisy value),
# then compare.
# ---------------------------------------------------------------------------

CC = AcbField(128)
QQx, xq = polynomial_ring(QQ, "x")
# Built directly from literal coefficients in QQ[x] -- deliberately NOT
# reusing f_omega/f_cubic, which live in Fp[x] (a different ring; you can't
# just coerce an Fp[x] polynomial back to QQ[x], the coefficients have
# already been reduced mod p and lost their integer identity).
omega_roots_C = roots(CC, xq^2 + xq + 1)
cubic_roots_C = roots(CC, xq^3 - xq^2 + 1)

const MATCH_TOL = 1e-4  # generous vs. the ~1e-6/1e-7 noise seen in the data

function classify_coordinate(z::ComplexF64)
    for (i, r) in enumerate(omega_roots_C)
        if abs(z - ComplexF64(r)) < MATCH_TOL
            return (:omega_type, i)
        end
    end
    for (i, r) in enumerate(cubic_roots_C)
        if abs(z - ComplexF64(r)) < MATCH_TOL
            return (:cubic_type, i)
        end
    end
    return (:unrecognized, nothing)
end

println("Classifying a1,a2,b1,b2 across all ", length(pts), " witness points ",
        "against the two known minimal polynomials (fast path), falling back ",
        "to nothing further for unrecognized coordinates (those need a fresh ",
        "guess() call -- flagged below, not silently dropped).")
println()

n_omega = 0
n_cubic = 0
n_unrecognized = 0
d1_points = Int[]           # points where ALL of a1,a2,b1,b2 are cubic-type (F_p-reducible)
unrecognized_examples = Tuple{Int,Symbol,ComplexF64}[]

for (i, pt) in enumerate(pts)
    all_cubic = true
    for (name, idx) in zip(x_var_names, x_idx)
        z = pt[idx]
        kind, _ = classify_coordinate(z)
        if kind == :omega_type
            global n_omega += 1
            all_cubic = false
        elseif kind == :cubic_type
            global n_cubic += 1
        else
            global n_unrecognized += 1
            all_cubic = false
            push!(unrecognized_examples, (i, name, z))
        end
    end
    all_cubic && push!(d1_points, i)
end

println("omega_type (x^2+x+1, NOT in F_p at this p): ", n_omega)
println("cubic_type (x^3-x^2+1, splits in F_p): ", n_cubic)
println("unrecognized (neither known polynomial): ", n_unrecognized)
println()
println("Points where a1,a2,b1,b2 are ALL cubic_type (d1 factor-base ",
        "candidates): ", length(d1_points), " / ", length(pts))
println()

if !isempty(unrecognized_examples)
    println("First few unrecognized coordinates (worth a fresh guess() pass,")
    println("these are real findings, not classification bugs, UNLESS the")
    println("count is suspiciously large relative to omega/cubic -- if so,")
    println("check MATCH_TOL and the root lists above before trusting this):")
    for (i, name, z) in first(unrecognized_examples, min(10, length(unrecognized_examples)))
        println("  point $i, $name = $z")
    end
end
println()

length(d1_points) > 0 ||
    println("WARNING: zero d1 candidates found among all ", length(pts),
            " points. Given x^2+x+1 was confirmed irreducible mod p ",
            "earlier, and roughly half the sampled coordinates were ",
            "omega_type, a fully empty d1 set across 2457 points would be ",
            "surprising -- worth double-checking MATCH_TOL / the root lists ",
            "before concluding d1 is genuinely empty at this p.")

# Save the d1 candidate point indices for downstream use, rather than just
# printing them and losing the result the way earlier runs lost the witness
# points themselves.
serialize("d1_candidate_indices.jls", d1_points)
println("Saved ", length(d1_points), " candidate point index(es) to d1_candidate_indices.jls")
