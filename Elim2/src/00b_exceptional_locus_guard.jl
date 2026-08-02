################################################################################
#
#  00b_exceptional_locus_guard.jl -- part of the Elim2 package (src/Elim2.jl
#  includes this file, between 00_sample_specs.jl and 01_elim2_main.jl -- see
#  src/Elim2.jl for the package-level include order).
#
#  Module: ExceptionalLocusGuard
#
#  Symbolic, mod-p precondition check on a SampleSpec: does its divisor
#  class D lie in section 6.2's exceptional locus (D ~ K_C), the one place
#  the advisory's generic-finiteness argument (sigma: C^(2) -> J generically
#  birational, for genus 2) does not apply? Checked here, BEFORE
#  Elim2Main.run_main does any tower construction or hands anything to
#  HC.jl, so a bad spec is caught for the cost of two mod-p operations
#  rather than after a ~26900s solve.
#
#  Depends only on SampleSpecs (for the SampleSpec type) -- no Oscar, no
#  HC.jl -- same "cheap, no heavy deps" placement rationale SampleSpecs
#  itself already documents for part_j_worker.jl's sake.
#
################################################################################
module ExceptionalLocusGuard

using ..SampleSpecs: SampleSpec

export hits_exceptional_locus, guard_sample_spec

"""
    hits_exceptional_locus(spec::SampleSpec, p::Int) -> (hits::Bool, detail::NamedTuple)

Exact, mod-p check of whether `spec`'s divisor class D lies in section 6.2's
exceptional locus (D ~ K_C), i.e. whether sigma: C^(2) -> J fails to be
injective at D. D ~ K_C iff {P,Q} is a hyperelliptic-involution-conjugate
pair, i.e. u(x) = x^2 + u1*x + u0 has a repeated root x0 AND v(x0) = 0.

Returns `hits = true` only when both conditions hold. `detail` always
reports the discriminant and (when computable) the repeated root and
v(x0), so a caller can distinguish "not exceptional" from "double point,
but not D~K_C specifically" (see the tangency case below) rather than
only getting a single boolean.

Sanity note kept from the derivation: a repeated root x0 of u forces
P=Q=(x0,y0) under a naive reading, but the Mumford v-polynomial resolves
the multiplicity -- the genuine reduced divisor with a double x-root is
P+iota(P) exactly when v(x0)=0 (the D~K_C case handled here), vs. the
honest double point 2P (a tangency, a DIFFERENT non-generic locus also
not covered by section 6.2) when v(x0)!=0.
"""
function hits_exceptional_locus(spec::SampleSpec, p::Int)
    u0, u1, v0, v1 = spec.u0, spec.u1, spec.v0, spec.v1

    disc = mod(u1^2 - 4*u0, p)

    if disc != 0
        return (false, (discriminant = disc, repeated_root = nothing,
                         v_at_root = nothing,
                         note = "u has distinct roots -- not on the exceptional locus"))
    end

    # disc == 0: repeated root x0 = -u1/2 mod p. Requires 2 invertible mod
    # p, true for any odd prime; default_curve_config's p=2371157 is odd,
    # but this is not silently assumed for a caller passing a different p.
    isodd(p) || error("hits_exceptional_locus: p=$p is even -- 2 is not " *
                       "invertible mod p, the repeated-root formula x0=-u1/2 " *
                       "does not apply as written")
    inv2 = invmod(2, p)
    x0 = mod(-u1 * inv2, p)

    v_at_x0 = mod(v1 * x0 + v0, p)

    if v_at_x0 == 0
        return (true, (discriminant = disc, repeated_root = x0, v_at_root = v_at_x0,
                        note = "u has repeated root x0 AND v(x0)=0 -- D = P+iota(P) ~ K_C, ON the exceptional locus"))
    else
        return (false, (discriminant = disc, repeated_root = x0, v_at_root = v_at_x0,
                         note = "u has repeated root x0 but v(x0)!=0 -- this is a tangency (D=2P), " *
                                "NOT the D~K_C exceptional locus of section 6.2; sigma's injectivity " *
                                "failure mode here is different and not covered by that argument either -- " *
                                "flagged, not silently treated as safe"))
    end
end

"""
    guard_sample_spec(spec::SampleSpec, p::Int; label::String="")

Raises an ErrorException if `spec` hits the D~K_C exceptional locus (section
6.2's argument does not cover this case, silently proceeding would let a
generic-finiteness argument be invoked where it doesn't apply). Also raises
-- with a distinct message -- on the tangency case (D=2P), a different,
also-uncovered failure mode of sigma's injectivity, so it isn't conflated
with "safe" either. Called from Elim2Main.run_main on both samples, right
after they're generated and before call_symbolic_residual does any tower
work.
"""
function guard_sample_spec(spec::SampleSpec, p::Int; label::String = "")
    hits, detail = hits_exceptional_locus(spec, p)
    if hits
        error("guard_sample_spec($label): D ~ K_C (exceptional locus of " *
              "section 6.2's generic-finiteness argument) -- discriminant=0, " *
              "repeated root x0=$(detail.repeated_root), v(x0)=0. This spec's " *
              "divisor class is exactly where sigma: C^(2) -> J fails to be " *
              "injective; section 6.2 does not establish finiteness here. " *
              "Regenerate the spec (different seed/alpha) rather than solving " *
              "this instance and trusting the generic argument.")
    end
    if detail.repeated_root !== nothing && detail.v_at_root != 0
        error("guard_sample_spec($label): u(x) has a repeated root (x0=" *
              "$(detail.repeated_root)) with v(x0)!=0 -- this is the D=2P " *
              "tangency case, a DIFFERENT non-generic locus not covered by " *
              "section 6.2 either. Regenerate the spec rather than solving " *
              "this instance and trusting the generic argument.")
    end
    return nothing
end

end # module ExceptionalLocusGuard
