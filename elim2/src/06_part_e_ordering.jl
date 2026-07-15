println("PART E: ordering actually in use")
println("===========================================================")
println()
println("block_ordering_dec (explicit, only consumed by direct groebner_basis")
println("calls, NOT by eliminate()):")
println("  ", block_ordering_dec)
println()
println("eliminate(I, vars) builds its own internal elimination ordering")
println("(an elimination-ordering variant, block-with-vars-dominant in spirit)")
println("and does not expose that ordering object for inspection via any")
println("documented Oscar API as of this writing -- not claiming a specific")
println("internal implementation here since it isn't independently checkable")
println("from user code. If the exact internal ordering matters, the only")
println("verifiable route is calling groebner_basis(I; ordering=<explicit")
println("elimination ordering built by hand>, algorithm=:f4) directly instead")
println("of eliminate(), so the ordering used is the one YOU constructed and")
println("printed above, not an opaque internal choice.")
println()

################################################################################
# NOTE on running this as isolated subprocesses instead of in-process
# timeouts:
#
# run_with_timeout above cannot truly kill a hung Singular/msolve C call
# -- it just stops WAITING for it. For a real kill (freeing CPU/RAM so
# the next step's timing isn't contaminated by a still-running previous
# step), run each Part B/C step as its own OS process instead:
#
#   timeout 300 julia -t 20 -e '
#       include("elim2_single_step.jl");   # a trimmed script that builds
#                                            # just R_dec/Fu_decoupled/curves
#                                            # and does ONE eliminate() call
#       eliminate(Ik, [wa1_d, wa2_d, wb1_d, wb2_d])
#   '
#
# `timeout 300 ...` (the coreutils command, not Julia code) sends SIGTERM
# after 300s and actually reclaims the process. This is more setup (needs
# the shared construction code factored into an includable file) but is
# the only way to get a clean kill; the in-process version above is
# faster to run right now and sufficient for the first-pass "where does
# it explode" question this instrumentation pass is actually for.
################################################################################

################################################################################
# PART G: FIBER-PRODUCT DECOMPOSITION.
#
# Part B's k=1->k=2 transition (15s, OK -> hang -> segfault) is not
# generic Groebner slowness. Fu_decoupled[1] (sample 1, target U0) and
# Fu_decoupled[2] (sample 2, target U0) share ONLY the variable U0 --
# their w/a/b variables are completely disjoint. That means
# ideal(Fu_decoupled[1], Fu_decoupled[2], curves) is, scheme-
# theoretically, the fiber product of the two samples' varieties over
# the shared U0-coordinate: R_dec/I = (R_a/I_a) (x)_{k[U0]} (R_b/I_b).
#
# Elimination commutes with this structure because eliminating the wa's
# cannot touch any generator that only involves wb's and vice versa:
#
#   elim_{wa1,wa2,wb1,wb2}(Ia + Ib) = elim_{wa1,wa2}(Ia) + elim_{wb1,wb2}(Ib)
#
# as ideals in k[a1,a2,b1,b2,U0]. This is a direct consequence of
# I ∩ k[remaining vars] applied to a sum of ideals in disjoint-except-
# shared-U0 variable sets -- eliminating the wa's is a self-contained
# computation inside k[wa1,wa2,a1,a2,U0] and simply passing through the
# wb-only generators unchanged (they contain no wa's to eliminate), and
# symmetrically for wb. So instead of handing Singular one 6-generator
# ideal in the union of both variable sets (which is what triggered the
# hang/segfault in Part B's k=2 step), do TWO independent eliminations,
# each in its own small ring, and take the SUM of the results in the
# combined ring at the end -- Singular never sees the joint system.
#
# This is built here for the U0-pair (Fu_decoupled[1] vs [2]) and the
# U1-pair (Fu_decoupled[3] vs [4]) separately, matching how the
# construction loop above actually built Fu_decoupled (alternating
# sample-1/sample-2 per target variable U0, then U1).
################################################################################

println()
println("===========================================================")
