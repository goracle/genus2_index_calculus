#!/usr/bin/env julia

################################################################################
#
#  run_elim2.jl  --  driver for the elim2 package.
#
#  Lives in ~/crypto, as a sibling of the elim2/ package directory and of
#  everything elim2 depends on (phi_general/, part_j_worker.jl,
#  part_k_summand_worker.jl, tmp/, part_f_scratch/, part_k_results/).
#
#  Usage:
#      cd ~/crypto && julia run_elim2.jl
#      cd ~/crypto && julia -t 8 run_elim2.jl     # PART J/K use Threads.nthreads()
#
################################################################################

import Pkg
Pkg.activate(joinpath(@__DIR__, "elim2"))
Pkg.instantiate()   # only does real work the first time / after Project.toml changes

using elim2
