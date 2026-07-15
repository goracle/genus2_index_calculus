# elim2/

This is `elim2.jl` (previously a single 6669-line file in `~/crypto`) split
into pieces for maintainability, packaged as a subdirectory so it can sit
inside `~/crypto` alongside everything else without cluttering the top
level.

## Layout

```
~/crypto/
├── run_elim2.jl          <- driver script, run this
├── phi_general/           <- unchanged, still lives here
├── part_j_worker.jl       <- unchanged, still lives here
├── part_k_summand_worker.jl
├── tmp/                    <- created/used by PART J
├── part_f_scratch/         <- created/used by PART K
├── part_k_results/         <- created/used by PART K
├── Project.toml / Manifest.toml   <- unchanged
├── LP1ConjDeepDiag/, LP1ConjLSM/, PhiBiasTypes/, TrialConfig/  <- unchanged
├── ... (everything else already in ~/crypto, untouched)
│
└── elim2/                          <- NEW: this package
    ├── elim2.jl                    <- entry point, includes all parts below
    ├── README.md                   <- this file
    └── elim2_parts/
        ├── 00_MANIFEST.md          <- line-range map back to the original file
        ├── 01a_header_and_ring_map.jl
        ├── 01b_wdegree_diagnostic.jl
        ├── 01c_norm_elim_diag_prelude.jl
        ├── 02_part_a_static_diagnostics.jl
        ├── ... (PARTS B through K, see 00_MANIFEST.md)
        └── 14c_part_k_resultant_finalize.jl
```

## Why `elim2/` doesn't also hold `phi_general/`, the worker scripts, etc.

Those were never part of the file-size problem -- only `elim2.jl` itself
was 6669 lines. Moving `phi_general/`, `part_j_worker.jl`,
`part_k_summand_worker.jl`, `tmp/`, `part_f_scratch/`, and
`part_k_results/` into `elim2/` too would just relocate a working
directory layout for no benefit, and would break `part_j_worker.jl`'s own
independent `@__DIR__`-based lookup of `phi_general/` (it's spawned as a
subprocess by PART J and is not one of the split files). So they all stay
exactly where they are in `~/crypto`, and only the split-up `elim2.jl`
moves into its own subdirectory.

## How path resolution works

`elim2.jl` (and several of its parts) need to find `phi_general/`,
`part_j_worker.jl`, `tmp/`, `part_f_scratch/`, and `part_k_results/` --
all siblings of `elim2/` in `~/crypto`, not siblings of `elim2.jl` itself
anymore. That location is held in one constant, `ELIM2_ROOT_DIR`, set at
the top of `elim2/elim2.jl`:

```julia
if !@isdefined(ELIM2_ROOT_DIR)
    const ELIM2_ROOT_DIR = dirname(@__DIR__)   # elim2/.. == ~/crypto
end
```

This defaults correctly as long as you keep `elim2/` directly inside
`~/crypto`. If you ever move `elim2/` somewhere else relative to
`phi_general/` etc., define `ELIM2_ROOT_DIR` yourself in your driver
script *before* including `elim2/elim2.jl`, e.g.:

```julia
const ELIM2_ROOT_DIR = "/some/other/path/to/crypto"
include(joinpath(@__DIR__, "elim2", "elim2.jl"))
```

## Running it

From `~/crypto`:

```bash
julia run_elim2.jl
# or, to control thread count (PART J/K use Threads.nthreads()):
julia -t 8 run_elim2.jl
```

`run_elim2.jl` is a two-line driver that just does
`include(joinpath(@__DIR__, "elim2", "elim2.jl"))` -- see that file if you
want to override `ELIM2_ROOT_DIR` or add setup before the run.
