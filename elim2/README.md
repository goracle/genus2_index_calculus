# elim2

Julia package wrapping the (formerly 6669-line) `elim2.jl` monster
elimination script for genus-2 index calculus work. Split into parts
under `src/` for maintainability, loaded as `module elim2` so it can be
`using`'d instead of `include`'d as a bare script.

## Layout

```
~/crypto/
├── run_elim2.jl          <- driver script, run this
├── elim2/                 <- this package
│   ├── Project.toml
│   ├── README.md           <- this file
│   └── src/
│       ├── elim2.jl        <- module entry point, includes everything below
│       ├── 00_MANIFEST.md  <- line-range map back to the original single file
│       ├── 01a_header_and_ring_map.jl
│       ├── 01b_wdegree_diagnostic.jl
│       ├── 01c_norm_elim_diag_prelude.jl
│       ├── 02_part_a_static_diagnostics.jl
│       ├── ... (PARTS B through K, see 00_MANIFEST.md)
│       └── 14c_part_k_resultant_finalize.jl
├── phi_general/            <- unchanged, still a sibling of elim2/
├── part_j_worker.jl        <- unchanged
├── part_k_summand_worker.jl
├── tmp/, part_f_scratch/, part_k_results/   <- unchanged
└── ... (everything else already in ~/crypto)
```

## Why `phi_general/`, the worker scripts, and the scratch dirs aren't inside `elim2/`

They were never part of the size problem -- only `elim2.jl` itself was
6669 lines. Moving them into `elim2/` would just relocate a working
directory layout for no benefit, and would break `part_j_worker.jl`'s own
independent `@__DIR__`-based lookup of `phi_general/` (it's spawned as a
subprocess by PART J, not `include`d, so it isn't part of this package).
They all stay exactly where they are in `~/crypto`.

## How path resolution works

Several parts need to find `phi_general/`, `part_j_worker.jl`, `tmp/`,
`part_f_scratch/`, and `part_k_results/` -- all siblings of `elim2/` in
`~/crypto`, two directory levels up from `src/elim2.jl`. That location is
held in one constant, `ELIM2_ROOT_DIR`, set at the top of `src/elim2.jl`:

```julia
const ELIM2_ROOT_DIR = haskey(ENV, "ELIM2_ROOT_DIR") ?
    ENV["ELIM2_ROOT_DIR"] :
    dirname(dirname(@__DIR__))   # src/ -> elim2/ -> crypto/
```

This defaults correctly as long as the layout above holds -- `elim2/`
directly inside `~/crypto`, with `src/elim2.jl` two levels below
`~/crypto`. If you ever move things around, set the environment variable
`ELIM2_ROOT_DIR` before loading the package instead of editing the
source:

```bash
ELIM2_ROOT_DIR=/some/other/path/to/crypto julia run_elim2.jl
```

`ELIM2_ROOT_DIR` is a `const` set once at module load, so this env-var
override is the only way to change it without editing `src/elim2.jl`
directly.

## Running it

From `~/crypto`:

```bash
julia run_elim2.jl
# or, to control thread count (PART J/K use Threads.nthreads()):
julia -t 8 run_elim2.jl
```

`run_elim2.jl` activates the `elim2/` project environment, instantiates
it (installs `Oscar` etc. into that environment if not already present --
a no-op after the first run or whenever `Project.toml` hasn't changed),
and then `using elim2`, which triggers module load and runs the full
pipeline as a side effect (same behavior as the original script -- this
was never designed as a library with an explicit entry-point function,
it's a top-to-bottom research pipeline that runs on load).

## Note on `Project.toml`

Only `Oscar` is listed under `[deps]`. There's no `[compat]` section --
that's deliberate, so `Pkg` resolves against whatever Oscar version is
already usable in your environment rather than risking a version pin
that conflicts with what you have installed. If you later want to pin a
version, add it yourself:

```toml
[compat]
Oscar = "1.8"
```
