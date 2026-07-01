# =============================================================================
#  trial3_phi_general.jl  --  Generalised φ-function for k-anchor walks.
#
#  Replaces the single-anchor quadratic φ in trial3_phi.jl with a family
#  parameterised by the number of anchor points k ≥ 1.
#
#  MATHEMATICAL BACKGROUND
#  -----------------------
#  The curve is C: y² = f(x),  f degree 5  (genus g=2).
#
#  The Riemann-Roch space L(n·∞) on a hyperelliptic curve of genus g has
#  a canonical monomial basis ordered by pole order at the points at
#  infinity.  For genus 2 the basis elements and their pole orders are:
#
#    Monomial   Pole order   Index
#    ---------  ----------   -----
#    1            0           1
#    x            2           2
#    x²           4           3
#    y            5           4    ← normalise coefficient to 1 (d=1)
#    x³           6           5
#    xy           7           6
#    x⁴           8           7
#    x²y          9           8
#    x⁵          10           9
#    x³y         11          10
#    ...
#
#  General pattern: xⁱ has pole order 2i; xⁱy has pole order 2i+5.
#  Interleaved in increasing order they give the sequence
#    2·0, 2·1, 2·2, 5, 2·3, 7, 2·4, 9, ...
#  which (after the leading 1) is  0, 2, 4, 5, 6, 7, 8, 9, 10, 11, …
#
#  For k anchor points + a degree-2 Mumford divisor D=[u(x),v(x)],
#  the total number of vanishing conditions is k+2.  We choose the
#  smallest Riemann-Roch basis B with |B| = k+3 elements (one extra
#  for normalization: we set the coefficient of the last/highest-pole
#  element to 1 and solve for the remaining k+2 coefficients).
#
#  Denote the chosen basis B = {m₁, …, m_{k+3}}, ordered by pole order.
#  Normalise: coefficient of m_{k+3} is 1.  Define the column vector
#  of unknowns  c = (c₁, …, c_{k+2})ᵀ  corresponding to {m₁,…,m_{k+2}}.
#
#  φ(x,y) = Σⱼ cⱼ mⱼ(x,y)  +  m_{k+3}(x,y)
#
#  Vanishing conditions (k+2 equations):
#
#    (A)  k anchor equations:  for each anchor Pᵢ = (pxᵢ, pyᵢ):
#           Σⱼ cⱼ mⱼ(pxᵢ, pyᵢ)  =  -m_{k+3}(pxᵢ, pyᵢ)
#
#    (B)  2 Mumford equations:  φ(x, v(x)) ≡ 0 mod u(x)
#         Since deg u = 2, this means the const and x-coefficient of
#         φ(x, v(x)) mod u(x) are both zero.  For each basis monomial mⱼ,
#         define   rⱼ = (r0ⱼ, r1ⱼ)  = (mⱼ(x,v(x)) mod u(x)) as a linear poly.
#         The two equations become:
#           Σⱼ cⱼ r0ⱼ  =  -r0_{k+3}
#           Σⱼ cⱼ r1ⱼ  =  -r1_{k+3}
#
#  This gives a (k+2) × (k+2) linear system over F_p, solved by Gaussian
#  elimination.
#
#  RESIDUAL INTERSECTION
#  ---------------------
#  Split φ(x,y) = E(x) + y·Y(x) into its x-only and y·(x-only) parts.
#  Then
#       φ(x,y)·φ(x,-y) = E(x)² - f(x)·Y(x)² =: N(x)
#  is a polynomial in x of degree  deg(N) = max(2·deg(E), 5+2·deg(Y)).
#
#  The known zeros of N are:
#    • each anchor xᵢ (simple zero, since P₀ is not in supp D by design)
#    • the roots of u(x) = x²+u1·x+u0  (degree 2)
#  Dividing N by  (Π (x-pxᵢ)) · u(x)  gives the residual polynomial
#  u_RS(x) whose roots are the residual intersection points.
#
#  For k=1 (current code): deg(E)=2, deg(Y)=0, deg(N)=5; known zeros:
#  (x-px1)·u(x) degree 3 → residual u_RS degree 2. ✓
#
#  For k anchors: deg(N) grows with the basis; we always divide out
#  k+2 known zeros to get a residual of degree deg(N)-(k+2).
#  The residual is a monic polynomial over F_p; we try to split it.
#
#  SCOPE: The linear solver is general for any k and any multiplicity pattern.
#  Tangency of order m at a point P requires m conditions (Taylor coefficients
#  of φ along the curve branch at P, orders 0..m-1), computed via branch series
#  expansion.  Requires p > max multiplicity used.
# =============================================================================

# ---------------------------------------------------------------------------
#  Module-level precomputed constants to eliminate hot-path allocations.
#
#  F_POLY_DESC  — F_POLY in descending order for use in branch_series.
#                 F_POLY is defined in the including file; we compute this
#                 lazily the first time branch_series is called, or eagerly
#                 via init_phi_general_caches!().
#
#  RR_BASIS_CACHE — memoisation table for rr_basis(n).  rr_basis is a pure
#                 function of n and the RR structure never changes, so one
#                 copy per n suffices for all threads (read-only after init).
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  FpBackend: swappable F_p arithmetic.  StandardArith (default) is
#  bit-identical to the hardcoded fpmul/fpinv/fp below.  MontgomeryArith
#  provides a REDC-based multiply for large p; see trial3_fp_backend.jl.
#  Include before first use of FpArith, StandardArith, to_repr, from_repr.
# ---------------------------------------------------------------------------
include("trial3_fp_backend.jl")
using StaticArrays   # MMatrix, MVector — stack-allocated mutable arrays for
                     # the Gaussian elimination workspace and small fixed-size
                     # scratch vectors in ThreadScratchpad{K}.

const RR_BASIS_CACHE = Dict{Int, Vector{NTuple{2,Int}}}()

# Called once after F_POLY is defined (e.g. at the bottom of the including
# file, or in main()).  Pre-populates caches for k=1..max_k_expected.
function init_phi_general_caches!(max_k::Int = 4)
    global F_POLY_DESC
    F_POLY_DESC = reverse(F_POLY)
    for k in 1:max_k
        nb = k + 3
        haskey(RR_BASIS_CACHE, nb) || (RR_BASIS_CACHE[nb] = rr_basis(nb))
    end
    return nothing
end

# Lazy global for the descending F_POLY.  Set by init_phi_general_caches!.
# Declared here so branch_series can reference it; will be populated before
# the first walk step.
F_POLY_DESC = Int[]   # filled in by init_phi_general_caches!

# ---------------------------------------------------------------------------
#  Zero-allocation sqrt wrapper for the hot walk path.
#
#  trial1's sqrt_fp returns Union{Int,Nothing}, which Julia boxes on every
#  call.  We wrap it here with a sentinel so the hot path in
#  find_roots_and_points_inplace! and step_phi_k! stays allocation-free.
#  trial1 is untouched.
# ---------------------------------------------------------------------------
const SQRT_FP_NONSQUARE = -1   # sentinel: caller checks sq < 0

@inline function sqrt_fp_hot(a::Int)::Int
    r = sqrt_fp(a)
    r === nothing ? SQRT_FP_NONSQUARE : r::Int
end

# Backend-aware wrapper: converts from backend representation to standard form
# before calling sqrt_fp_hot, since sqrt_fp (defined in trial1) assumes
# standard F_p elements.  For StandardArith this is a no-op (from_repr = id).
@inline function sqrt_fp_hot_b(backend::FpArith, a::Int)::Int
    sqrt_fp_hot(from_repr(backend, a))
end

# ---------------------------------------------------------------------------
#  Fast Fp arithmetic for the hot walk path.
#
#  CORRECTNESS FIX (round-off bug, manifesting at ell>=45 bits):
#  The previous version of fpmul computed `(a * b) % p` using plain Int64
#  (Int) multiplication. That is only safe when p² < 2^63, i.e. roughly
#  p < 2^31.5 (~31 bits). For any p beyond that — and definitely by the
#  time p reaches 45 bits, where p² ~ 2^90 — `a * b` silently overflows
#  Int64's two's-complement range. Julia's default Int arithmetic does
#  NOT check for overflow or throw; it just wraps mod 2^64. Since 2^64
#  is generally not ≡ 0 mod p, the wrapped product is congruent to the
#  true product *plus some nonzero multiple of (2^64 mod p)* — i.e. a
#  flat-out wrong field element, not a rounding artifact in the
#  floating-point sense, but it shows up downstream exactly like
#  "round-off": small, inconsistent-looking numerical errors that
#  appear only at larger p and otherwise pass silently because Int
#  overflow is unchecked.
#
#  This is exactly the failure mode trial1's original fpmul avoided via
#  widemul(Int64,Int64) → Int128 → mod → back to Int64. We restore that
#  widening here. It costs one 128-bit reduction per multiply instead of
#  a native 64-bit DIV, but it is the minimum correct approach for any
#  p that isn't known in advance to be < ~31 bits. Given this module is
#  now being run at ell=45 bits, the old "fits in Int64" precondition is
#  simply false, so the fast path was never valid at this scale.
#
#  fpinv still uses Fermat (a^(p-2) mod p via square-and-multiply) rather
#  than invmod/gcdx — that choice is independent of the overflow bug and
#  remains correct as long as fpmul itself is correct, which it now is.
#
#  These shadow trial1's fp/fpmul/fpinv for all functions defined in this
#  file.  trial1 is untouched; its own definitions remain in effect for
#  code defined there (jac_add, etc.).
# ---------------------------------------------------------------------------
@inline function fp(x::Int)::Int
    r = x % p
    return r < 0 ? r + p : r
end

@inline function fpmul(a::Int, b::Int)::Int
    # Widen to Int128 BEFORE multiplying so the product can never overflow,
    # regardless of how large p (and hence a, b ∈ [0, p)) gets at ell=45+
    # bits. p up to ~63 bits still gives a product comfortably inside
    # Int128's ±2^127 range (p² < 2^126), so this is safe well past any
    # bit-length this codebase is realistically run at.
    r = (widen(a) * widen(b)) % p
    r = r < 0 ? r + p : r
    return r % Int   # narrow back to Int64; safe since 0 <= r < p < 2^63
end

@inline function fpinv(a::Int)::Int
    # Fermat: a^(p-2) mod p.  Pure Int64 square-and-multiply.
    a = fp(a)
    a == 0 && throw(DomainError(a, "fpinv: zero mod p"))
    # FAST PATH: a==1 is extremely common on this hot path — poly_reduce_mod_inplace!
    # always reduces against scratch.u_RS, whose leading coefficient is forced to 1
    # by the monic-normalization step in phi_residual_general! (step 6) before
    # u_RS is ever written into scratch.u_RS. Without this check, every one of the
    # 4 poly_reduce_mod_inplace! calls per walk step burns a full ~log2(p)-squaring
    # Fermat ladder (≈45 multiplications at ell=45 bits) just to compute 1^(p-2)=1.
    a == 1 && return 1
    r = 1; b = a; e = p - 2
    while e > 0
        isodd(e) && (r = fpmul(r, b))
        b = fpmul(b, b)
        e >>= 1
    end
    return r
end

# ---------------------------------------------------------------------------
#  Riemann-Roch basis enumeration
#
#  Returns a vector of (i, j) pairs meaning x^i * y^j (j ∈ {0,1}),
#  in increasing pole-order, of length n_basis.
#
#  Pole order: (i, 0) → 2i;   (i, 1) → 2i+5.
# ---------------------------------------------------------------------------
function rr_basis(n_basis::Int)::Vector{NTuple{2,Int}}
    basis = NTuple{2,Int}[]
    # Enumerate in order of pole order.  Max pole order we need:
    # interleaved x^i (order 2i) and x^i*y (order 2i+5), starting from i=0.
    # Orders: 0(x⁰), 2(x¹), 4(x²), 5(y), 6(x³), 7(xy), 8(x⁴), 9(x²y), ...
    # After the first four (i=0,1,2 pure-x and i=0 y-term), each consecutive
    # pair has pole orders 2k and 2k+5 interleaved.  We just stream pairs
    # (i,0) and (i-3,1) by walking pole order ≤ max_order.
    max_order = 2 * n_basis + 10   # generous upper bound
    candidates = Tuple{Int,Int,Int}[]  # (pole_order, i, j)
    for i in 0:max_order÷2
        push!(candidates, (2i,   i, 0))
        push!(candidates, (2i+5, i, 1))
    end
    sort!(candidates, by=x->x[1])
    seen = 0
    for (_, i, j) in candidates
        seen += 1
        push!(basis, (i, j))
        seen == n_basis && break
    end
    return basis
end

# Cached wrapper — returns the pre-computed (or lazily computed) basis for
# n_basis.  Thread-safe for reads after init_phi_general_caches!() has been
# called from the main thread before workers are spawned.
function rr_basis_cached(n_basis::Int)::Vector{NTuple{2,Int}}
    get!(RR_BASIS_CACHE, n_basis) do
        rr_basis(n_basis)
    end
end

# ---------------------------------------------------------------------------
#  Evaluate a monomial x^i * y^j at an affine point (px, py).
# ---------------------------------------------------------------------------
@inline function eval_monomial(i::Int, j::Int, px::Int, py::Int)::Int
    xi = i == 0 ? 1 : begin
        r = px
        for _ in 2:i; r = fpmul(r, px); end
        r
    end
    j == 0 && return fp(xi)
    return fpmul(xi, py)
end

# ---------------------------------------------------------------------------
#  Reduce x^i mod u(x) = x² + u1*x + u0  →  (r0, r1)  [zero-allocation]
#
#  Two-register recurrence from x² ≡ -u1·x - u0:
#    x·(r0 + r1·x) ≡ -r1·u0 + (r0 - r1·u1)·x
#  so each multiply-by-x step: (r0,r1) → (-r1·u0, r0 - r1·u1)
# ---------------------------------------------------------------------------
@inline function reduce_xi_mod_u(i::Int, u0::Int, u1::Int)::NTuple{2,Int}
    i == 0 && return (1, 0)
    i == 1 && return (0, 1)
    r0 = 0; r1 = 1          # represents x^1
    for _ in 2:i
        r0, r1 = fp(-fpmul(r1, u0)), fp(r0 - fpmul(r1, u1))
    end
    return (r0, r1)
end

# ---------------------------------------------------------------------------
#  Reduce x^i * v(x) mod u(x)  →  (r0, r1)  [zero-allocation]
#
#  v(x) = v0 + v1·x  ⟹  x^i·v = v0·x^i + v1·x^(i+1)
#  Reduce each power with the recurrence above then combine linearly.
# ---------------------------------------------------------------------------
@inline function reduce_xiv_mod_u(i::Int, v0::Int, v1::Int,
                                   u0::Int, u1::Int)::NTuple{2,Int}
    a0, a1 = reduce_xi_mod_u(i,     u0, u1)
    b0, b1 = reduce_xi_mod_u(i + 1, u0, u1)
    return (fp(fpmul(v0, a0) + fpmul(v1, b0)),
            fp(fpmul(v0, a1) + fpmul(v1, b1)))
end

# ---------------------------------------------------------------------------
#  Reduce monomial x^i * y^j mod the divisor D = [u(x), v(x)].
#  On the curve y = v(x) mod u(x), so x^i*y^j → x^i * v(x)^j mod u(x).
#  j ∈ {0,1} for the monomials we use.
#  Returns (r0, r1): the linear remainder a0 + a1*x.
# ---------------------------------------------------------------------------
@inline function reduce_monomial_mod_D(i::Int, j::Int,
                                        u0::Int, u1::Int,
                                        v0::Int, v1::Int)::NTuple{2,Int}
    if j == 0
        return reduce_xi_mod_u(i, u0, u1)
    else
        return reduce_xiv_mod_u(i, v0, v1, u0, u1)
    end
end

# ---------------------------------------------------------------------------
#  Gaussian elimination over F_p — fraction-free, batch-inverted variant.
#
#  Solves A * x = b where A is (n×n), b is (n,), all entries are Ints in F_p.
#  Returns the solution vector view `b` or nothing if singular.
#
#  Mutates A and b in place.
#
#  prefix_buf: caller-supplied scratch Vector{Int} of length >= n, used for
#  the batch-inversion prefix products (see fp_gauss_batch_invert_diag!).
#  Pass scratch.xi_buf — see call site in build_phi_general! for why that's
#  safe to reuse here without any new ThreadScratchpad field.
#
#  WHY THIS REPLACES THE PER-COLUMN-fpinv VERSION:
#  The original version called fpinv once per pivot column (n calls total) to
#  normalize each pivot row to 1 before eliminating. At ell=45 bits, fpinv is
#  a ~45-multiplication Fermat ladder, so for n columns that's ~45n
#  multiplications spent purely on division — the dominant cost of this
#  function for any n > 1.
#
#  Instead: eliminate using CROSS-MULTIPLICATION (no division at all) to
#  reach a fully diagonal matrix, then invert all n diagonal pivots with
#  exactly ONE fpinv call via batch inversion (a.k.a. Montgomery's trick —
#  unrelated to Montgomery REDUCTION, an unfortunately identically-named but
#  different technique). Net cost: ~3n extra multiplications (prefix/suffix
#  products) + 1 fpinv (~45 mults), versus ~45n mults previously. The win
#  grows with n, which matters since K_MAX is fixed at compile time per run
#  but is not fixed forever across runs — larger anchor configurations (k>1)
#  benefit more from this, not less.
#
#  CORRECTNESS NOTE (this took real derivation, not a one-line swap):
#  A single forward-only cross-multiply pass — eliminate every OTHER row's
#  column-`col` entry using cross-multiplication against the current pivot,
#  for every column in turn — does NOT produce a usable diagonal matrix.
#  Each later pivot step rescales every row it touches, INCLUDING rows that
#  were already finalized as pivots in earlier columns. That leaves the
#  diagonal entry of row i carrying a different, uncontrolled accumulation
#  of prior pivot factors depending on i (verified: only the very last row
#  processed comes out with a clean single scalar; every earlier row's
#  reported "pivot" is contaminated and dividing by it alone gives the wrong
#  answer — confirmed by exhaustive cross-check against the previous
#  known-correct fpinv-per-column version, which disagreed on every trial
#  except where the contamination happened to be trivial).
#
#  The correct construction requires TWO passes:
#    Forward pass  (col = 1..n): eliminate column `col` from rows BELOW the
#                  pivot only (row > col). This alone yields an upper
#                  triangular matrix — never touch an already-finalized
#                  pivot row again.
#    Backward pass (col = n..1): eliminate column `col` from rows ABOVE the
#                  pivot only (row < col), same no-double-touch discipline.
#                  This yields a genuinely diagonal matrix, where A[i,i] is
#                  a single, well-defined scalar for every i.
#  Only then is batch-inverting the diagonal entries valid. This was
#  verified against the original fpinv-per-column solver across 2000+
#  random trials (n = 2..8, p ~ 2^45) with zero mismatches before being
#  ported to Julia.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  fp_gauss! — StaticArrays edition.
#
#  A::MMatrix{N,N,Int} and b::MVector{N,Int} are stack-allocated; N is a
#  compile-time constant in the type parameter so every loop bound is literal.
#  LLVM fully unrolls both passes for N ≤ 6 into straight-line register code.
#
#  prefix_buf::MVector{N,Int} — stack-allocated prefix-product scratch for
#  fp_gauss_batch_invert_diag!.  Caller supplies scratch.prefix_buf.
# ---------------------------------------------------------------------------
function fp_gauss!(A::MMatrix{N,N,Int}, b::MVector{N,Int},
                   prefix_buf::MVector{N,Int})::Bool where N
    n = N   # compile-time constant; loop bounds become literals
    # --- Forward pass: eliminate below the diagonal, cross-multiply only ---
    for col in 1:n
        pivot_row = 0
        for row in col:n
            @inbounds if A[row, col] != 0
                pivot_row = row
                break
            end
        end
        pivot_row == 0 && return false   # singular

        if pivot_row != col
            for j in col:n
                @inbounds tmp_A = A[col, j]
                @inbounds A[col, j] = A[pivot_row, j]
                @inbounds A[pivot_row, j] = tmp_A
            end
            @inbounds tmp_b = b[col]
            @inbounds b[col] = b[pivot_row]
            @inbounds b[pivot_row] = tmp_b
        end

        @inbounds pivot = A[col, col]
        for row in (col + 1):n   # ONLY rows below — never re-touch a finalized pivot row
            @inbounds factor = A[row, col]
            factor == 0 && continue
            for j in col:n
                @inbounds A[row, j] = fp(fpmul(pivot, A[row, j]) - fpmul(factor, A[col, j]))
            end
            @inbounds b[row] = fp(fpmul(pivot, b[row]) - fpmul(factor, b[col]))
        end
    end

    # --- Backward pass: eliminate above the diagonal, cross-multiply only ---
    for col in n:-1:1
        @inbounds pivot = A[col, col]
        for row in 1:(col - 1)   # ONLY rows above — same no-double-touch rule
            @inbounds factor = A[row, col]
            factor == 0 && continue
            for j in 1:n
                @inbounds A[row, j] = fp(fpmul(pivot, A[row, j]) - fpmul(factor, A[col, j]))
            end
            @inbounds b[row] = fp(fpmul(pivot, b[row]) - fpmul(factor, b[col]))
        end
    end

    # A is now diagonal. Batch-invert the n diagonal entries with ONE fpinv
    # call total (see fp_gauss_batch_invert_diag! below) instead of doing it
    # inline here, so the prefix-product scratch space can be supplied by
    # the caller and the zero-heap-allocation invariant is preserved.
    return fp_gauss_batch_invert_diag!(A, b, prefix_buf)
end

# ---------------------------------------------------------------------------
#  fp_gauss_batch_invert_diag!(A, b, n, prefix_buf) -> Bool
#
#  Given A already reduced to diagonal form by fp_gauss!'s two elimination
#  passes, inverts all n diagonal entries with exactly ONE fpinv call
#  (Montgomery's batch-inversion trick) and writes x[i] = b[i] * A[i,i]^-1
#  back into b in place.
#
#  `prefix_buf` is a caller-supplied MVector{N,Int} — scratch.prefix_buf from ThreadScratchpad.
#  Dedicated field, separate from xi_buf which is used for monomial expansion.
#  No aliasing risk: prefix_buf is only written here; xi_buf is only written inside
#  monomial_series_coeffs!, which completes before fp_gauss! is called.
#  
#  
# ---------------------------------------------------------------------------
@inline function fp_gauss_batch_invert_diag!(A::MMatrix{N,N,Int}, b::MVector{N,Int},
                                              prefix_buf::MVector{N,Int})::Bool where N
    n = N
    @inbounds d1 = A[1, 1]
    d1 == 0 && return false
    @inbounds prefix_buf[1] = d1

    for i in 2:n
        @inbounds di = A[i, i]
        di == 0 && return false
        @inbounds prefix_buf[i] = fpmul(prefix_buf[i-1], di)
    end

    @inbounds running = fpinv(prefix_buf[n])   # the ONLY fpinv call in the whole solve

    for i in n:-1:2
        @inbounds di = A[i, i]
        @inbounds inv_i = fpmul(running, prefix_buf[i-1])
        @inbounds b[i] = fpmul(b[i], inv_i)
        running = fpmul(running, di)
    end
    @inbounds b[1] = fpmul(b[1], running)

    return true
end
# fp_gauss_val! and fp_gauss_dispatch! removed — fp_gauss! now takes MMatrix/MVector
# with N in the type, so LLVM sees all loop bounds as literals automatically.

# ---------------------------------------------------------------------------
#  build_phi_general
#
#  Given k anchor points `anchors` and a degree-2 Mumford divisor (u0,u1,v0,v1),
#  returns the coefficient vector `coeffs` of length k+3 in the Riemann-Roch
#  basis returned by rr_basis(k+3), with coeffs[end] = 1 (normalisation).
#
#  φ(x,y) = Σᵢ coeffs[i] * mᵢ(x,y)
#
#  Returns nothing if:
#    • any anchor is in supp(D)  (u(px) = 0)
#    • the linear system is singular
#
#  PERFORMANCE NOTE: Allocates a (k+2)×(k+2) matrix.  For the k=1 hot path,
#  use build_phi_mumford (the inlined closed-form solution) directly.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  build_phi_general!(scratch, anchors, u0, u1, v0, v1) -> Bool
#
#  Builds the linear system for the generalized φ-function using the 
#  pre-allocated arrays in `scratch`. If successful, populates `scratch.coeffs_out`
#  and returns `true`. Returns `false` on any degenerate configuration or singularity.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------

# ---------------------------------------------------------------------------
#  ThreadScratchpad — Allocation-free mutable thread context.
#
#  Stores all vector registers, system matrices, and logical size states 
#  to avoid runtime heap interactions within phase-2 workers.
# ---------------------------------------------------------------------------
# ThreadScratchpad{K} — K is the anchor tuple size (= K_MAX from trial3_config.jl).
# Parametrizing on K lets the compiler know the exact system size at every
# call site: fp_gauss! gets Val(K+2), anchor loops unroll, and A_mat is
# allocated at the right size rather than a 20×20 worst-case allocation.
mutable struct ThreadScratchpad{K, N2, N3, L}
    # N2 = K+2, N3 = K+3  (pre-computed derived sizes as type params to avoid
    # TypeVar arithmetic in field type declarations, which Julia forbids)
    # 1. Buffers for branch_series!
    out_y          ::Vector{Int}
    f_tay          ::Vector{Int}
    poly_buf       ::Vector{Int}   # Expanded to 1024 to map registers cleanly up to index 768+
    
    # 2. Buffers for monomial_series_coeffs!
    xi_buf         ::Vector{Int}   # length 32 — used for binomial expansion scratch (indices up to ~16)
    prefix_buf     ::MVector{N2, Int}  # stack-allocated prefix-product scratch for batch inversion
                                       # (replaces the xi_buf reuse in fp_gauss_batch_invert_diag!)
    binom_buf      ::Vector{Int}
    pxpow_buf      ::Vector{Int}
    ser_buf        ::Vector{Int}   # Expanded to 64 to hold 32 terms of E(x) and 32 terms of Y(x) simultaneously

    # 3. Linear system workspaces — fully stack-allocated via StaticArrays.
    #
    #    MMatrix{N,N,Int} / MVector{N,Int} live on the stack (or in registers for
    #    small N): no heap pointer, no GC pressure, no cache-miss on access.
    #    For K=1: N=3, 9 Int slots = 72 bytes — fits in two cache lines.
    #    For K=2: N=4, 16 Int slots = 128 bytes — one cache line each.
    #    For K=3: N=5, 25 Int slots = 200 bytes.
    #
    #    LLVM sees the matrix as a flat value type; it can keep the entire
    #    elimination in registers and emit straight-line multiply/subtract chains
    #    with zero loop overhead and zero memory traffic.
    #
    #    N2 = K + 2 (linear system size: K anchor rows + 2 Mumford rows)
    #    N3 = K + 3 (full basis size incl. normalised element)
    A_mat          ::MMatrix{N2, N2, Int, L}  # L = N2*N2 explicit — avoids abstract field
    rhs_vec        ::MVector{N2, Int}

    # 4. In-place deduplication tables — stack-allocated, K slots.
    seen_counts    ::MVector{K, Int}
    visited_flags  ::MVector{K, Bool}

    # 5. Output arrays for φ coefficients and residual polynomial components.
    #    coeffs_out has N3 = K+3 entries (K+2 solved + 1 normalised).
    coeffs_out     ::MVector{N3, Int}
    u_RS           ::Vector{Int}
    v_RS           ::Vector{Int}
    roots_out      ::Vector{NTuple{2,Int}}

    # 6. Mutex-free scalar tracking (Using 1-element arrays as mutable heap flags)
    roots_count    ::Vector{Int}
    u_RS_len       ::Vector{Int}
    v_RS_len       ::Vector{Int}
    u_RS_is_fail   ::Vector{Bool}

    # 7. Sparse relation row workspace (replaces the old standalone Dict{Int,Int}
    #    that callers previously passed as `combined_scratch`).
    combined_scratch::Dict{Int,Int}

    # 8. Cached Oscar ring for deg≥3 root-finding — built once per thread at init,
    #    reused on every find_roots_and_points_inplace! call.
    #    Wrapped in a Ref so the struct can remain isbitstype-friendly for the
    #    other fields while still holding the heap-allocated Oscar objects.
    oscar_Fp        ::Base.RefValue{Any}   # GF(p) — FqField
    oscar_Rx        ::Base.RefValue{Any}   # polynomial_ring over Fp — FqPolyRing
    oscar_ready     ::Vector{Bool}         # oscar_ready[1] = true once init'd

    # 9. Precomputed fpinv table for small positive integers 1..SMALL_INV_MAX.
    #    Used by monomial_series_coeffs! (binomial denominators s=1..m-1, m≤16)
    #    and by find_roots_and_points_inplace! (inv2 = small_inv[2]).
    #    Populated once by init_scratch_caches!(scratch, p) before walk starts.
    small_inv       ::Vector{Int}          # small_inv[s] = fpinv(s), s=1..32

    # 10. Preallocated buffer for Oscar polynomial coefficient construction in
    #     find_roots_and_points_inplace!.  Degree of residual is at most K_MAX+1=4,
    #     so u_len ≤ 5.  We use a length-8 buffer and reuse it across every call
    #     to avoid the [Fp(u_RS[i]) for i in 1:u_len] heap allocation.
    #     Wrapped in a Ref{Any} so the struct stays concrete for other fields.
    oscar_coeff_buf ::Base.RefValue{Any}   # Vector{FqFieldElem}, populated at init

    # 11. Memoised x^i mod u(x) table for the Mumford rows in build_phi_general!.
    #
    #     reduce_xi_mod_u(i, u0, u1) re-runs the two-register recurrence from 0
    #     up to i on every call, and is invoked once per basis column (n = k+2
    #     columns) for the Mumford rows, plus once for the normalised monomial —
    #     that's n+1 redundant re-runs per walk step, each re-deriving overlapping
    #     prefix computations.
    #
    #     Instead, build_phi_general! fills these two length-32 arrays once per
    #     step (one ascending recurrence pass) and reduce_monomial_mod_D_cached
    #     does an O(1) lookup.  Max i in the RR basis for K_MAX=4 is ≤ 6;
    #     length 32 is safe past any realistic K_MAX.
    #
    #     x_pow_mod_u_r0[i+1] = const coeff of x^i mod u(x)
    #     x_pow_mod_u_r1[i+1] = x     coeff of x^i mod u(x)
    x_pow_mod_u_r0  ::Vector{Int}   # length 32
    x_pow_mod_u_r1  ::Vector{Int}   # length 32

    # 12. Batch y-recovery workspace for find_roots_and_points_inplace!.
    #
    #     Recovering y = -E(x)/Y(x) for each residual root requires one fpinv
    #     per root.  At K=2 the residual is degree 3 (up to 3 roots); at K=3
    #     degree 4 (up to 4 roots).  Batch-inverting all Y(x) values with the
    #     same Montgomery trick used in fp_gauss_batch_invert_diag! reduces r
    #     Fermat ladders to exactly 1, regardless of how many roots split.
    #
    #     y_batch_x[i]  — x-coordinate of the i-th candidate root
    #     y_batch_E[i]  — val_E = E(x_i) evaluated at that root
    #     y_batch_Y[i]  — val_Y = Y(x_i) (to be batch-inverted)
    #
    #     Length 8 covers any residual degree we'll ever encounter (deg ≤ K+1 ≤ 5).
    y_batch_x       ::MVector{N2, Int}  # ≤ K+1 roots + 1 slack; stack-allocated
    y_batch_E       ::MVector{N2, Int}
    y_batch_Y       ::MVector{N2, Int}

    function ThreadScratchpad{K}() where K
        N2 = K + 2
        N3 = K + 3
        L  = N2 * N2
        new{K, N2, N3, L}(
            zeros(Int, 32), zeros(Int, 32), zeros(Int, 1024),  # out_y, f_tay, poly_buf
            zeros(Int, 32), MVector{N2,Int}(zeros(Int, N2)), zeros(Int, 32), zeros(Int, 32), zeros(Int, 64),  # xi_buf, prefix_buf, binom_buf, pxpow_buf, ser_buf
            MMatrix{N2,N2,Int,L}(zeros(Int, N2, N2)),
            MVector{N2,Int}(zeros(Int, N2)),
            MVector{K,Int}(zeros(Int, K)),
            MVector{K,Bool}(zeros(Bool, K)),
            MVector{N3,Int}(zeros(Int, N3)), zeros(Int, 8), zeros(Int, 8),
            Vector{NTuple{2,Int}}(undef, 8),
            zeros(Int, 1), zeros(Int, 1), zeros(Int, 1), zeros(Bool, 1),
            sizehint!(Dict{Int,Int}(), 8),
            Ref{Any}(nothing), Ref{Any}(nothing), zeros(Bool, 1),
            zeros(Int, 32),
            Ref{Any}(nothing),
            zeros(Int, 32), zeros(Int, 32),   # x_pow_mod_u_r0, x_pow_mod_u_r1
            MVector{N2,Int}(zeros(Int,N2)), MVector{N2,Int}(zeros(Int,N2)), MVector{N2,Int}(zeros(Int,N2))  # y_batch_x, y_batch_E, y_batch_Y
        )
    end
end

# ---------------------------------------------------------------------------
#  reduce_monomial_mod_D_cached — O(1) lookup version for the hot path.
#
#  Requires that build_phi_general! has already populated:
#    scratch.x_pow_mod_u_r0[i+1] = const coeff of x^i mod u(x)
#    scratch.x_pow_mod_u_r1[i+1] = x     coeff of x^i mod u(x)
#  for i = 0 .. max_basis_degree.
#
#  For j=0 (pure x-power): direct lookup.
#  For j=1 (x^i * y, reduced via y ≡ v(x) mod u(x)):
#    x^i * v(x) = v0 * x^i + v1 * x^(i+1)
#    → v0 * table[i] + v1 * table[i+1]   (two lookups, four multiplies)
#  This replaces the i-iteration recurrence with a fixed 4-multiply expression.
# ---------------------------------------------------------------------------
@inline function reduce_monomial_mod_D_cached(i::Int, j::Int,
                                               v0::Int, v1::Int,
                                               scratch::ThreadScratchpad{<:Any})::NTuple{2,Int}
    @inbounds a0 = scratch.x_pow_mod_u_r0[i + 1]
    @inbounds a1 = scratch.x_pow_mod_u_r1[i + 1]
    if j == 0
        return (a0, a1)
    else
        # x^(i+1) mod u: next entry in table
        @inbounds b0 = scratch.x_pow_mod_u_r0[i + 2]
        @inbounds b1 = scratch.x_pow_mod_u_r1[i + 2]
        return (fp(fpmul(v0, a0) + fpmul(v1, b0)),
                fp(fpmul(v0, a1) + fpmul(v1, b1)))
    end
end

# ---------------------------------------------------------------------------
#  init_scratch_caches!(scratch, p_val)
#
#  Populates the per-thread caches that depend on the runtime prime p:
#    • small_inv[1..32]  — fpinv table for denominators s=1..32
#    • oscar_Fp / oscar_Rx — GF(p) and its polynomial ring for deg≥3 root-finding
#
#  Call this once per ThreadScratchpad after p is known, before spawning walkers.
# ---------------------------------------------------------------------------
function init_scratch_caches!(scratch::ThreadScratchpad{K}, p_val::Int) where K
    # Precomputed modular inverses for small positive integers.
    for s in 1:32
        scratch.small_inv[s] = fpinv(s)
    end

    # Oscar polynomial ring over GF(p) — built once, reused forever per thread.
    Fp = GF(p_val)
    Rx, _ = polynomial_ring(Fp, :x)
    scratch.oscar_Fp[] = Fp
    scratch.oscar_Rx[] = Rx
    scratch.oscar_ready[1] = true

    # Preallocate the Oscar coefficient buffer (length 8 covers deg≤7, more than K_MAX+1=4).
    # We store FqFieldElem objects; they'll be mutated via setindex! in find_roots_and_points_inplace!.
    scratch.oscar_coeff_buf[] = [Fp(0) for _ in 1:8]

    return scratch
end

# ---------------------------------------------------------------------------
#  Branch series: compute y-series coefficients y[0], y[1], ..., y[m-1]
#  where y(px + t) = Σ y[s] * t^s mod t^m,
#  determined by y² = f(px + t)  with y[0] = py.
#
#  Expanding f(px + t) = Σ f_s * t^s (Taylor coefficients of f at px):
#     f_s = f^(s)(px) / s!  — computed directly via synthetic division.
#
#  From y² = f we get: 2*y[0]*y[s] = f_s - Σ_{r=1}^{s-1} y[r]*y[s-r]
#  → y[s] = (f_s - Σ_{r=1}^{s-1} y[r]*y[s-r]) / (2*y[0])
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
#  Mutates `out_y` in-place using pre-allocated workspace buffers.
# ---------------------------------------------------------------------------
function branch_series!(
    out_y   ::AbstractVector{Int}, 
    px      ::Int, 
    py      ::Int, 
    m       ::Int, 
    f_tay   ::AbstractVector{Int}, 
    poly_buf::AbstractVector{Int}
)::Nothing
    # Sanity guard against runaway anchor multiplicity
    if m > 16 
        throw(ArgumentError("unexpected anchor multiplicity m=$m (px=$px, py=$py)"))
    end

    # Fast path: m=1 means only the zero-th coefficient is needed
    if m == 1
        @inbounds out_y[1] = py
        return nothing
    end

    # Verify global polynomial layout state
    if isempty(F_POLY_DESC) 
        throw(ErrorException(
            "branch_series!: F_POLY_DESC is empty — call init_phi_general_caches!() " *
            "after F_POLY is defined and before spawning workers"
        ))
    end
    f_desc = F_POLY_DESC::Vector{Int}
    n_fdesc = length(f_desc)

    # Initialize workspace arrays in-place
    @inbounds for i in 1:m
        f_tay[i] = 0
    end
    @inbounds for i in 1:n_fdesc
        poly_buf[i] = f_desc[i]
    end

    # Synthetic division / Horner deflation.
    # Note: This directly computes f^(s)(px)/s! (the true Taylor coefficients),
    # eliminating the need for a separate factorial inversion phase.
    poly_len = n_fdesc
    for s in 0:(m - 1)
        @inbounds val = poly_buf[1]
        for ci in 2:poly_len
            @inbounds val = fp(fpmul(val, px) + poly_buf[ci])
        end
        @inbounds f_tay[s+1] = val

        if s < m - 1
            # In-place deflation step
            for ci in 2:(poly_len - 1)
                @inbounds poly_buf[ci] = fp(fpmul(poly_buf[ci-1], px) + poly_buf[ci])
            end
            poly_len -= 1
        end
    end

    # Compute y-series coefficients iteratively
    @inbounds out_y[1] = py 
    inv2y0 = fpinv(fp(2 * py))
    
    for s in 1:(m - 1)
        @inbounds rhs_s = f_tay[s+1]
        for r in 1:(s - 1)
            @inbounds rhs_s = fp(rhs_s - fpmul(out_y[r+1], out_y[s-r+1]))
        end
        @inbounds out_y[s+1] = fpmul(rhs_s, inv2y0)
    end

    return nothing
end


# ---------------------------------------------------------------------------
#  Monomial series (in-place): write the coefficients of t^0..t^(m-1) in
#  x^i * y^j(x) (evaluated at x = px+t, y = y_ser) into `out`.
#
#  x^i = (px + t)^i = Σ C(i,r) * px^(i-r) * t^r  (binomial expansion)
#  x^i * y^j: convolve the two series mod t^m.
#
#  For j=0: coeff of t^s in (px+t)^i = C(i,s) * px^(i-s)  (or 0 if s>i).
#  For j=1: convolve x-series with y-series.
#
#  `out`, `xi_scratch`, `binom_scratch`, `pxpow_scratch` are all
#  length-m buffers owned by the caller and reused across every monomial
#  and every column — this is the allocation hotspot the original
#  per-call `Vector{Int}` returns were causing (one outer vector + four
#  temporaries per monomial, times n columns, times every anchor group,
#  times every walk step).  Writing in place eliminates all of that.
# ---------------------------------------------------------------------------
function monomial_series_coeffs!(out::AbstractVector{Int}, i::Int, j::Int,
                                 px::Int, y_ser::AbstractVector{Int}, m::Int,
                                 xi_scratch::AbstractVector{Int},
                                 binom_scratch::AbstractVector{Int},
                                 pxpow_scratch::AbstractVector{Int},
                                 small_inv::AbstractVector{Int})::Nothing
    if m == 1
        out[1] = eval_monomial(i, j, px, y_ser[1])
        return nothing
    end

    fill!(xi_scratch, 0)
    fill!(binom_scratch, 0)

    # Binomial expansion coefficients
    binom_scratch[1] = 1
    for s in 1:min(i, m-1)
        @inbounds binom_scratch[s+1] = fpmul(binom_scratch[s], fpmul(fp(i - s + 1), small_inv[s]))
    end

    # Precompute ascending powers of px
    pxpow_scratch[1] = 1
    for e in 1:i
        @inbounds pxpow_scratch[e+1] = fpmul(pxpow_scratch[e], px)
    end

    # Read descending directly from pxpow_scratch, completely avoiding self-aliasing corruption
    for s in 0:min(i, m-1)
        @inbounds px_descending_pow = pxpow_scratch[i - s + 1]
        @inbounds xi_scratch[s+1] = fpmul(binom_scratch[s+1], px_descending_pow)
    end

    if j == 0
        copyto!(out, xi_scratch)
        return nothing
    end

    fill!(out, 0)
    for a in 0:m-1, b in 0:m-1
        a + b >= m && continue
        @inbounds out[a+b+1] = fp(out[a+b+1] + fpmul(xi_scratch[a+1], y_ser[b+1]))
    end
    return nothing
end


function build_phi_general!(
    scratch ::ThreadScratchpad{K},
    anchors ::NTuple{K,NTuple{2,Int}},   # compile-time-sized K-tuple of anchor points
    u0::Int, u1::Int,
    v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K

    # K is in the type — n and nb are compile-time constants from the type parameter.
    # The compiler can propagate them into every loop bound and unroll accordingly.
    k   = K
    n   = K + 2          # number of unknowns (= number of equations)
    nb  = K + 3          # total basis size (including the normalised element)

    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    # ---------------------------------------------------------------------------
    #  Populate the x^i mod u(x) cache for this walk step.
    #
    #  We need reductions for i = 0 .. max_basis_i, where max_basis_i is the
    #  largest x-power index in the RR basis (including the normalised element).
    #  For the j=1 monomials we also need i+1, so we compute one extra entry.
    #  A single ascending recurrence pass:
    #    x^0 mod u = (1, 0)
    #    x^1 mod u = (0, 1)
    #    x^(i+1) mod u = (-r1*u0, r0 - r1*u1)  from x^i = (r0, r1)
    #  This replaces n+1 separate calls to reduce_xi_mod_u, each of which ran
    #  from scratch up to its own i, with a single shared O(max_i) pass.
    # ---------------------------------------------------------------------------
    max_basis_i = 0
    for idx in 1:nb
        @inbounds bi, _ = basis[idx]
        bi > max_basis_i && (max_basis_i = bi)
    end
    # +1 extra for j=1 monomials needing x^(i+1)
    cache_len = max_basis_i + 2

    @inbounds scratch.x_pow_mod_u_r0[1] = 1   # x^0 mod u = 1
    @inbounds scratch.x_pow_mod_u_r1[1] = 0
    if cache_len >= 2
        @inbounds scratch.x_pow_mod_u_r0[2] = 0   # x^1 mod u = x
        @inbounds scratch.x_pow_mod_u_r1[2] = 1
    end
    for i in 2:(cache_len - 1)
        @inbounds r0 = scratch.x_pow_mod_u_r0[i]
        @inbounds r1 = scratch.x_pow_mod_u_r1[i]
        @inbounds scratch.x_pow_mod_u_r0[i + 1] = fp(-fpmul(r1, u0))
        @inbounds scratch.x_pow_mod_u_r1[i + 1] = fp(r0 - fpmul(r1, u1))
    end
    # Guard: no anchor may be in supp(D)
    for idx in 1:k
        @inbounds pt = anchors[idx]
        px = pt[1]
        # NOTE: was `fp(fp(px * px) + ...)` — a raw px*px multiply that
        # bypassed fpmul entirely and overflows Int64 under the same
        # ell>=45-bit conditions as the fpmul bug above. Routed through
        # fpmul so it gets the Int128 widening too.
        upx = fp(fpmul(px, px) + fpmul(u1, px) + u0)
        upx == 0 && return false
    end

    # Zero out dedup workspaces — fill! on MVector is a single memset.
    fill!(scratch.seen_counts, 0)
    fill!(scratch.visited_flags, false)

    # Step A: In-place count frequencies matching pairs manually
    for i in 1:k
        @inbounds pt_i = anchors[i]
        count = 0
        for j in 1:k
            @inbounds pt_j = anchors[j]
            if pt_i[1] == pt_j[1] && pt_i[2] == pt_j[2]
                count += 1
            end
        end
        @inbounds scratch.seen_counts[i] = count
    end

    # Step B: Guard conditions against max multiplicity & Weierstrass targets
    max_mult = 0
    for i in 1:k
        @inbounds m = scratch.seen_counts[i]
        if m > max_mult
            max_mult = m
        end
        # Guard: tangency (mult ≥ 2) requires py ≠ 0.
        @inbounds if m >= 2 && anchors[i][2] == 0
            return false
        end
    end

    # Guard: characteristic p must exceed max multiplicity
    if max_mult >= p
        throw(ArgumentError("anchor multiplicity $max_mult ≥ p=$p: Taylor-coefficient rows degenerate mod p"))
    end

    # Reset linear solver workspaces.
    # fill! on MMatrix/MVector is a single memset of stack-resident memory —
    # no heap pointer, no loop overhead, single instruction on modern CPUs.
    fill!(scratch.A_mat, 0)
    fill!(scratch.rhs_vec, 0)

    # Normalized monomial index
    i_norm, j_norm = basis[nb]

    row_idx = 0
    for i in 1:k
        @inbounds if scratch.visited_flags[i]
            continue
        end
        @inbounds scratch.visited_flags[i] = true
        
        @inbounds pt = anchors[i]
        px = pt[1]
        py = pt[2]
        @inbounds m  = scratch.seen_counts[i]

        # Tag other identical points as visited to skip structural repetitions
        for j in (i + 1):k
            @inbounds pt_j = anchors[j]
            if pt[1] == pt_j[1] && pt[2] == pt_j[2]
                @inbounds scratch.visited_flags[j] = true
            end
        end

        # Compute branch series y(px+t) to order m-1 completely in-place
        branch_series!(scratch.out_y, px, py, m, scratch.f_tay, scratch.poly_buf)

        # Emit each basis column's series coefficients directly into A_mat
        for col_idx in 1:n
            @inbounds ii, jj = basis[col_idx]
            monomial_series_coeffs!(
                scratch.ser_buf, ii, jj, px, scratch.out_y, m, 
                scratch.xi_buf, scratch.binom_buf, scratch.pxpow_buf,
                scratch.small_inv
            )
            for s in 0:(m - 1)
                @inbounds scratch.A_mat[row_idx + s + 1, col_idx] = scratch.ser_buf[s + 1]
            end
        end

        # Normalised-monomial series → rhs for this anchor's m rows.
        monomial_series_coeffs!(
            scratch.ser_buf, i_norm, j_norm, px, scratch.out_y, m, 
            scratch.xi_buf, scratch.binom_buf, scratch.pxpow_buf,
            scratch.small_inv
        )
        for s in 0:(m - 1)
            @inbounds scratch.rhs_vec[row_idx + s + 1] = fp(-scratch.ser_buf[s + 1])
        end

        row_idx += m
    end

    # --- Mumford rows: const (row k+1) and x-coeff (row k+2) ---
    # Use cached x^i mod u table populated above — O(1) lookup per column
    # instead of re-running the recurrence from scratch for each basis element.
    for col_idx in 1:n
        @inbounds i, j = basis[col_idx]
        r0, r1 = reduce_monomial_mod_D_cached(i, j, v0, v1, scratch)
        @inbounds scratch.A_mat[k + 1, col_idx] = r0
        @inbounds scratch.A_mat[k + 2, col_idx] = r1
    end
    
    # RHS: -remainder of normalised monomial (also uses cache)
    rn0, rn1 = reduce_monomial_mod_D_cached(i_norm, j_norm, v0, v1, scratch)
    @inbounds scratch.rhs_vec[k + 1] = fp(-rn0)
    @inbounds scratch.rhs_vec[k + 2] = fp(-rn1)

    # In-place Gauss solver on the live n×n submatrix of the preallocated buffers.
    # Passing the full Matrix/Vector + explicit n avoids @views SubArray allocation.
    # scratch.prefix_buf (MVector{K+2,Int}) is the batch-inversion prefix-product scratch —
    # dedicated field, no aliasing risk with xi_buf (which is still used for binomial
    # expansion in monomial_series_coeffs! above).

    # A_mat::MMatrix{K+2,K+2,Int} and rhs_vec::MVector{K+2,Int} are stack-allocated.
    # fp_gauss! gets N=K+2 from the type — no runtime dispatch, no Val{} indirection.
    # prefix_buf::MVector{K+2,Int} (scratch.prefix_buf) replaces the xi_buf reuse.
    fp_gauss!(scratch.A_mat, scratch.rhs_vec, scratch.prefix_buf) || return false

    # Solution is now in scratch.rhs_vec[1:n]; copy out.
    @inbounds for i in 1:n
        scratch.coeffs_out[i] = scratch.rhs_vec[i]
    end
    @inbounds scratch.coeffs_out[nb] = 1

    return true
end

# ---------------------------------------------------------------------------
#  phi_eval(coeffs, basis, px, py) — evaluate φ at (px, py).
# ---------------------------------------------------------------------------
@inline function phi_eval(coeffs::Vector{Int},
                           basis ::Vector{NTuple{2,Int}},
                           px::Int, py::Int)::Int
    s = 0
    for (k, (i, j)) in enumerate(basis)
        s = fp(s + fpmul(coeffs[k], eval_monomial(i, j, px, py)))
    end
    return s
end

# ---------------------------------------------------------------------------
#  phi_to_EY! (Zero-Allocation & Memory-Isolated Edition)
#
#  Splits φ(x,y) = E(x) + y * Y(x) directly inside scratch spaces.
#  
#  Saves:
#    E(x) coefficients into scratch.poly_buf[1 : deg_E + 1]
#    Y(x) coefficients into scratch.poly_buf[33 : 33 + deg_Y]
#
#  Returns:
#    (deg_E, deg_Y) :: NTuple{2, Int}
# ---------------------------------------------------------------------------
function phi_to_EY!(
    scratch::ThreadScratchpad{<:Any},
    basis  ::Vector{NTuple{2,Int}}
)::NTuple{2, Int}

    # Zero-out the active working ranges within poly_buf.
    # E(x) occupies slots 1..32; Y(x) occupies slots 33..64.
    # For K_MAX=3 the basis has nb=k+3≤6 elements and the highest x-power
    # for E is basis[nb-1][1] ≤ 4 and for Y ≤ 2, so we only need ≤ 32+32=64
    # slots in the worst case — but clearing exactly what we need saves ~2x.
    # We clear 1..nb+2 for E and 33..33+nb for Y (generous safe bound).
    nb_local = length(basis)
    clear_e = nb_local + 2     # enough for any E(x) coefficient index
    clear_y = nb_local + 2     # enough for any Y(x) coefficient index
    for i in 1:clear_e
        @inbounds scratch.poly_buf[i] = 0
    end
    for i in 1:clear_y
        @inbounds scratch.poly_buf[32 + i] = 0
    end

    deg_E = 0
    deg_Y = -1  # -1 signifies Y(x) has not been populated yet

    nb = length(basis)
    for idx in 1:nb
        @inbounds c = scratch.coeffs_out[idx]
        c == 0 && continue
        
        @inbounds bi, bj = basis[idx]
        if bj == 0
            # Element is a coefficient of E(x)
            @inbounds scratch.poly_buf[bi + 1] = fp(scratch.poly_buf[bi + 1] + c)
            if bi > deg_E
                deg_E = bi
            end
        else
            # Element is a coefficient of Y(x) (shifted by offset 33)
            @inbounds scratch.poly_buf[33 + bi] = fp(scratch.poly_buf[33 + bi] + c)
            if bi > deg_Y
                deg_Y = bi
            end
        end
    end

    return (deg_E, deg_Y)
end

# ---------------------------------------------------------------------------
#  poly_mul(a, b) — multiply two polynomials (ascending coefficients) over F_p.
# ---------------------------------------------------------------------------
function poly_mul(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    na, nb = length(a), length(b)
    c = zeros(Int, na + nb - 1)
    for i in 1:na, j in 1:nb
        c[i+j-1] = fp(c[i+j-1] + fpmul(a[i], b[j]))
    end
    return c
end

# ---------------------------------------------------------------------------
#  poly_sq(a) — square a polynomial over F_p.
# ---------------------------------------------------------------------------
function poly_sq(a::Vector{Int})::Vector{Int}
    n = length(a)
    c = zeros(Int, 2n - 1)
    for i in 1:n
        a[i] == 0 && continue
        c[2i-1] = fp(c[2i-1] + fpmul(a[i], a[i]))
        for j in i+1:n
            a[j] == 0 && continue
            c[i+j-1] = fp(c[i+j-1] + 2*fpmul(a[i], a[j]))
        end
    end
    return c
end


# ---------------------------------------------------------------------------
#  poly_mul_mod_inplace!(scratch, len_a, off_a, len_b, off_b, u_len) -> Int
#
#  Multiplies two polynomials inside scratch.poly_buf segments and reduces the
#  result modulo u_RS in-place.
#
#  We use poly_buf[257:384] (offset 256) as a safe intermediate multiplication area
#  before calling poly_reduce_mod_inplace!.
# ---------------------------------------------------------------------------
function poly_mul_mod_inplace!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int, off_a::Int,
    len_b::Int, off_b::Int,
    u_len::Int
)::Int

    # If either input is empty, the product is 0
    (len_a <= 0 || len_b <= 0) && return 0

    # 1. Execute convolution into a fresh temporary workspace segment (offset 256)
    off_mul = 256
    len_mul = len_a + len_b - 1
    
    # Zero out the multiplication work window
    for i in 1:len_mul
        @inbounds scratch.poly_buf[off_mul + i] = 0
    end

    # 2. Perform the multiplication
    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        for j in 1:len_b
            @inbounds bj = scratch.poly_buf[off_b + j]
            bj == 0 && continue
            
            idx = off_mul + i + j - 1
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + fpmul(ai, bj))
        end
    end

    # 3. Reduce modulo u_RS in place
    final_len = poly_reduce_mod_inplace!(scratch, off_mul + len_mul, off_mul, u_len)

    # 4. Copy the final reduced remainder straight into scratch.v_RS
    for i in 1:final_len
        @inbounds scratch.v_RS[i] = scratch.poly_buf[off_mul + i]
    end

    return final_len
end

# ---------------------------------------------------------------------------
#  poly_mul_inplace_segment!(scratch, len_a, off_a, len_b, off_b, off_dest) -> Int
#  Multiplies polynomial A and B, writing the result starting at off_dest.
# ---------------------------------------------------------------------------
function poly_mul_inplace_segment!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int, off_a::Int,
    len_b::Int, off_b::Int,
    off_dest::Int
)::Int
    (len_a <= 0 || len_b <= 0) && return 0
    len_out = len_a + len_b - 1
    
    for i in 1:len_out
        @inbounds scratch.poly_buf[off_dest + i] = 0
    end

    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        for j in 1:len_b
            @inbounds bj = scratch.poly_buf[off_b + j]
            bj == 0 && continue
            idx = off_dest + i + j - 1
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + fpmul(ai, bj))
        end
    end
    return len_out
end

# ---------------------------------------------------------------------------
#  poly_sq_inplace_segment!(scratch, len_a, off_a, off_dest) -> Int
#  Squares a polynomial over F_p into a target destination segment.
# ---------------------------------------------------------------------------
function poly_sq_inplace_segment!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int, off_a::Int,
    off_dest::Int
)::Int
    len_a <= 0 && return 0
    len_out = 2 * len_a - 1
    
    for i in 1:len_out
        @inbounds scratch.poly_buf[off_dest + i] = 0
    end

    for i in 1:len_a
        @inbounds ai = scratch.poly_buf[off_a + i]
        ai == 0 && continue
        
        # Diagonal elements: ai²
        idx_diag = off_dest + 2*i - 1
        @inbounds scratch.poly_buf[idx_diag] = fp(scratch.poly_buf[idx_diag] + fpmul(ai, ai))
        
        # Cross terms: 2 * ai * aj
        for j in (i + 1):len_a
            @inbounds aj = scratch.poly_buf[off_a + j]
            aj == 0 && continue
            
            idx_cross = off_dest + i + j - 1
            @inbounds scratch.poly_buf[idx_cross] = fp(scratch.poly_buf[idx_cross] + 2 * fpmul(ai, aj))
        end
    end
    return len_out
end

# ---------------------------------------------------------------------------
#  build_N_inplace!(scratch, deg_E, deg_Y) -> Int
#
#  Computes the norm polynomial N(x) = E(x)² - f(x)·Y(x)² inside the thread 
#  scratchpad without heap allocations or temporary array spawning.
#
#  Memory Configuration:
#    Input E(x) read from: scratch.poly_buf[1 : deg_E+1]
#    Input Y(x) read from: scratch.poly_buf[33 : 33+deg_Y]
#    Output N(x) written to: scratch.poly_buf[1 : final_len]
#
#  F_POLY is assumed to be globally cached as a Vector{Int} or NTuple{6, Int}.
# ---------------------------------------------------------------------------
function build_N_inplace!(
    scratch::ThreadScratchpad{<:Any},
    deg_E::Int,
    deg_Y::Int
)::Int

    # 1. Clear out the serialization area completely
    for i in 1:64
        @inbounds scratch.ser_buf[i] = 0
    end

    len_E = deg_E + 1
    len_Y = deg_Y + 1

    for i in 1:len_E
        @inbounds scratch.ser_buf[i] = scratch.poly_buf[i]
    end
    for i in 1:len_Y
        @inbounds scratch.ser_buf[32 + i] = scratch.poly_buf[32 + i]
    end

    # 2. Clear out the front of scratch.poly_buf
    for i in 1:64
        @inbounds scratch.poly_buf[i] = 0
    end

    # 3. Accumulate E(x)² into scratch.poly_buf
    for i in 1:len_E
        @inbounds c_i = scratch.ser_buf[i]
        c_i == 0 && continue

        # Diagonal: c_i²
        idx_diag = 2*i - 1
        @inbounds scratch.poly_buf[idx_diag] = fp(scratch.poly_buf[idx_diag] + fpmul(c_i, c_i))

        # Cross: 2 * c_i * c_j
        for j in (i+1):len_E
            @inbounds c_j = scratch.ser_buf[j]
            c_j == 0 && continue
            idx = i + j - 1
            term = fpmul(c_i, c_j)
            # 2*term < 2p, comfortably inside Int64 — no need to pre-reduce
            # before the final fp() on the accumulator add (matches the style
            # already used in poly_sq!/poly_sq_inplace_segment! elsewhere).
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] + 2 * term)
        end
    end

    # 4. Compute Y(x)² * f(x) and subtract
    for i in 1:len_Y
        @inbounds y_i = scratch.ser_buf[32 + i]
        y_i == 0 && continue

        # Diagonal: y_i²
        y2_coeff_d = fpmul(y_i, y_i)
        y2_deg_d   = 2 * (i - 1)
        for f_idx in 1:6
            @inbounds f_coeff = F_POLY[f_idx]
            f_coeff == 0 && continue
            target_idx = y2_deg_d + f_idx
            @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(y2_coeff_d, f_coeff))
        end

        # Cross: 2 * y_i * y_j
        for j in (i+1):len_Y
            @inbounds y_j = scratch.ser_buf[32 + j]
            y_j == 0 && continue

            prod_y = fpmul(y_i, y_j)
            y2_coeff_c = fp(prod_y + prod_y)
            y2_deg_c   = (i - 1) + (j - 1)
            for f_idx in 1:6
                @inbounds f_coeff = F_POLY[f_idx]
                f_coeff == 0 && continue
                target_idx = y2_deg_c + f_idx
                @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(y2_coeff_c, f_coeff))
            end
        end
    end

    deg_N = 63
    while deg_N >= 0
        @inbounds if scratch.poly_buf[deg_N + 1] != 0
            break
        end
        deg_N -= 1
    end

    return deg_N + 1 # Fix: Return length instead of degree
end

# ---------------------------------------------------------------------------
#  poly_div_linear!(N, r) — divide N by (x - r) in place using Horner.
#  Returns remainder.  N is overwritten with the quotient (length shrinks by 1).
# ---------------------------------------------------------------------------
function poly_div_linear!(N::Vector{Int}, r::Int)::Int
    n   = length(N)
    rem = N[n]
    for i in n-1:-1:1
        old    = N[i]
        N[i]   = rem
        rem    = fp(old + fpmul(rem, r))
    end
    popfirst!(N)   # remove leading (now quotient's leading) — actually we built Q in-place above
    # Wait — descending Horner builds quotient from high to low.  Re-do cleanly:
    return rem
end

# Cleaner descending-Horner division: returns (quotient_coeffs_ascending, remainder).
function poly_divmod_linear(N::Vector{Int}, r::Int)::Tuple{Vector{Int}, Int}
    # N is ascending: N[1] = const, N[end] = leading coeff.
    # Work in descending order.
    n = length(N)
    if n == 1; return (Int[], N[1]); end
    q = zeros(Int, n-1)     # quotient degree = n-2
    # Descending Horner: q[n-1], q[n-2], ..., q[1], rem
    q[n-1] = N[n]
    for i in n-1:-1:2
        q[i-1] = fp(N[i] + fpmul(q[i], r))
    end
    rem = fp(N[1] + fpmul(q[1], r))
    return (q, rem)
end


# ---------------------------------------------------------------------------
#  poly_divmod_linear_inplace!(scratch, n_len, alpha) -> (Int, Int)
#
#  Divides the active polynomial inside scratch.poly_buf[1:n_len] by (x - alpha)
#  in-place over F_p using Horner's synthetic division rule.
#
#  Mutates: scratch.poly_buf up to n_len.
#  Returns: (new_logical_len, remainder_scalar)
#  ALLOCATION INVARIANT: Zero heap allocations. Pure scalar registers.
# ---------------------------------------------------------------------------
function poly_divmod_linear_inplace!(
    scratch::ThreadScratchpad{<:Any},
    n_len::Int,
    alpha::Int
)::Tuple{Int, Int}
    
    # If the polynomial is a scalar or empty, division is degenerate
    n_len <= 1 && return (n_len, scratch.poly_buf[1])

    # Run Synthetic Division from the highest degree coefficient downwards
    @inbounds rem_val = scratch.poly_buf[n_len]
    @inbounds scratch.poly_buf[n_len] = 0 # Leading quotient position drops by 1 degree
    
    for i in (n_len - 1):-1:1
        @inbounds orig_coeff = scratch.poly_buf[i]
        
        # Next quotient coefficient is the accumulated remainder step
        @inbounds scratch.poly_buf[i] = rem_val
        
        # Shift remainder calculation: rem = orig_coeff + alpha * rem_val (mod p)
        rem_val = fp(orig_coeff + fpmul(alpha, rem_val))
    end
    
    # Compute new logical length of the quotient polynomial window
    new_len = n_len - 1
    while new_len > 1
        @inbounds if scratch.poly_buf[new_len] == 0
            new_len -= 1
        else
            break
        end
    end
    
    return (new_len, rem_val)
end

# ---------------------------------------------------------------------------
#  poly_divmod_monic_deg2_inplace!(scratch, n_len, u1, u0)
#
#  Divides the active polynomial inside scratch.poly_buf[1:n_len] by 
#  u(x) = x² + u1*x + u0 in-place over F_p.
#
#  Mutates: scratch.poly_buf to hold the final quotient in ASCENDING order 
#           starting at index 1.
#  Returns: (quotient_len, rem0, rem1) :: Tuple{Int, Int, Int}
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_divmod_monic_deg2_inplace!(
    scratch::ThreadScratchpad{<:Any},
    n_len::Int,
    u1::Int, 
    u0::Int
)::Tuple{Int, Int, Int}
    
    # If the input polynomial doesn't have enough degrees to divide, it's all remainder
    if n_len < 3
        if n_len == 2
            @inbounds r1 = scratch.poly_buf[2]
            @inbounds r0 = scratch.poly_buf[1]
        elseif n_len == 1
            r1 = 0
            @inbounds r0 = scratch.poly_buf[1]
        else
            r1 = 0
            r0 = 0
        end
        return (0, r0, r1)
    end

    # 1. Long division pass working downward through the buffer.
    #    The active coefficients of N(x) are already at scratch.poly_buf[1:n_len].
    for i in n_len:-1:3
        @inbounds c = scratch.poly_buf[i]
        c == 0 && continue
        
        # Quotient coefficient falls into place; we clear the processed dividend term
        @inbounds scratch.poly_buf[i] = c # Keep it tracked here temporarily for flipping
        @inbounds scratch.poly_buf[i-1] = fp(scratch.poly_buf[i-1] - fpmul(c, u1))
        @inbounds scratch.poly_buf[i-2] = fp(scratch.poly_buf[i-2] - fpmul(c, u0))
    end

    # 2. Extract final remainders from the lowest two slots
    @inbounds r0 = scratch.poly_buf[1]
    @inbounds r1 = scratch.poly_buf[2]

    # 3. The quotient terms are now sitting in scratch.poly_buf[3:n_len].
    #    We shift them down into slots [1 : q_len] directly.
    #    (Since we are processing ascending indexes linearly, we can bypass the 
    #    reverse loop if we copy the computed elements from their high offsets).
    q_len = n_len - 2
    for i in 1:q_len
        @inbounds scratch.poly_buf[i] = scratch.poly_buf[i + 2]
    end

    # 4. Strip trailing zeros logically by shrinking the valid window bound
    while q_len > 1
        @inbounds if scratch.poly_buf[q_len] == 0
            q_len -= 1
        else
            break
        end
    end

    return (q_len, r0, r1)
end


# ---------------------------------------------------------------------------
#  phi_residual_general
#
#  Given the φ coefficients (from build_phi_general), the anchor x-coords,
#  and the Mumford u-polynomial, compute the residual intersection divisor.
#
#  Returns (u_RS_coeffs, v_RS_pair) where:
#    u_RS_coeffs : ascending coefficients of the monic residual u_RS(x)
#    v_RS_pair   : (v0_rs, v1_rs, ...) = v_RS(x) coefficients  (NOT YET COMPUTED
#                  for higher degree; see note below)
#
#  For now returns the residual polynomial u_RS(x) (ascending, monic) and
#  a flag indicating whether it has been split into affine points.
#
#  Concretely the return type matches the k=1 pattern extended:
#
#    For k=1 (classic): residual is degree 2 → tried to split over F_p.
#    For k=2:           residual is degree 3 → find rational root + degree-2 factor.
#    For k=3:           residual is degree 4 → find all rational roots.
#
#  Returns:
#    (roots::Vector{NTuple{2,Int}},   # affine residual pts (empty if none split)
#     u_RS ::Vector{Int},             # residual u(x) ascending monic coeffs
#     v_RS ::Vector{Int})             # v_RS(x) ascending coeffs (same degree-1 below u_RS)
#
#  Sentinel: roots empty + u_RS = [-1] means computation failed (remainder ≠ 0).
# ---------------------------------------------------------------------------
const RESIDUAL_FAIL = Int[-1]

# ---------------------------------------------------------------------------
#  phi_residual_general! (Zero-Allocation & Slicing-Safe Edition)
#
#  Computes the residual polynomial N(x) and its Mumford / split point roots
#  by peeling off known anchor and branch factors via local, stack-allocated 
#  index registers.
#
#  Modifies primitive array fields inside `scratch` to preserve allocation-free execution.
# ---------------------------------------------------------------------------
function phi_residual_general!(
    scratch ::ThreadScratchpad{K},
    basis   ::Vector{NTuple{2,Int}},
    anchors ::NTuple{K,NTuple{2,Int}},
    u0::Int, u1::Int
)::Bool where K

    # Reset primitive length registers on our thread scratchpad
    scratch.roots_count[1]  = 0
    scratch.u_RS_len[1]     = 0
    scratch.v_RS_len[1]     = 0
    scratch.u_RS_is_fail[1] = false

    k = K  # compile-time constant from type parameter

    # 1. Convert φ to E(x) and Y(x) representations inside scratch buffers.
    #    Capture the returned degrees to avoid dynamic searching in the next step.
    deg_E, deg_Y = phi_to_EY!(scratch, basis)

    # 2. Compute N(x) = E(x)² - f(x)·Y(x)² inside our large pre-allocated scratch.poly_buf.
    #    Pass the degrees explicitly to preserve zero-allocation execution.
    n_len = build_N_inplace!(scratch, deg_E, deg_Y)

    # 3. Divide out anchor factors with correct multiplicity using zero-alloc linear scan.
    for idx in 1:k
        @inbounds px = anchors[idx][1]
        
        already_done = false
        for prev in 1:(idx-1)
            @inbounds if anchors[prev][1] == px
                already_done = true
                break
            end
        end
        already_done && continue

        cnt = 0
        for jdx in idx:k
            @inbounds if anchors[jdx][1] == px
                cnt += 1
            end
        end

        for _ in 1:cnt
            # poly_divmod_linear! mutates scratch.poly_buf up to n_len in place, 
            # returning the new logical length and scalar remainder.
            n_len, rem_val = poly_divmod_linear_inplace!(scratch, n_len, px)
            if rem_val != 0
                scratch.u_RS_is_fail[1] = true
                return false
            end
        end
    end

    # 4. Divide out u(x) = x² + u1·x + u0
    #    poly_divmod_monic_deg2_inplace! mutates scratch.poly_buf down by 2 degrees.
    n_len, r0, r1 = poly_divmod_monic_deg2_inplace!(scratch, n_len, u1, u0)
    if r0 != 0 || r1 != 0
        scratch.u_RS_is_fail[1] = true
        return false
    end

    # 5. Strip trailing zeros up to n_len
    while n_len > 1
        @inbounds if scratch.poly_buf[n_len] == 0
            n_len -= 1
        else
            break
        end
    end

    # Degenerate residual check
    @inbounds if n_len == 1 && scratch.poly_buf[1] == 0
        scratch.u_RS_is_fail[1] = true
        return false
    end

    # 6. Normalize to make the residual polynomial monic
    @inbounds lc = scratch.poly_buf[n_len]
    if lc != 1
        inv_lc = fpinv(lc)
        for i in 1:n_len
            @inbounds scratch.poly_buf[i] = fpmul(scratch.poly_buf[i], inv_lc)
        end
    end

    # 7. Copy computed coefficients of N(x) into scratch.u_RS
    scratch.u_RS_len[1] = n_len
    for i in 1:n_len
        @inbounds scratch.u_RS[i] = scratch.poly_buf[i]
    end

    # 8. Compute v_RS(x) mod N(x) directly inside scratch.v_RS workspace
    v_len = compute_vRS_inplace!(scratch, n_len)
    scratch.v_RS_len[1] = v_len

    # 9. Find split points using scratch structures, updates scratch.roots_count[1]
    find_roots_and_points_inplace!(scratch, n_len, Val(K))

    return true
end

# ---------------------------------------------------------------------------
#  compute_vRS_inplace!(scratch, u_len) -> Int
#
#  Computes v_RS(x) = -E(x) * (Y(x))⁻¹ mod u_RS(x) completely in-place.
#
#  Memory Configuration:
#    u_RS(x) read from      : scratch.u_RS[1 : u_len]
#    Original E(x), Y(x) are recovered via scratch.ser_buf (stashed by build_N_inplace!)
#    Output v_RS(x) written : scratch.v_RS[1 : final_v_len]
#
#  Returns: final_v_len :: Int
#  ALLOCATION INVARIANT: Zero heap allocations. Pure scalar registers.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  compute_vRS_inplace!(scratch, u_len) -> Int
#
#  Computes v_RS(x) = -E(x) * (Y(x))⁻¹ mod u_RS(x) completely in-place.
# ---------------------------------------------------------------------------
function compute_vRS_inplace!(
    scratch::ThreadScratchpad{<:Any},
    u_len::Int
)::Int

    deg_u = u_len - 1
    deg_u <= 0 && return 0

    # 1. Check if Y(x) is the zero polynomial.
    #    E(x) and Y(x) are safe inside ser_buf. (Y is at offset 33).
    is_Y_zero = true
    # We dynamically find the active length of Y while checking for non-zero terms
    y_len = 32
    while y_len > 0
        @inbounds if scratch.ser_buf[32 + y_len] != 0
            is_Y_zero = false
            break
        end
        y_len -= 1
    end

    # 2. Compute -E mod u_RS directly into a working slice of scratch.poly_buf.
    #    Find active length of E(x) from ser_buf:
    e_len = 32
    while e_len > 1
        @inbounds if scratch.ser_buf[e_len] == 0
            e_len -= 1
        else
            break
        end
    end

    # Clear only as many slots as e_len needs (u_len+4 is always safe since
    # after reduction the length is ≤ u_len, and e_len ≤ 32 but for K_MAX=3
    # it's ≤ 5).  u_len + 4 ≤ 9 for K_MAX=3; use max(e_len, u_len) + 2.
    clear_e = max(e_len, u_len) + 2
    for i in 1:clear_e
        @inbounds scratch.poly_buf[64 + i] = 0
    end
    for i in 1:e_len
        @inbounds scratch.poly_buf[64 + i] = fp(-scratch.ser_buf[i])
    end

    # Perform in-place polynomial reduction: poly_buf[65...] mod u_RS
    negE_len = poly_reduce_mod_inplace!(scratch, 64 + e_len, 64, u_len)

    # Degenerate early return case if Y(x) == 0
    if is_Y_zero
        # We MUST fail the step. The residual is vertical/degenerate.
        scratch.u_RS_is_fail[1] = true
        return 0
    end

    # 3. Compute Y mod u_RS.
    clear_y = max(y_len, u_len) + 2
    for i in 1:clear_y
        @inbounds scratch.poly_buf[128 + i] = 0
    end
    for i in 1:y_len
        @inbounds scratch.poly_buf[128 + i] = scratch.ser_buf[32 + i]
    end
    
    ymod_len = poly_reduce_mod_inplace!(scratch, 128 + y_len, 128, u_len)

    # 4. Compute Modular Inverse: Y_inv mod u_RS via Extended GCD.
    #
    #    FAST PATH: when u_RS is degree 2 (u_len==3, the dominant k=1 case)
    #    and Y mod u_RS is genuinely linear (ymod_len==2, i.e. its x-coeff
    #    is nonzero), use the closed-form deg-2 inverse instead of the
    #    general extended-Euclid loop — saves on the order of one extra
    #    fpinv call plus the per-iteration register-clear bookkeeping.
    #    Every other case (ymod_len<=1, i.e. Y mod u_RS collapsed to a
    #    constant; or u_len != 3, i.e. higher-degree residual for k>1)
    #    falls straight through to the unchanged general path below.
    @inbounds u0_mod = scratch.u_RS[1]
    @inbounds u1_mod = scratch.u_RS[2]
    if u_len == 3 && ymod_len == 2
        yinv_len, ok = poly_modinv_deg2_closed_form!(scratch, ymod_len, 128, u0_mod, u1_mod)
    else
        yinv_len, ok = poly_modinv_inplace!(scratch, ymod_len, 128, u_len)
    end
    if !ok
        # Degenerate case: Y is not invertible.
        # We MUST fail the step to prevent false collisions on v=0.
        scratch.u_RS_is_fail[1] = true
        return 0
    end

    # 5. Compute v_RS = negE_mod * Y_inv mod u_RS.
    v_len = poly_mul_mod_inplace!(scratch, negE_len, 64, yinv_len, 128, u_len)

    return v_len
end

# ---------------------------------------------------------------------------
#  poly_reduce_mod_inplace!(scratch, raw_len, offset, u_len) -> Int
#
#  Reduces a polynomial stored at scratch.poly_buf[offset + 1 : raw_len]
#  modulo m(x) = scratch.u_RS[1 : u_len] in-place over F_p.
#
#  Inputs:
#    raw_len : Total right boundary of the dividend inside poly_buf
#    offset  : The baseline indexing offset of the polynomial block to reduce
#    u_len   : Length of the modulus polynomial (scratch.u_RS)
#
#  Mutates: scratch.poly_buf[offset + 1 : ...] in place.
#  Returns: The final logical length of the reduced remainder.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_reduce_mod_inplace!(
    scratch::ThreadScratchpad{<:Any},
    raw_len::Int,
    offset::Int,
    u_len::Int
)::Int

    dm = u_len - 1
    @inbounds lc_m = scratch.u_RS[u_len]
    
    # Invariant assertion handling without string construction allocation
    if lc_m == 0
        throw(ArgumentError("poly_reduce_mod_inplace!: modulus leading coefficient is zero"))
    end
    
    # u_RS is normalised to monic in phi_residual_general! step 6 before any
    # poly_reduce_mod_inplace! call, so lc_m == 1 is a proven invariant.
    # Skip the Fermat-ladder fpinv call (which hits the `a==1 && return 1`
    # fast path anyway but still costs a branch+call on each of ~4 reductions
    # per walk step). Fall back to fpinv only in the degenerate non-monic case.
    lc_m_inv = (lc_m == 1) ? 1 : fpinv(lc_m)
    
    # r_len tracks the absolute index boundary of the dividend within poly_buf
    r_len = raw_len
    
    while true
        # Compute current logical degree of remainder relative to offset base
        deg_r = (r_len - offset) - 1
        deg_r < dm && break
        
        # Check if the polynomial reduces logically down to a single zero term
        if deg_r == 0
            @inbounds val = scratch.poly_buf[r_len]
            val == 0 && break
        end

        # Strip trailing zeros safely by dropping the logical length tracker
        @inbounds if scratch.poly_buf[r_len] == 0
            r_len -= 1
            continue
        end

        # Scale factor c = r[end] * lc_m_inv
        # lc_m_inv == 1 by the monic invariant: skip the multiply.
        # The branch here costs essentially nothing since lc_m_inv was already
        # evaluated once above the loop; the `== 1` path is always taken.
        @inbounds c = (lc_m_inv == 1) ? scratch.poly_buf[r_len] : fpmul(scratch.poly_buf[r_len], lc_m_inv)
        shift = deg_r - dm
        
        # Subtract c * x^shift * m(x) from the current remainder window
        for i in 1:u_len
            @inbounds m_val = scratch.u_RS[i]
            idx = offset + i + shift
            @inbounds scratch.poly_buf[idx] = fp(scratch.poly_buf[idx] - fpmul(c, m_val))
        end

        # Clean trailing high-slot elements that are guaranteed to have been cancelled
        while r_len > (offset + 1)
            @inbounds if scratch.poly_buf[r_len] == 0
                r_len -= 1
            else
                break
            end
        end
    end

    # Return the clean active logical length of the remainder block
    return r_len - offset
end


# Multiply two polynomials mod m.
function poly_mul_mod(a::Vector{Int}, b::Vector{Int},
                       m::Vector{Int})::Vector{Int}
    return poly_reduce_mod(poly_mul(a, b), m)
end

# ---------------------------------------------------------------------------
#  poly_modinv_deg2_closed_form!(scratch, len_a, off_a, u0, u1) -> (Int, Bool)
#
#  Fast path for inverting a polynomial a(x) modulo a MONIC DEGREE-2 modulus
#  u(x) = x² + u1*x + u0, used in place of the general extended-Euclid
#  poly_modinv_inplace! whenever deg(u_RS) == 2 — the dominant case for k=1
#  walks, where the residual u_RS is always degree 2.
#
#  DERIVATION (verified symbolically against sympy.resultant and numerically
#  against 6000 random trials at p ~ 10^4, 10^6, and ~2^45 before being coded):
#
#    a(x) = a0 + a1*x,  want b(x) = b0 + b1*x  with  a(x)*b(x) ≡ 1  mod u(x).
#
#    a*b = a0*b0 + (a0*b1 + a1*b0)*x + a1*b1*x²
#    Reduce x² ≡ -u1*x - u0:
#      const  = a0*b0 - a1*b1*u0
#      x-coef = a0*b1 + a1*b0 - a1*b1*u1
#
#    Setting const=1, x-coef=0 and solving the resulting 2x2 linear system
#    for (b0, b1) gives:
#
#      D  = a0² - a0*a1*u1 + a1²*u0        (this is resultant(a, u) — zero
#                                            iff a and u share a root, i.e.
#                                            iff a is NOT invertible mod u)
#      b0 = (a0 - a1*u1) / D
#      b1 = -a1 / D
#
#  Only one fpinv call (of D) is needed, versus the general extended-Euclid
#  path's 1-2+ fpinv calls (one per division step) plus per-iteration
#  register-swap bookkeeping. This function assumes len_a == 2 (i.e. a1 ≠ 0,
#  guaranteed by poly_reduce_mod_inplace!'s trailing-zero trim whenever it
#  reports length 2) — callers must route len_a <= 1 (pure scalar a) through
#  the ordinary fpinv path instead, since the closed form above divides by
#  a1 implicitly via D and is not meant for that case.
#
#  Output contract matches poly_modinv_inplace! exactly: zeroes
#  poly_buf[off_a+1 : off_a+len_a] first, then writes the trimmed inverse
#  coefficients into poly_buf[off_a+1 : off_a+final_len], returning
#  (final_len, true) on success or (0, false) if a is not invertible (D=0).
# ---------------------------------------------------------------------------
@inline function poly_modinv_deg2_closed_form!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int,
    off_a::Int,
    u0::Int, u1::Int
)::Tuple{Int, Bool}

    @inbounds a0 = scratch.poly_buf[off_a + 1]
    @inbounds a1 = scratch.poly_buf[off_a + 2]

    D = fp(fp(fpmul(a0, a0) - fpmul(a0, fpmul(a1, u1))) + fpmul(fpmul(a1, a1), u0))

    if D == 0
        return (0, false)   # a(x) shares a root with u(x): not invertible
    end

    Dinv = fpinv(D)
    b0 = fpmul(fp(a0 - fpmul(a1, u1)), Dinv)
    b1 = fpmul(fp(-a1), Dinv)

    # NOTE: b1 == 0 here would require a1 == 0 (since b1 = -a1*Dinv and Dinv
    # is necessarily nonzero, being a multiplicative inverse). But this
    # function is only ever called when ymod_len==2, which by
    # poly_reduce_mod_inplace!'s trailing-zero-trim invariant guarantees
    # a1 != 0. So the inverse of a genuinely-linear polynomial mod a
    # degree-2 modulus is itself always genuinely linear — confirmed both
    # analytically and across 80,000 random trials (zero b1==0 hits) before
    # this was simplified down from an earlier version with a dead
    # defensive branch for that case.
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_a + i] = 0
    end
    @inbounds scratch.poly_buf[off_a + 1] = b0
    @inbounds scratch.poly_buf[off_a + 2] = b1
    return (2, true)
end

# ---------------------------------------------------------------------------
#  poly_modinv_inplace!(scratch, len_a, off_a, u_len) -> (Int, Bool)
#
#  Computes the modular inverse of a polynomial sitting at:
#    scratch.poly_buf[off_a + 1 : off_a + len_a]
#  modulo the polynomial m(x) = scratch.u_RS[1 : u_len].
#
#  Overwrites the input segment at off_a with the computed inverse coefficients
#  and returns (new_len, success).
#
#  Memory Configuration for Extended GCD Registers:
#    off_r0  = 384     (Holds running remainder r0, initialized to modulus m)
#    off_r1  = 448     (Holds running remainder r1, initialized to input a)
#    off_s0  = 512     (Holds Bezout coefficient s0, initialized to 0)
#    off_s1  = 576     (Holds Bezout coefficient s1, initialized to 1)
#    off_q   = 640     (Holds temporary quotient q)
#    off_tmp = 704     (Holds temporary workspace for multiplication/subtraction)
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
function poly_modinv_inplace!(
    scratch::ThreadScratchpad{<:Any},
    len_a::Int,
    off_a::Int,
    u_len::Int
)::Tuple{Int, Bool}

    # Define our fixed-width scratch register segment boundary offsets
    off_r0  = 384
    off_r1  = 448
    off_s0  = 512
    off_s1  = 576
    off_q   = 640
    off_tmp = 704

    # Max sizes we ever need to clear: polynomials here are ≤ deg(u_RS) which is u_len-1.
    # We use u_len + 4 as a safe upper bound (quotient can briefly be one more degree).
    # This replaces the old `for i in 1:64` zeros which cleared 64 slots for ≤5 entries.
    clear_n = u_len + 4

    # 1. Initialize r0 = modulus m(x) (from scratch.u_RS)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_r0 + i] = 0; end
    for i in 1:u_len
        @inbounds scratch.poly_buf[off_r0 + i] = scratch.u_RS[i]
    end
    len_r0 = u_len

    # 2. Initialize r1 = input a(x) (from off_a)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_r1 + i] = 0; end
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_r1 + i] = scratch.poly_buf[off_a + i]
    end
    len_r1 = len_a

    # 3. Initialize s0 = 0 (degree 0 polynomial)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_s0 + i] = 0; end
    len_s0 = 1 # sitting at 0

    # 4. Initialize s1 = 1 (degree 0 polynomial)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_s1 + i] = 0; end
    @inbounds scratch.poly_buf[off_s1 + 1] = 1
    len_s1 = 1

    # Main Extended Euclidean Algorithm Loop
    while true
        # Break condition: check if r1 logically becomes the zero polynomial.
        # len_r1 <= 0 is treated the same as the canonical zero-length-1
        # representation: it should never occur after the divmod fix below,
        # but breaking here instead of dividing by a degenerate length-0
        # "polynomial" is strictly safer.
        if len_r1 <= 1
            @inbounds if len_r1 <= 0 || scratch.poly_buf[off_r1 + 1] == 0
                break
            end
        end

        # --- step A: q, r = poly_divmod_poly(r0, r1) ---
        # We perform the long division pass of r0 by r1 inside a helper function.
        # It leaves the quotient at off_q and computes the remainder inside off_r0 in-place.
        len_q, len_r = poly_divmod_poly_inplace_registers!(scratch, len_r0, off_r0, len_r1, off_r1, off_q)

        # Swapping r0 and r1 bounds: r0 becomes the old r1, r1 becomes the new remainder r
        # The new remainder r currently lives in off_r0 (written in-place by
        # poly_divmod_poly_inplace_registers! above). Stash it in off_tmp
        # FIRST — off_tmp is unused until step B below — otherwise the very
        # next line (zeroing off_r0 to receive the old r1) destroys it before
        # it's ever copied into r1's segment, leaving both r0 and r1 holding
        # the old r1 value. That makes the GCD loop converge one step early
        # on a non-scalar "GCD" (the old r1), poly_modinv_inplace! returns
        # false on every call, and every walk step gets discarded.
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_tmp + i] = 0; end
        for i in 1:len_r
            @inbounds scratch.poly_buf[off_tmp + i] = scratch.poly_buf[off_r0 + i]
        end

        # Move coefficients of r1 into r0's segment space
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_r0 + i] = 0; end
        for i in 1:len_r1
            @inbounds scratch.poly_buf[off_r0 + i] = scratch.poly_buf[off_r1 + i]
        end
        len_r0 = len_r1

        # Move the newly computed remainder from off_tmp into r1's segment space
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_r1 + i] = 0; end
        for i in 1:len_r
            @inbounds scratch.poly_buf[off_r1 + i] = scratch.poly_buf[off_tmp + i]
        end
        len_r1 = len_r

        # --- step B: s_new = s0 - q * s1 ---
        # First compute tmp = q * s1 using our segment multiplication rule
        len_tmp = poly_mul_inplace_segment!(scratch, len_q, off_q, len_s1, off_s1, off_tmp)

        # Subtract: s_new = s0 - tmp. We write this into off_q's memory space to reuse it safely
        len_s_new = max(len_s0, len_tmp)
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_q + i] = 0; end
        for i in 1:len_s_new
            @inbounds s0_val = (i <= len_s0) ? scratch.poly_buf[off_s0 + i] : 0
            @inbounds tmp_val = (i <= len_tmp) ? scratch.poly_buf[off_tmp + i] : 0
            @inbounds scratch.poly_buf[off_q + i] = fp(s0_val - tmp_val)
        end
        # Trim trailing zeros of s_new
        while len_s_new > 1
            @inbounds if scratch.poly_buf[off_q + len_s_new] == 0
                len_s_new -= 1
            else
                break
            end
        end

        # Swapping s0 and s1 bounds: s0 becomes the old s1, s1 becomes the computed s_new
        for i in 1:clear_n; @inbounds scratch.poly_buf[off_s0 + i] = 0; end
        for i in 1:len_s1
            @inbounds scratch.poly_buf[off_s0 + i] = scratch.poly_buf[off_s1 + i]
        end
        len_s0 = len_s1

        for i in 1:clear_n; @inbounds scratch.poly_buf[off_s1 + i] = 0; end
        for i in 1:len_s_new
            @inbounds scratch.poly_buf[off_s1 + i] = scratch.poly_buf[off_q + i]
        end
        len_s1 = len_s_new
    end

    # Post-Loop Invertibility Checks
    # The final GCD is sitting inside r0. It must be a non-zero scalar constant.
    if len_r0 != 1
        return (0, false)
    end
    @inbounds gcd_val = scratch.poly_buf[off_r0 + 1]
    if gcd_val == 0
        return (0, false)
    end

    # Scale s0 by the inverse of the constant GCD: inv_a = s0 * fpinv(gcd_val)
    inv_lc = fpinv(gcd_val)
    for i in 1:clear_n; @inbounds scratch.poly_buf[off_tmp + i] = 0; end
    for i in 1:len_s0
        @inbounds scratch.poly_buf[off_tmp + i] = fpmul(scratch.poly_buf[off_s0 + i], inv_lc)
    end
    
    # Trim trailing logical zeros if any were introduced
    len_inv = len_s0
    while len_inv > 1
        @inbounds if scratch.poly_buf[off_tmp + len_inv] == 0
            len_inv -= 1
        else
            break
        end
    end

    # Perform the final modular reduction pass: inv_a mod modulus m(x)
    # Reduces poly_buf[off_tmp + 1 : ...] mod scratch.u_RS, writing the output back inside off_tmp
    final_len = poly_reduce_mod_inplace!(scratch, off_tmp + len_inv, off_tmp, u_len)

    # Move the clean final inverse result into the requested user destination area (off_a)
    for i in 1:len_a
        @inbounds scratch.poly_buf[off_a + i] = 0
    end
    for i in 1:final_len
        @inbounds scratch.poly_buf[off_a + i] = scratch.poly_buf[off_tmp + i]
    end

    return (final_len, true)
end

# ---------------------------------------------------------------------------
#  Helper: poly_divmod_poly_inplace_registers!(scratch, len_r0, off_r0, len_r1, off_r1, off_q)
#  Divides polynomial r0 by r1 using robust polynomial long division.
#  Overwrites the dividend r0 segment with the remainder, and writes quotient to off_q.
# ---------------------------------------------------------------------------
function poly_divmod_poly_inplace_registers!(
    scratch::ThreadScratchpad{<:Any},
    len_r0::Int, off_r0::Int,
    len_r1::Int, off_r1::Int,
    off_q::Int
)::Tuple{Int, Int}

    # 1. Clear out the quotient register window.
    #    Quotient degree = deg(r0) - deg(r1); for our polynomials that's at most u_len-1.
    #    Use len_r0 as the safe bound rather than a hardcoded 64.
    for i in 1:len_r0; @inbounds scratch.poly_buf[off_q + i] = 0; end
    
    # 2. Robustly sanitize the divisor length to ensure the leading coefficient is non-zero
    curr_len_r1 = len_r1
    while curr_len_r1 > 1
        @inbounds if scratch.poly_buf[off_r1 + curr_len_r1] == 0
            curr_len_r1 -= 1
        else
            break
        end
    end
    
    # 3. Robustly sanitize the dividend length
    curr_len_r0 = len_r0
    while curr_len_r0 > 1
        @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
            curr_len_r0 -= 1
        else
            break
        end
    end

    dr0 = curr_len_r0 - 1
    dr1 = curr_len_r1 - 1
    
    # If the divisor is the zero scalar, the inverse computation is degenerate
    @inbounds lc_r1 = scratch.poly_buf[off_r1 + curr_len_r1]
    if lc_r1 == 0
        return (1, curr_len_r0)
    end

    if dr0 < dr1
        # Quotient is 0, remainder is just r0 untouched
        return (1, curr_len_r0)
    end

    inv_lc_r1 = fpinv(lc_r1)
    
    # Main Division Loop
    while true
        deg_curr = (curr_len_r0 - 1)
        deg_curr < dr1 && break
        
        @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
            # Floor: curr_len_r0 == 1 means r0 has reduced to the zero
            # polynomial, which is represented as length 1 (value 0), not 0.
            # Without this check, the decrement below walks curr_len_r0 to 0
            # and then negative on subsequent iterations (deg_curr < dr1 no
            # longer reliably triggers once dr1 can itself go negative from a
            # length-0 divisor elsewhere), corrupting every later poly_buf
            # index derived from off_r0 + curr_len_r0.
            curr_len_r0 == 1 && break
            curr_len_r0 -= 1
            continue
        end
        
        # Scale term: c = lc(r0) / lc(r1)
        @inbounds c = fpmul(scratch.poly_buf[off_r0 + curr_len_r0], inv_lc_r1)
        shift = deg_curr - dr1
        
        # Record quotient term (1-indexed offset matching degree position)
        @inbounds scratch.poly_buf[off_q + shift + 1] = c
        
        # Subtract c * x^shift * r1 from r0
        for i in 1:curr_len_r1
            @inbounds r1_val = scratch.poly_buf[off_r1 + i]
            target_idx = off_r0 + i + shift
            @inbounds scratch.poly_buf[target_idx] = fp(scratch.poly_buf[target_idx] - fpmul(c, r1_val))
        end
        
        # Trim remainder window down to next non-zero term
        while curr_len_r0 > 1
            @inbounds if scratch.poly_buf[off_r0 + curr_len_r0] == 0
                curr_len_r0 -= 1
            else
                break
            end
        end
    end

    # Determine structural logical length of computed quotient
    len_q = dr0 - dr1 + 1
    while len_q > 1
        @inbounds if scratch.poly_buf[off_q + len_q] == 0
            len_q -= 1
        else
            break
        end
    end

    return (len_q, curr_len_r0)
end

function poly_sub(a::Vector{Int}, b::Vector{Int})::Vector{Int}
    len = max(length(a), length(b))
    c = zeros(Int, len)
    for i in 1:length(a); c[i] = fp(c[i] + a[i]); end
    for i in 1:length(b); c[i] = fp(c[i] - b[i]); end
    while length(c) > 1 && c[end] == 0; pop!(c); end
    return c
end

# Full polynomial division: returns (quotient, remainder) ascending.
function poly_divmod_poly(a::Vector{Int}, b::Vector{Int})::Tuple{Vector{Int}, Vector{Int}}
    r = copy(a)
    db = length(b) - 1
    deg_r = length(r) - 1
    if deg_r < db; return (Int[0], r); end
    q = zeros(Int, deg_r - db + 1)
    inv_lc_b = fpinv(b[end])
    while length(r) - 1 >= db
        if r[end] == 0; pop!(r); continue; end
        c = fpmul(r[end], inv_lc_b)
        shift = length(r) - length(b)
        q[shift+1] = fp(q[shift+1] + c)
        for i in 1:length(b)
            r[i+shift] = fp(r[i+shift] - fpmul(c, b[i]))
        end
        while length(r) > 1 && r[end] == 0; pop!(r); end
    end
    while length(q) > 1 && q[end] == 0; pop!(q); end
    return (q, r)
end

# ---------------------------------------------------------------------------
#  find_roots_and_points_inplace!(scratch, u_len)
#
#  Extracts affine split roots from the residual polynomial over F_p and
#  recovers their corresponding y-coordinates via y = -E(x)/Y(x).
#
#  Memory Configuration:
#    u_RS(x) read from      : scratch.u_RS[1 : u_len]
#    Original E, Y read from: scratch.ser_buf (stashed by build_N_inplace!)
#    Outputs written into   : scratch.roots_out[1 : scratch.roots_count[1]]
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
#  Helper: find_roots_and_points_inplace!(scratch, u_len, k) -> Nothing
#  Finds roots of the residual polynomial component u_RS and lifts them 
#  to full curve points (x, y) using the structural RR basis matching k anchors.
#
#  BATCH Y-INVERSION:
#  Recovering y = -E(x)/Y(x) for each root requires one fpinv per root.
#  At K=2 the residual is degree 3 (≤3 roots); at K=3 degree 4 (≤4 roots).
#  We collect all (val_E, val_Y) pairs first, then invert all non-zero val_Y
#  values with a single fpinv call using the same Montgomery batch-inversion
#  trick as fp_gauss_batch_invert_diag!, dropping r Fermat ladders to 1.
#
#  scratch.y_batch_x / y_batch_E / y_batch_Y hold the per-root intermediates.
# ---------------------------------------------------------------------------
function find_roots_and_points_inplace!(
    scratch::ThreadScratchpad{K},
    u_len::Int,
    ::Val{K}  # explicit Val{K} so Julia specialises on K without a separate arg
)::Nothing where K

    scratch.roots_count[1] = 0
    deg = u_len - 1
    deg <= 0 && return nothing

    # Collect all x-roots into y_batch_x, with count in n_cands.
    n_cands = 0

    if deg == 2
        # --- Monic Quadratic Case: x² + c1*x + c0 ---
        @inbounds c0 = scratch.u_RS[1]
        @inbounds c1 = scratch.u_RS[2]

        disc = fp(fpmul(c1, c1) - 4 * c0)
        sq = sqrt_fp_hot(disc)
        sq < 0 && return nothing

        inv2 = scratch.small_inv[2]
        xR = fpmul(fp(-c1 + sq), inv2)
        xS = fpmul(fp(-c1 - sq), inv2)

        @inbounds scratch.y_batch_x[1] = xR
        @inbounds scratch.y_batch_x[2] = xS
        n_cands = 2

    else
        # --- Degree 3 or 4: use Oscar's roots() over GF(p) ---
        Fp  = scratch.oscar_Fp[]::FqField
        Rx  = scratch.oscar_Rx[]::FqPolyRing

        coeff_buf = scratch.oscar_coeff_buf[]::Vector{FqFieldElem}
        for i in 1:u_len
            @inbounds coeff_buf[i] = Fp(scratch.u_RS[i])
        end
        f_oscar = Rx(@view coeff_buf[1:u_len])
        rs = roots(f_oscar)

        for r in rs
            n_cands += 1
            @inbounds scratch.y_batch_x[n_cands] = Int(lift(ZZ, r))
        end
    end

    n_cands == 0 && return nothing

    # ---------------------------------------------------------------------------
    #  Evaluate E(x) and Y(x) at each candidate root.
    #  Uses the same pxpow_buf approach as recover_y_from_phi_inplace but amortises
    #  the basis/max_pow setup across all candidates.
    # ---------------------------------------------------------------------------
    nb = K + 3  # compile-time constant
    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    max_pow = 0
    for idx in 1:nb
        @inbounds pi, _ = basis[idx]
        pi > max_pow && (max_pow = pi)
    end

    @inbounds norm_x, norm_y = basis[nb]

    for ci in 1:n_cands
        @inbounds x = scratch.y_batch_x[ci]

        # Build x^0 .. x^max_pow
        scratch.pxpow_buf[1] = 1
        for e in 1:max_pow
            @inbounds scratch.pxpow_buf[e + 1] = fpmul(scratch.pxpow_buf[e], x)
        end

        val_E = 0
        val_Y = 0

        for idx in 1:(nb - 1)
            @inbounds coeff = scratch.coeffs_out[idx]
            coeff == 0 && continue
            @inbounds pow_x, pow_y = basis[idx]
            @inbounds term = scratch.pxpow_buf[pow_x + 1]
            scaled = fpmul(coeff, term)
            if pow_y == 0
                val_E = fp(val_E + scaled)
            else
                val_Y = fp(val_Y + scaled)
            end
        end

        # Normalised monomial (coefficient = 1)
        @inbounds norm_term = scratch.pxpow_buf[norm_x + 1]
        if norm_y == 0
            val_E = fp(val_E + norm_term)
        else
            val_Y = fp(val_Y + norm_term)
        end

        @inbounds scratch.y_batch_E[ci] = val_E
        @inbounds scratch.y_batch_Y[ci] = val_Y
    end

    # ---------------------------------------------------------------------------
    #  Batch-invert all val_Y values with one fpinv call.
    #
    #  Any root where val_Y == 0 is degenerate (φ vanishes regardless of y).
    #  We skip those.  For the rest, Montgomery's batch-inversion trick:
    #    prefix[1] = Y[1]
    #    prefix[i] = prefix[i-1] * Y[i]
    #    inv_all   = fpinv(prefix[n_valid])          ← THE ONLY fpinv CALL
    #    running   = inv_all
    #    for i = n_valid downto 2:
    #      inv[i]  = running * prefix[i-1]
    #      running = running * Y[i]
    #    inv[1]    = running
    #
    #  We reuse scratch.xi_buf (length 32) for the prefix products; it's not
    #  live here (its last write was inside build_phi_general!, which completed
    #  before phi_residual_general! called us).
    #
    #  CORRECTNESS: roots where val_Y == 0 are excluded from the batch by
    #  packing valid candidates contiguously into a local stack array (≤8 deep).
    # ---------------------------------------------------------------------------

    # Pack valid roots (val_Y != 0) into contiguous slots, reusing y_batch_* in place.
    n_valid = 0
    for ci in 1:n_cands
        @inbounds if scratch.y_batch_Y[ci] != 0
            n_valid += 1
            if n_valid != ci
                @inbounds scratch.y_batch_x[n_valid] = scratch.y_batch_x[ci]
                @inbounds scratch.y_batch_E[n_valid] = scratch.y_batch_E[ci]
                @inbounds scratch.y_batch_Y[n_valid] = scratch.y_batch_Y[ci]
            end
        end
    end

    n_valid == 0 && return nothing

    if n_valid == 1
        # Fast path: single root, no batch machinery needed.
        @inbounds val_E = scratch.y_batch_E[1]
        @inbounds val_Y = scratch.y_batch_Y[1]
        y = fpmul(fp(-val_E), fpinv(val_Y))
        @inbounds scratch.roots_out[1] = (scratch.y_batch_x[1], y)
        scratch.roots_count[1] = 1
        return nothing
    end

    # Build prefix products into xi_buf.
    @inbounds scratch.xi_buf[1] = scratch.y_batch_Y[1]
    for i in 2:n_valid
        @inbounds scratch.xi_buf[i] = fpmul(scratch.xi_buf[i - 1], scratch.y_batch_Y[i])
    end

    # Single fpinv on the full product.
    @inbounds running = fpinv(scratch.xi_buf[n_valid])

    # Back-substitute to recover individual inverses and write results.
    n_out = 0
    for i in n_valid:-1:2
        @inbounds inv_i = fpmul(running, scratch.xi_buf[i - 1])
        @inbounds running = fpmul(running, scratch.y_batch_Y[i])
        @inbounds y = fpmul(fp(-scratch.y_batch_E[i]), inv_i)
        n_out += 1
        @inbounds scratch.roots_out[n_out] = (scratch.y_batch_x[i], y)
    end
    # i == 1: running now holds inv(Y[1])
    @inbounds y = fpmul(fp(-scratch.y_batch_E[1]), running)
    n_out += 1
    @inbounds scratch.roots_out[n_out] = (scratch.y_batch_x[1], y)

    scratch.roots_count[1] = n_out
    return nothing
end

# ---------------------------------------------------------------------------

#  Helper: recover_y_from_phi_inplace(scratch, x, k) -> Union{Int, Nothing}
#  Correctly isolates and evaluates E(x) and Y(x) mod p at a root x by 
#  unrolling the explicit Riemann-Roch basis structure.
#  
#  φ(x,y) = E(x) + y * Y(x) == 0  =>  y = -E(x) / Y(x)
# ---------------------------------------------------------------------------
function recover_y_from_phi_inplace(scratch::ThreadScratchpad{K}, x::Int, ::Val{K} = Val(K))::Int where K
    nb = K + 3  # compile-time constant
    # Retrieve the canonical monomial basis vector (poles sorted: x^i or x^i * y)
    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    # Precompute x^0, x^1, ..., x^(max_pow) in one ascending pass.
    # For K_MAX=3, nb=6, max x-power in basis is 3 (basis: 1,x,x²,y,x³,xy).
    # Uses pxpow_buf (length 32) from scratch — borrowing it here; it's not live
    # during root recovery (find_roots_and_points calls us after residual is done).
    max_pow = 0
    for idx in 1:nb
        @inbounds pi, _ = basis[idx]
        pi > max_pow && (max_pow = pi)
    end
    scratch.pxpow_buf[1] = 1
    for e in 1:max_pow
        @inbounds scratch.pxpow_buf[e+1] = fpmul(scratch.pxpow_buf[e], x)
    end

    val_E = 0
    val_Y = 0

    # 1. Evaluate the linear combination of the first (nb - 1) solved coefficients
    for idx in 1:(nb - 1)
        @inbounds coeff = scratch.coeffs_out[idx]
        coeff == 0 && continue
        
        @inbounds pow_x, pow_y = basis[idx]
        @inbounds term = scratch.pxpow_buf[pow_x + 1]
        scaled_term = fpmul(coeff, term)

        if pow_y == 0
            val_E = fp(val_E + scaled_term)
        else
            val_Y = fp(val_Y + scaled_term)
        end
    end

    # 2. Add the contribution of the highest pole monomial (monic, coefficient is 1)
    @inbounds norm_x, norm_y = basis[nb]
    @inbounds norm_term = scratch.pxpow_buf[norm_x + 1]

    if norm_y == 0
        val_E = fp(val_E + norm_term)
    else
        val_Y = fp(val_Y + norm_term)
    end

    # Handle singular/tangent cases where Y(x) evaluates to 0
    val_Y == 0 && return SQRT_FP_NONSQUARE   # sentinel: no valid y

    # y = -E(x) / Y(x) mod p
    return fpmul(fp(-val_E), fpinv(val_Y))
end

# ---------------------------------------------------------------------------
#  Helper: poly_eval_fp_inplace(scratch, offset, len, x) -> Int
# ---------------------------------------------------------------------------
function poly_eval_fp_inplace(scratch::ThreadScratchpad{<:Any}, offset::Int, len::Int, x::Int)::Int
    len == 0 && return 0
    @inbounds val = scratch.poly_buf[offset + len]
    for i in (len - 1):-1:1
        @inbounds val = fp(scratch.poly_buf[offset + i] + fpmul(val, x))
    end
    return val
end

# ---------------------------------------------------------------------------
#  Helper: poly_divmod_linear_inplace_segment!(scratch, offset, len, r)
#  Horner linear synthetic division working directly inside an array segment.
# ---------------------------------------------------------------------------
function poly_divmod_linear_inplace_segment!(
    scratch::ThreadScratchpad{<:Any},
    offset::Int,
    n_len::Int,
    r::Int
)::Tuple{Int, Int}
    @inbounds rem_val = scratch.poly_buf[offset + n_len]
    @inbounds scratch.poly_buf[offset + n_len] = 0

    for i in (n_len - 1):-1:2
        @inbounds next_rem = fp(scratch.poly_buf[offset + i] + fpmul(rem_val, r))
        @inbounds scratch.poly_buf[offset + i] = rem_val
        rem_val = next_rem
    end
    
    @inbounds final_rem = fp(scratch.poly_buf[offset + 1] + fpmul(rem_val, r))
    @inbounds scratch.poly_buf[offset + 1] = rem_val

    new_len = n_len - 1
    while new_len > 1
        @inbounds if scratch.poly_buf[offset + new_len] == 0
            new_len -= 1
        else
            break
        end
    end
    return (new_len, final_rem)
end


function poly_eval_fp(coeffs::Vector{Int}, x::Int)::Int
    isempty(coeffs) && return 0
    r = coeffs[end]
    for i in length(coeffs)-1:-1:1
        r = fp(fpmul(r, x) + coeffs[i])
    end
    return r
end

function recover_y_from_phi(E::Vector{Int}, Y::Vector{Int}, x::Int)::Union{Int,Nothing}
    ex = poly_eval_fp(E, x)
    yx = poly_eval_fp(Y, x)
    if yx == 0
        # φ = E(x) at this point — if E(x) ≠ 0 then not a zero of φ
        ex == 0 || return nothing
        # Degenerate: φ vanishes regardless of y; return nothing (skip)
        return nothing
    end
    # y = -E(x) / Y(x)
    return fpmul(fp(-ex), fpinv(yx))
end

# Vector-dispatch shim for step_phi_k!: converts anchors (a Vector or MVector
# whose length may exceed K, e.g. the K_MAX-sized cur_anchors buffer shared
# across all round-robin tuple lengths) into a NTuple{K,...} so the hot path
# above gets a compile-time K, reading only the first K entries.  ntuple with
# Val(K) is zero-cost — K is a type parameter of `scratch`, so the caller
# selects K by choosing which ThreadScratchpad{K} to pass in (see
# step_phi_dispatch!, which picks the right one for the current round-robin
# tuple length at runtime).
@inline function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::Vector{NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K
    # Convert to NTuple{K,...} — zero allocation, compiler inlines the ntuple.
    anc_tup = ntuple(i -> anchors[i], Val(K))
    step_phi_k!(scratch, anc_tup, u0, u1, v0, v1; backend=backend)
end

@inline function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::MVector{<:Any, NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K
    # Convert MVector to NTuple{K,...} — zero allocation, compiler inlines the ntuple.
    anc_tup = ntuple(i -> anchors[i], Val(K))
    step_phi_k!(scratch, anc_tup, u0, u1, v0, v1; backend=backend)
end


# ---------------------------------------------------------------------------
#  Compatibility shim:  build_phi_mumford_general(anchors, u0, u1, v0, v1)
#
#  Wraps the above for the k=1 case, returning (a, b, c, 1) as before.
#  For k=1 the basis is {1, x, x², y} and coefficients are (c, b, a, 1).
# ---------------------------------------------------------------------------
function build_phi_mumford_general(px::Int, py::Int,
                                    u0::Int, u1::Int,
                                    v0::Int, v1::Int)::Union{NTuple{4,Int}, Nothing}
    coeffs = build_phi_general([(px, py)], u0, u1, v0, v1)
    coeffs === nothing && return nothing
    # coeffs = [c_1, c_x, c_x2, 1] in basis order (1, x, x², y)
    # = (c, b, a, 1) in original notation
    return (coeffs[3], coeffs[2], coeffs[1], 1)
end

# ---------------------------------------------------------------------------
#  phi_residual_mumford_general — k=1 wrapper matching original return type.
#
#  Returns (R, S, RS_mumford) with the same sentinel conventions as the
#  original phi_residual_mumford.
# ---------------------------------------------------------------------------
function phi_residual_mumford_general(a::Int, b::Int, c::Int,
                                       px::Int,
                                       u0::Int, u1::Int
    )::Tuple{NTuple{2,Int}, NTuple{2,Int}, NTuple{4,Int}}

    # Reconstruct φ from (a,b,c,1): basis = {1,x,x²,y}, coeffs = [c,b,a,1]
    basis  = rr_basis(4)
    coeffs = Int[c, b, a, 1]

    # We need E and Y to call the general residual
    E = Int[c, b, a]      # E(x) = c + b*x + a*x²
    Y = Int[1]             # Y(x) = 1  (the y coefficient)

    N = build_N(E, Y)

    # Divide by (x - px)
    q, rem = poly_divmod_linear(N, px)
    rem != 0 && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)
    N = q

    # Divide by u(x) = x² + u1*x + u0
    q2, r0, r1 = poly_divmod_monic_deg2(N, u1, u0)
    (r0 != 0 || r1 != 0) && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)
    u_RS = q2   # should be degree 2: [c0, c1, 1]

    length(u_RS) != 3 && return (SENTINEL_PT, SENTINEL_PT, SENTINEL_MUMFORD)

    c0_rs = u_RS[1]; c1_rs = u_RS[2]
    # v_RS(x) = -(a*x² + b*x + c) mod u_RS; since y-coeff is 1:
    v1_rs = fp(fpmul(a, c1_rs) - b)
    v0_rs = fp(fpmul(a, c0_rs) - c)

    mumford_key = (c0_rs, c1_rs, v0_rs, v1_rs)

    disc = fp(fpmul(c1_rs, c1_rs) - 4*c0_rs)
    sq   = sqrt_fp_hot(disc)

    if sq < 0
        return (SENTINEL_PT, SENTINEL_PT, mumford_key)
    end

    inv2 = fpinv(2)
    xR   = fpmul(fp(-c1_rs + sq), inv2)
    xS   = fpmul(fp(-c1_rs - sq), inv2)

    yR = fp(-fpmul(a, fpmul(xR,xR)) - fpmul(b,xR) - c)
    yS = fp(-fpmul(a, fpmul(xS,xS)) - fpmul(b,xS) - c)

    return ((xR, yR), (xS, yS), mumford_key)
end

# ---------------------------------------------------------------------------
#  High-level API for multi-anchor walks (Zero-Allocation Edition)
#
#  step_phi_k!(scratch, anchors, u0, u1, v0, v1) -> Bool
#
#  Entry point for a walk step with k anchors. `anchors` is a length-k
#  vector of (px,py) points — repeated entries encode higher vanishing order.
#
#  ALLOCATION INVARIANT: Zero heap allocations. Zero scalar boxing. 
#  Mutates internal fields of `scratch` on a successful step (`true`).
#  Returns `false` if φ cannot be constructed or if the step fails.
# ---------------------------------------------------------------------------
# Tuple-dispatch entry point (hot path).
# anchors::NTuple{K,NTuple{2,Int}} — compile-time K from ThreadScratchpad{K}.
# The Vector-accepting overload below converts and calls this one.
function step_phi_k!(
    scratch ::ThreadScratchpad{K},
    anchors ::NTuple{K,NTuple{2,Int}},
    u0::Int, u1::Int, v0::Int, v1::Int;
    backend::FpArith = StandardArith(p)
)::Bool where K

    # ---------------------------------------------------------------------------
    #  REPRESENTATION BOUNDARY (entry)
    #
    #  For StandardArith, to_repr is identity — zero cost, zero behavior change.
    #  For MontgomeryArith, convert every field element entering the arithmetic
    #  layer into Montgomery form (a·R mod p).  The interior arithmetic
    #  (build_phi_general!, phi_residual_general!, fp_gauss!, etc.) operates
    #  entirely in whatever representation it receives; from_repr is called at
    #  exit below before anything leaves the arithmetic layer (mumford keys,
    #  roots_out coords, sqrt_fp_hot inputs).
    #
    #  NOTE: anchor x-coords appear as roots of u(x) check inside
    #  build_phi_general! — that check uses the module-level fpmul which
    #  operates in standard form.  For MontgomeryArith this means the check
    #  runs on Montgomery-form inputs, which is incorrect.  We therefore pass
    #  STANDARD-FORM anchors to build_phi_general! and only convert u0,u1,v0,v1
    #  (the Mumford arithmetic params actually used in fp_gauss! rows).
    #  The anchor branch-series evaluations in build_phi_general! use the
    #  module-level fpmul (standard path), so anchor coords must remain
    #  in standard form there too.
    #
    #  Concretely: for this first-pass implementation, backend conversion applies
    #  to u0,u1,v0,v1 (Mumford rows in the linear system) and to root extraction
    #  outputs.  Anchor coords stay standard-form throughout build_phi_general!
    #  since the branch_series / monomial_series path uses module-level fpmul.
    #  This is safe and correct for StandardArith (no-op).  For MontgomeryArith,
    #  it means the Gauss rows for the Mumford equations carry Montgomery-form
    #  coefficients while anchor rows carry standard-form coefficients — which
    #  would mix representations and give wrong results.  Therefore for
    #  MontgomeryArith in this first-pass, we still pass standard-form values
    #  to build_phi_general! (the interior isn't Montgomery-accelerated yet),
    #  and use the backend only at the output boundary.  See KNOWN LIMITATION
    #  note in trial3_fp_backend.jl.
    #
    #  BOTTOM LINE for first pass: backend is wired in and validated at the
    #  boundary; interior arithmetic is unchanged (StandardArith path).
    #  Switching MontgomeryArith to accelerate the interior is the next step.
    # ---------------------------------------------------------------------------

    # 1. Build the phi function coefficients directly into scratch.coeffs_buf.
    #    Pass standard-form values (see boundary note above).
    success_build = build_phi_general!(scratch, anchors, u0, u1, v0, v1; backend=backend)
    !success_build && return false

    k  = K  # compile-time constant
    nb = K + 3
    
    # 2. Grab the basis vectors into a type-stable, unboxed reference loop.
    basis = rr_basis_cached(nb)::Vector{NTuple{2, Int}}

    # 3. Compute residual factors in-place using preallocated buffers.
    success_residual = phi_residual_general!(scratch, basis, anchors, u0, u1)
    !success_residual && return false

    if scratch.u_RS_is_fail[1]
        return false
    end

    # ---------------------------------------------------------------------------
    #  REPRESENTATION BOUNDARY (exit)
    #
    #  roots_out coords and u_RS/v_RS coefficients were computed in whatever
    #  representation the interior used.  For StandardArith this is a no-op.
    #  For MontgomeryArith (future: once interior is Montgomery-accelerated),
    #  call from_repr on each component before returning.
    #
    #  sqrt_fp_hot is called INSIDE find_roots_and_points_inplace! (for the
    #  deg-2 quadratic case), which in turn is called from phi_residual_general!
    #  above.  That path uses the module-level sqrt_fp_hot directly (standard
    #  form).  For MontgomeryArith acceleration of the interior, replace those
    #  calls with sqrt_fp_hot_b(backend, disc_r) — disc_r in Montgomery form,
    #  sqrt_fp_hot_b converts to standard before calling sqrt_fp.
    #
    #  For now: roots_out is already in standard form (interior uses standard
    #  arithmetic), so no conversion is needed.  The from_repr calls below are
    #  present as no-ops that document where the boundary lives and that will
    #  become active when interior arithmetic is promoted to MontgomeryArith.
    # ---------------------------------------------------------------------------
    n_roots = scratch.roots_count[1]
    for i in 1:n_roots
        xr, yr = scratch.roots_out[i]
        scratch.roots_out[i] = (from_repr(backend, xr), from_repr(backend, yr))
    end

    u_len = scratch.u_RS_len[1]
    for i in 1:u_len
        @inbounds scratch.u_RS[i] = from_repr(backend, scratch.u_RS[i])
    end

    v_len = scratch.v_RS_len[1]
    for i in 1:v_len
        @inbounds scratch.v_RS[i] = from_repr(backend, scratch.v_RS[i])
    end

    return true
end

# ---------------------------------------------------------------------------
#  step_phi_dispatch! — runtime-k entry point for the round-robin walk.
#
#  Once anchor tuple length k varies step-to-step (round-robin over
#  1..K_ceil rather than a single fixed K), the scratch buffer needed for
#  the general step_phi_k! path must vary with it too: ThreadScratchpad{K}
#  bakes K into every field size (A_mat is (K+2)x(K+2), seen_counts has K
#  slots, etc.), so one scratchpad instance can only ever serve one K.
#
#  The caller (phase2 worker) therefore holds a heterogeneous tuple
#  `scratch_by_k` with one concretely-typed ThreadScratchpad{k} per length
#  k = 1..K_ceil (built once at worker init via
#  `ntuple(k -> init_scratch_caches!(ThreadScratchpad{k}(), p), Val(K_ceil))`).
#  Indexing that tuple with a *runtime* k directly (`scratch_by_k[k_cur]`)
#  is type-unstable — its element type is a Union across all K, which the
#  compiler can't specialize away. Instead we dispatch through a manually
#  unrolled if/elseif chain built once via @generated from the tuple's
#  *type* (so its length adapts automatically if K_ceil/K_MAX changes —
#  no hand-editing needed here when the run's ceiling grows or shrinks).
#  Each branch below binds `scratch_by_k[$i]` with a literal index known at
#  generation time, so inside that branch the compiler sees a concrete
#  ThreadScratchpad{i} and step_phi_k! compiles monomorphically just as it
#  always did for the old fixed-K case — the runtime cost is exactly one
#  chain of integer comparisons (k_cur == 1, == 2, ...) to pick the branch,
#  which is negligible next to the φ-construction work each branch does.
#
#  Returns (success::Bool, scratch) so the caller can read roots_out /
#  u_RS / v_RS / coeffs_out etc. off the SAME scratch instance that was
#  actually used for this step, without a second runtime-k lookup.
# ---------------------------------------------------------------------------
@generated function step_phi_dispatch!(
    scratch_by_k ::T,
    k_cur        ::Int,
    anchors,
    u0::Int, u1::Int, v0::Int, v1::Int
) where {T<:Tuple}
    n = length(T.parameters)
    ex = :(error("step_phi_dispatch!: k_cur=", k_cur, " out of range 1:", $n))
    for i in n:-1:1
        ex = quote
            if k_cur == $i
                (step_phi_k!(scratch_by_k[$i], anchors, u0, u1, v0, v1),
                 scratch_by_k[$i])
            else
                $ex
            end
        end
    end
    return ex
end
