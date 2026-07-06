import sanity_check as sc
import symbolic_port as sp
import random

p = sc.p
random.seed(123)

for K in [1,2,3]:
    xs = set()
    fixed_anchors = []
    for _ in range(K-1):
        x,y = sc.find_point(xs)
        xs.add(x)
        fixed_anchors.append((x,y))

    u0,u1,v0,v1,P1,P2 = sc.make_valid_mumford_divisor(xs)

    # pick a concrete last-anchor point (t0,y0) on the curve, distinct from fixed anchors
    t0,y0 = sc.find_point(xs)

    # Run the CONCRETE pipeline directly with all K anchors (K-1 fixed + (t0,y0))
    all_anchors = fixed_anchors + [(t0,y0)]
    try:
        u_RS_direct, v_RS_direct, degE, degY = sc.build_phi_and_residual(K, all_anchors, u0,u1,v0,v1, sc.f_asc)
    except AssertionError as e:
        print(f"K={K}: concrete direct pipeline FAILED: {e}")
        continue

    # Run the SYMBOLIC pipeline, then evaluate at t0 with y0
    try:
        u_RS_sym, v_RS_sym = sp.symbolic_residual(K, fixed_anchors, u0,u1,v0,v1, sc.f_asc, t0, y0)
    except AssertionError as e:
        print(f"K={K}: symbolic pipeline FAILED: {e}")
        continue

    match_u = (u_RS_direct == u_RS_sym)
    match_v = (v_RS_direct == v_RS_sym)
    print(f"K={K}: direct u_RS={u_RS_direct} v_RS={v_RS_direct}")
    print(f"K={K}: symb   u_RS={u_RS_sym} v_RS={v_RS_sym}")
    print(f"K={K}: MATCH u={match_u} v={match_v}")
