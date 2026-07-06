import sanity_check as sc
import symbolic_port as sp
import random

p = sc.p
fails = 0
trials = 0
for seed in range(200):
    random.seed(seed)
    for K in [1,2,3,4]:
        xs = set()
        fixed_anchors = []
        for _ in range(K-1):
            x,y = sc.find_point(xs)
            xs.add(x)
            fixed_anchors.append((x,y))
        u0,u1,v0,v1,P1,P2 = sc.make_valid_mumford_divisor(xs)
        t0,y0 = sc.find_point(xs)

        all_anchors = fixed_anchors + [(t0,y0)]
        try:
            u_RS_direct, v_RS_direct, degE, degY = sc.build_phi_and_residual(K, all_anchors, u0,u1,v0,v1, sc.f_asc)
        except AssertionError:
            continue

        trials += 1
        try:
            u_RS_sym, v_RS_sym = sp.symbolic_residual(K, fixed_anchors, u0,u1,v0,v1, sc.f_asc, t0, y0)
        except AssertionError as e:
            print(f"seed={seed} K={K}: symbolic FAILED: {e}")
            fails += 1
            continue

        if u_RS_direct != u_RS_sym or v_RS_direct != v_RS_sym:
            print(f"seed={seed} K={K}: MISMATCH direct={u_RS_direct},{v_RS_direct} symb={u_RS_sym},{v_RS_sym}")
            fails += 1

print(f"\n{trials} trials, {fails} failures")
