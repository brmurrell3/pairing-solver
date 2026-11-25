# Claim A: for a group balanced within calls and within puts, the netted intrinsic payoff at
#   each strike K_m equals  Q0 + sum_{j<m} D_j * (K_{j+1} - K_j),  where
#   Q0 = sum over puts of signed_qty * K   and   D_j = running sum of signed_qty (calls and puts
#   together) over strikes <= K_j.  Also: the minimum over a fine price grid equals the minimum
#   over strikes (strike evaluation is exact).
# Claim B: "each short pairs with a same-type long expiring on or after it" is feasible iff for
#   every expiry d, short units expiring >= d <= long units expiring >= d (nested Hall condition).
#   Checked against an explicit max-flow.
import random
def payoff(legs, P):
    return sum(q * (max(P - k, 0) if t == "C" else max(k - P, 0)) for t, k, e, q in legs)
def walk(legs):
    ks = sorted({k for _, k, _, _ in legs})
    q0 = sum(q * k for t, k, e, q in legs if t == "P")
    out, g, d = [], q0, 0
    for idx, k in enumerate(ks):
        if idx: g += d * (k - ks[idx - 1])
        out.append(g)
        d += sum(q for _, kk, _, q in legs if kk == k)
    return ks, out
def balanced(rng, n):
    legs = []
    for t in "CP":
        m = rng.randint(1, n)
        qs = [rng.randint(1, 5) for _ in range(m)]
        sides = [rng.choice((1, -1)) for _ in range(m)]
        legs += [(t, rng.randint(1, 40) * 5, rng.randint(1, 4), s * q) for s, q in zip(sides, qs)]
        net = sum(q for tt, _, _, q in legs if tt == t)
        if net: legs.append((t, rng.randint(1, 40) * 5, rng.randint(1, 4), -net))
    return legs
def hall(legs):
    for t in "CP":
        L = [(e, q) for tt, _, e, q in legs if tt == t and q > 0]
        S = [(e, -q) for tt, _, e, q in legs if tt == t and q < 0]
        for d in {e for e, _ in S}:
            if sum(q for e, q in S if e >= d) > sum(q for e, q in L if e >= d): return False
    return True
def maxflow_ok(legs):
    for t in "CP":
        L = [[e, q] for tt, _, e, q in legs if tt == t and q > 0]
        S = [[e, -q] for tt, _, e, q in legs if tt == t and q < 0]
        need = sum(q for _, q in S)
        # unit-by-unit augmenting paths on the bipartite graph (small instances)
        cap = {(i, j): 10**9 for i, (es, _) in enumerate(S) for j, (el, _) in enumerate(L) if el >= es}
        flow = {key: 0 for key in cap}
        sl, ll = [q for _, q in S], [q for _, q in L]
        sent = 0
        while True:
            # BFS from source over shorts with residual supply
            prev, frontier = {}, [("s", i) for i in range(len(S)) if sl[i] > 0]
            for node in frontier: prev[node] = None
            found = None
            while frontier and not found:
                nxt = []
                for kind, i in frontier:
                    if kind == "s":
                        for j in range(len(L)):
                            if (i, j) in cap and ("l", j) not in prev:
                                prev[("l", j)] = ("s", i); nxt.append(("l", j))
                                if ll[j] > 0: found = ("l", j); break
                    else:
                        for i2 in range(len(S)):
                            if (i2, i) in flow and flow[(i2, i)] > 0 and ("s", i2) not in prev:
                                prev[("s", i2)] = ("l", i); nxt.append(("s", i2))
                    if found: break
                frontier = nxt
            if not found: break
            node = found; ll[node[1]] -= 1
            while prev[node] is not None:
                p = prev[node]
                if p[0] == "s": flow[(p[1], node[1])] += 1
                else: flow[(node[1], p[1])] -= 1
                node = p
            sl[node[1]] -= 1; sent += 1
        if sent < need or sum(q for _, q in L) != need: return False
    return True
rng = random.Random(7)
a_bad = b_bad = grid_bad = 0
N = 3000
for _ in range(N):
    legs = balanced(rng, 4)
    ks, w = walk(legs)
    if any(abs(payoff(legs, k) - g) > 1e-9 for k, g in zip(ks, w)): a_bad += 1
    fine = min(payoff(legs, p / 4) for p in range(0, 4 * 260))
    if fine < min(w) - 1e-9: grid_bad += 1
    if hall(legs) != maxflow_ok(legs): b_bad += 1
print(f"claim A (walk formula) mismatches: {a_bad}/{N}")
print(f"strike evaluation missed a lower payoff on a fine grid: {grid_bad}/{N}")
print(f"claim B (nested Hall vs max-flow) disagreements: {b_bad}/{N}")
