#!/usr/bin/env python3
"""Brute-force checks of two results in docs/proofs.md, "Hardness":

- "Not approximable, premiums included": on the instances of Theorems 1 and 2,
  priced with small call premiums, the least total requirement (long premiums
  included) is the premiums alone when the source instance has a matching, and at
  least (1 + rho) times them when it has none.
- "Several expirations": the two dynamic programs for one maximum-loss group with
  several expirations (one over strikes that carries a net count per expiration, one
  over expirations that carries the payoff at every strike) agree with exhaustive
  search.

    python3 tools/check_approx_expiry.py            # about a minute
    python3 tools/check_approx_expiry.py --quick    # a few seconds

Python 3.9 or later, standard library only. Uses tools/check_hardness.py for the
reductions and the spread enumerations. Exit status 0 means every check passed.
"""

import os
import random
import sys
from fractions import Fraction
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_hardness as ch  # noqa: E402

failures = 0


def check(ok, what):
    global failures
    if not ok:
        failures += 1
        print(f"  FAIL: {what}")


# ---------------------------------------------------------------------------
# Part 1: premiums included.
# ---------------------------------------------------------------------------


def priced(position, unit, rho):
    """Shift the instance's strikes above the underlying and price it.

    Strikes become S + k for the instance's strike k, with S = 10 * unit, so every call
    is out of the money and R3 charges every short at least S / 10 = unit. Premiums are
    C(K) = pi * (1 + ((K_top - K) / range)^2): positive, falling and strictly convex in
    the strike, at most 2 * pi, so no butterfly or vertical is free. pi is chosen so that
    unit >= rho * (the long premiums), with the long premiums at most 2 * pi a contract.
    The premium formula is strictly convex, so no butterfly is free.
    """
    s = 10 * unit
    shifted = {s + k: q for k, q in position.items()}
    longs = sum(q for q in shifted.values() if q > 0)
    pi = Fraction(unit, 2 * longs * rho)
    top, bottom = max(shifted), min(shifted)
    width = max(top - bottom, 1)

    def price(k):
        return pi * (1 + Fraction(top - k, width) ** 2)

    for k in shifted:
        p = price(k)
        assert 0 < p <= s and p >= max(s - k, 0)
    naked = {k: ch.uncovered_call(k, price(k), s) for k in shifted}
    premiums = sum(q * price(k) for k, q in shifted.items() if q > 0)
    return shifted, naked, premiums


def check_premiums(rng, cases, rho):
    """Theorem 1 with lesser-of on and off, and Theorem 2 for three and four series."""
    counts = {"named": [0, 0], "three": [0, 0], "four": [0, 0]}
    worst = None
    for n, top, count in cases:
        for _ in range(count):
            a, b, c, bound = ch.random_n3dm(rng, n, top)
            want = ch.n3dm(a, b, c, bound)
            right = ch.total_is_right(a, b, c, bound)
            runs = [("named", ch.butterfly_instance(a, b, c, bound), None)]
            if right:
                runs.append(("three", ch.butterfly_instance(a, b, c, bound), 3))
                runs.append(("four", ch.condor_instance(a, b, c, bound), 4))
            for name, position, legs in runs:
                # Positive requirements are at least u and the R3 floor S / 10 = u. On the
                # named instance the only credit spreads are bear spreads from a short at
                # y <= M + W - 1 to a long at z >= 2M + 2, so u = M - W + 3. Under a leg
                # limit a positive maximum loss on whole strikes is at least u = 1.
                w = max([bound] + a + b + c)
                unit = ch.scale(a, b, c, bound) - w + 3 if name == "named" else 1
                shifted, naked, premiums = priced(position, unit, rho)
                for lesser_of in (False, True):
                    if legs is None:
                        spreads = ch.named_spreads(shifted, naked, lesser_of)
                    else:
                        spreads = ch.leg_limited_spreads(shifted, naked, legs, lesser_of)
                    total = premiums + ch.min_requirement(shifted, spreads)
                    if want:
                        check(total == premiums, f"{name} yes: a={a} b={b} c={c} B={bound}")
                    else:
                        ratio = total / premiums
                        check(ratio >= 1 + rho, f"{name} no: ratio {float(ratio)} a={a} b={b} c={c} B={bound}")
                        worst = ratio if worst is None else min(worst, ratio)
                counts[name][0 if want else 1] += 1
    print(f"premiums included, rho = {rho}: "
          + ", ".join(f"{k} {v[0]} yes / {v[1]} no" for k, v in counts.items())
          + " agree; least ratio on a no instance " + (f"{float(worst):.1f}" if worst else "none"))


# ---------------------------------------------------------------------------
# Part 2: one maximum-loss group with several expirations.
# ---------------------------------------------------------------------------
#
# A series is (type, strike, expiration), type 'C' or 'P'. Holdings: series -> signed
# contracts (one deliverable, per share). Every short has a standalone cost U. A group
# takes 0..|holding| contracts of each series. It must balance within calls and within
# puts (R1 d) and pass the pairwise expiration condition: for each type and expiration
# d, the shorts expiring on or after d are at most the longs expiring on or after d
# (proofs.md, item 4). Cost: the group's maximum loss at the strikes plus U for every
# short left out. Longs cost the same either way (nine months or less) and are left out.


def payoff_at(chosen, s):
    return sum(q * (max(s - k, 0) if t == "C" else max(k - s, 0))
               for (t, k, _), q in chosen.items())


def suffix_ok(nets):
    """nets: per-expiration net contracts of one type, earliest first."""
    run = 0
    for v in reversed(nets):
        run += v
        if run < 0:
            return False
    return run == 0


def brute(holdings, naked, strikes, exps):
    series = sorted(holdings)
    ranges = [range(0, holdings[x] + 1) if holdings[x] > 0 else range(holdings[x], 1) for x in series]
    best = None
    for qs in product(*ranges):
        chosen = dict(zip(series, qs))
        ok = True
        for t in "CP":
            nets = [sum(q for (tt, _, e), q in chosen.items() if tt == t and e == d) for d in exps]
            ok = ok and suffix_ok(nets)
        if not ok:
            continue
        loss = max(0, -min(payoff_at(chosen, s) for s in strikes))
        left = sum(naked[x] * (q - holdings[x]) for x, q in chosen.items() if holdings[x] < 0)
        cost = loss + left
        best = cost if best is None else min(best, cost)
    return best


def choices(holdings, members):
    ranges = [range(0, holdings[x] + 1) if holdings[x] > 0 else range(holdings[x], 1) for x in members]
    return product(*ranges)


def dp_strikes(holdings, naked, strikes, exps):
    """Walk the strikes (proofs.md, "Strike dynamic program"), carrying the net contracts
    of each type at each expiration, and Y, X of that section. With E expirations and N
    contracts held, a layer has at most (2N + 1)^(2E) count keys times the (X, Y) pairs."""
    m = len(strikes)
    ei = {d: i for i, d in enumerate(exps)}
    # state: (call nets tuple, put nets tuple, Y, X) -> least cost so far
    layer = {((0,) * len(exps), (0,) * len(exps), 0, 0): 0}
    for j, k in enumerate(strikes):
        members = [x for x in sorted(holdings) if x[1] == k]
        nxt = {}
        for (cn, pn, y, xv), cost in layer.items():
            for qs in choices(holdings, members):
                cn2, pn2 = list(cn), list(pn)
                add = 0
                for x, q in zip(members, qs):
                    (cn2 if x[0] == "C" else pn2)[ei[x[2]]] += q
                    if holdings[x] < 0:
                        add += naked[x] * (q - holdings[x])
                cum_c, cum_p = sum(cn2), sum(pn2)  # C_j and P'_j through strike j
                if j < m - 1:
                    d = strikes[j + 1] - k
                    y2 = y + cum_c * d
                    x2 = min(xv - cum_p * d, y2)
                else:
                    y2, x2 = y, xv
                key = (tuple(cn2), tuple(pn2), y2, x2)
                c2 = cost + add
                if key not in nxt or c2 < nxt[key]:
                    nxt[key] = c2
        layer = nxt
    best = None
    for (cn, pn, _, xv), cost in layer.items():
        if suffix_ok(list(cn)) and suffix_ok(list(pn)):
            total = cost + max(0, -xv)
            best = total if best is None else min(best, total)
    return best


def dp_expirations(holdings, naked, strikes, exps):
    """Walk the expirations from the latest, carrying the suffix net contracts of each
    type and the group's payoff at every strike. With m strikes, the payoffs take at most
    (2N * range + 1)^m values: polynomial in the contracts and the range for fixed m."""
    layer = {(0, 0, (0,) * len(strikes)): 0}
    for d in reversed(exps):
        members = [x for x in sorted(holdings) if x[2] == d]
        nxt = {}
        for (sc, sp, pay), cost in layer.items():
            for qs in choices(holdings, members):
                sc2, sp2 = sc, sp
                pay2 = list(pay)
                add = 0
                for x, q in zip(members, qs):
                    if x[0] == "C":
                        sc2 += q
                    else:
                        sp2 += q
                    for i, s in enumerate(strikes):
                        pay2[i] += q * (max(s - x[1], 0) if x[0] == "C" else max(x[1] - s, 0))
                    if holdings[x] < 0:
                        add += naked[x] * (q - holdings[x])
                if sc2 < 0 or sp2 < 0:
                    continue  # the suffix condition at d fails
                key = (sc2, sp2, tuple(pay2))
                c2 = cost + add
                if key not in nxt or c2 < nxt[key]:
                    nxt[key] = c2
        layer = nxt
    best = None
    for (sc, sp, pay), cost in layer.items():
        if sc == 0 and sp == 0:
            total = cost + max(0, -min(pay))
            best = total if best is None else min(best, total)
    return best


def min_cost_flow(n, arcs, supply):
    """Least cost of a flow meeting `supply` (node -> net outflow, summing to 0) on arcs
    (u, v, capacity, cost >= 0), or None if none exists. Successive shortest paths with
    Bellman-Ford; for the small networks here."""
    graph = [[] for _ in range(n + 2)]
    src, snk = n, n + 1

    def link(u, v, cap, cost):
        graph[u].append([v, cap, cost, len(graph[v])])
        graph[v].append([u, 0, -cost, len(graph[u]) - 1])

    for u, v, cap, cost in arcs:
        link(u, v, cap, cost)
    need = 0
    for v, b in supply.items():
        if b > 0:
            link(src, v, b, 0)
            need += b
        elif b < 0:
            link(v, snk, -b, 0)
    total = sent = 0
    while sent < need:
        dist = [None] * (n + 2)
        prev = [None] * (n + 2)
        dist[src] = 0
        for _ in range(n + 2):
            moved = False
            for u in range(n + 2):
                if dist[u] is None:
                    continue
                for i, (v, cap, cost, _) in enumerate(graph[u]):
                    if cap > 0 and (dist[v] is None or dist[u] + cost < dist[v]):
                        dist[v] = dist[u] + cost
                        prev[v] = (u, i)
                        moved = True
            if not moved:
                break
        if dist[snk] is None:
            return None
        push, v = need - sent, snk
        while v != src:
            u, i = prev[v]
            push = min(push, graph[u][i][1])
            v = u
        v = snk
        while v != src:
            u, i = prev[v]
            graph[u][i][1] -= push
            graph[v][graph[u][i][3]][1] += push
            v = u
        sent += push
        total += push * dist[snk]
    return total


def type_savings(holdings, naked, strikes, exps, t, y):
    """Most standalone requirement saved by shorts of type t when the group's net
    contracts at each strike are y (proofs.md, "Several expirations": a min-cost flow
    between strike and expiration nodes). None if no group has these strike totals."""
    m, e_count = len(strikes), len(exps)
    si = {k: i for i, k in enumerate(strikes)}
    ei = {d: m + i for i, d in enumerate(exps)}
    supply = {i: -y[i] for i in range(m)}  # net outflow; a strike with net long y > 0 takes in y
    arcs = []
    base = 0
    for i in range(e_count - 1):
        arcs.append((m + i, m + i + 1, 10 ** 9, 0))  # W_{e+1}: suffix slack, e -> e + 1
    for (tt, k, d), q in holdings.items():
        if tt != t:
            continue
        if q > 0:
            arcs.append((ei[d], si[k], q, 0))  # long: expiration -> strike
        else:
            # A short is a strike -> expiration arc of cost -U. Saturate it up front and
            # offer its reverse at cost +U, to take shorts back out.
            u = naked[(tt, k, d)]
            base += u * -q
            supply[si[k]] = supply.get(si[k], 0) + q  # it sends -q more out of the strike
            supply[ei[d]] = supply.get(ei[d], 0) - q
            arcs.append((ei[d], si[k], -q, u))
    cost = min_cost_flow(m + e_count, arcs, {v: b for v, b in supply.items() if b})
    return None if cost is None else base - cost


def flow_by_strike_totals(holdings, naked, strikes, exps):
    """Enumerate the group's net call and put contracts at each strike; price the
    maximum loss from those alone and the savings by a min-cost flow per type. With m
    strikes and N contracts this is (2N + 1)^(2m) flows."""
    ranges = {}
    for t in "CP":
        for k in strikes:
            lo = sum(q for (tt, kk, _), q in holdings.items() if tt == t and kk == k and q < 0)
            hi = sum(q for (tt, kk, _), q in holdings.items() if tt == t and kk == k and q > 0)
            ranges[(t, k)] = range(lo, hi + 1)
    keys = sorted(ranges)
    held = sum(naked[x] * -q for x, q in holdings.items() if q < 0)
    best = None
    for ys in product(*[ranges[x] for x in keys]):
        y = dict(zip(keys, ys))
        if sum(y[("C", k)] for k in strikes) or sum(y[("P", k)] for k in strikes):
            continue
        saved = 0
        for t in "CP":
            v = type_savings(holdings, naked, strikes, exps, t, [y[(t, k)] for k in strikes])
            if v is None:
                saved = None
                break
            saved += v
        if saved is None:
            continue
        pay = [sum(y[("C", k)] * max(s - k, 0) + y[("P", k)] * max(k - s, 0) for k in strikes)
               for s in strikes]
        cost = held - saved + max(0, -min(pay))
        best = cost if best is None else min(best, cost)
    return best


def random_book(rng, n_strikes, n_exps, n_series, most):
    strikes = sorted(rng.sample(range(10, 10 + 6 * n_strikes), n_strikes))
    exps = list(range(n_exps))
    holdings = {}
    # Half the books lean their shorts to later expirations, where the expiration
    # condition bites.
    lean = rng.random() < 0.5
    n_series = min(n_series, 2 * n_strikes * n_exps)
    while len(holdings) < n_series:
        x = (rng.choice("CP"), rng.choice(strikes), rng.choice(exps))
        if x not in holdings:
            q = rng.randint(1, most)
            p_long = (1 - (x[2] + 0.5) / n_exps) if lean else 0.5
            holdings[x] = q if rng.random() < p_long else -q
    naked = {x: rng.randint(1, 30) for x, q in holdings.items() if q < 0}
    # The class's strike set: the member strikes are enough (proofs.md, item 1).
    used = sorted({x[1] for x in holdings})
    return holdings, naked, used, exps


def check_expirations(rng, count, most):
    tested = binding = 0
    for _ in range(count):
        holdings, naked, strikes, exps = random_book(
            rng, rng.randint(2, 5), rng.randint(1, 4), rng.randint(2, 7), most)
        want = brute(holdings, naked, strikes, exps)
        a = dp_strikes(holdings, naked, strikes, exps)
        b = dp_expirations(holdings, naked, strikes, exps)
        f = flow_by_strike_totals(holdings, naked, strikes, exps)
        check(a == want and b == want and f == want,
              f"expirations: brute {want} strike DP {a} expiration DP {b} flow {f} {holdings} {naked}")
        tested += 1
        # Does the expiration condition matter? Merge every expiration into one.
        merged = {}
        for (t, k, _), q in holdings.items():
            merged[(t, k, 0)] = merged.get((t, k, 0), 0) + q
        if len(merged) == len(holdings) and brute(merged, {(t, k, 0): u for (t, k, _), u in naked.items()}, strikes, [0]) != want:
            binding += 1
    print(f"several expirations: {tested} random books ({binding} where the expiration condition "
          f"changes the minimum), both dynamic programs and the flow method equal exhaustive search")


def main():
    quick = "--quick" in sys.argv
    rng = random.Random(20261127)
    if quick:
        check_premiums(rng, [(2, 8, 20)], rho=100)
        check_expirations(rng, 150, 2)
    else:
        check_premiums(rng, [(2, 10, 150), (3, 9, 60), (4, 9, 10)], rho=100)
        check_premiums(rng, [(2, 10, 30)], rho=10 ** 6)
        check_expirations(rng, 3000, 3)
    if failures:
        print(f"{failures} checks FAILED")
        sys.exit(1)
    print("all checks passed")


if __name__ == "__main__":
    main()
