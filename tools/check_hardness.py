#!/usr/bin/env python3
"""Brute-force checks of the results in docs/proofs.md, "Hardness".

Each reduction turns an instance of a known NP-complete problem into a margin
instance. This script builds small instances, solves the source problem and the
margin problem by exhaustive search, and checks that the answers agree as the
theorems say. The margin side does not use the proofs' arguments: it enumerates
spreads and evaluates the maximum potential loss directly from intrinsic values
(rules.md R2). It also runs the dynamic program of Proposition 5 against the same
exhaustive search.

    python3 tools/check_hardness.py            # about half a minute
    python3 tools/check_hardness.py --quick    # about a second, fewer cases

Python 3.9 or later, standard library only. Exit status 0 means every check passed.
"""

import random
import sys
import time
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product

# ---------------------------------------------------------------------------
# Rules. Calls on one underlying, one expiration, one deliverable; per share.
# ---------------------------------------------------------------------------


def max_loss(legs):
    """Maximum potential loss of a balanced set of calls (rules.md R2).

    legs: iterable of (strike, signed contracts), long positive. Nets the intrinsic
    values at each member strike and returns the largest net loss, or 0.
    """
    legs = [(k, q) for k, q in legs if q]
    assert sum(q for _, q in legs) == 0, "a spread balances within calls (R1 d)"
    worst = 0
    for s, _ in legs:
        worst = min(worst, sum(q * max(s - k, 0) for k, q in legs))
    return -worst


def uncovered_call(strike, premium, underlying):
    """Uncovered short call at stock rates (rules.md R3): 100% of the premium plus the
    greater of 20% of the underlying less the out-of-the-money amount, and 10% of it."""
    otm = max(strike - underlying, 0)
    return premium + max(Fraction(1, 5) * underlying - otm, Fraction(1, 10) * underlying)


def spread_requirement(legs, naked, lesser_of):
    """Requirement of one spread net of its longs' premiums: its maximum loss, or (R2,
    lesser_of=True) the lesser of that and the uncovered requirement of its shorts."""
    loss = max_loss(legs.items())
    if not lesser_of:
        return loss
    return min(loss, sum(naked[k] * -q for k, q in legs.items() if q < 0))


# ---------------------------------------------------------------------------
# Exact minimum over a set of spreads.
# ---------------------------------------------------------------------------


def min_requirement(position, spreads):
    """Exact minimum total requirement of splitting `position` (strike -> signed
    contracts) into the given spreads. Every short contract lies in exactly one spread
    (an uncovered short is a one-leg spread); long contracts left over cost nothing.

    spreads: list of (legs, requirement), legs a dict strike -> signed contracts.
    Depth-first over the lowest strike that still has a short, memoized on the
    remaining position.
    """
    strikes = sorted(position)
    index = {k: i for i, k in enumerate(strikes)}
    by_short = [[] for _ in strikes]
    for legs, req in spreads:
        vec = [0] * len(strikes)
        for k, q in legs.items():
            vec[index[k]] = q
        for i, q in enumerate(vec):
            if q < 0:
                by_short[i].append((tuple(vec), req))

    @lru_cache(maxsize=None)
    def go(state):
        pivot = next((i for i, q in enumerate(state) if q < 0), None)
        if pivot is None:
            return 0
        best = None
        for vec, req in by_short[pivot]:
            if all((v <= r) if v > 0 else (v >= r) for r, v in zip(state, vec) if v):
                total = req + go(tuple(r - v for r, v in zip(state, vec)))
                if best is None or total < best:
                    best = total
        assert best is not None, "the uncovered short always fits"
        return best

    return go(tuple(position[k] for k in strikes))


def named_spreads(position, naked, lesser_of, equal_wings=False):
    """The named call spreads of the legacy rules (NYSE Rule 431(f)(2)(C) as Matsypura
    and Timkovsky use it): uncovered short, bull and bear vertical, long and short
    butterfly, long and short condor. Butterflies need equal intervals between their
    strikes, of any width. So do condors, between all four strikes; with equal_wings
    only the two outer intervals of a condor have to be equal.
    """
    strikes = sorted(position)
    have = set(strikes)
    out = [({k: -1}, naked[k]) for k in strikes]
    shapes = []
    for k1, k2 in combinations(strikes, 2):
        shapes.append({k1: 1, k2: -1})  # bull call spread (debit)
        shapes.append({k1: -1, k2: 1})  # bear call spread (credit)
        d = k2 - k1
        if k2 + d in have:
            shapes.append({k1: 1, k2: -2, k2 + d: 1})  # long butterfly
            shapes.append({k1: -1, k2: 2, k2 + d: -1})  # short butterfly
        for k3 in strikes:
            if k3 > k2 and k3 + d in have and (equal_wings or k3 == k2 + d):
                shapes.append({k1: 1, k2: -1, k3: -1, k3 + d: 1})  # long condor
                shapes.append({k1: -1, k2: 1, k3: 1, k3 + d: -1})  # short condor
    for legs in shapes:
        out.append((legs, spread_requirement(legs, naked, lesser_of)))
    return out


def leg_limited_spreads(position, naked, max_series, lesser_of):
    """Every balanced set of calls on at most `max_series` series that fits inside the
    position, each priced at its maximum loss (today's rule with a leg limit)."""
    strikes = sorted(position)
    out = [({k: -1}, naked[k]) for k in strikes if position[k] < 0]
    for r in range(2, max_series + 1):
        for combo in combinations(strikes, r):
            signs = [1 if position[k] > 0 else -1 for k in combo]
            if len(set(signs)) == 1:
                continue
            for qty in product(*[range(1, abs(position[k]) + 1) for k in combo]):
                if sum(s * q for s, q in zip(signs, qty)) != 0:
                    continue
                legs = {k: s * q for k, s, q in zip(combo, signs, qty)}
                out.append((legs, spread_requirement(legs, naked, lesser_of)))
    return out


def adjacent_spreads(position, naked, lesser_of, step):
    """Named call spreads when butterflies and condors are recognized only on consecutive
    points of one evenly spaced grid (Proposition 5). Verticals join any two strikes.
    position has an entry, possibly 0, for every grid point."""
    strikes = sorted(position)
    out = [({k: -1}, naked[k]) for k in strikes]
    shapes = []
    for k1, k2 in combinations(strikes, 2):
        shapes.append({k1: 1, k2: -1})
        shapes.append({k1: -1, k2: 1})
    for k in strikes:
        if k + 2 * step in position:
            shapes.append({k: 1, k + step: -2, k + 2 * step: 1})
            shapes.append({k: -1, k + step: 2, k + 2 * step: -1})
        if k + 3 * step in position:
            shapes.append({k: 1, k + step: -1, k + 2 * step: -1, k + 3 * step: 1})
            shapes.append({k: -1, k + step: 1, k + 2 * step: 1, k + 3 * step: -1})
    for legs in shapes:
        out.append((legs, spread_requirement(legs, naked, lesser_of)))
    return out


def adjacent_minimum(position, naked, lesser_of, step):
    """The dynamic program in the proof of Proposition 5. It walks the grid upward and
    carries only counts: bull spreads waiting for their short, bear spreads waiting for
    their long (each costs one grid interval per step), and the butterflies and condors
    begun at most three points back, by kind and by the legs they still need.
    """
    strikes = sorted(position)
    last = len(strikes) - 1

    def price(legs):
        return spread_requirement(legs, naked, lesser_of)

    @lru_cache(maxsize=None)
    def go(j, bulls, bears, pending):
        # pending counts spreads by the leg they need at strike j: long butterflies (two
        # shorts in the middle, then the top long), short butterflies (two longs, then
        # the top short), long condors (short, short, long), short condors (long, long,
        # short).
        lb_mid, lb_top, sb_mid, sb_top, lc_2, lc_3, lc_4, sc_2, sc_3, sc_4 = pending
        if j > last:
            return 0 if bears == 0 and not any(pending) else None
        k, q = strikes[j], position[strikes[j]]
        need_long = lb_top + 2 * sb_mid + lc_4 + sc_2 + sc_3
        need_short = 2 * lb_mid + sb_top + lc_2 + lc_3 + sc_4
        best = None

        def consider(cost, bulls2, bears2, pending2):
            nonlocal best
            rest = go(j + 1, bulls2, bears2, pending2)
            if rest is not None:
                total = cost + bears2 * step + rest if j < last else cost + rest
                if best is None or total < best:
                    best = total

        if q >= 0:
            free = q - need_long
            if need_short or free < 0:
                return None
            for butterflies in range(free + 1 if j + 2 <= last else 1):
                for condors in range(free - butterflies + 1 if j + 3 <= last else 1):
                    for closed in range(min(bears, free - butterflies - condors) + 1):
                        # Whatever is left waits as the long of a bull spread, or goes unused.
                        opened = free - butterflies - condors - closed
                        consider(0, bulls + opened, bears - closed,
                                 (butterflies, lb_mid, 0, sb_mid, condors, lc_2, lc_3, 0, sc_2, sc_3))
        else:
            free = -q - need_short
            if need_long or free < 0:
                return None
            butterfly = price({k: -1, k + step: 2, k + 2 * step: -1}) if j + 2 <= last else None
            condor = price({k: -1, k + step: 1, k + 2 * step: 1, k + 3 * step: -1}) if j + 3 <= last else None
            for butterflies in range(free + 1 if butterfly is not None else 1):
                for condors in range(free - butterflies + 1 if condor is not None else 1):
                    for closed in range(min(bulls, free - butterflies - condors) + 1):
                        for opened in range(free - butterflies - condors - closed + 1):
                            uncovered = free - butterflies - condors - closed - opened
                            cost = uncovered * naked[k]
                            if butterflies:
                                cost += butterflies * butterfly
                            if condors:
                                cost += condors * condor
                            consider(cost, bulls - closed, bears + opened,
                                     (0, lb_mid, butterflies, sb_mid, 0, lc_2, lc_3, condors, sc_2, sc_3))
        return best

    return go(0, 0, 0, (0,) * 10)


def one_group_min(longs, shorts, naked):
    """Exact minimum for the solver's model (spec §2, one flexible group): choose whole
    contracts for one balanced group; pay the group's maximum loss plus the uncovered
    requirement of every short left out. longs, shorts: strike -> contracts held."""
    ls, ss = sorted(longs), sorted(shorts)
    best = None
    for lq in product(*[range(longs[k] + 1) for k in ls]):
        for sq in product(*[range(shorts[k] + 1) for k in ss]):
            if sum(sq) != sum(lq):
                continue
            legs = list(zip(ls, lq)) + [(k, -q) for k, q in zip(ss, sq)]
            cost = max_loss(legs) + sum(naked[k] * (shorts[k] - q) for k, q in zip(ss, sq))
            if best is None or cost < best:
                best = cost
    return best


# ---------------------------------------------------------------------------
# Source problems, by exhaustive search.
# ---------------------------------------------------------------------------


def n3dm(a, b, c, bound):
    """Numerical 3-dimensional matching (Garey and Johnson SP16): can a, b, c be split
    into triples, one element of each, that each sum to `bound`?"""
    n = len(a)
    for pb in set(permutations(b)):
        for pc in set(permutations(c)):
            if all(a[i] + pb[i] + pc[i] == bound for i in range(n)):
                return True
    return False


def subset_sums(a, size=None):
    """Sums reachable by subsets of a (of exactly `size` elements when given)."""
    reach = {(0, 0)}
    for v in a:
        reach |= {(c + 1, s + v) for c, s in reach}
    return {s for c, s in reach if size is None or c == size}


# ---------------------------------------------------------------------------
# The reductions, as docs/proofs.md states them.
# ---------------------------------------------------------------------------

TRIVIAL_NO = {1: -1}  # one uncovered short call: no pairing has requirement zero


def add(position, strike, qty):
    position[strike] = position.get(strike, 0) + qty


def naked_requirements(position):
    """A positive uncovered requirement for every strike, from R3 with a made-up
    underlying price and premiums. Theorems 1 and 2 only need them positive."""
    strikes = sorted(position)
    underlying = Fraction(strikes[len(strikes) // 2])
    return {k: uncovered_call(k, max(underlying - k, 0) + 1, underlying) for k in strikes}


def scale(a, b, c, bound):
    """M = 6nW, with W the largest of the bound and the sizes."""
    return 6 * len(a) * max([bound] + a + b + c)


def total_is_right(a, b, c, bound):
    return sum(a) + sum(b) + sum(c) == len(a) * bound


def butterfly_instance(a, b, c, bound):
    """Theorem 1, and Theorem 2 for three series: long one call at 2a_i, short two at
    M + bound - b_j, long one at 2M + 2c_k. Then x + z = 2y exactly when
    a_i + b_j + c_k = bound."""
    m = scale(a, b, c, bound)
    position = {}
    for v in a:
        add(position, 2 * v, 1)
    for v in b:
        add(position, m + bound - v, -2)
    for v in c:
        add(position, 2 * m + 2 * v, 1)
    return position


def condor_instance(a, b, c, bound):
    """Theorem 2 for four series: long one call at a_i, short one at pM + bound - b_j,
    short n at qM, long one at (p+q)M + c_k, with p = n+1 and q = n+2. Then
    x + z = y + y' exactly when a_i + b_j + c_k = bound."""
    n = len(a)
    m = scale(a, b, c, bound)
    p, q = n + 1, n + 2
    position = {}
    for v in a:
        add(position, v, 1)
    for v in b:
        add(position, p * m + bound - v, -1)
    add(position, q * m, -n)
    for v in c:
        add(position, (p + q) * m + v, 1)
    return position


def subset_sum_instance(a, target):
    """Theorem 3: long one call at top - target, long n at top, short one at top - a_i
    with standalone cost a_i / 2. Every a_i is below the target."""
    top = target + 50
    longs = {top - target: 1, top: len(a)}
    shorts, naked = {}, {}
    for v in a:
        add(shorts, top - v, 1)
        naked[top - v] = Fraction(v, 2)
    return longs, shorts, naked, Fraction(sum(a) - target, 2)


def rule_priced_instance(a, k, t):
    """Theorem 4: the reduction of Theorem 3 with every short priced by R3 from call
    prices that are linear in the strike. The question is whether exactly k of the
    numbers a sum to t. Returns the instance and the floor on its minimum."""
    total = sum(a)
    assert 2 <= k <= len(a) and 1 <= t <= total
    shift = 8 * total
    sized = [v + shift for v in a]
    target = t + k * shift
    beta = Fraction(1, 2 * k)
    top_price = Fraction(1)  # the call price at the top strike
    underlying = 2 * (top_price + beta * target)
    low = -(-11 * underlying // 10)  # lowest strike: at least 10% out of the money
    top = low + target

    def price(strike):
        return top_price + beta * (top - strike)

    longs = {low: 1, top: len(a)}
    shorts, naked = {}, {}
    for v in sized:
        strike = top - v
        add(shorts, strike, 1)
        naked[strike] = uncovered_call(strike, price(strike), underlying)
    c = top_price + underlying / 10
    # What the proof relies on: the requirement is c + beta * size; every strike is at
    # least 10% out of the money and the shorts lie above the lowest strike; prices are
    # positive, fall with the strike and stay below the stock; inequalities (I1), (I2).
    assert all(naked[top - v] == c + beta * v for v in sized)
    assert all(low < strike for strike in shorts) and low >= Fraction(11, 10) * underlying
    assert 0 < price(top) and price(low) <= underlying
    assert shift > total and (1 - beta) * (shift - t) > c
    floor = sum(naked[top - v] for v in sized) - (c * k + beta * target)
    return longs, shorts, naked, floor


def random_n3dm(rng, n, top):
    """A triple-matching instance. One in four is not planted: 3n sizes that start at 1 and
    grow by random lumps until the total is n * bound, so sizes above the bound occur and
    a matching is rare. The others are a planted yes-instance, then (60% of the time) a
    few unit moves inside one set, which keep the total at n * bound and often destroy
    every matching; in one of six of those a single size is also changed by itself, so
    the total is off and no matching can exist."""
    bound = rng.randint(6, top)
    if rng.random() < 1 / 4:
        sizes = [1] * (3 * n)
        left = n * bound - 3 * n
        while left:
            lump = rng.randint(1, min(left, bound))
            sizes[rng.randrange(3 * n)] += lump
            left -= lump
        return sizes[:n], sizes[n:2 * n], sizes[2 * n:], bound
    a, b, c = [], [], []
    for _ in range(n):
        x = rng.randint(1, bound - 2)
        y = rng.randint(1, bound - x - 1)
        a.append(x), b.append(y), c.append(bound - x - y)
    if rng.random() < 0.6:
        for _ in range(rng.randint(1, 3)):
            s = rng.choice([a, b, c])
            i, j = rng.sample(range(n), 2)
            if s[i] > 1:
                s[i] -= 1
                s[j] += 1
    if rng.random() < 1 / 6:
        s = rng.choice([a, b, c])
        i = rng.randrange(n)
        s[i] = max(1, s[i] + rng.choice([-2, -1, 1, 2]))
    for s in (a, b, c):
        rng.shuffle(s)
    return a, b, c, bound


# ---------------------------------------------------------------------------
# Checks.
# ---------------------------------------------------------------------------

failures = 0


def check(ok, what):
    global failures
    if not ok:
        failures += 1
        print(f"  FAIL: {what}")


def check_named_values():
    """The named spreads priced by max_loss reproduce the legacy rule's figures: debit
    spreads 0, credit spreads one interval (Matsypura and Timkovsky 05/2010, formula (1)),
    and two uneven butterflies from the Cboe manual."""
    cases = [
        ({10: 1, 20: -1}, 0),  # bull call
        ({10: -1, 20: 1}, 10),  # bear call
        ({10: 1, 20: -2, 30: 1}, 0),  # long butterfly
        ({10: -1, 20: 2, 30: -1}, 10),  # short butterfly
        ({10: 1, 20: -1, 30: -1, 40: 1}, 0),  # long condor
        ({10: -1, 20: 1, 30: 1, 40: -1}, 10),  # short condor
        ({45: 1, 55: -2, 60: 1}, 0),  # manual p. 37: 45/55/60, no loss
        ({545: 1, 550: -2, 565: 1}, 10),  # manual p. 54: 545/550/565, $1,000 a contract
    ]
    for legs, want in cases:
        check(spread_requirement(legs, {}, False) == want, f"named value {legs}")
    print(f"named spread values: {len(cases)} checked")


def check_theorem_1(rng, cases):
    """Named spreads with equal intervals: the minimum is zero exactly when the triple
    matching exists."""
    yes = no = off = big = 0
    least = None
    for n, top, count in cases:
        for _ in range(count):
            a, b, c, bound = random_n3dm(rng, n, top)
            want = n3dm(a, b, c, bound)
            big += max(a + b + c) > bound
            position = butterfly_instance(a, b, c, bound)
            naked = naked_requirements(position)
            for lesser_of in (False, True):
                got = min_requirement(position, named_spreads(position, naked, lesser_of))
                check((got == 0) == want, f"theorem 1: a={a} b={b} c={c} bound={bound} got {got}")
                if not want and not lesser_of:
                    least = got if least is None else min(least, got)
            if total_is_right(a, b, c, bound):
                # With no leg limit the whole position is one spread without loss, matching
                # or not: the hardness comes from the limit on legs.
                check(max_loss(position.items()) == 0, f"whole position: a={a} b={b} c={c} bound={bound}")
            else:
                off += 1
            yes += want
            no += not want
    print(f"theorem 1 (named spreads, equal intervals): {yes} yes and {no} no instances agree "
          f"({off} of the no instances have the wrong total, {big} have a size above the bound); "
          f"smallest positive minimum {least}")


def check_theorem_2(rng, cases):
    """Spreads of at most three, or at most four, series priced at maximum loss: zero
    exactly when the matching exists. The reduction first checks the total; when it is
    off there is no matching and it outputs one uncovered short call."""
    for series, build in ((3, butterfly_instance), (4, condor_instance)):
        yes = no = off = big = 0
        for n, top, count in cases:
            for _ in range(count):
                a, b, c, bound = random_n3dm(rng, n, top)
                want = n3dm(a, b, c, bound)
                right = total_is_right(a, b, c, bound)
                position = build(a, b, c, bound) if right else TRIVIAL_NO
                naked = naked_requirements(position)
                for lesser_of in (False, True):
                    got = min_requirement(position, leg_limited_spreads(position, naked, series, lesser_of))
                    check((got == 0) == want,
                          f"theorem 2, {series} series: a={a} b={b} c={c} bound={bound} got {got}")
                    # The named lists: Theorem 1's on the butterfly instance, and on the condor
                    # instance the list whose condors need only equal wings (the remark after
                    # Theorem 1).
                    got = min_requirement(position, named_spreads(position, naked, lesser_of, series == 4))
                    check((got == 0) == want,
                          f"theorem 2, named list, {series} series: a={a} b={b} c={c} bound={bound} got {got}")
                yes += want
                no += not want
                off += not right
                big += right and max(a + b + c) > bound
        print(f"theorem 2 (at most {series} series, maximum loss): {yes} yes and {no} no instances agree "
              f"({off} of the no instances have the wrong total, {big} have a size above the bound)")


def check_examples():
    """The two worked examples in docs/proofs.md."""
    a, b, c, bound = [1, 2], [3, 1], [3, 4], 7
    position = butterfly_instance(a, b, c, bound)
    check(position == {2: 1, 4: 1, 88: -2, 90: -2, 174: 1, 176: 1}, f"first example position {position}")
    check(n3dm(a, b, c, bound), "first example has a matching")
    naked = naked_requirements(position)
    named = named_spreads(position, naked, False)
    check(min_requirement(position, named) == 0, "first example is zero")
    verticals = [(legs, req) for legs, req in named if len(legs) <= 2]
    print(f"example with a matching: named spreads 0, verticals only {min_requirement(position, verticals)}")

    # No matching, and yet four-series spreads priced at maximum loss reach zero on the
    # butterfly instance. This is why Theorem 2 uses a different instance for four series.
    a, b, c, bound = [1, 2], [5, 1], [3, 2], 7
    position = butterfly_instance(a, b, c, bound)
    check(position == {2: 1, 4: 1, 86: -2, 90: -2, 172: 1, 174: 1}, f"second example position {position}")
    check(not n3dm(a, b, c, bound) and total_is_right(a, b, c, bound), "second example has no matching")
    naked = naked_requirements(position)
    named = min_requirement(position, named_spreads(position, naked, False))
    three = min_requirement(position, leg_limited_spreads(position, naked, 3, False))
    four = min_requirement(position, leg_limited_spreads(position, naked, 4, False))
    check(named > 0 and three > 0 and four == 0, f"second example: named {named}, three {three}, four {four}")
    check(max_loss({2: 1, 86: -1, 90: -1, 174: 1}.items()) == 0, "uneven condor 2/86/90/174 has no loss")
    check(max_loss({4: 1, 86: -1, 90: -1, 172: 1}.items()) == 0, "uneven condor 4/86/90/172 has no loss")
    wings = min_requirement(position, named_spreads(position, naked, False, equal_wings=True))
    check(wings == 0, "second example: equal-wing condors reach zero on the butterfly instance")
    condor = condor_instance(a, b, c, bound)
    on_condor = min_requirement(condor, leg_limited_spreads(condor, naked_requirements(condor), 4, False))
    check(on_condor > 0, "second example on the condor instance")
    print(f"example without a matching, butterfly instance: named spreads {named}, at most 3 series {three}, "
          f"at most 4 series {four}; condor instance, at most 4 series: {on_condor}")


def check_proposition_5(rng, count):
    """Butterflies and condors on consecutive grid points only: the dynamic program over
    the strikes gives the same minimum as the search over every pairing."""
    for _ in range(count):
        points, step = rng.randint(3, 8), rng.choice([1, 5])
        position = {10 + i * step: rng.choice([-3, -2, -1, -1, 0, 1, 1, 2, 3]) for i in range(points)}
        naked = naked_requirements(position)
        if rng.random() < 0.3:  # cheap uncovered shorts, so the lesser-of clause binds
            naked = {k: v / 20 for k, v in naked.items()}
        for lesser_of in (False, True):
            want = min_requirement(position, adjacent_spreads(position, naked, lesser_of, step))
            got = adjacent_minimum(position, naked, lesser_of, step)
            check(got == want, f"proposition 5: {position} lesser_of={lesser_of} got {got} want {want}")
    print(f"proposition 5 (butterflies and condors on adjacent strikes): {count} positions, "
          f"dynamic program and search agree")


def check_theorem_3(rng, count, most):
    """One maximum-loss group, free standalone costs: the minimum equals
    (sum - target) / 2 exactly when a subset sums to the target."""
    yes = no = 0
    for _ in range(count):
        n = rng.randint(2, most)
        a = [rng.randint(1, 30) for _ in range(n)]
        if rng.random() < 0.5:
            target = sum(rng.sample(a, rng.randint(1, n)))
        else:
            target = rng.randint(1, sum(a))
        # The reduction drops numbers above the target and answers yes at once when one
        # equals it; what is left to check is every a_i below the target.
        a = [v for v in a if v < target]
        if not a:
            continue
        want = target in subset_sums(a)
        longs, shorts, naked, floor = subset_sum_instance(a, target)
        got = one_group_min(longs, shorts, naked)
        check(got >= floor and (got == floor) == want, f"theorem 3: a={a} target={target} got {got}")
        yes += want
        no += not want
    print(f"theorem 3 (one group, free standalone costs): {yes} yes and {no} no instances agree")


def check_theorem_4(rng, count, most):
    """One maximum-loss group, shorts priced by R3: the minimum equals the floor exactly
    when k of the numbers sum to the target."""
    yes = no = 0
    for _ in range(count):
        n = rng.randint(3, most)
        a = [rng.randint(1, 12) for _ in range(n)]
        k = rng.randint(2, n - 1)
        if rng.random() < 0.5:
            t = sum(rng.sample(a, k))
        else:
            t = rng.randint(1, sum(a))
        want = t in subset_sums(a, size=k)
        longs, shorts, naked, floor = rule_priced_instance(a, k, t)
        got = one_group_min(longs, shorts, naked)
        check(got >= floor and (got == floor) == want, f"theorem 4: a={a} k={k} t={t} got {got} floor {floor}")
        yes += want
        no += not want
    print(f"theorem 4 (one group, shorts priced by R3): {yes} yes and {no} no instances agree")


def main():
    quick = "--quick" in sys.argv
    rng = random.Random(20261126)
    start = time.time()
    check_named_values()
    check_examples()
    check_theorem_1(rng, [(2, 9, 60), (3, 9, 40)] if quick else [(2, 10, 400), (3, 10, 400), (4, 10, 150), (5, 10, 50)])
    check_theorem_2(rng, [(2, 9, 30), (3, 9, 6)] if quick else [(2, 9, 300), (3, 9, 150), (4, 9, 50)])
    check_theorem_3(rng, 200 if quick else 2000, 7 if quick else 9)
    check_theorem_4(rng, 100 if quick else 1500, 6 if quick else 8)
    check_proposition_5(rng, 60 if quick else 600)
    print(f"{'FAILED' if failures else 'all checks passed'} in {time.time() - start:.1f} s")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
