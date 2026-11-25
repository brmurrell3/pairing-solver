# Independent check of a fixture file: recomputes netted intrinsic values at each strike,
# maximum potential loss, requirement (max loss + long premiums), short proceeds, margin
# call, and validity under the three expiry_rule policies, then compares with the file.
# Written separately from the C++ engine so the fixtures are not checked by the code
# they test. Usage: python3 tools/check_fixtures.py <fixture.toml>
import sys, tomllib
cases = tomllib.load(open(sys.argv[1], "rb"))["case"]
def intrinsic(t, k, p): return max(p - k, 0) if t == "call" else max(k - p, 0)
def pairwise_ok(legs):
    # Hall condition for "each short pairs with a same-type long expiring on or after it":
    # for every date d, short units expiring at or after d <= long units expiring at or after d.
    for t in ("call", "put"):
        L = [(l["expiry"], l["qty"]) for l in legs if l["type"] == t and l["side"] == "long"]
        S = [(l["expiry"], l["qty"]) for l in legs if l["type"] == t and l["side"] == "short"]
        if sum(q for _, q in L) != sum(q for _, q in S): return False
        for d, _ in S:
            if sum(q for e, q in S if e >= d) > sum(q for e, q in L if e >= d): return False
    return True
fails = 0
for c in cases:
    m, legs = c["multiplier"], c["legs"]
    ks = sorted({l["strike"] for l in legs})
    sgn = lambda l: 1 if l["side"] == "long" else -1
    net = [round(sum(sgn(l) * l["qty"] * m * intrinsic(l["type"], l["strike"], p) for l in legs)) for p in ks]
    ml = max(0, -min(net))
    longs = [l for l in legs if l["side"] == "long"]; shorts = [l for l in legs if l["side"] == "short"]
    valid = {
        "pairwise": pairwise_ok(legs),
        "nearest_long": pairwise_ok(legs) and max(l["expiry"] for l in shorts) <= min(l["expiry"] for l in longs),
        "same_expiry": pairwise_ok(legs) and len({l["expiry"] for l in legs}) == 1,
    }
    got = {"netted": net, "max_loss": ml, "valid": valid}
    if all("premium" in l for l in legs):
        got["requirement"] = round(ml + sum(l["premium"] * m * l["qty"] for l in longs), 2)
        got["short_proceeds"] = round(sum(l["premium"] * m * l["qty"] for l in shorts), 2)
        got["margin_call"] = round(got["requirement"] - got["short_proceeds"], 2)
    bad = {k: (c[k], v) for k, v in got.items() if k in c and c[k] != v}
    fails += bool(bad)
    print(("FAIL " if bad else "ok   ") + c["id"], bad if bad else "")
print(f"{len(cases) - fails}/{len(cases)} cases match")
