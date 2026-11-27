// The LP solver, branch-and-bound, model and checker on cases with known answers.

#include <algorithm>
#include <cmath>
#include <map>
#include <random>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "check.hpp"
#include "generate.hpp"
#include "pairing/solver.hpp"

using namespace pairing;

namespace {

const SolveOptions exact{1, 0};  // hand cases compare exact optima

Money usd(double d) { return Money::dollars(d); }
double dollars_of(Money m) { return static_cast<double>(m.micros()) / Money::per_dollar; }

bool near(double a, double b, double tol = 1e-9) { return std::fabs(a - b) <= tol * std::max(1.0, std::fabs(b)); }

void small_lps() {
    // max x + y  s.t.  x + 2y ≤ 4,  3x + y ≤ 6: optimum at (1.6, 1.2).
    Lp lp;
    lp.add_row(-lp_infinity, 4);
    lp.add_row(-lp_infinity, 6);
    lp.add_column(-1, 0, lp_infinity, {{0, 1}, {1, 3}});
    lp.add_column(-1, 0, lp_infinity, {{0, 2}, {1, 1}});
    DualSimplex s(lp);
    LpSolution sol = s.solve();
    CHECK(sol.status == LpStatus::optimal);
    CHECK(near(sol.objective, -2.8));
    CHECK(near(sol.x[0], 1.6) && near(sol.x[1], 1.2));
    CHECK(near(sol.row_dual[0], -0.4) && near(sol.row_dual[1], -0.2));

    Lp infeasible;
    infeasible.add_row(2, lp_infinity);
    infeasible.add_column(1, 0, 1, {{0, 1}});
    CHECK(DualSimplex(infeasible).solve().status == LpStatus::infeasible);

    Lp unbounded;
    unbounded.add_row(-lp_infinity, 1);
    unbounded.add_column(-1, 0, lp_infinity, {{0, 1}});
    unbounded.add_column(0, 0, lp_infinity, {{0, -1}});
    CHECK(DualSimplex(unbounded).solve().status == LpStatus::unbounded);

    // Equality rows and a free row.
    Lp eq;
    eq.add_row(3, 3);
    eq.add_row(-lp_infinity, lp_infinity);
    eq.add_column(2, 0, 10, {{0, 1}, {1, 1}});
    eq.add_column(1, 1, 10, {{0, 1}, {1, -1}});
    LpSolution e = DualSimplex(eq).solve();
    CHECK(e.status == LpStatus::optimal);
    CHECK(near(e.objective, 3) && near(e.x[1], 3));
}

// Random boxed LPs, checked by the optimality conditions: primal feasibility, and every
// nonbasic reduced cost signed for the bound it sits at. Also: duals match a finite
// difference, and a warm start after a bound change matches a cold solve.
void random_lps() {
    std::mt19937_64 rng(20261125);
    std::uniform_real_distribution<double> u(-1, 1);
    int solved = 0;
    for (int trial = 0; trial < 300; ++trial) {
        int m = 2 + trial % 12, n = 2 + (trial * 7) % 20;
        // Rows bracket A·x0 for a point x0 inside the column bounds, so most LPs are
        // feasible; a few rows are shifted off it to exercise infeasibility.
        Lp lp;
        std::vector<double> x0(n);
        for (int j = 0; j < n; ++j) {
            double lo = std::round(2 * u(rng)), up = lo + 1 + std::round(3 * std::fabs(u(rng)));
            lp.add_column(std::round(5 * u(rng)), lo, up);
            x0[j] = lo + (up - lo) * (u(rng) + 1) / 2;
        }
        for (int i = 0; i < m; ++i) {
            double act = 0;
            for (int j = 0; j < n; ++j)
                if (u(rng) > 0.2) {
                    double a = std::round(4 * u(rng) * 4) / 4;  // repeated values invite degeneracy
                    lp.columns[j].push_back({i, a});
                    act += a * x0[j];
                }
            double lo = act - 2 * std::fabs(u(rng)), up = act + 2 * std::fabs(u(rng));
            if (trial % 3 == 0 && i % 2 == 0) lo = up = act;  // equality rows
            if (trial % 10 == 9 && i == 0) lo = up = act + 1000;
            lp.add_row(lo, up);
        }
        DualSimplex s(lp);
        LpSolution sol = s.solve();
        CHECK(sol.status == LpStatus::optimal || sol.status == LpStatus::infeasible);
        if (sol.status != LpStatus::optimal) continue;
        ++solved;
        std::vector<double> act(m, 0);
        for (int j = 0; j < n; ++j) {
            CHECK(sol.x[j] >= lp.col_lo[j] - 1e-9 && sol.x[j] <= lp.col_up[j] + 1e-9);
            for (const auto& e : lp.columns[j]) act[e.row] += e.value * sol.x[j];
        }
        for (int i = 0; i < m; ++i) CHECK(act[i] >= lp.row_lo[i] - 1e-8 && act[i] <= lp.row_up[i] + 1e-8);
        // Reduced costs from the reported duals.
        for (int j = 0; j < n; ++j) {
            double d = lp.cost[j];
            for (const auto& e : lp.columns[j]) d -= sol.row_dual[e.row] * e.value;
            if (sol.basis.state[j] == 0) CHECK(std::fabs(d) < 1e-8);
            if (sol.basis.state[j] == 1 && lp.col_lo[j] != lp.col_up[j]) CHECK(d > -1e-8);
            if (sol.basis.state[j] == 2) CHECK(d < 1e-8);
        }

        // Warm start: tighten one column, re-solve from the optimal basis and cold.
        int j = trial % n;
        double mid = std::floor((sol.x[j] + lp.col_lo[j]) / 2);
        s.set_bounds(j, lp.col_lo[j], mid);
        LpSolution warm = s.solve(sol.basis);
        Lp tightened = lp;
        tightened.col_up[j] = mid;
        LpSolution cold = DualSimplex(tightened).solve();
        CHECK(warm.status == cold.status);
        if (warm.status == LpStatus::optimal && cold.status == LpStatus::optimal) CHECK(near(warm.objective, cold.objective));
    }
    CHECK(solved > 100);
}

// 0-1 and general-integer knapsacks against enumeration.
void knapsacks() {
    std::mt19937_64 rng(7);
    std::uniform_int_distribution<int> val(1, 30), wt(1, 12), ub(1, 3);
    for (int trial = 0; trial < 200; ++trial) {
        int n = 2 + trial % 6;
        std::vector<int> v(n), w(n), hi(n);
        Lp lp;
        int cap = 10 + trial % 15;
        lp.add_row(-lp_infinity, cap);
        for (int j = 0; j < n; ++j) {
            v[j] = val(rng);
            w[j] = wt(rng);
            hi[j] = ub(rng);
            lp.add_column(-v[j], 0, hi[j], {{0, static_cast<double>(w[j])}});
        }
        MipSolution mip = branch_and_bound(lp, std::vector<bool>(n, true), MipOptions{});
        int best = 0;
        std::vector<int> x(n, 0);
        for (;;) {
            int weight = 0, value = 0;
            for (int j = 0; j < n; ++j) {
                weight += w[j] * x[j];
                value += v[j] * x[j];
            }
            if (weight <= cap) best = std::max(best, value);
            int j = 0;
            while (j < n && x[j] == hi[j]) x[j++] = 0;
            if (j == n) break;
            ++x[j];
        }
        CHECK(mip.status == MipStatus::optimal);
        CHECK(near(-mip.objective, best));
        CHECK(mip.root.objective <= mip.objective + 1e-9);
        CHECK(mip.bound <= mip.objective + 1e-9);

        // A node limit is a reported stop, with a valid incumbent and bound.
        MipOptions one;
        one.node_limit = 1;
        one.start.assign(n, 0.0);
        MipSolution cut = branch_and_bound(lp, std::vector<bool>(n, true), one);
        CHECK(cut.status == MipStatus::node_limit || cut.status == MipStatus::optimal);
        CHECK(cut.nodes <= 1);
        CHECK(cut.x.size() == static_cast<std::size_t>(n));
        CHECK(cut.bound <= -best + 1e-9);
        CHECK(cut.objective >= -best - 1e-9);

        // A relative gap stops within that gap of the optimum.
        MipOptions loose;
        loose.rel_gap = 0.1;
        MipSolution g = branch_and_bound(lp, std::vector<bool>(n, true), loose);
        CHECK(g.status == MipStatus::optimal);
        CHECK(-g.objective >= best - 0.1 * best - 1e-9);
    }
}

OptionLeg option(OptionType t, std::int64_t qty, double strike, double value, Date expiry = {2026, 6, 19},
                 std::int64_t w = 100) {
    OptionLeg l;
    l.option.underlying = "XYZ";
    l.option.type = t;
    l.option.strike = usd(strike);
    l.option.expiry = expiry;
    l.option.deliverable = w;
    l.quantity = qty;
    l.value = usd(value);
    return l;
}

Portfolio book(std::vector<OptionLeg> legs, StockLeg stock = {}) {
    Portfolio p;
    p.options = std::move(legs);
    p.stock = stock;
    p.market = Market{usd(50), Date{2026, 1, 15}};
    return p;
}

void hand_cases() {
    RuleSet r;
    using T = OptionType;

    // A bull call spread: the spread beats margining the short alone.
    Portfolio bull = book({option(T::call, 1, 50, 3), option(T::call, -1, 55, 1)});
    Solution s = solve(bull, r, exact);
    CHECK_EQ(s.structures.size(), std::size_t{1});
    CHECK_EQ(s.total, spread(bull.options, bull.market, r).requirement.total());
    CHECK(s.total < s.all_standalone);
    CHECK(near(s.lp_bound, s.lp_objective));

    // Covered call: 200 shares against two short calls.
    Portfolio cc = book({option(T::call, -2, 55, 1)}, StockLeg{200, usd(50)});
    s = solve(cc, r, exact);
    CHECK_EQ(s.structures.size(), std::size_t{1});
    CHECK(s.structures[0].kind == StructureKind::covered_call);
    CHECK_EQ(s.total, covered_call(cc.stock, cc.options[0], cc.market, r).total());

    // Two verticals in one class form one group; its maximum loss is the sum of theirs,
    // so the total matches pricing the two separately.
    Portfolio two = book({option(T::call, 1, 50, 3), option(T::call, -1, 55, 1), option(T::put, 1, 50, 3),
                          option(T::put, -1, 45, 1)});
    s = solve(two, r, exact);
    Money sum = spread({two.options[0], two.options[1]}, two.market, r).requirement.total() +
                spread({two.options[2], two.options[3]}, two.market, r).requirement.total();
    CHECK(s.total <= sum);

    // A calendar with the short outlasting the long is no spread.
    Portfolio backwards = book({option(T::call, -1, 50, 3, {2026, 9, 18}), option(T::call, 1, 50, 2, {2026, 3, 20})});
    s = solve(backwards, r, exact);
    CHECK(s.structures.empty());
    CHECK_EQ(s.total, s.all_standalone);

    // Adjusted series: a long 150-share call against short 100-share calls balances only in
    // part. Whole contracts cannot pair one against one; lots of 1/50 can pair 0.96 of the
    // short.
    Portfolio adj = book({option(T::call, 1, 50, 3, {2026, 6, 19}, 150), option(T::call, -1, 55, 1)});
    Solution whole = solve(adj, r, exact);
    Solution fifty = solve(adj, r, SolveOptions{50, 0});
    CHECK(whole.structures.empty());
    CHECK(fifty.total < whole.total);
    CHECK(fifty.lp_bound <= dollars_of(fifty.total) + 1e-9);
    CHECK_THROWS(solve(adj, r, SolveOptions{100, 0}));  // 150 is not a multiple of 100

    // A European long box (R2b): long call and short put at 45, long put and short call at
    // 55. The model offers the box as a template; the solve can do no worse than the box
    // alone, and a box it uses is priced as Phase 1 prices it.
    auto euro = [&](T t, std::int64_t q, double k, double v) {
        OptionLeg l = option(t, q, k, v);
        l.option.style = Style::european;
        return l;
    };
    Portfolio box = book({euro(T::call, 2, 45, 6), euro(T::put, -2, 45, 1), euro(T::put, 2, 55, 6), euro(T::call, -2, 55, 1)});
    Model bm = build_model(box, r);
    int box_columns = 0;
    for (const auto& c : bm.column)
        if (c.kind == Model::Column::template_unit && bm.templates[c.index].kind == StructureKind::long_box) ++box_columns;
    CHECK_EQ(box_columns, 1);
    Money box_alone = european_long_box(box.options, r).requirement.total();
    s = solve(box, r, exact);
    CHECK(s.total <= box_alone);
    for (const auto& st : s.structures)
        if (st.kind == StructureKind::long_box) {
            CHECK_EQ(st.legs.size(), std::size_t{4});
            CHECK_EQ(s.total, box_alone);
        }

    // Integrality counterexamples (docs/proofs.md, "Integrality"). The continuous optimum
    // is not whole even with one deliverable, and even with calls only.
    {
        // An iron condor, one contract a leg: the LP keeps the call spread and half the
        // wider put spread, whose loss rides under the call spread's.
        Portfolio condor = book({option(T::call, -1, 107.5, 2.34, {2026, 4, 17}), option(T::call, 1, 115, 1.07, {2026, 4, 17}),
                                 option(T::put, 1, 75, 0.22, {2026, 4, 17}), option(T::put, -1, 90, 2.71, {2026, 4, 17})});
        condor.market.underlying = usd(97.29);
        Solution c = solve(condor, r, exact);
        CHECK(!c.lp_integral);
        CHECK(near(c.lp_bound, 1622.90));

        CHECK_EQ(c.total, usd(1629));

        // Three calls: the LP pairs 11/9 short 45s with the long 40 and 2/9 of a long 67.50,
        // at zero loss; whole contracts cannot.
        Portfolio calls = book({option(T::call, 1, 40, 15.83, {2026, 2, 20}), option(T::call, -3, 45, 10.85, {2026, 2, 20}),
                                option(T::call, 4, 67.5, 0.22, {2026, 3, 20})});
        calls.market.underlying = usd(55.83);
        Solution k = solve(calls, r, exact);
        CHECK(!k.lp_integral);
        CHECK(near(9 * k.lp_bound, 50264.60));  // ninths: 11/9 and 2/9 of a contract
        CHECK_EQ(k.total, usd(5622.60));
    }

    // The checker rejects a structure Phase 1 does not accept and a miscount.
    Solution bad = solve(bull, r, exact);
    bad.structures[0].legs.pop_back();
    CHECK_THROWS(check_solution(bull, r, bad));
    bad = solve(bull, r, exact);
    bad.residuals.push_back({{0, 1}, {}});
    CHECK_THROWS(check_solution(bull, r, bad));
}

// The compact straddle form (Builder::straddles) against one template per pair: the same
// exact optimum on random books with many short puts and calls, and every straddle it
// reads back is one Phase 1 accepts (the checker prices it).
void compact_straddles() {
    std::mt19937_64 rng(5'160'000);
    const ExpiryRule rules[] = {ExpiryRule::pairwise, ExpiryRule::nearest_long, ExpiryRule::same_expiry};
    int used = 0;
    for (int k = 0; k < 400; ++k) {
        gen::Shape shape;
        shape.max_series = 14;
        shape.max_quantity = 4;
        shape.adjusted = k % 4 == 0;
        Portfolio p = gen::portfolio(rng, shape);
        RuleSet rr = gen::rules(rng, rules[k % 3]);
        SolveOptions pairs{1, 0}, compact{1, 0};
        pairs.compact_straddle_pairs = 1'000'000;
        compact.compact_straddle_pairs = 0;
        Solution a = solve(p, rr, pairs), b = solve(p, rr, compact);
        CHECK_EQ(a.total, b.total);
        CHECK(near(a.lp_bound, b.lp_bound));
        for (const auto& st : b.structures) used += st.kind == StructureKind::straddle;
    }
    CHECK(used > 100);  // the comparison exercised the compact form
}

// The greedy baseline: the checker accepts what it builds, it never beats the exact
// solve, and on a lone vertical it finds the spread.
void greedy_baseline() {
    RuleSet r;
    Portfolio bull = book({option(OptionType::call, 1, 50, 3), option(OptionType::call, -1, 55, 1)});
    Solution g = greedy(bull, r);
    CHECK_EQ(g.structures.size(), std::size_t{1});
    CHECK_EQ(g.total, solve(bull, r, exact).total);

    std::mt19937_64 rng(5'150'000);
    const ExpiryRule rules[] = {ExpiryRule::pairwise, ExpiryRule::nearest_long, ExpiryRule::same_expiry};
    for (int k = 0; k < 600; ++k) {
        gen::Shape shape;
        shape.max_series = 12;
        shape.max_quantity = 5;
        shape.adjusted = k % 3 == 0;
        Portfolio p = gen::portfolio(rng, shape);
        RuleSet rr = gen::rules(rng, rules[k % 3]);
        Solution gs = greedy(p, rr);
        Solution es = solve(p, rr, exact);
        CHECK(gs.total >= es.total);
        CHECK(gs.total <= gs.all_standalone);
        CHECK_EQ(gs.all_standalone, es.all_standalone);
    }
}

// One expiration, American, listed, 100-share series only: the scope of solve_strike_dp.
Portfolio dp_book(std::mt19937_64& rng, int series, int quantity) {
    gen::Shape shape;
    shape.max_series = series;
    shape.min_series = series;
    shape.max_quantity = quantity;
    shape.max_stock_lots = 0;
    shape.expiries = 1;
    Portfolio g = gen::portfolio(rng, shape), p = g;
    p.options.clear();
    std::set<std::pair<int, Money>> seen;
    for (const auto& l : g.options)
        if (l.option.style == Style::american && l.option.listing == Listing::listed &&
            seen.insert({static_cast<int>(l.option.type), l.option.strike}).second)
            p.options.push_back(l);
    return p;
}

// The strike dynamic program against branch-and-bound with straddles off, exact. Both
// totals come from the checker; the DP also checks its own objective against it.
void strike_dp() {
    RuleSet r;
    Portfolio bull = book({option(OptionType::call, 1, 50, 3), option(OptionType::call, -1, 55, 1)});
    SolveOptions plain{1, 0};
    plain.straddles = false;
    Solution d = solve_strike_dp(bull, r);
    CHECK_EQ(d.structures.size(), std::size_t{1});
    CHECK_EQ(d.total, solve(bull, r, plain).total);

    std::mt19937_64 rng(5'170'000);
    int grouped = 0;
    for (int k = 0; k < 1500; ++k) {
        Portfolio p = dp_book(rng, 2 + k % 13, k % 2 ? 3 : 6);
        if (p.options.empty()) continue;
        RuleSet rr = gen::rules(rng, ExpiryRule::pairwise);
        Solution a = solve_strike_dp(p, rr), b = solve(p, rr, plain);
        CHECK(a.status == MipStatus::optimal);
        CHECK_EQ(a.total, b.total);
        grouped += !a.structures.empty();
    }
    CHECK(grouped > 500);

    // Outside the scope it refuses rather than answering a different question.
    Portfolio two = bull;
    two.options[1].option.expiry = Date{2027, 1, 15};
    CHECK_THROWS(solve_strike_dp(two, r));
    DpOptions tiny;
    tiny.state_limit = 0;
    CHECK(solve_strike_dp(bull, r, tiny).status == MipStatus::node_limit);
}

// docs/proofs.md, "Hardness", Theorem 4: one max-loss group decides whether exactly k of
// n numbers sum to t. Every short is priced by R3 from call prices that are linear in the
// strike, so nothing here is outside the rules. The exact optimum equals the proof's floor
// exactly when such a subset exists, on branch-and-bound and on the strike DP.
void subset_sum_reduction() {
    RuleSet r;
    std::mt19937_64 rng(5'175'000);
    int yes = 0, no = 0, by_dp = 0;
    for (int trial = 0; trial < 120; ++trial) {
        const int n = 3 + trial % 6;
        const int k = gen::uniform_int(rng, 2, n - 1);
        std::vector<long> a(n);
        long total = 0;
        for (auto& v : a) total += v = gen::uniform_int(rng, 1, 12);
        // Half the targets are the sum of a random k of the numbers.
        long t = gen::uniform_int(rng, 1, static_cast<int>(total));
        if (trial % 2 == 0) {
            std::vector<long> pick = a;
            t = 0;
            for (int i = 0; i < k; ++i) {
                std::swap(pick[i], pick[gen::uniform_int(rng, i, n - 1)]);
                t += pick[i];
            }
        }
        bool want = false;
        for (unsigned mask = 0; mask < (1u << n); ++mask) {
            long count = 0, sum = 0;
            for (int i = 0; i < n; ++i)
                if (mask >> i & 1) ++count, sum += a[i];
            want = want || (count == k && sum == t);
        }

        // The proof's instance for the numbers 2k·a_i and the target 2k·t, in cents per
        // share: a unit of size is 2k cents of strike, so that prices, which fall 1/(2k)
        // per cent of strike, are whole cents.
        long shift = 8 * total, target = t + k * shift, step = 2 * k;
        long top_price = 1;
        long spot = 2 * (top_price + target);
        long low = (11 * spot + 9) / 10;  // every strike is at least 10% out of the money
        long top = low + step * target;
        Portfolio p;
        p.market = Market{gen::cents(spot), Date{2026, 1, 15}};
        auto leg = [&](long strike, std::int64_t quantity) {
            OptionLeg l = option(OptionType::call, quantity, 0, 0);
            l.option.strike = gen::cents(strike);
            l.value = gen::cents(top_price + (top - strike) / step);
            return l;
        };
        p.options.push_back(leg(low, 1));
        p.options.push_back(leg(top, n));
        std::map<long, std::int64_t> shorts;
        for (long v : a) ++shorts[top - step * (v + shift)];
        for (const auto& [strike, count] : shorts) p.options.push_back(leg(strike, -count));

        // The floor: every position standalone, less the largest saving the proof allows,
        // c·k + β·V per share, with c the part of R3 that does not depend on the strike.
        Solution s = solve(p, r, exact);
        Money c = gen::cents(top_price) + percent(10) * gen::cents(spot);
        Money floor = s.all_standalone - (c * k + gen::cents(target)) * 100;
        CHECK(s.status == MipStatus::optimal);
        CHECK(s.total >= floor);
        CHECK_EQ(s.total == floor, want);
        Solution d = solve_strike_dp(p, r);
        if (d.status == MipStatus::optimal) {
            CHECK_EQ(d.total, s.total);
            ++by_dp;
        }
        (want ? yes : no)++;
    }
    CHECK(yes > 30 && no > 30 && by_dp > 60);
}

// Book: pricing an order from the book's optimum must give what an exact cold solve of the
// book after the order gives, whichever path it takes: bounds only (a resize), or a new
// model (a new series, a close, a sign flip, stock). Filling it must leave the book where a
// fresh Book on the new portfolio would be.
void book_orders() {
    std::mt19937_64 rng(5'180'000);
    const ExpiryRule rules[] = {ExpiryRule::pairwise, ExpiryRule::nearest_long, ExpiryRule::same_expiry};
    int resized = 0, bounded = 0;
    for (int k = 0; k < 300; ++k) {
        gen::Shape shape;
        shape.max_series = 12;
        shape.max_quantity = 6;
        shape.adjusted = k % 4 == 0;
        Portfolio p = gen::portfolio(rng, shape);
        if (p.options.empty()) continue;
        RuleSet rr = gen::rules(rng, rules[k % 3]);
        Book book(p, rr, exact);
        CHECK_EQ(book.solution().total, solve(p, rr, exact).total);
        for (int t = 0; t < 4; ++t) {
            Portfolio after = p;
            OptionLeg order;
            const int i = gen::uniform_int(rng, 0, static_cast<int>(p.options.size()) - 1);
            const int kind = gen::uniform_int(rng, 0, 4);
            if (kind <= 2) {  // resize, keeping the side
                order = p.options[i];
                const std::int64_t q = order.quantity;
                order.quantity = gen::uniform_int(rng, 1, 3) * (q > 0 ? 1 : -1) * (kind == 2 && std::llabs(q) > 3 ? -1 : 1);
                after.options[i].quantity += order.quantity;
                ++resized;
            } else if (kind == 3) {  // close
                order = p.options[i];
                order.quantity = -order.quantity;
                after.options.erase(after.options.begin() + i);
            } else {  // a new series one strike step away
                order = p.options[i];
                order.option.strike = order.option.strike + Money::dollars(1);
                order.quantity = gen::uniform_int(rng, 1, 3) * (gen::uniform_01(rng) < 0.5 ? 1 : -1);
                bool held = false;
                for (const auto& l : p.options)
                    held |= l.option.type == order.option.type && l.option.strike == order.option.strike &&
                            l.option.expiry == order.option.expiry && l.option.deliverable == order.option.deliverable &&
                            l.option.style == order.option.style && l.option.listing == order.option.listing;
                if (held || (order.quantity < 0 && order.option.listing != Listing::listed)) continue;
                after.options.push_back(order);
            }
            if (after.options.empty()) continue;
            Solution w = book.what_if(order);
            CHECK_EQ(w.total, solve(after, rr, exact).total);
            // bounds() brackets the optimum, and fits() agrees with it on either side.
            const Book::OrderBounds b = book.bounds(order);
            CHECK(b.lower <= dollars_of(w.total) * (1 + 1e-9) + 1e-9);
            CHECK(b.upper >= w.total);
            CHECK(book.fits(order, w.total));
            CHECK(!book.fits(order, w.total - usd(0.01)));
            ++bounded;
            CHECK_EQ(book.solution().total, solve(book.portfolio(), rr, exact).total);  // unchanged
            if (t % 2 == 1) {
                book.fill(order);
                p = book.portfolio();
                CHECK_EQ(book.solution().total, w.total);
            }
        }
        if (p.stock.shares == 0 && p.options.front().option.product == ProductClass::equity) {
            Portfolio after = p;
            after.stock = StockLeg{100, p.market.underlying};
            CHECK_EQ(book.what_if_stock(100).total, solve(after, rr, exact).total);
        }
    }
    CHECK(resized > 500);
    CHECK(bounded > 900);
}

// Determinism: the same positions give the same answer, bit for bit, whatever order they
// are listed in, however often they are solved, and whichever orders led a Book to them.
// Pairings are compared as sorted lists of structures named by series, not position index.
std::vector<std::string> named_pairing(const Portfolio& p, const Solution& s) {
    std::vector<std::string> out;
    for (const auto& st : s.structures) {
        std::vector<std::string> legs;
        for (const auto& l : st.legs) {
            std::string name = "S";
            if (l.position != stock_position) {
                const Option& o = p.options[l.position].option;
                name = std::to_string(static_cast<int>(o.type)) + "/" + o.strike.str() + "/" + std::to_string(o.expiry.year) +
                       "-" + std::to_string(o.expiry.month) + "/" + std::to_string(o.deliverable);
            }
            legs.push_back(name + "x" + std::to_string(l.quantity));
        }
        std::sort(legs.begin(), legs.end());
        std::string k = kind_name(st.kind);
        for (const auto& l : legs) k += " " + l;
        out.push_back(k);
    }
    std::sort(out.begin(), out.end());
    return out;
}

void determinism() {
    std::mt19937_64 rng(5'190'000);
    const ExpiryRule rules[] = {ExpiryRule::pairwise, ExpiryRule::nearest_long, ExpiryRule::same_expiry};
    int compared = 0;
    for (int k = 0; k < 120; ++k) {
        gen::Shape shape;
        shape.max_series = 20;
        shape.max_quantity = 8;
        shape.adjusted = k % 4 == 0;
        Portfolio p = gen::portfolio(rng, shape);
        if (p.options.size() < 2) continue;
        RuleSet rr = gen::rules(rng, rules[k % 3]);
        const SolveOptions o;  // the default 1% gap, where near-optimal ties are many
        Solution a = solve(p, rr, o), again = solve(p, rr, o);
        CHECK_EQ(a.total, again.total);
        CHECK(named_pairing(p, a) == named_pairing(p, again));
        Portfolio shuffled = p;
        gen::shuffle(shuffled.options, rng);
        Solution b = solve(shuffled, rr, o);
        CHECK_EQ(a.total, b.total);
        CHECK(named_pairing(p, a) == named_pairing(shuffled, b));

        // Two orders filled one after the other, against a new Book on the result.
        Book book(p, rr, o);
        for (int t = 0; t < 2; ++t) {
            OptionLeg order = book.portfolio().options[gen::uniform_int(rng, 0, static_cast<int>(book.portfolio().options.size()) - 1)];
            const std::int64_t q = order.quantity;
            order.quantity = q > 1 ? -1 : 1;
            book.fill(order);
        }
        Book fresh(book.portfolio(), rr, o);
        CHECK_EQ(book.solution().total, fresh.solution().total);
        CHECK(named_pairing(book.portfolio(), book.solution()) == named_pairing(fresh.portfolio(), fresh.solution()));
        CHECK_EQ(book.solution().total, solve(book.portfolio(), rr, o).total);
        OptionLeg next = book.portfolio().options.front();
        next.quantity = next.quantity > 0 ? 1 : -1;
        Solution w1 = book.what_if(next), w2 = fresh.what_if(next);
        CHECK_EQ(w1.total, w2.total);
        CHECK(named_pairing(book.portfolio(), w1) == named_pairing(fresh.portfolio(), w2));
        Portfolio after = book.portfolio();
        after.options.front().quantity += next.quantity;
        CHECK_EQ(book.canonical_what_if(next).total, solve(after, rr, o).total);
        ++compared;
    }
    CHECK(compared > 100);
}

}  // namespace

int run_solver_tests() {
    int groups = 0;
    auto run = [&](const char* name, void (*f)()) {
        ::check::context() = name;
        f();
        ++groups;
    };
    run("small_lps", small_lps);
    run("random_lps", random_lps);
    run("knapsacks", knapsacks);
    run("hand_cases", hand_cases);
    run("greedy_baseline", greedy_baseline);
    run("compact_straddles", compact_straddles);
    run("strike_dp", strike_dp);
    run("subset_sum_reduction", subset_sum_reduction);
    run("book_orders", book_orders);
    run("determinism", determinism);
    ::check::context().clear();
    return groups;
}
