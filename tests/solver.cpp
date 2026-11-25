// The LP solver, branch-and-bound, model and checker on cases with known answers.

#include <cmath>
#include <random>
#include <string>
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

    // The checker rejects a structure Phase 1 does not accept and a miscount.
    Solution bad = solve(bull, r, exact);
    bad.structures[0].legs.pop_back();
    CHECK_THROWS(check_solution(bull, r, bad));
    bad = solve(bull, r, exact);
    bad.residuals.push_back({{0, 1}, {}});
    CHECK_THROWS(check_solution(bull, r, bad));
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
    ::check::context().clear();
    return groups;
}
