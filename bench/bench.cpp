// Phase 3 benchmarks (docs/plan.md). Regenerates every table in docs/benchmarks.md from
// fixed seeds:
//
//   tools/run_guarded.sh -m 4096 -t 3000 -- build/pairing_bench > docs/benchmarks.md
//
// Times are wall-clock on whatever machine runs it; everything else is deterministic.

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>

#include "books.hpp"
#include "pairing/solver.hpp"
#ifdef PAIRING_BENCH_HIGHS
#include "highs_oracle.hpp"
#endif

using namespace pairing;

namespace {

double dollars(Money m) { return static_cast<double>(m.micros()) / Money::per_dollar; }

double seconds_since(std::chrono::steady_clock::time_point t0) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}

struct Stats {
    std::vector<double> v;
    void add(double x) { v.push_back(x); }
    double mean() const { return v.empty() ? 0 : std::accumulate(v.begin(), v.end(), 0.0) / v.size(); }
    double quantile(double q) const {
        if (v.empty()) return 0;
        std::vector<double> s = v;
        std::sort(s.begin(), s.end());
        return s[std::min(s.size() - 1, static_cast<std::size_t>(q * (s.size() - 1) + 0.5))];
    }
    double max() const { return v.empty() ? 0 : *std::max_element(v.begin(), v.end()); }
};

std::string pct(double x, int digits = 2) {
    char b[32];
    std::snprintf(b, sizeof b, "%.*f%%", digits, 100 * x);
    return b;
}
std::string num(double x, int digits = 3) {
    char b[32];
    if (std::fabs(x) >= 1000) std::snprintf(b, sizeof b, "%.0f", x);
    else std::snprintf(b, sizeof b, "%.*g", digits, x);
    return b;
}
std::string ms(double s) {
    char b[32];
    if (s < 1) std::snprintf(b, sizeof b, "%.2f ms", 1000 * s);
    else std::snprintf(b, sizeof b, "%.2f s", s);
    return b;
}

struct Case {
    std::string family;
    Portfolio p;
};

std::vector<Case> family(const std::string& name, int count, std::uint64_t seed) {
    std::mt19937_64 rng(seed);
    std::vector<Case> out;
    for (int k = 0; k < count; ++k) {
        Portfolio p = name == "retail"     ? books::retail(rng)
                      : name == "adjusted" ? books::adjusted(rng)
                                           : books::market_maker(rng, books::pick(rng, 10, 40));
        if (!p.options.empty()) out.push_back({name, std::move(p)});
    }
    return out;
}

// Adversarial books: retail books chosen for how badly greedy pairs them. Of 4,000 seeded
// books, the 100 with the largest greedy excess over the optimum are kept.
std::vector<Case> adversarial(const RuleSet& r) {
    std::vector<Case> pool = family("retail", 4000, 3'003);
    std::vector<std::pair<double, int>> score;
    const SolveOptions exact{1, 0};
    for (int i = 0; i < static_cast<int>(pool.size()); ++i) {
        double g = dollars(greedy(pool[i].p, r).total), o = dollars(solve(pool[i].p, r, exact).total);
        score.push_back({g > 0 ? (g - o) / g : 0, i});
    }
    std::sort(score.rbegin(), score.rend());
    std::vector<Case> out;
    for (int k = 0; k < 100 && k < static_cast<int>(score.size()); ++k) out.push_back({"adversarial", pool[score[k].second].p});
    return out;
}

void savings_table(const RuleSet& r) {
    std::cout << "## Savings against greedy\n\n"
              << "Each family's books are solved three ways under the default rule set: every position margined on its "
                 "own, the greedy baseline (`greedy` in `src/greedy.cpp`), and the solver. Books in these families have up "
                 "to about 40 series, so the solver runs exact (`rel_gap = 0`). Savings are relative to the all-standalone "
                 "requirement; the excess is greedy's requirement above the solver's, relative to greedy's.\n\n"
              << "| Family | Books | Series (mean) | Greedy saves | Solver saves | Greedy excess: mean | median | max | Solver "
                 "strictly better |\n|---|---|---|---|---|---|---|---|---|\n";
    std::vector<std::vector<Case>> fams = {family("retail", 500, 1'001), family("adjusted", 500, 2'002), adversarial(r),
                                           family("market_maker", 200, 4'004)};
    const SolveOptions exact{1, 0};
    for (const auto& cases : fams) {
        Stats series, gsave, osave, excess;
        int better = 0;
        for (const auto& c : cases) {
            Solution g = greedy(c.p, r), o = solve(c.p, r, exact);
            double sa = dollars(o.all_standalone), gt = dollars(g.total), ot = dollars(o.total);
            series.add(static_cast<double>(c.p.options.size()));
            gsave.add(sa > 0 ? (sa - gt) / sa : 0);
            osave.add(sa > 0 ? (sa - ot) / sa : 0);
            excess.add(gt > 0 ? (gt - ot) / gt : 0);
            better += o.total < g.total;
        }
        std::cout << "| " << cases.front().family << " | " << cases.size() << " | " << num(series.mean()) << " | "
                  << pct(gsave.mean()) << " | " << pct(osave.mean()) << " | " << pct(excess.mean()) << " | "
                  << pct(excess.quantile(0.5)) << " | " << pct(excess.max()) << " | " << better << " |\n";
    }
    std::cout << "\nThe adversarial family is selected, not constructed: the 100 of 4,000 seeded retail books on which "
                 "greedy does worst.\n\n";
}

void integrality_table(const RuleSet& r) {
    std::cout << "## Continuous against whole-contract\n\n"
              << "The gap is the whole-contract requirement above the continuous (LP) bound, relative to the whole-contract "
                 "requirement, from the exact solve.\n\n"
              << "| Family | Books | LP already whole | Gap: mean | p90 | max |\n|---|---|---|---|---|---|\n";
    std::vector<std::vector<Case>> fams = {family("retail", 500, 1'001), family("adjusted", 500, 2'002),
                                           family("market_maker", 200, 4'004)};
    const SolveOptions exact{1, 0};
    for (const auto& cases : fams) {
        Stats gap;
        int whole = 0;
        for (const auto& c : cases) {
            Solution o = solve(c.p, r, exact);
            gap.add(o.gap);
            whole += o.lp_integral;
        }
        std::cout << "| " << cases.front().family << " | " << cases.size() << " | " << whole << " | " << pct(gap.mean(), 3)
                  << " | " << pct(gap.quantile(0.9), 3) << " | " << pct(gap.max(), 3) << " |\n";
    }
    std::cout << "\n";
}

void timing_table(const RuleSet& r) {
    std::cout << "## Solve time by size\n\n"
              << "Market-maker books of exactly n series (both sides, 1 to 50 contracts, eight expirations, stock half the "
                 "time), solved with the defaults (`rel_gap` 1%) and a budget of 3,000 nodes. The proven gap is against "
                 "the solver's own bound.\n\n"
              << "| Series | Books | Model rows x cols (median) | Time: median | p90 | max | Nodes (median) | Stopped at budget | "
                 "Proven gap (max) |\n|---|---|---|---|---|---|---|---|---|\n";
    const int sizes[] = {10, 30, 100, 300, 1000};
    const int counts[] = {50, 50, 20, 10, 1};  // one 1,000-series book takes minutes
    for (int z = 0; z < 5; ++z) {
        std::mt19937_64 rng(5'000 + sizes[z]);
        Stats t, nodes, rows, cols, gap;
        int stopped = 0;
        for (int k = 0; k < counts[z]; ++k) {
            Portfolio p = books::market_maker(rng, sizes[z]);
            SolveOptions o;
            o.node_limit = 3000;
            auto t0 = std::chrono::steady_clock::now();
            Solution s = solve(p, r, o);
            t.add(seconds_since(t0));
            nodes.add(s.nodes);
            rows.add(s.rows);
            cols.add(s.columns);
            gap.add(s.proven_gap);
            stopped += s.status == MipStatus::node_limit;
        }
        std::cout << "| " << sizes[z] << " | " << counts[z] << " | " << num(rows.quantile(0.5), 4) << " x "
                  << num(cols.quantile(0.5), 5) << " | " << ms(t.quantile(0.5)) << " | " << ms(t.quantile(0.9)) << " | "
                  << ms(t.max()) << " | " << num(nodes.quantile(0.5), 5) << " | " << stopped << " | " << pct(gap.max())
                  << " |\n";
    }
    std::cout << "\n";
}

void batch_table(const RuleSet& r) {
    std::cout << "## Batch throughput\n\n"
              << "Accounts that hold the same series in different sizes share the model's matrix and costs; only bounds "
                 "differ (spec §3.2), so one account's root basis can start the next. Each batch is 200 accounts on one "
                 "chain: the same series and signs, sizes redrawn per account.\n\n"
              << "| Series | Accounts | Cold: accounts/s | Warm: accounts/s | Root iterations: cold | warm |\n"
                 "|---|---|---|---|---|---|\n";
    for (int n : {10, 30, 100}) {
        std::mt19937_64 rng(6'000 + n);
        Portfolio base = books::market_maker(rng, n);
        std::vector<Portfolio> accounts;
        for (int a = 0; a < 200; ++a) {
            Portfolio p = base;
            for (auto& l : p.options) l.quantity = (l.quantity > 0 ? 1 : -1) * books::pick(rng, 1, 50);
            if (p.stock.shares != 0) p.stock.shares = (p.stock.shares > 0 ? 100 : -100) * books::pick(rng, 1, 100);
            accounts.push_back(std::move(p));
        }
        double cold_s = 0, warm_s = 0, cold_it = 0, warm_it = 0;
        for (int pass = 0; pass < 2; ++pass) {
            LpBasis basis;
            auto t0 = std::chrono::steady_clock::now();
            for (const auto& p : accounts) {
                SolveOptions o;
                if (pass == 1) o.warm_start = basis;
                Solution s = solve(p, r, o);
                basis = s.root_basis;
                (pass ? warm_it : cold_it) += static_cast<double>(s.root_iterations);
            }
            (pass ? warm_s : cold_s) = seconds_since(t0);
        }
        std::cout << "| " << n << " | " << accounts.size() << " | " << num(accounts.size() / cold_s, 4) << " | "
                  << num(accounts.size() / warm_s, 4) << " | " << num(cold_it / accounts.size(), 4) << " | "
                  << num(warm_it / accounts.size(), 4) << " |\n";
    }
    std::cout << "\nBatches use the defaults (`rel_gap` 1%, 200,000 nodes). Warm starts change only the root LP; "
                 "branch-and-bound nodes start from their own bases either way.\n\n";
}

#ifdef PAIRING_BENCH_HIGHS
void highs_table(const RuleSet& r) {
    std::cout << "## Against HiGHS\n\n"
              << "The same models handed to HiGHS 1.16 (one thread, `mip_rel_gap = 0`, a 120 s limit per model). The "
                 "solver runs with its defaults and a budget of 3,000 nodes. Above HiGHS is the solver's requirement over "
                 "HiGHS's optimum.\n\n"
              << "| Books | Count | Solver: median | max | HiGHS: median | max | HiGHS hit its limit | Above HiGHS: mean | "
                 "max |\n|---|---|---|---|---|---|---|---|---|\n";
    struct Set {
        std::string name;
        std::vector<Portfolio> books;
    };
    std::vector<Set> sets;
    {
        Set s{"retail", {}};
        for (auto& c : family("retail", 200, 1'001)) s.books.push_back(c.p);
        sets.push_back(std::move(s));
    }
    for (int n : {10, 30, 100}) {
        Set s{"market maker, " + std::to_string(n) + " series", {}};
        std::mt19937_64 rng(5'000 + n);
        for (int k = 0; k < (n == 100 ? 10 : 30); ++k) s.books.push_back(books::market_maker(rng, n));
        sets.push_back(std::move(s));
    }
    for (const auto& set : sets) {
        Stats ours, theirs, above;
        int limited = 0;
        for (const auto& p : set.books) {
            SolveOptions o;
            o.node_limit = 3000;
            auto t0 = std::chrono::steady_clock::now();
            Solution s = solve(p, r, o);
            ours.add(seconds_since(t0));
            Model m = build_model(p, r, o);
            oracle::Oracle h = oracle::highs(m, true, 120);
            theirs.add(h.seconds);
            if (h.status != HighsModelStatus::kOptimal) {
                ++limited;
                continue;
            }
            above.add((dollars(s.total) - h.objective) / std::max(1.0, h.objective));
        }
        std::cout << "| " << set.name << " | " << set.books.size() << " | " << ms(ours.quantile(0.5)) << " | "
                  << ms(ours.max()) << " | " << ms(theirs.quantile(0.5)) << " | " << ms(theirs.max()) << " | " << limited
                  << " | " << pct(above.mean(), 3) << " | " << pct(above.max(), 3) << " |\n";
    }
    std::cout << "\nCases where HiGHS hit its limit are left out of the comparison columns.\n\n";
}
#endif

}  // namespace

int main(int argc, char** argv) {
    RuleSet r;  // the defaults: maintenance basis, pairwise expirations
    const std::string only = argc > 1 ? argv[1] : "";
    std::cout << "# Benchmarks\n\nGenerated by `build/pairing_bench` (`bench/bench.cpp`) from fixed seeds; see "
                 "`bench/books.hpp` for the generators. Requirements and counts are deterministic; times depend on the "
                 "machine.\n\n";
    if (only.empty() || only == "savings") savings_table(r);
    if (only.empty() || only == "integrality") integrality_table(r);
    if (only.empty() || only == "timing") timing_table(r);
    if (only.empty() || only == "batch") batch_table(r);
#ifdef PAIRING_BENCH_HIGHS
    if (only.empty() || only == "highs") highs_table(r);
#else
    std::cout << "## Against HiGHS\n\nNot run: this build has no HiGHS.\n";
#endif
    return 0;
}
