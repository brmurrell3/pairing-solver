// Differential test against HiGHS, the test-only oracle (spec §3.4). Each random
// subproblem's model goes to both solvers:
// - continuous: our dual simplex against HiGHS's LP optimum;
// - continuous: our dual simplex against HiGHS's LP optimum, to 1e-9 relative;
// - grid: our branch-and-bound (through solve(), so the checker prices the assignment)
//   against HiGHS's proven MIP optimum (mip_rel_gap = 0). Ours may be up to rel_gap above
//   it (docs/plan.md, Phase 2 target) and never below it; a stop at the node limit passes
//   if the answer is still within that gap. HiGHS's own assignment, priced by the checker, must equal its
//   objective, which checks the model export.
//
// Usage: pairing_highs_tests <portfolios> [max series] [rel_gap]
//        pairing_highs_tests large [rel_gap] [case]
// "large" runs the Phase 2 performance cases: five fixed-seed portfolios of exactly 50,
// 100, 150, 200 and 200 series, each of which must also finish within 30 s.

#include <chrono>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <random>
#include <string>

#include "check.hpp"
#include "highs_oracle.hpp"
#include "generate.hpp"
#include "pairing/solver.hpp"

using namespace pairing;

namespace {

using oracle::dollars;
using oracle::highs;
using oracle::Oracle;

double relative(double a, double b) { return std::fabs(a - b) / std::max(1.0, std::fabs(b)); }

}  // namespace

int main(int argc, char** argv) {
    if (argc < 2 || argc > 4 + (argc >= 2 && std::string(argv[1]) == "large")) {
        std::cerr << "usage: pairing_highs_tests <portfolios> [max series] [rel_gap]\n"
                     "       pairing_highs_tests large [rel_gap] [case]\n";
        return 2;
    }
    const bool large = std::string(argv[1]) == "large";
    const int large_series[] = {50, 100, 150, 200, 200};
    constexpr double large_seconds = 30;
    constexpr long large_nodes = 3000;
    const int count = large ? 5 : std::stoi(argv[1]);
    const int only = large && argc >= 4 ? std::stoi(argv[3]) : -1;
    const int max_series = !large && argc >= 3 ? std::stoi(argv[2]) : 40;
    const char* gap_arg = large ? (argc >= 3 ? argv[2] : nullptr) : (argc >= 4 ? argv[3] : nullptr);
    const double rel_gap = gap_arg ? std::stod(gap_arg) : SolveOptions{}.rel_gap;
    const ExpiryRule rules[] = {ExpiryRule::pairwise, ExpiryRule::nearest_long, ExpiryRule::same_expiry};

    long series = 0, integral = 0, lots_runs = 0, nodes = 0, largest_rows = 0, largest_cols = 0;
    long stopped = 0;
    double worst_lp = 0, worst_mip = 0, worst_gap = 0, slowest = 0;
    double t_ours_lp = 0, t_ours_mip = 0, t_highs_lp = 0, t_highs_mip = 0;
    try {
        for (int k = 0; k < count; ++k) {
            if (only >= 0 && k != only) continue;
            std::mt19937_64 rng((large ? 78'000'000ULL : 77'000'000ULL) + k);
            gen::Shape shape;
            shape.max_series = max_series;
            if (large) shape.min_series = shape.max_series = large_series[k];
            shape.max_quantity = 10;
            shape.max_stock_lots = 20;
            shape.expiries = large ? 6 : 1 + k % 6;
            shape.strikes = large ? 15 : 5 + k % 11;
            shape.adjusted = true;
            shape.minis = k % 2 == 1;
            Portfolio p = gen::portfolio(rng, shape);
            RuleSet r = gen::rules(rng, rules[k % 3]);
            // Every tenth subproblem on a grid of tenths of a contract.
            SolveOptions o;
            o.rel_gap = rel_gap;
            // The large cases run under a node budget that keeps each within the time limit;
            // a stop there is acceptable if the answer is still within the gap of HiGHS.
            if (large) o.node_limit = large_nodes;
            if (k % 10 == 9) {
                o.lots_per_contract = 10;
                ++lots_runs;
            }
            ::check::context() = "#" + std::to_string(k);
            series += static_cast<long>(p.options.size());

            Model m = build_model(p, r, o);
            largest_rows = std::max<long>(largest_rows, m.lp.rows());
            largest_cols = std::max<long>(largest_cols, m.lp.cols());
            const double constant = dollars(m.constant);

            auto t0 = std::chrono::steady_clock::now();
            LpSolution lp = DualSimplex(m.lp).solve();
            auto t1 = std::chrono::steady_clock::now();
            Solution s = solve(p, r, o);
            auto t2 = std::chrono::steady_clock::now();
            t_ours_lp += std::chrono::duration<double>(t1 - t0).count();
            t_ours_mip += std::chrono::duration<double>(t2 - t1).count();
            const double seconds = std::chrono::duration<double>(t2 - t1).count();
            slowest = std::max(slowest, seconds);
            if (large) CHECK(seconds <= large_seconds);
            stopped += s.status != MipStatus::optimal;
            // A stop at the node limit passes if the answer is still within the gap of HiGHS,
            // checked below: the target is the answer's quality, not a proof (docs/plan.md,
            // Phase 2 target). Two of the 1,000 cases stop there, with a weak bound.
            CHECK(s.status == MipStatus::optimal || s.status == MipStatus::node_limit);
            nodes += s.nodes;
            integral += s.lp_integral;
            worst_gap = std::max(worst_gap, s.gap);
            CHECK(lp.status == LpStatus::optimal);

            Oracle hl = highs(m, false);
            Oracle hm = highs(m, true);
            t_highs_lp += hl.seconds;
            t_highs_mip += hm.seconds;
            CHECK(hl.status == HighsModelStatus::kOptimal);
            CHECK(hm.status == HighsModelStatus::kOptimal);

            // HiGHS's assignment, priced exactly, checks the model export: it can be no
            // worse than HiGHS reports. It can be slightly better, when HiGHS leaves a loss
            // column above its row's minimum within tolerance, so the reference optimum is
            // the lower of the two.
            Solution theirs = read_solution(m, p, hm.x);
            double priced = dollars(check_solution(p, r, theirs));
            CHECK(priced <= hm.objective * (1 + 1e-9) + 1e-9);
            const double optimum = std::min(priced, hm.objective);

            double total = dollars(s.total);
            double d_lp = relative(constant + lp.objective, hl.objective);
            // Above the optimum is the allowed gap; below it is a bug.
            double d_mip = (total - optimum) / std::max(1.0, std::fabs(optimum));
            worst_lp = std::max(worst_lp, d_lp);
            worst_mip = std::max(worst_mip, d_mip);
            CHECK(d_lp <= 1e-9);
            CHECK(d_mip <= rel_gap + 1e-9);
            CHECK(d_mip >= -1e-9);
            CHECK(relative(s.lp_bound, hl.objective) <= 1e-9);
            CHECK(s.bound <= optimum * (1 + 1e-9) + 1e-9);
            if (large)
                std::cout << "  #" << k << ": " << p.options.size() << " series, " << m.lp.rows() << " x " << m.lp.cols()
                          << ", " << status_name(s.status) << " in " << seconds << " s, " << s.nodes << " nodes, "
                          << d_mip * 100 << "% above HiGHS (" << hm.seconds << " s)" << std::endl;
            if (d_lp > 1e-9 || d_mip > rel_gap + 1e-9 || d_mip < -1e-9 || s.status != MipStatus::optimal)
                std::cerr << "  #" << k << ": " << status_name(s.status) << ", ours lp " << constant + lp.objective
                          << " mip " << total << "; HiGHS lp " << hl.objective << " mip " << hm.objective
                          << " (priced " << priced << ")\n";
        }
    } catch (const std::exception& e) {
        std::cerr << "error [" << ::check::context() << "]: " << e.what() << "\n";
        return 1;
    }
    const auto& c = ::check::counter();
    std::cout << "highs: " << count << " portfolios (" << lots_runs << " on a 1/10 grid), " << series
              << " series in all, largest model " << largest_rows << " rows x " << largest_cols << " columns\n"
              << "  max relative difference: LP " << worst_lp << ", MIP above HiGHS " << worst_mip << " (allowed " << rel_gap << ")" << "\n"
              << "  continuous optimum already on the grid: " << integral << "/" << count
              << "; largest gap " << worst_gap << "; branch-and-bound nodes " << nodes << "; stopped at the node limit "
              << stopped << "\n"
              << "  seconds: ours LP " << t_ours_lp << ", ours MIP " << t_ours_mip << ", HiGHS LP " << t_highs_lp
              << ", HiGHS MIP " << t_highs_mip << "; slowest of ours " << slowest << "\n"
              << "highs: " << c.checks << " checks, " << c.failures << " failed\n";
    return c.failures == 0 ? 0 : 1;
}
