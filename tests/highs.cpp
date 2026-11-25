// Differential test against HiGHS, the test-only oracle (spec §3.4). Each random
// subproblem's model goes to both solvers:
// - continuous: our dual simplex against HiGHS's LP optimum;
// - grid: our branch-and-bound (through solve(), so the checker prices the assignment)
//   against HiGHS's MIP optimum, and HiGHS's own assignment, rounded and priced by the
//   checker, must not beat ours.
// Agreement is to 1e-9 relative to the total requirement.
//
// Usage: pairing_highs_tests <portfolios> [max series]

#include <Highs.h>

#include <chrono>
#include <cmath>
#include <iostream>
#include <random>
#include <string>

#include "check.hpp"
#include "generate.hpp"
#include "pairing/solver.hpp"

using namespace pairing;

namespace {

double dollars(Money m) { return static_cast<double>(m.micros()) / Money::per_dollar; }

struct Oracle {
    HighsModelStatus status;
    double objective;
    std::vector<double> x;
    double seconds;
};

Oracle highs(const Model& m, bool integer) {
    HighsLp lp;
    lp.num_col_ = m.lp.cols();
    lp.num_row_ = m.lp.rows();
    lp.col_cost_ = m.lp.cost;
    lp.col_lower_ = m.lp.col_lo;
    lp.col_upper_ = m.lp.col_up;
    lp.row_lower_ = m.lp.row_lo;
    lp.row_upper_ = m.lp.row_up;
    lp.offset_ = dollars(m.constant);
    lp.a_matrix_.format_ = MatrixFormat::kColwise;
    lp.a_matrix_.num_col_ = lp.num_col_;
    lp.a_matrix_.num_row_ = lp.num_row_;
    lp.a_matrix_.start_.push_back(0);
    for (const auto& col : m.lp.columns) {
        for (const auto& e : col) {
            lp.a_matrix_.index_.push_back(e.row);
            lp.a_matrix_.value_.push_back(e.value);
        }
        lp.a_matrix_.start_.push_back(static_cast<HighsInt>(lp.a_matrix_.index_.size()));
    }
    if (integer)
        for (bool b : m.integer) lp.integrality_.push_back(b ? HighsVarType::kInteger : HighsVarType::kContinuous);

    Highs h;
    h.setOptionValue("output_flag", false);
    h.setOptionValue("threads", 1);
    h.setOptionValue("primal_feasibility_tolerance", 1e-10);
    h.setOptionValue("dual_feasibility_tolerance", 1e-10);
    h.setOptionValue("mip_feasibility_tolerance", 1e-10);
    h.setOptionValue("mip_rel_gap", 0.0);
    h.setOptionValue("mip_abs_gap", 1e-7);
    if (h.passModel(lp) != HighsStatus::kOk) throw std::runtime_error("HiGHS rejected the model");
    auto t0 = std::chrono::steady_clock::now();
    h.run();
    auto t1 = std::chrono::steady_clock::now();
    return {h.getModelStatus(), h.getInfo().objective_function_value, h.getSolution().col_value,
            std::chrono::duration<double>(t1 - t0).count()};
}

double relative(double a, double b) { return std::fabs(a - b) / std::max(1.0, std::fabs(b)); }

}  // namespace

int main(int argc, char** argv) {
    if (argc < 2 || argc > 3) {
        std::cerr << "usage: pairing_highs_tests <portfolios> [max series]\n";
        return 2;
    }
    const int count = std::stoi(argv[1]);
    const int max_series = argc == 3 ? std::stoi(argv[2]) : 200;
    const ExpiryRule rules[] = {ExpiryRule::pairwise, ExpiryRule::nearest_long, ExpiryRule::same_expiry};

    long series = 0, integral = 0, lots_runs = 0, nodes = 0, largest_rows = 0, largest_cols = 0;
    double worst_lp = 0, worst_mip = 0, worst_gap = 0;
    double t_ours_lp = 0, t_ours_mip = 0, t_highs_lp = 0, t_highs_mip = 0;
    try {
        for (int k = 0; k < count; ++k) {
            std::mt19937_64 rng(77'000'000ULL + k);
            gen::Shape shape;
            shape.max_series = max_series;
            shape.max_quantity = 10;
            shape.max_stock_lots = 20;
            shape.expiries = 1 + k % 6;
            shape.strikes = 5 + k % 11;
            shape.adjusted = true;
            shape.minis = k % 2 == 1;
            Portfolio p = gen::portfolio(rng, shape);
            RuleSet r = gen::rules(rng, rules[k % 3]);
            // Every tenth subproblem on a grid of tenths of a contract.
            SolveOptions o;
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

            double total = dollars(s.total);
            double d_lp = relative(constant + lp.objective, hl.objective);
            double d_mip = relative(total, hm.objective);
            worst_lp = std::max(worst_lp, d_lp);
            worst_mip = std::max(worst_mip, d_mip);
            CHECK(d_lp <= 1e-9);
            CHECK(d_mip <= 1e-9);
            CHECK(relative(s.lp_bound, hl.objective) <= 1e-9);

            // HiGHS's assignment, on the grid and priced exactly, never beats ours.
            Solution theirs = read_solution(m, p, hm.x);
            Money their_total = check_solution(p, r, theirs);
            CHECK(s.total <= their_total);
            if (d_lp > 1e-9 || d_mip > 1e-9 || their_total < s.total)
                std::cerr << "  #" << k << ": ours lp " << constant + lp.objective << " mip " << total << "; HiGHS lp "
                          << hl.objective << " mip " << hm.objective << " (priced " << their_total.str() << ")\n";
        }
    } catch (const std::exception& e) {
        std::cerr << "error [" << ::check::context() << "]: " << e.what() << "\n";
        return 1;
    }
    const auto& c = ::check::counter();
    std::cout << "highs: " << count << " portfolios (" << lots_runs << " on a 1/10 grid), " << series
              << " series in all, largest model " << largest_rows << " rows x " << largest_cols << " columns\n"
              << "  max relative difference: LP " << worst_lp << ", MIP " << worst_mip << "\n"
              << "  continuous optimum already on the grid: " << integral << "/" << count
              << "; largest gap " << worst_gap << "; branch-and-bound nodes " << nodes << "\n"
              << "  seconds: ours LP " << t_ours_lp << ", ours MIP " << t_ours_mip << ", HiGHS LP " << t_highs_lp
              << ", HiGHS MIP " << t_highs_mip << "\n"
              << "highs: " << c.checks << " checks, " << c.failures << " failed\n";
    return c.failures == 0 ? 0 : 1;
}
