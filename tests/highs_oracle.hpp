#pragma once

// HiGHS as the test-only oracle (spec §3.4): the same model, solved as an LP or a MIP with
// mip_rel_gap = 0. Shared by the differential test and the benchmarks.

#include <Highs.h>

#include <chrono>
#include <cstdlib>
#include <stdexcept>
#include <vector>

#include "pairing/solver.hpp"

namespace oracle {

using namespace pairing;

inline double dollars(Money m) { return static_cast<double>(m.micros()) / Money::per_dollar; }

struct Oracle {
    HighsModelStatus status;
    double objective;
    std::vector<double> x;
    double seconds;
};

inline Oracle highs(const Model& m, bool integer, double time_limit = lp_infinity) {
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
    lp.a_matrix_.start_.assign(1, 0);  // HighsSparseMatrix already holds a leading 0; a second makes num_col + 2 starts
    for (const auto& col : m.lp.columns) {
        for (const auto& e : col) {
            lp.a_matrix_.index_.push_back(e.row);
            lp.a_matrix_.value_.push_back(e.value);
        }
        lp.a_matrix_.start_.push_back(static_cast<HighsInt>(lp.a_matrix_.index_.size()));
    }
    if (integer)
        for (bool b : m.integer) lp.integrality_.push_back(b ? HighsVarType::kInteger : HighsVarType::kContinuous);

    // HiGHS reports 0, not the offset, for a model with no columns.
    if (lp.num_col_ == 0) return {HighsModelStatus::kOptimal, lp.offset_, {}, 0};
    Highs h;
    h.setOptionValue("output_flag", std::getenv("HIGHS_LOG") != nullptr);
    h.setOptionValue("threads", 1);
    h.setOptionValue("primal_feasibility_tolerance", 1e-10);
    h.setOptionValue("dual_feasibility_tolerance", 1e-10);
    h.setOptionValue("mip_feasibility_tolerance", 1e-10);
    h.setOptionValue("mip_rel_gap", 0.0);
    h.setOptionValue("mip_abs_gap", 1e-7);
    if (time_limit < lp_infinity) h.setOptionValue("time_limit", time_limit);
    if (h.passModel(lp) != HighsStatus::kOk) throw std::runtime_error("HiGHS rejected the model");
    auto t0 = std::chrono::steady_clock::now();
    h.run();
    auto t1 = std::chrono::steady_clock::now();
    return {h.getModelStatus(), h.getInfo().objective_function_value, h.getSolution().col_value,
            std::chrono::duration<double>(t1 - t0).count()};
}

}  // namespace oracle
