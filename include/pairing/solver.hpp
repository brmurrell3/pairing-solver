#pragma once

#include <cstdint>
#include <string>
#include <vector>

#include "pairing/margin.hpp"
#include "pairing/simplex.hpp"

namespace pairing {

// One (account, underlying) subproblem (spec §3.2).
struct Portfolio {
    std::vector<OptionLeg> options;  // one per series; quantity in whole contracts, signed
    StockLeg stock;                  // shares == 0: no stock line
    Market market;
};

// Quantity grid: structures use options in lots of 1/lots_per_contract of a contract
// (1: whole contracts; 100: hundredths). Shares stay whole, so every option's deliverable
// must be a multiple of lots_per_contract. The fully continuous grid is reported only as
// the LP lower bound (spec §3.4), never as an assignment.
struct SolveOptions {
    std::int64_t lots_per_contract = 1;
    // Branch-and-bound stops proving optimality once the total is within this fraction of
    // the best possible (owner, 2026-11-25: speed over the last 1%; docs/plan.md). 0 is exact.
    double rel_gap = 0.01;
    long node_limit = 200'000;  // a hit returns the best assignment found, with its status
};

// A lot of a position as a Phase 1 leg: one lot of a contract delivering w units is an
// option delivering w / lots_per_contract units, so every Phase 1 formula applies unchanged.
OptionLeg lot_leg(const OptionLeg& position, std::int64_t lots, std::int64_t lots_per_contract);

enum class StructureKind {
    spread,
    straddle,
    covered_call,
    covered_put,
    protective_put,
    protective_call,
    conversion,
    reverse_conversion,
    collar,
    long_box,
};
const char* kind_name(StructureKind k);

// position: index into Portfolio::options, or stock_position for the stock line.
// quantity: lots of the option, or shares; positive, on the position's own side.
constexpr int stock_position = -1;
struct StructureLeg {
    int position = 0;
    std::int64_t quantity = 0;
};

// Legs are in the order the Phase 1 function for the kind takes them: the stock line first,
// then, for straddle: put, call; conversion: call, put; reverse conversion: call, put;
// collar: put, call; long box and spread: any order.
struct Structure {
    StructureKind kind = StructureKind::spread;
    std::vector<StructureLeg> legs;
    Requirement requirement;
};

struct Residual {
    StructureLeg leg;
    Requirement requirement;
};

struct Solution {
    MipStatus status = MipStatus::optimal;  // node_limit: valid but not within rel_gap
    std::int64_t lots_per_contract = 1;
    std::vector<Structure> structures;
    std::vector<Residual> residuals;
    Money total;           // from the checker
    Money all_standalone;  // every position margined on its own
    double lp_bound = 0;   // continuous relaxation, dollars
    double gap = 0;        // (total - lp_bound) / total
    double bound = 0;      // proven lower bound on the optimal total, dollars
    double proven_gap = 0; // (total - bound) / total; at most rel_gap unless status is node_limit
    // ∂total/∂(position size) from the continuous solve, per contract (options) or per share
    // (stock): what one more unit of the position adds, or closing one frees. One-sided
    // when the LP is degenerate.
    std::vector<double> shadow_options;
    double shadow_stock = 0;

    // Diagnostics.
    double lp_objective = 0;  // the model's value for the reported assignment, dollars
    bool lp_integral = false; // the continuous optimum was already on the grid
    int rows = 0, columns = 0, nodes = 0;
    long iterations = 0;
};

Solution solve(const Portfolio& p, const RuleSet& r, const SolveOptions& o = {});

// The Phase 3 baseline: fixed template priority (spreads, then straddles, then stock
// against single options), nearest strikes first, two legs at a time, no revisiting. Only
// lots_per_contract is read from o. Fills structures, residuals, total and all_standalone.
Solution greedy(const Portfolio& p, const RuleSet& r, const SolveOptions& o = {});

// The independent checker. Re-derives every structure's validity and requirement and
// every residual's requirement with the Phase 1 engine, checks that structures and
// residuals use each position exactly, writes the requirements into s, and returns the
// exact total. Throws std::invalid_argument naming the first violation.
Money check_solution(const Portfolio& p, const RuleSet& r, Solution& s);

// The model of spec §2 for one subproblem, specialized as spec §3.1 describes. Exposed
// for the differential tests, which hand the same LP to HiGHS.
struct Model {
    Lp lp;
    std::vector<bool> integer;
    std::vector<int> priority;  // branching priority per column; higher branches first
    Money constant;  // all-standalone total in the LP's per-unit costs; objective = constant + lp
    std::int64_t lots_per_contract = 1;

    // What each column means, for reading a solution back.
    struct Column {
        enum Kind { template_unit, member, loss, aggregate } kind;
        int index;  // template, or group
        int position = 0;
    };
    std::vector<Column> column;
    struct Template {
        StructureKind kind;
        std::vector<StructureLeg> legs;  // per unit of the template
    };
    std::vector<Template> templates;
    int groups = 0;
    std::vector<int> capacity_row;  // per option position, then the stock line
};

Model build_model(const Portfolio& p, const RuleSet& r, const SolveOptions& o = {});

// Reads an integer solution (values within 1e-6 of integers) of a model back into
// structures and residuals, without requirements; check_solution fills those.
Solution read_solution(const Model& m, const Portfolio& p, const std::vector<double>& x);

}  // namespace pairing
