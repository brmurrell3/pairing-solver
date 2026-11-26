#pragma once

#include <limits>
#include <vector>

namespace pairing {

// The solver core (spec §3.4): it knows nothing about options.

constexpr double lp_infinity = std::numeric_limits<double>::infinity();

// minimize cost·x  subject to  row_lo ≤ A x ≤ row_up  and  col_lo ≤ x ≤ col_up.
// Every column needs a finite lower bound; upper bounds may be infinite.
struct Lp {
    struct Entry {
        int row;
        double value;
    };
    std::vector<double> row_lo, row_up;
    std::vector<std::vector<Entry>> columns;
    std::vector<double> cost, col_lo, col_up;

    int rows() const { return static_cast<int>(row_lo.size()); }
    int cols() const { return static_cast<int>(columns.size()); }
    int add_row(double lo, double up);
    int add_column(double cost, double lo, double up, std::vector<Entry> entries = {});
};

enum class LpStatus { optimal, infeasible, unbounded, iteration_limit };

// Variables 0..cols-1 are the columns; cols+i is row i's activity (its logical variable).
struct LpBasis {
    std::vector<int> head;            // the basic variable of each row
    std::vector<signed char> state;   // per variable: 0 basic, 1 at lower bound, 2 at upper bound
    bool empty() const { return head.empty(); }
};

struct LpSolution {
    LpStatus status = LpStatus::iteration_limit;
    double objective = 0;
    std::vector<double> x;         // column values
    std::vector<double> row_dual;  // ∂objective/∂(row bound) for a row held at a bound; 0 otherwise
    std::vector<double> reduced_cost;  // per column; 0 for a basic column
    LpBasis basis;
    int iterations = 0;
};

// Dense bounded-variable dual simplex with an explicit basis inverse, sized for one
// subproblem (tens to a few hundred rows). Bounds may change between solves; the matrix
// and costs may not, so a previous basis stays dual feasible and is a warm start (spec §3.2).
class DualSimplex {
public:
    explicit DualSimplex(const Lp& lp);

    void set_bounds(int col, double lo, double up);
    double lower(int col) const { return lo_[col]; }
    double upper(int col) const { return up_[col]; }

    // An empty start continues from the current basis: the slack basis on the first call,
    // otherwise the previous solve's.
    LpSolution solve(const LpBasis& start = {});

private:
    const Lp& lp_;
    int m_, n_;
    std::vector<double> lo_, up_, cost_;  // over columns then logicals
    std::vector<signed char> state_;
    std::vector<int> head_;
    std::vector<double> binv_;  // m×m, row-major
    std::vector<double> norm_;  // squared norm of each row of binv_, for steepest-edge pricing
    std::vector<double> x_, d_, alpha_;
    int since_refactor_ = 0;

    double nonbasic_value(int j) const;
    double dot_row(const double* rho, int j) const;
    void refactor();
    void compute_primal();
    void compute_dual();
    bool restore_dual_feasibility(double tol);
    int choose_row(bool bland, double slack = 1) const;
    void load(const LpBasis& b);
    LpSolution finish(LpStatus status, int iterations) const;
};

enum class MipStatus {
    optimal,     // the incumbent is within the requested gap of the optimum
    node_limit,  // stopped at the node limit; x holds the best incumbent, if any
    infeasible,
    unbounded,   // the continuous relaxation is unbounded
    lp_failed,   // a node LP hit its iteration limit
};
const char* status_name(MipStatus s);

struct MipOptions {
    // A node is pruned when its bound is not below the incumbent by more than
    // max(abs_tol, rel_gap * |offset + incumbent|). offset turns the LP objective into the
    // quantity the gap is relative to (for margin: the all-standalone total).
    double abs_tol = 1e-9;
    double rel_gap = 0;
    double offset = 0;
    long node_limit = 1'000'000;
    // A known feasible integer point (empty: none). Branch-and-bound starts with it as the
    // incumbent, so the gap test can prune from the first node.
    std::vector<double> start;
    // Branching priority per column (empty: all equal). Fractional columns of the highest
    // priority present are branched on, and fixed by the root dive, first.
    std::vector<int> priority;
    // A basis to start the root from (empty: the slack basis), such as another account's
    // root basis on the same model shape (spec §3.2). Ignored if its size does not match.
    LpBasis root_basis;
};

struct MipSolution {
    MipStatus status = MipStatus::infeasible;
    double objective = 0;
    double bound = 0;  // proven lower bound on the optimum
    std::vector<double> x;
    LpSolution root;   // the continuous relaxation
    long nodes = 0;
    long iterations = 0;
};

// Branch-and-bound over the integer columns: a rounding dive at the root for a first
// incumbent, then best-first search with plunging. Nodes hold only their bound changes and
// re-solve from the current basis. Every node is pruned or explored, so the result is
// optimal to within the pruning tolerance unless the node limit stops the search first.
MipSolution branch_and_bound(const Lp& lp, const std::vector<bool>& integer, const MipOptions& o);

}  // namespace pairing
