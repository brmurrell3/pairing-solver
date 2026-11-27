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

// Bounded-variable dual simplex with dual steepest-edge pricing, for one subproblem.
// The basis is held as a sparse LU factorization with product-form updates (Factor).
// Bounds may change between solves; the matrix and costs may not, so a previous basis
// stays dual feasible and is a warm start (spec §3.2).
class DualSimplex {
public:
    explicit DualSimplex(const Lp& lp);

    void set_bounds(int col, double lo, double up);
    double lower(int col) const { return lo_[col]; }
    double upper(int col) const { return up_[col]; }

    // An empty start continues from the current basis: the slack basis on the first call,
    // otherwise the previous solve's.
    LpSolution solve(const LpBasis& start = {});

    // The basis factorization: B = L·U from a left-looking LU whose column order comes
    // from peeling row and column singletons (on a 1,000-series book 1,160 of 1,182 basis
    // columns peel, leaving a 22-column nucleus, so L and U have almost no fill), then one
    // eta column per basis change. Solves cost O(nnz(L, U, etas)) instead of the O(m²) of
    // the explicit inverse it replaced.
    class Factor {
    public:
        // cols[k]: basis position k's column (row, value). A column with no usable pivot
        // is replaced by the logical of an unpivoted row; repairs lists (position, row).
        void factor(int m, const std::vector<std::vector<Lp::Entry>>& cols, std::vector<std::pair<int, int>>& repairs);
        // B⁻¹a: in indexed by row (overwritten), out by basis position.
        void ftran(std::vector<double>& in, std::vector<double>& out) const;
        // cᵀB⁻¹: in indexed by basis position (overwritten), out by row.
        void btran(std::vector<double>& in, std::vector<double>& out) const;
        // Position r's column became one whose B⁻¹-image is w.
        void update(int r, const std::vector<double>& w);

    private:
        int m_ = 0;
        std::vector<int> position_, row_;  // per pivot, in elimination order
        std::vector<double> diag_;
        std::vector<int> u_start_, u_pivot_;  // U by pivot: entries in earlier pivots' rows
        std::vector<double> u_value_;
        std::vector<int> ur_start_, ur_pivot_;  // the same entries by earlier pivot, for btran
        std::vector<double> ur_value_;
        std::vector<int> l_row_, l_start_, l_index_;  // L as elimination steps on rows
        std::vector<double> l_value_;
        std::vector<int> eta_r_, eta_start_, eta_index_;
        std::vector<double> eta_value_;
    };

    // The basis with its factorization, so a caller can return to it without refactoring.
    struct Snapshot {
        std::vector<int> head;
        std::vector<signed char> state;
        Factor factor;
        std::vector<double> norm;
        int since_refactor = 0;
    };
    Snapshot save() const { return {head_, state_, factor_, norm_, since_refactor_}; }
    void restore(Snapshot s);

private:
    const Lp& lp_;
    int m_, n_;
    std::vector<double> lo_, up_, cost_;  // over columns then logicals
    std::vector<int> row_start_, row_col_;  // A by rows, for the pivot row
    std::vector<double> row_value_;
    std::vector<signed char> state_;
    std::vector<int> head_;
    Factor factor_;
    std::vector<double> norm_;  // per basis position: squared norm of B⁻¹'s row, for steepest-edge pricing
    std::vector<double> rho_, work_, work2_;  // row r of B⁻¹; scratch for solves
    std::vector<int> cand_;                   // variables with a nonzero in the pivot row
    std::vector<int> eligible_;               // those that may enter
    std::vector<char> in_cand_;
    std::vector<double> x_, d_, alpha_;
    int since_refactor_ = 0;
    bool primal_current_ = false;  // x_ matches the basis and bounds (pivots and set_bounds keep it)
    bool dual_current_ = false;
    int pivots_since_compute_ = 0;
    bool artificial_in_use_ = true;  // some nonbasic variable sits at an artificial bound  // pivots since x_ and d_ were last computed from scratch    // d_ matches the basis and costs (pivots keep it; bounds do not enter)

    double nonbasic_value(int j) const;
    double dot_row(const double* rho, int j) const;
    void refactor();
    void column(int j, std::vector<double>& by_row) const;  // column j of [A, -I], dense
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
    // An integer point near which to look for an incumbent, feasible or not (empty: none),
    // such as the previous pairing of a book that has since changed.
    std::vector<double> guide;
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
// The same on the caller's simplex, built on lp with its bounds, so a search starts from the
// basis and inverse the last one left (a pre-trade check re-solving one book after each
// order, spec §3.2). On return the simplex is back at the root's optimal basis, with the
// integer columns' bounds reset to lp's.
MipSolution branch_and_bound(DualSimplex& simplex, const Lp& lp, const std::vector<bool>& integer, const MipOptions& o);

}  // namespace pairing
