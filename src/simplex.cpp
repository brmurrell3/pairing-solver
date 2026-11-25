#include "pairing/simplex.hpp"

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>

namespace pairing {

namespace {

constexpr signed char basic = 0, at_lower = 1, at_upper = 2;

// Costs are dollars per unit and quantities are contracts or shares, so absolute
// tolerances near the limit of double precision keep objectives well inside the 1e-9
// relative agreement the tests demand.
constexpr double primal_tol = 1e-9;  // bound violation, scaled by 1 + |bound|
constexpr double dual_tol = 1e-9;    // wrong-signed reduced cost; also Harris's relaxation
constexpr double pivot_tol = 1e-9;   // smallest pivot-row entry the ratio test accepts
constexpr double singular_tol = 1e-11;
constexpr int refactor_every = 64;
// Degenerate iterations in a row before switching to Bland's rule (smallest-index leaving
// and entering variables), which cannot cycle. The switch lasts until the objective moves.
constexpr int stall_limit = 50;
constexpr int max_iterations = 200000;
// Stands in for an infinite bound where a nonbasic variable must sit for dual feasibility.
// An optimum that still uses one is reported unbounded.
constexpr double artificial_bound = 1e9;

double sign(double v) { return v < 0 ? -1.0 : 1.0; }

}  // namespace

int Lp::add_row(double lo, double up) {
    row_lo.push_back(lo);
    row_up.push_back(up);
    return rows() - 1;
}

int Lp::add_column(double c, double lo, double up, std::vector<Entry> entries) {
    columns.push_back(std::move(entries));
    cost.push_back(c);
    col_lo.push_back(lo);
    col_up.push_back(up);
    return cols() - 1;
}

DualSimplex::DualSimplex(const Lp& lp) : lp_(lp), m_(lp.rows()), n_(lp.cols()) {
    if (lp.cost.size() != lp.columns.size() || lp.col_lo.size() != lp.columns.size() ||
        lp.col_up.size() != lp.columns.size() || lp.row_up.size() != lp.row_lo.size())
        throw std::invalid_argument("inconsistent LP dimensions");
    for (const auto& col : lp.columns)
        for (const auto& e : col)
            if (e.row < 0 || e.row >= m_) throw std::invalid_argument("LP entry outside the rows");
    lo_ = lp.col_lo;
    lo_.insert(lo_.end(), lp.row_lo.begin(), lp.row_lo.end());
    up_ = lp.col_up;
    up_.insert(up_.end(), lp.row_up.begin(), lp.row_up.end());
    cost_ = lp.cost;
    cost_.resize(n_ + m_, 0.0);
    x_.assign(n_ + m_, 0.0);
    d_.assign(n_ + m_, 0.0);
    alpha_.assign(n_ + m_, 0.0);

    // Slack basis: B = -I, so every reduced cost is the cost itself and each column starts
    // at the bound its cost sign makes dual feasible.
    state_.assign(n_ + m_, at_lower);
    head_.resize(m_);
    for (int i = 0; i < m_; ++i) {
        head_[i] = n_ + i;
        state_[n_ + i] = basic;
    }
    for (int j = 0; j < n_; ++j) state_[j] = cost_[j] >= 0 ? at_lower : at_upper;
    binv_.assign(static_cast<std::size_t>(m_) * m_, 0.0);
    for (int i = 0; i < m_; ++i) binv_[static_cast<std::size_t>(i) * m_ + i] = -1.0;
}

void DualSimplex::set_bounds(int col, double lo, double up) {
    lo_[col] = lo;
    up_[col] = up;
}

double DualSimplex::nonbasic_value(int j) const {
    double lo = lo_[j], up = up_[j];
    if (state_[j] == at_upper) return std::isfinite(up) ? up : (std::isfinite(lo) ? lo : 0.0) + artificial_bound;
    return std::isfinite(lo) ? lo : (std::isfinite(up) ? up : 0.0) - artificial_bound;
}

// Entry of row vector rho times column j of [A, -I].
double DualSimplex::dot_row(const double* rho, int j) const {
    if (j >= n_) return -rho[j - n_];
    double s = 0;
    for (const auto& e : lp_.columns[j]) s += rho[e.row] * e.value;
    return s;
}

// Gauss-Jordan inversion with partial pivoting. A (near-)singular basis is repaired by
// swapping in the logical variable whose transformed column gives the largest pivot.
void DualSimplex::refactor() {
    const std::size_t m = m_;
    std::vector<double> a(m * m, 0.0), inv(m * m, 0.0);
    for (std::size_t i = 0; i < m; ++i) inv[i * m + i] = 1.0;
    for (std::size_t k = 0; k < m; ++k) {
        int j = head_[k];
        if (j >= n_) a[(j - n_) * m + k] = -1.0;
        else
            for (const auto& e : lp_.columns[j]) a[e.row * m + k] = e.value;
    }
    for (std::size_t k = 0; k < m; ++k) {
        auto pivot_row = [&] {
            std::size_t p = k;
            for (std::size_t i = k + 1; i < m; ++i)
                if (std::fabs(a[i * m + k]) > std::fabs(a[p * m + k])) p = i;
            return p;
        };
        std::size_t p = pivot_row();
        if (std::fabs(a[p * m + k]) < singular_tol) {
            int best = -1;
            double best_v = singular_tol;
            for (int i = 0; i < m_; ++i) {
                if (state_[n_ + i] == basic) continue;
                for (std::size_t r = k; r < m; ++r) {
                    if (std::fabs(inv[r * m + i]) > best_v) {
                        best_v = std::fabs(inv[r * m + i]);
                        best = i;
                    }
                }
            }
            if (best < 0) throw std::runtime_error("singular basis could not be repaired");
            state_[head_[k]] = at_lower;
            head_[k] = n_ + best;
            state_[n_ + best] = basic;
            for (std::size_t r = 0; r < m; ++r) a[r * m + k] = -inv[r * m + best];
            p = pivot_row();
        }
        if (p != k) {
            for (std::size_t c = 0; c < m; ++c) {
                std::swap(a[p * m + c], a[k * m + c]);
                std::swap(inv[p * m + c], inv[k * m + c]);
            }
        }
        double piv = a[k * m + k];
        for (std::size_t c = k; c < m; ++c) a[k * m + c] /= piv;
        for (std::size_t c = 0; c < m; ++c) inv[k * m + c] /= piv;
        for (std::size_t i = 0; i < m; ++i) {
            if (i == k) continue;
            double f = a[i * m + k];
            if (f == 0) continue;
            for (std::size_t c = k; c < m; ++c) a[i * m + c] -= f * a[k * m + c];
            for (std::size_t c = 0; c < m; ++c) inv[i * m + c] -= f * inv[k * m + c];
        }
    }
    binv_ = std::move(inv);
    since_refactor_ = 0;
}

// x_B = -B⁻¹ N x_N, since [A, -I] x = 0.
void DualSimplex::compute_primal() {
    std::vector<double> r(m_, 0.0);
    for (int j = 0; j < n_ + m_; ++j) {
        if (state_[j] == basic) continue;
        double v = nonbasic_value(j);
        x_[j] = v;
        if (v == 0) continue;
        if (j >= n_) r[j - n_] -= v;
        else
            for (const auto& e : lp_.columns[j]) r[e.row] += e.value * v;
    }
    for (int k = 0; k < m_; ++k) {
        const double* row = &binv_[static_cast<std::size_t>(k) * m_];
        double s = 0;
        for (int i = 0; i < m_; ++i) s += row[i] * r[i];
        x_[head_[k]] = -s;
    }
}

void DualSimplex::compute_dual() {
    std::vector<double> pi(m_, 0.0);
    for (int k = 0; k < m_; ++k) {
        double c = cost_[head_[k]];
        if (c == 0) continue;
        const double* row = &binv_[static_cast<std::size_t>(k) * m_];
        for (int i = 0; i < m_; ++i) pi[i] += c * row[i];
    }
    for (int j = 0; j < n_ + m_; ++j) d_[j] = state_[j] == basic ? 0.0 : cost_[j] - dot_row(pi.data(), j);
}

// Every variable is boxed or carries an artificial bound, so a wrong-signed reduced cost
// is fixed by moving the variable to its other bound.
bool DualSimplex::restore_dual_feasibility() {
    bool flipped = false;
    for (int j = 0; j < n_ + m_; ++j) {
        if (state_[j] == basic || lo_[j] == up_[j]) continue;
        if (state_[j] == at_lower && d_[j] < -dual_tol) {
            state_[j] = at_upper;
            flipped = true;
        } else if (state_[j] == at_upper && d_[j] > dual_tol) {
            state_[j] = at_lower;
            flipped = true;
        }
    }
    return flipped;
}

int DualSimplex::choose_row(bool bland) const {
    int best = -1;
    double best_v = 0;
    for (int k = 0; k < m_; ++k) {
        int j = head_[k];
        double v = 0;
        if (x_[j] < lo_[j] - primal_tol * (1 + std::fabs(lo_[j]))) v = lo_[j] - x_[j];
        else if (x_[j] > up_[j] + primal_tol * (1 + std::fabs(up_[j]))) v = x_[j] - up_[j];
        if (v <= 0) continue;
        if (bland ? (best < 0 || j < head_[best]) : v > best_v) {
            best = k;
            best_v = v;
        }
    }
    return best;
}

void DualSimplex::load(const LpBasis& b) {
    if (static_cast<int>(b.head.size()) != m_ || static_cast<int>(b.state.size()) != n_ + m_)
        throw std::invalid_argument("basis has the wrong size");
    head_ = b.head;
    state_ = b.state;
    refactor();
}

LpSolution DualSimplex::finish(LpStatus status, int iterations) const {
    LpSolution s;
    s.status = status;
    s.iterations = iterations;
    s.x.assign(x_.begin(), x_.begin() + n_);
    for (int j = 0; j < n_; ++j) s.objective += cost_[j] * x_[j];
    s.row_dual.assign(m_, 0.0);
    for (int i = 0; i < m_; ++i)
        if (state_[n_ + i] != basic) s.row_dual[i] = d_[n_ + i];
    s.basis.head = head_;
    s.basis.state = state_;
    return s;
}

LpSolution DualSimplex::solve(const LpBasis& start) {
    for (int j = 0; j < n_ + m_; ++j)
        if (lo_[j] > up_[j]) return finish(LpStatus::infeasible, 0);
    if (!start.empty() && (start.head != head_ || start.state != state_)) load(start);
    compute_primal();
    compute_dual();
    if (restore_dual_feasibility()) compute_primal();

    int iterations = 0, degenerate = 0, checks = 0;
    bool bland = false;
    std::vector<double> w(m_);
    while (iterations < max_iterations) {
        int r = choose_row(bland);
        if (r < 0) {
            // Confirm on a fresh factorization before declaring optimality.
            if (++checks > 50) break;
            refactor();
            compute_primal();
            compute_dual();
            bool flipped = restore_dual_feasibility();
            if (flipped) compute_primal();
            if (flipped || choose_row(false) >= 0) continue;
            for (int j = 0; j < n_; ++j)
                if (std::fabs(x_[j]) >= artificial_bound / 2) return finish(LpStatus::unbounded, iterations);
            return finish(LpStatus::optimal, iterations);
        }

        int p = head_[r];
        double xp = x_[p];
        bool to_lower = xp < lo_[p];
        double target = to_lower ? lo_[p] : up_[p];
        double s = to_lower ? 1.0 : -1.0;
        const double* rho = &binv_[static_cast<std::size_t>(r) * m_];

        // Dual ratio test. Moving x_p toward its bound needs a nonbasic variable that can
        // move in the direction delta_j = -s·alpha_j allows; the ratio d_j/delta_j is how
        // far the duals can move before d_j changes sign. Harris's two passes trade a
        // dual_tol slack in that ratio for the largest available pivot.
        double theta_max = lp_infinity;
        for (int j = 0; j < n_ + m_; ++j) {
            if (state_[j] == basic) continue;
            alpha_[j] = dot_row(rho, j);
            if (lo_[j] == up_[j]) continue;
            double delta = -s * alpha_[j];
            bool eligible = state_[j] == at_lower ? delta > pivot_tol : delta < -pivot_tol;
            if (eligible && !bland) theta_max = std::min(theta_max, (d_[j] * sign(delta) + dual_tol) / std::fabs(delta));
        }
        int q = -1;
        double q_key = 0;
        for (int j = 0; j < n_ + m_; ++j) {
            if (state_[j] == basic || lo_[j] == up_[j]) continue;
            double delta = -s * alpha_[j];
            bool eligible = state_[j] == at_lower ? delta > pivot_tol : delta < -pivot_tol;
            if (!eligible) continue;
            double ratio = d_[j] * sign(delta) / std::fabs(delta);
            if (bland) {
                if (q < 0 || ratio < q_key - 1e-12) {
                    q = j;
                    q_key = ratio;
                }
            } else if (ratio <= theta_max && std::fabs(delta) > q_key) {
                q = j;
                q_key = std::fabs(delta);
            }
        }
        if (q < 0) {
            // No variable can repair row r: the dual is unbounded, so the primal is
            // infeasible. Confirm on a fresh factorization first.
            if (since_refactor_ > 0) {
                refactor();
                compute_primal();
                compute_dual();
                if (restore_dual_feasibility()) compute_primal();
                continue;
            }
            return finish(LpStatus::infeasible, iterations);
        }

        // Column q in terms of the basis.
        std::fill(w.begin(), w.end(), 0.0);
        for (int k = 0; k < m_; ++k) w[k] = dot_row(&binv_[static_cast<std::size_t>(k) * m_], q);
        if (std::fabs(w[r] - alpha_[q]) > 1e-7 * (1 + std::fabs(w[r]))) {
            refactor();
            compute_primal();
            compute_dual();
            if (restore_dual_feasibility()) compute_primal();
            continue;
        }

        double delta_q = -s * alpha_[q];
        double theta = std::max(0.0, d_[q] / delta_q);  // Harris may accept a slightly wrong-signed d_q
        for (int j = 0; j < n_ + m_; ++j)
            if (state_[j] != basic) d_[j] -= theta * (-s * alpha_[j]);
        d_[p] = s * theta;
        d_[q] = 0;

        double dx = (xp - target) / w[r];
        for (int k = 0; k < m_; ++k) x_[head_[k]] -= w[k] * dx;
        x_[q] += dx;
        x_[p] = target;
        state_[p] = to_lower ? at_lower : at_upper;
        state_[q] = basic;
        head_[r] = q;

        double* prow = &binv_[static_cast<std::size_t>(r) * m_];
        double piv = w[r];
        for (int c = 0; c < m_; ++c) prow[c] /= piv;
        for (int k = 0; k < m_; ++k) {
            if (k == r || w[k] == 0) continue;
            double f = w[k];
            double* row = &binv_[static_cast<std::size_t>(k) * m_];
            for (int c = 0; c < m_; ++c) row[c] -= f * prow[c];
        }

        ++iterations;
        if (++since_refactor_ >= refactor_every) {
            refactor();
            compute_primal();
            compute_dual();
            if (restore_dual_feasibility()) compute_primal();
        }
        // The dual objective rises by theta times the violation removed.
        if (theta * std::fabs(xp - target) > 1e-12) {
            degenerate = 0;
            bland = false;
        } else if (++degenerate > stall_limit) {
            bland = true;
        }
    }
    return finish(LpStatus::iteration_limit, iterations);
}

MipSolution branch_and_bound(const Lp& lp, const std::vector<bool>& integer, double prune_tol) {
    // Values this close to an integer count as integral; callers round them.
    constexpr double integer_tol = 1e-6;
    struct Node {
        std::vector<double> lo, up;
        LpBasis basis;
        double bound;
    };
    DualSimplex simplex(lp);
    MipSolution out;
    double incumbent = lp_infinity;
    std::vector<Node> stack;
    stack.push_back({lp.col_lo, lp.col_up, {}, -lp_infinity});
    bool root = true;
    while (!stack.empty()) {
        Node node = std::move(stack.back());
        stack.pop_back();
        if (node.bound >= incumbent - prune_tol) continue;
        for (int j = 0; j < lp.cols(); ++j)
            if (integer[j]) simplex.set_bounds(j, node.lo[j], node.up[j]);
        LpSolution sol = simplex.solve(node.basis);
        if (std::getenv("BB_TRACE")) { std::fprintf(stderr, "node %d status %d obj %.6f it %d stack %zu\n", out.nodes, (int)sol.status, sol.objective, sol.iterations, stack.size()); }
        ++out.nodes;
        out.iterations += sol.iterations;
        if (root) {
            out.root = sol;
            root = false;
            if (sol.status != LpStatus::optimal) {
                out.status = sol.status;
                return out;
            }
        }
        if (sol.status == LpStatus::infeasible) continue;
        if (sol.status != LpStatus::optimal) throw std::runtime_error("branch-and-bound node LP did not solve");
        if (sol.objective >= incumbent - prune_tol) continue;

        int branch = -1;
        double most = integer_tol;
        for (int j = 0; j < lp.cols(); ++j) {
            if (!integer[j]) continue;
            double f = sol.x[j] - std::floor(sol.x[j]);
            double frac = std::min(f, 1 - f);
            if (frac > most) {
                most = frac;
                branch = j;
            }
        }
        if (branch < 0) {
            incumbent = sol.objective;
            out.x = sol.x;
            continue;
        }
        double v = sol.x[branch];
        if (std::getenv("BB_TRACE")) { std::fprintf(stderr, "  branch x%d = %.9f bounds [%g,%g]\n", branch, v, node.lo[branch], node.up[branch]); }
        Node down{node.lo, node.up, sol.basis, sol.objective};
        down.up[branch] = std::floor(v);
        Node up{std::move(node.lo), std::move(node.up), sol.basis, sol.objective};
        up.lo[branch] = std::ceil(v);
        // A fractional upper bound (a template limited by a holding) leaves one side empty.
        bool up_empty = up.lo[branch] > up.up[branch];
        // The side nearer the LP value is explored first, so it goes on the stack last.
        if (up_empty) {
            stack.push_back(std::move(down));
        } else if (v - std::floor(v) < 0.5) {
            stack.push_back(std::move(up));
            stack.push_back(std::move(down));
        } else {
            stack.push_back(std::move(down));
            stack.push_back(std::move(up));
        }
    }
    out.status = incumbent < lp_infinity ? LpStatus::optimal : LpStatus::infeasible;
    out.objective = incumbent;
    return out;
}

}  // namespace pairing
