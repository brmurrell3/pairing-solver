#include "pairing/simplex.hpp"

#include <algorithm>
#include <cstdint>
#include <cmath>
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
bool DualSimplex::restore_dual_feasibility(double tol) {
    bool flipped = false;
    for (int j = 0; j < n_ + m_; ++j) {
        if (state_[j] == basic || lo_[j] == up_[j]) continue;
        if (state_[j] == at_lower && d_[j] < -tol) {
            state_[j] = at_upper;
            flipped = true;
        } else if (state_[j] == at_upper && d_[j] > tol) {
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
        if (!bland) {
            // Dual steepest edge: the violation over the norm of B⁻¹'s row, the step's
            // length in dual space; the dense inverse gives the norm exactly.
            const double* rho = &binv_[static_cast<std::size_t>(k) * m_];
            double norm = 0;
            for (int c = 0; c < m_; ++c) norm += rho[c] * rho[c];
            v = v * v / std::max(norm, 1e-12);
        }
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
    if (restore_dual_feasibility(dual_tol)) compute_primal();

    int iterations = 0, degenerate = 0, checks = 0;
    bool bland = false;
    // The dual objective (cost·x at the current basis) should rise. Steps that pass the
    // degeneracy test but are undone by refactorization and bound flips can cycle with no
    // net progress; after that many steps without a rise, Bland's rule stays on.
    bool stuck = false;
    long since_rise = 0;
    double best_objective = -lp_infinity;
    // When that happens, the costs are perturbed instead: each nonbasic variable's cost
    // moves a little further in the direction that keeps its reduced cost correctly signed,
    // which breaks the ties that let the steps cycle. At the perturbed optimum the true
    // costs come back and the solve continues from that basis.
    std::vector<double> true_cost;
    int perturbations = 0;
    auto unperturb = [&] {
        if (true_cost.empty()) return false;
        cost_ = std::move(true_cost);
        true_cost.clear();
        compute_dual();
        if (restore_dual_feasibility(dual_tol)) compute_primal();
        stuck = bland = false;
        since_rise = 0;
        best_objective = -lp_infinity;
        return true;
    };
    std::vector<double> w(m_);
    while (iterations < max_iterations) {
        int r = choose_row(bland);
        if (r < 0) {
            // Confirm on a fresh factorization before declaring optimality.
            if (++checks > 50) break;
            refactor();
            compute_primal();
            compute_dual();
            // Each refactorization moves reduced costs near zero by rounding noise of about
            // dual_tol, and two such columns can flip each other's bound forever. A widening
            // threshold on repeated checks ends that; it costs at most 100·dual_tol per unit
            // of a column's range in the objective.
            bool flipped = restore_dual_feasibility(checks > 10 ? 100 * dual_tol : checks > 1 ? 10 * dual_tol : dual_tol);
            if (flipped) compute_primal();
            if (flipped || choose_row(false) >= 0) continue;
            if (unperturb()) continue;
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
                if (restore_dual_feasibility(dual_tol)) compute_primal();
                continue;
            }
            unperturb();
            return finish(LpStatus::infeasible, iterations);
        }

        // Column q in terms of the basis.
        std::fill(w.begin(), w.end(), 0.0);
        for (int k = 0; k < m_; ++k) w[k] = dot_row(&binv_[static_cast<std::size_t>(k) * m_], q);
        if (std::fabs(w[r] - alpha_[q]) > 1e-7 * (1 + std::fabs(w[r]))) {
            refactor();
            compute_primal();
            compute_dual();
            if (restore_dual_feasibility(dual_tol)) compute_primal();
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
            if (restore_dual_feasibility(dual_tol)) compute_primal();
        }
        // The dual objective rises by theta times the violation removed.
        if (!stuck) {
            double objective = 0;
            for (int j = 0; j < n_; ++j) objective += cost_[j] * x_[j];
            if (objective > best_objective + 1e-9 * (1 + std::fabs(objective))) {
                best_objective = objective;
                since_rise = 0;
            } else if (++since_rise > 10L * (m_ + n_)) {
                if (true_cost.empty() && perturbations < 3) {
                    ++perturbations;
                    true_cost = cost_;
                    std::uint64_t seed = 0x9e3779b97f4a7c15ULL * static_cast<std::uint64_t>(perturbations);
                    for (int j = 0; j < n_ + m_; ++j) {
                        seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
                        double u = 0.5 + 0.5 * static_cast<double>(seed >> 11) / 9007199254740992.0;
                        double delta = 1e-7 * u * (1 + std::fabs(cost_[j]));
                        if (state_[j] == at_upper) cost_[j] -= delta;
                        else if (state_[j] == at_lower) cost_[j] += delta;
                    }
                    compute_dual();
                    if (restore_dual_feasibility(dual_tol)) compute_primal();
                    since_rise = 0;
                    best_objective = -lp_infinity;
                } else {
                    stuck = bland = true;
                }
            }
        }
        if (stuck) {
            bland = true;
        } else if (theta * std::fabs(xp - target) > 1e-12) {
            degenerate = 0;
            bland = false;
        } else if (++degenerate > stall_limit) {
            bland = true;
        }
    }
    unperturb();
    return finish(LpStatus::iteration_limit, iterations);
}

const char* status_name(MipStatus s) {
    switch (s) {
        case MipStatus::optimal: return "optimal";
        case MipStatus::node_limit: return "node_limit";
        case MipStatus::infeasible: return "infeasible";
        case MipStatus::unbounded: return "unbounded";
        case MipStatus::lp_failed: return "lp_failed";
    }
    return "?";
}

namespace {

// A rounding dive from a node's LP solution: fix the integer column nearest an integer to
// that integer, re-solve from the current basis, and repeat until the solution is on the
// grid. A fix that makes the LP infeasible is tried on the other side; when both fail, the
// dive backtracks to earlier fixes' other sides, within a budget. Fixing one count of a
// linked set (the share-size aggregates of one balance row) can leave the last one no
// integer value, which only an earlier choice can repair. Restores the bounds.
bool dive(DualSimplex& simplex, const Lp& lp, const std::vector<bool>& integer, const std::vector<int>& priority,
          const std::vector<double>* guide, LpSolution sol, double integer_tol, long& iterations, std::vector<double>& x,
          double& objective) {
    struct Fix {
        int col;
        double lo, up;  // the bounds before the fix
        double other;   // the side not yet tried, or NaN
        LpBasis basis;  // the basis before the fix
    };
    std::vector<Fix> fixes;
    int backtracks = 20;
    bool found = false;
    // Tries t for column j from basis b; on success the dive continues from the result.
    auto attempt = [&](int j, double t, const LpBasis& b) {
        if (t < simplex.lower(j) - 1e-9 || t > simplex.upper(j) + 1e-9) return false;
        simplex.set_bounds(j, t, t);
        LpSolution next = simplex.solve(b);
        iterations += next.iterations;
        if (next.status != LpStatus::optimal) return false;
        sol = std::move(next);
        return true;
    };
    for (long steps = 0; steps <= 4L * lp.cols() + 100; ++steps) {
        int pick = -1, level = 0;
        double nearest = 1;
        for (int j = 0; j < lp.cols(); ++j) {
            if (!integer[j]) continue;
            double f = sol.x[j] - std::floor(sol.x[j]);
            double d = std::min(f, 1 - f);
            if (d <= integer_tol) continue;
            int pr = priority.empty() ? 0 : priority[j];
            if (pick < 0 || pr > level || (pr == level && d < nearest)) {
                nearest = d;
                pick = j;
                level = pr;
            }
        }
        if (pick < 0) {
            found = true;
            x = sol.x;
            objective = sol.objective;
            break;
        }
        const double v = sol.x[pick], lo = simplex.lower(pick), up = simplex.upper(pick);
        // Guided by an incumbent, the dive rounds toward it where it can, searching near a
        // known good solution; otherwise toward the nearer integer.
        double first = std::round(v);
        if (guide && ((*guide)[pick] == std::floor(v) || (*guide)[pick] == std::ceil(v))) first = (*guide)[pick];
        double second = first > v ? std::floor(v) : std::ceil(v);
        if (first < lo || first > up) std::swap(first, second);
        fixes.push_back({pick, lo, up, (second < lo || second > up) ? std::nan("") : second, sol.basis});
        if (first >= lo && first <= up && attempt(pick, first, fixes.back().basis)) continue;
        // Undo fixes, newest first, until one has an untried side that solves.
        bool resumed = false;
        while (!fixes.empty() && !resumed) {
            Fix& f = fixes.back();
            if (!std::isnan(f.other) && backtracks-- > 0) {
                double t = f.other;
                f.other = std::nan("");
                if (attempt(f.col, t, f.basis)) {
                    resumed = true;
                    break;
                }
            }
            simplex.set_bounds(f.col, f.lo, f.up);
            fixes.pop_back();
            if (backtracks <= 0) break;
        }
        if (!resumed) break;
    }
    for (auto it = fixes.rbegin(); it != fixes.rend(); ++it) simplex.set_bounds(it->col, it->lo, it->up);
    return found;
}

}  // namespace

MipSolution branch_and_bound(const Lp& lp, const std::vector<bool>& integer, const MipOptions& o) {
    // Values this close to an integer count as integral; callers round them.
    constexpr double integer_tol = 1e-6;
    // A node is its bound changes from the root. Any basis stays dual feasible when only
    // bounds change, so a node re-solves from whatever basis the simplex holds.
    struct Change {
        int col;
        double lo, up;
    };
    struct Node {
        std::vector<Change> changes;
        double bound;
    };
    auto worse = [](const Node& a, const Node& b) { return a.bound > b.bound; };
    std::vector<Node> heap;  // open nodes, best bound on top

    DualSimplex simplex(lp);
    MipSolution out;
    double incumbent = lp_infinity;
    if (!o.start.empty()) {
        incumbent = 0;
        for (int j = 0; j < lp.cols(); ++j) incumbent += lp.cost[j] * o.start[j];
        out.x = o.start;
    }
    // A node is pruned when its bound b cannot beat the incumbent by more than the gap,
    // measured against offset + b: the gap is then relative to the optimum, not to the
    // incumbent. pruned_bound is the lowest bound pruned, a proven bound on the optimum.
    double pruned_bound = lp_infinity;
    auto prune = [&](double b) {
        if (b == -lp_infinity || incumbent == lp_infinity) return false;
        if (b < incumbent - std::max(o.abs_tol, o.rel_gap * std::fabs(o.offset + b))) return false;
        pruned_bound = std::min(pruned_bound, b);
        return true;
    };
    auto pick_branch = [&](const LpSolution& sol) {
        int branch = -1, level = 0;
        double most = 0;
        for (int j = 0; j < lp.cols(); ++j) {
            if (!integer[j]) continue;
            double f = sol.x[j] - std::floor(sol.x[j]);
            double frac = std::min(f, 1 - f);
            if (frac <= integer_tol) continue;
            int pr = o.priority.empty() ? 0 : o.priority[j];
            if (branch < 0 || pr > level || (pr == level && frac > most)) {
                most = frac;
                branch = j;
                level = pr;
            }
        }
        return branch;
    };
    std::vector<double> lo(lp.col_lo), up(lp.col_up);
    auto load = [&](const std::vector<Change>& changes) {
        for (int j = 0; j < lp.cols(); ++j) {
            lo[j] = lp.col_lo[j];
            up[j] = lp.col_up[j];
        }
        for (const auto& c : changes) {
            lo[c.col] = c.lo;
            up[c.col] = c.up;
        }
        for (int j = 0; j < lp.cols(); ++j)
            if (integer[j]) simplex.set_bounds(j, lo[j], up[j]);
    };

    // Best-first search with plunging: after a branch the nearer child is solved at once
    // (depth-first, which finds incumbents), the other waits in the heap; when a plunge
    // ends, the open node with the lowest bound is next (which raises the proven bound).
    Node current{{}, -lp_infinity};
    bool have_current = true, root = true;
    bool searched = false;  // the incumbent came from the search, not from o.start
    for (;;) {
        if (!have_current) {
            while (!heap.empty() && prune(heap.front().bound)) {
                std::pop_heap(heap.begin(), heap.end(), worse);
                heap.pop_back();
            }
            if (heap.empty()) break;
            std::pop_heap(heap.begin(), heap.end(), worse);
            current = std::move(heap.back());
            heap.pop_back();
            have_current = true;
        }
        if (out.nodes >= o.node_limit) {
            double bound = std::min(incumbent, current.bound);
            for (const auto& n : heap) bound = std::min(bound, n.bound);
            out.status = MipStatus::node_limit;
            out.objective = incumbent;
            out.bound = bound;
            return out;
        }
        have_current = false;
        if (prune(current.bound)) continue;
        load(current.changes);
        LpSolution sol = simplex.solve();
        ++out.nodes;
        out.iterations += sol.iterations;
        if (root) {
            out.root = sol;
            root = false;
            if (sol.status == LpStatus::infeasible || sol.status == LpStatus::unbounded) {
                out.status = sol.status == LpStatus::infeasible ? MipStatus::infeasible : MipStatus::unbounded;
                return out;
            }
            std::vector<double> x;
            double obj = 0;
            if (sol.status == LpStatus::optimal &&
                dive(simplex, lp, integer, o.priority, nullptr, sol, integer_tol, out.iterations, x, obj) && obj < incumbent) {
                incumbent = obj;
                out.x = std::move(x);
                searched = true;
            }
        }
        if (sol.status == LpStatus::infeasible) continue;
        if (sol.status != LpStatus::optimal) {
            out.status = MipStatus::lp_failed;
            out.objective = incumbent;
            return out;
        }
        if (prune(sol.objective)) continue;
        // Dive again now and then: the incumbent, not the bound, is what usually stops a
        // gap-limited search, and a dive from deep in the tree often improves it.
        if (out.nodes % 64 == 0) {
            std::vector<double> x;
            double obj = 0;
            if (dive(simplex, lp, integer, o.priority, searched ? &out.x : nullptr, sol, integer_tol, out.iterations, x,
                     obj) &&
                obj < incumbent) {
                incumbent = obj;
                out.x = std::move(x);
                searched = true;
                if (prune(sol.objective)) continue;
            }
        }

        int branch = pick_branch(sol);
        if (branch < 0) {
            incumbent = sol.objective;
            out.x = sol.x;
            searched = true;
            continue;
        }
        const double v = sol.x[branch];
        Node down{current.changes, sol.objective};
        down.changes.push_back({branch, lo[branch], std::floor(v)});
        // A fractional upper bound (a template limited by a holding) leaves one side empty.
        const bool up_empty = std::ceil(v) > up[branch];
        Node upper{std::move(current.changes), sol.objective};
        upper.changes.push_back({branch, std::ceil(v), up[branch]});
        Node* first = (up_empty || v - std::floor(v) < 0.5) ? &down : &upper;
        Node* second = first == &down ? &upper : &down;
        if (!(up_empty && second == &upper)) {
            heap.push_back(std::move(*second));
            std::push_heap(heap.begin(), heap.end(), worse);
        }
        current = std::move(*first);
        have_current = true;
    }
    out.status = incumbent < lp_infinity ? MipStatus::optimal : MipStatus::infeasible;
    out.objective = incumbent;
    out.bound = std::min(incumbent, pruned_bound);
    return out;
}

}  // namespace pairing
