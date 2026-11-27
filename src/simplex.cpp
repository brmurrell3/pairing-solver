#include "pairing/simplex.hpp"

#include <algorithm>
#include <cstdint>
#include <cmath>
#include <cstdlib>
#include <optional>
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

// A single running sum is a chain of dependent adds the compiler may not reorder (no
// -ffast-math); four independent sums let it vectorize and pipeline.
double dot(const double* a, const double* b, int n) {
    double s0 = 0, s1 = 0, s2 = 0, s3 = 0;
    int i = 0;
    for (; i + 4 <= n; i += 4) {
        s0 += a[i] * b[i];
        s1 += a[i + 1] * b[i + 1];
        s2 += a[i + 2] * b[i + 2];
        s3 += a[i + 3] * b[i + 3];
    }
    for (; i < n; ++i) s0 += a[i] * b[i];
    return (s0 + s1) + (s2 + s3);
}

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
    row_start_.assign(m_ + 1, 0);
    for (const auto& col : lp.columns)
        for (const auto& e : col) ++row_start_[e.row + 1];
    for (int i = 0; i < m_; ++i) row_start_[i + 1] += row_start_[i];
    row_col_.resize(row_start_[m_]);
    row_value_.resize(row_start_[m_]);
    {
        std::vector<int> fill(row_start_.begin(), row_start_.end() - 1);
        for (int j = 0; j < n_; ++j)
            for (const auto& e : lp.columns[j]) {
                row_col_[fill[e.row]] = j;
                row_value_[fill[e.row]++] = e.value;
            }
    }
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
    rho_.assign(m_, 0.0);
    in_cand_.assign(n_ + m_, 0);
    work_.assign(m_, 0.0);
    work2_.assign(m_, 0.0);
    refactor();
    norm_.assign(m_, 1.0);  // B = -I: every row of B⁻¹ has norm 1
}

void DualSimplex::restore(Snapshot s) {
    primal_current_ = dual_current_ = false;
    head_ = std::move(s.head);
    state_ = std::move(s.state);
    factor_ = std::move(s.factor);
    norm_ = std::move(s.norm);
    since_refactor_ = s.since_refactor;
}

// A nonbasic variable whose value moves with its bound moves the basic values with it,
// x_B -= B⁻¹ a_col · delta, so the next solve need not recompute them all (O(m·nnz(a_col))
// here against O(m²) there, and a dive changes one bound per solve).
void DualSimplex::set_bounds(int col, double lo, double up) {
    if (!primal_current_ || state_[col] == basic) {
        lo_[col] = lo;
        up_[col] = up;
        return;
    }
    const double before = x_[col];
    lo_[col] = lo;
    up_[col] = up;
    const double delta = nonbasic_value(col) - before;
    if (delta == 0) return;
    x_[col] += delta;
    column(col, work_);
    factor_.ftran(work_, work2_);
    for (int k = 0; k < m_; ++k)
        if (work2_[k] != 0) x_[head_[k]] -= work2_[k] * delta;
}

void DualSimplex::column(int j, std::vector<double>& by_row) const {
    std::fill(by_row.begin(), by_row.end(), 0.0);
    if (j >= n_) by_row[j - n_] = -1.0;
    else
        for (const auto& e : lp_.columns[j]) by_row[e.row] = e.value;
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

void DualSimplex::Factor::factor(int m, const std::vector<std::vector<Lp::Entry>>& cols,
                                 std::vector<std::pair<int, int>>& repairs) {
    m_ = m;
    position_.clear();
    row_.clear();
    diag_.clear();
    u_start_.assign(1, 0);
    u_pivot_.clear();
    u_value_.clear();
    l_row_.clear();
    l_start_.assign(1, 0);
    l_index_.clear();
    l_value_.clear();
    eta_r_.clear();
    eta_start_.assign(1, 0);
    eta_index_.clear();
    eta_value_.clear();
    repairs.clear();

    // Peel singletons of the active submatrix: a column with one active row pivots there
    // (front of the order, no fill below it); a row with one active column pivots there
    // (back of the order, reversed, every other row of its column pivoted before it). What
    // is left, the nucleus, goes between them with partial pivoting.
    std::vector<std::vector<int>> row_cols(m);
    for (int k = 0; k < m; ++k)
        for (const auto& e : cols[k]) row_cols[e.row].push_back(k);
    std::vector<int> col_count(m), row_count(m);
    std::vector<char> col_active(m, 1), row_active(m, 1);
    std::vector<int> col_queue, row_queue;
    for (int k = 0; k < m; ++k) {
        col_count[k] = static_cast<int>(cols[k].size());
        if (col_count[k] == 1) col_queue.push_back(k);
    }
    for (int i = 0; i < m; ++i) {
        row_count[i] = static_cast<int>(row_cols[i].size());
        if (row_count[i] == 1) row_queue.push_back(i);
    }
    std::vector<std::pair<int, int>> front, back;  // (position, row)
    auto take = [&](int k, int i) {
        col_active[k] = row_active[i] = 0;
        for (const auto& e : cols[k])
            if (row_active[e.row] && --row_count[e.row] == 1) row_queue.push_back(e.row);
        for (int c : row_cols[i])
            if (col_active[c] && --col_count[c] == 1) col_queue.push_back(c);
    };
    while (!col_queue.empty() || !row_queue.empty()) {
        if (!col_queue.empty()) {
            const int k = col_queue.back();
            col_queue.pop_back();
            if (!col_active[k] || col_count[k] != 1) continue;
            int i = -1;
            for (const auto& e : cols[k])
                if (row_active[e.row]) i = e.row;
            front.push_back({k, i});
            take(k, i);
        } else {
            const int i = row_queue.back();
            row_queue.pop_back();
            if (!row_active[i] || row_count[i] != 1) continue;
            int k = -1;
            for (int c : row_cols[i])
                if (col_active[c]) k = c;
            back.push_back({k, i});
            take(k, i);
        }
    }
    std::vector<std::pair<int, int>> order = front;
    for (int k = 0; k < m; ++k)
        if (col_active[k]) order.push_back({k, -1});
    for (auto it = back.rbegin(); it != back.rend(); ++it) order.push_back(*it);
    std::vector<char> reserved(m, 0);
    for (const auto& [k, i] : back) reserved[i] = 1;

    // Left-looking elimination in that order: each column is transformed by the earlier
    // steps of L, its entries in pivoted rows form U, the rest (scaled) a new step of L.
    std::vector<double> z(m, 0.0);
    std::vector<char> touched_mark(m, 0);
    std::vector<int> touched, pivot_of(m, -1);
    std::vector<char> pivoted(m, 0);
    auto touch = [&](int i) {
        if (!touched_mark[i]) {
            touched_mark[i] = 1;
            touched.push_back(i);
        }
    };
    auto apply_l = [&] {
        for (std::size_t l = 0; l < l_row_.size(); ++l) {
            const double vp = z[l_row_[l]];
            if (vp == 0) continue;
            for (int e = l_start_[l]; e < l_start_[l + 1]; ++e) {
                touch(l_index_[e]);
                z[l_index_[e]] -= l_value_[e] * vp;
            }
        }
    };
    for (auto [k, forced] : order) {
        for (const auto& e : cols[k]) {
            touch(e.row);
            z[e.row] = e.value;
        }
        apply_l();
        int p = -1;
        double biggest = 0;
        for (int i : touched)
            if (!pivoted[i]) biggest = std::max(biggest, std::fabs(z[i]));
        if (forced >= 0 && std::fabs(z[forced]) > singular_tol && std::fabs(z[forced]) >= 1e-3 * biggest) p = forced;
        if (p < 0) {
            double best = singular_tol;
            for (int pass = 0; pass < 2 && p < 0; ++pass)
                for (int i : touched)
                    if (!pivoted[i] && (pass == 1 || !reserved[i]) && std::fabs(z[i]) > best) {
                        best = std::fabs(z[i]);
                        p = i;
                    }
        }
        if (p < 0) {
            // No usable pivot: the basis is (nearly) singular here. The logical of an
            // unpivoted row replaces the column; its image is -e_row, since L only acts on
            // pivoted rows' values.
            for (int pass = 0; pass < 2 && p < 0; ++pass)
                for (int i = 0; i < m && p < 0; ++i)
                    if (!pivoted[i] && (pass == 1 || !reserved[i])) p = i;
            if (p < 0) throw std::runtime_error("singular basis could not be repaired");
            for (int i : touched) z[i] = 0;
            touch(p);
            z[p] = -1.0;
            repairs.push_back({k, p});
        }
        const int t = static_cast<int>(position_.size());
        position_.push_back(k);
        row_.push_back(p);
        diag_.push_back(z[p]);
        pivot_of[p] = t;
        pivoted[p] = 1;
        const int l_begin = static_cast<int>(l_index_.size());
        for (int i : touched) {
            if (i != p && z[i] != 0) {
                if (pivot_of[i] >= 0) {
                    u_pivot_.push_back(pivot_of[i]);
                    u_value_.push_back(z[i]);
                } else {
                    l_index_.push_back(i);
                    l_value_.push_back(z[i] / diag_.back());
                }
            }
            z[i] = 0;
            touched_mark[i] = 0;
        }
        touched.clear();
        u_start_.push_back(static_cast<int>(u_pivot_.size()));
        if (static_cast<int>(l_index_.size()) > l_begin) {
            l_row_.push_back(p);
            l_start_.push_back(static_cast<int>(l_index_.size()));
        }
    }
    // U again by the earlier pivot, so btran can push each solved value forward and skip
    // the zeros: a row of B⁻¹ is about 20% dense, and the dot-product form read all of U.
    ur_start_.assign(m + 1, 0);
    for (int e = 0; e < static_cast<int>(u_pivot_.size()); ++e) ++ur_start_[u_pivot_[e] + 1];
    for (int t = 0; t < m; ++t) ur_start_[t + 1] += ur_start_[t];
    ur_pivot_.resize(u_pivot_.size());
    ur_value_.resize(u_pivot_.size());
    std::vector<int> next(ur_start_.begin(), ur_start_.end() - 1);
    for (int t = 0; t < m; ++t)
        for (int e = u_start_[t]; e < u_start_[t + 1]; ++e) {
            ur_pivot_[next[u_pivot_[e]]] = t;
            ur_value_[next[u_pivot_[e]]++] = u_value_[e];
        }
}

void DualSimplex::Factor::ftran(std::vector<double>& v, std::vector<double>& out) const {
    for (std::size_t l = 0; l < l_row_.size(); ++l) {
        const double vp = v[l_row_[l]];
        if (vp == 0) continue;
        for (int e = l_start_[l]; e < l_start_[l + 1]; ++e) v[l_index_[e]] -= l_value_[e] * vp;
    }
    for (int t = m_ - 1; t >= 0; --t) {
        const double xt = v[row_[t]] / diag_[t];
        out[position_[t]] = xt;
        if (xt == 0) continue;
        for (int e = u_start_[t]; e < u_start_[t + 1]; ++e) v[row_[u_pivot_[e]]] -= u_value_[e] * xt;
    }
    for (std::size_t q = 0; q < eta_r_.size(); ++q) {
        const double zr = out[eta_r_[q]];
        if (zr == 0) continue;
        out[eta_r_[q]] = 0;
        for (int e = eta_start_[q]; e < eta_start_[q + 1]; ++e) out[eta_index_[e]] += eta_value_[e] * zr;
    }
}

void DualSimplex::Factor::btran(std::vector<double>& c, std::vector<double>& y) const {
    for (std::size_t q = eta_r_.size(); q-- > 0;) {
        double s = 0;
        for (int e = eta_start_[q]; e < eta_start_[q + 1]; ++e) s += eta_value_[e] * c[eta_index_[e]];
        c[eta_r_[q]] = s;
    }
    for (int t = 0; t < m_; ++t) {
        const double v = c[position_[t]] / diag_[t];
        y[row_[t]] = v;
        if (v == 0) continue;
        for (int e = ur_start_[t]; e < ur_start_[t + 1]; ++e) c[position_[ur_pivot_[e]]] -= ur_value_[e] * v;
    }
    for (std::size_t l = l_row_.size(); l-- > 0;) {
        double acc = 0;
        for (int e = l_start_[l]; e < l_start_[l + 1]; ++e) acc += l_value_[e] * y[l_index_[e]];
        y[l_row_[l]] -= acc;
    }
}

void DualSimplex::Factor::update(int r, const std::vector<double>& w) {
    const double wr = w[r];
    for (int i = 0; i < m_; ++i) {
        if (i == r || w[i] == 0) continue;
        eta_index_.push_back(i);
        eta_value_.push_back(-w[i] / wr);
    }
    eta_index_.push_back(r);
    eta_value_.push_back(1 / wr);
    eta_r_.push_back(r);
    eta_start_.push_back(static_cast<int>(eta_index_.size()));
}

void DualSimplex::refactor() {
    std::vector<std::vector<Lp::Entry>> cols(m_);
    for (int k = 0; k < m_; ++k) {
        const int j = head_[k];
        if (j >= n_) cols[k] = {{j - n_, -1.0}};
        else cols[k] = lp_.columns[j];
    }
    std::vector<std::pair<int, int>> repairs;
    factor_.factor(m_, cols, repairs);
    for (auto [k, row] : repairs) {
        primal_current_ = dual_current_ = false;
        state_[head_[k]] = at_lower;
        head_[k] = n_ + row;
        state_[n_ + row] = basic;
        if (!norm_.empty()) norm_[k] = 1.0;
    }
    since_refactor_ = 0;
}

// x_B = -B⁻¹ N x_N, since [A, -I] x = 0.
void DualSimplex::compute_primal() {
    std::vector<double> r(m_, 0.0);
    artificial_in_use_ = false;
    for (int j = 0; j < n_ + m_; ++j) {
        if (state_[j] == basic) continue;
        double v = nonbasic_value(j);
        x_[j] = v;
        if (v == 0) continue;
        if (!std::isfinite(state_[j] == at_upper ? up_[j] : lo_[j])) artificial_in_use_ = true;
        if (j >= n_) r[j - n_] -= v;
        else
            for (const auto& e : lp_.columns[j]) r[e.row] += e.value * v;
    }
    factor_.ftran(r, work2_);
    for (int k = 0; k < m_; ++k) x_[head_[k]] = -work2_[k];
    pivots_since_compute_ = 0;
    primal_current_ = true;
}

void DualSimplex::compute_dual() {
    std::vector<double> c(m_), pi(m_);
    for (int k = 0; k < m_; ++k) c[k] = cost_[head_[k]];
    factor_.btran(c, pi);
    for (int j = 0; j < n_ + m_; ++j) d_[j] = state_[j] == basic ? 0.0 : cost_[j] - dot_row(pi.data(), j);
    dual_current_ = true;
}

// Every variable is boxed or carries an artificial bound, so a wrong-signed reduced cost
// is fixed by moving the variable to its other bound.
bool DualSimplex::restore_dual_feasibility(double tol) {
    bool flipped = false;
    struct Stale {
        bool& flipped;
        bool& current;
        ~Stale() {
            if (flipped) current = false;
        }
    } stale{flipped, primal_current_};
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

int DualSimplex::choose_row(bool bland, double slack) const {
    int best = -1;
    double best_v = 0;
    for (int k = 0; k < m_; ++k) {
        int j = head_[k];
        double v = 0;
        if (x_[j] < lo_[j] - slack * primal_tol * (1 + std::fabs(lo_[j]))) v = lo_[j] - x_[j];
        else if (x_[j] > up_[j] + slack * primal_tol * (1 + std::fabs(up_[j]))) v = x_[j] - up_[j];
        if (v <= 0) continue;
        if (!bland) {
            // Dual steepest edge: the violation over the norm of B⁻¹'s row, the step's
            // length in dual space. The norms are kept by the update formula of Forrest and
            // Goldfarb; after a load they restart at 1.
            v = v * v / std::max(norm_[k], 1e-12);
        }
        if (bland ? (best < 0 || j < head_[best]) : v > best_v) {
            best = k;
            best_v = v;
        }
    }
    return best;
}

void DualSimplex::load(const LpBasis& b) {
    primal_current_ = dual_current_ = false;
    if (static_cast<int>(b.head.size()) != m_ || static_cast<int>(b.state.size()) != n_ + m_)
        throw std::invalid_argument("basis has the wrong size");
    head_ = b.head;
    state_ = b.state;
    norm_.assign(m_, 1.0);
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
    s.reduced_cost.assign(n_, 0.0);
    for (int j = 0; j < n_; ++j)
        if (state_[j] != basic) s.reduced_cost[j] = d_[j];
    s.basis.head = head_;
    s.basis.state = state_;
    return s;
}

LpSolution DualSimplex::solve(const LpBasis& start) {
    for (int j = 0; j < n_ + m_; ++j)
        if (lo_[j] > up_[j]) return finish(LpStatus::infeasible, 0);
    if (!start.empty() && (start.head != head_ || start.state != state_)) load(start);
    if (!primal_current_) compute_primal();
    if (!dual_current_) compute_dual();
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
    int confirmed_row = -1;  // a row whose infeasibility certificate passed the residual check
    while (iterations < max_iterations) {
        int r = choose_row(bland);
        if (r < 0) {
            // Confirm before declaring optimality: recompute the primal and dual values from
            // the inverse, refreshed when it has taken many updates or a first check failed.
            // Refactoring on every check cost one O(m³) factorization per solve, which
            // dominated the rounding dive's many short solves (24 of 30 s on a 1,000-series book).
            // At 32 updates rather than 16, an order on that book prices 15% faster; the
            // HiGHS tests still agree to 1e-14.
            if (++checks > 50) break;
            if (since_refactor_ >= 32 || (since_refactor_ > 0 && checks > 1)) refactor();
            // After a handful of pivots the kept values are as good as recomputed ones, and the
            // recomputation (a solve and a pass over A each) was a quarter of an order's time
            // on a 1,000-series book, whose dive solves take a few pivots each.
            // Not when a nonbasic variable sits at an artificial bound: values updated from
            // 1e9 lose the digits a recomputation keeps.
            if (pivots_since_compute_ >= 8 || checks > 1 || since_refactor_ == 0 || artificial_in_use_) {
                compute_primal();
                compute_dual();
            }
            // Each refactorization moves reduced costs near zero by rounding noise of about
            // dual_tol, and two such columns can flip each other's bound forever. A widening
            // threshold on repeated checks ends that; it costs at most 100·dual_tol per unit
            // of a column's range in the objective.
            bool flipped = restore_dual_feasibility(checks > 10 ? 100 * dual_tol : checks > 1 ? 10 * dual_tol : dual_tol);
            if (flipped) compute_primal();
            // The same holds for primal values: on rows whose ranges reach 1e8 (loss rows), a
            // refactorization can leave a basic variable a few 1e-9 outside its bound, and
            // pivoting it back can undo itself. Repeated checks accept up to 1,000 times the
            // tolerance, about 1e-6 at a zero bound.
            if (flipped || choose_row(false, checks > 10 ? 1000 : checks > 1 ? 10 : 1) >= 0) continue;
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
        std::fill(work_.begin(), work_.end(), 0.0);
        work_[r] = 1.0;
        factor_.btran(work_, rho_);
        const double* rho = rho_.data();

        // Dual ratio test. Moving x_p toward its bound needs a nonbasic variable that can
        // move in the direction delta_j = -s·alpha_j allows; the ratio d_j/delta_j is how
        // far the duals can move before d_j changes sign. Harris's two passes trade a
        // dual_tol slack in that ratio for the largest available pivot.
        //
        // The pivot row alpha = rho·[A, -I] is formed row by row from rho's nonzeros, which
        // are about 20% of rho on a 1,000-series book; column by column it cost a pass over
        // every nonzero of A per iteration. Only the variables it touches (cand_) can enter, so
        // the ratio test and the reduced-cost update run over those, not all n + m: on a
        // 1,000-series book those passes were half the time of a cold solve.
        for (int j : cand_) {
            alpha_[j] = 0;
            in_cand_[j] = 0;
        }
        cand_.clear();
        for (int i = 0; i < m_; ++i) {
            const double v = rho[i];
            if (v == 0) continue;
            alpha_[n_ + i] = -v;
            cand_.push_back(n_ + i);
            for (int e = row_start_[i]; e < row_start_[i + 1]; ++e) {
                const int j = row_col_[e];
                alpha_[j] += v * row_value_[e];
                if (!in_cand_[j]) {
                    in_cand_[j] = 1;
                    cand_.push_back(j);
                }
            }
        }
        for (int j : cand_) in_cand_[j] = 1;
        double theta_max = lp_infinity;
        for (int j : cand_) {
            if (state_[j] == basic || lo_[j] == up_[j]) continue;
            double delta = -s * alpha_[j];
            bool eligible = state_[j] == at_lower ? delta > pivot_tol : delta < -pivot_tol;
            if (eligible && !bland) theta_max = std::min(theta_max, (d_[j] * sign(delta) + dual_tol) / std::fabs(delta));
        }
        int q = -1;
        double q_key = 0;
        for (int j : cand_) {
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
            // infeasible. Confirm first: when row r of the inverse times the basis is the unit
            // row to rounding, on primal values recomputed from it (O(m²)); otherwise on a
            // fresh factorization (O(m³); on a 1,000-series book this confirmation was most of
            // the refactorizations in the rounding dive, where failed fixes are common).
            if (since_refactor_ > 0 && confirmed_row != r) {
                double residual = 0;
                for (int k = 0; k < m_; ++k)
                    residual = std::max(residual, std::fabs(dot_row(rho, head_[k]) - (k == r ? 1.0 : 0.0)));
                if (residual < 1e-9) {
                    confirmed_row = r;
                    compute_primal();
                    continue;
                }
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
        column(q, work_);
        factor_.ftran(work_, w);
        if (std::fabs(w[r] - alpha_[q]) > 1e-7 * (1 + std::fabs(w[r]))) {
            refactor();
            compute_primal();
            compute_dual();
            if (restore_dual_feasibility(dual_tol)) compute_primal();
            continue;
        }

        double delta_q = -s * alpha_[q];
        double theta = std::max(0.0, d_[q] / delta_q);  // Harris may accept a slightly wrong-signed d_q
        for (int j : cand_)
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

        // Steepest-edge weights (Forrest and Goldfarb, dual): with tau = B⁻¹rho and
        // beta_r = |rho|², beta_k += -2(w_k/w_r)tau_k + (w_k/w_r)² beta_r, and beta_r / w_r².
        {
            const double beta_r = dot(rho, rho, m_);
            work_.assign(rho_.begin(), rho_.end());
            factor_.ftran(work_, work2_);
            const double piv = w[r];
            for (int k = 0; k < m_; ++k) {
                if (k == r || w[k] == 0) continue;
                const double a = w[k] / piv;
                norm_[k] = std::max(norm_[k] - 2 * a * work2_[k] + a * a * beta_r, 1e-12);
            }
            norm_[r] = std::max(beta_r / (piv * piv), 1e-12);
            factor_.update(r, w);
        }

        ++iterations;
        confirmed_row = -1;
        ++pivots_since_compute_;
        if (++since_refactor_ >= refactor_every) {
            refactor();
            compute_primal();
            compute_dual();
            if (restore_dual_feasibility(dual_tol)) compute_primal();
        }
        // The dual objective rises by theta times the violation removed.
        // Checked every 8 pivots: the sum is a pass over the columns.
        if (!stuck && iterations % 8 == 0) {
            double objective = 0;
            for (int j = 0; j < n_; ++j) objective += cost_[j] * x_[j];
            if (objective > best_objective + 1e-9 * (1 + std::fabs(objective))) {
                best_objective = objective;
                since_rise = 0;
            } else if ((since_rise += 8) > 10L * (m_ + n_)) {
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
//
// Hold::all holds every integer column already on the grid at its value first, and the
// dive rounds only the rest. On a 1,000-series book the root LP has 15 fractional columns
// among 4,679; rounding one at a time while the others stay free let each fix move many
// more off the grid, and the dive took 300 to 450 LP solves. Holding the rest takes about
// 12. Held columns can leave no way to round a linked set (balance and suffix rows), so
// Hold::at_bounds holds only those at a bound and leaves on-grid interior values free to
// absorb the rounding; the caller tries that next. With a guide (a pre-trade check's
// previous pairing, which may no longer fit), Hold::agree then holds only the columns where
// the LP agrees with it and rounds toward it elsewhere, a search near the old answer
// (as in RINS). Last comes a dive that holds nothing.
enum class Hold { none, all, at_bounds, agree };

bool dive(DualSimplex& simplex, const Lp& lp, const std::vector<bool>& integer, const std::vector<int>& priority,
          const std::vector<double>* guide, LpSolution sol, double integer_tol, long& iterations, std::vector<double>& x,
          double& objective, Hold hold = Hold::none) {
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
    struct Held {
        int col;
        double lo, up;
    };
    std::vector<Held> held;
    if (hold != Hold::none) {
        for (int j = 0; j < lp.cols(); ++j) {
            if (!integer[j]) continue;
            const double v = std::round(sol.x[j]);
            if (std::fabs(sol.x[j] - v) > integer_tol) continue;
            if (hold == Hold::at_bounds && v != simplex.lower(j) && v != simplex.upper(j)) continue;
            if (hold == Hold::agree && (*guide)[j] != v) continue;
            held.push_back({j, simplex.lower(j), simplex.upper(j)});
            simplex.set_bounds(j, v, v);
        }
        // With the rest held each LP is small, so trying the other sides is cheap.
        backtracks = 40;
    }
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
    for (const Held& h : held) simplex.set_bounds(h.col, h.lo, h.up);
    return found;
}

}  // namespace

MipSolution branch_and_bound(const Lp& lp, const std::vector<bool>& integer, const MipOptions& o) {
    DualSimplex simplex(lp);
    return branch_and_bound(simplex, lp, integer, o);
}

MipSolution branch_and_bound(DualSimplex& simplex, const Lp& lp, const std::vector<bool>& integer, const MipOptions& o) {
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
    // prune() without recording the bound, for a test that is not a pruning.
    auto prune_test = [&](double b) {
        return b != -lp_infinity && incumbent != lp_infinity &&
               b >= incumbent - std::max(o.abs_tol, o.rel_gap * std::fabs(o.offset + b));
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
    // The caller's simplex gets the root's bounds and optimal basis back on every return,
    // so the next search on it (the next order's) starts at most a few pivots away. Left
    // at the last node's basis instead, an order's root took 270 to 1,400 iterations on a
    // 1,000-series book; from the root's, 0 to 18.
    struct Restore {
        DualSimplex& s;
        const Lp& lp;
        const std::vector<bool>& integer;
        std::optional<DualSimplex::Snapshot> root;
        ~Restore() {
            for (int j = 0; j < lp.cols(); ++j)
                if (integer[j]) s.set_bounds(j, lp.col_lo[j], lp.col_up[j]);
            if (root) s.restore(std::move(*root));
        }
    } restore{simplex, lp, integer, std::nullopt};
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
        const bool warm = root && o.root_basis.head.size() == static_cast<std::size_t>(lp.rows()) &&
                          o.root_basis.state.size() == static_cast<std::size_t>(lp.rows() + lp.cols());
        LpSolution sol = simplex.solve(warm ? o.root_basis : LpBasis{});
        ++out.nodes;
        out.iterations += sol.iterations;
        if (root) {
            out.root = sol;
            root = false;
            if (sol.status == LpStatus::optimal) restore.root = simplex.save();
            if (sol.status == LpStatus::infeasible || sol.status == LpStatus::unbounded) {
                out.status = sol.status == LpStatus::infeasible ? MipStatus::infeasible : MipStatus::unbounded;
                return out;
            }
            std::vector<double> x;
            double obj = 0;
            // The dive that holds nothing can take seconds on a large book; it is skipped
            // when the incumbent passed in (a pre-trade check's previous pairing) is already
            // within the gap of the root bound.
            auto try_dive = [&](Hold h) {
                const std::vector<double>* g = h == Hold::agree ? &o.guide : nullptr;
                return dive(simplex, lp, integer, o.priority, g, sol, integer_tol, out.iterations, x, obj, h);
            };
            const bool guided = o.guide.size() == static_cast<std::size_t>(lp.cols());
            bool found = sol.status == LpStatus::optimal &&
                         (try_dive(Hold::all) || try_dive(Hold::at_bounds) || (guided && try_dive(Hold::agree)) ||
                          (!(o.start.size() && incumbent < lp_infinity && prune_test(sol.objective)) && try_dive(Hold::none)));
            if (found && obj < incumbent) {
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
