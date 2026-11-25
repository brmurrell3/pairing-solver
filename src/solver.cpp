// The model of spec §2 for one (account, underlying) subproblem, specialized as spec §3.1
// describes, and the solve that reads it back. Every cost and validity decision comes from
// the Phase 1 engine; this file only decides which candidates to offer it.

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <map>
#include <numeric>
#include <set>
#include <stdexcept>

#include "pairing/solver.hpp"

namespace pairing {

namespace {

double dollars(Money m) { return static_cast<double>(m.micros()) / Money::per_dollar; }

// Phase 1 rejects legs that do not form the structure with std::invalid_argument, so a
// candidate is whatever Phase 1 accepts.
template <class F>
bool accepted(F&& f, Requirement& out) {
    try {
        out = f();
        return true;
    } catch (const std::invalid_argument&) {
        return false;
    }
}

struct Builder {
    const Portfolio& p;
    const RuleSet& r;
    std::int64_t lots;
    Model m;
    std::vector<std::int64_t> cap;  // lots per option position, then shares of stock
    std::vector<Money> unit;        // standalone requirement per lot or share
    int n;
    bool has_stock;

    Builder(const Portfolio& p_, const RuleSet& r_, std::int64_t lots_) : p(p_), r(r_), lots(lots_) {
        n = static_cast<int>(p.options.size());
        has_stock = p.stock.shares != 0;
        m.lots_per_contract = lots;
    }

    OptionLeg leg(int i, std::int64_t q) const { return lot_leg(p.options[i], q, lots); }
    StockLeg shares(std::int64_t q) const { return StockLeg{p.stock.shares < 0 ? -q : q, p.stock.price}; }
    int cap_index(int position) const { return position == stock_position ? n : position; }
    bool is(int i, OptionType t, int side) const {
        return p.options[i].option.type == t && (p.options[i].quantity > 0) == (side > 0);
    }

    void capacities() {
        for (int i = 0; i < n; ++i) {
            const OptionLeg& o = p.options[i];
            if (o.quantity == 0) throw std::invalid_argument("zero-quantity position");
            if (o.option.underlying != p.options.front().option.underlying)
                throw std::invalid_argument("a subproblem has one underlying");
            if (o.quantity < 0 && o.option.listing != Listing::listed)
                throw std::domain_error("uncovered OTC short options ((f)(2)(E)(iii)) are not implemented");
            cap.push_back(std::llabs(o.quantity) * lots);
            unit.push_back(separate({leg(i, 1)}, p.market, r).total());
        }
        cap.push_back(std::llabs(p.stock.shares));
        unit.push_back(has_stock ? stock(shares(1), r).total() : Money{});
        for (int i = 0; i <= n; ++i) {
            if (i == n && !has_stock) {
                m.capacity_row.push_back(-1);
                continue;
            }
            m.capacity_row.push_back(m.lp.add_row(0, static_cast<double>(cap[i])));
            m.constant += unit[i] * cap[i];
        }
    }

    // A template's column costs its requirement less the standalone requirements it
    // replaces; one that saves nothing is never needed, since its legs can stay standalone.
    void add_template(StructureKind kind, std::vector<StructureLeg> legs, const Requirement& q) {
        Money saving = q.total();
        double ub = lp_infinity;
        std::vector<Lp::Entry> entries;
        for (const auto& l : legs) {
            int c = cap_index(l.position);
            saving -= unit[c] * l.quantity;
            ub = std::min(ub, static_cast<double>(cap[c]) / static_cast<double>(l.quantity));
            entries.push_back({m.capacity_row[c], static_cast<double>(l.quantity)});
        }
        if (saving >= Money{}) return;
        m.lp.add_column(dollars(saving), 0, ub, std::move(entries));
        m.integer.push_back(true);
        m.column.push_back({Model::Column::template_unit, static_cast<int>(m.templates.size())});
        m.templates.push_back({kind, std::move(legs)});
    }

    void templates() {
        const Market& mk = p.market;
        Requirement q;
        // R6: short put and short call in the smallest whole-lot ratio of equal share-equivalents.
        for (int i = 0; i < n; ++i) {
            if (!is(i, OptionType::put, -1)) continue;
            for (int j = 0; j < n; ++j) {
                if (!is(j, OptionType::call, -1)) continue;
                std::int64_t wi = leg(i, 1).option.deliverable, wj = leg(j, 1).option.deliverable;
                std::int64_t g = std::gcd(wi, wj), qi = wj / g, qj = wi / g;
                if (accepted([&] { return short_straddle(leg(i, qi), leg(j, qj), mk, r); }, q))
                    add_template(StructureKind::straddle, {{i, qi}, {j, qj}}, q);
            }
        }
        if (!has_stock) return;
        const bool long_stock = p.stock.shares > 0;
        // R7 and R8a: one lot of the option against the shares it delivers.
        for (int i = 0; i < n; ++i) {
            StockLeg s = shares(leg(i, 1).option.deliverable);
            StructureKind kind;
            bool ok;
            if (long_stock && is(i, OptionType::call, -1)) {
                kind = StructureKind::covered_call;
                ok = accepted([&] { return covered_call(s, leg(i, 1), mk, r); }, q);
            } else if (!long_stock && is(i, OptionType::put, -1)) {
                kind = StructureKind::covered_put;
                ok = accepted([&] { return covered_put(s, leg(i, 1), mk, r); }, q);
            } else if (long_stock && is(i, OptionType::put, +1)) {
                kind = StructureKind::protective_put;
                ok = accepted([&] { return protective_put(s, leg(i, 1), mk, r); }, q);
            } else if (!long_stock && is(i, OptionType::call, +1)) {
                kind = StructureKind::protective_call;
                ok = accepted([&] { return protective_call(s, leg(i, 1), mk, r); }, q);
            } else {
                continue;
            }
            if (ok) add_template(kind, {{stock_position, s.shares < 0 ? -s.shares : s.shares}, {i, 1}}, q);
        }
        // R8b–d: a call and a put on one lot each against the shares. Phase 1 needs both
        // options to cover the same shares and share an expiration; skipping other pairs
        // only saves calls it would reject.
        for (int c = 0; c < n; ++c) {
            if (p.options[c].option.type != OptionType::call) continue;
            for (int u = 0; u < n; ++u) {
                const OptionLeg &call = p.options[c], &put = p.options[u];
                if (put.option.type != OptionType::put || call.option.expiry != put.option.expiry ||
                    call.option.deliverable != put.option.deliverable)
                    continue;
                std::int64_t w = leg(c, 1).option.deliverable;
                StockLeg s = shares(w);
                if (long_stock && call.quantity < 0 && put.quantity > 0) {
                    if (accepted([&] { return conversion(s, leg(c, 1), leg(u, 1), mk, r); }, q))
                        add_template(StructureKind::conversion, {{stock_position, w}, {c, 1}, {u, 1}}, q);
                    if (accepted([&] { return collar(s, leg(u, 1), leg(c, 1), mk, r); }, q))
                        add_template(StructureKind::collar, {{stock_position, w}, {u, 1}, {c, 1}}, q);
                } else if (!long_stock && call.quantity > 0 && put.quantity < 0) {
                    if (accepted([&] { return reverse_conversion(s, leg(c, 1), leg(u, 1), mk, r); }, q))
                        add_template(StructureKind::reverse_conversion, {{stock_position, w}, {c, 1}, {u, 1}}, q);
                }
            }
        }
    }

    // R2b. A box's buy side is a long call and short put at one strike, its sell side a long
    // put and short call at another; Phase 1 decides the rest.
    void long_boxes() {
        auto same_series_but_type = [&](int a, int b) {
            const Option &x = p.options[a].option, &y = p.options[b].option;
            return x.strike == y.strike && x.expiry == y.expiry && x.deliverable == y.deliverable;
        };
        std::vector<std::pair<int, int>> buy, sell;
        for (int a = 0; a < n; ++a)
            for (int b = 0; b < n; ++b) {
                if (!same_series_but_type(a, b)) continue;
                if (is(a, OptionType::call, +1) && is(b, OptionType::put, -1)) buy.push_back({a, b});
                if (is(a, OptionType::put, +1) && is(b, OptionType::call, -1)) sell.push_back({a, b});
            }
        Requirement q;
        for (auto [lc, sp] : buy)
            for (auto [lp, sc] : sell) {
                if (p.options[lc].option.expiry != p.options[lp].option.expiry) continue;
                std::vector<OptionLeg> legs = {leg(lc, 1), leg(sp, 1), leg(lp, 1), leg(sc, 1)};
                if (accepted([&] { return european_long_box(legs, r).requirement; }, q))
                    add_template(StructureKind::long_box, {{lc, 1}, {sp, 1}, {lp, 1}, {sc, 1}}, q);
            }
    }

    // One flexible max-loss group (spec §2) over candidate options. Rows: a loss row per
    // candidate strike, a balance equality per type in share-equivalents and, under the
    // pairwise reading, the suffix inequalities of spec §3.1 item 4 in place of flows.
    void group(const std::vector<int>& candidates, bool suffix_rows) {
        bool short_seen = false, long_seen = false;
        for (int i : candidates) (p.options[i].quantity < 0 ? short_seen : long_seen) = true;
        if (!short_seen || !long_seen) return;
        const int h = m.groups++;

        std::set<Money> strike_set;
        for (int i : candidates) strike_set.insert(p.options[i].option.strike);
        std::vector<Money> strikes(strike_set.begin(), strike_set.end());

        // Netted value of one lot at each strike, from Phase 1.
        std::map<int, std::vector<double>> value;
        double t_up = 0;  // the shorts' loss alone bounds the group's
        std::vector<double> loss_up(strikes.size(), 0);
        for (int i : candidates) {
            auto& v = value[i];
            double worst = 0, best = 0;
            for (Money k : strikes) {
                v.push_back(dollars(payoff_at({leg(i, 1)}, k)));
                worst = std::min(worst, v.back());
                best = std::max(best, v.back());
            }
            t_up += -worst * static_cast<double>(cap[i]);
            for (std::size_t k = 0; k < strikes.size(); ++k) loss_up[k] += best * static_cast<double>(cap[i]);
        }
        std::vector<int> loss_row;
        std::vector<Lp::Entry> t_entries;
        for (std::size_t k = 0; k < strikes.size(); ++k) {
            loss_row.push_back(m.lp.add_row(0, t_up + loss_up[k]));
            t_entries.push_back({loss_row.back(), 1.0});
        }
        m.lp.add_column(1.0, 0, t_up, std::move(t_entries));
        m.integer.push_back(false);
        m.column.push_back({Model::Column::loss, h});

        struct TypeRows {
            int balance = -1;
            std::vector<std::pair<Date, int>> suffix;
        };
        std::map<OptionType, TypeRows> rows;
        for (OptionType t : {OptionType::call, OptionType::put}) {
            std::set<Date> expiries;
            double long_units = 0;
            for (int i : candidates)
                if (p.options[i].option.type == t) {
                    expiries.insert(p.options[i].option.expiry);
                    if (p.options[i].quantity > 0) long_units += static_cast<double>(leg(i, cap[i]).units());
                }
            if (expiries.empty()) continue;
            TypeRows& tr = rows[t];
            tr.balance = m.lp.add_row(0, 0);
            // The earliest date's suffix is the balance row itself.
            if (suffix_rows)
                for (auto it = std::next(expiries.begin()); it != expiries.end(); ++it)
                    tr.suffix.push_back({*it, m.lp.add_row(0, long_units)});
        }

        for (int i : candidates) {
            const OptionLeg& o = p.options[i];
            OptionLeg one = leg(i, 1);
            double units = static_cast<double>(one.units());
            std::vector<Lp::Entry> e = {{m.capacity_row[i], 1.0}};
            for (std::size_t k = 0; k < strikes.size(); ++k)
                if (value[i][k] != 0) e.push_back({loss_row[k], value[i][k]});
            const TypeRows& tr = rows[o.option.type];
            e.push_back({tr.balance, units});
            for (auto [d, row] : tr.suffix)
                if (o.option.expiry >= d) e.push_back({row, units});
            // Shorts in the group leave their standalone requirement for the group's loss.
            // Longs are paid in full, which costs a long beyond nine months its loan value (Q3).
            Money cost = o.quantity > 0 ? market_value(one) - unit[i] : -unit[i];
            m.lp.add_column(dollars(cost), 0, static_cast<double>(cap[i]), std::move(e));
            m.integer.push_back(true);
            m.column.push_back({Model::Column::member, h, i});
        }
    }

    // Spec §3.1 item 2: one group per (style, listing) class under the pairwise reading; one
    // per cut date under nearest_long; one per expiration under same_expiry, and for
    // European classes when European calendars are disallowed.
    void groups() {
        std::map<std::pair<Style, Listing>, std::vector<int>> classes;
        for (int i = 0; i < n; ++i) classes[{p.options[i].option.style, p.options[i].option.listing}].push_back(i);
        for (const auto& [cls, members] : classes) {
            ExpiryRule rule = r.expiry_rule;
            if (cls.first == Style::european && r.european_calendars == EuropeanCalendars::disallowed)
                rule = ExpiryRule::same_expiry;
            if (rule == ExpiryRule::pairwise) {
                group(members, true);
                continue;
            }
            std::set<Date> expiries;
            for (int i : members) expiries.insert(p.options[i].option.expiry);
            for (Date d : expiries) {
                std::vector<int> c;
                for (int i : members) {
                    Date e = p.options[i].option.expiry;
                    bool in = rule == ExpiryRule::same_expiry ? e == d : (p.options[i].quantity < 0 ? e <= d : e >= d);
                    if (in) c.push_back(i);
                }
                group(c, false);
            }
        }
    }
};

}  // namespace

Model build_model(const Portfolio& p, const RuleSet& r, const SolveOptions& o) {
    if (o.lots_per_contract < 1) throw std::invalid_argument("lots per contract must be at least 1");
    Builder b(p, r, o.lots_per_contract);
    b.capacities();
    b.templates();
    b.long_boxes();
    b.groups();
    return std::move(b.m);
}

Solution read_solution(const Model& m, const Portfolio& p, const std::vector<double>& x) {
    Solution s;
    s.lots_per_contract = m.lots_per_contract;
    const int n = static_cast<int>(p.options.size());
    std::vector<std::int64_t> used(n + 1, 0);
    std::vector<std::vector<StructureLeg>> spreads(m.groups);
    for (int j = 0; j < m.lp.cols(); ++j) {
        const auto& c = m.column[j];
        if (c.kind == Model::Column::loss) continue;
        std::int64_t v = std::llround(x[j]);
        if (std::fabs(x[j] - static_cast<double>(v)) > 1e-6) throw std::logic_error("solution is not on the grid");
        if (v <= 0) continue;
        if (c.kind == Model::Column::member) {
            spreads[c.index].push_back({c.position, v});
            used[c.position] += v;
            continue;
        }
        Structure st;
        st.kind = m.templates[c.index].kind;
        for (auto l : m.templates[c.index].legs) {
            l.quantity *= v;
            used[l.position == stock_position ? n : l.position] += l.quantity;
            st.legs.push_back(l);
        }
        s.structures.push_back(std::move(st));
    }
    for (auto& legs : spreads)
        if (!legs.empty()) s.structures.push_back({StructureKind::spread, std::move(legs), {}});
    for (int i = 0; i <= n; ++i) {
        std::int64_t cap = i < n ? std::llabs(p.options[i].quantity) * m.lots_per_contract : std::llabs(p.stock.shares);
        if (used[i] > cap) throw std::logic_error("solution uses more than a position holds");
        if (used[i] < cap) s.residuals.push_back({{i < n ? i : stock_position, cap - used[i]}, {}});
    }
    return s;
}

Solution solve(const Portfolio& p, const RuleSet& r, const SolveOptions& o) {
    Model m = build_model(p, r, o);
    // Integer assignments cost whole micro-dollars, so a node that cannot beat the
    // incumbent by half of one cannot beat it at all; the relative term absorbs LP rounding.
    double scale = std::fabs(dollars(m.constant));
    MipSolution mip = branch_and_bound(m.lp, m.integer, 0.5e-6 + 1e-12 * scale);
    if (mip.status != LpStatus::optimal) throw std::runtime_error("the subproblem did not solve");

    Solution s = read_solution(m, p, mip.x);
    s.total = check_solution(p, r, s);
    for (const auto& l : p.options) s.all_standalone += separate({l}, p.market, r).total();
    if (p.stock.shares != 0) s.all_standalone += stock(p.stock, r).total();

    const double constant = dollars(m.constant);
    s.lp_objective = constant + mip.objective;
    s.lp_bound = constant + mip.root.objective;
    double total = dollars(s.total);
    if (std::fabs(s.lp_objective - total) > 1e-9 * std::max(1.0, std::fabs(total)))
        throw std::logic_error("the model's objective disagrees with the checker's total");
    s.gap = total > 0 ? (total - s.lp_bound) / total : 0;

    s.lp_integral = true;
    for (int j = 0; j < m.lp.cols(); ++j)
        if (m.integer[j] && std::fabs(mip.root.x[j] - std::round(mip.root.x[j])) > 1e-6) s.lp_integral = false;

    // ∂total/∂cap is the unit's standalone cost (it enters the constant) plus the capacity
    // row's dual when the row is held at its upper bound; otherwise extra units would stay
    // standalone.
    auto shadow = [&](int position, Money unit) {
        int row = m.capacity_row[position];
        double d = mip.root.basis.state[m.lp.cols() + row] == 2 ? mip.root.row_dual[row] : 0.0;
        return dollars(unit) + d;
    };
    const int n = static_cast<int>(p.options.size());
    for (int i = 0; i < n; ++i) {
        Money unit = separate({lot_leg(p.options[i], 1, o.lots_per_contract)}, p.market, r).total();
        s.shadow_options.push_back(shadow(i, unit) * static_cast<double>(o.lots_per_contract));
    }
    if (p.stock.shares != 0) s.shadow_stock = shadow(n, stock({p.stock.shares < 0 ? -1 : 1, p.stock.price}, r).total());

    s.rows = m.lp.rows();
    s.columns = m.lp.cols();
    s.nodes = mip.nodes;
    s.iterations = mip.iterations;
    return s;
}

}  // namespace pairing
