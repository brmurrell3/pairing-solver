// The model of spec §2 for one (account, underlying) subproblem, specialized as spec §3.1
// describes, and the solve that reads it back. Every cost and validity decision comes from
// the Phase 1 engine; this file only decides which candidates to offer it.

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <map>
#include <memory>
#include <numeric>
#include <set>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_map>

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

// 64-bit FNV-1a over a sequence of integers: the identity of a row or column in terms of
// series, not indices, so one book's basis can start another's (Model::row_key).
struct Key {
    std::uint64_t h = 0xcbf29ce484222325ULL;
    template <class T>
    Key& operator<<(T value) {
        const auto v = static_cast<std::uint64_t>(value);
        for (int b = 0; b < 8; ++b) {
            h ^= (v >> (8 * b)) & 0xff;
            h *= 0x100000001b3ULL;
        }
        return *this;
    }
    operator std::uint64_t() const { return h; }
};

struct Builder {
    const Portfolio& p;
    const RuleSet& r;
    std::int64_t lots;
    Model m;
    std::vector<std::int64_t> cap;  // lots per option position, then shares of stock
    std::vector<Money> unit;        // standalone requirement per lot or share
    int n;
    bool has_stock;

    std::int64_t compact_straddle_pairs;
    bool straddles_on;
    Builder(const Portfolio& p_, const RuleSet& r_, std::int64_t lots_, std::int64_t compact, bool straddles_)
        : p(p_), r(r_), lots(lots_), compact_straddle_pairs(compact), straddles_on(straddles_) {
        n = static_cast<int>(p.options.size());
        has_stock = p.stock.shares != 0;
        m.lots_per_contract = lots;
    }

    OptionLeg leg(int i, std::int64_t q) const { return lot_leg(p.options[i], q, lots); }
    StockLeg shares(std::int64_t q) const { return StockLeg{p.stock.shares < 0 ? -q : q, p.stock.price}; }
    int cap_index(int position) const { return position == stock_position ? n : position; }
    std::int64_t series(int position) const {
        if (position == stock_position || position == n) return static_cast<std::int64_t>(Key{} << 'T');
        const Option& o = p.options[position].option;
        Key k;
        k << 'S' << static_cast<int>(o.type) << o.strike.micros() << o.expiry.year << o.expiry.month << o.expiry.day
          << o.deliverable << static_cast<int>(o.style) << static_cast<int>(o.listing) << static_cast<int>(o.product)
          << (p.options[position].quantity > 0);
        return static_cast<std::int64_t>(k);
    }
    int row(double lo, double up, std::uint64_t key) {
        m.row_key.push_back(key);
        return m.lp.add_row(lo, up);
    }
    int column(double cost, double lo, double up, std::vector<Lp::Entry> entries, std::uint64_t key) {
        m.col_key.push_back(key);
        return m.lp.add_column(cost, lo, up, std::move(entries));
    }
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
            m.capacity_row.push_back(row(0, static_cast<double>(cap[i]), Key{} << 'c' << series(i)));
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
        Key key;
        key << 't' << static_cast<int>(kind);
        for (const auto& l : legs) key << series(l.position) << l.quantity;
        column(dollars(saving), 0, ub, std::move(entries), key);
        m.integer.push_back(true);
        m.column.push_back({Model::Column::template_unit, static_cast<int>(m.templates.size())});
        m.templates.push_back({kind, std::move(legs)});
    }

    void templates() {
        const Market& mk = p.market;
        Requirement q;
        // R6: short put and short call in the smallest whole-lot ratio of equal share-equivalents.
        // Large classes of one lot size go through straddles(), which needs O(n) columns, not
        // one per pair; small classes and mixed lot sizes keep a template per pair.
        // The compact form is used only for classes with more pairs than
        // SolveOptions::compact_straddle_pairs: on
        // small books, branching on pair columns is faster (the 1,000-case HiGHS test took
        // 40 s with the compact form everywhere, against 18 s).
        const std::int64_t compact_pairs = compact_straddle_pairs;
        std::map<std::int64_t, std::vector<int>> by_size;
        for (int i = 0; i < n; ++i)
            if (straddles_on && p.options[i].quantity < 0) by_size[std::llabs(leg(i, 1).units())].push_back(i);
        std::set<std::int64_t> compact;
        for (const auto& [size, shorts] : by_size) {
            std::int64_t puts = 0, calls = 0;
            for (int i : shorts) (p.options[i].option.type == OptionType::put ? puts : calls) += 1;
            if (puts * calls > compact_pairs) {
                compact.insert(size);
                straddles(shorts);
            }
        }
        // Per-lot deliverables and units, computed once: leg() copies the position.
        std::vector<int> short_puts, short_calls;
        std::vector<std::int64_t> lot_w(n), lot_units(n);
        for (int i = 0; i < n; ++i) {
            const OptionLeg one = leg(i, 1);
            lot_w[i] = one.option.deliverable;
            lot_units[i] = std::llabs(one.units());
            if (is(i, OptionType::put, -1)) short_puts.push_back(i);
            if (is(i, OptionType::call, -1)) short_calls.push_back(i);
        }
        for (int i : short_puts) {
            if (!straddles_on) break;
            const bool compact_i = compact.count(lot_units[i]) > 0;
            for (int j : short_calls) {
                std::int64_t wi = lot_w[i], wj = lot_w[j];
                if (wi == wj && compact_i) continue;
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
        // options to cover the same shares and share an expiration, a conversion needs one
        // strike and a collar the put's strike below the call's; skipping other pairs only
        // saves calls it would reject. (Its rejections are exceptions, about 5 µs each:
        // trying every pair cost 70 ms of the 85 ms model build for a 1,000-series book.)
        for (int c = 0; c < n; ++c) {
            if (p.options[c].option.type != OptionType::call) continue;
            for (int u = 0; u < n; ++u) {
                const OptionLeg &call = p.options[c], &put = p.options[u];
                if (put.option.type != OptionType::put || call.option.expiry != put.option.expiry ||
                    call.option.deliverable != put.option.deliverable)
                    continue;
                std::int64_t w = leg(c, 1).option.deliverable;
                StockLeg s = shares(w);
                const bool same_strike = call.option.strike == put.option.strike;
                if (long_stock && call.quantity < 0 && put.quantity > 0) {
                    if (same_strike && accepted([&] { return conversion(s, leg(c, 1), leg(u, 1), mk, r); }, q))
                        add_template(StructureKind::conversion, {{stock_position, w}, {c, 1}, {u, 1}}, q);
                    if (put.option.strike < call.option.strike &&
                        accepted([&] { return collar(s, leg(u, 1), leg(c, 1), mk, r); }, q))
                        add_template(StructureKind::collar, {{stock_position, w}, {u, 1}, {c, 1}}, q);
                } else if (!long_stock && call.quantity > 0 && put.quantity < 0) {
                    if (same_strike && accepted([&] { return reverse_conversion(s, leg(c, 1), leg(u, 1), mk, r); }, q))
                        add_template(StructureKind::reverse_conversion, {{stock_position, w}, {c, 1}, {u, 1}}, q);
                }
            }
        }
    }

    // R6 for short puts and calls of one lot size. One lot of each costs the greater of the
    // two uncovered requirements plus the other's market value, so the pair saves
    // g = U − V of its cheaper leg (U uncovered, V market value), whatever the dearer leg
    // is. Order the class's shorts by (U, calls before puts): Phase 1 charges a tie as if
    // the put were dearer. Any put and call pair, the lower-ranked leg being the cheap one.
    // So each short gets two columns, its lots on the cheap side (saving g) and on the dear
    // side (saving nothing). Cheap puts must be matched to dearer calls and cheap calls to
    // dearer puts. Each is a transportation problem on a nested graph, feasible exactly when
    // the suffix condition of spec §3.1 item 4 holds over ranks (docs/proofs.md), with
    // equal totals. That replaces one template per pair: 57,600 of the 58,601 columns of a
    // 1,000-series book.
    void straddles(const std::vector<int>& shorts) {
        std::vector<std::tuple<Money, int, int>> order;  // (U per lot, 0 call / 1 put, position)
        bool puts = false, calls = false;
        for (int i : shorts) {
            const bool put = p.options[i].option.type == OptionType::put;
            (put ? puts : calls) = true;
            order.push_back({uncovered_short(leg(i, 1), p.market, r), put ? 1 : 0, i});
        }
        if (!puts || !calls) return;
        std::sort(order.begin(), order.end());
        const int cls = m.straddle_classes++;
        const std::int64_t cls_key = Key{} << 'q' << std::llabs(leg(shorts.front(), 1).units());
        const int k = static_cast<int>(order.size());
        std::vector<int> cheap(k, -1), dear(k, -1);
        for (int rank = 0; rank < k; ++rank) {
            const auto [u, put, i] = order[rank];
            // The cheap side needs a dearer leg of the other type; the dear side a cheaper one.
            bool above = false, below = false;
            for (int o = 0; o < k; ++o)
                if (std::get<1>(order[o]) != put) (o > rank ? above : below) = true;
            Money saving = u - market_value(leg(i, 1));
            const double up = static_cast<double>(cap[i]);
            if (above && saving > Money{}) {
                cheap[rank] = column(-dollars(saving), 0, up, {{m.capacity_row[i], 1.0}}, Key{} << 'a' << cls_key << series(i));
                m.integer.push_back(true);
                m.column.push_back({Model::Column::straddle_cheap, cls, i, rank});
            }
            if (below) {
                dear[rank] = column(0, 0, up, {{m.capacity_row[i], 1.0}}, Key{} << 'b' << cls_key << series(i));
                m.integer.push_back(true);
                m.column.push_back({Model::Column::straddle_expensive, cls, i, rank});
            }
        }
        // For each direction (cheap puts against dear calls, cheap calls against dear puts):
        // total cheap lots equal total dear lots, and for every rank t the cheap lots ranked
        // t or higher do not exceed the dear lots ranked above t.
        for (int cheap_type : {1, 0}) {
            int total = row(0, 0, Key{} << 'u' << cls_key << cheap_type);
            bool any = false;
            for (int rank = 0; rank < k; ++rank) {
                const int type = std::get<1>(order[rank]);
                if (type == cheap_type && cheap[rank] >= 0) {
                    m.lp.columns[cheap[rank]].push_back({total, 1.0});
                    any = true;
                }
                if (type != cheap_type && dear[rank] >= 0) m.lp.columns[dear[rank]].push_back({total, -1.0});
            }
            (void)any;
            for (int t = 0; t < k; ++t) {
                if (std::get<1>(order[t]) != cheap_type || cheap[t] < 0) continue;
                // dear lots ranked above t, less cheap lots ranked t or higher, at least 0
                int row = this->row(0, lp_infinity, Key{} << 'v' << cls_key << cheap_type << series(std::get<2>(order[t])));
                for (int rank = t; rank < k; ++rank) {
                    const int type = std::get<1>(order[rank]);
                    if (type == cheap_type && cheap[rank] >= 0) m.lp.columns[cheap[rank]].push_back({row, -1.0});
                    if (type != cheap_type && rank > t && dear[rank] >= 0) m.lp.columns[dear[rank]].push_back({row, 1.0});
                }
            }
        }
    }

    // A capacity row that only one column uses, with coefficient 1, repeats that column's
    // upper bound. In a market-maker book about 30% of the rows are of this kind (most
    // longs pair only through their group member), and every simplex iteration costs
    // O(rows²) with the dense inverse, so they go. capacity_row is -1 for a dropped row;
    // the position's shadow price then comes from the column's reduced cost.
    void drop_single_capacity_rows() {
        Lp& lp = m.lp;
        std::vector<int> count(lp.rows(), 0), only(lp.rows(), -1);
        for (int j = 0; j < lp.cols(); ++j)
            for (const auto& e : lp.columns[j]) {
                ++count[e.row];
                only[e.row] = j;
            }
        std::vector<bool> drop(lp.rows(), false);
        for (int& row : m.capacity_row) {
            if (row < 0 || count[row] != 1) continue;
            const int j = only[row];
            double coef = 0;
            for (const auto& e : lp.columns[j])
                if (e.row == row) coef = e.value;
            if (coef != 1 || lp.col_lo[j] < lp.row_lo[row] || lp.col_up[j] > lp.row_up[row]) continue;
            drop[row] = true;
            m.capacity_column.resize(m.capacity_row.size(), -1);
            m.capacity_column[&row - m.capacity_row.data()] = j;
            row = -1;
        }
        std::vector<int> renumber(lp.rows(), -1);
        int next = 0;
        for (int i = 0; i < lp.rows(); ++i)
            if (!drop[i]) {
                renumber[i] = next;
                lp.row_lo[next] = lp.row_lo[i];
                lp.row_up[next] = lp.row_up[i];
                m.row_key[next] = m.row_key[i];
                ++next;
            }
        lp.row_lo.resize(next);
        lp.row_up.resize(next);
        m.row_key.resize(next);
        for (auto& col : lp.columns) {
            std::erase_if(col, [&](const Lp::Entry& e) { return drop[e.row]; });
            for (auto& e : col) e.row = renumber[e.row];
        }
        for (int& row : m.capacity_row)
            if (row >= 0) row = renumber[row];
        m.capacity_column.resize(m.capacity_row.size(), -1);
    }

    // R2b. A box's buy side is a long call and short put at one strike, its sell side a long
    // put and short call at another; Phase 1 decides the rest.
    void long_boxes() {
        auto same_series_but_type = [&](int a, int b) {
            const Option &x = p.options[a].option, &y = p.options[b].option;
            return x.strike == y.strike && x.expiry == y.expiry && x.deliverable == y.deliverable;
        };
        std::vector<std::pair<int, int>> buy, sell;
        // Candidates share a strike, so only positions at one strike are compared.
        std::map<Money, std::vector<int>> at_strike;
        for (int a = 0; a < n; ++a) at_strike[p.options[a].option.strike].push_back(a);
        for (const auto& [k, here] : at_strike)
            for (int a : here)
                for (int b : here) {
                    if (!same_series_but_type(a, b)) continue;
                    if (is(a, OptionType::call, +1) && is(b, OptionType::put, -1)) buy.push_back({a, b});
                    if (is(a, OptionType::put, +1) && is(b, OptionType::call, -1)) sell.push_back({a, b});
                }
        Requirement q;
        // Phase 1 takes European legs only, with the sell side's strike above the buy
        // side's; trying the rest only collects its rejections, at about 5 µs each.
        auto european = [&](int a) { return p.options[a].option.style == Style::european; };
        for (auto [lc, sp] : buy)
            for (auto [lp, sc] : sell) {
                if (p.options[lc].option.expiry != p.options[lp].option.expiry) continue;
                if (!european(lc) || !european(sp) || !european(lp) || !european(sc) ||
                    p.options[lp].option.strike <= p.options[lc].option.strike)
                    continue;
                std::vector<OptionLeg> legs = {leg(lc, 1), leg(sp, 1), leg(lp, 1), leg(sc, 1)};
                if (accepted([&] { return european_long_box(legs, r).requirement; }, q))
                    add_template(StructureKind::long_box, {{lc, 1}, {sp, 1}, {lp, 1}, {sc, 1}}, q);
            }
    }

    // One flexible max-loss group (spec §2) over candidate options. Rows: a loss row per
    // candidate strike, a balance equality per type in share-equivalents and, under the
    // pairwise reading, the suffix inequalities of spec §3.1 item 4 in place of flows.
    void group(const std::vector<int>& candidates, bool suffix_rows, std::int64_t g) {
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
            const std::vector<OptionLeg> one = {leg(i, 1)};
            for (Money k : strikes) {
                v.push_back(dollars(payoff_at(one, k)));
                worst = std::min(worst, v.back());
                best = std::max(best, v.back());
            }
            t_up += -worst * static_cast<double>(cap[i]);
            for (std::size_t k = 0; k < strikes.size(); ++k) loss_up[k] += best * static_cast<double>(cap[i]);
        }
        std::vector<int> loss_row;
        std::vector<Lp::Entry> t_entries;
        for (std::size_t k = 0; k < strikes.size(); ++k) {
            loss_row.push_back(row(0, t_up + loss_up[k], Key{} << 'l' << g << strikes[k].micros()));
            t_entries.push_back({loss_row.back(), 1.0});
        }
        column(1.0, 0, t_up, std::move(t_entries), Key{} << 'L' << g);
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
            tr.balance = row(0, 0, Key{} << 'B' << g << static_cast<int>(t));
            // The earliest date's suffix is the balance row itself.
            if (suffix_rows)
                for (auto it = std::next(expiries.begin()); it != expiries.end(); ++it)
                    tr.suffix.push_back({*it, row(0, long_units, Key{} << 'U' << g << static_cast<int>(t) << it->year << it->month << it->day)});
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
            column(dollars(cost), 0, static_cast<double>(cap[i]), std::move(e), Key{} << 'm' << g << series(i));
            m.integer.push_back(true);
            m.column.push_back({Model::Column::member, h, i});
        }
        aggregates(candidates, g);
    }

    // With mixed deliverables (100, 150 and 10 shares, or lots of them) the balance rows have
    // unequal coefficients, and whole-lot balance needs congruences the LP cannot see. A
    // type's balance is the sum over share sizes u of u·N_u = 0, N_u being the net lots
    // (long less short) of that size, so u·N_u ≡ 0 modulo g, the gcd of the other sizes:
    // N_u is a multiple of k_u = g / gcd(u, g). Against 100-share calls, net 150-share calls
    // come in pairs, and against 150-share calls net 100-share calls come in threes.
    // Branching on single members reaches such an infeasibility only at the bottom of deep
    // subtrees, so each size gets an integer column M_u with N_u = k_u·M_u, branched on
    // first. The congruence holds for every whole-lot solution, so no solution is lost.
    // (A full lattice basis of the balance row, which makes every integer choice balance,
    // was tried and was 2.8 times slower on the 1,000-case test: its columns are dense.)
    void aggregates(const std::vector<int>& candidates, std::int64_t g) {
        const int first = static_cast<int>(m.column.size()) - static_cast<int>(candidates.size());
        for (OptionType t : {OptionType::call, OptionType::put}) {
            std::map<std::int64_t, std::vector<std::pair<int, double>>> by;  // |units| -> (member column, ±1)
            for (std::size_t c = 0; c < candidates.size(); ++c) {
                const int i = candidates[c];
                if (p.options[i].option.type != t) continue;
                by[std::llabs(leg(i, 1).units())].push_back({first + static_cast<int>(c), p.options[i].quantity > 0 ? 1.0 : -1.0});
            }
            if (by.size() < 2) continue;
            for (const auto& [u, cols] : by) {
                std::int64_t g = 0;
                for (const auto& other : by)
                    if (other.first != u) g = std::gcd(g, other.first);
                const std::int64_t k = g / std::gcd(u, g);
                if (k == 1 && cols.size() < 2) continue;  // a lone member is already an integer column
                int row = this->row(0, 0, Key{} << 'A' << g << static_cast<int>(t) << u);
                double lo = 0, up = 0;
                for (auto [col, sign] : cols) {
                    m.lp.columns[col].push_back({row, sign});
                    (sign > 0 ? up : lo) += sign * m.lp.col_up[col];
                }
                const double kd = static_cast<double>(k);
                column(0, std::ceil(lo / kd), std::floor(up / kd), {{row, -kd}}, Key{} << 'M' << g << static_cast<int>(t) << u);
                m.integer.push_back(true);
                m.column.push_back({Model::Column::aggregate, m.groups - 1});
            }
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
            const std::int64_t g = Key{} << 'g' << static_cast<int>(cls.first) << static_cast<int>(cls.second) << static_cast<int>(rule);
            if (rule == ExpiryRule::pairwise) {
                group(members, true, g);
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
                group(c, false, Key{} << g << d.year << d.month << d.day);
            }
        }
    }
};

}  // namespace

Model build_model(const Portfolio& p, const RuleSet& r, const SolveOptions& o) {
    if (o.lots_per_contract < 1) throw std::invalid_argument("lots per contract must be at least 1");
    Builder b(p, r, o.lots_per_contract, o.compact_straddle_pairs, o.straddles);
    b.capacities();
    b.templates();
    b.long_boxes();
    b.groups();
    for (const auto& c : b.m.column) b.m.priority.push_back(c.kind == Model::Column::aggregate ? 1 : 0);
    b.drop_single_capacity_rows();
    return std::move(b.m);
}

Solution read_solution(const Model& m, const Portfolio& p, const std::vector<double>& x) {
    Solution s;
    s.lots_per_contract = m.lots_per_contract;
    const int n = static_cast<int>(p.options.size());
    std::vector<std::int64_t> used(n + 1, 0);
    std::vector<std::vector<StructureLeg>> spreads(m.groups);
    struct Lots {
        int rank;
        bool cheap;
        int position;
        std::int64_t lots;
    };
    std::vector<std::vector<Lots>> straddle_lots(m.straddle_classes);
    for (int j = 0; j < m.lp.cols(); ++j) {
        const auto& c = m.column[j];
        if (c.kind == Model::Column::loss || c.kind == Model::Column::aggregate) continue;
        if (c.kind == Model::Column::straddle_cheap || c.kind == Model::Column::straddle_expensive) {
            std::int64_t v = std::llround(x[j]);
            if (std::fabs(x[j] - static_cast<double>(v)) > 1e-6) throw std::logic_error("solution is not on the grid");
            if (v > 0) straddle_lots[c.index].push_back({c.rank, c.kind == Model::Column::straddle_cheap, c.position, v});
            continue;
        }
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
    // Straddles: match cheap lots to dear lots of the other type ranked above them, dearest
    // cheap lots first. Each cheap lot's candidates contain those of every dearer cheap lot,
    // so taking any candidate never blocks a later one, and the suffix rows guarantee one.
    for (auto& lots : straddle_lots) {
        std::sort(lots.begin(), lots.end(), [](const Lots& a, const Lots& b) { return a.rank > b.rank; });
        for (int cheap_type : {1, 0}) {
            std::vector<Lots*> pool;  // dear lots of the other type seen so far (ranked higher)
            for (auto& l : lots) {
                const bool put = p.options[l.position].option.type == OptionType::put;
                if (!l.cheap && put != (cheap_type == 1)) {
                    pool.push_back(&l);
                    continue;
                }
                if (!l.cheap || put != (cheap_type == 1)) continue;
                std::int64_t need = l.lots;
                while (need > 0) {
                    while (!pool.empty() && pool.back()->lots == 0) pool.pop_back();
                    if (pool.empty()) throw std::logic_error("straddle lots do not match");
                    Lots& d = *pool.back();
                    const std::int64_t q = std::min(need, d.lots);
                    const int put_pos = put ? l.position : d.position, call_pos = put ? d.position : l.position;
                    s.structures.push_back({StructureKind::straddle, {{put_pos, q}, {call_pos, q}}, {}});
                    for (int pos : {put_pos, call_pos}) used[pos] += q;
                    need -= q;
                    d.lots -= q;
                }
            }
            for (auto* d : pool)
                if (d->lots != 0) throw std::logic_error("straddle lots do not match");
        }
    }
    for (int i = 0; i <= n; ++i) {
        std::int64_t cap = i < n ? std::llabs(p.options[i].quantity) * m.lots_per_contract : std::llabs(p.stock.shares);
        if (used[i] > cap) throw std::logic_error("solution uses more than a position holds");
        if (used[i] < cap) s.residuals.push_back({{i < n ? i : stock_position, cap - used[i]}, {}});
    }
    return s;
}

namespace {

// solve() on a built model. simplex, if given, is built on a model with m's matrix and
// costs and holds m's bounds; the search starts from its basis. start, if given, is a
// feasible integer point of m. x receives the model's assignment.
Solution solve_model(const Portfolio& p, const RuleSet& r, const SolveOptions& o, const Model& m, DualSimplex* simplex,
                     const std::vector<double>* start, std::vector<double>* x, const std::vector<double>* guide = nullptr) {
    // Integer assignments cost whole micro-dollars, so a node that cannot beat the
    // incumbent by half of one cannot beat it at all; the relative term absorbs LP rounding.
    double scale = std::fabs(dollars(m.constant));
    MipOptions mo;
    mo.abs_tol = 0.5e-6 + 1e-12 * scale;
    mo.rel_gap = o.rel_gap;
    mo.offset = dollars(m.constant);
    mo.node_limit = o.node_limit;
    if (start) mo.start = *start;
    else mo.start.assign(m.lp.cols(), 0.0);  // everything standalone is always feasible
    mo.priority = m.priority;
    mo.root_basis = o.warm_start;
    if (guide) {
        mo.guide = *guide;
        for (double& v : mo.guide) v = std::round(v);  // only integer columns read it
    }
    MipSolution mip = simplex ? branch_and_bound(*simplex, m.lp, m.integer, mo) : branch_and_bound(m.lp, m.integer, mo);
    if (mip.status != MipStatus::optimal && mip.status != MipStatus::node_limit)
        throw std::runtime_error(std::string("the subproblem did not solve: ") + status_name(mip.status));

    Solution s = read_solution(m, p, mip.x);
    s.total = check_solution(p, r, s);
    for (const auto& l : p.options) s.all_standalone += separate({l}, p.market, r).total();
    if (p.stock.shares != 0) s.all_standalone += stock(p.stock, r).total();

    const double constant = dollars(m.constant);
    s.lp_objective = constant + mip.objective;
    s.lp_bound = constant + mip.root.objective;
    double total = dollars(s.total);
    // The model prices a group at its maximum loss; Phase 1 prices a spread at the lesser
    // of that and its shorts' uncovered requirement (R2). They agree wherever pairing pays,
    // so always at the optimum, but an assignment accepted within the gap can hold a group
    // that Phase 1 prices lower. The checker's total is the one reported; the model's can
    // never be below it.
    if (total > s.lp_objective + 1e-9 * std::max(1.0, std::fabs(total)) ||
        (o.rel_gap == 0 && mip.status == MipStatus::optimal &&
         s.lp_objective - total > 1e-9 * std::max(1.0, std::fabs(total))))
        throw std::logic_error("the model's objective " + std::to_string(s.lp_objective) +
                               " disagrees with the checker's total " + std::to_string(total));
    s.gap = total > 0 ? (total - s.lp_bound) / total : 0;
    s.status = mip.status;
    s.bound = std::max(s.lp_bound, constant + mip.bound);
    s.proven_gap = total > 0 ? std::max(0.0, (total - s.bound) / total) : 0;

    s.lp_integral = true;
    for (int j = 0; j < m.lp.cols(); ++j)
        if (m.integer[j] && std::fabs(mip.root.x[j] - std::round(mip.root.x[j])) > 1e-6) s.lp_integral = false;

    // ∂total/∂cap is the unit's standalone cost (it enters the constant) plus the capacity
    // row's dual when the row is held at its upper bound; otherwise extra units would stay
    // standalone.
    auto shadow = [&](int position, Money unit) {
        int row = m.capacity_row[position];
        double d = 0;
        if (row >= 0) d = mip.root.basis.state[m.lp.cols() + row] == 2 ? mip.root.row_dual[row] : 0.0;
        else if (int j = m.capacity_column[position]; j >= 0 && mip.root.basis.state[j] == 2)
            d = mip.root.reduced_cost[j];
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
    s.root_iterations = mip.root.iterations;
    s.root_basis = mip.root.basis;
    if (x) *x = std::move(mip.x);
    return s;
}

// The same matrix and costs: then one model's basis and inverse serve the other.
bool same_shape(const Lp& a, const Lp& b) {
    if (a.rows() != b.rows() || a.cols() != b.cols() || a.cost != b.cost) return false;
    for (int j = 0; j < a.cols(); ++j) {
        const auto &x = a.columns[j], &y = b.columns[j];
        if (x.size() != y.size()) return false;
        for (std::size_t k = 0; k < x.size(); ++k)
            if (x[k].row != y[k].row || x[k].value != y[k].value) return false;
    }
    return true;
}

bool feasible(const Lp& lp, const std::vector<double>& x) {
    if (static_cast<int>(x.size()) != lp.cols()) return false;
    std::vector<double> activity(lp.rows(), 0.0);
    for (int j = 0; j < lp.cols(); ++j) {
        if (x[j] < lp.col_lo[j] - 1e-9 || x[j] > lp.col_up[j] + 1e-9) return false;
        for (const auto& e : lp.columns[j]) activity[e.row] += e.value * x[j];
    }
    for (int i = 0; i < lp.rows(); ++i) {
        const double tol = 1e-9 * (1 + std::fabs(activity[i]));
        if (activity[i] < lp.row_lo[i] - tol || activity[i] > lp.row_up[i] + tol) return false;
    }
    return true;
}

// A basis for `to` from a basis of `from`, matching rows and columns by key: each keeps its
// state, new columns sit at the bound their cost makes dual feasible (as in the slack
// basis), and new rows' logicals are basic. The basic count is then made the row count:
// surplus logicals, then surplus columns, become nonbasic; a shortfall is made up with
// logicals, first of the rows that basic columns of `from` missing from `to` touched,
// since those are the rows that lost their basic variable. (Any logicals left the dual
// simplex up to 3,000 pivots from the optimum after a close; those rows' take it a few.)
// refactor() repairs any singularity left. Every variable is boxed, so the dual
// simplex restores dual feasibility by bound flips.
LpBasis map_basis(const Model& from, const LpBasis& b, const Model& to) {
    const int n0 = from.lp.cols(), n1 = to.lp.cols(), m1 = to.lp.rows();
    std::unordered_map<std::uint64_t, int> col, row;
    for (int j = 0; j < n0; ++j) col.emplace(from.col_key[j], j);
    for (int i = 0; i < from.lp.rows(); ++i) row.emplace(from.row_key[i], i);
    LpBasis out;
    out.state.assign(n1 + m1, 1);
    std::vector<int> basic_cols, basic_logicals;
    for (int j = 0; j < n1; ++j) {
        auto it = col.find(to.col_key[j]);
        signed char st = it != col.end() ? b.state[it->second] : (to.lp.cost[j] >= 0 ? 1 : 2);
        out.state[j] = st;
        if (st == 0) basic_cols.push_back(j);
    }
    for (int i = 0; i < m1; ++i) {
        auto it = row.find(to.row_key[i]);
        signed char st = it != row.end() ? b.state[n0 + it->second] : 0;
        out.state[n1 + i] = st;
        if (st == 0) basic_logicals.push_back(n1 + i);
    }
    while (static_cast<int>(basic_cols.size() + basic_logicals.size()) > m1) {
        int v;
        if (!basic_logicals.empty()) {
            v = basic_logicals.back();
            basic_logicals.pop_back();
        } else {
            v = basic_cols.back();
            basic_cols.pop_back();
        }
        out.state[v] = 1;
    }
    std::vector<int> lost;  // rows of `to` that a dropped basic column of `from` touched
    {
        std::unordered_map<std::uint64_t, int> to_row, to_col;
        for (int i = 0; i < m1; ++i) to_row.emplace(to.row_key[i], i);
        for (int j = 0; j < n1; ++j) to_col.emplace(to.col_key[j], j);
        for (int j = 0; j < n0; ++j) {
            if (b.state[j] != 0 || to_col.count(from.col_key[j])) continue;
            for (const auto& e : from.lp.columns[j])
                if (auto it = to_row.find(from.row_key[e.row]); it != to_row.end()) lost.push_back(it->second);
        }
    }
    auto add_logical = [&](int i) {
        if (static_cast<int>(basic_cols.size() + basic_logicals.size()) >= m1 || out.state[n1 + i] == 0) return;
        out.state[n1 + i] = 0;
        basic_logicals.push_back(n1 + i);
    };
    for (int i : lost) add_logical(i);
    for (int i = 0; i < m1; ++i) add_logical(i);
    for (int v : basic_cols) out.state[v] = 0;
    for (int v : basic_logicals) out.state[v] = 0;
    out.head = basic_cols;
    out.head.insert(out.head.end(), basic_logicals.begin(), basic_logicals.end());
    return out;
}

// The book's assignment carried to another model by column key; new columns are 0.
std::vector<double> map_assignment(const Model& from, const std::vector<double>& x, const Model& to) {
    std::unordered_map<std::uint64_t, int> col;
    for (int j = 0; j < from.lp.cols(); ++j) col.emplace(from.col_key[j], j);
    std::vector<double> y(to.lp.cols(), 0.0);
    for (int j = 0; j < to.lp.cols(); ++j)
        if (auto it = col.find(to.col_key[j]); it != col.end()) y[j] = x[it->second];
    return y;
}

}  // namespace

Solution solve(const Portfolio& p, const RuleSet& r, const SolveOptions& o) {
    Model m = build_model(p, r, o);
    return solve_model(p, r, o, m, nullptr, nullptr, nullptr);
}

Book::Book(Portfolio p, RuleSet r, SolveOptions o) : p_(std::move(p)), r_(std::move(r)), o_(std::move(o)) {
    model_ = std::make_unique<Model>(build_model(p_, r_, o_));
    simplex_ = std::make_unique<DualSimplex>(model_->lp);
    SolveOptions cold = o_;
    cold.warm_start = {};
    s_ = solve_model(p_, r_, cold, *model_, simplex_.get(), nullptr, &x_);
}

Book::~Book() = default;

Portfolio Book::after(const OptionLeg& order) const {
    Portfolio q = p_;
    auto same_series = [&](const OptionLeg& l) {
        const Option &a = l.option, &b = order.option;
        return a.underlying == b.underlying && a.type == b.type && a.strike == b.strike && a.expiry == b.expiry &&
               a.style == b.style && a.listing == b.listing && a.deliverable == b.deliverable &&
               a.product == b.product;
    };
    auto it = std::find_if(q.options.begin(), q.options.end(), same_series);
    if (it == q.options.end()) {
        if (order.quantity != 0) q.options.push_back(order);
    } else {
        it->quantity += order.quantity;
        it->value = order.value;
        if (it->quantity == 0) q.options.erase(it);
    }
    return q;
}

Portfolio Book::after_stock(std::int64_t shares) const {
    Portfolio q = p_;
    if (q.stock.shares == 0) q.stock.price = q.market.underlying;
    q.stock.shares += shares;
    return q;
}

Book::Trial Book::price(Portfolio q) {
    Trial t;
    t.portfolio = std::move(q);
    t.model = std::make_unique<Model>(build_model(t.portfolio, r_, o_));
    SolveOptions so = o_;
    so.warm_start = {};
    if (same_shape(t.model->lp, model_->lp)) {
        // Only bounds moved: the book's simplex keeps its basis and inverse, and the book's
        // pairing, where it still fits, is the first incumbent.
        const Lp& lp = t.model->lp;
        for (int j = 0; j < lp.cols(); ++j) simplex_->set_bounds(j, lp.col_lo[j], lp.col_up[j]);
        for (int i = 0; i < lp.rows(); ++i) simplex_->set_bounds(lp.cols() + i, lp.row_lo[i], lp.row_up[i]);
        const bool fits = feasible(lp, x_);
        t.solution = solve_model(t.portfolio, r_, so, *t.model, simplex_.get(), fits ? &x_ : nullptr, &t.x, &x_);
        t.shape_kept = true;
    } else {
        // A new model: it starts from the book's root basis and pairing, matched by key.
        so.warm_start = map_basis(*model_, s_.root_basis, *t.model);
        std::vector<double> start = map_assignment(*model_, x_, *t.model);
        const bool fits = feasible(t.model->lp, start);
        t.solution = solve_model(t.portfolio, r_, so, *t.model, nullptr, fits ? &start : nullptr, &t.x, &start);
    }
    return t;
}

void Book::restore_bounds() {
    const Lp& lp = model_->lp;
    for (int j = 0; j < lp.cols(); ++j) simplex_->set_bounds(j, lp.col_lo[j], lp.col_up[j]);
    for (int i = 0; i < lp.rows(); ++i) simplex_->set_bounds(lp.cols() + i, lp.row_lo[i], lp.row_up[i]);
}

// A close is priced on the book's own model and simplex: every column that uses the
// position is held at 0, so the position stays standalone and interacts with nothing, and
// its standalone requirement then comes off. That equals pricing the book without it, and
// keeps the book's basis: through a new model, one close in 40 took 3,000 pivots (0.5 s)
// on a 1,000-series book.
Solution Book::price_close(int i) {
    Lp& lp = model_->lp;
    std::vector<std::pair<int, double>> held;  // column, its upper bound
    const int row = model_->capacity_row[i];
    for (int j = 0; j < lp.cols(); ++j) {
        bool uses = j == model_->capacity_column[i];
        if (row >= 0)
            for (const auto& e : lp.columns[j]) uses |= e.row == row;
        if (!uses || lp.col_up[j] == 0) continue;
        held.push_back({j, lp.col_up[j]});
        lp.col_up[j] = 0;
        simplex_->set_bounds(j, lp.col_lo[j], 0);
    }
    SolveOptions so = o_;
    so.warm_start = {};
    std::vector<double> x;
    Solution s = solve_model(p_, r_, so, *model_, simplex_.get(), nullptr, &x, &x_);
    for (auto [j, up] : held) lp.col_up[j] = up;
    restore_bounds();

    auto it = std::find_if(s.residuals.begin(), s.residuals.end(), [&](const Residual& res) { return res.leg.position == i; });
    if (it == s.residuals.end()) throw std::logic_error("a closed position is not standalone");
    const Money standalone = it->requirement.total();
    s.residuals.erase(it);
    auto renumber = [&](int& position) {
        if (position > i) --position;
    };
    for (auto& st : s.structures)
        for (auto& l : st.legs) renumber(l.position);
    for (auto& res : s.residuals) renumber(res.leg.position);
    s.shadow_options.erase(s.shadow_options.begin() + i);
    s.total -= standalone;
    s.all_standalone -= standalone;
    const double d = static_cast<double>(standalone.micros()) / Money::per_dollar;
    s.lp_objective -= d;
    s.lp_bound -= d;
    s.bound -= d;
    const double total = static_cast<double>(s.total.micros()) / Money::per_dollar;
    s.gap = total > 0 ? (total - s.lp_bound) / total : 0;
    s.proven_gap = total > 0 ? std::max(0.0, (total - s.bound) / total) : 0;
    s.root_basis = {};  // the book's model, not the closed book's
    return s;
}

Solution Book::what_if(const OptionLeg& order) {
    for (std::size_t i = 0; i < p_.options.size(); ++i) {
        const Option &a = p_.options[i].option, &b = order.option;
        if (a.underlying == b.underlying && a.type == b.type && a.strike == b.strike && a.expiry == b.expiry &&
            a.style == b.style && a.listing == b.listing && a.deliverable == b.deliverable && a.product == b.product &&
            p_.options[i].quantity + order.quantity == 0 && p_.options.size() > 1)
            return price_close(static_cast<int>(i));
    }
    Trial t = price(after(order));
    if (t.shape_kept) restore_bounds();
    return std::move(t.solution);
}

Solution Book::what_if_stock(std::int64_t shares) {
    Trial t = price(after_stock(shares));
    if (t.shape_kept) restore_bounds();
    return std::move(t.solution);
}

void Book::commit(Trial t) {
    p_ = std::move(t.portfolio);
    s_ = std::move(t.solution);
    x_ = std::move(t.x);
    if (t.shape_kept) {
        // The simplex refers to model_->lp, whose matrix is t's; only the bounds move.
        model_->lp.col_lo = t.model->lp.col_lo;
        model_->lp.col_up = t.model->lp.col_up;
        model_->lp.row_lo = t.model->lp.row_lo;
        model_->lp.row_up = t.model->lp.row_up;
        model_->constant = t.model->constant;
        model_->capacity_row = t.model->capacity_row;
        model_->capacity_column = t.model->capacity_column;
    } else {
        model_ = std::move(t.model);
        simplex_ = std::make_unique<DualSimplex>(model_->lp);
    }
}

void Book::fill(const OptionLeg& order) { commit(price(after(order))); }

void Book::fill_stock(std::int64_t shares) { commit(price(after_stock(shares))); }

}  // namespace pairing
