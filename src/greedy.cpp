// The Phase 3 greedy baseline (docs/plan.md): a fixed template priority with nearest
// strikes first, standing in for common production practice. It pairs two legs at a time
// (then merges call and put spreads into iron condors), takes a pairing whenever Phase 1
// prices it below the legs' standalone requirements, and never revisits a choice. The checker prices the result, as it does the solver's.
#include <algorithm>
#include <cstdlib>
#include <numeric>
#include <stdexcept>
#include <tuple>

#include "pairing/solver.hpp"

namespace pairing {

namespace {

template <class F>
bool accepted(F&& f, Requirement& out) {
    try {
        out = f();
        return true;
    } catch (const std::invalid_argument&) {
        return false;
    }
}

Money abs_diff(Money a, Money b) { return a < b ? b - a : a - b; }

}  // namespace

Solution greedy(const Portfolio& p, const RuleSet& r, const SolveOptions& o) {
    const std::int64_t lots = o.lots_per_contract;
    const int n = static_cast<int>(p.options.size());
    std::vector<std::int64_t> left(n);
    for (int i = 0; i < n; ++i) left[i] = std::llabs(p.options[i].quantity) * lots;
    std::int64_t shares_left = std::llabs(p.stock.shares);
    const Market& mk = p.market;

    Solution s;
    s.lots_per_contract = lots;
    auto leg = [&](int i, std::int64_t q) { return lot_leg(p.options[i], q, lots); };
    auto alone = [&](int i, std::int64_t q) { return separate({leg(i, q)}, mk, r).total(); };
    auto is = [&](int i, OptionType t, int side) {
        return p.options[i].option.type == t && (p.options[i].quantity > 0) == (side > 0);
    };

    // Shorts are covered in order of their standalone requirement per lot, most expensive
    // first, so the costliest shorts get the longs (index order would make the baseline
    // weaker than practice for no reason).
    std::vector<int> shorts_first(n);
    std::iota(shorts_first.begin(), shorts_first.end(), 0);
    std::vector<Money> per_lot(n);
    for (int i = 0; i < n; ++i) per_lot[i] = alone(i, 1);
    std::stable_sort(shorts_first.begin(), shorts_first.end(), [&](int a, int b) { return per_lot[b] < per_lot[a]; });

    // 1. Vertical and calendar spreads: each short against the nearest-strike long of its
    //    type and contract size that Phase 1 accepts as a spread, one lot for one lot.
    for (OptionType t : {OptionType::call, OptionType::put}) {
        for (int i : shorts_first) {
            if (!is(i, t, -1)) continue;
            std::vector<int> longs;
            for (int j = 0; j < n; ++j)
                if (is(j, t, +1) && p.options[j].option.deliverable == p.options[i].option.deliverable) longs.push_back(j);
            std::stable_sort(longs.begin(), longs.end(), [&](int a, int b) {
                return std::make_tuple(abs_diff(p.options[a].option.strike, p.options[i].option.strike), p.options[a].option.expiry) <
                       std::make_tuple(abs_diff(p.options[b].option.strike, p.options[i].option.strike), p.options[b].option.expiry);
            });
            for (int j : longs) {
                const std::int64_t q = std::min(left[i], left[j]);
                if (q <= 0) continue;
                std::vector<OptionLeg> legs = {leg(j, q), leg(i, q)};
                if (!spread_validity(legs, r)) continue;
                Requirement req;
                if (!accepted([&] { return spread(legs, mk, r).requirement; }, req)) continue;
                if (!(req.total() < alone(i, q) + alone(j, q))) continue;
                s.structures.push_back({StructureKind::spread, {{j, q}, {i, q}}, {}});
                left[i] -= q;
                left[j] -= q;
                if (left[i] == 0) break;
            }
        }
    }

    // 1b. Iron condors and butterflies: a call spread and a put spread of the same size
    //     and expirations merge into one four-leg spread when Phase 1 prices it lower,
    //     since a price can finish beyond only one of the two (R2's maximum loss).
    for (std::size_t a = 0; a < s.structures.size(); ++a) {
        for (std::size_t b = a + 1; b < s.structures.size(); ++b) {
            Structure &x = s.structures[a], &y = s.structures[b];
            if (x.kind != StructureKind::spread || y.kind != StructureKind::spread || x.legs.size() != 2 ||
                y.legs.size() != 2 || x.legs[0].quantity != y.legs[0].quantity)
                continue;
            const auto& ox = p.options[x.legs[0].position].option;
            const auto& oy = p.options[y.legs[0].position].option;
            if (ox.type == oy.type) continue;
            std::vector<OptionLeg> two_x, two_y, four;
            for (const auto& l : x.legs) two_x.push_back(leg(l.position, l.quantity));
            for (const auto& l : y.legs) two_y.push_back(leg(l.position, l.quantity));
            four = two_x;
            four.insert(four.end(), two_y.begin(), two_y.end());
            if (!spread_validity(four, r)) continue;
            Requirement req;
            if (!accepted([&] { return spread(four, mk, r).requirement; }, req)) continue;
            Money apart = spread(two_x, mk, r).requirement.total() + spread(two_y, mk, r).requirement.total();
            if (!(req.total() < apart)) continue;
            x.legs.insert(x.legs.end(), y.legs.begin(), y.legs.end());
            s.structures.erase(s.structures.begin() + static_cast<std::ptrdiff_t>(b));
            break;
        }
    }

    // 2. Short straddles and strangles: each remaining short put against the nearest-strike
    //    remaining short call of its contract size.
    for (int i : shorts_first) {
        if (!is(i, OptionType::put, -1)) continue;
        std::vector<int> calls;
        for (int j = 0; j < n; ++j)
            if (is(j, OptionType::call, -1) && p.options[j].option.deliverable == p.options[i].option.deliverable)
                calls.push_back(j);
        std::stable_sort(calls.begin(), calls.end(), [&](int a, int b) {
            return abs_diff(p.options[a].option.strike, p.options[i].option.strike) <
                   abs_diff(p.options[b].option.strike, p.options[i].option.strike);
        });
        for (int j : calls) {
            const std::int64_t q = std::min(left[i], left[j]);
            if (q <= 0) continue;
            Requirement req;
            if (!accepted([&] { return short_straddle(leg(i, q), leg(j, q), mk, r); }, req)) continue;
            if (!(req.total() < alone(i, q) + alone(j, q))) continue;
            s.structures.push_back({StructureKind::straddle, {{i, q}, {j, q}}, {}});
            left[i] -= q;
            left[j] -= q;
            if (left[i] == 0) break;
        }
    }

    // 3. Stock against single options: covered calls or puts first, then protective puts or
    //    calls, each in order of strike nearest the stock price.
    if (p.stock.shares != 0) {
        const bool long_stock = p.stock.shares > 0;
        const OptionType cover = long_stock ? OptionType::call : OptionType::put;
        const OptionType protect = long_stock ? OptionType::put : OptionType::call;
        const StructureKind cover_kind = long_stock ? StructureKind::covered_call : StructureKind::covered_put;
        const StructureKind protect_kind = long_stock ? StructureKind::protective_put : StructureKind::protective_call;
        for (auto [t, side, kind] : {std::make_tuple(cover, -1, cover_kind), std::make_tuple(protect, +1, protect_kind)}) {
            std::vector<int> c;
            for (int i = 0; i < n; ++i)
                if (is(i, t, side)) c.push_back(i);
            std::stable_sort(c.begin(), c.end(), [&](int a, int b) {
                return abs_diff(p.options[a].option.strike, p.stock.price) < abs_diff(p.options[b].option.strike, p.stock.price);
            });
            for (int i : c) {
                const std::int64_t per_lot = leg(i, 1).option.deliverable;
                const std::int64_t q = std::min(left[i], shares_left / per_lot);
                if (q <= 0) continue;
                StockLeg st{long_stock ? q * per_lot : -q * per_lot, p.stock.price};
                Requirement req;
                bool ok = accepted(
                    [&] {
                        switch (kind) {
                            case StructureKind::covered_call: return covered_call(st, leg(i, q), mk, r);
                            case StructureKind::covered_put: return covered_put(st, leg(i, q), mk, r);
                            case StructureKind::protective_put: return protective_put(st, leg(i, q), mk, r);
                            default: return protective_call(st, leg(i, q), mk, r);
                        }
                    },
                    req);
                if (!ok || !(req.total() < alone(i, q) + stock(st, r).total())) continue;
                s.structures.push_back({kind, {{stock_position, q * per_lot}, {i, q}}, {}});
                left[i] -= q;
                shares_left -= q * per_lot;
            }
        }
    }

    for (int i = 0; i < n; ++i)
        if (left[i] > 0) s.residuals.push_back({{i, left[i]}, {}});
    if (shares_left > 0) s.residuals.push_back({{stock_position, shares_left}, {}});
    s.total = check_solution(p, r, s);
    for (const auto& l : p.options) s.all_standalone += separate({l}, mk, r).total();
    if (p.stock.shares != 0) s.all_standalone += stock(p.stock, r).total();
    return s;
}

}  // namespace pairing
