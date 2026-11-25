#pragma once

// Random (account, underlying) subproblems for the differential tests, from fixed seeds.
// Prices are whole cents and deliverables 10, 100 or 150, so every Phase 1 requirement is
// exactly proportional to quantity and solver totals can be compared without tolerance.

#include <algorithm>
#include <cmath>
#include <random>
#include <set>
#include <tuple>

#include "pairing/solver.hpp"

namespace gen {

struct Shape {
    int max_series = 7;      // option positions; the count is drawn from 1..max_series
    int max_quantity = 3;    // contracts per position
    int max_stock_lots = 3;  // stock in hundreds of shares; 0 for none
    int expiries = 3;        // drawn from six dates, two of them beyond nine months
    int strikes = 6;         // strikes on each side of the money, roughly
    bool adjusted = false;   // some 150-share series
    bool minis = false;      // some 10-share series
};

inline pairing::Money cents(long c) { return pairing::Money::from_micros(c * 10'000); }

inline pairing::Portfolio portfolio(std::mt19937_64& rng, const Shape& s) {
    using namespace pairing;
    auto uniform = [&](int lo, int hi) { return std::uniform_int_distribution<int>(lo, hi)(rng); };
    auto chance = [&](double p) { return std::uniform_real_distribution<double>(0, 1)(rng) < p; };

    Portfolio p;
    p.market.as_of = Date{2026, 1, 15};
    long spot = uniform(20, 150) * 100 + uniform(0, 99);  // cents
    p.market.underlying = cents(spot);
    bool index = chance(0.1);
    long step = spot < 5000 ? 250 : 500;
    long center = (spot + step / 2) / step * step;

    const Date all[] = {{2026, 2, 20}, {2026, 3, 20}, {2026, 6, 19}, {2026, 9, 18}, {2027, 1, 15}, {2027, 6, 18}};
    std::vector<Date> dates(std::begin(all), std::end(all));
    std::shuffle(dates.begin(), dates.end(), rng);
    dates.resize(std::min<std::size_t>(s.expiries, dates.size()));

    int series = uniform(1, s.max_series);
    std::set<std::tuple<int, long, Date, std::int64_t, int, int>> seen;
    for (int tries = 0; static_cast<int>(p.options.size()) < series && tries < 50 * series; ++tries) {
        OptionLeg l;
        Option& o = l.option;
        o.underlying = index ? "IDX" : "XYZ";
        o.product = index ? ProductClass::broad_index : ProductClass::equity;
        o.type = chance(0.5) ? OptionType::call : OptionType::put;
        long k = center + step * uniform(-s.strikes, s.strikes);
        if (k <= 0) continue;
        o.strike = cents(k);
        o.expiry = dates[uniform(0, static_cast<int>(dates.size()) - 1)];
        o.style = chance(index ? 0.7 : 0.1) ? Style::european : Style::american;
        o.deliverable = 100;
        if (s.adjusted && chance(0.2)) o.deliverable = 150;
        if (s.minis && chance(0.1)) o.deliverable = 10;
        l.quantity = uniform(1, s.max_quantity) * (chance(0.45) ? -1 : 1);
        // OTC shorts have no uncovered formula in the engine yet, so OTC positions are long.
        if (l.quantity > 0 && chance(0.05)) o.listing = Listing::otc;

        // Intrinsic value plus a time value that decays away from the money.
        double years = ((o.expiry.year - 2026) * 12 + o.expiry.month - 1 + 0.2) / 12.0;
        double intrinsic = std::max(0.0, static_cast<double>(o.type == OptionType::call ? spot - k : k - spot));
        double width = 0.3 * static_cast<double>(spot) * std::sqrt(years) + 100;
        double z = static_cast<double>(k - spot) / width;
        double time = 0.12 * static_cast<double>(spot) * std::sqrt(years) * std::exp(-z * z);
        l.value = cents(std::max(5L, std::lround(intrinsic + time)));

        auto key = std::make_tuple(static_cast<int>(o.type), k, o.expiry, o.deliverable, static_cast<int>(o.style),
                                   static_cast<int>(o.listing));
        if (!seen.insert(key).second) continue;
        p.options.push_back(l);
    }
    if (!index && s.max_stock_lots > 0 && chance(0.5)) {
        p.stock.shares = 100 * uniform(1, s.max_stock_lots) * (chance(0.4) ? -1 : 1);
        p.stock.price = p.market.underlying;
    }
    return p;
}

inline pairing::RuleSet rules(std::mt19937_64& rng, pairing::ExpiryRule e) {
    using namespace pairing;
    auto chance = [&](double p) { return std::uniform_real_distribution<double>(0, 1)(rng) < p; };
    RuleSet r;
    r.expiry_rule = e;
    r.basis = chance(0.5) ? Basis::initial : Basis::maintenance;
    r.hedged_short_value = chance(0.5) ? HedgedShortValue::exercise_price : HedgedShortValue::market_value;
    r.european_calendars = chance(0.7) ? EuropeanCalendars::allowed : EuropeanCalendars::disallowed;
    return r;
}

}  // namespace gen
