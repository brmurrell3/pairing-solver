#pragma once

// Seeded portfolio generators for the Phase 3 benchmarks (data/README.md, "What still has
// to be built"). Marks come from a synthetic chain priced with Black-Scholes, so every
// book is deterministic, reproducible and safe to publish.

#include <algorithm>
#include <cmath>
#include <map>
#include <random>
#include <string>
#include <tuple>
#include <vector>

#include "generate.hpp"
#include "pairing/solver.hpp"

namespace books {

using namespace pairing;

inline Money cents(long c) { return Money::from_micros(c * 10'000); }

// A synthetic option chain: one underlying, a strike grid, a set of expirations, and
// Black-Scholes marks at a flat 30% volatility and zero rates and dividends.
struct Chain {
    Date as_of{2026, 1, 15};
    long spot = 0;  // cents
    long step = 0;  // strike spacing, cents
    std::vector<Date> expiries;

    static Chain make(std::mt19937_64& rng, int expiries) {
        Chain c;
        c.spot = gen::uniform_int(rng, 2'000, 30'000);
        c.step = c.spot < 5'000 ? 100 : c.spot < 20'000 ? 250 : 500;
        const Date all[] = {{2026, 2, 20}, {2026, 3, 20}, {2026, 4, 17}, {2026, 6, 19},
                            {2026, 9, 18}, {2026, 12, 18}, {2027, 1, 15}, {2027, 6, 18}};
        for (int i = 0; i < std::min(expiries, 8); ++i) c.expiries.push_back(all[i]);
        return c;
    }
    long atm() const { return (spot + step / 2) / step * step; }
    static double years(Date from, Date to) {
        auto days = [](Date d) {  // days since 1970-01-01 (civil calendar)
            int y = d.year - (d.month <= 2), era = y / 400, yoe = y - era * 400;
            int doy = (153 * (d.month + (d.month > 2 ? -3 : 9)) + 2) / 5 + d.day - 1;
            return era * 146097 + yoe * 365 + yoe / 4 - yoe / 100 + doy - 719468;
        };
        return (days(to) - days(from)) / 365.0;
    }
    // Mark per share, in cents, at least one cent.
    long mark(OptionType t, long strike, Date expiry) const {
        const double s = spot / 100.0, k = strike / 100.0, tau = std::max(years(as_of, expiry), 1.0 / 365);
        const double vol = 0.30, sd = vol * std::sqrt(tau);
        const double d1 = (std::log(s / k) + 0.5 * sd * sd) / sd, d2 = d1 - sd;
        auto n = [](double x) { return 0.5 * std::erfc(-x / std::sqrt(2.0)); };
        double call = s * n(d1) - k * n(d2);
        double v = t == OptionType::call ? call : call - s + k;
        return std::max(1L, std::lround(v * 100));
    }
};

// Accumulates legs by series, so trades that touch one series net out.
struct Book {
    const Chain& chain;
    std::map<std::tuple<int, long, int, int>, std::int64_t> legs{};  // (type, strike, expiry index, deliverable) -> qty
    std::int64_t shares = 0;

    void add(OptionType t, long strike, int expiry, std::int64_t qty, int deliverable = 100) {
        if (strike > 0) legs[{static_cast<int>(t), strike, expiry, deliverable}] += qty;
    }
    Portfolio portfolio() const {
        Portfolio p;
        p.market.as_of = chain.as_of;
        p.market.underlying = cents(chain.spot);
        for (const auto& [key, q] : legs) {
            if (q == 0) continue;
            auto [t, strike, e, w] = key;
            OptionLeg l;
            l.option.underlying = "XYZ";
            l.option.type = static_cast<OptionType>(t);
            l.option.strike = cents(strike);
            l.option.expiry = chain.expiries[e];
            l.option.deliverable = w;
            l.quantity = q;
            // An adjusted series delivers w shares; its per-share mark is the ordinary one.
            l.value = cents(chain.mark(l.option.type, strike, l.option.expiry));
            p.options.push_back(l);
        }
        if (shares != 0) p.stock = StockLeg{shares, cents(chain.spot)};
        return p;
    }
};

// Portable draws (tests/generate.hpp), so a seed gives the same book on every platform.
inline int pick(std::mt19937_64& rng, int lo, int hi) { return gen::uniform_int(rng, lo, hi); }
inline bool chance(std::mt19937_64& rng, double p) { return gen::uniform_01(rng) < p; }

// Retail-like: a few verticals, iron condors, covered calls and single options, 1 to 5 lots.
inline Portfolio retail(std::mt19937_64& rng) {
    Chain c = Chain::make(rng, 4);
    Book b{c};
    const int trades = pick(rng, 1, 6);
    for (int i = 0; i < trades; ++i) {
        const int e = pick(rng, 0, 3);
        const std::int64_t q = pick(rng, 1, 5);
        const long k = c.atm() + c.step * pick(rng, -6, 6), w = c.step * pick(rng, 1, 3);
        const OptionType t = chance(rng, 0.5) ? OptionType::call : OptionType::put;
        const int sign = chance(rng, 0.5) ? 1 : -1;
        switch (pick(rng, 0, 4)) {
            case 0:  // vertical, debit or credit
                b.add(t, k, e, sign * q);
                b.add(t, t == OptionType::call ? k + w : k - w, e, -sign * q);
                break;
            case 1: {  // iron condor
                const long put_short = c.atm() - c.step * pick(rng, 1, 4), call_short = c.atm() + c.step * pick(rng, 1, 4);
                b.add(OptionType::put, put_short, e, -q);
                b.add(OptionType::put, put_short - w, e, q);
                b.add(OptionType::call, call_short, e, -q);
                b.add(OptionType::call, call_short + w, e, q);
                break;
            }
            case 2:  // covered call
                b.shares += 100 * q;
                b.add(OptionType::call, c.atm() + c.step * pick(rng, 0, 5), e, -q);
                break;
            case 3:  // calendar
                b.add(t, k, e, -q);
                b.add(t, k, std::min(3, e + 1), q);
                break;
            default:  // single option
                b.add(t, k, e, sign * q);
        }
    }
    return b.portfolio();
}

// Market-maker-like: n distinct series on both sides of many strikes and expirations,
// 1 to 50 contracts each, with a stock hedge half the time.
inline Portfolio market_maker(std::mt19937_64& rng, int n) {
    Chain c = Chain::make(rng, 8);
    Book b{c};
    const int half = std::max(10, n / 8);  // strikes each side of the money
    for (int tries = 0; static_cast<int>(b.legs.size()) < n && tries < 50 * n; ++tries) {
        const OptionType t = chance(rng, 0.5) ? OptionType::call : OptionType::put;
        const long k = c.atm() + c.step * pick(rng, -half, half);
        const int e = pick(rng, 0, 7);
        if (k <= 0 || b.legs.count({static_cast<int>(t), k, e, 100})) continue;
        b.add(t, k, e, pick(rng, 1, 50) * (chance(rng, 0.5) ? 1 : -1));
    }
    if (chance(rng, 0.5)) b.shares = 100 * pick(rng, 1, 100) * (chance(rng, 0.5) ? 1 : -1);
    return b.portfolio();
}

// One expiration (the June one), 100-share series on both sides, 1 to max_quantity
// contracts each, no stock: the scope of solve_strike_dp.
inline Portfolio one_expiry(std::mt19937_64& rng, int n, int max_quantity) {
    Chain c = Chain::make(rng, 4);
    Book b{c};
    const int half = std::max(10, n / 4);
    for (int tries = 0; static_cast<int>(b.legs.size()) < n && tries < 50 * n; ++tries) {
        const OptionType t = chance(rng, 0.5) ? OptionType::call : OptionType::put;
        const long k = c.atm() + c.step * pick(rng, -half, half);
        if (k <= 0 || b.legs.count({static_cast<int>(t), k, 3, 100})) continue;
        b.add(t, k, 3, pick(rng, 1, max_quantity) * (chance(rng, 0.5) ? 1 : -1));
    }
    return b.portfolio();
}

// Adjusted series: a retail book in which about a third of the series deliver 150 shares
// (as after a 3-for-2 split) and some 10 (mini contracts).
inline Portfolio adjusted(std::mt19937_64& rng) {
    Portfolio p = retail(rng);
    for (auto& l : p.options) {
        if (chance(rng, 0.3)) l.option.deliverable = 150;
        else if (chance(rng, 0.1)) l.option.deliverable = 10;
    }
    // Two series that now differ only in deliverable stay distinct positions.
    return p;
}

}  // namespace books
