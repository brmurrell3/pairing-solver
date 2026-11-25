#include <algorithm>
#include <cstdlib>
#include <stdexcept>

#include "pairing/margin.hpp"

namespace pairing {

namespace {

void require(bool ok, const char* what) {
    if (!ok) throw std::invalid_argument(what);
}

Money positive_part(Money m) { return std::max(m, Money{}); }

bool is_short(const OptionLeg& l, OptionType t) { return l.quantity < 0 && l.option.type == t; }
bool is_long(const OptionLeg& l, OptionType t) { return l.quantity > 0 && l.option.type == t; }

// The stock leg covers exactly the option's share-equivalents, on the stated side.
void require_cover(const StockLeg& s, const OptionLeg& o, bool stock_long) {
    require(stock_long ? s.shares > 0 : s.shares < 0, "stock leg is on the wrong side");
    require(std::llabs(s.shares) == std::llabs(o.units()), "stock does not match the option's share-equivalents");
}

void require_american(const OptionLeg& o) {
    require(o.option.style == Style::american, "hedged-underlying minimums need American-style options");
}

void require_same_underlying(const OptionLeg& a, const OptionLeg& b) {
    require(a.option.underlying == b.option.underlying, "options have different underlyings");
}

Money stock_value(const StockLeg& s) { return s.price * std::llabs(s.shares); }

// 4210(c)(2)–(3), on top of 100% of the short market value.
Money short_stock_addon(const StockLeg& s, const RuleSet& r) {
    std::int64_t n = std::llabs(s.shares);
    Money mv = stock_value(s);
    if (s.price < r.short_low_price) return std::max(r.short_low_per_share * n, r.short_low_percentage * mv);
    return std::max(r.short_per_share * n, r.short_percentage * mv);
}

// Base value of the short stock in the R8 short-side hedges; see HedgedShortValue.
Money hedged_short_base(const StockLeg& s, Money call_strike, const RuleSet& r) {
    std::int64_t n = std::llabs(s.shares);
    return r.hedged_short_value == HedgedShortValue::exercise_price ? call_strike * n : stock_value(s);
}

}  // namespace

Money market_value(const OptionLeg& leg) { return leg.value * std::llabs(leg.units()); }

bool beyond_long_option_months(const Option& o, Date as_of, const RuleSet& r) {
    require(!as_of.empty() && as_of.day > 0, "the nine-month test needs a full as-of date");
    require(!o.expiry.empty() && o.expiry.day > 0, "the nine-month test needs a full expiration date");
    return o.expiry > add_months(as_of, r.long_option_months);
}

Money long_option(const OptionLeg& leg, const Market& m, const RuleSet& r) {
    require(leg.quantity > 0, "long_option needs a long leg");
    Money mv = market_value(leg);
    if (!beyond_long_option_months(leg.option, m.as_of, r)) return mv;
    if (leg.option.listing == Listing::listed) return r.long_option_beyond * mv;

    // OTC beyond nine months: 75% of the in-the-money amount plus 100% of the rest of the
    // value, if American-style. "OTC" already means guaranteed by the carrying
    // broker-dealer ((f)(2)(A)(xxvii)).
    if (leg.option.style != Style::american) return mv;
    std::int64_t u = leg.units();
    Money uv = m.underlying * u;
    Money aep = leg.option.strike * u;
    Money itm = positive_part(leg.option.type == OptionType::call ? uv - aep : aep - uv);
    itm = std::min(itm, mv);  // a quote below intrinsic must not make the time-value part negative
    return r.long_option_beyond * itm + (mv - itm);
}

Money uncovered_short(const OptionLeg& leg, const Market& m, const RuleSet& r) {
    require(leg.quantity < 0, "uncovered_short needs a short leg");
    if (leg.option.listing != Listing::listed)
        throw std::domain_error("uncovered OTC short options ((f)(2)(E)(iii)) are not implemented");
    const auto& rates = r.short_rates(leg.option.product);
    Rate pct = rates.percentage * leg.option.leverage;
    Rate min = rates.minimum * leg.option.leverage;

    std::int64_t u = -leg.units();
    Money mv = leg.value * u;
    Money uv = m.underlying * u;
    Money aep = leg.option.strike * u;
    bool call = leg.option.type == OptionType::call;
    Money otm = positive_part(call ? aep - uv : uv - aep);
    Money base = mv + pct * uv - otm;
    // The floor for puts is on the aggregate exercise price, for calls on the underlying value.
    Money floor = mv + min * (call ? uv : aep);
    return std::max(base, floor);
}

Requirement separate(const std::vector<OptionLeg>& legs, const Market& m, const RuleSet& r) {
    Requirement q;
    for (const auto& l : legs) {
        require(l.quantity != 0, "zero-quantity leg");
        if (l.quantity > 0) {
            q.options += long_option(l, m, r);
        } else {
            q.options += uncovered_short(l, m, r);
            q.proceeds += market_value(l);
        }
    }
    return q;
}

Requirement short_straddle(const OptionLeg& put, const OptionLeg& call, const Market& m, const RuleSet& r) {
    require(is_short(put, OptionType::put) && is_short(call, OptionType::call), "straddle needs a short put and short call");
    require_same_underlying(put, call);
    require(put.units() == call.units(), "straddle legs differ in share-equivalents");
    Money rp = uncovered_short(put, m, r);
    Money rc = uncovered_short(call, m, r);
    Requirement q;
    q.options = rp >= rc ? rp + market_value(call) : rc + market_value(put);
    q.proceeds = market_value(put) + market_value(call);
    return q;
}

Requirement stock(const StockLeg& s, const RuleSet& r) {
    require(s.shares != 0, "zero-quantity stock leg");
    Money mv = stock_value(s);
    Requirement q;
    if (s.shares > 0) {
        q.underlying = r.basis == Basis::initial ? r.stock_initial_long * mv : r.stock_maintenance_long * mv;
    } else {
        q.underlying = r.basis == Basis::initial ? r.stock_initial_short * mv : mv + short_stock_addon(s, r);
        q.proceeds = mv;
    }
    return q;
}

Requirement covered_call(const StockLeg& s, const OptionLeg& call, const Market&, const RuleSet& r) {
    require(is_short(call, OptionType::call), "covered_call needs a short call");
    require_cover(s, call, true);
    Requirement q;
    if (r.basis == Basis::initial) {
        q.underlying = r.stock_initial_long * stock_value(s);
    } else {
        // (f)(2)(I)(iii): the long stock is valued at no more than the call's exercise price.
        q.underlying = r.stock_maintenance_long * (std::min(s.price, call.option.strike) * s.shares);
    }
    q.proceeds = market_value(call);
    return q;
}

Requirement covered_put(const StockLeg& s, const OptionLeg& put, const Market&, const RuleSet& r) {
    require(is_short(put, OptionType::put), "covered_put needs a short put");
    require_cover(s, put, false);
    Requirement q = stock(s, r);
    // The manual adds the put's in-the-money amount to the maintenance requirement, and to
    // the initial one only when testing for excess Regulation T equity, not to the
    // requirement it reports.
    if (r.basis == Basis::maintenance) q.underlying += positive_part(put.option.strike - s.price) * -s.shares;
    q.proceeds += market_value(put);
    return q;
}

Requirement protective_put(const StockLeg& s, const OptionLeg& put, const Market&, const RuleSet& r) {
    require(is_long(put, OptionType::put), "protective_put needs a long put");
    require_cover(s, put, true);
    require_american(put);
    Requirement q = stock(s, r);
    if (r.basis == Basis::maintenance) {
        std::int64_t n = s.shares;
        Money hedged = r.hedge_exercise * (put.option.strike * n) + positive_part(s.price - put.option.strike) * n;
        q.underlying = std::min(hedged, q.underlying);
    }
    // An option in a hedge has no loan value (manual, note 6): paid in full.
    q.options = market_value(put);
    return q;
}

Requirement protective_call(const StockLeg& s, const OptionLeg& call, const Market&, const RuleSet& r) {
    require(is_long(call, OptionType::call), "protective_call needs a long call");
    require_cover(s, call, false);
    require_american(call);
    Requirement q = stock(s, r);
    if (r.basis == Basis::maintenance) {
        std::int64_t n = -s.shares;
        Money hedged = hedged_short_base(s, call.option.strike, r) + r.hedge_exercise * (call.option.strike * n) +
                       positive_part(call.option.strike - s.price) * n;
        q.underlying = std::min(hedged, q.underlying);
    }
    q.options = market_value(call);
    return q;
}

Requirement conversion(const StockLeg& s, const OptionLeg& call, const OptionLeg& put, const Market&,
                       const RuleSet& r) {
    require(is_short(call, OptionType::call) && is_long(put, OptionType::put), "conversion needs a short call and long put");
    require_cover(s, call, true);
    require_cover(s, put, true);
    require_same_underlying(call, put);
    require(call.option.strike == put.option.strike && call.option.expiry == put.option.expiry,
            "conversion needs the same exercise price and expiration");
    require_american(call);
    require_american(put);
    Requirement q = stock(s, r);
    if (r.basis == Basis::maintenance) q.underlying = r.hedge_exercise * (call.option.strike * s.shares);
    q.options = market_value(put);
    q.proceeds = market_value(call);
    return q;
}

Requirement reverse_conversion(const StockLeg& s, const OptionLeg& call, const OptionLeg& put, const Market&,
                               const RuleSet& r) {
    require(is_long(call, OptionType::call) && is_short(put, OptionType::put),
            "reverse conversion needs a long call and short put");
    require_cover(s, call, false);
    require_cover(s, put, false);
    require_same_underlying(call, put);
    require(call.option.strike == put.option.strike && call.option.expiry == put.option.expiry,
            "reverse conversion needs the same exercise price and expiration");
    require_american(call);
    require_american(put);
    Requirement q = stock(s, r);
    if (r.basis == Basis::maintenance) {
        std::int64_t n = -s.shares;
        q.underlying = hedged_short_base(s, call.option.strike, r) + r.hedge_exercise * (call.option.strike * n) +
                       positive_part(put.option.strike - s.price) * n;
    }
    q.options = market_value(call);
    q.proceeds += market_value(put);
    return q;
}

Requirement collar(const StockLeg& s, const OptionLeg& put, const OptionLeg& call, const Market&, const RuleSet& r) {
    require(is_long(put, OptionType::put) && is_short(call, OptionType::call), "collar needs a long put and short call");
    require_cover(s, put, true);
    require_cover(s, call, true);
    require_same_underlying(call, put);
    require(put.option.strike < call.option.strike, "collar needs the put strike below the call strike");
    require(put.option.expiry == call.option.expiry, "collar needs the same expiration");
    require_american(put);
    require_american(call);
    Requirement q = stock(s, r);
    if (r.basis == Basis::maintenance) {
        std::int64_t n = s.shares;
        Money put_side = r.hedge_exercise * (put.option.strike * n) + positive_part(s.price - put.option.strike) * n;
        Money call_side = r.collar_call * (call.option.strike * n);
        q.underlying = std::min(put_side, call_side);
    }
    q.options = market_value(put);
    q.proceeds = market_value(call);
    return q;
}

Requirement index_call_etf(const StockLeg& etf, const OptionLeg& call, const Market& index, const RuleSet& r) {
    require(is_short(call, OptionType::call), "index_call_etf needs a short call");
    require(call.option.product != ProductClass::equity, "index_call_etf needs an index option");
    require(etf.shares > 0, "index_call_etf needs a long ETF position");
    if (r.basis != Basis::initial) throw std::domain_error("index_call_etf maintenance is not implemented");
    require(stock_value(etf) >= index.underlying * -call.units(),
            "ETF value is below the aggregate current index value");
    Requirement q;
    q.underlying = r.stock_initial_long * stock_value(etf);
    q.proceeds = market_value(call);
    return q;
}

LongBox european_long_box(const std::vector<OptionLeg>& legs, const RuleSet& r) {
    require(legs.size() == 4, "a box has four legs");
    const OptionLeg *long_call = nullptr, *short_call = nullptr, *long_put = nullptr, *short_put = nullptr;
    for (const auto& l : legs) {
        require(l.option.style == Style::european, "the long box minimum needs European-style options");
        require(l.option.underlying == legs[0].option.underlying, "box legs have different underlyings");
        require(l.option.expiry == legs[0].option.expiry, "box legs expire at different times");
        require(l.option.listing == legs[0].option.listing, "box legs mix listed and OTC");
        require(l.option.deliverable == legs[0].option.deliverable, "box legs differ in contract size");
        require(std::llabs(l.quantity) == std::llabs(legs[0].quantity), "box legs differ in quantity");
        const OptionLeg** slot = l.option.type == OptionType::call ? (l.quantity > 0 ? &long_call : &short_call)
                                                                    : (l.quantity > 0 ? &long_put : &short_put);
        require(*slot == nullptr, "a box has one leg of each kind");
        *slot = &l;
    }
    // Buy side: long call and short put at one strike. Sell side: long put and short call
    // at a higher strike.
    require(long_call->option.strike == short_put->option.strike, "buy side strikes differ");
    require(long_put->option.strike == short_call->option.strike, "sell side strikes differ");
    require(long_put->option.strike > long_call->option.strike, "not a long box");

    Money diff = (long_put->option.strike - long_call->option.strike) * std::llabs(long_call->units());
    LongBox b;
    b.margin = r.long_box_margin * diff;
    b.value = r.long_box_value * diff;
    b.requirement.options = market_value(*long_call) + market_value(*long_put) + b.margin - b.value;
    b.requirement.proceeds = market_value(*short_call) + market_value(*short_put);
    return b;
}

}  // namespace pairing
