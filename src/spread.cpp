#include <algorithm>
#include <iterator>
#include <map>
#include <set>
#include <stdexcept>

#include "pairing/margin.hpp"

namespace pairing {

namespace {

bool balanced(const std::vector<OptionLeg>& legs, OptionType t) {
    std::int64_t net = 0;
    for (const auto& l : legs)
        if (l.option.type == t) net += l.units();
    return net == 0;
}

Validity fail(std::string reason) { return Validity{false, std::move(reason)}; }

const char* type_name(OptionType t) { return t == OptionType::call ? "calls" : "puts"; }

}  // namespace

std::vector<StrikeValue> strike_walk(const std::vector<OptionLeg>& legs) {
    if (!balanced(legs, OptionType::call) || !balanced(legs, OptionType::put))
        throw std::invalid_argument("strike walk needs legs balanced within calls and within puts");

    // Signed units at each strike, calls and puts together, and Q_0 = sum of put units × strike.
    std::map<Money, std::int64_t> at;
    Money v;
    for (const auto& l : legs) {
        at[l.option.strike] += l.units();
        if (l.option.type == OptionType::put) v += l.option.strike * l.units();
    }

    // Payoff at K_1 is Q_0; between strikes the slope is the running unit count D_j.
    std::vector<StrikeValue> out;
    std::int64_t d = 0;
    for (auto it = at.begin(); it != at.end(); ++it) {
        if (it != at.begin()) v += (it->first - std::prev(it)->first) * d;
        out.push_back({it->first, v});
        d += it->second;
    }
    return out;
}

Money payoff_at(const std::vector<OptionLeg>& legs, Money price) {
    Money total;
    for (const auto& l : legs) {
        Money intrinsic = l.option.type == OptionType::call ? price - l.option.strike : l.option.strike - price;
        total += std::max(intrinsic, Money{}) * l.units();
    }
    return total;
}

Money max_potential_loss(const std::vector<OptionLeg>& legs) {
    Money worst;
    for (const auto& sv : strike_walk(legs)) worst = std::min(worst, sv.value);
    return -worst;
}

Validity spread_validity(const std::vector<OptionLeg>& legs, const RuleSet& r) {
    if (legs.empty()) return fail("no legs");
    const Option& first = legs.front().option;
    for (const auto& l : legs) {
        if (l.quantity == 0) return fail("zero-quantity leg");
        if (l.option.underlying != first.underlying) return fail("different underlyings");
        if (l.option.style != first.style) return fail("mixed exercise styles");
        if (l.option.listing != first.listing) return fail("mixed listed and OTC");
    }
    for (OptionType t : {OptionType::call, OptionType::put})
        if (!balanced(legs, t)) return fail(std::string(type_name(t)) + " not balanced in share-equivalents");

    std::set<Date> expiries;
    for (const auto& l : legs) expiries.insert(l.option.expiry);
    if (first.style == Style::european && expiries.size() > 1 &&
        r.european_calendars == EuropeanCalendars::disallowed)
        return fail("European-style calendar spreads are disallowed");

    switch (r.expiry_rule) {
        case ExpiryRule::pairwise:
            // The longs that may pair with a short are those expiring on or after it, so the
            // candidate sets are nested and Hall's condition reduces to suffixes: for every
            // date d, short units expiring on or after d must not exceed long units doing so.
            for (OptionType t : {OptionType::call, OptionType::put}) {
                for (Date d : expiries) {
                    std::int64_t shorts = 0, longs = 0;
                    for (const auto& l : legs) {
                        if (l.option.type != t || l.option.expiry < d) continue;
                        (l.quantity < 0 ? shorts : longs) += std::llabs(l.units());
                    }
                    if (shorts > longs) return fail(std::string("short ") + type_name(t) + " outlast their longs");
                }
            }
            break;
        case ExpiryRule::nearest_long: {
            Date last_short{}, first_long{9999, 12, 31};
            for (const auto& l : legs) {
                if (l.quantity < 0) last_short = std::max(last_short, l.option.expiry);
                else first_long = std::min(first_long, l.option.expiry);
            }
            if (last_short > first_long) return fail("a short expires after the nearest long");
            break;
        }
        case ExpiryRule::same_expiry:
            if (expiries.size() > 1) return fail("legs expire on different dates");
            break;
    }
    return Validity{};
}

Spread spread(const std::vector<OptionLeg>& legs, const Market& m, const RuleSet& r) {
    if (auto v = spread_validity(legs, r); !v) throw std::invalid_argument("not a valid spread: " + v.reason);
    Spread s;
    s.max_loss = max_potential_loss(legs);
    Money long_cost;
    for (const auto& l : legs) {
        if (l.quantity > 0) {
            long_cost += market_value(l);
        } else {
            s.short_uncovered += uncovered_short(l, m, r);
            s.requirement.proceeds += market_value(l);
        }
    }
    s.requirement.options = std::min(s.short_uncovered, s.max_loss) + long_cost;
    return s;
}

}  // namespace pairing
