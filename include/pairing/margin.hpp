#pragma once

#include <string>
#include <vector>

#include "pairing/model.hpp"

namespace pairing {

// Conventions, matching the Cboe manual's "Margin Requirement" and "SMA Debit or Margin
// Call" lines:
// - a short option's requirement includes 100% of its market value ((f)(2)(E));
// - a short stock requirement includes 100% of its market value (150% initial);
// - long options are counted at cost when they must be paid for in full;
// - proceeds are the short legs at market value, which may be applied, so
//   margin_call = total - proceeds.
struct Requirement {
    Money underlying;  // on the stock or ETF leg
    Money options;     // on the option legs
    Money proceeds;

    Money total() const { return underlying + options; }
    Money margin_call() const { return total() - proceeds; }
};

// |units| × value.
Money market_value(const OptionLeg& leg);

// Remaining time to expiration exceeds the rule set's month count (nine by default).
bool beyond_long_option_months(const Option& o, Date as_of, const RuleSet& r);

// R4. Throws on a short leg.
Money long_option(const OptionLeg& leg, const Market& m, const RuleSet& r);

// R3, listed options only; (f)(2)(E)(iii) for OTC shorts is not implemented and throws.
Money uncovered_short(const OptionLeg& leg, const Market& m, const RuleSet& r);

// R5: every leg on its own.
Requirement separate(const std::vector<OptionLeg>& legs, const Market& m, const RuleSet& r);

// R6. Equal share-equivalents, same underlying, both listed.
Requirement short_straddle(const OptionLeg& put, const OptionLeg& call, const Market& m, const RuleSet& r);

// R9. Initial: Regulation T. Maintenance: 4210(c).
Requirement stock(const StockLeg& s, const RuleSet& r);

// R7 and R8. The stock leg must cover exactly the option's share-equivalents, the
// options must share the underlying, and the R8 structures need American-style options.
// Initial basis: stock on Regulation T, long options paid in full, covered shorts free.
// Maintenance basis: the R8 minimum on the stock leg; options as for initial.
Requirement covered_call(const StockLeg& stock, const OptionLeg& short_call, const Market& m, const RuleSet& r);
Requirement covered_put(const StockLeg& stock, const OptionLeg& short_put, const Market& m, const RuleSet& r);
Requirement protective_put(const StockLeg& stock, const OptionLeg& long_put, const Market& m, const RuleSet& r);
Requirement protective_call(const StockLeg& stock, const OptionLeg& long_call, const Market& m, const RuleSet& r);
Requirement conversion(const StockLeg& stock, const OptionLeg& short_call, const OptionLeg& long_put, const Market& m,
                       const RuleSet& r);
Requirement reverse_conversion(const StockLeg& stock, const OptionLeg& long_call, const OptionLeg& short_put,
                               const Market& m, const RuleSet& r);
Requirement collar(const StockLeg& stock, const OptionLeg& long_put, const OptionLeg& short_call, const Market& m,
                   const RuleSet& r);

// Short index call against a long ETF on the same index (Cboe manual, "Short Index Call
// and Long ETF"). Initial basis only: the manual's maintenance treatment and FINRA
// (f)(2)(H)(v)f differ, and neither has a worked example.
Requirement index_call_etf(const StockLeg& etf, const OptionLeg& short_call, const Market& index, const RuleSet& r);

// R2b. A European-style long box: 50% of the aggregate strike difference, with the box
// valued at up to 100% of that difference. requirement.options counts the longs at cost
// less that value plus the margin, so requirement.margin_call() is the manual's figure
// and requirement.total() compares directly with the spread treatment of the same legs.
struct LongBox {
    Money margin;  // the manual's "Margin Requirement"
    Money value;
    Requirement requirement;
};
LongBox european_long_box(const std::vector<OptionLeg>& legs, const RuleSet& r);

// Spreads (R1, R2).

struct StrikeValue {
    Money strike;
    Money value;
};

// Netted intrinsic value at every distinct strike, by the strike walk of spec §3.1 item 5.
// The legs must balance within calls and within puts; otherwise this throws.
std::vector<StrikeValue> strike_walk(const std::vector<OptionLeg>& legs);

// Netted intrinsic value at one underlying price, evaluated leg by leg.
Money payoff_at(const std::vector<OptionLeg>& legs, Money price);

// The largest netted loss at the strikes, or zero.
Money max_potential_loss(const std::vector<OptionLeg>& legs);

struct Validity {
    bool ok = true;
    std::string reason;
    explicit operator bool() const { return ok; }
};

// R1 a–e under r.expiry_rule and r.european_calendars. For pairwise, condition e is the
// suffix condition of spec §3.1 item 4.
Validity spread_validity(const std::vector<OptionLeg>& legs, const RuleSet& r);

struct Spread {
    Money max_loss;
    Money short_uncovered;  // sum of R3 over the shorts
    Requirement requirement;
};

// R2: lesser of the shorts' uncovered requirement and the maximum loss, plus the longs
// paid in full. Longs beyond nine months are paid in full too: the manual's
// reduced-value put and call spread examples charge them 100% (rules.md Q3).
// Throws if the legs are not a valid spread.
Spread spread(const std::vector<OptionLeg>& legs, const Market& m, const RuleSet& r);

}  // namespace pairing
