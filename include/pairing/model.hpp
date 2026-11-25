#pragma once

#include <array>
#include <cstdint>
#include <string>
#include <string_view>

#include "pairing/money.hpp"

namespace pairing {

struct Date {
    int year = 0;
    int month = 0;
    int day = 0;  // 0: known to the month only; sorts before every day of that month

    // "YYYY-MM" or "YYYY-MM-DD".
    static Date parse(std::string_view s);
    bool empty() const { return year == 0; }
    constexpr auto operator<=>(const Date&) const = default;
};

// Same day of the month, clamped to the month's last day.
Date add_months(Date d, int months);

enum class ProductClass { equity, narrow_index, broad_index };  // equity covers stock, ETF and ETN
enum class OptionType { call, put };
enum class Style { american, european };
enum class Listing { listed, otc };

// Strike, underlying price and option value are all per unit of the underlying as the
// deliverable counts it. A reduced-value index option is therefore expressed in units of
// the full index: an XSP 45 strike is an SPX 450 strike with a deliverable of 10, which is
// what lets it balance against SPX contracts (rules.md U2, U3).
struct Option {
    std::string underlying;
    ProductClass product = ProductClass::equity;
    OptionType type = OptionType::call;
    Money strike;
    Date expiry;
    Style style = Style::american;
    Listing listing = Listing::listed;
    std::int64_t deliverable = 100;  // w_i: shares, or the index multiplier
    Rate leverage = percent(100);    // leveraged ETF factor; scales the short-option rates (Cboe RG09-97)
};

struct OptionLeg {
    Option option;
    std::int64_t quantity = 0;  // contracts; positive long, negative short
    Money value;                // current market value per underlying unit

    // Signed share-equivalents, w_i × contracts.
    std::int64_t units() const { return quantity * option.deliverable; }
};

struct StockLeg {
    std::int64_t shares = 0;  // positive long, negative short
    Money price;
};

struct Market {
    Money underlying;  // price of the options' underlying
    Date as_of;        // needed only for the nine-month test on long options
};

enum class Basis { initial, maintenance };
enum class ExpiryRule { pairwise, nearest_long, same_expiry };
enum class EuropeanCalendars { allowed, disallowed };
// How the manual's hedged short-stock examples value the short leg; see RuleSet.
enum class HedgedShortValue { exercise_price, market_value };

struct ShortOptionRates {
    Rate percentage;
    Rate minimum;
    bool operator==(const ShortOptionRates&) const = default;
};

// Rates, minimums and policies. Defaults follow docs/rules.md; data/rules/default.toml
// spells out the same values.
struct RuleSet {
    Basis basis = Basis::maintenance;
    ExpiryRule expiry_rule = ExpiryRule::pairwise;
    EuropeanCalendars european_calendars = EuropeanCalendars::allowed;
    // For long call / short stock and reverse conversions, the Cboe manual's worked numbers
    // carry the short stock at 100% of the call exercise price, not its market value. The
    // FINRA text alone reads as market value. Default reproduces the manual.
    HedgedShortValue hedged_short_value = HedgedShortValue::exercise_price;

    // R3, indexed by ProductClass.
    std::array<ShortOptionRates, 3> short_option{{
        {percent(20), percent(10)},
        {percent(20), percent(10)},
        {percent(15), percent(10)},
    }};

    // R4.
    int long_option_months = 9;
    Rate long_option_beyond = percent(75);

    // R9: Regulation T initial; 4210(c) maintenance.
    Rate stock_initial_long = percent(50);
    Rate stock_initial_short = percent(150);
    Rate stock_maintenance_long = percent(25);
    Money short_low_price = Money::from_micros(5'000'000);
    Money short_low_per_share = Money::from_micros(2'500'000);
    Rate short_low_percentage = percent(100);
    Money short_per_share = Money::from_micros(5'000'000);
    Rate short_percentage = percent(30);

    // R8.
    Rate hedge_exercise = percent(10);
    Rate collar_call = percent(25);

    // R2b.
    Rate long_box_margin = percent(50);
    Rate long_box_value = percent(100);

    const ShortOptionRates& short_rates(ProductClass p) const { return short_option[static_cast<int>(p)]; }
    bool operator==(const RuleSet&) const = default;
};

// Keys absent from the file keep their defaults; unknown keys are errors.
RuleSet parse_rules(std::string_view toml_text);
RuleSet load_rules(const std::string& path);

}  // namespace pairing
