#include <algorithm>
#include <random>
#include <string>
#include <vector>

#include "check.hpp"
#include "pairing/margin.hpp"

#ifndef PAIRING_DATA_DIR
#error "PAIRING_DATA_DIR must point at the repository's data directory"
#endif

using namespace pairing;

namespace {

Money usd(double d) { return Money::dollars(d); }

OptionLeg leg(OptionType t, std::int64_t qty, double strike, Date expiry, double value = 0, std::int64_t w = 100) {
    OptionLeg l;
    l.option.underlying = "XYZ";
    l.option.type = t;
    l.option.strike = usd(strike);
    l.option.expiry = expiry;
    l.option.deliverable = w;
    l.quantity = qty;
    l.value = usd(value);
    return l;
}

void money_arithmetic() {
    CHECK_EQ(usd(433.35).micros(), 433'350'000);
    CHECK_EQ(usd(-0.1).str(), std::string("-0.10"));
    CHECK_EQ(Money::from_micros(1'234'567).str(), std::string("1.234567"));
    CHECK_EQ((percent(15) * (usd(433.35) * 100)).str(), std::string("6500.25"));
    // Half a micro-dollar rounds away from zero.
    CHECK_EQ((percent(50) * Money::from_micros(1)).micros(), 1);
    CHECK_EQ((percent(50) * Money::from_micros(-1)).micros(), -1);
    CHECK_EQ(percent(15) * Rate::from_double(1.5), Rate{225'000});
    CHECK_THROWS(usd(1e12) * std::int64_t{100'000'000});
}

void dates() {
    CHECK(Date::parse("2021-06") < Date::parse("2021-06-01"));
    CHECK_THROWS(Date::parse("2021-13-01"));
    CHECK_THROWS(Date::parse("2021-02-29"));
    CHECK(add_months(Date::parse("2021-08-31"), 6) == Date::parse("2022-02-28"));
    CHECK(add_months(Date::parse("2021-11-15"), 14) == Date::parse("2023-01-15"));

    RuleSet r;
    Option o;
    o.expiry = Date::parse("2021-10-15");
    CHECK(!beyond_long_option_months(o, Date::parse("2021-01-15"), r));  // exactly nine months
    o.expiry = Date::parse("2021-10-16");
    CHECK(beyond_long_option_months(o, Date::parse("2021-01-15"), r));
}

// Random portfolios balanced within calls and within puts, built from long/short pairs of
// equal share-equivalents, sometimes across 100- and 10-unit deliverables.
std::vector<OptionLeg> random_balanced(std::mt19937_64& rng, int pairs, int expiries) {
    std::uniform_int_distribution<int> strike(8, 16), qty(1, 5), coin(0, 1), exp(1, expiries);
    std::vector<OptionLeg> legs;
    for (int i = 0; i < pairs; ++i) {
        OptionType t = coin(rng) ? OptionType::call : OptionType::put;
        int q = qty(rng);
        Date e1{2021, exp(rng), 15}, e2{2021, exp(rng), 15};
        legs.push_back(leg(t, q, 5.0 * strike(rng), e1));
        if (coin(rng)) legs.push_back(leg(t, -q, 5.0 * strike(rng), e2));
        else legs.push_back(leg(t, -10 * q, 5.0 * strike(rng), e2, 0, 10));
    }
    return legs;
}

// Spec §3.1 items 1 and 5: the walk equals leg-by-leg evaluation at every strike, and no
// price between or beyond the strikes has a lower netted value.
void strike_walk_matches_direct() {
    std::mt19937_64 rng(20261125);
    for (int trial = 0; trial < 2000; ++trial) {
        auto legs = random_balanced(rng, 1 + trial % 4, 4);
        auto walk = strike_walk(legs);
        Money lowest = walk.front().value;
        for (const auto& sv : walk) {
            CHECK_EQ(payoff_at(legs, sv.strike), sv.value);
            lowest = std::min(lowest, sv.value);
        }
        for (double p = 0; p <= 100; p += 0.25) CHECK(payoff_at(legs, usd(p)) >= lowest);
    }
    std::vector<OptionLeg> unbalanced = {leg(OptionType::call, 1, 50, Date{2021, 1, 15})};
    CHECK_THROWS(strike_walk(unbalanced));
}

// Maximum flow from shorts to the same-type longs expiring on or after them, in
// share-equivalents. Small dense Edmonds-Karp; independent of the suffix condition.
bool pairing_exists(const std::vector<OptionLeg>& legs) {
    int n = static_cast<int>(legs.size()) + 2, src = n - 2, sink = n - 1;
    std::vector<std::vector<std::int64_t>> cap(n, std::vector<std::int64_t>(n, 0));
    std::int64_t need = 0;
    for (int i = 0; i < static_cast<int>(legs.size()); ++i) {
        const auto& a = legs[i];
        if (a.quantity < 0) {
            cap[src][i] = -a.units();
            need += -a.units();
            for (int j = 0; j < static_cast<int>(legs.size()); ++j) {
                const auto& b = legs[j];
                if (b.quantity > 0 && b.option.type == a.option.type && b.option.expiry >= a.option.expiry)
                    cap[i][j] = need + 1'000'000;
            }
        } else {
            cap[i][sink] = a.units();
        }
    }
    std::int64_t flow = 0;
    for (;;) {
        std::vector<int> prev(n, -1);
        prev[src] = src;
        std::vector<int> queue = {src};
        for (std::size_t h = 0; h < queue.size() && prev[sink] < 0; ++h)
            for (int v = 0; v < n; ++v)
                if (prev[v] < 0 && cap[queue[h]][v] > 0) {
                    prev[v] = queue[h];
                    queue.push_back(v);
                }
        if (prev[sink] < 0) break;
        std::int64_t push = INT64_MAX;
        for (int v = sink; v != src; v = prev[v]) push = std::min(push, cap[prev[v]][v]);
        for (int v = sink; v != src; v = prev[v]) {
            cap[prev[v]][v] -= push;
            cap[v][prev[v]] += push;
        }
        flow += push;
    }
    return flow == need;
}

// Spec §3.1 item 4: on balanced groups, the suffix condition agrees with maximum flow.
void suffix_condition_matches_flow() {
    std::mt19937_64 rng(4210);
    RuleSet r;
    int feasible = 0, infeasible = 0;
    for (int trial = 0; trial < 3000; ++trial) {
        auto legs = random_balanced(rng, 1 + trial % 4, 4);
        bool flow = pairing_exists(legs);
        CHECK_EQ(static_cast<bool>(spread_validity(legs, r)), flow);
        (flow ? feasible : infeasible)++;
    }
    // Both outcomes must actually be exercised.
    CHECK(feasible > 100);
    CHECK(infeasible > 100);
}

void validity_policies() {
    RuleSet r;
    Date mar{2021, 3, 19}, jun{2021, 6, 18};
    // A calendar: short March, long June. Valid pairwise and nearest_long, not same_expiry.
    std::vector<OptionLeg> cal = {leg(OptionType::call, -1, 50, mar), leg(OptionType::call, 1, 50, jun)};
    CHECK(static_cast<bool>(spread_validity(cal, r)));
    r.expiry_rule = ExpiryRule::same_expiry;
    CHECK(!spread_validity(cal, r));
    r.expiry_rule = ExpiryRule::pairwise;
    for (auto& l : cal) l.option.style = Style::european;
    CHECK(static_cast<bool>(spread_validity(cal, r)));
    r.european_calendars = EuropeanCalendars::disallowed;
    CHECK(!spread_validity(cal, r));

    std::vector<OptionLeg> mixed = {leg(OptionType::call, -1, 50, mar), leg(OptionType::call, 1, 55, mar)};
    mixed[1].option.listing = Listing::otc;
    CHECK(!spread_validity(mixed, RuleSet{}));
    mixed[1].option.listing = Listing::listed;
    mixed[1].option.underlying = "ABC";
    CHECK(!spread_validity(mixed, RuleSet{}));

    Market m{usd(50), Date{2021, 1, 15}};
    std::vector<OptionLeg> backwards = {leg(OptionType::call, -1, 50, jun, 2), leg(OptionType::call, 1, 55, mar, 1)};
    CHECK_THROWS(spread(backwards, m, RuleSet{}));
}

// The FINRA-literal reading of the short-side hedges, for comparison with the manual's
// worked numbers (5,900; 12,100; 8,560) that the default reproduces.
void hedged_short_value_policy() {
    RuleSet r;
    r.hedged_short_value = HedgedShortValue::market_value;
    Market m;
    Date dec{2021, 12, 17};
    StockLeg s46{-100, usd(46)};
    CHECK_EQ(protective_call(s46, leg(OptionType::call, 1, 50, dec), m, r).underlying, usd(5500));
    StockLeg s115{-100, usd(115)};
    CHECK_EQ(reverse_conversion(s115, leg(OptionType::call, 1, 110, dec), leg(OptionType::put, -1, 110, dec), m, r)
                 .underlying,
             usd(12600));
    StockLeg s7190{-100, usd(71.90)};
    CHECK_EQ(reverse_conversion(s7190, leg(OptionType::call, 1, 75, dec), leg(OptionType::put, -1, 75, dec), m, r)
                 .underlying,
             usd(8250));
}

void stock_requirements() {
    RuleSet r;
    CHECK_EQ(stock({100, usd(40)}, r).underlying, usd(1000));
    CHECK_EQ(stock({-100, usd(40)}, r).underlying, usd(5200));  // 4,000 + 30%
    CHECK_EQ(stock({-100, usd(10)}, r).underlying, usd(1500));  // 1,000 + $5 a share
    CHECK_EQ(stock({-100, usd(2)}, r).underlying, usd(450));    // 200 + $2.50 a share
    CHECK_EQ(stock({-100, usd(4)}, r).underlying, usd(800));    // 400 + 100%
    r.basis = Basis::initial;
    CHECK_EQ(stock({100, usd(40)}, r).underlying, usd(2000));
    CHECK_EQ(stock({-100, usd(40)}, r).underlying, usd(6000));
    CHECK_EQ(stock({-100, usd(40)}, r).proceeds, usd(4000));
}

void covered_call_maintenance_uses_strike() {
    // (f)(2)(I)(iii): stock at 92.38 against a 90 call is valued at 90.
    RuleSet r;
    StockLeg s{100, usd(92.38)};
    CHECK_EQ(covered_call(s, leg(OptionType::call, -1, 90, Date{2021, 12, 17}, 7), Market{}, r).underlying, usd(2250));
    CHECK_THROWS(covered_call(StockLeg{50, usd(92.38)}, leg(OptionType::call, -1, 90, Date{2021, 12, 17}), Market{}, r));
}

void otc_short_not_implemented() {
    auto l = leg(OptionType::put, -1, 50, Date{2021, 12, 17}, 1);
    l.option.listing = Listing::otc;
    CHECK_THROWS(uncovered_short(l, Market{usd(50), {}}, RuleSet{}));
}

void rule_files() {
    RuleSet defaults;
    CHECK(load_rules(std::string(PAIRING_DATA_DIR) + "/rules/default.toml") == defaults);

    RuleSet r = parse_rules(R"(
        basis = "initial"
        expiry_rule = "nearest_long"
        [short_option.broad_index]
        percentage = 0.18
        [stock]
        short_per_share = 6
    )");
    CHECK(r.basis == Basis::initial);
    CHECK(r.expiry_rule == ExpiryRule::nearest_long);
    CHECK_EQ(r.short_rates(ProductClass::broad_index).percentage, Rate{180'000});
    CHECK_EQ(r.short_rates(ProductClass::broad_index).minimum, percent(10));
    CHECK_EQ(r.short_per_share, usd(6));
    CHECK_EQ(r.stock_maintenance_long, percent(25));

    CHECK_THROWS(parse_rules("expiry_rule = \"loose\""));
    CHECK_THROWS(parse_rules("[stock]\nmaintenance_lng = 0.3"));
    CHECK_THROWS(parse_rules("[hedge]\nexercise_percentage = \"ten\""));
}

}  // namespace

int run_unit_tests() {
    int groups = 0;
    auto run = [&](const char* name, void (*f)()) {
        ::check::context() = name;
        f();
        ++groups;
    };
    run("money", money_arithmetic);
    run("dates", dates);
    run("strike_walk", strike_walk_matches_direct);
    run("suffix_condition", suffix_condition_matches_flow);
    run("validity_policies", validity_policies);
    run("hedged_short_value", hedged_short_value_policy);
    run("stock", stock_requirements);
    run("covered_call", covered_call_maintenance_uses_strike);
    run("otc_short", otc_short_not_implemented);
    run("rules", rule_files);
    ::check::context().clear();
    return groups;
}
