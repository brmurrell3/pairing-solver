#include "pairing/model.hpp"

#include <algorithm>
#include <charconv>
#include <fstream>
#include <initializer_list>
#include <sstream>
#include <stdexcept>

#include <toml++/toml.hpp>

namespace pairing {

namespace {

int parse_int(std::string_view s, std::string_view whole) {
    int v = 0;
    auto [p, ec] = std::from_chars(s.data(), s.data() + s.size(), v);
    if (ec != std::errc() || p != s.data() + s.size()) throw std::invalid_argument("bad date: " + std::string(whole));
    return v;
}

int days_in_month(int year, int month) {
    static constexpr int days[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    bool leap = (year % 4 == 0 && year % 100 != 0) || year % 400 == 0;
    return month == 2 && leap ? 29 : days[month - 1];
}

void check_keys(const toml::table& t, std::initializer_list<std::string_view> known, std::string_view where) {
    for (auto&& [key, node] : t) {
        bool ok = false;
        for (auto k : known) ok = ok || key.str() == k;
        if (!ok) throw std::invalid_argument("unknown rule key: " + std::string(where) + std::string(key.str()));
    }
}

const toml::table* subtable(const toml::table& t, std::string_view key) {
    const toml::node* n = t.get(key);
    if (!n) return nullptr;
    if (!n->is_table()) throw std::invalid_argument("rule key must be a table: " + std::string(key));
    return n->as_table();
}

void read(const toml::table& t, std::string_view key, Rate& out) {
    const toml::node* n = t.get(key);
    if (!n) return;
    auto v = n->value<double>();
    if (!v || n->is_boolean()) throw std::invalid_argument("rule key must be a number: " + std::string(key));
    out = Rate::from_double(*v);
}

void read(const toml::table& t, std::string_view key, Money& out) {
    const toml::node* n = t.get(key);
    if (!n) return;
    auto v = n->value<double>();
    if (!v || n->is_boolean()) throw std::invalid_argument("rule key must be a number: " + std::string(key));
    out = Money::dollars(*v);
}

void read(const toml::table& t, std::string_view key, int& out) {
    const toml::node* n = t.get(key);
    if (!n) return;
    if (!n->is_integer()) throw std::invalid_argument("rule key must be an integer: " + std::string(key));
    out = static_cast<int>(*n->value<std::int64_t>());
}

template <class E>
void read(const toml::table& t, std::string_view key, E& out, std::initializer_list<std::pair<std::string_view, E>> names) {
    const toml::node* n = t.get(key);
    if (!n) return;
    auto s = n->value<std::string>();
    if (!s) throw std::invalid_argument("rule key must be a string: " + std::string(key));
    for (auto& [name, value] : names) {
        if (*s == name) {
            out = value;
            return;
        }
    }
    throw std::invalid_argument("unknown value for " + std::string(key) + ": " + *s);
}

}  // namespace

Date Date::parse(std::string_view s) {
    Date d;
    if (s.size() != 7 && s.size() != 10) throw std::invalid_argument("bad date: " + std::string(s));
    if (s[4] != '-' || (s.size() == 10 && s[7] != '-')) throw std::invalid_argument("bad date: " + std::string(s));
    d.year = parse_int(s.substr(0, 4), s);
    d.month = parse_int(s.substr(5, 2), s);
    if (d.month < 1 || d.month > 12) throw std::invalid_argument("bad date: " + std::string(s));
    if (s.size() == 10) {
        d.day = parse_int(s.substr(8, 2), s);
        if (d.day < 1 || d.day > days_in_month(d.year, d.month)) throw std::invalid_argument("bad date: " + std::string(s));
    }
    return d;
}

Date add_months(Date d, int months) {
    int m = d.year * 12 + (d.month - 1) + months;
    Date out{m / 12, m % 12 + 1, d.day};
    if (out.day > 0) out.day = std::min(out.day, days_in_month(out.year, out.month));
    return out;
}

RuleSet parse_rules(std::string_view text) {
    toml::table t = toml::parse(text);
    RuleSet r;
    check_keys(t, {"basis", "expiry_rule", "european_calendars", "hedged_short_value", "short_option", "long_option",
                   "stock", "hedge", "long_box"},
               "");

    read(t, "basis", r.basis, {{"initial", Basis::initial}, {"maintenance", Basis::maintenance}});
    read(t, "expiry_rule", r.expiry_rule,
         {{"pairwise", ExpiryRule::pairwise},
          {"nearest_long", ExpiryRule::nearest_long},
          {"same_expiry", ExpiryRule::same_expiry}});
    read(t, "european_calendars", r.european_calendars,
         {{"allowed", EuropeanCalendars::allowed}, {"disallowed", EuropeanCalendars::disallowed}});
    read(t, "hedged_short_value", r.hedged_short_value,
         {{"exercise_price", HedgedShortValue::exercise_price}, {"market_value", HedgedShortValue::market_value}});

    if (auto s = subtable(t, "short_option")) {
        check_keys(*s, {"equity", "narrow_index", "broad_index"}, "short_option.");
        const std::pair<std::string_view, ProductClass> classes[] = {{"equity", ProductClass::equity},
                                                                     {"narrow_index", ProductClass::narrow_index},
                                                                     {"broad_index", ProductClass::broad_index}};
        for (auto& [name, cls] : classes) {
            if (auto c = subtable(*s, name)) {
                check_keys(*c, {"percentage", "minimum"}, "short_option." + std::string(name) + ".");
                auto& rates = r.short_option[static_cast<int>(cls)];
                read(*c, "percentage", rates.percentage);
                read(*c, "minimum", rates.minimum);
            }
        }
    }
    if (auto s = subtable(t, "long_option")) {
        check_keys(*s, {"months", "beyond_months"}, "long_option.");
        read(*s, "months", r.long_option_months);
        read(*s, "beyond_months", r.long_option_beyond);
    }
    if (auto s = subtable(t, "stock")) {
        check_keys(*s,
                   {"initial_long", "initial_short", "maintenance_long", "short_low_price", "short_low_per_share",
                    "short_low_percentage", "short_per_share", "short_percentage"},
                   "stock.");
        read(*s, "initial_long", r.stock_initial_long);
        read(*s, "initial_short", r.stock_initial_short);
        read(*s, "maintenance_long", r.stock_maintenance_long);
        read(*s, "short_low_price", r.short_low_price);
        read(*s, "short_low_per_share", r.short_low_per_share);
        read(*s, "short_low_percentage", r.short_low_percentage);
        read(*s, "short_per_share", r.short_per_share);
        read(*s, "short_percentage", r.short_percentage);
    }
    if (auto s = subtable(t, "hedge")) {
        check_keys(*s, {"exercise_percentage", "collar_call_percentage"}, "hedge.");
        read(*s, "exercise_percentage", r.hedge_exercise);
        read(*s, "collar_call_percentage", r.collar_call);
    }
    if (auto s = subtable(t, "long_box")) {
        check_keys(*s, {"margin_percentage", "value_percentage"}, "long_box.");
        read(*s, "margin_percentage", r.long_box_margin);
        read(*s, "value_percentage", r.long_box_value);
    }
    return r;
}

RuleSet load_rules(const std::string& path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open rule set: " + path);
    std::stringstream ss;
    ss << in.rdbuf();
    return parse_rules(ss.str());
}

}  // namespace pairing
