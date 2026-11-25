// Runs the worked examples in data/fixtures/*.toml through the engine.
//
// Case fields (see the fixture headers for the meaning of each):
//   kind      spread (default), long_option, short_option, straddle, covered_call,
//             covered_put, protective_put, protective_call, conversion,
//             reverse_conversion, collar, index_call_etf, european_long_box
//   basis, product, style, listing, leverage, multiplier, underlying, as_of
//   legs      side, qty, type (call, put, stock), expiry, strike, premium, price, reduced
//   expected  netted, max_loss, valid, requirement, underlying_requirement,
//             short_proceeds, margin_call, box_margin

#include <initializer_list>
#include <stdexcept>
#include <string>
#include <vector>

#include <toml++/toml.hpp>

#include "check.hpp"
#include "pairing/margin.hpp"

using namespace pairing;

namespace {

void check_keys(const toml::table& t, std::initializer_list<std::string_view> known) {
    for (auto&& [key, node] : t) {
        bool ok = false;
        for (auto k : known) ok = ok || key.str() == k;
        if (!ok) throw std::invalid_argument("unknown fixture key: " + std::string(key.str()));
    }
}

std::string str(const toml::table& t, std::string_view key, std::string fallback = "") {
    return t[key].value_or(fallback);
}

Money money(const toml::node& n) {
    auto v = n.value<double>();
    if (!v) throw std::invalid_argument("expected a number");
    return Money::dollars(*v);
}

Money money(const toml::table& t, std::string_view key) {
    const toml::node* n = t.get(key);
    if (!n) throw std::invalid_argument("missing key: " + std::string(key));
    return money(*n);
}

template <class E>
E pick(const std::string& s, std::initializer_list<std::pair<std::string_view, E>> names) {
    for (auto& [name, value] : names)
        if (s == name) return value;
    throw std::invalid_argument("unknown value: " + s);
}

struct Case {
    std::string kind;
    RuleSet rules;
    Market market;
    std::vector<OptionLeg> options;
    std::vector<StockLeg> stocks;
};

Case load_case(const toml::table& c) {
    check_keys(c, {"id", "section", "kind", "basis", "product", "style", "listing", "leverage", "multiplier",
                   "underlying", "as_of", "legs", "netted", "max_loss", "valid", "requirement",
                   "underlying_requirement", "short_proceeds", "margin_call", "box_margin"});
    Case k;
    k.kind = str(c, "kind", "spread");
    k.rules.basis = pick<Basis>(str(c, "basis", "maintenance"),
                                {{"initial", Basis::initial}, {"maintenance", Basis::maintenance}});
    if (c.contains("underlying")) k.market.underlying = money(c, "underlying");
    if (c.contains("as_of")) k.market.as_of = Date::parse(str(c, "as_of"));

    Option base;
    base.underlying = "XYZ";
    base.product = pick<ProductClass>(str(c, "product", "equity"), {{"equity", ProductClass::equity},
                                                                     {"narrow_index", ProductClass::narrow_index},
                                                                     {"broad_index", ProductClass::broad_index}});
    base.style = pick<Style>(str(c, "style", "american"), {{"american", Style::american}, {"european", Style::european}});
    base.listing = pick<Listing>(str(c, "listing", "listed"), {{"listed", Listing::listed}, {"otc", Listing::otc}});
    base.deliverable = c["multiplier"].value_or<std::int64_t>(100);
    if (c.contains("leverage")) base.leverage = Rate::from_double(*c["leverage"].value<double>());

    const toml::array* legs = c["legs"].as_array();
    if (!legs) throw std::invalid_argument("case has no legs");
    for (const auto& node : *legs) {
        const toml::table& l = *node.as_table();
        check_keys(l, {"side", "qty", "type", "expiry", "strike", "premium", "price", "reduced"});
        std::string side = str(l, "side");
        if (side != "long" && side != "short") throw std::invalid_argument("bad side: " + side);
        std::int64_t qty = *l["qty"].value<std::int64_t>();
        if (side == "short") qty = -qty;

        std::string type = str(l, "type");
        if (type == "stock") {
            k.stocks.push_back({qty, money(l, "price")});
            continue;
        }
        OptionLeg leg;
        leg.option = base;
        leg.option.type = pick<OptionType>(type, {{"call", OptionType::call}, {"put", OptionType::put}});
        leg.option.expiry = Date::parse(str(l, "expiry"));
        leg.option.strike = money(l, "strike");
        leg.quantity = qty;
        if (l.contains("premium")) leg.value = money(l, "premium");
        // A reduced-value index option on index/n is expressed in the full index: strike and
        // value per unit scale by n, and the deliverable shrinks by n (model.hpp, Option).
        if (auto n = l["reduced"].value<std::int64_t>()) {
            if (leg.option.deliverable % *n != 0) throw std::invalid_argument("reduced does not divide multiplier");
            leg.option.strike = leg.option.strike * *n;
            leg.value = leg.value * *n;
            leg.option.deliverable /= *n;
        }
        k.options.push_back(leg);
    }
    return k;
}

const OptionLeg& find(const Case& k, int sign, OptionType t) {
    for (const auto& l : k.options)
        if (l.option.type == t && (l.quantity > 0) == (sign > 0)) return l;
    throw std::invalid_argument("case lacks a required option leg");
}

const StockLeg& only_stock(const Case& k) {
    if (k.stocks.size() != 1) throw std::invalid_argument("case needs exactly one stock leg");
    return k.stocks[0];
}

const OptionLeg& only_option(const Case& k) {
    if (k.options.size() != 1) throw std::invalid_argument("case needs exactly one option leg");
    return k.options[0];
}

// netted, max_loss and valid: the parts of a spread case that need no prices.
void check_spread_shape(const toml::table& c, const Case& k) {
    if (const toml::array* netted = c["netted"].as_array()) {
        auto walk = strike_walk(k.options);
        CHECK_EQ(walk.size(), netted->size());
        for (std::size_t i = 0; i < walk.size() && i < netted->size(); ++i) {
            CHECK_EQ(walk[i].value, money(*netted->get(i)));
            CHECK_EQ(payoff_at(k.options, walk[i].strike), walk[i].value);
        }
    }
    if (c.contains("max_loss")) CHECK_EQ(max_potential_loss(k.options), money(c, "max_loss"));
    if (const toml::table* valid = c["valid"].as_table()) {
        check_keys(*valid, {"pairwise", "nearest_long", "same_expiry"});
        for (auto&& [key, flag] : *valid) {
            RuleSet r = k.rules;
            r.expiry_rule = pick<ExpiryRule>(std::string(key.str()), {{"pairwise", ExpiryRule::pairwise},
                                                                     {"nearest_long", ExpiryRule::nearest_long},
                                                                     {"same_expiry", ExpiryRule::same_expiry}});
            Validity v = spread_validity(k.options, r);
            ::check::context() += " " + std::string(key.str());
            CHECK_EQ(v.ok, *flag.value<bool>());
            ::check::context().resize(::check::context().size() - key.str().size() - 1);
        }
    }
}

bool has_expectation(const toml::table& c) {
    for (auto key : {"requirement", "underlying_requirement", "short_proceeds", "margin_call"})
        if (c.contains(key)) return true;
    return false;
}

void check_requirement(const toml::table& c, const Requirement& q) {
    if (c.contains("requirement")) CHECK_EQ(q.total(), money(c, "requirement"));
    if (c.contains("underlying_requirement")) CHECK_EQ(q.underlying, money(c, "underlying_requirement"));
    if (c.contains("short_proceeds")) CHECK_EQ(q.proceeds, money(c, "short_proceeds"));
    if (c.contains("margin_call")) CHECK_EQ(q.margin_call(), money(c, "margin_call"));
}

void run_case(const toml::table& c) {
    Case k = load_case(c);
    const RuleSet& r = k.rules;
    const Market& m = k.market;
    using T = OptionType;

    if (k.kind == "spread" || k.kind == "european_long_box") {
        if (!k.stocks.empty()) throw std::invalid_argument("spread case with a stock leg");
        check_spread_shape(c, k);
        if (k.kind == "european_long_box") {
            LongBox b = european_long_box(k.options, r);
            if (c.contains("box_margin")) CHECK_EQ(b.margin, money(c, "box_margin"));
            check_requirement(c, b.requirement);
        } else if (has_expectation(c)) {
            // Under the default rule set (pairwise); otherwise the manual margins each leg separately.
            check_requirement(c, spread_validity(k.options, r) ? spread(k.options, m, r).requirement
                                                               : separate(k.options, m, r));
        }
        return;
    }

    Requirement q;
    if (k.kind == "long_option") {
        q.options = long_option(only_option(k), m, r);
    } else if (k.kind == "short_option") {
        const OptionLeg& l = only_option(k);
        q.options = uncovered_short(l, m, r);
        q.proceeds = market_value(l);
    } else if (k.kind == "straddle") {
        q = short_straddle(find(k, -1, T::put), find(k, -1, T::call), m, r);
    } else if (k.kind == "covered_call") {
        q = covered_call(only_stock(k), find(k, -1, T::call), m, r);
    } else if (k.kind == "covered_put") {
        q = covered_put(only_stock(k), find(k, -1, T::put), m, r);
    } else if (k.kind == "protective_put") {
        q = protective_put(only_stock(k), find(k, +1, T::put), m, r);
    } else if (k.kind == "protective_call") {
        q = protective_call(only_stock(k), find(k, +1, T::call), m, r);
    } else if (k.kind == "conversion") {
        q = conversion(only_stock(k), find(k, -1, T::call), find(k, +1, T::put), m, r);
    } else if (k.kind == "reverse_conversion") {
        q = reverse_conversion(only_stock(k), find(k, +1, T::call), find(k, -1, T::put), m, r);
    } else if (k.kind == "collar") {
        q = collar(only_stock(k), find(k, +1, T::put), find(k, -1, T::call), m, r);
    } else if (k.kind == "index_call_etf") {
        q = index_call_etf(only_stock(k), find(k, -1, T::call), m, r);
    } else {
        throw std::invalid_argument("unknown kind: " + k.kind);
    }
    if (!has_expectation(c)) throw std::invalid_argument("case has no expected requirement");
    check_requirement(c, q);
}

}  // namespace

int run_fixture_file(const std::string& path) {
    toml::table doc = toml::parse_file(path);
    check_keys(doc, {"case"});
    const toml::array* cases = doc["case"].as_array();
    if (!cases || cases->empty()) throw std::invalid_argument("no cases in " + path);
    int ran = 0;
    for (const auto& node : *cases) {
        const toml::table& c = *node.as_table();
        ::check::context() = str(c, "id", "?");
        try {
            run_case(c);
        } catch (const std::exception& e) {
            ::check::report(std::string("threw: ") + e.what(), __FILE__, __LINE__);
        }
        ++ran;
    }
    ::check::context().clear();
    return ran;
}
