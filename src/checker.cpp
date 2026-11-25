// The independent checker: it knows the Phase 1 engine and the meaning of a Solution, and
// nothing about the model the solver built.

#include <cstdlib>
#include <stdexcept>
#include <string>

#include "pairing/solver.hpp"

namespace pairing {

OptionLeg lot_leg(const OptionLeg& position, std::int64_t lots, std::int64_t lots_per_contract) {
    if (lots_per_contract < 1 || position.option.deliverable % lots_per_contract != 0)
        throw std::invalid_argument("lots per contract must divide the deliverable");
    OptionLeg l = position;
    l.option.deliverable /= lots_per_contract;
    l.quantity = position.quantity < 0 ? -lots : lots;
    return l;
}

const char* kind_name(StructureKind k) {
    switch (k) {
        case StructureKind::spread: return "spread";
        case StructureKind::straddle: return "straddle";
        case StructureKind::covered_call: return "covered_call";
        case StructureKind::covered_put: return "covered_put";
        case StructureKind::protective_put: return "protective_put";
        case StructureKind::protective_call: return "protective_call";
        case StructureKind::conversion: return "conversion";
        case StructureKind::reverse_conversion: return "reverse_conversion";
        case StructureKind::collar: return "collar";
        case StructureKind::long_box: return "long_box";
    }
    return "?";
}

namespace {

void require(bool ok, const std::string& what) {
    if (!ok) throw std::invalid_argument(what);
}

struct Usage {
    const Portfolio& p;
    std::int64_t lots_per_contract;
    std::vector<std::int64_t> options;
    std::int64_t stock = 0;

    OptionLeg option(const StructureLeg& l) {
        require(l.position >= 0 && l.position < static_cast<int>(p.options.size()), "leg names no option position");
        require(l.quantity > 0, "leg quantity must be positive");
        options[l.position] += l.quantity;
        return lot_leg(p.options[l.position], l.quantity, lots_per_contract);
    }
    StockLeg shares(const StructureLeg& l) {
        require(l.position == stock_position && p.stock.shares != 0, "leg names no stock line");
        require(l.quantity > 0, "leg quantity must be positive");
        stock += l.quantity;
        return StockLeg{p.stock.shares < 0 ? -l.quantity : l.quantity, p.stock.price};
    }
};

Requirement price(const Structure& st, Usage& u, const Portfolio& p, const RuleSet& r) {
    const auto& legs = st.legs;
    for (std::size_t i = 0; i < legs.size(); ++i)
        for (std::size_t j = i + 1; j < legs.size(); ++j)
            require(legs[i].position != legs[j].position, "a position appears twice in one structure");
    auto count = [&](std::size_t n, bool with_stock) {
        require(legs.size() == n, "wrong number of legs");
        if (with_stock) require(legs[0].position == stock_position, "the stock leg must come first");
        for (std::size_t i = with_stock ? 1 : 0; i < n; ++i)
            require(legs[i].position != stock_position, "unexpected stock leg");
    };
    const Market& m = p.market;
    switch (st.kind) {
        case StructureKind::spread: {
            require(!legs.empty(), "empty spread");
            std::vector<OptionLeg> ol;
            for (const auto& l : legs) ol.push_back(u.option(l));
            Validity v = spread_validity(ol, r);
            require(v.ok, "invalid spread: " + v.reason);
            return spread(ol, m, r).requirement;
        }
        case StructureKind::straddle:
            count(2, false);
            return short_straddle(u.option(legs[0]), u.option(legs[1]), m, r);
        case StructureKind::covered_call:
            count(2, true);
            return covered_call(u.shares(legs[0]), u.option(legs[1]), m, r);
        case StructureKind::covered_put:
            count(2, true);
            return covered_put(u.shares(legs[0]), u.option(legs[1]), m, r);
        case StructureKind::protective_put:
            count(2, true);
            return protective_put(u.shares(legs[0]), u.option(legs[1]), m, r);
        case StructureKind::protective_call:
            count(2, true);
            return protective_call(u.shares(legs[0]), u.option(legs[1]), m, r);
        case StructureKind::conversion:
            count(3, true);
            return conversion(u.shares(legs[0]), u.option(legs[1]), u.option(legs[2]), m, r);
        case StructureKind::reverse_conversion:
            count(3, true);
            return reverse_conversion(u.shares(legs[0]), u.option(legs[1]), u.option(legs[2]), m, r);
        case StructureKind::collar:
            count(3, true);
            return collar(u.shares(legs[0]), u.option(legs[1]), u.option(legs[2]), m, r);
        case StructureKind::long_box: {
            count(4, false);
            std::vector<OptionLeg> ol;
            for (const auto& l : legs) ol.push_back(u.option(l));
            return european_long_box(ol, r).requirement;
        }
    }
    throw std::invalid_argument("unknown structure kind");
}

}  // namespace

Money check_solution(const Portfolio& p, const RuleSet& r, Solution& s) {
    Usage u{p, s.lots_per_contract, std::vector<std::int64_t>(p.options.size(), 0)};
    for (const auto& o : p.options) {
        require(o.quantity != 0, "zero-quantity position");
        require(o.option.underlying == p.options.front().option.underlying, "positions have different underlyings");
    }
    Money total;
    for (std::size_t k = 0; k < s.structures.size(); ++k) {
        Structure& st = s.structures[k];
        try {
            st.requirement = price(st, u, p, r);
        } catch (const std::invalid_argument& e) {
            throw std::invalid_argument("structure " + std::to_string(k) + " (" + kind_name(st.kind) + "): " + e.what());
        }
        total += st.requirement.total();
    }
    for (auto& res : s.residuals) {
        if (res.leg.position == stock_position) res.requirement = stock(u.shares(res.leg), r);
        else res.requirement = separate({u.option(res.leg)}, p.market, r);
        total += res.requirement.total();
    }
    for (std::size_t i = 0; i < p.options.size(); ++i)
        require(u.options[i] == std::llabs(p.options[i].quantity) * s.lots_per_contract,
                "option position " + std::to_string(i) + " is not used exactly");
    require(u.stock == std::llabs(p.stock.shares), "the stock line is not used exactly");
    return total;
}

}  // namespace pairing
