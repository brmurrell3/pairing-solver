// Exhaustive search on small subproblems (spec §5.2), compared with the solver.
//
// The search divides every position's units into blocks in every possible way and prices
// each block as the cheapest structure Phase 1 accepts for exactly those legs, or
// standalone when the block is one position. It relies on none of spec §3.1:
// - blocks are arbitrary sub-multisets, so a class may hold several spreads (item 2);
// - pairwise validity is decided by an explicit maximum flow as well as by Phase 1's
//   suffix condition (item 4), and any disagreement fails the test;
// - Phase 1's maximum loss is checked against evaluation at zero, every strike and far
//   above the highest strike (item 1);
// - nothing assumes longs only lower a loss (item 6) or that the lesser-of rule needs no
//   variable (item 3): spread blocks are priced by Phase 1's spread(), lesser-of included.

#include <chrono>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <optional>
#include <random>
#include <set>
#include <string>
#include <vector>

#include "check.hpp"
#include "generate.hpp"
#include "pairing/solver.hpp"

using namespace pairing;

namespace {

struct Stats {
    long portfolios = 0, states = 0, blocks = 0, spread_blocks = 0, flow_feasible = 0, flow_infeasible = 0;
    long multi_spread_classes = 0, mismatches = 0, lp_integral = 0;
    double seconds_search = 0, seconds_solve = 0;
    std::map<std::string, long> kinds;
};

// Short units of each type flow to same-type longs expiring on or after them.
bool pairing_by_flow(const std::vector<OptionLeg>& legs) {
    int n = static_cast<int>(legs.size()) + 2, src = n - 2, sink = n - 1;
    std::vector<std::vector<std::int64_t>> cap(n, std::vector<std::int64_t>(n, 0));
    std::int64_t need = 0, supply = 0;
    for (int i = 0; i < n - 2; ++i) {
        if (legs[i].quantity < 0) {
            cap[src][i] = -legs[i].units();
            need += -legs[i].units();
            for (int j = 0; j < n - 2; ++j)
                if (legs[j].quantity > 0 && legs[j].option.type == legs[i].option.type &&
                    legs[j].option.expiry >= legs[i].option.expiry)
                    cap[i][j] = 1'000'000'000;
        } else {
            cap[i][sink] = legs[i].units();
            supply += legs[i].units();
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
    // Every short paired and every long used: per type, longs equal shorts.
    return flow == need && need == supply;
}

bool balanced_by_type(const std::vector<OptionLeg>& legs) {
    std::int64_t calls = 0, puts = 0;
    for (const auto& l : legs) (l.option.type == OptionType::call ? calls : puts) += l.units();
    return calls == 0 && puts == 0;
}

// R1 a–e under the pairwise reading, without the suffix condition.
bool pairwise_valid(const std::vector<OptionLeg>& legs, const RuleSet& r) {
    std::set<Date> expiries;
    for (const auto& l : legs) {
        if (l.option.style != legs[0].option.style || l.option.listing != legs[0].option.listing ||
            l.option.underlying != legs[0].option.underlying)
            return false;
        expiries.insert(l.option.expiry);
    }
    if (legs[0].option.style == Style::european && expiries.size() > 1 &&
        r.european_calendars == EuropeanCalendars::disallowed)
        return false;
    // Balance per type and a complete pairing; the flow alone checks both, per type.
    for (OptionType t : {OptionType::call, OptionType::put}) {
        std::vector<OptionLeg> of_type;
        for (const auto& l : legs)
            if (l.option.type == t) of_type.push_back(l);
        if (!of_type.empty() && !pairing_by_flow(of_type)) return false;
    }
    return true;
}

Money loss_by_evaluation(const std::vector<OptionLeg>& legs) {
    Money worst = payoff_at(legs, Money{});
    Money top;
    for (const auto& l : legs) {
        worst = std::min(worst, payoff_at(legs, l.option.strike));
        top = std::max(top, l.option.strike);
    }
    worst = std::min(worst, payoff_at(legs, top * 10 + Money::dollars(1)));
    return std::max(Money{}, -worst);
}

struct Block {
    std::vector<int> b;
    std::int64_t index;
    Money cost;
    std::string kind;
};

class Search {
public:
    Search(const Portfolio& p, const RuleSet& r, Stats& st) : p_(p), r_(r), st_(st) {
        n_ = static_cast<int>(p.options.size());
        for (const auto& o : p.options) count_.push_back(static_cast<int>(std::llabs(o.quantity)));
        if (p.stock.shares != 0) {
            unit_ = std::llabs(p.stock.shares);
            for (const auto& o : p.options) unit_ = std::gcd(unit_, o.option.deliverable);
            count_.push_back(static_cast<int>(std::llabs(p.stock.shares) / unit_));
        }
        std::int64_t s = 1;
        for (int c : count_) {
            stride_.push_back(s);
            s *= c + 1;
        }
        states_ = s;
    }

    std::int64_t states() const { return states_; }

    Money run() {
        std::vector<std::vector<Block>> by_first(count_.size());
        std::vector<int> v(count_.size(), 0);
        for (std::int64_t idx = 1; idx < states_; ++idx) {
            increment(v);
            if (auto blk = price(v)) {
                blk->index = idx;
                int f = 0;
                while (v[f] == 0) ++f;
                by_first[f].push_back(*blk);
                ++st_.blocks;
            }
        }
        std::vector<Money> best(states_);
        std::vector<int> choice(states_, -1), choice_first(states_, -1);
        std::fill(v.begin(), v.end(), 0);
        for (std::int64_t idx = 1; idx < states_; ++idx) {
            increment(v);
            int f = 0;
            while (v[f] == 0) ++f;
            bool found = false;
            for (std::size_t k = 0; k < by_first[f].size(); ++k) {
                const Block& blk = by_first[f][k];
                bool fits = true;
                for (std::size_t i = f; i < v.size() && fits; ++i) fits = blk.b[i] <= v[i];
                if (!fits) continue;
                Money c = blk.cost + best[idx - blk.index];
                if (!found || c < best[idx]) {
                    best[idx] = c;
                    choice[idx] = static_cast<int>(k);
                    choice_first[idx] = f;
                    found = true;
                }
            }
            if (!found) throw std::logic_error("exhaustive search found no division");  // singletons always fit
        }
        // Read back the optimum's blocks.
        std::map<std::pair<int, int>, int> spreads_per_class;
        for (std::int64_t idx = states_ - 1; idx > 0;) {
            const Block& blk = by_first[choice_first[idx]][choice[idx]];
            ++st_.kinds[blk.kind];
            if (blk.kind == "spread") {
                int i = 0;
                while (blk.b[i] == 0) ++i;
                const Option& o = p_.options[i].option;
                ++spreads_per_class[{static_cast<int>(o.style), static_cast<int>(o.listing)}];
            }
            idx -= blk.index;
        }
        for (auto& [cls, k] : spreads_per_class)
            if (k > 1) ++st_.multi_spread_classes;
        return best[states_ - 1];
    }

private:
    const Portfolio& p_;
    const RuleSet& r_;
    Stats& st_;
    int n_;
    std::int64_t unit_ = 1;
    std::vector<int> count_;
    std::vector<std::int64_t> stride_;
    std::int64_t states_;

    void increment(std::vector<int>& v) const {
        for (std::size_t i = 0; i < v.size(); ++i) {
            if (v[i] < count_[i]) {
                ++v[i];
                return;
            }
            v[i] = 0;
        }
    }

    std::optional<Block> price(const std::vector<int>& b) {
        std::vector<OptionLeg> opts;
        std::optional<StockLeg> stk;
        for (int i = 0; i < n_; ++i)
            if (b[i] > 0) {
                OptionLeg l = p_.options[i];
                l.quantity = l.quantity < 0 ? -b[i] : b[i];
                opts.push_back(l);
            }
        if (static_cast<int>(b.size()) > n_ && b[n_] > 0)
            stk = StockLeg{(p_.stock.shares < 0 ? -1 : 1) * b[n_] * unit_, p_.stock.price};

        std::optional<Block> out;
        auto offer = [&](Money c, const char* kind) {
            if (!out || c < out->cost) out = Block{b, 0, c, kind};
        };
        auto attempt = [&](auto f, const char* kind) {
            try {
                offer(f().total(), kind);
            } catch (const std::invalid_argument&) {
            }
        };
        const Market& m = p_.market;
        std::size_t positions = opts.size() + (stk ? 1 : 0);
        if (positions == 1) {
            if (stk) offer(stock(*stk, r_).total(), "standalone");
            else offer(separate(opts, m, r_).total(), "standalone");
            return out;
        }
        if (!stk && balanced_by_type(opts)) {
            bool phase1 = static_cast<bool>(spread_validity(opts, r_));
            if (r_.expiry_rule == ExpiryRule::pairwise) {
                bool flow = pairwise_valid(opts, r_);
                (flow ? st_.flow_feasible : st_.flow_infeasible)++;
                CHECK_EQ(phase1, flow);
            }
            if (phase1) {
                ++st_.spread_blocks;
                CHECK_EQ(max_potential_loss(opts), loss_by_evaluation(opts));
                offer(spread(opts, m, r_).requirement.total(), "spread");
            }
        }
        if (!stk && opts.size() == 2) {
            attempt([&] { return short_straddle(opts[0], opts[1], m, r_); }, "straddle");
            attempt([&] { return short_straddle(opts[1], opts[0], m, r_); }, "straddle");
        }
        if (!stk && opts.size() == 4) attempt([&] { return european_long_box(opts, r_).requirement; }, "long_box");
        if (stk && opts.size() == 1) {
            attempt([&] { return covered_call(*stk, opts[0], m, r_); }, "covered_call");
            attempt([&] { return covered_put(*stk, opts[0], m, r_); }, "covered_put");
            attempt([&] { return protective_put(*stk, opts[0], m, r_); }, "protective_put");
            attempt([&] { return protective_call(*stk, opts[0], m, r_); }, "protective_call");
        }
        if (stk && opts.size() == 2) {
            for (int a = 0; a < 2; ++a) {
                const OptionLeg &x = opts[a], &y = opts[1 - a];
                attempt([&] { return conversion(*stk, x, y, m, r_); }, "conversion");
                attempt([&] { return reverse_conversion(*stk, x, y, m, r_); }, "reverse_conversion");
                attempt([&] { return collar(*stk, x, y, m, r_); }, "collar");
            }
        }
        return out;
    }
};

std::string describe(const Portfolio& p, const RuleSet& r) {
    std::string s = "rules: basis=" + std::string(r.basis == Basis::initial ? "initial" : "maintenance") +
                    " expiry=" + std::to_string(static_cast<int>(r.expiry_rule)) +
                    " euro_cal=" + std::to_string(static_cast<int>(r.european_calendars)) +
                    " hedged=" + std::to_string(static_cast<int>(r.hedged_short_value)) +
                    "\n  underlying " + p.market.underlying.str() + "\n";
    for (const auto& l : p.options) {
        const Option& o = l.option;
        s += "  " + std::to_string(l.quantity) + (o.type == OptionType::call ? " C " : " P ") + o.strike.str() + " " +
             std::to_string(o.expiry.year) + "-" + std::to_string(o.expiry.month) + " w" +
             std::to_string(o.deliverable) + (o.style == Style::european ? " eu" : " am") +
             (o.listing == Listing::otc ? " otc" : "") + " @" + l.value.str() + "\n";
    }
    if (p.stock.shares != 0) s += "  stock " + std::to_string(p.stock.shares) + " @" + p.stock.price.str() + "\n";
    return s;
}

// Keep the search to a size that runs in well under a second.
void shrink(Portfolio& p, std::int64_t max_states) {
    for (;;) {
        std::int64_t s = p.stock.shares != 0 ? std::llabs(p.stock.shares) / 50 + 1 : 1;
        for (const auto& o : p.options) s *= std::llabs(o.quantity) + 1;
        if (s <= max_states) return;
        auto it = std::max_element(p.options.begin(), p.options.end(), [](const OptionLeg& a, const OptionLeg& b) {
            return std::llabs(a.quantity) < std::llabs(b.quantity);
        });
        if (std::llabs(it->quantity) <= 1) {
            p.options.pop_back();
            continue;
        }
        it->quantity += it->quantity < 0 ? 1 : -1;
    }
}

}  // namespace

int run_exhaustive(int per_policy) {
    const std::pair<ExpiryRule, const char*> policies[] = {
        {ExpiryRule::pairwise, "pairwise"}, {ExpiryRule::nearest_long, "nearest_long"}, {ExpiryRule::same_expiry, "same_expiry"}};
    int ran = 0;
    for (auto [rule, name] : policies) {
        Stats st;
        for (int k = 0; k < per_policy; ++k) {
            std::mt19937_64 rng(1'000'003ULL * static_cast<unsigned>(rule) + k);
            gen::Shape shape;
            shape.max_series = 8;
            shape.max_quantity = 3;
            shape.expiries = 1 + k % 3;
            shape.strikes = 2 + k % 3;
            shape.adjusted = k % 4 == 0;
            Portfolio p = gen::portfolio(rng, shape);
            if (p.stock.shares != 0 && p.options.size() > 7) p.options.pop_back();
            if (p.options.empty()) continue;
            shrink(p, 40'000);
            RuleSet r = gen::rules(rng, rule);
            ::check::context() = std::string(name) + " #" + std::to_string(k);

            if (std::getenv("PAIRING_TRACE")) std::cerr << ::check::context() << "\n" << describe(p, r);
            auto t0 = std::chrono::steady_clock::now();
            Search search(p, r, st);
            st.states += search.states();
            Money expected = search.run();
            auto t1 = std::chrono::steady_clock::now();
            Solution s = solve(p, r);
            auto t2 = std::chrono::steady_clock::now();
            st.seconds_search += std::chrono::duration<double>(t1 - t0).count();
            st.seconds_solve += std::chrono::duration<double>(t2 - t1).count();
            ++st.portfolios;
            st.lp_integral += s.lp_integral;
            CHECK_EQ(s.total, expected);
            CHECK(s.lp_bound <= static_cast<double>(s.total.micros()) / 1e6 + 1e-6);
            if (s.total != expected) {
                ++st.mismatches;
                std::cerr << describe(p, r);
            }
        }
        std::cout << "exhaustive " << name << ": " << st.portfolios << " portfolios, " << st.mismatches
                  << " mismatches; " << st.states << " states, " << st.blocks << " priced blocks, " << st.spread_blocks
                  << " valid spread blocks";
        if (rule == ExpiryRule::pairwise)
            std::cout << " (flow: " << st.flow_feasible << " feasible, " << st.flow_infeasible << " infeasible)";
        std::cout << "; " << st.multi_spread_classes << " optima with 2+ spreads in one class; continuous optimum on grid "
                  << st.lp_integral << "/" << st.portfolios << "; search " << st.seconds_search << " s, solver "
                  << st.seconds_solve << " s\n  blocks in optima:";
        for (auto& [kind, c] : st.kinds) std::cout << " " << kind << "=" << c;
        std::cout << "\n";
        ran += static_cast<int>(st.portfolios);
    }
    ::check::context().clear();
    return ran;
}
