// Dynamic program over the strike walk (spec §3.4 item 2; docs/proofs.md, "Strike dynamic
// program").
//
// With put balance, the payoff at strike k splits into calls to its left and puts to its
// right: P_k = Σ_{j<k} C_j ΔK_j − Σ_{j≥k} P'_j ΔK_j, where C_j and P'_j are the cumulative
// call and put units through strike j and ΔK_j = K_{j+1} − K_j. Walking left to right, keep
//   Y = Σ_{j<k} C_j ΔK_j                       (the call part of P_k), and
//   X = min_{i≤k} P_i + Σ_{j≥k} P'_j ΔK_j       (the running minimum, less the put tail),
// which update as Y += C ΔK and X = min(X − P' ΔK, Y). After the last strike X is the
// minimum payoff, so the group's loss is max(0, −X). X and Y only ever help, and the cost
// only ever hurts, so states with the same (C, P') are kept as a Pareto front.

#include <algorithm>
#include <map>
#include <stdexcept>
#include <utility>
#include <vector>

#include "pairing/solver.hpp"

namespace pairing {

namespace {

struct State {
    Money cost;  // members' change against standalone: −U for a short, loan value lost for a long
    Money x, y;
    int parent;
    std::int64_t call, put;  // contracts chosen at this strike, signed
};

// Keeps the states not dominated in (lower cost, higher x, higher y).
void pareto(std::vector<State>& v) {
    std::sort(v.begin(), v.end(), [](const State& a, const State& b) {
        if (a.cost != b.cost) return a.cost < b.cost;
        if (a.x != b.x) return a.x > b.x;
        return a.y > b.y;
    });
    std::vector<State> kept;
    for (const State& s : v) {
        bool dominated = false;
        for (const State& k : kept)
            if (k.x >= s.x && k.y >= s.y) {
                dominated = true;
                break;
            }
        if (!dominated) kept.push_back(s);
    }
    v = std::move(kept);
}

}  // namespace

Solution solve_strike_dp(const Portfolio& p, const RuleSet& r, const DpOptions& o) {
    const int n = static_cast<int>(p.options.size());
    if (p.stock.shares != 0) throw std::invalid_argument("the strike dynamic program takes options only");
    for (const auto& l : p.options) {
        const Option &a = l.option, &b = p.options.front().option;
        if (l.quantity == 0) throw std::invalid_argument("zero-quantity position");
        if (a.underlying != b.underlying || a.style != b.style || a.listing != b.listing || a.expiry != b.expiry ||
            a.deliverable != b.deliverable)
            throw std::invalid_argument(
                "the strike dynamic program needs one underlying, style, listing, expiration and deliverable");
    }

    Solution s;
    std::vector<Money> unit(n), delta(n);
    for (int i = 0; i < n; ++i) {
        OptionLeg one = lot_leg(p.options[i], 1, 1);
        unit[i] = separate({one}, p.market, r).total();
        delta[i] = p.options[i].quantity > 0 ? market_value(one) - unit[i] : -unit[i];
        s.all_standalone += unit[i] * std::llabs(p.options[i].quantity);
    }

    // Strikes in order, with the call and put position at each (one series per type).
    std::map<Money, std::pair<int, int>> at;
    for (int i = 0; i < n; ++i) {
        auto& slot = at.try_emplace(p.options[i].option.strike, -1, -1).first->second;
        int& pos = p.options[i].option.type == OptionType::call ? slot.first : slot.second;
        if (pos >= 0) throw std::invalid_argument("two positions in one series");
        pos = i;
    }
    std::vector<Money> strike;
    std::vector<std::pair<int, int>> pos;
    for (const auto& [k, v] : at) {
        strike.push_back(k);
        pos.push_back(v);
    }
    const int m = static_cast<int>(strike.size());
    const std::int64_t w = n > 0 ? p.options.front().option.deliverable : 1;

    // Reach: from strike k on, how far the cumulative contracts can still move up and down,
    // so states that can no longer balance are dropped. Best: the most the remaining shorts
    // can still save, for the bound against the incumbent.
    std::vector<std::int64_t> call_up(m + 1, 0), call_down(m + 1, 0), put_up(m + 1, 0), put_down(m + 1, 0);
    std::vector<Money> best(m + 1);
    for (int k = m - 1; k >= 0; --k) {
        call_up[k] = call_up[k + 1], call_down[k] = call_down[k + 1];
        put_up[k] = put_up[k + 1], put_down[k] = put_down[k + 1];
        best[k] = best[k + 1];
        for (int i : {pos[k].first, pos[k].second}) {
            if (i < 0) continue;
            std::int64_t q = p.options[i].quantity;
            bool call = p.options[i].option.type == OptionType::call;
            (q > 0 ? (call ? call_up : put_up) : (call ? call_down : put_down))[k] += std::llabs(q);
            if (delta[i] < Money{}) best[k] += delta[i] * std::llabs(q);
        }
    }

    // Layer k holds the states after strike k's choices, keyed by cumulative contracts.
    using Key = std::pair<std::int64_t, std::int64_t>;
    std::vector<std::vector<State>> layers;  // flattened, for reconstruction
    std::map<Key, std::vector<State>> front{{{0, 0}, {State{Money{}, Money{}, Money{}, -1, 0, 0}}}};
    Money incumbent{};  // every position standalone
    long kept = 0;  // states generated, before dominance and pruning
    bool limit = false;
    for (int k = 0; k < m && !limit; ++k) {
        // Move from strike k−1 to strike k: the walk's step, applied to the cumulative state.
        std::vector<State> flat;
        std::map<Key, std::vector<State>> next;
        for (auto& [key, states] : front) {
            if (limit) break;
            for (State st : states) {
                if (limit) break;
                if (k > 0) {
                    Money dk = strike[k] - strike[k - 1];
                    st.y = st.y + dk * (key.first * w);
                    st.x = std::min(st.x - dk * (key.second * w), st.y);
                }
                const int here = static_cast<int>(flat.size());
                flat.push_back(st);
                auto range = [&](int i) {
                    if (i < 0) return std::pair<std::int64_t, std::int64_t>{0, 0};
                    std::int64_t q = p.options[i].quantity;
                    return q > 0 ? std::pair<std::int64_t, std::int64_t>{0, q} : std::pair<std::int64_t, std::int64_t>{q, 0};
                };
                auto [c_lo, c_hi] = range(pos[k].first);
                auto [p_lo, p_hi] = range(pos[k].second);
                for (std::int64_t c = c_lo; c <= c_hi; ++c) {
                    std::int64_t cc = key.first + c;
                    if (cc > call_down[k + 1] || -cc > call_up[k + 1]) continue;
                    for (std::int64_t u = p_lo; u <= p_hi; ++u) {
                        std::int64_t pp = key.second + u;
                        if (pp > put_down[k + 1] || -pp > put_up[k + 1]) continue;
                        State t = st;
                        t.parent = here, t.call = c, t.put = u;
                        if (pos[k].first >= 0) t.cost += delta[pos[k].first] * std::llabs(c);
                        if (pos[k].second >= 0) t.cost += delta[pos[k].second] * std::llabs(u);
                        // The remaining shorts save at most best[k+1]. X can still rise, by
                        // −P'ΔK at each later step while the cumulative puts are net short,
                        // and P' can fall to pp less the shorts still to come, so the loss
                        // is at least −X less that rise. (Treating the loss as never falling
                        // pruned a long put below a short one: 10 and 32.5 against 15.)
                        const Money rise = (strike[m - 1] - strike[k]) * (std::max<std::int64_t>(0, put_down[k + 1] - pp) * w);
                        Money lower = t.cost + best[k + 1] + std::max(Money{}, -t.x - rise);
                        if (lower >= incumbent) continue;
                        next[{cc, pp}].push_back(t);
                        // Unpruned candidates count too, so one layer cannot run away.
                        if (++kept > o.state_limit) limit = true;
                    }
                }
            }
        }
        // The first strike's step does nothing; record the parents of layer k.
        layers.push_back(std::move(flat));
        front.clear();
        for (auto& [key, states] : next) {
            pareto(states);
            if (key.first == 0 && key.second == 0 && k + 1 == m)
                for (const State& t : states) incumbent = std::min(incumbent, t.cost + std::max(Money{}, -t.x));
        }
        front = std::move(next);
        if (kept > o.state_limit) limit = true;
    }

    s.status = limit ? MipStatus::node_limit : MipStatus::optimal;
    s.nodes = static_cast<int>(std::min<long>(kept, 2'000'000'000));
    std::vector<std::int64_t> chosen(n, 0);
    Money objective{};
    if (!limit && m > 0) {
        auto it = front.find({0, 0});
        const State* bestState = nullptr;
        Money bestTotal{};
        if (it != front.end())
            for (const State& t : it->second) {
                // After the last strike the walk is flat (balance), so X is the minimum payoff.
                Money total = t.cost + std::max(Money{}, -t.x);
                if (total < bestTotal) bestTotal = total, bestState = &t;
            }
        if (bestState) {
            objective = bestTotal;
            State cur = *bestState;
            for (int k = m - 1; k >= 0; --k) {
                if (pos[k].first >= 0) chosen[pos[k].first] = cur.call;
                if (pos[k].second >= 0) chosen[pos[k].second] = cur.put;
                if (k > 0) cur = layers[k][cur.parent];
            }
        }
    }

    Structure group{StructureKind::spread, {}, {}};
    for (int i = 0; i < n; ++i) {
        std::int64_t in = std::llabs(chosen[i]), all = std::llabs(p.options[i].quantity);
        if (in > 0) group.legs.push_back({i, in});
        if (in < all) s.residuals.push_back({{i, all - in}, {}});
    }
    if (!group.legs.empty()) s.structures.push_back(std::move(group));
    s.total = check_solution(p, r, s);
    // At the optimum a group's loss is below its shorts' uncovered requirement, or leaving
    // them standalone would be cheaper, so Phase 1's spread price equals the DP's.
    if (s.total != s.all_standalone + objective)
        throw std::logic_error("the dynamic program's total " + (s.all_standalone + objective).str() +
                               " disagrees with the checker's " + s.total.str());
    s.bound = s.status == MipStatus::optimal ? static_cast<double>(s.total.micros()) / Money::per_dollar : 0;
    return s;
}

}  // namespace pairing
