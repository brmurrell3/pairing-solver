# Specification

## 1. Problem

An account holds signed quantities of instruments. Some combinations of
instruments, held together, carry less risk than their parts held alone, and a
rulebook prices each recognized combination at a lower requirement. The account
holder may choose how to divide the positions among combinations. The solver
chooses the division that minimizes the total requirement. The rules must accept
the division, and the solver must report it leg by leg.

For options margin the rulebook treats the division as the holder's choice. The
Cboe Margin Manual allows positions to be margined separately to get the lowest
requirement, and FINRA 4210(f)(2)(M) lets a customer designate which held position
stands in for margin on an option (rules.md, R10). Brokers today mostly run greedy
pairing heuristics, so the gap between greedy and optimal pairing is real money.
See [sources.md](sources.md) for the evidence.

## 2. General model

The solver core knows nothing about options. It sees four things.

**Inventory.** Items `i` with long capacity `L_i ≥ 0` and short capacity `S_i ≥ 0`,
and a quantity grid `g_i`:

- `g_i = 1`: whole units.
- `g_i = 0.01`: hundredths.
- `g_i = 0`: continuous.

A quantity `x` is admissible when `x = g_i · n` for some integer `n ≥ 0`, or any
`x ≥ 0` when `g_i = 0`.

**Standalone cost.** Each unit of `i` left outside every structure costs
`u_i^L` (long) or `u_i^S` (short).

**Templates** `j`. A fixed leg vector `a_j` (signed units of each item per unit of
the template), a cost `c_j` per unit, and a multiplicity `y_j` on the grid. A
vertical spread, a straddle and a covered call are templates.

**Flexible groups** `h`. These are structures whose composition the solver chooses.
- **Membership:** `z_{h,i} ≥ 0` units of item `i` (on the grid), drawn from a candidate set.
- **Pairing graph:** a bipartite graph between the group's short items and its long items. A continuous flow `f_{h,s,l} ≥ 0` on each edge must exactly account for the members: every short unit is paired with some long unit, measured in a common unit (for options, the underlying's share-equivalents).
- **Loss rows:** a finite set `k` of linear loss functions. The group's cost is `t_h = max(0, max_k (−p_{h,k} · z_h))`, where `p_{h,k}` gives each member's signed value in scenario `k`.

Under the options rules, the rows are the netted intrinsic values at each strike price.

**Problem.**

```
minimize   Σ_j c_j y_j  +  Σ_h (t_h + e_h · z_h)  +  Σ_i (u_i^L r_i^L + u_i^S r_i^S)

subject to for every item i:
             Σ_j a⁺_{j,i} y_j + Σ_h z⁺_{h,i} + r_i^L = L_i        (long capacity)
             Σ_j a⁻_{j,i} y_j + Σ_h z⁻_{h,i} + r_i^S = S_i        (short capacity)
           for every group h and loss row k:
             t_h ≥ −p_{h,k} · z_h,   t_h ≥ 0
           for every group h, short member s, long member l:
             Σ_l f_{h,s,l} = w_s z_{h,s},   Σ_s f_{h,s,l} = w_l z_{h,l}  (pairing; w = units per contract)
           y, z on their grids; r, f, t ≥ 0
```

`e_h` is a per-unit surcharge for membership, such as the loan value a long option
gives up when it joins a spread (see rules.md, R4).

Every cost is linear in the decision variables, and each group cost is the maximum of linear
functions, so the whole problem is a linear program when every grid is continuous.
It is a mixed-integer program otherwise: the grid variables are integer in units of `g`,
and the flows and losses stay continuous. A step of 0.01 is the same integer
program with quantities scaled by 100, so one formulation covers whole, decimal and
continuous quantities. The continuous solve is always available as a lower bound.

## 3. The options-margin application

A module turns positions, market data and a rule set into the general model:

| General model | Options margin |
|---|---|
| Item | One option series, or one stock/ETF line. A series is a class, expiration, strike and unit of trading (FINRA 4210(f)(2)(A)(xxx)). |
| `L_i`, `S_i` | Contracts held long or short; shares for stock. |
| `w_i` | Deliverable per contract in underlying units: 100 for standard equity options, 10 for minis, and for example 150 after an adjustment. Index options use the index multiplier. |
| Standalone cost | Long option: premium paid in full, or 75% of value beyond 9 months. Short option: the uncovered requirement of 4210(f)(2)(E). Stock: Reg T or 4210(c). |
| Templates | Straddles and combinations, covered calls and puts, protective puts and calls, conversions, reversals, collars, European long boxes, and (under template-only policies) the named spreads. |
| Flexible groups | Spreads under 4210(f)(2)(A)(xxxii) and (H)(i). Members share an underlying, exercise style and listing. Within calls and within puts, long and short share-equivalents balance. Each short pairs with a long that expires on or after it. The group's cost is the maximum potential loss over the strike prices. |

### 3.1 Results that shape the design

These follow from the rule text in [rules.md](rules.md). They need proofs in the
write-up and tests in code.

1. **Evaluating at strikes is exact.** In a group that balances within calls and within puts, the netted payoff is piecewise linear in the underlying price. Its kinks sit only at member strikes, and its slope is zero below the lowest strike and above the highest. Its minimum is therefore attained at a member strike. Evaluating the loss rows at every strike in the class, not only the member strikes, gives the same maximum loss. So the loss rows can be fixed before the solve.
2. **One group per class is enough under the pairwise expiration reading.**
   - *Merging is valid:* the union of two valid groups is a valid group, because its pairing is the union of their pairings.
   - *Merging never costs more:* maximum loss is subadditive, since the maximum of a sum is at most the sum of the maxima.
   - *So one group suffices:* a single flexible group per (underlying, style, listing) class loses no optimality.
   - *Stricter house rules change the count:* under "every short expires on or before the nearest long", groups are indexed by a cut date, one per distinct expiration. Under "same expiration only", one group per expiration.
3. **"Lesser of uncovered or maximum loss" needs no extra variable.** Leaving a short out of the group and paying its uncovered requirement is the same choice, made per unit. The solver makes it.
4. **No flow variables are needed.** A short can pair with any same-type long that expires on or after it. The candidate longs for one short therefore contain those for any short that expires later, so the pairing graph is nested. For nested graphs, Hall's condition only has to be checked on suffixes. A perfect pairing exists if and only if, for each type and each expiration date `d`, the short units expiring on or after `d` do not exceed the long units expiring on or after `d`. That is one linear inequality per expiration per type, in place of a flow variable per edge.
5. **The payoff is a walk along the strikes.** In a group balanced within calls and within puts, sort the strikes `K_1 < … < K_n`.
   - Let `D_j` be the running signed quantity of all options (calls and puts together) at strikes up to `K_j`.
   - Let `Q_0` be the sum of signed put quantity times strike.
   - Then the netted payoff at `K_m` is `Q_0 + Σ_{j<m} D_j (K_{j+1} − K_j)`.

   Every loss row is a prefix sum of one strike-ordered sequence. The constraint matrix is a dense staircase, not a general sparse matrix, and all rows can be evaluated in O(n).
6. **Longs never raise the loss.** A long option's intrinsic value is nonnegative at every price, so adding a long can only lower a group's loss. Only the balance requirement and the loan-value surcharge limit which longs join. This is the starting point for pruning rules, which still need proofs.

Items 1, 4 and 5 were checked numerically on 3,000 random balanced portfolios of calls and puts across four expirations:
- **Walk formula** (item 5): it matched direct evaluation in every case.
- **Strike evaluation** (item 1): a 0.25-point price grid never found a lower payoff than the strikes.
- **Pairing condition** (item 4): the suffix condition agreed with an explicit maximum-flow check in every case. 457 cases were feasible and 1,543 infeasible.

Proofs are still owed for the write-up.

7. **Two-legged pairing alone is polynomial.** With only vertical, calendar and straddle templates, the problem is a transportation problem. Rudd and Schroeder (1982) showed this, and Matsypura and Timkovsky extended it to network flows. Fixed three- and four-leg templates (butterflies, condors) break that structure. Pairing whole contracts into named spreads is NP-hard in the strong sense when butterflies may have equal intervals of any width, and so is pairing into maximum-loss spreads of at most three or four legs (proofs.md, "Hardness", Theorems 1 and 2). The max-loss group avoids this in the continuous case, where it is a linear program. In whole contracts it is NP-hard too, but only in the weak sense (Theorems 3 and 4).

### 3.2 Problem size

These facts keep each solve small:

- **Decomposition:** subproblems are independent across accounts and across underlyings. Within an underlying, maximum-loss groups split further by exercise style and listing; stock structures tie options only to stock in the same underlying. A batch run is many small independent solves, one per (account, underlying).
- **Size:** assumed, not yet measured, to be tens to a few hundred series per subproblem. Strategy-based margin applies to customer accounts; large professional books generally use portfolio margin or market-maker treatment. Phase 3 measures this.
- **Shared rows:** every account holding the same underlying on the same day shares the strike set, prices and therefore the constraint coefficients and standalone costs. Only the bounds (holdings) differ, so a batch can reuse factorizations and warm-start from a similar account's solution.
- **Small integers:** customer holdings per series are usually small whole numbers. That keeps branch-and-bound or dynamic programming over quantities cheap.

### 3.3 Policies

The rule set is data, not code, so stricter broker rules are configuration:

- `basis`: `initial` (Reg T and Cboe 10.3) or `maintenance` (FINRA 4210).
- `expiry_rule`: `pairwise` (Cboe manual reading), `nearest_long`, or `same_expiry`.
- `max_loss_groups`: on, or off for template-only pairing.
- `templates`: which named structures are allowed.
- `european_calendars`: allowed, surcharged, or disallowed. The Cboe manual notes that brokers add margin when the later-expiring long is European-style.
- `grid`: per instrument kind, e.g. options 1, shares 1, or options 0.01.
- Rate table: percentages and minimums by product class, from 4210(f)(2)(E).

### 3.4 Solver

The project writes its own solver; it does not wrap a general-purpose one.

1. **Exact baseline:**
   - A dense, bounded-variable dual simplex sized for one subproblem.
   - The rows are the strike-walk loss rows, the two balance equalities and the suffix pairing inequalities; every variable is boxed between zero and its holding.
   - Branch-and-bound on top of the simplex for grid quantities.
   - Dual simplex suits a batch: moving to another account changes bounds, not coefficients, so the previous basis stays dual feasible.
2. **Structured algorithm:** a combinatorial method that uses the walk structure. The candidate is dynamic programming over strikes, with the running quantity `D` and the payoff level as state; for whole contracts it is exact. It is pseudo-polynomial, and no exact method is polynomial in the digits of the strikes unless P = NP (proofs.md, "Strike dynamic program" and "Hardness").
3. **Reference only:** HiGHS is a test-time dependency, never shipped. It certifies optimal values for randomized differential tests against both of the above.

The library is C++20 behind a small C interface (handle in, flat arrays in, results out, error codes). Java can call it through the Foreign Function & Memory API, and Python through ctypes.

### 3.5 Out of scope for version 1

- Portfolio margin (4210(g)). It is a scenario-based alternative regime, not a pairing problem.
- Options whose deliverable includes several securities or cash.
- Futures, warrants, GNMA and Treasury options.
- Intraday and day-trading margin.

## 4. Outputs

For each solve:

1. **Structures:** every structure used, with its legs, quantities and requirement, plus the residual standalone positions and their requirements.
2. **Totals:** the total requirement, the all-standalone total, and the greedy-baseline total.
3. **Optimality certificate:** the continuous lower bound and the gap. The gap is zero for a continuous solve.
4. **Shadow prices:** for each position, the change in requirement per unit, taken from the duals of the continuous solve. These answer "what does closing this leg free up".

## 5. What "correct" means

1. Every requirement formula reproduces the worked examples in the Cboe Margin Manual to the cent. The fixtures are in [../data/fixtures](../data/fixtures).
2. On every portfolio small enough to enumerate (about 8 positions), the solver matches exhaustive search.
3. No solution violates a policy. An independent checker re-derives each structure's validity and requirement from the rules, separate from the model builder.
4. Results are deterministic: the same input gives the same total.
