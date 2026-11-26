# Proofs for spec §3.1

Plan Phase 4 asks for written proofs of spec §3.1 items 1, 2, 4 and 5. They are below,
with items 3 and 6, which the others lean on. The rule references are to
[rules.md](rules.md). `tools/check_structure.py` and the `unit` test check items 1, 4 and 5
numerically. The sections after item 6 are the other Phase 4 results: integrality, compact
straddles, the strike dynamic program, and hardness (Theorems 1 to 4 and Proposition 5),
which `tools/check_hardness.py` checks by exhaustive search on small instances. Theorems 1
and 2 are also proved in Lean 4 (`lean/`).

## Setting

A group is a set of option positions on one underlying, all of one exercise style and
one listing (R1 a–c). Each member `i` has a type (call or put), a strike `K_i`, an
expiration `e_i`, and a signed size `n_i = q_i · w_i` in share-equivalents: contracts
`q_i` (positive long, negative short) times deliverable `w_i` (U3). The group is
*balanced* (R1 d) when

    Σ_{calls} n_i = 0   and   Σ_{puts} n_i = 0.

Its netted intrinsic value at an underlying price `S ≥ 0` is

    P(S) = Σ_{calls} n_i (S − K_i)⁺ + Σ_{puts} n_i (K_i − S)⁺.

R2 defines the maximum potential loss as `max(0, −min_{K ∈ 𝒦} P(K))`, where `𝒦` is the set of
the members' strikes.

## Item 1: evaluating at strikes is exact

**Claim.** For a balanced group, `min_{S ≥ 0} P(S) = min_{K ∈ 𝒦} P(K)`. Hence, for any finite
set `𝒦' ⊇ 𝒦` of nonnegative prices, `min_{K ∈ 𝒦'} P(K) = min_{K ∈ 𝒦} P(K)`.

**Proof.** Each term of `P` is linear in `S` except for a kink at its strike, so `P` is
continuous and piecewise linear with kinks only in `𝒦`. Let `K_1 < … < K_m` be the
distinct members' strikes.

- On `[0, K_1]` every call term is zero and every put term is `n_i (K_i − S)`. The slope is
  `−Σ_{puts} n_i = 0` by put balance, so `P` is constant there.
- On `[K_m, ∞)` every put term is zero and every call term is `n_i (S − K_i)`. The slope is
  `Σ_{calls} n_i = 0` by call balance, so `P` is constant there.
- On each `[K_j, K_{j+1}]`, `P` is linear, so its minimum on that interval is at an end.

The minimum over `S ≥ 0` is therefore attained at some `K_j`. Every price in `𝒦'` lies in the
domain, so a minimum over `𝒦'` cannot fall below the global minimum, and `𝒦' ⊇ 𝒦` contains a
point that attains it. ∎

**Use.** The model writes one loss row per strike of the whole candidate set (every strike
in the class), not only the strikes a solution ends up using. By the claim, those rows give
exactly R2's maximum loss for any balanced choice of members. So the rows can be fixed
before the solve.

Without balance the claim fails: a lone long call has `P(S) = n (S − K)⁺`, which is
unbounded, and a lone short call has no minimum. R1 d rules both out.

## Item 5: the payoff is a walk along the strikes

**Claim.** Sort the distinct strikes `K_1 < … < K_m`. Let `c_j` and `p_j` be the signed
call and put share-equivalents at `K_j`, `D_j = Σ_{i ≤ j} (c_i + p_i)`, and
`Q_0 = Σ_j p_j K_j`. If the puts balance (`Σ_j p_j = 0`), then for every `k`

    P(K_k) = Q_0 + Σ_{j < k} D_j (K_{j+1} − K_j).

**Proof.** By induction on `k`.

- `k = 1`: no call is in the money at `K_1`, and every put has `K_j ≥ K_1`, so
  `P(K_1) = Σ_j p_j (K_j − K_1) = Q_0 − K_1 Σ_j p_j = Q_0`.
- Step: on `[K_k, K_{k+1}]` the calls with strike at most `K_k` are in the money, with
  slope `+c_j` each, and the puts with strike above `K_k` are in the money, with slope
  `−p_j` each. So the slope is `Σ_{j ≤ k} c_j − Σ_{j > k} p_j`. Put balance gives
  `−Σ_{j > k} p_j = Σ_{j ≤ k} p_j`, so the slope is `D_k`, and
  `P(K_{k+1}) = P(K_k) + D_k (K_{k+1} − K_k)`. ∎

Only put balance is used. Call balance adds `D_m = 0`, which is the flat right tail of
item 1.

**Use.** Every loss row is a prefix sum of one strike-ordered sequence. All `m` rows can be
evaluated in O(m) once the `c_j` and `p_j` are known. This is the structure a dynamic
program over strikes would exploit (plan Phase 4).

## Item 4: no flow variables are needed

**Setting.** Fix one type (calls or puts) in a group under the pairwise reading (R2a): a
short may pair with a long of the same type that expires on or after it. Short `s`
supplies `a_s = −n_s > 0` share-equivalents to be paired, and long `l` supplies
`b_l = n_l > 0`. The group's members must be paired exactly: there must be a flow
`f_{s,l} ≥ 0` on edges with `e_l ≥ e_s` such that `Σ_l f_{s,l} = a_s` for every short and
`Σ_s f_{s,l} = b_l` for every long (spec §2). Balance gives `Σ_s a_s = Σ_l b_l`.

**Claim.** Such a flow exists if and only if, for every expiration `d`,

    A(d) := Σ_{s : e_s ≥ d} a_s  ≤  B(d) := Σ_{l : e_l ≥ d} b_l.

**Proof.** This is a transportation problem with equal totals. By the max-flow min-cut
theorem (or Gale's supply-demand theorem), a flow that ships every `a_s` exists iff every
set `X` of shorts satisfies `a(X) ≤ b(N(X))`, where `N(X)` is the set of longs adjacent to
some short in `X`. When the totals are equal, a flow that ships every `a_s` also uses every
`b_l` exactly.

The graph is nested. For a set `X`, let `d_X` be the earliest expiration in `X`; then
`N(X) = {l : e_l ≥ d_X}`, which depends on `X` only through `d_X`. Among all `X` with the
same `d_X`, the largest `a(X)` belongs to the set of all shorts expiring on or after `d_X`.
So Hall's condition for every `X` reduces to `A(d) ≤ B(d)` at each `d = d_X`, which is a
short's expiration.

- *Necessity:* the suffix sets are among the sets `X`.
- *Sufficiency:* any `X` has `a(X) ≤ A(d_X) ≤ B(d_X) = b(N(X))`.

For `d` that is not a short's expiration, `A(d) = A(d')` for the next short expiration
`d' > d` (or `0`), and `B(d) ≥ B(d')`, so those inequalities are implied. ∎

**Use.** At the earliest expiration, `A = B` is the balance equality itself. Each later
expiration adds one linear inequality in the member quantities: `B(d) − A(d) ≥ 0`. These
are the suffix rows in `group()` (`src/solver.cpp`), and they replace one flow variable per
edge. The inequalities are linear in the quantities and hold for real values, so they are
exact on every grid.

## Item 2: one group per class is enough under the pairwise reading

**Claim.** Under `expiry_rule = pairwise`, for any collection of valid groups in one
(underlying, style, listing) class, the single group made of their sum is valid and its
maximum loss is at most the sum of theirs.

**Proof.**

- *Valid.* Same underlying, style and listing hold by construction (R1 a–c). Balance within
  calls and within puts is additive, so it holds for the sum (R1 d). For R1 e under the
  pairwise reading, the union of the groups' pairing flows is a pairing flow for the sum,
  so item 4's condition holds. Equivalently, each `A(d) ≤ B(d)` is additive over groups.
- *No more costly.* Let `P_1` and `P_2` be the groups' payoffs. The merged payoff is
  `P_1 + P_2`. By item 1, each group's loss can be computed on the union of all their
  strikes, `𝒦`, without changing it. Then
  `max(0, −min_𝒦 (P_1 + P_2)) ≤ max(0, −min_𝒦 P_1) + max(0, −min_𝒦 P_2)`, since
  `min (P_1 + P_2) ≥ min P_1 + min P_2` and `x ↦ max(0, −x)` is nonincreasing and
  subadditive.
- The other costs are linear in the members: a long pays its premium in full whether it is
  in one group or another (R2), so the surcharge `e_h` adds up. ∎

By induction, one group per class does at least as well as any set of groups.

**Stricter readings.** Under `nearest_long` (every short expires on or before the group's
earliest long), the union of two valid groups can be invalid: a short in one group may
outlast the other group's earliest long. Validity is closed under union only among groups
whose earliest long expires on or after a common cut date `c` and whose shorts all expire
on or before `c`. The model therefore uses one group per cut date `c` (one per distinct
expiration in the class), with shorts expiring at or before `c` and longs at or after it.
The argument above applies within each cut date. Under `same_expiry`, the cut date is the
single expiration, so there is one group per expiration.

## Item 3: "lesser of uncovered or maximum loss" needs no extra variable

R2 charges a spread `min(U, M) + L_full`, where `U` is the shorts' uncovered requirement, `M`
is the maximum loss and `L_full` is the longs' premiums in full.

**Claim.** `min(U, M) + L_full ≥ min(U + L_alone, M + L_full)`, where `L_alone ≤ L_full` is
what the same longs cost standalone (R4: full premium, or 75% beyond nine months).

**Proof.** If `M ≤ U`, both sides equal `M + L_full`. If `U < M`, the left side is
`U + L_full ≥ U + L_alone`, which is on the right. ∎

So the cheaper of "the group as a spread at its maximum loss" and "every member
standalone" is never worse than R2's formula, and the solver chooses between those per
unit. The model prices a group at `M + L_full` only.

**Consequence for checking** (found in Phase 2). An assignment accepted within the gap may
keep a group with `U < M`. Phase 1 prices that spread at `U + L_full`, below the model's
`M + L_full`. The checker's total is reported, and it can only be lower than the model's.
At the optimum the two agree, because unpairing such a group would be cheaper in the model
too.

## Item 6: longs never raise the loss

A long's term in `P` is `n_i (S − K_i)⁺` or `n_i (K_i − S)⁺` with `n_i > 0`, nonnegative at
every price. So, for fixed members, raising a long's size raises `P` everywhere and cannot
raise the maximum loss. Balance means a long's size cannot change on its own, so the useful
form is a swap between two longs of one type. Moving `x` share-equivalents from a long call
at `K` to a long call at `K' < K` with the same or a later expiration raises `P` by
`x((S − K')⁺ − (S − K)⁺) ≥ 0` at every `S`. It keeps both balance and item 4's suffix
condition, so the loss cannot rise. The same holds for puts with `K' > K`. What remains is
the premium: the deeper long costs more (R2: paid in full), so the swap is a trade-off, not
a dominance. Pruning rules built on this are not yet written or proved.

## Integrality (plan Phase 4)

**Question.** When is the continuous optimum already whole-contract?

**Measured.** In docs/benchmarks.md, the continuous optimum is whole for 456 of 496 retail
books, 232 of 496 books with adjusted series, and 91 of 200 market-maker books. A random
search of 40,000 books per shape (`solve` with `rel_gap = 0`) found:

| Books | With a gap |
|---|---|
| 2 series, calls only | 0 of 38,957 |
| 2 series, calls and puts | 0 of 39,475 |
| 3 series, calls only | 7 of 36,946 |
| 3 series, calls and puts | 0 of 38,518 |

Two series form at most one vertical or one straddle. The LP has a whole optimum there,
which matches item 7's transportation structure for two-legged pairing. The two
counterexamples below are in the `solver` test.

**Three calls, two expirations, one deliverable.** Spot 55.83; long 1 Feb 40 call (15.83),
short 3 Feb 45 calls (10.85), long 4 Mar 67.50 calls (0.22). The LP pairs the long 40 and
2/9 of a long 67.50 against 11/9 of the short 45s. The payoff is 5.00 per share at 45 and
`27.50 − (11/9)(22.50) + 0 = 0` at 67.50, so the loss is zero. The continuous bound is
5,584.96 (exactly 50,264.60 / 9). Whole contracts cannot reach a zero-loss ratio of 11 to
9, and the best is 5,622.60, 0.67% above the bound.

**An iron condor, one contract a leg.** Spot 97.29, all April: short 107.50 call (2.34),
long 115 call (1.07), long 75 put (0.22), short 90 put (2.71). The call spread's loss is
750 and the put spread's is 1,500. In one group, the loss is the larger of the two wings,
not the sum. The LP takes the call spread and half the put spread, whose 750 loss on the
downside matches the call wing's 750 on the upside, so it adds nothing. The other half of
the short put stays standalone. The bound is 1,622.90. The whole optimum is 1,629.00, the
full condor at a 1,500 loss, 0.37% above.

**What this shows.** Fractional optima come from the loss being a maximum over strikes.
A fraction of one wing can sit under another wing's loss, or a ratio of contracts can make
a loss row exactly zero. Neither needs mixed deliverables, puts or several expirations,
though mixed deliverables make gaps much larger (mean 3.0% and up to 39% in the adjusted
family, against 0.03% for retail books). No sufficient condition for integrality beyond
two series is known yet.

## Compact short straddles (plan Phase 4)

**Setting.** Short puts and short calls of one lot size, on one underlying. R6 charges one
lot of put `p` with one lot of call `c` at `max(U_p, U_c) + V_o`, where `U` is the uncovered
requirement, `V` the market value, and `o` the leg with the smaller requirement. Phase 1
(`short_straddle`) treats a tie as if the put were dearer, so `o` is the call when
`U_p = U_c`. Margined separately, the two cost `U_p + U_c`, so the pair saves

    U_p + U_c − max(U_p, U_c) − V_o = U_o − V_o =: g_o.

The saving depends only on the cheaper leg.

**Order.** Rank the class's shorts by `(U, calls before puts)`. Then any put and any call
can pair, with the lower-ranked one as the cheap side. Each pair saves the cheap leg's `g`,
and ties are charged as Phase 1 charges them.

**Claim.** Choosing integer lots `y_{p,c}` for every pair is equivalent to choosing, for
each short `k`, lots `a_k` on the cheap side and `b_k` on the dear side, with the same
objective `Σ g_k a_k` and the same capacity use `a_k + b_k`. The conditions, for each
direction (cheap puts against dear calls, and cheap calls against dear puts), are:

- total cheap lots equal total dear lots, and
- for every cheap leg at rank `t`, the cheap lots at rank `t` or above do not exceed the
  dear lots of the other type ranked above `t`.

**Proof.** In one direction, a cheap lot at rank `t` may pair with any dear lot of the
other type ranked above `t`. The candidate sets shrink as `t` rises, so the graph is nested
as in item 4, and the same argument applies with ranks in place of expirations. A pairing
that uses every cheap and every dear lot exactly exists if and only if the conditions hold.
It can be taken integral, because the supplies are integers and transportation problems
have integral vertices. Given `y`, setting `a` and `b` to its cheap-side and dear-side sums
satisfies the conditions; given `a` and `b`, the pairing is a valid `y`. ∎

`read_solution` builds the pairing by taking cheap lots from the highest rank down and
matching each with any unused dear lot ranked above it. That never blocks a later cheap
lot, whose candidates include all of these.

**Effect.** Two columns per short and about one row per short replace one column per
pair. The `solver` test checks that both forms give the same exact optimum on 400 random
books. Branching is slower on the compact form for small books (the 1,000-case HiGHS test
took 40 s against 18 s), so it applies only to classes with more than 256 pairs
(`SolveOptions::compact_straddle_pairs`). A 1,000-series market-maker book went from
58,601 to 1,765 columns and from 153 s to 18.0 s.

## Strike dynamic program (plan Phase 4)

**Scope.** One max-loss group and standalone residuals: options of one style, listing,
expiration and deliverable `w`, no stock, no straddles. With one expiration the suffix rows
of item 4 are empty and, by item 2, one group per class is enough. `solve_strike_dp` in
`src/dp.cpp` implements it.

**Objective.** Choose signed contracts `x_i` in the group, between zero and the holding.
A short in the group gives up its standalone requirement `U_i`; a long pays its market
value instead of its standalone requirement (the loan value of a long beyond nine months is
lost, Q3). With `δ_i` the per-contract change, the total is the all-standalone total plus
`Σ δ_i |x_i| + max(0, −min_k P_k)`, subject to call and put balance.

**Walk in one pass.** Sort the strikes `K_1 < … < K_m`, let `C_j` and `P'_j` be the
cumulative call and put units through strike `j`, and `Δ_j = K_{j+1} − K_j`. Summation by
parts on item 5's `Q_0`, using `P'_m = 0`, gives `Q_0 = −Σ_{j<m} P'_j Δ_j`. So

    P_k = Σ_{j<k} C_j Δ_j − Σ_{j≥k} P'_j Δ_j:

the calls to the left of `k` and the puts to its right. The second sum depends on choices
not yet made, so the DP carries, after strike `k`,

    Y_k = Σ_{j<k} C_j Δ_j,    X_k = min_{i≤k} P_i + Σ_{j≥k} P'_j Δ_j.

Both start at 0 and update as `Y_{k+1} = Y_k + C_k Δ_k` and
`X_{k+1} = min(X_k − P'_k Δ_k, Y_{k+1})`, since `P_{k+1} + Σ_{j≥k+1} P'_j Δ_j = Y_{k+1}`. At
the last strike the put tail is empty, so `X_m = min_k P_k`.

**Dominance.** For states with the same `(C, P')`, the future updates are nondecreasing in
`X` and `Y`, and the final cost `cost + max(0, −X_m)` is nondecreasing in cost and
nonincreasing in `X_m`. So a state with no lower cost and no higher `X` and `Y` than another
can be dropped, and each `(C, P')` keeps a Pareto front in (cost, `X`, `Y`). States that can
no longer reach `C = P' = 0` with the remaining holdings are dropped.

**Bound.** `X` can rise. A step adds `−P'_k Δ_k` to it, up to the cap `Y_{k+1}`, and that is
positive while the cumulative puts are net short (`P'_k < 0`). Let `s_k` be the short put
units held above strike `k`. Every later `P'_j` is at least `P'_k − s_k`, so

    X_m ≤ X_k + r_k,    r_k = (K_m − K_k) · max(0, s_k − P'_k).

A state is dropped when its cost, less the most the remaining shorts can still save, plus
`max(0, −X_k − r_k)`, is not below the incumbent. Without puts `r_k = 0` and the loss so far
never falls. (Until 2026-11-26 the bound used `max(0, −X_k)` for every book, as if `X` never
rose. That could prune the optimum when puts were net short below a strike: with the
`strike_dp` test's books redrawn, one of the 1,500 came out at 13,719.00 against
branch-and-bound's 13,343.00.) The program is exact for whole contracts: every balanced
choice is some path, and dominance and the bound remove only paths that cannot be better.

**Complexity.** Let `N_c` and `N_p` be the total call and put contracts held, `w` the
deliverable and `τ` the strike tick. `X` and `Y` are multiples of `wτ` with magnitude at
most `(N_c + N_p) w (K_m − K_1)`, so each takes at most `R = 2(N_c + N_p)(K_m − K_1)/τ + 1`
values. Each layer has at most `(2N_c + 1)(2N_p + 1)` keys, and a front keeps at most the
cheapest state for each (`X`, `Y`) pair, so at most `R²` states. Strike `k` fans each state
out to at most `(q + 1)²` choices, with `q` the largest holding. The total is
`O(m · N_c N_p · R² · q²)` states generated: pseudo-polynomial in contracts and in the strike range over the tick,
not polynomial in the input size. That is the right kind of bound. The one-group problem is
NP-hard, so no exact method is polynomial in the input size unless P = NP, but it is
NP-hard only in the weak sense, through strikes with many digits ("Hardness" below,
Theorems 3 and 4). The integrality counterexamples above already show it is not a network
problem, even with calls only.

**Measured** (docs/benchmarks.md, "Strike dynamic program"). The `solver` test checks the
DP against exact branch-and-bound with straddles off on 1,500 random books, all equal.
Against branch-and-bound on the same books, the DP loses everywhere measured. At 10
series of 1 to 5 contracts both take under a millisecond. At 10 series of 1 to 50
contracts the DP's median is 82 ms against 0.09 ms, and at 100 series it reaches its
5,000,000-state limit on every book, while exact branch-and-bound has a median of 9 to
50 ms. The front grows with the payoff range, as the bound says, and the LP bound that
lets branch-and-bound stop at the root has no counterpart here. The DP stays as an
independent exact check that shares no code with the simplex.

## Hardness (plan Phase 4)

**Status (2026-11-26).** These results have not been independently reviewed. No earlier
proof was found, but the search was incomplete: Rudd and Schroeder (1982) and Chen and Li,
"Margin Calculation of Multi-Leg Option Strategies", are unread (sources.md). Each reduction
is checked by exhaustive search on small instances ("Checks" below), which tests the
constructions and cannot prove them. The correctness and size of the reductions of
Theorems 1 and 2 are machine-checked in Lean 4 ([lean/](../lean/README.md)); the
NP-completeness of numerical 3-dimensional matching is cited there, not proved. Theorems 3
and 4 and Proposition 5 are not formalized.

**Questions.**
(a) Matsypura and Timkovsky write that "the complexity status of the problem with offsets
based on option spreads with more than two legs remains unknown" (05/2010, Introduction;
04/2010, concluding remarks, for a portfolio of individual options). Is finding the minimum
margin NP-hard once butterflies and condors count as offsets?
(b) Is the solver's own problem, one maximum-loss group in whole contracts, NP-hard?

**Answers.**

| Which spreads the rules recognize | Result | Reduction from |
|---|---|---|
| Named spreads of two to four legs; butterflies and condors have equal strike intervals, of any width (the legacy rule, question (a)) | NP-hard in the strong sense (Theorem 1) | numerical 3-dimensional matching |
| The same, with butterflies and condors only on adjacent strikes of one evenly spaced grid | Solvable in time polynomial in the grid length and the contracts held, so not NP-hard in the strong sense unless P = NP (Proposition 5) | none |
| Spreads of at most three legs, or at most four, priced at their maximum loss (today's rule with a leg limit) | NP-hard in the strong sense (Theorem 2) | numerical 3-dimensional matching |
| Any balanced set, priced at its maximum loss (today's rule and the solver's model, question (b)) | NP-hard; with one expiration only in the weak sense (Theorems 3 and 4) | subset sum |

Every hard instance below uses calls of one expiration and one deliverable, in whole
contracts. With continuous quantities the solver's problem is a linear program (spec §2),
so the hardness comes from whole contracts.

*Strong* means the problem stays NP-hard when every strike, counted in ticks, and every
quantity is at most a polynomial in the number of contracts. Such a problem has no
pseudo-polynomial algorithm, one whose time is polynomial in those numbers themselves,
unless P = NP. *Weak* means the hard instances need strikes with many digits.

`tools/check_hardness.py` checks each reduction by exhaustive search on small instances,
and the `solver` test `subset_sum_reduction` checks Theorem 4 on the solver and on the
strike dynamic program ("Checks" below). The assumptions behind the statements are listed
in plan.md, Phase 4.

### Setting

Calls on one underlying, of one expiration, style, listing and deliverable. Amounts are per
share. A *position* holds `q_K` whole contracts at each strike `K`, positive long and
negative short. A *spread* is a balanced set of long and short contracts taken from the
position (R1 d): as many long as short. Its payoff `P` and maximum loss are those of
"Setting" at the top of this file. A *leg* is the spread's contracts in one series, so here
at one strike.

A *pairing* puts every short contract into exactly one spread or leaves it uncovered, and
every long contract into at most one spread. Its requirement is the sum of its spreads'
requirements, plus `U_K` for each short contract at `K` left uncovered, where `U_K > 0` is
the uncovered requirement (R3). A long call is paid for in full whether or not it is in a
spread (R2, and R4 at nine months or less), so the longs cost the same under every pairing
and are left out. What remains is what Matsypura and Timkovsky call the market risk
(05/2010, Section 3).

Three rules say which spreads exist and what they require:

- **Named spreads.** The legacy list: verticals, butterflies and condors, with equal
  intervals where the definition asks for them (Theorem 1 gives the list).
- **Leg limit `ℓ`.** Any spread of at most `ℓ` legs. Its requirement is its maximum loss,
  or the lesser of that and the uncovered requirement of its shorts (R2). The proofs hold
  for both.
- **One group.** Any spread at all, priced the same way. This is the solver's model.

For a spread `t`, its *moment* is `m(t) = Σ q_i K_i` over its contracts: the sum of the
long strikes minus the sum of the short strikes.

**Lemma (moment).** At and above its highest strike, a spread's payoff is `−m(t)`. So a
spread with no loss has `m(t) ≤ 0`.

**Proof.** For `S` at or above every strike of `t`,
`P(S) = Σ q_i (S − K_i) = S Σ q_i − m(t) = −m(t)`, because `t` is balanced. The highest
strike is one of the prices R2 evaluates. ∎

**Numerical 3-dimensional matching.** Given positive integers `a_1 … a_n`, `b_1 … b_n`,
`c_1 … c_n` and a bound `B`: can they be split into `n` triples `(a_i, b_j, c_k)`, each
number used once, with `a_i + b_j + c_k = B` in every triple? This is NP-complete in the
strong sense (Garey and Johnson, problem SP16). Adding up the triples shows that a matching
needs `Σa + Σb + Σc = nB`.

Below, `W` is the largest of `B` and the `3n` numbers, and `M = 6nW`.

### Theorem 1: named spreads with butterflies and condors

**The rule.** The named call spreads, per unit, for strikes `K_1 < K_2 < K_3 < K_4`:

| Spread | Contracts | Requirement |
|---|---|---|
| Bull call spread | long `K_1`, short `K_2` | 0 |
| Bear call spread | short `K_1`, long `K_2` | positive |
| Long butterfly | long `K_1`, short two `K_2`, long `K_3`, with `K_2 − K_1 = K_3 − K_2` | 0 |
| Short butterfly | short `K_1`, long two `K_2`, short `K_3`, same condition | positive |
| Long condor | long `K_1`, short `K_2`, short `K_3`, long `K_4`, all three intervals equal | 0 |
| Short condor | short `K_1`, long `K_2`, long `K_3`, short `K_4`, same condition | positive |

These are the call-side main spreads of Matsypura and Timkovsky (05/2010, Table 2), which
follow NYSE Rule 431(f)(2)(C). No text of the legacy rule is in `refs/`. What is used here is
what their paper shows of it, compared with regulatory texts that were read on 2026-11-26
only through a subagent's reports (sources.md): NASD Notices to Members 01-11 and 06-26, for
the NASD rules that the notices call substantially similar to, or consistent with, the
NYSE's amendments; a FINRA text of Rule 4210 that shows the old definitions as deleted; and
SEC Release 34-52951 for NYSE Rule 431.

- *Intervals.* Their Section 2 recognizes a long butterfly from `K_1 < K_2 < K_3` and
  `K_2 − K_1 = K_3 − K_2`. Their model calls a spread uniform when its consecutive legs
  are one exercise differential apart (Section 4), and keeps one portfolio for each
  differential (04/2010, Sections 6 and 10). Theorem 1 reads this as: the intervals inside one
  spread are equal and may be any width, so a position can hold butterflies of many widths
  at once. The NASD's definition agrees, as reported: a butterfly spread is three series
  "where the interval between the exercise price of each series is equal" (Rule 2522(a)(9),
  Notice 01-11), with no condition that the strikes be adjacent and no limit on the width.
  Proposition 5 covers the narrower reading in which only one differential counts.
- *Condors.* The definition since deleted from FINRA Rule 4210 asks, as reported, that the
  interval between each of the four series be equal and that "the exercise prices are in
  consecutive order", and Release 34-52951 describes the NYSE's long condor as two long
  butterflies with equal intervals. So all three intervals are equal. If "consecutive" also
  means adjacent listed strikes, nothing changes: the proof forms no condor, and fact 3
  below rules out every equally spaced one. Those texts name no short condor. Without a
  name it is two verticals, and its requirement is positive either way.
- *Requirements.* A debit spread has no market risk and a credit spread has one interval
  of it (their formula (1)), or the lesser of that and the uncovered requirement of its
  short under the current-loss rule (their Section 3). Notice 01-11 has the same shape, as
  reported: the net debit of a long butterfly is paid in full, and a short butterfly of
  calls requires the difference between its two lowest exercise prices. The proof uses only
  which requirements are zero.
- *Other main spreads.* Iron butterflies, iron condors and boxes contain puts and cannot
  be formed from calls.

**Theorem 1.** Deciding whether a position of calls can be paired into named spreads with
requirement zero is NP-complete in the strong sense. So finding the minimum requirement
when butterflies and condors count as offsets is NP-hard in the strong sense.

**Reduction.** From `(a, b, c, B)` build the *butterfly instance*:

    long one call at   x_i = 2 a_i             for each i
    short two calls at y_j = M + B − b_j       for each j
    long one call at   z_k = 2M + 2 c_k        for each k

Numbers that coincide share a strike, and their contracts add up. Every strike is a positive
integer below `2M + 2W + 1` and there are `4n` contracts, so the instance sits on a grid of
unit strike steps whose length is a polynomial in `n` and `W`.

1. *Order.* Every `x` is below every `y`, and every `y` below every `z`:
   `x ≤ 2W < M − W + 1 ≤ y ≤ M + W − 1 < 2M + 2 ≤ z`.
2. *Triples.* `x_i + z_k = 2 y_j` exactly when `a_i + b_j + c_k = B`.
3. *No condor.* No strikes `x < y < y' < z` are equally spaced: two short strikes differ by
   at most `W − 1`, and a short strike is at least `M − 3W + 1 > W − 1` above every `x`.

**Proof.** *A matching gives requirement zero.* For each triple take the long butterfly
long `x_i`, short two `y_j`, long `z_k`. By 1 and 2 its strikes are in order with equal
intervals. The `n` butterflies use every contract once, and each requires nothing.

*Requirement zero gives a matching.* In such a pairing no short is uncovered, and every
spread that holds a short has requirement zero, so it is a bull call spread, a long
butterfly or a long condor. By 1, the shorts sit only at `y` strikes, the longs below them
are the `x`, and the longs above them are the `z`. So a bull call spread is one `x` with one
short, a long butterfly is one `x`, two shorts at one `y`, and one `z`, and a long condor
would be `x < y < y' < z` equally spaced, which 3 rules out. Let there be `β` butterflies
and `v` bull call spreads. The shorts give `2β + v = 2n`, and the `x` contracts give
`β + v ≤ n`. Subtracting, `β ≥ n`, and `β ≤ n` because each butterfly uses an `x`. So
`β = n` and `v = 0`: the pairing is `n` butterflies that use every `x` and every `z` once
and the two shorts of every `b_j`. By 2 each is a triple with sum `B`.

The problem is in NP: a pairing names one multiplicity for each named spread, and there
are `O(h²)` of those on `h` strikes. The reduction is polynomial and keeps every number
polynomial in `n` and `W`, which is what the strong sense needs. ∎

**If a condor needs only equal wings.** Fact 3 uses the reading of Table 2 in which all
three intervals of a condor are equal. If only the two outer intervals had to be equal,
the butterfly instance would fail ("Why two instances" below), and the condor instance of
Theorem 2 takes its place. The named list is then a family of spreads of at most four legs
that contains every long condor with equal wings, and in it a requirement is zero exactly
when the maximum loss is. So Theorem 2 gives the same conclusion.

**Example.** `a = (1, 2)`, `b = (3, 1)`, `c = (3, 4)`, `B = 7` has the matching
`1 + 3 + 3` and `2 + 1 + 4`. Here `W = 7` and `M = 84`. The position is long one call at 2
and at 4, short two at 88 and at 90, and long one at 174 and at 176. The butterflies
2/88/174 and 4/90/176, each with intervals of 86, cover it at zero. With verticals alone,
the longs at 2 and 4 cover two shorts for nothing and the other two shorts are left to
bear spreads against 174 and 176 or to their uncovered requirement.

**Not approximable.** The theorem separates a minimum of zero from a positive one. So,
unless P = NP, no polynomial algorithm guarantees any fixed multiple of the minimum
requirement net of long premiums. With the premiums added, which are the same for every
pairing, this says nothing.

### Theorem 2: a leg limit under the maximum-loss rule

Theorem 1 leans on the equal-interval clause, and today's rule has no such clause: R2 prices
an uneven butterfly by its maximum loss (Cboe manual p. 37). The hardness does not come from
the clause. It comes from the limit on legs.

**Theorem 2.** Let `ℓ` be 3 or 4. Let the recognized spreads be any family of balanced call
spreads of at most `ℓ` legs in which a spread's requirement is zero exactly when its
maximum loss is zero, and which contains

- for `ℓ = 3`: every long butterfly with equal intervals;
- for `ℓ = 4`: every long condor with equal wings, that is long `K_1`, short `K_2`, short
  `K_3`, long `K_4` with `K_2 − K_1 = K_4 − K_3`.

Then deciding whether a position of calls has a pairing with requirement zero is NP-hard in
the strong sense.

R2 prices a spread at its maximum loss, or at the lesser of that and the uncovered
requirement of its shorts, which is positive. Either way the requirement is zero exactly
when the loss is. So the theorem covers the family of all balanced sets of at most `ℓ`
legs, with any whole number of contracts a leg, and any list of named shapes with free
intervals (verticals, 1-2-1 butterflies, 1-1-1-1 condors) priced by R2.

**Reduction.** If `Σa + Σb + Σc ≠ nB` there is no matching, and the reduction outputs one
uncovered short call, which no pairing brings to zero. Otherwise:

- for `ℓ = 3`, the butterfly instance of Theorem 1;
- for `ℓ = 4`, the *condor instance*, with `p = n + 1` and `q = n + 2`:

      long one call at  x_i = a_i                   for each i
      short one call at y_j = pM + B − b_j          for each j
      short n calls at  y*  = qM
      long one call at  z_k = (p + q)M + c_k        for each k

  Its strikes are positive and in the order `x < y < y* < z`, because `M > 2W`, and
  `x_i + z_k = y_j + y*` exactly when `a_i + b_j + c_k = B`.

**Proof.** *A matching gives requirement zero.* For `ℓ = 3`, the butterflies of Theorem 1
have payoff `0` at `x`, `y − x > 0` at `y` and `2y − x − z = 0` at `z`. For `ℓ = 4`, each
triple gives the condor long `x_i`, short `y_j`, short `y*`, long `z_k`. Its wings are
equal, and its payoff is `0` at `x`, `y − x > 0` at `y` and at `y*`, and
`y + y* − x − z = 0` at `z`. In both cases the spreads belong to the family, have no loss,
and use every contract once.

*Requirement zero gives a matching.* No short is uncovered, and every spread in the
pairing has requirement zero and so no loss. The spreads hold all `2n` short contracts
and, being balanced, `2n` long contracts, which is every long in the position. By the
lemma each spread has `m(t) ≤ 0`. The moments add up to the moment of the whole position,
which is `2(Σa + Σb + Σc − nB) = 0` for the butterfly instance and `Σa + Σb + Σc − nB = 0`
for the condor instance. So every spread has `m(t) = 0`.

*Three legs.* Let `t` hold `α` contracts at `x` strikes, `γ` at `y` strikes and `β` at `z`
strikes. Balance gives `α + β = γ`. Its moment is `(2β − γ)M + λ`, where `λ` collects the
low-order parts of its contracts: `2a` for a contract at an `x` strike, `2c` at a `z`
strike and `−(B − b)` at a `y` strike. The long parts are positive and at most `2W` each,
and `t` has at most `2n` of them. The short parts are below `W` in size, and `t` has at
most `2n` of them. So `−2nW < λ < 6nW`, that is `|λ| < M`. With `m(t) = 0` this gives
`γ = 2β` and `λ = 0`, and then `α = β`. Since `t` holds a short, `β ≥ 1`, so `t` has
contracts at all three kinds of strike. With at most three legs it is `β` contracts at one
`x_i`, `2β` at one `y_j` and `β` at one `z_k`, and `λ = 2β(a_i + b_j + c_k − B) = 0`. So
`t` is `β` copies of a triple with sum `B`.

*Four legs.* Let `t` hold `α` contracts at `x` strikes, `γ` at `y` strikes, `γ*` at `y*`
and `β` at `z` strikes. Balance gives `α + β = γ + γ*`. Its moment is
`((p + q)β − pγ − qγ*)M + λ`, where `λ` now collects `a`, `c` and `−(B − b)`: at most `2n`
long parts of at most `W` each, and at most `n` short parts below `W` in size. So
`|λ| < 3nW < M`, hence `λ = 0` and `p(β − γ) = q(γ* − β)`. The consecutive numbers `p` and
`q` have no common factor, so `q` divides `β − γ`. But `|β − γ| ≤ n < q`, so `γ = β`, then
`γ* = β` and `α = β`. Since `t` holds a short, `β ≥ 1`, and `t` has contracts at all four
kinds of strike. With at most four legs it is `β` contracts at each of one `x_i`, one
`y_j`, `y*` and one `z_k`, and `λ = β(a_i + b_j + c_k − B) = 0`.

In both cases, cutting every spread into its `β` copies gives triples with sum `B` that use
every `a_i`, `b_j` and `c_k` once. The reduction keeps every number polynomial in `n` and
`W`. ∎

**Why two instances.** On the butterfly instance, four-leg spreads can reach zero without
a matching. `a = (1, 2)`, `b = (5, 1)`, `c = (3, 2)`, `B = 7` has the right total and no
matching. Its butterfly instance is long one call at 2 and at 4, short two at 86 and at 90,
and long one at 172 and at 174. No three of these strikes form a butterfly, so named
spreads and three-leg spreads cannot reach zero. The uneven condors 2/86/90/174, with wings
of 84, and 4/86/90/172, with wings of 82, have no loss, and they cover the position. The
condor instance closes that gap by putting the two shorts of a condor at two different
scales.

### Theorem 3: one maximum-loss group

**The rule.** The solver's model (spec §2 and §3.1): choose whole contracts for one
balanced group. The requirement is the group's maximum loss plus `U_K` for each short
contract left out. Items 2 and 3 show this is the least requirement over every way of
forming spreads under R2. In this theorem the `U_K` are free inputs, as the standalone
costs of the general model are.

**Subset sum.** Given positive integers `a_1 … a_n` and `T`: do some of the `a_i` sum to
`T`? This is NP-complete (Garey and Johnson, problem SP13). A number above `T` cannot be
used and is dropped, and if a number equals `T` the answer is yes. So take every
`a_i < T`.

**Theorem 3.** Deciding whether the one-group minimum is at most a given bound is
NP-complete, already for calls of one expiration and one deliverable.

**Reduction.** Pick a strike `K_top > T`. The position is

    long one call at  K_low = K_top − T
    long n calls at   K_top
    short one call at K_i = K_top − a_i,  with U = a_i / 2,  for each i

and the bound is `R = (Σa − T) / 2`.

**Proof.** A group is a set `A` of the shorts, `l ∈ {0, 1}` of the low long, and `|A| − l`
of the top longs. Write `a(A)` for the sum of its numbers. Its payoff is zero at its lowest
strike. From there up to `K_top` only the low long and the shorts have intrinsic value: the
slope starts at `l` and drops by one at each short strike, so the payoff is concave and its
least value over the strikes is at an end. At the top it is `l·T − a(A)`, by the lemma. So
the maximum loss is `max(0, a(A) − l·T)`, and the requirement is

    f(A, l) = (Σa − a(A)) / 2 + max(0, a(A) − l·T).

- `l = 0`: `f = (Σa + a(A)) / 2 ≥ Σa / 2 > R`.
- `l = 1` and `a(A) ≤ T`: `f = (Σa − a(A)) / 2 ≥ R`, with equality exactly when `a(A) = T`.
- `l = 1` and `a(A) > T`: `f = (Σa + a(A)) / 2 − T > R`.

So the minimum is `R` when some subset sums to `T`, and above `R` otherwise. The problem is
in NP because a group is a certificate. ∎

### Theorem 4: the same with every short priced by R3

Theorem 3 sets the standalone costs freely. The rule does not: R3 ties them to prices. The
reduction survives that.

**k-subset sum.** Given positive integers `a_1 … a_n`, a count `k` and a target `T`: do
exactly `k` of the numbers sum to `T`? This is NP-complete. Subset sum reduces to it:
replace each `a_i` by `(n + 1)a_i + 1`, add `n` numbers equal to 1, and ask for `n` numbers
that sum to `(n + 1)T + n`. Take `2 ≤ k ≤ n` and `T ≤ Σ`, where `Σ = Σa`; the other cases
are answered by inspection.

**Theorem 4.** The one-group problem stays NP-hard when the market data are call prices
free of arbitrage and every uncovered requirement is computed by R3 at stock rates.

**Reduction.** Let `shift = 8Σ`, `v_i = a_i + shift`, `V = T + k·shift`, `β = 1/(2k)` and
`π = 1`. Set the underlying at `S = 2(π + βV)`, pick `K_low ≥ 1.1 S`, and let
`K_top = K_low + V`. The call at strike `K` is priced at `C(K) = π + β(K_top − K)`. The
position is

    long one call at  K_low
    long n calls at   K_top
    short one call at K_i = K_top − v_i    for each i

and the bound is `R = Σ_i U_i − (c·k + βV)`, with `c = π + S/10`. Then:

- *Strikes.* `K_low < K_i < K_top`, since `k ≥ 2` and `shift > a_i` give `v_i < V`.
- *Prices.* `C` is linear and falls by `β < 1` per point of strike. `C(K_top) = π > 0` and
  `C(K_low) = S/2 < S`. Every strike is above `S`, so the lower bound `S − K` is negative.
  The prices are decreasing, convex and within the no-arbitrage bounds.
- *R3.* Every strike is at least 10% out of the money, so 20% of the underlying less the
  out-of-the-money amount is at most the 10% floor, and `U_i = C(K_i) + S/10 = c + β v_i`.
- *(I1)* `shift > Σ`.
- *(I2)* `(1 − β)(shift − T) > c`. The left side is at least `(3/4)(7Σ)`, and
  `c = 1.2π + T/(10k) + shift/10 < 2.1Σ`.

**Proof.** As in Theorem 3, a group is `(A, l)` with maximum loss `max(0, v(A) − l·V)`. It
saves, against leaving every short uncovered,

    g(A, l) = c|A| + β v(A) − max(0, v(A) − l·V),

and the minimum requirement is `Σ_i U_i − max g`. The claim is that `g ≤ c·k + βV`, with
equality exactly when `l = 1`, `|A| = k` and `a(A) = T`. Write `j = |A|`, so
`v(A) = j·shift + a(A)`.

- `l = 0`: `g = Σ_{i∈A} (c − (1 − β) v_i) ≤ 0`, because `(1 − β) v_i > c` by (I2).
- `l = 1`, `j < k`: `v(A) < (j + 1)·shift ≤ V` by (I1), so there is no loss, and
  `g ≤ c(k − 1) + β(k·shift) < c·k + βV`.
- `l = 1`, `j = k`: `v(A) − V = a(A) − T`. If `a(A) ≤ T`, `g = c·k + βV − β(T − a(A))`. If
  `a(A) > T`, `g = c·k + βV − (1 − β)(a(A) − T)`. Either way `g ≤ c·k + βV`, with equality
  exactly when `a(A) = T`.
- `l = 1`, `j > k`: `v(A) − V ≥ (j − k)(shift − T) > 0`, so
  `g ≤ c·j + βV − (1 − β)(j − k)(shift − T) < c·k + βV` by (I2).

So the minimum is `R` when `k` of the numbers sum to `T`, and above `R` otherwise. Every
number has polynomially many digits, and multiplying strikes and prices by `2k` makes them
whole. ∎

These prices obey the rules but are not a realistic chain: a linear price curve, and every
strike at least 10% out of the money.

### Proposition 5: butterflies and condors on adjacent strikes only

Theorem 1's butterflies are about `M` wide, and no two matched triples need share a width.
Take that away and the strong hardness goes with it.

**Proposition 5.** Let the strikes lie on an evenly spaced grid of `h` points. Let the
named spreads be the verticals between any two strikes, and the butterflies and condors on
consecutive grid points only. Debit spreads require nothing, a bear spread its width, and
a short butterfly or condor one grid interval, or in each case the lesser of that and the
uncovered requirement of the shorts. Then the minimum requirement of a position of `N`
call contracts can be found in time polynomial in `h` and `N`.

**Proof.** Walk the grid upward. Contracts at one strike are alike, so a pairing matters
only through how many spreads of each kind begin at each strike. After a strike, the
spreads begun and not finished are:

- bull spreads waiting for their short: one count;
- bear spreads waiting for their long: one count. Each costs one grid interval for every
  step it waits, because a bear spread's requirement is its width. Under the lesser-of
  clause a bear spread wider than the uncovered requirement of its short is never needed,
  since leaving that short uncovered costs the same;
- butterflies and condors begun at most three points back: ten counts, by kind (long or
  short, butterfly or condor) and by the legs still owed.

These twelve counts, each at most `N`, fix what the rest of the walk can do and what it
will cost. A butterfly or condor is charged when it begins. So there are at most
`h (N + 1)^12` states, each with at most `(N + 1)^4` successors, and keeping the least cost
for each state gives the minimum. ∎

The bound is far from practical. It is here for what it rules out: a problem with such an
algorithm is not NP-hard in the strong sense unless P = NP, so Theorem 1 does not extend to
this reading. Whether this version can be solved in time polynomial in the digits of the
quantities is open. The same walk should handle puts and the two-sided main spreads on
consecutive strikes, which add counts of the same kind; that is not written out or
checked.

### What the results say

- **Limits on the shape of a spread are what make pairing hard in the strong sense.** With
  at most three or four legs a spread, the problem is hard even when the strike grid has
  polynomially many points and the position holds `4n` contracts. On the same butterfly
  instances the whole position is one spread with no loss whenever the total is right,
  matching or not (checked below), so under the one-group rule they are trivial. For the
  named spreads, the hardness also needs butterflies of many widths (Proposition 5).
- **One group is hard only through large numbers.** Take the scope of the strike dynamic
  program above: options of one expiration and deliverable, no stock, no straddle
  templates. Keeping the cheapest cost for each state `(C, P', X, Y)` is exact there, and
  there are at most `m (2N_c + 1)(2N_p + 1) R²` states, which is polynomial in the
  contracts held and in the strike range over the tick. So in that scope the one-group
  problem is not NP-hard in the strong sense unless P = NP, and Theorems 3 and 4 are as
  strong as a hardness result for it can be. Their hard instances need a strike range that
  grows faster than any polynomial in the number of positions. A listed chain has a fixed
  range, and there the dynamic program's time is polynomial in the contracts held. This
  answers spec §3.4 item 2: the dynamic program is pseudo-polynomial, and no exact method
  is polynomial in the digits of the strikes unless P = NP.
- **What stays polynomial.**
  - Continuous quantities: a linear program (spec §2).
  - Two-leg spreads alone: a network flow problem (Rudd and Schroeder 1982, as Matsypura
    and Timkovsky report it; the paper itself is unread).
  - A portfolio already split into two-leg basic spreads on one uniform exercise domain:
    a maximum flow (Matsypura and Timkovsky 04/2010, Theorem 6 with Section 6).
  - A fixed number of series, whatever the quantities, under the named-spread rule or the
    one-group rule: integer programming with a fixed number of variables (Lenstra 1983).
- **Not settled here.**
  - Whether the adjacent-strike reading of Proposition 5 is polynomial in the digits of
    the quantities.
  - Whether the one-group problem with several expirations or deliverables is NP-hard in
    the strong sense. The dynamic program covers one of each.
  - Leg limits of five or more.
  - How these results sit beside Chen and Li's. Their conference abstract (2015) reports an
    integer margin model, "based on the strategy-based approach and vector model", that is
    equivalent to a linear program. If that model were the rule of Theorem 1 or of
    Theorem 2, P would equal NP, so it is a different rule. The paper is unread, and how it
    differs is not known here (sources.md).
- **None of this is about typical books.** The results are worst cases. The benchmarks
  (benchmarks.md) show branch-and-bound solving retail and market-maker books quickly, and
  nothing here contradicts that.

### Checks

`python3 tools/check_hardness.py` (about half a minute; `--quick` takes a second) builds
random small instances, solves the source problem and the margin problem by exhaustive
search, and compares. It enumerates spreads and evaluates losses from intrinsic values, so
it does not lean on the lemma or on the case analyses above. Every check on named or
leg-limited spreads runs with and without the lesser-of clause. A quarter of the matching
instances are not planted, so that sizes above the bound occur.

| Check | Instances | Agree |
|---|---|---|
| Theorem 1: named spreads reach zero exactly when the matching exists (`n` = 2 to 5) | 491 yes, 509 no | all |
| The whole butterfly position has no loss as one spread, when the total is right | 904 | all |
| Theorem 2, at most 3 legs (`n` = 2 to 4) | 262 yes, 238 no | all |
| Theorem 2, at most 4 legs (`n` = 2 to 4) | 263 yes, 237 no | all |
| Theorem 2's condor instance under the named list with equal-wing condors | the same 500 | all |
| Theorem 3: the minimum equals `R` exactly when a subset sums to `T` (up to 9 numbers) | 1,204 yes, 617 no | all |
| Theorem 4, shorts priced by R3 (3 to 8 numbers) | 897 yes, 603 no | all |
| Proposition 5: the dynamic program against the search over every pairing (3 to 8 grid points, up to 3 contracts a strike) | 600 | all |

It also checks both examples above and that the named spreads' requirements match the
legacy figures and two uneven butterflies from the Cboe manual (pp. 37 and 54).

`lean/` proves Theorems 1 and 2 in Lean 4 with Mathlib (`lake build` in that folder; see
its README for the statements). For every instance of numerical 3-dimensional matching it
proves that the butterfly instance has a zero pairing into named spreads exactly when a
matching exists (`N3DM.theorem1`), the same for spreads of at most three or four legs
priced by their maximum loss on the butterfly and condor instances (`N3DM.theorem2_three`,
`N3DM.theorem2_four`), and that both instances have `4n` contracts at strikes polynomial in
`n` and `W` (`N3DM.butterfly_size`, `N3DM.condor_size`). The Lean proofs follow the
arguments above and found no gap.

The `solver` test `subset_sum_reduction` builds Theorem 4's instance for 120 random
`k`-subset-sum instances of 3 to 8 numbers (71 yes, 49 no), with the numbers scaled by
`2k` so that prices are whole cents. The exact branch-and-bound total equals `R` plus the
long premiums exactly when the subset exists, and is above it otherwise. The strike dynamic
program gives the same total on all 120. The requirement there comes from the Phase 1
engine, not from this file's formulas.
