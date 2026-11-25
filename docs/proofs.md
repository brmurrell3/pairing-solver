# Proofs for spec §3.1

Plan Phase 4 asks for written proofs of spec §3.1 items 1, 2, 4 and 5. They are below,
with items 3 and 6, which the others lean on. The rule references are to
[rules.md](rules.md). `tools/check_structure.py` and the `unit` test check items 1, 4 and 5
numerically.

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
58,601 to 1,765 columns and from 153 s to 17.7 s.
