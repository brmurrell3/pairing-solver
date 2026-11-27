# Plan

**Current status (2026-11-26):** Phases 0 to 3 done. Phase 4: the proofs, the integrality counterexamples, the dynamic program and the hardness results are written (proofs.md); what is still open is listed under Phase 4. Phase 5: the code is public. Phase 6 (pre-trade speed) done 2026-11-26: every order on a 1,000-series book in under 50 ms on the Mac.

## Decisions

- **Language (2026-11-25):** C++20 core behind a small C interface. Java calls it through the Foreign Function & Memory API; Python through ctypes for analysis.
- **Solver (2026-11-25):** the project writes its own solver (spec §3.4). HiGHS is used only in tests, as an independent oracle, and is never shipped.

## Phase 0: specification (done 2026-11-25)

- **Docs:** spec, rules catalog with paragraph citations, and sources with their access status.
- **Fixtures:** eight Cboe worked examples in `data/fixtures/cboe_manual.toml`. An independent script recomputed every netted value, maximum loss, requirement and validity flag, and all eight match.
- **Structure checks:** the strike-walk payoff formula, exact evaluation at strikes, and the suffix pairing condition held on 3,000 random portfolios (spec §3.1).
- **Checks to rerun:** `tools/check_fixtures.py` and `tools/check_structure.py` (commands in CLAUDE.md).

## Inputs still open

1. **Q1 in rules.md:** where the recollection of two-decimal partial contracts comes from. The grid is a policy until this is answered.
2. **Papers:** the three Matsypura and Timkovsky papers are in `refs/` and read (2026-11-26; sources.md). Rudd and Schroeder (1982) is still missing: paywalled, needs a library copy.
3. **Toolchain:** compiler and TOML parser confirmed 2026-11-25 (Apple clang 21, CMake 4.4, toml++ 3.4.0 from Homebrew). No test framework is installed; Phase 1 uses a small harness in `tests/check.hpp`. Still open: HiGHS as a test-only dependency (Phase 2).

## Phase 1: rule engine (done 2026-11-25)

Compute requirements; no optimization yet.

- **Types:**
  - instrument, position and market data;
  - a rule set loaded from TOML (rates, minimums, policies).
- **Functions:**
  - requirements: uncovered short, long option (including beyond nine months), straddle, covered call and put;
  - hedged-underlying minimums: protective put, conversion, reverse conversion, collar, European long box;
  - stock requirements;
  - spreads: maximum loss by the strike walk, and validity under each `expiry_rule` by the suffix condition.

**Done when** every fixture passes to the cent, including the manual's remaining sample calculations once transcribed.

**Evidence:** `ctest` passes 3 of 3 (commands in CLAUDE.md): `unit` (10 groups, 812,690 checks, including the strike walk against direct evaluation on 2,000 random portfolios and the suffix condition against max-flow on 3,000), `cboe_manual` (8 cases) and `cboe_manual_samples` (53 cases). Every figure matches exactly.

- **Money:** integer millionths of a dollar with 128-bit intermediates, so results are exact and deterministic and the tests compare without tolerance.
- **Rule questions:** Q3 was answered by the manual's numbers. Phase 1 found Q8 to Q12 (rules.md).
- **Review (2026-11-25):** clean out-of-tree build, 3 of 3 suites pass with no warnings. Two samples (short-call-otm, collar) were rechecked by hand against the manual text.
- **Not implemented:** uncovered OTC shorts ((f)(2)(E)(iii)), maintenance on a short index call against a long ETF, `european_calendars = surcharged`, and fractional contracts.

## Phase 2: exact solver

**Status (2026-11-25, done; see Evidence below):**
- **Built:** model builder, checker, dense dual simplex and branch-and-bound (`src/simplex.cpp`, `src/solver.cpp`, `src/checker.cpp`).
- **The crash:** during development, a branch-and-bound bug (branching up on a bound below 1 produced lower > upper, which the simplex accepted as optimal) made every node re-branch the same column. Six orphaned debug runs of it exhausted memory and panicked the Mac. The bug is fixed: `simplex.cpp` rejects lower > upper as infeasible, and branch-and-bound skips empty branches. See CLAUDE.md, "Running code safely".
- **Items closed 2026-11-25:**
  1. **Node limit:** `MipOptions::node_limit` (default 1,000,000; `SolveOptions::node_limit` 200,000, lowered to 20,000 in Phase 6). A hit returns `MipStatus::node_limit` with the best assignment and a proven bound (`Solution::status`, `bound`, `proven_gap`).
  2. **HiGHS export:** `HighsSparseMatrix` already holds the leading 0 of `start_`; the test pushed a second, so HiGHS rejected every model. HiGHS also reports 0, not the offset, for a model with no columns.
  3. **Speed.** Four changes, measured on the HiGHS test:
     - *Share-size congruences.* With 100-, 150- and 10-share series in one balance row, whole-lot balance needs congruences the LP cannot see (net 150-share calls against 100-share calls come in pairs). Branching found that infeasibility only at the bottom of deep subtrees: one 21-series case ran 200,000 nodes without finding any pairing, and setting every deliverable to 100 solved it at the root. Each share size now gets an integer column for its net lots divided by its modulus, branched on first (`aggregates` in `src/solver.cpp`). 30 test cases went from 58 s to 0.02 s. A full lattice basis instead was 2.8 times slower on 1,000 cases.
     - *Search.* A rounding dive with limited backtracking gives a first incumbent at the root and every 64 nodes. The search is best-first with plunging, and nodes store only their bound changes. Pruning uses `SolveOptions::rel_gap` (default 1%, relative to the bound).
     - *Simplex pricing.* Dual steepest edge, exact from the dense inverse, cut the 100-series root LP from 27,476 to 1,750 iterations.
     - *Simplex stalls.* Reduced costs within rounding noise of zero could flip each other's bounds forever, and on degenerate models steps could cycle with no rise in the objective. The flip threshold now widens on repeated optimality checks, and a stall perturbs the costs, then restores them at the perturbed optimum.
  4. **Sanitizers:** an AddressSanitizer and UndefinedBehaviorSanitizer build (commands in CLAUDE.md) passes `unit`, `cboe_manual`, `cboe_manual_samples`, `solver`, `exhaustive` and 100 HiGHS cases, with no reports.
  5. **Trace code:** `BB_TRACE` and `PAIRING_TRACE` removed.
  6. **Long box:** `solver` checks that the model offers a European long box as a template, and that the solve is never worse than the box alone.
- **Found on the way:** the model prices a group at its maximum loss, while Phase 1 prices a spread at the lesser of that and the shorts' uncovered requirement (R2). The two agree wherever pairing pays, so always at the optimum. An assignment accepted within the gap can be priced lower by the checker. The checker's total is reported, and the consistency check now requires only that the model is never below it (and equal when exact).

- **Subproblems:** build them per (account, underlying), with strike-walk loss rows, balance equalities, suffix pairing inequalities, templates and residuals.
- **Algorithms:**
  - a dense bounded-variable dual simplex for the continuous problem;
  - branch-and-bound for grid quantities.
- **Checking:**
  - an independent checker re-derives every structure's validity and requirement with the Phase 1 engine;
  - exhaustive search on small portfolios;
  - differential tests against HiGHS on random portfolios.

**Target decision (2026-11-25, owner):** HiGHS stays the reference. On large portfolios, a requirement slightly above HiGHS's optimum is acceptable in exchange for large speed gains, so branch-and-bound may stop at a relative gap instead of proving optimality. Correctness is tested on many small portfolios and performance on a few large ones. The owner asked the agent to set the values below by judgment; each is marked *(agent's choice)* and is open to revision.

**Done when:**
- **Small, correctness:** the solver matches exhaustive search on at least 1,000 random portfolios of up to 8 positions under every policy. These stay exact: no gap tolerance applies. *(agent's choice)*
- **HiGHS reference:** HiGHS runs with `mip_rel_gap = 0`, so its value is a proven optimum. On at least 1,000 random portfolios of up to 40 series, the solver's requirement is at most 1% above HiGHS's value per case, and never below it by more than 1e-9 relative (a lower value means a bug or an invalid pairing). *(agent's choice: 1% tolerance, 1,000 cases, 40 series)*
- **Large, performance:** five fixed-seed portfolios of 50, 100, 150, 200 and 200 series each finish in at most 30 s under `tools/run_guarded.sh -m 4096`, within the same 1% of HiGHS, with time and gap reported. They run under a budget of 3,000 nodes; a stop at that budget passes if the answer is still within 1%. *(agent's choice: five cases, 30 s each, 3,000 nodes)*
- The checker accepts every solution.

Superseded criterion: match HiGHS to 1e-9 relative on at least 10,000 random portfolios of up to 200 series.

**Evidence (2026-11-25):** `tools/run_guarded.sh -m 4096 -t 1200 -- ctest --test-dir build --output-on-failure` passes 7 of 7 in 510 s. These runs were on Linux (g++ 13.3, HiGHS 1.16.0 built from source); they have not yet been repeated on the Mac with Apple clang.
- `exhaustive`: 3,000 portfolios (1,000 per `expiry_rule`) match brute force exactly, in 4.6 s.
- `highs` (`pairing_highs_tests 1000 40`): 1,000 portfolios, 20,334 series, 100 of them on a 1/10 grid. The LP agrees with HiGHS to 9e-15. The whole-lot result is at most 0.999% above HiGHS's optimum, never below it, and none stopped at the node limit. Ours took 17 s in all (slowest case 7 s); HiGHS took 139 s.
- `highs_large` (`pairing_highs_tests large`):

  | Series | Model (rows x columns) | Ours | Above HiGHS | HiGHS |
  |---|---|---|---|---|
  | 50 | 101 x 218 | 0.17 s, optimal within 1% | 0.33% | 0.03 s |
  | 100 | 294 x 829 | 10.7 s, stopped at 3,000 nodes | 0.91% | 172 s |
  | 150 | 307 x 1,378 | 0.35 s, optimal within 1% | 0.48% | 6.4 s |
  | 200 | 273 x 2,184 | 0.98 s, optimal within 1% | 0.15% | 0.71 s |
  | 200 | 442 x 2,084 | 5.0 s, optimal within 1% | 0.27% | 162 s |

  The 100-series case is the weak one. Its LP bound is 0.41% below the optimum, and the search's best answer within the budget is 0.91% above it, so it passes with little margin. Better incumbents there (stronger dives or local search) are Phase 4 work.

## Phase 3: baselines and benchmarks

- **Greedy baseline:** fixed template priority, nearest strikes first. It stands in for common production practice.
- **Generators:** the portfolio generators in `data/README.md`, with fixed seeds.
- **Measurements:**
  - savings against greedy;
  - the gap between the continuous and whole-contract solves;
  - solve time per subproblem from 10 to 1,000 series;
  - accounts per second in a batch, with and without warm starts;
  - all of the above against HiGHS on the same subproblems.

**Done when** one command regenerates every table from fixed seeds.

**Status (2026-11-25, done):** `tools/run_guarded.sh -m 4096 -t 3000 -- build/pairing_bench > docs/benchmarks.md` regenerates all five tables in about 8 minutes (Linux, g++ 13.3, HiGHS 1.16). `pairing_bench <table>` runs one table: `savings`, `integrality`, `timing`, `batch` or `highs`.
- **Greedy** (`src/greedy.cpp`): verticals and calendars by nearest strike, costliest shorts first, merged into iron condors where Phase 1 prices them lower; then straddles; then covered and protective stock. The `solver` test checks it never beats the exact solve on 600 random books. Two choices made it stronger than a naive version, measured as greedy's mean excess on retail books. The condor merge brought it from 11.1% to 6.9%, and covering the costliest shorts first (instead of index order) brought it to 5.4%.
- **Generators** (`bench/books.hpp`): retail, market maker, adjusted series and adversarial, described in `data/README.md`.
- **Results** (docs/benchmarks.md):
  - The solver saves 57.9% of the standalone requirement on retail books, against 55.4% for greedy. Greedy's excess averages 5.4% (median 0) on retail, 15.5% with adjusted series, 10.8% on market-maker books and 37.5% on the adversarial set.
  - The continuous optimum is already whole for 456 of 496 retail books. With adjusted series, only 232 of 496 are whole, and the mean gap is 3.0% (largest 39%).
  - Market-maker books solve at the root up to 300 series (median 1.8 s). One 1,000-series book took 153 s: its model had 58,601 columns, 57,600 of them short straddle templates, which grow as short puts × short calls, and its root LP took about 107,000 iterations in the dense simplex. The compact straddle form (Phase 4) brought it to 1,765 columns and 18.0 s.
  - Warm-starting each account from the previous account's root basis cuts root iterations 5 to 8 times and raises throughput 1.5 to 2 times (100 series: 23 to 47 accounts per second).
  - On retail books and market-maker books of up to 100 series, the solver is 2.5 to 25 times faster than HiGHS at the median, and on average 0.004% to 0.02% above its optimum.
- **Not covered:** HiGHS is not timed at 300 and 1,000 series or in batches. Real chains (`data/private/`) are not benchmarked.
- **For Phase 4:** the 1,000-series case points at two things: pruning dominated straddle templates (or generating them as needed), and a sparse or structured method in place of the dense inverse.

## Phase 4: structured algorithm and theory

- **Proofs:** write up spec §3.1 items 1, 2, 4 and 5.
- **Algorithm:** dynamic programming over the strike walk for whole contracts; establish its complexity and benchmark it against the Phase 2 solver and HiGHS.
- **Integrality:** when is the continuous solution already whole-contract? Find counterexamples where it is not.
- **Template-only policies:** hardness, or a cited result, for butterfly and condor templates. Check against Matsypura and Timkovsky first.

**Done when** each claim has a proof or a cited result, and the benchmarks say where each algorithm wins.

**Status (2026-11-25, in progress):**
- **Proofs:** written in [proofs.md](proofs.md) for items 1, 2 (with the cut-date argument for the stricter readings), 4 and 5, and short ones for items 3 and 6.
- **Integrality:** the `solver` test keeps two counterexamples: three calls on one deliverable (gap 0.67%) and a one-lot iron condor (0.37%). No 2-series book of 78,000 searched had a gap. No sufficient condition beyond two series yet (proofs.md, "Integrality").
- **Straddles:** done. Above 256 short put-call pairs, the model uses one cheap and one dear column per short and suffix rows instead of one template per pair (proofs.md, "Compact short straddles"). The `solver` test `compact_straddles` checks equal totals against the per-pair form on 400 random books. The 1,000-series book went from 58,601 to 1,765 columns and from 153 s to 18.0 s; 300 series from 1.8 s to 0.73 s median. Below the threshold the per-pair form stays, because the compact form slowed small books (the 1,000 x 40 HiGHS run took 40 s instead of 18 s with it everywhere).
- **Dynamic program:** done for one max-loss group: one expiration, style, listing and deliverable, options only, no straddles (`solve_strike_dp`, `src/dp.cpp`; proofs.md, "Strike dynamic program"). It is exact and pseudo-polynomial, `O(m · N_c N_p · R² · q²)` states with `R` the payoff range over the tick. The `solver` test `strike_dp` matches exact branch-and-bound with straddles off on 1,500 random books. It is slower everywhere measured (benchmarks.md, "Strike dynamic program"): 82 ms median against 0.09 ms at 10 series of up to 50 contracts, and at 100 series it hits its 5,000,000-state limit on every book while branch-and-bound takes 9 to 50 ms. Branch-and-bound stays the solver; the DP is kept as an independent exact check. Multiple expirations, straddles and stock are not in the DP, since each adds a state dimension per expiration or per rank.
- **Hardness (done 2026-11-26):** proved in proofs.md, "Hardness". No cited result was found: Matsypura and Timkovsky (05/2010, Introduction; 04/2010, concluding remarks) state that the complexity with three- and four-leg spreads on individual options is unknown, and give only a heuristic and a polynomial method for portfolios already split into two-leg spreads (sources.md).
  - **Template-only pairing** is NP-hard in the strong sense, by reduction from numerical 3-dimensional matching: with the legacy named spreads when butterflies and condors may have equal intervals of any width (Theorem 1), and with maximum-loss spreads of at most three or at most four legs (Theorem 2).
  - **Adjacent strikes only:** if butterflies and condors count only on consecutive strikes of one evenly spaced grid, a dynamic program runs in time polynomial in the grid length and the contracts held, so that reading is not NP-hard in the strong sense unless P = NP (Proposition 5).
  - **The one-group problem** is NP-hard by reduction from subset sum (Theorem 3), also when every short is priced by R3 from arbitrage-free call prices (Theorem 4). With one expiration it is hard only in the weak sense, because the strike dynamic program is pseudo-polynomial. This settles spec §3.4 item 2.
  - **Evidence:** `python3 tools/check_hardness.py` compares each reduction with exhaustive search, with and without the lesser-of clause: 1,000 instances for Theorem 1, 500 for each case of Theorem 2, 1,821 for Theorem 3, 1,500 for Theorem 4 and 600 positions for Proposition 5, all in agreement (about half a minute). The `solver` test `subset_sum_reduction` checks Theorem 4 on 120 instances against exact branch-and-bound and the strike dynamic program (the `solver` suite then has 9 cases and 20,723 checks, 0 failed).
  - **Machine-checked (2026-11-26):** Theorems 1 to 4 in Lean 4.36.0 with Mathlib v4.36.0 (`lean/`, README there). Proved for every instance: each reduction is correct in both directions (`N3DM.theorem1`, `N3DM.theorem2_three`, `N3DM.theorem2_four`, `SubsetSumInstance.theorem3`, `KSubsetSumInstance.theorem4`, and `subsetSum_iff_kSubsetSum` for the step to `k`-subset sum), its output size is bounded (`4n` contracts at strikes at most `2M + 2W` or `(2n + 3)M + W`; `2n + 1` contracts for Theorems 3 and 4), and Theorem 4's prices are free of arbitrage and its requirements are R3's. `lake build --wfail` passes with no warnings, `lake env lean AxiomCheck.lean` shows only `propext`, `Classical.choice` and `Quot.sound`, and the Lean CI job (`.github/workflows/lean.yml`) runs both; its first run passed in 3 minutes. Formalizing found no gap in the paper proofs. Not formalized: the source problems' NP-completeness (cited, Garey and Johnson SP13 and SP16; Mathlib has no complexity classes), the polynomial running time of the reductions, membership in NP, and Proposition 5 (a sketched dynamic program; its transitions would need writing out first).
  - **Assumptions:**
    1. "The butterfly case" is read as Matsypura and Timkovsky's question: named spreads of two to four legs on individual options. Butterflies and condors need equal intervals, of any width. No text of NYSE Rule 431(f)(2)(C) is in `refs/`. The reading comes from their use of the rule (05/2010, Sections 2 and 4) and agrees with the NASD's butterfly definition in Notice to Members 01-11, which asks only for equal intervals. That notice was read through a subagent's report (sources.md); put it in `refs/` and read it directly before leaning on it. The narrower reading, adjacent strikes of one grid only, is Proposition 5.
    2. A condor needs all three intervals equal (their Table 2, and the definition deleted from FINRA Rule 4210 as reported in sources.md). If only its wings had to be equal, Theorem 2's condor instance gives the same result.
    3. The objective is the requirement net of long premiums (their "market risk"), because a long is paid in full under every pairing at nine months or less.
    4. Whole contracts, and a positive uncovered requirement for every short.
    5. Theorem 3 takes standalone costs as free inputs, as the general model (spec §2) does. Theorem 4 uses R3 at stock rates with call prices linear in the strike and every strike at least 10% out of the money. Those prices are within the rules and free of static arbitrage, but they are not a realistic chain.
    6. "Strong" and "weak" are Garey and Johnson's terms. Their book (problems SP13 and SP16) and Lenstra (1983) are cited from memory, not from a copy in `refs/`.
    7. "No cited result" means none in what was checked on 2026-11-26: the three papers in `refs/`; through a subagent's reports, the second ICORES 2012 paper, Coffman, Matsypura and Timkovsky (2009), the abstract and reference list of the 2013 paper and the conference abstract of Chen and Li; and web searches. Rudd and Schroeder (1982) and Chen and Li's paper are unread. Chen and Li's abstract reports an integer margin model equivalent to a linear program. That cannot be the rule of Theorem 1 or 2 unless P = NP, and how it differs is not known (sources.md).
    8. The constants in the constructions are sufficient, not tight (agent's choice): `M = 6nW`, `p = n + 1`, `q = n + 2`, `shift = 8Σ`, `β = 1/(2k)`, `π = 1`.
    9. Check sizes and seeds are the agent's choice: seed 20261126 with up to 5 triples and up to 9 numbers in the script, seed 5,175,000 with 120 instances in the test.
    10. Lean modeling choices (agent's choice): Theorem 4 is stated in units of `1/(2k)` with `K_low = 2S`, one admissible value of the paper's `K_low ≥ 1.1 S`; strikes are integers in ticks; a spread is two multisets of strikes, one entry per contract; R2's maximum loss is taken at the members' strikes; legs are distinct strikes; requirements are abstract, nonnegative, zero exactly for debit spreads (Theorem 1) or exactly when the maximum loss is zero (Theorem 2), with a positive requirement per uncovered short; a matching is a multiset of triples whose projections are `A`, `B` and `C`.
- **Open:** whether the one-group problem with several expirations or deliverables is NP-hard in the strong sense; whether the adjacent-strike reading is polynomial in the digits of the quantities; leg limits of five or more.

## Phase 5: publish

- **Code:** a public repository with the clean-room note, after checking the employer's outside-activity and IP policy. Done 2026-11-26: https://github.com/brmurrell3/pairing-solver, releases v1.0.0 and v1.1.0 (Phase 6 speed, `Book`, hardness results). CI (`.github/workflows/ci.yml`) builds and runs the five non-HiGHS tests and both Python checks on Ubuntu 24.04 (GCC) and macOS (Clang); first run green in under a minute per job. Assumptions: "published version" is a tagged GitHub release with no package registry (owner, 2026-11-26); CI skips the HiGHS tests (about 9 minutes) because HiGHS is not installed there, so they stay a local gate.
- **Write-up:** a project page on brendanmurrell.com covering the formulation, the proofs and the benchmark results.
- **Resume:** a project line on the resume.

## Phase 6: pre-trade check speed

**Why (owner, 2026-11-26):** the solver runs before every order is routed, on automated books of about 1,000 positions, so it must be near realtime. The 18 s for a 1,000-series book is unacceptable. Up to 1% above HiGHS per case is still acceptable in exchange for speed, and HiGHS stays the reference.

**Target** *(agent's choice, open to revision)*: on the owner's Mac (M3 Max), price one order against a solved 1,000-position book in under **50 ms at p99**, and solve a 1,000-position book cold in under **1 s**, with every answer within 1% of HiGHS. The per-order number is the one that matters; the cold solve happens once, when a book is loaded.

**Measured first (2026-11-26, Mac):** the earlier Linux figures did not hold. The generators used the standard library's distributions, which libc++ and libstdc++ implement differently, so the Mac ran a different case set, and on it the 1,000-case HiGHS test failed: ours 175 s against HiGHS's 46 s, 2 node-limit stops, and one large case 70% above HiGHS. The 1,000-series book took 30 s: 6.8 s root LP, then 24 s in 446 dense refactorizations during the rounding dive.

**Done (commits 925313f to dbf13ba):**
- *Simplex:* refactor at an optimality check only after 32 updates or a failed first check; steepest-edge norms kept through the inverse's row updates; refactorization keeps B column-major with a pivot permutation instead of row swaps, logicals first (43 to about 5 ms at 1,182 rows); capacity rows that one column alone uses are dropped (453 of 1,527 rows); the pivot row is formed row-wise from rho's nonzeros; bound changes update the primal values incrementally; dense dot products and row updates use four independent sums so they vectorize.
- *Dive:* the root dive first holds every on-grid integer column and rounds only the fractional ones (about 12 LP solves instead of 300 to 450), then holds only columns at a bound, then (given a guide) holds the columns where the LP agrees with the previous pairing, then holds nothing; the last is skipped when a passed-in incumbent already meets the gap.
- *Model build and checker:* build 85 to 5.8 ms at 1,000 series, mostly by not asking Phase 1 about pairs it always rejects (its rejections are exceptions); the checker's duplicate-leg test 6 to 0.2 ms.
- *Book (`include/pairing/solver.hpp`):* keeps one subproblem solved. A resize updates the bounds that depend on the position's size in place (no model rebuild) and re-solves on the book's own simplex, basis, inverse and pairing. A close holds the position's columns at 0 on the same model and takes its standalone requirement off. Other orders (new series, sign flips, first stock) build a new model started from the book's basis and pairing, matched by row and column keys.
- *Node limit:* `SolveOptions::node_limit` default 200,000 to 20,000. The cases that reach it have weak bounds under `nearest_long` (overlapping groups), not bad answers.
- *Portable generators* (`tests/generate.hpp`): seeded books are now the same on every platform. They exposed a pruning bug in the strike DP (fixed, ab6dea7; proofs.md corrected, 7f981c9).
- *HiGHS test:* a node-limit stop passes if the answer is within the gap of HiGHS (assumption: the Phase 2 criterion is quality, not proof).

**Evidence (2026-11-26, Mac):** `ctest -E highs` passes 5 of 5, also under AddressSanitizer and UndefinedBehaviorSanitizer; the `solver` group `book_orders` checks `what_if` and `fill` against exact cold solves on 300 random books, through every path. `pairing_highs_tests 1000 40`: 0 failures, LP within 1e-15 of HiGHS, at most 0.996% above it, 3 stops at the node limit; ours 4.5 s, HiGHS 28 s. `pairing_highs_tests large`: all five within 0.93%, slowest 0.26 s (HiGHS up to 28 s). docs/benchmarks.md was regenerated in full on the Mac with the portable books, so its tables no longer match the Linux figures quoted under Phase 3.

  | 1,000-series book | Start of Phase 6 (Mac) | Now |
  |---|---|---|
  | Cold solve | 30 s | 0.42 s |
  | Order, resize (200): median / p90 / p99 / max | 3.7 s (cold) | 10.5 / 18 / 23 / 26 ms |
  | Order, new series (20): median / p90 / max | 3.7 s | 19.5 / 20 / 23 ms |
  | Order, close (20): median / p90 / max | 3.7 s | 12 / 20 / 22 ms |

  At 300 series every order prices in under 3.5 ms, at 100 series under 0.6 ms. Order totals differ from a cold solve's by at most 0.033%.

- *Order bounds (owner approved, 2026-11-26):* `Book::bounds(order)` returns a lower bound (the continuous relaxation re-solved from the book's basis) and an upper bound (the book's pairing carried over, priced by the checker: added lots standalone, removed lots trimmed out of their spread with matching units of the other side, other structures broken up). `Book::fits(order, limit)` decides from the bounds and calls `what_if` only when the limit falls between them. On the 1,000-series book bounds take 0.8 ms for a resize or close and 9 ms for a new series; the band (upper − lower) / upper has median 0.009% (resize), 0.014% (new series) and 0.16% (close). The `book_orders` test checks lower ≤ optimum ≤ upper and `fits` on both sides of the exact total for every order.

**Status (2026-11-26): target met.** Every order on the 1,000-series book prices in under 50 ms (worst of 240: 26 ms), and the cold solve takes 0.42 s, with every HiGHS comparison within 1%. Further gains, if wanted:
1. A bound-flipping (long-step) dual ratio test, for the cold solve's root pivots.
2. Hypersparse solves (skipping zeros by a symbolic reach) once etas and pivots dominate.
3. A stronger formulation for `nearest_long`, whose LP bound is 2.5% below the optimum on the two hardest test cases.

## Phase 7: second speed round and determinism (2026-11-27)

**Targets** *(agent's choice, flagged; owner asked for another round)*: on the 1,000-series book, a full order solve (`what_if`) under **10 ms at p99**, `fits` under **0.5 ms**, a cold solve under **0.2 s**; every HiGHS comparison within 1%.

**Profiling.** `sample` against `pairing` runs under the guard (no Xcode on this Mac, so no Instruments). The order path was btran 28%, the reduced-cost recompute at each solve's optimality check 13%, ftran 10%, the model build 10% (new series); the cold solve was half in the per-pivot passes over all n + m variables.

**Done (commits after 1b50720):**
- btran pushes each solved value forward through U by rows and skips zeros; reduced costs are kept between solves, and an optimality check after fewer than 8 pivots does not recompute the primal and dual values (unless a nonbasic variable sits at an artificial bound).
- The ratio test and reduced-cost update run over the pivot row's nonzeros only.
- A bound-flipping (long-step) dual ratio test, after a solve's first 20 pivots: the cold 1,000-series solve went from 6,306 to 790 pivots.
- Model build 5.8 to 3.5 ms: integer payoffs, cached series keys, calls paired only with puts of their expiration and size, straddle partner checks in O(k).
- Tried and reverted: a running-balance form of the straddle matching rows (fewer nonzeros, but 446 more rows; cold solve slower and new-series p99 142 ms), and refactoring every 24 or 40 updates instead of 64 (slower).

**Measured (Mac, before it went onto battery and began throttling background work):**

  | 1,000-series book | Start of Phase 7 | Now |
  |---|---|---|
  | Cold solve | 400 ms | 33 ms |
  | Order, resize: median / p99 / max | 12.4 / 21.9 / 22.5 ms | 2.5 / 3.6 / 5.0 ms |
  | Order, new series: median / p99 / max | 17.7 / 23.4 / 30.2 ms | 7.6 / 10.5 / 10.8 ms |
  | Order, close: median / p99 / max | 10.9 / 24.0 / 25.2 ms | 3.4 / 15.5 / 20.4 ms |
  | `bounds` / `fits` (resize, close): median | 0.70 ms | 0.51 ms |

  The cold-solve and resize targets are met; the new-series p99 (10.5 ms, a model rebuild each), the close tail (1 order in 100 needs 145 warm pivots) and `fits` (0.51 ms) are just over theirs. `pairing_highs_tests 1000 40` and `large`: 0 failures, LP within 6e-16 of HiGHS, every answer within 1%.

**Determinism (owner, 2026-11-27: "do anything we can to preserve determinism").** Measured first on the 1,000-series book: the same input solved twice gave the same answer; but listing the positions in another order moved the total by 0.002%, a warm `what_if` matched a cold solve of the same positions in 0 of 40 orders (totals up to 0.0074% apart, pairings different), and an exact solve (`rel_gap` 0) cannot prove optimality at this size within its node budget (5.5 s, stopped), so exactness is no route to path independence. Done:
- `solve()` and `Book` work in canonical position order (`canonical()`), so the answer depends on the positions, not on how they are listed.
- `Book::fill` re-solves cold, so a book's state, and every later `what_if`, is the same as a new `Book` on the same positions, whatever orders led there. Cost: a fill is a cold solve (about 35 ms at 1,000 series) instead of a warm one; fills are not on the pre-trade path.
- `Book::canonical_what_if(order)` is opt-in full path independence: bit for bit `solve()` of the book after the order, at the cost of a cold solve (about 35 ms median at 1,000 series, against `what_if`'s 2.5 to 8 ms).
- The `determinism` solver test checks all of it on 120 books, pairings included.
- Not deterministic across platforms: the floating-point sums depend on the compiler and CPU, so Linux and the Mac may pick different near-optimal pairings.

**Still to measure on mains power:** the 5,000-series book, and a full benchmark regeneration.
