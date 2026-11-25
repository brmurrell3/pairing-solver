# Plan

**Current status (2026-11-25):** Phases 0 to 3 done. Phase 4 in progress: proofs and integrality counterexamples written; the dynamic program and template-only hardness are open.

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
2. **Papers:** download the two Matsypura and Timkovsky working papers by hand (automated fetches get 403), and Rudd and Schroeder if a library copy is available. Put them in `refs/`.
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
  1. **Node limit:** `MipOptions::node_limit` (default 1,000,000; `SolveOptions::node_limit` 200,000). A hit returns `MipStatus::node_limit` with the best assignment and a proven bound (`Solution::status`, `bound`, `proven_gap`).
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
- **Open:** the dynamic program over strikes and its complexity; template-only hardness (needs the Matsypura and Timkovsky papers, Inputs item 2).

## Phase 5: publish

- **Code:** a public repository with the clean-room note, after checking the employer's outside-activity and IP policy.
- **Write-up:** a project page on brendanmurrell.com covering the formulation, the proofs and the benchmark results.
- **Resume:** a project line on the resume.
