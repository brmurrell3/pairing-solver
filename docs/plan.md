# Plan

**Current status (2026-11-25):** Phase 0 and Phase 1 done. Phase 2 partly built and stopped after a crash; see its status note.

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

**Status (2026-11-25, stopped, not done):**
- **Built:** model builder, checker, dense dual simplex and branch-and-bound (`src/simplex.cpp`, `src/solver.cpp`, `src/checker.cpp`).
- **Passing under `tools/run_guarded.sh`:** `unit`, `cboe_manual`, `cboe_manual_samples`, `solver` and `exhaustive`. Exhaustive search: 1,000 portfolios per `expiry_rule` policy (3,000 total) match exactly, in about 11 s.
- **The crash:** during development, a branch-and-bound bug (branching up on a bound below 1 produced lower > upper, which the simplex accepted as optimal) made every node re-branch the same column. Six orphaned debug runs of it exhausted memory and panicked the Mac. The bug is fixed: `simplex.cpp` rejects lower > upper as infeasible, and branch-and-bound skips empty branches. See CLAUDE.md, "Running code safely".
- **Open:**
  1. Branch-and-bound has no node limit; add one that reports a status.
  2. The HiGHS differential test (`tests/highs.cpp`, CTest `highs`) never ran: HiGHS rejects the first model it is given, so the model export is wrong.
  3. Branch-and-bound is slow at size. One 40-series case takes about 9 s, and a 200-series case did not finish in 9 minutes. The criterion was revisited on 2026-11-25 (see "Target decision" below): speed now takes priority over exact optimality on large portfolios.
  4. Sanitizer build not run.
  5. `BB_TRACE` and `PAIRING_TRACE` debug code still in `src/simplex.cpp` and `tests/exhaustive.cpp`.
  6. Long-box template test missing; docs not updated.

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
- **Large, performance:** five fixed-seed portfolios of 50, 100, 150, 200 and 200 series each finish in at most 30 s under `tools/run_guarded.sh -m 4096`, within the same 1% of HiGHS, with time and gap reported. *(agent's choice: five cases, 30 s each)*
- The checker accepts every solution.

Superseded criterion: match HiGHS to 1e-9 relative on at least 10,000 random portfolios of up to 200 series.

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

## Phase 4: structured algorithm and theory

- **Proofs:** write up spec §3.1 items 1, 2, 4 and 5.
- **Algorithm:** dynamic programming over the strike walk for whole contracts; establish its complexity and benchmark it against the Phase 2 solver and HiGHS.
- **Integrality:** when is the continuous solution already whole-contract? Find counterexamples where it is not.
- **Template-only policies:** hardness, or a cited result, for butterfly and condor templates. Check against Matsypura and Timkovsky first.

**Done when** each claim has a proof or a cited result, and the benchmarks say where each algorithm wins.

## Phase 5: publish

- **Code:** a public repository with the clean-room note, after checking the employer's outside-activity and IP policy.
- **Write-up:** a project page on brendanmurrell.com covering the formulation, the proofs and the benchmark results.
- **Resume:** a project line on the resume.
