# Agent guide

This file lets an agent with no prior context pick up the project. `AGENTS.md` is a
symlink to it.

## What this is

A C++20 library that pairs an account's options and stock into the margin
structures U.S. rules recognize (spreads, straddles, covered positions, conversions,
collars), so the total strategy-based margin requirement is as low as the rules
allow.

The problem's structure makes a fast exact method possible, so the project writes
its own solver rather than wrapping a general LP/MIP package. The core is framed as a
general solver for packing an inventory into offset structures, with quantities in
whole units, a fixed decimal step, or continuous. Margin is its first application.

## Read in this order

1. [docs/plan.md](docs/plan.md): decisions, current phase, and what "done" means for each phase. Start here to find the next task.
2. [docs/spec.md](docs/spec.md): the general model (§2), the margin application and its structural results (§3.1), problem size (§3.2), policies (§3.3), solver design (§3.4), scope (§3.5), outputs and correctness (§4–5).
3. [docs/rules.md](docs/rules.md): every rule encoded, as R1–R10 and U1–U3, with FINRA 4210 paragraph citations. Open interpretation questions are Q1–Q7.
4. [docs/sources.md](docs/sources.md): rule texts, papers and prior art, with what each settled and what is still unread.
5. [data/README.md](data/README.md): data the solver needs, the fixtures, and the generators still to build.

## Decisions already made (do not reopen without the owner)

| Decision | Reason |
|---|---|
| C++20 core behind a small C interface | Java calls it through the Foreign Function & Memory API, Python through ctypes. C++ links HiGHS directly for tests. |
| Own solver: dense bounded-variable dual simplex, branch-and-bound, then a structured dynamic program (spec §3.4) | Writing the solver is the point of the project. |
| HiGHS is a test-only oracle, never shipped | Gives an independent optimal value for differential tests. |
| Quantity grid is a policy, not a fixed rule | Whether partial contracts may be paired is unresolved (rules.md Q1). |
| Default `expiry_rule = pairwise` | The Cboe manual's mixed-expiration examples support it (rules.md R2a). Stricter readings are policies. |

## Rules for working here

- **Sources:** rule claims come only from the primary texts in `refs/`. Cite the paragraph (e.g. 4210(f)(2)(H)(i)) or the Cboe manual section heading.
- **Ambiguity:** if a source is ambiguous, add or extend a Q item in rules.md. Do not resolve it silently in code.
- **Proof:** verify before claiming. Every requirement formula has a fixture with a known answer. Every structural claim in spec §3.1 has a randomized check in `tools/` until a proof is written.
- **Plan status:** keep `docs/plan.md` current. When a phase or input item is finished, mark it done with the date and the evidence (test counts, commands).
- **Clean room:** use only public rule texts and published papers. Never use employer code, documents or data.
- **Licenses:** never commit `refs/` (the Cboe manual's license forbids redistribution) or `data/private/`. Numbers transcribed from the manual into fixtures are fine; its prose is not.
- **Git:** this is the owner's private repository with no other contributors, so agents may commit freely (owner, 2026-11-25). Never put Claude or any AI tool in commit messages or as a co-author. Do not push to a remote or open pull requests on repositories the owner does not own.
- **Docs style:** plain, precise prose with real numbers and commands. Comment the why, not the what.

## Tools

The Python checks need Python 3.11 or later for `tomllib`. `/opt/homebrew/bin/python3` is 3.15.

```bash
/opt/homebrew/bin/python3 tools/check_fixtures.py data/fixtures/cboe_manual.toml
```

```bash
/opt/homebrew/bin/python3 tools/check_structure.py
```

- **`check_fixtures.py`** independently recomputes each fixture's netted values, maximum loss, requirement and expiry-policy validity.
- **`check_structure.py`** tests spec §3.1 items 1, 4 and 5 on 3,000 random portfolios. The pairing condition is checked against an explicit max-flow.
- **`check_hardness.py`** checks the reductions of proofs.md, "Hardness", against exhaustive search on small random instances: `python3 tools/check_hardness.py` (about half a minute; `--quick` takes a second). It uses only the standard library and runs on Python 3.9 or later.

## Running code safely (read before running anything)

On 2026-11-25, six orphaned debug runs of an unbounded branch-and-bound loop used about 205 GB on this 36 GB machine. The memory compressor filled up and the Mac kernel-panicked. These rules exist because of that.

- **Use the guard.** Run every test binary, solver run or ad hoc program through `tools/run_guarded.sh`. It kills the whole process tree above a memory cap (default 4096 MB) or a time cap (default 600 s). Example: `tools/run_guarded.sh -m 4096 -t 300 -- ctest --test-dir build --output-on-failure`.
- **Never orphan a process.** Do not start test or debug programs in the background with `&`, and do not stop one with `kill %1`. Non-interactive shells have no job table, so that silently fails. If something must run in the background, record its PID and use `kill <pid>`, or let the guard enforce the limit.
- **Bound every search.** Every search in the library carries an explicit limit and returns a status when it hits it: simplex iterations, branch-and-bound nodes, exhaustive-search enumeration size. A limit hit is a reported result, never an endless loop.
- **Keep scratch files in the session's scratchpad**, not elsewhere in `/tmp`, and delete ad hoc debug binaries when you finish.
- **Before ending a task, check for leftovers.** `pgrep -lf 'pairing_|dbg'` should print nothing.

## Build and test

Requires CMake 3.24 or later and toml++ 3.4 (`brew install tomlplusplus`). Nothing is fetched. HiGHS 1.16 or later (`brew install highs`, or a source build passed with `-DCMAKE_PREFIX_PATH`) enables the `highs` and `highs_large` tests; without it they are skipped.

```bash
/opt/homebrew/bin/cmake -S . -B build
/opt/homebrew/bin/cmake --build build -j
ctest --test-dir build --output-on-failure
```

- **`unit`:** money arithmetic, dates, rule-file loading, policies, and the spec §3.1 items 1, 4 and 5 checks run against the engine.
- **`cboe_manual`, `cboe_manual_samples`:** every case in the two fixture files. `build/pairing_tests fixture <file.toml>` runs one file.
- **`solver`:** the simplex and branch-and-bound on small LPs and knapsacks, hand-built portfolios (including the long box), the greedy baseline, the strike dynamic program against the exact solve, and the subset-sum reduction of proofs.md Theorem 4.
- **`exhaustive`:** the solver against brute force on 3,000 small portfolios, exact (`rel_gap = 0`).
- **`highs`, `highs_large`:** the Phase 2 criteria against HiGHS (about 3 and 6 minutes). `pairing_highs_tests <n> [max series] [rel_gap]` and `pairing_highs_tests large [rel_gap] [case]` run them by hand.
- **Sanitizers:** `cmake -S . -B build-asan -DCMAKE_BUILD_TYPE=Debug -DCMAKE_CXX_FLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer -fno-sanitize-recover=undefined -O1"`, then build and run `ctest --test-dir build-asan -E highs` under the guard with `-m 8192`. ASan needs the higher memory cap.
- **Benchmarks:** `tools/run_guarded.sh -m 4096 -t 3000 -- build/pairing_bench > docs/benchmarks.md` regenerates every Phase 3 table (about 8 minutes); `pairing_bench <table>` runs one.
- `tools/check_fixtures.py` reads spread cases only, so it runs on `cboe_manual.toml` but not on `cboe_manual_samples.toml`.
