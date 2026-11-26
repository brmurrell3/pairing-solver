# pairing-solver

A solver for packing an inventory of positions into offset structures at minimum
cost. The quantity grid is configurable: whole units, a fixed decimal step, or continuous. The first application is
strategy-based options margin: pairing a customer's options and stock into the
spreads, straddles and covered positions that FINRA Rule 4210(f)(2) and Cboe
Rule 10.3 recognize, so the margin requirement is as low as the rules allow.

The solver is written from scratch: a dense bounded-variable dual simplex with
branch-and-bound on top, using the problem's structure (strike-walk loss rows, suffix
pairing rows instead of flows, a compact form for straddles). HiGHS is used only in tests,
as an independent optimum.

Status: Phases 1 to 3 are done and Phase 4 is mostly done ([docs/plan.md](docs/plan.md)).
- Exact on 3,000 small portfolios against brute force.
- Within 1% of HiGHS's proven optimum on 1,000 portfolios of up to 40 series, in 17 s
  against HiGHS's 139 s.
- A 1,000-series market-maker book solves in 18 s; see [docs/benchmarks.md](docs/benchmarks.md).

## Build and test

Requires a C++20 compiler, CMake 3.24 or later and toml++ 3.4. HiGHS 1.16 or later is
optional and enables the differential tests against it.

```bash
cmake -S . -B build
cmake --build build -j
ctest --test-dir build --output-on-failure
```

[CLAUDE.md](CLAUDE.md) (also `AGENTS.md`) has the full test list, the sanitizer build and
the benchmark command.

- [docs/spec.md](docs/spec.md): the problem, the general formulation, and what the
  solver must produce.
- [docs/rules.md](docs/rules.md): the margin rules the first application encodes, with
  paragraph citations and the open interpretation questions.
- [docs/sources.md](docs/sources.md): rule texts, papers and prior art, and what each
  one settled.
- [docs/plan.md](docs/plan.md): build phases and what "done" means for each.
- [docs/proofs.md](docs/proofs.md): proofs of the structural results the solver relies on,
  integrality counterexamples, and the strike dynamic program's complexity.
- [docs/benchmarks.md](docs/benchmarks.md): savings against a greedy baseline, solve times
  and comparisons with HiGHS.
- [data/](data/): test fixtures with known answers, and the default rule set.
- `include/`, `src/`, `tests/`, `bench/`: the C++20 rule engine, solver, tests and
  benchmarks.

## Clean room

This project is built only from public rule texts and published papers. It uses no
employer code, documents or data.

## Local references

`refs/` holds copies of the rule texts used to write the spec. It is not committed:
the Cboe manual's license forbids redistribution.

## License

MIT; see [LICENSE](LICENSE). `refs/` is not part of the repository or the license.
