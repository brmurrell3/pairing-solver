# pairing-solver

A C++20 library that finds the lowest strategy-based margin requirement for a book of
options and stock.

## Background

An account that holds options must keep margin against them. Under FINRA Rule 4210(f)(2)
and Cboe Rule 10.3, positions that offset each other can be grouped into recognized
structures (spreads, straddles, covered calls and puts, conversions, collars, boxes),
and each structure carries a lower requirement than its legs held alone. The same book
can usually be grouped many ways, and the totals differ. This library finds the
grouping with the lowest total.

It does that with its own solver: a bounded-variable dual simplex with branch-and-bound
on top, using the problem's structure to keep the model small. The rules encoded, with
paragraph citations, are in [docs/rules.md](docs/rules.md); the model and solver design
are in [docs/spec.md](docs/spec.md).

## How to run

Requires a C++20 compiler, CMake 3.24 or later and
[toml++](https://github.com/marzer/tomlplusplus) 3.4 (`brew install tomlplusplus` or
`apt install libtomlplusplus-dev`).

```bash
cmake -S . -B build
cmake --build build -j
ctest --test-dir build --output-on-failure
```

Run one fixture file of known answers, or the benchmarks (about 8 minutes):

```bash
build/pairing_tests fixture data/fixtures/cboe_manual_samples.toml
build/pairing_bench
```

HiGHS 1.16 or later is optional; when CMake finds it, the build adds differential tests
against it. [CLAUDE.md](CLAUDE.md) lists every test and the sanitizer build.

## License

MIT; see [LICENSE](LICENSE).
