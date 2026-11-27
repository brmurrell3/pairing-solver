# pairing-solver

[![CI](https://github.com/brmurrell3/pairing-solver/actions/workflows/ci.yml/badge.svg)](https://github.com/brmurrell3/pairing-solver/actions/workflows/ci.yml)
[![Lean](https://github.com/brmurrell3/pairing-solver/actions/workflows/lean.yml/badge.svg)](https://github.com/brmurrell3/pairing-solver/actions/workflows/lean.yml)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

A C++20 library that finds the lowest strategy-based margin requirement for a book of
options and stock, fast enough to re-price the book before every order.

## Background

An account that holds options must keep margin against them. Under FINRA Rule 4210(f)(2)
and Cboe Rule 10.3, positions that offset each other can be grouped into recognized
structures (spreads, straddles, covered calls and puts, conversions, collars, boxes),
and each structure carries a lower requirement than its legs held alone. The same book
can usually be grouped many ways, and the totals differ. This library finds the
grouping with the lowest total.

It does that with its own solver: a bounded-variable dual simplex on a sparse LU basis
factorization, with branch-and-bound on top, using the problem's structure to keep the
model small. The rules encoded, with paragraph citations, are in
[docs/rules.md](docs/rules.md); the model and solver design in [docs/spec.md](docs/spec.md);
proofs, including when the problem is NP-hard and hard to approximate, in
[docs/proofs.md](docs/proofs.md). The hardness reductions (Theorems 1 to 4, and the gap
lemmas behind Corollary 6) are also machine-checked in Lean 4
([lean/README.md](lean/README.md)). The hardness results have not been independently
reviewed, and whether they are new is not established.

## Results

On generated market-maker books (Apple M3 Max, one thread; [docs/benchmarks.md](docs/benchmarks.md)):

| | 1,000 positions | 5,000 positions |
|---|---|---|
| Solve the book from scratch | 29 ms | 2.0 s |
| Price one order from the solved book: median | 2.6–7.3 ms | 25–53 ms |
| Price one order: p99 | 7.6–12 ms | 75–103 ms |
| Bound the requirement after one order: median | 0.5–5.2 ms | 1.7–17 ms |

Ranges run over the three order kinds (resize, new series, close), from 240 orders at
1,000 positions and 90 at 5,000. Priced orders stay within 0.15% of a cold solve of the
same positions. Against HiGHS's proven optimum on 1,000 random books, every answer is
within 1%, and the whole set solves in 4.0 s against HiGHS's 28 s; on the benchmark books
the mean excess is 0.004% to 0.023%.

## How to run

Requires a C++20 compiler, CMake 3.24 or later and
[toml++](https://github.com/marzer/tomlplusplus) 3.4 (`brew install tomlplusplus` or
`apt install libtomlplusplus-dev`).

```bash
cmake -S . -B build
cmake --build build -j
ctest --test-dir build --output-on-failure
```

Run one fixture file of known answers, or regenerate the benchmark tables:

```bash
build/pairing_tests fixture data/fixtures/cboe_manual_samples.toml
build/pairing_bench
```

Check the hardness reductions by exhaustive search on small instances (Python 3.9 or
later, standard library only):

```bash
python3 tools/check_hardness.py --quick
python3 tools/check_approx_expiry.py
```

From C++, solve a book once and then price orders against it
([include/pairing/solver.hpp](include/pairing/solver.hpp)):

```cpp
pairing::Book book(portfolio, rules);
pairing::Solution after = book.what_if(order);           // the requirement if the order filled
bool ok = book.fits(order, limit);                        // from bounds when they decide it
pairing::Solution same = book.canonical_what_if(order);  // solve() after the order, bit for bit
```

`solve()` and `Book` work in canonical position order, so the answer depends on the
positions, not on how they are listed.

HiGHS 1.16 or later is optional; when CMake finds it, the build adds differential tests
against it. [CLAUDE.md](CLAUDE.md) lists every test and the sanitizer build.

## License

MIT; see [LICENSE](LICENSE).
