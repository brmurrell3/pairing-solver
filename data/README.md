# Data

## What the solver needs per instrument

- **Every line:** underlying symbol and product class (equity/ETF, narrow index, broad index), and signed quantity.
- **Options:** type, strike, expiration, exercise style, listed or OTC, and deliverable (underlying units per contract).
- **Market data:** the option's current market value and the underlying's current price, for uncovered requirements, out-of-the-money amounts, covered-call valuation and stock requirements.

Maximum-loss checks need only strikes, quantities and deliverables. The fixtures
use that to test the spread logic without prices.

## What is here

- `fixtures/cboe_manual.toml`: the Cboe Margin Manual's maximum-loss examples, the short box and the long put butterfly.
- `fixtures/cboe_manual_samples.toml`: the manual's other 53 sample calculations: long options, short puts and calls, put and call spreads, straddles, stock against options, complex spreads and hedged-underlying maintenance. The header lists the fields.
- `rules/default.toml`: the default rule set (rates, minimums, policies), equal to the engine's built-in defaults.

## Generators (built 2026-11-25)

`bench/books.hpp` builds every benchmark book from a fixed seed; nothing is stored here.

1. **Synthetic chain:** one underlying at a random price, a strike grid (1, 2.50 or 5 apart by price), up to eight expirations, and Black-Scholes marks at a flat 30% volatility with zero rates.
2. **Families:**
   - `retail`: one to six trades (verticals, iron condors, covered calls, calendars, single options), 1 to 5 lots;
   - `market_maker`: n distinct series on both sides of many strikes and eight expirations, 1 to 50 contracts, with a stock hedge half the time;
   - `adjusted`: retail books in which about 30% of the series deliver 150 shares and about 7% deliver 10;
   - adversarial: the 100 of 4,000 seeded retail books on which greedy does worst (in `bench/bench.cpp`). They are selected, not constructed.
3. **Brute-force set:** `tests/exhaustive.cpp` enumerates every division of 3,000 random portfolios of up to 8 positions (`tests/generate.hpp`).

## Private data

Real option chains may be used for local benchmarks under `data/private/`, which is
ignored by git. They are never committed or published.
