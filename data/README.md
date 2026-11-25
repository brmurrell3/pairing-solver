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

## What still has to be built

1. **Synthetic chains.** Strikes, expirations and Black-Scholes marks for chosen underlyings. They are deterministic and reproducible, and safe to publish.
2. **Portfolio generators**, each seeded:
   - retail-like books of verticals, condors and covered calls;
   - market-maker-like books with many strikes and both sides;
   - books with adjusted series (150-share and 10-share deliverables);
   - adversarial books built so greedy pairing does badly.
3. **Brute-force set.** Portfolios small enough (about 8 positions) to enumerate every division, to certify optimality.

## Private data

Real option chains, such as the Schwab API captures in `vol-infra`, may be used for
local benchmarks under `data/private/`, which is ignored by git. They are never
committed or published.
