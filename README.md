# pairing-solver

A solver for packing an inventory of positions into offset structures at minimum
cost. The quantity grid is configurable: whole units, a fixed decimal step, or continuous. The first application is
strategy-based options margin: pairing a customer's options and stock into the
spreads, straddles and covered positions that FINRA Rule 4210(f)(2) and Cboe
Rule 10.3 recognize, so the margin requirement is as low as the rules allow.

Status: specification and rule engine (Phase 1) done; the solver (Phase 2) is next.
Agents: start with [CLAUDE.md](CLAUDE.md), which also has the build and test commands.

- [docs/spec.md](docs/spec.md): the problem, the general formulation, and what the
  solver must produce.
- [docs/rules.md](docs/rules.md): the margin rules the first application encodes, with
  paragraph citations and the open interpretation questions.
- [docs/sources.md](docs/sources.md): rule texts, papers and prior art, and what each
  one settled.
- [docs/plan.md](docs/plan.md): build phases and what "done" means for each.
- [data/](data/): test fixtures with known answers, and the default rule set.
- `include/`, `src/`, `tests/`: the C++20 rule engine and its tests.

## Clean room

This project is built only from public rule texts and published papers. It uses no
employer code, documents or data. Check the employer's outside-activity and IP
policy before publishing it.

## Local references

`refs/` holds copies of the rule texts used to write the spec. It is not committed:
the Cboe manual's license forbids redistribution.
