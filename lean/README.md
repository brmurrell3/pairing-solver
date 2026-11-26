# Machine-checked hardness proofs

Lean 4 proofs of Theorems 1 and 2 of [docs/proofs.md](../docs/proofs.md), "Hardness": pairing
calls into spreads is NP-hard in the strong sense, by reduction from numerical
3-dimensional matching. Built against Lean 4.36.0 and Mathlib v4.36.0, both pinned
(`lean-toolchain`, `lake-manifest.json`).

## What is proved

For every well-formed instance `I` of numerical 3-dimensional matching (`N3DM.Valid`: `n`
positive numbers in each of `A`, `B`, `C` and a positive bound):

| Lean | Statement |
|---|---|
| `N3DM.theorem1` | The butterfly instance has a pairing into named spreads (bull, bear, butterflies and condors with equal intervals of any width) with requirement zero exactly when `I` has a matching. The requirements are any nonnegative numbers that are zero exactly for the debit spreads, with a positive requirement for each uncovered short. |
| `N3DM.theorem2_three` | For any family of balanced spreads of at most 3 legs that contains every long butterfly with equal intervals, priced so that a requirement is zero exactly when the maximum loss is: the reduction (butterfly instance if `ΣA + ΣB + ΣC = nB`, else one uncovered short) has a pairing with requirement zero exactly when `I` has a matching. |
| `N3DM.theorem2_four` | The same for at most 4 legs and every long condor with equal wings, on the condor instance. |
| `N3DM.butterfly_size`, `N3DM.condor_size` | Both instances have `4n` contracts at positive integer strikes of at most `2M + 2W` and `(2n + 3)M + W`, with `M = 6nW` and `W` the largest input number. So every number in the output is bounded by a polynomial in `n` and `W`, which is what a reduction in the strong sense needs. |
| `Named.maxLoss_eq_zero_iff_isDebit` | A valid named spread has R2 maximum loss zero exactly when it is a debit spread, so Theorem 1's requirement hypothesis agrees with R2. |
| `moment_nonpos` | The moment lemma: a balanced spread with no loss has `m(t) ≤ 0`. |

`AxiomCheck.lean` prints the axioms each result uses (only `propext`, `Classical.choice`
and `Quot.sound`, no `sorryAx`) and checks the example of Theorem 1 by `decide`.

## What is assumed, not proved

- **The source problem is NP-complete in the strong sense** (Garey and Johnson, problem
  SP16). Mathlib has no complexity classes or polynomial-time reductions, so this is cited,
  not stated in Lean.
- **The reductions run in polynomial time.** They are explicit closed-form definitions
  (`N3DM.butterfly`, `N3DM.reduce3`, `N3DM.reduce4`), and their output size is proved
  bounded, but running time is not formalized.
- **Membership in NP** (Theorem 1's "NP-complete") is not formalized. The hardness, which is
  what the results are used for, does not need it.
- Theorems 3 and 4 (subset sum, one maximum-loss group) and Proposition 5 are not
  formalized. `tools/check_hardness.py` still checks them by exhaustive search.

## Modeling choices

- Calls of one underlying, expiration, style, listing and deliverable; amounts per share;
  strikes are integers (ticks). A spread is two multisets of strikes, one entry per long and
  per short contract, so coinciding numbers simply share a strike.
- The maximum loss is R2's: the largest net loss at the members' strikes, or zero
  (`maxLoss`). Legs are distinct strikes (`legs`).
- A pairing (`Pairing`) is a list of spreads plus a multiset of uncovered shorts: every short
  is in exactly one spread or uncovered, and the spreads' longs fit inside the position's.
  Repeated spreads are repeated list entries.
- A matching (`N3DM.HasMatching`) is a multiset of triples whose three projections are
  exactly `A`, `B` and `C`, each triple summing to the bound.

## Relation to the paper proof

The Lean proofs follow docs/proofs.md: Theorem 1 by its counting argument (two shorts per
long below `M` only for a butterfly, and fact 3 against condors), Theorem 2 by the moment
lemma and the bounds on the low-order parts. Formalizing found no gap. The only cases the
paper leaves implicit are `n = 0`, where both sides hold trivially, and empty spreads.

## Build

Install elan (`brew install elan-init`, or the installer at
https://github.com/leanprover/elan), then:

```bash
cd lean
lake exe cache get
lake build --wfail
lake env lean AxiomCheck.lean
```

`lake exe cache get` downloads about 7 GB of prebuilt Mathlib. With it in place the build
takes about half a minute.

## Files

| File | Contents |
|---|---|
| `PairingHardness/Spread.lean` | Spreads, payoff, maximum loss, legs, moment lemma |
| `PairingHardness/Basic.lean` | Numerical 3-dimensional matching, pairings, list and multiset lemmas |
| `PairingHardness/Named.lean` | The named call spreads and their R2 losses |
| `PairingHardness/Butterfly.lean` | The butterfly instance, its facts 1 to 3, size, and decoding to a matching |
| `PairingHardness/Theorem1.lean` | Theorem 1 |
| `PairingHardness/Theorem2Three.lean` | Theorem 2 with at most 3 legs |
| `PairingHardness/Theorem2Four.lean` | The condor instance and Theorem 2 with at most 4 legs |
