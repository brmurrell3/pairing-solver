# Machine-checked hardness proofs

Lean 4 proofs of Theorems 1 to 4 of [docs/proofs.md](../docs/proofs.md), "Hardness": pairing
calls into spreads of limited shape is NP-hard in the strong sense, by reduction from
numerical 3-dimensional matching (Theorems 1 and 2), and the solver's one-group problem is
NP-hard, by reduction from subset sum (Theorems 3 and 4). Built against Lean 4.36.0 and Mathlib v4.36.0, both pinned
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
| `moment_nonpos`, `moment_le_maxLoss` | The moment lemma: a balanced spread's loss at its highest strike is its moment `m(t)`, so a spread with no loss has `m(t) ≤ 0`. |
| `SubsetSumInstance.theorem3` | For positive numbers `a_i < T`: some of them sum to `T` exactly when one maximum-loss group of the position costs at most `R = (Σa − T)/2`, with uncovered requirements `a_i/2`. `cost_ge_R`: no group costs less than `R`, so the minimum is `R` then. `subsetSum_iff_filter` is the preprocessing that drops numbers `≥ T`. |
| `subsetSum_iff_kSubsetSum` | Subset sum reduces to `k`-subset sum, by the replacement in Theorem 4's text. |
| `KSubsetSumInstance.theorem4` | For positive numbers, `k ≥ 2` and `T ≤ Σa`: exactly `k` of them sum to `T` exactly when one group costs at most `R`, with every uncovered requirement computed by R3 at stock rates (`r3Call`) from the call prices `C(K) = 2k + (K_top − K)/(2k)`. `price_valid` and `price_antitone`: those prices are positive, at most the underlying, at least intrinsic value, falling in the strike and affine. |
| `SubsetSumInstance.size`, `KSubsetSumInstance.size` | `2n + 1` contracts, at strikes from 1 to `T + 1` and from `2S` to `2S + V`. |
| `N3DM.theorem1_gap`, `N3DM.theorem2_three_gap`, `N3DM.theorem2_four_gap` | The gap behind Corollary 6: if every positive spread requirement and every uncovered requirement is at least `μ > 0`, then on a source instance with no matching every pairing of the instance requires at least `μ`. `Pairing.requirement_eq_zero_or_ge` is the general step. |

`AxiomCheck.lean` prints the axioms each result uses (only `propext`, `Classical.choice`
and `Quot.sound`, no `sorryAx`) and checks the example of Theorem 1 by `decide`.

## What is assumed, not proved

- **The source problems are NP-complete**: numerical 3-dimensional matching in the strong
  sense (Garey and Johnson, problem SP16) and subset sum (SP13). Mathlib has no complexity
  classes or polynomial-time reductions, so these are cited, not stated in Lean.
- **The reductions run in polynomial time.** They are explicit closed-form definitions
  (`N3DM.butterfly`, `N3DM.reduce3`, `N3DM.reduce4`, `SubsetSumInstance.pos`,
  `KSubsetSumInstance.pos`), and their output size is proved bounded, but running time is
  not formalized. Theorems 3 and 4 assume the trivial cases are answered by inspection
  (`T ≤ a_i` for some `i`; `k < 2` or `T > Σa`); `subsetSum_iff_filter` covers the first.
- **Membership in NP** is not formalized. The hardness, which is what the results are used
  for, does not need it.
- **Corollary 6's pricing step**: that the shifted, small-premium prices are valid, that R3
  charges every short at least `μ`, and that the long premiums are at most `μ / ρ`. The
  Lean statements take `μ` as a hypothesis on the requirements.
- **Proposition 7** (one group with several expirations) is not formalized.
- **Proposition 5** (a dynamic program for butterflies and condors on adjacent strikes) is not
  formalized. It is an algorithm with a 12-counter state, and proofs.md gives it as a sketch;
  a Lean proof would first need the transitions and their costs written out. Its claim is
  checked against exhaustive search in `tools/check_hardness.py`.

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
  exactly `A`, `B` and `C`, each triple summing to the bound. A subset is a sub-multiset.
- One maximum-loss group (`IsGroup`, `groupCost`) is any balanced set of the position's
  contracts, costing its maximum loss plus `U K` for each short left out.

## Relation to the paper proof

The Lean proofs follow docs/proofs.md: Theorem 1 by its counting argument (two shorts per
long below `M` only for a butterfly, and fact 3 against condors), Theorem 2 by the moment
lemma and the bounds on the low-order parts. Theorems 3 and 4 take a shorter route than the
paper's exact maximum loss `max(0, a(A) − lT)`: the hard direction needs only the lower
bound, the loss at the top strike, and the construction shows no loss by giving each short
its share `a_i/T` of the low long's gain (`Ladder.decomp`, `Ladder.construct`, shared by
both theorems). Theorem 4 works in units of `1/(2k)` so that strikes are whole, as the paper
says is possible, and takes `K_low = 2S`, one admissible choice of its `K_low ≥ 1.1S`.

Formalizing found no gap. The cases the paper leaves implicit are `n = 0`, where both sides
hold trivially, and empty spreads.

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
| `PairingHardness/Ladder.lean` | One-group requirement, and the position shared by Theorems 3 and 4 |
| `PairingHardness/Theorem3.lean` | Theorem 3 |
| `PairingHardness/Theorem4.lean` | Subset sum to `k`-subset sum, R3 prices, Theorem 4 |
| `PairingHardness/Approx.lean` | The gap form of Theorems 1 and 2 (Corollary 6) |
