module

public import PairingHardness.Theorem1
public import PairingHardness.Theorem2Four
public import PairingHardness.Theorem4
public import PairingHardness.Approx

/-!
# Hardness of pairing, machine-checked

Lean statements of docs/proofs.md, "Hardness", Theorems 1 to 4. See README.md in this
folder for what is proved and what is assumed.

* `PairingHardness.N3DM.theorem1`: the butterfly instance has a pairing into named spreads
  with requirement zero exactly when the source instance has a matching.
* `PairingHardness.N3DM.theorem2_three`, `PairingHardness.N3DM.theorem2_four`: the same for
  any family of spreads of at most three or four legs priced so that a requirement is zero
  exactly when the maximum loss is, on the butterfly and condor instances.
* `PairingHardness.N3DM.butterfly_size`, `PairingHardness.N3DM.condor_size`: the instances
  have `4n` contracts at strikes bounded by a polynomial in `n` and `W`.
* `PairingHardness.SubsetSumInstance.theorem3`: some numbers sum to `T` exactly when one
  maximum-loss group costs at most `R`; `cost_ge_R` shows no group costs less.
* `PairingHardness.KSubsetSumInstance.theorem4`: the same for `k`-subset sum with every
  uncovered requirement R3's from prices within the no-arbitrage bounds (`price_valid`, `price_antitone`);
  `PairingHardness.subsetSum_iff_kSubsetSum` reduces subset sum to `k`-subset sum.
* `PairingHardness.N3DM.theorem1_gap`, `PairingHardness.N3DM.theorem2_three_gap`,
  `PairingHardness.N3DM.theorem2_four_gap`: when every positive requirement is at least
  `μ > 0`, a source instance with no matching has no pairing below `μ` (Corollary 6).
-/
