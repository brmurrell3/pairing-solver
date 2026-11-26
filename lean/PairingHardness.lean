module

public import PairingHardness.Theorem1
public import PairingHardness.Theorem2Four

/-!
# Hardness of pairing, machine-checked

Lean statements of docs/proofs.md, "Hardness", Theorems 1 and 2. See README.md in this
folder for what is proved and what is assumed.

* `PairingHardness.N3DM.theorem1`: the butterfly instance has a pairing into named spreads
  with requirement zero exactly when the source instance has a matching.
* `PairingHardness.N3DM.theorem2_three`, `PairingHardness.N3DM.theorem2_four`: the same for
  any family of spreads of at most three or four legs priced so that a requirement is zero
  exactly when the maximum loss is, on the butterfly and condor instances.
* `PairingHardness.N3DM.butterfly_size`, `PairingHardness.N3DM.condor_size`: the instances
  have `4n` contracts at strikes bounded by a polynomial in `n` and `W`.
-/
