import PairingHardness

/-! Lists the axioms each main result depends on. Run with `lake env lean AxiomCheck.lean`.
Every line should show only `propext`, `Classical.choice` and `Quot.sound`: no `sorryAx`. -/

open PairingHardness

#print axioms N3DM.theorem1
#print axioms N3DM.theorem2_three
#print axioms N3DM.theorem2_four
#print axioms N3DM.butterfly_size
#print axioms N3DM.condor_size
#print axioms Named.maxLoss_eq_zero_iff_isDebit
#print axioms SubsetSumInstance.theorem3
#print axioms SubsetSumInstance.cost_ge_R
#print axioms SubsetSumInstance.size
#print axioms subsetSum_iff_filter
#print axioms subsetSum_iff_kSubsetSum
#print axioms KSubsetSumInstance.theorem4
#print axioms KSubsetSumInstance.price_valid
#print axioms KSubsetSumInstance.price_antitone
#print axioms KSubsetSumInstance.size

/-- The example of docs/proofs.md, Theorem 1: `a = (1, 2)`, `b = (3, 1)`, `c = (3, 4)`,
`B = 7`, so `W = 7` and `M = 84`. -/
def example1 : N3DM := ⟨{1, 2}, {3, 1}, {3, 4}, 7⟩

example : example1.W = 7 ∧ example1.M = 84 := by decide
example : example1.butterfly = ({2, 4, 174, 176}, {88, 88, 90, 90}) := by decide
