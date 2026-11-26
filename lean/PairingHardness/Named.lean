module

public import PairingHardness.Basic

/-!
# The named call spreads of the legacy rule

The call-side main spreads of Theorem 1 (Matsypura and Timkovsky 05/2010, Table 2), one unit
each. A pairing that holds several units of one spread lists it several times.
-/

@[expose] public section

namespace PairingHardness

/-- A named call spread, by its strikes in increasing order. -/
inductive Named where
  | bull (k₁ k₂ : ℤ)
  | bear (k₁ k₂ : ℤ)
  | longButterfly (k₁ k₂ k₃ : ℤ)
  | shortButterfly (k₁ k₂ k₃ : ℤ)
  | longCondor (k₁ k₂ k₃ k₄ : ℤ)
  | shortCondor (k₁ k₂ k₃ k₄ : ℤ)

namespace Named

/-- Strikes in increasing order; butterflies and condors with all intervals equal, of any
width. -/
def Valid : Named → Prop
  | bull k₁ k₂ | bear k₁ k₂ => k₁ < k₂
  | longButterfly k₁ k₂ k₃ | shortButterfly k₁ k₂ k₃ =>
      k₁ < k₂ ∧ k₂ < k₃ ∧ k₂ - k₁ = k₃ - k₂
  | longCondor k₁ k₂ k₃ k₄ | shortCondor k₁ k₂ k₃ k₄ =>
      k₁ < k₂ ∧ k₂ < k₃ ∧ k₃ < k₄ ∧ k₂ - k₁ = k₃ - k₂ ∧ k₃ - k₂ = k₄ - k₃

/-- The debit spreads, which the legacy rule requires nothing for. -/
def IsDebit : Named → Prop
  | bull .. | longButterfly .. | longCondor .. => True
  | bear .. | shortButterfly .. | shortCondor .. => False

/-- The contracts of one unit. -/
def shape : Named → Spread
  | bull k₁ k₂ => ({k₁}, {k₂})
  | bear k₁ k₂ => ({k₂}, {k₁})
  | longButterfly k₁ k₂ k₃ => ({k₁} + {k₃}, {k₂} + {k₂})
  | shortButterfly k₁ k₂ k₃ => ({k₂} + {k₂}, {k₁} + {k₃})
  | longCondor k₁ k₂ k₃ k₄ => ({k₁} + {k₄}, {k₂} + {k₃})
  | shortCondor k₁ k₂ k₃ k₄ => ({k₂} + {k₃}, {k₁} + {k₄})

lemma balanced_shape (s : Named) : Balanced s.shape := by
  cases s <;> simp [Balanced, shape]

/-- The legacy requirements agree with R2 on which spreads require nothing: a valid named
spread has no loss exactly when it is a debit spread. -/
theorem maxLoss_eq_zero_iff_isDebit (s : Named) (hs : s.Valid) :
    maxLoss s.shape = 0 ↔ s.IsDebit := by
  rw [PairingHardness.maxLoss_eq_zero_iff]
  cases s <;> simp only [Valid] at hs <;>
    simp [NoLoss, shape, strikes, payoff, callValue, IsDebit] <;> omega

end Named

end PairingHardness
