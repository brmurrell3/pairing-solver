module

public import Mathlib

/-!
# Spreads of calls

The setting of docs/proofs.md, "Hardness": calls on one underlying, of one expiration,
style, listing and deliverable, in whole contracts. Amounts are per share, so a strike is an
integer number of ticks.

A spread is recorded as two multisets of strikes, one entry per contract: the long
contracts and the short contracts. Its payoff, maximum loss (rules.md R2), legs and moment
are defined here, with the moment lemma of the proof.
-/

@[expose] public section

namespace PairingHardness

/-- A spread of calls: the strike of each long contract and of each short contract. -/
abbrev Spread := Multiset ℤ × Multiset ℤ

/-- Intrinsic value at underlying price `S` of one call struck at `K`. -/
def callValue (S K : ℤ) : ℤ := max (S - K) 0

/-- Netted intrinsic value of a spread at underlying price `S`. -/
def payoff (t : Spread) (S : ℤ) : ℤ :=
  (t.1.map (callValue S)).sum - (t.2.map (callValue S)).sum

/-- The strikes of a spread, one entry per contract. -/
def strikes (t : Spread) : Multiset ℤ := t.1 + t.2

/-- As many long contracts as short (rules.md R1 d). -/
def Balanced (t : Spread) : Prop := Multiset.card t.1 = Multiset.card t.2

/-- Maximum potential loss (rules.md R2): the largest net loss at the members' strikes,
or zero. -/
def maxLoss (t : Spread) : ℤ := ((strikes t).map fun K => -payoff t K).fold max 0

/-- No net loss at any of the members' strikes. -/
def NoLoss (t : Spread) : Prop := ∀ K ∈ strikes t, 0 ≤ payoff t K

/-- The number of legs: distinct series, here distinct strikes. -/
def legs (t : Spread) : ℕ := (strikes t).toFinset.card

/-- The moment `m(t)`: the sum of the long strikes minus the sum of the short strikes. -/
def moment (t : Spread) : ℤ := t.1.sum - t.2.sum

lemma fold_max_nonneg (s : Multiset ℤ) : 0 ≤ s.fold max 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => rw [Multiset.fold_cons_left]; omega

lemma fold_max_eq_zero_iff (s : Multiset ℤ) : s.fold max 0 = 0 ↔ ∀ x ∈ s, x ≤ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.fold_cons_left]
    simp only [Multiset.mem_cons, forall_eq_or_imp]
    have h0 : 0 ≤ s.fold max 0 := fold_max_nonneg s
    constructor
    · intro h
      exact ⟨by omega, ih.1 (by omega)⟩
    · rintro ⟨ha, hs⟩
      rw [ih.2 hs]; omega

/-- The maximum loss is zero exactly when there is no loss at any strike. -/
lemma maxLoss_eq_zero_iff (t : Spread) : maxLoss t = 0 ↔ NoLoss t := by
  simp [maxLoss, NoLoss, fold_max_eq_zero_iff]

lemma sum_callValue_of_le (s : Multiset ℤ) (K : ℤ) (h : ∀ k ∈ s, k ≤ K) :
    (s.map (callValue K)).sum = Multiset.card s * K - s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    rw [Multiset.map_cons, Multiset.sum_cons, ih fun k hk => h k (Multiset.mem_cons_of_mem hk)]
    simp only [callValue, Multiset.card_cons, Multiset.sum_cons]
    push_cast
    rw [max_eq_left (by omega)]
    ring

/-- At and above its highest strike, a balanced spread's payoff is `-m(t)`. -/
lemma payoff_of_ge (t : Spread) (hb : Balanced t) (K : ℤ) (hK : ∀ k ∈ strikes t, k ≤ K) :
    payoff t K = -moment t := by
  have h1 : ∀ k ∈ t.1, k ≤ K := fun k hk => hK k (Multiset.mem_add.2 (Or.inl hk))
  have h2 : ∀ k ∈ t.2, k ≤ K := fun k hk => hK k (Multiset.mem_add.2 (Or.inr hk))
  rw [payoff, sum_callValue_of_le _ _ h1, sum_callValue_of_le _ _ h2, moment, hb]
  ring

/-- **Lemma (moment).** A balanced spread with no loss has `m(t) ≤ 0`. -/
lemma moment_nonpos (t : Spread) (hb : Balanced t) (hl : NoLoss t) : moment t ≤ 0 := by
  rcases Multiset.empty_or_exists_mem (strikes t) with h | ⟨k₀, hk₀⟩
  · have h' : t.1 + t.2 = 0 := h
    rw [add_eq_zero] at h'
    simp [moment, h'.1, h'.2]
  · obtain ⟨K, hK, hmax⟩ :=
      (strikes t).toFinset.exists_max_image id ⟨k₀, Multiset.mem_toFinset.2 hk₀⟩
    rw [Multiset.mem_toFinset] at hK
    have := hl K hK
    rw [payoff_of_ge t hb K fun k hk => hmax k (Multiset.mem_toFinset.2 hk)] at this
    omega

lemma mem_strikes_of_long {t : Spread} {k : ℤ} (h : k ∈ t.1) : k ∈ strikes t :=
  Multiset.mem_add.2 (Or.inl h)

lemma mem_strikes_of_short {t : Spread} {k : ℤ} (h : k ∈ t.2) : k ∈ strikes t :=
  Multiset.mem_add.2 (Or.inr h)

/-- Four distinct strikes make at least four legs. -/
lemma four_le_legs (t : Spread) {a b c d : ℤ} (ha : a ∈ strikes t) (hb : b ∈ strikes t)
    (hc : c ∈ strikes t) (hd : d ∈ strikes t) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : 4 ≤ legs t := by
  have hsub : ({a, b, c, d} : Finset ℤ) ⊆ (strikes t).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simpa
  have hcard : ({a, b, c, d} : Finset ℤ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  exact hcard ▸ Finset.card_le_card hsub

/-- Five distinct strikes make at least five legs. -/
lemma five_le_legs (t : Spread) {a b c d e : ℤ} (ha : a ∈ strikes t) (hb : b ∈ strikes t)
    (hc : c ∈ strikes t) (hd : d ∈ strikes t) (he : e ∈ strikes t) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) : 5 ≤ legs t := by
  have hsub : ({a, b, c, d, e} : Finset ℤ) ⊆ (strikes t).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simpa
  have hcard : ({a, b, c, d, e} : Finset ℤ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
      Finset.card_insert_of_notMem (by simp [hcd, hce]), Finset.card_pair hde]
  exact hcard ▸ Finset.card_le_card hsub

end PairingHardness
