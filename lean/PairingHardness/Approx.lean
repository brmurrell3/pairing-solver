module

public import PairingHardness.Theorem2Four

/-!
# No approximation within any factor

Theorems 1 and 2 separate a requirement of zero from a positive one. When every positive
requirement on the instance is at least some `μ > 0`, a source instance with no matching
has no pairing below `μ` (docs/proofs.md, "Not approximable"). The paper then prices the
instance so that the long premiums, the same for every pairing, are at most `μ / ρ`, which
gives the ratio `1 + ρ`. That pricing step (R3 bounds and the premium bound) is in the
paper and `tools/check_approx_expiry.py`, not here.
-/

@[expose] public section

namespace PairingHardness

namespace Pairing

variable {σ : Type} {shape : σ → Spread} {pos : Spread}

lemma le_list_sum_of_mem {α : Type} (l : List α) (f : α → ℚ) (hf : ∀ a, 0 ≤ f a) :
    ∀ a ∈ l, f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have h0 : 0 ≤ (l.map f).sum := List.sum_nonneg (by simp [hf])
    intro a ha
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ha with rfl | ha
    · linarith
    · linarith [ih a ha, hf b]

/-- If every spread requires either nothing or at least `μ`, and every uncovered short at
least `μ > 0`, then a pairing requires nothing or at least `μ`. -/
lemma requirement_eq_zero_or_ge (p : Pairing shape pos) (req : σ → ℚ) (U : ℤ → ℚ) (μ : ℚ)
    (hμ : 0 < μ) (hreq : ∀ s, 0 ≤ req s) (hgap : ∀ s, req s = 0 ∨ μ ≤ req s)
    (hU : ∀ K, μ ≤ U K) :
    p.requirement req U = 0 ∨ μ ≤ p.requirement req U := by
  have hU0 : ∀ K, 0 < U K := fun K => lt_of_lt_of_le hμ (hU K)
  have h1 : 0 ≤ (p.spreads.map req).sum := List.sum_nonneg (by simp [hreq])
  have h2 : 0 ≤ (p.uncovered.map U).sum :=
    Multiset.sum_nonneg (by simp only [Multiset.mem_map]; rintro _ ⟨K, _, rfl⟩; exact (hU0 K).le)
  by_cases hu : p.uncovered = 0
  · by_cases hs : ∀ s ∈ p.spreads, req s = 0
    · exact Or.inl ((p.requirement_eq_zero_iff req U hreq hU0).2 ⟨hu, hs⟩)
    · right
      push Not at hs
      obtain ⟨s, hs, hne⟩ := hs
      have hle := le_list_sum_of_mem p.spreads req hreq s hs
      have hμs := (hgap s).resolve_left hne
      unfold requirement
      linarith
  · right
    obtain ⟨K, hK⟩ := Multiset.exists_mem_of_ne_zero hu
    have hle : U K ≤ (p.uncovered.map U).sum :=
      Multiset.single_le_sum
        (by simp only [Multiset.mem_map]; rintro _ ⟨K, _, rfl⟩; exact (hU0 K).le)
        _ (Multiset.mem_map_of_mem U hK)
    unfold requirement
    linarith [hU K]

end Pairing

namespace N3DM

variable {I : N3DM}

/-- **Theorem 1, gap form.** If every valid named spread that is not a debit spread requires
at least `μ > 0`, and so does every uncovered short, then on a source instance with no
matching every pairing of the butterfly instance requires at least `μ`. -/
theorem theorem1_gap (hI : I.Valid) (req : ValidNamed → ℚ) (hreq0 : ∀ s, 0 ≤ req s)
    (hreq : ∀ s, req s = 0 ↔ s.1.IsDebit) (U : ℤ → ℚ) (μ : ℚ) (hμ : 0 < μ)
    (hcredit : ∀ s : ValidNamed, ¬ s.1.IsDebit → μ ≤ req s) (hU : ∀ K, μ ≤ U K)
    (hno : ¬ I.HasMatching) (p : Pairing (fun s : ValidNamed => s.1.shape) I.butterfly) :
    μ ≤ p.requirement req U := by
  have hU0 : ∀ K, 0 < U K := fun K => lt_of_lt_of_le hμ (hU K)
  have hgap : ∀ s, req s = 0 ∨ μ ≤ req s := fun s => by
    by_cases hd : s.1.IsDebit
    · exact Or.inl ((hreq s).2 hd)
    · exact Or.inr (hcredit s hd)
  rcases p.requirement_eq_zero_or_ge req U μ hμ hreq0 hgap hU with h | h
  · exact absurd ((theorem1 hI req hreq0 hreq U hU0).2 ⟨p, h⟩) hno
  · exact h

/-- **Theorem 2 with at most three legs, gap form.** -/
theorem theorem2_three_gap (hI : I.Valid) (F : Spread → Prop) (hbal : ∀ t, F t → Balanced t)
    (hlegs : ∀ t, F t → legs t ≤ 3)
    (hbfly : ∀ k₁ k₂ k₃ : ℤ, k₁ < k₂ → k₂ < k₃ → k₂ - k₁ = k₃ - k₂ →
      F (Named.longButterfly k₁ k₂ k₃).shape)
    (req : Subtype F → ℚ) (hreq0 : ∀ t, 0 ≤ req t) (hreq : ∀ t, req t = 0 ↔ maxLoss t.1 = 0)
    (U : ℤ → ℚ) (μ : ℚ) (hμ : 0 < μ) (hloss : ∀ t, maxLoss t.1 ≠ 0 → μ ≤ req t)
    (hU : ∀ K, μ ≤ U K) (hno : ¬ I.HasMatching)
    (p : Pairing (Subtype.val : Subtype F → Spread) I.reduce3) :
    μ ≤ p.requirement req U := by
  have hU0 : ∀ K, 0 < U K := fun K => lt_of_lt_of_le hμ (hU K)
  have hgap : ∀ t, req t = 0 ∨ μ ≤ req t := fun t => by
    by_cases hd : maxLoss t.1 = 0
    · exact Or.inl ((hreq t).2 hd)
    · exact Or.inr (hloss t hd)
  rcases p.requirement_eq_zero_or_ge req U μ hμ hreq0 hgap hU with h | h
  · exact absurd ((theorem2_three hI F hbal hlegs hbfly req hreq0 hreq U hU0).2 ⟨p, h⟩) hno
  · exact h

/-- **Theorem 2 with at most four legs, gap form.** -/
theorem theorem2_four_gap (hI : I.Valid) (F : Spread → Prop) (hbal : ∀ t, F t → Balanced t)
    (hlegs : ∀ t, F t → legs t ≤ 4)
    (hcondor : ∀ k₁ k₂ k₃ k₄ : ℤ, k₁ < k₂ → k₂ < k₃ → k₃ < k₄ → k₂ - k₁ = k₄ - k₃ →
      F (Named.longCondor k₁ k₂ k₃ k₄).shape)
    (req : Subtype F → ℚ) (hreq0 : ∀ t, 0 ≤ req t) (hreq : ∀ t, req t = 0 ↔ maxLoss t.1 = 0)
    (U : ℤ → ℚ) (μ : ℚ) (hμ : 0 < μ) (hloss : ∀ t, maxLoss t.1 ≠ 0 → μ ≤ req t)
    (hU : ∀ K, μ ≤ U K) (hno : ¬ I.HasMatching)
    (p : Pairing (Subtype.val : Subtype F → Spread) I.reduce4) :
    μ ≤ p.requirement req U := by
  have hU0 : ∀ K, 0 < U K := fun K => lt_of_lt_of_le hμ (hU K)
  have hgap : ∀ t, req t = 0 ∨ μ ≤ req t := fun t => by
    by_cases hd : maxLoss t.1 = 0
    · exact Or.inl ((hreq t).2 hd)
    · exact Or.inr (hloss t hd)
  rcases p.requirement_eq_zero_or_ge req U μ hμ hreq0 hgap hU with h | h
  · exact absurd ((theorem2_four hI F hbal hlegs hcondor req hreq0 hreq U hU0).2 ⟨p, h⟩) hno
  · exact h

end N3DM

end PairingHardness
