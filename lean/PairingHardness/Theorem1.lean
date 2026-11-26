module

public import PairingHardness.Butterfly

/-!
# Theorem 1: named spreads with butterflies and condors

On the butterfly instance, a pairing into the named call spreads with requirement zero
exists exactly when the numerical 3-dimensional matching instance has a matching
(docs/proofs.md, Theorem 1).

The requirements are left abstract, as in the proof, which uses only which of them are
zero: a named spread requires nothing exactly when it is a debit spread, and an uncovered
short requires a positive amount. `Named.maxLoss_eq_zero_iff_isDebit` shows that this is
also R2's maximum loss being zero.
-/

@[expose] public section

namespace PairingHardness

open Multiset

/-- A named spread with its strikes in order and its intervals equal. -/
abbrev ValidNamed := {s : Named // s.Valid}

namespace N3DM

variable {I : N3DM}

/-- The classification step of the proof. On the butterfly instance, a valid debit named
spread taken from the position holds at most two shorts for each of its longs below `M`.
It holds exactly two only when it is a butterfly `x_i / y_j / z_k` of a good triple; a
bull call spread holds one, and fact 3 rules out every long condor. -/
lemma named_debit_cases (hI : I.Valid) (hn : 1 ≤ I.n) (s : Named) (hv : s.Valid)
    (hd : s.IsDebit) (hL : s.shape.1 ≤ I.butterfly.1) (hS : s.shape.2 ≤ I.butterfly.2) :
    card s.shape.2 ≤ 2 * card (s.shape.1.filter (· < (I.M : ℤ))) ∧
    (card s.shape.2 = 2 * card (s.shape.1.filter (· < (I.M : ℤ))) →
      ∃ τ, I.Good τ ∧ s.shape = (I.bflyLongs {τ}, I.bflyShorts {τ})) := by
  have h6 := six_W_le_M hn
  have hW := hI.one_le_W
  have memL : ∀ k, k ∈ s.shape.1 → k ∈ I.butterfly.1 := fun k hk => Multiset.mem_of_le hL hk
  have memS : ∀ k, k ∈ s.shape.2 → k ∈ I.butterfly.2 := fun k hk => Multiset.mem_of_le hS hk
  cases s with
  | bull k₁ k₂ =>
    simp only [Named.shape] at memL memS ⊢
    simp only [Named.Valid] at hv
    obtain ⟨-, -, -, h1, h2⟩ := butterfly_short_bounds hI (memS k₂ (by simp))
    rcases butterfly_long_cases hI hn (memL k₁ (by simp)) with ⟨hlt, -⟩ | ⟨-, -, -, -, h3, -⟩
    · simp [Multiset.filter_singleton, hlt]
    · omega
  | longButterfly k₁ k₂ k₃ =>
    simp only [Named.shape] at memL memS ⊢
    obtain ⟨h12, h23, heq⟩ := hv
    obtain ⟨b, hb, rfl, hb1, hb2⟩ := butterfly_short_bounds hI (memS k₂ (by simp))
    rcases butterfly_long_cases hI hn (memL k₁ (by simp)) with
      ⟨hlt1, a, ha, rfl, -⟩ | ⟨-, -, -, -, h3, -⟩
    swap
    · omega
    rcases butterfly_long_cases hI hn (memL k₃ (by simp)) with
      ⟨-, -, -, -, -, h4⟩ | ⟨hlt3, c, hc, rfl, -⟩
    · omega
    refine ⟨by simp [Multiset.filter_singleton, hlt1, hlt3],
      fun _ => ⟨(a, b, c), ⟨ha, hb, hc, ?_⟩, by simp⟩⟩
    have : (I.M : ℤ) + I.bound - b - 2 * a = 2 * I.M + 2 * c - (I.M + I.bound - b) := heq
    show a + b + c = I.bound
    omega
  | longCondor k₁ k₂ k₃ k₄ =>
    exfalso
    simp only [Named.shape] at memL memS
    obtain ⟨h12, h23, h34, e1, e2⟩ := hv
    obtain ⟨-, -, -, hb1, hb2⟩ := butterfly_short_bounds hI (memS k₂ (by simp))
    obtain ⟨-, -, -, hc1, hc2⟩ := butterfly_short_bounds hI (memS k₃ (by simp))
    rcases butterfly_long_cases hI hn (memL k₁ (by simp)) with
      ⟨-, -, -, -, -, h1⟩ | ⟨-, -, -, -, h1, -⟩ <;> omega
  | bear | shortButterfly | shortCondor => simp [Named.IsDebit] at hd

/-- **Theorem 1.** Let every valid named spread have a nonnegative requirement that is zero
exactly for the debit spreads, and every uncovered short a positive one. Then the butterfly
instance has a pairing into named spreads with requirement zero exactly when the source
instance has a matching. -/
theorem theorem1 (hI : I.Valid) (req : ValidNamed → ℚ) (hreq0 : ∀ s, 0 ≤ req s)
    (hreq : ∀ s, req s = 0 ↔ s.1.IsDebit) (U : ℤ → ℚ) (hU : ∀ K, 0 < U K) :
    I.HasMatching ↔
      ∃ p : Pairing (fun s : ValidNamed => s.1.shape) I.butterfly, p.requirement req U = 0 := by
  constructor
  · intro h
    obtain ⟨p, hu, hs⟩ := exists_bfly_pairing (fun s : ValidNamed => s.1.shape) h
      (fun τ hτ => ⟨_, good_butterfly_valid hI hτ⟩) (fun τ _ => good_butterfly_shape τ)
    refine ⟨p, (p.requirement_eq_zero_iff req U hreq0 hU).2 ⟨hu, fun s hs' => ?_⟩⟩
    obtain ⟨τ, hτ, rfl⟩ := hs s hs'
    exact (hreq _).2 trivial
  · rintro ⟨p, hp⟩
    obtain ⟨hu, hz⟩ := (p.requirement_eq_zero_iff req U hreq0 hU).1 hp
    by_cases hn0 : I.n = 0
    · exact hI.hasMatching_of_n_eq_zero hn0
    have hn : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn0
    have hcases := fun (s : ValidNamed) (hs : s ∈ p.spreads) =>
      named_debit_cases hI hn s.1 s.2 ((hreq s).1 (hz s hs)) (p.longs_le' hs) (p.shorts_le hs)
    have hshorts : (p.spreads.map fun s : ValidNamed => s.1.shape.2).sum = I.butterfly.2 := by
      simpa [hu] using p.shorts_eq
    -- Counting: the shorts number `2n`, and the longs below `M` at most `n`.
    have h1 : (p.spreads.map fun s : ValidNamed => card s.1.shape.2).sum = 2 * I.n := by
      rw [← card_list_sum, hshorts]
      simp [butterfly, hI.1]
      ring
    have h2 : (p.spreads.map fun s : ValidNamed =>
        card (s.1.shape.1.filter (· < (I.M : ℤ)))).sum ≤ I.n := by
      rw [← card_list_sum, ← filter_list_sum]
      calc card ((p.spreads.map fun s : ValidNamed => s.1.shape.1).sum.filter (· < (I.M : ℤ)))
          ≤ card (I.butterfly.1.filter (· < (I.M : ℤ))) :=
            Multiset.card_le_card (Multiset.filter_le_filter _ p.longs_le)
        _ = I.n := by rw [butterfly_longs_filter hI hn, Multiset.card_map]; rfl
    have hcount := list_eq_of_le_of_sum_le p.spreads
      (fun s : ValidNamed => 2 * card (s.1.shape.1.filter (· < (I.M : ℤ))))
      (fun s : ValidNamed => card s.1.shape.2)
      (fun s hs => (hcases s hs).1) (by rw [List.sum_map_mul_left]; omega)
    -- So every spread is a butterfly of a good triple.
    have hall : ∀ s ∈ p.spreads, ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, I.Good τ) ∧
        s.1.shape.1 = I.bflyLongs T ∧ s.1.shape.2 = I.bflyShorts T := by
      intro s hs
      obtain ⟨τ, hτ, he⟩ := (hcases s hs).2 (hcount s hs).symm
      exact ⟨{τ}, by simpa using hτ, by rw [he], by rw [he]⟩
    obtain ⟨T, hT, hL, hS⟩ :=
      exists_triples_of_forall (fun s : ValidNamed => s.1.shape) I.Good _ _ p.spreads hall
    exact hasMatching_of_bfly hI T hT (hL ▸ p.longs_le) (hS ▸ hshorts)

end N3DM

end PairingHardness
