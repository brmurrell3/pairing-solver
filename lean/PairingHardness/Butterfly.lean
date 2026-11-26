module

public import PairingHardness.Named

/-!
# The butterfly instance

The reduction of Theorem 1 (docs/proofs.md, "Hardness"): from `(a, b, c, B)` build

    long one call at   x_i = 2 a_i             for each i
    short two calls at y_j = M + B − b_j       for each j
    long one call at   z_k = 2M + 2 c_k        for each k

with `M = 6nW`. This file defines it, proves its facts 1 to 3 and its size, and shows how a
decomposition into butterflies gives back a matching.
-/

@[expose] public section

namespace PairingHardness

open Multiset

namespace N3DM

variable (I : N3DM)

/-- `x = 2a`. -/
def bx (a : ℕ) : ℤ := 2 * a
/-- `y = M + B − b`. -/
def byy (b : ℕ) : ℤ := I.M + I.bound - b
/-- `z = 2M + 2c`. -/
def bz (c : ℕ) : ℤ := 2 * I.M + 2 * c

/-- The butterfly instance. -/
def butterfly : Spread := (I.A.map bx + I.C.map I.bz, I.B.map I.byy + I.B.map I.byy)

/-- The long contracts of butterflies `x_i / y_j / z_k`, one for each triple. -/
def bflyLongs : Multiset (ℕ × ℕ × ℕ) →+ Multiset ℤ :=
  mapAddMonoidHom (fun τ => bx τ.1) + mapAddMonoidHom (fun τ => I.bz τ.2.2)

/-- The short contracts of the same butterflies. -/
def bflyShorts : Multiset (ℕ × ℕ × ℕ) →+ Multiset ℤ :=
  mapAddMonoidHom (fun τ => I.byy τ.2.1) + mapAddMonoidHom (fun τ => I.byy τ.2.1)

@[simp] lemma bflyLongs_apply (T : Multiset (ℕ × ℕ × ℕ)) :
    I.bflyLongs T = T.map (fun τ => bx τ.1) + T.map (fun τ => I.bz τ.2.2) := rfl

@[simp] lemma bflyShorts_apply (T : Multiset (ℕ × ℕ × ℕ)) :
    I.bflyShorts T = T.map (fun τ => I.byy τ.2.1) + T.map (fun τ => I.byy τ.2.1) := rfl

lemma bx_injective : Function.Injective bx := fun a b h => by simp only [bx] at h; omega
lemma byy_injective : Function.Injective I.byy := fun a b h => by simp only [byy] at h; omega
lemma bz_injective : Function.Injective I.bz := fun a b h => by simp only [bz] at h; omega

variable {I}

lemma one_le_n_of_mem {a : ℕ} (h : a ∈ I.A) : 1 ≤ I.n :=
  Multiset.card_pos_iff_exists_mem.2 ⟨a, h⟩

/-- `M ≥ 6W` once there is a triple. -/
lemma six_W_le_M (hn : 1 ≤ I.n) : 6 * (I.W : ℤ) ≤ I.M := by
  have : 6 * I.W ≤ I.M := by
    unfold N3DM.M; nlinarith [Nat.zero_le I.W]
  exact_mod_cast this

lemma M_eq : (I.M : ℤ) = 6 * I.n * I.W := by simp [N3DM.M]

lemma bx_bounds (hI : I.Valid) {a : ℕ} (h : a ∈ I.A) : 2 ≤ bx a ∧ bx a ≤ 2 * I.W := by
  have := hI.A_pos h; have := I.A_le_W h; simp only [bx]; omega

lemma byy_bounds (hI : I.Valid) {b : ℕ} (h : b ∈ I.B) :
    I.M + 1 - I.W ≤ I.byy b ∧ I.byy b ≤ I.M + I.W - 1 := by
  have := hI.B_pos h; have := I.B_le_W h; have := I.bound_le_W; have := hI.2.2.1
  simp only [byy]; omega

lemma bz_bounds (hI : I.Valid) {c : ℕ} (h : c ∈ I.C) :
    2 * I.M + 2 ≤ I.bz c ∧ I.bz c ≤ 2 * I.M + 2 * I.W := by
  have := hI.C_pos h; have := I.C_le_W h; simp only [bz]; omega

lemma mem_butterfly_longs {k : ℤ} :
    k ∈ I.butterfly.1 ↔ (∃ a ∈ I.A, bx a = k) ∨ (∃ c ∈ I.C, I.bz c = k) := by
  simp [butterfly]

lemma mem_butterfly_shorts {k : ℤ} : k ∈ I.butterfly.2 ↔ ∃ b ∈ I.B, I.byy b = k := by
  simp [butterfly]

/-- Fact 1 and the split at `M`: a long below `M` is an `x`, any other long is a `z`, and
the shorts lie strictly between. -/
lemma butterfly_long_cases (hI : I.Valid) (hn : 1 ≤ I.n) {k : ℤ} (hk : k ∈ I.butterfly.1) :
    (k < I.M ∧ ∃ a ∈ I.A, bx a = k ∧ 2 ≤ k ∧ k ≤ 2 * I.W) ∨
    (¬ k < I.M ∧ ∃ c ∈ I.C, I.bz c = k ∧ 2 * I.M + 2 ≤ k ∧ k ≤ 2 * I.M + 2 * I.W) := by
  have h6 := six_W_le_M hn
  rcases mem_butterfly_longs.1 hk with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
  · have := bx_bounds hI ha
    exact Or.inl ⟨by omega, a, ha, rfl, this⟩
  · have hb := bz_bounds hI hc
    have := hI.one_le_W
    exact Or.inr ⟨by omega, c, hc, rfl, hb⟩

lemma butterfly_short_bounds (hI : I.Valid) {k : ℤ} (hk : k ∈ I.butterfly.2) :
    ∃ b ∈ I.B, I.byy b = k ∧ I.M + 1 - I.W ≤ k ∧ k ≤ I.M + I.W - 1 := by
  obtain ⟨b, hb, rfl⟩ := mem_butterfly_shorts.1 hk
  exact ⟨b, hb, rfl, byy_bounds hI hb⟩

/-- The longs of the butterfly instance below `M` are exactly the `x`. -/
lemma butterfly_longs_filter (hI : I.Valid) (hn : 1 ≤ I.n) :
    I.butterfly.1.filter (· < (I.M : ℤ)) = I.A.map bx := by
  have h6 := six_W_le_M hn
  have hW := hI.one_le_W
  rw [butterfly, Multiset.filter_add, Multiset.filter_eq_self.2, Multiset.filter_eq_nil.2,
    add_zero]
  · intro k hk
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hk
    have := bz_bounds hI hc; omega
  · intro k hk
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hk
    have := bx_bounds hI ha; omega

/-- **Size.** The butterfly instance has `4n` contracts, at positive strikes of at most
`2M + 2W = 12nW + 2W`. -/
theorem butterfly_size (hI : I.Valid) :
    card I.butterfly.1 + card I.butterfly.2 = 4 * I.n ∧
    ∀ k ∈ strikes I.butterfly, 0 < k ∧ k ≤ 2 * I.M + 2 * I.W := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [butterfly, hI.1, hI.2.1, N3DM.n]; ring
  · have hn : 1 ≤ I.n := by
      rcases Multiset.mem_add.1 hk with hk | hk
      · rcases mem_butterfly_longs.1 hk with ⟨a, ha, -⟩ | ⟨c, hc, -⟩
        · exact one_le_n_of_mem ha
        · exact (hI.2.1 ▸ Multiset.card_pos_iff_exists_mem.2 ⟨c, hc⟩ : 0 < I.n)
      · obtain ⟨b, hb, -⟩ := mem_butterfly_shorts.1 hk
        exact (hI.1 ▸ Multiset.card_pos_iff_exists_mem.2 ⟨b, hb⟩ : 0 < I.n)
    have h6 := six_W_le_M hn
    have := hI.one_le_W
    rcases Multiset.mem_add.1 hk with hk | hk
    · rcases butterfly_long_cases hI hn hk with ⟨-, -, -, -, h1, h2⟩ | ⟨-, -, -, -, h1, h2⟩ <;>
        constructor <;> omega
    · obtain ⟨-, -, -, h1, h2⟩ := butterfly_short_bounds hI hk
      constructor <;> omega

/-- A butterfly `x_i / y_j / z_k` from a good triple is in order with equal intervals
(facts 1 and 2). -/
lemma good_butterfly_valid (hI : I.Valid) {τ : ℕ × ℕ × ℕ} (h : I.Good τ) :
    (Named.longButterfly (bx τ.1) (I.byy τ.2.1) (I.bz τ.2.2)).Valid := by
  obtain ⟨ha, hb, hc, hs⟩ := h
  have hn := one_le_n_of_mem ha
  have h6 := six_W_le_M hn
  have := bx_bounds hI ha; have := byy_bounds hI hb; have := bz_bounds hI hc
  refine ⟨by omega, by omega, ?_⟩
  simp only [bx, byy, bz]
  have : (τ.1 : ℤ) + τ.2.1 + τ.2.2 = I.bound := by exact_mod_cast hs
  omega

lemma good_butterfly_shape (τ : ℕ × ℕ × ℕ) :
    (Named.longButterfly (bx τ.1) (I.byy τ.2.1) (I.bz τ.2.2)).shape =
      (I.bflyLongs {τ}, I.bflyShorts {τ}) := by
  simp [Named.shape]

/-- **Decoding.** Butterflies from good triples that cover every short of the butterfly
instance, using longs it holds, come from a matching. -/
theorem hasMatching_of_bfly (hI : I.Valid) (T : Multiset (ℕ × ℕ × ℕ))
    (hT : ∀ τ ∈ T, I.Good τ) (hL : I.bflyLongs T ≤ I.butterfly.1)
    (hS : I.bflyShorts T = I.butterfly.2) : I.HasMatching := by
  by_cases hn0 : I.n = 0
  · exact hI.hasMatching_of_n_eq_zero hn0
  have hn : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn0
  have h6 := six_W_le_M hn
  have hW := hI.one_le_W
  have hcardT : card T = I.n := by
    have := congrArg card hS
    simp [butterfly, hI.1] at this
    omega
  have hLeq : I.bflyLongs T = I.butterfly.1 := by
    refine Multiset.eq_of_le_of_card_le hL ?_
    simp [butterfly, hI.2.1, hcardT, N3DM.n]
  have hAC := decode_add bx_injective I.bz_injective I.M
    (A := T.map (·.1)) (C := T.map (·.2.2)) (A' := I.A) (C' := I.C)
    (by
      intro a ha
      have ha : a ∈ I.A := by
        rcases Multiset.mem_add.1 ha with ha | ha
        · obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 ha; exact (hT τ hτ).1
        · exact ha
      have := bx_bounds hI ha; omega)
    (by
      intro c hc
      have hc : c ∈ I.C := by
        rcases Multiset.mem_add.1 hc with hc | hc
        · obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hc; exact (hT τ hτ).2.2.1
        · exact hc
      have := bz_bounds hI hc; omega)
    (by rw [Multiset.map_map, Multiset.map_map]; exact hLeq)
  have hB : T.map (·.2.1) = I.B := by
    refine Multiset.map_injective I.byy_injective ?_
    rw [Multiset.map_map]
    ext k
    have := congrArg (Multiset.count k) hS
    simp only [bflyShorts_apply, butterfly, Multiset.count_add] at this
    simp only [Function.comp_def]
    omega
  exact hasMatching_of_good T hT hAC.1 hB hAC.2

/-- A matching gives a pairing of the butterfly instance into butterflies `x_i / y_j / z_k`
that leaves no short uncovered. -/
lemma exists_bfly_pairing {σ : Type} (shape : σ → Spread) (h : I.HasMatching)
    (mk : ∀ τ, I.Good τ → σ) (hmk : ∀ τ h, shape (mk τ h) = (I.bflyLongs {τ}, I.bflyShorts {τ})) :
    ∃ p : Pairing shape I.butterfly, p.uncovered = 0 ∧ ∀ s ∈ p.spreads, ∃ τ h, s = mk τ h := by
  obtain ⟨T, hT, hA, hB, hC⟩ := h.exists_good
  refine exists_pairing_of_triples shape I.butterfly I.bflyLongs I.bflyShorts I.Good T hT mk hmk
    (le_of_eq ?_) ?_
  · simp only [bflyLongs_apply, butterfly, ← hA, ← hC, Multiset.map_map, Function.comp_def]
  · simp only [bflyShorts_apply, butterfly, ← hB, Multiset.map_map, Function.comp_def]

end N3DM

end PairingHardness
