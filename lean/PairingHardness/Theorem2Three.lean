module

public import PairingHardness.Theorem1

/-!
# Theorem 2 with at most three legs

Any family of balanced call spreads of at most three legs, in which a spread requires
nothing exactly when its maximum loss is zero, and which contains every long butterfly with
equal intervals. On the butterfly instance (after a check of the totals) a pairing with
requirement zero exists exactly when the source instance has a matching
(docs/proofs.md, Theorem 2, `ℓ = 3`).
-/

@[expose] public section

namespace PairingHardness

open Multiset

namespace N3DM

variable {I : N3DM}

/-- The moment of the whole butterfly instance: `2(ΣA + ΣB + ΣC − nB)`. -/
lemma moment_butterfly (hI : I.Valid) :
    moment I.butterfly = 2 * ((I.A.sum : ℤ) + I.B.sum + I.C.sum - I.n * I.bound) := by
  have hB : (card I.B : ℤ) = I.n := by exact_mod_cast hI.1
  have hC : (card I.C : ℤ) = I.n := by exact_mod_cast hI.2.1
  have eA : (I.A.map bx).sum = 2 * (I.A.sum : ℤ) := by
    show (I.A.map fun a : ℕ => 2 * (a : ℤ)).sum = _
    rw [Multiset.sum_map_mul_left, Nat.cast_multiset_sum]
  have eC : (I.C.map I.bz).sum = I.n * (2 * I.M) + 2 * (I.C.sum : ℤ) := by
    show (I.C.map fun c : ℕ => 2 * (I.M : ℤ) + 2 * c).sum = _
    rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hC,
      Multiset.sum_map_mul_left, Nat.cast_multiset_sum]
  have eB : (I.B.map I.byy).sum = I.n * (I.M + I.bound) - (I.B.sum : ℤ) := by
    show (I.B.map fun b : ℕ => (I.M : ℤ) + I.bound - b).sum = _
    rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hB,
      Nat.cast_multiset_sum]
  simp only [moment, butterfly, Multiset.sum_add, eA, eB, eC]
  ring

/-- The per-spread step of the proof. A balanced spread of at most three legs with moment
zero, taken from the butterfly instance, is some number of copies of the butterfly of one
good triple. -/
lemma bfly_three (hI : I.Valid) (hn : 1 ≤ I.n) (t : Spread) (hb : Balanced t)
    (hlegs : legs t ≤ 3) (hm : moment t = 0) (hL : t.1 ≤ I.butterfly.1)
    (hS : t.2 ≤ I.butterfly.2) :
    ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, I.Good τ) ∧ t.1 = I.bflyLongs T ∧
      t.2 = I.bflyShorts T := by
  have h6 := six_W_le_M hn
  have hW := hI.one_le_W
  have hMe : (I.M : ℤ) = 6 * I.n * I.W := M_eq
  by_cases h0 : t.2 = 0
  · refine ⟨0, by simp, ?_, by simp [h0]⟩
    have : card t.1 = 0 := by rw [hb, h0]; rfl
    simpa using this
  set Lx := t.1.filter (· < (I.M : ℤ)) with hLx
  set Lz := t.1.filter (fun k => ¬ k < (I.M : ℤ)) with hLz
  have hsplit : Lx + Lz = t.1 := Multiset.filter_add_not _ _
  have memL : ∀ k ∈ t.1, k ∈ I.butterfly.1 := fun k hk => Multiset.mem_of_le hL hk
  have hx : ∀ k ∈ Lx, ∃ a ∈ I.A, bx a = k ∧ 2 ≤ k ∧ k ≤ 2 * I.W := by
    intro k hk
    rw [hLx, Multiset.mem_filter] at hk
    rcases butterfly_long_cases hI hn (memL k hk.1) with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hk.2 h
  have hz : ∀ k ∈ Lz, ∃ c ∈ I.C, I.bz c = k ∧ 2 * I.M + 2 ≤ k ∧ k ≤ 2 * I.M + 2 * I.W := by
    intro k hk
    rw [hLz, Multiset.mem_filter] at hk
    rcases butterfly_long_cases hI hn (memL k hk.1) with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hk.2
    · exact h
  have hy : ∀ k ∈ t.2, ∃ b ∈ I.B, I.byy b = k ∧ I.M + 1 - I.W ≤ k ∧ k ≤ I.M + I.W - 1 :=
    fun k hk => butterfly_short_bounds hI (Multiset.mem_of_le hS hk)
  -- Bounds on the three sums.
  have sx1 : (card Lx : ℤ) * 2 ≤ Lx.sum := by
    rw [← nsmul_eq_mul]
    exact Multiset.card_nsmul_le_sum fun k hk => by obtain ⟨_, _, _, h, _⟩ := hx k hk; exact h
  have sx2 : Lx.sum ≤ (card Lx : ℤ) * (2 * I.W) := by
    rw [← nsmul_eq_mul]
    exact Multiset.sum_le_card_nsmul _ _ fun k hk => by obtain ⟨_, _, _, _, h⟩ := hx k hk; exact h
  have sz1 : (card Lz : ℤ) * (2 * I.M + 2) ≤ Lz.sum := by
    rw [← nsmul_eq_mul]
    exact Multiset.card_nsmul_le_sum fun k hk => by obtain ⟨_, _, _, h, _⟩ := hz k hk; exact h
  have sz2 : Lz.sum ≤ (card Lz : ℤ) * (2 * I.M + 2 * I.W) := by
    rw [← nsmul_eq_mul]
    exact Multiset.sum_le_card_nsmul _ _ fun k hk => by obtain ⟨_, _, _, _, h⟩ := hz k hk; exact h
  have sy1 : (card t.2 : ℤ) * (I.M + 1 - I.W) ≤ t.2.sum := by
    rw [← nsmul_eq_mul]
    exact Multiset.card_nsmul_le_sum fun k hk => by obtain ⟨_, _, _, h, _⟩ := hy k hk; exact h
  have sy2 : t.2.sum ≤ (card t.2 : ℤ) * (I.M + I.W - 1) := by
    rw [← nsmul_eq_mul]
    exact Multiset.sum_le_card_nsmul _ _ fun k hk => by obtain ⟨_, _, _, _, h⟩ := hy k hk; exact h
  have hcard : (card Lx : ℤ) + card Lz = card t.2 := by
    have := congrArg card hsplit
    rw [Multiset.card_add] at this
    rw [← hb]; exact_mod_cast this
  have hγ : (card t.2 : ℤ) ≤ 2 * I.n := by
    have := Multiset.card_le_card hS
    simp [butterfly, hI.1] at this
    omega
  have hγ1 : (1 : ℤ) ≤ card t.2 := by
    have := Multiset.card_pos.2 h0; omega
  have hsum : Lx.sum + Lz.sum - t.2.sum = 0 := by
    rw [← Multiset.sum_add, hsplit]; exact hm
  -- The moment fixes the number of shorts: `γ = 2β`.
  have key : (card t.2 : ℤ) = 2 * card Lz := by
    set α : ℤ := (card Lx : ℤ)
    set β : ℤ := (card Lz : ℤ)
    set γ : ℤ := (card t.2 : ℤ)
    rcases lt_trichotomy γ (2 * β) with h | h | h
    · exfalso
      have e1 : (I.M : ℤ) * 1 ≤ I.M * (2 * β - γ) :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have e2 : ((I.W : ℤ) - 1) * γ ≤ ((I.W : ℤ) - 1) * (2 * I.n) :=
        mul_le_mul_of_nonneg_left hγ (by omega)
      have e3 : (0 : ℤ) ≤ α := by positivity
      nlinarith
    · exact h
    · exfalso
      have e1 : (I.M : ℤ) * 1 ≤ I.M * (γ - 2 * β) :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have e2 : ((3 * I.W : ℤ) - 1) * γ ≤ ((3 * I.W : ℤ) - 1) * (2 * I.n) :=
        mul_le_mul_of_nonneg_left hγ (by omega)
      nlinarith
  have hαβ : card Lx = card Lz := by omega
  have hβ1 : 1 ≤ card Lz := by omega
  -- Each of the three kinds of strike holds one strike only: else four legs.
  obtain ⟨p₀, hp₀⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < card Lx by omega)
  obtain ⟨q₀, hq₀⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < card Lz by omega)
  obtain ⟨r₀, hr₀⟩ := Multiset.exists_mem_of_ne_zero h0
  have sLx : ∀ k ∈ Lx, k ∈ strikes t := fun k hk =>
    mem_strikes_of_long (Multiset.mem_of_mem_filter hk)
  have sLz : ∀ k ∈ Lz, k ∈ strikes t := fun k hk =>
    mem_strikes_of_long (Multiset.mem_of_mem_filter hk)
  have sS : ∀ k ∈ t.2, k ∈ strikes t := fun k hk => mem_strikes_of_short hk
  obtain ⟨-, -, -, p1, p2⟩ := hx p₀ hp₀
  obtain ⟨-, -, -, q1, q2⟩ := hz q₀ hq₀
  obtain ⟨-, -, -, r1, r2⟩ := hy r₀ hr₀
  have eLx : Lx = replicate (card Lx) p₀ := by
    refine Multiset.eq_replicate.2 ⟨rfl, fun k hk => ?_⟩
    by_contra hne
    obtain ⟨-, -, -, k1, k2⟩ := hx k hk
    have := four_le_legs t (sLx k hk) (sLx p₀ hp₀) (sLz q₀ hq₀) (sS r₀ hr₀)
      hne (by omega) (by omega) (by omega) (by omega) (by omega)
    omega
  have eLz : Lz = replicate (card Lz) q₀ := by
    refine Multiset.eq_replicate.2 ⟨rfl, fun k hk => ?_⟩
    by_contra hne
    obtain ⟨-, -, -, k1, k2⟩ := hz k hk
    have := four_le_legs t (sLz k hk) (sLz q₀ hq₀) (sLx p₀ hp₀) (sS r₀ hr₀)
      hne (by omega) (by omega) (by omega) (by omega) (by omega)
    omega
  have eS : t.2 = replicate (card t.2) r₀ := by
    refine Multiset.eq_replicate.2 ⟨rfl, fun k hk => ?_⟩
    by_contra hne
    obtain ⟨-, -, -, k1, k2⟩ := hy k hk
    have := four_le_legs t (sS k hk) (sS r₀ hr₀) (sLx p₀ hp₀) (sLz q₀ hq₀)
      hne (by omega) (by omega) (by omega) (by omega) (by omega)
    omega
  -- The one triple has sum `B`.
  obtain ⟨a, ha, rfl, -⟩ := hx p₀ hp₀
  obtain ⟨c, hc, rfl, -⟩ := hz _ hq₀
  obtain ⟨b, hb', rfl, -⟩ := hy _ hr₀
  have hsum' : (card Lz : ℤ) * (bx a + I.bz c - 2 * I.byy b) = 0 := by
    rw [eLx, eLz, eS] at hsum
    simp only [Multiset.sum_replicate, nsmul_eq_mul] at hsum
    rw [hαβ] at hsum
    push_cast [key] at hsum
    linarith
  have hgood : I.Good (a, b, c) := by
    refine ⟨ha, hb', hc, ?_⟩
    have h' : bx a + I.bz c - 2 * I.byy b = 0 := by
      rcases mul_eq_zero.1 hsum' with h | h
      · omega
      · exact h
    simp only [bx, bz, byy] at h'
    show a + b + c = I.bound
    omega
  refine ⟨replicate (card Lz) (a, b, c), fun τ hτ => ?_, ?_, ?_⟩
  · rw [Multiset.eq_of_mem_replicate hτ]; exact hgood
  · rw [← hsplit, eLx, eLz, hαβ]; simp [Multiset.map_replicate]
  · rw [eS]
    simp only [bflyShorts_apply, Multiset.map_replicate]
    rw [← Multiset.replicate_add]
    congr 1
    omega

/-- The reduction of Theorem 2 for `ℓ = 3`: the butterfly instance when the totals add up,
and one uncovered short call otherwise. -/
def reduce3 (I : N3DM) : Spread :=
  if I.A.sum + I.B.sum + I.C.sum = I.n * I.bound then I.butterfly else (0, {1})

/-- No pairing covers a lone short call at zero: its shorts would need longs. -/
lemma no_cover_lone_short {σ : Type} {shape : σ → Spread} {pos : Spread}
    (hbal : ∀ s, Balanced (shape s)) (p : Pairing shape pos) (hpos : pos = (0, {1}))
    (hu : p.uncovered = 0) : False := by
  subst hpos
  have h1 := congrArg card p.shorts_eq
  have h2 := Multiset.card_le_card p.longs_le
  rw [hu, add_zero, card_list_sum] at h1
  rw [card_list_sum] at h2
  simp only [Balanced] at hbal
  have : (p.spreads.map fun s => card (shape s).1) = p.spreads.map fun s => card (shape s).2 :=
    List.map_congr_left fun s _ => hbal s
  rw [this] at h2
  simp at h1 h2
  omega

/-- **Theorem 2, `ℓ = 3`.** Let `F` be any family of balanced spreads of at most three legs
that contains every long butterfly with equal intervals, with nonnegative requirements that
are zero exactly when the maximum loss is, and a positive requirement for each uncovered
short. Then `reduce3 I` has a pairing into `F` with requirement zero exactly when `I` has a
matching. -/
theorem theorem2_three (hI : I.Valid) (F : Spread → Prop) (hbal : ∀ t, F t → Balanced t)
    (hlegs : ∀ t, F t → legs t ≤ 3)
    (hbfly : ∀ k₁ k₂ k₃ : ℤ, k₁ < k₂ → k₂ < k₃ → k₂ - k₁ = k₃ - k₂ →
      F (Named.longButterfly k₁ k₂ k₃).shape)
    (req : Subtype F → ℚ) (hreq0 : ∀ t, 0 ≤ req t) (hreq : ∀ t, req t = 0 ↔ maxLoss t.1 = 0)
    (U : ℤ → ℚ) (hU : ∀ K, 0 < U K) :
    I.HasMatching ↔
      ∃ p : Pairing (Subtype.val : Subtype F → Spread) I.reduce3, p.requirement req U = 0 := by
  constructor
  · intro h
    have hr : I.reduce3 = I.butterfly := ite_eq_left_of_eq_true _ _ (eq_true h.sum_eq)
    rw [hr]
    obtain ⟨p, hu, hs⟩ := exists_bfly_pairing (Subtype.val : Subtype F → Spread) h
      (fun τ hτ => ⟨_, (good_butterfly_shape τ) ▸
        hbfly _ _ _ (good_butterfly_valid hI hτ).1 (good_butterfly_valid hI hτ).2.1
          (good_butterfly_valid hI hτ).2.2⟩)
      (fun τ _ => rfl)
    refine ⟨p, (p.requirement_eq_zero_iff req U hreq0 hU).2 ⟨hu, fun s hs' => ?_⟩⟩
    obtain ⟨τ, hτ, rfl⟩ := hs s hs'
    rw [hreq]
    show maxLoss (I.bflyLongs {τ}, I.bflyShorts {τ}) = 0
    rw [← good_butterfly_shape]
    exact (Named.maxLoss_eq_zero_iff_isDebit _ (good_butterfly_valid hI hτ)).2 trivial
  · intro hex
    by_cases hsum : I.A.sum + I.B.sum + I.C.sum = I.n * I.bound
    swap
    · obtain ⟨p, hp⟩ := hex
      have hu := ((p.requirement_eq_zero_iff req U hreq0 hU).1 hp).1
      exact (no_cover_lone_short (fun s => hbal _ s.2) p
        (ite_eq_right_of_eq_false _ _ (eq_false hsum)) hu).elim
    have hr : I.reduce3 = I.butterfly := ite_eq_left_of_eq_true _ _ (eq_true hsum)
    rw [hr] at hex
    obtain ⟨p, hp⟩ := hex
    obtain ⟨hu, hz⟩ := (p.requirement_eq_zero_iff req U hreq0 hU).1 hp
    have hnl : ∀ s ∈ p.spreads, NoLoss s.1 := fun s hs =>
      (maxLoss_eq_zero_iff _).1 ((hreq s).1 (hz s hs))
    by_cases hn0 : I.n = 0
    · exact hI.hasMatching_of_n_eq_zero hn0
    have hn : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn0
    have hshorts : (p.spreads.map fun s : Subtype F => s.1.2).sum = I.butterfly.2 := by
      have := p.shorts_eq; rw [hu, add_zero] at this; exact this
    have hlongs_le : (p.spreads.map fun s : Subtype F => s.1.1).sum ≤ I.butterfly.1 :=
      p.longs_le
    -- Every long is used, since the spreads hold `2n` shorts and are balanced.
    have hlongs : (p.spreads.map fun s : Subtype F => s.1.1).sum = I.butterfly.1 := by
      refine Multiset.eq_of_le_of_card_le hlongs_le ?_
      rw [card_list_sum]
      have : (p.spreads.map fun s : Subtype F => card s.1.1) =
          p.spreads.map fun s : Subtype F => card s.1.2 :=
        List.map_congr_left fun s _ => hbal _ s.2
      rw [this, ← card_list_sum, hshorts]
      simp [butterfly, hI.1, hI.2.1, N3DM.n]
    -- So the moments add up to that of the position, which is zero, and each is zero.
    have hmom : (p.spreads.map fun s : Subtype F => moment s.1).sum = 0 := by
      have : (p.spreads.map fun s : Subtype F => moment s.1) =
          p.spreads.map fun s : Subtype F => s.1.1.sum - s.1.2.sum := rfl
      rw [this, list_sum_map_sub, ← sum_list_sum, ← sum_list_sum, hlongs, hshorts]
      have := moment_butterfly hI
      rw [moment] at this
      rw [this]
      have : (I.A.sum : ℤ) + I.B.sum + I.C.sum = I.n * I.bound := by exact_mod_cast hsum
      linarith
    have hm0 := list_eq_zero_of_nonpos p.spreads (fun s : Subtype F => moment s.1)
      (fun s hs => moment_nonpos _ (hbal _ s.2) (hnl s hs)) hmom
    have hall : ∀ s ∈ p.spreads, ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, I.Good τ) ∧
        s.1.1 = I.bflyLongs T ∧ s.1.2 = I.bflyShorts T := fun s hs =>
      bfly_three hI hn s.1 (hbal _ s.2) (hlegs _ s.2) (hm0 s hs)
        (p.longs_le' hs) (p.shorts_le hs)
    obtain ⟨T, hT, hL, hS⟩ :=
      exists_triples_of_forall (Subtype.val : Subtype F → Spread) I.Good _ _ p.spreads hall
    exact hasMatching_of_bfly hI T hT (hL ▸ hlongs_le) (hS ▸ hshorts)

end N3DM

end PairingHardness
