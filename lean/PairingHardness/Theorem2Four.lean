module

public import PairingHardness.Theorem2Three

/-!
# Theorem 2 with at most four legs: the condor instance

With `p = n + 1` and `q = n + 2` (docs/proofs.md, Theorem 2):

    long one call at  x_i = a_i                   for each i
    short one call at y_j = pM + B − b_j          for each j
    short n calls at  y*  = qM
    long one call at  z_k = (p + q)M + c_k        for each k

Any family of balanced call spreads of at most four legs, in which a spread requires
nothing exactly when its maximum loss is zero, and which contains every long condor with
equal wings. On the condor instance (after a check of the totals) a pairing with
requirement zero exists exactly when the source instance has a matching.
-/

@[expose] public section

namespace PairingHardness

open Multiset

namespace N3DM

variable (I : N3DM)

/-- `x = a`. -/
def cx (a : ℕ) : ℤ := a
/-- `y = pM + B − b`, with `p = n + 1`. -/
def cy (b : ℕ) : ℤ := (I.n + 1) * I.M + I.bound - b
/-- `y* = qM`, with `q = n + 2`. -/
def cstar : ℤ := (I.n + 2) * I.M
/-- `z = (p + q)M + c`. -/
def cz (c : ℕ) : ℤ := (2 * I.n + 3) * I.M + c

/-- The condor instance. -/
def condor : Spread :=
  (I.A.map cx + I.C.map I.cz, I.B.map I.cy + replicate I.n I.cstar)

/-- The long contracts of condors `x_i / y_j / y* / z_k`, one for each triple. -/
def condorLongs : Multiset (ℕ × ℕ × ℕ) →+ Multiset ℤ :=
  mapAddMonoidHom (fun τ => cx τ.1) + mapAddMonoidHom (fun τ => I.cz τ.2.2)

/-- The short contracts of the same condors. -/
def condorShorts : Multiset (ℕ × ℕ × ℕ) →+ Multiset ℤ :=
  mapAddMonoidHom (fun τ => I.cy τ.2.1) + mapAddMonoidHom (fun _ => I.cstar)

@[simp] lemma condorLongs_apply (T : Multiset (ℕ × ℕ × ℕ)) :
    I.condorLongs T = T.map (fun τ => cx τ.1) + T.map (fun τ => I.cz τ.2.2) := rfl

@[simp] lemma condorShorts_apply (T : Multiset (ℕ × ℕ × ℕ)) :
    I.condorShorts T = T.map (fun τ => I.cy τ.2.1) + T.map (fun _ => I.cstar) := rfl

lemma cx_injective : Function.Injective cx := fun a b h => by simp only [cx] at h; omega
lemma cy_injective : Function.Injective I.cy := fun a b h => by simp only [cy] at h; omega
lemma cz_injective : Function.Injective I.cz := fun a b h => by simp only [cz] at h; omega

/-- The reduction of Theorem 2 for `ℓ = 4`: the condor instance when the totals add up,
and one uncovered short call otherwise. -/
def reduce4 : Spread :=
  if I.A.sum + I.B.sum + I.C.sum = I.n * I.bound then I.condor else (0, {1})

variable {I}

/-- The four kinds of strike, in order: `x ≤ W < M`, then `y`, then `y*`, then `z`. -/
lemma condor_bounds (hI : I.Valid) :
    (∀ a ∈ I.A, 1 ≤ cx a ∧ cx a ≤ I.W) ∧
    (∀ b ∈ I.B, (I.n + 1) * I.M + 1 - I.W ≤ I.cy b ∧ I.cy b ≤ (I.n + 1) * I.M + I.W - 1) ∧
    (∀ c ∈ I.C, (2 * I.n + 3) * I.M + 1 ≤ I.cz c ∧ I.cz c ≤ (2 * I.n + 3) * I.M + I.W) := by
  refine ⟨fun a ha => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · have := hI.A_pos ha; have := I.A_le_W ha; simp only [cx]; omega
  · have := hI.B_pos hb; have := I.B_le_W hb; have := I.bound_le_W; have := hI.2.2.1
    simp only [cy]; omega
  · have := hI.C_pos hc; have := I.C_le_W hc; simp only [cz]; omega

lemma mem_condor_longs {k : ℤ} :
    k ∈ I.condor.1 ↔ (∃ a ∈ I.A, cx a = k) ∨ (∃ c ∈ I.C, I.cz c = k) := by
  simp [condor]

lemma mem_condor_shorts {k : ℤ} :
    k ∈ I.condor.2 ↔ (∃ b ∈ I.B, I.cy b = k) ∨ (1 ≤ I.n ∧ k = I.cstar) := by
  simp [condor, Multiset.mem_replicate, Nat.one_le_iff_ne_zero]

/-- **Size.** The condor instance has `4n` contracts, at positive strikes of at most
`(2n + 3)M + W`. -/
theorem condor_size (hI : I.Valid) :
    card I.condor.1 + card I.condor.2 = 4 * I.n ∧
    ∀ k ∈ strikes I.condor, 0 < k ∧ k ≤ (2 * I.n + 3) * I.M + I.W := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [condor, hI.1, hI.2.1, N3DM.n]; ring
  · have hn : 1 ≤ I.n := by
      rcases Multiset.mem_add.1 hk with hk | hk
      · rcases mem_condor_longs.1 hk with ⟨a, ha, -⟩ | ⟨c, hc, -⟩
        · exact one_le_n_of_mem ha
        · exact (hI.2.1 ▸ Multiset.card_pos_iff_exists_mem.2 ⟨c, hc⟩ : 0 < I.n)
      · rcases mem_condor_shorts.1 hk with ⟨b, hb, -⟩ | ⟨h, -⟩
        · exact (hI.1 ▸ Multiset.card_pos_iff_exists_mem.2 ⟨b, hb⟩ : 0 < I.n)
        · exact h
    have h6 := six_W_le_M hn
    have hW := hI.one_le_W
    have hn' : (1 : ℤ) ≤ I.n := by exact_mod_cast hn
    have hM0 : (0 : ℤ) ≤ I.M := by omega
    have e1 : (I.M : ℤ) ≤ I.n * I.M := by nlinarith
    obtain ⟨bA, bB, bC⟩ := condor_bounds hI
    rcases Multiset.mem_add.1 hk with hk | hk
    · rcases mem_condor_longs.1 hk with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
      · have := bA a ha; constructor <;> nlinarith
      · have := bC c hc; constructor <;> nlinarith
    · rcases mem_condor_shorts.1 hk with ⟨b, hb, rfl⟩ | ⟨-, rfl⟩
      · have := bB b hb; constructor <;> nlinarith
      · simp only [cstar]; constructor <;> nlinarith

/-- A long condor with equal wings has no loss. -/
lemma condor_noLoss {k₁ k₂ k₃ k₄ : ℤ} (h12 : k₁ < k₂) (h23 : k₂ < k₃)
    (h : k₂ - k₁ = k₄ - k₃) : NoLoss (Named.longCondor k₁ k₂ k₃ k₄).shape := by
  simp [NoLoss, Named.shape, strikes, payoff, callValue]
  omega

/-- A condor `x_i / y_j / y* / z_k` from a good triple is in order with equal wings. -/
lemma good_condor_valid (hI : I.Valid) {τ : ℕ × ℕ × ℕ} (h : I.Good τ) :
    cx τ.1 < I.cy τ.2.1 ∧ I.cy τ.2.1 < I.cstar ∧ I.cstar < I.cz τ.2.2 ∧
      I.cy τ.2.1 - cx τ.1 = I.cz τ.2.2 - I.cstar := by
  obtain ⟨ha, hb, hc, hs⟩ := h
  have hn := one_le_n_of_mem ha
  have h6 := six_W_le_M hn
  obtain ⟨bA, bB, bC⟩ := condor_bounds hI
  have := bA _ ha; have := bB _ hb; have := bC _ hc
  have hn' : (1 : ℤ) ≤ I.n := by exact_mod_cast hn
  have hW := hI.one_le_W
  refine ⟨by nlinarith, by simp only [cstar]; nlinarith, by simp only [cstar]; nlinarith, ?_⟩
  simp only [cx, cy, cz, cstar]
  have : (τ.1 : ℤ) + τ.2.1 + τ.2.2 = I.bound := by exact_mod_cast hs
  linarith

lemma good_condor_shape (τ : ℕ × ℕ × ℕ) :
    (Named.longCondor (cx τ.1) (I.cy τ.2.1) I.cstar (I.cz τ.2.2)).shape =
      (I.condorLongs {τ}, I.condorShorts {τ}) := by
  simp [Named.shape]

/-- **Decoding.** Condors from good triples that cover every short of the condor
instance, using longs it holds, come from a matching. -/
theorem hasMatching_of_condor (hI : I.Valid) (T : Multiset (ℕ × ℕ × ℕ))
    (hT : ∀ τ ∈ T, I.Good τ) (hL : I.condorLongs T ≤ I.condor.1)
    (hS : I.condorShorts T = I.condor.2) : I.HasMatching := by
  by_cases hn0 : I.n = 0
  · exact hI.hasMatching_of_n_eq_zero hn0
  have hn : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn0
  obtain ⟨bA, -, bC⟩ := condor_bounds hI
  have h6 := six_W_le_M hn
  have hW := hI.one_le_W
  have hn' : (1 : ℤ) ≤ I.n := by exact_mod_cast hn
  have hcardT : card T = I.n := by
    have := congrArg card hS
    simp [condor, hI.1] at this
    omega
  have hLeq : I.condorLongs T = I.condor.1 := by
    refine Multiset.eq_of_le_of_card_le hL ?_
    simp [condor, hI.2.1, hcardT, N3DM.n]
  have hAC := decode_add cx_injective I.cz_injective I.M
    (A := T.map (·.1)) (C := T.map (·.2.2)) (A' := I.A) (C' := I.C)
    (by
      intro a ha
      have ha : a ∈ I.A := by
        rcases Multiset.mem_add.1 ha with ha | ha
        · obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 ha; exact (hT τ hτ).1
        · exact ha
      have := bA a ha; omega)
    (by
      intro c hc
      have hc : c ∈ I.C := by
        rcases Multiset.mem_add.1 hc with hc | hc
        · obtain ⟨τ, hτ, rfl⟩ := Multiset.mem_map.1 hc; exact (hT τ hτ).2.2.1
        · exact hc
      have := bC c hc; nlinarith)
    (by rw [Multiset.map_map, Multiset.map_map]; exact hLeq)
  have hB : T.map (·.2.1) = I.B := by
    refine Multiset.map_injective I.cy_injective ?_
    rw [Multiset.map_map]
    simp only [condorShorts_apply, condor, Multiset.map_const', hcardT] at hS
    exact add_right_cancel hS
  exact hasMatching_of_good T hT hAC.1 hB hAC.2

/-- The arithmetic of the four-leg step. With `p = n + 1`, `q = n + 2` and `M = 6nW`, a
spread holding `α` contracts at `x` strikes, `β` at `z`, `γ` at `y` and `γ*` at `y*`, with
those strikes' bounds and moment zero, has `γ = γ* = α = β`. -/
lemma condor_counts {n M W α β γ γs sx sz sy : ℤ} (hn : 1 ≤ n) (hW : 1 ≤ W)
    (hM : M = 6 * n * W) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ) (hγs0 : 0 ≤ γs)
    (hαn : α ≤ n) (hβn : β ≤ n) (hγn : γ ≤ n) (hcard : α + β = γ + γs)
    (sx1 : α * 1 ≤ sx) (sx2 : sx ≤ α * W)
    (sz1 : β * ((2 * n + 3) * M + 1) ≤ sz) (sz2 : sz ≤ β * ((2 * n + 3) * M + W))
    (sy1 : γ * ((n + 1) * M + 1 - W) ≤ sy) (sy2 : sy ≤ γ * ((n + 1) * M + W - 1))
    (hsum : sx + sz - sy - γs * ((n + 2) * M) = 0) : γ = β ∧ γs = β ∧ α = β := by
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hMW : 3 * n * W < M := by rw [hM]; nlinarith
  -- The coefficient of `M` in the moment is zero, since what is left is below `M` in size.
  have hcoef : (2 * n + 3) * β - (n + 1) * γ - (n + 2) * γs = 0 := by
    set c := (2 * n + 3) * β - (n + 1) * γ - (n + 2) * γs with hc
    rcases lt_trichotomy c 0 with h | h | h
    · exfalso
      have e1 : M * 1 ≤ M * (-c) := mul_le_mul_of_nonneg_left (by omega) hM0
      have e2 : W * α ≤ W * n := mul_le_mul_of_nonneg_left hαn (by omega)
      have e3 : W * β ≤ W * n := mul_le_mul_of_nonneg_left hβn (by omega)
      have e4 : (W - 1) * γ ≤ (W - 1) * n := mul_le_mul_of_nonneg_left hγn (by omega)
      nlinarith
    · exact h
    · exfalso
      have e1 : M * 1 ≤ M * c := mul_le_mul_of_nonneg_left (by omega) hM0
      have e4 : (W - 1) * γ ≤ (W - 1) * n := mul_le_mul_of_nonneg_left hγn (by omega)
      nlinarith
  -- `p(β − γ) = q(γ* − β)` with `p`, `q` coprime and `|β − γ| ≤ n < q`, so `β = γ`.
  have hγβ : γ = β := by
    set k := (β - γ) - (γs - β) with hk
    have hd : β - γ = (n + 2) * k := by rw [hk]; linarith
    rcases lt_trichotomy k 0 with h | h | h
    · exfalso
      have : (n + 2) * k ≤ (n + 2) * (-1) := mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
    · rw [h, mul_zero] at hd; linarith
    · exfalso
      have : (n + 2) * 1 ≤ (n + 2) * k := mul_le_mul_of_nonneg_left (by omega) (by omega)
      linarith
  have hγsβ : γs = β := by
    rw [hγβ] at hcoef
    have : (n + 2) * (β - γs) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  exact ⟨hγβ, hγsβ, by linarith⟩

/-- The per-spread step of the proof. A balanced spread of at most four legs with moment
zero, taken from the condor instance, is some number of copies of the condor of one good
triple. -/
lemma condor_four (hI : I.Valid) (hn : 1 ≤ I.n) (t : Spread) (hb : Balanced t)
    (hlegs : legs t ≤ 4) (hm : moment t = 0) (hL : t.1 ≤ I.condor.1)
    (hS : t.2 ≤ I.condor.2) :
    ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, I.Good τ) ∧ t.1 = I.condorLongs T ∧
      t.2 = I.condorShorts T := by
  have h6 := six_W_le_M hn
  have hW := hI.one_le_W
  have hMe : (I.M : ℤ) = 6 * I.n * I.W := M_eq
  have hn' : (1 : ℤ) ≤ I.n := by exact_mod_cast hn
  have hW' : (1 : ℤ) ≤ I.W := by exact_mod_cast hW
  have hM0 : (0 : ℤ) ≤ I.M := by omega
  have hnM : (I.M : ℤ) ≤ I.n * I.M := by nlinarith
  have o1 : (I.W : ℤ) < (I.n + 1) * I.M + 1 - I.W := by linarith
  have o2 : (I.n + 1) * (I.M : ℤ) + I.W - 1 < (I.n + 2) * I.M := by linarith
  have o3 : (I.n + 2) * (I.M : ℤ) < (2 * I.n + 3) * I.M + 1 := by nlinarith
  obtain ⟨bA, bB, bC⟩ := condor_bounds hI
  by_cases h0 : t.2 = 0
  · refine ⟨0, by simp, ?_, by simp [h0]⟩
    have : card t.1 = 0 := by rw [hb, h0]; rfl
    simpa using this
  set Lx := t.1.filter (· < (I.M : ℤ)) with hLx
  set Lz := t.1.filter (fun k => ¬ k < (I.M : ℤ)) with hLz
  set Sy := t.2.filter (· ≠ I.cstar) with hSy
  set Ss := t.2.filter (fun k => ¬ k ≠ I.cstar) with hSs
  have hsplitL : Lx + Lz = t.1 := Multiset.filter_add_not _ _
  have hsplitS : Sy + Ss = t.2 := Multiset.filter_add_not _ _
  have memL : ∀ k ∈ t.1, k ∈ I.condor.1 := fun k hk => Multiset.mem_of_le hL hk
  have memS : ∀ k ∈ t.2, k ∈ I.condor.2 := fun k hk => Multiset.mem_of_le hS hk
  have hx : ∀ k ∈ Lx, ∃ a ∈ I.A, cx a = k ∧ 1 ≤ k ∧ k ≤ I.W := by
    intro k hk
    rw [hLx, Multiset.mem_filter] at hk
    rcases mem_condor_longs.1 (memL k hk.1) with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
    · exact ⟨a, ha, rfl, bA a ha⟩
    · have := bC c hc; exfalso; nlinarith [hk.2]
  have hz : ∀ k ∈ Lz, ∃ c ∈ I.C, I.cz c = k ∧ (2 * I.n + 3) * I.M + 1 ≤ k ∧
      k ≤ (2 * I.n + 3) * I.M + I.W := by
    intro k hk
    rw [hLz, Multiset.mem_filter] at hk
    rcases mem_condor_longs.1 (memL k hk.1) with ⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩
    · have := bA a ha; exfalso; exact hk.2 (by omega)
    · exact ⟨c, hc, rfl, bC c hc⟩
  have hy : ∀ k ∈ Sy, ∃ b ∈ I.B, I.cy b = k ∧ (I.n + 1) * I.M + 1 - I.W ≤ k ∧
      k ≤ (I.n + 1) * I.M + I.W - 1 := by
    intro k hk
    rw [hSy, Multiset.mem_filter] at hk
    rcases mem_condor_shorts.1 (memS k hk.1) with ⟨b, hb, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨b, hb, rfl, bB b hb⟩
    · exact absurd rfl hk.2
  have hs : ∀ k ∈ Ss, k = I.cstar := by
    intro k hk
    rw [hSs, Multiset.mem_filter] at hk
    exact not_not.1 hk.2
  -- Counts: each kind of strike holds at most `n` contracts of the position.
  have cLz : card Lz ≤ I.n := by
    have : Lz ≤ I.condor.1.filter (fun k => ¬ k < (I.M : ℤ)) := Multiset.filter_le_filter _ hL
    have h2 : I.condor.1.filter (fun k => ¬ k < (I.M : ℤ)) = I.C.map I.cz := by
      rw [condor, Multiset.filter_add, Multiset.filter_eq_nil.2, Multiset.filter_eq_self.2,
        zero_add]
      · intro k hk
        obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hk
        have := bC c hc; nlinarith
      · intro k hk
        obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hk
        have := bA a ha; omega
    have := Multiset.card_le_card this
    rw [h2, Multiset.card_map, hI.2.1] at this
    exact this
  have cLx : card Lx ≤ I.n := by
    have : Lx ≤ I.condor.1.filter (· < (I.M : ℤ)) := Multiset.filter_le_filter _ hL
    have h2 : I.condor.1.filter (· < (I.M : ℤ)) = I.A.map cx := by
      rw [condor, Multiset.filter_add, Multiset.filter_eq_self.2, Multiset.filter_eq_nil.2,
        add_zero]
      · intro k hk
        obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hk
        have := bC c hc; nlinarith
      · intro k hk
        obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hk
        have := bA a ha; omega
    have := Multiset.card_le_card this
    rw [h2, Multiset.card_map] at this
    exact this
  have cSy : card Sy ≤ I.n := by
    have : Sy ≤ I.condor.2.filter (· ≠ I.cstar) := Multiset.filter_le_filter _ hS
    have h2 : I.condor.2.filter (· ≠ I.cstar) = I.B.map I.cy := by
      rw [condor, Multiset.filter_add, Multiset.filter_eq_self.2, Multiset.filter_eq_nil.2,
        add_zero]
      · intro k hk
        rw [Multiset.eq_of_mem_replicate hk]
        simp
      · intro k hk
        obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hk
        have := bB b hb
        simp only [cstar]
        nlinarith
    have := Multiset.card_le_card this
    rw [h2, Multiset.card_map, hI.1] at this
    exact this
  have cSs : card Ss ≤ I.n := by
    have : Ss ≤ I.condor.2.filter (fun k => ¬ k ≠ I.cstar) := Multiset.filter_le_filter _ hS
    have := Multiset.card_le_card this
    have h3 := Multiset.card_le_card (Multiset.filter_le_filter (fun k => ¬ k ≠ I.cstar)
      (le_of_eq (show I.condor.2 = I.B.map I.cy + replicate I.n I.cstar from rfl)))
    rw [Multiset.filter_add] at h3
    have h4 : (I.B.map I.cy).filter (fun k => ¬ k ≠ I.cstar) = 0 := by
      refine Multiset.filter_eq_nil.2 fun k hk => ?_
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hk
      have := bB b hb
      simp only [cstar, ne_eq, not_not]
      nlinarith
    rw [h4, zero_add] at h3
    have h5 := Multiset.card_le_card
      (Multiset.filter_le (fun k => ¬ k ≠ I.cstar) (replicate I.n I.cstar))
    rw [Multiset.card_replicate] at h5
    omega
  -- Sums.
  have sx1 : (card Lx : ℤ) * 1 ≤ Lx.sum := by
    rw [← nsmul_eq_mul]
    exact Multiset.card_nsmul_le_sum fun k hk => by obtain ⟨_, _, _, h, _⟩ := hx k hk; exact h
  have sx2 : Lx.sum ≤ (card Lx : ℤ) * I.W := by
    rw [← nsmul_eq_mul]
    exact Multiset.sum_le_card_nsmul _ _ fun k hk => by obtain ⟨_, _, _, _, h⟩ := hx k hk; exact h
  have sz1 : (card Lz : ℤ) * ((2 * I.n + 3) * I.M + 1) ≤ Lz.sum := by
    rw [← nsmul_eq_mul]
    exact Multiset.card_nsmul_le_sum fun k hk => by obtain ⟨_, _, _, h, _⟩ := hz k hk; exact h
  have sz2 : Lz.sum ≤ (card Lz : ℤ) * ((2 * I.n + 3) * I.M + I.W) := by
    rw [← nsmul_eq_mul]
    exact Multiset.sum_le_card_nsmul _ _ fun k hk => by obtain ⟨_, _, _, _, h⟩ := hz k hk; exact h
  have sy1 : (card Sy : ℤ) * ((I.n + 1) * I.M + 1 - I.W) ≤ Sy.sum := by
    rw [← nsmul_eq_mul]
    exact Multiset.card_nsmul_le_sum fun k hk => by obtain ⟨_, _, _, h, _⟩ := hy k hk; exact h
  have sy2 : Sy.sum ≤ (card Sy : ℤ) * ((I.n + 1) * I.M + I.W - 1) := by
    rw [← nsmul_eq_mul]
    exact Multiset.sum_le_card_nsmul _ _ fun k hk => by obtain ⟨_, _, _, _, h⟩ := hy k hk; exact h
  have eSs : Ss = replicate (card Ss) I.cstar := Multiset.eq_replicate.2 ⟨rfl, hs⟩
  have ss : Ss.sum = (card Ss : ℤ) * ((I.n + 2) * I.M) := by
    conv_lhs => rw [eSs]
    rw [Multiset.sum_replicate, nsmul_eq_mul, cstar]
  have hcard : (card Lx : ℤ) + card Lz = card Sy + card Ss := by
    have h1 := congrArg card hsplitL
    have h2 := congrArg card hsplitS
    rw [Multiset.card_add] at h1 h2
    have := hb
    unfold Balanced at this
    omega
  have hsum : Lx.sum + Lz.sum - Sy.sum - Ss.sum = 0 := by
    have := hm
    rw [moment, ← hsplitL, ← hsplitS, Multiset.sum_add, Multiset.sum_add] at this
    linarith
  -- The moment fixes the counts: `γ = γ* = β`.
  have hαn : (card Lx : ℤ) ≤ I.n := by exact_mod_cast cLx
  have hβn : (card Lz : ℤ) ≤ I.n := by exact_mod_cast cLz
  have hγn : (card Sy : ℤ) ≤ I.n := by exact_mod_cast cSy
  rw [ss] at hsum
  obtain ⟨hγβ, hγsβ, hαβ⟩ := condor_counts hn' hW' hMe (by positivity) (by positivity)
    (by positivity) (by positivity) hαn hβn hγn hcard sx1 sx2 sz1 sz2 sy1 sy2 hsum
  have hβ1 : 1 ≤ (card Lz : ℤ) := by
    have h1 := Multiset.card_pos.2 h0
    have h2 := congrArg card hsplitS
    rw [Multiset.card_add] at h2
    omega
  -- Each kind of strike holds one strike only: else five legs.
  obtain ⟨p₀, hp₀⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < card Lx by omega)
  obtain ⟨q₀, hq₀⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < card Lz by omega)
  obtain ⟨r₀, hr₀⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < card Sy by omega)
  obtain ⟨s₀, hs₀⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < card Ss by omega)
  have sLx : ∀ k ∈ Lx, k ∈ strikes t := fun k hk =>
    mem_strikes_of_long (Multiset.mem_of_mem_filter hk)
  have sLz : ∀ k ∈ Lz, k ∈ strikes t := fun k hk =>
    mem_strikes_of_long (Multiset.mem_of_mem_filter hk)
  have sSy : ∀ k ∈ Sy, k ∈ strikes t := fun k hk =>
    mem_strikes_of_short (Multiset.mem_of_mem_filter hk)
  have sSs : ∀ k ∈ Ss, k ∈ strikes t := fun k hk =>
    mem_strikes_of_short (Multiset.mem_of_mem_filter hk)
  obtain ⟨-, -, -, p1, p2⟩ := hx p₀ hp₀
  obtain ⟨-, -, -, q1, q2⟩ := hz q₀ hq₀
  obtain ⟨-, -, -, r1, r2⟩ := hy r₀ hr₀
  have hs₀' := hs s₀ hs₀
  have hstar : I.cstar = (I.n + 2) * I.M := rfl
  have eLx : Lx = replicate (card Lx) p₀ := by
    refine Multiset.eq_replicate.2 ⟨rfl, fun k hk => ?_⟩
    by_contra hne
    obtain ⟨-, -, -, k1, k2⟩ := hx k hk
    have := five_le_legs t (sLx k hk) (sLx p₀ hp₀) (sSy r₀ hr₀) (sSs s₀ hs₀) (sLz q₀ hq₀)
      hne (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    omega
  have eLz : Lz = replicate (card Lz) q₀ := by
    refine Multiset.eq_replicate.2 ⟨rfl, fun k hk => ?_⟩
    by_contra hne
    obtain ⟨-, -, -, k1, k2⟩ := hz k hk
    have := five_le_legs t (sLx p₀ hp₀) (sSy r₀ hr₀) (sSs s₀ hs₀) (sLz k hk) (sLz q₀ hq₀)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hne
    omega
  have eSy : Sy = replicate (card Sy) r₀ := by
    refine Multiset.eq_replicate.2 ⟨rfl, fun k hk => ?_⟩
    by_contra hne
    obtain ⟨-, -, -, k1, k2⟩ := hy k hk
    have := five_le_legs t (sLx p₀ hp₀) (sSy k hk) (sSy r₀ hr₀) (sSs s₀ hs₀) (sLz q₀ hq₀)
      (by omega) (by omega) (by omega) (by omega) hne (by omega) (by omega) (by omega)
      (by omega) (by omega)
    omega
  -- The one triple has sum `B`.
  obtain ⟨a, ha, rfl, -⟩ := hx p₀ hp₀
  obtain ⟨c, hc, rfl, -⟩ := hz _ hq₀
  obtain ⟨b, hb', rfl, -⟩ := hy _ hr₀
  have hsum' : (card Lz : ℤ) * (cx a + I.cz c - I.cy b - I.cstar) = 0 := by
    have e1 : Lx.sum = (card Lx : ℤ) * cx a := by
      conv_lhs => rw [eLx]
      rw [Multiset.sum_replicate, nsmul_eq_mul]
    have e2 : Lz.sum = (card Lz : ℤ) * I.cz c := by
      conv_lhs => rw [eLz]
      rw [Multiset.sum_replicate, nsmul_eq_mul]
    have e3 : Sy.sum = (card Sy : ℤ) * I.cy b := by
      conv_lhs => rw [eSy]
      rw [Multiset.sum_replicate, nsmul_eq_mul]
    rw [e1, e2, e3, hαβ, hγβ, hγsβ] at hsum
    rw [hstar]
    linear_combination hsum
  have hgood : I.Good (a, b, c) := by
    refine ⟨ha, hb', hc, ?_⟩
    have h' : cx a + I.cz c - I.cy b - I.cstar = 0 := by
      rcases mul_eq_zero.1 hsum' with h | h
      · omega
      · exact h
    simp only [cx, cz, cy, cstar] at h'
    show a + b + c = I.bound
    have : (a : ℤ) + b + c = I.bound := by linarith
    exact_mod_cast this
  have nLx : card Lx = card Lz := by omega
  have nSy : card Sy = card Lz := by omega
  have nSs : card Ss = card Lz := by omega
  refine ⟨replicate (card Lz) (a, b, c), fun τ hτ => ?_, ?_, ?_⟩
  · rw [Multiset.eq_of_mem_replicate hτ]; exact hgood
  · rw [← hsplitL, eLx, eLz, nLx]; simp [Multiset.map_replicate]
  · rw [← hsplitS, eSy, eSs, nSy, nSs]; simp [Multiset.map_replicate]

/-- **Theorem 2, `ℓ = 4`.** As `theorem2_three`, for a family of at most four legs that
contains every long condor with equal wings, on `reduce4 I`. -/
theorem theorem2_four (hI : I.Valid) (F : Spread → Prop) (hbal : ∀ t, F t → Balanced t)
    (hlegs : ∀ t, F t → legs t ≤ 4)
    (hcondor : ∀ k₁ k₂ k₃ k₄ : ℤ, k₁ < k₂ → k₂ < k₃ → k₃ < k₄ → k₂ - k₁ = k₄ - k₃ →
      F (Named.longCondor k₁ k₂ k₃ k₄).shape)
    (req : Subtype F → ℚ) (hreq0 : ∀ t, 0 ≤ req t) (hreq : ∀ t, req t = 0 ↔ maxLoss t.1 = 0)
    (U : ℤ → ℚ) (hU : ∀ K, 0 < U K) :
    I.HasMatching ↔
      ∃ p : Pairing (Subtype.val : Subtype F → Spread) I.reduce4, p.requirement req U = 0 := by
  constructor
  · intro h
    have hr : I.reduce4 = I.condor := ite_eq_left_of_eq_true _ _ (eq_true h.sum_eq)
    rw [hr]
    obtain ⟨T, hT, hA, hB, hC⟩ := h.exists_good
    obtain ⟨p, hu, hs⟩ := exists_pairing_of_triples (Subtype.val : Subtype F → Spread)
      I.condor I.condorLongs I.condorShorts I.Good T hT
      (fun τ hτ => ⟨_, (good_condor_shape τ) ▸
        hcondor _ _ _ _ (good_condor_valid hI hτ).1 (good_condor_valid hI hτ).2.1
          (good_condor_valid hI hτ).2.2.1 (good_condor_valid hI hτ).2.2.2⟩)
      (fun τ _ => rfl)
      (le_of_eq (by simp only [condorLongs_apply, condor, ← hA, ← hC, Multiset.map_map,
        Function.comp_def]))
      (by
        have hcard : card T = I.n := by rw [N3DM.n, ← hA, Multiset.card_map]
        simp only [condorShorts_apply, condor, ← hB, Multiset.map_map, Function.comp_def,
          Multiset.map_const', hcard])
    refine ⟨p, (p.requirement_eq_zero_iff req U hreq0 hU).2 ⟨hu, fun s hs' => ?_⟩⟩
    obtain ⟨τ, hτ, rfl⟩ := hs s hs'
    rw [hreq, maxLoss_eq_zero_iff]
    show NoLoss (I.condorLongs {τ}, I.condorShorts {τ})
    rw [← good_condor_shape]
    obtain ⟨v1, v2, -, v4⟩ := good_condor_valid hI hτ
    exact condor_noLoss v1 v2 v4
  · intro hex
    by_cases hsum : I.A.sum + I.B.sum + I.C.sum = I.n * I.bound
    swap
    · obtain ⟨p, hp⟩ := hex
      have hu := ((p.requirement_eq_zero_iff req U hreq0 hU).1 hp).1
      exact (no_cover_lone_short (fun s => hbal _ s.2) p
        (ite_eq_right_of_eq_false _ _ (eq_false hsum)) hu).elim
    have hr : I.reduce4 = I.condor := ite_eq_left_of_eq_true _ _ (eq_true hsum)
    rw [hr] at hex
    obtain ⟨p, hp⟩ := hex
    obtain ⟨hu, hz⟩ := (p.requirement_eq_zero_iff req U hreq0 hU).1 hp
    have hnl : ∀ s ∈ p.spreads, NoLoss s.1 := fun s hs =>
      (maxLoss_eq_zero_iff _).1 ((hreq s).1 (hz s hs))
    by_cases hn0 : I.n = 0
    · exact hI.hasMatching_of_n_eq_zero hn0
    have hn : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn0
    have hshorts : (p.spreads.map fun s : Subtype F => s.1.2).sum = I.condor.2 := by
      have := p.shorts_eq; rw [hu, add_zero] at this; exact this
    have hlongs : (p.spreads.map fun s : Subtype F => s.1.1).sum = I.condor.1 := by
      refine Multiset.eq_of_le_of_card_le p.longs_le ?_
      rw [card_list_sum]
      have : (p.spreads.map fun s : Subtype F => card s.1.1) =
          p.spreads.map fun s : Subtype F => card s.1.2 :=
        List.map_congr_left fun s _ => hbal _ s.2
      rw [this, ← card_list_sum, hshorts]
      simp [condor, hI.1, hI.2.1, N3DM.n]
    have hmom : (p.spreads.map fun s : Subtype F => moment s.1).sum = 0 := by
      have : (p.spreads.map fun s : Subtype F => moment s.1) =
          p.spreads.map fun s : Subtype F => s.1.1.sum - s.1.2.sum := rfl
      rw [this, list_sum_map_sub, ← sum_list_sum, ← sum_list_sum, hlongs, hshorts]
      have hB : (card I.B : ℤ) = I.n := by exact_mod_cast hI.1
      have hC : (card I.C : ℤ) = I.n := by exact_mod_cast hI.2.1
      have eA : (I.A.map cx).sum = (I.A.sum : ℤ) := by
        show (I.A.map fun a : ℕ => (a : ℤ)).sum = _
        rw [Nat.cast_multiset_sum]
      have eC : (I.C.map I.cz).sum = I.n * ((2 * I.n + 3) * I.M) + (I.C.sum : ℤ) := by
        show (I.C.map fun c : ℕ => (2 * (I.n : ℤ) + 3) * I.M + c).sum = _
        rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hC,
          Nat.cast_multiset_sum]
      have eB : (I.B.map I.cy).sum = I.n * ((I.n + 1) * I.M + I.bound) - (I.B.sum : ℤ) := by
        show (I.B.map fun b : ℕ => ((I.n : ℤ) + 1) * I.M + I.bound - b).sum = _
        rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hB,
          Nat.cast_multiset_sum]
      have : (I.A.sum : ℤ) + I.B.sum + I.C.sum = I.n * I.bound := by exact_mod_cast hsum
      simp only [condor, Multiset.sum_add, eA, eB, eC, Multiset.sum_replicate, nsmul_eq_mul,
        cstar]
      linear_combination this
    have hm0 := list_eq_zero_of_nonpos p.spreads (fun s : Subtype F => moment s.1)
      (fun s hs => moment_nonpos _ (hbal _ s.2) (hnl s hs)) hmom
    have hall : ∀ s ∈ p.spreads, ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, I.Good τ) ∧
        s.1.1 = I.condorLongs T ∧ s.1.2 = I.condorShorts T := fun s hs =>
      condor_four hI hn s.1 (hbal _ s.2) (hlegs _ s.2) (hm0 s hs)
        (p.longs_le' hs) (p.shorts_le hs)
    obtain ⟨T, hT, hL, hS⟩ :=
      exists_triples_of_forall (Subtype.val : Subtype F → Spread) I.Good _ _ p.spreads hall
    exact hasMatching_of_condor hI T hT (hL ▸ p.longs_le) (hS ▸ hshorts)

end N3DM

end PairingHardness
