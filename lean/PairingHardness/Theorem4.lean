module

public import PairingHardness.Theorem3

/-!
# Theorem 4: the one-group problem with every short priced by R3

docs/proofs.md, Theorem 4. The uncovered requirements are no longer free inputs: each is
R3's, at stock rates, from call prices within the no-arbitrage bounds. The source problem is
`k`-subset sum, which subset sum reduces to (`subsetSum_iff_kSubsetSum`).

The paper's construction has fractional strikes and prices; multiplying every amount by
`2k`, as it says, makes the strikes whole. In those units, with `Σ = Σa`, `shift = 8Σ`:

* the depth of the number `x` is `w x = 2k(x + shift)`, and `V = 2k(T + k·shift)`;
* the underlying is at `S = 2(2k + T + k·shift)`, and `K_low = 2S`, `K_top = K_low + V`;
* the call at `K` is priced `C(K) = 2k + (K_top − K)/(2k)`, which is `π + β(K_top − K)` with
  `π = 1` and `β = 1/(2k)` before scaling;
* the position is long one call at `K_low`, `n` at `K_top`, and short one at `K_top − w x`
  for each number `x`: `Ladder.pos`.

`K_low = 2S` is one admissible choice of the paper's `K_low ≥ 1.1 S`.
-/

@[expose] public section

namespace PairingHardness

open Multiset

/-- `k`-subset sum: exactly `k` of the numbers `a` sum to `T`. -/
def KSubsetSum (a : Multiset ℕ) (k T : ℕ) : Prop := ∃ S ≤ a, card S = k ∧ S.sum = T

/-- A sub-multiset of the image of an injective map is the image of a sub-multiset. -/
lemma exists_le_of_le_map {f : ℕ → ℕ} (hf : Function.Injective f) {a B : Multiset ℕ}
    (h : B ≤ a.map f) : ∃ S ≤ a, B = S.map f := by
  refine ⟨B.map (Function.invFun f), ?_, ?_⟩
  · have := Multiset.map_le_map (f := Function.invFun f) h
    rwa [Multiset.map_map, Function.invFun_comp hf, Multiset.map_id] at this
  · rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id B]
    refine Multiset.map_congr rfl fun b hb => ?_
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_of_le h hb)
    simp [Function.leftInverse_invFun hf x]

/-- **Subset sum reduces to `k`-subset sum** (docs/proofs.md, Theorem 4): replace each `a_i`
by `(n + 1)a_i + 1`, add `n` numbers equal to 1, and ask for `n` numbers that sum to
`(n + 1)T + n`. -/
theorem subsetSum_iff_kSubsetSum (a : Multiset ℕ) (T : ℕ) (ha : ∀ x ∈ a, 0 < x) :
    SubsetSum a T ↔
      KSubsetSum (a.map (fun x => (card a + 1) * x + 1) + replicate (card a) 1) (card a)
        ((card a + 1) * T + card a) := by
  set n := card a
  set φ : ℕ → ℕ := fun x => (n + 1) * x + 1 with hφ
  have hφi : Function.Injective φ := fun x y h => by
    simp only [hφ] at h
    have : (n + 1) * x = (n + 1) * y := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hsumφ : ∀ S : Multiset ℕ, (S.map φ).sum = (n + 1) * S.sum + card S := by
    intro S
    induction S using Multiset.induction_on with
    | empty => simp
    | cons x S ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons, Multiset.sum_cons]
      simp only [hφ]
      ring
  constructor
  · rintro ⟨S, hS, hsum⟩
    have hc := Multiset.card_le_card hS
    refine ⟨S.map φ + replicate (n - card S) 1, ?_, ?_, ?_⟩
    · exact add_le_add (Multiset.map_le_map hS)
        ((Multiset.replicate_le_replicate _).2 (Nat.sub_le _ _))
    · simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate]; omega
    · rw [Multiset.sum_add, hsumφ, Multiset.sum_replicate, smul_eq_mul, mul_one, hsum]; omega
  · rintro ⟨S', hS', hcard, hsum⟩
    have hbig : ∀ y ∈ a.map φ, y ≠ 1 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hy
      have := ha x hx
      simp only [hφ]; nlinarith
    have h1 : S'.filter (· ≠ 1) ≤ a.map φ := by
      have := Multiset.filter_le_filter (· ≠ 1) hS'
      have hr : (replicate n 1).filter (· ≠ 1) = 0 :=
        Multiset.filter_eq_nil.2 fun y hy => by rw [Multiset.eq_of_mem_replicate hy]; simp
      rwa [Multiset.filter_add, Multiset.filter_eq_self.2 hbig, hr, add_zero] at this
    obtain ⟨S, hS, hSeq⟩ := exists_le_of_le_map hφi h1
    have hones : S'.filter (fun y => ¬ y ≠ 1) = replicate (card (S'.filter fun y => ¬ y ≠ 1)) 1 :=
      Multiset.eq_replicate.2 ⟨rfl, fun y hy => by simpa using (Multiset.mem_filter.1 hy).2⟩
    have e := Multiset.filter_add_not (· ≠ 1) S'
    have hc := congrArg card e
    have hs := congrArg Multiset.sum e
    rw [hones, hSeq, Multiset.sum_add, hsumφ, Multiset.sum_replicate, smul_eq_mul, mul_one]
      at hs
    rw [hones, hSeq, Multiset.card_add, Multiset.card_map, Multiset.card_replicate] at hc
    refine ⟨S, hS, ?_⟩
    have : (n + 1) * S.sum = (n + 1) * T := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) this

/-- The uncovered requirement of a short call at stock rates (rules.md R3): the premium plus
the greater of 20% of the underlying less the out-of-the-money amount, and 10% of it. -/
def r3Call (premium : ℚ) (S K : ℤ) : ℚ :=
  premium + max ((S : ℚ) / 5 - max ((K : ℚ) - S) 0) ((S : ℚ) / 10)

namespace KSubsetSumInstance

variable (a : Multiset ℕ) (k T : ℕ)

/-- `shift = 8Σa`. -/
def shift : ℕ := 8 * a.sum
/-- The depth `w x = 2k(x + shift)` of the short of `x`. -/
def w (x : ℕ) : ℕ := 2 * k * (x + shift a)
/-- `V = 2k(T + k·shift)`. -/
def V : ℕ := 2 * k * (T + k * shift a)
/-- The underlying price `S = 2(2k + T + k·shift)`. -/
def und : ℤ := 2 * (2 * k + T + k * shift a)
/-- `K_top = 2S + V`. -/
def top : ℤ := 2 * und a k T + V a k T
/-- The call price `C(K) = 2k + (K_top − K)/(2k)`. -/
def price (K : ℤ) : ℚ := 2 * k + ((top a k T - K : ℤ) : ℚ) / (2 * k)
/-- The position. -/
def pos : Spread := Ladder.pos a (w a k) (V a k T) (top a k T)
/-- Every uncovered requirement is R3's. -/
def U (K : ℤ) : ℚ := r3Call (price a k T K) (und a k T) K
/-- `c = π + S/10`, scaled. -/
def c : ℚ := 2 * k + (und a k T : ℚ) / 10
/-- The bound `R = Σ U_i − (c·k + βV)`, with `βV = T + k·shift`. -/
def R : ℚ := ((a.map (Ladder.short (w a k) (top a k T))).map (U a k T)).sum -
  (c a k T * k + (T + k * shift a))

variable {a k T}

/-- **Prices.** Between `K_low` and `K_top` the call prices are positive, at most the
underlying, at least the intrinsic value (which is zero, every strike being out of the
money), and fall as the strike rises; the price curve is affine, so convex. -/
theorem price_valid (hk : 1 ≤ k) {K : ℤ} (h1 : 2 * und a k T ≤ K) (h2 : K ≤ top a k T) :
    0 < price a k T K ∧ price a k T K ≤ und a k T ∧
      max ((und a k T : ℚ) - K) 0 = 0 ∧ max ((und a k T : ℚ) - K) 0 ≤ price a k T K := by
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hu : (0 : ℤ) < und a k T := by simp only [und]; positivity
  have hd : ((top a k T - K : ℤ) : ℚ) ≤ V a k T := by
    have : top a k T - K ≤ V a k T := by simp only [top] at h2 ⊢; omega
    exact_mod_cast this
  have hd0 : (0 : ℚ) ≤ ((top a k T - K : ℤ) : ℚ) := by
    have : 0 ≤ top a k T - K := by omega
    exact_mod_cast this
  have hK : (2 * und a k T : ℚ) ≤ K := by exact_mod_cast h1
  have hu' : (0 : ℚ) < und a k T := by exact_mod_cast hu
  have hmax : max ((und a k T : ℚ) - K) 0 = 0 := max_eq_right (by linarith)
  have hpos : 0 < price a k T K := by simp only [price]; positivity
  refine ⟨hpos, ?_, hmax, by rw [hmax]; exact hpos.le⟩
  have : ((top a k T - K : ℤ) : ℚ) / (2 * k) ≤ T + k * shift a := by
    rw [div_le_iff₀ (by positivity)]
    calc ((top a k T - K : ℤ) : ℚ) ≤ V a k T := hd
      _ = (T + k * shift a) * (2 * k) := by simp only [V]; push_cast; ring
  have h0 : (0 : ℚ) ≤ T := by positivity
  have h0' : (0 : ℚ) ≤ k * shift a := by positivity
  simp only [price, und]
  push_cast at this ⊢
  linarith

theorem price_antitone {K₁ K₂ : ℤ} (hk : 1 ≤ k) (h : K₁ ≤ K₂) :
    price a k T K₂ ≤ price a k T K₁ := by
  have hk' : (0 : ℚ) < 2 * k := by have : (1 : ℚ) ≤ k := by exact_mod_cast hk
                                   linarith
  simp only [price]
  have : ((top a k T - K₂ : ℤ) : ℚ) ≤ ((top a k T - K₁ : ℤ) : ℚ) := by
    exact_mod_cast (by omega : top a k T - K₂ ≤ top a k T - K₁)
  have := div_le_div_of_nonneg_right this hk'.le
  linarith

/-- The short of `x` is priced `2k + x + shift`, and R3 asks `c + x + shift` for it. -/
lemma U_short (hk : 1 ≤ k) (x : ℕ) (hx : w a k x ≤ V a k T) :
    U a k T (Ladder.short (w a k) (top a k T) x) = c a k T + (x + shift a) := by
  have hk' : (0 : ℚ) < 2 * k := by have : (1 : ℚ) ≤ k := by exact_mod_cast hk
                                   linarith
  set K := Ladder.short (w a k) (top a k T) x
  have hKt : top a k T - K = 2 * k * (x + shift a) := by simp [K, Ladder.short, w]
  have hK : 2 * und a k T ≤ K := by
    have : (w a k x : ℤ) ≤ V a k T := by exact_mod_cast hx
    simp only [K, Ladder.short, top]; omega
  have hp : price a k T K = 2 * k + (x + shift a) := by
    simp only [price, hKt]
    push_cast
    field_simp
  have hu : (0 : ℚ) < und a k T := by
    have : (0 : ℤ) < und a k T := by simp only [und]; positivity
    exact_mod_cast this
  have hK' : (2 * und a k T : ℚ) ≤ K := by exact_mod_cast hK
  have hm : max ((und a k T : ℚ) / 5 - max ((K : ℚ) - und a k T) 0) ((und a k T : ℚ) / 10) =
      (und a k T : ℚ) / 10 := by
    rw [max_eq_left (show (0 : ℚ) ≤ K - und a k T by linarith)]
    exact max_eq_right (by linarith)
  simp only [U, r3Call, hm, hp, c]
  ring

/-- The arithmetic of the proof. A group holding `j` shorts whose numbers sum to `s`, and
`l ∈ {0, 1}` low longs, saves `g = c j + (j·shift + s) − maxLoss` against leaving every
short uncovered; `g` is at most `c k + T + k·shift`, with equality only when `l = 1`,
`j = k` and `s = T`. -/
lemma saving_le {k j l s sm T sh c m : ℚ} (hk : 2 ≤ k) (hsm : 1 ≤ sm) (hsh : sh = 8 * sm)
    (hT : 0 ≤ T) (hTsm : T ≤ sm) (hj : 0 ≤ j) (hs : 0 ≤ s) (hssm : s ≤ sm) (hjs : j ≤ s)
    (hc : c = 2 * k + (2 * (2 * k + T + k * sh)) / 10)
    (hl : l = 0 ∨ l = 1) (hm0 : 0 ≤ m)
    (hm : 2 * k * ((j * sh + s) - l * (T + k * sh)) ≤ m)
    (hjint : j ≤ k - 1 ∨ j = k ∨ k + 1 ≤ j) :
    c * j + (j * sh + s) - m ≤ c * k + (T + k * sh) ∧
      (c * k + (T + k * sh) ≤ c * j + (j * sh + s) - m → l = 1 ∧ j = k ∧ s = T) := by
  have hc0 : 0 < c := by rw [hc]; nlinarith
  -- (I2): `(2k − 1)(shift − T) > c`, so also `(2k − 1)·shift > c`.
  have hI2 : c < (2 * k - 1) * (sh - T) := by
    rw [hc, hsh]
    nlinarith [mul_le_mul_of_nonneg_left hTsm (show (0 : ℚ) ≤ k by linarith)]
  have hI2' : c ≤ (2 * k - 1) * sh := by nlinarith
  rcases hl with rfl | rfl
  · -- No low long: every short costs more than it saves.
    have e1 : c * j ≤ (2 * k - 1) * sh * j := mul_le_mul_of_nonneg_right hI2' hj
    have e2 : 0 ≤ (2 * k - 1) * s := mul_nonneg (by linarith) hs
    have hpos : 0 < c * k + (T + k * sh) := by nlinarith
    refine ⟨by nlinarith, fun h => ?_⟩
    exfalso; nlinarith
  · simp only [one_mul] at hm
    rcases hjint with hj' | hjk | hj'
    · -- Fewer than `k` shorts: no loss is charged, and too little is saved.
      have e1 : c * j ≤ c * (k - 1) := mul_le_mul_of_nonneg_left hj' hc0.le
      have e2 : j * sh ≤ (k - 1) * sh := mul_le_mul_of_nonneg_right hj' (by linarith)
      refine ⟨by nlinarith, fun h => ?_⟩
      exfalso; nlinarith
    · -- Exactly `k`: the loss is `2k(s − T)` if positive.
      have hk1 : (1 : ℚ) ≤ 2 * k - 1 := by linarith
      rw [hjk] at hm ⊢
      refine ⟨?_, fun h => ⟨rfl, rfl, ?_⟩⟩
      · rcases le_total s T with h' | h'
        · nlinarith
        · nlinarith [mul_le_mul_of_nonneg_right hk1 (sub_nonneg.2 h')]
      · rcases le_total s T with h' | h'
        · nlinarith
        · nlinarith [mul_le_mul_of_nonneg_right hk1 (sub_nonneg.2 h')]
    · -- More than `k`: the loss outweighs the extra saving.
      have hd : 1 ≤ j - k := by linarith
      have e1 : (j - k) * (sh - T) ≤ (j - k) * sh - T := by nlinarith
      have e2 : (2 * k - 1) * ((j - k) * (sh - T)) ≤ (2 * k - 1) * ((j * sh + s) - (T + k * sh)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      have e3 : c * (j - k) < (2 * k - 1) * (sh - T) * (j - k) :=
        mul_lt_mul_of_pos_right hI2 (by linarith)
      refine ⟨by nlinarith, fun h => ?_⟩
      exfalso; nlinarith

/-- **Theorem 4.** Let the numbers be positive, `2 ≤ k` and `T ≤ Σa`. Then exactly `k` of
the numbers sum to `T` exactly when some group of the position, with every uncovered
requirement R3's (`U`), costs at most `R`. -/
theorem theorem4 (ha : ∀ x ∈ a, 0 < x) (hne : a ≠ 0) (hk : 2 ≤ k) (hTsm : T ≤ a.sum) :
    KSubsetSum a k T ↔
      ∃ g, IsGroup (pos a k T) g ∧ groupCost (pos a k T) g (U a k T) ≤ R a k T := by
  have hsm : 1 ≤ a.sum := by
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    exact le_trans (ha x hx) (Multiset.le_sum_of_mem hx)
  have hk1 : 1 ≤ k := by omega
  have hV : 0 < V a k T := by simp only [V, shift]; positivity
  have hw : ∀ x ∈ a, w a k x ≤ V a k T := by
    intro x hx
    have := Multiset.le_sum_of_mem hx
    simp only [w, V, shift]
    have : x + 8 * a.sum ≤ T + k * (8 * a.sum) := by nlinarith
    exact Nat.mul_le_mul_left _ this
  have hsumU : ∀ A ≤ a, ((A.map (Ladder.short (w a k) (top a k T))).map (U a k T)).sum =
      c a k T * card A + (card A * shift a + A.sum) := by
    intro A hA
    rw [Multiset.map_map, Multiset.map_congr rfl fun x hx => by
      simp only [Function.comp_apply]
      exact U_short hk1 x (hw x (Multiset.mem_of_le hA hx))]
    rw [Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
      Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
      Nat.cast_multiset_sum]
    ring
  have hcost : ∀ g A, A ≤ a → g.2 = A.map (Ladder.short (w a k) (top a k T)) →
      groupCost (pos a k T) g (U a k T) = maxLoss g +
        ((a.map (Ladder.short (w a k) (top a k T))).map (U a k T)).sum -
        (c a k T * card A + (card A * shift a + A.sum)) := by
    intro g A hA hg2
    rw [groupCost, hg2, pos, Ladder.sum_rest _ hA, hsumU A hA]
    ring
  have hk' : (2 : ℚ) ≤ k := by exact_mod_cast hk
  constructor
  · rintro ⟨S, hS, hcard, hsum⟩
    have hsw : (S.map (w a k)).sum = V a k T := by
      show (S.map fun x => 2 * k * (x + shift a)).sum = _
      rw [Multiset.sum_map_mul_left, Multiset.sum_map_add, Multiset.map_const',
        Multiset.sum_replicate, smul_eq_mul, Multiset.map_id', hsum, hcard, V]
    obtain ⟨g, hg, hg2, hml⟩ := Ladder.construct hV hw hS hsw
    refine ⟨g, hg, le_of_eq ?_⟩
    rw [hcost g S hS hg2, hml, R, hcard, hsum]
    push_cast
    ring
  · rintro ⟨g, hg, hle⟩
    obtain ⟨A, hA, l, hl, hg2, hml⟩ := Ladder.decomp hV
      (fun K => (top a k T - K).toNat / (2 * k) - shift a)
      (fun x _ => by
        show (top a k T - (top a k T - (w a k x : ℤ))).toNat / (2 * k) - shift a = x
        rw [sub_sub_cancel, Int.toNat_natCast, w, Nat.mul_div_cancel_left _ (by omega)]
        omega) hg
    rw [hcost g A hA hg2, R] at hle
    -- The loss bound, in the paper's units: `maxLoss ≥ 2k(j·shift + s − l(T + k·shift))`.
    have hwA : ((A.map (w a k)).sum : ℤ) = 2 * k * (card A * shift a + A.sum) := by
      show (((A.map fun x => 2 * k * (x + shift a)).sum : ℕ) : ℤ) = _
      rw [Multiset.sum_map_mul_left, Multiset.sum_map_add, Multiset.map_const',
        Multiset.sum_replicate, smul_eq_mul, Multiset.map_id']
      push_cast; ring
    have hVc : (V a k T : ℤ) = 2 * k * (T + k * shift a) := by simp [V]
    have hmlq : (2 * k * ((card A * shift a + A.sum) - l * (T + k * shift a)) : ℚ) ≤
        maxLoss g := by
      have h := hml
      rw [hwA, hVc] at h
      have : (2 * k * ((card A * shift a + A.sum) - l * (T + k * shift a)) : ℤ) ≤ maxLoss g := by
        linarith
      exact_mod_cast this
    have hjs : (card A : ℚ) ≤ A.sum := by
      have : card A ≤ A.sum := by
        have := Multiset.card_nsmul_le_sum (s := A) (a := 1)
          (fun x hx => ha x (Multiset.mem_of_le hA hx))
        simpa using this
      exact_mod_cast this
    have hssm : (A.sum : ℚ) ≤ a.sum := by
      have := congrArg Multiset.sum (add_tsub_cancel_of_le hA)
      rw [Multiset.sum_add] at this
      exact_mod_cast (by omega : A.sum ≤ a.sum)
    have hjint : (card A : ℚ) ≤ k - 1 ∨ (card A : ℚ) = k ∨ (k : ℚ) + 1 ≤ card A := by
      rcases lt_trichotomy (card A) k with h | h | h
      · left; have : card A + 1 ≤ k := h; exact_mod_cast (by omega : (card A : ℤ) ≤ k - 1)
      · right; left; exact_mod_cast h
      · right; right; exact_mod_cast h
    have key := saving_le (k := k) (j := card A) (l := l) (s := A.sum) (sm := a.sum) (T := T)
      (sh := shift a) (c := c a k T) (m := maxLoss g) hk' (by exact_mod_cast hsm)
      (by simp [shift]) (by positivity) (by exact_mod_cast hTsm) (by positivity)
      (by positivity) hssm hjs (by simp [c, und]) (by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with h | h <;> simp [h])
      (by exact_mod_cast maxLoss_nonneg g) hmlq hjint
    obtain ⟨-, hj, hs⟩ := key.2 (by linarith)
    exact ⟨A, hA, by exact_mod_cast hj, by exact_mod_cast hs⟩

/-- **Size.** The position has `2n + 1` contracts at strikes from `K_low = 2S` to
`K_top = 2S + V`, every number polynomial in `k`, `T` and `Σa`. -/
theorem size (hk : 2 ≤ k) (hTsm : T ≤ a.sum) :
    card (pos a k T).1 + card (pos a k T).2 = 2 * card a + 1 ∧
    ∀ K ∈ strikes (pos a k T), 2 * und a k T ≤ K ∧ K ≤ top a k T := by
  have hw : ∀ x ∈ a, w a k x ≤ V a k T := by
    intro x hx
    have := Multiset.le_sum_of_mem hx
    simp only [w, V, shift]
    have : x + 8 * a.sum ≤ T + k * (8 * a.sum) := by nlinarith
    exact Nat.mul_le_mul_left _ this
  obtain ⟨h1, h2⟩ := Ladder.size (top := top a k T) hw
  refine ⟨h1, fun K hK => ?_⟩
  have := h2 K hK
  simp only [top] at this ⊢
  constructor <;> omega

end KSubsetSumInstance

end PairingHardness
