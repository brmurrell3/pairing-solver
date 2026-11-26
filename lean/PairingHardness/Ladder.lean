module

public import PairingHardness.Basic

/-!
# The position of Theorems 3 and 4

Both reductions to the one-group problem use the same shape (docs/proofs.md, Theorems 3 and
4). For numbers `a`, a depth `w x` for each number and a total `V`, the position is

    long one call at  top − V
    long n calls at   top
    short one call at top − w(x)    for each number x

A group is a set of its contracts. This file proves the two facts the theorems share: a group
holding `l ∈ {0, 1}` low longs and the shorts of `A` has maximum loss at least `w(A) − l V`,
and when `w(A) = V` the low long, `|A| − 1` top longs and the shorts of `A` have no loss.
-/

@[expose] public section

namespace PairingHardness

open Multiset

/-- A group taken from a position: some of its longs and shorts, balanced. -/
def IsGroup (pos g : Spread) : Prop := g.1 ≤ pos.1 ∧ g.2 ≤ pos.2 ∧ Balanced g

/-- The requirement of one maximum-loss group: its maximum loss, plus `U K` for each short
of the position at `K` left out of it. -/
def groupCost (pos g : Spread) (U : ℤ → ℚ) : ℚ := maxLoss g + ((pos.2 - g.2).map U).sum

namespace Ladder

variable (a : Multiset ℕ) (w : ℕ → ℕ) (V : ℕ) (top : ℤ)

/-- The short strike of the number `x`. -/
def short (x : ℕ) : ℤ := top - w x

/-- The position. -/
def pos : Spread := ({top - V} + replicate (card a) top, a.map (short w top))

variable {a w V top}

/-- The shorts left out of a group with the shorts of `A` require all the shorts' amounts
less those of `A`. -/
lemma sum_rest (U : ℤ → ℚ) {A : Multiset ℕ} (hA : A ≤ a) :
    (((pos a w V top).2 - A.map (short w top)).map U).sum =
      ((a.map (short w top)).map U).sum - ((A.map (short w top)).map U).sum := by
  have hle : A.map (short w top) ≤ (pos a w V top).2 := Multiset.map_le_map hA
  have e := congrArg (fun s => (s.map U).sum) (add_tsub_cancel_of_le hle)
  simp only [Multiset.map_add, Multiset.sum_add] at e
  simp only [pos] at e ⊢
  linarith

/-- **The lower bound.** A group holds the shorts of some `A ≤ a` and `l ≤ 1` low longs, and
its maximum loss is at least `w(A) − l V`, its loss at `top`. -/
lemma decomp (hV : 0 < V) (dec : ℤ → ℕ) (hdec : ∀ x ∈ a, dec (short w top x) = x)
    {g : Spread} (hg : IsGroup (pos a w V top) g) :
    ∃ A ≤ a, ∃ l : ℕ, l ≤ 1 ∧ g.2 = A.map (short w top) ∧
      ((A.map w).sum : ℤ) - l * V ≤ maxLoss g := by
  obtain ⟨hL, hS, hb⟩ := hg
  have hmem : ∀ k ∈ g.2, ∃ x ∈ a, short w top x = k := fun k hk =>
    Multiset.mem_map.1 (Multiset.mem_of_le hS hk)
  have hA : g.2.map dec ≤ a := by
    have := Multiset.map_le_map (f := dec) hS
    simp only [pos, Multiset.map_map] at this
    rwa [Multiset.map_congr rfl (g := id) (fun x hx => by simp [hdec x hx]),
      Multiset.map_id] at this
  have hg2 : g.2 = (g.2.map dec).map (short w top) := by
    rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id g.2]
    refine Multiset.map_congr rfl fun k hk => ?_
    obtain ⟨x, hx, rfl⟩ := hmem k hk
    simp [hdec x hx]
  refine ⟨g.2.map dec, hA, count (top - V) g.1, ?_, hg2, ?_⟩
  · have := Multiset.count_le_of_le (top - V) hL
    simp only [pos, Multiset.count_add, Multiset.count_singleton_self,
      Multiset.count_replicate] at this
    split_ifs at this <;> omega
  -- The longs: `l` at `top − V`, the rest at `top`.
  have hlongs : g.1.sum = count (top - V) g.1 * (top - V) +
      (card g.1 - count (top - V) g.1 : ℕ) * top := by
    have e := Multiset.filter_add_not (· = top - V) g.1
    have e1 : g.1.filter (· = top - V) = replicate (count (top - V) g.1) (top - V) :=
      Multiset.filter_eq' g.1 _
    have e2 : g.1.filter (fun k => ¬ k = top - V) =
        replicate (card g.1 - count (top - V) g.1) top := by
      refine Multiset.eq_replicate.2 ⟨?_, fun k hk => ?_⟩
      · have := congrArg card e
        rw [Multiset.card_add, e1, Multiset.card_replicate] at this
        omega
      · rw [Multiset.mem_filter] at hk
        have := Multiset.mem_of_le hL hk.1
        simp only [pos, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate] at this
        rcases this with h1 | ⟨-, h2⟩
        · exact absurd h1 hk.2
        · exact h2
    conv_lhs => rw [← e]
    rw [Multiset.sum_add, e1, e2, Multiset.sum_replicate, Multiset.sum_replicate, nsmul_eq_mul,
      nsmul_eq_mul]
  have hshorts : g.2.sum = card g.2 * top - ((g.2.map dec).map w).sum := by
    conv_lhs => rw [hg2]
    show ((g.2.map dec).map fun x => top - (w x : ℤ)).sum = _
    rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
      Multiset.card_map, Nat.cast_multiset_sum, Multiset.map_map, Multiset.map_map,
      Multiset.map_map]
    rfl
  have hcount : count (top - V) g.1 ≤ card g.1 := Multiset.count_le_card _ _
  have hmom : moment g = ((g.2.map dec).map w).sum - count (top - V) g.1 * V := by
    rw [moment, hlongs, hshorts, ← hb]
    push_cast [hcount]
    ring
  have := moment_le_maxLoss g hb
  rw [hmom] at this
  exact_mod_cast this

/-- **The construction.** If `w(S) = V`, the low long, `|S| − 1` top longs and the shorts of
`S` form a group with no loss: between `top − V` and `top` each short loses at most its share
`w(x) / V` of the low long's gain. -/
lemma construct (hV : 0 < V) (hw : ∀ x ∈ a, w x ≤ V) {S : Multiset ℕ} (hS : S ≤ a)
    (hsum : (S.map w).sum = V) :
    ∃ g, IsGroup (pos a w V top) g ∧ g.2 = S.map (short w top) ∧ maxLoss g = 0 := by
  have hS0 : S ≠ 0 := by rintro rfl; simp at hsum; omega
  have hc : 1 ≤ card S := Multiset.card_pos.2 hS0
  let g : Spread := ({top - V} + replicate (card S - 1) top, S.map (short w top))
  have hwS : ∀ x ∈ S, w x ≤ V := fun x hx => hw x (Multiset.mem_of_le hS hx)
  refine ⟨g, ⟨?_, Multiset.map_le_map hS, ?_⟩, rfl, ?_⟩
  · show {top - V} + replicate (card S - 1) top ≤ {top - V} + replicate (card a) top
    refine add_le_add_right ((Multiset.replicate_le_replicate _).2 ?_) _
    have := Multiset.card_le_card hS; omega
  · simp [g, Balanced]; omega
  refine (maxLoss_eq_zero_iff g).2 fun K hK => ?_
  have hKr : top - V ≤ K ∧ K ≤ top := by
    simp only [g, strikes, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate,
      Multiset.mem_map] at hK
    rcases hK with (rfl | ⟨-, rfl⟩) | ⟨x, hx, rfl⟩
    · omega
    · omega
    · have : (w x : ℤ) ≤ V := by exact_mod_cast hwS x hx
      simp only [short]; omega
  have hV' : (0 : ℤ) < V := by exact_mod_cast hV
  have hshort : ∀ x ∈ S, (V : ℤ) * callValue K (short w top x) ≤ (K - (top - V)) * w x := by
    intro x hx
    have hxV : (w x : ℤ) ≤ V := by exact_mod_cast hwS x hx
    have hx0 : (0 : ℤ) ≤ w x := by positivity
    simp only [callValue, short]
    rcases le_total (K - (top - w x)) 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]
      nlinarith [mul_nonneg (sub_nonneg.2 hxV) (show (0 : ℤ) ≤ top - K by omega)]
  have hsum' : (V : ℤ) * ((S.map (short w top)).map (callValue K)).sum ≤ (K - (top - V)) * V := by
    rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
    calc (S.map fun x => (V : ℤ) * (callValue K ∘ short w top) x).sum
        ≤ (S.map fun x : ℕ => (K - (top - V)) * (w x : ℤ)).sum :=
          Multiset.sum_map_le_sum_map _ _ fun x hx => hshort x hx
      _ = (K - (top - V)) * V := by
          rw [Multiset.sum_map_mul_left, ← hsum, Nat.cast_multiset_sum, Multiset.map_map]
          rfl
  have hlow : callValue K (top - V) = K - (top - V) := by simp [callValue]; omega
  have htop : callValue K top = 0 := by simp [callValue]; omega
  simp only [payoff, g, Multiset.map_add, Multiset.map_singleton, Multiset.map_replicate,
    Multiset.sum_add, Multiset.sum_singleton, Multiset.sum_replicate, hlow, htop,
    smul_zero, add_zero]
  by_contra hneg
  push Not at hneg
  nlinarith

/-- **Size.** The position has `2n + 1` contracts at strikes from `top − V` to `top`. -/
lemma size (hw : ∀ x ∈ a, w x ≤ V) :
    card (pos a w V top).1 + card (pos a w V top).2 = 2 * card a + 1 ∧
    ∀ k ∈ strikes (pos a w V top), top - V ≤ k ∧ k ≤ top := by
  refine ⟨by simp [pos]; ring, fun k hk => ?_⟩
  simp only [pos, strikes, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_replicate,
    Multiset.mem_map] at hk
  rcases hk with (rfl | ⟨-, rfl⟩) | ⟨x, hx, rfl⟩
  · constructor <;> omega
  · constructor <;> omega
  · have : (w x : ℤ) ≤ V := by exact_mod_cast hw x hx
    simp only [short]; constructor <;> omega

end Ladder

end PairingHardness
