module

public import PairingHardness.Ladder

/-!
# Theorem 3: one maximum-loss group

The solver's model (docs/proofs.md, Theorem 3): choose one balanced group of contracts from
the position. Its requirement is the group's maximum loss plus `U K` for each short contract
at `K` left out. Subset sum reduces to deciding whether the least requirement is at most a
bound. With `K_top = T + 1` the position is

    long one call at  K_low = K_top − T = 1
    long n calls at   K_top
    short one call at K_i = K_top − a_i,  with U = a_i / 2,  for each i

and the bound is `R = (Σa − T) / 2`. It is `Ladder.pos` with `w = id` and `V = T`.
-/

@[expose] public section

namespace PairingHardness

open Multiset

/-- Subset sum: some of the numbers `a` sum to `T`. -/
def SubsetSum (a : Multiset ℕ) (T : ℕ) : Prop := ∃ S ≤ a, S.sum = T

/-- A number above `T` cannot be used, and a number equal to `T` answers yes. So it is
enough to decide instances whose numbers are all below `T`, as Theorem 3 assumes. -/
lemma subsetSum_iff_filter (a : Multiset ℕ) (T : ℕ) :
    SubsetSum a T ↔ T ∈ a ∨ SubsetSum (a.filter (· < T)) T := by
  constructor
  · rintro ⟨S, hS, hsum⟩
    by_cases h : ∀ x ∈ S, x < T
    · exact Or.inr ⟨S, Multiset.le_filter.2 ⟨hS, h⟩, hsum⟩
    · push Not at h
      obtain ⟨x, hx, hxT⟩ := h
      have := Multiset.le_sum_of_mem hx
      left
      rw [show T = x by omega]
      exact Multiset.mem_of_le hS hx
  · rintro (h | ⟨S, hS, hsum⟩)
    · exact ⟨{T}, Multiset.singleton_le.2 h, by simp⟩
    · exact ⟨S, le_trans hS (Multiset.filter_le _ _), hsum⟩

namespace SubsetSumInstance

variable (a : Multiset ℕ) (T : ℕ)

/-- The position of Theorem 3. -/
def pos : Spread := Ladder.pos a id T ((T : ℤ) + 1)

/-- The uncovered requirement at strike `K_i = K_top − a_i`, which is `a_i / 2`. -/
def U (k : ℤ) : ℚ := (((T : ℤ) + 1 - k : ℤ) : ℚ) / 2

/-- The bound `R = (Σa − T) / 2`. -/
def R : ℚ := ((a.sum : ℚ) - T) / 2

variable {a T}

lemma sum_U (s : Multiset ℕ) :
    ((s.map (Ladder.short id ((T : ℤ) + 1))).map (U T)).sum = (s.sum : ℚ) / 2 := by
  rw [Multiset.map_map]
  have : (U T ∘ Ladder.short id ((T : ℤ) + 1)) = fun x : ℕ => (x : ℚ) / 2 := by
    funext x; simp [U, Ladder.short]
  rw [this, Multiset.sum_map_div, Nat.cast_multiset_sum]

/-- No group costs less than `R`, and one costing `R` or less has the low long and shorts
whose numbers sum to `T`. -/
lemma cost_ge_R (hT : 0 < T) {g : Spread} (hg : IsGroup (pos a T) g) :
    R a T ≤ groupCost (pos a T) g (U T) ∧
      (groupCost (pos a T) g (U T) ≤ R a T → SubsetSum a T) := by
  obtain ⟨S, hS, l, hl, hg2, hml⟩ := Ladder.decomp hT (fun k => ((T : ℤ) + 1 - k).toNat)
    (fun x _ => by simp [Ladder.short]) hg
  have hcost : groupCost (pos a T) g (U T) = maxLoss g + ((a.sum : ℚ) - S.sum) / 2 := by
    rw [groupCost, hg2, pos, Ladder.sum_rest _ hS, sum_U, sum_U]
    ring
  rw [Multiset.map_id] at hml
  have hmlq : (S.sum : ℚ) - l * T ≤ maxLoss g := by exact_mod_cast hml
  have hml0 : (0 : ℚ) ≤ maxLoss g := by exact_mod_cast maxLoss_nonneg g
  have hT' : (0 : ℚ) < T := by exact_mod_cast hT
  have hS0 : (0 : ℚ) ≤ S.sum := by positivity
  rw [hcost, R]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with rfl | rfl
  · simp only [Nat.cast_zero, zero_mul, sub_zero] at hmlq
    exact ⟨by linarith, fun h => absurd h (by linarith)⟩
  · simp only [Nat.cast_one, one_mul] at hmlq
    refine ⟨?_, fun h => ⟨S, hS, ?_⟩⟩
    · rcases le_or_gt (S.sum : ℚ) T with h3 | h3 <;> linarith
    · have : (S.sum : ℚ) = T := by linarith
      exact_mod_cast this

/-- **Theorem 3.** For numbers `0 < a_i < T`: some of them sum to `T` exactly when some group
of the position costs at most `R`. Every group costs at least `R` (`cost_ge_R`), so then the
minimum is `R`. -/
theorem theorem3 (ha : ∀ x ∈ a, 0 < x ∧ x < T) (hT : 0 < T) :
    SubsetSum a T ↔ ∃ g, IsGroup (pos a T) g ∧ groupCost (pos a T) g (U T) ≤ R a T := by
  constructor
  · rintro ⟨S, hS, hsum⟩
    obtain ⟨g, hg, hg2, hml⟩ := Ladder.construct (w := id) (top := (T : ℤ) + 1) hT
      (fun x hx => (ha x hx).2.le) hS (by rwa [Multiset.map_id])
    refine ⟨g, hg, le_of_eq ?_⟩
    rw [groupCost, hml, hg2, pos, Ladder.sum_rest _ hS, sum_U, sum_U, hsum, R]
    push_cast
    ring
  · rintro ⟨g, hg, h⟩
    exact (cost_ge_R hT hg).2 h

/-- **Size.** The position has `2n + 1` contracts at strikes from 1 to `T + 1`. -/
theorem size (ha : ∀ x ∈ a, 0 < x ∧ x < T) :
    card (pos a T).1 + card (pos a T).2 = 2 * card a + 1 ∧
    ∀ k ∈ strikes (pos a T), 1 ≤ k ∧ k ≤ (T : ℤ) + 1 := by
  obtain ⟨h1, h2⟩ := Ladder.size (a := a) (w := id) (V := T) (top := (T : ℤ) + 1)
    (fun x hx => (ha x hx).2.le)
  exact ⟨h1, fun k hk => by have := h2 k hk; constructor <;> omega⟩

end SubsetSumInstance

end PairingHardness
