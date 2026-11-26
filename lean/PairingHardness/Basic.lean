module

public import PairingHardness.Spread

/-!
# Numerical 3-dimensional matching and pairings

The source problem of Theorems 1 and 2, and what a pairing of a position is.
-/

@[expose] public section

namespace PairingHardness

open Multiset

/-- An instance of numerical 3-dimensional matching: three multisets of numbers and a
bound. -/
structure N3DM where
  A : Multiset ℕ
  B : Multiset ℕ
  C : Multiset ℕ
  bound : ℕ

namespace N3DM

variable (I : N3DM)

/-- The number of triples. -/
def n : ℕ := card I.A

/-- A well-formed instance: `n` positive numbers in each multiset and a positive bound
(Garey and Johnson, problem SP16). -/
def Valid : Prop :=
  card I.B = I.n ∧ card I.C = I.n ∧ 0 < I.bound ∧ ∀ a ∈ I.A + I.B + I.C, 0 < a

/-- A triple `(a, b, c)` taken from the instance with `a + b + c` equal to the bound. -/
def Good (τ : ℕ × ℕ × ℕ) : Prop :=
  τ.1 ∈ I.A ∧ τ.2.1 ∈ I.B ∧ τ.2.2 ∈ I.C ∧ τ.1 + τ.2.1 + τ.2.2 = I.bound

/-- The numbers split into triples, each number used once, each triple summing to the
bound. -/
def HasMatching : Prop :=
  ∃ T : Multiset (ℕ × ℕ × ℕ), T.map (·.1) = I.A ∧ T.map (·.2.1) = I.B ∧
    T.map (·.2.2) = I.C ∧ ∀ τ ∈ T, τ.1 + τ.2.1 + τ.2.2 = I.bound

/-- `W`: the largest of the bound and the `3n` numbers. -/
def W : ℕ := max I.bound (I.A + I.B + I.C).sup

/-- `M = 6nW`. -/
def M : ℕ := 6 * I.n * I.W

lemma bound_le_W : I.bound ≤ I.W := le_max_left _ _

lemma le_W {a : ℕ} (h : a ∈ I.A + I.B + I.C) : a ≤ I.W :=
  le_trans (Multiset.le_sup h) (le_max_right _ _)

lemma A_le_W {a : ℕ} (h : a ∈ I.A) : a ≤ I.W := I.le_W (by simp [h])
lemma B_le_W {a : ℕ} (h : a ∈ I.B) : a ≤ I.W := I.le_W (by simp [h])
lemma C_le_W {a : ℕ} (h : a ∈ I.C) : a ≤ I.W := I.le_W (by simp [h])

variable {I}

lemma Valid.A_pos (hI : I.Valid) {a : ℕ} (h : a ∈ I.A) : 0 < a := hI.2.2.2 a (by simp [h])
lemma Valid.B_pos (hI : I.Valid) {a : ℕ} (h : a ∈ I.B) : 0 < a := hI.2.2.2 a (by simp [h])
lemma Valid.C_pos (hI : I.Valid) {a : ℕ} (h : a ∈ I.C) : 0 < a := hI.2.2.2 a (by simp [h])

lemma Valid.one_le_W (hI : I.Valid) : 1 ≤ I.W := le_trans hI.2.2.1 I.bound_le_W

/-- With no triples the empty matching works. -/
lemma Valid.hasMatching_of_n_eq_zero (hI : I.Valid) (h : I.n = 0) : I.HasMatching := by
  have hA : I.A = 0 := Multiset.card_eq_zero.1 h
  have hB : I.B = 0 := Multiset.card_eq_zero.1 (hI.1.trans h)
  have hC : I.C = 0 := Multiset.card_eq_zero.1 (hI.2.1.trans h)
  exact ⟨0, by simp [hA], by simp [hB], by simp [hC], by simp⟩

/-- A matching makes the totals add up: `ΣA + ΣB + ΣC = nB`. -/
lemma HasMatching.sum_eq (h : I.HasMatching) :
    I.A.sum + I.B.sum + I.C.sum = I.n * I.bound := by
  obtain ⟨T, hA, hB, hC, hT⟩ := h
  have : (T.map fun τ => τ.1 + τ.2.1 + τ.2.2).sum = (T.map fun _ => I.bound).sum :=
    congrArg Multiset.sum (Multiset.map_congr rfl hT)
  rw [Multiset.sum_map_add, Multiset.sum_map_add, Multiset.map_const', Multiset.sum_replicate,
    hA, hB, hC] at this
  rw [this, N3DM.n, ← hA, Multiset.card_map, smul_eq_mul]

/-- The triples of a matching are good. -/
lemma HasMatching.exists_good (h : I.HasMatching) :
    ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, I.Good τ) ∧ T.map (·.1) = I.A ∧
      T.map (·.2.1) = I.B ∧ T.map (·.2.2) = I.C := by
  obtain ⟨T, hA, hB, hC, hT⟩ := h
  refine ⟨T, fun τ hτ => ⟨?_, ?_, ?_, hT τ hτ⟩, hA, hB, hC⟩
  · rw [← hA]; exact Multiset.mem_map_of_mem _ hτ
  · rw [← hB]; exact Multiset.mem_map_of_mem _ hτ
  · rw [← hC]; exact Multiset.mem_map_of_mem _ hτ

/-- A multiset of good triples using each number once is a matching. -/
lemma hasMatching_of_good (T : Multiset (ℕ × ℕ × ℕ)) (hT : ∀ τ ∈ T, I.Good τ)
    (hA : T.map (·.1) = I.A) (hB : T.map (·.2.1) = I.B) (hC : T.map (·.2.2) = I.C) :
    I.HasMatching :=
  ⟨T, hA, hB, hC, fun τ h => (hT τ h).2.2.2⟩

end N3DM

/-- A pairing of a position into spreads of some recognized kinds `σ`, each with its
contracts `shape s`. Every short contract is in exactly one spread or left uncovered, and
every long contract is in at most one spread. -/
structure Pairing {σ : Type} (shape : σ → Spread) (pos : Spread) where
  spreads : List σ
  uncovered : Multiset ℤ
  shorts_eq : (spreads.map fun s => (shape s).2).sum + uncovered = pos.2
  longs_le : (spreads.map fun s => (shape s).1).sum ≤ pos.1

namespace Pairing

variable {σ : Type} {shape : σ → Spread} {pos : Spread}

/-- The requirement of a pairing: the requirements of its spreads, plus `U K` for each
short contract at `K` left uncovered (rules.md R3). -/
def requirement (p : Pairing shape pos) (req : σ → ℚ) (U : ℤ → ℚ) : ℚ :=
  (p.spreads.map req).sum + (p.uncovered.map U).sum

lemma list_sum_eq_zero_iff {α : Type} (l : List α) (f : α → ℚ) (hf : ∀ a, 0 ≤ f a) :
    (l.map f).sum = 0 ↔ ∀ a ∈ l, f a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h0 : 0 ≤ (l.map f).sum := List.sum_nonneg (by simp [hf])
    simp only [List.map_cons, List.sum_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · intro h
      have ha : f a = 0 := le_antisymm (by linarith [hf a]) (hf a)
      exact ⟨ha, ih.1 (by linarith)⟩
    · rintro ⟨ha, hl⟩
      rw [ha, ih.2 hl, add_zero]

/-- With nonnegative spread requirements and positive uncovered requirements, a pairing
requires nothing exactly when it leaves no short uncovered and every spread in it
requires nothing. -/
lemma requirement_eq_zero_iff (p : Pairing shape pos) (req : σ → ℚ) (U : ℤ → ℚ)
    (hreq : ∀ s, 0 ≤ req s) (hU : ∀ K, 0 < U K) :
    p.requirement req U = 0 ↔ p.uncovered = 0 ∧ ∀ s ∈ p.spreads, req s = 0 := by
  have h1 : 0 ≤ (p.spreads.map req).sum := List.sum_nonneg (by simp [hreq])
  have h2 : 0 ≤ (p.uncovered.map U).sum :=
    Multiset.sum_nonneg (by simp only [Multiset.mem_map]; rintro _ ⟨K, _, rfl⟩; exact (hU K).le)
  have h3 : (p.uncovered.map U).sum = 0 ↔ p.uncovered = 0 := by
    constructor
    · intro h
      by_contra hne
      obtain ⟨K, hK⟩ := Multiset.exists_mem_of_ne_zero hne
      have hle : U K ≤ (p.uncovered.map U).sum :=
        Multiset.single_le_sum
          (by simp only [Multiset.mem_map]; rintro _ ⟨K, _, rfl⟩; exact (hU K).le)
          _ (Multiset.mem_map_of_mem U hK)
      linarith [hU K]
    · rintro h; simp [h]
  rw [requirement, ← list_sum_eq_zero_iff _ _ hreq, ← h3]
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨ha, hb⟩; rw [ha, hb, add_zero]

/-- Each spread's contracts come from the position. -/
lemma shorts_le (p : Pairing shape pos) {s : σ} (hs : s ∈ p.spreads) : (shape s).2 ≤ pos.2 := by
  rw [← p.shorts_eq]
  exact le_trans (List.le_sum_of_mem (List.mem_map_of_mem (f := fun s => (shape s).2) hs))
    (Multiset.le_add_right _ _)

lemma longs_le' (p : Pairing shape pos) {s : σ} (hs : s ∈ p.spreads) : (shape s).1 ≤ pos.1 :=
  le_trans (List.le_sum_of_mem (List.mem_map_of_mem (f := fun s => (shape s).1) hs)) p.longs_le

end Pairing

/-! ### Sums over lists of spreads -/

section ListSums

variable {σ α : Type}

lemma card_list_sum (l : List σ) (f : σ → Multiset α) :
    card (l.map f).sum = (l.map fun s => card (f s)).sum := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

lemma filter_list_sum (p : α → Prop) [DecidablePred p] (l : List σ) (f : σ → Multiset α) :
    (l.map f).sum.filter p = (l.map fun s => (f s).filter p).sum := by
  induction l with
  | nil => simp
  | cons s l ih => simp [Multiset.filter_add, ih]

lemma sum_list_sum (l : List σ) (f : σ → Multiset ℤ) :
    (l.map f).sum.sum = (l.map fun s => (f s).sum).sum := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

/-- If `g ≤ f` term by term and the totals go the other way, then `f = g` term by term. -/
lemma list_eq_of_le_of_sum_le (l : List σ) (f g : σ → ℕ) (h : ∀ s ∈ l, g s ≤ f s)
    (hs : (l.map f).sum ≤ (l.map g).sum) : ∀ s ∈ l, f s = g s := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    have hl : ∀ s ∈ l, g s ≤ f s := fun s hs => h s (List.mem_cons_of_mem _ hs)
    have h1 := List.sum_le_sum (l := l) (f := g) (g := f) hl
    have h2 := h s (List.mem_cons_self ..)
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · omega
    · exact ih hl (by omega) s' hs'

/-- Nonpositive terms with total zero are all zero. -/
lemma list_eq_zero_of_nonpos (l : List σ) (f : σ → ℤ) (h : ∀ s ∈ l, f s ≤ 0)
    (hs : (l.map f).sum = 0) : ∀ s ∈ l, f s = 0 := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    have hl : ∀ s ∈ l, f s ≤ 0 := fun s hs => h s (List.mem_cons_of_mem _ hs)
    have h1 : (l.map f).sum ≤ 0 := by
      have := List.sum_le_sum (l := l) (f := f) (g := fun _ => (0 : ℤ)) hl
      simpa using this
    have h2 := h s (List.mem_cons_self ..)
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · omega
    · exact ih hl (by omega) s' hs'

lemma list_sum_map_sub (l : List σ) (f g : σ → ℤ) :
    (l.map fun s => f s - g s).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]; ring

lemma list_sum_map_toList {M : Type} [AddCommMonoid M] (T : Multiset α) (g : α → M) :
    (T.toList.map g).sum = (T.map g).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]

lemma sum_map_hom_singleton {β : Type} (φ : Multiset α →+ Multiset β) (T : Multiset α) :
    (T.map fun τ => φ {τ}).sum = φ T := by
  induction T using Multiset.induction_on with
  | empty => simp
  | cons a T ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, ← _root_.map_add, Multiset.singleton_add]

end ListSums

/-- A multiset of triples, each giving one spread `(φ {τ}, ψ {τ})`, makes a pairing that
covers every short when `ψ T` is all the shorts and `φ T` fits in the longs. -/
lemma exists_pairing_of_triples {σ : Type} (shape : σ → Spread) (pos : Spread)
    (φ ψ : Multiset (ℕ × ℕ × ℕ) →+ Multiset ℤ) (P : ℕ × ℕ × ℕ → Prop)
    (T : Multiset (ℕ × ℕ × ℕ)) (hP : ∀ τ ∈ T, P τ) (mk : ∀ τ, P τ → σ)
    (hmk : ∀ τ h, shape (mk τ h) = (φ {τ}, ψ {τ})) (hL : φ T ≤ pos.1) (hS : ψ T = pos.2) :
    ∃ p : Pairing shape pos, p.uncovered = 0 ∧ ∀ s ∈ p.spreads, ∃ τ h, s = mk τ h := by
  let l := T.toList.attach.map fun x => mk x.1 (hP x.1 (Multiset.mem_toList.1 x.2))
  have hl : ∀ f : Spread → Multiset ℤ, (l.map fun s => f (shape s)) =
      T.toList.map fun τ => f (φ {τ}, ψ {τ}) := by
    intro f
    simp only [l, List.map_map, Function.comp_def, hmk]
    exact List.attach_map_val (f := fun τ => f (φ {τ}, ψ {τ}))
  refine ⟨⟨l, 0, ?_, ?_⟩, rfl, ?_⟩
  · rw [add_zero, hl (·.2), list_sum_map_toList, sum_map_hom_singleton, hS]
  · rw [hl (·.1), list_sum_map_toList, sum_map_hom_singleton]; exact hL
  · intro s hs
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hs
    exact ⟨_, _, rfl⟩

/-- Collect a decomposition of each spread in a list into one decomposition of their
sums. `φ` and `ψ` read off the long and short contracts of a multiset of triples. -/
lemma exists_triples_of_forall {σ : Type} (shape : σ → Spread) (P : ℕ × ℕ × ℕ → Prop)
    (φ ψ : Multiset (ℕ × ℕ × ℕ) →+ Multiset ℤ) (l : List σ)
    (h : ∀ s ∈ l, ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, P τ) ∧ (shape s).1 = φ T ∧
      (shape s).2 = ψ T) :
    ∃ T : Multiset (ℕ × ℕ × ℕ), (∀ τ ∈ T, P τ) ∧ (l.map fun s => (shape s).1).sum = φ T ∧
      (l.map fun s => (shape s).2).sum = ψ T := by
  induction l with
  | nil => exact ⟨0, by simp, by simp, by simp⟩
  | cons s l ih =>
    obtain ⟨T₁, hP₁, h₁, h₁'⟩ := h s (List.mem_cons_self ..)
    obtain ⟨T₂, hP₂, h₂, h₂'⟩ := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    refine ⟨T₁ + T₂, ?_, ?_, ?_⟩
    · intro τ hτ
      rcases Multiset.mem_add.1 hτ with hτ | hτ
      exacts [hP₁ τ hτ, hP₂ τ hτ]
    · simp [h₁, h₂]
    · simp [h₁', h₂']

/-- Split a multiset `A.map f + C.map g` back into `A` and `C`, when `f` and `g` are
injective and every value of `f` lies below every value of `g`. -/
lemma decode_add {f g : ℕ → ℤ} (hf : Function.Injective f) (hg : Function.Injective g)
    (θ : ℤ) {A C A' C' : Multiset ℕ} (hA : ∀ a ∈ A + A', f a < θ)
    (hC : ∀ c ∈ C + C', θ ≤ g c) (h : A.map f + C.map g = A'.map f + C'.map g) :
    A = A' ∧ C = C' := by
  have key : ∀ X Y : Multiset ℕ, (∀ a ∈ X, f a < θ) → (∀ c ∈ Y, θ ≤ g c) →
      (X.map f + Y.map g).filter (· < θ) = X.map f ∧
      (X.map f + Y.map g).filter (fun k => ¬ k < θ) = Y.map g := by
    intro X Y hX hY
    rw [Multiset.filter_add, Multiset.filter_add,
      Multiset.filter_eq_self.2 (by simpa using hX),
      Multiset.filter_eq_nil.2 (by simpa using hY),
      Multiset.filter_eq_nil.2 (by simpa using hX),
      Multiset.filter_eq_self.2 (by simpa using hY)]
    simp
  have k1 := key A C (fun a h => hA a (Multiset.mem_add.2 (Or.inl h)))
    (fun c h => hC c (Multiset.mem_add.2 (Or.inl h)))
  have k2 := key A' C' (fun a h => hA a (Multiset.mem_add.2 (Or.inr h)))
    (fun c h => hC c (Multiset.mem_add.2 (Or.inr h)))
  refine ⟨Multiset.map_injective hf ?_, Multiset.map_injective hg ?_⟩
  · rw [← k1.1, ← k2.1, h]
  · rw [← k1.2, ← k2.2, h]

end PairingHardness
