import Std.Tactic.BVDecide

def binarySearch {α : Type u} (midpoint : α → α → α) (rangeSize : α → α → Nat)
    (hr₁ : ∀ a b, 2 ≤ rangeSize a b → rangeSize a (midpoint a b) < rangeSize a b)
    (hr₂ : ∀ a b, 2 ≤ rangeSize a b → rangeSize (midpoint a b) b < rangeSize a b)
    (f : α → Bool) (lo hi : α) : α :=
  match _ : rangeSize lo hi with
  | 0 => hi
  | 1 => if f lo then lo else hi
  | _ + 2 =>
    let mid := midpoint lo hi
    if f mid then
      have := hr₁ lo hi
      binarySearch midpoint rangeSize hr₁ hr₂ f lo mid
    else
      have := hr₂ lo hi
      binarySearch midpoint rangeSize hr₁ hr₂ f mid hi
termination_by rangeSize lo hi

theorem binarySearch_correct {α : Type u} [LE α] [LT α]
    (lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c)
    (lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c)
    (lt_irrefl : ∀ (a : α), ¬a < a)
    (not_le : ∀ {a b : α}, ¬a ≤ b ↔ b < a)
    (lt_or_le : ∀ (a b : α), a < b ∨ b ≤ a)
    (le_of_lt : ∀ {a b : α}, a < b → a ≤ b)
    (le_refl : ∀ {a : α}, a ≤ a)
    (le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c)

    {midpoint : α → α → α} {rangeSize : α → α → Nat}
    (hr₁ : ∀ a b, 2 ≤ rangeSize a b → rangeSize a (midpoint a b) < rangeSize a b)
    (hr₂ : ∀ a b, 2 ≤ rangeSize a b → rangeSize (midpoint a b) b < rangeSize a b)
    (hr₃ : ∀ a b, 2 ≤ rangeSize a b → a < midpoint a b)
    (hr₄ : ∀ a b, 2 ≤ rangeSize a b → midpoint a b < b)
    (hr₅ : ∀ a b, rangeSize a b = 0 → ∀ c, c < a ∨ b ≤ c)
    (hr₆ : ∀ a b, rangeSize a b = 1 → ∀ c, a ≤ c ∧ c < b ↔ c = a)
    (f : α → Bool) (hf : ∀ a, f a = true → ∀ b, a ≤ b → f b = true)
    (lo hi : α) (hlh : lo ≤ hi) :
    binarySearch midpoint rangeSize hr₁ hr₂ f lo hi ≤ hi ∧
    lo ≤ binarySearch midpoint rangeSize hr₁ hr₂ f lo hi ∧
    (∀ a, lo ≤ a → a < hi → (f a = true ↔ binarySearch midpoint rangeSize hr₁ hr₂ f lo hi ≤ a)) := by
  fun_induction binarySearch with
  | case1 lo hi h =>
    refine ⟨le_refl, hlh, fun a ha₁ ha₂ => ?_⟩
    obtain ha | ha := hr₅ _ _ h a
    · exact (lt_irrefl lo (lt_of_le_of_lt ha₁ ha)).elim
    · exact (lt_irrefl hi (lt_of_le_of_lt ha ha₂)).elim
  | case2 lo hi h₁ h₂ =>
    refine ⟨hlh, le_refl, fun a ha₁ ha₂ => ?_⟩
    obtain rfl := (hr₆ _ _ h₁ a).1 ⟨ha₁, ha₂⟩
    simp_all
  | case3 lo hi h₁ h₂ =>
    refine ⟨le_refl, hlh, fun a ha₁ ha₂ => ?_⟩
    obtain rfl := (hr₆ _ _ h₁ a).1 ⟨ha₁, ha₂⟩
    simp_all
  | case4 lo hi n hrs mid hmid _ ih =>
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (le_of_lt (hr₃ _ _ (by omega)))
    refine ⟨?_, ih₂, fun a ha₁ ha₂ => ?_⟩
    · exact le_of_lt (lt_of_le_of_lt ih₁ (hr₄ _ _ (by omega)))
    · obtain (hamid|hamid) := lt_or_le a mid
      · exact ih₃ _ ha₁ hamid
      · refine ⟨fun _ => le_trans ih₁ hamid, fun ih₃ => ?_⟩
        exact hf _ hmid _ hamid
  | case5 lo hi n hrs mid hmid _ ih =>
    obtain ⟨ih₁, ih₂, ih₃⟩ := ih (le_of_lt (hr₄ _ _ (by omega)))
    refine ⟨ih₁, ?_, fun a ha₁ ha₂ => ?_⟩
    · exact le_of_lt (lt_of_lt_of_le (hr₃ _ _ (by omega)) ih₂)
    · obtain (hmida|hmida) := lt_or_le a mid
      · classical
        rw [← Decidable.not_iff_not]
        simp only [not_le]
        refine ⟨fun _ => lt_of_lt_of_le hmida ih₂, fun ha hfa => ?_⟩
        exact hmid (hf _ hfa _ (le_of_lt hmida))
      · exact ih₃ _ hmida ha₂

section UInt64

def UInt64.midpoint (lo hi : UInt64) : UInt64 :=
  lo + (hi - lo) / 2

def UInt64.rangeSize (lo hi : UInt64) : Nat :=
  if lo ≤ hi then (hi - lo).toNat else 0

theorem UInt64.le_of_rangeSize_pos {lo hi : UInt64} (h : 0 < rangeSize lo hi) : lo ≤ hi := by
  grind [rangeSize]

theorem UInt64.rangeSize_eq_of_pos {lo hi : UInt64} (h : 0 < rangeSize lo hi) : rangeSize lo hi = (hi - lo).toNat := by
  grind [rangeSize]

theorem helper {lo hi : UInt64} (h : lo ≤ hi) (h : 2 ≤ hi - lo) : lo < (lo + (hi - lo) / 2) := by grind

theorem UInt64.rangeSize_midpoint_right (lo hi : UInt64) (h : 2 ≤ rangeSize lo hi) :
    rangeSize lo (midpoint lo hi) < rangeSize lo hi := by
  simp only [rangeSize, midpoint]
  rw [if_pos, if_pos, UInt64.add_comm, UInt64.add_sub_cancel, UInt64.toNat_div]
  all_goals grind [rangeSize]

theorem UInt64.rangeSize_midpoint_left (lo hi : UInt64) (h : 2 ≤ rangeSize lo hi) :
    rangeSize (midpoint lo hi) hi < rangeSize lo hi := by
  simp only [rangeSize, midpoint]
  rw [if_pos, if_pos]
  · rw [← UInt64.lt_iff_toNat_lt]
    rw [UInt64.rangeSize_eq_of_pos (by omega)] at h
    have : 2 ≤ hi - lo := by simpa [UInt64.le_iff_toNat_le]
    grind
  all_goals grind [rangeSize]

end UInt64
