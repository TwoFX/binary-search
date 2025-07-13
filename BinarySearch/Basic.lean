import Std.Tactic.BVDecide

inductive RangeCheck where
  | empty
  | singleton
  | large

class HasBinarySearch (α : Type u) where
  checkRange : α → α → RangeCheck
  rangeSize : α → α → Nat
  midpoint : α → α → α
  rangeSize_midpoint_right (lo hi : α) : checkRange lo hi = .large → rangeSize lo (midpoint lo hi) < rangeSize lo hi
  rangeSize_midpoint_left (lo hi : α) : checkRange lo hi = .large → rangeSize (midpoint lo hi) hi < rangeSize lo hi

open HasBinarySearch

@[specialize]
def binarySearch {α : Type u} [HasBinarySearch α] (f : α → Bool) (lo hi : α) : α :=
  match h : checkRange lo hi with
  | .empty => hi
  | .singleton => if f lo then lo else hi
  | .large =>
    let mid := midpoint lo hi
    if f mid then
      have := rangeSize_midpoint_right lo hi h
      binarySearch f lo mid
    else
      have := rangeSize_midpoint_left lo hi h
      binarySearch f mid hi
termination_by rangeSize lo hi

class MyLinearOrder (α : Type u) extends LE α, LT α where
  not_le {a b : α} : ¬a ≤ b ↔ b < a
  le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b
  lt_trans {a b c : α} : a < b → b < c → a < c

theorem MyLinearOrder.le_or_lt [MyLinearOrder α] {a b : α} : a ≤ b ∨ b < a := by
  simp [Classical.or_iff_not_imp_left, MyLinearOrder.not_le]

theorem MyLinearOrder.le_refl [MyLinearOrder α] {a : α} : a ≤ a := by
  simp [le_iff_lt_or_eq]

theorem MyLinearOrder.le_of_lt [MyLinearOrder α] {a b : α} : a < b → a ≤ b := by
  simp_all [le_iff_lt_or_eq]

theorem MyLinearOrder.le_trans [MyLinearOrder α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  rintro (hab|rfl) (hbc|rfl)
  · exact le_of_lt (lt_trans hab hbc)
  · exact le_of_lt hab
  · exact le_of_lt hbc
  · exact le_refl

class HasPartialBinarySearch (α : Type u) extends HasBinarySearch α, MyLinearOrder α where
  checkRange_eq_empty_iff {lo hi : α} : checkRange lo hi = .empty ↔ hi ≤ lo
  lt_midpoint {lo hi : α} : checkRange lo hi = .large → lo < midpoint lo hi
  midpoint_lt {lo hi : α} : checkRange lo hi = .large → midpoint lo hi < hi

theorem HasPartialBinarySearch.le_midpoint {α : Type u} [HasPartialBinarySearch α] {lo hi : α} :
    checkRange lo hi = .large → lo ≤ midpoint lo hi :=
  fun h => MyLinearOrder.le_of_lt (lt_midpoint h)

theorem HasPartialBinarySearch.midpoint_le {α : Type u} [HasPartialBinarySearch α] {lo hi : α} :
    checkRange lo hi = .large → midpoint lo hi ≤ hi :=
  fun h => MyLinearOrder.le_of_lt (midpoint_lt h)

open HasPartialBinarySearch

def partialBinarySearch {α : Type u} [HasPartialBinarySearch α] (lo hi : α) (f : (a : α) → lo ≤ a → a < hi → Bool) : α :=
  match h : checkRange lo hi with
  | .empty => hi
  | .singleton => if f lo MyLinearOrder.le_refl (by simp [← MyLinearOrder.not_le, ← checkRange_eq_empty_iff, h]) then lo else hi
  | .large =>
    let mid := HasBinarySearch.midpoint lo hi
    if f mid (le_midpoint h) (midpoint_lt h) then
      have := HasBinarySearch.rangeSize_midpoint_right lo hi h
      partialBinarySearch lo mid (fun a h₁ h₂ => f a h₁ (MyLinearOrder.lt_trans h₂ (midpoint_lt h)))
    else
      have := HasBinarySearch.rangeSize_midpoint_left lo hi h
      partialBinarySearch mid hi (fun a h₁ h₂ => f a (MyLinearOrder.le_trans (le_midpoint h) h₁) h₂)
termination_by rangeSize lo hi

/- theorem binarySearch_correct {α : Type u} [LE α] [LT α]
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
 -/
section UInt64

@[inline]
def UInt64.checkRange (lo hi : UInt64) : RangeCheck :=
  if hi ≤ lo then
    .empty
  else if hi - lo = 1 then
    .singleton
  else
    .large

@[inline]
def UInt64.midpoint (lo hi : UInt64) : UInt64 :=
  lo + (hi - lo) / 2

def UInt64.rangeSize (lo hi : UInt64) : Nat :=
  if lo ≤ hi then (hi - lo).toNat else 0

theorem ite_eq_iff {p : Prop} [Decidable p] {a b c : α} :
    (if p then a else b) = c ↔ (p ∧ a = c) ∨ (¬ p ∧ b = c) := by
  split <;> simp_all

theorem helper {lo hi : UInt64} : 2 ≤ (hi - lo).toNat ↔ 2 ≤ hi - lo := by
  rw [UInt64.le_iff_toNat_le]
  grind

theorem UInt64.checkRange_eq_empty_iff {lo hi : UInt64} :
    checkRange lo hi = .empty ↔ hi ≤ lo := by
  grind [UInt64.checkRange]

theorem UInt64.checkRange_eq_large_iff {lo hi : UInt64} :
    checkRange lo hi = .large ↔ 2 ≤ rangeSize lo hi := by
  rw [checkRange, rangeSize]
  rw [ite_eq_iff]
  simp only [reduceCtorEq, and_false, UInt64.not_le, ite_eq_right_iff, imp_false, false_or]
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · rw [if_pos (by grind), helper]
    grind
  · split
    · rw [helper]
      grind
    · simp

theorem UInt64.le_of_rangeSize_pos {lo hi : UInt64} (h : 0 < rangeSize lo hi) : lo ≤ hi := by
  grind [rangeSize]

theorem UInt64.rangeSize_eq_of_pos {lo hi : UInt64} (h : 0 < rangeSize lo hi) : rangeSize lo hi = (hi - lo).toNat := by
  grind [rangeSize]

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

theorem UInt64.lt_midpoint {lo hi : UInt64} (h : 2 ≤ rangeSize lo hi) : lo < UInt64.midpoint lo hi := by
  simp only [midpoint]
  have := UInt64.le_of_rangeSize_pos (lo := lo) (hi := hi) (by grind)
  rw [UInt64.rangeSize_eq_of_pos (by grind), helper] at h
  grind

theorem UInt64.midpoint_lt {lo hi : UInt64} (h : 2 ≤ rangeSize lo hi) : UInt64.midpoint lo hi < hi := by
  simp only [midpoint]
  have := UInt64.le_of_rangeSize_pos (lo := lo) (hi := hi) (by grind)
  rw [UInt64.rangeSize_eq_of_pos (by grind), helper] at h
  grind

-- Probably `range_size_midpoint_(right_left)` follow from `lt_midpoint`/`midpoint_lt` in some general setting

instance : HasBinarySearch UInt64 where
  checkRange := UInt64.checkRange
  rangeSize := UInt64.rangeSize
  midpoint := UInt64.midpoint
  rangeSize_midpoint_right := by
    simp only [UInt64.checkRange_eq_large_iff]
    apply UInt64.rangeSize_midpoint_right
  rangeSize_midpoint_left := by
    simp only [UInt64.checkRange_eq_large_iff]
    apply UInt64.rangeSize_midpoint_left

@[inline, specialize]
def UInt64.binarySearch (f : UInt64 → Bool) (lo hi : UInt64) : UInt64 :=
  _root_.binarySearch f lo hi

set_option trace.compiler.ir.result true in
def sqrt (a : UInt64) : UInt64 :=
  UInt64.binarySearch (fun b => b * b ≥ a) 0 a

instance : MyLinearOrder UInt64 where
  not_le := UInt64.not_le
  le_iff_lt_or_eq := UInt64.le_iff_lt_or_eq
  lt_trans := UInt64.lt_trans

instance : HasPartialBinarySearch UInt64 where
  checkRange_eq_empty_iff := UInt64.checkRange_eq_empty_iff
  lt_midpoint := by
    simp only [checkRange, midpoint, UInt64.checkRange_eq_large_iff]
    apply UInt64.lt_midpoint
  midpoint_lt := by
    simp only [checkRange, midpoint, UInt64.checkRange_eq_large_iff]
    apply UInt64.midpoint_lt


end UInt64
