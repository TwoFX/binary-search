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

theorem MyLinearOrder.le_or_lt [MyLinearOrder α] (a b : α) : a ≤ b ∨ b < a := by
  simp [Classical.or_iff_not_imp_left, MyLinearOrder.not_le]

theorem MyLinearOrder.le_refl [MyLinearOrder α] {a : α} : a ≤ a := by
  simp [le_iff_lt_or_eq]

theorem MyLinearOrder.not_lt [MyLinearOrder α] {a b : α} : ¬a < b ↔ b ≤ a := by
  grind [MyLinearOrder.not_le]

theorem MyLinearOrder.lt_irrefl [MyLinearOrder α] {a : α} : ¬a < a := by
  simp [MyLinearOrder.not_lt, MyLinearOrder.le_refl]

theorem MyLinearOrder.le_of_lt [MyLinearOrder α] {a b : α} : a < b → a ≤ b := by
  simp_all [le_iff_lt_or_eq]

theorem MyLinearOrder.le_trans [MyLinearOrder α] {a b c : α} : a ≤ b → b ≤ c → a ≤ c := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  rintro (hab|rfl) (hbc|rfl)
  · exact le_of_lt (lt_trans hab hbc)
  · exact le_of_lt hab
  · exact le_of_lt hbc
  · exact le_refl

theorem MyLinearOrder.lt_of_le_of_lt [MyLinearOrder α] {a b c : α} : a ≤ b → b < c → a < c := by
  rw [le_iff_lt_or_eq]
  rintro (hab|rfl) hbc
  · exact lt_trans hab hbc
  · exact hbc

theorem MyLinearOrder.lt_of_lt_of_le [MyLinearOrder α] {a b c : α} : a < b → b ≤ c → a < c := by
  rw [le_iff_lt_or_eq]
  rintro hab (hbc|rfl)
  · exact lt_trans hab hbc
  · exact hab

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

theorem binarySearch_eq_partialBinarySearch {α : Type u} [HasPartialBinarySearch α] (f : α → Bool) (lo hi : α) :
    binarySearch f lo hi = partialBinarySearch lo hi (fun a _ _ => f a) := by
  fun_induction binarySearch <;> grind [partialBinarySearch]

class HasLawfulBinarySearch (α : Type u) extends HasPartialBinarySearch α where
  of_checkRange_eq_singleton {lo hi : α} : checkRange lo hi = .singleton → ∀ c, lo ≤ c ∧ c < hi → c = lo

open HasLawfulBinarySearch

theorem partialBinarySearch_correct [HasLawfulBinarySearch α] (lo hi : α)
    (f : (a : α) → lo ≤ a → a < hi → Bool)
    (hf : ∀ a b, (h₁ : lo ≤ a) → (h₂ : a ≤ b) → (h₃ : b < hi) → f a h₁ (MyLinearOrder.lt_of_le_of_lt h₂ h₃) = true →
      f b (MyLinearOrder.le_trans h₁ h₂) h₃ = true) (hlh : lo ≤ hi) :
    partialBinarySearch lo hi f ≤ hi ∧
    lo ≤ partialBinarySearch lo hi f ∧
    (∀ a h₁ h₂, f a h₁ h₂ = true ↔ partialBinarySearch lo hi f ≤ a) := by
  fun_induction partialBinarySearch with
  | case1 lo hi f h =>
    refine ⟨MyLinearOrder.le_refl, hlh, ?_⟩
    rw [checkRange_eq_empty_iff] at h
    intro _ h₁ h₂
    exact absurd (MyLinearOrder.lt_of_le_of_lt (MyLinearOrder.le_trans h h₁) h₂) (MyLinearOrder.lt_irrefl)
  | case2 lo hi f h hflo =>
    refine ⟨hlh, MyLinearOrder.le_refl, fun a h₁ h₂ => ?_⟩
    simp_all [of_checkRange_eq_singleton h _ ⟨h₁, h₂⟩, MyLinearOrder.le_refl]
  | case3 lo hi f h hflo =>
    refine ⟨MyLinearOrder.le_refl, hlh, fun a h₁ h₂ => ?_⟩
    simp_all [of_checkRange_eq_singleton h _ ⟨h₁, h₂⟩, MyLinearOrder.not_le, MyLinearOrder.lt_of_le_of_lt h₁ h₂]
  | case4 lo hi f h mid hfmid _ ih =>
    replace ih := ih ?_ (le_midpoint h)
    · rcases ih with ⟨ih₁, ih₂, ih₃⟩
      refine ⟨MyLinearOrder.le_trans ih₁ (midpoint_le h), ih₂, fun a h₁ h₂ => ?_⟩
      obtain (hamid|hamid) := MyLinearOrder.le_or_lt mid a
      · simp [MyLinearOrder.le_trans ih₁ hamid, hf mid a (le_midpoint h) hamid h₂ hfmid]
      · exact ih₃ _ h₁ hamid
    · exact fun a b h₁ h₂ h₃ hfa => hf a b h₁ h₂ (MyLinearOrder.lt_trans h₃ (midpoint_lt h)) hfa
  | case5 lo hi f h mid hfmid _ ih =>
    replace ih := ih ?_ (midpoint_le h)
    · rcases ih with ⟨ih₁, ih₂, ih₃⟩
      refine ⟨ih₁, MyLinearOrder.le_trans (le_midpoint h) ih₂, fun a h₁ h₂ => ?_⟩
      obtain (hamid|hamid) := MyLinearOrder.le_or_lt mid a
      · exact ih₃ _ hamid h₂
      · refine iff_of_false (fun haf => hfmid ?_) (MyLinearOrder.not_le.2 ?_)
        · exact hf a mid h₁ (MyLinearOrder.le_of_lt hamid) _ haf
        · exact MyLinearOrder.lt_of_lt_of_le hamid ih₂
    · exact fun a b h₁ h₂ h₃ hfa => hf a b (MyLinearOrder.le_trans (le_midpoint h) h₁) h₂ h₃ hfa

theorem binarySearch_correct [HasLawfulBinarySearch α]
    (f : α → Bool)
    (hf : ∀ a, f a = true → ∀ b, a ≤ b → f b = true)
    (lo hi : α) (hlh : lo ≤ hi) :
    binarySearch f lo hi ≤ hi ∧
    lo ≤ binarySearch  f lo hi ∧
    (∀ a, lo ≤ a → a < hi → (f a = true ↔ binarySearch f lo hi ≤ a)) := by
  simp only [binarySearch_eq_partialBinarySearch]
  exact partialBinarySearch_correct lo hi (fun a _ _ => f a) (fun a b h₁ h₂ h₃ haf => hf _ haf _ h₂) hlh

theorem ite_eq_iff {p : Prop} [Decidable p] {a b c : α} :
    (if p then a else b) = c ↔ (p ∧ a = c) ∨ (¬ p ∧ b = c) := by
  split <;> simp_all
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

section USize

@[inline]
def USize.checkRange (lo hi : USize) : RangeCheck :=
  if hi ≤ lo then
    .empty
  else if hi - lo = 1 then
    .singleton
  else
    .large

@[inline]
def USize.midpoint (lo hi : USize) : USize :=
  lo + (hi - lo) / 2

def USize.rangeSize (lo hi : USize) : Nat :=
  if lo ≤ hi then (hi - lo).toNat else 0

theorem USize.helper {lo hi : USize} : 2 ≤ (hi - lo).toNat ↔ 2 ≤ hi - lo := by
  rw [USize.le_iff_toNat_le]
  grind

theorem USize.checkRange_eq_empty_iff {lo hi : USize} :
    checkRange lo hi = .empty ↔ hi ≤ lo := by
  grind [USize.checkRange]

theorem USize.checkRange_eq_large_iff {lo hi : USize} :
    checkRange lo hi = .large ↔ 2 ≤ rangeSize lo hi := by
  rw [checkRange, rangeSize]
  rw [ite_eq_iff]
  simp only [reduceCtorEq, and_false, USize.not_le, ite_eq_right_iff, imp_false, false_or]
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · rw [if_pos, helper]
    · sorry
    · apply USize.le_of_lt h₁
  · split
    · rw [helper]
      sorry
    · simp

theorem USize.le_of_rangeSize_pos {lo hi : USize} (h : 0 < rangeSize lo hi) : lo ≤ hi := by
  grind [rangeSize]

theorem USize.rangeSize_eq_of_pos {lo hi : USize} (h : 0 < rangeSize lo hi) : rangeSize lo hi = (hi - lo).toNat := by
  grind [rangeSize]

end USize
