/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.FirstMatch
import Init.Data.List.Zip

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.FirstMatch

universe u v
variable {α : Type u} {β : Type v}

/-- A binary predicate uses the same relation on paired elements. -/
theorem MatchesAt.zip_iff {left : List α} {right : List β} {predicate : α → β → Bool}
    {index : Nat} :
    MatchesAt (left.zip right) (fun pair => predicate pair.1 pair.2) index ↔
      ∃ a b, left[index]? = some a ∧ right[index]? = some b ∧ predicate a b = true := by
  constructor
  · rintro ⟨⟨a, b⟩, present, hit⟩
    obtain ⟨presentLeft, presentRight⟩ := List.getElem?_zip_eq_some.mp present
    exact ⟨a, b, presentLeft, presentRight, hit⟩
  · rintro ⟨a, b, presentLeft, presentRight, hit⟩
    exact ⟨(a, b), List.getElem?_zip_eq_some.mpr ⟨presentLeft, presentRight⟩, hit⟩

/-- Zipping compares only the common extent; equal lengths must be supplied
when a client intends to compare two whole buffers. -/
theorem Result.zip_bound {left : List α} {right : List β} {predicate : α → β → Bool}
    {result : Nat}
    (first : Result (left.zip right) (fun pair => predicate pair.1 pair.2) result) :
    result ≤ min left.length right.length := by
  simpa using first.bound

/-- For equal extents the common bound is exactly the left buffer's length. -/
theorem Result.zip_bound_of_length_eq {left : List α} {right : List β}
    {predicate : α → β → Bool} {result : Nat} (sameLength : left.length = right.length)
    (first : Result (left.zip right) (fun pair => predicate pair.1 pair.2) result) :
    result ≤ left.length := by
  simpa [sameLength] using first.zip_bound

end EDSL.Grading.FirstMatch
