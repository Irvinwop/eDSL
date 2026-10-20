/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import Init.Data.List.Find
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.FirstMatch

universe u
variable {α : Type u}

/-- A present element satisfying the predicate; out-of-range indices never match. -/
def MatchesAt (values : List α) (predicate : α → Bool) (index : Nat) : Prop :=
  ∃ value, values[index]? = some value ∧ predicate value = true

theorem MatchesAt.bound {values : List α} {predicate : α → Bool} {index : Nat}
    (hit : MatchesAt values predicate index) : index < values.length := by
  obtain ⟨value, present, _⟩ := hit
  exact (List.getElem_of_getElem? present).1

/-- Exactly the inspected prefix contains no match. No execution model is assumed. -/
structure Prefix (values : List α) (predicate : α → Bool) (count : Nat) : Prop where
  bound : count ≤ values.length
  nonmatch : ∀ index, index < count → ¬ MatchesAt values predicate index

/-- The earliest matching index, or the list length when there is no match. -/
structure Result (values : List α) (predicate : α → Bool) (result : Nat) : Prop
    extends Prefix values predicate result where
  hit : result < values.length → MatchesAt values predicate result

theorem Prefix.start (values : List α) (predicate : α → Bool) : Prefix values predicate 0 :=
  ⟨Nat.zero_le _, by omega⟩

theorem Prefix.advance {values : List α} {predicate : α → Bool} {count : Nat} {value : α}
    (scanned : Prefix values predicate count) (present : values[count]? = some value)
    (miss : predicate value = false) : Prefix values predicate (count + 1) := by
  have inside := (List.getElem_of_getElem? present).1
  refine ⟨by omega, ?_⟩
  intro index before
  by_cases earlier : index < count
  · exact scanned.nonmatch index earlier
  · have same : index = count := by omega
    subst index
    rintro ⟨other, observed, accepted⟩
    have equal : other = value := Option.some.inj (observed.symm.trans present)
    subst other
    exact Bool.false_ne_true (miss.symm.trans accepted)

theorem Prefix.finish_hit {values : List α} {predicate : α → Bool} {count : Nat}
    (scanned : Prefix values predicate count) (hit : MatchesAt values predicate count) :
    Result values predicate count := ⟨scanned, fun _ => hit⟩

theorem Prefix.finish_bound {values : List α} {predicate : α → Bool} {count : Nat}
    (scanned : Prefix values predicate count) (done : count = values.length) :
    Result values predicate count :=
  ⟨scanned, fun inside => False.elim (Nat.lt_irrefl _ (done ▸ inside))⟩

theorem Result.unique {values : List α} {predicate : α → Bool} {a b : Nat}
    (first : Result values predicate a) (second : Result values predicate b) : a = b := by
  by_cases earlier : a < b
  · exact False.elim (second.nonmatch a earlier
      (first.hit (Nat.lt_of_lt_of_le earlier second.bound)))
  · by_cases later : b < a
    · exact False.elim (first.nonmatch b later
        (second.hit (Nat.lt_of_lt_of_le later first.bound)))
    · omega

/-- Explicit Boolean cases construct a canonical witness for the relation. -/
theorem Result.findIdx (values : List α) (predicate : α → Bool) :
    Result values predicate (values.findIdx predicate) := by
  induction values with
  | nil =>
    exact ⟨Prefix.start _ _, fun inside => False.elim (Nat.not_lt_zero _ inside)⟩
  | cons value tail induction =>
    cases test : predicate value with
    | true =>
      have atHead : Result (value :: tail) predicate 0 :=
        (Prefix.start _ _).finish_hit ⟨value, rfl, test⟩
      simpa [List.findIdx_cons, test] using atHead
    | false =>
      simp only [List.findIdx_cons, test, Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨by simpa using Nat.succ_le_succ induction.bound, ?_⟩, ?_⟩
      · intro index before
        cases index with
        | zero => simp [MatchesAt, test]
        | succ index =>
          simpa only [MatchesAt, List.getElem?_cons_succ] using
            induction.nonmatch index (by omega)
      · intro inside
        have bound : tail.findIdx predicate < tail.length := by simpa using inside
        simpa only [MatchesAt, List.getElem?_cons_succ] using induction.hit bound

theorem Result.exists (values : List α) (predicate : α → Bool) :
    ∃ result, Result values predicate result :=
  ⟨values.findIdx predicate, Result.findIdx values predicate⟩

theorem Result.iff_findIdx {values : List α} {predicate : α → Bool} {result : Nat} :
    Result values predicate result ↔ result = values.findIdx predicate := by
  constructor
  · intro first
    exact first.unique (Result.findIdx values predicate)
  · rintro rfl
    exact Result.findIdx values predicate

theorem Result.nil_iff (predicate : α → Bool) (result : Nat) :
    Result [] predicate result ↔ result = 0 := by
  simp [Result.iff_findIdx]

/-- Exhaustion is equivalent to rejection of every element, including the empty list. -/
theorem Result.at_bound_iff (values : List α) (predicate : α → Bool) :
    Result values predicate values.length ↔ ∀ value ∈ values, predicate value = false := by
  rw [Result.iff_findIdx, eq_comm, List.findIdx_eq_length]

theorem Result.eq_length_iff {values : List α} {predicate : α → Bool} {result : Nat}
    (first : Result values predicate result) :
    result = values.length ↔ ∀ value ∈ values, predicate value = false := by
  constructor
  · rintro rfl
    exact (Result.at_bound_iff values predicate).mp first
  · intro noMatch
    exact first.unique ((Result.at_bound_iff values predicate).mpr noMatch)

end EDSL.Grading.FirstMatch
