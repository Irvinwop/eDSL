/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.FirstMatchByteScan
import EDSL.Grading.FirstMatchPairs

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.FirstMatch.Consumers

universe u v
variable {α : Type u} {β : Type v}

/-- Searching after a rejected segment adds exactly that segment's length. -/
theorem skip_nonmatching {front tail : List α} {predicate : α → Bool} {result : Nat}
    (rejected : ∀ value ∈ front, predicate value = false)
    (first : Result tail predicate result) :
    Result (front ++ tail) predicate (front.length + result) := by
  have exhausted := List.findIdx_eq_length.mpr rejected
  rw [Result.iff_findIdx, List.findIdx_append, exhausted]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [← Result.iff_findIdx.mp first]
  exact Nat.add_comm _ _

/-- An arbitrary suffix, including more matches, cannot change an earlier hit. -/
theorem append_after_hit {front : List α} {predicate : α → Bool} {result : Nat}
    (first : Result front predicate result) (inside : result < front.length)
    (suffix : List α) : Result (front ++ suffix) predicate result := by
  rw [Result.iff_findIdx, List.findIdx_append, ← Result.iff_findIdx.mp first]
  simp [inside]

/-- Representation changes preserve search when the predicate is transported. -/
theorem map_iff (values : List α) (encode : α → β) (predicate : β → Bool) (result : Nat) :
    Result (values.map encode) predicate result ↔ Result values (predicate ∘ encode) result := by
  rw [Result.iff_findIdx, Result.iff_findIdx, List.findIdx_map]

/-- A symbolic sentinel theorem shared by NUL, needle and linear searches. -/
theorem prefix_then_match {front suffix : List α} {predicate : α → Bool} {value : α}
    (rejected : ∀ earlier ∈ front, predicate earlier = false) (hit : predicate value = true) :
    Result (front ++ value :: suffix) predicate front.length := by
  have atHead : Result (value :: suffix) predicate 0 :=
    (Prefix.start _ _).finish_hit ⟨value, rfl, hit⟩
  simpa using skip_nonmatching rejected atHead

/-- Lawful equality suffices for memchr-style or linear search in any element type. -/
theorem needle_at_sentinel [BEq α] [LawfulBEq α] {front suffix : List α} {needle : α}
    (absent : needle ∉ front) :
    Result (front ++ needle :: suffix) (fun value => value == needle) front.length := by
  apply prefix_then_match
  · intro value member
    have different : value ≠ needle := by
      intro same
      exact absent (same ▸ member)
    simpa using different
  · simp

/-- The existing NUL contract follows from the shared sentinel theorem. -/
theorem boundedNulLength_at_sentinel {front suffix : List X86.Byte}
    (nonzero : ∀ byte ∈ front, byte ≠ 0) :
    ByteScan.BoundedNulLength (front ++ 0 :: suffix) front.length := by
  apply zero_result_iff.mp
  apply prefix_then_match
  · intro byte member
    simpa using nonzero byte member
  · rfl

/-- Exhausting equal-length paired buffers under inequality means actual list equality. -/
theorem paired_exhaustion_iff_equal [BEq α] [LawfulBEq α] {left right : List α}
    (sameLength : left.length = right.length) :
    Result (left.zip right) (fun pair => pair.1 != pair.2) left.length ↔ left = right := by
  constructor
  · intro first
    apply List.ext_getElem?
    intro index
    by_cases inside : index < left.length
    · have insideRight : index < right.length := by omega
      have equal : left[index] = right[index] := by
        apply beq_iff_eq.mp
        apply Bool.eq_true_of_ne_false
        intro different
        have hit : MatchesAt (left.zip right) (fun pair => pair.1 != pair.2) index := by
          apply MatchesAt.zip_iff.mpr
          exact ⟨left[index], right[index], List.getElem?_eq_getElem inside,
            List.getElem?_eq_getElem insideRight, by
              change (!(left[index] == right[index])) = true
              rw [different]
              rfl⟩
        exact first.nonmatch index inside hit
      rw [List.getElem?_eq_getElem inside, List.getElem?_eq_getElem insideRight, equal]
    · have outsideRight : ¬ index < right.length := by omega
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · rintro rfl
    have lengthZip : (left.zip left).length = left.length := by simp
    rw [← lengthZip, Result.at_bound_iff]
    intro pair member
    obtain ⟨index, present⟩ := List.mem_iff_getElem?.mp member
    have components := List.getElem?_zip_eq_some.mp present
    have equal : pair.1 = pair.2 := Option.some.inj (components.1.symm.trans components.2)
    simp [equal]

end EDSL.Grading.FirstMatch.Consumers
