/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.FirstMatch
import EDSL.Grading.ByteScan

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Grading.FirstMatch

/-- Byte equality is the only specialization needed for bounded NUL length. -/
theorem matchesAt_zero_iff {values : List X86.Byte} {index : Nat} :
    MatchesAt values (fun byte => byte == 0) index ↔ values[index]? = some 0 := by
  constructor
  · rintro ⟨byte, present, isZero⟩
    have zero : byte = 0 := by simpa using isZero
    simpa [zero] using present
  · intro zero
    exact ⟨0, zero, rfl⟩

/-- The accepted prefix API needs no change to consume the generic mathematics. -/
theorem zero_prefix_iff {values : List X86.Byte} {count : Nat} :
    Prefix values (fun byte => byte == 0) count ↔ ByteScan.NonzeroPrefix values count := by
  constructor
  · intro scanned
    exact ⟨scanned.bound, fun index before zero =>
      scanned.nonmatch index before (matchesAt_zero_iff.mpr zero)⟩
  · intro scanned
    exact ⟨scanned.1, fun index before hit =>
      scanned.2 index before (matchesAt_zero_iff.mp hit)⟩

/-- Sound in both directions, including exhaustion and the empty input. -/
theorem zero_result_iff {values : List X86.Byte} {result : Nat} :
    Result values (fun byte => byte == 0) result ↔ ByteScan.BoundedNulLength values result := by
  constructor
  · intro first
    exact ⟨first.bound, fun index before zero =>
      first.nonmatch index before (matchesAt_zero_iff.mpr zero),
      fun inside => matchesAt_zero_iff.mp (first.hit inside)⟩
  · intro first
    exact ⟨⟨first.bound, fun index before hit =>
      first.nonzero index before (matchesAt_zero_iff.mp hit)⟩,
      fun inside => matchesAt_zero_iff.mpr (first.zero inside)⟩

end EDSL.Grading.FirstMatch
