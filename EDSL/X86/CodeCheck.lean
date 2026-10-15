/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.State

namespace EDSL.X86

/-- Check every exact executable byte, including its address and nonwrapping
extent. This is a code binding check, not a functional specification. -/
def checkCode (memory : Memory) (base : Word) (bytes : List Byte) : Bool :=
  decide (base.toNat + bytes.length ≤ 2^64) &&
    (List.range bytes.length).all fun offset =>
      match bytes[offset]? with
      | none => false
      | some byte => match fetchByte memory (base + BitVec.ofNat 64 offset) with
        | .error _ => false
        | .ok actual => decide (actual = byte)

theorem checkCode_sound (memory : Memory) (base : Word) (bytes : List Byte)
    (checked : checkCode memory base bytes = true) : CodeAt memory base bytes := by
  obtain ⟨bound, all⟩ := Bool.and_eq_true_iff.mp checked
  refine ⟨of_decide_eq_true bound, ?_⟩
  intro offset byte present
  have existsAt : bytes[offset]?.isSome = true := by simp [present]
  have offsetBound : offset < bytes.length := by simpa using existsAt
  have entry := List.all_eq_true.mp all offset (List.mem_range.mpr offsetBound)
  rw [present] at entry
  cases fetched : fetchByte memory (base + BitVec.ofNat 64 offset) with
  | error fault => simp [fetched] at entry
  | ok actual =>
    have same : actual = byte := of_decide_eq_true (by simpa only [fetched] using entry)
    cases same
    rfl

end EDSL.X86
