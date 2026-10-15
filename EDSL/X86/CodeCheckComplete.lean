/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CodeCheck

namespace EDSL.X86

/-- Every accessible executable byte in the nonwrapping code contract passes
the exact byte checker. -/
theorem checkCode_complete (memory : Memory) (base : Word) (bytes : List Byte)
    (code : CodeAt memory base bytes) : checkCode memory base bytes = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by simpa only [decide_eq_true_eq] using code.1, ?_⟩
  apply List.all_eq_true.mpr
  intro offset member
  have existsAt : bytes[offset]?.isSome = true := by
    simpa using List.mem_range.mp member
  cases present : bytes[offset]? with
  | none => simp [present] at existsAt
  | some byte => simp [code.2 offset byte present]

end EDSL.X86
