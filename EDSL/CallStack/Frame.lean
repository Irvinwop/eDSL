/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Resources
import EDSL.OS.StackFrame.CPU

set_option warningAsError true

namespace EDSL.CallStack
open X86 OS

/-- Recover the machine-level memory contract from the same two coupled OS
worlds and the actual checked private-write history between them. -/
theorem memory_frame {frame : StackFrame.Descriptor} {before after : Borrowing.State}
    {initial final : State} (first : StackFrame.Current frame before initial)
    (last : StackFrame.Current frame after final)
    (preserved : StackFrame.Preservation frame before after) :
    (∀ query, ¬frame.region.Contains query → final.memory.read query = initial.memory.read query) ∧
      final.memory.executable = initial.memory.executable ∧
      final.memory.writable = initial.memory.writable := by
  rw [first.coupled, last.coupled]
  refine ⟨?_, ?_, ?_⟩
  · intro query outside
    simp only [AddressSpace.toMemory, preserved.outside query outside]
  · funext query
    have same := preserved.permissions query
    cases a : after.resources.space.cells query <;>
      cases b : before.resources.space.cells query <;>
      simp_all [AddressSpace.toMemory]
  · funext query
    have same := preserved.permissions query
    cases a : after.resources.space.cells query <;>
      cases b : before.resources.space.cells query <;>
      simp_all [AddressSpace.toMemory]

end EDSL.CallStack
