/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Composition.Core
import EDSL.Examples.Compiler.MemoryOps

namespace EDSL.OS.AddressSpace
open X86

/-- A successful abstract protection change disjoint from this binary's code,
data and return stack preserves its admitted-entry contract and exact result.
This composes two models; it does not verify a Linux syscall implementation. -/
theorem load32_after_protect (space result : Space) (region : Region)
    (permissions : Permissions) (initial : State) (value : BitVec 32) (returnAddress : Word)
    (success : protect space region permissions = .ok result)
    (code : CodeAt (toMemory space) initial.rip Examples.Compiler.MemoryOps.loadBytes)
    (data : loadDWord (toMemory space) (initial.registers .rdi) = .ok value)
    (stack : readWord (toMemory space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true)
    (codeOutside : region.Avoids initial.rip Examples.Compiler.MemoryOps.loadBytes.length)
    (dataOutside : region.Avoids (initial.registers .rdi) 4)
    (stackOutside : region.Avoids (initial.registers .rsp) 8) :
    let entry := { initial with memory := toMemory result }
    Executes entry (Examples.Compiler.MemoryOps.loadFinal entry value returnAddress) 2 ∧
    ¬ Diverges entry ∧
    ∀ final count, Executes entry final count →
      final = Examples.Compiler.MemoryOps.loadFinal entry value returnAddress ∧ count = 2 := by
  have updated := (protect_ok space result region permissions success).1
  subst result
  apply Examples.Compiler.MemoryOps.load_correct
  · exact agrees_code _ _ _ _ (protect_agrees _ _ _ _ _ codeOutside) code
  · exact (loadDWord_congr _ _ _
      (agrees_read _ _ _ _ (protect_agrees _ _ _ _ _ dataOutside))).trans data
  · exact (readWord_congr _ _ _
      (agrees_read _ _ _ _ (protect_agrees _ _ _ _ _ stackOutside))).trans stack
  · exact returnValid

end EDSL.OS.AddressSpace
