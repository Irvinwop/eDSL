/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordStore.Core
import EDSL.OS.Composition

namespace EDSL.OS.AddressSpace
open X86

-- Retain the historical private declaration as well as the public API.
private theorem memory_ext {left right : X86.Memory}
    (reads : left.read = right.read) (executes : left.executable = right.executable)
    (writes : left.writable = right.writable) : left = right := by
  cases left
  cases right
  cases reads
  cases executes
  cases writes
  rfl


/-- An actual store/RET binary implements a checked update of OS cells and
returns with the same exact state/count, under code and return-stack framing. -/
theorem store32_updates_space (space result : Space) (initial : State) (returnAddress : Word)
    (success : storeWord space (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32) = .ok result)
    (code : CodeAt (toMemory space) initial.rip Examples.Compiler.MemoryOps.storeBytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip
      Examples.Compiler.MemoryOps.storeBytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory space }
    Executes entry (storeFinalWithSpace entry result returnAddress) 2 ∧
    ¬ Diverges entry ∧
    ∀ final count, Executes entry final count →
      final = storeFinalWithSpace entry result returnAddress ∧ count = 2 := by
  obtain ⟨resultEq, allowed⟩ := storeWord_ok space result _ _ success
  have execution := Examples.Compiler.MemoryOps.store_correct
    { initial with memory := toMemory space } returnAddress code allowed
    codeDisjoint stackDisjoint stack returnValid
  have projects : toMemory result = X86.writeDWordUnchecked (toMemory space)
      (initial.registers .rdi) ((initial.registers .rsi).setWidth 32) := by
    rw [resultEq]
    exact writeWord_projects _ _ _ allowed
  have finalEq : Examples.Compiler.MemoryOps.storeFinal
      { initial with memory := toMemory space } returnAddress =
      storeFinalWithSpace { initial with memory := toMemory space } result returnAddress := by
    simp only [Examples.Compiler.MemoryOps.storeFinal, storeFinalWithSpace, projects]
  rw [finalEq] at execution
  exact execution

end EDSL.OS.AddressSpace
