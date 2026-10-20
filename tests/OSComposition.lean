/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Composition
import EDSL.Examples.Compiler.MemoryWitness
import EDSL.Audit

namespace EDSL.Tests.OSComposition
open X86 OS.AddressSpace Examples.Compiler.MemoryOps

/-- Code, stack and data from the compiler witness, plus an unrelated mapping. -/
def space : Space where
  cells address :=
    if address = 73728 then some ⟨0x6e, readWrite⟩ else
    ((dataMemory 0x8b 0x07 0x11223344).read address).map fun byte =>
      ⟨byte, ⟨true, (dataMemory 0x8b 0x07 0x11223344).writable address,
        (dataMemory 0x8b 0x07 0x11223344).executable address⟩⟩

def region : Region := ⟨73728, 1⟩
def changed : Space := protectUnchecked space region inaccessible

theorem entry_code : CodeAt (toMemory space) 4096 loadBytes := by
  refine ⟨by decide, ?_⟩
  intro offset byte atOffset
  match offset with
  | 0 | 1 | 2 =>
    simp [loadBytes] at atOffset
    subst byte
    rfl
  | n + 3 => simp [loadBytes] at atOffset

theorem code_outside : region.Avoids 4096 loadBytes.length := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 := by
    change offset < 3 at bound
    omega
  rcases cases with rfl | rfl | rfl <;> decide

theorem data_outside : region.Avoids 65536 4 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> decide

theorem stack_outside : region.Avoids 32768 8 := by
  intro offset bound
  have cases : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
    offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def entry : State := { loadEntry 0x11223344 with memory := toMemory changed }

/-- Instantiate the cross-layer theorem with satisfiable OS and byte premises. -/
example : Executes entry (loadFinal entry 0x11223344 8192) 2 := by
  exact (load32_after_protect space changed region inaccessible (loadEntry 0x11223344)
    0x11223344 8192 (by rfl) entry_code (by rfl) (by rfl) (by decide)
    code_outside data_outside stack_outside).1

-- The caller observes a load result and a real modeled return after revocation
-- of a neighboring mapping, while revoking the data itself denies the call.
example : (run 2 entry).map (fun result =>
    (result.state.registers .rax, result.state.registers .rsp, result.state.rip)) =
      .ok (0x11223344, 32776, 8192) := by rfl

example : run 2 { entry with memory := toMemory (protectUnchecked space ⟨65536, 4⟩ inaccessible) } =
    .error (.inaccessibleData 65536) := by rfl

end EDSL.Tests.OSComposition

#audit_edsl
