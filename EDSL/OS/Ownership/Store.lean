/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Ownership.Store.Core
import EDSL.OS.WordStore

namespace EDSL.OS.Ownership
open X86 AddressSpace

/-- The authority gate justifies this modeled store; the exact machine bytes
implement its OS-cell update. Hardware does not inspect ticket/owner fields.
The ordinary code/stack framing premises remain explicit. -/
theorem owned_store32_correct (world : World) (owner : Nat) (ticket : Ticket)
    (result : World) (initial : State) (returnAddress : Word)
    (success : storeWord world owner ticket (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32) = .ok result)
    (code : CodeAt (toMemory world.space) initial.rip Examples.Compiler.MemoryOps.storeBytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.MemoryOps.storeBytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory world.space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory world.space }
    Executes entry (storeFinalWithSpace entry result.space returnAddress) 2 ∧
    ¬ Diverges entry ∧ ∀ final count, Executes entry final count →
      final = storeFinalWithSpace entry result.space returnAddress ∧ count = 2 := by
  obtain ⟨_, space, _, _, stored, resultEq⟩ := storeWord_ok _ _ _ _ _ _ success
  subst result
  exact store32_updates_space world.space space initial returnAddress stored code codeDisjoint
    stackDisjoint stack returnValid

end EDSL.OS.Ownership
