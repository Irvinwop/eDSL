/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.AtomicExchange.Core
import EDSL.OS.Borrowing.Read
import EDSL.Examples.Compiler.Exchange

namespace EDSL.OS.AtomicExchange
open X86 AddressSpace

/-- The checked resource exchange is implemented by the exact compiler routine
with one atomic event and an exact three-instruction execution. Code and stack
framing, coherent ordinary RAM and physical architectural conformance remain
explicit environmental obligations; no managed-worker scheduling is claimed. -/
theorem exchange32_updates_space (state : Borrowing.State) (owner : Nat)
    (ticket : Ownership.Ticket) (result : Borrowing.State × BitVec 32)
    (initial : X86.State) (returnAddress : Word)
    (success : exchangeWord state owner ticket (initial.registers .rdi)
      ((initial.registers .rsi).setWidth 32) = .ok result)
    (code : CodeAt (toMemory state.resources.space) initial.rip Examples.Compiler.Exchange.bytes)
    (codeDisjoint : DWordDisjoint (initial.registers .rdi) initial.rip Examples.Compiler.Exchange.bytes.length)
    (stackDisjoint : DWordDisjoint (initial.registers .rdi) (initial.registers .rsp) 8)
    (stack : readWord (toMemory state.resources.space) (initial.registers .rsp) = .ok returnAddress)
    (returnValid : canonical returnAddress = true) :
    let entry := { initial with memory := toMemory state.resources.space }
    let final := finalWithSpace entry result.1.resources.space result.2 returnAddress
    AtomicExecutes entry final 3 [Examples.Compiler.Exchange.event entry result.2] ∧
    Executes entry final 3 ∧ ¬ Diverges entry ∧
    ∀ other count, Executes entry other count → other = final ∧ count = 3 := by
  have transition := exchangeWord_sound _ _ _ _ _ _ success
  have execution := Examples.Compiler.Exchange.correct
    { initial with memory := toMemory state.resources.space } result.2 returnAddress code
    transition.1 transition.2.1 transition.2.2.1 codeDisjoint stackDisjoint stack returnValid
  have finalEq : Examples.Compiler.Exchange.finalState
      { initial with memory := toMemory state.resources.space } result.2 returnAddress =
      finalWithSpace { initial with memory := toMemory state.resources.space }
        result.1.resources.space result.2 returnAddress := by
    simp only [Examples.Compiler.Exchange.finalState, finalWithSpace, transition.2.2.2]
  rw [finalEq] at execution
  exact execution

end EDSL.OS.AtomicExchange
