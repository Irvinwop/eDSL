/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.CPUFixture
import EDSL.Audit

set_option warningAsError true
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

namespace EDSL.Tests.StackFrameCPU
open X86 OS OS.AddressSpace OS.StackFrame

example (choices : CallReturn.Choices) :
    (CallReturn.run choices 3 start).map
      (fun result => (result.state.rip, result.state.registers .rsp, result.instructions, result.reads)) =
      .ok (0xffff800000004444,65552,3,[⟨.stack,65536,8⟩,⟨.stack,65544,8⟩]) := by
  have actual := CallReturn.runFrom_complete (complete choices).machine (by decide : 3 ≤ 3)
  exact congrArg (Except.map _) actual

-- The caller and code loans survive the CPU writes; no private read introduces
-- a loan. The dirty return word remains in the frame after both RETs.
example (choices : CallReturn.Choices) :
    Current frame calledWorld finished ∧ calledWorld.loans = seed.loans ∧
    calledWorld.nextLoan = seed.nextLoan ∧
    readWord finished.memory 65536 = .ok 4101 ∧
    readWord finished.memory 65544 = .ok 0xffff800000004444 :=
  ⟨(complete choices).current startCurrent, (complete choices).preserves.loans,
    (complete choices).preserves.nextLoan, rfl, rfl⟩

example (choices : CallReturn.Choices) (query : Word) (outside : ¬frame.region.Contains query) :
    calledWorld.resources.space.cells query = seed.resources.space.cells query :=
  (complete choices).preserves.outside query outside

-- A successful owner read at one slot does not freeze the other slot. This
-- actual follow-up mutation would fail if a POP/RET bridge created a loan.
example : Borrowing.loadOwnedWord64 calledWorld frame.owner frame.ticket 65536 = .ok 4101 ∧
    ∃ after, Borrowing.mutate calledWorld
      (.store64 frame.owner frame.ticket 65528 0xfedcba9876543210) = .ok (after, none) := by
  refine ⟨rfl, ?_⟩
  exact current_store64_enabled ((callStep false).current startCurrent) (by decide) _

-- PUSH RSP must save the old RSP, and POP RSP must end at that saved word,
-- rather than old-RSP+8. These independent ISA expectations also pass through
-- the same full-memory owner bridge despite not belonging to the code window.
def pushedWorld : Shared := evolve seed (.store64 frame.owner frame.ticket 65536 65544)
def pushed : X86.State := CallReturn.pushState start false (toMemory pushedWorld.resources.space)
def popped : X86.State := CallReturn.popState pushed .rsp false 65544

example : ∃ evolved, Current frame evolved pushed ∧
    Borrowing.loadOwnedWord64 evolved frame.owner frame.ticket 65536 = .ok 65544 := by
  have stored := (Borrowing.store64_effect (show Borrowing.mutate seed
    (.store64 frame.owner frame.ticket 65536 65544) = .ok (pushedWorld, none) by rfl)).machine
  have actual : CallReturn.execute start (.push64 .rsp false) false = .ok ⟨.next pushed, []⟩ :=
    CallReturn.execute_push start .rsp false false _ stored
  obtain ⟨evolved, success, current, _, _⟩ := CPU.push_current startCurrent (source := .rsp)
    (prefixed := false) (af := false) (by decide) actual
  exact ⟨evolved, current, Borrowing.store64_owned_readback success⟩

example : popped.registers .rsp = 65544 ∧ readWord popped.memory 65536 = .ok 65544 ∧
    Current frame pushedWorld popped := by
  have pushedCurrent : Current frame pushedWorld pushed :=
    ⟨(contract_store64 ready (show Borrowing.mutate seed
      (.store64 frame.owner frame.ticket 65536 65544) = .ok (pushedWorld, none) by rfl)).1, rfl⟩
  exact ⟨rfl, rfl, (CPU.pop_current pushedCurrent (destination := .rsp) (prefixed := false)
    (af := false) (by decide) (show CallReturn.execute pushed (.pop64 .rsp false) false =
      .ok ⟨.next popped, [⟨.stack,65536,8⟩]⟩ by rfl)).1⟩

-- Neighboring readable RAM outside the complete private interval cannot be
-- used for a private RET receipt, even if a raw stack read accepts that word.
example : ¬Slot frame 65544 ∧ ¬ReadAllowed frame seed ⟨.stack,65540,8⟩ := by
  refine ⟨by decide, ?_⟩
  intro allowed
  cases allowed with
  | original original => exact (by decide : (65540 : Word) ≠ frame.call.stack) original.2.1
  | privateSlot _ _ present => exact (by decide : ¬Slot frame 65540) present.fits

end EDSL.Tests.StackFrameCPU

#print axioms EDSL.OS.StackFrame.CPU.call_enabled
#print axioms EDSL.OS.StackFrame.CPU.push_enabled
#print axioms EDSL.OS.StackFrame.CPU.private_ret_step
#print axioms EDSL.OS.StackFrame.CPU.original_ret_step
#print axioms EDSL.OS.StackFrame.CPU.Execution.machine
#print axioms EDSL.OS.StackFrame.CPU.Execution.current
#print axioms EDSL.OS.StackFrame.CPU.Execution.preserves
#print axioms EDSL.Tests.StackFrameCPU.complete
#audit_edsl
