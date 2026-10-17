/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.ArrayResources
import EDSL.X86.Sequential.Return

set_option warningAsError true

namespace EDSL.OS.CallResources
open EDSL.X86 EDSL.X86.Sequential

abbrev Shared := Borrowing.State

/-- Immutable handles for an ordinary call with no mutable DATA operand.
The current world remains a separate argument; no target allocation or ticket
is required for a pure register computation. -/
structure Call where
  worker : Nat
  code : Word
  stack : Word
  returnAddress : Word
  bytes : List Byte
  codeLoan : Nat
  stackLoan : Nat

/-- Current code and original caller-slot resources. Successful future
execution is not an admission premise. CPU features, ordinary RET without CET,
and absence of asynchronous interference belong to the target assumptions. -/
structure Contract (call : Call) (shared : Shared) : Prop where
  wellFormed : Borrowing.WellFormed shared
  codeLoan : Threads.HasLoan shared call.worker call.codeLoan ⟨call.code, call.bytes.length⟩
  stackLoan : Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack, 8⟩
  code : CodeAt (AddressSpace.toMemory shared.resources.space) call.code call.bytes
  stack : readWord (AddressSpace.toMemory shared.resources.space) call.stack = .ok call.returnAddress
  returnCanonical : canonical call.returnAddress = true
  stackBound : call.stack.toNat + 8 < 2^64
  postStackCanonical : canonical (call.stack + 8) = true

structure Current (call : Call) (shared : Shared) (machine : State) : Prop where
  contract : Contract call shared
  coupled : machine.memory = AddressSpace.toMemory shared.resources.space

/-- A retained original slot is independent of the machine's current RSP.
This lemma grants no read permission at a changed stack pointer. -/
theorem Current.sameMemory {call : Call} {shared : Shared} {before after : State}
    (current : Current call shared before) (memory : after.memory = before.memory) :
    Current call shared after := ⟨current.contract, memory.trans current.coupled⟩

def ReadAllowed (call : Call) (shared : Shared) (read : Read) : Prop :=
  read.kind = .stack ∧ read.address = call.stack ∧ read.bytes = 8 ∧
    ArrayResources.ReadPermission shared call.worker read

theorem stackRead_permission {call : Call} {shared : Shared}
    (contract : Contract call shared) : ReadAllowed call shared ⟨.stack, call.stack, 8⟩ := by
  obtain ⟨loan, live, borrower, sameRegion⟩ := contract.stackLoan
  refine ⟨rfl, rfl, rfl, call.stackLoan, loan, ?_, ?_⟩
  · simp [Borrowing.authorize, live, borrower]
  · rw [← sameRegion]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Actual CMOV success is derived from decoding. The same complete OS world
survives, including permissions, allocation owner/epoch metadata and all loans. -/
theorem current_cmovReg64_step {call : Call} {shared : Shared} {before : State}
    {condition : Condition} {destination source : Register}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.cmovReg64 condition destination source)) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧ Current call shared after ∧
      after.registers destination =
        (if condition.holds before.flags then before.registers source else before.registers destination) ∧
      (∀ register, register ≠ destination → after.registers register = before.registers register) ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧ after.rip = before.rip + 4 := by
  obtain ⟨after, executed, assigned, other, memory, flags, pc⟩ :=
    execute_cmovReg64_context before condition destination source af
  refine ⟨after, ?_, current.sameMemory memory, assigned, other, memory, flags, pc⟩
  rw [step_eq_execute af decoded]
  exact executed

def returnAfter (before : State) (returnAddress : Word) : State :=
  { before.writeRegister .rsp (before.registers .rsp + 8) with rip := returnAddress }

/-- The actual RSP must bind to the original complete caller slot. Its present
eight bytes derive RET success, authorized operand reading and unchanged RAM.
The resources remain usable in the same world after returning. -/
theorem current_ret_step {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.legacy .ret))
    (stack : before.registers .rsp = call.stack) (af : Bool) :
    step af before = .ok ⟨.returned (returnAfter before call.returnAddress),
      [⟨.stack, call.stack, 8⟩]⟩ ∧
    Current call shared (returnAfter before call.returnAddress) ∧
    ReadAllowed call shared ⟨.stack, call.stack, 8⟩ ∧
    OperandReadSucceeds before ⟨.stack, call.stack, 8⟩ := by
  have loaded : readWord before.memory call.stack = .ok call.returnAddress := by
    rw [current.coupled]
    exact current.contract.stack
  refine ⟨?_, ⟨current.contract, current.coupled⟩,
    stackRead_permission current.contract, rfl, call.returnAddress, loaded⟩
  rw [step_eq_execute af decoded]
  simp [execute, X86.executeInstruction, X86.executeRet, loaded,
    current.contract.returnCanonical, Sequential.Instruction.operandReads, returnAfter, stack]

end EDSL.OS.CallResources
