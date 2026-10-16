/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources

set_option warningAsError true

namespace EDSL.OS.WordResources
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS

/-- Complete caller-slot authority is about the actual current eight bytes. -/
theorem stackRead_permission {call : Call} {shared : Shared}
    (contract : Contract call shared) :
    ArrayResources.ReadPermission shared call.worker ⟨.stack, call.stack, 8⟩ := by
  obtain ⟨loan, live, borrower, sameRegion⟩ := contract.stackLoan
  refine ⟨call.stackLoan, loan, ?_, ?_⟩
  · simp [Borrowing.authorize, live, borrower]
  · rw [← sameRegion]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

structure RetReady (call : Call) (machine : State) : Prop where
  stack : readWord machine.memory (machine.registers .rsp) = .ok call.returnAddress
  returnCanonical : canonical call.returnAddress = true
  stackBound : (machine.registers .rsp).toNat + 8 < 2^64
  postStackCanonical : canonical (machine.registers .rsp + 8) = true

theorem Current.retReady {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (stack : machine.registers .rsp = call.stack) :
    RetReady call machine := by
  refine ⟨?_, current.contract.returnCanonical, ?_, ?_⟩
  · rw [stack, current.coupled]
    exact current.contract.stack
  · rw [stack]
    exact current.contract.stackBound
  · rw [stack]
    exact current.contract.postStackCanonical

def returnAfter (before : State) (returnAddress : Word) : State :=
  { before.writeRegister .rsp (before.registers .rsp + 8) with rip := returnAddress }

/-- Enabled RET is derived from current slot contents and canonicality. -/
theorem current_ret_step {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.legacy .ret))
    (stack : before.registers .rsp = call.stack) (af : Bool) :
    step af before = .ok ⟨.returned (returnAfter before call.returnAddress),
      [⟨.stack, call.stack, 8⟩]⟩ ∧
    Current call shared (returnAfter before call.returnAddress) ∧
    ArrayResources.ReadPermission shared call.worker ⟨.stack, call.stack, 8⟩ ∧
    OperandReadSucceeds before ⟨.stack, call.stack, 8⟩ := by
  have ready := current.retReady stack
  have loaded : readWord before.memory call.stack = .ok call.returnAddress := by
    rw [← stack]
    exact ready.stack
  refine ⟨?_, ⟨current.contract, current.coupled⟩, stackRead_permission current.contract,
    rfl, call.returnAddress, ?_⟩
  · rw [step_eq_execute af decoded]
    simp [execute, X86.executeInstruction, X86.executeRet, loaded,
      ready.returnCanonical, Sequential.Instruction.operandReads, returnAfter, stack]
  · rw [← stack]
    exact ready.stack

/-- Exact store bytes derive the instruction, without a decode premise in the
resource domain. Independent admission also works for other candidate bytes. -/
theorem decode_store32 {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (bytes : call.bytes = Examples.Compiler.MemoryOps.storeBytes)
    (entry : before.rip = call.code) :
    Sequential.decodeAt before = .ok (.legacy .storeEsiRdi) := by
  have code : CodeAt before.memory before.rip Examples.Compiler.MemoryOps.storeBytes := by
    rw [current.coupled, entry, ← bytes]
    exact current.contract.code
  have b0 := code.2 0 0x89 (by decide)
  have b1 := code.2 1 0x37 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1
  apply decodeAt_legacy
  simp [X86.decodeAt, b0, b1]

/-- Every authorized ordinary store retains the complete code and return slot;
for this binary the next instruction is an actually readable/executable RET. -/
theorem decode_ret_after_store32 {call : Call} {evolved : Shared} {before : State}
    (current : Current call evolved (storeAfter before evolved))
    (bytes : call.bytes = Examples.Compiler.MemoryOps.storeBytes)
    (entry : before.rip = call.code) :
    Sequential.decodeAt (storeAfter before evolved) = .ok (.legacy .ret) := by
  have b2 := current.contract.code.2 2 0xc3 (by simp [bytes, Examples.Compiler.MemoryOps.storeBytes])
  change fetchByte (AddressSpace.toMemory evolved.resources.space) (call.code + 2) = .ok 0xc3 at b2
  apply decodeAt_legacy
  simp only [X86.decodeAt, storeAfter, entry]
  rw [b2]
  rfl

/-- Both actual transitions share the same evolved resource witness. Registers
and all flags are untouched by the store; RET changes only RSP and RIP. -/
theorem store32_ret_steps {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (bytes : call.bytes = Examples.Compiler.MemoryOps.storeBytes)
    (entry : before.rip = call.code)
    (pointer : before.registers .rdi = call.targetPointer)
    (stack : before.registers .rsp = call.stack) (afStore afRet : Bool) :
    ∃ evolved,
      Borrowing.mutate shared (.store (Threads.principal call.worker) call.ticket
        call.targetPointer ((before.registers .rsi).setWidth 32)) = .ok (evolved, none) ∧
      step afStore before = .ok ⟨.next (storeAfter before evolved), []⟩ ∧
      step afRet (storeAfter before evolved) = .ok
        ⟨.returned (returnAfter (storeAfter before evolved) call.returnAddress),
          [⟨.stack, call.stack, 8⟩]⟩ ∧
      Current call evolved (returnAfter (storeAfter before evolved) call.returnAddress) ∧
      Mutex.StoreEffect shared evolved call.targetPointer ((before.registers .rsi).setWidth 32) ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) ∧
      ArrayResources.ReadPermission evolved call.worker ⟨.stack, call.stack, 8⟩ := by
  have decoded := decode_store32 current bytes entry
  have intent : Sequential.Instruction.storeIntent (.legacy .storeEsiRdi) before =
      some (call.targetPointer, (before.registers .rsi).setWidth 32) := by
    simp [Sequential.Instruction.storeIntent, X86.Instruction.storeIntent, pointer]
  obtain ⟨evolved, admitted, actual, middleCurrent, effect, loans⟩ :=
    current_store_step current decoded intent afStore
  have retDecoded := decode_ret_after_store32 middleCurrent bytes entry
  have ret := current_ret_step middleCurrent retDecoded (by exact stack) afRet
  exact ⟨evolved, admitted, actual, ret.1, ret.2.1, effect, loans, ret.2.2.1⟩


end EDSL.OS.WordResources
