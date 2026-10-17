/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources64.Bridge
import EDSL.Grading.StoreReturnValue64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialLogical64Resources
open EDSL X86 X86.Sequential OS
open EDSL.OS.WordResources64

-- OR RSP,RCX; RET. Unlike a data write, changing the actual stack pointer
-- cannot transfer the original caller's loan to that computed address.
private def bytes : List Byte := [0x48,0x09,0xcc,0xc3]

private theorem decoded {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (codeBytes : call.bytes = bytes)
    (offset : Nat) (inside : offset < bytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code bytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code (by decide) offset inside machine rfl pc) literal

/-- Actual current bytes perform the register operation in the same OS world:
all RAM, ownership, epochs, loans and permissions survive, along with reusable
DATA8 mutation authority. A computed RSP distinct from the original caller slot
has no STACK8 authority merely because that original slot remains live. -/
theorem or_rsp_preserves_original_authority {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code)
    (different : before.registers .rsp ||| before.registers .rcx ≠ call.stack)
    (af : Bool) :
    ∃ after,
      step af before = .ok ⟨.next after, []⟩ ∧
      Current call shared after ∧ after.memory = before.memory ∧
      after.registers .rsp = before.registers .rsp ||| before.registers .rcx ∧
      (∀ register, register ≠ .rsp → after.registers register = before.registers register) ∧
      after.flags.getLsbD 4 = af ∧
      after.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask ∧
      after.rip = call.code + 3 ∧
      Threads.HasLoan shared call.worker call.codeLoan ⟨call.code,call.bytes.length⟩ ∧
      Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord after.memory call.stack = .ok call.returnAddress ∧
      (¬ReadAllowed call shared after ⟨.stack,after.registers .rsp,8⟩) ∧
      (∀ value : Word, ∃ evolved,
        Borrowing.mutate shared (.store64 (Threads.principal call.worker) call.ticket
          call.targetPointer value) = .ok (evolved,none)) := by
  have instruction := decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .logicalReg64 .bor .rsp .rcx) rfl
  obtain ⟨after,executed,result,others,memory,flags,pc⟩ :=
    execute_logicalReg64_context before .bor .rsp .rcx af
  have currentAfter : Current call shared after := current.sameMemory memory
  have resultOr : after.registers .rsp = before.registers .rsp ||| before.registers .rcx := result
  refine ⟨after,?_,currentAfter,memory,resultOr,others,?_,?_,?_,
    currentAfter.contract.codeLoan,currentAfter.contract.stackLoan,?_,?_,
    current_store64_enabled currentAfter⟩
  · rw [step_eq_execute af instruction]
    exact executed
  · rw [flags]
    exact (logicalFlags64_bits ..).2.2.1
  · rw [flags]
    exact logicalFlags64_preserves ..
  · simpa only [entry] using pc
  · rw [currentAfter.coupled]
    exact currentAfter.contract.stack
  · intro allowed
    exact different (resultOr.symm.trans allowed.1)

/-- A checked allocated OS world witnesses the distinction, for either AF
choice. OR makes RSP noncanonical while the original caller bytes and store
capability remain valid; the real next RET faults at the computed pointer. -/
theorem admitted_noncanonical_rsp_ret_faults (afLogical afRet : Bool) :
    ∃ call shared before after,
      Current call shared before ∧
      step afLogical before = .ok ⟨.next after, []⟩ ∧
      Current call shared after ∧ after.memory = before.memory ∧
      after.registers .rsp = 0x800000010008 ∧ canonical (after.registers .rsp) = false ∧
      Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord after.memory call.stack = .ok call.returnAddress ∧
      (¬ReadAllowed call shared after ⟨.stack,after.registers .rsp,8⟩) ∧
      step afRet after = .error (.inaccessibleStack 0x800000010008) := by
  let registers : Register → Word := fun _ => 0x800000000000
  let before := Grading.StoreReturnValue64.Domain.initial bytes 0 registers 0xed7
  have current : Current (Grading.StoreReturnValue64.Domain.call bytes)
      (Grading.StoreReturnValue64.Domain.shared bytes) before :=
    (Grading.StoreReturnValue64.Domain.arbitrary_current bytes (by decide) (by decide)
      0 registers 0xed7).1
  obtain ⟨after,actual,currentAfter,memory,rsp,_,_,_,pc,_,stackLoan,slot,notAllowed,_⟩ :=
    or_rsp_preserves_original_authority current rfl rfl (by decide) afLogical
  have rspAfter : after.registers .rsp = 0x800000010008 := by
    calc
      after.registers .rsp = (65544 : Word) ||| 0x800000000000 := rsp
      _ = 0x800000010008 := by decide
  have retDecoded := decoded currentAfter rfl 3 (by decide) pc
    (instruction := .legacy .ret) rfl
  refine ⟨Grading.StoreReturnValue64.Domain.call bytes,
    Grading.StoreReturnValue64.Domain.shared bytes,before,after,current,actual,
    currentAfter,memory,rspAfter,?_,stackLoan,slot,notAllowed,?_⟩
  · rw [rspAfter]
    decide
  · rw [step_eq_execute afRet retDecoded]
    simp [execute, X86.executeInstruction, X86.executeRet, rspAfter,
      readWord, readStackByte, canonical]

end EDSL.Tests.SequentialLogical64Resources

#print axioms EDSL.Tests.SequentialLogical64Resources.or_rsp_preserves_original_authority
#print axioms EDSL.Tests.SequentialLogical64Resources.admitted_noncanonical_rsp_ret_faults
#audit_edsl
