/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources
import EDSL.Grading.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialCmov64Resources
open EDSL X86 X86.Sequential OS OS.CallResources

-- CMOVE RSP,RDI; RET. The code/caller-slot loans are the complete admission
-- resources: no unrelated owned mutable word is required.
private def bytes : List Byte := [0x48,0x0f,0x44,0xe7,0xc3]

/-- The pure-call contract is inhabited for every nonempty bounded code
span, independently of decoding and for arbitrary incoming flags. The shared
domain supplies checked current loans and RAM, not a future execution premise. -/
theorem admission_inhabited (code : List Byte) (positive : 0 < code.length)
    (bound : code.length ≤ 4096) (flags : Word) :
    ∃ (call : Call) (shared : Shared) (machine : State),
      call.bytes = code ∧ Current call shared machine ∧ machine.rip = call.code ∧
      machine.registers .rsp = call.stack ∧ machine.flags = flags := by
  let call : Call := ⟨10,4096,65544,8192,code,0,1⟩
  let machine : State := ⟨fun _ => 65544,4096,flags,
    AddressSpace.toMemory (Grading.Domain.shared code).resources.space⟩
  have base := Grading.Domain.contractA code positive bound
  refine ⟨call,Grading.Domain.shared code,machine,rfl,?_,rfl,rfl,rfl⟩
  exact ⟨⟨base.wellFormed,base.held.code,base.held.stack,base.code,base.stack,
    base.returnCanonical,base.stackBound,base.postStackCanonical⟩,rfl⟩

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

/-- Taking a conditional RSP assignment preserves the original caller-slot
loan and every current OS resource. It does not authorize reading a different
slot. The proof derives the real byte-decoded CMOV transition. -/
theorem taken_rsp_retains_original_slot {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code) (taken : before.flags.getLsbD 6 = true)
    (different : before.registers .rdi ≠ call.stack) (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧
      after.registers .rsp = before.registers .rdi ∧
      Current call shared after ∧ after.memory = before.memory ∧ after.flags = before.flags ∧
      Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord after.memory call.stack = .ok call.returnAddress ∧
      ReadAllowed call shared ⟨.stack,call.stack,8⟩ ∧
      ¬ ReadAllowed call shared ⟨.stack,after.registers .rsp,8⟩ := by
  have decode := decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .cmovReg64 .equal .rsp .rdi) rfl
  obtain ⟨after, actual, currentAfter, value, _, memory, flags, _⟩ :=
    current_cmovReg64_step current decode af
  have rsp : after.registers .rsp = before.registers .rdi := by
    simpa only [Condition.holds,taken,Bool.true_eq,ite_true] using value
  refine ⟨after,actual,rsp,currentAfter,memory,flags,currentAfter.contract.stackLoan,
    ?_,stackRead_permission currentAfter.contract,?_⟩
  · rw [currentAfter.coupled]
    exact currentAfter.contract.stack
  · intro permission
    exact different (rsp.symm.trans permission.2.1)

/-- A false full64 CMOV retains the actual caller binding. The following RET
reads the original eight bytes, returns to their address and retains the same
RAM, allocation metadata and reusable loans. Both steps allow either AF choice. -/
theorem false_rsp_returns {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code) (stack : before.registers .rsp = call.stack)
    (untaken : before.flags.getLsbD 6 = false) (afMove afRet : Bool) :
    ∃ middle final,
      step afMove before = .ok ⟨.next middle, []⟩ ∧
      middle.registers = before.registers ∧
      step afRet middle = .ok ⟨.returned final,[⟨.stack,call.stack,8⟩]⟩ ∧
      final.rip = call.returnAddress ∧ final.registers .rsp = call.stack + 8 ∧
      final.memory = before.memory ∧ final.flags = before.flags ∧
      Current call shared final ∧
      ReadAllowed call shared ⟨.stack,call.stack,8⟩ ∧
      OperandReadSucceeds middle ⟨.stack,call.stack,8⟩ := by
  have decode := decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .cmovReg64 .equal .rsp .rdi) rfl
  let middle : State := { before with rip := before.rip + 4 }
  have actual : step afMove before = .ok ⟨.next middle,[]⟩ := by
    rw [step_eq_execute afMove decode]
    exact execute_cmovReg64_false before .equal .rsp .rdi afMove untaken
  have currentMiddle : Current call shared middle := current.sameMemory rfl
  have middleStack : middle.registers .rsp = call.stack := stack
  have retDecode := decoded currentMiddle codeBytes 4 (by decide)
    (by change before.rip + 4 = call.code + BitVec.ofNat 64 4; rw [entry]; rfl)
    (instruction := .legacy .ret) rfl
  obtain ⟨returned,currentFinal,allowed,read⟩ :=
    current_ret_step currentMiddle retDecode middleStack afRet
  refine ⟨middle,returnAfter middle call.returnAddress,actual,rfl,returned,rfl,?_,
    rfl,rfl,currentFinal,allowed,read⟩
  simp [returnAfter,State.writeRegister,middle,stack]

end EDSL.Tests.SequentialCmov64Resources

#audit_edsl
