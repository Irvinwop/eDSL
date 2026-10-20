/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialCmov32Resources
open EDSL X86 X86.Sequential OS OS.CallResources

private def rspBytes : List Byte := [0x0f,0x44,0xe7,0xc3]
private def valueBytes : List Byte := [0x0f,0x44,0xc7,0xc3]

private theorem decoded {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (bytes : List Byte) (codeBytes : call.bytes = bytes)
    (bound : bytes.length ≤ 64) (offset : Nat) (inside : offset < bytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code bytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code bound offset inside machine rfl pc) literal

/-- A false low32 CMOV can replace RSP. Retaining the original caller-slot
loan does not authorize the resulting truncated pointer. The theorem uses
actual byte decoding and the same complete resource world after the step. -/
theorem false_rsp_requires_original_slot {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = rspBytes)
    (entry : before.rip = call.code) (untaken : before.flags.getLsbD 6 = false)
    (changed : (((before.registers .rsp).setWidth 32).setWidth 64) ≠ call.stack)
    (af : Bool) :
    ∃ after, step af before = .ok ⟨.next after, []⟩ ∧
      after.registers .rsp = (((before.registers .rsp).setWidth 32).setWidth 64) ∧
      Current call shared after ∧ after.memory = before.memory ∧ after.flags = before.flags ∧
      Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord after.memory call.stack = .ok call.returnAddress ∧
      ReadAllowed call shared ⟨.stack,call.stack,8⟩ ∧
      ¬ ReadAllowed call shared ⟨.stack,after.registers .rsp,8⟩ := by
  have decode := decoded current rspBytes codeBytes (by decide) 0 (by decide)
    (by simpa using entry) (instruction := .cmovReg32 .equal .rsp .rdi false) rfl
  obtain ⟨after,actual,currentAfter,value,_,memory,flags,_⟩ :=
    current_cmovReg32_step current decode af
  have rsp : after.registers .rsp = (((before.registers .rsp).setWidth 32).setWidth 64) := by
    simpa only [Condition.holds,untaken,Bool.false_eq_true,ite_false] using value
  refine ⟨after,actual,rsp,currentAfter,memory,flags,currentAfter.contract.stackLoan,
    ?_,stackRead_permission currentAfter.contract,?_⟩
  · rw [currentAfter.coupled]
    exact currentAfter.contract.stack
  · intro permission
    exact changed (rsp.symm.trans permission.2.1)

/-- Both condition outcomes compose with ordinary RET when CMOV's destination
is RAX and current RSP still binds to the original complete caller slot.
Selected low32 bits, all flags, RAM/permissions and the entire OS world survive. -/
theorem rax_cmov_then_return {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = valueBytes)
    (entry : before.rip = call.code) (stack : before.registers .rsp = call.stack)
    (afMove afRet : Bool) :
    ∃ middle final,
      step afMove before = .ok ⟨.next middle,[]⟩ ∧
      step afRet middle = .ok ⟨.returned final,[⟨.stack,call.stack,8⟩]⟩ ∧
      final.registers .rax =
        ((((if before.flags.getLsbD 6 then before.registers .rdi
          else before.registers .rax) : Word).setWidth 32).setWidth 64) ∧
      final.rip = call.returnAddress ∧ final.registers .rsp = call.stack + 8 ∧
      final.memory = before.memory ∧ final.flags = before.flags ∧
      Current call shared final ∧ ReadAllowed call shared ⟨.stack,call.stack,8⟩ ∧
      OperandReadSucceeds middle ⟨.stack,call.stack,8⟩ := by
  have decode := decoded current valueBytes codeBytes (by decide) 0 (by decide)
    (by simpa using entry) (instruction := .cmovReg32 .equal .rax .rdi false) rfl
  obtain ⟨middle,actual,currentMiddle,value,other,memory,flags,pc⟩ :=
    current_cmovReg32_step current decode afMove
  have middleStack : middle.registers .rsp = call.stack :=
    (other .rsp (by decide)).trans stack
  have retDecode := decoded currentMiddle valueBytes codeBytes (by decide) 3 (by decide)
    (by simpa [entry] using pc) (instruction := .legacy .ret) rfl
  obtain ⟨returned,currentFinal,allowed,read⟩ :=
    current_ret_step currentMiddle retDecode middleStack afRet
  refine ⟨middle,returnAfter middle call.returnAddress,actual,returned,?_,rfl,?_,
    memory,flags,currentFinal,allowed,read⟩
  · simpa [returnAfter,State.writeRegister,Condition.holds] using value
  · simp [returnAfter,State.writeRegister,middleStack]

end EDSL.Tests.SequentialCmov32Resources

#audit_edsl
