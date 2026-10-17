/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallResources
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialJccResources
open EDSL X86 X86.Sequential OS OS.CallResources

-- JA +1; unsupported owned byte; RET. Both entry operands remain unconstrained.
private def bytes : List Byte := [0x77,1,0xff,0xc3]

private theorem decoded {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (codeBytes : call.bytes = bytes)
    (offset : Nat) (inside : offset < bytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code bytes := by
    rw [current.coupled,← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code (by decide) offset inside machine rfl pc) literal

/-- A real taken branch skips an unsupported byte and reaches the original
RET. The same coherent OS world supplies both fetches and the retained caller
slot; successful future execution is derived, rather than assumed. -/
theorem branch_then_return {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code) (stack : before.registers .rsp = call.stack)
    (above : Condition.holds .above before.flags = true) (afBranch afRet : Bool) :
    ∃ middle final,
      step afBranch before = .ok ⟨.next middle,[]⟩ ∧
      step afRet middle = .ok ⟨.returned final,[⟨.stack,call.stack,8⟩]⟩ ∧
      middle.registers = before.registers ∧ middle.flags = before.flags ∧
      final.rip = call.returnAddress ∧ final.registers .rsp = call.stack + 8 ∧
      final.memory = before.memory ∧ final.flags = before.flags ∧
      Current call shared middle ∧ Current call shared final ∧
      ReadAllowed call shared ⟨.stack,call.stack,8⟩ := by
  have code : CodeAt before.memory call.code bytes := by
    rw [current.coupled,← codeBytes]
    exact current.contract.code
  have safe : ShortBranchSafe before .above 1 := by
    intro _
    have target := code_canonical_offset code 3 (by decide)
    simpa [entry,BitVec.add_assoc] using target
  have branchDecode := decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .jcc .above 1) rfl
  obtain ⟨actual,currentMiddle,registers,memory,flags⟩ :=
    current_shortBranch_step current branchDecode (.generic .above 1) safe afBranch
  let middle := { before with rip := shortBranchTarget before .above 1 }
  have pc : middle.rip = call.code + BitVec.ofNat 64 3 := by
    simp [middle,shortBranchTarget,above,entry,BitVec.add_assoc]
  have retDecode := decoded currentMiddle codeBytes 3 (by decide) pc
    (instruction := .legacy .ret) rfl
  have middleStack : middle.registers .rsp = call.stack := stack
  obtain ⟨returned,currentFinal,allowed,_⟩ :=
    current_ret_step currentMiddle retDecode middleStack afRet
  refine ⟨middle,returnAfter middle call.returnAddress,actual,returned,registers,flags,
    rfl,?_,rfl,rfl,currentMiddle,currentFinal,allowed⟩
  simp [returnAfter,State.writeRegister,middle,stack]

end EDSL.Tests.SequentialJccResources

#audit_edsl
