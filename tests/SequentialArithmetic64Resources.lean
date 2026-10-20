/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources64.Bridge
import EDSL.Grading.StoreReturnValue64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialArithmetic64Resources
open EDSL X86 X86.Sequential OS
open EDSL.OS.WordResources64

-- LEA RSP,[RDI+R12]; ADD RSP,R12; RET. X extends LEA's SIB index,
-- while R extends ADD's register source; both actually replace machine RSP.
private def bytes : List Byte := [0x4a,0x8d,0x24,0x27,0x4c,0x01,0xe4,0xc3]

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

private theorem readonly_current {call : Call} {shared : Shared} {before after : State}
    {instruction : Sequential.Instruction} {af : Bool}
    (current : Current call shared before)
    (decode : Sequential.decodeAt before = .ok instruction)
    (readonly : CFG.readOnly instruction = true)
    (actual : step af before = .ok ⟨.next after, []⟩) : Current call shared after := by
  obtain ⟨found, outcome, currentFound⟩ := current_readOnly_step current decode readonly actual
  rcases outcome with next | returned
  · cases StepResult.next.inj next
    exact currentFound
  · cases returned

/-- Actual decoded address arithmetic and ADD preserve arbitrary current RAM,
owner authority, epochs and live loans in the same world. The original caller
slot survives, but neither changed RSP is bound to it or gains STACK8 authority. -/
theorem lea_add_preserves_same_world {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code) (stack : before.registers .rsp = call.stack)
    (firstDifferent : before.registers .rdi + before.registers .r12 ≠ call.stack)
    (lastDifferent : before.registers .rdi + before.registers .r12 + before.registers .r12 ≠ call.stack)
    (afLea afAdd : Bool) :
    ∃ middle final,
      step afLea before = .ok ⟨.next middle, []⟩ ∧
      middle.registers .rsp = before.registers .rdi + before.registers .r12 ∧
      middle.registers .rsp ≠ before.registers .rsp ∧
      middle.flags = before.flags ∧ Current call shared middle ∧
      step afAdd middle = .ok ⟨.next final, []⟩ ∧
      final.registers .rsp = before.registers .rdi + before.registers .r12 + before.registers .r12 ∧
      final.registers .rsp ≠ call.stack ∧ Current call shared final ∧
      final.memory = before.memory ∧
      final.flags &&& ~~~arithmeticFlagMask = before.flags &&& ~~~arithmeticFlagMask ∧
      final.rip = call.code + 7 ∧
      Threads.HasLoan shared call.worker call.codeLoan ⟨call.code, call.bytes.length⟩ ∧
      Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack,8⟩ ∧
      readWord final.memory call.stack = .ok call.returnAddress ∧
      (¬ReadAllowed call shared final ⟨.stack,final.registers .rsp,8⟩) ∧
      (∀ value : Word, ∃ evolved,
        Borrowing.mutate shared (.store64 (Threads.principal call.worker) call.ticket
          call.targetPointer value) = .ok (evolved,none)) := by
  have leaDecoded := decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .lea64 .rsp (.indexed .rdi .r12 0)) rfl
  let middle : State := { before.writeRegister .rsp (before.registers .rdi + before.registers .r12) with
    rip := before.rip + 4 }
  have actualLea : step afLea before = .ok ⟨.next middle, []⟩ := by
    have operand : (Address.indexed .rdi .r12 0).eval before =
        before.registers .rdi + before.registers .r12 := by
      change before.registers .rdi + (before.registers .r12 <<< (0 : Nat)) = _
      rw [BitVec.shiftLeft_zero]
    rw [step_eq_execute afLea leaDecoded, execute_lea64, operand]
    rfl
  have currentMiddle : Current call shared middle := current.sameMemory rfl
  have middlePC : middle.rip = call.code + 4 := by simp only [middle, entry]
  have addDecoded := decoded currentMiddle codeBytes 4 (by decide) middlePC
    (instruction := .addReg64 .rsp .r12) rfl
  let final : State := { middle.writeRegister .rsp (middle.registers .rsp + middle.registers .r12) with
    rip := middle.rip + 3,
    flags := addFlags64 middle.flags (middle.registers .rsp) (middle.registers .r12) }
  have actualAdd : step afAdd middle = .ok ⟨.next final, []⟩ := by
    rw [step_eq_execute afAdd addDecoded]
    rfl
  have currentFinal : Current call shared final :=
    readonly_current currentMiddle addDecoded rfl actualAdd
  have finalRsp : final.registers .rsp =
      before.registers .rdi + before.registers .r12 + before.registers .r12 := by
    simp only [final, middle, State.writeRegister, reduceCtorEq, ite_true, ite_false]
  refine ⟨middle,final,actualLea,rfl,?_,rfl,currentMiddle,actualAdd,finalRsp,?_,currentFinal,
    rfl,?_,?_,currentFinal.contract.codeLoan,currentFinal.contract.stackLoan,?_,?_,
    current_store64_enabled currentFinal⟩
  · simpa only [middle, State.writeRegister, ite_true, stack] using firstDifferent
  · simpa only [finalRsp] using lastDifferent
  · exact addFlags64_preserves ..
  · simp only [final, middle, entry, BitVec.add_assoc]
    rfl
  · rw [currentFinal.coupled]
    exact currentFinal.contract.stack
  · intro allowed
    exact lastDifferent (finalRsp.symm.trans allowed.1)


/-- A real admitted OS world witnesses the missing return binding: LEA
computes a noncanonical RSP, ADD keeps all original authority, and the actual
following RET faults at that RSP rather than using the retained caller loan. -/
theorem admitted_noncanonical_rsp_faults (afLea afAdd afRet : Bool) :
    ∃ call shared before middle final,
      Current call shared before ∧
      step afLea before = .ok ⟨.next middle, []⟩ ∧
      middle.registers .rsp = 0x800000000000 ∧ canonical (middle.registers .rsp) = false ∧
      step afAdd middle = .ok ⟨.next final, []⟩ ∧
      final.registers .rsp = 0xfffffffc0000 ∧ Current call shared final ∧
      readWord final.memory call.stack = .ok call.returnAddress ∧
      (¬ReadAllowed call shared final ⟨.stack,final.registers .rsp,8⟩) ∧
      step afRet final = .error (.inaccessibleStack 0xfffffffc0000) := by
  let registers : Register → Word := fun _ => 0x7ffffffc0000
  let before := Grading.StoreReturnValue64.Domain.initial bytes 0 registers 0x246
  have current : Current (Grading.StoreReturnValue64.Domain.call bytes) (Grading.StoreReturnValue64.Domain.shared bytes) before :=
    (Grading.StoreReturnValue64.Domain.arbitrary_current bytes (by decide) (by decide) 0 registers 0x246).1
  obtain ⟨middle,final,actualLea,middleRsp,_,_,_,actualAdd,finalRsp,_,currentFinal,
      _,_,finalPC,_,_,slot,notBound,_⟩ :=
    lea_add_preserves_same_world current rfl rfl rfl (by decide) (by decide) afLea afAdd
  have rspMiddle : middle.registers .rsp = 0x800000000000 := by
    calc
      middle.registers .rsp = (262144 : Word) + 0x7ffffffc0000 := middleRsp
      _ = 0x800000000000 := by decide
  have rspFinal : final.registers .rsp = 0xfffffffc0000 := by
    calc
      final.registers .rsp = (262144 : Word) + 0x7ffffffc0000 + 0x7ffffffc0000 := finalRsp
      _ = 0xfffffffc0000 := by decide
  have retDecoded := decoded currentFinal rfl 7 (by decide) finalPC
    (instruction := .legacy .ret) rfl
  refine ⟨Grading.StoreReturnValue64.Domain.call bytes,Grading.StoreReturnValue64.Domain.shared bytes,before,middle,final,current,actualLea,
    rspMiddle,?_,actualAdd,rspFinal,currentFinal,slot,notBound,?_⟩
  · rw [rspMiddle]; decide
  · rw [step_eq_execute afRet retDecoded]
    simp [execute, X86.executeInstruction, X86.executeRet, rspFinal,
      readWord, readStackByte, canonical]

end EDSL.Tests.SequentialArithmetic64Resources

#print axioms EDSL.Tests.SequentialArithmetic64Resources.lea_add_preserves_same_world
#print axioms EDSL.Tests.SequentialArithmetic64Resources.admitted_noncanonical_rsp_faults
#audit_edsl
