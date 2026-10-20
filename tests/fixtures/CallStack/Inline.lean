/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Grading.CallStack.Contract
import EDSL.X86.CallReturn.DecodeTransport

set_option warningAsError true

namespace EDSL.CallStack.Inline
open X86 OS

def bytes : List Byte := [0x48,0x8d,0x47,0x02,0xc3]
def program : Program := ⟨bytes, 0⟩
def after (initial : State) : State := CallReturn.leaState initial .rax (.plain .rdi) 2
def finish (resource : Resources) (initial : State) : State :=
  { (after initial).writeRegister .rsp ((after initial).registers .rsp + 8) with
    rip := resource.frame.call.returnAddress }
def result (resource : Resources) (initial : State) : CallReturn.Result :=
  ⟨finish resource initial, 2, [⟨.stack, resource.frame.top, 8⟩]⟩

/-- A different implementation meets the same fixed contract without CALL,
PUSH or a compiler-profile enum. Its footprint still includes the actual RET. -/
theorem correct {resource initial} (pre : ResourcePre program resource initial)
    (choices : CallReturn.Choices) :
    CoveredExecution resource.frame choices resource.shared initial resource.shared (result resource initial) ∧
      Post (resourceInput resource) initial (result resource initial).state := by
  have code : CodeAt initial.memory resource.frame.call.code bytes := by
    have same : resource.frame.call.bytes = bytes := pre.code
    rw [pre.current.coupled, ← same]
    exact pre.current.contract.pureCall.code
  have decoded : CallReturn.decodeAt initial = .ok (.leaDisp8 .rax (.plain .rdi) 2) :=
    CallReturn.decodeAt_code code (by decide) (by decide : 0 < bytes.length) initial rfl pre.entry rfl
  have step : StackFrame.CPU.Step resource.frame resource.shared resource.shared initial
      (after initial) (choices 0) ⟨.next (after initial), []⟩ :=
    ⟨_, _, decoded, rfl, rfl, rfl, .unchanged rfl rfl,
      by simp [Sequential.Instruction.operandReads]⟩
  have current := step.current pre.current
  have codeAfter : CodeAt (after initial).memory resource.frame.call.code bytes := code
  have start : initial.rip = resource.frame.call.code := pre.entry.trans (BitVec.add_zero _)
  have pc : (after initial).rip = resource.frame.call.code + 4 := by
    change initial.rip + 4 = _
    rw [start]
  have decodedRet : CallReturn.decodeAt (after initial) = .ok (.sequential (.legacy .ret)) :=
    CallReturn.decodeAt_code codeAfter (by decide) (by decide : 4 < bytes.length) _ rfl pc rfl
  have sp : (after initial).registers .rsp = resource.frame.top := pre.stack
  have last := StackFrame.CPU.original_ret_step current sp ((choices.drop 1) 0) decodedRet
  have firstWithin : FetchWithin resource.frame initial :=
    ⟨0, _, pre.entry, decoded, by rw [pre.code]; decide⟩
  have lastWithin : FetchWithin resource.frame (after initial) :=
    ⟨4, _, pc, decodedRet, by rw [pre.code]; decide⟩
  have covered : CoveredExecution resource.frame choices resource.shared initial resource.shared
      ⟨finish resource initial, 2, [⟨.stack, (after initial).registers .rsp, 8⟩]⟩ :=
    .next step firstWithin (.ret last lastWithin)
  refine ⟨?_, ?_⟩
  · change CoveredExecution resource.frame choices resource.shared initial resource.shared
      ⟨finish resource initial, 2, [⟨.stack, resource.frame.top, 8⟩]⟩
    simpa only [sp] using covered
  · refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
    · change (initial.registers .rdi + 2).toNat = resultNat resource.value
      rw [pre.argument]
      rfl
    · intro register outside
      have notSP : register ≠ .rsp := by
        intro same
        subst register
        exact outside (by decide)
      have notAX : register ≠ .rax := by
        intro same
        subst register
        exact outside (by decide)
      change (if register = .rsp then _ else if register = .rax then _ else initial.registers register) = _
      rw [ite_eq_right notSP, ite_eq_right notAX]

theorem claim : Grading.CallStack.Claim program := by
  refine ⟨?_, Grading.CallStack.domain_nonvacuous program (by decide) (by decide)⟩
  intro resource initial pre choices
  exact ⟨resource.shared, result resource initial, (correct pre choices).1, (correct pre choices).2⟩

theorem exact_two {resource initial} (pre : ResourcePre program resource initial)
    (choices : CallReturn.Choices) :
    CallReturn.run choices 2 initial = .ok (result resource initial) := by
  have execution : CallReturn.Executes choices initial (result resource initial) := by
    change CallReturn.ExecutesFrom (initial.registers .rsp) choices initial (result resource initial)
    rw [pre.stack]
    exact (correct pre choices).1.machine
  exact CallReturn.run_complete execution (Nat.le_refl _)

end EDSL.CallStack.Inline
