/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Progress
import EDSL.OS.ScalarCall64

/-!
Transport the shared plain-method body result to independent scalar ABI
observations. Original entry and final resources refer to actual worker slots.
A returned store may still have pending publications; collection is separate.
-/

set_option autoImplicit false

namespace EDSL.X86.VCGen.PlainMethods
open OS OS.TSO64 AtomicMethods

/-- A plain MOV load changes only RAX; a store preserves every register. -/
theorem Operation.registers_other (operation : Operation) (entry : Register → Word)
    (reply : operation.Reply) (register : Register) (other : register ≠ .rax) :
    operation.registers entry reply register = entry register := by
  cases operation with
  | load _ => exact written_other entry .rax reply register other
  | store _ _ => rfl

/-- Apart from RAX and the actual RET pop of RSP, all GPRs retain their entry
values. This is stronger than the represented callee-saved subset. -/
theorem BodyPost.registers_other {method : Method} {worker : Worker}
    {reply : method.operation.Reply} (post : BodyPost method worker reply)
    (register : Register) (notRax : register ≠ .rax) (notRsp : register ≠ .rsp) :
    worker.context.registers register = method.entry register := by
  rw [post.registers, written_other _ .rsp _ register notRsp]
  exact method.operation.registers_other method.entry reply register notRax

/-- The body proof discharges the independent scalar return frame, including
DF, canonical post-pop stack, original protected caller and current authority.
Entry admission concerns only the actual initial state. No queue emptiness or
successful collection is needed at return. -/
theorem BodyPost.return_frame {method : Method} {before after : OS.TSO64.State}
    {tid : Nat} {initial final : Worker} {padding : List Padding}
    {reply : method.operation.Reply}
    (current : Current method before)
    (initialLive : before.workers[tid]? = some initial)
    (entry : At method (.preamble 0 padding) initial)
    (admitted : ScalarCall64.Entry initial)
    (valid : WellFormed after .sharedCell)
    (live : after.workers[tid]? = some final)
    (post : BodyPost method final reply) :
    ScalarCall64.ReturnFrame before after tid initial final := by
  have entryRegisters : initial.context.registers = method.entry := entry.location.2.2.1
  have flags : final.context.flags = initial.context.flags := post.flags.trans entry.flags.symm
  have stack : final.context.registers .rsp = initial.context.registers .rsp + 8 := by
    rw [post.rsp, entryRegisters]
  refine ⟨initialLive, live, post.phase, post.resources.trans entry.resources.symm,
    (valid.2 final (List.mem_of_getElem? live)).1, ?_, flags, stack, ?_, ?_, ?_, ?_⟩
  · intro register member
    have notRax : register ≠ .rax := by
      cases register <;> simp_all [PureCall.calleeSaved]
    have notRsp : register ≠ .rsp := by
      cases register <;> simp_all [PureCall.calleeSaved]
    exact (post.registers_other register notRax notRsp).trans
      (congrFun entryRegisters register).symm
  · rw [stack]
    exact admitted.postStackCanonical
  · rw [flags]
    exact admitted.direction
  · rw [post.rip]
    exact method.returnCanonical
  · refine ⟨method.returnAddress, ?_, post.rip⟩
    simpa only [entry.resources] using current.caller

end EDSL.X86.VCGen.PlainMethods

#audit_edsl
