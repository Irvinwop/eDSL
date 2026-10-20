/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources64.Bridge
import EDSL.Grading.Write32.Resources
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialMemory64Resources
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.OS.WordResources64

private def rspBytes : List Byte := [0x48, 0x89, 0x37, 0x48, 0x8b, 0x27]

private theorem decoded {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (codeBytes : call.bytes = rspBytes)
    (offset : Nat) (inside : offset < rspBytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState rspBytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code rspBytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code (by decide) offset inside machine rfl pc) literal

/-- Arbitrary current worlds derive a full64 store and then a full64 load into
RSP. The real stack loan and its contents survive; the resulting RSP is NOT
bound to the original caller slot when the stored value differs from it. -/
theorem checked_store_load_rsp {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = rspBytes)
    (entry : before.rip = call.code) (pointer : before.registers .rdi = call.targetPointer)
    (different : before.registers .rsi ≠ call.stack) (afStore afLoad : Bool) :
    ∃ evolved middle final,
      Borrowing.mutate shared (.store64 (Threads.principal call.worker) call.ticket
        call.targetPointer (before.registers .rsi)) = .ok (evolved, none) ∧
      step afStore before = .ok ⟨.next middle, []⟩ ∧
      step afLoad middle = .ok ⟨.next final, [⟨.data, call.targetPointer, 8⟩]⟩ ∧
      final.registers .rsp = before.registers .rsi ∧ final.registers .rsp ≠ call.stack ∧
      Current call evolved final ∧
      Threads.HasLoan evolved call.worker call.stackLoan ⟨call.stack, 8⟩ ∧
      readWord final.memory call.stack = .ok call.returnAddress ∧
      ReadAllowed call evolved middle ⟨.data, call.targetPointer, 8⟩ ∧
      OperandReadSucceeds middle ⟨.data, call.targetPointer, 8⟩ ∧
      Borrowing.StoreEffect64 shared evolved call.targetPointer (before.registers .rsi) := by
  have storeDecoded := decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .storeMem64 (.base .rdi) .rsi) rfl
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rsi) before =
      some (call.targetPointer, before.registers .rsi) := by
    simp [Sequential.Instruction.storeIntent64, Address.eval, pointer]
  obtain ⟨evolved, stored, actualStore, currentMiddle, effect, _⟩ :=
    current_store64_step current storeDecoded intent afStore
  let middle := storeAfterLength before evolved 3
  change step afStore before = .ok ⟨.next middle, []⟩ at actualStore
  change Current call evolved middle at currentMiddle
  have middlePC : middle.rip = call.code + 3 := by simp [middle, storeAfterLength, entry]
  have loadDecoded := decoded currentMiddle codeBytes 3 (by decide) middlePC
    (instruction := .loadMem64 .rsp (.base .rdi)) rfl
  have effective : (Address.base .rdi).eval middle = call.targetPointer := pointer
  obtain ⟨value, final, actualLoad, assigned, observed, permission, readSuccess,
      currentFinal, _, _, _, _⟩ := current_load64_step currentMiddle loadDecoded effective afLoad
  have valueEq : value = before.registers .rsi := by
    apply Except.ok.inj
    exact observed.symm.trans (by rw [currentMiddle.coupled]; exact effect.readback)
  have assignedFull := assigned.trans valueEq
  refine ⟨evolved, middle, final, stored, actualStore, actualLoad, assignedFull,
    ?_, currentFinal, currentFinal.contract.stackLoan, ?_, permission, readSuccess, effect⟩
  · simpa only [assignedFull] using different
  · rw [currentFinal.coupled]
    exact currentFinal.contract.stack

/-- A destination/base alias reads the real full pre-state pointer. Current
owner authority suffices, without an additional target read loan. -/
theorem checked_load_base_alias {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before)
    (decoded : Sequential.decodeAt before = .ok (.loadMem64 .rdi (.base .rdi)))
    (pointer : before.registers .rdi = call.targetPointer) (af : Bool) :
    ∃ value after,
      step af before = .ok ⟨.next after, [⟨.data, call.targetPointer, 8⟩]⟩ ∧
      loadQWord before.memory call.targetPointer = .ok value ∧ after.registers .rdi = value ∧
      Current call shared after ∧ ReadAllowed call shared before ⟨.data, call.targetPointer, 8⟩ := by
  obtain ⟨value, after, actual, assigned, observed, permission, _, currentAfter, _, _, _, _⟩ :=
    current_load64_step current decoded pointer af
  exact ⟨value, after, actual, observed, assigned, currentAfter, permission⟩

-- A full64 ordinary write cannot spend the existing four-byte raw authority.
example (target : Word) (before : State) (address : Address) (source : Register) :
    ¬Grading.Write32.RawEffect target before (.storeMem64 address source) := by
  intro effect
  rcases effect with allowed | ⟨_, intent⟩
  · cases allowed
  · cases intent

-- The old four-byte OS effect rejects it even if the stored high bits are zero.
example (owner : Nat) (ticket : Ownership.Ticket) (target : Word)
    (shared evolved : Borrowing.State) (before : State) (address : Address)
    (source : Register) (observation : Observation) :
    ¬WordResources.WordEffect owner ticket target shared before (.storeMem64 address source) observation evolved := by
  intro effect
  cases effect with
  | readOnly allowed => cases allowed
  | store intent _ => cases intent

end EDSL.Tests.SequentialMemory64Resources

#print axioms EDSL.OS.WordResources64.current_store64_step
#print axioms EDSL.OS.WordResources64.current_load64_step
#print axioms EDSL.OS.WordResources64.current_ret_step
#print axioms EDSL.Tests.SequentialMemory64Resources.checked_store_load_rsp
#print axioms EDSL.Tests.SequentialMemory64Resources.checked_load_base_alias

#audit_edsl
