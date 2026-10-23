/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources.Bridge
import EDSL.Grading.Write32.Resources
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialMoveResources
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.OS.WordResources

-- Store EDI through a full64 SIB address, then load the same word into ESP.
-- The source aliases the base and the load overwrites the caller's machine RSP.
-- Arbitrary current OS worlds supply all data, authority and memory permissions.
private def bytes : List Byte := [0x89, 0x3c, 0xb7, 0x8b, 0x24, 0xb7]
private def operand : Address := .indexed .rdi .rsi ⟨2, by decide⟩

private theorem store_decoded {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code) :
    Sequential.decodeAt before = .ok (.storeMem32 operand .rdi) := by
  have code : CodeAt before.memory before.rip bytes := by
    rw [current.coupled, entry, ← codeBytes]
    exact current.contract.code
  have b0 := code.2 0 0x89 (by decide)
  have b1 := code.2 1 0x3c (by decide)
  have b2 := code.2 2 0xb7 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0 b1 b2
  simp [Sequential.decodeAt, X86.decodeAt, b0, b1, b2, decodeNewAt, decodeTailAt,
    decodeAddressAt, modRMRM, modRMReg, lowRegister, operand]

private theorem load_decoded {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code + 3) :
    Sequential.decodeAt before = .ok (.loadMem32 .rsp operand) := by
  have code : CodeAt before.memory call.code bytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  have c3 := code.2 3 0x8b (by decide)
  have c4 := code.2 4 0x24 (by decide)
  have c5 := code.2 5 0xb7 (by decide)
  have b0 : fetchByte before.memory before.rip = .ok 0x8b := by simpa [entry] using c3
  have b1 : fetchByte before.memory (before.rip + 1) = .ok 0x24 := by
    simpa [entry, BitVec.add_assoc] using c4
  have b2 : fetchByte before.memory (before.rip + 2) = .ok 0xb7 := by
    simpa [entry, BitVec.add_assoc] using c5
  simp only [BitVec.ofNat_eq_ofNat] at b0 b1 b2
  simp [Sequential.decodeAt, X86.decodeAt, b0, b1, b2, decodeNewAt, decodeTailAt,
    decodeAddressAt, modRMRM, modRMReg, lowRegister, operand]

/-- The actual code and current resources derive both steps. The loaded value
comes from the checked OS update, with intact owner metadata and all live loans.
The original stack slot survives even though the load replaces machine RSP. -/
theorem checked_sib_store_then_load_rsp {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = bytes)
    (entry : before.rip = call.code)
    (effective : before.registers .rdi + (before.registers .rsi <<< 2) = call.targetPointer)
    (afStore afLoad : Bool) :
    ∃ evolved middle final,
      Borrowing.mutate shared (.store (Threads.principal call.worker) call.ticket
        call.targetPointer ((before.registers .rdi).setWidth 32)) = .ok (evolved, none) ∧
      step afStore before = .ok ⟨.next middle, []⟩ ∧
      middle.rip = before.rip + 3 ∧
      step afLoad middle = .ok ⟨.next final, [⟨.data, call.targetPointer, 4⟩]⟩ ∧
      final.registers .rsp = ((before.registers .rdi).setWidth 32).setWidth 64 ∧
      final.rip = before.rip + 3 + 3 ∧
      Current call evolved final ∧
      Grading.Write32.ReadAllowed call evolved middle ⟨.data, call.targetPointer, 4⟩ ∧
      OperandReadSucceeds middle ⟨.data, call.targetPointer, 4⟩ ∧
      readWord final.memory call.stack = .ok call.returnAddress ∧
      evolved.resources.allocations = shared.resources.allocations ∧
      evolved.loans = shared.loans ∧
      (∀ query, ¬(AddressSpace.wordRegion call.targetPointer).Contains query →
        evolved.resources.space.cells query = shared.resources.space.cells query) := by
  have decoded := store_decoded current codeBytes entry
  have intent : Sequential.Instruction.storeIntent (.storeMem32 operand .rdi) before =
      some (call.targetPointer, (before.registers .rdi).setWidth 32) := by
    simpa [Sequential.Instruction.storeIntent, operand, Address.eval] using
      congrArg (fun pointer => some (pointer, (before.registers .rdi).setWidth 32)) effective
  obtain ⟨evolved, stored, actualStore, currentMiddle, effect, _⟩ :=
    current_store_step current decoded intent afStore
  let middle := storeAfterLength before evolved 3
  change step afStore before = .ok ⟨.next middle, []⟩ at actualStore
  change Current call evolved middle at currentMiddle
  have middleEntry : middle.rip = call.code + 3 := by simp [middle, storeAfterLength, entry]
  have loadDecoded := load_decoded currentMiddle codeBytes middleEntry
  have nextEffective : operand.eval middle = call.targetPointer := by
    simpa [operand, Address.eval, middle, storeAfterLength] using effective
  obtain ⟨value, final, actualLoad, loadedReg, observed, ⟨allocation, authorized, fits⟩,
      readSuccess, currentFinal, _, _, _, advance⟩ :=
    current_load_step currentMiddle loadDecoded nextEffective afLoad
  have valueEq : value = (before.registers .rdi).setWidth 32 := by
    apply Except.ok.inj
    exact observed.symm.trans (by rw [currentMiddle.coupled]; exact effect.readback)
  subst value
  refine ⟨evolved, middle, final, stored, actualStore, rfl, actualLoad, loadedReg,
    advance, currentFinal, ?_, readSuccess, ?_, effect.allocations, effect.loans, effect.outside⟩
  · exact ⟨rfl, rfl, allocation, _, authorized, fits, observed⟩
  · rw [currentFinal.coupled]
    exact currentFinal.contract.stack

private def pointerBytes : List Byte := [0x48, 0x89, 0xf8, 0x89, 0x30, 0xc3]

private theorem pointer_decoded {call : Call} {shared : Shared} {machine : State}
    (current : Current call shared machine) (codeBytes : call.bytes = pointerBytes)
    (offset : Nat) (inside : offset < pointerBytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState pointerBytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code pointerBytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code (by decide) offset inside machine rfl pc) literal

/-- Copy a full-width owned pointer to RAX, store through that actual copied
pointer, and return it. Current resources derive all three actual steps and
the same evolved OS world; no 32-bit pointer bound or future-step premise is used. -/
theorem checked_pointer_copy_store_return {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = pointerBytes)
    (entry : before.rip = call.code) (pointer : before.registers .rdi = call.targetPointer)
    (stack : before.registers .rsp = call.stack) (afCopy afStore afRet : Bool) :
    ∃ copied evolved written final,
      step afCopy before = .ok ⟨.next copied, []⟩ ∧
      copied.registers .rax = call.targetPointer ∧
      Borrowing.mutate shared (.store (Threads.principal call.worker) call.ticket
        call.targetPointer ((before.registers .rsi).setWidth 32)) = .ok (evolved, none) ∧
      step afStore copied = .ok ⟨.next written, []⟩ ∧
      step afRet written = .ok ⟨.returned final, [⟨.stack, call.stack, 8⟩]⟩ ∧
      final.registers .rax = call.targetPointer ∧ final.rip = call.returnAddress ∧
      final.registers .rsp = call.stack + 8 ∧ Current call evolved final ∧
      loadDWord final.memory call.targetPointer = .ok ((before.registers .rsi).setWidth 32) ∧
      Mutex.StoreEffect shared evolved call.targetPointer ((before.registers .rsi).setWidth 32) := by
  have copyDecoded := pointer_decoded current codeBytes 0 (by decide) (by simpa using entry)
    (instruction := .movReg64 .rax .rdi) (by cbv)
  obtain ⟨copied, actualCopy, currentCopy, assigned, other, _, _, advance⟩ :=
    current_movReg64_step current copyDecoded afCopy
  have copiedPointer : copied.registers .rax = call.targetPointer := assigned.trans pointer
  have copiedPC : copied.rip = call.code + 3 := by simpa [entry] using advance
  have storeDecoded := pointer_decoded currentCopy codeBytes 3 (by decide) copiedPC
    (instruction := .storeMem32 (.base .rax) .rsi) (by cbv)
  have source : copied.registers .rsi = before.registers .rsi := other .rsi (by decide)
  have intent : Sequential.Instruction.storeIntent (.storeMem32 (.base .rax) .rsi) copied =
      some (call.targetPointer, (before.registers .rsi).setWidth 32) := by
    simp [Sequential.Instruction.storeIntent, Address.eval, copiedPointer, source]
  obtain ⟨evolved, stored, actualStore, currentWritten, effect, _⟩ :=
    current_store_step currentCopy storeDecoded intent afStore
  let written := storeAfterLength copied evolved 2
  change step afStore copied = .ok ⟨.next written, []⟩ at actualStore
  change Current call evolved written at currentWritten
  have writtenPC : written.rip = call.code + 5 := by
    simp [written, storeAfterLength, copiedPC, BitVec.add_assoc]
  have retDecoded := pointer_decoded currentWritten codeBytes 5 (by decide) writtenPC
    (instruction := .legacy .ret) (by cbv)
  have stackBinding : written.registers .rsp = call.stack :=
    (other .rsp (by decide)).trans stack
  have ret := current_ret_step currentWritten retDecoded stackBinding afRet
  let final := returnAfter written call.returnAddress
  have currentFinal : Current call evolved final := ret.2.1
  refine ⟨copied, evolved, written, final, actualCopy, copiedPointer, stored, actualStore,
    ?_, ?_, rfl, ?_, currentFinal, ?_, effect⟩
  · simpa only [stackBinding] using ret.1
  · simpa [final, returnAfter, State.writeRegister, written, storeAfterLength] using copiedPointer
  · simp [final, returnAfter, State.writeRegister, stackBinding]
  · rw [currentFinal.coupled]
    exact effect.readback

end EDSL.Tests.SequentialMoveResources

#print axioms EDSL.OS.WordResources.actual_store_bridge
#print axioms EDSL.OS.WordResources.current_store_step
#print axioms EDSL.OS.WordResources.current_load_step
#print axioms EDSL.Tests.SequentialMoveResources.checked_sib_store_then_load_rsp
#print axioms EDSL.Tests.SequentialMoveResources.checked_pointer_copy_store_return

#audit_edsl
