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
  simp [Sequential.decodeAt, X86.decodeAt, b0, b1, b2, decodeNewAt,
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
  simp [Sequential.decodeAt, X86.decodeAt, b0, b1, b2, decodeNewAt,
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

end EDSL.Tests.SequentialMoveResources

#print axioms EDSL.OS.WordResources.actual_store_bridge
#print axioms EDSL.OS.WordResources.current_store_step
#print axioms EDSL.OS.WordResources.current_load_step
#print axioms EDSL.Tests.SequentialMoveResources.checked_sib_store_then_load_rsp

#audit_edsl
