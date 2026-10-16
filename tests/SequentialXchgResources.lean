/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.WordResources.Bridge
import EDSL.Grading.Write32.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.SequentialXchgResources
open EDSL EDSL.X86 EDSL.X86.Sequential EDSL.OS
open EDSL.OS.WordResources

private theorem exact_decoded {call : Call} {shared : Shared} {machine : State}
    {bytes : List Byte}
    (current : Current call shared machine) (codeBytes : call.bytes = bytes)
    (small : bytes.length ≤ 64)
    (offset : Nat) (inside : offset < bytes.length)
    (pc : machine.rip = call.code + BitVec.ofNat 64 offset)
    {instruction : Sequential.Instruction}
    (literal : Sequential.decodeAt (codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt machine = .ok instruction := by
  have code : CodeAt machine.memory call.code bytes := by
    rw [current.coupled, ← codeBytes]
    exact current.contract.code
  exact decodeAt_transport (code_fetch_transport code small offset inside machine rfl pc) literal

private def shortBytes : List Byte := [0x48, 0x94]

/-- Exchanging RAX with machine RSP preserves the original caller-slot
authority and all current RAM, while actually moving RSP away from that slot.
Current resources alone therefore cannot supply a later RET's stack binding. -/
theorem short_rsp_retains_original_loan {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = shortBytes)
    (entry : before.rip = call.code) (stack : before.registers .rsp = call.stack)
    (different : before.registers .rax ≠ call.stack) (af : Bool) :
    ∃ after,
      step af before = .ok ⟨.next after, []⟩ ∧
      after.registers .rsp ≠ call.stack ∧ after.registers .rax = call.stack ∧
      Current call shared after ∧
      Threads.HasLoan shared call.worker call.stackLoan ⟨call.stack, 8⟩ ∧
      readWord after.memory call.stack = .ok call.returnAddress ∧
      after.memory = before.memory ∧ after.flags = before.flags ∧
      after.rip = call.code + 2 := by
  have decoded := exact_decoded current codeBytes (by decide) 0 (by decide)
    (by simpa using entry) (instruction := .xchgRax64 .rsp) rfl
  obtain ⟨after, actual, currentAfter, raxValue, rspValue, _, memory, flags, pc⟩ :=
    current_xchgRax64_step current decoded af
  refine ⟨after, actual, ?_, raxValue.trans stack, currentAfter,
    currentAfter.contract.stackLoan, ?_, memory, flags, ?_⟩
  · simpa only [rspValue] using different
  · rw [currentAfter.coupled]
    exact currentAfter.contract.stack
  · simpa only [entry] using pc

-- XCHG RSP,R12 twice, ordinary STORE ESI,[RDI], RET. The first exchange
-- temporarily replaces the actual stack pointer with an arbitrary full64 word.
private def restoreBytes : List Byte :=
  [0x4c, 0x87, 0xe4, 0x4c, 0x87, 0xe4, 0x89, 0x37, 0xc3]

/-- The second actual exchange restores the caller binding. Checked mutation
then uses the original owner ticket, frames every live loan and returns through
the retained caller slot. No fixed target/stack address or 32-bit bound is used. -/
theorem double_rsp_exchange_store_return {call : Call} {shared : Shared} {before : State}
    (current : Current call shared before) (codeBytes : call.bytes = restoreBytes)
    (entry : before.rip = call.code) (stack : before.registers .rsp = call.stack)
    (different : before.registers .r12 ≠ call.stack)
    (pointer : before.registers .rdi = call.targetPointer)
    (afFirst afSecond afStore afRet : Bool) :
    ∃ first second evolved written final,
      step afFirst before = .ok ⟨.next first, []⟩ ∧
      first.registers .rsp = before.registers .r12 ∧
      first.registers .rsp ≠ call.stack ∧ first.registers .r12 = call.stack ∧
      Current call shared first ∧ first.memory = before.memory ∧ first.flags = before.flags ∧
      step afSecond first = .ok ⟨.next second, []⟩ ∧
      second.registers = before.registers ∧ second.flags = before.flags ∧
      Borrowing.mutate shared (.store (Threads.principal call.worker) call.ticket
        call.targetPointer ((before.registers .rsi).setWidth 32)) = .ok (evolved, none) ∧
      step afStore second = .ok ⟨.next written, []⟩ ∧
      step afRet written = .ok ⟨.returned final, [⟨.stack, call.stack, 8⟩]⟩ ∧
      final.registers .r12 = before.registers .r12 ∧
      final.registers .rsp = call.stack + 8 ∧ final.rip = call.returnAddress ∧
      Current call evolved final ∧
      loadDWord final.memory call.targetPointer = .ok ((before.registers .rsi).setWidth 32) ∧
      Mutex.StoreEffect shared evolved call.targetPointer ((before.registers .rsi).setWidth 32) ∧
      (∀ identifier loan, shared.loans identifier = some loan →
        ∀ query, loan.region.Contains query →
          evolved.resources.space.cells query = shared.resources.space.cells query) := by
  have firstDecoded := exact_decoded current codeBytes (by decide) 0 (by decide)
    (by simpa using entry) (instruction := .xchgReg64 .rsp .r12) rfl
  obtain ⟨first, actualFirst, currentFirst, firstRsp, firstR12, firstOther,
      firstMemory, firstFlags, firstPC⟩ :=
    current_xchgReg64_step current firstDecoded afFirst
  have firstEntry : first.rip = call.code + 3 := by simpa only [entry] using firstPC
  have secondDecoded := exact_decoded currentFirst codeBytes (by decide) 3 (by decide)
    firstEntry (instruction := .xchgReg64 .rsp .r12) rfl
  obtain ⟨second, actualSecond, currentSecond, secondRsp, secondR12, secondOther,
      _, secondFlags, secondPC⟩ :=
    current_xchgReg64_step currentFirst secondDecoded afSecond
  have registers : second.registers = before.registers := by
    funext register
    by_cases isRsp : register = .rsp
    · subst register
      exact secondRsp.trans firstR12
    · by_cases isR12 : register = .r12
      · subst register
        exact secondR12.trans firstRsp
      · exact (secondOther register isRsp isR12).trans (firstOther register isRsp isR12)
  have secondEntry : second.rip = call.code + 6 := by
    simpa [firstEntry, BitVec.add_assoc] using secondPC
  have storeDecoded := exact_decoded currentSecond codeBytes (by decide) 6 (by decide)
    secondEntry (instruction := .legacy .storeEsiRdi) rfl
  have intent : Sequential.Instruction.storeIntent (.legacy .storeEsiRdi) second =
      some (call.targetPointer, (before.registers .rsi).setWidth 32) := by
    simp [Sequential.Instruction.storeIntent, X86.Instruction.storeIntent, registers, pointer]
  obtain ⟨evolved, stored, actualStore, currentWritten, effect, loans⟩ :=
    current_store_step currentSecond storeDecoded intent afStore
  let written := storeAfterLength second evolved 2
  change step afStore second = .ok ⟨.next written, []⟩ at actualStore
  change Current call evolved written at currentWritten
  have writtenEntry : written.rip = call.code + 8 := by
    simp [written, storeAfterLength, secondEntry, BitVec.add_assoc]
  have retDecoded := exact_decoded currentWritten codeBytes (by decide) 8 (by decide)
    writtenEntry (instruction := .legacy .ret) rfl
  have stackBinding : written.registers .rsp = call.stack := by
    simpa only [written, storeAfterLength, registers] using stack
  have ret := current_ret_step currentWritten retDecoded stackBinding afRet
  let final := returnAfter written call.returnAddress
  have currentFinal : Current call evolved final := ret.2.1
  refine ⟨first, second, evolved, written, final, actualFirst, firstRsp, ?_, firstR12.trans stack,
    currentFirst, firstMemory, firstFlags, actualSecond, registers,
    secondFlags.trans firstFlags, stored, actualStore, ?_, ?_, ?_, rfl,
    currentFinal, ?_, effect, loans⟩
  · simpa only [firstRsp] using different
  · simpa only [stackBinding] using ret.1
  · simp [final, returnAfter, State.writeRegister, written, storeAfterLength, registers]
  · simp [final, returnAfter, State.writeRegister, stackBinding]
  · rw [currentFinal.coupled]
    exact effect.readback

/-- Nonvacuous resource admission uses independent argument data and a
noncanonical temporary RSP. Register-only exchange never dereferences it. -/
theorem admitted_restore_stores_and_returns (afFirst afSecond afStore afRet : Bool) :
    ∃ call shared before first second evolved written final,
      Current call shared before ∧
      step afFirst before = .ok ⟨.next first, []⟩ ∧
      canonical (first.registers .rsp) = false ∧
      step afSecond first = .ok ⟨.next second, []⟩ ∧
      second.registers .rsp = 65544 ∧
      step afStore second = .ok ⟨.next written, []⟩ ∧
      step afRet written = .ok ⟨.returned final, [⟨.stack, 65544, 8⟩]⟩ ∧
      final.registers .r12 = 0xfedcba9876543210 ∧
      final.registers .rsp = 65552 ∧ final.rip = 8192 ∧
      loadDWord final.memory 262144 = .ok 0x89abcdef ∧
      Current call evolved final ∧ evolved.loans = shared.loans := by
  let witness := Grading.Write32.Domain.candidate restoreBytes (by decide) (by decide)
  obtain ⟨first, second, evolved, written, final, actualFirst, firstRsp, _, _,
      _, _, _, actualSecond, registers, _, _, actualStore, actualRet,
      finalR12, finalRsp, finalPC, currentFinal, readback, effect, _⟩ :=
    double_rsp_exchange_store_return witness.current witness.raw.codeBytes witness.raw.entry
      witness.raw.stackPointer (by change (0xfedcba9876543210 : Word) ≠ 65544; decide)
      witness.raw.targetPointer afFirst afSecond afStore afRet
  refine ⟨witness.call, witness.shared, witness.initial, first, second, evolved, written, final,
    witness.current, actualFirst, ?_, actualSecond, ?_, actualStore, ?_, ?_, ?_, ?_,
    ?_, currentFinal, effect.loans⟩
  · rw [firstRsp]
    decide
  · rw [registers]
    rfl
  · simpa only [witness, Grading.Write32.Domain.candidate, Grading.Write32.Domain.call]
      using actualRet
  · exact finalR12
  · exact finalRsp
  · exact finalPC
  · have argument : (witness.initial.registers .rsi).setWidth 32 = (0x89abcdef : BitVec 32) :=
      by decide
    rw [argument] at readback
    exact readback

end EDSL.Tests.SequentialXchgResources

#print axioms EDSL.OS.WordResources.current_xchgReg64_step
#print axioms EDSL.OS.WordResources.current_xchgRax64_step
#print axioms EDSL.Tests.SequentialXchgResources.short_rsp_retains_original_loan
#print axioms EDSL.Tests.SequentialXchgResources.double_rsp_exchange_store_return
#print axioms EDSL.Tests.SequentialXchgResources.admitted_restore_stores_and_returns

#audit_edsl
