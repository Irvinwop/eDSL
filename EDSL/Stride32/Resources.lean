/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Stride32.Contract
import EDSL.OS.ArrayResources

namespace EDSL.Stride32
open X86

theorem inputReads_member {base : Word} {count : Nat} {read : Sequential.Read}
    (member : read ∈ inputReads base count) :
    read.kind = .data ∧ read.bytes = 4 ∧
      ∃ index, index < count ∧ read.address = base + BitVec.ofNat 64 (8 * index) := by
  obtain ⟨index, inside, same⟩ := List.mem_map.mp member
  subst read
  exact ⟨rfl, rfl, index, List.mem_range.mp inside, rfl⟩

theorem data_read_member {initial : State} {count index : Nat} (inside : index < count) :
    (⟨.data, initial.registers .rdi + BitVec.ofNat 64 (8 * index), 4⟩ : Sequential.Read) ∈
      operandReads initial count := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨index, List.mem_range.mpr inside, rfl⟩

theorem stack_read_member (initial : State) (count : Nat) :
    (⟨.stack, initial.registers .rsp, 8⟩ : Sequential.Read) ∈ operandReads initial count := by
  exact List.mem_append_right _ (by simp)

/-- Current full RAM coupling and current loans supply the machine precondition;
the hardware count denotes half the size of the contiguous logical array. -/
theorem pre_of_admission {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {initial : State} {count : Nat}
    (admitted : OS.ArrayResources.Admission shared call initial)
    (entry : initial.rip = call.code) (stack : initial.registers .rsp = call.stack)
    (base : initial.registers .rdi = call.base) (length : call.values.length = 2 * count)
    (counter : initial.registers .rsi = BitVec.ofNat 64 count) :
    Pre call.bytes initial call.values count call.target := by
  obtain ⟨code, returned, array⟩ := admitted.current
  refine ⟨?_, ?_, ?_, length, counter, ?_, admitted.resources.returnCanonical, ?_⟩
  · simpa only [entry] using code
  · simpa only [base] using array
  · simpa only [base] using admitted.resources.bound
  · simpa only [stack] using returned
  · simpa only [stack] using admitted.resources.postStackCanonical

/-- Each even-index operand is a full four-byte subregion of the current loan
for the original contiguous array. Empty input makes no input-loan request. -/
theorem inputReads_permission {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {count : Nat} (resources : OS.ArrayResources.Contract shared call)
    (length : call.values.length = 2 * count) {read : Sequential.Read}
    (member : read ∈ inputReads call.base count) :
    OS.ArrayResources.ReadPermission shared call.worker read := by
  obtain ⟨kind, width, index, inside, address⟩ := inputReads_member member
  apply OS.ArrayResources.arrayRead_permission resources
  refine ⟨kind, width, 2 * index, by omega, ?_⟩
  have product : 4 * (2 * index) = 8 * index := by omega
  simpa only [product] using address

theorem operandReads_permission {shared : OS.Borrowing.State} {call : OS.ArrayResources.Call}
    {initial : State} {count : Nat}
    (admitted : OS.ArrayResources.Admission shared call initial)
    (length : call.values.length = 2 * count)
    (base : initial.registers .rdi = call.base) (stack : initial.registers .rsp = call.stack)
    {read : Sequential.Read} (member : read ∈ operandReads initial count) :
    OS.ArrayResources.ReadPermission shared call.worker read := by
  rcases List.mem_append.mp member with data | returned
  · exact inputReads_permission admitted.resources length (by simpa only [base] using data)
  · have same : read = ⟨.stack, call.stack, 8⟩ := by simpa only [List.mem_singleton, stack] using returned
    subst read
    exact OS.ArrayResources.stackRead_permission admitted.resources

end EDSL.Stride32
