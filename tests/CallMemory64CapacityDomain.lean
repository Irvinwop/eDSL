/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.CapacityDomain
import EDSL.X86.CallReturn.Decode
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallMemory64CapacityDomain
open X86 OS OS.AddressSpace CallMemory64.CapacityDomain

/-- Every complete start in the 32-byte interval admits an actual arbitrary
full64 store. In particular depths 8, 16, 24 and 32 cover all four saved/CALL
slots; unaligned depths are checked too. DATA and the loaded original caller
word survive in the same current world, with the complete symbolic code loan. -/
theorem every_depth_store (program : CallStack.Program)
    (entry : program.entry < program.bytes.length) (bound : program.bytes.length ≤ 4096)
    (input old value : Word) (registers : Register → Word) (flags : Word)
    (depth : Nat) (minimum : 8 ≤ depth) (maximum : depth ≤ 32) :
    ∃ evolved,
      Borrowing.mutate (shared 32 program.bytes old)
        (.store64 (descriptor 32 program.bytes).owner (descriptor 32 program.bytes).frame.ticket
          ((descriptor 32 program.bytes).frame.top - BitVec.ofNat 64 depth) value) =
        .ok (evolved, none) ∧
      Borrowing.loadOwnedWord64 evolved (descriptor 32 program.bytes).owner
        (descriptor 32 program.bytes).frame.ticket
        ((descriptor 32 program.bytes).frame.top - BitVec.ofNat 64 depth) = .ok value ∧
      Borrowing.loadOwnedWord64 evolved (descriptor 32 program.bytes).owner
        (ticket 32 program.bytes) target = .ok old ∧
      readWord (toMemory evolved.resources.space) 65544 = .ok 8192 ∧
      CodeAt (toMemory evolved.resources.space) 4096 program.bytes ∧
      OS.CallMemory64.Current (descriptor 32 program.bytes) evolved
        (StackFrame.recouple (initialCPU 32 program input old registers flags) evolved) := by
  have start := current 32 CallStack.CapacityDomain.supported32
    program entry bound input old registers flags
  have slot := CallStack.private_slot_at_depth start.contract.stack minimum maximum
  obtain ⟨evolved, stored, afterStore, _, _, readback, _⟩ := start.private_store64 slot value
  exact ⟨evolved, stored, readback,
    OS.CallMemory64.private_store64_preserves_data start.contract slot stored
      (target_read 32 CallStack.CapacityDomain.supported32 program.bytes (by omega) bound old).1,
    afterStore.contract.stack.pureCall.stack, afterStore.contract.stack.pureCall.code, afterStore⟩

/-- Exercise each of the four literal qword starts through the checked gate;
the independent list would catch a shifted base or accidental 16-byte frame. -/
theorem four_slots (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old value address : Word)
    (member : address ∈ ([65512, 65520, 65528, 65536] : List Word)) :
    ∃ evolved, Borrowing.mutate (shared 32 bytes old)
      (.store64 (descriptor 32 bytes).owner (descriptor 32 bytes).frame.ticket address value) =
        .ok (evolved, none) ∧
      Borrowing.loadOwnedWord64 evolved (descriptor 32 bytes).owner
        (descriptor 32 bytes).frame.ticket address = .ok value := by
  have slot : StackFrame.Slot (descriptor 32 bytes).frame address := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · change (65512 : Nat) ≤ (65512 : Word).toNat ∧ (65512 : Word).toNat + 8 ≤ 65544
      decide
    · change (65512 : Nat) ≤ (65520 : Word).toNat ∧ (65520 : Word).toNat + 8 ≤ 65544
      decide
    · change (65512 : Nat) ≤ (65528 : Word).toNat ∧ (65528 : Word).toNat + 8 ≤ 65544
      decide
    · change (65512 : Nat) ≤ (65536 : Word).toNat ∧ (65536 : Word).toNat + 8 ≤ 65544
      decide
  obtain ⟨evolved, stored⟩ :=
    (contract 32 CallStack.CapacityDomain.supported32 bytes positive bound old).private_store64_enabled
      slot value
  exact ⟨evolved, stored, Borrowing.store64_owned_readback stored⟩

private theorem disjoint_qwords (writer reader : Word)
    (writerValid : (qwordRegion writer).valid = true)
    (readerValid : (qwordRegion reader).valid = true)
    (separate : Ownership.Disjoint (qwordRegion writer) (qwordRegion reader)) :
    QWordDisjoint writer reader 8 := by
  have limit := (of_decide_eq_true writerValid).2.1
  have noWrap : writer.toNat + 7 < 2^64 := by
    change writer.toNat + 8 ≤ 2^64 at limit
    omega
  intro offset bound
  have inside : (qwordRegion reader).Contains (reader + BitVec.ofNat 64 offset) :=
    Ownership.addresses_inside _ readerValid _
      (List.mem_map.mpr ⟨offset, List.mem_range.mpr bound, rfl⟩)
  have outside := Ownership.disjoint_outside separate inside
  have notSmall : ¬((reader + BitVec.ofNat 64 offset) - writer).toNat < 8 := by
    intro small
    exact outside ((qword_contains_iff writer _ noWrap).mpr small)
  omega

/-- Four actual alternating private/DATA writes retain arbitrary saved words,
read back the first DATA value across the intervening private write, then read
the replacement value in the final current world. Original code and caller RAM
are transported by checked history, rather than installed as expected fixtures. -/
theorem alternating_writes (program : CallStack.Program)
    (entry : program.entry < program.bytes.length) (bound : program.bytes.length ≤ 4096)
    (input old savedLow savedHigh firstData lastData : Word)
    (registers : Register → Word) (flags : Word) :
    ∃ one two three four,
      Borrowing.mutate (shared 32 program.bytes old)
        (.store64 (descriptor 32 program.bytes).owner (descriptor 32 program.bytes).frame.ticket
          65512 savedLow) = .ok (one, none) ∧
      Borrowing.mutate one (.store64 (descriptor 32 program.bytes).owner
        (ticket 32 program.bytes) target firstData) = .ok (two, none) ∧
      Borrowing.mutate two (.store64 (descriptor 32 program.bytes).owner
        (descriptor 32 program.bytes).frame.ticket 65536 savedHigh) = .ok (three, none) ∧
      Borrowing.mutate three (.store64 (descriptor 32 program.bytes).owner
        (ticket 32 program.bytes) target lastData) = .ok (four, none) ∧
      Borrowing.loadOwnedWord64 two (descriptor 32 program.bytes).owner
        (descriptor 32 program.bytes).frame.ticket 65512 = .ok savedLow ∧
      Borrowing.loadOwnedWord64 three (descriptor 32 program.bytes).owner
        (ticket 32 program.bytes) target = .ok firstData ∧
      Borrowing.loadOwnedWord64 four (descriptor 32 program.bytes).owner
        (descriptor 32 program.bytes).frame.ticket 65512 = .ok savedLow ∧
      Borrowing.loadOwnedWord64 four (descriptor 32 program.bytes).owner
        (descriptor 32 program.bytes).frame.ticket 65536 = .ok savedHigh ∧
      Borrowing.loadOwnedWord64 four (descriptor 32 program.bytes).owner
        (ticket 32 program.bytes) target = .ok lastData ∧
      readWord (toMemory four.resources.space) 65544 = .ok 8192 ∧
      CodeAt (toMemory four.resources.space) 4096 program.bytes ∧
      OS.CallMemory64.Current (descriptor 32 program.bytes) four
        (StackFrame.recouple (initialCPU 32 program input old registers flags) four) ∧
      OS.CallMemory64.History (descriptor 32 program.bytes) (shared 32 program.bytes old) four := by
  have start := current 32 CallStack.CapacityDomain.supported32
    program entry bound input old registers flags
  have lowSlot : StackFrame.Slot (descriptor 32 program.bytes).frame 65512 := by
    change (65512 : Nat) ≤ (65512 : Word).toNat ∧ (65512 : Word).toNat + 8 ≤ 65544
    decide
  have highSlot : StackFrame.Slot (descriptor 32 program.bytes).frame 65536 := by
    change (65512 : Nat) ≤ (65536 : Word).toNat ∧ (65536 : Word).toNat + 8 ≤ 65544
    decide
  obtain ⟨one, storedOne, currentOne, _, _, lowOne, _⟩ := start.private_store64 lowSlot savedLow
  obtain ⟨two, storedTwo, currentTwo, _, _, dataTwo, _⟩ := currentOne.data_store64 firstData
  have lowTwo := Borrowing.store64_preserves_owned_read storedTwo lowOne
    (disjoint_qwords target 65512 (by decide) (by decide) (by decide))
  obtain ⟨three, storedThree, currentThree, _, _, highThree, _⟩ :=
    currentTwo.private_store64 highSlot savedHigh
  have lowThree := Borrowing.store64_preserves_owned_read storedThree lowTwo
    (disjoint_qwords 65536 65512 (by decide) (by decide) (by decide))
  have dataThree := OS.CallMemory64.private_store64_preserves_data
    currentTwo.contract highSlot storedThree dataTwo
  obtain ⟨four, storedFour, currentFour, _, _, dataFour, _⟩ := currentThree.data_store64 lastData
  have lowFour := Borrowing.store64_preserves_owned_read storedFour lowThree
    (disjoint_qwords target 65512 (by decide) (by decide) (by decide))
  have highFour := Borrowing.store64_preserves_owned_read storedFour highThree
    (disjoint_qwords target 65536 (by decide) (by decide) (by decide))
  have history : OS.CallMemory64.History (descriptor 32 program.bytes)
      (shared 32 program.bytes old) four :=
    .next (.privateSlot lowSlot storedOne) (.next (.data storedTwo)
      (.next (.privateSlot highSlot storedThree) (.next (.data storedFour) .refl)))
  exact ⟨one, two, three, four, storedOne, storedTwo, storedThree, storedFour,
    lowTwo, dataThree, lowFour, highFour, dataFour, currentFour.contract.stack.pureCall.stack,
    currentFour.contract.stack.pureCall.code, ⟨currentFour.contract, rfl⟩, history⟩

/-- One byte beyond the last private qword start is still inside the private
region, but its complete operand reaches the immutable original caller slot.
Both owner read and checked mutation reject it for arbitrary code/data/value. -/
theorem private_boundary (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old value : Word) :
    (descriptor 32 bytes).frame.region.Contains 65537 ∧
      Borrowing.loadOwnedWord64 (shared 32 bytes old) (descriptor 32 bytes).owner
        (descriptor 32 bytes).frame.ticket 65537 = .error .outsideAllocation ∧
      Borrowing.mutate (shared 32 bytes old) (.store64 (descriptor 32 bytes).owner
        (descriptor 32 bytes).frame.ticket 65537 value) =
          .error (.ownership .outsideAllocation) := by
  have present := contract 32 CallStack.CapacityDomain.supported32 bytes positive bound old
  obtain ⟨allocation, authorized, region⟩ := present.stack.allocation
  change Ownership.authorize (shared 32 bytes old).resources (descriptor 32 bytes).owner
    (descriptor 32 bytes).frame.ticket = .ok allocation at authorized
  have crosses : Ownership.containsQWord allocation 65537 = false := by
    simp only [Ownership.containsQWord, region]
    change decide ((65512 : Nat) ≤ (65537 : Word).toNat ∧
      (65537 : Word).toNat + 8 ≤ 65544) = false
    decide
  simp only [BitVec.ofNat_eq_ofNat] at crosses
  have allowed := Borrowing.unborrowed64 _ (descriptor 32 bytes).owner
    (descriptor 32 bytes).frame.ticket 65537 value present.stack.unborrowed
  refine ⟨?_, ?_, ?_⟩
  · change (65512 : Nat) ≤ (65537 : Word).toNat ∧ (65537 : Word).toNat < 65544
    decide
  · unfold Borrowing.loadOwnedWord64 Ownership.loadWord64
    rw [authorized]
    simp [crosses, Except.mapError]
  · unfold Borrowing.mutate
    rw [allowed]
    simp [Ownership.Mutation.run, Ownership.storeWord64, authorized, crosses,
      Except.map, Except.mapError]

/-- Attempting to allocate DATA8 a second time reaches the actual mapping
overlap check; the fresh frontier does not authorize replacing live cells. -/
theorem allocation_collision (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) :
    Ownership.allocate (shared 32 bytes old).resources (descriptor 32 bytes).owner region readWrite =
      .error (.addressSpace .overlap) ∧
      Borrowing.mutate (shared 32 bytes old) (.allocate (descriptor 32 bytes).owner region readWrite) =
        .error (.ownership (.addressSpace .overlap)) := by
  have present := contract 32 CallStack.CapacityDomain.supported32 bytes positive bound old
  have occupied : allUnmapped (shared 32 bytes old).resources.space region ≠ true := by
    intro free
    have missing := allUnmapped_inside _ _ free target (by decide)
    obtain ⟨allocation, foundAllocation, _, _, fits, _⟩ := present.word
    have inside := Ownership.containsQWord_inside allocation target target fits (by decide)
    obtain ⟨cell, found⟩ := (present.wellFormed.1.1 _ _ foundAllocation).2.2 target inside
    rw [found] at missing
    cases missing
  have fresh := Ownership.fresh_identity _ present.wellFormed.1
  have rejected : Ownership.allocate (shared 32 bytes old).resources
      (descriptor 32 bytes).owner region readWrite = .error (.addressSpace .overlap) := by
    simp [Ownership.allocate, fresh, AddressSpace.map, show region.valid = true by decide,
      show readWrite.supported = true by decide, occupied, Except.mapError]
  have allowed : Borrowing.allowed (shared 32 bytes old)
      (.allocate (descriptor 32 bytes).owner region readWrite) = true := by
    apply List.all_eq_true.mpr
    intro identifier _
    cases (shared 32 bytes old).loans identifier <;> rfl
  exact ⟨rejected, by simp [Borrowing.mutate, allowed, Ownership.Mutation.run, rejected,
    Except.map, Except.mapError]⟩

def lastEntry : CallStack.Program := ⟨List.replicate 4096 0xff, 4095⟩

/-- Maximal code and capacity bounds, last-byte entry, arbitrary old DATA,
registers and flags are admitted. Fetch/decode observe the actual endpoint
memory; unsupported execution remains separate from resource admission. -/
theorem maximal_admission (input old : Word) (registers : Register → Word) (flags : Word) :
    CallMemory64.ResourcePre lastEntry (resource 4096 lastEntry input old)
        (initialCPU 4096 lastEntry input old registers flags) ∧
      fetchByte (initialCPU 4096 lastEntry input old registers flags).memory
        (initialCPU 4096 lastEntry input old registers flags).rip = .ok 0xff ∧
      X86.CallReturn.decodeAt (initialCPU 4096 lastEntry input old registers flags) =
        .error (.unsupportedOpcode 0xff) := by
  have entry : lastEntry.entry < lastEntry.bytes.length := by
    simp only [lastEntry, List.length_replicate]
    decide
  have bound : lastEntry.bytes.length ≤ 4096 := by
    simp only [lastEntry, List.length_replicate, Nat.le_refl]
  have pre := resource_pre 4096 (by decide) (by decide)
    lastEntry entry bound input old registers flags
  have fetched : fetchByte (initialCPU 4096 lastEntry input old registers flags).memory
      (initialCPU 4096 lastEntry input old registers flags).rip = .ok 0xff :=
    pre.current.contract.stack.pureCall.code.2 4095 0xff
      (List.getElem?_replicate_of_lt (by decide))
  refine ⟨pre, fetched, ?_⟩
  have legacy : X86.decodeAt (initialCPU 4096 lastEntry input old registers flags) =
      .error (.unsupportedOpcode 0xff) := by
    rw [X86.decodeAt, fetched]
    rfl
  have sequential : Sequential.decodeAt (initialCPU 4096 lastEntry input old registers flags) =
      .error (.unsupportedOpcode 0xff) := by
    simp only [Sequential.decodeAt, legacy]
    unfold Sequential.decodeNewAt
    rw [fetched]
    rfl
  simp only [X86.CallReturn.decodeAt, sequential]
  unfold X86.CallReturn.decodeNewAt
  rw [fetched]
  rfl

end EDSL.Tests.CallMemory64CapacityDomain

#print axioms EDSL.OS.Borrowing.transportStackContract
#print axioms EDSL.CallStack.CapacityDomain.private_bounds
#print axioms EDSL.CallStack.CapacityDomain.private_separate
#print axioms EDSL.CallStack.CapacityDomain.allocated
#print axioms EDSL.CallStack.CapacityDomain.contract
#print axioms EDSL.CallMemory64.CapacityDomain.allocated
#print axioms EDSL.CallMemory64.CapacityDomain.initialized
#print axioms EDSL.CallMemory64.CapacityDomain.original_allocation
#print axioms EDSL.CallMemory64.CapacityDomain.stack_contract
#print axioms EDSL.CallMemory64.CapacityDomain.loan_cells_preserved
#print axioms EDSL.CallMemory64.CapacityDomain.owned_read_iff
#print axioms EDSL.CallMemory64.CapacityDomain.resource_pre
#print axioms EDSL.Tests.CallMemory64CapacityDomain.every_depth_store
#print axioms EDSL.Tests.CallMemory64CapacityDomain.four_slots
#print axioms EDSL.Tests.CallMemory64CapacityDomain.alternating_writes
#print axioms EDSL.Tests.CallMemory64CapacityDomain.private_boundary
#print axioms EDSL.Tests.CallMemory64CapacityDomain.allocation_collision
#print axioms EDSL.Tests.CallMemory64CapacityDomain.maximal_admission
#audit_edsl
