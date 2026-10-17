/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.Private
import EDSL.CallMemory64.Domain
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallMemory64Private
open X86 OS AddressSpace CallMemory64.Domain

private def savedAddress : Word := 65528
private def padAddress : Word := 65536

private theorem saved_slot (bytes : List Byte) :
    StackFrame.Slot (descriptor bytes).frame savedAddress := by
  change (65528 : Nat) ≤ 65528 ∧ 65528 + 8 ≤ 65544
  decide

private theorem pad_slot (bytes : List Byte) :
    StackFrame.Slot (descriptor bytes).frame padAddress := by
  change (65528 : Nat) ≤ 65536 ∧ 65536 + 8 ≤ 65544
  decide

private theorem pad_disjoint :
    Ownership.Disjoint (qwordRegion padAddress) (qwordRegion savedAddress) := by decide

/-- This starts in the real checked allocation/initialization domain, saves an
arbitrary full64 word, overwrites DATA, writes the adjacent private pad, and
overwrites DATA again. The independent final reads must retain the saved word,
the latest DATA value and the pad simultaneously in one current world. -/
theorem saved_through_mixed_stores (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old saved firstData padding lastData : Word) :
    Borrowing.mutate (CallStack.Domain.shared bytes)
        (.allocate (descriptor bytes).owner region readWrite) =
      .ok (allocatedShared bytes, some (ticket bytes)) ∧
    ∃ savedWorld dataWorld padWorld finalWorld,
      Borrowing.mutate (shared bytes old)
        (.store64 (descriptor bytes).owner (descriptor bytes).frame.ticket savedAddress saved) =
          .ok (savedWorld, none) ∧
      Borrowing.mutate savedWorld
        (.store64 (descriptor bytes).owner (ticket bytes) target firstData) =
          .ok (dataWorld, none) ∧
      Borrowing.mutate dataWorld
        (.store64 (descriptor bytes).owner (descriptor bytes).frame.ticket padAddress padding) =
          .ok (padWorld, none) ∧
      Borrowing.mutate padWorld
        (.store64 (descriptor bytes).owner (ticket bytes) target lastData) =
          .ok (finalWorld, none) ∧
      CallMemory64.Current (descriptor bytes) finalWorld
        (StackFrame.recouple (initial ⟨bytes, 0⟩ 0 old) finalWorld) ∧
      CallMemory64.Preservation (descriptor bytes) savedWorld finalWorld ∧
      readWord (toMemory finalWorld.resources.space) savedAddress = .ok saved ∧
      Borrowing.loadOwnedWord64 finalWorld (descriptor bytes).owner
        (descriptor bytes).frame.ticket savedAddress = .ok saved ∧
      readWord (toMemory finalWorld.resources.space) target = .ok lastData ∧
      readWord (toMemory finalWorld.resources.space) padAddress = .ok padding := by
  have start := current ⟨bytes, 0⟩ positive bound 0 old
  obtain ⟨savedWorld, save, savedCurrent, _, _, _, savedRead⟩ :=
    start.private_store64 (saved_slot bytes) saved
  obtain ⟨dataWorld, data1, dataCurrent, dataWrite, dataEffect, _, _⟩ :=
    savedCurrent.data_store64 firstData
  obtain ⟨padWorld, pad, padCurrent, padWrite, padEffect, _, padRead⟩ :=
    dataCurrent.private_store64 (pad_slot bytes) padding
  obtain ⟨finalWorld, data2, finalCurrent, lastWrite, lastEffect, _, finalData⟩ :=
    padCurrent.data_store64 lastData
  have history : CallMemory64.History (descriptor bytes) savedWorld finalWorld :=
    .next dataWrite (.next padWrite (.next lastWrite .refl))
  have excludes : history.Excludes savedAddress :=
    .next (.data data1) (.next (.privateSlot (pad_slot bytes) pad pad_disjoint)
      (.next (.data data2) .refl))
  have savedFinal := (history.preserves_private savedCurrent finalCurrent
    (saved_slot bytes) excludes).trans savedRead
  have directData := CallMemory64.data_preserves_private savedCurrent dataCurrent
    dataEffect (saved_slot bytes)
  have directPrivate := CallMemory64.store64_preserves_private dataCurrent padCurrent
    padEffect (saved_slot bytes) pad_disjoint
  have directFinal := (CallMemory64.data_preserves_private padCurrent finalCurrent
    lastEffect (saved_slot bytes)).trans (directPrivate.trans (directData.trans savedRead))
  have padFinal := (CallMemory64.data_preserves_private padCurrent finalCurrent
    lastEffect (pad_slot bytes)).trans padRead
  obtain ⟨observed, owned, observedRead, _⟩ :=
    (StackFrame.PresentSlot.mk finalCurrent.contract.stack (saved_slot bytes)).read
  have same : observed = saved := Except.ok.inj (observedRead.symm.trans directFinal)
  subst observed
  exact ⟨allocated bytes positive bound, savedWorld, dataWorld, padWorld, finalWorld,
    save, data1, pad, data2, finalCurrent, history.preserves, savedFinal, owned, finalData, padFinal⟩

/-- A start inside the private frame is insufficient: shifting the last full
slot by one byte crosses into the original caller word, and both checked gates
reject it for arbitrary contents. The caller loan is a separate allocation. -/
theorem private_boundary_rejected (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old value : Word) :
    (descriptor bytes).frame.region.Contains (padAddress + 1#64) ∧
      ¬StackFrame.Slot (descriptor bytes).frame (padAddress + 1#64) ∧
      Borrowing.loadOwnedWord64 (shared bytes old) (descriptor bytes).owner
        (descriptor bytes).frame.ticket (padAddress + 1#64) = .error .outsideAllocation ∧
      Borrowing.mutate (shared bytes old)
        (.store64 (descriptor bytes).owner (descriptor bytes).frame.ticket
          (padAddress + 1#64) value) = .error (.ownership .outsideAllocation) := by
  have present := contract bytes positive bound old
  obtain ⟨allocation, authorized, regionEq⟩ := present.stack.allocation
  change Ownership.authorize (shared bytes old).resources (descriptor bytes).owner
    (descriptor bytes).frame.ticket = .ok allocation at authorized
  have crosses : Ownership.containsQWord allocation (padAddress + 1#64) = false := by
    unfold Ownership.containsQWord
    apply decide_eq_false_iff_not.mpr
    intro fits
    rw [regionEq] at fits
    change (65528 : Nat) ≤ 65537 ∧ 65537 + 8 ≤ 65544 at fits
    omega
  have allowed := Borrowing.unborrowed64 _ (descriptor bytes).owner
    (descriptor bytes).frame.ticket (padAddress + 1#64) value present.stack.unborrowed
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (65528 : Nat) ≤ 65537 ∧ 65537 < 65544
    decide
  · change ¬((65528 : Nat) ≤ 65537 ∧ 65537 + 8 ≤ 65544)
    decide
  · simp [Borrowing.loadOwnedWord64, Ownership.loadWord64, authorized, crosses, Except.mapError]
  · simp [Borrowing.mutate, allowed, Ownership.Mutation.run, Ownership.storeWord64,
      authorized, crosses, Except.map, Except.mapError]

/-- A legal unaligned private write can start elsewhere and still overlap seven
saved bytes. Actual checked stores produce the independently specified mixed
word, demonstrating why per-write whole-word exclusion is necessary. -/
theorem partial_overlap_changes_saved (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) :
    ∃ savedWorld finalWorld,
      Borrowing.mutate (shared bytes old)
        (.store64 (descriptor bytes).owner (descriptor bytes).frame.ticket savedAddress 0) =
          .ok (savedWorld, none) ∧
      Borrowing.mutate savedWorld
        (.store64 (descriptor bytes).owner (descriptor bytes).frame.ticket
          (savedAddress + 1#64) 0xffffffffffffffff) = .ok (finalWorld, none) ∧
      CallMemory64.Contract (descriptor bytes) finalWorld ∧
      ¬Ownership.Disjoint (qwordRegion (savedAddress + 1#64)) (qwordRegion savedAddress) ∧
      readWord (toMemory finalWorld.resources.space) savedAddress = .ok 0xffffffffffffff00 := by
  have start := current ⟨bytes, 0⟩ positive bound 0 old
  obtain ⟨savedWorld, save, savedCurrent, _, saveEffect, _, _⟩ :=
    start.private_store64 (saved_slot bytes) 0
  have shifted : StackFrame.Slot (descriptor bytes).frame (savedAddress + 1#64) := by
    change (65528 : Nat) ≤ 65529 ∧ 65529 + 8 ≤ 65544
    decide
  obtain ⟨finalWorld, overlap, finalCurrent, _, overlapEffect, _, _⟩ :=
    savedCurrent.private_store64 shifted 0xffffffffffffffff
  refine ⟨savedWorld, finalWorld, save, overlap, finalCurrent.contract, by decide, ?_⟩
  rw [overlapEffect.projection, saveEffect.projection]
  simp [readWord, readStackByte, writeQWordUnchecked, storedQWordByte, savedAddress, canonical]

end EDSL.Tests.CallMemory64Private

#print axioms EDSL.OS.CallMemory64.Contract.private_valid
#print axioms EDSL.OS.CallMemory64.data_preserves_private_cells
#print axioms EDSL.OS.CallMemory64.store64_preserves_disjoint_cells
#print axioms EDSL.OS.CallMemory64.data_preserves_private
#print axioms EDSL.OS.CallMemory64.store64_preserves_private
#print axioms EDSL.OS.CallMemory64.History.excludes_trans
#print axioms EDSL.OS.CallMemory64.Write.preserves_private_cells
#print axioms EDSL.OS.CallMemory64.History.preserves_private_cells
#print axioms EDSL.OS.CallMemory64.History.preserves_private
#print axioms EDSL.Tests.CallMemory64Private.saved_through_mixed_stores
#print axioms EDSL.Tests.CallMemory64Private.private_boundary_rejected
#print axioms EDSL.Tests.CallMemory64Private.partial_overlap_changes_saved
#audit_edsl
