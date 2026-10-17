/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.Domain
import EDSL.X86.CallReturn.Decode
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallMemory64Domain
open X86 OS OS.AddressSpace CallMemory64.Domain

/-- Existing readable DATA bytes do not bypass present owner or epoch checks.
The world, code window and full64 initialized value are arbitrary. -/
theorem authority_failures (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old : Word) :
    Borrowing.loadOwnedWord64 (shared bytes old) 12 (ticket bytes) target =
        .error (.authority .wrongOwner) ∧
      Borrowing.loadOwnedWord64 (shared bytes old) (descriptor bytes).owner
        ⟨(ticket bytes).identifier, 1⟩ target = .error (.authority .staleEpoch) := by
  have found := target_allocation bytes positive bound old
  have wrong : (descriptor bytes).owner ≠ 12 := by change 11 ≠ 12; decide
  constructor <;>
    simp [Borrowing.loadOwnedWord64, Ownership.loadWord64, Ownership.authorize,
      found, wrong, show (ticket bytes).epoch = 0 from rfl, Except.mapError]

/-- Starting one byte into DATA is inside its allocation, but the complete
qword overflows it. Both actual owner observation and checked mutation reject
the operand before a machine read/write, for every stored full64 value. -/
theorem full_word_boundary (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old value : Word) :
    region.Contains (target + 1#64) ∧
      Borrowing.loadOwnedWord64 (shared bytes old) (descriptor bytes).owner (ticket bytes)
        (target + 1#64) = .error .outsideAllocation ∧
      Borrowing.mutate (shared bytes old)
        (.store64 (descriptor bytes).owner (ticket bytes) (target + 1#64) value) =
        .error (.ownership .outsideAllocation) := by
  have authorized := Ownership.authorize_success _ _ _ _
    (target_allocation bytes positive bound old) rfl rfl
  have crosses : Ownership.containsQWord ⟨(descriptor bytes).owner, 0, region⟩ (target + 1#64) =
      false := by change Ownership.containsQWord ⟨11, 0, region⟩ (target + 1#64) = false; decide
  have allowed := Borrowing.unborrowed64 _ (descriptor bytes).owner (ticket bytes)
    (target + 1#64) value (contract bytes positive bound old).unborrowed
  refine ⟨by decide, ?_, ?_⟩
  · simp [Borrowing.loadOwnedWord64, Ownership.loadWord64, authorized, crosses, Except.mapError]
  · simp [Borrowing.mutate, allowed, Ownership.Mutation.run, Ownership.storeWord64,
      authorized, crosses, Except.map, Except.mapError]

/-- The real private ticket 4 cannot acquire the readable DATA qword at ticket
5. This exercises both gates in the shared allocation sequence, rather than
checking only two descriptor constants for inequality. -/
theorem distinct_authority (bytes : List Byte) (positive : 0 < bytes.length)
    (bound : bytes.length ≤ 4096) (old value : Word) :
    Borrowing.loadOwnedWord64 (shared bytes old) (descriptor bytes).owner
        (descriptor bytes).frame.ticket target = .error .outsideAllocation ∧
      Borrowing.mutate (shared bytes old)
        (.store64 (descriptor bytes).owner (descriptor bytes).frame.ticket target value) =
        .error (.ownership .outsideAllocation) := by
  have current := contract bytes positive bound old
  obtain ⟨allocation, authorized, regionEq⟩ := current.stack.allocation
  change Ownership.authorize (shared bytes old).resources (descriptor bytes).owner
    (descriptor bytes).frame.ticket = .ok allocation at authorized
  have outside : Ownership.containsQWord allocation target = false := by
    unfold Ownership.containsQWord
    apply decide_eq_false_iff_not.mpr
    intro fits
    rw [regionEq] at fits
    change (65528 : Nat) ≤ 262144 ∧ 262144 + 8 ≤ 65544 at fits
    omega
  have allowed := Borrowing.unborrowed64 _ (descriptor bytes).owner
    (descriptor bytes).frame.ticket target value current.stack.unborrowed
  constructor
  · simp [Borrowing.loadOwnedWord64, Ownership.loadWord64, authorized, outside, Except.mapError]
  · simp [Borrowing.mutate, allowed, Ownership.Mutation.run, Ownership.storeWord64,
      authorized, outside, Except.map, Except.mapError]

def lastEntry : CallStack.Program := ⟨List.replicate 4096 0xff, 4095⟩

/-- The largest window and final entry fetch their actual selected byte from
the fully initialized world. DATA initialization retains the entire code loan,
and unsupported bytes still admit resources independently of decoding. -/
theorem last_entry_admitted (input old : Word) (registers : Register → Word) (flags : Word) :
    OS.CallMemory64.Current (descriptor lastEntry.bytes) (shared lastEntry.bytes old)
        (initial lastEntry input old registers flags) ∧
      fetchByte (initial lastEntry input old registers flags).memory
        (initial lastEntry input old registers flags).rip = .ok 0xff ∧
      X86.CallReturn.decodeAt (initial lastEntry input old registers flags) =
        .error (.unsupportedOpcode 0xff) := by
  have entry : lastEntry.entry < lastEntry.bytes.length := by
    simp only [lastEntry, List.length_replicate]
    decide
  have bound : lastEntry.bytes.length ≤ 4096 := by
    simp only [lastEntry, List.length_replicate, Nat.le_refl]
  have admitted := current lastEntry entry bound input old registers flags
  have fetched : fetchByte (initial lastEntry input old registers flags).memory
      (initial lastEntry input old registers flags).rip = .ok 0xff :=
    admitted.contract.stack.pureCall.code.2 4095 0xff
      (List.getElem?_replicate_of_lt (by decide))
  refine ⟨admitted, fetched, ?_⟩
  have legacy : X86.decodeAt (initial lastEntry input old registers flags) =
      .error (.unsupportedOpcode 0xff) := by
    rw [X86.decodeAt, fetched]
    rfl
  have sequential : Sequential.decodeAt (initial lastEntry input old registers flags) =
      .error (.unsupportedOpcode 0xff) := by
    simp only [Sequential.decodeAt, legacy]
    unfold Sequential.decodeNewAt
    rw [fetched]
    rfl
  simp only [X86.CallReturn.decodeAt, sequential]
  unfold X86.CallReturn.decodeNewAt
  rw [fetched]
  rfl

end EDSL.Tests.CallMemory64Domain

#print axioms EDSL.CallMemory64.Domain.allocated
#print axioms EDSL.CallMemory64.Domain.initialized
#print axioms EDSL.CallMemory64.Domain.original_allocation
#print axioms EDSL.CallMemory64.Domain.loan_cells_preserved
#print axioms EDSL.CallMemory64.Domain.owned_read_iff
#print axioms EDSL.CallMemory64.Domain.current
#print axioms EDSL.Tests.CallMemory64Domain.authority_failures
#print axioms EDSL.Tests.CallMemory64Domain.full_word_boundary
#print axioms EDSL.Tests.CallMemory64Domain.distinct_authority
#print axioms EDSL.Tests.CallMemory64Domain.last_entry_admitted
#audit_edsl
