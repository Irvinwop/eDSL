/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallStack.Domain
import EDSL.X86.CallReturn.Decode
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallStackDomain
open X86 OS OS.AddressSpace CallStack CallStack.Domain

/-- At every one of the nine contained starts, actual OS stores of arbitrary
full64 values are enabled by the constructed domain. Owner readback and the
original code/caller resources survive. No CPU execution is asserted. -/
theorem every_depth_store (program : Program)
    (entry : program.entry < program.bytes.length) (bound : program.bytes.length ≤ 4096)
    (argument value : Word) (registers : Register → Word) (flags : Word)
    (depth : Nat) (minimum : 8 ≤ depth) (maximum : depth ≤ 16) :
    ∃ evolved,
      Borrowing.mutate (shared program.bytes)
        (.store64 (frame program.bytes).owner (frame program.bytes).ticket
          ((frame program.bytes).top - BitVec.ofNat 64 depth) value) = .ok (evolved, none) ∧
      Borrowing.loadOwnedWord64 evolved (frame program.bytes).owner (frame program.bytes).ticket
        ((frame program.bytes).top - BitVec.ofNat 64 depth) = .ok value ∧
      CallResources.Contract (frame program.bytes).call evolved ∧
      evolved.loans = (Grading.Domain.shared program.bytes).loans := by
  have current := (resource_pre program entry bound argument registers flags).current
  have slot := private_slot_at_depth current.contract minimum maximum
  obtain ⟨evolved, stored⟩ := StackFrame.current_store64_enabled current slot value
  exact ⟨evolved, stored, Borrowing.store64_owned_readback stored,
    (StackFrame.contract_store64 current.contract stored).1.pureCall,
    (Borrowing.store64_effect stored).loans⟩

def lastEntry : Program := ⟨List.replicate 4096 0xff, 4095⟩

/-- The maximum supported window and its final entry have full admission,
and the actual byte at RIP is fetched from the end of that whole window.
This catches accidental entry-zero and decoder/importer admission bounds. -/
theorem last_entry_admitted (argument : Word) (registers : Register → Word) (flags : Word) :
    ResourcePre lastEntry (resource lastEntry argument)
        (initial lastEntry argument registers flags) ∧
      fetchByte (initial lastEntry argument registers flags).memory
        (initial lastEntry argument registers flags).rip = .ok 0xff := by
  have entry : lastEntry.entry < lastEntry.bytes.length := by
    simp only [lastEntry, List.length_replicate]
    decide
  have bound : lastEntry.bytes.length ≤ 4096 := by
    simp only [lastEntry, List.length_replicate, Nat.le_refl]
  have pre := resource_pre lastEntry entry bound argument registers flags
  refine ⟨pre, ?_⟩
  have code := pre.current.contract.pureCall.code
  have present : lastEntry.bytes[4095]? = some (0xff : Byte) :=
    List.getElem?_replicate_of_lt (by decide)
  exact code.2 4095 0xff present

private def unalignedWorld : Borrowing.State :=
  match Borrowing.mutate (shared unsupported.bytes)
      (.store64 (frame unsupported.bytes).owner (frame unsupported.bytes).ticket
        65529 0x89abcdef01234567) with
  | .ok (evolved, _) => evolved
  | .error _ => shared unsupported.bytes

/-- The concrete checked operation succeeds; the independent little-endian
expectation catches high-half truncation, reversed order and shifted writes.
The adjacent frame cells, original caller word and code remain intact. -/
theorem unaligned_full64 :
    Borrowing.mutate (shared unsupported.bytes)
        (.store64 (frame unsupported.bytes).owner (frame unsupported.bytes).ticket
          65529 0x89abcdef01234567) = .ok (unalignedWorld, none) ∧
      (List.range 8).map (fun index =>
        (toMemory unalignedWorld.resources.space).read (65529 + BitVec.ofNat 64 index)) =
        [some 0x67, some 0x45, some 0x23, some 0x01,
          some 0xef, some 0xcd, some 0xab, some 0x89] ∧
      (toMemory unalignedWorld.resources.space).read 65528 = some 0 ∧
      (toMemory unalignedWorld.resources.space).read 65537 = some 0 ∧
      readWord (toMemory unalignedWorld.resources.space) 65529 = .ok 0x89abcdef01234567 ∧
      readWord (toMemory unalignedWorld.resources.space) 65544 = .ok 8192 ∧
      fetchByte (toMemory unalignedWorld.resources.space) 4096 = .ok 0xff :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Raw readable neighboring RAM cannot enlarge private owner authority.
Wrong-owner and stale-epoch tickets fail against this actual allocated world. -/
theorem authority_boundaries (value : Word) :
    readWord (toMemory (shared unsupported.bytes).resources.space) 65537 = .ok 0 ∧
      Borrowing.loadOwnedWord64 (shared unsupported.bytes) (frame unsupported.bytes).owner
        (frame unsupported.bytes).ticket 65537 = .error .outsideAllocation ∧
      Borrowing.mutate (shared unsupported.bytes)
        (.store64 (frame unsupported.bytes).owner (frame unsupported.bytes).ticket 65537 value) =
        .error (.ownership .outsideAllocation) ∧
      Borrowing.loadOwnedWord64 (shared unsupported.bytes) 12
        (frame unsupported.bytes).ticket 65528 = .error (.authority .wrongOwner) ∧
      Borrowing.loadOwnedWord64 (shared unsupported.bytes) (frame unsupported.bytes).owner
        ⟨(ticket unsupported.bytes).identifier, 1⟩ 65528 = .error (.authority .staleEpoch) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Observe the actual call/return profile at the initialized current state,
separately from resource admission. -/
theorem unsupported_rejected :
    CallReturn.decodeAt (initial unsupported 0xfffffffffffffffe) =
      .error (.unsupportedOpcode 0xff) := rfl

/-- A candidate rejected by the selected profile still has both resource and
derived raw admission with a full64 input; rejection establishes no defect. -/
theorem unsupported_domain :
    ResourcePre unsupported (resource unsupported 0xfffffffffffffffe)
        (initial unsupported 0xfffffffffffffffe) ∧
      Pre unsupported (resourceInput (resource unsupported 0xfffffffffffffffe))
        (initial unsupported 0xfffffffffffffffe) ∧
      CallReturn.decodeAt (initial unsupported 0xfffffffffffffffe) =
        .error (.unsupportedOpcode 0xff) :=
  ⟨unsupported_admitted, raw_pre unsupported (by decide) (by decide) _, unsupported_rejected⟩

end EDSL.Tests.CallStackDomain

#print axioms EDSL.Tests.CallStackDomain.every_depth_store
#print axioms EDSL.Tests.CallStackDomain.last_entry_admitted
#print axioms EDSL.Tests.CallStackDomain.unaligned_full64
#print axioms EDSL.Tests.CallStackDomain.authority_boundaries
#print axioms EDSL.Tests.CallStackDomain.unsupported_rejected
#print axioms EDSL.Tests.CallStackDomain.unsupported_domain
#audit_edsl
