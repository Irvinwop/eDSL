/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Queue.Publication
import EDSL.OS.TSO64.Queue.Sequence
import tests.TSO64Fixtures
import EDSL.Audit

namespace EDSL.Tests.ManagedQueue64
open X86 OS.AddressSpace OS.TSO64

abbrev Fault := OS.TSO64.Fault

structure Setup where
  ready : TSO64.Ready
  writer : Worker
  reader : Worker

/-- Both workers retain real code/caller loans and separate ordinary grants.
They receive handles to the same initialized cell through checked OS setup. -/
def setup : Except Fault Setup := do
  let ready ← (TSO64.fixture 0xc3 0 0x0000000100000000).mapError Fault.os
  let state ← TSO64.start ready 0 0 0
  let some writer := state.workers[0]? | throw .missingWorker
  let some reader := state.workers[1]? | throw .missingWorker
  return ⟨ready, writer, reader⟩

def isFault {α : Type} (value : Except Fault α) (fault : Fault) : Bool :=
  match value with
  | .error actual => decide (actual = fault)
  | .ok _ => false

def eventValue (event : Option OS.Atomics64.StoreEvent64) : Option Word := event.map (·.value)

def roundTrip : Except Fault
    (Word × Except Error Word × Word × List (Option Byte) ×
      Except Error Word × Except OS.Borrowing.ReadFault Word × Nat × Option Word) := do
  let current ← setup
  let world := current.ready.checked.world
  let entry ← Queue.admit world current.writer.resources ⟨65536, .qword 0xfedcba9876543210⟩ 0 .sharedCell
  let before ← (OS.Atomics64.load world 12 current.ready.atomicB).mapError Fault.os
  let localValue := loadQWord (StoreBuffer.Mixed.view (published world) (Queue.payload [entry])) 65536
  let after ← Queue.publishHead world current.writer.resources [entry] .sharedCell
  let observed ← (OS.Atomics64.load after.1 12 current.ready.atomicB).mapError Fault.os
  let memory := published after.1
  return (before.2.value, localValue, observed.2.value,
    [65536, 65539, 65540, 65543].map memory.read,
    loadQWord memory 65544,
    OS.Borrowing.loadWord64 after.1.legacy.shared 11 current.ready.callerA 262144,
    after.2.1.length, eventValue after.2.2)

/-- The peer sees published RAM, while the writer's existing Mixed view
forwards the pending full64 word. Publication changes both high and low halves,
keeps the adjacent qword and original caller bytes, and removes one FIFO head. -/
theorem peer_publication_and_own_forwarding : roundTrip = .ok
    (0x0000000100000000, .ok 0xfedcba9876543210, 0xfedcba9876543210,
      [some 0x10, some 0x76, some 0x98, some 0xfe],
      .ok 0xabcdef0123456789, .ok 0x7000, 0, some 0xfedcba9876543210) := by rfl

def denials : Except Fault (List Bool) := do
  let current ← setup
  let world := current.ready.checked.world
  let resources := current.writer.resources
  let store : Store := ⟨65536, .qword 0x0000000100000000⟩
  let entry ← Queue.admit world resources store 0 .sharedCell
  let stranger := { resources with actor := 12 }
  return [isFault (Queue.admit world resources store 0) .noGrant,
    isFault (Queue.publish world resources entry) .resource,
    isFault (Queue.admit world resources ⟨65536, .dword 0⟩ 0 .sharedCell) .noGrant,
    isFault (Queue.admit world resources ⟨65537, .qword 0⟩ 0 .sharedCell) .noAtomicGrant,
    isFault (Queue.admit world resources ⟨65544, .qword 0⟩ 0 .sharedCell) .noAtomicGrant,
    isFault (Queue.admit world stranger store 0 .sharedCell) .noAtomicGrant,
    isFault (Queue.publish world { resources with atomics := [] } entry .sharedCell) .resource,
    isFault (Queue.publishHead world resources [] .sharedCell) .emptyBuffer]

/-- Same-value writes still require current exact authority. A neighboring
address in the reserved allocation and a DWORD at the cell have no fallback. -/
theorem authority_and_profile_denials : denials = .ok
    [true, true, true, true, true, true, true, true] := by rfl

def mixedFIFO : Except Fault
    (Except Error Word × Except Error Word × Except Error Word × Except Error Word ×
      Nat × Option Word × Nat × Option Word) := do
  let current ← setup
  let world := current.ready.checked.world
  let resources := current.writer.resources
  let ordinary ← Queue.admit world resources ⟨131072, .qword 0x1122334455667788⟩ 0 .sharedCell
  let managed ← Queue.admit world resources ⟨65536, .qword 0x8070605040302010⟩ 1 .sharedCell
  let first ← Queue.publishHead world resources [ordinary, managed] .sharedCell
  let second ← Queue.publishHead first.1 resources first.2.1 .sharedCell
  return (loadQWord (published first.1) 131072, loadQWord (published first.1) 65536,
    loadQWord (published second.1) 131072, loadQWord (published second.1) 65536,
    first.2.1.length, eventValue first.2.2, second.2.1.length, eventValue second.2.2)

/-- A single mixed FIFO publishes the ordinary head first. The managed word
must remain old until the next publication; the earlier ordinary word survives. -/
theorem mixed_authorities_share_fifo : mixedFIFO = .ok
    (.ok 0x1122334455667788, .ok 0x0000000100000000,
      .ok 0x1122334455667788, .ok 0x8070605040302010,
      1, none, 0, some 0x8070605040302010) := by rfl

/-- A hostile initial world may rebind a handle to a fresh persistent identity
at the same address. The primitive can authorize it; the retained queue entry
must reject it because its ORIGINAL complete handle is different. This is not
an admitted scheduler transition. -/
def reboundHandle : Except Fault (Bool × Word × Bool) := do
  let current ← setup
  let world := current.ready.checked.world
  let resources := current.writer.resources
  let entry ← Queue.admit world resources ⟨65536, .qword 0x8070605040302010⟩ 0 .sharedCell
  let selected ← (OS.Atomics64.authorize world 11 current.ready.atomicA).mapError Fault.os
  let other : OS.Atomics64.CellId64 := ⟨world.nextCell⟩
  let hostile := { world with
    nextCell := world.nextCell + 1
    cells := (fun id => if id = other then some selected.2 else world.cells id)
    handles := (fun id => if id = current.ready.atomicA then
      some { selected.1 with cell := other } else world.handles id) }
  let primitive ← (OS.Atomics64.load hostile 11 current.ready.atomicA).mapError Fault.os
  return (isFault (Queue.publish hostile resources entry .sharedCell) .resource,
    primitive.2.value, decide (primitive.2.cell = other))

theorem exact_handle_identity_is_rechecked : reboundHandle =
    .ok (true, 0x0000000100000000, true) := by rfl

def changedCellEpoch : Except Fault (Bool × Word) := do
  let current ← setup
  let world := current.ready.checked.world
  let resources := current.writer.resources
  let entry ← Queue.admit world resources ⟨65536, .qword 0x8070605040302010⟩ 0 .sharedCell
  let selected ← (OS.Atomics64.authorize world 11 current.ready.atomicA).mapError Fault.os
  let allocations := world.legacy.shared.resources.allocations
  let updated := { world.legacy.shared.resources with allocations := (fun id =>
    if id = selected.2.ticket.identifier then
      (allocations id).map (fun allocation => { allocation with epoch := allocation.epoch + 1 })
    else allocations id) }
  let hostile := { world with
    legacy := { world.legacy with shared := { world.legacy.shared with resources := updated } }
    cells := (fun id => if id = selected.1.cell then
      some { selected.2 with ticket := { selected.2.ticket with epoch := selected.2.ticket.epoch + 1 } }
      else world.cells id) }
  let primitive ← (OS.Atomics64.load hostile 11 current.ready.atomicA).mapError Fault.os
  return (isFault (Queue.publish hostile resources entry .sharedCell) .resource, primitive.2.value)

/-- Reauthorizing a live identifier/address is insufficient if its cell ticket
was replaced by another currently valid epoch. Compare the complete cell too. -/
theorem complete_cell_descriptor_is_rechecked : changedCellEpoch =
    .ok (true, 0x0000000100000000) := by rfl

def deniedLastByte : Except Fault (List Bool) := do
  let current ← setup
  let world := current.ready.checked.world
  let resources := current.writer.resources
  let entry ← Queue.admit world resources ⟨65536, .qword 0x8070605040302010⟩ 0 .sharedCell
  let damaged := { world with legacy := { world.legacy with shared := { world.legacy.shared with
    resources := { world.legacy.shared.resources with
      space := protectUnchecked world.legacy.shared.resources.space ⟨65543, 1⟩ readOnly } } } }
  return [isFault (Queue.publish damaged resources entry .sharedCell) .resource,
    isFault (Queue.admit damaged resources ⟨65536, .qword 0x8070605040302010⟩ 1 .sharedCell) .noAtomicGrant]

/-- A pending overlay contains every value byte but cannot authorize a store
when the CURRENT last byte is no longer writable. -/
theorem current_upper_byte_permission_is_required : deniedLastByte = .ok [true, true] := by rfl

def newestOccurrence (cursor : Queue.Cursor) : Option Nat := do
  let origin ← StoreBuffer.Mixed.newestQWord (Queue.payload cursor.pending) 65536
  match ← cursor.pending[origin.index]? with
  | .ordinary _ _ => none
  | .managed _ _ occurrence => some occurrence

def repeatedOccurrences : Except Fault
    (List Nat × Option Nat × Except Error Word × List Nat × Option Nat ×
      Except Error Word × Except Error Word × Nat × Option Word × Option Word) := do
  let current ← setup
  let world := current.ready.checked.world
  let resources := current.writer.resources
  let ordinary ← Queue.Cursor.empty.enqueue world resources ⟨131072, .qword 0x1122334455667788⟩
  let first ← Queue.publishHead world resources ordinary.pending
  let afterOrdinary := ordinary.dropHead
  let one ← afterOrdinary.enqueue first.1 resources ⟨65536, .qword 0xfedcba9876543210⟩ .sharedCell
  let two ← one.enqueue first.1 resources ⟨65536, .qword 0xfedcba9876543210⟩ .sharedCell
  let before := loadQWord (published first.1) 65536
  let second ← Queue.publishHead first.1 resources two.pending .sharedCell
  let remaining : Queue.Cursor := ⟨second.2.1, two.nextStore⟩
  let three ← remaining.enqueue second.1 resources ⟨65536, .qword 0xfedcba9876543210⟩ .sharedCell
  let third ← Queue.publishHead second.1 resources three.pending .sharedCell
  return (Queue.occurrences two.pending, newestOccurrence two, before,
    Queue.occurrences three.pending, newestOccurrence three,
    loadQWord (published second.1) 65536, loadQWord (published third.1) 65536,
    three.nextStore, eventValue second.2.2, eventValue third.2.2)

/-- An ordinary enqueue consumes the first sequence number even after its
publication. Equal managed writes then receive distinct, nonrecycled IDs.
The newest actual buffer position names the later issue; both FIFO drains
emit events although the second writes the same bits already in RAM. -/
theorem equal_values_do_not_recycle_occurrences : repeatedOccurrences = .ok
    ([1, 2], some 2, .ok 0x0000000100000000, [2, 3], some 3,
      .ok 0xfedcba9876543210, .ok 0xfedcba9876543210,
      4, some 0xfedcba9876543210, some 0xfedcba9876543210) := by rfl

end EDSL.Tests.ManagedQueue64

#audit_edsl
