/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace
import tests.TSO64StoreTrace
import EDSL.Audit

set_option autoImplicit false

namespace EDSL.Tests.TSO64AtomicTrace
open X86 OS.TSO64 OS.TSO64.C23Projection
open AtomicTrace

/-- Orders belong to the declared primitive interface. They are not decoded
from the MOV/LOCK bytes used by these project-owned synthetic programs. -/
def interfaceOrders : Orders where
  read _ _ := .acquire
  write _ _ := .release
  rmw _ _ := .acqRel

/-- Report origin identities independently of the source-graph index mapping.
The tag distinguishes a load, buffered store issue and successful RMW. -/
def eventSummary (event : AtomicTrace.Event) :
    Nat × Nat × Nat × OS.Atomics64.CellId64 × Word × Option WriterId × Option WriterId :=
  match event.access with
  | .load reference value source =>
      (event.position, event.tid, 0, reference.handle.cell, value, some source, none)
  | .store reference value occurrence =>
      (event.position, event.tid, 1, reference.handle.cell, value, none,
        some (.store event.tid occurrence))
  | .rmw changed source =>
      (event.position, event.tid, 2, changed.cell, changed.arithmetic.event.after,
        some source, some (.rmw event.position))

/-- Real registration, retirement and re-registration create a numeric gap.
The final live cell has no handles, and its value equals the handled cell's
value. Neither handle enumeration nor deduplication by word can find it. -/
def gapWorld : Except OS.Atomics64.Fault World := do
  let ready ← TSO64.fixture 0x00000000000000c3 0 0
  let (allocated, output) ← OS.Atomics64.mutate ready.checked.world
    (.allocate 7 ⟨458752, 8⟩ OS.AddressSpace.readWrite)
  let ticket ← TSO64.ticket output
  let (initialized, _) ← OS.Atomics64.mutate allocated (.store64 7 ticket 458752 0)
  let (registered, first) ← OS.Atomics64.enroll initialized 7 ticket 458752
  let retired ← OS.Atomics64.retire registered 7 first
  let (again, _) ← OS.Atomics64.enroll retired 7 ticket 458752
  pure again

def gapInitials : Except Fault (List (Nat × Word × Word)) := do
  let world ← gapWorld.mapError Fault.os
  let entries ← Initials.enumerate world
  pure (entries.map fun entry => (entry.identifier.index, entry.cell.address, entry.value))

/-- Complete registry scanning includes a live unhandled cell after a retired
slot. Equal initial bits do not merge distinct object identities. -/
theorem initial_manifest_covers_unhandled_cells_and_retired_gaps :
    gapInitials = .ok [(0, 65536, 0), (2, 458752, 0)] := by rfl

/-- Two stores followed by two loads, with a peer starting at the first load.
Every store and initial word is zero, so the observed origin identities cannot
be recovered by comparing word values. -/
def equalStart : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x8b48378948378948 0x000000c3078b4807 0 0 0 0 6

def equalActions : List Action :=
  [.issue 1 false, .issue 0 false, .issue 0 true, .issue 0 false,
    .drain 0, .issue 1 true, .issue 0 true, .drain 0,
    .issue 0 false, .issue 1 false]

def equalTrace : Except Fault AtomicTrace.Result := do
  let initial ← equalStart
  AtomicTrace.scan initial equalActions .sharedCell 10

def equalOrigins : Except Fault
    (List (Nat × Nat × Nat × OS.Atomics64.CellId64 × Word × Option WriterId × Option WriterId) ×
      Except Error Word × Except Error Word) := do
  let result ← equalTrace
  pure (result.events.map eventSummary,
    loadQWord (published result.state.world) 65536,
    loadQWord (published result.state.world) 65544)

/-- The peer first reads initialization, then the first published store. The
writer always forwards its newest own store, including while the older store
has already drained. Drains and RET consume positions without atomic events.
The untouched neighboring word also checks the actual memory frame. -/
theorem actual_equal_words_keep_initial_forwarded_and_published_sources :
    equalOrigins = .ok
      ([(10, 1, 0, ⟨0⟩, 0, some (.initial ⟨0⟩), none),
        (11, 0, 1, ⟨0⟩, 0, none, some (.store 0 0)),
        (12, 0, 1, ⟨0⟩, 0, none, some (.store 0 1)),
        (13, 0, 0, ⟨0⟩, 0, some (.store 0 1), none),
        (15, 1, 0, ⟨0⟩, 0, some (.store 0 0), none),
        (16, 0, 0, ⟨0⟩, 0, some (.store 0 1), none)],
        .ok 0, .ok 0xabcdef0123456789) := by rfl

def equalInputs : Except Fault Graph.Inputs := do
  let initial ← equalStart
  let initials ← Initials.enumerate initial.world
  let result ← AtomicTrace.scan initial equalActions .sharedCell 10
  pure ⟨initials, result.events, writes 10 result.observations⟩

def certifiedEqualGraph : Except Fault (Option (List (Option Nat) × List Nat)) := do
  let inputs ← equalInputs
  pure ((Graph.certify inputs interfaceOrders).map fun table => (table.sources, table.ranks))

/-- RF uses complete graph indices, including the initial read before either
store and every later load. Modification ranks are actual publication+1, not
issue positions or filtered event indices. The declared release/acquire graph
must pass the existing semantic checker as well as structural admission. -/
theorem actual_execution_builds_a_checked_graph_with_full_indices :
    certifiedEqualGraph = .ok (some
      ([none, some 0, none, none, some 3, some 2, some 3],
        [0, 0, 15, 18, 0, 0, 0])) := by rfl

def deniedTrace : Except Fault Nat := do
  let initial ← equalStart
  let result ← AtomicTrace.scan initial [.issue 0 false] .ownedOnly
  pure result.events.length

theorem atomic_scanner_preserves_the_actual_admission_fault :
    deniedTrace = .error .noGrant := by rfl

/-- A disjoint ordinary store remains queued while the reader falls back to
published managed RAM. A peer drain changes the selected writer, even though
the reader's own nonempty FIFO is unchanged. -/
def disjointPendingOrigins : Except Fault
    (List (Nat × Nat × Nat × OS.Atomics64.CellId64 × Word × Option WriterId × Option WriterId)) := do
  let initial ← TSO64SharedCells.start 0x8b48078b48328948 0x000000c337894807
    0x1122334455667788 0xfedcba9876543210 9 9 0
  let result ← AtomicTrace.scan initial [.issue 0 false, .issue 1 false,
    .issue 1 false, .drain 0, .issue 1 false] .sharedCell 30
  pure (result.events.map eventSummary)

theorem ordinary_pending_store_does_not_hide_current_published_origin :
    disjointPendingOrigins = .ok
      [(30, 0, 1, ⟨0⟩, 0xfedcba9876543210, none, some (.store 0 0)),
        (32, 1, 0, ⟨0⟩, 0x1122334455667788, some (.initial ⟨0⟩), none),
        (34, 1, 0, ⟨0⟩, 0xfedcba9876543210, some (.store 0 0), none)] := by rfl

def rmwActions : List Action :=
  [.issue 0 false, .issue 0 false, .drain 0,
    .issue 0 false, .issue 0 true, .issue 0 false]

def rmwInputs : Except Fault Graph.Inputs := do
  let initial ← TSO64PublishedWriters.start
  let initials ← Initials.enumerate initial.world
  let result ← AtomicTrace.scan initial rmwActions .sharedCell 20
  pure ⟨initials, result.events, writes 20 result.observations⟩

def rmwOrigins : Except Fault
    (List (Nat × Nat × Nat × OS.Atomics64.CellId64 × Word × Option WriterId × Option WriterId)) := do
  let inputs ← rmwInputs
  pure (inputs.events.map eventSummary)

/-- A blocked LOCK contributes neither a read nor a write. Two successful
zero-delta RMWs keep distinct action identities and read the immediate actual
predecessor, although both complete arithmetic event payloads are identical. -/
theorem successful_unchanged_rmws_use_the_pre_observation_writer :
    rmwOrigins = .ok
      [(20, 0, 1, ⟨0⟩, 0, none, some (.store 0 0)),
        (23, 0, 2, ⟨0⟩, 0, some (.store 0 0), some (.rmw 23)),
        (24, 0, 2, ⟨0⟩, 0, some (.rmw 23), some (.rmw 24))] := by rfl

def certifiedRMWGraph : Except Fault (Option (List (Option Nat) × List Nat)) := do
  let inputs ← rmwInputs
  pure ((Graph.certify inputs interfaceOrders).map fun table => (table.sources, table.ranks))

theorem actual_unchanged_rmw_chain_is_certified :
    certifiedRMWGraph = .ok (some ([none, none, some 1, some 2], [0, 23, 24, 25])) := by rfl

/-- Change a requested source identity while retaining the actual event word,
all other event fields and every actual publication. This deliberately corrupts
the graph input, not the execution that produced it. -/
def skipRMWPredecessor (event : AtomicTrace.Event) : AtomicTrace.Event :=
  match event.access with
  | .rmw changed _ =>
      if event.position = 24 then { event with access := .rmw changed (.store 0 0) }
      else event
  | _ => event

def skippedRMWStatus : Except Fault (Bool × Bool) := do
  let inputs ← rmwInputs
  let changed := { inputs with events := inputs.events.map skipRMWPredecessor }
  pure ((Graph.build changed interfaceOrders).isSome,
    (Graph.certify changed interfaceOrders).isSome)

/-- Equal-word/object mapping alone admits the deliberately stale source. The
semantic checker must reject its skipped predecessor before exposing legality. -/
theorem equal_bits_do_not_admit_a_skipped_rmw_predecessor :
    skippedRMWStatus = .ok (true, false) := by rfl

def omittedEqualWriteStatus : Except Fault Bool := do
  let inputs ← rmwInputs
  let changed := { inputs with events :=
    (inputs.events.filter (fun event => event.position != 23)).map skipRMWPredecessor }
  pure (Graph.build changed interfaceOrders).isSome

/-- Keeping the complete publication list prevents deletion of an unchanged
intervening write. Retargeting the following read to the still-present equal
writer avoids relying on a missing RF key to reject the omission. -/
theorem an_equal_write_cannot_be_omitted_from_the_event_graph :
    omittedEqualWriteStatus = .ok false := by rfl

def missingPublicationStatus : Except Fault Bool := do
  let inputs ← rmwInputs
  let changed := { inputs with writes := inputs.writes.filter (fun stamp => stamp.position != 23) }
  pure (Graph.build changed interfaceOrders).isSome

theorem required_actual_publication_cannot_be_replaced_by_a_default_rank :
    missingPublicationStatus = .ok false := by rfl

def duplicateWriterStatus : Except Fault Bool := do
  let inputs ← rmwInputs
  let duplicated := inputs.events.filter (fun event => event.position == 24)
  let changed := { inputs with events := inputs.events ++ duplicated }
  pure (Graph.build changed interfaceOrders).isSome

/-- A duplicated terminal RMW key is rejected even without any reader requesting
that key. Its complete arithmetic event agrees with the original. -/
theorem an_unused_duplicate_writer_identity_is_rejected :
    duplicateWriterStatus = .ok false := by rfl

def duplicatePublicationStatus : Except Fault Bool := do
  let inputs ← equalInputs
  let changed := { inputs with writes := inputs.writes ++ inputs.writes }
  pure (Graph.build changed interfaceOrders).isSome

theorem ambiguous_publication_identity_is_rejected :
    duplicatePublicationStatus = .ok false := by rfl

def absentWriterStatus : Except Fault Bool := do
  let inputs ← equalInputs
  let changed := { inputs with events := inputs.events.map fun event =>
    match event.access with
    | .load reference value _ =>
        { event with access := .load reference value (.store 99 0) }
    | _ => event }
  pure (Graph.build changed interfaceOrders).isSome

theorem an_absent_equal_value_writer_is_rejected :
    absentWriterStatus = .ok false := by rfl

/-- Both scheduler slots issue occurrences zero and one. Their complete graph
keys must retain the slot as well as the local number, across empty FIFOs. -/
def peerWriterKeys : Except Fault (List (Option WriterId)) := do
  let initial ← TSO64StoreIdentities.start
  let result ← AtomicTrace.scan initial [.issue 0 false, .drain 0,
    .issue 1 false, .issue 0 true, .drain 1, .issue 0 false, .drain 0,
    .issue 1 true, .issue 1 false, .drain 1] .sharedCell 60
  pure (result.events.map AtomicTrace.Event.writer)

theorem equal_local_occurrences_on_different_threads_remain_distinct :
    peerWriterKeys = .ok
      [some (.store 0 0), some (.store 1 0), some (.store 0 1), some (.store 1 1)] := by rfl

/-- The public entry point obtains the manifest, trace, RF slots and ranks
itself. The blocked LOCK remains in the original action index space. -/
def verifiedRMW : Except Fault (Except AtomicTrace.Failure
    (List (Option Nat) × List Nat)) := do
  let initial ← TSO64PublishedWriters.start
  pure ((AtomicTrace.verify initial rmwActions interfaceOrders).map fun output =>
    (output.table.sources, output.table.ranks))

theorem public_verifier_extracts_and_checks_the_actual_rmw_run :
    verifiedRMW = .ok (.ok ([none, none, some 1, some 2], [0, 3, 4, 5])) := by rfl

def openFinalQueues : Except Fault (Except AtomicTrace.Failure Nat) := do
  let initial ← equalStart
  pure ((AtomicTrace.verify initial [.issue 0 false] interfaceOrders).map
    (fun output => output.table.events.length))

/-- A successful store instruction leaves unpublished state. Its return value
alone cannot turn the finite run into a closed graph boundary. -/
theorem public_verifier_rejects_an_unpublished_final_store :
    openFinalQueues = .ok (.error .finalQueues) := by rfl

def openInitialQueues : Except Fault (Except AtomicTrace.Failure Nat) := do
  let initial ← equalStart
  let pending ← step initial (.issue 0 false) .sharedCell
  pure ((AtomicTrace.verify pending.1 [.drain 0] interfaceOrders).map
    (fun output => output.table.events.length))

/-- Draining a pre-existing real store cannot invent its missing issue origin
inside the selected run, even though the final queues would be empty. -/
theorem public_verifier_rejects_an_unrecorded_initial_store :
    openInitialQueues = .ok (.error .initialQueues) := by rfl

def publicAdmissionFault : Except Fault (Except AtomicTrace.Failure Nat) := do
  let initial ← equalStart
  pure ((AtomicTrace.verify initial [.issue 0 false] interfaceOrders .ownedOnly).map
    (fun output => output.table.events.length))

theorem public_verifier_distinguishes_an_actual_execution_fault :
    publicAdmissionFault = .ok (.error (.execution .noGrant)) := by rfl

end EDSL.Tests.TSO64AtomicTrace

#print axioms EDSL.OS.TSO64.C23Projection.AtomicTrace.Initials.enumerate_complete
#print axioms EDSL.OS.TSO64.C23Projection.AtomicTrace.scan_certificate
#print axioms EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph.certify_sound
#print axioms EDSL.OS.TSO64.C23Projection.AtomicTrace.verify_sound
#print axioms EDSL.OS.TSO64.C23Projection.AtomicTrace.scan_source_origins
#print axioms EDSL.Tests.TSO64AtomicTrace.actual_execution_builds_a_checked_graph_with_full_indices
#print axioms EDSL.Tests.TSO64AtomicTrace.actual_unchanged_rmw_chain_is_certified
#audit_edsl
