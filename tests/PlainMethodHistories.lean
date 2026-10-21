/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.History
import tests.PlainCallBatch

/-!
A raw captured-scan client with two actual admitted calls. Reuse the checked
installation, live authority and method shapes from PlainCallBatch, but drain
the reader's ordinary FIFO BEFORE the invocation boundary. Its nextStore stays
one, so an empty boundary does not imply fresh machine counters. Current is
transported forward through that actual publication, and the reader's method
records the actual now-empty queue rather than the old invocation's FIFO.

The peer stores, returns with its managed FIFO outstanding, and only later
publishes. Between that RET and publication the reader loads the old full
64-bit word; its RET follows publication and still returns the old word.
Literal machine events, replies, publication metadata and call-event positions
are independent expectations on production execution. No candidate or table is
supplied to the raw History theorem, and no new instruction proof is used.

Scope is the existing sharedCell, scalar-RAM, long-mode/CET-off finite model,
with initialized stable resources, code/caller authority and declared interface
orders. There is no source/compiler, final-ELF, native CPU/kernel, fairness or
new compiler-corpus claim. These are owned synthetic programs and resources.
-/

set_option autoImplicit false

namespace EDSL.Tests.PlainMethodHistories
open X86 OS.TSO64 X86.VCGen.PlainMethods
open OS.TSO64.C23Projection Concurrency

private instance : DecidableEq PlainMethods.PendingView := inferInstance
private instance : DecidableEq (List PlainMethods.PendingView) := inferInstance
private instance : DecidableEq (Option (List PlainMethods.PendingView)) := inferInstance
private instance : DecidableEq (List (Except Error Word)) := inferInstance
private instance : DecidableEq (List (Option (Nat × Word))) := inferInstance
private instance : DecidableEq (List AtomicTrace.Event) := inferInstance
private instance : DecidableEq (List PublishedHistory.Stamp) := inferInstance
private instance : DecidableEq (List AtomicTrace.Initials.Entry) := inferInstance
private instance : DecidableEq (List (Option Nat) × List Nat) := inferInstance

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private def found {α : Type} (value : Option α) (present : value.isSome = true) : α :=
  value.get present

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (found value present) := by
  cases value with
  | none => cases present
  | some value => rfl

-- Only the queue field changes at this new invocation boundary. All current
-- code, caller, resource and selected-cell evidence remains the same evidence.
private theorem requeue_current {method : Method} {state : OS.TSO64.State}
    (current : Current method state) (queue : Queue.Cursor) :
    Current { method with initialQueue := queue } state :=
  ⟨current.valid, current.code, current.fits, current.caller, current.selected⟩

private theorem requeue_entry {method : Method} {worker : Worker}
    (entry : At method (.preamble 0 []) worker) (pending : List Pending) :
    At { method with initialQueue := ⟨pending, worker.nextStore⟩ } (.preamble 0 [])
      { worker with pending := pending } :=
  ⟨entry.resources, entry.flags, QueueFrame.refl _, entry.location⟩

-- Authenticate the changed worker through the real drain effect. This is a
-- queue frame lemma, not a reconstruction of an instruction's semantics.
private theorem drained_singleton {state : OS.TSO64.State} {tid : Nat}
    {result : OS.TSO64.State × Observation} {worker : Worker}
    (success : step state (.drain tid) .sharedCell = .ok result)
    (live : state.workers[tid]? = some worker) (single : worker.pending.tail = []) :
    result.1.workers[tid]? = some { worker with pending := [] } := by
  obtain ⟨draining, head, tail, output, drainingLive, pending, _, _, equal⟩ :=
    drain_effect (profile := .sharedCell) success
  have same : draining = worker := Option.some.inj (drainingLive.symm.trans live)
  subst draining
  have empty : tail = [] := by simpa only [pending, List.tail_cons] using single
  subst tail
  rw [equal]
  change (state.workers.set tid { worker with pending := [] })[tid]? = _
  exact List.getElem?_set_self (List.getElem_of_getElem? live).1

private theorem quiescent_of_projection {state : OS.TSO64.State}
    (empty : state.workers.map Worker.pending = [[], []]) : Quiescent state := by
  intro worker member
  have mapped : worker.pending ∈ state.workers.map Worker.pending :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  rw [empty] at mapped
  simpa using mapped

def boundaryAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step PlainCallBatch.initial (.drain 0) .sharedCell

theorem boundary_succeeds : boundaryAttempt.toOption.isSome = true := by decide +kernel

def boundary : OS.TSO64.State × Observation := checked boundaryAttempt boundary_succeeds

theorem boundary_actual : step PlainCallBatch.initial (.drain 0) .sharedCell = .ok boundary :=
  checked_ok _ _

def initial : OS.TSO64.State := boundary.1

def reader : Worker := { PlainCallInterference.boundaryReader with pending := [] }

theorem reader_live : initial.workers[0]? = some reader := by
  simpa only [initial, reader] using
    (drained_singleton (state := PlainCallBatch.initial) (tid := 0) (result := boundary)
      (worker := PlainCallInterference.boundaryReader) boundary_actual
      PlainCallBatch.reader_live (by decide +kernel))

theorem peer_live : initial.workers[1]? = some PlainCallInterference.peer := by
  simpa only [initial] using
    ((step_peer (state := PlainCallBatch.initial) (result := boundary) (peer := 1)
      boundary_actual (by decide)).trans PlainCallBatch.peer_live)

def readerMethod : Method :=
  { PlainCallInterference.method with initialQueue := ⟨[], reader.nextStore⟩ }

theorem reader_current : Current readerMethod initial :=
  requeue_current (PlainCallBatch.reader_current.step boundary_actual) _

theorem peer_current : Current PlainCallBatch.peerMethod initial :=
  PlainCallBatch.peer_current.step boundary_actual

theorem reader_entry : At readerMethod (.preamble 0 []) reader := by
  simpa only [readerMethod, reader] using
    (requeue_entry (method := PlainCallInterference.method)
      (worker := PlainCallInterference.boundaryReader) PlainCallInterference.entry [])

theorem initial_length : initial.workers.length = 2 := by decide +kernel

theorem initial_quiescent : Quiescent initial := quiescent_of_projection (by decide +kernel)

def readerInvocation : Invocation initial 0 where
  method := readerMethod
  padding := []
  occurrence := 17
  initial := reader
  current := reader_current
  live := reader_live
  entry := reader_entry

def peerInvocation : Invocation initial 1 where
  method := PlainCallBatch.peerMethod
  padding := []
  occurrence := 17
  initial := PlainCallInterference.peer
  current := peer_current
  live := peer_live
  entry := PlainCallBatch.peer_entry

def invocations (tid : Fin initial.workers.length) : Invocation initial tid.val := by
  by_cases zero : tid.val = 0
  · rw [zero]
    exact readerInvocation
  · have bound : tid.val < 2 := by simpa only [initial_length] using tid.isLt
    have one : tid.val = 1 := by omega
    rw [one]
    exact peerInvocation

-- Every following state is extracted from an actual production step. No
-- expected reply, poststate, graph event or table is an execution input.
def storeAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step initial (.issue 1 true) .sharedCell

theorem store_succeeds : storeAttempt.toOption.isSome = true := by decide +kernel
def stored : OS.TSO64.State × Observation := checked storeAttempt store_succeeds

theorem store_actual : step initial (.issue 1 true) .sharedCell = .ok stored := checked_ok _ _

def storeReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step stored.1 (.issue 1 false) .sharedCell

theorem store_return_succeeds : storeReturnAttempt.toOption.isSome = true := by decide +kernel
def storeReturned : OS.TSO64.State × Observation := checked storeReturnAttempt store_return_succeeds

theorem store_return_actual : step stored.1 (.issue 1 false) .sharedCell = .ok storeReturned :=
  checked_ok _ _

def loadAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step storeReturned.1 (.issue 0 false) .sharedCell

theorem load_succeeds : loadAttempt.toOption.isSome = true := by decide +kernel
def loaded : OS.TSO64.State × Observation := checked loadAttempt load_succeeds

theorem load_actual : step storeReturned.1 (.issue 0 false) .sharedCell = .ok loaded := checked_ok _ _

def publicationAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step loaded.1 (.drain 1) .sharedCell

theorem publication_succeeds : publicationAttempt.toOption.isSome = true := by decide +kernel
def publishedStore : OS.TSO64.State × Observation := checked publicationAttempt publication_succeeds

theorem publication_actual : step loaded.1 (.drain 1) .sharedCell = .ok publishedStore := checked_ok _ _

def readerReturnAttempt : Except Fault (OS.TSO64.State × Observation) :=
  step publishedStore.1 (.issue 0 true) .sharedCell

theorem reader_return_succeeds : readerReturnAttempt.toOption.isSome = true := by decide +kernel
def readerReturned : OS.TSO64.State × Observation := checked readerReturnAttempt reader_return_succeeds

theorem reader_return_actual : step publishedStore.1 (.issue 0 true) .sharedCell = .ok readerReturned :=
  checked_ok _ _

def actions : List Action :=
  [.issue 1 true, .issue 1 false, .issue 0 false, .drain 1, .issue 0 true]

def result : OS.TSO64.State × List Observation :=
  (readerReturned.1, [stored.2, storeReturned.2, loaded.2, publishedStore.2, readerReturned.2])

theorem scheduled : schedule initial actions .sharedCell = .ok result := by
  simp only [actions, result, schedule, store_actual, store_return_actual, load_actual,
    publication_actual, reader_return_actual, ok_bind, pure_ok]

theorem final_reader_present : (result.1.workers[0]?).isSome = true := by decide +kernel
theorem final_peer_present : (result.1.workers[1]?).isSome = true := by decide +kernel
def finalReader : Worker := found (result.1.workers[0]?) final_reader_present
def finalPeer : Worker := found (result.1.workers[1]?) final_peer_present

theorem final_reader_live : result.1.workers[0]? = some finalReader := found_ok _ _
theorem final_peer_live : result.1.workers[1]? = some finalPeer := found_ok _ _
theorem final_reader_returned : finalReader.phase = .returned := by decide +kernel
theorem final_peer_returned : finalPeer.phase = .returned := by decide +kernel

theorem all_returned (tid : Fin initial.workers.length) :
    ∃ final, result.1.workers[tid.val]? = some final ∧ final.phase = .returned := by
  have bound : tid.val < 2 := by simpa only [initial_length] using tid.isLt
  have slots : tid.val = 0 ∨ tid.val = 1 := by omega
  rcases slots with zero | one
  · rw [zero]
    exact ⟨finalReader, final_reader_live, final_reader_returned⟩
  · rw [one]
    exact ⟨finalPeer, final_peer_live, final_peer_returned⟩

theorem final_quiescent : Quiescent result.1 := quiescent_of_projection (by decide +kernel)

private theorem scan_success {state : OS.TSO64.State} {plan : List Action}
    {output : OS.TSO64.State × List Observation}
    (success : schedule state plan .sharedCell = .ok output) (offset : Nat) :
    (AtomicTrace.scan state plan .sharedCell offset PublishedHistory.empty).toOption.isSome = true := by
  have erased := AtomicTrace.scan_execution state plan .sharedCell offset PublishedHistory.empty
  rw [success] at erased
  cases actual : AtomicTrace.scan state plan .sharedCell offset PublishedHistory.empty with
  | error fault =>
      have impossible : (Except.error fault : Except Fault (OS.TSO64.State × List Observation)) =
          .ok output := by
        simpa only [actual, Except.map] using erased
      cases impossible
  | ok run => rfl

def scanAttempt : Except Fault AtomicTrace.Result :=
  AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty

theorem scan_succeeds : scanAttempt.toOption.isSome = true := scan_success scheduled 37
def scanned : AtomicTrace.Result := checked scanAttempt scan_succeeds

theorem scanned_actual : AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty =
    .ok scanned := checked_ok _ _

theorem scanned_execution : scanned.execution = result :=
  Except.ok.inj ((AtomicTrace.scan_scheduled scanned_actual).symm.trans scheduled)

theorem manifest_succeeds : (AtomicTrace.Initials.enumerate initial.world).toOption.isSome = true := by
  obtain ⟨entries, success⟩ := AtomicTrace.Initials.enumerate_success reader_current.valid.1
  rw [success]
  rfl

def manifest : List AtomicTrace.Initials.Entry :=
  checked (AtomicTrace.Initials.enumerate initial.world) manifest_succeeds

theorem manifest_actual : AtomicTrace.Initials.enumerate initial.world = .ok manifest := checked_ok _ _

private theorem run_quiescent {run : AtomicTrace.Result}
    {output : OS.TSO64.State × List Observation} (execution : run.execution = output)
    (closed : Quiescent output.1) : Quiescent run.state := by
  change Quiescent run.execution.1
  rw [execution]
  exact closed

theorem captured : AtomicTrace.Graph.Captured initial actions .sharedCell 37 scanned manifest where
  valid := reader_current.valid
  initialEmpty := initial_quiescent
  scanned := scanned_actual
  quiescent := run_quiescent scanned_execution final_quiescent
  enumerated := manifest_actual

/-- Independent exact scanner requirements include complete references, the
old full word, the new full word and the INITIAL writer key. A store's RET
and the later drain consume positions without creating atomic events. -/
theorem literal_machine_events : scanned.events =
    [⟨37, 1, .store PlainCallBatch.peerReference 0xfedcba9876543210 0⟩,
     ⟨39, 0, .load PlainMethodAdmission.reference 0x1122334455667788 (.initial ⟨0⟩)⟩] := by
  decide +kernel

theorem literal_initials : manifest =
    [⟨⟨0⟩, PlainMethodAdmission.reference.cell, 0x1122334455667788⟩] := by decide +kernel

theorem literal_publications : writes 37 result.2 =
    [⟨40, .buffered 1 PlainCallBatch.peerReference 0xfedcba9876543210 0⟩] := by decide +kernel

private theorem observations_at_output {run : AtomicTrace.Result}
    {output : OS.TSO64.State × List Observation} (same : run.execution = output) :
    run.observations = output.2 := by
  simpa only [AtomicTrace.Result.execution] using congrArg Prod.snd same

/-- Observe metadata of the actual executable builder, after rewriting only
independently checked runtime inputs. No proposed table supplies success
or legality to Correspondence.history. Rank 41 is publication+1, not the
issue position 37, the writer's RET position 38, or an event-list index. -/
theorem literal_graph_metadata :
    (AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs manifest scanned 37)
      AtomicEvents.orders).map (fun table => (table.sources, table.ranks)) =
      some ([none, none, some 0], [0, 41, 0]) := by
  have observations : scanned.observations = result.2 := observations_at_output scanned_execution
  change (AtomicTrace.Graph.build
    ⟨manifest, scanned.events, writes 37 scanned.observations⟩
      AtomicEvents.orders).map (fun table => (table.sources, table.ranks)) = _
  rw [literal_initials, literal_machine_events, observations, literal_publications]
  decide +kernel

/-- Literal executable observations distinguish the returned load reply from
final RAM, and require the writer's real RET to leave its managed entry
queued. The ordinary pre-boundary drain retains the reader's counter one. -/
theorem literal_runtime :
    initial.workers.map (fun worker => worker.nextStore) = [1, 0] ∧
    result.2.map PlainMethods.eventKind = [(0, 1), (1, 1), (0, 0), (2, 1), (1, 0)] ∧
    storeReturned.1.workers[1]?.map (fun worker => worker.pending.map PlainMethods.pendingView) =
      some [(1, 65536, .qword 0xfedcba9876543210, some 0)] ∧
    [Return.returnValue storeReturned, Return.returnValue readerReturned] =
      [some (1, 5), some (0, 0x1122334455667788)] ∧
    PlainMethods.worldWords result.1 =
      [.ok 9, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem store_response : result.2[1]? = some (.returned 1) := by decide +kernel

-- Keep all dependent execution conversions abstract. In particular the raw
-- theorem never has to unfold this concrete fixture while unifying a batch's
-- result index at the parent's unchanged depth limit.
private theorem history_at_output {state : OS.TSO64.State} {plan : List Action}
    {output : OS.TSO64.State × List Observation} {run : AtomicTrace.Result}
    {offset : Nat} {initials : List AtomicTrace.Initials.Entry}
    (raw : AtomicTrace.Graph.Captured state plan .sharedCell offset run initials)
    (execution : run.execution = output)
    (entries : (tid : Fin state.workers.length) → Invocation state tid.val)
    (returned : ∀ tid : Fin state.workers.length,
      ∃ final, output.1.workers[tid.val]? = some final ∧ final.phase = .returned) :
    ∃ table,
      AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs initials run offset)
        AtomicEvents.orders = some table ∧
      ∃ batch : BatchResult state plan output entries,
        AtomicCalls.History (initials.map AtomicTrace.Graph.initialEvent)
          batch.calls table.toCandidate := by
  subst output
  have returnedState : ∀ tid : Fin state.workers.length,
      ∃ final, run.state.workers[tid.val]? = some final ∧ final.phase = .returned := by
    simpa only [AtomicTrace.Result.execution] using returned
  exact Correspondence.history raw entries returnedState

private theorem positioned_at_output {state : OS.TSO64.State} {plan : List Action}
    {output : OS.TSO64.State × List Observation} {run : AtomicTrace.Result}
    {entries : (tid : Fin state.workers.length) → Invocation state tid.val}
    {offset : Nat} {initials : List AtomicTrace.Initials.Entry}
    (batch : BatchResult state plan output entries)
    (raw : AtomicTrace.Graph.Captured state plan .sharedCell offset run initials)
    (execution : run.execution = output) :
    run.events.map (fun actual => (actual.position, actual.toSource AtomicEvents.orders)) =
      batch.calls.map (fun actual => (offset + actual.performed, actual.event)) := by
  subst output
  exact Correspondence.positioned_events batch raw.valid raw.sequenced raw.scanned

/-- Closed nonempty raw-scan construction, followed by independent call,
source and publication-rank expectations. Both slots and all graph rows
come from the real run. The returned writer's response is action 1, before
its publication at action 3; the reader keeps its actual old-word reply. -/
theorem integration_client :
    ∃ table,
      AtomicTrace.Graph.build (AtomicTrace.Graph.runInputs manifest scanned 37)
        AtomicEvents.orders = some table ∧
      ∃ batch : BatchResult initial actions result invocations,
        AtomicCalls.History (manifest.map AtomicTrace.Graph.initialEvent)
          batch.calls table.toCandidate ∧
        batch.calls.map (fun actual => (37 + actual.performed, actual.event)) =
          [(37, ⟨some 1, ⟨0⟩, .store .release 0xfedcba9876543210⟩),
           (39, ⟨some 0, ⟨0⟩, .load .acquire 0x1122334455667788⟩)] ∧
        (∃ store ∈ batch.calls, store.thread = 1 ∧ store.returned = 1) ∧
        table.sources = [none, none, some 0] ∧ table.ranks = [0, 41, 0] := by
  obtain ⟨table, built, batch, accepted⟩ :=
    history_at_output captured scanned_execution invocations all_returned
  have positioned := positioned_at_output batch captured scanned_execution
  have literal : scanned.events.map
      (fun actual => (actual.position, actual.toSource AtomicEvents.orders)) =
      [(37, (⟨some 1, ⟨0⟩, .store .release 0xfedcba9876543210⟩ :
        C23Atomic.Event OS.Atomics64.CellId64 Word)),
       (39, ⟨some 0, ⟨0⟩, .load .acquire 0x1122334455667788⟩)] := by
    rw [literal_machine_events]
    rfl
  have metadata := literal_graph_metadata
  rw [built, Option.map_some] at metadata
  have exactMetadata : (table.sources, table.ranks) =
      ([none, none, some 0], [0, 41, 0]) := Option.some.inj metadata
  obtain ⟨store, member, thread, returned⟩ := batch.responded store_response
  exact ⟨table, built, batch, accepted, positioned.symm.trans literal,
    ⟨store, member, thread, returned⟩, congrArg Prod.fst exactMetadata, congrArg Prod.snd exactMetadata⟩

end EDSL.Tests.PlainMethodHistories

#print axioms EDSL.Tests.PlainMethodHistories.reader_current
#print axioms EDSL.Tests.PlainMethodHistories.reader_entry
#print axioms EDSL.Tests.PlainMethodHistories.captured
#print axioms EDSL.Tests.PlainMethodHistories.literal_machine_events
#print axioms EDSL.Tests.PlainMethodHistories.literal_graph_metadata
#print axioms EDSL.Tests.PlainMethodHistories.literal_runtime
#print axioms EDSL.Tests.PlainMethodHistories.integration_client
#audit_edsl
