/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.VCGen.PlainMethods.Correspondence
import EDSL.OS.TSO64.PublishedOrder
import tests.PlainCallBatch

/-!
One integration client of the production scanner and complete plain-call
adapter. All setup, admission, scheduling and completed-call extraction are
reused from PlainCallBatch. No fixture, scheduler or sorting is reconstructed.
Scanner existence follows from execution erasure and that actual six-action
run; scanner acceptance and candidate/call equality are not admission inputs.

The literal machine list retains the two different complete authority
references, the old full qword, the peer's new full qword, original positions
37/38 and the initializer read-source key. In the imported fixture the peer's
allocated store occurrence is zero: its writer key is `.store 1 0`, and its
counter after issue is one. The logical call occurrences are separate labels.
The observed RET indices remain 3/4, including the intervening peer drain.

This is structural correspondence for the sharedCell scalar-RAM model, with
the imported long-mode, CET-off, translation/alias, resource and queue-boundary
assumptions. Acquire/release orders are explicit interface annotations. The
empty incoming writer map denotes a boundary, not an invented earlier issue.
The candidate below has an empty initializer prefix and arbitrary RF/rank
metadata; Realizes establishes no Legal, History, universal C23, compiler,
final-ELF or native-execution claim. Published views concern publications only.
-/

set_option autoImplicit false

namespace EDSL.Tests.PlainEventCorrespondence
open X86 OS.TSO64 X86.VCGen.PlainMethods
open OS.TSO64.C23Projection Concurrency PlainCallBatch

theorem initial_valid : WellFormed initial .sharedCell := reader_current.valid

theorem initial_sequenced : Sequenced initial :=
  step_sequenced
    (attach_sequenced
      (attach_sequenced (sequenced_empty _) PlainCallInterference.reader_attached)
      PlainCallInterference.peer_attached)
    PlainCallInterference.own_issued

/-- Only repack the existing actual execution with a scanner-returned event
list. The theorem below proves that this is the scanner's own result. -/
def observed (events : List AtomicTrace.Event) : AtomicTrace.Result :=
  ⟨result.1, result.2, events⟩

/-- Closed existence from the real scheduled run, without evaluating another
fixture or assuming success of the scanner being exercised. -/
theorem scanner_exists :
    ∃ events, AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty =
      .ok (observed events) := by
  have erasure := AtomicTrace.scan_execution initial actions .sharedCell 37 PublishedHistory.empty
  rw [scheduled] at erasure
  cases scanned : AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty with
  | error fault =>
    have impossible : (Except.error fault : Except Fault (OS.TSO64.State × List Observation)) =
        .ok result := by
      simpa only [scanned, Except.map] using erasure
    cases impossible
  | ok run =>
    have same : run.execution = result := Except.ok.inj (by
      simpa only [scanned, Except.map] using erasure)
    refine ⟨run.events, congrArg Except.ok ?_⟩
    cases run with
    | mk state observations events =>
      exact congrArg (fun output : OS.TSO64.State × List Observation =>
        (⟨output.1, output.2, events⟩ : AtomicTrace.Result)) same

-- Recover slot order from the existing independently observed call chronology;
-- this neither inspects nor implements the adapter's sorting algorithm.
theorem chronological_slots (batch : BatchResult initial actions result invocations) :
    batch.slots = [peerSlot, readerSlot] := by
  have threads := congrArg (List.map (fun triple : Nat × Nat × Nat => triple.1))
    (chronological_calls batch)
  apply (List.map_inj_right (f := fun slot : Fin initial.workers.length => slot.val)
    (fun _ _ equal => Fin.ext equal)).mp
  change batch.slots.map (fun slot => slot.val) = [1, 0]
  simpa only [BatchResult.calls, List.map_map, Function.comp_def, BatchResult.call,
    CompletedCall.call, List.map_cons, List.map_nil] using threads

private theorem same_schedule_state {state : OS.TSO64.State} {plan : List Action}
    {first second : OS.TSO64.State} {observations : List Observation}
    (left : schedule state plan .sharedCell = .ok (first, observations))
    (right : schedule state plan .sharedCell = .ok (second, observations)) : first = second :=
  congrArg Prod.fst (Except.ok.inj (left.symm.trans right))

private theorem before_reader {before : OS.TSO64.State}
    (prefixRun : schedule initial (actions.take 1) .sharedCell =
      .ok (before, result.2.take 1)) : before = PlainCallInterference.boundary := by
  have actual : schedule initial (actions.take 1) .sharedCell =
      .ok (PlainCallInterference.boundary, result.2.take 1) := by
    change schedule initial [.issue 1 true] .sharedCell =
      .ok (PlainCallInterference.boundary, [PlainCallInterference.peerQueued.2])
    simp only [schedule, store_actual, ok_bind, pure_ok, PlainCallInterference.boundary]
  exact same_schedule_state prefixRun actual

private theorem writers_before_reader :
    PublishedHistory.after 37 (result.2.take 1) PublishedHistory.empty = PublishedHistory.empty := by
  change PublishedHistory.after 37 [PlainCallInterference.peerQueued.2] PublishedHistory.empty =
    PublishedHistory.empty
  rw [PlainCallInterference.prefix_created_entries.2.1]
  rfl

/-- Recover the saved reply from the actual access prefix and local qword read.
No proposed reply, final RAX or later shared-memory value is supplied to it. -/
theorem reader_value (batch : BatchResult initial actions result invocations) :
    (batch.completed readerSlot).reply = (0x1122334455667788 : Word) := by
  let completed : CompletedCall PlainCallInterference.method 0 initial actions result :=
    batch.completed readerSlot
  have performed : completed.performed = 1 :=
    (completed.performed_unique reader_dispatched).symm
  have access : AccessAt PlainCallInterference.method 0 initial actions result 1 completed.reply := by
    simpa only [performed] using completed.access
  obtain ⟨before, _, _, prefixRun, _, _, _, origin⟩ := access
  have sameBefore := before_reader prefixRun
  subst before
  obtain ⟨_, worker, _, workerLive, _, _, _, _, _, _, _, _, _, value⟩ := origin.evidence
  have sameWorker : worker = PlainCallInterference.boundaryReader :=
    Option.some.inj (workerLive.symm.trans PlainCallInterference.live)
  subst worker
  have read : loadQWord (localCPU PlainCallInterference.boundary
      PlainCallInterference.boundaryReader).memory 65536 = .ok completed.reply := value.1
  exact Except.ok.inj (read.symm.trans PlainCallInterference.boundary_reads.1)

private theorem load_key {state : OS.TSO64.State} {action : Action}
    {first : OS.TSO64.State × Observation} {position tid : Nat}
    {writers : PublishedHistory.Writers} {reference : Queue.ManagedRef}
    {value : Word} {source : AtomicTrace.WriterId}
    (actual : AtomicTrace.AtomicStep state action first .sharedCell position writers
      ⟨position, tid, .load reference value source⟩) :
    ∃ worker, state.workers[tid]? = some worker ∧
      AtomicTrace.readKey worker tid reference writers = some source := by
  cases actual with
  | load origin live read => exact ⟨_, live, read.key⟩

-- Scanner soundness identifies the actual input worker and prefix writer map.
-- Payload equality is never used to select a writer identity.
private theorem reader_source {events : List AtomicTrace.Event} {source : AtomicTrace.WriterId}
    (success : AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty =
      .ok (observed events))
    (member : (⟨38, 0, .load PlainMethodAdmission.reference 0x1122334455667788 source⟩ :
      AtomicTrace.Event) ∈ events) : source = .initial ⟨0⟩ := by
  obtain ⟨index, origin⟩ := AtomicTrace.scan_sound initial_valid initial_sequenced success member
  have position := origin.position
  change 38 = 37 + index at position
  have indexEq : index = 1 := by omega
  subst index
  obtain ⟨before, _, _, prefixRun, _, _, _, atomic⟩ := origin.prestate
  have sameBefore := before_reader prefixRun
  subst before
  obtain ⟨worker, workerLive, key⟩ := load_key atomic
  have sameWorker : worker = PlainCallInterference.boundaryReader :=
    Option.some.inj (workerLive.symm.trans PlainCallInterference.live)
  subst worker
  change AtomicTrace.readKey PlainCallInterference.boundaryReader 0
    PlainMethodAdmission.reference
      (PublishedHistory.after 37 (result.2.take 1) PublishedHistory.empty) = some source at key
  rw [writers_before_reader] at key
  have absent := PlainCallInterference.boundary_reads.2.1
  change StoreBuffer.Mixed.newestQWord (payload PlainCallInterference.boundaryReader.pending)
    PlainMethodAdmission.reference.cell.address = none at absent
  have expected : AtomicTrace.readKey PlainCallInterference.boundaryReader 0
      PlainMethodAdmission.reference PublishedHistory.empty = some (.initial ⟨0⟩) := by
    simp only [AtomicTrace.readKey, absent, AtomicTrace.publishedSource, PublishedHistory.empty]
    rfl
  exact Option.some.inj (key.symm.trans expected)

-- Keep execution transport abstract instead of unfolding the concrete fixture
-- while elaborating the adapters' dependent batch indices.
private theorem output_correspondence {state : OS.TSO64.State} {plan : List Action}
    {output : OS.TSO64.State × List Observation}
    {entries : (tid : Fin state.workers.length) → Invocation state tid.val}
    {offset : Nat} {writers : PublishedHistory.Writers} {events : List AtomicTrace.Event}
    (batch : BatchResult state plan output entries)
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (success : AtomicTrace.scan state plan .sharedCell offset writers =
      .ok ⟨output.1, output.2, events⟩) :
    (∃ sources : Fin state.workers.length → AtomicTrace.WriterId,
      events = batch.slots.map (fun slot => AtomicEvents.event (entries slot).method slot.val
        (offset + (batch.completed slot).performed) (batch.completed slot).reply (sources slot))) ∧
    events.map (fun actual => actual.toSource AtomicEvents.orders) =
      batch.calls.map AtomicCalls.Call.event ∧
    events.map (fun actual => (actual.position, actual.toSource AtomicEvents.orders)) =
      batch.calls.map (fun actual => (offset + actual.performed, actual.event)) := by
  exact ⟨Correspondence.machine_events batch valid sequenced success,
    Correspondence.source_events batch valid sequenced success,
    Correspondence.positioned_events batch valid sequenced success⟩

private theorem output_realizes {state : OS.TSO64.State} {plan : List Action}
    {output : OS.TSO64.State × List Observation}
    {entries : (tid : Fin state.workers.length) → Invocation state tid.val}
    {offset : Nat} {writers : PublishedHistory.Writers} {events : List AtomicTrace.Event}
    (batch : BatchResult state plan output entries)
    (valid : WellFormed state .sharedCell) (sequenced : Sequenced state)
    (success : AtomicTrace.scan state plan .sharedCell offset writers =
      .ok ⟨output.1, output.2, events⟩)
    {c : C23Atomic.Candidate OS.Atomics64.CellId64 Word}
    (bound : c.events = events.map (fun actual => actual.toSource AtomicEvents.orders)) :
    AtomicCalls.Realizes [] batch.calls c := by
  apply Correspondence.realizes batch valid sequenced success
  · exact bound
  · intro actual impossible
    cases impossible

private theorem peer_initial_counter : PlainCallInterference.peer.nextStore = 0 := by
  decide +kernel

private theorem packed_execution (output : OS.TSO64.State × List Observation)
    (events : List AtomicTrace.Event) :
    (⟨output.1, output.2, events⟩ : AtomicTrace.Result).execution = output := by
  cases output
  rfl

private theorem peer_invocation_method : (invocations peerSlot).method = peerMethod := by
  rfl

private theorem peer_event_data (position : Nat)
    (reply : (invocations peerSlot).method.operation.Reply) (source : AtomicTrace.WriterId) :
    AtomicEvents.event (invocations peerSlot).method peerSlot.val position reply source =
      ⟨position, 1, .store peerReference 0xfedcba9876543210 0⟩ := by
  revert reply
  rw [peer_invocation_method]
  intro reply
  dsimp only [peerMethod, AtomicEvents.event, AtomicEvents.access]
  simp only [peer_initial_counter]
  rfl

private theorem peer_event (batch : BatchResult initial actions result invocations)
    (source : AtomicTrace.WriterId) :
    AtomicEvents.event (invocations peerSlot).method peerSlot.val
      (37 + (batch.completed peerSlot).performed) (batch.completed peerSlot).reply source =
      ⟨37, 1, .store peerReference 0xfedcba9876543210 0⟩ := by
  have performed : (batch.completed peerSlot).performed = 0 :=
    ((batch.completed peerSlot).performed_unique store_dispatched).symm
  rw [performed]
  exact peer_event_data 37 (batch.completed peerSlot).reply source

private theorem reader_event (batch : BatchResult initial actions result invocations)
    (source : AtomicTrace.WriterId) :
    AtomicEvents.event (invocations readerSlot).method readerSlot.val
      (37 + (batch.completed readerSlot).performed) (batch.completed readerSlot).reply source =
      ⟨38, 0, .load PlainMethodAdmission.reference 0x1122334455667788 source⟩ := by
  have performed : (batch.completed readerSlot).performed = 1 :=
    ((batch.completed readerSlot).performed_unique reader_dispatched).symm
  rw [performed]
  change (⟨38, 0, .load PlainMethodAdmission.reference (batch.completed readerSlot).reply source⟩ :
    AtomicTrace.Event) = _
  rw [reader_value batch]

/-- Independent requirements for every machine event, in order. The complete
references distinguish the peer handle from the reader handle on the same cell.
The occurrence zero is distinct from nextStore=1 and logical occurrence=17. -/
def expectedEvents : List AtomicTrace.Event :=
  [⟨37, 1, .store peerReference 0xfedcba9876543210 0⟩,
   ⟨38, 0, .load PlainMethodAdmission.reference 0x1122334455667788 (.initial ⟨0⟩)⟩]

theorem literal_machine_events (batch : BatchResult initial actions result invocations)
    {events : List AtomicTrace.Event}
    (success : AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty =
      .ok (observed events)) : events = expectedEvents := by
  obtain ⟨⟨sources, machine⟩, _, _⟩ :=
    output_correspondence batch initial_valid initial_sequenced success
  have literal : events =
      [⟨37, 1, .store peerReference 0xfedcba9876543210 0⟩,
       ⟨38, 0, .load PlainMethodAdmission.reference 0x1122334455667788 (sources readerSlot)⟩] := by
    simpa only [observed, chronological_slots batch, List.map_cons, List.map_nil,
      peer_event batch, reader_event batch] using machine
  have member : (⟨38, 0, .load PlainMethodAdmission.reference 0x1122334455667788
      (sources readerSlot)⟩ : AtomicTrace.Event) ∈ events := by
    rw [literal]
    simp
  have key := reader_source success member
  rw [key] at literal
  exact literal

/-- The event binding uses the actual scanner list. RF and rank remain
arbitrary data because only structural Realizes is exercised here. -/
def candidate (run : AtomicTrace.Result) (readsFrom : Nat → Option Nat) (rank : Nat → Nat) :
    C23Atomic.Candidate OS.Atomics64.CellId64 Word where
  events := run.events.map (fun actual => actual.toSource AtomicEvents.orders)
  readsFrom := readsFrom
  rank := rank

structure Regression (run : AtomicTrace.Result)
    (batch : BatchResult initial actions result invocations) : Prop where
  scanned : AtomicTrace.scan initial actions .sharedCell 37 PublishedHistory.empty = .ok run
  execution : run.execution = result
  machine : ∃ sources : Fin initial.workers.length → AtomicTrace.WriterId,
    run.events = batch.slots.map (fun slot =>
      AtomicEvents.event (invocations slot).method slot.val
        (37 + (batch.completed slot).performed) (batch.completed slot).reply (sources slot))
  source : run.events.map (fun actual => actual.toSource AtomicEvents.orders) =
    batch.calls.map AtomicCalls.Call.event
  positioned : run.events.map (fun actual => (actual.position, actual.toSource AtomicEvents.orders)) =
    batch.calls.map (fun actual => (37 + actual.performed, actual.event))
  literal : run.events = expectedEvents
  slots : batch.slots = [peerSlot, readerSlot]
  calls : batch.calls.map (fun actual => (actual.thread, actual.performed, actual.returned)) =
    [(1, 0, 3), (0, 1, 4)]
  positionedCalls : batch.calls.map (fun actual => (37 + actual.performed, actual.event)) =
    [(37, ⟨some 1, ⟨0⟩, .store .release 0xfedcba9876543210⟩),
     (38, ⟨some 0, ⟨0⟩, .load .acquire 0x1122334455667788⟩)]
  returned : [Return.returnValue peerReturned, Return.returnValue readerReturned] =
    [some (1, 5), some (0, 0x1122334455667788)]
  published : PlainMethods.worldWords run.state =
    [.ok 9, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000]
  monotone : ∀ first last : Nat, first ≤ last → ∀ target : OS.Atomics64.CellId64,
    PublishedOrder.view (PublishedHistory.after 37 (run.observations.take first)
      PublishedHistory.empty) target ≤
    PublishedOrder.view (PublishedHistory.after 37 (run.observations.take last)
      PublishedHistory.empty) target
  realizes : ∀ (readsFrom : Nat → Option Nat) (rank : Nat → Nat),
    AtomicCalls.Realizes [] batch.calls (candidate run readsFrom rank)

private theorem published_words (events : List AtomicTrace.Event) :
    PlainMethods.worldWords (observed events).state =
      [.ok 9, .ok 0, .ok 0xfedcba9876543210, .ok 0xabcdef0123456789, .ok 0x7000, .ok 0x8000] := by
  simpa only [observed] using literal_runtime.2.2.2.2.1

/-- One closed actual-scanner client of all three whole-list correspondence
APIs and Realizes. Literal machine/source requirements rule out event omission,
reversal, slot sorting, compressed RET indices, truncated words and mistaken
read-source identities. The newer published word is an actual runtime output.
Monotonicity is instantiated on those same scanner observations at offset 37. -/
theorem integration_client :
    ∃ (run : AtomicTrace.Result) (batch : BatchResult initial actions result invocations),
      Regression run batch := by
  obtain ⟨events, success⟩ := scanner_exists
  obtain ⟨batch⟩ := admitted_batch
  have literal := literal_machine_events batch success
  obtain ⟨machine, source, positioned⟩ :=
    output_correspondence batch initial_valid initial_sequenced success
  have located : (observed events).events.map
      (fun actual => (actual.position, actual.toSource AtomicEvents.orders)) =
      [(37, (⟨some 1, ⟨0⟩, .store .release 0xfedcba9876543210⟩ :
        C23Atomic.Event OS.Atomics64.CellId64 Word)),
       (38, ⟨some 0, ⟨0⟩, .load .acquire 0x1122334455667788⟩)] := by
    change events.map (fun actual => (actual.position, actual.toSource AtomicEvents.orders)) = _
    rw [literal]
    rfl
  refine ⟨observed events, batch, {
    scanned := success
    execution := packed_execution result events
    machine := machine
    source := source
    positioned := positioned
    literal := literal
    slots := chronological_slots batch
    calls := chronological_calls batch
    positionedCalls := positioned.symm.trans located
    returned := literal_runtime.2.2.1
    published := published_words events
    monotone := ?_
    realizes := ?_ }⟩
  · intro first last ordered target
    exact PublishedOrder.prefix_view (observations := (observed events).observations)
      (PublishedOrder.prior_empty 37) ordered target
  · intro readsFrom rank
    apply output_realizes batch initial_valid initial_sequenced success
    rfl

end EDSL.Tests.PlainEventCorrespondence

#print axioms EDSL.Tests.PlainEventCorrespondence.initial_sequenced
#print axioms EDSL.Tests.PlainEventCorrespondence.scanner_exists
#print axioms EDSL.Tests.PlainEventCorrespondence.chronological_slots
#print axioms EDSL.Tests.PlainEventCorrespondence.reader_value
#print axioms EDSL.Tests.PlainEventCorrespondence.literal_machine_events
#print axioms EDSL.Tests.PlainEventCorrespondence.integration_client
#audit_edsl
