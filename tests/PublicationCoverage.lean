/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64CrossCellFixtures
import EDSL.OS.TSO64.ExecutionViews.PublicationCovers
import EDSL.OS.TSO64.ExecutionViews.Query
import EDSL.OS.TSO64.StoreHistory.Trace
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Capture
import EDSL.Audit

/-!
Actual two-cell publication-coverage clients. A uses allocation 0 at 65536;
B uses separate allocation 6 at 458752. Both workers retain current handles to
both cells, and original code/caller/private resources. The ordinary dword
store at privateData+4 is mixed into the same FIFO as two managed qword stores.

The naturally aligned ordinary store is 89 31, MOV dword [RCX],ESI. The remaining
instructions are MOV qword [RDI],RSI; MOV qword [RDX],RSI; LOCK XADD qword
[RDX],RSI; RET. Their byte offsets are 0/2/5/8/13, so the peer starts at 5.

Actual store and access scans produce their own annotations. Independent
literal contracts below specify positions, values and full writer identities.
Real indexed issues and real publications construct InstructionWriteAt;
successful queries become actual At witnesses through query_sound. Numerical
coverage is obtained only by invoking the universal covers_after theorem.

These are finite stable-resource scalar-RAM, long-mode/CET-off clients. They
make no source-release, HB, C23 legality, fairness, native, ELF or corpus claim.
The access scanner's namespace supplies no source-language interpretation here.
-/

set_option autoImplicit false

namespace EDSL.Tests.PublicationCoverage
open X86 OS.TSO64 OS.TSO64.PublishedHistory OS.TSO64.ExecutionViews

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private theorem found_ok {α : Type} (value : Option α) (present : value.isSome = true) :
    value = some (value.get present) := by
  cases value with
  | none => cases present
  | some value => rfl

def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64CrossCellFixtures.start TSO64CrossCellFixtures.codeFirst TSO64CrossCellFixtures.codeSecond
    3 5 7 11 0 TSO64CrossCellFixtures.peerOffset

theorem initial_succeeds : initialAttempt.toOption.isSome = true := by decide +kernel

def initial : OS.TSO64.State := checked initialAttempt initial_succeeds

theorem initial_actual : initialAttempt = .ok initial := checked_ok _ _

theorem initial_valid : WellFormed initial .sharedCell :=
  TSO64CrossCellFixtures.start_valid initial_actual

/-- The ordinary head and A/B stores all precede the own RMW. Both blocked
attempts count, and peer B is published between the ordinary head and own A. -/
def actions : List Action :=
  [.issue 0 false, .issue 0 true, .issue 1 false, .issue 0 false,
    .issue 0 true, .drain 0, .drain 1, .drain 0,
    .issue 0 false, .drain 0, .issue 0 true, .issue 1 false,
    .issue 0 false, .issue 1 true]

def scanAttempt : Except Fault StoreHistory.Trace.Result :=
  StoreHistory.Trace.scan initial actions .sharedCell 37

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

def scanned : StoreHistory.Trace.Result := checked scanAttempt scan_succeeds

theorem scanned_actual : StoreHistory.Trace.scan initial actions .sharedCell 37 = .ok scanned :=
  checked_ok _ _

def result : OS.TSO64.State × List Observation := scanned.execution

theorem scheduled : schedule initial actions .sharedCell = .ok result :=
  StoreHistory.Trace.scan_scheduled scanned_actual

def annotatedAttempt : Except Fault C23Projection.AtomicTrace.Result :=
  C23Projection.AtomicTrace.scan initial actions .sharedCell 37 empty

theorem annotation_succeeds : annotatedAttempt.toOption.isSome = true := by decide +kernel

def annotated : C23Projection.AtomicTrace.Result := checked annotatedAttempt annotation_succeeds

theorem annotated_actual : C23Projection.AtomicTrace.scan initial actions .sharedCell 37 empty = .ok annotated :=
  checked_ok _ _

/-- Both independently run production scans erase to exactly the same real
state and observations, by scheduler determinism. -/
theorem scans_agree : annotated.execution = result :=
  Except.ok.inj ((C23Projection.AtomicTrace.scan_scheduled annotated_actual).symm.trans scheduled)

private theorem prefix_succeeds (cut : Nat) :
    (schedule initial (actions.take cut) .sharedCell).toOption.isSome = true := by
  obtain ⟨before, success, _suffix⟩ := ScheduleTrace.cut scheduled cut
  rw [success]
  rfl

def atCut (cut : Nat) : OS.TSO64.State × List Observation :=
  checked (schedule initial (actions.take cut) .sharedCell) (prefix_succeeds cut)

theorem prefix_scheduled (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell = .ok (atCut cut) := checked_ok _ _

theorem prefix_exact (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell =
      .ok ((atCut cut).1, result.2.take cut) := by
  have same := (ScheduleTrace.suffix scheduled (prefix_scheduled cut)).1
  rw [← same]
  exact prefix_scheduled cut

theorem initial_queues : initial.workers.map Worker.pending = [[], []] := by decide +kernel
theorem final_queues : result.1.workers.map Worker.pending = [[], []] := by decide +kernel

private theorem quiescent_of_queues {state : OS.TSO64.State}
    (emptyQueues : state.workers.map Worker.pending = [[], []]) : Quiescent state := by
  intro worker member
  have mapped : worker.pending ∈ state.workers.map Worker.pending :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  rw [emptyQueues] at mapped
  simpa using mapped

theorem initial_quiescent : Quiescent initial := quiescent_of_queues initial_queues

theorem initial_sequenced : Sequenced initial := by
  intro worker member
  have noPending := initial_quiescent worker member
  simp [Worker.storeCursor, Queue.Cursor.Ordered, noPending]

/-- Quiescence is checked from both actual final queues, independently of RET. -/
theorem final_quiescent : Quiescent result.1 := quiescent_of_queues final_queues

theorem execution : Execution initial actions result .sharedCell :=
  ⟨scheduled, initial_valid, initial_sequenced, final_quiescent⟩

theorem store_certificate : StoreHistory.Trace.Certificate initial actions .sharedCell 37 scanned :=
  StoreHistory.Trace.scan_certificate scanned_actual

theorem access_certificate :
    C23Projection.AtomicTrace.Certificate initial actions .sharedCell 37 empty annotated :=
  C23Projection.AtomicTrace.scan_certificate initial_valid initial_sequenced annotated_actual

def ownWorker : Worker := (initial.workers[0]?).get (by decide +kernel)
def peerWorker : Worker := (initial.workers[1]?).get (by decide +kernel)

theorem own_live : initial.workers[0]? = some ownWorker := found_ok _ _
theorem peer_live : initial.workers[1]? = some peerWorker := found_ok _ _

private def referenceAt (index : Nat) : Option Queue.ManagedRef := do
  let issue ← scanned.issues[index]?
  match issue.entry with
  | .ordinary _ _ => none
  | .managed reference _ _ => some reference

/-- These are the complete actual admitted descriptors, never address-built
substitutes. Equal own values on A and B cannot select either descriptor. -/
def referenceA : Queue.ManagedRef := (referenceAt 1).get (by decide +kernel)
def referenceB : Queue.ManagedRef := (referenceAt 3).get (by decide +kernel)
def peerReferenceB : Queue.ManagedRef := (referenceAt 2).get (by decide +kernel)

private def eventAt (index : Nat) : Option OS.Atomics64.FetchAddEvent := do
  let observation ← result.2[index]?
  match observation with
  | .rmw _ event => some event
  | _ => none

def ownEvent : OS.Atomics64.FetchAddEvent := (eventAt 10).get (by decide +kernel)
def peerEvent : OS.Atomics64.FetchAddEvent := (eventAt 11).get (by decide +kernel)

/-- Literal independent authority/epoch/allocation identities of the actual
decoded admissions. B is not a second address in A's reserved allocation. -/
theorem descriptors_exact :
    referenceA = ⟨⟨0⟩, ⟨11, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩⟩ ∧
    referenceB = ⟨⟨2⟩, ⟨11, ⟨1⟩⟩, ⟨7, ⟨6, 0⟩, 458752⟩⟩ ∧
    peerReferenceB = ⟨⟨3⟩, ⟨12, ⟨1⟩⟩, ⟨7, ⟨6, 0⟩, 458752⟩⟩ := by
  decide +kernel

theorem separate_cells_and_allocations :
    referenceA.handle.cell ≠ referenceB.handle.cell ∧
    referenceA.cell.ticket.identifier ≠ referenceB.cell.ticket.identifier ∧
    peerReferenceB.cell = referenceB.cell ∧ peerReferenceB.identifier ≠ referenceB.identifier := by
  rw [descriptors_exact.1, descriptors_exact.2.1, descriptors_exact.2.2]
  decide

theorem targetA_current : Queue.Current initial.world ownWorker.resources referenceA := by decide +kernel
theorem targetB_current : Queue.Current initial.world ownWorker.resources referenceB := by decide +kernel
theorem peer_targetB_current : Queue.Current initial.world peerWorker.resources peerReferenceB := by
  decide +kernel

/-- The complete issue list detects omitted or invented stores, consumes an
occurrence for the ordinary dword head, and excludes both blocked attempts. -/
theorem issues_exact : scanned.issues =
    [⟨37, 0, .ordinary ⟨1, 0⟩ ⟨131076, .dword 7⟩⟩,
      ⟨38, 0, .managed referenceA 7 1⟩,
      ⟨39, 1, .managed peerReferenceB 11 0⟩,
      ⟨40, 0, .managed referenceB 7 2⟩] := by decide +kernel

theorem observations_exact : result.2 =
    [.ordinary 0, .ordinary 0, .ordinary 1, .ordinary 0,
      .blocked 0, .drained 0 (.ordinary ⟨1, 0⟩ ⟨131076, .dword 7⟩),
      .drained 1 (.managed peerReferenceB 11 0),
      .drained 0 (.managed referenceA 7 1), .blocked 0,
      .drained 0 (.managed referenceB 7 2), .rmw 0 ownEvent, .rmw 1 peerEvent,
      .returned 0, .returned 1] := by decide +kernel

/-- Arithmetic and authority are specified independently of event extraction. -/
theorem own_event_contract :
    ownEvent.actor = 11 ∧ ownEvent.handle = referenceB.identifier ∧
    ownEvent.cell = referenceB.handle.cell ∧ ownEvent.arithmetic.delta = 7 ∧
    ownEvent.arithmetic.event.address = 458752 ∧
    ownEvent.arithmetic.event.before = 7 ∧ ownEvent.arithmetic.event.after = 14 := by
  decide +kernel

theorem peer_event_contract :
    peerEvent.actor = 12 ∧ peerEvent.handle = peerReferenceB.identifier ∧
    peerEvent.cell = referenceB.handle.cell ∧ peerEvent.arithmetic.delta = 11 ∧
    peerEvent.arithmetic.event.address = 458752 ∧
    peerEvent.arithmetic.event.before = 14 ∧ peerEvent.arithmetic.event.after = 25 := by
  decide +kernel

/-- The actual access scanner omits ordinary RAM and the two blocked attempts.
Its RMW sources retain the exact previous buffered occurrence / RMW position. -/
theorem annotations_exact : annotated.events =
    [⟨38, 0, .store referenceA 7 1⟩,
      ⟨39, 1, .store peerReferenceB 11 0⟩,
      ⟨40, 0, .store referenceB 7 2⟩,
      ⟨47, 0, .rmw ownEvent (.store 0 2)⟩,
      ⟨48, 1, .rmw peerEvent (.rmw 47)⟩] := by decide +kernel

private theorem scan_issue_at {state : OS.TSO64.State} {actions : List Action}
    {profile : Profile} {offset index tid : Nat} {entry : Pending}
    {scanned : StoreHistory.Trace.Result}
    (success : StoreHistory.Trace.scan state actions profile offset = .ok scanned)
    (member : (⟨offset + index, tid, entry⟩ : StoreHistory.Trace.Issue) ∈ scanned.issues) :
    StoreHistory.IssuedAt profile tid entry index state actions scanned.execution := by
  obtain ⟨actualIndex, position, actual⟩ := (StoreHistory.Trace.scan_issues_iff success).mp member
  change offset + index = offset + actualIndex at position
  have same : actualIndex = index := by omega
  subst actualIndex
  exact actual

theorem ownA_issued :
    StoreHistory.IssuedAt .sharedCell 0 (.managed referenceA 7 1) 1 initial actions result := by
  apply scan_issue_at scanned_actual
  rw [issues_exact]
  simp

theorem ownB_issued :
    StoreHistory.IssuedAt .sharedCell 0 (.managed referenceB 7 2) 3 initial actions result := by
  apply scan_issue_at scanned_actual
  rw [issues_exact]
  simp

theorem peerB_issued :
    StoreHistory.IssuedAt .sharedCell 1 (.managed peerReferenceB 11 0) 2 initial actions result := by
  apply scan_issue_at scanned_actual
  rw [issues_exact]
  simp

private theorem rmw_instruction_at {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile} {offset index tid : Nat}
    {event : OS.Atomics64.FetchAddEvent}
    (success : schedule state actions profile = .ok result)
    (observed : result.2[index]? = some (.rmw tid event)) :
    ∃ actual : InstructionWriteAt state actions result profile offset index
      ⟨offset + index, .rmw tid event⟩, actual.publication.index = index := by
  obtain ⟨before, action, next, prefixRun, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  let publication : WriteAt state actions result profile offset ⟨offset + index, .rmw tid event⟩ :=
    ⟨index, .rmw tid event, before, action, next, rfl, observed, prefixRun, actionAt, stepped, rfl⟩
  exact ⟨InstructionWriteAt.rmw publication, rfl⟩

def ownAStamp : Stamp := ⟨44, .buffered 0 referenceA 7 1⟩
def peerBStamp : Stamp := ⟨43, .buffered 1 peerReferenceB 11 0⟩
def ownBStamp : Stamp := ⟨46, .buffered 0 referenceB 7 2⟩
def ownRMWStamp : Stamp := ⟨47, .rmw 0 ownEvent⟩
def peerRMWStamp : Stamp := ⟨48, .rmw 1 peerEvent⟩

/-- Every managed write has both its actual instruction and actual publication
witness, including the two distinct cells accessed by the same worker. -/
theorem instruction_writes :
    ∃ ownA : InstructionWriteAt initial actions result .sharedCell 37 1 ownAStamp,
    ∃ peerB : InstructionWriteAt initial actions result .sharedCell 37 2 peerBStamp,
    ∃ ownB : InstructionWriteAt initial actions result .sharedCell 37 3 ownBStamp,
    ∃ ownRMW : InstructionWriteAt initial actions result .sharedCell 37 10 ownRMWStamp,
    ∃ peerRMW : InstructionWriteAt initial actions result .sharedCell 37 11 peerRMWStamp,
      ownA.publication.index = 7 ∧ peerB.publication.index = 6 ∧
      ownB.publication.index = 9 ∧ ownRMW.publication.index = 10 ∧ peerRMW.publication.index = 11 := by
  have observedA : result.2[7]? = some (.drained 0 (.managed referenceA 7 1)) := by
    rw [observations_exact]; rfl
  have observedPeerB : result.2[6]? = some (.drained 1 (.managed peerReferenceB 11 0)) := by
    rw [observations_exact]; rfl
  have observedB : result.2[9]? = some (.drained 0 (.managed referenceB 7 2)) := by
    rw [observations_exact]; rfl
  have observedOwnRMW : result.2[10]? = some (.rmw 0 ownEvent) := by
    rw [observations_exact]; rfl
  have observedPeerRMW : result.2[11]? = some (.rmw 1 peerEvent) := by
    rw [observations_exact]; rfl
  obtain ⟨a, aIndex⟩ := managed_drain_writeAt (offset := 37) scheduled observedA
  obtain ⟨peer, peerIndex⟩ := managed_drain_writeAt (offset := 37) scheduled observedPeerB
  obtain ⟨b, bIndex⟩ := managed_drain_writeAt (offset := 37) scheduled observedB
  obtain ⟨ownRMW, ownRMWIndex⟩ := rmw_instruction_at (offset := 37) scheduled observedOwnRMW
  obtain ⟨peerRMW, peerRMWIndex⟩ := rmw_instruction_at (offset := 37) scheduled observedPeerRMW
  exact ⟨InstructionWriteAt.buffered ownA_issued a, InstructionWriteAt.buffered peerB_issued peer,
    InstructionWriteAt.buffered ownB_issued b, ownRMW, peerRMW,
    aIndex, peerIndex, bIndex, ownRMWIndex, peerRMWIndex⟩

def publications : List Stamp := C23Projection.writes 37 result.2

theorem publications_exact : publications =
    [peerBStamp, ownAStamp, ownBStamp, ownRMWStamp, peerRMWStamp] := by
  rw [publications, observations_exact]
  rfl

theorem literal_positions_and_ranks :
    scanned.issues.map StoreHistory.Trace.Issue.position = [37, 38, 39, 40] ∧
    publications.map Stamp.position = [43, 44, 46, 47, 48] ∧
    publications.map (fun stamp => stamp.position + 1) = [44, 45, 47, 48, 49] := by
  rw [issues_exact, publications_exact]
  exact ⟨rfl, rfl, rfl⟩

def queried (cut tid : Nat) (target : Queue.ManagedRef) : Option Nat :=
  query (atCut cut).1 result.2 cut tid target 37 empty

theorem cut4_queries :
    queried 4 0 referenceA = some 45 ∧ queried 4 0 referenceB = some 47 ∧
    queried 4 1 referenceB = some 44 := by decide +kernel

theorem cut11_queries :
    queried 11 0 referenceA = some 45 ∧ queried 11 0 referenceB = some 48 := by decide +kernel

theorem cut12_query : queried 12 0 referenceB = some 49 := by decide +kernel

/-- Full execution, current original authority, and actual finite prefixes
turn query results into actual sources, rather than desired rank hypotheses. -/
theorem queried_at {cut tid value : Nat} {worker : Worker} {resources : Resources}
    {target : Queue.ManagedRef}
    (live : initial.workers[tid]? = some worker)
    (current : Queue.Current initial.world resources target)
    (answered : queried cut tid target = some value) :
    Nonempty (At initial actions result .sharedCell cut tid target 37 empty value) :=
  query_sound execution live (prefix_exact cut) current answered

theorem actual_after_B_store_A :
    Nonempty (At initial actions result .sharedCell 4 0 referenceA 37 empty 45) :=
  queried_at own_live targetA_current cut4_queries.1

theorem actual_after_B_store_B :
    Nonempty (At initial actions result .sharedCell 4 0 referenceB 37 empty 47) :=
  queried_at own_live targetB_current cut4_queries.2.1

theorem actual_after_B_store_peer :
    Nonempty (At initial actions result .sharedCell 4 1 referenceB 37 empty 44) :=
  queried_at peer_live targetB_current cut4_queries.2.2

theorem actual_after_RMW_A :
    Nonempty (At initial actions result .sharedCell 11 0 referenceA 37 empty 45) :=
  queried_at own_live targetA_current cut11_queries.1

theorem actual_after_RMW_B :
    Nonempty (At initial actions result .sharedCell 11 0 referenceB 37 empty 48) :=
  queried_at own_live targetB_current cut11_queries.2

/-- Arbitrary target, incoming metadata and actual postview. No same-cell,
single-access, desired view order or initial-empty premise enters this client.
The real B store's complete issue/publication witness supplies the bound. -/
theorem store_covers_every_actual_target {target : Queue.ManagedRef} {incoming : Writers} {value : Nat}
    (prior : PublishedOrder.Prior 37 incoming)
    (view : At initial actions result .sharedCell 4 0 target 37 incoming value) : value ≤ 47 := by
  obtain ⟨_ownA, _peerB, ownB, _ownRMW, _peerRMW, _indices⟩ := instruction_writes
  exact InstructionWriteAt.covers_after execution prior ownB view

/-- The RMW branch uses its own real postcut. Final emptiness is separately
established from the actual queues and is never inferred from RET. -/
theorem rmw_covers_every_actual_target {target : Queue.ManagedRef} {incoming : Writers} {value : Nat}
    (prior : PublishedOrder.Prior 37 incoming)
    (view : At initial actions result .sharedCell 11 0 target 37 incoming value) : value ≤ 48 := by
  obtain ⟨_ownA, _peerB, _ownB, ownRMW, _peerRMW, _indices⟩ := instruction_writes
  exact InstructionWriteAt.covers_after execution prior ownRMW view

/-- Both different-cell and same-cell literal postviews instantiate the same
universal coverage contract on actual At witnesses. -/
theorem store_covers_both_cells :
    (∃ _view : At initial actions result .sharedCell 4 0 referenceA 37 empty 45,
      45 ≤ ownBStamp.position + 1) ∧
    (∃ _view : At initial actions result .sharedCell 4 0 referenceB 37 empty 47,
      47 ≤ ownBStamp.position + 1) := by
  obtain ⟨a⟩ := actual_after_B_store_A
  obtain ⟨b⟩ := actual_after_B_store_B
  exact ⟨⟨a, store_covers_every_actual_target (PublishedOrder.prior_empty 37) a⟩,
    ⟨b, store_covers_every_actual_target (PublishedOrder.prior_empty 37) b⟩⟩

theorem rmw_covers_both_cells :
    (∃ _view : At initial actions result .sharedCell 11 0 referenceA 37 empty 45,
      45 ≤ ownRMWStamp.position + 1) ∧
    (∃ _view : At initial actions result .sharedCell 11 0 referenceB 37 empty 48,
      48 ≤ ownRMWStamp.position + 1) := by
  obtain ⟨a⟩ := actual_after_RMW_A
  obtain ⟨b⟩ := actual_after_RMW_B
  exact ⟨⟨a, rmw_covers_every_actual_target (PublishedOrder.prior_empty 37) a⟩,
    ⟨b, rmw_covers_every_actual_target (PublishedOrder.prior_empty 37) b⟩⟩

/-- At cut four the ordinary head and both managed cells really coexist;
pending views cannot be implemented as a same-cell singleton special case. -/
theorem mixed_cross_cell_FIFO :
    ((atCut 4).1.workers[0]?).map (fun worker => (worker.pending, worker.nextStore)) =
      some ([.ordinary ⟨1, 0⟩ ⟨131076, .dword 7⟩,
        .managed referenceA 7 1, .managed referenceB 7 2], 3) ∧
    (loadQWord (published (atCut 4).1.world) 65536).toOption = some 3 ∧
    (loadQWord (published (atCut 4).1.world) 458752).toOption = some 5 := by
  decide +kernel

/-- At the second blocked attempt A has already published, B remains queued,
and peer B's earlier write is in RAM. Own LOCK cannot bypass that FIFO tail. -/
theorem blocked_after_A_publication :
    ((atCut 9).1.workers[0]?).map (fun worker =>
      (worker.pending, worker.nextStore, worker.context.rip)) =
      some ([.managed referenceB 7 2], 3, 393224) ∧
    (loadQWord (published (atCut 9).1.world) 65536).toOption = some 7 ∧
    (loadQWord (published (atCut 9).1.world) 458752).toOption = some 11 := by
  decide +kernel

private def resourceView (worker : Worker) :
    Nat × Lease × Lease × Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64 :=
  (worker.resources.actor, worker.resources.code, worker.resources.caller,
    worker.resources.callerAddress, worker.resources.grants, worker.resources.atomics)

private instance : DecidableEq (Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64) :=
  inferInstance
private instance : DecidableEq (Lease × Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64) :=
  inferInstance
private instance : DecidableEq
    (Nat × Lease × Lease × Word × List OS.Ownership.Ticket × List OS.Atomics64.HandleId64) :=
  inferInstance

private instance : DecidableEq (Word × Word × Phase × Nat) :=
  inferInstance
private instance : DecidableEq (Word × Word × Word × Word × Phase × Nat) :=
  inferInstance
private instance : DecidableEq (Word × Word × Word × Word × Word × Word × Phase × Nat) :=
  inferInstance

/-- Preserve full original loans, caller slots and private grants across all
instructions and publications; neither worker gets an ordinary shared grant. -/
theorem original_resources_retained :
    result.1.workers.map resourceView = initial.workers.map resourceView ∧
    initial.workers.map (fun worker => (worker.resources.grants, worker.resources.atomics)) =
      [([⟨1, 0⟩], [⟨0⟩, ⟨2⟩]), ([⟨2, 0⟩], [⟨1⟩, ⟨3⟩])] := by
  decide +kernel

/-- Real arithmetic, both returns and framed memory are checked together.
The ordinary dword store changes only the upper half of the private qword. -/
theorem final_machine_contract :
    (loadQWord (published result.1.world) 65536).toOption = some 7 ∧
    (loadQWord (published result.1.world) 458752).toOption = some 25 ∧
    (loadQWord (published result.1.world) 131072).toOption = some 0x0000000700000000 ∧
    (loadQWord (published result.1.world) 196608).toOption = some 0 ∧
    (loadQWord (published result.1.world) 65544).toOption = some 0xabcdef0123456789 ∧
    result.1.workers.map (fun worker =>
      (worker.context.registers .rax, worker.context.registers .rsi,
        worker.context.registers .rdi, worker.context.registers .rdx, worker.context.registers .rcx,
        worker.context.rip, worker.phase, worker.nextStore)) =
      [(5, 7, 65536, 458752, 131076, 0x7000, .returned, 3),
       (5, 14, 65536, 458752, 196612, 0x8000, .returned, 1)] := by
  decide +kernel

end EDSL.Tests.PublicationCoverage

#print axioms EDSL.Tests.TSO64CrossCellFixtures.start_valid
#print axioms EDSL.Tests.PublicationCoverage.initial_valid
#print axioms EDSL.Tests.PublicationCoverage.execution
#print axioms EDSL.Tests.PublicationCoverage.store_certificate
#print axioms EDSL.Tests.PublicationCoverage.access_certificate
#print axioms EDSL.Tests.PublicationCoverage.instruction_writes
#print axioms EDSL.Tests.PublicationCoverage.actual_after_B_store_A
#print axioms EDSL.Tests.PublicationCoverage.actual_after_RMW_A
#print axioms EDSL.Tests.PublicationCoverage.store_covers_every_actual_target
#print axioms EDSL.Tests.PublicationCoverage.rmw_covers_every_actual_target
#print axioms EDSL.Tests.PublicationCoverage.store_covers_both_cells
#print axioms EDSL.Tests.PublicationCoverage.rmw_covers_both_cells
#print axioms EDSL.Tests.PublicationCoverage.final_machine_contract
#audit_edsl
