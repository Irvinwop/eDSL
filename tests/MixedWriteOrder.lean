/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.WriteOrder
import EDSL.OS.TSO64.StoreHistory.Trace
import EDSL.OS.TSO64.C23Projection.StoreTrace
import tests.TSO64SharedCells
import EDSL.Audit

/-!
Closed integration client of the universal instruction/publication order rules.
Both checked contexts come from the existing shared-cell fixture.
The sixteen code bytes are two copies of
`48 89 37 f0 48 0f c1 37`: MOV [RDI],RSI; LOCK XADD [RDI],RSI.
There is no RET. Both FIFOs are empty at the end; both workers remain running.

RSI starts at 7. Each MOV queues 7, and each XADD fetches 7, publishes 14,
and writes 7 back to RSI. Thus even the complete RMW event repeats. Blocked
attempts retain their positions. Store issues are at actions 0/4, publications
at 2/6, and RMWs at 3/7. Offset 37 gives positions 39/40/43/44 and ranks
40/41/44/45. No intended successor state or issue oracle is an input.

These are finite abstract scheduler claims under the imported scalar-memory,
managed-resource, long-mode/CET-disabled and translation/alias assumptions.
They do not establish a returned call, C23 legality or physical LOCK refinement.
-/

set_option autoImplicit false

namespace EDSL.Tests.MixedWriteOrder
open X86 OS.TSO64 OS.TSO64.PublishedHistory

deriving instance DecidableEq for Except

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private def found {α : Type} (attempt : Option α) (present : attempt.isSome = true) : α :=
  attempt.get present

def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x37c10f48f0378948 0x37c10f48f0378948 9 7 0 0 0

theorem initial_succeeds : initialAttempt.toOption.isSome = true := by decide +kernel

def initial : OS.TSO64.State := checked initialAttempt initial_succeeds

theorem initial_actual : initialAttempt = .ok initial :=
  checked_ok initialAttempt initial_succeeds

def actions : List Action :=
  [.issue 0 false, .issue 0 false, .drain 0, .issue 0 true,
    .issue 0 false, .issue 0 true, .drain 0, .issue 0 false]

def scanAttempt : Except Fault StoreHistory.Trace.Result :=
  StoreHistory.Trace.scan initial actions .sharedCell 37

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

def scanned : StoreHistory.Trace.Result := checked scanAttempt scan_succeeds

theorem scanned_actual : StoreHistory.Trace.scan initial actions .sharedCell 37 = .ok scanned :=
  checked_ok scanAttempt scan_succeeds

def result : OS.TSO64.State × List Observation := scanned.execution

theorem scheduled : schedule initial actions .sharedCell = .ok result :=
  StoreHistory.Trace.scan_scheduled scanned_actual

-- Only finite metadata is reduced below. Order proofs keep the real states
-- abstract through generic helpers, rather than simplifying their worlds.
theorem initial_queues : initial.workers.map Worker.pending = [[], []] := by decide +kernel

private theorem quiescent_of_empty_projection {state : OS.TSO64.State}
    (empty : ∀ pending ∈ state.workers.map Worker.pending, pending = []) : Quiescent state := by
  intro worker member
  exact empty worker.pending (List.mem_map.mpr ⟨worker, member, rfl⟩)

theorem initial_quiescent : Quiescent initial := by
  apply quiescent_of_empty_projection
  rw [initial_queues]
  simp

theorem initial_sequenced : Sequenced initial :=
  C23Projection.quiescent_sequenced initial_quiescent

/-- Recover the complete descriptor from the production scan's first issue.
Neither a replacement handle nor a reconstructed authority record is used. -/
def referenceAttempt : Option Queue.ManagedRef := do
  let issue ← scanned.issues[0]?
  match issue.entry with
  | .managed reference _ _ => some reference
  | .ordinary _ _ => none

theorem reference_present : referenceAttempt.isSome = true := by decide +kernel

def reference : Queue.ManagedRef := found referenceAttempt reference_present

/-- Extract the full actual event, including actor, handle, cell and arithmetic.
The later event must agree with this one in the exact observation assertion. -/
def eventAttempt : Option OS.Atomics64.FetchAddEvent := do
  let observation ← result.2[3]?
  match observation with
  | .rmw _ event => some event
  | _ => none

theorem event_present : eventAttempt.isSome = true := by decide +kernel

def event : OS.Atomics64.FetchAddEvent := found eventAttempt event_present

/-- Exact coverage rejects missing or invented store issues, wrong occurrences,
and treating blocked LOCKs or real RMWs as buffered stores. -/
theorem issue_coverage : scanned.issues =
    [⟨37, 0, .managed reference 7 0⟩, ⟨41, 0, .managed reference 7 1⟩] := by decide +kernel

theorem observations_exact : result.2 =
    [.ordinary 0, .blocked 0, .drained 0 (.managed reference 7 0), .rmw 0 event,
      .ordinary 0, .blocked 0, .drained 0 (.managed reference 7 1), .rmw 0 event] := by decide +kernel

/-- The repeated event is checked against an independent arithmetic/authority
contract, rather than accepted merely because the two payloads agree. -/
theorem event_contract :
    event.actor = 11 ∧ event.handle = reference.identifier ∧
      event.cell = reference.handle.cell ∧ event.arithmetic.delta = 7 ∧
      event.arithmetic.event.address = 65536 ∧
      event.arithmetic.event.before = 7 ∧ event.arithmetic.event.after = 14 := by
  decide +kernel

private theorem scan_issue_at {state : OS.TSO64.State} {actions : List Action}
    {profile : Profile} {offset index tid : Nat} {entry : Pending}
    {scanned : StoreHistory.Trace.Result}
    (success : StoreHistory.Trace.scan state actions profile offset = .ok scanned)
    (member : (⟨offset + index, tid, entry⟩ : StoreHistory.Trace.Issue) ∈ scanned.issues) :
    StoreHistory.IssuedAt profile tid entry index state actions scanned.execution := by
  obtain ⟨actualIndex, position, actual⟩ :=
    (StoreHistory.Trace.scan_issues_iff success).mp member
  change offset + index = offset + actualIndex at position
  have same : actualIndex = index := by omega
  subst actualIndex
  exact actual

theorem first_store_issued :
    StoreHistory.IssuedAt .sharedCell 0 (.managed reference 7 0) 0 initial actions result := by
  apply scan_issue_at scanned_actual
  rw [issue_coverage]
  exact List.mem_cons_self

theorem second_store_issued :
    StoreHistory.IssuedAt .sharedCell 0 (.managed reference 7 1) 4 initial actions result := by
  apply scan_issue_at scanned_actual
  rw [issue_coverage]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem first_store_observed :
    result.2[2]? = some (.drained 0 (.managed reference 7 0)) := by
  rw [observations_exact]
  rfl

theorem second_store_observed :
    result.2[6]? = some (.drained 0 (.managed reference 7 1)) := by
  rw [observations_exact]
  rfl

theorem first_rmw_observed : result.2[3]? = some (.rmw 0 event) := by
  rw [observations_exact]
  rfl

theorem second_rmw_observed : result.2[7]? = some (.rmw 0 event) := by
  rw [observations_exact]
  rfl

private theorem rmw_write_at {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {offset index tid : Nat} {event : OS.Atomics64.FetchAddEvent}
    (success : schedule state actions profile = .ok result)
    (observed : result.2[index]? = some (.rmw tid event)) :
    ∃ witness : WriteAt state actions result profile offset
      ⟨offset + index, .rmw tid event⟩, witness.index = index := by
  obtain ⟨before, action, next, prefixRun, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  exact ⟨⟨index, .rmw tid event, before, action, next, rfl, observed,
    prefixRun, actionAt, stepped, rfl⟩, rfl⟩

-- Normalize the library RMW constructor's instruction index while the state,
-- stamp and observation list are still abstract.
private theorem rmw_instruction_at {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {offset position index tid : Nat} {event : OS.Atomics64.FetchAddEvent}
    (published : WriteAt state actions result profile offset ⟨position, .rmw tid event⟩)
    (atIndex : published.index = index) :
    ∃ witness : InstructionWriteAt state actions result profile offset index
      ⟨position, .rmw tid event⟩, witness.publication.index = index := by
  subst index
  exact ⟨InstructionWriteAt.rmw published, rfl⟩

def firstStoreStamp : Stamp := ⟨39, .buffered 0 reference 7 0⟩
def firstRMWStamp : Stamp := ⟨40, .rmw 0 event⟩
def secondStoreStamp : Stamp := ⟨43, .buffered 0 reference 7 1⟩
def secondRMWStamp : Stamp := ⟨44, .rmw 0 event⟩

/-- All four actual instruction writes and their real publication indices.
No final-quiescence or desired poststate premise is used to construct them. -/
theorem instruction_writes :
    ∃ firstStore : InstructionWriteAt initial actions result .sharedCell 37 0 firstStoreStamp,
    ∃ firstRMW : InstructionWriteAt initial actions result .sharedCell 37 3 firstRMWStamp,
    ∃ secondStore : InstructionWriteAt initial actions result .sharedCell 37 4 secondStoreStamp,
    ∃ secondRMW : InstructionWriteAt initial actions result .sharedCell 37 7 secondRMWStamp,
      firstStore.publication.index = 2 ∧ firstRMW.publication.index = 3 ∧
        secondStore.publication.index = 6 ∧ secondRMW.publication.index = 7 := by
  obtain ⟨firstStore, firstAt⟩ := managed_drain_writeAt
    (offset := 37) scheduled first_store_observed
  obtain ⟨secondStore, secondAt⟩ := managed_drain_writeAt
    (offset := 37) scheduled second_store_observed
  obtain ⟨firstRMW, firstRMWAt⟩ := rmw_write_at (offset := 37) scheduled first_rmw_observed
  obtain ⟨secondRMW, secondRMWAt⟩ := rmw_write_at (offset := 37) scheduled second_rmw_observed
  obtain ⟨firstActualRMW, firstActualAt⟩ := rmw_instruction_at firstRMW firstRMWAt
  obtain ⟨secondActualRMW, secondActualAt⟩ := rmw_instruction_at secondRMW secondRMWAt
  exact ⟨InstructionWriteAt.buffered first_store_issued firstStore, firstActualRMW,
    InstructionWriteAt.buffered second_store_issued secondStore, secondActualRMW,
    firstAt, firstActualAt, secondAt, secondActualAt⟩

/-- The two public strict-order contracts, for positions and ranks. -/
def Orders (firstIndex secondIndex : Nat) (firstStamp secondStamp : Stamp) : Prop :=
  (firstIndex < secondIndex ↔ firstStamp.position < secondStamp.position) ∧
    (firstIndex < secondIndex ↔ firstStamp.position + 1 < secondStamp.position + 1)

private theorem actual_orders {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {offset firstIndex secondIndex : Nat} {firstStamp secondStamp : Stamp}
    (first : InstructionWriteAt state actions result profile offset firstIndex firstStamp)
    (second : InstructionWriteAt state actions result profile offset secondIndex secondStamp)
    (success : schedule state actions profile = .ok result) (sequenced : Sequenced state)
    (sameThread : firstStamp.cause.tid = secondStamp.cause.tid) :
    Orders firstIndex secondIndex firstStamp secondStamp :=
  ⟨first.order_iff second success sequenced sameThread,
    first.rank_order_iff second success sequenced sameThread⟩

/-- Instantiate BOTH universal iff rules for store/store, store/RMW,
RMW/store and RMW/RMW on genuine witnesses of this one successful execution. -/
theorem all_four_orders :
    Orders 0 4 firstStoreStamp secondStoreStamp ∧
    Orders 0 3 firstStoreStamp firstRMWStamp ∧
    Orders 3 4 firstRMWStamp secondStoreStamp ∧
    Orders 3 7 firstRMWStamp secondRMWStamp := by
  obtain ⟨firstStore, firstRMW, secondStore, secondRMW, _indices⟩ := instruction_writes
  exact ⟨actual_orders firstStore secondStore scheduled initial_sequenced rfl,
    actual_orders firstStore firstRMW scheduled initial_sequenced rfl,
    actual_orders firstRMW secondStore scheduled initial_sequenced rfl,
    actual_orders firstRMW secondRMW scheduled initial_sequenced rfl⟩

def publications : List Stamp := C23Projection.writes 37 result.2

theorem publications_exact :
    publications = [firstStoreStamp, firstRMWStamp, secondStoreStamp, secondRMWStamp] := by
  rw [publications, observations_exact]
  rfl

/-- Literal positions distinguish store issue from publication and retain
blocked attempts in the original action space. Ranks reserve zero. -/
theorem issue_publication_positions_and_ranks :
    scanned.issues.map (fun issue => issue.position) = [37, 41] ∧
    publications.map Stamp.position = [39, 40, 43, 44] ∧
    publications.map (fun stamp => stamp.position + 1) = [40, 41, 44, 45] := by
  rw [issue_coverage, publications_exact]
  exact ⟨rfl, rfl, rfl⟩

/-- Equal store values keep their occurrences; even equal complete RMW causes
keep distinct positions. These are projections of the actual production writes. -/
theorem repeated_values_keep_distinct_writers :
    publications.map (fun stamp => (stamp.position, stamp.cause.value)) =
      [(39, 7), (40, 14), (43, 7), (44, 14)] ∧
    result.2[3]? = result.2[7]? ∧
    (publications[1]?).map Stamp.cause = (publications[3]?).map Stamp.cause ∧
    publications[1]? ≠ publications[3]? := by
  rw [publications_exact, observations_exact]
  refine ⟨?_, rfl, rfl, ?_⟩
  · decide +kernel
  · intro same
    have different : (some 40 : Option Nat) ≠ some 44 := by decide
    exact different (congrArg (fun stamp : Option Stamp => stamp.map Stamp.position) same)

theorem final_queues : result.1.workers.map Worker.pending = [[], []] := by decide +kernel

theorem final_quiescent : Quiescent result.1 := by
  apply quiescent_of_empty_projection
  rw [final_queues]
  simp

/-- The run really publishes the two additions. It ends at the code boundary,
without assuming a return or collecting a still-running worker. -/
theorem final_execution_contract :
    loadQWord (published result.1.world) 65536 = .ok 14 ∧
    result.1.workers.map (fun worker =>
      (worker.context.registers .rax, worker.context.registers .rsi,
        worker.context.rip, worker.phase, worker.nextStore)) =
      [(5, 7, 393232, .running, 2), (5, 0, 393216, .running, 0)] := by
  decide +kernel

end EDSL.Tests.MixedWriteOrder

#print axioms EDSL.Tests.MixedWriteOrder.scanned_actual
#print axioms EDSL.Tests.MixedWriteOrder.scheduled
#print axioms EDSL.Tests.MixedWriteOrder.initial_sequenced
#print axioms EDSL.Tests.MixedWriteOrder.instruction_writes
#print axioms EDSL.Tests.MixedWriteOrder.all_four_orders
#print axioms EDSL.Tests.MixedWriteOrder.repeated_values_keep_distinct_writers
#audit_edsl
