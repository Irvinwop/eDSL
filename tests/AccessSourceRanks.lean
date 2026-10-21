/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.ExecutionViews
import tests.TSO64AtomicTrace
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphRanks
import EDSL.OS.TSO64.C23Projection.AtomicTrace.ReadRanks

/-!
Integration clients for actual-access authority and exact source-writer ranks.
The inputs below are checked setup/attachment and production annotated scans.
Literal contracts specify original action positions, source identities, loaded
words and publication ranks independently of the access classifier. Equal words
cannot select a writer. No desired rank or `LoadSource` is an execution input.

The load client reuses the initial/forwarded/published equal-word program. The
RMW client annotates the actual `MixedWriteOrder` execution, including blocked
attempts and equal complete RMW payloads. Empty queues and RET are separate:
the RMW execution finishes with both workers running. All claims concern finite
sharedCell scalar-RAM, long-mode/CET-off executions with stable resources, not
fairness, physical execution, source-C23 legality or additional corpus coverage.
-/

set_option autoImplicit false

namespace EDSL.Tests.AccessSourceRanks
open X86 OS.TSO64 OS.TSO64.C23Projection
open AtomicTrace

-- Stage the observation tuple's equality before reducing concrete traces.
private instance : DecidableEq (Word × Option WriterId × Option WriterId) := inferInstance
private instance : DecidableEq
    (Nat × Nat × Nat × OS.Atomics64.CellId64 × Word × Option WriterId × Option WriterId) :=
  inferInstance

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private theorem empty_valid (world : World) (valid : OS.Atomics64.WellFormed world) :
    WellFormed ⟨world, []⟩ .sharedCell := by
  refine ⟨valid, ?_⟩
  intro worker absent
  cases absent

private theorem fixture_start_valid {first second old : Word} {a b : Context}
    {state : OS.TSO64.State}
    (success : (do
      let ready ← (TSO64.fixture first second old).mapError Fault.os
      let one ← attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA
        [ready.dataA] [ready.atomicA]
      attach one 12 b ready.codeB ready.callerB [ready.dataB] [ready.atomicB]) = .ok state) :
    WellFormed state .sharedCell := by
  cases setup : TSO64.fixture first second old with
  | error fault => simp [setup, Except.mapError] at success
  | ok ready =>
      have attached : (do
          let one ← attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA
            [ready.dataA] [ready.atomicA]
          attach one 12 b ready.codeB ready.callerB [ready.dataB] [ready.atomicB]) = .ok state := by
        simpa only [setup, Except.mapError, ok_bind] using success
      cases one : attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA
          [ready.dataA] [ready.atomicA] with
      | error fault => simp [one] at attached
      | ok firstState =>
          have final : attach firstState 12 b ready.codeB ready.callerB
              [ready.dataB] [ready.atomicB] = .ok state := by
            simpa only [one, ok_bind] using attached
          exact attach_valid_for .sharedCell
            (attach_valid_for .sharedCell (empty_valid _ ready.checked.valid) one) final

-- Reuse the actual setup and both successful attachments. This is the same
-- validity argument as ExecutionViews, generalized to the two programs here;
-- no intermediate well-formed state or target authority is assumed.
theorem shared_start_valid {first second old deltaA deltaB : Word}
    {offsetA offsetB : Nat} {state : OS.TSO64.State}
    (success : TSO64SharedCells.start first second old deltaA deltaB offsetA offsetB = .ok state) :
    WellFormed state .sharedCell := by
  cases setup : TSO64.fixture first second old with
  | error fault =>
      simp [TSO64SharedCells.start, setup, Except.mapError] at success
  | ok ready =>
      let a : Context :=
        { TSO64.context 262144 131072 deltaA 5 with rip := 393216 + BitVec.ofNat 64 offsetA }
      let b : Context :=
        { TSO64.context 327680 196608 deltaB 5 with rip := 393216 + BitVec.ofNat 64 offsetB }
      have attached : (do
          let one ← attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA
            [ready.dataA] [ready.atomicA]
          attach one 12 b ready.codeB ready.callerB [ready.dataB] [ready.atomicB]) = .ok state := by
        simpa only [TSO64SharedCells.start, setup, Except.mapError, ok_bind] using success
      cases one : attach ⟨ready.checked.world, []⟩ 11 a ready.codeA ready.callerA
          [ready.dataA] [ready.atomicA] with
      | error fault => simp [one] at attached
      | ok firstState =>
          have final : attach firstState 12 b ready.codeB ready.callerB
              [ready.dataB] [ready.atomicB] = .ok state := by
            simpa only [one, ok_bind] using attached
          exact attach_valid_for .sharedCell
            (attach_valid_for .sharedCell (empty_valid _ ready.checked.valid) one) final

theorem quiescent_of_empty_projection {state : OS.TSO64.State}
    (empty : state.workers.map Worker.pending = [[], []]) : Quiescent state := by
  intro worker member
  have mapped : worker.pending ∈ state.workers.map Worker.pending :=
    List.mem_map.mpr ⟨worker, member, rfl⟩
  rw [empty] at mapped
  simpa using mapped

/-- Scan membership fixes the original action index even when drains, blocked
instructions and returns do not emit atomic events. -/
theorem scanned_at_position {initial : OS.TSO64.State} {actions : List Action}
    {profile : Profile} {offset index : Nat} {incoming : PublishedHistory.Writers}
    {scanned : AtomicTrace.Result} {event : AtomicTrace.Event}
    (valid : WellFormed initial profile) (sequenced : Sequenced initial)
    (success : AtomicTrace.scan initial actions profile offset incoming = .ok scanned)
    (member : event ∈ scanned.events) (position : event.position = offset + index) :
    EventAt profile event index initial actions scanned.execution offset incoming := by
  obtain ⟨actualIndex, actual⟩ := scan_sound valid sequenced success member
  have actualPosition := actual.position
  have same : actualIndex = index := by omega
  subst actualIndex
  exact actual

/-- Every computed access authenticates an original worker and exact target.
The cut is arbitrary, including cuts beyond the last action. No authority,
view-domain or current-cell oracle is an input to this client. -/
theorem scanned_access_domain {initial : OS.TSO64.State} {actions : List Action}
    {profile : Profile} {offset : Nat} {incoming : PublishedHistory.Writers}
    {scanned : AtomicTrace.Result} {event : AtomicTrace.Event}
    (execution : ExecutionViews.Execution initial actions scanned.execution profile)
    (success : AtomicTrace.scan initial actions profile offset incoming = .ok scanned)
    (member : event ∈ scanned.events) (cut : Nat) :
    (∃ original target, initial.workers[event.tid]? = some original ∧
      Queue.Current initial.world original.resources target ∧ AccessTarget event target) ∧
    (∃ target rank, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions scanned.execution profile cut event.tid
        target offset incoming rank)) := by
  obtain ⟨_index, actual⟩ := scan_sound execution.valid execution.sequenced success member
  exact ⟨actual.initial_authority, EventAt.views execution actual cut⟩

/-- Actual access authority composes with view existence and monotonicity at
two arbitrary ordered cuts. The incoming-map condition is solely the published
order boundary, not a certificate for incoming writer identities. -/
theorem actual_access_monotone {initial : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {event : AtomicTrace.Event} {index offset first last : Nat}
    {incoming : PublishedHistory.Writers}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset incoming)
    (prior : PublishedOrder.Prior offset incoming) (ordered : first ≤ last) :
    ∃ target firstRank lastRank, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile first event.tid
        target offset incoming firstRank) ∧
      Nonempty (ExecutionViews.At initial actions result profile last event.tid
        target offset incoming lastRank) ∧ firstRank ≤ lastRank := by
  obtain ⟨_original, target, live, current, related⟩ := actual.initial_authority
  obtain ⟨firstRank, ⟨earlier⟩⟩ :=
    ExecutionViews.exists_at execution live first current offset incoming
  obtain ⟨lastRank, ⟨later⟩⟩ :=
    ExecutionViews.exists_at execution live last current offset incoming
  exact ⟨target, firstRank, lastRank, related, ⟨earlier⟩, ⟨later⟩,
    ExecutionViews.At.monotone execution prior ordered earlier later⟩

/-- An independently computed query fixes the exact writer rank obtained from
the actual annotated load. Deterministic prefix execution aligns the view's
snapshot with the queried state; the caller supplies neither `LoadSource` nor
target authority, selected publication, view witness or writer rank. -/
theorem actual_load_rank_of_query {initial before : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {event : AtomicTrace.Event} {index offset expected : Nat} {target : Queue.ManagedRef}
    {value : Word} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset PublishedHistory.empty)
    (loaded : event.access = .load target value source)
    (prefixRun : schedule initial (actions.take index) profile =
      .ok (before, result.2.take index))
    (answered : ExecutionViews.query before result.2 index event.tid target offset
      PublishedHistory.empty = some expected) :
    Nonempty (ExecutionViews.At initial actions result profile index event.tid target offset
      PublishedHistory.empty expected) ∧
      WriterRank initial actions result profile offset target.handle.cell source expected := by
  obtain ⟨rank, ⟨view⟩, writer⟩ := EventAt.load_view_rank execution actual loaded
  have aligned : before = view.snapshot.state :=
    congrArg Prod.fst (Except.ok.inj (prefixRun.symm.trans view.snapshot.scheduled))
  have correct : ExecutionViews.query before result.2 index event.tid target offset
      PublishedHistory.empty = some rank := by
    rw [aligned]
    exact view.query_eq
  have same : rank = expected := Option.some.inj (correct.symm.trans answered)
  subst expected
  exact ⟨⟨view⟩, writer⟩

namespace Loads

def initial : OS.TSO64.State := checked TSO64AtomicTrace.equalStart (by decide +kernel)

theorem initial_actual : TSO64AtomicTrace.equalStart = .ok initial := checked_ok _ _

theorem initial_valid : WellFormed initial .sharedCell := shared_start_valid initial_actual

def actions : List Action := TSO64AtomicTrace.equalActions

def scanAttempt : Except Fault AtomicTrace.Result :=
  AtomicTrace.scan initial actions .sharedCell 10

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

def scanned : AtomicTrace.Result := checked scanAttempt scan_succeeds

theorem scanned_actual : AtomicTrace.scan initial actions .sharedCell 10 = .ok scanned :=
  checked_ok _ _

def result : OS.TSO64.State × List Observation := scanned.execution

theorem scheduled : schedule initial actions .sharedCell = .ok result :=
  scan_scheduled scanned_actual

theorem initial_quiescent : Quiescent initial := quiescent_of_empty_projection (by decide +kernel)

theorem initial_sequenced : Sequenced initial := quiescent_sequenced initial_quiescent

theorem final_quiescent : Quiescent result.1 := quiescent_of_empty_projection (by decide +kernel)

theorem execution : ExecutionViews.Execution initial actions result .sharedCell :=
  ⟨scheduled, initial_valid, initial_sequenced, final_quiescent⟩

private theorem prefix_succeeds (cut : Nat) :
    (schedule initial (actions.take cut) .sharedCell).toOption.isSome = true := by
  obtain ⟨before, success, _suffix⟩ := ScheduleTrace.cut scheduled cut
  rw [success]
  rfl

def atCut (cut : Nat) : OS.TSO64.State × List Observation :=
  checked (schedule initial (actions.take cut) .sharedCell) (prefix_succeeds cut)

theorem prefix_exact (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell =
      .ok ((atCut cut).1, result.2.take cut) := by
  have actual : schedule initial (actions.take cut) .sharedCell = .ok (atCut cut) := checked_ok _ _
  have same := (ScheduleTrace.suffix scheduled actual).1
  rw [← same]
  exact actual

/-- All source/value contracts concern the real scanner output. Both stores
and initialization have word zero. The first drain is position 14, the second
17; the peer load between them reads occurrence zero while own loads read one. -/
theorem literal_access_contract : scanned.events.map TSO64AtomicTrace.eventSummary =
    [(10, 1, 0, ⟨0⟩, 0, some (.initial ⟨0⟩), none),
      (11, 0, 1, ⟨0⟩, 0, none, some (.store 0 0)),
      (12, 0, 1, ⟨0⟩, 0, none, some (.store 0 1)),
      (13, 0, 0, ⟨0⟩, 0, some (.store 0 1), none),
      (15, 1, 0, ⟨0⟩, 0, some (.store 0 0), none),
      (16, 0, 0, ⟨0⟩, 0, some (.store 0 1), none)] := by
  decide +kernel

-- Every descriptor below is extracted from an actual computed access, not
-- constructed to match a desired cell, handle, rank or source key.
def readReference (event : AtomicTrace.Event) : Option Queue.ManagedRef :=
  match event.access with
  | .load reference .. => some reference
  | _ => none

def firstReference : Queue.ManagedRef :=
  ((scanned.events[0]?).bind readReference).get (by decide +kernel)

def ownReference : Queue.ManagedRef :=
  ((scanned.events[3]?).bind readReference).get (by decide +kernel)

def peerReference : Queue.ManagedRef :=
  ((scanned.events[4]?).bind readReference).get (by decide +kernel)

theorem computed_loads :
    scanned.events[0]? = some ⟨10, 1, .load firstReference 0 (.initial ⟨0⟩)⟩ ∧
      scanned.events[3]? = some ⟨13, 0, .load ownReference 0 (.store 0 1)⟩ ∧
      scanned.events[4]? = some ⟨15, 1, .load peerReference 0 (.store 0 0)⟩ ∧
      scanned.events[5]? = some ⟨16, 0, .load ownReference 0 (.store 0 1)⟩ := by
  decide +kernel

/-- These are authenticated computed events, with the unfiltered prestate cuts
0/3/5/6. The ranks tested below are not used to produce any access origin. -/
theorem initial_load_at : EventAt .sharedCell
    ⟨10, 1, .load firstReference 0 (.initial ⟨0⟩)⟩ 0 initial actions result
      10 PublishedHistory.empty :=
  scanned_at_position initial_valid initial_sequenced scanned_actual
    (List.mem_of_getElem? computed_loads.1) rfl

theorem forwarded_load_at : EventAt .sharedCell
    ⟨13, 0, .load ownReference 0 (.store 0 1)⟩ 3 initial actions result
      10 PublishedHistory.empty :=
  scanned_at_position initial_valid initial_sequenced scanned_actual
    (List.mem_of_getElem? computed_loads.2.1) rfl

theorem published_load_at : EventAt .sharedCell
    ⟨15, 1, .load peerReference 0 (.store 0 0)⟩ 5 initial actions result
      10 PublishedHistory.empty :=
  scanned_at_position initial_valid initial_sequenced scanned_actual
    (List.mem_of_getElem? computed_loads.2.2.1) rfl

theorem forwarded_after_older_drain_at : EventAt .sharedCell
    ⟨16, 0, .load ownReference 0 (.store 0 1)⟩ 6 initial actions result
      10 PublishedHistory.empty :=
  scanned_at_position initial_valid initial_sequenced scanned_actual
    (List.mem_of_getElem? computed_loads.2.2.2) rfl

def queried (cut tid : Nat) (reference : Queue.ManagedRef) : Option Nat :=
  ExecutionViews.query (atCut cut).1 result.2 cut tid reference 10 PublishedHistory.empty

/-- Literal source publication+1 ranks retain the action gaps. The own reads
use rank 18 before publication, even after the other equal writer drains. -/
theorem initial_query : queried 0 1 firstReference = some 0 := by decide +kernel
theorem forwarded_query : queried 3 0 ownReference = some 18 := by decide +kernel
theorem published_query : queried 5 1 peerReference = some 15 := by decide +kernel
theorem forwarded_after_older_drain_query : queried 6 0 ownReference = some 18 := by decide +kernel

/-- Every event in this actual computed trace has an authenticated domain and
view at every cut, including stores and cuts after both returns. -/
theorem every_access_domain {event : AtomicTrace.Event} (member : event ∈ scanned.events)
    (cut : Nat) :
    (∃ original target, initial.workers[event.tid]? = some original ∧
      Queue.Current initial.world original.resources target ∧ AccessTarget event target) ∧
    (∃ target rank, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result .sharedCell cut event.tid
        target 10 PublishedHistory.empty rank)) :=
  scanned_access_domain execution scanned_actual member cut

theorem initial_source_view :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 0 1 firstReference
      10 PublishedHistory.empty 0) ∧
      WriterRank initial actions result .sharedCell 10 firstReference.handle.cell (.initial ⟨0⟩) 0 :=
  actual_load_rank_of_query execution initial_load_at rfl (prefix_exact 0) initial_query

/-- The source's own publication rank is eighteen while the load's action
position is thirteen. The equal older writer's actual rank is fifteen. -/
theorem forwarded_source_view :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 3 0 ownReference
      10 PublishedHistory.empty 18) ∧
      WriterRank initial actions result .sharedCell 10 ownReference.handle.cell (.store 0 1) 18 :=
  actual_load_rank_of_query execution forwarded_load_at rfl (prefix_exact 3) forwarded_query

theorem published_source_view :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 5 1 peerReference
      10 PublishedHistory.empty 15) ∧
      WriterRank initial actions result .sharedCell 10 peerReference.handle.cell (.store 0 0) 15 :=
  actual_load_rank_of_query execution published_load_at rfl (prefix_exact 5) published_query

theorem forwarded_after_older_drain_source_view :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 6 0 ownReference
      10 PublishedHistory.empty 18) ∧
      WriterRank initial actions result .sharedCell 10 ownReference.handle.cell (.store 0 1) 18 :=
  actual_load_rank_of_query execution forwarded_after_older_drain_at rfl
    (prefix_exact 6) forwarded_after_older_drain_query

/-- The actual newer zero-valued writer cannot borrow the older zero-valued
writer's rank. This quantifies over every putative competing rank witness. -/
theorem equal_value_cannot_alias_publication_rank
    (wrong : WriterRank initial actions result .sharedCell 10 ownReference.handle.cell
      (.store 0 1) 15) : False := by
  have same := WriterRank.unique scheduled initial_sequenced forwarded_source_view.2 wrong
  omega

/-- The actual forwarded load supplies the complete target for view
monotonicity at arbitrary cuts; the theorem does not assume either endpoint
view or restrict the cuts to atomic-event positions or running workers. -/
theorem own_target_monotone {first last : Nat} (ordered : first ≤ last) :
    ∃ firstRank lastRank,
      Nonempty (ExecutionViews.At initial actions result .sharedCell first 0 ownReference
        10 PublishedHistory.empty firstRank) ∧
      Nonempty (ExecutionViews.At initial actions result .sharedCell last 0 ownReference
        10 PublishedHistory.empty lastRank) ∧ firstRank ≤ lastRank := by
  obtain ⟨target, firstRank, lastRank, related, earlier, later, monotone⟩ :=
    actual_access_monotone execution forwarded_load_at (PublishedOrder.prior_empty 10) ordered
  have same : target = ownReference := related.2
  subst target
  exact ⟨firstRank, lastRank, earlier, later, monotone⟩

/-- Quiescence already holds before either RET. Returned phase is a different
property; neither phase nor an atomic-event index supplies publication ranks. -/
theorem quiescent_before_return :
    (atCut 8).1.workers.map (fun worker => (worker.phase, worker.pending.length)) =
      [(.running, 0), (.running, 0)] := by
  decide +kernel

end Loads

namespace RMW

def scanAttempt : Except Fault AtomicTrace.Result :=
  AtomicTrace.scan MixedWriteOrder.initial MixedWriteOrder.actions .sharedCell 37

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

def scanned : AtomicTrace.Result := checked scanAttempt scan_succeeds

theorem scanned_actual :
    AtomicTrace.scan MixedWriteOrder.initial MixedWriteOrder.actions .sharedCell 37 = .ok scanned :=
  checked_ok _ _

theorem scheduled : schedule MixedWriteOrder.initial MixedWriteOrder.actions .sharedCell =
    .ok scanned.execution := scan_scheduled scanned_actual

/-- Deterministic production execution identifies the atomic scan with the
existing actual store/RMW fixture, rather than assuming a matching final state. -/
theorem execution_eq : scanned.execution = MixedWriteOrder.result :=
  Except.ok.inj (scheduled.symm.trans MixedWriteOrder.scheduled)

theorem initial_valid : WellFormed MixedWriteOrder.initial .sharedCell :=
  shared_start_valid MixedWriteOrder.initial_actual

theorem execution : ExecutionViews.Execution MixedWriteOrder.initial MixedWriteOrder.actions
    scanned.execution .sharedCell := by
  refine ⟨scheduled, initial_valid, MixedWriteOrder.initial_sequenced, ?_⟩
  rw [execution_eq]
  exact MixedWriteOrder.final_quiescent

/-- Blocked actions at positions 38/42 produce no access. Stores of seven
publish at 39/43; the two identical RMW payloads have positions 40/44. -/
theorem literal_access_contract : scanned.events.map TSO64AtomicTrace.eventSummary =
    [(37, 0, 1, ⟨0⟩, 7, none, some (.store 0 0)),
      (40, 0, 2, ⟨0⟩, 14, some (.store 0 0), some (.rmw 40)),
      (41, 0, 1, ⟨0⟩, 7, none, some (.store 0 1)),
      (44, 0, 2, ⟨0⟩, 14, some (.store 0 1), some (.rmw 44))] := by
  decide +kernel

theorem computed_rmws :
    scanned.events[1]? = some ⟨40, 0, .rmw MixedWriteOrder.event (.store 0 0)⟩ ∧
      scanned.events[3]? = some ⟨44, 0, .rmw MixedWriteOrder.event (.store 0 1)⟩ := by
  decide +kernel

theorem first_rmw_at : EventAt .sharedCell
    ⟨40, 0, .rmw MixedWriteOrder.event (.store 0 0)⟩ 3
      MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution
      37 PublishedHistory.empty :=
  scanned_at_position initial_valid MixedWriteOrder.initial_sequenced scanned_actual
    (List.mem_of_getElem? computed_rmws.1) rfl

theorem second_rmw_at : EventAt .sharedCell
    ⟨44, 0, .rmw MixedWriteOrder.event (.store 0 1)⟩ 7
      MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution
      37 PublishedHistory.empty :=
  scanned_at_position initial_valid MixedWriteOrder.initial_sequenced scanned_actual
    (List.mem_of_getElem? computed_rmws.2) rfl

/-- Independent rank evidence uses the existing real instruction/publication
witnesses, not the RMW's requested source key or its equal arithmetic payload. -/
theorem first_store_rank : WriterRank MixedWriteOrder.initial MixedWriteOrder.actions
    scanned.execution .sharedCell 37 MixedWriteOrder.event.cell (.store 0 0) 40 := by
  rw [execution_eq]
  obtain ⟨firstStore, _firstRMW, _secondStore, _secondRMW, _indices⟩ :=
    MixedWriteOrder.instruction_writes
  simpa only [MixedWriteOrder.firstStoreStamp, Graph.publicationKey] using
    (WriterRank.publication firstStore.publication MixedWriteOrder.event_contract.2.2.1.symm)

theorem second_store_rank : WriterRank MixedWriteOrder.initial MixedWriteOrder.actions
    scanned.execution .sharedCell 37 MixedWriteOrder.event.cell (.store 0 1) 44 := by
  rw [execution_eq]
  obtain ⟨_firstStore, _firstRMW, secondStore, _secondRMW, _indices⟩ :=
    MixedWriteOrder.instruction_writes
  simpa only [MixedWriteOrder.secondStoreStamp, Graph.publicationKey] using
    (WriterRank.publication secondStore.publication MixedWriteOrder.event_contract.2.2.1.symm)

/-- Source rank forty and own rank forty-one come from the real store drain
and real RMW respectively. Action three is not filtered atomic-event index one. -/
theorem first_source_and_own_rank :
    ∃ target, AccessTarget ⟨40, 0, .rmw MixedWriteOrder.event (.store 0 0)⟩ target ∧
      Nonempty (ExecutionViews.At MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution
        .sharedCell 3 0 target 37 PublishedHistory.empty 40) ∧
      WriterRank MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution .sharedCell
        37 MixedWriteOrder.event.cell (.store 0 0) 40 ∧
      WriterRank MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution .sharedCell
        37 MixedWriteOrder.event.cell (.rmw 40) 41 ∧ 40 < 41 := by
  obtain ⟨target, rank, related, view, sourceRank, ownRank, earlier⟩ :=
    EventAt.rmw_view_rank execution first_rmw_at rfl
  have same : rank = 40 :=
    WriterRank.unique scheduled MixedWriteOrder.initial_sequenced sourceRank first_store_rank
  subst rank
  exact ⟨target, related, view, sourceRank, ownRank, earlier⟩

/-- The second identical RMW reads the second store and has a different own
identity and rank. Neither equal source words nor equal RMW payloads merge it. -/
theorem second_source_and_own_rank :
    ∃ target, AccessTarget ⟨44, 0, .rmw MixedWriteOrder.event (.store 0 1)⟩ target ∧
      Nonempty (ExecutionViews.At MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution
        .sharedCell 7 0 target 37 PublishedHistory.empty 44) ∧
      WriterRank MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution .sharedCell
        37 MixedWriteOrder.event.cell (.store 0 1) 44 ∧
      WriterRank MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution .sharedCell
        37 MixedWriteOrder.event.cell (.rmw 44) 45 ∧ 44 < 45 := by
  obtain ⟨target, rank, related, view, sourceRank, ownRank, earlier⟩ :=
    EventAt.rmw_view_rank execution second_rmw_at rfl
  have same : rank = 44 :=
    WriterRank.unique scheduled MixedWriteOrder.initial_sequenced sourceRank second_store_rank
  subst rank
  exact ⟨target, related, view, sourceRank, ownRank, earlier⟩

/-- RMW authority authenticates the handle/cell/address at every cut, including
the endpoint where both workers remain running with empty queues. -/
theorem every_access_domain {event : AtomicTrace.Event} (member : event ∈ scanned.events)
    (cut : Nat) :
    (∃ original target, MixedWriteOrder.initial.workers[event.tid]? = some original ∧
      Queue.Current MixedWriteOrder.initial.world original.resources target ∧ AccessTarget event target) ∧
    (∃ target rank, AccessTarget event target ∧
      Nonempty (ExecutionViews.At MixedWriteOrder.initial MixedWriteOrder.actions scanned.execution
        .sharedCell cut event.tid target 37 PublishedHistory.empty rank)) :=
  scanned_access_domain execution scanned_actual member cut

end RMW

namespace RMWChain

def initial : OS.TSO64.State := checked TSO64PublishedWriters.start (by decide +kernel)

theorem initial_actual : TSO64PublishedWriters.start = .ok initial := checked_ok _ _

/-- The unchanged-RMW fixture uses RAX zero, whereas SharedCells.start uses
five. Retain its real checked setup and both exact successful attachments. -/
theorem initial_valid : WellFormed initial .sharedCell := by
  have actual := initial_actual
  unfold TSO64PublishedWriters.start at actual
  exact fixture_start_valid actual

def actions : List Action := TSO64AtomicTrace.rmwActions

def scanAttempt : Except Fault AtomicTrace.Result := AtomicTrace.scan initial actions .sharedCell 20

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

def scanned : AtomicTrace.Result := checked scanAttempt scan_succeeds

theorem scanned_actual : AtomicTrace.scan initial actions .sharedCell 20 = .ok scanned :=
  checked_ok _ _

theorem scheduled : schedule initial actions .sharedCell = .ok scanned.execution :=
  scan_scheduled scanned_actual

theorem initial_quiescent : Quiescent initial := quiescent_of_empty_projection (by decide +kernel)

theorem initial_sequenced : Sequenced initial := quiescent_sequenced initial_quiescent

theorem final_quiescent : Quiescent scanned.execution.1 :=
  quiescent_of_empty_projection (state := scanned.execution.1) (by decide +kernel)

theorem execution : ExecutionViews.Execution initial actions scanned.execution .sharedCell :=
  ⟨scheduled, initial_valid, initial_sequenced, final_quiescent⟩

def changed : OS.Atomics64.FetchAddEvent :=
  ((scanned.events[1]?).bind fun event => match event.access with
    | .rmw actual _ => some actual
    | _ => none).get (by decide +kernel)

/-- Actual source identities, arithmetic and action positions are specified
without looking up a writer by word value. The blocked LOCK and drain consume
positions 21/22; RET consumes 25. Both successful RMW payloads are identical. -/
theorem unchanged_chain_contract :
    scanned.events.map TSO64AtomicTrace.eventSummary =
      [(20, 0, 1, ⟨0⟩, 0, none, some (.store 0 0)),
        (23, 0, 2, ⟨0⟩, 0, some (.store 0 0), some (.rmw 23)),
        (24, 0, 2, ⟨0⟩, 0, some (.rmw 23), some (.rmw 24))] ∧
      scanned.events[1]? = some ⟨23, 0, .rmw changed (.store 0 0)⟩ ∧
      scanned.events[2]? = some ⟨24, 0, .rmw changed (.rmw 23)⟩ ∧
      changed.arithmetic.delta = 0 ∧ changed.arithmetic.event.address = 65536 ∧
      changed.arithmetic.event.before = 0 ∧ changed.arithmetic.event.after = 0 := by
  decide +kernel

theorem first_rmw_at : EventAt .sharedCell ⟨23, 0, .rmw changed (.store 0 0)⟩ 3
    initial actions scanned.execution 20 PublishedHistory.empty :=
  scanned_at_position initial_valid initial_sequenced scanned_actual
    (List.mem_of_getElem? unchanged_chain_contract.2.1) rfl

theorem second_rmw_at : EventAt .sharedCell ⟨24, 0, .rmw changed (.rmw 23)⟩ 4
    initial actions scanned.execution 20 PublishedHistory.empty :=
  scanned_at_position initial_valid initial_sequenced scanned_actual
    (List.mem_of_getElem? unchanged_chain_contract.2.2.1) rfl

/-- The first RMW's own actual publication supplies independent rank evidence
for the second RMW's read source. No source-rank premise is supplied to either
actual-access bridge. -/
theorem first_own_rank :
    WriterRank initial actions scanned.execution .sharedCell 20 changed.cell (.rmw 23) 24 := by
  obtain ⟨_target, _rank, _related, _view, _sourceRank, ownRank, _earlier⟩ :=
    EventAt.rmw_view_rank execution first_rmw_at rfl
  exact ownRank

theorem second_source_and_own_rank :
    ∃ target, AccessTarget ⟨24, 0, .rmw changed (.rmw 23)⟩ target ∧
      Nonempty (ExecutionViews.At initial actions scanned.execution .sharedCell 4 0 target
        20 PublishedHistory.empty 24) ∧
      WriterRank initial actions scanned.execution .sharedCell 20 changed.cell (.rmw 23) 24 ∧
      WriterRank initial actions scanned.execution .sharedCell 20 changed.cell (.rmw 24) 25 ∧
      24 < 25 := by
  obtain ⟨target, rank, related, view, sourceRank, ownRank, earlier⟩ :=
    EventAt.rmw_view_rank execution second_rmw_at rfl
  have same : rank = 24 := WriterRank.unique scheduled initial_sequenced sourceRank first_own_rank
  subst rank
  exact ⟨target, related, view, sourceRank, ownRank, earlier⟩

end RMWChain

end EDSL.Tests.AccessSourceRanks

#print axioms EDSL.Tests.AccessSourceRanks.scanned_at_position
#print axioms EDSL.Tests.AccessSourceRanks.scanned_access_domain
#print axioms EDSL.Tests.AccessSourceRanks.actual_access_monotone
#print axioms EDSL.Tests.AccessSourceRanks.actual_load_rank_of_query
#print axioms EDSL.Tests.AccessSourceRanks.Loads.execution
#print axioms EDSL.Tests.AccessSourceRanks.Loads.literal_access_contract
#print axioms EDSL.Tests.AccessSourceRanks.Loads.computed_loads
#print axioms EDSL.Tests.AccessSourceRanks.Loads.initial_load_at
#print axioms EDSL.Tests.AccessSourceRanks.Loads.forwarded_load_at
#print axioms EDSL.Tests.AccessSourceRanks.Loads.published_load_at
#print axioms EDSL.Tests.AccessSourceRanks.Loads.forwarded_after_older_drain_at
#print axioms EDSL.Tests.AccessSourceRanks.Loads.forwarded_query
#print axioms EDSL.Tests.AccessSourceRanks.Loads.published_query
#print axioms EDSL.Tests.AccessSourceRanks.Loads.forwarded_after_older_drain_query
#print axioms EDSL.Tests.AccessSourceRanks.Loads.every_access_domain
#print axioms EDSL.Tests.AccessSourceRanks.Loads.initial_source_view
#print axioms EDSL.Tests.AccessSourceRanks.Loads.forwarded_source_view
#print axioms EDSL.Tests.AccessSourceRanks.Loads.published_source_view
#print axioms EDSL.Tests.AccessSourceRanks.Loads.forwarded_after_older_drain_source_view
#print axioms EDSL.Tests.AccessSourceRanks.Loads.equal_value_cannot_alias_publication_rank
#print axioms EDSL.Tests.AccessSourceRanks.Loads.own_target_monotone
#print axioms EDSL.Tests.AccessSourceRanks.Loads.quiescent_before_return
#print axioms EDSL.Tests.AccessSourceRanks.RMW.execution
#print axioms EDSL.Tests.AccessSourceRanks.RMW.literal_access_contract
#print axioms EDSL.Tests.AccessSourceRanks.RMW.computed_rmws
#print axioms EDSL.Tests.AccessSourceRanks.RMW.first_rmw_at
#print axioms EDSL.Tests.AccessSourceRanks.RMW.second_rmw_at
#print axioms EDSL.Tests.AccessSourceRanks.RMW.first_store_rank
#print axioms EDSL.Tests.AccessSourceRanks.RMW.second_store_rank
#print axioms EDSL.Tests.AccessSourceRanks.RMW.first_source_and_own_rank
#print axioms EDSL.Tests.AccessSourceRanks.RMW.second_source_and_own_rank
#print axioms EDSL.Tests.AccessSourceRanks.RMW.every_access_domain
#print axioms EDSL.Tests.AccessSourceRanks.RMWChain.execution
#print axioms EDSL.Tests.AccessSourceRanks.RMWChain.unchanged_chain_contract
#print axioms EDSL.Tests.AccessSourceRanks.RMWChain.first_rmw_at
#print axioms EDSL.Tests.AccessSourceRanks.RMWChain.second_rmw_at
#print axioms EDSL.Tests.AccessSourceRanks.RMWChain.first_own_rank
#print axioms EDSL.Tests.AccessSourceRanks.RMWChain.second_source_and_own_rank
#audit_edsl
