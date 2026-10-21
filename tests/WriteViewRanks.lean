/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.TSO64CrossCellFixtures
import tests.AccessSourceRanks
import tests.ViewTransfer
import EDSL.OS.TSO64.C23Projection.AtomicTrace.RMWPredecessor
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Coherence
import EDSL.OS.TSO64.ExecutionViews.Query
import EDSL.Audit

/-!
Actual zero-delta RMW endpoint, predecessor and exact-source transfer clients.
A publishes at position 152; the unchanged B RMW at position 153 reads initial
B, then the peer reads that exact RMW and A's buffered writer. Equal B words
must retain different initial/RMW identities and publication ranks.

The second scan begins after the real A issue. Its initial FIFO is nonempty,
and no A issue exists in that suffix. Validity and sequencing come from the
actual parent prefix; the suffix scanner supplies its own actual accesses.

All programs and mappings are project-owned synthetic fixtures. These finite
sharedCell scalar-RAM, long-mode/CET-off statements give no new compiler-corpus
credit, source-C23 legality, happens-before, native execution, fairness or
source-order inference. Endpoint and ordering proofs use production APIs.
-/

namespace EDSL.Tests.WriteViewRanks
open X86 OS.TSO64 OS.TSO64.PublishedHistory OS.TSO64.C23Projection.AtomicTrace

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

/-- Construct the RMW writer from its real observed step and prefix. The
instruction index is normalized while the scheduler states remain abstract. -/
private theorem rmw_instruction {state : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {offset index tid : Nat} {changed : OS.Atomics64.FetchAddEvent}
    (success : schedule state actions profile = .ok result)
    (observed : result.2[index]? = some (.rmw tid changed)) :
    ∃ actual : InstructionWriteAt state actions result profile offset index
      ⟨offset + index, .rmw tid changed⟩, actual.publication.index = index := by
  obtain ⟨before, action, next, prefixRun, actionAt, stepped⟩ :=
    ScheduleTrace.observation_at success observed
  let publication : WriteAt state actions result profile offset
      ⟨offset + index, .rmw tid changed⟩ :=
    ⟨index, .rmw tid changed, before, action, next, rfl, observed,
      prefixRun, actionAt, stepped, rfl⟩
  exact ⟨InstructionWriteAt.rmw publication, rfl⟩

private theorem suffix_execution {state before : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {profile : Profile} {cut : Nat}
    (execution : ExecutionViews.Execution state actions result profile)
    (prefixRun : schedule state (actions.take cut) profile =
      .ok (before, result.2.take cut)) :
    ExecutionViews.Execution before (actions.drop cut)
      (result.1, result.2.drop cut) profile :=
  ⟨(ScheduleTrace.suffix execution.success prefixRun).2,
    schedule_wellFormed execution.valid prefixRun,
    schedule_sequenced execution.sequenced prefixRun, execution.quiescent⟩

private theorem queued_current {state : OS.TSO64.State} {worker : Worker}
    {profile : Profile} {tid occurrence : Nat} {reference : Queue.ManagedRef}
    {word : Word} (valid : WellFormed state profile)
    (live : state.workers[tid]? = some worker)
    (member : .managed reference word occurrence ∈ worker.pending) :
    Queue.Current state.world worker.resources reference :=
  ((valid.2 worker (List.mem_of_getElem? live)).2 _ member).2

/-- Independent complete descriptors, including actor, allocation and epoch.
Their current authority is recovered below from actual admissions/queued tags. -/
def ownA : Queue.ManagedRef := ⟨⟨0⟩, ⟨11, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩⟩
def peerA : Queue.ManagedRef := ⟨⟨1⟩, ⟨12, ⟨0⟩⟩, ⟨7, ⟨0, 0⟩, 65536⟩⟩
def ownB : Queue.ManagedRef := ⟨⟨2⟩, ⟨11, ⟨1⟩⟩, ⟨7, ⟨6, 0⟩, 458752⟩⟩
def peerB : Queue.ManagedRef := ⟨⟨3⟩, ⟨12, ⟨1⟩⟩, ⟨7, ⟨6, 0⟩, 458752⟩⟩

namespace Whole

/-- MOV [RDI],RSI (0); LOCK XADD [RDX],RSI (3); RET (8);
MOV RAX,[RDX] (9); MOV RAX,[RDI] (12); RET (15). -/
def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64CrossCellFixtures.start 0x32c10f48f0378948 0xc3078b48028b48c3
    3 7 0 11 0 9

theorem initial_succeeds : initialAttempt.toOption.isSome = true := by decide +kernel

@[irreducible] def initial : OS.TSO64.State := checked initialAttempt initial_succeeds

theorem initial_actual : initialAttempt = .ok initial := by
  unfold initial
  exact checked_ok _ _

theorem initial_valid : WellFormed initial .sharedCell :=
  TSO64CrossCellFixtures.start_valid initial_actual

def actions : List Action :=
  [.issue 0 false, .drain 0, .issue 0 false, .issue 1 false,
    .issue 1 false, .issue 0 true, .issue 1 true]

def scanAttempt : Except Fault Result := scan initial actions .sharedCell 151 empty

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

@[irreducible] def scanned : Result := checked scanAttempt scan_succeeds

theorem scanned_actual : scan initial actions .sharedCell 151 empty = .ok scanned := by
  unfold scanned
  exact checked_ok _ _

@[irreducible] def result : OS.TSO64.State × List Observation := scanned.execution

theorem scheduled : schedule initial actions .sharedCell = .ok result := by
  unfold result
  exact scan_scheduled scanned_actual

theorem initial_quiescent : Quiescent initial :=
  AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)

theorem initial_sequenced : Sequenced initial :=
  OS.TSO64.C23Projection.quiescent_sequenced initial_quiescent

theorem final_quiescent : Quiescent result.1 :=
  AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)

theorem execution : ExecutionViews.Execution initial actions result .sharedCell :=
  ⟨scheduled, initial_valid, initial_sequenced, final_quiescent⟩

private theorem prefix_succeeds (cut : Nat) :
    (schedule initial (actions.take cut) .sharedCell).toOption.isSome = true := by
  obtain ⟨before, success, _suffix⟩ := ScheduleTrace.cut scheduled cut
  rw [success]
  rfl

@[irreducible] def atCut (cut : Nat) : OS.TSO64.State × List Observation :=
  checked (schedule initial (actions.take cut) .sharedCell) (prefix_succeeds cut)

theorem prefix_exact (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell =
      .ok ((atCut cut).1, result.2.take cut) := by
  have actual : schedule initial (actions.take cut) .sharedCell = .ok (atCut cut) := by
    unfold atCut
    exact checked_ok _ _
  have same := (ScheduleTrace.suffix scheduled actual).1
  rw [← same]
  exact actual

/-- Extract the event from the actual successful RMW observation. Its complete
independent contract below catches a wrong actor, handle, operand or arithmetic. -/
@[irreducible] def changed : OS.Atomics64.FetchAddEvent :=
  found (result.2[2]?.bind fun observation => match observation with
    | .rmw _ event => some event
    | _ => none) (by decide +kernel)

theorem changed_contract : changed = ⟨11, ⟨2⟩, ⟨1⟩, ⟨0, ⟨458752, 7, 7⟩⟩⟩ := by
  decide +kernel

theorem changed_cell : changed.cell = ⟨1⟩ := congrArg OS.Atomics64.FetchAddEvent.cell changed_contract

theorem literal_accesses : scanned.events =
    [⟨151, 0, .store ownA 0 0⟩, ⟨153, 0, .rmw changed (.initial ⟨1⟩)⟩,
      ⟨154, 1, .load peerB 7 (.rmw 153)⟩, ⟨155, 1, .load peerA 0 (.store 0 0)⟩] := by
  decide +kernel

theorem literal_observations : result.2 =
    [.ordinary 0, .drained 0 (.managed ownA 0 0), .rmw 0 changed,
      .ordinary 1, .ordinary 1, .returned 0, .returned 1] := by
  decide +kernel

theorem A_at : EventAt .sharedCell ⟨151, 0, .store ownA 0 0⟩
    0 initial actions result 151 empty := by
  unfold result
  apply AccessSourceRanks.scanned_at_position initial_valid initial_sequenced scanned_actual
  · rw [literal_accesses]; simp
  · rfl

theorem rmw_at : EventAt .sharedCell ⟨153, 0, .rmw changed (.initial ⟨1⟩)⟩
    2 initial actions result 151 empty := by
  unfold result
  apply AccessSourceRanks.scanned_at_position initial_valid initial_sequenced scanned_actual
  · rw [literal_accesses]; simp
  · rfl

theorem B_load_at : EventAt .sharedCell ⟨154, 1, .load peerB 7 (.rmw 153)⟩
    3 initial actions result 151 empty := by
  unfold result
  apply AccessSourceRanks.scanned_at_position initial_valid initial_sequenced scanned_actual
  · rw [literal_accesses]; simp
  · rfl

theorem A_load_at : EventAt .sharedCell ⟨155, 1, .load peerA 0 (.store 0 0)⟩
    4 initial actions result 151 empty := by
  unfold result
  apply AccessSourceRanks.scanned_at_position initial_valid initial_sequenced scanned_actual
  · rw [literal_accesses]; simp
  · rfl

def AStamp : Stamp := ⟨152, .buffered 0 ownA 0 0⟩
def BStamp : Stamp := ⟨153, .rmw 0 changed⟩

theorem A_written : Nonempty (InstructionWriteAt initial actions result .sharedCell 151 0 AStamp) := by
  have observed : result.2[1]? = some (.drained 0 (.managed ownA 0 0)) := by
    rw [literal_observations]; rfl
  obtain ⟨publication, _index⟩ := managed_drain_writeAt (offset := 151) scheduled observed
  exact ⟨InstructionWriteAt.buffered A_at.store_issued publication⟩

theorem B_written :
    ∃ actual : InstructionWriteAt initial actions result .sharedCell 151 2 BStamp,
      actual.publication.index = 2 := by
  apply rmw_instruction (offset := 151) scheduled
  rw [literal_observations]
  rfl

theorem A_rank : WriterRank initial actions result .sharedCell 151 ⟨0⟩ (.store 0 0) 153 := by
  obtain ⟨written⟩ := A_written
  exact WriterRank.publication written.publication rfl

def queried (cut tid : Nat) (target : Queue.ManagedRef) : Option Nat :=
  ExecutionViews.query (atCut cut).1 result.2 cut tid target 151 empty

/-- Independently expected ranks retain the global gap between initial B and
the RMW despite the intervening publication to the separately allocated A. -/
theorem literal_queries :
    queried 1 0 ownA = some 153 ∧ queried 2 0 ownB = some 0 ∧
      queried 3 0 ownB = some 154 ∧ queried 3 0 ownA = some 153 ∧
      queried 3 1 peerA = some 153 ∧ queried 3 1 peerB = some 154 := by
  decide +kernel

private instance : DecidableEq (Word × Word) := inferInstance
private instance : DecidableEq (Nat × Word × Word) := inferInstance
private instance : DecidableEq (List Pending × Nat × Word × Word) := inferInstance

/-- Inspect actual queues, counters and full RAM words at real prefixes. -/
def visibility (cut tid : Nat) : Option (List Pending × Nat × Word × Word) := do
  let before ← (schedule initial (actions.take cut) .sharedCell).toOption
  let worker ← before.1.workers[tid]?
  let a ← (loadQWord (published before.1.world) 65536).toOption
  let b ← (loadQWord (published before.1.world) 458752).toOption
  return (worker.pending, worker.nextStore, a, b)

theorem prefix_queue_RAM_contract :
    visibility 0 0 = some ([], 0, 3, 7) ∧
      visibility 1 0 = some ([.managed ownA 0 0], 1, 3, 7) ∧
      visibility 2 0 = some ([], 1, 0, 7) ∧
      visibility 3 0 = some ([], 1, 0, 7) ∧
      visibility 3 1 = some ([], 0, 0, 7) := by
  decide +kernel

theorem final_machine_contract :
    result.1.workers.map (fun worker => worker.context.registers .rax) = [5, 0] ∧
      result.1.workers.map (fun worker => worker.context.registers .rsi) = [7, 11] ∧
      result.1.workers.map (fun worker => worker.context.registers .rsp) = [262152, 327688] ∧
      result.1.workers.map Worker.phase = [.returned, .returned] ∧
      result.1.workers.map Worker.nextStore = [1, 0] ∧
      (loadQWord (published result.1.world) 65536).toOption = some 0 ∧
      (loadQWord (published result.1.world) 458752).toOption = some 7 := by
  decide +kernel

/-- The production endpoint constructs the current B authority and exact
postcut rank from the real RMW writer. Incoming metadata is arbitrary. -/
theorem rmw_self_view (incoming : Writers) :
    ∃ original target, initial.workers[0]? = some original ∧
      Queue.Current initial.world original.resources target ∧ target.handle.cell = ⟨1⟩ ∧
      Nonempty (ExecutionViews.At initial actions result .sharedCell 3 0 target
        151 incoming 154) := by
  obtain ⟨written, _index⟩ := B_written
  simpa only [BStamp, WriteCause.tid, WriteCause.cell, changed_cell] using
    (InstructionWriteAt.self_view execution written incoming)

/-- Retarget the actual self-view through the peer's separately admitted
current B handle. Its identifier differs from the RMW's actual handle. -/
theorem rmw_self_current_alias :
    changed.handle ≠ peerB.identifier ∧
      ∃ peer, initial.workers[1]? = some peer ∧
        Queue.Current initial.world peer.resources peerB ∧
        Nonempty (ExecutionViews.At initial actions result .sharedCell 3 0 peerB
          151 empty 154) := by
  obtain ⟨_writer, target, _writerLive, writerCurrent, cell, ⟨view⟩⟩ := rmw_self_view empty
  obtain ⟨peer, selected, peerLive, peerCurrent, related⟩ := B_load_at.initial_authority
  have selectedEq : selected = peerB := related.2
  subst selected
  have sameCell : target.handle.cell = peerB.handle.cell := cell
  refine ⟨?_, peer, peerLive, peerCurrent,
    ⟨view.retarget_current writerCurrent peerCurrent sameCell⟩⟩
  rw [changed_contract]
  decide

/-- The exact RMW source is initial B at rank zero, and its own rank is 154.
The universal predecessor bound excludes every earlier actual B publication. -/
theorem initial_B_predecessor :
    WriterRank initial actions result .sharedCell 151 ⟨1⟩ (.initial ⟨1⟩) 0 ∧
      WriterRank initial actions result .sharedCell 151 ⟨1⟩ (.rmw 153) 154 ∧
      0 < 154 ∧
      ∀ stamp, WriteAt initial actions result .sharedCell 151 stamp →
        stamp.cause.cell = ⟨1⟩ → ¬ stamp.position < 153 := by
  obtain ⟨rank, source, own, before, prior⟩ := EventAt.rmw_predecessor execution rmw_at rfl
  have zero : rank = 0 := by
    apply WriterRank.unique scheduled initial_sequenced source
    rw [changed_cell]
    exact .initial
  subst rank
  refine ⟨?_, ?_, before, ?_⟩
  · simpa only [changed_cell] using source
  · simpa only [changed_cell] using own
  · intro stamp written cell earlier
    have bound := prior stamp written (cell.trans changed_cell.symm) earlier
    omega

/-- A genuinely published between initial B and the RMW. It is another cell,
so the global rank gap cannot be mistaken for a missing B predecessor. -/
theorem intervening_A_publication :
    ∃ actual : WriteAt initial actions result .sharedCell 151 AStamp,
      actual.index = 1 ∧ AStamp.position = 152 ∧ AStamp.cause.cell ≠ changed.cell := by
  obtain ⟨written⟩ := A_written
  have position := written.publication.position
  have index : written.publication.index = 1 := by
    change 152 = 151 + written.publication.index at position
    omega
  refine ⟨written.publication, index, rfl, ?_⟩
  rw [changed_cell]
  decide

theorem B_load_source_rank :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 3 1 peerB 151 empty 154) ∧
      WriterRank initial actions result .sharedCell 151 ⟨1⟩ (.rmw 153) 154 :=
  AccessSourceRanks.actual_load_rank_of_query execution B_load_at rfl
    (prefix_exact 3) literal_queries.2.2.2.2.2

theorem A_load_source_rank :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 4 1 peerA 151 empty 153) ∧
      WriterRank initial actions result .sharedCell 151 ⟨0⟩ (.store 0 0) 153 := by
  have answer : queried 4 1 peerA = some 153 := by decide +kernel
  exact AccessSourceRanks.actual_load_rank_of_query execution A_load_at rfl (prefix_exact 4) answer

/-- Apply exact-source transfer to the separate A cell. The source is the
actual RMW, both A views come from queries, and both aliases have authority
recovered from actual access admissions. No ordering premise is supplied. -/
theorem rmw_transfers_A :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 3 0 ownA 151 empty 153) ∧
      Nonempty (ExecutionViews.At initial actions result .sharedCell 3 1 peerA 151 empty 153) ∧
      153 ≤ 153 := by
  obtain ⟨_writer, target, writerLive, writerCurrent, writerRelated⟩ := A_at.initial_authority
  have targetEq : target = ownA := writerRelated.2
  subst target
  obtain ⟨_peer, alias, peerLive, peerCurrent, peerRelated⟩ := A_load_at.initial_authority
  have aliasEq : alias = peerA := peerRelated.2
  subst alias
  obtain ⟨earlier⟩ := ExecutionViews.query_sound execution writerLive (prefix_exact 3)
    writerCurrent literal_queries.2.2.2.1
  obtain ⟨later⟩ := ExecutionViews.query_sound execution peerLive (prefix_exact 3)
    peerCurrent literal_queries.2.2.2.2.1
  obtain ⟨written, _index⟩ := B_written
  exact ⟨⟨earlier⟩, ⟨later⟩,
    B_load_at.transfers_view_alias execution rfl written rfl
      earlier later writerCurrent peerCurrent rfl⟩

end Whole

namespace Suffix

@[irreducible] def initial : OS.TSO64.State := (Whole.atCut 1).1
def actions : List Action := Whole.actions.drop 1

def scanAttempt : Except Fault Result := scan initial actions .sharedCell 152 empty

theorem scan_succeeds : scanAttempt.toOption.isSome = true := by decide +kernel

@[irreducible] def scanned : Result := checked scanAttempt scan_succeeds

theorem scanned_actual : scan initial actions .sharedCell 152 empty = .ok scanned := by
  unfold scanned
  exact checked_ok _ _

@[irreducible] def result : OS.TSO64.State × List Observation := scanned.execution

theorem scheduled : schedule initial actions .sharedCell = .ok result := by
  unfold result
  exact scan_scheduled scanned_actual

/-- Determinism identifies the suffix scanner with the actual parent suffix;
the boundary state, final state and observation stream are not premises. -/
theorem execution_eq : result = (Whole.result.1, Whole.result.2.drop 1) := by
  have actual : schedule initial actions .sharedCell =
      .ok (Whole.result.1, Whole.result.2.drop 1) := by
    simpa only [initial, actions] using
      (ScheduleTrace.suffix Whole.scheduled (Whole.prefix_exact 1)).2
  exact Except.ok.inj (scheduled.symm.trans actual)

theorem execution : ExecutionViews.Execution initial actions result .sharedCell := by
  rw [execution_eq]
  unfold initial actions
  exact suffix_execution Whole.execution (Whole.prefix_exact 1)

private theorem prefix_succeeds (cut : Nat) :
    (schedule initial (actions.take cut) .sharedCell).toOption.isSome = true := by
  obtain ⟨before, success, _suffix⟩ := ScheduleTrace.cut scheduled cut
  rw [success]
  rfl

@[irreducible] def atCut (cut : Nat) : OS.TSO64.State × List Observation :=
  checked (schedule initial (actions.take cut) .sharedCell) (prefix_succeeds cut)

theorem prefix_exact (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell =
      .ok ((atCut cut).1, result.2.take cut) := by
  have actual : schedule initial (actions.take cut) .sharedCell = .ok (atCut cut) := by
    unfold atCut
    exact checked_ok _ _
  have same := (ScheduleTrace.suffix scheduled actual).1
  rw [← same]
  exact actual

@[irreducible] def incomingWorker : Worker := found (initial.workers[0]?) (by decide +kernel)

theorem incoming_live : initial.workers[0]? = some incomingWorker := by
  unfold incomingWorker
  exact found_ok _ _

theorem incoming_fifo_contract : incomingWorker.pending = [.managed ownA 0 0] ∧
    incomingWorker.nextStore = 1 ∧ incomingWorker.resources.actor = 11 := by
  decide +kernel

theorem incoming_A_current : Queue.Current initial.world incomingWorker.resources ownA :=
  queued_current (word := 0) (occurrence := 0) execution.valid incoming_live
    (by rw [incoming_fifo_contract.1]; simp)

/-- Occurrence zero is already below the incoming counter one. No complete
reference or value can manufacture a suffix instruction with that occurrence. -/
theorem no_new_occurrence_zero (index : Nat) (target : Queue.ManagedRef) (word : Word) :
    ¬ StoreHistory.IssuedAt .sharedCell 0 (.managed target word 0) index initial actions result := by
  intro issued
  have lower := issued.occurrence_lower incoming_live
  have counter := incoming_fifo_contract.2.1
  omega

theorem no_new_A_instruction_write (index position : Nat) :
    ¬ Nonempty (InstructionWriteAt initial actions result .sharedCell 152 index
      ⟨position, .buffered 0 ownA 0 0⟩) := by
  rintro ⟨written⟩
  exact no_new_occurrence_zero index ownA 0 written.actual

/-- The suffix emits no A store access. The RMW and both peer loads keep their
absolute positions even though their local indices have each decreased by one. -/
theorem literal_accesses : scanned.events =
    [⟨153, 0, .rmw Whole.changed (.initial ⟨1⟩)⟩,
      ⟨154, 1, .load peerB 7 (.rmw 153)⟩, ⟨155, 1, .load peerA 0 (.store 0 0)⟩] := by
  decide +kernel

theorem literal_observations : result.2 =
    [.drained 0 (.managed ownA 0 0), .rmw 0 Whole.changed,
      .ordinary 1, .ordinary 1, .returned 0, .returned 1] := by
  simp only [execution_eq, Whole.literal_observations, List.drop_succ_cons, List.drop_zero]

theorem rmw_at : EventAt .sharedCell ⟨153, 0, .rmw Whole.changed (.initial ⟨1⟩)⟩
    1 initial actions result 152 empty := by
  unfold result
  apply AccessSourceRanks.scanned_at_position execution.valid execution.sequenced scanned_actual
  · rw [literal_accesses]; simp
  · rfl

theorem B_load_at : EventAt .sharedCell ⟨154, 1, .load peerB 7 (.rmw 153)⟩
    2 initial actions result 152 empty := by
  unfold result
  apply AccessSourceRanks.scanned_at_position execution.valid execution.sequenced scanned_actual
  · rw [literal_accesses]; simp
  · rfl

theorem A_load_at : EventAt .sharedCell ⟨155, 1, .load peerA 0 (.store 0 0)⟩
    3 initial actions result 152 empty := by
  unfold result
  apply AccessSourceRanks.scanned_at_position execution.valid execution.sequenced scanned_actual
  · rw [literal_accesses]; simp
  · rfl

theorem B_written :
    ∃ actual : InstructionWriteAt initial actions result .sharedCell 152 1 Whole.BStamp,
      actual.publication.index = 1 := by
  apply rmw_instruction (offset := 152) scheduled
  rw [literal_observations]
  rfl

/-- A has a real publication rank in this suffix without an instruction origin
in this suffix. The actual incoming occurrence publishes at local zero. -/
theorem A_rank : WriterRank initial actions result .sharedCell 152 ⟨0⟩ (.store 0 0) 153 := by
  have observed : result.2[0]? = some (.drained 0 (.managed ownA 0 0)) := by
    rw [literal_observations]; rfl
  obtain ⟨publication, _index⟩ := managed_drain_writeAt (offset := 152) scheduled observed
  exact WriterRank.publication publication rfl

def queried (cut tid : Nat) (target : Queue.ManagedRef) : Option Nat :=
  ExecutionViews.query (atCut cut).1 result.2 cut tid target 152 empty

theorem literal_queries :
    queried 0 0 ownA = some 153 ∧ queried 1 0 ownB = some 0 ∧
      queried 2 0 ownB = some 154 ∧ queried 2 0 ownA = some 153 ∧
      queried 2 1 peerA = some 153 ∧ queried 2 1 peerB = some 154 := by
  decide +kernel

/-- A's incoming pending view is authenticated by the actual queued full tag,
the actual suffix and the actual later drain. No new A instruction is needed. -/
theorem incoming_A_view :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 0 0 ownA 152 empty 153) :=
  ExecutionViews.query_sound execution incoming_live (prefix_exact 0)
    incoming_A_current literal_queries.1

theorem final_machine_contract :
    result.1.workers.map (fun worker => worker.context.registers .rax) = [5, 0] ∧
      result.1.workers.map (fun worker => worker.context.registers .rsi) = [7, 11] ∧
      result.1.workers.map Worker.phase = [.returned, .returned] ∧
      result.1.workers.map Worker.nextStore = [1, 0] ∧
      (loadQWord (published result.1.world) 65536).toOption = some 0 ∧
      (loadQWord (published result.1.world) 458752).toOption = some 7 := by
  rw [execution_eq]
  have parent := Whole.final_machine_contract
  exact ⟨parent.1, parent.2.1, parent.2.2.2.1, parent.2.2.2.2.1,
    parent.2.2.2.2.2.1, parent.2.2.2.2.2.2⟩

/-- The same endpoint applies when this run starts with A already queued.
The actual RMW is local one, with successor cut two and absolute rank 154. -/
theorem rmw_self_view (incoming : Writers) :
    ∃ original target, initial.workers[0]? = some original ∧
      Queue.Current initial.world original.resources target ∧ target.handle.cell = ⟨1⟩ ∧
      Nonempty (ExecutionViews.At initial actions result .sharedCell 2 0 target
        152 incoming 154) := by
  obtain ⟨written, _index⟩ := B_written
  simpa only [Whole.BStamp, WriteCause.tid, WriteCause.cell, Whole.changed_cell] using
    (InstructionWriteAt.self_view execution written incoming)

theorem initial_B_predecessor :
    WriterRank initial actions result .sharedCell 152 ⟨1⟩ (.initial ⟨1⟩) 0 ∧
      WriterRank initial actions result .sharedCell 152 ⟨1⟩ (.rmw 153) 154 ∧
      0 < 154 ∧
      ∀ stamp, WriteAt initial actions result .sharedCell 152 stamp →
        stamp.cause.cell = ⟨1⟩ → ¬ stamp.position < 153 := by
  obtain ⟨rank, source, own, before, prior⟩ := EventAt.rmw_predecessor execution rmw_at rfl
  have zero : rank = 0 := by
    apply WriterRank.unique scheduled execution.sequenced source
    rw [Whole.changed_cell]
    exact .initial
  subst rank
  refine ⟨?_, ?_, before, ?_⟩
  · simpa only [Whole.changed_cell] using source
  · simpa only [Whole.changed_cell] using own
  · intro stamp written cell earlier
    have bound := prior stamp written (cell.trans Whole.changed_cell.symm) earlier
    omega

theorem B_load_source_rank :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 2 1 peerB 152 empty 154) ∧
      WriterRank initial actions result .sharedCell 152 ⟨1⟩ (.rmw 153) 154 :=
  AccessSourceRanks.actual_load_rank_of_query execution B_load_at rfl
    (prefix_exact 2) literal_queries.2.2.2.2.2

theorem A_load_source_rank :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 3 1 peerA 152 empty 153) ∧
      WriterRank initial actions result .sharedCell 152 ⟨0⟩ (.store 0 0) 153 := by
  have answer : queried 3 1 peerA = some 153 := by decide +kernel
  exact AccessSourceRanks.actual_load_rank_of_query execution A_load_at rfl (prefix_exact 3) answer

/-- The transferred A domain is the nonempty incoming FIFO's actual current
target. Its earlier instruction is absent from this scan. The new writer is
the actual RMW, and the actual peer B load identifies its exact source. -/
theorem incoming_A_transferred_by_RMW :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 0 0 ownA 152 empty 153) ∧
      Nonempty (ExecutionViews.At initial actions result .sharedCell 2 0 ownA 152 empty 153) ∧
      Nonempty (ExecutionViews.At initial actions result .sharedCell 2 1 peerA 152 empty 153) ∧
      153 ≤ 153 ∧
      (∀ index, ¬ StoreHistory.IssuedAt .sharedCell 0 (.managed ownA 0 0)
        index initial actions result) := by
  obtain ⟨_peer, alias, peerLive, peerCurrent, related⟩ := A_load_at.initial_authority
  have aliasEq : alias = peerA := related.2
  subst alias
  obtain ⟨earlier⟩ := ExecutionViews.query_sound execution incoming_live (prefix_exact 2)
    incoming_A_current literal_queries.2.2.2.1
  obtain ⟨later⟩ := ExecutionViews.query_sound execution peerLive (prefix_exact 2)
    peerCurrent literal_queries.2.2.2.2.1
  obtain ⟨written, _index⟩ := B_written
  exact ⟨incoming_A_view, ⟨earlier⟩, ⟨later⟩,
    B_load_at.transfers_view_alias execution rfl written rfl
      earlier later incoming_A_current peerCurrent rfl,
    fun index => no_new_occurrence_zero index ownA 0⟩

end Suffix

namespace Reused

/-- Reuse the initial and published reads of the existing equal-word fixture.
The RR API obtains both source ranks; independent existing view witnesses fix
them at zero and fifteen, including the peer's separate current handle. -/
theorem initial_to_published_RR :
    WriterRank AccessSourceRanks.Loads.initial AccessSourceRanks.Loads.actions
      AccessSourceRanks.Loads.result .sharedCell 10
      AccessSourceRanks.Loads.firstReference.handle.cell (.initial ⟨0⟩) 0 ∧
    WriterRank AccessSourceRanks.Loads.initial AccessSourceRanks.Loads.actions
      AccessSourceRanks.Loads.result .sharedCell 10
      AccessSourceRanks.Loads.peerReference.handle.cell (.store 0 0) 15 ∧ 0 ≤ 15 := by
  have sameCell : AccessSourceRanks.Loads.firstReference.handle.cell =
      AccessSourceRanks.Loads.peerReference.handle.cell := by decide +kernel
  obtain ⟨firstRank, secondRank, first, second, ordered⟩ := EventAt.read_read_rank
    AccessSourceRanks.Loads.execution AccessSourceRanks.Loads.initial_load_at rfl
    AccessSourceRanks.Loads.published_load_at rfl rfl sameCell (by decide)
  have firstEq := WriterRank.unique AccessSourceRanks.Loads.scheduled
    AccessSourceRanks.Loads.initial_sequenced first AccessSourceRanks.Loads.initial_source_view.2
  have secondEq := WriterRank.unique AccessSourceRanks.Loads.scheduled
    AccessSourceRanks.Loads.initial_sequenced second AccessSourceRanks.Loads.published_source_view.2
  subst firstRank
  subst secondRank
  exact ⟨first, second, ordered⟩

/-- Own forwarding retains the future publication rank eighteen across the
older equal-word writer's drain. The actual load indices are three and six. -/
theorem forwarding_RR :
    WriterRank AccessSourceRanks.Loads.initial AccessSourceRanks.Loads.actions
      AccessSourceRanks.Loads.result .sharedCell 10
      AccessSourceRanks.Loads.ownReference.handle.cell (.store 0 1) 18 ∧ 18 ≤ 18 := by
  obtain ⟨firstRank, secondRank, first, second, ordered⟩ := EventAt.read_read_rank
    AccessSourceRanks.Loads.execution AccessSourceRanks.Loads.forwarded_load_at rfl
    AccessSourceRanks.Loads.forwarded_after_older_drain_at rfl rfl rfl (by decide)
  have firstEq := WriterRank.unique AccessSourceRanks.Loads.scheduled
    AccessSourceRanks.Loads.initial_sequenced first AccessSourceRanks.Loads.forwarded_source_view.2
  have secondEq := WriterRank.unique AccessSourceRanks.Loads.scheduled
    AccessSourceRanks.Loads.initial_sequenced second
    AccessSourceRanks.Loads.forwarded_after_older_drain_source_view.2
  subst firstRank
  subst secondRank
  exact ⟨first, ordered⟩

/-- Exercise buffered write/read coherence on the existing own-forwarding
trace, where the publication rank 109 is later than the load's position 104. -/
theorem forwarded_WR :
    WriterRank (ViewTransfer.initial .forwarded) (ViewTransfer.actions .forwarded)
      (ViewTransfer.result .forwarded) .sharedCell 101 ViewTransfer.ownB.handle.cell
      (.store 0 1) 109 ∧ 109 ≤ 109 := by
  obtain ⟨written⟩ := ViewTransfer.B_written .forwarded
  obtain ⟨rank, ranked, bound⟩ := EventAt.write_read_rank (ViewTransfer.execution .forwarded)
    written (ViewTransfer.read_at .forwarded) rfl rfl rfl (by decide)
  have expected := AccessSourceRanks.actual_load_rank_of_query (ViewTransfer.execution .forwarded)
    (ViewTransfer.read_at .forwarded) rfl (ViewTransfer.prefix_exact .forwarded 3)
    (ViewTransfer.literal_view_queries .forwarded).2.2
  have same := WriterRank.unique (ViewTransfer.scheduled .forwarded)
    (ViewTransfer.initial_sequenced .forwarded) ranked expected.2
  subst rank
  exact ⟨ranked, bound⟩

private theorem own_B_initial_load : EventAt .sharedCell
    ⟨102, 0, .load ViewTransfer.ownB 7 (.initial ⟨1⟩)⟩ 1
    (ViewTransfer.initial .pending) (ViewTransfer.actions .pending)
    (ViewTransfer.result .pending) 101 empty := by
  unfold ViewTransfer.result
  apply AccessSourceRanks.scanned_at_position (ViewTransfer.initial_valid .pending)
    (ViewTransfer.initial_sequenced .pending) (ViewTransfer.scanned_actual .pending)
  · rw [ViewTransfer.literal_accesses]; simp
  · rfl

/-- Initial seven and the later written seven remain distinct sources. Strict
RW is derived from the actual early B load and later B instruction write. -/
theorem initial_RW :
    WriterRank (ViewTransfer.initial .pending) (ViewTransfer.actions .pending)
      (ViewTransfer.result .pending) .sharedCell 101 ViewTransfer.ownB.handle.cell
      (.initial ⟨1⟩) 0 ∧ 0 < 107 := by
  obtain ⟨written⟩ := ViewTransfer.B_written .pending
  obtain ⟨rank, ranked, bound⟩ := EventAt.read_write_rank_lt (ViewTransfer.execution .pending)
    own_B_initial_load rfl written rfl (by decide)
  have zero := WriterRank.unique (ViewTransfer.scheduled .pending)
    (ViewTransfer.initial_sequenced .pending) ranked .initial
  subst rank
  exact ⟨ranked, bound⟩

private theorem peer_B_store : EventAt .sharedCell
    ⟨108, 1, .store ViewTransfer.peerB 11 1⟩ 7
    (ViewTransfer.initial .pending) (ViewTransfer.actions .pending)
    (ViewTransfer.result .pending) 101 empty := by
  unfold ViewTransfer.result
  apply AccessSourceRanks.scanned_at_position (ViewTransfer.initial_valid .pending)
    (ViewTransfer.initial_sequenced .pending) (ViewTransfer.scanned_actual .pending)
  · rw [ViewTransfer.literal_accesses]; simp
  · rfl

private theorem peer_B_written :
    ∃ actual : InstructionWriteAt (ViewTransfer.initial .pending) (ViewTransfer.actions .pending)
      (ViewTransfer.result .pending) .sharedCell 101 7
      ⟨114, .buffered 1 ViewTransfer.peerB 11 1⟩, actual.publication.index = 13 := by
  have observed : (ViewTransfer.result .pending).2[13]? =
      some (.drained 1 (.managed ViewTransfer.peerB 11 1)) := by
    rw [ViewTransfer.literal_observations]; rfl
  obtain ⟨publication, index⟩ := managed_drain_writeAt
    (offset := 101) (ViewTransfer.scheduled .pending) observed
  exact ⟨InstructionWriteAt.buffered peer_B_store.store_issued publication, index⟩

/-- The actual peer reads the writer at rank 107 before issuing its own B
store, whose later real drain gives rank 115. No program is reconstructed. -/
theorem peer_RW :
    WriterRank (ViewTransfer.initial .pending) (ViewTransfer.actions .pending)
      (ViewTransfer.result .pending) .sharedCell 101 ViewTransfer.peerB.handle.cell
      (.store 0 1) 107 ∧ 107 < 115 := by
  obtain ⟨written, _index⟩ := peer_B_written
  obtain ⟨rank, ranked, bound⟩ := EventAt.read_write_rank_lt (ViewTransfer.execution .pending)
    (ViewTransfer.read_at .pending) rfl written rfl (by decide)
  have expected := AccessSourceRanks.actual_load_rank_of_query (ViewTransfer.execution .pending)
    (ViewTransfer.read_at .pending) rfl (ViewTransfer.prefix_exact .pending 6)
    (ViewTransfer.literal_view_queries .pending).2.2
  have same := WriterRank.unique (ViewTransfer.scheduled .pending)
    (ViewTransfer.initial_sequenced .pending) ranked expected.2
  subst rank
  exact ⟨ranked, bound⟩

end Reused

end EDSL.Tests.WriteViewRanks

#print axioms EDSL.Tests.WriteViewRanks.Whole.execution
#print axioms EDSL.Tests.WriteViewRanks.Whole.changed_contract
#print axioms EDSL.Tests.WriteViewRanks.Whole.literal_accesses
#print axioms EDSL.Tests.WriteViewRanks.Whole.literal_observations
#print axioms EDSL.Tests.WriteViewRanks.Whole.A_written
#print axioms EDSL.Tests.WriteViewRanks.Whole.B_written
#print axioms EDSL.Tests.WriteViewRanks.Whole.A_rank
#print axioms EDSL.Tests.WriteViewRanks.Whole.literal_queries
#print axioms EDSL.Tests.WriteViewRanks.Whole.prefix_queue_RAM_contract
#print axioms EDSL.Tests.WriteViewRanks.Whole.final_machine_contract
#print axioms EDSL.Tests.WriteViewRanks.Whole.rmw_self_view
#print axioms EDSL.Tests.WriteViewRanks.Whole.rmw_self_current_alias
#print axioms EDSL.Tests.WriteViewRanks.Whole.initial_B_predecessor
#print axioms EDSL.Tests.WriteViewRanks.Whole.intervening_A_publication
#print axioms EDSL.Tests.WriteViewRanks.Whole.B_load_source_rank
#print axioms EDSL.Tests.WriteViewRanks.Whole.A_load_source_rank
#print axioms EDSL.Tests.WriteViewRanks.Whole.rmw_transfers_A
#print axioms EDSL.Tests.WriteViewRanks.Suffix.execution_eq
#print axioms EDSL.Tests.WriteViewRanks.Suffix.execution
#print axioms EDSL.Tests.WriteViewRanks.Suffix.incoming_fifo_contract
#print axioms EDSL.Tests.WriteViewRanks.Suffix.incoming_A_current
#print axioms EDSL.Tests.WriteViewRanks.Suffix.no_new_occurrence_zero
#print axioms EDSL.Tests.WriteViewRanks.Suffix.no_new_A_instruction_write
#print axioms EDSL.Tests.WriteViewRanks.Suffix.literal_accesses
#print axioms EDSL.Tests.WriteViewRanks.Suffix.literal_observations
#print axioms EDSL.Tests.WriteViewRanks.Suffix.B_written
#print axioms EDSL.Tests.WriteViewRanks.Suffix.A_rank
#print axioms EDSL.Tests.WriteViewRanks.Suffix.literal_queries
#print axioms EDSL.Tests.WriteViewRanks.Suffix.incoming_A_view
#print axioms EDSL.Tests.WriteViewRanks.Suffix.final_machine_contract
#print axioms EDSL.Tests.WriteViewRanks.Suffix.rmw_self_view
#print axioms EDSL.Tests.WriteViewRanks.Suffix.initial_B_predecessor
#print axioms EDSL.Tests.WriteViewRanks.Suffix.B_load_source_rank
#print axioms EDSL.Tests.WriteViewRanks.Suffix.A_load_source_rank
#print axioms EDSL.Tests.WriteViewRanks.Suffix.incoming_A_transferred_by_RMW
#print axioms EDSL.Tests.WriteViewRanks.Reused.initial_to_published_RR
#print axioms EDSL.Tests.WriteViewRanks.Reused.forwarding_RR
#print axioms EDSL.Tests.WriteViewRanks.Reused.forwarded_WR
#print axioms EDSL.Tests.WriteViewRanks.Reused.initial_RW
#print axioms EDSL.Tests.WriteViewRanks.Reused.peer_RW
#audit_edsl
