/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.PublicationCoverage

/-!
A positive finite-execution boundary client starting after the actual ordinary
store and A store. The incoming mixed FIFO is retained, including A occurrence
one below the incoming counter two. Its actual later publication supplies a
pending view without an invented instruction issue in this suffix.

The numerical cross-cell bound uses an actual later B issue and publication.
These are scalar-RAM, sharedCell, long-mode, CET-off model statements; they do
not establish source legality, fairness, native execution or graph acceptance.
-/

set_option autoImplicit false

namespace EDSL.Tests.PublicationCoverageBoundary
open X86 OS.TSO64 StoreHistory PublishedHistory

/-- Remove two real executed actions from an indexed issue. Prefix determinism
identifies the supplied boundary with the actual second successor state. Keep
the endpoint states abstract so this proof does not normalize fixture worlds. -/
private theorem issue_after_two {state before : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {profile : Profile} {tid index : Nat} {entry : Pending}
    (issued : IssuedAt profile tid entry (index + 2) state actions result)
    (prefixRun : schedule state (actions.take 2) profile =
      .ok (before, result.2.take 2)) :
    IssuedAt profile tid entry index before (actions.drop 2)
      (result.1, result.2.drop 2) := by
  cases issued with
  | @later state action _ first _ _ stepped _ later =>
      cases later with
      | @later _ nextAction rest second _ _ nextStep _ actual =>
          have actualPrefix :
              schedule state ((action :: nextAction :: rest).take 2) profile =
                .ok (second.1, [first.2, second.2]) := by
            simp only [List.take_succ_cons, List.take_zero, schedule, stepped,
              nextStep, ok_bind, pure_ok]
          have stateEq : before = second.1 :=
            congrArg Prod.fst (Except.ok.inj (prefixRun.symm.trans actualPrefix))
          simpa only [stateEq, List.drop_succ_cons, List.drop_zero] using actual

/-- Current authority is recovered from the actual managed tag and full global
well-formedness, rather than decided from a constructed address-only handle. -/
private theorem queued_current {state : OS.TSO64.State} {worker : Worker}
    {profile : Profile} {tid occurrence : Nat} {reference : Queue.ManagedRef}
    {value : Word} (valid : WellFormed state profile)
    (live : state.workers[tid]? = some worker)
    (member : .managed reference value occurrence ∈ worker.pending) :
    Queue.Current state.world worker.resources reference :=
  ((valid.2 worker (List.mem_of_getElem? live)).2 _ member).2

private theorem suffix_execution {state before : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {profile : Profile} (execution : ExecutionViews.Execution state actions result profile)
    (prefixRun : schedule state (actions.take 2) profile =
      .ok (before, result.2.take 2)) :
    ExecutionViews.Execution before (actions.drop 2) (result.1, result.2.drop 2) profile :=
  ⟨(ScheduleTrace.suffix execution.success prefixRun).2,
    schedule_wellFormed execution.valid prefixRun,
    schedule_sequenced execution.sequenced prefixRun, execution.quiescent⟩

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

/-- The boundary is the real parent cut after ordinary occurrence zero and
managed A occurrence one. It is not a replacement worker or assumed poststate. -/
@[irreducible] def initial : OS.TSO64.State := (PublicationCoverage.atCut 2).1

def actions : List Action := PublicationCoverage.actions.drop 2

@[irreducible] def result : OS.TSO64.State × List Observation :=
  (PublicationCoverage.result.1, PublicationCoverage.result.2.drop 2)

theorem execution : ExecutionViews.Execution initial actions result .sharedCell := by
  unfold initial actions result
  exact suffix_execution (state := PublicationCoverage.initial)
      (before := (PublicationCoverage.atCut 2).1) (actions := PublicationCoverage.actions)
      (result := PublicationCoverage.result)
      PublicationCoverage.execution (PublicationCoverage.prefix_exact 2)

theorem scheduled : schedule initial actions .sharedCell = .ok result := execution.success

/-- Every local position counts one original action, including the blocked
LOCK attempts, the ordinary drain, peer actions and RETs. -/
theorem remaining_actions : actions =
    [.issue 1 false, .issue 0 false, .issue 0 true,
      .drain 0, .drain 1, .drain 0, .issue 0 false, .drain 0,
      .issue 0 true, .issue 1 false, .issue 0 false, .issue 1 true] := by
  decide +kernel

private theorem prefix_succeeds (cut : Nat) :
    (schedule initial (actions.take cut) .sharedCell).toOption.isSome = true := by
  obtain ⟨before, success, _suffix⟩ := ScheduleTrace.cut scheduled cut
  rw [success]
  rfl

@[irreducible] def atCut (cut : Nat) : OS.TSO64.State × List Observation :=
  checked (schedule initial (actions.take cut) .sharedCell) (prefix_succeeds cut)

theorem prefix_scheduled (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell = .ok (atCut cut) := by
  unfold atCut
  exact checked_ok _ _

theorem prefix_exact (cut : Nat) :
    schedule initial (actions.take cut) .sharedCell =
      .ok ((atCut cut).1, result.2.take cut) := by
  have same := (ScheduleTrace.suffix scheduled (prefix_scheduled cut)).1
  rw [← same]
  exact prefix_scheduled cut

@[irreducible] def incomingWorker : Worker :=
  found (initial.workers[0]?) (by decide +kernel)

theorem incoming_live : initial.workers[0]? = some incomingWorker := by
  unfold incomingWorker
  exact found_ok _ _

private def managedReference (entry : Pending) : Option Queue.ManagedRef :=
  match entry with
  | .ordinary _ _ => none
  | .managed reference _ _ => some reference

/-- Extract the complete descriptor actually retained by the incoming FIFO. -/
@[irreducible] def incomingA : Queue.ManagedRef :=
  found (incomingWorker.pending[1]?.bind managedReference) (by decide +kernel)

private def entrySummary (entry : Pending) :
    Nat × Word × StoreBuffer.Mixed.Value × Option Nat :=
  match entry with
  | .ordinary _ store => (0, store.address, store.value, none)
  | .managed reference value occurrence =>
      (1, reference.cell.address, .qword value, some occurrence)

/-- Literal byte addresses, widths and payloads check the actual decoded store
operands; the managed identity retains the gap consumed by the ordinary head. -/
theorem incoming_mixed_fifo :
    incomingWorker.pending.map entrySummary =
      [(0, 131076, .dword 7, none), (1, 65536, .qword 7, some 1)] ∧
      incomingWorker.nextStore = 2 := by
  decide +kernel

theorem incoming_A_tag : incomingWorker.pending[1]? =
    some (.managed incomingA 7 1) := by
  decide +kernel

theorem incoming_A_queued : Queued initial 0 (.managed incomingA 7 1) :=
  ⟨incomingWorker, incoming_live, List.mem_of_getElem? incoming_A_tag⟩

theorem incoming_A_current : Queue.Current initial.world incomingWorker.resources incomingA :=
  queued_current execution.valid incoming_live (List.mem_of_getElem? incoming_A_tag)

/-- The earlier A issue belongs to the parent prefix. Every actual new-run
issue must allocate at least the actual incoming counter two, so no index,
reference or equal-valued payload can invent a new issue of occurrence one. -/
theorem incoming_occurrence_has_no_new_issue (index : Nat) (reference : Queue.ManagedRef)
    (value : Word) :
    ¬ IssuedAt .sharedCell 0 (.managed reference value 1) index initial actions result := by
  intro issued
  have lower := issued.occurrence_lower incoming_live
  have counter := incoming_mixed_fifo.2
  omega

theorem incoming_A_has_no_new_issue (index : Nat) :
    ¬ IssuedAt .sharedCell 0 (.managed incomingA 7 1) index initial actions result :=
  incoming_occurrence_has_no_new_issue index incomingA 7

theorem incoming_A_has_no_new_instruction_write (index position : Nat) :
    ¬ Nonempty (InstructionWriteAt initial actions result .sharedCell 61 index
      ⟨position, .buffered 0 incomingA 7 1⟩) := by
  rintro ⟨actual⟩
  exact incoming_A_has_no_new_issue index actual.actual

@[irreducible] def afterBWorker : Worker :=
  found ((atCut 2).1.workers[0]?) (by decide +kernel)

theorem afterB_live : (atCut 2).1.workers[0]? = some afterBWorker := by
  unfold afterBWorker
  exact found_ok _ _

/-- B's descriptor also comes from a real admitted tag, now after local action
one. The incoming ordinary and A entries still precede it in the same FIFO. -/
@[irreducible] def writtenB : Queue.ManagedRef :=
  found (afterBWorker.pending[2]?.bind managedReference) (by decide +kernel)

theorem after_B_issue_tags :
    afterBWorker.pending[1]? = some (.managed incomingA 7 1) ∧
      afterBWorker.pending[2]? = some (.managed writtenB 7 2) ∧
      afterBWorker.nextStore = 3 := by
  decide +kernel

/-- The scanner's typed instruction origins and the actual prefix FIFOs retain
the same complete descriptors. Neither comparison identifies writers by value. -/
theorem retained_descriptors :
    incomingA = PublicationCoverage.referenceA ∧ writtenB = PublicationCoverage.referenceB := by
  decide +kernel

theorem new_B_issued :
    IssuedAt .sharedCell 0 (.managed writtenB 7 2) 1 initial actions result := by
  rw [retained_descriptors.2]
  unfold initial actions result
  exact issue_after_two (state := PublicationCoverage.initial)
    (before := (PublicationCoverage.atCut 2).1) (actions := PublicationCoverage.actions)
    (result := PublicationCoverage.result) (index := 1)
    PublicationCoverage.ownB_issued (PublicationCoverage.prefix_exact 2)

theorem actual_targets_are_different_cells :
    incomingA.cell.address = 65536 ∧ writtenB.cell.address = 458752 ∧
      incomingA.handle.cell ≠ writtenB.handle.cell := by
  decide +kernel

theorem B_current_at_issue_successor :
    Queue.Current (atCut 2).1.world afterBWorker.resources writtenB :=
  queued_current (schedule_wellFormed execution.valid (prefix_scheduled 2))
    afterB_live (List.mem_of_getElem? after_B_issue_tags.2.1)

def incomingASelection : Queue.SelectionOrder.ManagedSelection
    afterBWorker.storeCursor incomingA.cell.address ⟨1, 7⟩ :=
  ⟨incomingA, 1, after_B_issue_tags.1, rfl, by decide +kernel⟩

/-- These independent literal positions include both blocked LOCK attempts and
the ordinary drain. A's publication is local five; B's is local seven. -/
theorem actual_buffered_publications :
    result.2[5]? = some (.drained 0 (.managed incomingA 7 1)) ∧
      result.2[7]? = some (.drained 0 (.managed writtenB 7 2)) := by
  decide +kernel

/-- Actual publication enumeration retains the peer B drain, A and B drains,
and both later RMWs. This is a publication list, with no graph row assigned to
the incoming A instruction that is absent from this suffix. -/
theorem actual_later_publication_ranks :
    (C23Projection.writes 61 result.2).map (fun stamp => stamp.position + 1) =
      [66, 67, 69, 70, 71] := by
  unfold result
  rw [PublicationCoverage.observations_exact]
  rfl

private theorem selected_view {state before : OS.TSO64.State}
    {actions : List Action} {result : OS.TSO64.State × List Observation}
    {profile : Profile} {cut tid offset : Nat} {worker : Worker}
    {target : Queue.ManagedRef} {incoming : Writers}
    {origin : StoreBuffer.Mixed.QWordOrigin}
    (prefixRun : schedule state (actions.take cut) profile =
      .ok (before, result.2.take cut))
    (live : before.workers[tid]? = some worker)
    (selection : Queue.SelectionOrder.ManagedSelection worker.storeCursor
      target.cell.address origin)
    (publication : PendingPublication state actions result profile cut tid
      selection.reference origin.value selection.occurrence)
    (cell : selection.reference.handle.cell = target.handle.cell) :
    Nonempty (ExecutionViews.At state actions result profile cut tid target offset incoming
      (publication.rank offset)) := by
  let snapshot : ExecutionViews.Cut state actions result profile cut tid :=
    ⟨before, worker, prefixRun, live⟩
  refine ⟨⟨snapshot, ?_⟩⟩
  exact ExecutionViews.Source.pending (snapshot := snapshot) selection publication cell

/-- The incoming A writer is actually selected immediately after the new B
issue. Its rank comes from its unique later drain, with no new-run A issue. -/
theorem incoming_A_view_after_B_issue :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 2 0 incomingA 61 empty 67) := by
  obtain ⟨publication⟩ := PendingViews.selected_publication scheduled execution.sequenced
    (prefix_exact 2) execution.quiescent afterB_live incomingASelection
  have observed : result.2[5]? =
      some (.drained 0 (.managed incomingASelection.reference 7 incomingASelection.occurrence)) :=
    actual_buffered_publications.1
  have position : publication.index = 5 :=
    (publication.unique 5 incomingASelection.reference 7 observed).1.symm
  have rank : publication.rank 61 = 67 := by
    change 61 + publication.index + 1 = 67
    omega
  have view := selected_view (target := incomingA) (offset := 61) (incoming := empty)
    (prefix_exact 2) afterB_live incomingASelection publication rfl
  simpa only [rank] using view

def BStamp : Stamp := ⟨68, .buffered 0 writtenB 7 2⟩

theorem new_B_actual_publication :
    Nonempty (WriteAt initial actions result .sharedCell 61 BStamp) := by
  have queued : Queued (atCut 2).1 0 (.managed writtenB 7 2) :=
    ⟨afterBWorker, afterB_live, List.mem_of_getElem? after_B_issue_tags.2.1⟩
  obtain ⟨publication⟩ := pending_managed_publication scheduled execution.sequenced
    (prefix_exact 2) execution.quiescent queued
  have position : publication.index = 7 :=
    (publication.unique 7 writtenB 7 actual_buffered_publications.2).1.symm
  have stamp : publication.stamp 61 = BStamp := by
    change (⟨61 + publication.index, .buffered 0 writtenB 7 2⟩ : Stamp) = BStamp
    rw [position]
    rfl
  obtain ⟨actual⟩ := publication.writeAt 61
  rw [stamp] at actual
  exact ⟨actual⟩

/-- The new B issue has an actual matching publication at local seven, hence
position 68 and rank 69 at offset 61. Its issue is local one, not local seven. -/
theorem new_B_instruction_write :
    ∃ actual : InstructionWriteAt initial actions result .sharedCell 61 1 BStamp,
      actual.publication.index = 7 := by
  obtain ⟨publication⟩ := new_B_actual_publication
  have position := publication.position
  change 68 = 61 + publication.index at position
  have index : publication.index = 7 := by omega
  exact ⟨InstructionWriteAt.buffered new_B_issued publication, index⟩

/-- No relation between target and B is assumed. This is the production
universal numerical coverage theorem instantiated on this nonempty boundary. -/
theorem every_target_covered_after_new_B {target : Queue.ManagedRef} {incoming : Writers}
    {value : Nat} (prior : PublishedOrder.Prior 61 incoming)
    (view : ExecutionViews.At initial actions result .sharedCell 2 0 target 61 incoming value) :
    value ≤ 69 := by
  obtain ⟨actual, _publicationIndex⟩ := new_B_instruction_write
  exact actual.covers_after execution prior view

/-- Positive evidence combines the incoming A's real full-tag pending source,
the later B's real instruction/publication origin, and the independent literal
ranks 67 and 69. The incoming A is expressly not a new-run instruction write. -/
theorem incoming_A_covered_by_later_B :
    Nonempty (ExecutionViews.At initial actions result .sharedCell 2 0 incomingA 61 empty 67) ∧
      (∃ actual : InstructionWriteAt initial actions result .sharedCell 61 1 BStamp,
        actual.publication.index = 7) ∧
      incomingA.handle.cell ≠ writtenB.handle.cell ∧
      67 ≤ 69 ∧
      (∀ index, ¬ IssuedAt .sharedCell 0 (.managed incomingA 7 1) index initial actions result) := by
  obtain ⟨view⟩ := incoming_A_view_after_B_issue
  exact ⟨⟨view⟩, new_B_instruction_write, actual_targets_are_different_cells.2.2,
    every_target_covered_after_new_B (PublishedOrder.prior_empty 61) view,
    incoming_A_has_no_new_issue⟩

end EDSL.Tests.PublicationCoverageBoundary

#print axioms EDSL.Tests.PublicationCoverageBoundary.execution
#print axioms EDSL.Tests.PublicationCoverageBoundary.incoming_mixed_fifo
#print axioms EDSL.Tests.PublicationCoverageBoundary.incoming_A_current
#print axioms EDSL.Tests.PublicationCoverageBoundary.incoming_A_has_no_new_issue
#print axioms EDSL.Tests.PublicationCoverageBoundary.new_B_issued
#print axioms EDSL.Tests.PublicationCoverageBoundary.actual_later_publication_ranks
#print axioms EDSL.Tests.PublicationCoverageBoundary.incoming_A_view_after_B_issue
#print axioms EDSL.Tests.PublicationCoverageBoundary.new_B_instruction_write
#print axioms EDSL.Tests.PublicationCoverageBoundary.every_target_covered_after_new_B
#print axioms EDSL.Tests.PublicationCoverageBoundary.incoming_A_covered_by_later_B
#audit_edsl
