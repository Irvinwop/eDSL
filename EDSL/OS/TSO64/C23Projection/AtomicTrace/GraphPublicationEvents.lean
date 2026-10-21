/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.GraphCapture
import EDSL.OS.TSO64.StoreHistory.PendingPublication

/-!
Both directions of actual writing-event/publication coverage before graph
construction. A store event supplies its real issue and the final quiescent
endpoint forces its exact pending entry to drain. Conversely, initial empty
queues exclude incoming entries when recovering an issue from a publication.
An RMW issues and publishes at the same actual action.

Every witness retains the full original reference, word, occurrence or RMW
cause. Positions count all scheduler actions from the arbitrary scan offset.
RMW sources use the actual publication map before that action, including every
silent prefix observation. Initial occurrence counters need not be zero.
These finite execution facts choose no interface orders and establish neither
source/native preservation, full C23 legality, fairness nor builder totality.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph
open X86 PublishedHistory StoreHistory

/-- Recover the complete real store issue from an actual store event. This
direction does not need a publication, a table or an empty initial boundary. -/
theorem store_issued_at {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset occurrence : Nat} {writers : PublishedHistory.Writers}
    {reference : Queue.ManagedRef} {value : Word}
    (actual : EventAt profile event index initial actions result offset writers)
    (stored : event.access = .store reference value occurrence) :
    IssuedAt profile event.tid (.managed reference value occurrence)
      index initial actions result := by
  induction actual with
  | head stepped following origin =>
      cases origin with
      | load => cases stored
      | store issued =>
          cases stored
          exact .head stepped following issued
      | rmw => cases stored
  | later stepped following actual ih => exact .later stepped following ih

/-- Inverse store bridge: an independent actual instruction issue supplies an
event at that same original action, with the complete admitted queue entry. -/
theorem store_event_at {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {index offset tid occurrence : Nat} {writers : PublishedHistory.Writers}
    {reference : Queue.ManagedRef} {value : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      index initial actions result) :
    EventAt profile (⟨offset + index, tid, .store reference value occurrence⟩ : Event)
      index initial actions result offset writers := by
  obtain ⟨before, action, first, prefixRun, selected, executed, origin⟩ := issued.prestate
  exact EventAt.of_prestate issued.forget.scheduled prefixRun selected executed (.store origin)

/-- The exact entry is pending immediately after its real issue. The cut
counts scheduler actions, including preceding silent actions and drains. -/
theorem issued_pending_at {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid index : Nat}
    {entry : Pending} (issued : IssuedAt profile tid entry index initial actions result) :
    ∃ after,
      schedule initial (actions.take (index + 1)) profile =
        .ok (after, result.2.take (index + 1)) ∧ Queued after tid entry := by
  induction issued with
  | head stepped _following actual =>
      refine ⟨_, ?_, actual.queued⟩
      simp only [List.take_succ_cons, List.take_zero, schedule, stepped, ok_bind, pure_ok]
  | later stepped _following actual ih =>
      obtain ⟨after, prefixRun, pending⟩ := ih
      refine ⟨after, ?_, pending⟩
      simp only [List.take_succ_cons, schedule, stepped, ok_bind, prefixRun, pure_ok]

/-- Final quiescence constructs the unique actual publication of an issued
managed entry from its real pending cut. Neither a future drain nor a desired
publication position is a premise. Initial counters may be arbitrary. -/
theorem issued_pending_publication {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {tid index occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
    (issued : IssuedAt profile tid (.managed reference value occurrence)
      index initial actions result)
    (sequenced : Sequenced initial) (quiescent : Quiescent result.1) :
    Nonempty (PendingPublication initial actions result profile (index + 1)
      tid reference value occurrence) := by
  obtain ⟨after, prefixRun, pending⟩ := issued_pending_at issued
  exact pending_managed_publication issued.forget.scheduled sequenced prefixRun quiescent pending

/-- An actual RMW event has its full instruction/publication witness at its
own action. This extracts the actual step rather than matching equal words. -/
theorem rmw_instruction_at {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {event : Event}
    {index offset : Nat} {writers : PublishedHistory.Writers}
    {changed : Atomics64.FetchAddEvent} {source : WriterId}
    (actual : EventAt profile event index initial actions result offset writers)
    (modified : event.access = .rmw changed source) :
    Nonempty (InstructionWriteAt initial actions result profile offset index
      ⟨event.position, .rmw event.tid changed⟩) := by
  obtain ⟨before, action, first, prefixRun, selected, observed, stepped, origin⟩ := actual.prestate
  have written : writeOf first.2 = some (.rmw event.tid changed) := by
    cases origin with
    | load => cases modified
    | store => cases modified
    | rmw observation _origin =>
        cases modified
        simp only [observation, writeOf]
  exact ⟨⟨⟨index, first.2, before, action, first.1, actual.position,
    observed, prefixRun, selected, stepped, written⟩, rfl⟩⟩

/-- Inverse RMW bridge: its actual publication supplies an access at exactly
that action. The source annotation is computed from the real prefix, before
the RMW's own publication and with the original offset and initial map. -/
theorem rmw_event_at {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile}
    {offset position tid : Nat} {writers : PublishedHistory.Writers}
    {changed : Atomics64.FetchAddEvent}
    (success : schedule initial actions profile = .ok result)
    (published : WriteAt initial actions result profile offset ⟨position, .rmw tid changed⟩) :
    EventAt profile (⟨offset + published.index, tid,
      .rmw changed (publishedSource
        (PublishedHistory.after offset (result.2.take published.index) writers) changed.cell)⟩ : Event)
      published.index initial actions result offset writers := by
  obtain ⟨before, action, next, prefixRun, selected, stepped⟩ :=
    ScheduleTrace.observation_at success published.rmw_observed
  exact EventAt.of_prestate success prefixRun selected stepped (.rmw rfl (step_origin stepped))

namespace Captured
variable {initial : State} {actions : List Action} {profile : Profile}
  {offset : Nat} {run : Result} {initials : List Initials.Entry}

/-- A real writing event supplies its complete matching publication, retained
in the complete actual write enumeration, and its actual instruction witness.
The store case uses the real post-issue cut and actual final quiescence. -/
theorem event_instruction_publication
    (captured : Captured initial actions profile offset run initials)
    {event : Event} {index : Nat}
    (actual : EventAt profile event index initial actions run.execution offset empty)
    (writing : event.writer.isSome = true) :
    ∃ stamp, Publication event stamp ∧ stamp ∈ writes offset run.observations ∧
      Nonempty (InstructionWriteAt initial actions run.execution profile offset index stamp) := by
  cases access : event.access with
  | load reference value source =>
      simp only [Event.writer, access, Option.isSome_none, Bool.false_eq_true] at writing
  | store reference value occurrence =>
      have issued := store_issued_at actual access
      obtain ⟨publication⟩ :=
        issued_pending_publication issued captured.sequenced captured.quiescent
      obtain ⟨published⟩ := publication.writeAt offset
      refine ⟨publication.stamp offset, ?_, publication.stamp_mem_writes offset,
        ⟨InstructionWriteAt.buffered issued published⟩⟩
      rw [Publication, access]
      refine ⟨rfl, ?_⟩
      change event.position < offset + publication.index
      have eventPosition := actual.position
      have future := publication.future
      omega
  | rmw changed source =>
      obtain ⟨instruction⟩ := rmw_instruction_at actual access
      refine ⟨⟨event.position, .rmw event.tid changed⟩, ?_,
        writeAt_mem_writes instruction.publication, ⟨instruction⟩⟩
      rw [Publication, access]
      exact ⟨rfl, rfl⟩

/-- Every full actual publication recovers its real writing instruction and
its event at the exact action. Empty initial queues rule out invented issues
for incoming entries; RMW annotations use the actual pre-action writer map. -/
theorem publication_instruction_event
    (captured : Captured initial actions profile offset run initials)
    {stamp : Stamp} (published : WriteAt initial actions run.execution profile offset stamp) :
    ∃ event index, EventAt profile event index initial actions run.execution offset empty ∧
      Publication event stamp ∧
      Nonempty (InstructionWriteAt initial actions run.execution profile offset index stamp) := by
  cases stamp with
  | mk position cause =>
      cases cause with
      | buffered tid reference value occurrence =>
          obtain ⟨index, earlier, issued, _unique⟩ :=
            buffered_issue_unique captured.initialEmpty captured.certificate.scheduled published
          refine ⟨⟨offset + index, tid, .store reference value occurrence⟩, index,
            store_event_at issued, ?_, ⟨InstructionWriteAt.buffered issued published⟩⟩
          refine ⟨rfl, ?_⟩
          have publicationPosition : position = offset + published.index := published.position
          change offset + index < position
          omega
      | rmw tid changed =>
          refine ⟨⟨offset + published.index, tid, .rmw changed (publishedSource
            (PublishedHistory.after offset (run.observations.take published.index) empty)
              changed.cell)⟩, published.index,
            rmw_event_at captured.certificate.scheduled published, ?_,
            ⟨InstructionWriteAt.rmw published⟩⟩
          exact ⟨rfl, published.position⟩

/-- The `InputsReady.writes` obligation for raw captured run inputs. Each
writing slot retains the full matching actual publication, with no table or
rank oracle and no restriction on subsequently declared interface orders. -/
theorem event_publication
    (captured : Captured initial actions profile offset run initials)
    (slot : Fin (runInputs initials run offset).events.length)
    (writing : (runInputs initials run offset).events[slot.val].writer.isSome = true) :
    ∃ publication : Fin (runInputs initials run offset).writes.length,
      Publication (runInputs initials run offset).events[slot.val]
        (runInputs initials run offset).writes[publication.val] := by
  have slotBound : slot.val < run.events.length := by
    simpa only [runInputs] using slot.isLt
  change run.events[slot.val].writer.isSome = true at writing
  change ∃ publication : Fin (writes offset run.observations).length,
    Publication run.events[slot.val] (writes offset run.observations)[publication.val]
  obtain ⟨index, actual⟩ := captured.event_origin slot
  obtain ⟨stamp, matched, member, _instruction⟩ :=
    captured.event_instruction_publication actual writing
  obtain ⟨publicationIndex, selected⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨bound, equal⟩ := List.getElem_of_getElem? selected
  refine ⟨⟨publicationIndex, bound⟩, ?_⟩
  change Publication run.events[slot.val] (writes offset run.observations)[publicationIndex]
  rw [equal]
  exact matched

/-- The `InputsReady.complete` obligation for raw captured run inputs. No
computed publication is omitted: the independent issue/publication witnesses
give a real access and the scan certificate supplies its retained event slot. -/
theorem publication_event
    (captured : Captured initial actions profile offset run initials)
    (publication : Fin (runInputs initials run offset).writes.length) :
    ∃ slot : Fin (runInputs initials run offset).events.length,
      Publication (runInputs initials run offset).events[slot.val]
        (runInputs initials run offset).writes[publication.val] := by
  have publicationBound : publication.val < (writes offset run.observations).length := by
    simpa only [runInputs] using publication.isLt
  change ∃ slot : Fin run.events.length,
    Publication run.events[slot.val] (writes offset run.observations)[publication.val]
  have member : (writes offset run.observations)[publication.val] ∈
      writes offset run.observations := List.getElem_mem publication.isLt
  obtain ⟨published⟩ := captured.publication_origin member
  obtain ⟨event, index, actual, matched, _instruction⟩ :=
    captured.publication_instruction_event published
  have retained : event ∈ run.events :=
    (captured.certificate.events event).mpr ⟨index, actual⟩
  obtain ⟨eventIndex, selected⟩ := List.mem_iff_getElem?.mp retained
  obtain ⟨bound, equal⟩ := List.getElem_of_getElem? selected
  refine ⟨⟨eventIndex, bound⟩, ?_⟩
  change Publication run.events[eventIndex] (writes offset run.observations)[publication.val]
  rw [equal]
  exact matched

end Captured
end EDSL.OS.TSO64.C23Projection.AtomicTrace.Graph

#audit_edsl
