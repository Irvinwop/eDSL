/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Model

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86 PublishedHistory StoreHistory

/-- An actual published source identity. The initial case retains a no-write
boundary; buffered sources name original issues and RMWs name real action
positions. This identity contract alone does not assert a loaded value. -/
inductive WriterOrigin (initial : State) (actions : List Action)
    (result : State × List Observation) (profile : Profile) (offset : Nat)
    (target : Atomics64.CellId64) : WriterId → Prop where
  | initial (absent : after offset result.2 empty target = none) :
      WriterOrigin initial actions result profile offset target (.initial target)
  | buffered {position tid occurrence : Nat} {reference : Queue.ManagedRef} {value : Word}
      (latest : after offset result.2 empty target =
        some ⟨position, .buffered tid reference value occurrence⟩)
      (witness : WriteAt initial actions result profile offset
        ⟨position, .buffered tid reference value occurrence⟩)
      (cell : reference.handle.cell = target)
      (issued : ∃ index, index < witness.index ∧
        IssuedAt profile tid (.managed reference value occurrence) index initial actions result) :
      WriterOrigin initial actions result profile offset target (.store tid occurrence)
  | rmw {position tid : Nat} {event : Atomics64.FetchAddEvent}
      (latest : after offset result.2 empty target = some ⟨position, .rmw tid event⟩)
      (witness : WriteAt initial actions result profile offset ⟨position, .rmw tid event⟩)
      (cell : event.cell = target) :
      WriterOrigin initial actions result profile offset target (.rmw position)

/-- A computed latest-writer key resolves to a real execution origin. Empty
initial queues exclude pre-run buffered stores; equal values play no role. -/
theorem publishedSource_origin {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {offset : Nat}
    (boundary : Quiescent initial) (success : schedule initial actions profile = .ok result)
    (target : Atomics64.CellId64) :
    WriterOrigin initial actions result profile offset target
      (publishedSource (after offset result.2 empty) target) := by
  cases found : after offset result.2 empty target with
  | none =>
      simpa only [publishedSource, found] using
        (WriterOrigin.initial (initial := initial) (actions := actions) (profile := profile) found)
  | some stamp =>
      obtain ⟨witness, cell, _noLater⟩ := newest_write_at success found
      cases stamp with
      | mk position cause =>
          cases cause with
          | buffered tid reference value occurrence =>
              obtain ⟨index, before, actual, _unique⟩ := buffered_issue_unique boundary success witness
              simpa only [publishedSource, found] using
                (WriterOrigin.buffered found witness cell ⟨index, before, actual⟩)
          | rmw tid event =>
              simpa only [publishedSource, found] using (WriterOrigin.rmw found witness cell)

/-- A selected own-buffer entry resolves to an actual issue in the supplied
prefix. Its list index is a snapshot lookup; the persistent writer identity
uses its original thread and occurrence, even after earlier entries drain. -/
theorem forwardedSource_origin {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {tid pendingIndex occurrence : Nat}
    {worker : Worker} {reference : Queue.ManagedRef} {value : Word}
    (boundary : Quiescent initial) (success : schedule initial actions profile = .ok result)
    (live : result.1.workers[tid]? = some worker)
    (selected : worker.pending[pendingIndex]? = some (.managed reference value occurrence)) :
    ∃ issueIndex, issueIndex < actions.length ∧
      IssuedAt profile tid (.managed reference value occurrence) issueIndex initial actions result := by
  have queued : Queued result.1 tid (.managed reference value occurrence) :=
    ⟨worker, live, List.mem_of_getElem? selected⟩
  obtain ⟨index, actual⟩ := (schedule_pending_issued boundary success queued).indexed
  exact ⟨index, actual.bound, actual⟩

end EDSL.OS.TSO64.C23Projection.AtomicTrace
