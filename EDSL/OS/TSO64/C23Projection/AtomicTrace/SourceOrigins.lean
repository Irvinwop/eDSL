/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.C23Projection.AtomicTrace.Capture
import EDSL.OS.TSO64.C23Projection.AtomicTrace.WriterOrigins

set_option autoImplicit false

namespace EDSL.OS.TSO64.C23Projection.AtomicTrace
open X86

/-- Resolve the computed key at a real prestate. Published keys retain their
latest actual publication (or absence at the initialized boundary). Forwarded
keys retain both the exact newest queue entry and its actual earlier issue.
No identity is recovered by searching for an equal word. -/
inductive ResolvedSource (initial : State) (priorActions : List Action)
    (execution : State × List Observation) (profile : Profile) (event : Event) : Prop where
  | nonread (absent : event.source = none) :
      ResolvedSource initial priorActions execution profile event
  | published {source : WriterId}
      (selected : event.source = some source)
      (origin : WriterOrigin initial priorActions execution profile 0 event.object source) :
      ResolvedSource initial priorActions execution profile event
  | forwarded {worker : Worker} {reference writer : Queue.ManagedRef}
      {value : Word} {occurrence : Nat} {selector : StoreBuffer.Mixed.QWordOrigin}
      (access : event.access = .load reference value (.store event.tid occurrence))
      (live : execution.1.workers[event.tid]? = some worker)
      (newest : StoreBuffer.Mixed.newestQWord (payload worker.pending)
        reference.cell.address = some selector)
      (entry : worker.pending[selector.index]? = some (.managed writer value occurrence))
      (issued : ∃ index, index < priorActions.length ∧
        StoreHistory.IssuedAt profile event.tid (.managed writer value occurrence)
          index initial priorActions execution) :
      ResolvedSource initial priorActions execution profile event

/-- Access and source facts at the actual original action position. This
record is a proof contract; the executable scanner never consumes it. -/
inductive OriginAt (initial : State) (actions : List Action)
    (execution : State × List Observation) (profile : Profile) (event : Event) : Prop where
  | intro (index : Nat) (before : State) (action : Action) (first : State × Observation)
      (position : event.position = index)
      (bound : index < actions.length)
      (prefixRun : schedule initial (actions.take index) profile =
        .ok (before, execution.2.take index))
      (actionAt : actions[index]? = some action)
      (observationAt : execution.2[index]? = some first.2)
      (stepped : step before action profile = .ok first)
      (access : AtomicStep before action first profile index
        (PublishedHistory.after 0 (execution.2.take index) PublishedHistory.empty) event)
      (source : ResolvedSource initial (actions.take index)
        (before, execution.2.take index) profile event) :
      OriginAt initial actions execution profile event

/-- Empty initial FIFOs exclude arbitrary pre-run buffered identities. Every
source is resolved in the original successful prefix, including silent actions.
The access witness separately retains loaded values and actual authorization. -/
theorem EventAt.source_origin {initial : State} {actions : List Action}
    {execution : State × List Observation} {profile : Profile} {event : Event} {index : Nat}
    (empty : Quiescent initial)
    (actual : EventAt profile event index initial actions execution 0 PublishedHistory.empty) :
    OriginAt initial actions execution profile event := by
  obtain ⟨before, action, first, prefixRun, actionAt, observationAt, stepped, access⟩ :=
    actual.prestate
  have realAccess : AtomicStep before action first profile index
      (PublishedHistory.after 0 (execution.2.take index) PublishedHistory.empty) event := by
    simpa only [Nat.zero_add] using access
  refine ⟨index, before, action, first, by simpa only [Nat.zero_add] using actual.position,
    actual.bound, prefixRun, actionAt, observationAt, stepped, realAccess, ?_⟩
  cases realAccess with
  | store issued => exact .nonread rfl
  | rmw observed origin =>
      exact .published rfl (publishedSource_origin empty prefixRun _)
  | load origin live read =>
      cases read with
      | published absent read =>
          exact .published rfl (publishedSource_origin empty prefixRun _)
      | forwarded selector writer occurrence newest entry payload address current below =>
          exact .forwarded rfl live newest entry
            (forwardedSource_origin empty prefixRun live entry)

/-- Successful computed scans expose all real source origins without a caller
history, classification oracle or assumptions about intermediate states. -/
theorem scan_source_origins {initial : State} {actions : List Action} {profile : Profile}
    {result : Result} {event : Event}
    (valid : WellFormed initial profile) (empty : Quiescent initial)
    (success : scan initial actions profile 0 PublishedHistory.empty = .ok result)
    (member : event ∈ result.events) :
    OriginAt initial actions result.execution profile event := by
  obtain ⟨index, actual⟩ := scan_sound valid (quiescent_sequenced empty) success member
  exact actual.source_origin empty

end EDSL.OS.TSO64.C23Projection.AtomicTrace
