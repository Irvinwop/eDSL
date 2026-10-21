/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.ExecutionViews.Model

/-!
Computable metadata for the existing actual-execution views. The supplied state
is inspected with the production newest-qword selector; no scheduler is run.
A selected managed entry is identified by its complete reference, value and
occurrence, and searched for in the complete observation stream, including
ordinary steps and returns. This is an offline query, not a future-drain oracle.

The data function alone checks neither execution nor resource authority. Its
connection to `At` requires an actual prefix of the fixed successful, initially
well-formed/sequenced, finally quiescent execution and a current target. Failure
on arbitrary metadata is unsupported input, not evidence of a program defect.
-/

set_option autoImplicit false

namespace EDSL.OS.TSO64.ExecutionViews
open X86 PublishedHistory StoreHistory

/-- Query the existing view from a prefix state and a complete observation
stream. The pending branch retains the production queue index and rejects
ordinary/missing entries or inconsistent address, value or persistent cell.
Different current handles for the same cell remain allowed. -/
def query (before : State) (observations : List Observation) (index tid : Nat)
    (target : Queue.ManagedRef) (offset : Nat) (incoming : Writers) : Option Nat := do
  let worker ← before.workers[tid]?
  match StoreBuffer.Mixed.newestQWord (Queue.payload worker.pending) target.cell.address with
  | none =>
    some (PublishedOrder.view (after offset (observations.take index) incoming) target.handle.cell)
  | some origin =>
    match worker.pending[origin.index]? with
    | some (.managed reference value occurrence) =>
      if reference.cell.address = target.cell.address ∧ value = origin.value ∧
          reference.handle.cell = target.handle.cell then
        (observations.findIdx? fun observation =>
          decide (observation = .drained tid (.managed reference value occurrence))).map
            (fun publication => offset + publication + 1)
      else none
    | _ => none

/-- Uniqueness of the actual publication fixes the search result. In particular
an earlier equal payload cannot supply a desired rank for this writer. -/
private theorem publication_findIdx {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index tid occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word}
    (publication : PendingPublication initial actions result profile index tid reference value occurrence) :
    result.2.findIdx? (fun observation =>
      decide (observation = .drained tid (.managed reference value occurrence))) =
        some publication.index := by
  apply List.findIdx?_eq_some_iff_getElem.mpr
  obtain ⟨bound, observed⟩ := List.getElem_of_getElem? publication.observed
  refine ⟨bound, ?_, ?_⟩
  · exact decide_eq_true observed
  · intro other earlier matched
    have exactEntry : result.2[other] = .drained tid (.managed reference value occurrence) :=
      of_decide_eq_true matched
    have actual : result.2[other]? = some (.drained tid (.managed reference value occurrence)) :=
      List.getElem?_eq_some_iff.mpr ⟨Nat.lt_trans earlier bound, exactEntry⟩
    have same := (publication.unique other reference value actual).1
    omega

/-- Every actual source witness computes its indexed value. The pending case
uses the witness's unique real drain, with no assumed publication position. -/
theorem Source.query_eq {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index tid offset value : Nat}
    {snapshot : Cut initial actions result profile index tid} {target : Queue.ManagedRef}
    {incoming : Writers} (source : Source snapshot target offset incoming value) :
    query snapshot.state result.2 index tid target offset incoming = some value := by
  cases source with
  | published absent =>
    have missing : StoreBuffer.Mixed.newestQWord (Queue.payload snapshot.worker.pending)
        target.cell.address = none := absent
    simp [query, snapshot.live, missing]
  | @pending origin selection publication cell =>
    have newest : StoreBuffer.Mixed.newestQWord (Queue.payload snapshot.worker.pending)
        target.cell.address = some origin := selection.newest
    have selected : snapshot.worker.pending[origin.index]? =
        some (.managed selection.reference origin.value selection.occurrence) := selection.selected
    simp [query, snapshot.live, newest, selected, selection.address, cell,
      publication_findIdx publication, PendingPublication.rank, PendingPublication.stamp]

/-- The query accepts the actual cut and complete observations of any `At`
witness, independently of the proof witnesses used to construct that view. -/
theorem At.query_eq {initial : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index tid offset value : Nat}
    {target : Queue.ManagedRef} {incoming : Writers}
    (view : At initial actions result profile index tid target offset incoming value) :
    query view.snapshot.state result.2 index tid target offset incoming = some value :=
  view.source.query_eq

/-- A successful query at an actual prefix denotes an actual view in the
current-target domain. Existence is obtained from the full execution; the
independently obtained cuts are aligned by `Cut.same`. Incoming writer metadata
is arbitrary here; its `Prior` premise is needed separately for monotonicity. -/
theorem query_sound {initial before : State} {actions : List Action}
    {result : State × List Observation} {profile : Profile} {index tid offset value : Nat}
    {worker : Worker} {resources : Resources} {target : Queue.ManagedRef} {incoming : Writers}
    (execution : Execution initial actions result profile)
    (live : initial.workers[tid]? = some worker)
    (prefixRun : schedule initial (actions.take index) profile = .ok (before, result.2.take index))
    (current : Queue.Current initial.world resources target)
    (answered : query before result.2 index tid target offset incoming = some value) :
    Nonempty (At initial actions result profile index tid target offset incoming value) := by
  obtain ⟨actualValue, ⟨view⟩⟩ := exists_at execution live index current offset incoming
  obtain ⟨present, presentLive⟩ := schedule_worker_present prefixRun live
  let snapshot : Cut initial actions result profile index tid :=
    ⟨before, present, prefixRun, presentLive⟩
  have aligned : before = view.snapshot.state := (snapshot.same view.snapshot).1
  have correct : query before result.2 index tid target offset incoming = some actualValue := by
    rw [aligned]
    exact view.query_eq
  have same : actualValue = value := Option.some.inj (correct.symm.trans answered)
  subst value
  exact ⟨view⟩

end EDSL.OS.TSO64.ExecutionViews

#audit_edsl
