/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.AccessSourceRanks

/-!
Actual RMW source boundaries: a peer action separates a source publication from
the RMW, and a first RMW reads the initialized boundary. Both are production
annotated executions with checked resources. Peer pending stores are allowed
at an own-empty RMW. These finite abstract checks establish no native execution,
fairness, C23 legality, source-order mapping or new compiler-corpus coverage.
-/

set_option autoImplicit false

namespace EDSL.Tests.RMWSourceRanks
open X86 OS.TSO64 OS.TSO64.C23Projection AtomicTrace

private def checked {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : α := attempt.toOption.get accepted

private theorem checked_ok {ε α : Type} (attempt : Except ε α)
    (accepted : attempt.toOption.isSome = true) : attempt = .ok (checked attempt accepted) := by
  cases attempt with
  | error fault => cases accepted
  | ok value => rfl

private theorem known_source {initial : OS.TSO64.State} {actions : List Action}
    {result : OS.TSO64.State × List Observation} {profile : Profile}
    {event : AtomicTrace.Event} {index offset rank : Nat}
    {changed : OS.Atomics64.FetchAddEvent} {source : WriterId}
    (execution : ExecutionViews.Execution initial actions result profile)
    (actual : EventAt profile event index initial actions result offset PublishedHistory.empty)
    (rmw : event.access = .rmw changed source)
    (known : WriterRank initial actions result profile offset changed.cell source rank) :
    ∃ target, AccessTarget event target ∧
      Nonempty (ExecutionViews.At initial actions result profile index event.tid target
        offset PublishedHistory.empty rank) ∧
      WriterRank initial actions result profile offset changed.cell
        (.rmw event.position) (event.position + 1) ∧ rank < event.position + 1 := by
  obtain ⟨target, actualRank, related, view, ranked, own, earlier⟩ :=
    actual.rmw_view_rank execution rmw
  have same := WriterRank.unique execution.success execution.sequenced ranked known
  subst actualRank
  exact ⟨target, related, view, own, earlier⟩

namespace Gap

def actions : List Action :=
  [.issue 0 false, .drain 0, .issue 1 false, .issue 0 true, .drain 1]

def attempt : Except Fault AtomicTrace.Result :=
  AtomicTrace.scan MixedWriteOrder.initial actions .sharedCell 61

def scanned : AtomicTrace.Result := checked attempt (by decide +kernel)

theorem scanned_actual :
    AtomicTrace.scan MixedWriteOrder.initial actions .sharedCell 61 = .ok scanned := checked_ok _ _

theorem scheduled : schedule MixedWriteOrder.initial actions .sharedCell = .ok scanned.execution :=
  scan_scheduled scanned_actual

theorem execution : ExecutionViews.Execution MixedWriteOrder.initial actions scanned.execution
    .sharedCell :=
  ⟨scheduled, AccessSourceRanks.RMW.initial_valid, MixedWriteOrder.initial_sequenced,
    AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)⟩

def changed : OS.Atomics64.FetchAddEvent :=
  ((scanned.events[2]?).bind fun event => match event.access with
    | .rmw actual _ => some actual
    | _ => none).get (by decide +kernel)

/-- The peer store remains pending during the RMW and publishes afterwards.
Its later write does not replace the RMW's source in the earlier prefix. -/
theorem execution_contract :
    scanned.events.map TSO64AtomicTrace.eventSummary =
      [(61, 0, 1, ⟨0⟩, 7, none, some (.store 0 0)),
        (63, 1, 1, ⟨0⟩, 0, none, some (.store 1 0)),
        (64, 0, 2, ⟨0⟩, 14, some (.store 0 0), some (.rmw 64))] ∧
      scanned.events[2]? = some ⟨64, 0, .rmw changed (.store 0 0)⟩ ∧
      changed.arithmetic.event.before = 7 ∧ changed.arithmetic.delta = 7 ∧
      changed.arithmetic.event.after = 14 ∧
      loadQWord (published scanned.state.world) 65536 = .ok 0 := by
  decide +kernel

theorem actual : EventAt .sharedCell ⟨64, 0, .rmw changed (.store 0 0)⟩ 3
    MixedWriteOrder.initial actions scanned.execution 61 PublishedHistory.empty :=
  AccessSourceRanks.scanned_at_position execution.valid execution.sequenced scanned_actual
    (List.mem_of_getElem? execution_contract.2.1) rfl

/-- Prefix metadata is computed from the real full observation list, then
authenticated by the published-prefix theorem. No issue is inferred from a word. -/
theorem source_rank : WriterRank MixedWriteOrder.initial actions scanned.execution .sharedCell
    61 changed.cell (.store 0 0) 63 := by
  obtain ⟨before, prefixRun, _suffix⟩ := ScheduleTrace.cut scheduled 3
  have ranked := publishedSource_prefix_rank (offset := 61) scheduled prefixRun changed.cell
  dsimp only [AtomicTrace.Result.execution] at ranked
  have metadata :
      publishedSource (PublishedHistory.after 61 (scanned.observations.take 3)
        PublishedHistory.empty) changed.cell = .store 0 0 ∧
      PublishedOrder.view (PublishedHistory.after 61 (scanned.observations.take 3)
        PublishedHistory.empty) changed.cell = 63 := by decide +kernel
  rw [metadata.1, metadata.2] at ranked
  exact ranked

/-- There is a genuine rank gap: source63, own65. Adjacency would be false. -/
theorem gapped_source_and_own :
    ∃ target, AccessTarget ⟨64, 0, .rmw changed (.store 0 0)⟩ target ∧
      Nonempty (ExecutionViews.At MixedWriteOrder.initial actions scanned.execution .sharedCell
        3 0 target 61 PublishedHistory.empty 63) ∧
      WriterRank MixedWriteOrder.initial actions scanned.execution .sharedCell 61 changed.cell
        (.rmw 64) 65 ∧ 63 < 65 :=
  known_source execution actual rfl source_rank

end Gap

namespace Initial

def initialAttempt : Except Fault OS.TSO64.State :=
  TSO64SharedCells.start 0x37c10f48f0378948 0x37c10f48f0378948 9 7 0 3 0

def initial : OS.TSO64.State := checked initialAttempt (by decide +kernel)

theorem initial_actual : initialAttempt = .ok initial := checked_ok _ _

def actions : List Action := [.issue 0 false]

def attempt : Except Fault AtomicTrace.Result := AtomicTrace.scan initial actions .sharedCell 81

def scanned : AtomicTrace.Result := checked attempt (by decide +kernel)

theorem scanned_actual : AtomicTrace.scan initial actions .sharedCell 81 = .ok scanned :=
  checked_ok _ _

theorem scheduled : schedule initial actions .sharedCell = .ok scanned.execution :=
  scan_scheduled scanned_actual

theorem execution : ExecutionViews.Execution initial actions scanned.execution .sharedCell :=
  ⟨scheduled, AccessSourceRanks.shared_start_valid initial_actual,
    quiescent_sequenced (AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)),
    AccessSourceRanks.quiescent_of_empty_projection (by decide +kernel)⟩

def changed : OS.Atomics64.FetchAddEvent :=
  ((scanned.events[0]?).bind fun event => match event.access with
    | .rmw actual _ => some actual
    | _ => none).get (by decide +kernel)

/-- The first RMW reads initialized nine, writes sixteen and returns nine in
RSI. An absent prior writer is rank zero, not a fabricated pre-run publication. -/
theorem execution_contract :
    scanned.events[0]? = some ⟨81, 0, .rmw changed (.initial changed.cell)⟩ ∧
      changed.arithmetic.event.before = 9 ∧ changed.arithmetic.delta = 7 ∧
      changed.arithmetic.event.after = 16 ∧
      loadQWord (published scanned.state.world) 65536 = .ok 16 ∧
      (scanned.state.workers[0]?).map (fun worker => worker.context.registers .rsi) = some 9 := by
  decide +kernel

theorem actual : EventAt .sharedCell ⟨81, 0, .rmw changed (.initial changed.cell)⟩ 0
    initial actions scanned.execution 81 PublishedHistory.empty :=
  AccessSourceRanks.scanned_at_position execution.valid execution.sequenced scanned_actual
    (List.mem_of_getElem? execution_contract.1) rfl

theorem initial_source_and_own :
    ∃ target, AccessTarget ⟨81, 0, .rmw changed (.initial changed.cell)⟩ target ∧
      Nonempty (ExecutionViews.At initial actions scanned.execution .sharedCell 0 0 target
        81 PublishedHistory.empty 0) ∧
      WriterRank initial actions scanned.execution .sharedCell 81 changed.cell (.rmw 81) 82 ∧
      0 < 82 :=
  known_source execution actual rfl WriterRank.initial

end Initial
end EDSL.Tests.RMWSourceRanks

#print axioms EDSL.Tests.RMWSourceRanks.Gap.gapped_source_and_own
#print axioms EDSL.Tests.RMWSourceRanks.Initial.initial_source_and_own
#audit_edsl
