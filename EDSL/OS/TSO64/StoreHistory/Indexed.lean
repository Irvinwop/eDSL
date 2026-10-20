/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.StoreHistory.Counter

set_option autoImplicit false

namespace EDSL.OS.TSO64.StoreHistory
open X86

/-- A real issue at its exact action position. Positions count every action,
including blocked attempts and drains, rather than just retired instructions.
The selected step and suffix are the existing executable scheduler. -/
inductive IssuedAt (profile : Profile) (tid : Nat) (entry : Pending) :
    Nat → State → List Action → (State × List Observation) → Prop where
  | head {state : State} {action : Action} {rest : List Action}
      {first : State × Observation} {tail : State × List Observation}
      (stepped : step state action profile = .ok first)
      (following : schedule first.1 rest profile = .ok tail)
      (issued : Issued state action first profile tid entry) :
      IssuedAt profile tid entry 0 state (action :: rest) (tail.1, first.2 :: tail.2)
  | later {state : State} {action : Action} {rest : List Action}
      {first : State × Observation} {tail : State × List Observation} {index : Nat}
      (stepped : step state action profile = .ok first)
      (following : schedule first.1 rest profile = .ok tail)
      (issued : IssuedAt profile tid entry index first.1 rest tail) :
      IssuedAt profile tid entry (index + 1) state (action :: rest) (tail.1, first.2 :: tail.2)

theorem IssuedAt.forget {profile : Profile} {tid index : Nat} {entry : Pending}
    {state : State} {actions : List Action} {result : State × List Observation}
    (issued : IssuedAt profile tid entry index state actions result) :
    IssuedIn profile tid entry state actions result := by
  induction issued with
  | head stepped following actual => exact .head stepped following actual
  | later stepped following actual ih => exact .later stepped following ih

/-- Old existential issue histories gain an exact action index without any
extra execution or numerical assumption. -/
theorem IssuedIn.indexed {profile : Profile} {tid : Nat} {entry : Pending}
    {state : State} {actions : List Action} {result : State × List Observation}
    (issued : IssuedIn profile tid entry state actions result) :
    ∃ index, IssuedAt profile tid entry index state actions result := by
  induction issued with
  | head stepped following actual => exact ⟨0, .head stepped following actual⟩
  | later stepped following actual ih =>
      obtain ⟨index, indexed⟩ := ih
      exact ⟨index + 1, .later stepped following indexed⟩

theorem IssuedAt.bound {profile : Profile} {tid index : Nat} {entry : Pending}
    {state : State} {actions : List Action} {result : State × List Observation}
    (issued : IssuedAt profile tid entry index state actions result) : index < actions.length := by
  induction issued with
  | head => exact Nat.zero_lt_succ _
  | later stepped following actual ih => exact Nat.succ_lt_succ ih

/-- Expose the successful prefix, actual selected action and actual store
admission at the indexed position. No writer is reconstructed from RAM bits. -/
theorem IssuedAt.prestate {profile : Profile} {tid index : Nat} {entry : Pending}
    {state : State} {actions : List Action} {result : State × List Observation}
    (issued : IssuedAt profile tid entry index state actions result) :
    ∃ before action first,
      schedule state (actions.take index) profile = .ok (before, result.2.take index) ∧
      actions[index]? = some action ∧ step before action profile = .ok first ∧
      Issued before action first profile tid entry := by
  induction issued with
  | head stepped following actual => exact ⟨_, _, _, rfl, rfl, stepped, actual⟩
  | later stepped following actual ih =>
      obtain ⟨before, action, first, prefixRun, selected, executed, origin⟩ := ih
      refine ⟨before, action, first, ?_, ?_, executed, origin⟩
      · simp only [List.take_succ_cons, schedule, stepped, ok_bind, prefixRun, pure_ok]
      · exact selected

/-- A managed occurrence allocated later in this run cannot be below its
worker's initial counter, regardless of drains, peer steps or equal payloads. -/
theorem IssuedAt.occurrence_lower {profile : Profile} {tid index occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word} {state : State}
    {actions : List Action} {result : State × List Observation} {prior : Worker}
    (issued : IssuedAt profile tid (.managed reference value occurrence) index state actions result)
    (live : state.workers[tid]? = some prior) : prior.nextStore ≤ occurrence := by
  obtain ⟨before, action, first, prefixRun, _, _, origin⟩ := issued.prestate
  obtain ⟨worker, workerLive, allocated⟩ := origin.managed_occurrence
  rw [allocated]
  exact schedule_nextStore_le prefixRun live workerLive

/-- Once an issue has happened its occurrence remains strictly below the
worker's final counter, even after the exact entry has left the FIFO. -/
theorem IssuedAt.occurrence_upper {profile : Profile} {tid index occurrence : Nat}
    {reference : Queue.ManagedRef} {value : Word} {state : State}
    {actions : List Action} {result : State × List Observation} {current : Worker}
    (issued : IssuedAt profile tid (.managed reference value occurrence) index state actions result)
    (live : result.1.workers[tid]? = some current) : occurrence < current.nextStore := by
  induction issued with
  | head stepped following actual =>
      obtain ⟨prior, priorLive, allocated⟩ := actual.managed_occurrence
      obtain ⟨middle, middleLive⟩ := step_worker_present stepped priorLive
      have increment := actual.nextStore_succ priorLive middleLive
      have later := schedule_nextStore_le following middleLive live
      omega
  | later stepped following actual ih => exact ih live

private theorem no_same_occurrence_in_suffix {profile : Profile} {tid occurrence index : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {action : Action} {first : State × Observation} {rest : List Action}
    {tail : State × List Observation}
    (here : Issued state action first profile tid (.managed firstReference firstValue occurrence))
    (later : IssuedAt profile tid (.managed secondReference secondValue occurrence)
      index first.1 rest tail) : False := by
  obtain ⟨prior, priorLive, allocated⟩ := here.managed_occurrence
  have success : step state action profile = .ok first := by
    cases here with
    | ordinary issuing success => exact success
  obtain ⟨middle, middleLive⟩ := step_worker_present success priorLive
  have increment := here.nextStore_succ priorLive middleLive
  have lower := later.occurrence_lower middleLive
  omega

/-- A managed writer identity `(tid, occurrence)` determines one global action
position in an actual successful run. References and values need not agree in
this premise; equal payloads are never used to disambiguate two issues. No
pending-queue ordering invariant or empty-boundary assumption is needed. -/
theorem IssuedAt.occurrence_index_unique {profile : Profile} {tid occurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {actions : List Action} {result otherResult : State × List Observation}
    (first : IssuedAt profile tid (.managed firstReference firstValue occurrence)
      firstIndex state actions result)
    (second : IssuedAt profile tid (.managed secondReference secondValue occurrence)
      secondIndex state actions otherResult) : firstIndex = secondIndex := by
  induction first generalizing secondIndex secondReference secondValue otherResult with
  | head stepped following actual =>
      cases second with
      | head => rfl
      | later steppedSecond followingSecond actualSecond =>
          have same := Except.ok.inj (stepped.symm.trans steppedSecond)
          cases same
          exact False.elim (no_same_occurrence_in_suffix actual actualSecond)
  | later stepped following actual ih =>
      cases second with
      | head steppedSecond followingSecond actualSecond =>
          have same := Except.ok.inj (stepped.symm.trans steppedSecond)
          cases same
          exact False.elim (no_same_occurrence_in_suffix actualSecond actual)
      | later steppedSecond followingSecond actualSecond =>
          have same := Except.ok.inj (stepped.symm.trans steppedSecond)
          cases same
          exact congrArg Nat.succ (ih actualSecond)

private theorem finish_pending_eq {state : State} {tid : Nat} {worker current : Worker}
    {pending : List Pending} {observation : Sequential.Observation}
    {result : State × Observation} {nextStore : Nat}
    (live : state.workers[tid]? = some worker)
    (finish : FinishEffect state tid worker pending observation result nextStore)
    (currentLive : result.1.workers[tid]? = some current) : current.pending = pending := by
  cases finish <;>
    exact congrArg Worker.pending (Option.some.inj
      (currentLive.symm.trans (List.getElem?_set_self (List.getElem_of_getElem? live).1)))

private theorem issued_pending_eq {state : State} {action : Action}
    {result : State × Observation} {profile : Profile} {tid : Nat} {entry : Pending}
    (issued : Issued state action result profile tid entry) {prior current : Worker}
    (priorLive : state.workers[tid]? = some prior)
    (currentLive : result.1.workers[tid]? = some current) :
    current.pending = prior.pending ++ [entry] := by
  cases issued with
  | ordinary issuing success live fetched effect intent admission committed =>
      have same := Option.some.inj (priorLive.symm.trans live)
      rw [same]
      exact finish_pending_eq live committed currentLive

/-- Two issue witnesses for the same actual step retain the same complete
entry. A successful enqueue appends exactly one entry to the actual prior FIFO. -/
theorem Issued.entry_eq {state : State} {action : Action} {result : State × Observation}
    {profile : Profile} {tid : Nat} {firstEntry secondEntry : Pending}
    (first : Issued state action result profile tid firstEntry)
    (second : Issued state action result profile tid secondEntry) : firstEntry = secondEntry := by
  cases first with
  | ordinary issuing success live fetched effect intent admission committed =>
      obtain ⟨current, currentLive⟩ := step_worker_present success live
      have left := finish_pending_eq live committed currentLive
      have right := issued_pending_eq second live currentLive
      have appended := List.append_cancel_left (left.symm.trans right)
      exact (List.cons.inj appended).1

/-- The indexed action fixes its full issued entry, including authority, width,
value and occurrence. Prefix and selected-step determinism are derived from
successful execution; matching payload bits supply no premise. -/
theorem IssuedAt.entry_eq {profile : Profile} {tid index : Nat}
    {firstEntry secondEntry : Pending} {state : State} {actions : List Action}
    {result otherResult : State × List Observation}
    (first : IssuedAt profile tid firstEntry index state actions result)
    (second : IssuedAt profile tid secondEntry index state actions otherResult) :
    firstEntry = secondEntry := by
  obtain ⟨before, action, output, prefixRun, selected, stepped, actual⟩ := first.prestate
  obtain ⟨otherBefore, otherAction, otherOutput, otherPrefix, otherSelected,
    otherStepped, otherActual⟩ := second.prestate
  have sameBefore : before = otherBefore := congrArg Prod.fst (Except.ok.inj (prefixRun.symm.trans otherPrefix))
  have sameAction := Option.some.inj (selected.symm.trans otherSelected)
  subst otherBefore
  subst otherAction
  have sameOutput := Except.ok.inj (stepped.symm.trans otherStepped)
  subst otherOutput
  exact actual.entry_eq otherActual

/-- Within one actual schedule, `(tid, occurrence)` names both one issue
position and one complete managed entry, even after publication has removed it
from the FIFO. No value comparison or current-queue membership is used. -/
theorem IssuedAt.managed_identity_unique {profile : Profile}
    {tid occurrence firstIndex secondIndex : Nat}
    {firstReference secondReference : Queue.ManagedRef} {firstValue secondValue : Word}
    {state : State} {actions : List Action} {result otherResult : State × List Observation}
    (first : IssuedAt profile tid (.managed firstReference firstValue occurrence)
      firstIndex state actions result)
    (second : IssuedAt profile tid (.managed secondReference secondValue occurrence)
      secondIndex state actions otherResult) :
    firstIndex = secondIndex ∧ firstReference = secondReference ∧ firstValue = secondValue := by
  have sameIndex := first.occurrence_index_unique second
  subst secondIndex
  have sameEntry := first.entry_eq second
  cases sameEntry
  exact ⟨rfl, rfl, rfl⟩

/-- An actual issue inside a successful prefix is the same indexed issue in
the complete successful schedule. The common prefix is identified by execution
determinism, not by equality of observed payloads. -/
theorem IssuedAt.lift_prefix {profile : Profile} {tid index stop : Nat} {entry : Pending}
    {state : State} {actions : List Action} {prefixResult result : State × List Observation}
    (issued : IssuedAt profile tid entry index state (actions.take stop) prefixResult)
    (success : schedule state actions profile = .ok result) :
    IssuedAt profile tid entry index state actions result := by
  induction stop generalizing state actions prefixResult result index with
  | zero =>
      have bound := issued.bound
      simp only [List.take_zero, List.length_nil] at bound
      omega
  | succ stop ih =>
      cases actions with
      | nil =>
          have bound := issued.bound
          simp only [List.take_nil, List.length_nil] at bound
          omega
      | cons action rest =>
          obtain ⟨first, tail, stepped, following, same⟩ := schedule_cons_ok success
          simp only [List.take_succ_cons] at issued
          rw [same]
          cases issued with
          | head actualStep actualFollowing actual =>
              have equal := Except.ok.inj (stepped.symm.trans actualStep)
              cases equal
              exact .head stepped following actual
          | later actualStep actualFollowing actual =>
              have equal := Except.ok.inj (stepped.symm.trans actualStep)
              cases equal
              exact .later stepped following (ih actual following)

end EDSL.OS.TSO64.StoreHistory
