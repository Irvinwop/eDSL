/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Entry
import EDSL.OS.Futex.History

namespace EDSL.OS.Futex.Physical
open X86 AddressSpace

/-- A new service record is justified by the actual entry instruction and its
allocated Saved identifier. Existing calls cannot occupy that fresh identifier. -/
theorem entered_wellFormed {config : Config} {state : State} {suspended : Suspend.State}
    {worker invocation : Nat} {after : State}
    (valid : WellFormed config state)
    (issued : Suspend.issue state.suspended worker = .ok (suspended, .entered worker invocation))
    (captured : captureEntered config { state with suspended := suspended } worker invocation = .ok after) :
    WellFormed config after ∧ after.suspended = suspended ∧
      after.authority.shared = state.authority.shared ∧ Atomics.History state.authority after.authority := by
  obtain ⟨fresh, selected, request, live, running, absent, empty, decoded, stepped, user,
    requestMemory, context, continuation, suspendedEq, machine, frontier, pending⟩ :=
    Suspend.issue_entered_effect issued
  obtain ⟨saved, operation, registration, retained, savedAt, current, owner, noCall,
    classified, registered, address, kept, resultEq⟩ := captureEntered_effect captured
  have savedEq : saved = ⟨invocation, worker, request⟩ :=
    Option.some.inj (savedAt.symm.trans pending)
  subst saved
  have keeper := (Resources.retainCall_ok _ _ _ _ kept).1
  have retainedEq := Except.ok.inj
    ((Resources.retainCall_enabled state.authority registration config.serviceActor valid.authority keeper).symm.trans kept)
  subst retained
  have afterEq : after = enteredState config state registration worker request operation := by
    rw [resultEq, suspendedEq, fresh]
    rfl
  have invariant := enteredState_wellFormed valid registration worker selected request operation
    registered keeper live running empty absent user continuation classified address
  have issuedPin := (Resources.retainCall_ok _ _ _ _ kept).2
  exact ⟨afterEq ▸ invariant, by rw [afterEq, suspendedEq]; rfl,
    by rw [afterEq]; rfl, by rw [afterEq]; exact .next (.issue issuedPin) .refl⟩

/-- Every successful physical issue preserves the current call/queue/resource
invariant and exact RAM coupling. Resource failures cannot partially capture. -/
theorem issue_sound (profile : Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) (valid : WellFormed profile.service state)
    (memory : toMemory state.authority.shared.resources.space = state.suspended.machine.memory)
    (success : issue profile state worker = .ok result) :
    WellFormed profile.service result.1 ∧
      toMemory result.1.authority.shared.resources.space = result.1.suspended.machine.memory ∧
      Atomics.History state.authority result.1.authority := by
  cases issued : Suspend.issue state.suspended worker with
  | error fault => simp [issue, issued, Except.mapError] at success
  | ok actual =>
    rcases actual with ⟨suspended, observation⟩
    cases synced : synchronize profile state.authority observation with
    | error fault => simp [issue, issued, synced, Except.mapError] at success
    | ok authority =>
      have facts := synchronize_sound profile state.authority authority _ _ observation valid.authority memory
        (issue_effect issued) synced
      have frames := synchronize_frames profile state.authority authority observation synced
      cases observation with
      | entered selected invocation =>
        have actualIssued := issued
        have sameWorker : selected = worker := by
          cases Suspend.issue_effect _ _ _ actualIssued
          rfl
        subst selected
        have authorityEq : authority = state.authority := by
          simpa [synchronize] using synced.symm
        subst authority
        cases captured : captureEntered profile.service { state with suspended := suspended } worker invocation with
        | error fault => simp [issue, issued, synchronize, captured, Except.mapError] at success
        | ok after =>
          simp [issue, issued, synchronize, captured, Except.mapError] at success
          subst result
          have resultFacts := entered_wellFormed valid actualIssued captured
          exact ⟨resultFacts.1, by rw [resultFacts.2.2.1, resultFacts.2.1]; exact facts.1,
            resultFacts.2.2.2⟩
      | machine machine =>
        have actualIssued := issued
        have effect := Suspend.issue_machine_effect actualIssued
        simp [issue, issued, synced, Except.mapError] at success
        subst result
        exact ⟨valid.physicalFrame suspended authority (valid.suspended.issue issued) facts.2.2 effect.2.2.1 frames.1,
          facts.1, facts.2.1⟩
      | parked selected invocation =>
        have actualIssued := issued
        have sameWorker : selected = worker := by cases Suspend.issue_effect _ _ _ actualIssued; rfl
        subst selected
        have authorityEq : authority = state.authority := by
          simpa [synchronize] using synced.symm
        subst authority
        have effect := Suspend.issue_parked_effect actualIssued
        simp [issue, issued, synchronize, Except.mapError] at success
        subst result
        exact ⟨valid.physicalFrame suspended state.authority (valid.suspended.issue issued) facts.2.2
          (by rw [effect.1]) frames.1, facts.1, facts.2.1⟩
      | resumed selected invocation raw =>
        cases Suspend.issue_effect _ _ _ issued
      | idle =>
        cases Suspend.issue_effect _ _ _ issued

theorem drain_sound (profile : Profile) (state : State) (worker : Nat)
    (result : State × Suspend.Observation) (valid : WellFormed profile.service state)
    (memory : toMemory state.authority.shared.resources.space = state.suspended.machine.memory)
    (success : drain profile state worker = .ok result) :
    WellFormed profile.service result.1 ∧
      toMemory result.1.authority.shared.resources.space = result.1.suspended.machine.memory ∧
      Atomics.History state.authority result.1.authority := by
  cases drained : Suspend.drain state.suspended worker with
  | error fault => simp [drain, drained, Except.mapError] at success
  | ok actual =>
    cases synced : synchronize profile state.authority actual.2 with
    | error fault => simp [drain, drained, synced, Except.mapError] at success
    | ok authority =>
      simp [drain, drained, synced, Except.mapError] at success
      subst result
      have facts := synchronize_sound profile state.authority authority _ _ actual.2 valid.authority memory
        (drain_effect drained) synced
      have frames := synchronize_frames profile state.authority authority actual.2 synced
      obtain ⟨machine, observation, executed, same⟩ := Suspend.drain_ok _ _ _ drained
      refine ⟨valid.physicalFrame actual.1 authority (valid.suspended.drain drained) facts.2.2 ?_ frames.1,
        facts.1, facts.2.1⟩
      have projected := congrArg Prod.fst same
      dsimp only at projected
      rw [projected]

end EDSL.OS.Futex.Physical
