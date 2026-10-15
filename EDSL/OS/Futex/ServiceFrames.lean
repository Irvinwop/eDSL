/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.History

namespace EDSL.OS.Futex
open X86

/-- Service bookkeeping does not publish a store, mutate RAM, move a worker,
close a pin, or change the registered cell. Only ready resume changes context. -/
def Stutter (before after : State) : Prop :=
  after.suspended = before.suspended ∧ after.authority = before.authority ∧
    after.registration = before.registration

theorem compareWait_stutter {config : Config} {state after : State}
    {invocation : Nat}
    (success : compareWait config state invocation = .ok after) : Stutter state after := by
  cases found : state.calls invocation with
  | none => simp [compareWait, found] at success
  | some call =>
    rcases call with ⟨worker, operation, pin, phase⟩
    cases operation with
    | wakeOne => cases phase <;> simp [compareWait, found] at success
    | wait expected =>
      cases phase with
      | queued => simp [compareWait, found] at success
      | ready result origin => simp [compareWait, found] at success
      | entered =>
        cases read : Resources.readPinned state.authority config.serviceActor pin with
        | error fault => simp [compareWait, found, read, Except.mapError] at success
        | ok current =>
          by_cases equal : current = expected
          · by_cases absent : invocation ∉ state.queue
            · simp [compareWait, found, read, equal, absent, Except.mapError] at success
              subst after
              exact ⟨rfl, rfl, rfl⟩
            · have present : invocation ∈ state.queue := Classical.not_not.mp absent
              simp [compareWait, found, read, equal, present, Except.mapError] at success
          · simp [compareWait, found, read, equal, Except.mapError] at success
            subst after
            exact ⟨rfl, rfl, rfl⟩

theorem retryQueued_stutter {state after : State}
    {invocation : Nat}
    (success : retryQueued state invocation = .ok after) : Stutter state after := by
  cases found : state.calls invocation with
  | none => simp [retryQueued, found] at success
  | some call =>
    rcases call with ⟨worker, operation, pin, phase⟩
    cases operation with
    | wakeOne => cases phase <;> simp [retryQueued, found] at success
    | wait expected =>
      cases phase with
      | entered => simp [retryQueued, found] at success
      | ready result origin => simp [retryQueued, found] at success
      | queued =>
        simp [retryQueued, found] at success
        subst after
        exact ⟨rfl, rfl, rfl⟩

theorem spuriousReady_stutter {state after : State}
    {invocation : Nat}
    (success : spuriousReady state invocation = .ok after) : Stutter state after := by
  cases found : state.calls invocation with
  | none => simp [spuriousReady, found] at success
  | some call =>
    rcases call with ⟨worker, operation, pin, phase⟩
    cases operation with
    | wakeOne => cases phase <;> simp [spuriousReady, found] at success
    | wait expected =>
      cases phase with
      | entered => simp [spuriousReady, found] at success
      | ready result origin => simp [spuriousReady, found] at success
      | queued =>
        simp [spuriousReady, found] at success
        subst after
        exact ⟨rfl, rfl, rfl⟩

theorem wakeOne_stutter {state after : State}
    {invocation : Nat} {selected : Option Nat}
    (success : wakeOne state invocation selected = .ok after) : Stutter state after := by
  cases found : state.calls invocation with
  | none => simp [wakeOne, found] at success
  | some call =>
    rcases call with ⟨worker, operation, pin, phase⟩
    cases operation with
    | wait expected => cases phase <;> simp [wakeOne, found] at success
    | wakeOne =>
      cases phase with
      | ready result origin => simp [wakeOne, found] at success
      | entered =>
        cases selected with
        | none =>
          by_cases empty : state.queue = []
          · simp [wakeOne, found, empty] at success
            subst after
            exact ⟨rfl, rfl, rfl⟩
          · simp [wakeOne, found, empty] at success
        | some target =>
          by_cases different : target ≠ invocation
          · by_cases member : target ∈ state.queue
            · cases waiting : state.calls target with
              | none => simp [wakeOne, found, different, member, waiting] at success
              | some waiter =>
                rcases waiter with ⟨waitingWorker, waitingOp, waitingPin, waitingPhase⟩
                cases waitingOp with
                | wakeOne => cases waitingPhase <;> simp [wakeOne, found, different, member, waiting] at success
                | wait expected =>
                  cases waitingPhase with
                  | entered => simp [wakeOne, found, different, member, waiting] at success
                  | ready result origin => simp [wakeOne, found, different, member, waiting] at success
                  | queued =>
                    simp [wakeOne, found, different, member, waiting] at success
                    subst after
                    exact ⟨rfl, rfl, rfl⟩
            · simp [wakeOne, found, different, member] at success
          · have same : target = invocation := Classical.not_not.mp different
            simp [wakeOne, found, same] at success


theorem service_memory {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) :
    after.suspended.machine.memory = state.suspended.machine.memory := by
  cases action with
  | compare invocation => rw [(compareWait_stutter success).1]
  | wake invocation target => rw [(wakeOne_stutter success).1]
  | retry invocation => rw [(retryQueued_stutter success).1]
  | spurious invocation => rw [(spuriousReady_stutter success).1]
  | resume invocation flags rcx r11 => exact resumeReady_memory success
  | idle => simp [step] at success; subst after; rfl

theorem service_shared {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) :
    after.authority.shared = state.authority.shared := by
  cases action with
  | compare invocation => rw [(compareWait_stutter success).2.1]
  | wake invocation target => rw [(wakeOne_stutter success).2.1]
  | retry invocation => rw [(retryQueued_stutter success).2.1]
  | spurious invocation => rw [(spuriousReady_stutter success).2.1]
  | resume invocation flags rcx r11 => exact resumeReady_resources success
  | idle => simp [step] at success; subst after; rfl


/-- Service scheduling projects to an existing machine resume or an idle
mechanism step. This connects service traces to invocation non-reuse proofs. -/
theorem service_suspend_step {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) :
    ∃ actual observation, Suspend.step state.suspended actual = .ok (after.suspended, observation) := by
  cases action with
  | compare invocation =>
    exact ⟨.idle, .idle, by rw [(compareWait_stutter success).1]; rfl⟩
  | wake invocation target =>
    exact ⟨.idle, .idle, by rw [(wakeOne_stutter success).1]; rfl⟩
  | retry invocation =>
    exact ⟨.idle, .idle, by rw [(retryQueued_stutter success).1]; rfl⟩
  | spurious invocation =>
    exact ⟨.idle, .idle, by rw [(spuriousReady_stutter success).1]; rfl⟩
  | resume invocation flags rcx r11 =>
    obtain ⟨call, outcome, _, _, _, _, _, _, _, resumed, _, same⟩ := resumeReady_effect success
    exact ⟨.resume call.worker invocation outcome.raw flags rcx r11,
      .resumed call.worker invocation outcome.raw, by rw [same]; simp [Suspend.step, resumed]⟩
  | idle => simp [step] at success; subst after; exact ⟨.idle, .idle, rfl⟩

/-- Every service resource transition is a checked Atomics operation. -/
theorem service_resources_step {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) : Atomics.Step state.authority after.authority := by
  cases action with
  | compare invocation => rw [(compareWait_stutter success).2.1]; exact .idle
  | wake invocation target => rw [(wakeOne_stutter success).2.1]; exact .idle
  | retry invocation => rw [(retryQueued_stutter success).2.1]; exact .idle
  | spurious invocation => rw [(spuriousReady_stutter success).2.1]; exact .idle
  | resume invocation flags rcx r11 =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, closed, same⟩ := resumeReady_effect success
    rw [same]
    exact .close (Resources.closeCall_ok _ _ _ _ _ closed).2.2
  | idle => simp [step] at success; subst after; exact .idle

theorem service_frontier {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) : after.suspended.nextCall = state.suspended.nextCall := by
  cases action with
  | compare invocation => rw [(compareWait_stutter success).1]
  | wake invocation target => rw [(wakeOne_stutter success).1]
  | retry invocation => rw [(retryQueued_stutter success).1]
  | spurious invocation => rw [(spuriousReady_stutter success).1]
  | resume invocation flags rcx r11 =>
    obtain ⟨_, _, _, _, _, _, _, _, _, resumed, _, same⟩ := resumeReady_effect success
    rw [same, Suspend.resume_nextCall resumed]
  | idle => simp [step] at success; subst after; rfl

theorem service_no_reuse {config : Config} {state after : State} {action : Action} {invocation : Nat}
    (allocated : invocation < state.suspended.nextCall)
    (absent : ∀ query saved, state.suspended.pending query = some saved → saved.identifier ≠ invocation)
    (success : step config state action = .ok after) :
    ∀ query saved, after.suspended.pending query = some saved → saved.identifier ≠ invocation := by
  obtain ⟨actual, observation, projected⟩ := service_suspend_step success
  exact Suspend.step_no_reuse allocated absent projected


theorem service_resources_history {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) : Atomics.History state.authority after.authority :=
  .next (service_resources_step success) .refl

end EDSL.OS.Futex
