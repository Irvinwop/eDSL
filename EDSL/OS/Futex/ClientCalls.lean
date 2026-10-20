/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ServiceFrames

namespace EDSL.OS.Futex.Clients
open X86

/-- Service bookkeeping only rephases or consumes existing invocations; it
cannot manufacture a different worker, operation or resource pin. -/
def CallPreimage (before after : State) : Prop :=
  ∀ identifier call, after.calls identifier = some call →
    ∃ original, before.calls identifier = some original ∧ call.worker = original.worker ∧
      call.op = original.op ∧ call.pin = original.pin

theorem CallPreimage.refl (state : State) : CallPreimage state state :=
  fun _ call found => ⟨call, found, rfl, rfl, rfl⟩

theorem CallPreimage.trans {before middle after : State}
    (first : CallPreimage before middle) (second : CallPreimage middle after) : CallPreimage before after := by
  intro identifier call found
  obtain ⟨original, prior, worker, op, pin⟩ := second identifier call found
  obtain ⟨base, live, workerBase, opBase, pinBase⟩ := first identifier original prior
  exact ⟨base, live, worker.trans workerBase, op.trans opBase, pin.trans pinBase⟩

theorem rephase_preimage (state : State) (identifier : Nat) (call : Call)
    (found : state.calls identifier = some call) (phase : Phase call.op) (queue : List Nat) :
    CallPreimage state { setPhase state identifier call phase with queue := queue } := by
  intro query selected current
  by_cases same : query = identifier
  · subst query
    have equal : selected = {call with phase := phase} := by simpa [setPhase, putCall] using current.symm
    subst selected
    exact ⟨call, found, rfl, rfl, rfl⟩
  · exact ⟨selected, by simpa [setPhase, putCall, same] using current, rfl, rfl, rfl⟩

theorem compare_preimage {config : Config} {state after : State} {invocation : Nat}
    (success : compareWait config state invocation = .ok after) : CallPreimage state after := by
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
              exact rephase_preimage _ _ _ found _ _
            · have present : invocation ∈ state.queue := Classical.not_not.mp absent
              simp [compareWait, found, read, equal, present, Except.mapError] at success
          · simp [compareWait, found, read, equal, Except.mapError] at success
            subst after
            exact rephase_preimage _ _ _ found _ _

theorem retry_preimage {state after : State} {invocation : Nat}
    (success : retryQueued state invocation = .ok after) : CallPreimage state after := by
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
        exact rephase_preimage _ _ _ found _ _

theorem spurious_preimage {state after : State} {invocation : Nat}
    (success : spuriousReady state invocation = .ok after) : CallPreimage state after := by
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
        exact rephase_preimage _ _ _ found _ _

theorem wake_preimage {state after : State} {invocation : Nat} {selected : Option Nat}
    (success : wakeOne state invocation selected = .ok after) : CallPreimage state after := by
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
            exact rephase_preimage _ _ _ found _ _
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
                    let middle := setPhase state target ⟨waitingWorker, .wait expected, waitingPin, .queued⟩
                      (.ready .waitZero (.wake invocation))
                    have first : CallPreimage state middle := rephase_preimage _ _ _ waiting _ state.queue
                    have atWaker : middle.calls invocation = some ⟨worker, .wakeOne, pin, .entered⟩ := by
                      simpa [middle, setPhase, putCall, Ne.symm different] using found
                    exact first.trans (rephase_preimage _ _ _ atWaker _ _)
            · simp [wakeOne, found, different, member] at success
          · have same : target = invocation := Classical.not_not.mp different
            simp [wakeOne, found, same] at success

theorem resume_preimage {config : Config} {state after : State} {invocation : Nat}
    {flags rcx r11 : Word} (success : resumeReady config state invocation flags rcx r11 = .ok after) :
    CallPreimage state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same⟩ := resumeReady_effect success
  rw [same]
  intro query selected found
  by_cases consumed : query = invocation
  · simp [consumed] at found
  · exact ⟨selected, by simpa [consumed] using found, rfl, rfl, rfl⟩

theorem service_preimage {config : Config} {state after : State} {action : Futex.Action}
    (success : Futex.step config state action = .ok after) : CallPreimage state after := by
  cases action with
  | compare invocation => exact compare_preimage success
  | wake invocation selected => exact wake_preimage success
  | retry invocation => exact retry_preimage success
  | spurious invocation => exact spurious_preimage success
  | resume invocation flags rcx r11 => exact resume_preimage success
  | idle => simp [Futex.step] at success; subst after; exact .refl _

theorem service_registration {config : Config} {state after : State} {action : Futex.Action}
    (success : Futex.step config state action = .ok after) : after.registration = state.registration := by
  cases action with
  | compare invocation => exact (compareWait_stutter success).2.2
  | wake invocation selected => exact (wakeOne_stutter success).2.2
  | retry invocation => exact (retryQueued_stutter success).2.2
  | spurious invocation => exact (spuriousReady_stutter success).2.2
  | resume invocation flags rcx r11 =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same⟩ := resumeReady_effect success
    rw [same]
  | idle => simp [Futex.step] at success; subst after; rfl

end EDSL.OS.Futex.Clients
