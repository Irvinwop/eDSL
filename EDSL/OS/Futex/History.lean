/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Invariant

namespace EDSL.OS.Futex
open X86

/-- Positive capture from the actual pending Saved record; pin issuance is
derived from the keeper, not a premise asserting future service success. -/
theorem captureEntered_enabled (config : Config) (state : State) (worker invocation : Nat)
    (saved : Suspend.Saved) (operation : Op) (registration : Resources.Registration)
    (pending : state.suspended.pending worker = some saved)
    (current : saved.identifier = invocation) (owner : saved.worker = worker)
    (absent : state.calls invocation = none)
    (classified : classify saved.request = .ok operation)
    (registered : state.registration = some registration)
    (address : saved.request.user.registers .rdi = registration.address)
    (target : targetSupported config state.authority registration.address = true)
    (valid : Atomics.WellFormed state.authority) (live : Resources.Valid state.authority registration) :
    captureEntered config state worker invocation = .ok
      (putCall { state with authority := Atomics.install state.authority (registration.callHandle config.serviceActor) }
        invocation ⟨worker, operation, state.authority.nextHandle, .entered⟩) := by
  simp [captureEntered, pending, current, owner, absent, classified, registered, address, target,
    Resources.retainCall_enabled _ _ _ valid live, Except.mapError]

/-- Inversion binds capture to the real invocation and exact canonical request,
and retains a fresh compatible pin in the same transition. -/
theorem captureEntered_effect {config : Config} {state after : State} {worker invocation : Nat}
    (success : captureEntered config state worker invocation = .ok after) :
    ∃ saved operation registration retained,
      state.suspended.pending worker = some saved ∧ saved.identifier = invocation ∧
      saved.worker = worker ∧ state.calls invocation = none ∧
      classify saved.request = .ok operation ∧ state.registration = some registration ∧
      saved.request.user.registers .rdi = registration.address ∧
      Resources.retainCall state.authority registration config.serviceActor = .ok retained ∧
      after = putCall { state with authority := retained.1 } invocation
        ⟨worker, operation, retained.2, .entered⟩ := by
  cases pending : state.suspended.pending worker with
  | none => simp [captureEntered, pending] at success
  | some saved =>
    by_cases current : saved.identifier = invocation
    · by_cases owner : saved.worker = worker
      · cases found : state.calls invocation with
        | some call => simp [captureEntered, pending, current, owner, found] at success
        | none =>
          cases classified : classify saved.request with
          | error fault => simp [captureEntered, pending, current, owner, found, classified] at success
          | ok operation =>
            cases registered : state.registration with
            | none => simp [captureEntered, pending, current, owner, found, classified, registered] at success
            | some registration =>
              by_cases address : saved.request.user.registers .rdi = registration.address
              · cases target : targetSupported config state.authority registration.address with
                | false => simp [captureEntered, pending, current, owner, found, classified, registered,
                    address, target] at success
                | true =>
                  cases retained : Resources.retainCall state.authority registration config.serviceActor with
                  | error fault => simp [captureEntered, pending, current, owner, found, classified, registered,
                      address, target, retained, Except.mapError] at success
                  | ok result =>
                    refine ⟨saved, operation, registration, result, rfl, current, owner, rfl,
                      classified, rfl, address, retained, ?_⟩
                    simpa [captureEntered, pending, current, owner, found, classified, registered,
                      address, target, retained, Except.mapError] using success.symm
              · simp [captureEntered, pending, current, owner, found, classified, registered, address] at success
      · simp [captureEntered, pending, current, owner] at success
    · simp [captureEntered, pending, current] at success

/-- Successful resumption contains the actual architectural resume with the
stored typed raw result, followed by the checked closure of only its call pin. -/
theorem resumeReady_effect {config : Config} {state after : State} {invocation : Nat}
    {flags rcx r11 : Word} (success : resumeReady config state invocation flags rcx r11 = .ok after) :
    ∃ call outcome origin registration resumed closed,
      state.calls invocation = some call ∧ call.phase = .ready outcome origin ∧
      state.registration = some registration ∧
      Suspend.resume state.suspended call.worker invocation outcome.raw flags rcx r11 = .ok resumed ∧
      Resources.closeCall state.authority registration config.serviceActor call.pin = .ok closed ∧
      after = { state with suspended := resumed
                           authority := closed
                           calls := fun query => if query = invocation then none else state.calls query } := by
  cases found : state.calls invocation with
  | none => simp [resumeReady, found] at success
  | some call =>
    have readyExists : ∃ outcome origin, call.phase = .ready outcome origin := by
      rcases call with ⟨worker, operation, pin, phase⟩
      cases operation with
      | wait expected =>
        cases phase with
        | entered => simp [resumeReady, found] at success
        | queued => simp [resumeReady, found] at success
        | ready outcome origin => exact ⟨outcome, origin, rfl⟩
      | wakeOne =>
        cases phase with
        | entered => simp [resumeReady, found] at success
        | ready outcome origin => exact ⟨outcome, origin, rfl⟩
    obtain ⟨outcome, origin, phase⟩ := readyExists
    cases registered : state.registration with
    | none => simp [resumeReady, found, phase, registered] at success
    | some registration =>
      cases resumed : Suspend.resume state.suspended call.worker invocation outcome.raw flags rcx r11 with
      | error fault => simp [resumeReady, found, phase, registered, resumed, Except.mapError] at success
      | ok middle =>
        cases closed : Resources.closeCall state.authority registration config.serviceActor call.pin with
        | error fault => simp [resumeReady, found, phase, registered, resumed, closed, Except.mapError] at success
        | ok final =>
          refine ⟨call, outcome, origin, registration, middle, final, rfl, phase, rfl,
            resumed, closed, ?_⟩
          simpa [resumeReady, found, phase, registered, resumed, closed, Except.mapError] using success.symm

theorem resumeReady_consumed {config : Config} {state after : State} {invocation : Nat}
    {flags rcx r11 : Word} (success : resumeReady config state invocation flags rcx r11 = .ok after) :
    after.calls invocation = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same⟩ := resumeReady_effect success
  rw [same]
  simp

/-- All peer workers and FIFOs survive a ready resume exactly. -/
theorem resumeReady_peer {config : Config} {state after : State} {invocation query : Nat}
    {flags rcx r11 : Word} (success : resumeReady config state invocation flags rcx r11 = .ok after)
    (different : ∀ call, state.calls invocation = some call → query ≠ call.worker) :
    after.suspended.machine.workers[query]? = state.suspended.machine.workers[query]? := by
  obtain ⟨call, _, _, _, _, _, found, _, _, resumed, _, same⟩ := resumeReady_effect success
  rw [same]
  exact Suspend.resume_peer (Ne.symm (different call found)) resumed

theorem resumeReady_memory {config : Config} {state after : State} {invocation : Nat}
    {flags rcx r11 : Word} (success : resumeReady config state invocation flags rcx r11 = .ok after) :
    after.suspended.machine.memory = state.suspended.machine.memory := by
  obtain ⟨_, _, _, _, _, _, _, _, _, resumed, _, same⟩ := resumeReady_effect success
  rw [same]
  exact Suspend.resume_memory resumed

theorem resumeReady_resources {config : Config} {state after : State} {invocation : Nat}
    {flags rcx r11 : Word} (success : resumeReady config state invocation flags rcx r11 = .ok after) :
    after.authority.shared = state.authority.shared := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, closed, same⟩ := resumeReady_effect success
  obtain ⟨_, _, actual⟩ := Resources.closeCall_ok _ _ _ _ _ closed
  obtain ⟨_, _, exactClosed⟩ := Atomics.close_ok _ _ _ _ actual
  rw [same, exactClosed]

/-- A stale service resume cannot bypass consumption even if a later syscall
has been captured at the same worker index. -/
theorem resumeReady_missing (config : Config) (state : State) (invocation : Nat)
    (absent : state.calls invocation = none) (flags rcx r11 : Word) :
    resumeReady config state invocation flags rcx r11 = .error .missingCall := by
  simp [resumeReady, absent]

theorem resumeReady_twice {config : Config} {state after : State} {invocation : Nat}
    {flags rcx r11 : Word} (success : resumeReady config state invocation flags rcx r11 = .ok after)
    (flags' rcx' r11' : Word) :
    resumeReady config after invocation flags' rcx' r11' = .error .missingCall :=
  resumeReady_missing _ _ _ (resumeReady_consumed success) _ _ _


/-- Distinct invocations cannot share a suspended physical worker. -/
theorem WellFormed.same_worker {config : Config} {state : State} (valid : WellFormed config state)
    {left right : Nat} {a b : Call} (first : state.calls left = some a)
    (second : state.calls right = some b) (same : a.worker = b.worker) : left = right := by
  obtain ⟨savedA, pendingA, currentA⟩ := valid.bound first
  obtain ⟨savedB, pendingB, currentB⟩ := valid.bound second
  rw [same] at pendingA
  have equal := Option.some.inj (pendingA.symm.trans pendingB)
  subst savedB
  exact currentA.symm.trans currentB

/-- Every prefix retains the pending-call bijection, live unique pins and
exact eligibility set when a ready invocation is consumed. -/
theorem WellFormed.resume_step {config : Config} {state after : State}
    (valid : WellFormed config state) {invocation : Nat} {flags rcx r11 : Word}
    (success : resumeReady config state invocation flags rcx r11 = .ok after) :
    WellFormed config after := by
  obtain ⟨call, outcome, origin, registration, resumed, closed, found, ready, registered,
    resume, close, same⟩ := resumeReady_effect success
  have callValid := valid.calls invocation call found
  obtain ⟨reg, regEq, regLive, _, _, _⟩ := callValid.registration
  have regSame := Option.some.inj (registered.symm.trans regEq)
  subst reg
  have resourceEffect := Resources.closeCall_effect _ _ _ _ _ valid.authority regLive close
  have suspendValid := valid.suspended.resume resume
  have noQueue : invocation ∉ state.queue := by
    apply valid.notQueued found
    rintro ⟨worker, expected, pin, equal⟩
    have tagged := congrArg (fun selected : Call => selected.phase.isQueued) equal
    simp [ready, Phase.isQueued] at tagged
  subst after
  refine ⟨suspendValid, resourceEffect.1, ?_, ?_, valid.queue, ?_, ?_⟩
  · intro identifier selected live
    have separate : identifier ≠ invocation := by
      intro same
      subst identifier
      simp at live
    have prior : state.calls identifier = some selected := by simpa [separate] using live
    have before := valid.calls identifier selected prior
    have workers : selected.worker ≠ call.worker := by
      intro equal
      exact separate (valid.same_worker prior found equal)
    obtain ⟨saved, pending, current, owner, classified⟩ := before.saved
    have afterPending : resumed.pending selected.worker = some saved := by
      simpa only [Suspend.resume_pending resume, ite_eq_right workers] using pending
    obtain ⟨otherReg, otherEq, _, pinLive, notKeeper, addresses⟩ := before.registration
    have regSame := Option.some.inj (registered.symm.trans otherEq)
    subst otherReg
    have pins : selected.pin ≠ call.pin := by
      intro equal
      exact separate (valid.pins _ _ _ _ prior found equal)
    refine ⟨⟨saved, afterPending, current, owner, classified⟩,
      ⟨registration, registered, resourceEffect.2.1, ?_, notKeeper, ?_⟩, before.outcome⟩
    · exact (resourceEffect.2.2.2.2.2 _ pins).trans pinLive
    · intro saved pending
      apply addresses saved
      simpa only [Suspend.resume_pending resume, ite_eq_right workers] using pending
  · intro worker saved pending
    have workers : worker ≠ call.worker := by
      intro equal
      subst worker
      rw [Suspend.resume_consumed resume] at pending
      cases pending
    have prior : state.suspended.pending worker = some saved := by
      simpa only [Suspend.resume_pending resume, ite_eq_right workers] using pending
    obtain ⟨selected, live, selectedWorker⟩ := valid.pending worker saved prior
    have separate : saved.identifier ≠ invocation := by
      intro equal
      have impossible := Option.some.inj ((equal ▸ live).symm.trans found)
      subst selected
      exact workers selectedWorker.symm
    exact ⟨selected, by simpa [separate] using live, selectedWorker⟩
  · intro identifier
    by_cases separate : identifier ≠ invocation
    · simpa only [ite_eq_right separate] using valid.eligible identifier
    · have equal : identifier = invocation := Classical.not_not.mp separate
      subst identifier
      simp [noQueue]
  · intro left a right b first second equal
    have leftDifferent : left ≠ invocation := by intro h; subst left; simp at first
    have rightDifferent : right ≠ invocation := by intro h; subst right; simp at second
    apply valid.pins left a right b
      (by simpa [leftDifferent] using first) (by simpa [rightDifferent] using second) equal

/-- Prefix preservation for every successful service scheduler action. -/
theorem WellFormed.service_step {config : Config} {state after : State} {action : Action}
    (valid : WellFormed config state) (success : step config state action = .ok after) :
    WellFormed config after := by
  cases action with
  | compare invocation => exact valid.compare_step success
  | wake invocation target => exact valid.wake_step success
  | retry invocation => exact valid.retry_step success
  | spurious invocation => exact valid.spurious_step success
  | resume invocation flags rcx r11 => exact valid.resume_step success
  | idle => simp [step] at success; subst after; exact valid

theorem WellFormed.schedule {config : Config} {state after : State} {actions : List Action}
    (valid : WellFormed config state) (success : Futex.schedule config state actions = .ok after) :
    WellFormed config after := by
  induction actions generalizing state with
  | nil => simp [Futex.schedule] at success; subst after; exact valid
  | cons action rest ih =>
    cases first : step config state action with
    | error fault => simp [Futex.schedule, first] at success
    | ok middle =>
      exact ih (valid.service_step first) (by simpa [Futex.schedule, first] using success)


/-- Consumption removes the actual invocation globally, rather than merely
clearing this service-map index. Later entries use the monotone frontier. -/
theorem resumeReady_invocation_absent {config : Config} {state after : State} {invocation : Nat}
    {flags rcx r11 : Word} (valid : WellFormed config state)
    (success : resumeReady config state invocation flags rcx r11 = .ok after) :
    invocation < after.suspended.nextCall ∧
    ∀ query saved, after.suspended.pending query = some saved → saved.identifier ≠ invocation := by
  obtain ⟨_, _, _, _, _, _, _, _, _, resumed, _, same⟩ := resumeReady_effect success
  rw [same]
  exact ⟨valid.suspended.resume_identifier_lt resumed, valid.suspended.resume_consumed_id resumed⟩

end EDSL.OS.Futex
