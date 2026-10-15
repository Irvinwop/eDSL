/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.History
import EDSL.OS.Futex.PhysicalFacts

namespace EDSL.OS.Futex
open X86

/-- Every actual accepted capture passed the complete target-address check.
The supplied interval is a target assumption; it is not inferred from mere
canonicality or from the existence of writable managed cells. -/
theorem captureEntered_target {config : Config} {state after : State} {worker invocation : Nat}
    (success : captureEntered config state worker invocation = .ok after) :
    ∃ registration, state.registration = some registration ∧
      targetSupported config state.authority registration.address = true := by
  obtain ⟨saved, operation, registration, retained, pending, current, owner, absent,
    classified, registered, address, keeping, same⟩ := captureEntered_effect success
  refine ⟨registration, registered, ?_⟩
  cases supported : targetSupported config state.authority registration.address with
  | true => rfl
  | false => simp [captureEntered, pending, current, owner, absent, classified, registered,
      address, supported] at success

/-- Physical execution may change RAM while retaining every pending invocation
and live handle. Historical entry memory remains historical. -/
theorem WellFormed.physicalFrame {config : Config} {state : State}
    (valid : WellFormed config state) (suspended : Suspend.State) (authority : Atomics.State)
    (machine : Suspend.WellFormed suspended) (resources : Atomics.WellFormed authority)
    (pending : suspended.pending = state.suspended.pending)
    (handles : authority.handles = state.authority.handles) :
    WellFormed config { state with suspended := suspended, authority := authority } := by
  refine ⟨machine, resources, ?_, ?_, valid.queue, valid.eligible, valid.pins⟩
  · intro identifier call found
    have current := valid.calls identifier call found
    refine ⟨?_, ?_, current.outcome⟩
    · simpa [pending] using current.saved
    · obtain ⟨registration, registered, keeper, pin, separate, address⟩ := current.registration
      exact ⟨registration, registered, by simpa [Resources.Valid, handles] using keeper,
        by simpa [handles] using pin, separate, by simpa [pending] using address⟩
  · intro worker saved found
    exact valid.pending worker saved (by simpa [pending] using found)

/-- Concrete fresh-entry construction. The existing keeper spans physical
entry and call-pin issuance. No accepted intermediate state loses reservation. -/
def enteredState (config : Config) (state : State) (registration : Resources.Registration)
    (worker : Nat) (request : SyscallRequest) (operation : Op) : State :=
  putCall { state with
    suspended := Suspend.capture state.suspended worker request
    authority := Atomics.install state.authority (registration.callHandle config.serviceActor) }
    state.suspended.nextCall ⟨worker, operation, state.authority.nextHandle, .entered⟩

theorem enteredState_wellFormed {config : Config} {state : State}
    (valid : WellFormed config state) (registration : Resources.Registration)
    (worker : Nat) (selected : TSO.Worker) (request : SyscallRequest) (operation : Op)
    (registered : state.registration = some registration)
    (keeper : Resources.Valid state.authority registration)
    (live : state.suspended.machine.workers[worker]? = some selected)
    (running : selected.returned = false) (empty : selected.buffer = [])
    (noPending : state.suspended.pending worker = none)
    (user : request.user = TSO.sharedState state.suspended.machine selected)
    (continuation : request.continuation = request.user.rip + 2)
    (classified : classify request = .ok operation)
    (address : request.user.registers .rdi = registration.address) :
    WellFormed config (enteredState config state registration worker request operation) := by
  have retained := Resources.retainCall_enabled state.authority registration config.serviceActor valid.authority keeper
  have effects := Resources.retainCall_effect _ _ _ _ valid.authority retained
  have newMachine := valid.suspended.capture live running empty user continuation
  have oldDifferent : ∀ identifier call, state.calls identifier = some call →
      identifier ≠ state.suspended.nextCall := by
    intro identifier call found
    exact Nat.ne_of_lt (valid.allocated found)
  have oldWorker : ∀ identifier call, state.calls identifier = some call → call.worker ≠ worker := by
    intro identifier call found same
    obtain ⟨saved, pending, _⟩ := valid.bound found
    rw [same, noPending] at pending
    cases pending
  have oldPin : ∀ identifier call, state.calls identifier = some call → call.pin ≠ state.authority.nextHandle := by
    intro identifier call found
    obtain ⟨reg, _, _, pin, _, _⟩ := (valid.calls identifier call found).registration
    exact Nat.ne_of_lt (valid.authority.handles _ _ pin).1
  refine ⟨newMachine, effects.1, ?_, ?_, valid.queue, ?_, ?_⟩
  · intro identifier call found
    by_cases fresh : identifier = state.suspended.nextCall
    · subst identifier
      have same : call = ⟨worker, operation, state.authority.nextHandle, .entered⟩ := by
        simpa [enteredState, putCall] using found.symm
      subst call
      refine ⟨⟨⟨state.suspended.nextCall, worker, request⟩, ?_, rfl, rfl, classified⟩,
        ⟨registration, registered, effects.2.1, effects.2.2.1, effects.2.2.2.2.1, ?_⟩, trivial⟩
      · simp [enteredState, putCall, Suspend.capture]
      · intro saved pending
        have same : saved = ⟨state.suspended.nextCall, worker, request⟩ := by
          simpa [enteredState, putCall, Suspend.capture] using pending.symm
        subst saved
        exact address
    · have prior : state.calls identifier = some call := by simpa [enteredState, putCall, fresh] using found
      have current := valid.calls identifier call prior
      refine ⟨?_, ?_, current.outcome⟩
      · obtain ⟨saved, pending, invocation, owner, abi⟩ := current.saved
        exact ⟨saved, by simpa [enteredState, putCall, Suspend.capture, oldWorker identifier call prior] using pending,
          invocation, owner, abi⟩
      · obtain ⟨reg, atReg, liveReg, pin, separate, operand⟩ := current.registration
        have regEq : reg = registration := Option.some.inj (atReg.symm.trans registered)
        subst reg
        refine ⟨registration, registered, effects.2.1, ?_, separate, ?_⟩
        · simpa [enteredState, putCall, Atomics.install, oldPin identifier call prior] using pin
        · intro saved pending
          apply operand saved
          simpa [enteredState, putCall, Suspend.capture, oldWorker identifier call prior] using pending
  · intro query saved pending
    by_cases own : query = worker
    · subst query
      have same : saved = ⟨state.suspended.nextCall, worker, request⟩ := by
        simpa [enteredState, putCall, Suspend.capture] using pending.symm
      subst saved
      exact ⟨⟨worker, operation, state.authority.nextHandle, .entered⟩, by simp [enteredState, putCall], rfl⟩
    · have prior : state.suspended.pending query = some saved := by
        simpa [enteredState, putCall, Suspend.capture, own] using pending
      obtain ⟨call, atCall, owner⟩ := valid.pending query saved prior
      exact ⟨call, by simpa [enteredState, putCall, oldDifferent _ call atCall] using atCall, owner⟩
  · intro identifier
    by_cases fresh : identifier = state.suspended.nextCall
    · subst identifier
      have absent : state.suspended.nextCall ∉ state.queue := by
        intro member
        obtain ⟨call, found, _⟩ := (valid.eligible _).mp member
        exact oldDifferent _ _ found rfl
      simp only [enteredState, putCall, ↓reduceIte]
      constructor
      · exact fun member => (absent member).elim
      · rintro ⟨call, found, queued⟩
        have same := Option.some.inj found
        subst call
        obtain ⟨w, expected, pin, equal⟩ := queued
        cases equal
    · simpa [enteredState, putCall, fresh] using valid.eligible identifier
  · intro left a right b first second equal
    by_cases freshLeft : left = state.suspended.nextCall
    · subst left
      have same : a = ⟨worker, operation, state.authority.nextHandle, .entered⟩ := by
        simpa [enteredState, putCall] using first.symm
      subst a
      by_cases freshRight : right = state.suspended.nextCall
      · exact freshRight.symm
      · have old : state.calls right = some b := by simpa [enteredState, putCall, freshRight] using second
        exact False.elim (oldPin right b old equal.symm)
    · have oldLeft : state.calls left = some a := by simpa [enteredState, putCall, freshLeft] using first
      by_cases freshRight : right = state.suspended.nextCall
      · subst right
        have same : b = ⟨worker, operation, state.authority.nextHandle, .entered⟩ := by
          simpa [enteredState, putCall] using second.symm
        subst b
        exact False.elim (oldPin left a oldLeft equal)
      · have oldRight : state.calls right = some b := by simpa [enteredState, putCall, freshRight] using second
        exact valid.pins _ _ _ _ oldLeft oldRight equal

end EDSL.OS.Futex
