/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.History

namespace EDSL.OS.Futex
open X86 AddressSpace

/-- Once the current pinned word differs, a retrying/entered WAIT cannot queue.
This reads current resources, whose coupling to physical RAM is separate. -/
theorem compare_current_mismatch {config : Config} {state : State}
    (valid : WellFormed config state) {invocation worker pin : Nat}
    {expected current : BitVec 32} {registration : Resources.Registration}
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .entered⟩)
    (registered : state.registration = some registration)
    (read : loadDWord (toMemory state.authority.shared.resources.space) registration.address = .ok current)
    (different : current ≠ expected) :
    compareWait config state invocation = .ok
      (setPhase state invocation ⟨worker, .wait expected, pin, .entered⟩ (.ready .waitAgain .mismatch)) := by
  obtain ⟨reg, atReg, _, live, _, _⟩ := (valid.calls _ _ found).registration
  have same := Option.some.inj (atReg.symm.trans registered)
  subst reg
  have pinned : Resources.readPinned state.authority config.serviceActor pin = .ok current := by
    simp [Resources.readPinned, Atomics.authorize, live, Resources.Registration.callHandle, read, Except.mapError]
  exact compareWait_mismatch _ _ _ _ _ _ _ found pinned different

/-- WAKE1 removes the selected sole waiter and readies it. There is no future
wake credit, ownership transfer or word mutation in this transition. -/
theorem sole_waiter_woken (state : State) (waker waiter worker pin waitingWorker waitingPin : Nat)
    (expected : BitVec 32)
    (entered : state.calls waker = some ⟨worker, .wakeOne, pin, .entered⟩)
    (queued : state.calls waiter = some ⟨waitingWorker, .wait expected, waitingPin, .queued⟩)
    (distinct : waiter ≠ waker) (sole : state.queue = [waiter]) :
    ∃ after, wakeOne state waker (some waiter) = .ok after ∧
      after.queue = [] ∧
      after.calls waiter = some ⟨waitingWorker, .wait expected, waitingPin, .ready .waitZero (.wake waker)⟩ ∧
      after.calls waker = some ⟨worker, .wakeOne, pin, .ready .wakeOne (.wake waker)⟩ ∧
      after.authority = state.authority ∧ after.suspended = state.suspended := by
  have member : waiter ∈ state.queue := by simp [sole]
  refine ⟨_, wakeOne_selected _ _ _ _ _ _ _ _ entered queued distinct member, ?_, ?_, ?_, rfl, rfl⟩
  · simp [sole]
  · simp [setPhase, putCall, distinct]
  · simp [setPhase, putCall]

/-- Empty wake has no effect on a later WAIT's readiness. If its predicate
still matches at a later comparison, it queues despite that earlier wake. -/
theorem empty_wake_then_wait (config : Config) (state : State)
    (waker waiter worker pin waitingWorker waitingPin : Nat) (expected : BitVec 32)
    (entered : state.calls waker = some ⟨worker, .wakeOne, pin, .entered⟩)
    (waiting : state.calls waiter = some ⟨waitingWorker, .wait expected, waitingPin, .entered⟩)
    (distinct : waiter ≠ waker) (empty : state.queue = [])
    (read : Resources.readPinned state.authority config.serviceActor waitingPin = .ok expected) :
    ∃ afterWake afterWait, wakeOne state waker none = .ok afterWake ∧
      compareWait config afterWake waiter = .ok afterWait ∧ afterWait.queue = [waiter] ∧
      afterWait.calls waiter = some ⟨waitingWorker, .wait expected, waitingPin, .queued⟩ := by
  let afterWake := setPhase state waker ⟨worker, .wakeOne, pin, .entered⟩ (.ready .wakeZero .emptyWake)
  have found : afterWake.calls waiter = some ⟨waitingWorker, .wait expected, waitingPin, .entered⟩ := by
    simpa [afterWake, setPhase, putCall, distinct] using waiting
  have available := compareWait_equal config afterWake waiter waitingWorker waitingPin expected found read
    (by simp [afterWake, setPhase, putCall, empty])
  exact ⟨afterWake, _, wakeOne_empty _ _ _ _ entered empty, available,
    by simp [afterWake, setPhase, putCall, empty], by simp [setPhase, putCall]⟩

/-- A permitted spurious zero supplies no proof of the user predicate. This
explicitly constructs zero readiness while the compared word is unchanged. -/
theorem spurious_keeps_word (state : State) (invocation worker pin : Nat) (expected : BitVec 32)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .queued⟩) :
    ∃ after, spuriousReady state invocation = .ok after ∧
      after.authority = state.authority ∧ after.suspended = state.suspended ∧
      after.calls invocation = some ⟨worker, .wait expected, pin, .ready .waitZero .spurious⟩ :=
  ⟨_, spuriousReady_enabled _ _ _ _ _ found, rfl, rfl, by simp [setPhase, putCall]⟩

end EDSL.OS.Futex
