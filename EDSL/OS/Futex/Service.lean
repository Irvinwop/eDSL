/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Model

namespace EDSL.OS.Futex
open X86

/-- Current-RAM comparison and queue insertion form one service action. There
is no interval in which an equal comparison has occurred but insertion has not. -/
def compareWait (config : Config) (state : State) (invocation : Nat) : Except Fault State := do
  let some call := state.calls invocation | throw .missingCall
  match call with
  | ⟨worker, .wait expected, pin, .entered⟩ =>
    let current ← (Resources.readPinned state.authority config.serviceActor pin).mapError Fault.resources
    if current = expected then
      if invocation ∈ state.queue then throw .ineligible
      return { setPhase state invocation ⟨worker, .wait expected, pin, .entered⟩ .queued with
        queue := state.queue ++ [invocation] }
    else
      return setPhase state invocation ⟨worker, .wait expected, pin, .entered⟩
        (.ready .waitAgain .mismatch)
  | _ => throw .wrongPhase

/-- Choice is an explicit eligible invocation, never a FIFO convention. None
means an empty wake: it creates no credit that a later WAIT could consume. -/
def wakeOne (state : State) (invocation : Nat) (selected : Option Nat) : Except Fault State := do
  let some call := state.calls invocation | throw .missingCall
  match call with
  | ⟨worker, .wakeOne, pin, .entered⟩ =>
    match selected with
    | none =>
      if state.queue ≠ [] then throw .queueNotEmpty
      return setPhase state invocation ⟨worker, .wakeOne, pin, .entered⟩ (.ready .wakeZero .emptyWake)
    | some target =>
      if target = invocation then throw .ineligible
      if target ∉ state.queue then throw .ineligible
      let some waiter := state.calls target | throw .missingCall
      match waiter with
      | ⟨waitingWorker, .wait expected, waitingPin, .queued⟩ =>
        let marked := setPhase state target ⟨waitingWorker, .wait expected, waitingPin, .queued⟩
          (.ready .waitZero (.wake invocation))
        return { setPhase marked invocation ⟨worker, .wakeOne, pin, .entered⟩
          (.ready .wakeOne (.wake invocation)) with
          queue := state.queue.filter (fun identifier => identifier != target) }
      | _ => throw .wrongPhase
  | _ => throw .wrongPhase

/-- A modeled kernel retry retains the exact invocation and pin, and must
perform a fresh current-RAM comparison before queueing again. -/
def retryQueued (state : State) (invocation : Nat) : Except Fault State := do
  let some call := state.calls invocation | throw .missingCall
  match call with
  | ⟨worker, .wait expected, pin, .queued⟩ =>
    return { setPhase state invocation ⟨worker, .wait expected, pin, .queued⟩ .entered with
      queue := state.queue.filter (fun identifier => identifier != invocation) }
  | _ => throw .wrongPhase

/-- Zero from WAIT does not establish predicate truth or mutex acquisition.
The service explicitly permits a spurious return without a write or wake. -/
def spuriousReady (state : State) (invocation : Nat) : Except Fault State := do
  let some call := state.calls invocation | throw .missingCall
  match call with
  | ⟨worker, .wait expected, pin, .queued⟩ =>
    return { setPhase state invocation ⟨worker, .wait expected, pin, .queued⟩
      (.ready .waitZero .spurious) with
      queue := state.queue.filter (fun identifier => identifier != invocation) }
  | _ => throw .wrongPhase

/-- RAX is derived solely from the stored operation-specific outcome. The
actual Suspend resume supplies current RAM internally. Pin closure and record
consumption are part of the same pure transition; errors expose no partial state. -/
def resumeReady (config : Config) (state : State) (invocation : Nat)
    (flags rcx r11 : Word) : Except Fault State := do
  let some call := state.calls invocation | throw .missingCall
  match call.phase with
  | .ready outcome _ =>
    let some registration := state.registration | throw .unregistered
    let resumed ← (Suspend.resume state.suspended call.worker invocation outcome.raw flags rcx r11).mapError Fault.suspended
    let closed ← (Resources.closeCall state.authority registration config.serviceActor call.pin).mapError Fault.resources
    return { state with suspended := resumed
                        authority := closed
                        calls := fun query => if query = invocation then none else state.calls query }
  | _ => throw .wrongPhase

inductive Action where
  | compare (invocation : Nat)
  | wake (invocation : Nat) (selected : Option Nat)
  | retry (invocation : Nat)
  | spurious (invocation : Nat)
  | resume (invocation : Nat) (flags rcx r11 : Word)
  | idle
  deriving DecidableEq, Repr

def step (config : Config) (state : State) : Action → Except Fault State
  | .compare invocation => compareWait config state invocation
  | .wake invocation selected => wakeOne state invocation selected
  | .retry invocation => retryQueued state invocation
  | .spurious invocation => spuriousReady state invocation
  | .resume invocation flags rcx r11 => resumeReady config state invocation flags rcx r11
  | .idle => .ok state

def schedule (config : Config) (state : State) : List Action → Except Fault State
  | [] => .ok state
  | action :: rest => do
    let after ← step config state action
    schedule config after rest

@[simp] theorem putCall_self (state : State) (identifier : Nat) (call : Call) :
    (putCall state identifier call).calls identifier = some call := by simp [putCall]

@[simp] theorem putCall_peer (state : State) (identifier query : Nat) (call : Call)
    (different : query ≠ identifier) :
    (putCall state identifier call).calls query = state.calls query := by simp [putCall, different]

@[simp] theorem setPhase_suspended (state : State) (identifier : Nat) (call : Call) (phase : Phase call.op) :
    (setPhase state identifier call phase).suspended = state.suspended := rfl

@[simp] theorem setPhase_authority (state : State) (identifier : Nat) (call : Call) (phase : Phase call.op) :
    (setPhase state identifier call phase).authority = state.authority := rfl

@[simp] theorem setPhase_registration (state : State) (identifier : Nat) (call : Call) (phase : Phase call.op) :
    (setPhase state identifier call phase).registration = state.registration := rfl

/-- Positive enabledness for equal comparison, from an actual readable pin. -/
theorem compareWait_equal (config : Config) (state : State) (invocation worker pin : Nat)
    (expected : BitVec 32)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .entered⟩)
    (read : Resources.readPinned state.authority config.serviceActor pin = .ok expected)
    (absent : invocation ∉ state.queue) :
    compareWait config state invocation = .ok
      { setPhase state invocation ⟨worker, .wait expected, pin, .entered⟩ .queued with
        queue := state.queue ++ [invocation] } := by
  simp [compareWait, found, read, absent, Except.mapError]

theorem compareWait_mismatch (config : Config) (state : State) (invocation worker pin : Nat)
    (expected current : BitVec 32)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .entered⟩)
    (read : Resources.readPinned state.authority config.serviceActor pin = .ok current)
    (different : current ≠ expected) :
    compareWait config state invocation = .ok
      (setPhase state invocation ⟨worker, .wait expected, pin, .entered⟩ (.ready .waitAgain .mismatch)) := by
  simp [compareWait, found, read, different, Except.mapError]

theorem wakeOne_empty (state : State) (invocation worker pin : Nat)
    (found : state.calls invocation = some ⟨worker, .wakeOne, pin, .entered⟩)
    (empty : state.queue = []) :
    wakeOne state invocation none = .ok
      (setPhase state invocation ⟨worker, .wakeOne, pin, .entered⟩ (.ready .wakeZero .emptyWake)) := by
  simp [wakeOne, found, empty]

theorem wakeOne_selected (state : State) (invocation target worker pin waitingWorker waitingPin : Nat)
    (expected : BitVec 32)
    (found : state.calls invocation = some ⟨worker, .wakeOne, pin, .entered⟩)
    (waiting : state.calls target = some ⟨waitingWorker, .wait expected, waitingPin, .queued⟩)
    (different : target ≠ invocation) (eligible : target ∈ state.queue) :
    wakeOne state invocation (some target) = .ok
      { setPhase (setPhase state target ⟨waitingWorker, .wait expected, waitingPin, .queued⟩
          (.ready .waitZero (.wake invocation))) invocation ⟨worker, .wakeOne, pin, .entered⟩
          (.ready .wakeOne (.wake invocation)) with
        queue := state.queue.filter (fun identifier => identifier != target) } := by
  simp [wakeOne, found, waiting, different, eligible]

theorem retryQueued_enabled (state : State) (invocation worker pin : Nat) (expected : BitVec 32)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .queued⟩) :
    retryQueued state invocation = .ok
      { setPhase state invocation ⟨worker, .wait expected, pin, .queued⟩ .entered with
        queue := state.queue.filter (fun identifier => identifier != invocation) } := by
  simp [retryQueued, found]

theorem spuriousReady_enabled (state : State) (invocation worker pin : Nat) (expected : BitVec 32)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .queued⟩) :
    spuriousReady state invocation = .ok
      { setPhase state invocation ⟨worker, .wait expected, pin, .queued⟩ (.ready .waitZero .spurious) with
        queue := state.queue.filter (fun identifier => identifier != invocation) } := by
  simp [spuriousReady, found]

end EDSL.OS.Futex
