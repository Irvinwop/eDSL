/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Service

namespace EDSL.OS.Futex
open X86

/-- Origins make the allowed Linux-profile conclusions explicit. In particular
zero from WAIT may be spurious, while EAGAIN comes only from mismatch. -/
def ReadyValid : {op : Op} → Phase op → Prop
  | _, .entered => True
  | _, .queued => True
  | _, .ready .waitZero (.wake _) => True
  | _, .ready .waitZero .spurious => True
  | _, .ready .waitAgain .mismatch => True
  | _, .ready .wakeZero .emptyWake => True
  | _, .ready .wakeOne (.wake _) => True
  | _, _ => False

/-- Queue membership is exactly service eligibility, not an inference from
word value or a promise that a caller will eventually be scheduled. -/
def Queued (call : Call) : Prop :=
  ∃ worker expected pin, call = ⟨worker, .wait expected, pin, .queued⟩

/-- Current binding to the actual suspended syscall and current live pin.
The request's memory is not related to current physical RAM here. -/
structure CallValid (config : Config) (state : State) (identifier : Nat) (call : Call) : Prop where
  saved : ∃ saved, state.suspended.pending call.worker = some saved ∧
    saved.identifier = identifier ∧ saved.worker = call.worker ∧ classify saved.request = .ok call.op
  registration : ∃ registration, state.registration = some registration ∧
    Resources.Valid state.authority registration ∧
    state.authority.handles call.pin = some (registration.callHandle config.serviceActor) ∧
    call.pin ≠ registration.keeper ∧
    ∀ saved, state.suspended.pending call.worker = some saved →
      saved.request.user.registers .rdi = registration.address
  outcome : ReadyValid call.phase

/-- This service invariant is orthogonal to physical client/FIFO admission.
Every pending syscall is represented and every queued ID denotes a WAIT pin. -/
structure WellFormed (config : Config) (state : State) : Prop where
  suspended : Suspend.WellFormed state.suspended
  authority : Atomics.WellFormed state.authority
  calls : ∀ identifier call, state.calls identifier = some call → CallValid config state identifier call
  pending : ∀ worker saved, state.suspended.pending worker = some saved →
    ∃ call, state.calls saved.identifier = some call ∧ call.worker = worker
  queue : state.queue.Nodup
  eligible : ∀ identifier, identifier ∈ state.queue ↔
    ∃ call, state.calls identifier = some call ∧ Queued call
  pins : ∀ left a right b, state.calls left = some a → state.calls right = some b →
    a.pin = b.pin → left = right

/-- A lighter binding predicate supports physical frames, without assuming
that a just-entered syscall has already received its service record. -/
def Bound (state : State) (identifier : Nat) (call : Call) : Prop :=
  ∃ saved, state.suspended.pending call.worker = some saved ∧ saved.identifier = identifier

theorem WellFormed.bound {config : Config} {state : State} (valid : WellFormed config state)
    {identifier : Nat} {call : Call} (found : state.calls identifier = some call) :
    Bound state identifier call := by
  obtain ⟨saved, pending, current, _⟩ := (valid.calls identifier call found).saved
  exact ⟨saved, pending, current⟩

theorem WellFormed.allocated {config : Config} {state : State} (valid : WellFormed config state)
    {identifier : Nat} {call : Call} (found : state.calls identifier = some call) :
    identifier < state.suspended.nextCall := by
  obtain ⟨saved, pending, current⟩ := valid.bound found
  rw [← current]
  exact (valid.suspended.pending _ _ pending).allocated

theorem WellFormed.no_entered_queue {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat} {op : Op}
    (found : state.calls identifier = some ⟨worker, op, pin, .entered⟩) : identifier ∉ state.queue := by
  intro member
  obtain ⟨call, other, w, expected, p, same⟩ := (valid.eligible identifier).mp member
  have equal := Option.some.inj (found.symm.trans other)
  subst call
  cases op <;> cases equal

/-- Current well-formed pins positively enable the compare operation. -/
theorem WellFormed.compare_enabled {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat} {expected : BitVec 32}
    (found : state.calls identifier = some ⟨worker, .wait expected, pin, .entered⟩) :
    ∃ after, compareWait config state identifier = .ok after := by
  obtain ⟨registration, _, _, live, _, _⟩ := (valid.calls _ _ found).registration
  have authorized : Atomics.authorize state.authority config.serviceActor pin =
      .ok (registration.callHandle config.serviceActor) := by
    simp [Atomics.authorize, live, Resources.Registration.callHandle]
  obtain ⟨current, read, _⟩ := Resources.readPinned_enabled _ _ _ _ valid.authority authorized
  by_cases equal : current = expected
  · subst current
    exact ⟨_, compareWait_equal _ _ _ _ _ _ found read (valid.no_entered_queue found)⟩
  · exact ⟨_, compareWait_mismatch _ _ _ _ _ _ _ found read equal⟩

/-- Each eligible choice is enabled, independently of list order. -/
theorem WellFormed.wake_selected_enabled {config : Config} {state : State}
    (valid : WellFormed config state) {invocation worker pin target : Nat}
    (found : state.calls invocation = some ⟨worker, .wakeOne, pin, .entered⟩)
    (member : target ∈ state.queue) : ∃ after, wakeOne state invocation (some target) = .ok after := by
  obtain ⟨call, waiting, waitingWorker, expected, waitingPin, same⟩ := (valid.eligible target).mp member
  subst call
  have different : target ≠ invocation := by
    intro equal
    subst target
    have impossible := Option.some.inj (waiting.symm.trans found)
    cases impossible
  exact ⟨_, wakeOne_selected _ _ _ _ _ _ _ _ found waiting different member⟩

/-- Ready resumption is available under current guards, including resource
closure, rather than being assumed successful in its theorem contract. -/
theorem WellFormed.resume_enabled {config : Config} {state : State}
    (valid : WellFormed config state) {invocation : Nat} {call : Call}
    {outcome : Outcome call.op} {origin : Origin}
    (found : state.calls invocation = some call) (ready : call.phase = .ready outcome origin)
    (flags rcx r11 : Word) : ∃ after, resumeReady config state invocation flags rcx r11 = .ok after := by
  obtain ⟨saved, pending, current, _⟩ := (valid.calls _ _ found).saved
  obtain ⟨registration, registered, _, live, separate, _⟩ := (valid.calls _ _ found).registration
  obtain ⟨resumed, success⟩ := valid.suspended.resume_enabled pending outcome.raw flags rcx r11
  rw [current] at success
  have closed := Resources.closeCall_enabled state.authority registration config.serviceActor call.pin live separate
  refine ⟨{ state with suspended := resumed
                       authority := {state.authority with handles := fun query => if query = call.pin then none else state.authority.handles query}
                       calls := fun query => if query = invocation then none else state.calls query }, ?_⟩
  simp [resumeReady, found, ready, registered, success, closed, Except.mapError]


theorem CallValid.rephase {config : Config} {state : State} {identifier : Nat} {call : Call}
    (valid : CallValid config state identifier call) (phase : Phase call.op)
    (outcome : ReadyValid phase) :
    CallValid config state identifier { call with phase := phase } :=
  ⟨valid.saved, valid.registration, outcome⟩

/-- Generic checked phase replacement. The membership premise specifies the
new eligibility set; all syscall bindings, pins and unrelated calls are framed. -/
theorem WellFormed.rephase {config : Config} {state : State} (valid : WellFormed config state)
    {identifier : Nat} {call : Call} (found : state.calls identifier = some call)
    (phase : Phase call.op) (outcome : ReadyValid phase) (queue : List Nat)
    (nodup : queue.Nodup)
    (members : ∀ query, query ∈ queue ↔
      (query = identifier ∧ Queued { call with phase := phase }) ∨
      (query ≠ identifier ∧ query ∈ state.queue)) :
    WellFormed config { setPhase state identifier call phase with queue := queue } := by
  refine ⟨valid.suspended, valid.authority, ?_, ?_, nodup, ?_, ?_⟩
  · intro query selected live
    by_cases own : query = identifier
    · subst query
      have same : selected = {call with phase := phase} := by
        simpa [setPhase, putCall] using live.symm
      subst selected
      have base := (valid.calls identifier call found).rephase phase outcome
      exact ⟨base.saved, base.registration, base.outcome⟩
    · have prior : state.calls query = some selected := by
        simpa [setPhase, putCall, own] using live
      have base := valid.calls query selected prior
      exact ⟨base.saved, base.registration, base.outcome⟩
  · intro worker saved pending
    obtain ⟨selected, live, workerEq⟩ := valid.pending worker saved pending
    by_cases own : saved.identifier = identifier
    · have same := Option.some.inj ((own ▸ live).symm.trans found)
      subst selected
      exact ⟨{call with phase := phase}, by simp [setPhase, putCall, own], workerEq⟩
    · exact ⟨selected, by simpa [setPhase, putCall, own] using live, workerEq⟩
  · intro query
    rw [members]
    by_cases own : query = identifier
    · subst query
      simp [setPhase, putCall]
    · simp only [own, false_and, false_or]
      simpa [setPhase, putCall, own] using valid.eligible query
  · intro left a right b first second equal
    by_cases ownLeft : left = identifier
    · subst left
      have same : a = {call with phase := phase} := by simpa [setPhase, putCall] using first.symm
      subst a
      by_cases ownRight : right = identifier
      · exact ownRight.symm
      · have prior : state.calls right = some b := by simpa [setPhase, putCall, ownRight] using second
        exact valid.pins _ call _ b found prior equal
    · have priorLeft : state.calls left = some a := by simpa [setPhase, putCall, ownLeft] using first
      by_cases ownRight : right = identifier
      · subst right
        have same : b = {call with phase := phase} := by simpa [setPhase, putCall] using second.symm
        subst b
        exact valid.pins _ a _ call priorLeft found equal
      · have priorRight : state.calls right = some b := by simpa [setPhase, putCall, ownRight] using second
        exact valid.pins _ a _ b priorLeft priorRight equal

@[simp] theorem queued_entered (worker pin : Nat) (op : Op) :
    ¬ Queued ⟨worker, op, pin, .entered⟩ := by
  rintro ⟨w, expected, p, same⟩
  cases op <;> cases same

@[simp] theorem queued_ready (worker pin : Nat) (op : Op) (outcome : Outcome op) (origin : Origin) :
    ¬ Queued ⟨worker, op, pin, .ready outcome origin⟩ := by
  rintro ⟨w, expected, p, same⟩
  cases op <;> cases same

@[simp] theorem queued_queued (worker pin : Nat) (expected : BitVec 32) :
    Queued ⟨worker, .wait expected, pin, .queued⟩ := ⟨worker, expected, pin, rfl⟩

/-- Removing an invocation from eligibility keeps its resource pin and exact
pending syscall; this helper covers retry, spurious and explicit waking. -/
theorem WellFormed.removeQueued {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat} {expected : BitVec 32}
    (found : state.calls identifier = some ⟨worker, .wait expected, pin, .queued⟩)
    (phase : Phase (.wait expected)) (outcome : ReadyValid phase)
    (notQueued : ¬ Queued ⟨worker, .wait expected, pin, phase⟩) :
    WellFormed config
      { setPhase state identifier ⟨worker, .wait expected, pin, .queued⟩ phase with
        queue := state.queue.filter (fun query => query != identifier) } := by
  apply valid.rephase found phase outcome _ (valid.queue.filter _)
  intro query
  simp only [List.mem_filter, bne_iff_ne]
  constructor
  · rintro ⟨member, separate⟩
    exact .inr ⟨separate, member⟩
  · rintro (⟨_, queued⟩ | ⟨separate, member⟩)
    · exact (notQueued queued).elim
    · exact ⟨member, separate⟩

theorem WellFormed.retry {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat} {expected : BitVec 32}
    (found : state.calls identifier = some ⟨worker, .wait expected, pin, .queued⟩) :
    WellFormed config
      { setPhase state identifier ⟨worker, .wait expected, pin, .queued⟩ .entered with
        queue := state.queue.filter (fun query => query != identifier) } :=
  valid.removeQueued found .entered trivial (queued_entered _ _ _)

theorem WellFormed.spurious {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat} {expected : BitVec 32}
    (found : state.calls identifier = some ⟨worker, .wait expected, pin, .queued⟩) :
    WellFormed config
      { setPhase state identifier ⟨worker, .wait expected, pin, .queued⟩ (.ready .waitZero .spurious) with
        queue := state.queue.filter (fun query => query != identifier) } :=
  valid.removeQueued found _ trivial (queued_ready _ _ _ _ _)


theorem WellFormed.notQueued {config : Config} {state : State} (valid : WellFormed config state)
    {identifier : Nat} {call : Call} (found : state.calls identifier = some call)
    (notQueued : ¬ Queued call) : identifier ∉ state.queue := by
  intro member
  obtain ⟨other, live, queued⟩ := (valid.eligible identifier).mp member
  have same := Option.some.inj (found.symm.trans live)
  subst other
  exact notQueued queued

theorem WellFormed.keepQueue {config : Config} {state : State} (valid : WellFormed config state)
    {identifier : Nat} {call : Call} (found : state.calls identifier = some call)
    (before : ¬ Queued call) (phase : Phase call.op) (outcome : ReadyValid phase)
    (after : ¬ Queued {call with phase := phase}) :
    WellFormed config (setPhase state identifier call phase) := by
  have absent := valid.notQueued found before
  apply valid.rephase found phase outcome state.queue valid.queue
  intro query
  by_cases own : query = identifier
  · subst query
    simp [absent, after]
  · simp [own]

theorem WellFormed.compare_equal {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat} {expected : BitVec 32}
    (found : state.calls identifier = some ⟨worker, .wait expected, pin, .entered⟩) :
    WellFormed config
      { setPhase state identifier ⟨worker, .wait expected, pin, .entered⟩ .queued with
        queue := state.queue ++ [identifier] } := by
  have absent := valid.no_entered_queue found
  apply valid.rephase found .queued trivial _
  · apply List.nodup_append.mpr
    exact ⟨valid.queue, by simp, by
      intro a member b singleton
      have same : b = identifier := by simpa using singleton
      subst b
      intro equal
      exact absent (equal ▸ member)⟩
  · intro query
    simp only [List.mem_append, List.mem_singleton, queued_queued, and_true]
    constructor
    · rintro (member | own)
      · exact .inr ⟨fun equal => absent (equal ▸ member), member⟩
      · exact .inl own
    · rintro (own | ⟨_, member⟩)
      · exact .inr own
      · exact .inl member

theorem WellFormed.compare_mismatch {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat} {expected : BitVec 32}
    (found : state.calls identifier = some ⟨worker, .wait expected, pin, .entered⟩) :
    WellFormed config
      (setPhase state identifier ⟨worker, .wait expected, pin, .entered⟩ (.ready .waitAgain .mismatch)) :=
  valid.keepQueue found (queued_entered _ _ _) _ trivial (queued_ready _ _ _ _ _)

theorem WellFormed.wake_empty {config : Config} {state : State} (valid : WellFormed config state)
    {identifier worker pin : Nat}
    (found : state.calls identifier = some ⟨worker, .wakeOne, pin, .entered⟩) :
    WellFormed config
      (setPhase state identifier ⟨worker, .wakeOne, pin, .entered⟩ (.ready .wakeZero .emptyWake)) :=
  valid.keepQueue found (queued_entered _ _ _) _ trivial (queued_ready _ _ _ _ _)

theorem WellFormed.wake_selected {config : Config} {state : State} (valid : WellFormed config state)
    {invocation target worker pin waitingWorker waitingPin : Nat} {expected : BitVec 32}
    (found : state.calls invocation = some ⟨worker, .wakeOne, pin, .entered⟩)
    (waiting : state.calls target = some ⟨waitingWorker, .wait expected, waitingPin, .queued⟩)
    (different : target ≠ invocation) :
    WellFormed config
      { setPhase (setPhase state target ⟨waitingWorker, .wait expected, waitingPin, .queued⟩
          (.ready .waitZero (.wake invocation))) invocation ⟨worker, .wakeOne, pin, .entered⟩
          (.ready .wakeOne (.wake invocation)) with
        queue := state.queue.filter (fun identifier => identifier != target) } := by
  have marked := valid.removeQueued waiting (.ready .waitZero (.wake invocation)) trivial (queued_ready _ _ _ _ _)
  have still : ({ setPhase state target ⟨waitingWorker, .wait expected, waitingPin, .queued⟩
      (.ready .waitZero (.wake invocation)) with queue := state.queue.filter (fun identifier => identifier != target) }).calls invocation =
      some ⟨worker, .wakeOne, pin, .entered⟩ := by
    simpa [setPhase, putCall, Ne.symm different] using found
  exact marked.keepQueue still (queued_entered _ _ _) _ trivial (queued_ready _ _ _ _ _)


theorem WellFormed.compare_step {config : Config} {state after : State}
    (valid : WellFormed config state) {invocation : Nat}
    (success : compareWait config state invocation = .ok after) : WellFormed config after := by
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
              exact valid.compare_equal found
            · have present : invocation ∈ state.queue := Classical.not_not.mp absent
              simp [compareWait, found, read, equal, present, Except.mapError] at success
          · simp [compareWait, found, read, equal, Except.mapError] at success
            subst after
            exact valid.compare_mismatch found

theorem WellFormed.retry_step {config : Config} {state after : State}
    (valid : WellFormed config state) {invocation : Nat}
    (success : retryQueued state invocation = .ok after) : WellFormed config after := by
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
        exact valid.retry found

theorem WellFormed.spurious_step {config : Config} {state after : State}
    (valid : WellFormed config state) {invocation : Nat}
    (success : spuriousReady state invocation = .ok after) : WellFormed config after := by
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
        exact valid.spurious found

theorem WellFormed.wake_step {config : Config} {state after : State}
    (valid : WellFormed config state) {invocation : Nat} {selected : Option Nat}
    (success : wakeOne state invocation selected = .ok after) : WellFormed config after := by
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
            exact valid.wake_empty found
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
                    exact valid.wake_selected found waiting different
            · simp [wakeOne, found, different, member] at success
          · have same : target = invocation := Classical.not_not.mp different
            simp [wakeOne, found, same] at success

end EDSL.OS.Futex
