/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Publication
import EDSL.OS.Futex.ServiceFrames

set_option warningAsError true

namespace EDSL.OS.Futex.Notification
open X86

/-! Notification safety for the existing private WAIT/WAKE1 service. All
predicates describe current records or current resource RAM. No scheduling
progress, successful future service, acquisition right or truth of a user
predicate follows from a zero WAIT result. Physical client preservation and
artifact binding are separate from this service-level composition layer. -/

/-- The designated worker has no currently queued WAIT invocation. Ready,
entered, resumed and absent calls are not classified as queued. -/
def NoQueuedWait (state : State) (worker : Nat) : Prop :=
  ∀ identifier call, state.calls identifier = some call → call.worker = worker → ¬ Queued call

/-- Every current WAIT of this worker compares the declared expected value.
Other workers and WAKE records are unrestricted. -/
def ExpectedFor (state : State) (worker : Nat) (expected : BitVec 32) : Prop :=
  ∀ identifier call observed, state.calls identifier = some call → call.worker = worker →
    call.op = .wait observed → observed = expected

/-- All current WAIT records belong to one designated worker. This structural
restriction and the service invariant derive the sole eligible waiter; no
queue shape or successful future wake is assumed. -/
def OnlyWaiter (state : State) (worker : Nat) : Prop :=
  ∀ identifier call expected, state.calls identifier = some call → call.op = .wait expected →
    call.worker = worker

/-- The exact registration and current managed RAM word, rather than a word
copied from a syscall's earlier capture snapshot. -/
structure CurrentWord (state : State) (registration : Resources.Registration)
    (value : BitVec 32) : Prop where
  registered : state.registration = some registration
  read : loadDWord (AddressSpace.toMemory state.authority.shared.resources.space)
    registration.address = .ok value

/-- Service actions retain the identity, worker, operation and pin of every
surviving call. Its phase may change or its entire record may be consumed. -/
def CallFrame (before after : State) : Prop :=
  ∀ identifier call, after.calls identifier = some call →
    ∃ prior, before.calls identifier = some prior ∧ prior.worker = call.worker ∧
      prior.op = call.op ∧ prior.pin = call.pin

theorem CallFrame.refl (state : State) : CallFrame state state :=
  fun _ call found => ⟨call, found, rfl, rfl, rfl⟩

theorem CallFrame.trans {before middle after : State}
    (first : CallFrame before middle) (last : CallFrame middle after) : CallFrame before after := by
  intro identifier call found
  obtain ⟨prior, live, worker, operation, pin⟩ := last identifier call found
  obtain ⟨original, initial, worker', operation', pin'⟩ := first identifier prior live
  exact ⟨original, initial, worker'.trans worker, operation'.trans operation, pin'.trans pin⟩

theorem CallFrame.rephase {state : State} {identifier : Nat} {call : Call}
    (found : state.calls identifier = some call) (phase : Phase call.op) :
    CallFrame state (setPhase state identifier call phase) := by
  intro query selected live
  by_cases own : query = identifier
  · subst query
    have same : selected = {call with phase := phase} := by
      simpa [setPhase, putCall] using live.symm
    subst selected
    exact ⟨call, found, rfl, rfl, rfl⟩
  · exact ⟨selected, by simpa [setPhase, putCall, own] using live, rfl, rfl, rfl⟩

theorem ExpectedFor.frame {before after : State} {worker : Nat} {expected : BitVec 32}
    (beforeExpected : ExpectedFor before worker expected) (frame : CallFrame before after) :
    ExpectedFor after worker expected := by
  intro identifier call observed found selected operation
  obtain ⟨prior, live, sameWorker, sameOp, _⟩ := frame identifier call found
  exact beforeExpected identifier prior observed live (sameWorker.trans selected)
    (sameOp.trans operation)

theorem OnlyWaiter.frame {before after : State} {worker : Nat}
    (only : OnlyWaiter before worker) (frame : CallFrame before after) : OnlyWaiter after worker := by
  intro identifier call expected found operation
  obtain ⟨prior, live, sameWorker, sameOp, _⟩ := frame identifier call found
  exact sameWorker.symm.trans (only identifier prior expected live (sameOp.trans operation))

/-- Pure call-map transport is useful for physical steps that do not capture
another invocation. It imposes no equality on private contexts or current RAM. -/
theorem NoQueuedWait.calls {before after : State} {worker : Nat}
    (clear : NoQueuedWait before worker) (same : after.calls = before.calls) :
    NoQueuedWait after worker := by
  intro identifier call found selected
  exact clear identifier call (same ▸ found) selected

theorem NoQueuedWait.rephase {state : State} {worker identifier : Nat} {call : Call}
    (clear : NoQueuedWait state worker) (phase : Phase call.op)
    (safe : call.worker = worker → ¬ Queued {call with phase := phase}) :
    NoQueuedWait (setPhase state identifier call phase) worker := by
  intro query selected live chosen
  by_cases own : query = identifier
  · subst query
    have same : selected = {call with phase := phase} := by
      simpa [setPhase, putCall] using live.symm
    subst selected
    exact safe chosen
  · exact clear query selected (by simpa [setPhase, putCall, own] using live) chosen

/-- A new entered invocation cannot by itself enqueue a worker. This includes
recapture after an earlier invocation was resumed and consumed. -/
theorem NoQueuedWait.put_entered {state : State} {worker identifier owner pin : Nat} {op : Op}
    (clear : NoQueuedWait state worker) :
    NoQueuedWait (putCall state identifier ⟨owner, op, pin, .entered⟩) worker := by
  intro query call found selected
  by_cases own : query = identifier
  · subst query
    have same : call = ⟨owner, op, pin, .entered⟩ := by simpa [putCall] using found.symm
    subst call
    exact queued_entered _ _ _
  · exact clear query call (by simpa [putCall, own] using found) selected

/-- Readability is derived from the current live pin, and actual comparison
produces typed EAGAIN readiness. No future compare-success premise is used. -/
theorem compare_mismatch_enabled {config : Config} {state : State}
    {registration : Resources.Registration} {value expected : BitVec 32}
    {invocation worker pin : Nat} (valid : WellFormed config state)
    (current : CurrentWord state registration value) (different : value ≠ expected)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .entered⟩) :
    compareWait config state invocation = .ok
      (setPhase state invocation ⟨worker, .wait expected, pin, .entered⟩
        (.ready .waitAgain .mismatch)) :=
  compare_current_mismatch valid found current.registered current.read different


/-- Every surviving queued call was already queued, or arose from an actual
current-pin equality comparison. This is a derived effect of service code,
not an admission policy forbidding a bad outcome. -/
def QueueFrame (config : Config) (before after : State) : Prop :=
  ∀ identifier call, after.calls identifier = some call → Queued call →
    (∃ prior, before.calls identifier = some prior ∧ prior.worker = call.worker ∧ Queued prior) ∨
    (∃ owner expected pin,
      before.calls identifier = some ⟨owner, .wait expected, pin, .entered⟩ ∧
      Resources.readPinned before.authority config.serviceActor pin = .ok expected ∧
      owner = call.worker)

private theorem queueFrame_rephase {config : Config} {state : State} {identifier : Nat}
    {call : Call} (phase : Phase call.op) (notQueued : ¬ Queued {call with phase := phase}) :
    QueueFrame config state (setPhase state identifier call phase) := by
  intro query selected live queued
  by_cases own : query = identifier
  · subst query
    have same : selected = {call with phase := phase} := by
      simpa [setPhase, putCall] using live.symm
    exact (notQueued (same ▸ queued)).elim
  · exact .inl ⟨selected, by simpa [setPhase, putCall, own] using live, rfl, queued⟩

private theorem queueFrame_compare {config : Config} {state : State}
    {identifier owner pin : Nat} {expected : BitVec 32}
    (found : state.calls identifier = some ⟨owner, .wait expected, pin, .entered⟩)
    (read : Resources.readPinned state.authority config.serviceActor pin = .ok expected) :
    QueueFrame config state (setPhase state identifier ⟨owner, .wait expected, pin, .entered⟩ .queued) := by
  intro query call live queued
  by_cases own : query = identifier
  · subst query
    have same : call = ⟨owner, .wait expected, pin, .queued⟩ := by
      simpa [setPhase, putCall] using live.symm
    exact .inr ⟨owner, expected, pin, found, read, congrArg Call.worker same.symm⟩
  · exact .inl ⟨call, by simpa [setPhase, putCall, own] using live, rfl, queued⟩

private theorem compare_frames {config : Config} {state after : State} {invocation : Nat}
    (success : compareWait config state invocation = .ok after) :
    CallFrame state after ∧ QueueFrame config state after := by
  cases found : state.calls invocation with
  | none => simp [compareWait, found] at success
  | some call =>
    rcases call with ⟨owner, operation, pin, phase⟩
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
              exact ⟨CallFrame.rephase found _, queueFrame_compare found (equal ▸ read)⟩
            · have present : invocation ∈ state.queue := Classical.not_not.mp absent
              simp [compareWait, found, read, equal, present, Except.mapError] at success
          · simp [compareWait, found, read, equal, Except.mapError] at success
            subst after
            exact ⟨CallFrame.rephase found _, queueFrame_rephase _ (queued_ready _ _ _ _ _)⟩

private theorem retry_frames {config : Config} {state after : State} {invocation : Nat}
    (success : retryQueued state invocation = .ok after) :
    CallFrame state after ∧ QueueFrame config state after := by
  cases found : state.calls invocation with
  | none => simp [retryQueued, found] at success
  | some call =>
    rcases call with ⟨owner, operation, pin, phase⟩
    cases operation with
    | wakeOne => cases phase <;> simp [retryQueued, found] at success
    | wait expected =>
      cases phase with
      | entered => simp [retryQueued, found] at success
      | ready result origin => simp [retryQueued, found] at success
      | queued =>
        simp [retryQueued, found] at success
        subst after
        exact ⟨CallFrame.rephase found _, queueFrame_rephase _ (queued_entered _ _ _)⟩

private theorem spurious_frames {config : Config} {state after : State} {invocation : Nat}
    (success : spuriousReady state invocation = .ok after) :
    CallFrame state after ∧ QueueFrame config state after := by
  cases found : state.calls invocation with
  | none => simp [spuriousReady, found] at success
  | some call =>
    rcases call with ⟨owner, operation, pin, phase⟩
    cases operation with
    | wakeOne => cases phase <;> simp [spuriousReady, found] at success
    | wait expected =>
      cases phase with
      | entered => simp [spuriousReady, found] at success
      | ready result origin => simp [spuriousReady, found] at success
      | queued =>
        simp [spuriousReady, found] at success
        subst after
        exact ⟨CallFrame.rephase found _, queueFrame_rephase _ (queued_ready _ _ _ _ _)⟩

private theorem wake_frames {config : Config} {state after : State} {invocation : Nat}
    {selected : Option Nat} (success : wakeOne state invocation selected = .ok after) :
    CallFrame state after ∧ QueueFrame config state after := by
  cases found : state.calls invocation with
  | none => simp [wakeOne, found] at success
  | some call =>
    rcases call with ⟨owner, operation, pin, phase⟩
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
            exact ⟨CallFrame.rephase found _, queueFrame_rephase _ (queued_ready _ _ _ _ _)⟩
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
                    constructor
                    · exact (CallFrame.rephase waiting _).trans
                        (CallFrame.rephase (by simpa [setPhase, putCall, Ne.symm different] using found) _)
                    · intro query call live queued
                      by_cases own : query = invocation
                      · subst query
                        have same : call = ⟨owner, .wakeOne, pin, .ready .wakeOne (.wake invocation)⟩ := by
                          simpa [setPhase, putCall] using live.symm
                        exact (queued_ready _ _ _ _ _ (same ▸ queued)).elim
                      · by_cases chosen : query = target
                        · subst query
                          have same : call = ⟨waitingWorker, .wait expected, waitingPin,
                              .ready .waitZero (.wake invocation)⟩ := by
                            simpa [setPhase, putCall, different] using live.symm
                          exact (queued_ready _ _ _ _ _ (same ▸ queued)).elim
                        · exact .inl ⟨call, by simpa [setPhase, putCall, own, chosen] using live, rfl, queued⟩
            · simp [wakeOne, found, different, member] at success
          · have same : target = invocation := Classical.not_not.mp different
            simp [wakeOne, found, same] at success

/-- Exact service execution preserves call cores; the only possible new queue
entry comes from that action's actual equal current-resource comparison. -/
theorem service_frames {config : Config} {state after : State} {action : Action}
    (success : step config state action = .ok after) :
    CallFrame state after ∧ QueueFrame config state after := by
  cases action with
  | compare invocation => exact compare_frames success
  | wake invocation selected => exact wake_frames success
  | retry invocation => exact retry_frames success
  | spurious invocation => exact spurious_frames success
  | resume invocation flags rcx r11 =>
    obtain ⟨call, outcome, origin, registration, resumed, closed, found, ready, registered,
      resume, close, same⟩ := resumeReady_effect success
    subst after
    constructor
    · intro query selected live
      by_cases own : query = invocation
      · subst query; simp at live
      · exact ⟨selected, by simpa [own] using live, rfl, rfl, rfl⟩
    · intro query selected live queued
      by_cases own : query = invocation
      · subst query; simp at live
      · exact .inl ⟨selected, by simpa [own] using live, rfl, queued⟩
  | idle =>
    simp [step] at success
    subst after
    exact ⟨CallFrame.refl _, fun _ call found queued => .inl ⟨call, found, rfl, queued⟩⟩


/-- A surviving call's live pin reads the same current word as its exact
registration, independently of the captured syscall RAM. -/
theorem CurrentWord.pinned_read {config : Config} {state : State}
    {registration : Resources.Registration} {value : BitVec 32}
    {identifier : Nat} {call : Call} (current : CurrentWord state registration value)
    (valid : WellFormed config state) (found : state.calls identifier = some call) :
    Resources.readPinned state.authority config.serviceActor call.pin = .ok value := by
  obtain ⟨reg, atReg, _, live, _, _⟩ := (valid.calls _ _ found).registration
  have same := Option.some.inj (atReg.symm.trans current.registered)
  subst reg
  simp [Resources.readPinned, Atomics.authorize, live, Resources.Registration.callHandle,
    current.read, Except.mapError]

theorem ExpectedFor.service {config : Config} {state after : State}
    {action : Action} {worker : Nat} {expected : BitVec 32}
    (expectedFor : ExpectedFor state worker expected)
    (success : step config state action = .ok after) : ExpectedFor after worker expected :=
  expectedFor.frame (service_frames success).1

theorem OnlyWaiter.service {config : Config} {state after : State}
    {action : Action} {worker : Nat} (only : OnlyWaiter state worker)
    (success : step config state action = .ok after) : OnlyWaiter after worker :=
  only.frame (service_frames success).1

/-- Service actions neither replace the registration nor change resource RAM,
including a resume that closes its individual mutable-word pin. -/
theorem CurrentWord.service {config : Config} {state after : State}
    {action : Action} {registration : Resources.Registration} {value : BitVec 32}
    (current : CurrentWord state registration value)
    (success : step config state action = .ok after) : CurrentWord after registration value := by
  have registered : after.registration = state.registration := by
    cases action with
    | compare invocation => exact (compareWait_stutter success).2.2
    | wake invocation target => exact (wakeOne_stutter success).2.2
    | retry invocation => exact (retryQueued_stutter success).2.2
    | spurious invocation => exact (spuriousReady_stutter success).2.2
    | resume invocation flags rcx r11 =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, same⟩ := resumeReady_effect success
      rw [same]
    | idle => simp [step] at success; subst after; rfl
  exact ⟨registered.trans current.registered, by rw [service_shared success]; exact current.read⟩

/-- Once this worker has no queued WAIT, service cannot create one while its
expected value differs from current registered RAM. Retry, spurious readiness,
wake and resume are included; no service/scheduler progress is asserted. -/
theorem service_preserves {config : Config} {state after : State}
    {action : Action} {worker : Nat} {expected value : BitVec 32}
    {registration : Resources.Registration} (valid : WellFormed config state)
    (current : CurrentWord state registration value) (different : value ≠ expected)
    (expectedFor : ExpectedFor state worker expected) (clear : NoQueuedWait state worker)
    (success : step config state action = .ok after) : NoQueuedWait after worker := by
  intro identifier call found selected queued
  rcases (service_frames success).2 identifier call found queued with
    ⟨prior, live, sameWorker, priorQueued⟩ | ⟨owner, compared, pin, entered, read, sameWorker⟩
  · exact clear identifier prior live (sameWorker.trans selected) priorQueued
  · have sameExpected := expectedFor identifier ⟨owner, .wait compared, pin, .entered⟩ compared
      entered (sameWorker.trans selected) rfl
    have observed := current.pinned_read valid entered
    have equal : value = compared := Except.ok.inj (observed.symm.trans read)
    exact different (equal.trans sameExpected)

/-- Arbitrarily many actual service actions preserve the notification safety
contract. The sequence may contain idle steps, retries and spurious returns. -/
theorem schedule_preserves {config : Config} {state after : State}
    {actions : List Action} {worker : Nat} {expected value : BitVec 32}
    {registration : Resources.Registration} (valid : WellFormed config state)
    (current : CurrentWord state registration value) (different : value ≠ expected)
    (expectedFor : ExpectedFor state worker expected) (clear : NoQueuedWait state worker)
    (success : Futex.schedule config state actions = .ok after) :
    WellFormed config after ∧ CurrentWord after registration value ∧
      ExpectedFor after worker expected ∧ NoQueuedWait after worker := by
  induction actions generalizing state with
  | nil =>
    simp [Futex.schedule] at success
    subst after
    exact ⟨valid, current, expectedFor, clear⟩
  | cons action rest ih =>
    cases first : step config state action with
    | error fault => simp [Futex.schedule, first] at success
    | ok middle =>
      have tail : Futex.schedule config middle rest = .ok after := by
        simpa [Futex.schedule, first] using success
      exact ih (valid.service_step first) (current.service first) (expectedFor.service first)
        (service_preserves valid current different expectedFor clear first) tail

/-- An empty eligibility queue excludes a queued record by the actual service
invariant; merely returning from a syscall is not used as a queue observation. -/
theorem noQueuedWait_of_empty {config : Config} {state : State} {worker : Nat}
    (valid : WellFormed config state) (empty : state.queue = []) : NoQueuedWait state worker := by
  intro identifier call found _ queued
  have member := (valid.eligible identifier).mpr ⟨call, found, queued⟩
  simp [empty] at member

private theorem singleton_of_nodup {values : List Nat} {identifier : Nat}
    (nodup : values.Nodup) (member : identifier ∈ values)
    (unique : ∀ query, query ∈ values → query = identifier) : values = [identifier] := by
  cases values with
  | nil => cases member
  | cons head tail =>
    have headEq := unique head (by simp)
    have empty : tail = [] := by
      cases tail with
      | nil => rfl
      | cons next rest =>
        have nextEq := unique next (by simp)
        have absent := (List.nodup_cons.mp nodup).1
        exact (absent (by simp [headEq, nextEq])).elim
    simp [headEq, empty]

/-- One physical worker cannot own two current invocations. Consequently all
WAIT records belonging to that worker derive a singleton nonempty queue. -/
theorem OnlyWaiter.queue_singleton {config : Config} {state : State} {worker identifier : Nat}
    (only : OnlyWaiter state worker) (valid : WellFormed config state)
    (member : identifier ∈ state.queue) : state.queue = [identifier] := by
  obtain ⟨call, found, owner, expected, pin, same⟩ := (valid.eligible identifier).mp member
  subst call
  apply singleton_of_nodup valid.queue member
  intro query queued
  obtain ⟨call, live, selected, observed, handle, same⟩ := (valid.eligible query).mp queued
  subst call
  exact valid.same_worker live found
    ((only query _ observed live rfl).trans (only identifier _ expected found rfl).symm)

/-- Any successful WAKE1 clears eligibility under the structural one-worker
WAIT policy. Empty wake and any eligible selection are both covered. The word
value is intentionally absent: a wake alone does not prove publication. -/
theorem wake_queue_empty {config : Config} {state after : State} {worker invocation : Nat}
    {selected : Option Nat} (valid : WellFormed config state) (only : OnlyWaiter state worker)
    (success : wakeOne state invocation selected = .ok after) : after.queue = [] := by
  cases found : state.calls invocation with
  | none => simp [wakeOne, found] at success
  | some call =>
    rcases call with ⟨owner, operation, pin, phase⟩
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
            exact empty
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
                    simp [only.queue_singleton valid member]
            · simp [wakeOne, found, different, member] at success
          · have same : target = invocation := Classical.not_not.mp different
            simp [wakeOne, found, same] at success

/-- A checked wake clears the designated queued WAIT, with no prior
NoQueuedWait premise. Future no-requeue follows separately from current RAM. -/
theorem wake_clears {config : Config} {state after : State} {worker invocation : Nat}
    {selected : Option Nat} (valid : WellFormed config state) (only : OnlyWaiter state worker)
    (success : wakeOne state invocation selected = .ok after) : NoQueuedWait after worker :=
  noQueuedWait_of_empty (valid.wake_step success) (wake_queue_empty valid only success)

/-- From an actual entered wake and current single-waiter structure, an empty
or eligible wake choice is positively enabled and leaves no queued WAIT. -/
theorem wake_enabled_clears {config : Config} {state : State} {worker invocation owner pin : Nat}
    (valid : WellFormed config state) (only : OnlyWaiter state worker)
    (found : state.calls invocation = some ⟨owner, .wakeOne, pin, .entered⟩) :
    ∃ selected after, wakeOne state invocation selected = .ok after ∧
      after.queue = [] ∧ NoQueuedWait after worker := by
  cases queue : state.queue with
  | nil =>
    have enabled := wakeOne_empty state invocation owner pin found queue
    exact ⟨none, _, enabled, wake_queue_empty valid only enabled, wake_clears valid only enabled⟩
  | cons first rest =>
    have member : first ∈ state.queue := by simp [queue]
    obtain ⟨after, enabled⟩ := valid.wake_selected_enabled found member
    exact ⟨some first, after, enabled, wake_queue_empty valid only enabled, wake_clears valid only enabled⟩


/-- Surviving call identities, operations and pins are retained through an
arbitrarily long finite service schedule. -/
theorem schedule_callFrame {config : Config} {state after : State} {actions : List Action}
    (success : Futex.schedule config state actions = .ok after) : CallFrame state after := by
  induction actions generalizing state with
  | nil =>
    simp [Futex.schedule] at success
    subst after
    exact CallFrame.refl _
  | cons action rest ih =>
    cases first : step config state action with
    | error fault => simp [Futex.schedule, first] at success
    | ok middle =>
      have tail : Futex.schedule config middle rest = .ok after := by
        simpa [Futex.schedule, first] using success
      exact (service_frames first).1.trans (ih tail)

theorem ExpectedFor.schedule {config : Config} {state after : State}
    {actions : List Action} {worker : Nat} {expected : BitVec 32}
    (expectedFor : ExpectedFor state worker expected)
    (success : Futex.schedule config state actions = .ok after) : ExpectedFor after worker expected :=
  expectedFor.frame (schedule_callFrame success)

theorem OnlyWaiter.schedule {config : Config} {state after : State}
    {actions : List Action} {worker : Nat} (only : OnlyWaiter state worker)
    (success : Futex.schedule config state actions = .ok after) : OnlyWaiter after worker :=
  only.frame (schedule_callFrame success)

theorem CurrentWord.schedule {config : Config} {state after : State}
    {actions : List Action} {registration : Resources.Registration} {value : BitVec 32}
    (current : CurrentWord state registration value)
    (success : Futex.schedule config state actions = .ok after) : CurrentWord after registration value := by
  induction actions generalizing state with
  | nil => simp [Futex.schedule] at success; subst after; exact current
  | cons action rest ih =>
    cases first : step config state action with
    | error fault => simp [Futex.schedule, first] at success
    | ok middle =>
      have tail : Futex.schedule config middle rest = .ok after := by
        simpa [Futex.schedule, first] using success
      exact ih (current.service first) tail

/-- Under the one-worker WAIT policy, clearing that worker clears the entire
eligibility queue. This conclusion is derived from current records. -/
theorem OnlyWaiter.queue_empty {config : Config} {state : State} {worker : Nat}
    (only : OnlyWaiter state worker) (valid : WellFormed config state)
    (clear : NoQueuedWait state worker) : state.queue = [] := by
  cases queue : state.queue with
  | nil => rfl
  | cons identifier rest =>
    have member : identifier ∈ state.queue := by simp [queue]
    obtain ⟨call, found, owner, expected, pin, same⟩ := (valid.eligible identifier).mp member
    subst call
    exact (clear identifier _ found (only identifier _ expected found rfl)
      (queued_queued _ _ _)).elim

/-- Trace-wide notification safety: arbitrary service actions may occur after
publication and before WAKE1, including a previously queued WAIT. The actual
wake clears the queue; any later service schedule cannot queue it again while
current RAM continues to differ from the declared expected value. The finite prefix, wake and suffix supply actual execution evidence; current
admission requires no empty queue, ready call or future-progress promise. -/
theorem wake_then_schedule {config : Config} {state beforeWake afterWake final : State}
    {beforeActions afterActions : List Action} {worker invocation : Nat} {selected : Option Nat}
    {expected value : BitVec 32} {registration : Resources.Registration}
    (valid : WellFormed config state) (current : CurrentWord state registration value)
    (different : value ≠ expected) (expectedFor : ExpectedFor state worker expected)
    (only : OnlyWaiter state worker)
    (before : Futex.schedule config state beforeActions = .ok beforeWake)
    (wake : wakeOne beforeWake invocation selected = .ok afterWake)
    (after : Futex.schedule config afterWake afterActions = .ok final) :
    WellFormed config final ∧ CurrentWord final registration value ∧
      ExpectedFor final worker expected ∧ NoQueuedWait final worker ∧ final.queue = [] := by
  have validBefore := valid.schedule before
  have currentBefore := current.schedule before
  have expectedBefore := expectedFor.schedule before
  have onlyBefore := only.schedule before
  have actual : step config beforeWake (.wake invocation selected) = .ok afterWake := wake
  have onlyAfter := onlyBefore.service actual
  obtain ⟨validFinal, currentFinal, expectedFinal, clearFinal⟩ := schedule_preserves
    (validBefore.wake_step wake) (currentBefore.service actual) different
    (expectedBefore.service actual) (wake_clears validBefore onlyBefore wake) after
  exact ⟨validFinal, currentFinal, expectedFinal, clearFinal,
    (onlyAfter.schedule after).queue_empty validFinal clearFinal⟩

end EDSL.OS.Futex.Notification
