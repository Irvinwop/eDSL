import EDSL.OS.Futex.Predicate.Raw.Steps

namespace EDSL.OS.Futex.Predicate
open X86

theorem WorkerControl.pending_family {client : Client} {state : Suspend.State} {worker : Nat}
    {actual : TSO.Worker} {saved : Suspend.Saved}
    (control : WorkerControl client worker state actual) (pending : state.pending worker = some saved) :
    client.Family saved.request := by
  cases control with
  | running _ _ _ free _ => simp [free] at pending
  | returned _ _ _ _ _ free _ => simp [free] at pending
  | entered captured savedAt _ family _ _ _ =>
    cases Option.some.inj (savedAt.symm.trans pending)
    exact family

theorem current_syscall_family {client : Client} {state : Suspend.State} {worker : Nat}
    {actual : TSO.Worker} (control : WorkerControl client worker state actual)
    (live : actual.returned = false) (free : state.pending worker = none)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (decoded : decodeAt (TSO.sharedState state.machine actual) = .ok .syscall) :
    client.Family ⟨TSO.sharedState state.machine actual, actual.context.rip + 2⟩ := by
  cases control with
  | entered _ pending _ _ _ _ _ => simp [free] at pending
  | returned _ _ _ _ done _ _ => simp [live] at done
  | running point current _ _ _ =>
    have expected := decode_point current code
    have same := Except.ok.inj (expected.symm.trans decoded)
    have phase := Point.syscall_only same
    subst point
    exact ⟨current, rfl⟩

theorem WorkerControl.issue_selected {client : Client} {state after : Suspend.State} {worker : Nat}
    {before : TSO.Worker} {observation : Suspend.Observation}
    (control : WorkerControl client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (ready : ∀ point, Running client point before.context → Ready client point state.machine.memory)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    ∃ selected, after.machine.workers[worker]? = some selected ∧
      WorkerControl client worker after selected := by
  cases control with
  | entered saved pending owner family context live empty =>
    have enabled := parked_enabled atWorker live pending owner family context empty
    have same := Except.ok.inj (actual.symm.trans enabled.1)
    cases same
    exact ⟨before, atWorker, enabled.2⟩
  | returned _ _ _ _ done _ _ => simp [Suspend.issue, atWorker, done] at actual
  | running point current live free empty =>
    by_cases call : point = .syscall
    · subst point
      obtain ⟨issued, _, _, _, controlled⟩ := syscall_enabled atWorker current live free empty code
      have same := Except.ok.inj (actual.symm.trans issued)
      cases same
      exact ⟨before, atWorker, controlled⟩
    · by_cases returned : ∃ observed, point = .done observed
      · obtain ⟨observed, rfl⟩ := returned
        obtain ⟨issued, selected, controlled, _⟩ := ret_enabled atWorker current live free empty code
          (ready _ current).1 (ready _ current).2
        have same := Except.ok.inj (actual.symm.trans issued)
        cases same
        exact ⟨_, selected, controlled⟩
      · obtain ⟨_, _, issued, _, selected, controlled⟩ := ordinary_enabled atWorker current live free empty code
          (ready _ current) call (fun observed same => returned ⟨observed, same⟩)
        have same := Except.ok.inj (actual.symm.trans issued)
        cases same
        exact ⟨_, selected, controlled⟩

theorem WorkerControl.enabled {client : Client} {state : Suspend.State} {worker : Nat}
    {before : TSO.Worker} (control : WorkerControl client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (ready : ∀ point, Running client point before.context → Ready client point state.machine.memory) :
    before.returned = true ∨
      ∃ after observation selected,
        Suspend.issue state worker = .ok (after, observation) ∧
        after.machine.workers[worker]? = some selected ∧ WorkerControl client worker after selected ∧
        after.machine.memory = state.machine.memory := by
  cases control with
  | entered saved pending owner family context live empty =>
    have enabled := parked_enabled atWorker live pending owner family context empty
    exact Or.inr ⟨state, .parked worker saved.identifier, before, enabled.1, atWorker, enabled.2, rfl⟩
  | returned _ _ _ _ done _ _ => exact Or.inl done
  | running point current live free empty =>
    apply Or.inr
    by_cases call : point = .syscall
    · subst point
      obtain ⟨issued, _, _, _, controlled⟩ := syscall_enabled atWorker current live free empty code
      exact ⟨_, _, before, issued, atWorker, controlled, rfl⟩
    · by_cases returned : ∃ observed, point = .done observed
      · obtain ⟨observed, rfl⟩ := returned
        obtain ⟨issued, selected, controlled, _⟩ := ret_enabled atWorker current live free empty code
          (ready _ current).1 (ready _ current).2
        exact ⟨_, _, _, issued, selected, controlled, rfl⟩
      · obtain ⟨_, _, issued, _, selected, controlled⟩ := ordinary_enabled atWorker current live free empty code
          (ready _ current) call (fun observed same => returned ⟨observed, same⟩)
        exact ⟨_, _, _, issued, selected, controlled, rfl⟩

theorem WorkerControl.issue_memory {client : Client} {state after : Suspend.State} {worker : Nat}
    {before : TSO.Worker} {observation : Suspend.Observation}
    (control : WorkerControl client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (ready : ∀ point, Running client point before.context → Ready client point state.machine.memory)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    after.machine.memory = state.machine.memory := by
  rcases control.enabled atWorker code ready with done | ⟨_, _, _, enabled, _, _, memory⟩
  · simp [Suspend.issue, atWorker, done] at actual
  · cases Except.ok.inj (actual.symm.trans enabled)
    exact memory

theorem WorkerControl.resume_selected {client : Client} {state after : Suspend.State}
    {worker invocation : Nat} {before : TSO.Worker} {raw flags rcx r11 : Word}
    (control : WorkerControl client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (actual : Suspend.resume state worker invocation raw flags rcx r11 = .ok after) :
    ∃ selected, after.machine.workers[worker]? = some selected ∧
      Running client (.resumed raw) selected.context ∧ WorkerControl client worker after selected := by
  obtain ⟨selected, saved, found, _, pending, identity, _, _, _⟩ :=
    Suspend.resume_ok _ _ _ _ _ _ _ _ actual
  cases Option.some.inj (atWorker.symm.trans found)
  have family := control.pending_family pending
  cases control with
  | running _ _ _ free _ => simp [free] at pending
  | returned _ _ _ _ _ free _ => simp [free] at pending
  | entered captured savedAt owner _ _ live empty =>
    cases Option.some.inj (savedAt.symm.trans pending)
    obtain ⟨enabled, selectedAt, current, controlled, _⟩ :=
      resume_enabled atWorker live pending owner family empty raw flags rcx r11
    rw [identity] at enabled
    have same := Except.ok.inj (actual.symm.trans enabled)
    subst after
    exact ⟨_, selectedAt, current, controlled⟩

theorem WorkerControl.empty {client : Client} {state : Suspend.State} {worker : Nat}
    {actual : TSO.Worker} (control : WorkerControl client worker state actual) : actual.buffer = [] := by
  cases control with
  | running _ _ _ _ empty | entered _ _ _ _ _ _ empty | returned _ _ _ _ _ _ empty => exact empty

theorem WorkerControl.drain_impossible {client : Client} {state : Suspend.State} {worker : Nat}
    {actual : TSO.Worker} (control : WorkerControl client worker state actual)
    (atWorker : state.machine.workers[worker]? = some actual) :
    Suspend.drain state worker = .error (.underlying .emptyBuffer) := by
  simp [Suspend.drain, TSO.drain, atWorker, control.empty, Except.mapError]

theorem issue_pending_peer {state after : Suspend.State} {worker peer : Nat}
    {observation : Suspend.Observation} (different : peer ≠ worker)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    after.pending peer = state.pending peer := by
  cases Suspend.issue_effect _ _ _ actual with
  | entered => simp [Suspend.capture, different]
  | parked => rfl
  | machine => rfl

theorem issue_peer_frame {state after : Suspend.State} {worker peer : Nat}
    {observation : Suspend.Observation} (different : peer ≠ worker)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    after.machine.workers[peer]? = state.machine.workers[peer]? ∧
      after.pending peer = state.pending peer :=
  ⟨Suspend.issue_peer different.symm actual, issue_pending_peer different actual⟩

end EDSL.OS.Futex.Predicate
