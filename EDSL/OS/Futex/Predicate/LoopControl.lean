/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Guards
import EDSL.OS.Futex.Predicate.Raw.Control

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86

theorem Point.Known.of_read {address : Word} {memory : Memory} {observed : BitVec 32}
    (domain : loadDWord memory address = .ok 0 ∨ loadDWord memory address = .ok 1)
    (readable : loadDWord memory address = .ok observed) :
    (Point.compare observed).Known address memory := by
  have value : observed = 0 ∨ observed = 1 := by
    rcases domain with zero | one
    · exact Or.inl (Except.ok.inj (readable.symm.trans zero))
    · exact Or.inr (Except.ok.inj (readable.symm.trans one))
  intro query same
  have equal : observed = query := Option.some.inj same
  subst query
  exact ⟨value, fun one => by simpa [one] using readable⟩

/-- The successor's signal knowledge is tied to the actual operand read and
actual instruction equations. It is not inferred from an opaque post-control
witness and does not require a stale zero to equal the current word. -/
theorem ordinary_known_next {address : Word} {client : Client} {point : Point}
    {context : Threads.Context} {memory : Memory}
    (current : Running client point context) (known : point.Known address memory)
    (wordAddress : client.entry.registers .rdi = address)
    (domain : loadDWord memory address = .ok 0 ∨ loadDWord memory address = .ok 1)
    (ready : Ready client point memory) (notCall : point ≠ .syscall)
    (notReturn : ∀ observed, point ≠ .done observed) :
    ∃ next after, executeInstruction (MachineThreads.contextState context memory) point.instruction =
      .ok (.next (MachineThreads.contextState after memory)) ∧
      Running client next after ∧ next.Known address memory := by
  cases point with
  | load =>
    obtain ⟨_, observed, readable⟩ := ready
    rw [wordAddress] at readable
    exact ⟨.compare observed, context.loaded observed,
      execute_load context memory observed (by rw [current.rdi, wordAddress]; exact readable),
      current.load_next observed, Point.Known.of_read domain readable⟩
  | compare observed =>
    exact ⟨.branch observed, cmpContext context, execute_cmp context memory,
      current.compare_next, known⟩
  | branch observed =>
    by_cases zero : observed = 0
    · subst observed
      have zf : context.flags.getLsbD 6 = true := by simpa using current.fields.2
      exact ⟨.number, branchContext context (context.rip + 2),
        execute_jnz_fallthrough context memory 0x16 zf, current.branch_zero,
        by simp [Point.Known, Point.Observed]⟩
    · have zf : context.flags.getLsbD 6 = false := by
        have bits := current.fields.2
        rw [beq_eq_false_iff_ne.mpr zero] at bits
        exact bits
      have executed := execute_jnz_taken context memory 0x16 zf
        (by rw [branch_done_target current]; exact ready zero)
      rw [branch_done_target current] at executed
      exact ⟨.done observed, branchContext context (client.entry.rip + 29),
        executed, current.branch_nonzero zero, known⟩
  | number =>
    exact ⟨.operation, movContext context .rax 202, execute_mov .., current.number_next,
      by simp [Point.Known, Point.Observed]⟩
  | operation =>
    exact ⟨.syscall, movContext context .rsi 128, execute_mov .., current.operation_next,
      by simp [Point.Known, Point.Observed]⟩
  | syscall => exact (notCall rfl).elim
  | resumed raw =>
    exact ⟨.retryCompare, movContext context .rax 1, execute_mov .., current.resumed_next,
      by simp [Point.Known, Point.Observed]⟩
  | retryCompare =>
    exact ⟨.retryBranch, cmpContext context, execute_cmp .., current.retryCompare_next,
      by simp [Point.Known, Point.Observed]⟩
  | retryBranch =>
    have executed := execute_jnz_taken context memory 0xe3 current.fields.2.2
      (by rw [branch_retry_target current]; exact ready)
    rw [branch_retry_target current] at executed
    exact ⟨.load, branchContext context client.entry.rip, executed, current.retryBranch_next,
      by simp [Point.Known, Point.Observed]⟩
  | done observed => exact (notReturn observed rfl).elim

theorem LoopControl.of_pending {address : Word} {client : Client} {worker : Nat}
    {state : Suspend.State} {actual : TSO.Worker} {saved : Suspend.Saved}
    (raw : WorkerControl client worker state actual)
    (pending : state.pending worker = some saved) : LoopControl address client worker state actual := by
  cases raw with
  | running _ _ _ free _ => simp [free] at pending
  | returned _ _ _ _ _ free _ => simp [free] at pending
  | entered captured found owner family context live empty =>
    exact .entered captured found owner family context live empty

/-- Any successful actual selected loop issue preserves its enriched current
control. LOAD creates its snapshot knowledge from real current RAM. -/
theorem LoopControl.issue_selected {address : Word} {client : Client}
    {state after : Suspend.State} {worker : Nat} {before : TSO.Worker}
    {observation : Suspend.Observation}
    (control : LoopControl address client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (wordAddress : client.entry.registers .rdi = address)
    (domain : loadDWord state.machine.memory address = .ok 0 ∨
      loadDWord state.machine.memory address = .ok 1)
    (ready : ∀ point, Running client point before.context → Ready client point state.machine.memory)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    ∃ selected, after.machine.workers[worker]? = some selected ∧
      LoopControl address client worker after selected := by
  cases control with
  | entered saved pending owner family context live empty =>
    have enabled := parked_enabled atWorker live pending owner family context empty
    have same := Except.ok.inj (actual.symm.trans enabled.1)
    cases same
    exact ⟨before, atWorker, .entered saved pending owner family context live empty⟩
  | returned _ _ _ _ _ done _ _ => simp [Suspend.issue, atWorker, done] at actual
  | running point current known live free empty =>
    by_cases call : point = .syscall
    · subst point
      obtain ⟨issued, pending, _, _, raw⟩ := syscall_enabled atWorker current live free empty code
      have same := Except.ok.inj (actual.symm.trans issued)
      cases same
      exact ⟨before, atWorker, LoopControl.of_pending raw pending⟩
    · by_cases returned : ∃ observed, point = .done observed
      · obtain ⟨observed, rfl⟩ := returned
        obtain ⟨issued, selected, _, _⟩ := ret_enabled atWorker current live free empty code
          (ready _ current).1 (ready _ current).2
        have same := Except.ok.inj (actual.symm.trans issued)
        cases same
        exact ⟨_, selected, .returned before.context observed current known rfl rfl free rfl⟩
      · obtain ⟨next, context, executed, currentNext, knownNext⟩ :=
          ordinary_known_next current known wordAddress domain (ready _ current) call
            (fun observed same => returned ⟨observed, same⟩)
        have issued := issue_next atWorker current live free empty code (ready _ current) call executed
        have same := Except.ok.inj (actual.symm.trans issued)
        cases same
        exact ⟨⟨context, false, []⟩, List.getElem?_set_self (List.getElem_of_getElem? atWorker).1,
          .running next currentNext knownNext rfl free rfl⟩

/-- Positive raw enabledness uses present read/canonical/stack guards. Its
resulting selected control is enriched independently by actual issue above. -/
theorem LoopControl.enabled {address : Word} {client : Client} {state : Suspend.State}
    {worker : Nat} {before : TSO.Worker} (control : LoopControl address client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (code : CodeAt state.machine.memory client.entry.rip bytes)
    (wordAddress : client.entry.registers .rdi = address)
    (domain : loadDWord state.machine.memory address = .ok 0 ∨
      loadDWord state.machine.memory address = .ok 1)
    (ready : ∀ point, Running client point before.context → Ready client point state.machine.memory) :
    before.returned = true ∨ ∃ after observation selected,
      Suspend.issue state worker = .ok (after, observation) ∧
      after.machine.workers[worker]? = some selected ∧ LoopControl address client worker after selected := by
  rcases control.raw.enabled atWorker code ready with done | ⟨after, observation, _, actual, _, _⟩
  · exact Or.inl done
  · obtain ⟨selected, found, controlled⟩ :=
      control.issue_selected atWorker code wordAddress domain ready actual
    exact Or.inr ⟨after, observation, selected, actual, found, controlled⟩

theorem LoopControl.resume_selected {address : Word} {client : Client}
    {state after : Suspend.State} {worker invocation : Nat} {before : TSO.Worker}
    {raw flags rcx r11 : Word} (control : LoopControl address client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (actual : Suspend.resume state worker invocation raw flags rcx r11 = .ok after) :
    ∃ selected, after.machine.workers[worker]? = some selected ∧
      Running client (.resumed raw) selected.context ∧ LoopControl address client worker after selected := by
  obtain ⟨selected, saved, found, _, pending, identity, _, _, _⟩ :=
    Suspend.resume_ok _ _ _ _ _ _ _ _ actual
  cases Option.some.inj (atWorker.symm.trans found)
  cases control with
  | running _ _ _ _ free _ => simp [free] at pending
  | returned _ _ _ _ _ _ free _ => simp [free] at pending
  | entered captured savedAt owner family _ live empty =>
    cases Option.some.inj (savedAt.symm.trans pending)
    obtain ⟨enabled, selectedAt, current, _, consumed, _, _, _⟩ :=
      resume_enabled atWorker live pending owner family empty raw flags rcx r11
    rw [identity] at enabled
    have same := Except.ok.inj (actual.symm.trans enabled)
    subst after
    exact ⟨_, selectedAt, current, .running (.resumed raw) current
      (by simp [Point.Known, Point.Observed]) rfl consumed rfl⟩

end EDSL.OS.Futex.Predicate

#audit_edsl
