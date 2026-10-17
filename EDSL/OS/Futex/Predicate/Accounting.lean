/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Completion
import EDSL.OS.Futex.Predicate.Raw.Validation

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate.Accounting
open X86

/-- Modeled user instructions retired by one actual worker. Capturing SYSCALL
retires one instruction. Parked selections, resumption, service, propagation
and idle retire none. This is neither a cycle count nor kernel work. -/
def instructionCost (worker : Nat) : Runtime.Observation → Nat
  | .physical (.machine (.retired selected _)) | .physical (.entered selected _) =>
      if selected = worker then 1 else 0
  | _ => 0

/-- Cost is read from the actual observations of an accepted trace, rather
than counting selections that may be parked or blocked. -/
def retiredInstructions (worker : Nat) (observations : List Runtime.Observation) : Nat :=
  (observations.map (instructionCost worker)).sum

@[simp] theorem retiredInstructions_nil (worker : Nat) : retiredInstructions worker [] = 0 := rfl

@[simp] theorem retiredInstructions_cons (worker : Nat) (first : Runtime.Observation)
    (rest : List Runtime.Observation) :
    retiredInstructions worker (first :: rest) =
      instructionCost worker first + retiredInstructions worker rest := by
  simp [retiredInstructions]

theorem retiredInstructions_append (worker : Nat) (first rest : List Runtime.Observation) :
    retiredInstructions worker (first ++ rest) =
      retiredInstructions worker first + retiredInstructions worker rest := by
  simp [retiredInstructions, List.sum_append]

/-- Current fast-path cuts. The index is the number of this loop's remaining
retirements. In particular, this witness retains the actual current LOAD and
its pending/FIFO state; it is not merely a program-counter label. -/
inductive Cut (client : Client) (worker : Nat) (state : Suspend.State) : Nat → Prop where
  | load (current : Completion.RunningAt client worker state .load) : Cut client worker state 4
  | compare (current : Completion.RunningAt client worker state (.compare 1)) : Cut client worker state 3
  | branch (current : Completion.RunningAt client worker state (.branch 1)) : Cut client worker state 2
  | done (current : Completion.RunningAt client worker state (.done 1)) : Cut client worker state 1
  | returned {actual : TSO.Worker} (selected : state.machine.workers[worker]? = some actual)
      (done : actual.returned = true) (free : state.pending worker = none)
      (empty : actual.buffer = []) : Cut client worker state 0

private theorem running_frame {client : Client} {worker : Nat} {point : Point}
    {before after : Suspend.State} (current : Completion.RunningAt client worker before point)
    (slot : after.machine.workers[worker]? = before.machine.workers[worker]?)
    (pending : after.pending worker = before.pending worker) :
    Completion.RunningAt client worker after point := by
  obtain ⟨actual, found, running, live, free, empty⟩ := current
  exact ⟨actual, slot.trans found, running, live, pending.trans free, empty⟩

theorem Cut.frame {client : Client} {worker count : Nat} {before after : Suspend.State}
    (cut : Cut client worker before count)
    (slot : after.machine.workers[worker]? = before.machine.workers[worker]?)
    (pending : after.pending worker = before.pending worker) : Cut client worker after count := by
  cases cut with
  | load current => exact .load (running_frame current slot pending)
  | compare current => exact .compare (running_frame current slot pending)
  | branch current => exact .branch (running_frame current slot pending)
  | done current => exact .done (running_frame current slot pending)
  | returned selected done free empty => exact .returned (slot.trans selected) done (pending.trans free) empty

theorem Cut.free {client : Client} {worker count : Nat} {state : Suspend.State}
    (cut : Cut client worker state count) : state.pending worker = none := by
  cases cut with
  | load current | compare current | branch current | done current => exact current.choose_spec.2.2.2.1
  | returned _ _ free _ => exact free

theorem Cut.slot {client : Client} {worker count : Nat} {state : Suspend.State}
    (cut : Cut client worker state count) :
    ∃ actual, state.machine.workers[worker]? = some actual ∧ actual.buffer = [] := by
  cases cut with
  | load current | compare current | branch current | done current =>
    obtain ⟨actual, found, _, _, _, empty⟩ := current
    exact ⟨actual, found, empty⟩
  | returned selected _ _ empty => exact ⟨_, selected, empty⟩

theorem Cut.returned_zero {client : Client} {worker count : Nat} {state : Suspend.State}
    {actual : TSO.Worker} (cut : Cut client worker state count)
    (selected : state.machine.workers[worker]? = some actual) (done : actual.returned = true) :
    count = 0 := by
  cases cut with
  | load current | compare current | branch current | done current =>
    obtain ⟨before, found, _, live, _, _⟩ := current
    cases Option.some.inj (found.symm.trans selected)
    simp [done] at live
  | returned => rfl

/-- Each live fast-path cut has one actual retiring successor. The return cut
has no successful issue. Current W1 is used only for the LOAD, and survives
accepted peer/service steps through the separate admission theorem. -/
theorem Cut.issue {cohort : Cohort} {state : Futex.State} {worker count : Nat}
    {client : Client} {after : Suspend.State} {observation : Suspend.Observation}
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (cut : Cut client worker state.suspended count)
    (actual : Suspend.issue state.suspended worker = .ok (after, observation)) :
    ∃ next, Cut client worker after next ∧ count = next + 1 ∧
      observation = .machine (.retired worker none) := by
  have code := admitted.currentCode worker (.waitLoop client) member
  cases cut with
  | load current =>
    obtain ⟨before, found, running, live, free, empty⟩ := current
    have reads : loadDWord state.suspended.machine.memory (before.context.registers .rdi) = .ok 1 := by
      rw [running.rdi, (admitted.static.descriptors worker _ member).1]
      exact published
    have issued := issue_next found running live free empty code
      (admitted.loop_ready member .load) (by decide) (execute_load before.context _ 1 reads)
    cases Except.ok.inj (actual.symm.trans issued)
    exact ⟨3, .compare ⟨_, retire_selected found _, running.load_next 1, rfl, free, rfl⟩, rfl, rfl⟩
  | compare current =>
    obtain ⟨before, found, running, live, free, empty⟩ := current
    have issued := issue_next found running live free empty code trivial (by decide) (execute_cmp ..)
    cases Except.ok.inj (actual.symm.trans issued)
    exact ⟨2, .branch ⟨_, retire_selected found _, running.compare_next, rfl, free, rfl⟩, rfl, rfl⟩
  | branch current =>
    obtain ⟨before, found, running, live, free, empty⟩ := current
    have zf : before.context.flags.getLsbD 6 = false := by simpa using running.fields.2
    have canonical := admitted.loop_ready member (.branch 1) (by decide)
    have executed := execute_jnz_taken before.context state.suspended.machine.memory 0x16 zf
      (by rw [branch_done_target running]; exact canonical)
    rw [branch_done_target running] at executed
    have issued := issue_next found running live free empty code
      (admitted.loop_ready member (.branch 1)) (by decide) executed
    cases Except.ok.inj (actual.symm.trans issued)
    exact ⟨1, .done ⟨_, retire_selected found _, running.branch_nonzero (by decide), rfl, free, rfl⟩, rfl, rfl⟩
  | done current =>
    obtain ⟨before, found, running, live, free, empty⟩ := current
    have guards := admitted.loop_ready member (.done 1)
    have issued := (ret_enabled found running live free empty code guards.1 guards.2).1
    cases Except.ok.inj (actual.symm.trans issued)
    exact ⟨0, .returned (retire_selected found _ true) rfl free rfl, rfl, rfl⟩
  | returned selected done _ _ => simp [Suspend.issue, selected, done] at actual

/-- Service can resume only a worker with an actual pending invocation. Every
fast-path cut has none, so even arbitrary accepted service actions frame it. -/
theorem Cut.service {cohort : Cohort} {state after : Futex.State} {worker count : Nat}
    {client : Client} {action : Futex.Action} (cut : Cut client worker state.suspended count)
    (actual : Futex.step cohort.profile.service state action = .ok after) :
    Cut client worker after.suspended count := by
  cases action with
  | compare invocation => rw [(compareWait_stutter actual).1]; exact cut
  | wake invocation selected => rw [(wakeOne_stutter actual).1]; exact cut
  | retry invocation => rw [(retryQueued_stutter actual).1]; exact cut
  | spurious invocation => rw [(spuriousReady_stutter actual).1]; exact cut
  | idle => cases Except.ok.inj actual; exact cut
  | resume invocation flags rcx r11 =>
    obtain ⟨call, outcome, _, _, resumed, _, _, _, _, completed, _, same⟩ := resumeReady_effect actual
    have different : call.worker ≠ worker := by
      intro own
      obtain ⟨_, _, _, _, pending, _, _, _, _⟩ := Suspend.resume_ok _ _ _ _ _ _ _ _ completed
      rw [own, cut.free] at pending
      cases pending
    rw [same]
    apply cut.frame (Suspend.resume_peer different completed)
    simp [Suspend.resume_pending completed, Ne.symm different]

/-- Universal mixed-step accounting. Peer instructions, drains and unrelated
service may interleave freely; none can shortcut this worker's four real cuts. -/
theorem Cut.step {cohort : Cohort} {state after : Futex.State} {worker count : Nat}
    {client : Client} {action : Runtime.Action} {observation : Runtime.Observation}
    (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (cut : Cut client worker state.suspended count)
    (actual : Runtime.step cohort.profile state action = .ok (after, observation)) :
    ∃ next, Cut client worker after.suspended next ∧ count ≤ instructionCost worker observation + next := by
  cases action with
  | issue selected =>
    cases issued : Physical.issue cohort.profile state selected with
    | error fault => simp [Runtime.step, issued] at actual
    | ok output =>
      simp [Runtime.step, issued] at actual
      rcases actual with ⟨rfl, rfl⟩
      have raw := Physical.issue_projection _ _ _ _ issued
      by_cases own : selected = worker
      · subst selected
        obtain ⟨next, afterCut, countEq, observed⟩ := cut.issue admitted member published raw
        exact ⟨next, afterCut, by simp [instructionCost, observed, countEq, Nat.add_comm]⟩
      · refine ⟨count, cut.frame (Suspend.issue_peer own raw) (issue_pending_peer (Ne.symm own) raw), ?_⟩
        omega
  | drain selected =>
    cases drained : Physical.drain cohort.profile state selected with
    | error fault => simp [Runtime.step, drained] at actual
    | ok output =>
      simp [Runtime.step, drained] at actual
      rcases actual with ⟨rfl, rfl⟩
      have raw := Physical.drain_projection _ _ _ _ drained
      by_cases own : selected = worker
      · subst selected
        obtain ⟨before, found, empty⟩ := cut.slot
        simp [Suspend.drain, TSO.drain, found, empty, Except.mapError] at raw
      · refine ⟨count, cut.frame (Suspend.drain_peer own raw) ?_, ?_⟩
        · rw [Suspend.drain_pending raw]
        · omega
  | service serviceAction =>
    cases serviced : Futex.step cohort.profile.service state serviceAction with
    | error fault => simp [Runtime.step, serviced, Except.mapError] at actual
    | ok next =>
      simp [Runtime.step, serviced, Except.mapError] at actual
      rcases actual with ⟨rfl, rfl⟩
      exact ⟨count, cut.service serviced, by simp [instructionCost]⟩

/-- A potential inequality for arbitrary accepted finite interleavings. It
tracks actual retirement observations, including zero-cost selections. -/
theorem Cut.trace {cohort : Cohort} {before after : Futex.State} {worker count : Nat}
    {client : Client} {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (cut : Cut client worker before.suspended count)
    (trace : Runtime.Trace cohort.profile before actions observations after) :
    ∃ remaining, Cut client worker after.suspended remaining ∧
      count ≤ retiredInstructions worker observations + remaining := by
  induction trace generalizing count with
  | nil => exact ⟨count, cut, by simp⟩
  | cons first tail ih =>
    obtain ⟨next, nextCut, bound⟩ := cut.step admitted member published first
    obtain ⟨remaining, finalCut, rest⟩ := ih (admitted_step admitted first)
      (published_word_step admitted published first) nextCut
    exact ⟨remaining, finalCut, by simp only [retiredInstructions_cons]; omega⟩

/-- For these exact bytes, any accepted execution from an actual current LOAD
with signal one to the independent return contract retires at least four of
this worker's user instructions. Other workers and service may interleave.
This is a lower bound for this program, not an ISA-wide optimality claim. -/
theorem load_to_returns_lower_bound {cohort : Cohort} {before after : Futex.State}
    {worker : Nat} {client : Client} {actual : TSO.Worker}
    {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (admitted : Admitted cohort before)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (current : Completion.RunningAt client worker before.suspended .load)
    (trace : Runtime.Trace cohort.profile before actions observations after)
    (returned : Returns client cohort.registration.address after.suspended worker actual) :
    4 ≤ retiredInstructions worker observations := by
  obtain ⟨remaining, cut, bound⟩ := (Cut.load current).trace admitted member published trace
  have zero := cut.returned_zero returned.selected returned.done
  omega

/-- The exact user issue list for the four-instruction fast path. -/
def fastActions (worker : Nat) : List Runtime.Action :=
  [.issue worker, .issue worker, .issue worker, .issue worker]

/-- Exact actual retirements of LOAD, CMP, taken JNZ and RET. -/
def fastObservations (worker : Nat) : List Runtime.Observation :=
  [.physical (.machine (.retired worker none)), .physical (.machine (.retired worker none)),
   .physical (.machine (.retired worker none)), .physical (.machine (.retired worker none))]

private theorem issues_machineTrace {worker count : Nat} {before after : Suspend.State}
    {observations : List Suspend.Observation}
    (success : Suspend.schedule before (List.replicate count (.issue worker)) = .ok (after, observations)) :
    MachineTrace before (List.replicate count (.issue worker)) (observations.map Runtime.Observation.physical) after := by
  induction count generalizing before after observations with
  | zero =>
    simp [Suspend.schedule] at success
    rcases success with ⟨rfl, rfl⟩
    exact .nil
  | succ count ih =>
    rw [List.replicate_succ] at success
    obtain ⟨head, tail, first, rest, same⟩ := Suspend.schedule_cons_ok _ _ _ _ success
    cases same
    exact .issue first (ih rest)

/-- Attainment is an actual managed execution with the independent return
contract, current admission and whole RAM/peer-private frames. Its four
selected retirement observations are explicit; no successful suffix is an input. -/
theorem load_fastpath_attains {cohort : Cohort} {before : Futex.State}
    {worker : Nat} {client : Client} (admitted : Admitted cohort before)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (current : Completion.RunningAt client worker before.suspended .load) :
    ∃ after actual, Runtime.Trace cohort.profile before (fastActions worker) (fastObservations worker) after ∧
      retiredInstructions worker (fastObservations worker) = 4 ∧
      Returns client cohort.registration.address after.suspended worker actual ∧
      Admitted cohort after ∧ PrivateFrame worker before.suspended after.suspended := by
  obtain ⟨actual, found, running, live, free, empty⟩ := current
  have descriptor := admitted.static.descriptors worker (.waitLoop client) member
  have loadReady := admitted.loop_ready member .load
  have returnReady := admitted.loop_ready member (.done 1)
  obtain ⟨suspended, selected, scheduled, selectedAt, done, _, _, _, _, _, _, _, _, memory, _, peers⟩ :=
    published_one_returns found running live free empty (admitted.currentCode worker _ member)
      loadReady.1 (by rw [descriptor.1]; exact published)
      (admitted.static.loopTargets worker client member).2 returnReady.1 returnReady.2
  have rawTrace : MachineTrace before.suspended (fastActions worker) (fastObservations worker) suspended :=
    issues_machineTrace (count := 4) scheduled
  obtain ⟨after, trace, exactState, valid⟩ := rawTrace.lift admitted rfl
  have afterSelected : after.suspended.machine.workers[worker]? = some selected := by
    rw [exactState]
    exact selectedAt
  refine ⟨after, selected, trace, ?_, valid.returned_sound member afterSelected done, valid, ?_⟩
  · simp [retiredInstructions, fastObservations, instructionCost]
  · rw [exactState]
    exact ⟨memory, peers⟩

end EDSL.OS.Futex.Predicate.Accounting

#print axioms EDSL.OS.Futex.Predicate.Accounting.load_to_returns_lower_bound
#print axioms EDSL.OS.Futex.Predicate.Accounting.load_fastpath_attains
#audit_edsl
