/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.Effects

namespace EDSL.OS.Suspend
open X86

/-- Current facts about a saved invocation. Entry memory is deliberately
historical: neither current RAM equality nor a canonical continuation is required. -/
structure PendingValid (state : State) (identifier : Nat) (saved : Saved) : Prop where
  owner : saved.worker = identifier
  allocated : saved.identifier < state.nextCall
  live : ∃ worker, state.machine.workers[identifier]? = some worker ∧ worker.returned = false ∧
    worker.buffer = [] ∧ worker.context = Threads.Context.ofState saved.request.user
  continuation : saved.request.continuation = saved.request.user.rip + 2

/-- Safety depends only on present queues, contexts and pending records. It
assumes no future successful instruction, service result, or peer quiescence. -/
structure WellFormed (state : State) : Prop where
  buffers : TSO.BuffersValid state.machine
  pending : ∀ identifier saved, state.pending identifier = some saved → PendingValid state identifier saved
  distinct : ∀ left right a b, state.pending left = some a → state.pending right = some b →
    a.identifier = b.identifier → left = right

theorem WellFormed.initial {machine : TSO.State} (valid : TSO.BuffersValid machine) :
    WellFormed (Suspend.initial machine) := by
  refine ⟨valid, ?_, ?_⟩
  · intro identifier saved pending
    cases pending
  · intro left right a b first
    cases first

theorem PendingValid.frame {before after : State} {identifier : Nat} {saved : Saved}
    (valid : PendingValid before identifier saved) (frontier : before.nextCall ≤ after.nextCall)
    (worker : after.machine.workers[identifier]? = before.machine.workers[identifier]?) :
    PendingValid after identifier saved := by
  obtain ⟨selected, live, returned, empty, context⟩ := valid.live
  exact ⟨valid.owner, Nat.lt_of_lt_of_le valid.allocated frontier,
    ⟨selected, worker.trans live, returned, empty, context⟩, valid.continuation⟩

/-- Removing pending records and retaining their whole workers preserves the
invariant even when current RAM changes. -/
theorem WellFormed.frame {before after : State} (valid : WellFormed before)
    (frontier : before.nextCall ≤ after.nextCall) (buffers : TSO.BuffersValid after.machine)
    (pending : ∀ identifier saved, after.pending identifier = some saved →
      before.pending identifier = some saved)
    (workers : ∀ identifier saved, after.pending identifier = some saved →
      after.machine.workers[identifier]? = before.machine.workers[identifier]?) :
    WellFormed after := by
  refine ⟨buffers, ?_, ?_⟩
  · intro identifier saved found
    exact (valid.pending identifier saved (pending identifier saved found)).frame frontier
      (workers identifier saved found)
  · intro left right a b first second equal
    exact valid.distinct left right a b (pending left a first) (pending right b second) equal

theorem WellFormed.fresh {state : State} {identifier : Nat} {saved : Saved}
    (valid : WellFormed state) (pending : state.pending identifier = some saved) :
    saved.identifier ≠ state.nextCall :=
  Nat.ne_of_lt (valid.pending identifier saved pending).allocated

theorem WellFormed.pending_worker {state : State} {identifier : Nat} {saved : Saved}
    {worker : TSO.Worker} (valid : WellFormed state) (pending : state.pending identifier = some saved)
    (live : state.machine.workers[identifier]? = some worker) :
    worker.returned = false ∧ worker.buffer = [] ∧
      worker.context = Threads.Context.ofState saved.request.user := by
  obtain ⟨parked, atParked, returned, empty, context⟩ := (valid.pending identifier saved pending).live
  have same := Option.some.inj (atParked.symm.trans live)
  subst parked
  exact ⟨returned, empty, context⟩

/-- A parked context projects the saved private state against current RAM.
The saved entry-memory snapshot is retained solely inside the request. -/
theorem WellFormed.pending_sharedState {state : State} {identifier : Nat} {saved : Saved}
    {worker : TSO.Worker} (valid : WellFormed state) (pending : state.pending identifier = some saved)
    (live : state.machine.workers[identifier]? = some worker) :
    TSO.sharedState state.machine worker = { saved.request.user with memory := state.machine.memory } := by
  have context := (valid.pending_worker pending live).2.2
  unfold TSO.sharedState MachineThreads.contextState
  rw [context]
  rfl

/-- Capture uses a fresh invocation ID and preserves every existing record and
the entire machine. Its premises are current entry facts, not future behavior. -/
theorem WellFormed.capture {state : State} {identifier : Nat} {worker : TSO.Worker}
    {request : SyscallRequest} (valid : WellFormed state)
    (live : state.machine.workers[identifier]? = some worker) (returned : worker.returned = false)
    (empty : worker.buffer = [])
    (user : request.user = TSO.sharedState state.machine worker)
    (continuation : request.continuation = request.user.rip + 2) :
    WellFormed (Suspend.capture state identifier request) := by
  refine ⟨valid.buffers, ?_, ?_⟩
  · intro query saved found
    by_cases own : query = identifier
    · subst query
      have same : saved = ⟨state.nextCall, identifier, request⟩ := by
        simpa only [Suspend.capture, ↓reduceIte, Option.some.injEq] using found.symm
      subst saved
      refine ⟨rfl, Nat.lt_succ_self _, ⟨worker, live, returned, empty, ?_⟩, continuation⟩
      rw [user]
      rfl
    · have prior : state.pending query = some saved := by
        simpa only [Suspend.capture, ite_eq_right own] using found
      exact (valid.pending query saved prior).frame (Nat.le_succ _) rfl
  · intro left right a b first second equal
    by_cases ownLeft : left = identifier
    · subst left
      have same : a = ⟨state.nextCall, identifier, request⟩ := by
        simpa only [Suspend.capture, ↓reduceIte, Option.some.injEq] using first.symm
      subst a
      by_cases ownRight : right = identifier
      · exact ownRight.symm
      · have prior : state.pending right = some b := by
          simpa only [Suspend.capture, ite_eq_right ownRight] using second
        have allocated := (valid.pending right b prior).allocated
        change state.nextCall = b.identifier at equal
        omega
    · by_cases ownRight : right = identifier
      · subst right
        have same : b = ⟨state.nextCall, identifier, request⟩ := by
          simpa only [Suspend.capture, ↓reduceIte, Option.some.injEq] using second.symm
        subst b
        have prior : state.pending left = some a := by
          simpa only [Suspend.capture, ite_eq_right ownLeft] using first
        have allocated := (valid.pending left a prior).allocated
        change a.identifier = state.nextCall at equal
        omega
      · exact valid.distinct left right a b
          (by simpa only [Suspend.capture, ite_eq_right ownLeft] using first)
          (by simpa only [Suspend.capture, ite_eq_right ownRight] using second) equal

theorem buffersValid_execute {state : State} {identifier : Nat} {worker : TSO.Worker}
    {instruction : Instruction} {result : State × Observation}
    (valid : TSO.BuffersValid state.machine) (live : state.machine.workers[identifier]? = some worker)
    (success : Suspend.execute state identifier worker instruction = .ok result) :
    TSO.BuffersValid result.1.machine := by
  cases execute_effect _ _ _ _ _ success with
  | entered => exact valid
  | machine _ executed => exact valid.execute live executed

theorem buffersValid_issue {state : State} {identifier : Nat} {result : State × Observation}
    (valid : TSO.BuffersValid state.machine) (success : Suspend.issue state identifier = .ok result) :
    TSO.BuffersValid result.1.machine := by
  cases issue_effect _ _ _ success with
  | parked | entered => exact valid
  | machine _ issued => exact valid.issue issued

theorem buffersValid_drain {state : State} {identifier : Nat} {result : State × Observation}
    (valid : TSO.BuffersValid state.machine) (success : Suspend.drain state identifier = .ok result) :
    TSO.BuffersValid result.1.machine := by
  obtain ⟨_, _, drained, same⟩ := drain_ok _ _ _ success
  rw [same]
  exact valid.drain drained

theorem buffersValid_resume {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word} (valid : TSO.BuffersValid state.machine)
    (success : Suspend.resume state identifier invocation raw flags rcx r11 = .ok after) :
    TSO.BuffersValid after.machine := by
  obtain ⟨_, _, _, _, _, _, _, _, same⟩ := resume_ok _ _ _ _ _ _ _ _ success
  rw [same]
  intro worker member store queued
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact valid worker old store queued
  · cases queued

theorem buffersValid_step {state : State} {action : Action} {result : State × Observation}
    (valid : TSO.BuffersValid state.machine) (success : Suspend.step state action = .ok result) :
    TSO.BuffersValid result.1.machine := by
  cases action with
  | issue identifier => exact buffersValid_issue valid success
  | drain identifier => exact buffersValid_drain valid success
  | resume identifier invocation raw flags rcx r11 =>
    cases completed : Suspend.resume state identifier invocation raw flags rcx r11 with
    | error fault => simp [Suspend.step, completed] at success
    | ok after =>
      simp [Suspend.step, completed] at success
      subst result
      exact buffersValid_resume valid completed
  | idle => simp [Suspend.step] at success; subst result; exact valid

theorem WellFormed.issue {state : State} {identifier : Nat} {result : State × Observation}
    (valid : WellFormed state) (success : Suspend.issue state identifier = .ok result) :
    WellFormed result.1 := by
  cases issue_effect _ _ _ success with
  | parked => exact valid
  | entered live returned absent decoded empty executed stepped user continuation =>
    exact valid.capture live returned empty user continuation
  | @machine after observation absent issued =>
    apply valid.frame (after := { state with machine := after })
      (Nat.le_refl _) (valid.buffers.issue issued)
      (fun _ _ pending => pending)
    intro query saved pending
    apply tso_issue_peer ?_ issued
    intro same
    subst query
    rw [absent] at pending
    cases pending

theorem WellFormed.issue_entered_fresh {state after : State} {identifier invocation : Nat}
    (valid : WellFormed state)
    (success : Suspend.issue state identifier = .ok (after, .entered identifier invocation)) :
    invocation = state.nextCall ∧
      ∀ query saved, state.pending query = some saved → saved.identifier < invocation := by
  have frontier := (issue_entered_effect success).1
  refine ⟨frontier, ?_⟩
  intro query saved pending
  rw [frontier]
  exact (valid.pending query saved pending).allocated

theorem WellFormed.drain {state : State} {identifier : Nat} {result : State × Observation}
    (valid : WellFormed state) (success : Suspend.drain state identifier = .ok result) :
    WellFormed result.1 := by
  obtain ⟨machine, observation, drained, same⟩ := drain_ok _ _ _ success
  rw [same]
  apply valid.frame (after := { state with machine := machine })
    (Nat.le_refl _) (valid.buffers.drain drained)
    (fun _ _ pending => pending)
  intro query saved pending
  apply tso_drain_peer ?_ drained
  intro equal
  subst query
  obtain ⟨parked, atParked, _, empty, _⟩ := (valid.pending identifier saved pending).live
  obtain ⟨worker, head, tail, _, live, nonempty, _, _⟩ := TSO.drain_ok _ _ _ drained
  have workersEqual := Option.some.inj (live.symm.trans atParked)
  subst worker
  rw [empty] at nonempty
  cases nonempty

theorem WellFormed.pending_drain_error {state : State} {identifier : Nat} {saved : Saved}
    (valid : WellFormed state) (pending : state.pending identifier = some saved) :
    Suspend.drain state identifier = .error (.underlying .emptyBuffer) := by
  obtain ⟨worker, live, _, empty, _⟩ := (valid.pending identifier saved pending).live
  simp [Suspend.drain, TSO.drain, live, empty, Except.mapError]

theorem WellFormed.resume {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word} (valid : WellFormed state)
    (success : Suspend.resume state identifier invocation raw flags rcx r11 = .ok after) :
    WellFormed after := by
  apply valid.frame (after := after)
    (by rw [resume_nextCall success]; exact Nat.le_refl _) (buffersValid_resume valid.buffers success)
  · intro query saved pending
    by_cases own : query = identifier
    · subst query
      rw [resume_consumed success] at pending
      cases pending
    · simpa only [resume_pending success, ite_eq_right own] using pending
  · intro query saved pending
    apply resume_peer ?_ success
    intro same
    subst query
    rw [resume_consumed success] at pending
    cases pending

theorem WellFormed.step {state : State} {action : Action} {result : State × Observation}
    (valid : WellFormed state) (success : Suspend.step state action = .ok result) :
    WellFormed result.1 := by
  cases action with
  | issue identifier => exact valid.issue success
  | drain identifier => exact valid.drain success
  | resume identifier invocation raw flags rcx r11 =>
    cases completed : Suspend.resume state identifier invocation raw flags rcx r11 with
    | error fault => simp [Suspend.step, completed] at success
    | ok after =>
      simp [Suspend.step, completed] at success
      subst result
      exact valid.resume completed
  | idle => simp [Suspend.step] at success; subst result; exact valid

/-- A returned worker cannot also have a saved invocation. Draining a
returned worker remains available to the underlying memory model. -/
theorem WellFormed.returned_noPending {state : State} {identifier : Nat} {worker : TSO.Worker}
    (valid : WellFormed state) (live : state.machine.workers[identifier]? = some worker)
    (returned : worker.returned = true) : state.pending identifier = none := by
  cases pending : state.pending identifier with
  | none => rfl
  | some saved =>
    obtain ⟨parked, atParked, unreturned, _, _⟩ := (valid.pending identifier saved pending).live
    have same := Option.some.inj (atParked.symm.trans live)
    subst parked
    rw [returned] at unreturned
    cases unreturned

/-- Completion is a generic mechanism: a valid pending invocation admits any
private return fields. This asserts no Linux service or fairness guarantee. -/
theorem WellFormed.resume_enabled {state : State} {identifier : Nat} {saved : Saved}
    (valid : WellFormed state) (pending : state.pending identifier = some saved)
    (raw flags rcx r11 : Word) :
    ∃ after, Suspend.resume state identifier saved.identifier raw flags rcx r11 = .ok after := by
  have ready := valid.pending identifier saved pending
  obtain ⟨worker, live, returned, empty, _⟩ := ready.live
  exact ⟨_, resume_success raw flags rcx r11 live returned pending rfl ready.owner empty⟩

theorem WellFormed.resume_identifier_lt {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word} (valid : WellFormed state)
    (success : Suspend.resume state identifier invocation raw flags rcx r11 = .ok after) :
    invocation < after.nextCall := by
  obtain ⟨_, saved, _, _, pending, current, _, _, _⟩ := resume_ok _ _ _ _ _ _ _ _ success
  rw [resume_nextCall success, ← current]
  exact (valid.pending identifier saved pending).allocated

/-- Consumption removes this invocation ID globally, including every peer
index, because live invocation IDs were distinct before completion. -/
theorem WellFormed.resume_consumed_id {state after : State} {identifier invocation : Nat}
    {raw flags rcx r11 : Word} (valid : WellFormed state)
    (success : Suspend.resume state identifier invocation raw flags rcx r11 = .ok after) :
    ∀ query saved, after.pending query = some saved → saved.identifier ≠ invocation := by
  obtain ⟨_, original, _, _, pending, current, _, _, _⟩ := resume_ok _ _ _ _ _ _ _ _ success
  intro query saved found equal
  by_cases own : query = identifier
  · subst query
    rw [resume_consumed success] at found
    cases found
  · have prior : state.pending query = some saved := by
      simpa only [resume_pending success, ite_eq_right own] using found
    exact own (valid.distinct query identifier saved original prior pending (equal.trans current.symm))

/-- Once an ID below the frontier has disappeared, a successful action cannot
create it again. Together with `step_nextCall`, this supports arbitrary traces. -/
theorem step_no_reuse {state : State} {action : Action} {result : State × Observation}
    {invocation : Nat} (allocated : invocation < state.nextCall)
    (consumed : ∀ query saved, state.pending query = some saved → saved.identifier ≠ invocation)
    (success : Suspend.step state action = .ok result) :
    ∀ query saved, result.1.pending query = some saved → saved.identifier ≠ invocation := by
  intro query saved pending
  rcases step_pending_origin success pending with old | fresh
  · exact consumed query saved old
  · intro equal
    have frontier := fresh.1
    omega

theorem resume_no_reuse {state : State} {identifier invocation : Nat} {raw flags rcx r11 : Word}
    (consumed : ∀ query saved, state.pending query = some saved → saved.identifier ≠ invocation) :
    ∀ after, Suspend.resume state identifier invocation raw flags rcx r11 ≠ .ok after := by
  intro after success
  obtain ⟨_, saved, _, _, pending, current, _, _, _⟩ := resume_ok _ _ _ _ _ _ _ _ success
  exact consumed identifier saved pending current

theorem issue_memory_frame {state : State} {identifier : Nat} {result : State × Observation}
    (success : Suspend.issue state identifier = .ok result) :
    TSO.MemoryFrame state.machine.memory result.1.machine.memory := by
  cases issue_effect _ _ _ success with
  | parked | entered => exact .refl _
  | machine _ issued => exact TSO.issue_memory_frame issued

theorem drain_memory_frame {state : State} {identifier : Nat} {result : State × Observation}
    (valid : TSO.BuffersValid state.machine) (success : Suspend.drain state identifier = .ok result) :
    TSO.MemoryFrame state.machine.memory result.1.machine.memory := by
  obtain ⟨_, _, drained, same⟩ := drain_ok _ _ _ success
  rw [same]
  exact TSO.drain_memory_frame valid drained

theorem step_memory_frame {state : State} {action : Action} {result : State × Observation}
    (valid : TSO.BuffersValid state.machine) (success : Suspend.step state action = .ok result) :
    TSO.MemoryFrame state.machine.memory result.1.machine.memory := by
  cases action with
  | issue identifier => exact issue_memory_frame success
  | drain identifier => exact drain_memory_frame valid success
  | resume identifier invocation raw flags rcx r11 =>
    cases completed : Suspend.resume state identifier invocation raw flags rcx r11 with
    | error fault => simp [Suspend.step, completed] at success
    | ok after =>
      simp [Suspend.step, completed] at success
      subst result
      rw [resume_memory completed]
      exact .refl _
  | idle => simp [Suspend.step] at success; subst result; exact .refl _

end EDSL.OS.Suspend

#audit_edsl
