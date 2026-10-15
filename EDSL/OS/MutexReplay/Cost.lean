/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Control

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

/-- Remaining user instructions, with four additional instructions reserved
after an unsuccessful exchange until the retry reaches the loop entry. -/
def potential (worker : Worker) : Nat :=
  match worker.phase with
  | .entry => 13
  | .acquiring => 12
  | .comparing => if worker.guard = none then 15 else 11
  | .branching => if worker.guard = none then 14 else 10
  | .loading => 9
  | .incrementingFirst => 8
  | .storingFirst => 7
  | .incrementingSecond => 6
  | .storingSecond => 5
  | .preparingRelease => 4
  | .releasing => 3
  | .finishing => 2
  | .returning => 1
  | .completed => 0

def potentialSum (state : State) : Nat := (state.workers.map potential).sum

/-- A busy acquisition is identified by the actual exchange's old and new
dwords. Releases and absent events contribute zero. -/
def busy (event : Option AtomicEvent) : Nat :=
  match event with
  | none => 0
  | some actual => if actual.before = 1 ∧ actual.after = 1 then 1 else 0

def busyCount (events : List (Nat × AtomicEvent)) : Nat :=
  (events.map fun event => busy (some event.2)).sum

/-- Only shared well-formedness and each worker's private control fact are
needed for instruction accounting. No payload endpoint contract is assumed. -/
def Controlled (state : State) : Prop :=
  Mutex.WellFormed state.shared ∧
    ∀ (identifier : Nat) (worker : Worker), state.workers[identifier]? = some worker → Control worker

theorem Invariant.controlled {config : Mutex.Config} {state : State}
    (invariant : Invariant config state) : Controlled state :=
  ⟨invariant.shared, fun identifier worker live => (invariant.workers identifier worker live).control⟩

/-- Each successful advance executes one actual user instruction. A busy
exchange adds exactly the four instructions of another loop attempt. -/
theorem advance_potential (state : State) (identifier : Nat) (worker : Worker) (result : Result)
    (valid : Mutex.WellFormed state.shared) (control : Control worker)
    (success : advance state identifier worker = .ok result) :
    potential (evolved worker result) + 1 = potential worker + 4 * busy result.event := by
  have afterControl := advance_control _ _ _ _ valid control success
  obtain ⟨_, operation, selected, performed, _⟩ := advance_ok _ _ _ _ success
  cases phase : worker.phase with
  | entry =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | plain instruction context ran => simp [potential, evolved, nextPhase, phase, busy]
  | acquiring =>
    simp only [Control, phase] at control
    have unheld : worker.guard = none := control.1
    simp [action, phase, unheld] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | acquire record attempt context found operand replacement acquired ran =>
      rcases Mutex.acquisition _ _ _ valid acquired with granted | failed
      · obtain ⟨lease, _, guard, _, _, _, _, _, before, after⟩ := granted
        simp [potential, evolved, nextPhase, phase, busy, guard, before, after]
      · obtain ⟨guard, _, before, after⟩ := failed
        simp [potential, evolved, nextPhase, phase, busy, guard, before, after]
  | comparing =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | plain instruction context ran =>
      cases guard : worker.guard <;> simp [potential, evolved, nextPhase, phase, busy, guard]
  | branching =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | plain instruction context ran =>
      cases guard : worker.guard with
      | none =>
        have retry : context.rip = worker.entry.rip := by
          by_cases retry : context.rip = worker.entry.rip
          · exact retry
          · simp [Control, evolved, nextPhase, phase, retry, guard] at afterControl
        simp [potential, evolved, nextPhase, phase, retry, guard, busy]
      | some lease =>
        have fallthrough : context.rip ≠ worker.entry.rip := by
          intro retry
          simp [Control, evolved, nextPhase, phase, retry, guard] at afterControl
        simp [potential, evolved, nextPhase, phase, fallthrough, guard, busy]
  | loading =>
    cases guard : worker.guard with
    | none => simp [action, phase, guard] at selected
    | some lease =>
      simp [action, phase, guard] at selected
      cases selected
      cases perform_effect _ _ _ _ _ performed with
      | load lease record value context authorized operand loaded ran =>
        simp [potential, evolved, nextPhase, phase, busy]
  | incrementingFirst =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | plain instruction context ran => simp [potential, evolved, nextPhase, phase, busy]
  | storingFirst =>
    cases guard : worker.guard with
    | none => simp [action, phase, guard] at selected
    | some lease =>
      simp [action, phase, guard] at selected
      cases selected
      cases perform_effect _ _ _ _ _ performed with
      | store lease record after context authorized operand stored ran =>
        simp [potential, evolved, nextPhase, phase, busy]
  | incrementingSecond =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | plain instruction context ran => simp [potential, evolved, nextPhase, phase, busy]
  | storingSecond =>
    cases guard : worker.guard with
    | none => simp [action, phase, guard] at selected
    | some lease =>
      simp [action, phase, guard] at selected
      cases selected
      cases perform_effect _ _ _ _ _ performed with
      | store lease record after context authorized operand stored ran =>
        simp [potential, evolved, nextPhase, phase, busy]
  | preparingRelease =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | plain instruction context ran => simp [potential, evolved, nextPhase, phase, busy]
  | releasing =>
    cases guard : worker.guard with
    | none => simp [action, phase, guard] at selected
    | some lease =>
      simp [action, phase, guard] at selected
      cases selected
      cases perform_effect _ _ _ _ _ performed with
      | release lease record released context authorized operand replacement finished ran =>
        obtain ⟨_, _, _, _, before, after⟩ := Mutex.release_result _ _ _ _ valid finished
        simp [potential, evolved, nextPhase, phase, busy, before, after]
  | finishing =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | plain instruction context ran => simp [potential, evolved, nextPhase, phase, busy]
  | returning =>
    simp [action, phase] at selected
    cases selected
    cases perform_effect _ _ _ _ _ performed with
    | ret context ran => simp [potential, evolved, nextPhase, phase, busy]
  | completed => simp [action, phase] at selected

theorem dispatch_controlled (state : State) (identifier : Nat)
    (result : State × Option AtomicEvent) (controlled : Controlled state)
    (success : dispatch state identifier = .ok result) : Controlled result.1 := by
  obtain ⟨worker, output, live, advanced, same⟩ := dispatch_ok _ _ _ success
  obtain ⟨_, operation, _, performed, _⟩ := advance_ok _ _ _ _ advanced
  have selected := advance_control _ _ _ _ controlled.1 (controlled.2 _ _ live) advanced
  rw [same]
  refine ⟨(perform_history _ _ _ _ _ performed).wellFormed controlled.1, ?_⟩
  intro query after found
  by_cases own : identifier = query
  · subst query
    have bound := (List.getElem_of_getElem? live).1
    have equal := Option.some.inj ((List.getElem?_set_self bound).symm.trans found)
    exact equal ▸ selected
  · have previous : state.workers[query]? = some after := by
      simpa only [List.getElem?_set_ne own] using found
    exact controlled.2 query after previous

theorem schedule_controlled (state : State) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (controlled : Controlled state)
    (success : schedule state selections = .ok result) : Controlled result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact controlled
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact induction first.1 tail (dispatch_controlled _ _ _ controlled head) next

theorem potential_sum_set (workers : List Worker) (identifier : Nat) (before after : Worker)
    (live : workers[identifier]? = some before) :
    ((workers.set identifier after).map potential).sum + potential before =
      (workers.map potential).sum + potential after := by
  induction workers generalizing identifier with
  | nil => simp at live
  | cons first rest induction =>
    cases identifier with
    | zero => simp at live; cases live; simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    | succ index =>
      have tail : rest[index]? = some before := by simpa using live
      have result := induction index tail
      simp only [List.set, List.map_cons, List.sum_cons]
      omega

theorem dispatch_potential (state : State) (identifier : Nat)
    (result : State × Option AtomicEvent) (controlled : Controlled state)
    (success : dispatch state identifier = .ok result) :
    potentialSum result.1 + 1 = potentialSum state + 4 * busy result.2 := by
  obtain ⟨worker, output, live, advanced, same⟩ := dispatch_ok _ _ _ success
  have sum := potential_sum_set state.workers identifier worker (evolved worker output) live
  have step := advance_potential _ _ _ _ controlled.1 (controlled.2 _ _ live) advanced
  rw [same]
  dsimp only [potentialSum]
  omega

theorem busyCount_recordEvent (identifier : Nat) (event : Option AtomicEvent)
    (events : List (Nat × AtomicEvent)) :
    busyCount (recordEvent identifier event events) = busy event + busyCount events := by
  cases event <;> simp [recordEvent, busyCount, busy]

/-- Exact accounting for every successful supplied schedule, including one
that stops before completion. All selections execute an actual instruction. -/
theorem schedule_potential (state : State) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (controlled : Controlled state)
    (success : schedule state selections = .ok result) :
    potentialSum result.1 + selections.length = potentialSum state + 4 * busyCount result.2 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; simp [busyCount]
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    have step := dispatch_potential _ _ _ controlled head
    have following := induction first.1 tail (dispatch_controlled _ _ _ controlled head) next
    rw [same]
    simp only [List.length_cons, busyCount_recordEvent]
    omega

theorem entry_potential (state : State)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry) :
    potentialSum state = 13 * state.workers.length := by
  have each : ∀ worker ∈ state.workers, potential worker = 13 := by
    intro worker member
    simp [potential, entry worker member]
  rw [potentialSum, List.map_eq_replicate_iff.mpr each]
  generalize state.workers.length = count
  induction count with
  | zero => rfl
  | succ count induction => simp [List.replicate_succ, induction]; omega

theorem completed_potential (state : State) (done : completed state = true) :
    potentialSum state = 0 := by
  have each : ∀ worker ∈ state.workers, potential worker = 0 := by
    intro worker member
    have phase := (of_decide_eq_true (List.all_eq_true.mp done worker member)).1
    simp [potential, phase]
  rw [potentialSum, List.map_eq_replicate_iff.mpr each]
  generalize state.workers.length = count
  induction count with
  | zero => rfl
  | succ count induction => simp [List.replicate_succ, induction]

/-- Every successful schedule that completes an entry-phase cohort executes
thirteen user instructions per worker and four per actual busy exchange.
Completion is conditional: no fairness, elapsed-time, or minimum-cost claim
is made, and no endpoint checker is an assumption of this theorem. -/
theorem completed_cost (state : State) (selections : List Nat)
    (result : State × List (Nat × AtomicEvent)) (controlled : Controlled state)
    (entry : ∀ worker ∈ state.workers, worker.phase = .entry)
    (success : schedule state selections = .ok result) (done : completed result.1 = true) :
    selections.length = 13 * state.workers.length + 4 * busyCount result.2 := by
  have cost := schedule_potential _ _ _ controlled success
  rw [completed_potential _ done, entry_potential _ entry, Nat.zero_add] at cost
  exact cost

end EDSL.OS.MutexReplay
