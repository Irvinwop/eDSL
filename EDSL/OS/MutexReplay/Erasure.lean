/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Safety
import EDSL.OS.MachineThreads

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

def eraseWorker (worker : Worker) : MachineThreads.Worker :=
  ⟨worker.context, decide (worker.phase = .completed)⟩

def erase (state : State) : MachineThreads.State :=
  ⟨toMemory state.shared.shared.resources.space, state.workers.map eraseWorker⟩

theorem advance_unfinished (state : State) (identifier : Nat) (worker : Worker) (result : Result)
    (success : advance state identifier worker = .ok result) : worker.phase ≠ .completed := by
  obtain ⟨_, operation, selected, _, _⟩ := advance_ok _ _ _ _ success
  intro completed
  simp [action, completed] at selected

/-- Erasure retains the entire architectural memory/context, the actual atomic
event, and the actual function return. No admission gate is added to the bare
machine to make this correspondence hold. -/
theorem dispatch_erases (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (success : dispatch state identifier = .ok result) :
    MachineThreads.dispatch (erase state) identifier = .ok (erase result.1, result.2) := by
  obtain ⟨worker, output, live, advanced, same⟩ := dispatch_ok _ _ _ success
  obtain ⟨_, operation, _, performed, returned⟩ := advance_ok _ _ _ _ advanced
  change output.returned = decide (nextPhase worker output = .completed) at returned
  have unfinished := advance_unfinished _ _ _ _ advanced
  have found : (erase state).workers[identifier]? = some (eraseWorker worker) := by
    simp only [erase, List.getElem?_map, live, Option.map_some]
  have actual := perform_refines _ _ _ _ _ performed
  change X86.step (MachineThreads.contextState worker.context (erase state).memory) = .ok output.outcome at actual
  rw [same]
  simp only [MachineThreads.dispatch, found, eraseWorker, unfinished, decide_false,
    Bool.false_eq_true, ↓reduceIte]
  rw [actual]
  cases done : output.returned with
  | true =>
    have event := perform_return_event _ _ _ _ _ performed done
    simp only [Except.mapError, Result.outcome, done, ite_true, event, ok_bind,
      MachineThreads.install, erase, List.map_set, eraseWorker, evolved, ← returned,
      Threads.Context.ofState, Threads.Context.snapshot, pure_ok]
  | false =>
    cases event : output.event <;>
      simp only [Except.mapError, Result.outcome, done, Bool.false_eq_true, ite_false, event, ok_bind,
        MachineThreads.install, erase, List.map_set, eraseWorker, evolved, ← returned,
        Threads.Context.ofState, Threads.Context.snapshot, pure_ok]

theorem schedule_erases (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) :
    MachineThreads.schedule (erase state) selections = .ok (erase result.1, result.2) := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; rfl
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    have firstStep := dispatch_erases _ _ _ head
    have tailSteps := induction first.1 tail next
    rw [same]
    cases event : first.2 <;>
      simp [MachineThreads.schedule, firstStep, tailSteps, recordEvent, MachineThreads.recordEvent, event]

end EDSL.OS.MutexReplay
