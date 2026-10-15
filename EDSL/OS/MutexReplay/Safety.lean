/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.MutexReplay.Refinement

namespace EDSL.OS.MutexReplay
open X86 AddressSpace

def evolved (worker : Worker) (result : Result) : Worker :=
  { worker with context := result.context, phase := nextPhase worker result, guard := result.guard }

theorem advance_ok (state : State) (identifier : Nat) (worker : Worker) (result : Result)
    (success : advance state identifier worker = .ok result) :
    checkCode (toMemory state.shared.shared.resources.space) worker.entry.rip bytes = true ∧
    ∃ operation, action worker = .ok operation ∧
      perform state.shared identifier worker operation = .ok result ∧
      result.returned = decide ((evolved worker result).phase = .completed) := by
  by_cases context : contextValid worker = true
  · by_cases code : checkCode (toMemory state.shared.shared.resources.space) worker.entry.rip bytes = true
    · cases selected : action worker with
      | error fault => simp [advance, context, code, selected] at success
      | ok operation =>
        cases actual : perform state.shared identifier worker operation with
        | error fault => simp [advance, context, code, selected, actual] at success
        | ok output =>
          by_cases after : contextValid (evolved worker output) = true
          · simp only [evolved] at after
            simp only [advance, context, code, Bool.not_true, Bool.false_eq_true, ↓reduceIte, selected, actual, ok_bind, after] at success
            by_cases done : nextPhase worker output = .completed
            · cases returned : output.returned with
              | false => simp [returned, done] at success
              | true =>
                simp [returned, done] at success
                subst result
                refine ⟨code, operation, rfl, actual, ?_⟩
                change output.returned = decide (nextPhase worker output = .completed)
                rw [returned]
                simp [done]
            · cases returned : output.returned with
              | false =>
                simp [returned, done] at success
                subst result
                refine ⟨code, operation, rfl, actual, ?_⟩
                change output.returned = decide (nextPhase worker output = .completed)
                rw [returned]
                simp [done]
              | true => simp [returned, done] at success
          · simp only [evolved] at after
            simp [advance, context, code, selected, actual, after] at success
    · simp [advance, context, code] at success
  · simp [advance, context] at success

theorem dispatch_ok (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (success : dispatch state identifier = .ok result) :
    ∃ worker output, state.workers[identifier]? = some worker ∧
      advance state identifier worker = .ok output ∧
      result = (⟨output.shared, state.workers.set identifier (evolved worker output)⟩, output.event) := by
  cases found : state.workers[identifier]? with
  | none => simp [dispatch, found] at success
  | some worker =>
    cases actual : advance state identifier worker with
    | error fault => simp [dispatch, found, actual] at success
    | ok output =>
      simp [dispatch, found, actual] at success
      exact ⟨worker, output, rfl, actual, success.symm⟩

/-- One complete projected instruction, including peer-context framing and
the actual current shared memory on both sides. The OS protocol history does
not authenticate real kernel threads; the immutable cohort index is logical. -/
inductive MachineStep (before : State) (identifier : Nat) (event : Option AtomicEvent) (after : State) : Prop where
  | mk (worker output : Worker)
    (live : before.workers[identifier]? = some worker)
    (replaced : after.workers = before.workers.set identifier output)
    (code : CodeAt (toMemory before.shared.shared.resources.space) worker.entry.rip bytes)
    (history : Mutex.History before.shared after.shared)
    (actual : X86.step (worker.context.snapshot before.shared.shared.resources.space) = .ok
    (if output.phase = .completed then .returned (output.context.snapshot after.shared.shared.resources.space)
      else match event with
      | some event => .atomic event (output.context.snapshot after.shared.shared.resources.space)
      | none => .next (output.context.snapshot after.shared.shared.resources.space)))
    (returnEvent : output.phase = .completed → event = none) :
    MachineStep before identifier event after

theorem dispatch_refines (state : State) (identifier : Nat) (result : State × Option AtomicEvent)
    (success : dispatch state identifier = .ok result) : MachineStep state identifier result.2 result.1 := by
  obtain ⟨worker, output, live, advanced, same⟩ := dispatch_ok _ _ _ success
  obtain ⟨code, operation, _, performed, returned⟩ := advance_ok _ _ _ _ advanced
  rw [same]
  refine ⟨worker, evolved worker output, live, rfl, checkCode_sound _ _ _ code,
    perform_history _ _ _ _ _ performed, ?_, ?_⟩
  · have actual := perform_refines _ _ _ _ _ performed
    unfold Result.outcome at actual
    rw [returned] at actual
    by_cases done : nextPhase worker output = .completed <;>
      cases event : output.event <;> simpa [done, event, evolved] using actual
  · intro done
    apply perform_return_event _ _ _ _ _ performed
    rw [returned]
    simp [done]

theorem MachineStep.peer {before after : State} {identifier : Nat} {event : Option AtomicEvent}
    (step : MachineStep before identifier event after) (query : Nat) (different : identifier ≠ query) :
    after.workers[query]? = before.workers[query]? := by
  cases step with
  | mk _ _ _ replaced _ _ _ _ => rw [replaced, List.getElem?_set_ne different]

theorem MachineStep.length {before after : State} {identifier : Nat} {event : Option AtomicEvent}
    (step : MachineStep before identifier event after) : after.workers.length = before.workers.length := by
  cases step with
  | mk _ _ _ replaced _ _ _ _ => rw [replaced, List.length_set]

theorem MachineStep.history {before after : State} {identifier : Nat} {event : Option AtomicEvent}
    (step : MachineStep before identifier event after) : Mutex.History before.shared after.shared := by
  cases step with
  | mk _ _ _ _ _ history _ _ => exact history

inductive Trace : State → List Nat → List (Nat × AtomicEvent) → State → Prop where
  | nil {state} : Trace state [] [] state
  | cons {before middle after identifier event selections events}
      (step : MachineStep before identifier event middle)
      (tail : Trace middle selections events after) :
      Trace before (identifier :: selections) (recordEvent identifier event events) after

theorem schedule_cons_ok (state : State) (identifier : Nat) (rest : List Nat)
    (result : State × List (Nat × AtomicEvent))
    (success : schedule state (identifier :: rest) = .ok result) :
    ∃ first tail, dispatch state identifier = .ok first ∧ schedule first.1 rest = .ok tail ∧
      result = (tail.1, recordEvent identifier first.2 tail.2) := by
  cases head : dispatch state identifier with
  | error fault => simp [schedule, head] at success
  | ok first =>
    cases next : schedule first.1 rest with
    | error fault => simp [schedule, head, next] at success
    | ok tail =>
      simp [schedule, head, next] at success
      exact ⟨first, tail, rfl, next, success.symm⟩

theorem schedule_trace (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (success : schedule state selections = .ok result) : Trace state selections result.2 result.1 := by
  induction selections generalizing state result with
  | nil => simp [schedule] at success; cases success; exact .nil
  | cons identifier rest induction =>
    obtain ⟨first, tail, head, next, same⟩ := schedule_cons_ok _ _ _ _ success
    rw [same]
    exact .cons (dispatch_refines _ _ _ head) (induction first.1 tail next)

private theorem appendHistory {before middle after : Mutex.State}
    (first : Mutex.History before middle) (last : Mutex.History middle after) : Mutex.History before after := by
  induction first with
  | refl => exact last
  | next step _ induction => exact .next step (induction last)

theorem Trace.history {before after : State} {selections : List Nat} {events : List (Nat × AtomicEvent)}
    (trace : Trace before selections events after) : Mutex.History before.shared after.shared := by
  induction trace with
  | nil => exact .refl
  | cons step _ induction => exact appendHistory step.history induction

theorem Trace.length {before after : State} {selections : List Nat} {events : List (Nat × AtomicEvent)}
    (trace : Trace before selections events after) : after.workers.length = before.workers.length := by
  induction trace with
  | nil => rfl
  | cons step _ induction => exact induction.trans step.length

theorem Trace.wellFormed {before after : State} {selections : List Nat} {events : List (Nat × AtomicEvent)}
    (trace : Trace before selections events after) (valid : Mutex.WellFormed before.shared) :
    Mutex.WellFormed after.shared := trace.history.wellFormed valid

private theorem toOption_ok {result : Except ε α} {value : α}
    (success : result.toOption = some value) : result = .ok value := by
  cases result <;> simp_all [Except.toOption]

theorem checkPost_sound (before after : State) (initial : BitVec 32)
    (accepted : checkPost before after initial = true) : Post before after initial := by
  cases originalAt : before.shared.mutex with
  | none => simp [checkPost, originalAt] at accepted
  | some original =>
    cases live : after.shared.mutex with
    | none => simp [checkPost, originalAt, live] at accepted
    | some record =>
      have checked := of_decide_eq_true (show decide _ = true by simpa only [checkPost, originalAt, live] using accepted)
      exact ⟨checked.1, checked.2.1, original, record, originalAt, live,
        checked.2.2.1, toOption_ok checked.2.2.2.1, toOption_ok checked.2.2.2.2.1, checked.2.2.2.2.2⟩

/-- Checking a finite schedule establishes its exact instruction trace and
independent endpoint contract. This does not assert that every schedule is
accepted, that every worker can advance, or that a scheduler is fair. -/
theorem verify_sound (state : State) (selections : List Nat) (result : State × List (Nat × AtomicEvent))
    (accepted : verify state selections = .ok result) :
    ∃ record initial, state.shared.mutex = some record ∧
      loadDWord (toMemory state.shared.shared.resources.space) record.config.dataAddress = .ok initial ∧
      schedule state selections = .ok result ∧ Trace state selections result.2 result.1 ∧ Post state result.1 initial := by
  by_cases running : started state = true
  · simp [verify, running] at accepted
  · cases selected : Mutex.registered state.shared with
    | error fault => simp [verify, running, selected, Except.mapError] at accepted
    | ok record =>
      by_cases held : record.holder.isSome = true
      · simp [verify, running, selected, held, Except.mapError] at accepted
      · cases read : loadDWord (toMemory state.shared.shared.resources.space) record.config.dataAddress with
        | error fault => simp [verify, running, selected, held, read, Except.mapError] at accepted
        | ok initial =>
          cases scheduled : schedule state selections with
          | error fault => simp [verify, running, selected, held, read, scheduled, Except.mapError] at accepted
          | ok output =>
            by_cases post : checkPost state output.1 initial = true
            · simp [verify, running, selected, held, read, scheduled, post, Except.mapError] at accepted
              cases accepted
              exact ⟨record, initial, Mutex.registered_ok _ _ selected, read, rfl,
                schedule_trace _ _ _ scheduled, checkPost_sound _ _ _ post⟩
            · simp [verify, running, selected, held, read, scheduled, post, Except.mapError] at accepted

end EDSL.OS.MutexReplay
