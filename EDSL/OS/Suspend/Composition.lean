/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Suspend.History
import EDSL.OS.Suspend.Frames

namespace EDSL.OS.Suspend
open X86

theorem Trace.wellFormed {before after : State} {actions : List Action} {observations : List Observation}
    (trace : Trace before actions observations after) (valid : WellFormed before) : WellFormed after := by
  induction trace with
  | nil => exact valid
  | cons first tail ih => exact ih (valid.step first)

theorem schedule_wellFormed {state : State} (valid : WellFormed state) {actions : List Action}
    {result : State × List Observation} (success : schedule state actions = .ok result) :
    WellFormed result.1 := (schedule_trace _ _ _ success).wellFormed valid

/-- Arbitrary actual prefixes retain the current pending-call invariant,
full memory frame and exact fresh-call frontier. No successful future return
or service result is an admission condition. -/
theorem prefix_safety {state : State} (valid : WellFormed state) {actions : List Action}
    {result : State × List Observation} (success : schedule state actions = .ok result) :
    WellFormed result.1 ∧ TSO.MemoryFrame state.machine.memory result.1.machine.memory ∧
      result.1.nextCall = state.nextCall + enteredCount result.2 :=
  ⟨schedule_wellFormed valid success, schedule_memory_frame valid success, schedule_call_count success⟩

/-- Every registered pending caller can be selected while parked. Selection
retains its complete machine and OS-wrapper state and never fetches ahead. -/
theorem pending_issue {state : State} (valid : WellFormed state) {identifier : Nat} {saved : Saved}
    (pending : state.pending identifier = some saved) :
    issue state identifier = .ok (state, .parked identifier saved.identifier) := by
  obtain ⟨worker, live, running, _, _⟩ := (valid.pending identifier saved pending).live
  exact (IssueEffect.parked live running pending).success

/-- Current invariants construct the mechanism's completion for any external
raw result and permitted private clobbers. This asserts no Linux service policy
or eventual completion. Peers need not have empty store buffers. -/
theorem resume_available {state : State} (valid : WellFormed state) {identifier : Nat} {saved : Saved}
    (pending : state.pending identifier = some saved) (raw flags rcx r11 : Word) :
    ∃ after,
      resume state identifier saved.identifier raw flags rcx r11 = .ok after ∧
      WellFormed after ∧ after.machine.memory = state.machine.memory ∧
      after.pending identifier = none ∧ after.nextCall = state.nextCall ∧
      ∀ query, identifier ≠ query → after.machine.workers[query]? = state.machine.workers[query]? := by
  have current := valid.pending identifier saved pending
  obtain ⟨worker, live, running, empty, context⟩ := current.live
  let after : State := { state with
    machine := TSO.install state.machine identifier state.machine.memory
      (.ofState (X86.resumeAt saved.request state.machine.memory raw flags rcx r11)) false []
    pending := fun query => if query = identifier then none else state.pending query }
  have completed : resume state identifier saved.identifier raw flags rcx r11 = .ok after :=
    resume_success raw flags rcx r11 live running pending rfl current.owner empty
  exact ⟨after, completed, valid.resume completed, resume_memory completed,
    resume_consumed completed, resume_nextCall completed,
    fun _ different => resume_peer different completed⟩

/-- A returned caller cannot retain a pending call. Actual RET is distinct
from parking and resumption; pending calls require an unreturned caller. -/
theorem WellFormed.no_pending_after_all_returns {state : State} (valid : WellFormed state)
    (returned : Returned state) : ∀ identifier, state.pending identifier = none := by
  intro identifier
  cases pending : state.pending identifier with
  | none => rfl
  | some saved =>
    obtain ⟨worker, live, running, _, _⟩ := (valid.pending identifier saved pending).live
    have actual := returned worker (List.mem_of_getElem? live)
    simp [running] at actual

theorem WellFormed.finished_iff {state : State} (valid : WellFormed state) :
    Finished state ↔ TSO.Finished state.machine :=
  ⟨fun finished => finished.1, fun finished =>
    ⟨finished, valid.no_pending_after_all_returns finished.1⟩⟩

/-- A genuine pending caller admits an infinite parked trace with no further
user instructions. There is no hidden fairness or service-progress assertion. -/
def parked_forever {state : State} (valid : WellFormed state) {identifier : Nat} {saved : Saved}
    (pending : state.pending identifier = some saved) : InfiniteTrace state :=
  ⟨fun _ => state, fun _ => .issue identifier,
    fun _ => .parked identifier saved.identifier, rfl,
    fun _ => pending_issue valid pending⟩

end EDSL.OS.Suspend
