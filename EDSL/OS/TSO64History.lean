/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO64.Run
import EDSL.OS.AtomicFetchAddHistory64

namespace EDSL.OS.TSO64History
open X86

/-- Retain the actual typed RMW output; ordinary issue, blocked attempts,
RET and FIFO publication are silent positions in the OS arithmetic history.
Silence does not erase those actions from the scheduler's original trace. -/
def label : TSO64.Observation → Option Atomics64.FetchAddEvent
  | .rmw _ event => some event
  | _ => none

/-- An actual RMW observation retains its issuing context, prestate operands,
guarded current fetch, empty own FIFO and complete joint OS/CPU effect. The
scheduler index and the OS actor are intentionally separate identities. -/
theorem step_event_origin {before after : TSO64.State} {action : TSO64.Action}
    {tid : Nat} {event : Atomics64.FetchAddEvent}
    (success : TSO64.step before action = .ok (after, .rmw tid event)) :
    ∃ af worker instruction identifier machine,
      action = .issue tid af ∧ before.workers[tid]? = some worker ∧
      worker.phase ≠ .returned ∧ worker.pending = [] ∧
      TSO64.decode (TSO64.fetchCPU before worker) = .ok (.locked instruction) ∧
      Atomics64.FetchAddMachineEffect before.world worker.resources.actor identifier
        (TSO64.sharedCPU before worker) instruction (after.world, event) machine ∧
      after = TSO64.install before tid after.world
        { worker with context := .ofCPU machine.state } := by
  cases TSO64.step_origin success with
  | ordinary live running code caller fetched effect =>
    cases effect with
    | intro supported bounds decoded reads queue step finish => cases finish
  | rmw live running code caller fetched bounds empty grant effect =>
    exact ⟨_, _, _, _, _, rfl, live, running, empty, fetched, effect, rfl⟩

/-- Every successful default-policy scheduler action projects to a real checked OS operation
or an unchanged world. No desired value, future success, or arithmetic checker
is a premise. Machine origins remain in TSO64's separate effect theorems. -/
theorem step_history {before : TSO64.State} {action : TSO64.Action}
    {result : TSO64.State × TSO64.Observation}
    (success : TSO64.step before action = .ok result) :
    AtomicFetchAddHistory64.Step before.world (label result.2) result.1.world := by
  cases action with
  | issue tid af =>
    obtain ⟨worker, _, _, _, _, instruction, _, effect⟩ := TSO64.issue_effect success
    cases instruction with
    | ordinary instruction =>
      cases effect with
      | intro supported bounds decoded reads queue step finish =>
        cases finish <;> exact .idle
    | locked instruction =>
      cases effect with
      | blocked => exact .idle
      | rmw bounds empty decoded selected changed executed => exact .fetchAdd changed
  | drain tid =>
    obtain ⟨_, _, _, _, _, _, _, _, changed, same⟩ := TSO64.drain_effect_owned success
    rw [same]
    exact .mutate changed

/-- This is a projection of actual scheduling, including every silent action
and every other-cell RMW, rather than an alternative counter execution engine. -/
theorem schedule_history {before : TSO64.State} {actions : List TSO64.Action}
    {result : TSO64.State × List TSO64.Observation}
    (success : TSO64.schedule before actions = .ok result) :
    AtomicFetchAddHistory64.History before.world (result.2.map label) result.1.world := by
  induction actions generalizing before result with
  | nil =>
    have same : (before, []) = result := Except.ok.inj success
    subst result
    exact .refl
  | cons action actions ih =>
    obtain ⟨head, tail, first, following, same⟩ := TSO64.schedule_cons_ok success
    rw [same]
    exact .next (step_history first) (ih following)

/-- A selected persistent cell has a mathematical sequential history for every
successful finite schedule from current well-formed resources. Target reads
through quiet actions are derived from the OS reservation/frame theorems.

Identifier/thread labels below are client names only. In particular a function
of an OS event does not authenticate a scheduler tid, distinguish identical
zero-update occurrences, or supply invocation/RET intervals. -/
theorem schedule_sequential {Id Thread : Type} {before : TSO64.State}
    {actions : List TSO64.Action} {result : TSO64.State × List TSO64.Observation}
    (valid : TSO64.WellFormed before)
    (success : TSO64.schedule before actions = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : before.world.cells target = some cell)
    (identifier : Atomics64.FetchAddEvent → Id) (thread : Atomics64.FetchAddEvent → Thread)
    (prior : Word)
    (read : loadQWord (AddressSpace.toMemory before.world.legacy.shared.resources.space)
      cell.address = .ok prior) :
    ∃ final,
      loadQWord (AddressSpace.toMemory result.1.world.legacy.shared.resources.space)
        cell.address = .ok final ∧
      Concurrency.ModuloCounter.Sequential prior
        (AtomicFetchAddHistory64.selectedCalls target identifier thread (result.2.map label)) final :=
  (schedule_history success).project_exists valid.1 target cell live identifier thread prior read

/-- Current target authority and the persistent descriptor survive the entire
schedule. This is neither teardown nor a resource-releasing join. -/
theorem schedule_retained {before : TSO64.State} {actions : List TSO64.Action}
    {result : TSO64.State × List TSO64.Observation}
    (valid : TSO64.WellFormed before)
    (success : TSO64.schedule before actions = .ok result)
    (target : Atomics64.CellId64) (cell : Atomics64.Cell)
    (live : before.world.cells target = some cell) :
    result.1.world.cells target = some cell ∧
      Atomics64.ValidCell result.1.world.legacy.shared cell ∧
      Atomics64.reserved result.1.world cell.ticket.identifier = true :=
  (schedule_history success).retained valid.1 target cell live

end EDSL.OS.TSO64History

#audit_edsl
