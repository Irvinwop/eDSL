/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.CallFacts
import EDSL.OS.Futex.Predicate.Contract
import EDSL.OS.Futex.Predicate.Raw.Control

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86

/-- The complete shared RAM and every other worker's complete record and
pending invocation are unchanged. Peer FIFOs may be nonempty, even after RET. -/
def PrivateFrame (worker : Nat) (before after : Suspend.State) : Prop :=
  after.machine.memory = before.machine.memory ∧
    ∀ peer, peer ≠ worker →
      after.machine.workers[peer]? = before.machine.workers[peer]? ∧
      after.pending peer = before.pending peer

theorem PrivateFrame.refl (worker : Nat) (state : Suspend.State) :
    PrivateFrame worker state state := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem PrivateFrame.trans {worker : Nat} {before middle after : Suspend.State}
    (first : PrivateFrame worker before middle) (last : PrivateFrame worker middle after) :
    PrivateFrame worker before after := by
  refine ⟨last.1.trans first.1, ?_⟩
  intro peer different
  exact ⟨(last.2 peer different).1.trans (first.2 peer different).1,
    (last.2 peer different).2.trans (first.2 peer different).2⟩

/-- Constructive completion against the independent observable return
contract. The witness is an actual finite runtime trace, counted in runtime
actions, and retains current resource admission and every peer's private state. -/
def CompletesWithin (limit : Nat) (cohort : Cohort) (worker : Nat) (client : Client)
    (before after : Futex.State) : Prop :=
  ∃ actions observations actual,
    Runtime.Trace cohort.profile before actions observations after ∧
    actions.length ≤ limit ∧
    Returns client cohort.registration.address after.suspended worker actual ∧
    Admitted cohort after ∧ PrivateFrame worker before.suspended after.suspended

theorem CompletesWithin.mono {limit larger : Nat} {cohort : Cohort} {worker : Nat}
    {client : Client} {before after : Futex.State}
    (completed : CompletesWithin limit cohort worker client before after) (bound : limit ≤ larger) :
    CompletesWithin larger cohort worker client before after := by
  obtain ⟨actions, observations, actual, trace, length, returned, admitted, frame⟩ := completed
  exact ⟨actions, observations, actual, trace, Nat.le_trans length bound, returned, admitted, frame⟩

theorem CompletesWithin.prepend {limit : Nat} {cohort : Cohort} {worker : Nat}
    {client : Client} {before middle after : Futex.State}
    {action : Runtime.Action} {observation : Runtime.Observation}
    (completed : CompletesWithin limit cohort worker client middle after)
    (step : Runtime.step cohort.profile before action = .ok (middle, observation))
    (frame : PrivateFrame worker before.suspended middle.suspended) :
    CompletesWithin (limit + 1) cohort worker client before after := by
  obtain ⟨actions, observations, actual, trace, length, returned, admitted, finalFrame⟩ := completed
  exact ⟨action :: actions, observation :: observations, actual, .cons step trace,
    Nat.succ_le_succ length, returned, admitted, frame.trans finalFrame⟩

/-- The suffix issues only its own loop or compares/resumes an actual current
WAIT0 call of that worker. Drains and unrelated service actions are excluded. -/
def CompletionAction (worker : Nat) (state : Futex.State) : Runtime.Action → Prop
  | .issue selected => selected = worker
  | .service (.compare invocation) | .service (.resume invocation _ _ _) =>
      ∃ call, state.calls invocation = some call ∧ call.worker = worker ∧ call.op = .wait 0
  | _ => False

/-- An actual runtime trace with the selected worker/call checked at every
intermediate state, rather than just an unchecked list of action labels. -/
inductive CompletionTrace (profile : Physical.Profile) (worker : Nat) :
    Futex.State → List Runtime.Action → List Runtime.Observation → Futex.State → Prop where
  | nil {state} : CompletionTrace profile worker state [] [] state
  | cons {before middle after action observation actions observations}
      (selected : CompletionAction worker before action)
      (first : Runtime.step profile before action = .ok (middle, observation))
      (tail : CompletionTrace profile worker middle actions observations after) :
      CompletionTrace profile worker before (action :: actions) (observation :: observations) after

theorem CompletionTrace.runtime {profile : Physical.Profile} {worker : Nat}
    {before after : Futex.State} {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (trace : CompletionTrace profile worker before actions observations after) :
    Runtime.Trace profile before actions observations after := by
  induction trace with
  | nil => exact .nil
  | cons _ first _ ih => exact .cons first ih

/-- A strengthening of the independent completion relation that also exposes
selection of only the loop's issues and its own current typed service calls. -/
def SelectedCompletesWithin (limit : Nat) (cohort : Cohort) (worker : Nat) (client : Client)
    (before after : Futex.State) : Prop :=
  ∃ actions observations actual,
    CompletionTrace cohort.profile worker before actions observations after ∧
    actions.length ≤ limit ∧
    Returns client cohort.registration.address after.suspended worker actual ∧
    Admitted cohort after ∧ PrivateFrame worker before.suspended after.suspended

theorem SelectedCompletesWithin.forget {limit : Nat} {cohort : Cohort} {worker : Nat}
    {client : Client} {before after : Futex.State}
    (completed : SelectedCompletesWithin limit cohort worker client before after) :
    CompletesWithin limit cohort worker client before after := by
  obtain ⟨actions, observations, actual, trace, length, returned, admitted, frame⟩ := completed
  exact ⟨actions, observations, actual, trace.runtime, length, returned, admitted, frame⟩

theorem SelectedCompletesWithin.mono {limit larger : Nat} {cohort : Cohort} {worker : Nat}
    {client : Client} {before after : Futex.State}
    (completed : SelectedCompletesWithin limit cohort worker client before after)
    (bound : limit ≤ larger) : SelectedCompletesWithin larger cohort worker client before after := by
  obtain ⟨actions, observations, actual, trace, length, returned, admitted, frame⟩ := completed
  exact ⟨actions, observations, actual, trace, Nat.le_trans length bound, returned, admitted, frame⟩

theorem SelectedCompletesWithin.prepend {limit : Nat} {cohort : Cohort} {worker : Nat}
    {client : Client} {before middle after : Futex.State}
    {action : Runtime.Action} {observation : Runtime.Observation}
    (completed : SelectedCompletesWithin limit cohort worker client middle after)
    (selected : CompletionAction worker before action)
    (step : Runtime.step cohort.profile before action = .ok (middle, observation))
    (frame : PrivateFrame worker before.suspended middle.suspended) :
    SelectedCompletesWithin (limit + 1) cohort worker client before after := by
  obtain ⟨actions, observations, actual, trace, length, returned, admitted, finalFrame⟩ := completed
  exact ⟨action :: actions, observation :: observations, actual, .cons selected step trace,
    Nat.succ_le_succ length, returned, admitted, frame.trans finalFrame⟩

namespace Completion

/-- These are upper bounds for the actual instruction/service suffix, not
hardware cycles. In particular a stale comparison of zero still costs fourteen. -/
def remaining : Point → Nat
  | .load => 4
  | .compare observed => if observed = 0 then 14 else 3
  | .branch observed => if observed = 0 then 13 else 2
  | .number => 12
  | .operation => 11
  | .syscall => 10
  | .resumed _ => 7
  | .retryCompare => 6
  | .retryBranch => 5
  | .done _ => 1

theorem remaining_le (point : Point) : remaining point ≤ 14 := by
  cases point <;> simp only [remaining] <;> first | decide | (split <;> decide)

/-- Internal current execution witness. Historical flags/RCX/R11 are left in
the actual context, including on every already-resumed cut. -/
def RunningAt (client : Client) (worker : Nat) (state : Suspend.State) (point : Point) : Prop :=
  ∃ actual, state.machine.workers[worker]? = some actual ∧
    Running client point actual.context ∧ actual.returned = false ∧
    state.pending worker = none ∧ actual.buffer = []

/-- A current cut and its remaining action bound. This is a proof-internal
classification; the independent final contract contains none of these controls. -/
inductive Cut (client : Client) (worker : Nat) (state : Futex.State) : Nat → Prop where
  | running {point : Point} (current : RunningAt client worker state.suspended point) :
      Cut client worker state (remaining point)
  | entered {saved : Suspend.Saved} {pin : Nat}
      (pending : state.suspended.pending worker = some saved)
      (call : state.calls saved.identifier = some ⟨worker, .wait 0, pin, .entered⟩) :
      Cut client worker state 9
  | ready {saved : Suspend.Saved} {pin : Nat} {outcome : Outcome (.wait 0)} {origin : Origin}
      (pending : state.suspended.pending worker = some saved)
      (call : state.calls saved.identifier = some ⟨worker, .wait 0, pin, .ready outcome origin⟩) :
      Cut client worker state 8
  | returned {actual : TSO.Worker}
      (selected : state.suspended.machine.workers[worker]? = some actual)
      (done : actual.returned = true) : Cut client worker state 0

theorem pending_cut {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} {saved : Suspend.Saved} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (clear : Futex.Notification.NoQueuedWait state worker)
    (pending : state.suspended.pending worker = some saved) :
    ∃ count, count ≤ 9 ∧ Cut client worker state count := by
  obtain ⟨pin, phase, found⟩ := admitted.pending_loop_call member pending
  cases phase with
  | entered => exact ⟨9, by decide, .entered pending found⟩
  | ready outcome origin => exact ⟨8, by decide, .ready pending found⟩
  | queued => exact (clear saved.identifier _ found rfl (queued_queued _ _ _)).elim

theorem current_cut {cohort : Cohort} {state : Futex.State} {worker : Nat}
    {client : Client} (admitted : Admitted cohort state)
    (member : cohort.clients[worker]? = some (.waitLoop client))
    (clear : Futex.Notification.NoQueuedWait state worker) :
    ∃ count, count ≤ 14 ∧ Cut client worker state count := by
  have index : worker < state.suspended.machine.workers.length := by
    rw [admitted.slots]
    exact (List.getElem_of_getElem? member).1
  let actual := state.suspended.machine.workers[worker]
  have found : state.suspended.machine.workers[worker]? = some actual :=
    List.getElem?_eq_getElem index
  obtain ⟨kind, atKind, control⟩ := admitted.control worker actual found
  cases Option.some.inj (atKind.symm.trans member)
  change LoopControl cohort.registration.address client worker state.suspended actual at control
  cases control with
  | running point current _ live free empty =>
    exact ⟨remaining point, remaining_le point, .running ⟨actual, found, current, live, free, empty⟩⟩
  | entered saved pending _ _ _ _ _ =>
    obtain ⟨count, bound, cut⟩ := pending_cut admitted member clear pending
    exact ⟨count, Nat.le_trans bound (by decide), cut⟩
  | returned _ _ _ _ _ done _ _ => exact ⟨0, Nat.zero_le _, .returned found done⟩

end Completion
end EDSL.OS.Futex.Predicate

#audit_edsl
