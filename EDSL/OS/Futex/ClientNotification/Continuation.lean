/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientNotification.Continuation.Entry
import EDSL.Audit

set_option warningAsError true

namespace EDSL.OS.Futex.Clients.Notification
open X86

/-- A resumed WAIT needs exactly the enabled RET suffix, retaining its actual
historical private context rather than requesting new clobber values. -/
theorem resumed_completes {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {expected : BitVec 32} {actual : TSO.Worker}
    {outcome : Outcome client.operation} {flags rcx r11 : Word}
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (role : client.role = .wait expected)
    (found : state.suspended.machine.workers[worker]? = some actual)
    (context : actual.context = client.resumed outcome.raw flags rcx r11)
    (live : actual.returned = false) (free : state.suspended.pending worker = none)
    (empty : actual.buffer = []) :
    ∃ after returned, CompletesWithin 1 cohort worker expected state after ∧
      after.suspended.machine.workers[worker]? = some returned ∧
      returned.context = client.returned actual.context := by
  obtain ⟨after, returned, first, valid, atReturned, historical, done, _, frame⟩ :=
    resumed_ret_enabled admitted member found (by simp [role]) context live free empty
  exact ⟨after, returned,
    (returned_completes valid member role atReturned done).prepend first frame, atReturned, historical⟩

/-- Every current designated WAIT phase has a constructive suffix after
publication and queue clearance. `Policy.mismatch` explicitly requires
expected32 ≠ 1. Current resources and exact finite control derive each actual
physical/service step: unentered (≤6), pending (≤3), resumed (≤1), returned (0).
This is existential enabled continuation, without scheduler fairness or a
premise asserting future successful physical execution or service. -/
theorem worker_completes {cohort : Cohort} {state : State} {worker : Nat}
    {expected : BitVec 32} (policy : Policy cohort worker expected)
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker) :
    ∃ after, CompletesWithin 6 cohort worker expected state after := by
  obtain ⟨client, member, role⟩ := policy.designated
  have bound : worker < state.suspended.machine.workers.length := by
    rw [admitted.slots]
    exact (List.getElem_of_getElem? member).1
  let actual := state.suspended.machine.workers[worker]
  have found : state.suspended.machine.workers[worker]? = some actual := by
    simp only [List.getElem?_eq_getElem bound, actual]
  obtain ⟨controlled, atClient, control⟩ := admitted.control worker actual found
  have same : controlled = client := Option.some.inj (atClient.symm.trans member)
  subst controlled
  cases control with
  | running stage supported context live free fifo =>
    have empty : actual.buffer = [] := by simpa only [Stage.FIFO, Stage.bufferCondition, role] using fifo
    obtain ⟨after, finished, valid⟩ := running_finishes policy admitted member role published clear supported
      ⟨actual, found, context, live, free, empty⟩ 0 0 0
    exact ⟨after, finished.completes valid⟩
  | entered saved pending _ _ _ _ _ _ =>
    obtain ⟨after, finished, valid⟩ := pending_worker_finishes policy admitted published clear pending 0 0 0
    exact ⟨after, (finished.completes valid).mono (by decide)⟩
  | resumed outcome flags rcx r11 _ context live free empty _ =>
    obtain ⟨after, _, completed, _, _⟩ := resumed_completes admitted member role found context live free empty
    exact ⟨after, completed.mono (by decide)⟩
  | returned _ _ _ _ _ _ done _ _ _ =>
    exact ⟨state, (returned_completes admitted member role found done).mono (by decide)⟩
  | peerReturned peer _ _ _ _ => simp [role] at peer

/-- The constructive suffix is available after every accepted mixed prefix
following notification, including prefixes which have already resumed or
returned the designated worker. Safety remains trace-wide. -/
theorem trace_completes {cohort : Cohort} {before current : State} {worker : Nat}
    {expected : BitVec 32} {actions : List Runtime.Action} {observations : List Runtime.Observation}
    (policy : Policy cohort worker expected) (admitted : Admitted cohort before)
    (published : loadDWord before.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait before worker)
    (history : Runtime.Trace cohort.profile before actions observations current) :
    Futex.Notification.NoQueuedWait current worker ∧
      loadDWord current.suspended.machine.memory cohort.registration.address = .ok 1 ∧
      Admitted cohort current ∧ ∃ after, CompletesWithin 6 cohort worker expected current after := by
  obtain ⟨safe, word, valid⟩ := trace_preserves policy admitted published clear history
  exact ⟨safe, word, valid, worker_completes policy valid word safe⟩

end EDSL.OS.Futex.Clients.Notification

#audit_edsl
