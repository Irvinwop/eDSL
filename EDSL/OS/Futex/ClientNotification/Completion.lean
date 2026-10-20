/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientNotification.Base

set_option warningAsError true

namespace EDSL.OS.Futex.Clients.Notification
open X86

/-- A finite actual continuation through service resume and decoded RET.
Private clobbers are arbitrary full words; RAM and every peer are framed.
This is an existential enabled suffix, not fairness of an arbitrary scheduler. -/
def FinishesWithin (limit : Nat) (cohort : Cohort) (worker : Nat) (expected : BitVec 32)
    (flags rcx r11 : Word) (before after : State) : Prop :=
  ∃ actions observations returned client, ∃ outcome : Outcome (.wait expected),
    Runtime.Trace cohort.profile before actions observations after ∧ actions.length ≤ limit ∧
    cohort.clients[worker]? = some client ∧ client.role = .wait expected ∧
    after.suspended.machine.workers[worker]? = some returned ∧
    returned.returned = true ∧ returned.buffer = [] ∧
    returned.context.registers .rax = outcome.raw ∧
    returned.context.rip = client.returnTarget ∧
    returned.context.registers .rsp = client.entry.registers .rsp + 8 ∧
    returned.context.flags = flags ∧ returned.context.registers .rcx = rcx ∧
    returned.context.registers .r11 = r11 ∧
    after.suspended.machine.memory = before.suspended.machine.memory ∧
    (∀ query, query ≠ worker →
      after.suspended.machine.workers[query]? = before.suspended.machine.workers[query]? ∧
      after.suspended.pending query = before.suspended.pending query)

/-- A current typed readiness, current exact code and current return-stack
ownership construct the actual resume/RET suffix for any private clobbers. -/
theorem ready_finishes {cohort : Cohort} {state : State} {worker invocation pin : Nat}
    {expected : BitVec 32} {outcome : Outcome (.wait expected)} {origin : Origin}
    (admitted : Admitted cohort state)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, .ready outcome origin⟩)
    (flags rcx r11 : Word) :
    ∃ after, FinishesWithin 2 cohort worker expected flags rcx r11 state after ∧ Admitted cohort after := by
  obtain ⟨resumed, after, returned, client, member, resume, issue, live, done, empty, raw,
    target, stack, privateFlags, privateRcx, privateR11, memory, peers, _, valid⟩ :=
    ready_ret_enabled admitted found rfl flags rcx r11
  obtain ⟨actualClient, atActual, _, actualOperation⟩ := call_family admitted found
  have same : actualClient = client := Option.some.inj (atActual.symm.trans member)
  subst actualClient
  have role : client.role = .wait expected := by
    cases kind : client.role with
    | wait value =>
      have equal : Op.wait value = .wait expected := by
        simpa only [Client.operation, kind] using actualOperation
      exact congrArg Role.wait (Op.wait.inj equal)
    | publishPayloadWake | payloadPeer =>
      simp [Client.operation, kind] at actualOperation
  have first : Runtime.step cohort.profile state (.service (.resume invocation flags rcx r11)) =
      .ok (resumed, .serviced (.resume invocation flags rcx r11)) := by
    simp [Runtime.step, Futex.step, resume, Except.mapError]
  have last : Runtime.step cohort.profile resumed (.issue worker) =
      .ok (after, .physical (.machine (.retired worker none))) := by
    simp only at issue
    simp [Runtime.step, issue]
  refine ⟨after, ?_, valid⟩
  exact ⟨[.service (.resume invocation flags rcx r11), .issue worker],
    [.serviced (.resume invocation flags rcx r11), .physical (.machine (.retired worker none))],
    returned, client, outcome, .cons first (.cons last .nil), by simp,
    member, role, live, done, empty, raw, target, stack, privateFlags, privateRcx, privateR11,
    memory, peers⟩

/-- Prepending a memory/private-state stutter preserves the completion
contract. Only a single actual compare service transition uses this helper. -/
theorem FinishesWithin.prepend_compare {cohort : Cohort} {before middle after : State}
    {worker invocation : Nat} {expected : BitVec 32} {flags rcx r11 : Word}
    (first : Runtime.step cohort.profile before (.service (.compare invocation)) =
      .ok (middle, .serviced (.compare invocation)))
    (same : middle.suspended = before.suspended)
    (tail : FinishesWithin 2 cohort worker expected flags rcx r11 middle after) :
    FinishesWithin 3 cohort worker expected flags rcx r11 before after := by
  obtain ⟨actions, observations, returned, client, outcome, trace, short, member, role,
    live, done, empty, raw, target, stack, privateFlags, privateRcx, privateR11, memory, peers⟩ := tail
  refine ⟨.service (.compare invocation) :: actions, .serviced (.compare invocation) :: observations,
    returned, client, outcome, .cons first trace, ?_, member, role,
    live, done, empty, raw, target, stack, privateFlags, privateRcx, privateR11, ?_, ?_⟩
  · simp only [List.length_cons]
    omega
  · exact memory.trans (congrArg (fun s : Suspend.State => s.machine.memory) same)
  · intro query different
    obtain ⟨workers, pending⟩ := peers query different
    exact ⟨workers.trans (congrArg (fun s : Suspend.State => s.machine.workers[query]?) same),
      pending.trans (congrArg (fun s : Suspend.State => s.pending query) same)⟩


theorem FinishesWithin.mono {cohort : Cohort} {before after : State}
    {worker limit larger : Nat} {expected : BitVec 32} {flags rcx r11 : Word}
    (completed : FinishesWithin limit cohort worker expected flags rcx r11 before after)
    (bound : limit ≤ larger) :
    FinishesWithin larger cohort worker expected flags rcx r11 before after := by
  obtain ⟨actions, observations, returned, client, outcome, trace, short, rest⟩ := completed
  exact ⟨actions, observations, returned, client, outcome, trace, Nat.le_trans short bound, rest⟩

/-- With a live WAIT record after notification, no queued call remains. If
it has not yet compared, the persistent current mismatch enables EAGAIN;
otherwise its typed readiness enables completion. The witness has at most
three actual transitions and imposes no eventual scheduling assumption. -/
theorem pending_finishes {cohort : Cohort} {state : State} {worker invocation pin : Nat}
    {expected : BitVec 32} {phase : Phase (.wait expected)}
    (admitted : Admitted cohort state)
    (current : Futex.Notification.CurrentWord state cohort.registration 1)
    (different : expected ≠ 1) (clear : Futex.Notification.NoQueuedWait state worker)
    (found : state.calls invocation = some ⟨worker, .wait expected, pin, phase⟩)
    (flags rcx r11 : Word) :
    ∃ after, FinishesWithin 3 cohort worker expected flags rcx r11 state after ∧
      Admitted cohort after := by
  cases phase with
  | queued =>
    exact (clear _ _ found rfl (queued_queued _ _ _)).elim
  | ready outcome origin =>
    obtain ⟨after, completion, valid⟩ := ready_finishes admitted found flags rcx r11
    exact ⟨after, completion.mono (by decide), valid⟩
  | entered =>
    let compared := setPhase state invocation ⟨worker, .wait expected, pin, .entered⟩
      (.ready .waitAgain .mismatch)
    have compare : compareWait cohort.profile.service state invocation = .ok compared :=
      Futex.Notification.compare_mismatch_enabled admitted.runtime.service current (Ne.symm different) found
    have first : Runtime.step cohort.profile state (.service (.compare invocation)) =
        .ok (compared, .serviced (.compare invocation)) := by
      simp [Runtime.step, Futex.step, compare, Except.mapError]
    have atCompared : compared.calls invocation = some
        ⟨worker, .wait expected, pin, .ready .waitAgain .mismatch⟩ := by
      simp [compared, setPhase, putCall]
    obtain ⟨after, completion, valid⟩ :=
      ready_finishes (admitted_step admitted first) atCompared flags rcx r11
    exact ⟨after, FinishesWithin.prepend_compare first rfl completion, valid⟩


/-- A real currently pending designated worker suffices: its typed record and
phase are recovered from the current invariant and exact captured family. -/
theorem pending_worker_finishes {cohort : Cohort} {state : State} {worker : Nat}
    {expected : BitVec 32} {saved : Suspend.Saved} (policy : Policy cohort worker expected)
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1)
    (clear : Futex.Notification.NoQueuedWait state worker)
    (pending : state.suspended.pending worker = some saved) (flags rcx r11 : Word) :
    ∃ after, FinishesWithin 3 cohort worker expected flags rcx r11 state after ∧
      Admitted cohort after := by
  obtain ⟨pin, phase, found⟩ := policy.pending_call admitted pending
  exact pending_finishes admitted (currentWord admitted published) policy.mismatch clear found flags rcx r11

end EDSL.OS.Futex.Clients.Notification
