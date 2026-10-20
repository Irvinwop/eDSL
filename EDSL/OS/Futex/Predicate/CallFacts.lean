/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.Predicate.Admission
import EDSL.OS.Futex.Notification

set_option warningAsError true

namespace EDSL.OS.Futex.Predicate
open X86

/-- Current service records are bound to their real saved request, selected
member and classified operation. Historical capture RAM remains historical. -/
theorem Admitted.call_family {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) {identifier : Nat} {call : Call}
    (found : state.calls identifier = some call) :
    ∃ kind saved, cohort.clients[call.worker]? = some kind ∧
      state.suspended.pending call.worker = some saved ∧ saved.identifier = identifier ∧
      kind.Family saved.request ∧ kind.operation = call.op := by
  obtain ⟨saved, pending, identity, _, classified⟩ := (admitted.runtime.service.calls _ _ found).saved
  obtain ⟨kind, member, family⟩ := admitted.pending_family pending
  have actual := (Kind.family_classifies (admitted.static.descriptors _ _ member) family).1
  exact ⟨kind, saved, member, pending, identity, family, Except.ok.inj (actual.symm.trans classified)⟩

/-- A WAIT operation identifies an actual loop member, its sole worker and
expected zero. No queue state or future service result is assumed. -/
theorem Admitted.wait_call {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) {identifier : Nat} {call : Call} {observed : BitVec 32}
    (found : state.calls identifier = some call) (waits : call.op = .wait observed) :
    ∃ client, cohort.clients[call.worker]? = some (.waitLoop client) ∧
      call.worker = cohort.waiter ∧ observed = 0 := by
  obtain ⟨kind, _, member, _, _, _, operation⟩ := admitted.call_family found
  cases kind with
  | waitLoop client =>
    have equal : Op.wait 0 = .wait observed := operation.trans waits
    exact ⟨client, member, (admitted.static.descriptors _ _ member).2.2.2.2,
      (Op.wait.inj equal).symm⟩
  | legacy client =>
    have role := (admitted.static.descriptors _ _ member).2
    have wakes : client.operation = .wakeOne := by
      rcases role with publisher | peer
      · simp [Clients.Client.operation, publisher]
      · simp [Clients.Client.operation, peer]
    have impossible : Op.wakeOne = .wait observed := (wakes.symm.trans operation).trans waits
    cases impossible

theorem Admitted.expectedFor {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) : Futex.Notification.ExpectedFor state cohort.waiter 0 := by
  intro identifier call observed found _ waits
  obtain ⟨_, _, _, zero⟩ := admitted.wait_call found waits
  exact zero

theorem Admitted.onlyWaiter {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state) : Futex.Notification.OnlyWaiter state cohort.waiter := by
  intro identifier call observed found waits
  obtain ⟨_, _, worker, _⟩ := admitted.wait_call found waits
  exact worker

/-- Publication is interpreted in actual current resource RAM, not the saved
syscall snapshot. Equality covers every physical byte and permission. -/
theorem Admitted.currentWord {cohort : Cohort} {state : Futex.State}
    (admitted : Admitted cohort state)
    (published : loadDWord state.suspended.machine.memory cohort.registration.address = .ok 1) :
    Futex.Notification.CurrentWord state cohort.registration 1 :=
  ⟨admitted.registration, by rw [admitted.runtime.memory]; exact published⟩

theorem Admitted.loop_call_operation {cohort : Cohort} {state : Futex.State}
    {worker identifier : Nat} {client : Client} {call : Call}
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some (.waitLoop client))
    (found : state.calls identifier = some call) (same : call.worker = worker) : call.op = .wait 0 := by
  obtain ⟨kind, _, atKind, _, _, _, operation⟩ := admitted.call_family found
  rw [same] at atKind
  cases Option.some.inj (atKind.symm.trans member)
  exact operation.symm

/-- Actual pending identity determines the current typed call and phase,
including repeated invocations of the same loop worker. -/
theorem Admitted.pending_loop_call {cohort : Cohort} {state : Futex.State}
    {worker : Nat} {client : Client} {saved : Suspend.Saved}
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some (.waitLoop client))
    (pending : state.suspended.pending worker = some saved) :
    ∃ pin phase, state.calls saved.identifier = some ⟨worker, .wait 0, pin, phase⟩ := by
  obtain ⟨call, found, same⟩ := admitted.runtime.service.pending _ _ pending
  have operation := admitted.loop_call_operation member found same
  rcases call with ⟨owner, op, pin, phase⟩
  dsimp only at same operation
  subst owner
  subst op
  exact ⟨pin, phase, found⟩

end EDSL.OS.Futex.Predicate

#audit_edsl
