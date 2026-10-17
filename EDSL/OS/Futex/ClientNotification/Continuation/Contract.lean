/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientNotification.Continuation.Physical

set_option warningAsError true

namespace EDSL.OS.Futex.Clients.Notification
open X86

/-- Independent final WAIT contract. The full private return context belongs
to a typed WAIT outcome, with its historical flags/RCX/R11. Zero and EAGAIN
are syscall results; neither asserts that a user predicate is satisfied. -/
def ReturnedWait (client : Client) (expected : BitVec 32) (actual : TSO.Worker) : Prop :=
  actual.returned = true ∧ actual.buffer = [] ∧
    ∃ outcome : Outcome (.wait expected), ∃ flags rcx r11 : Word,
      actual.context = client.returned (client.resumed outcome.raw flags rcx r11) ∧
      actual.context.registers .rax = outcome.raw ∧
      (outcome.raw = 0 ∨ outcome.raw = -(BitVec.ofNat 64 11)) ∧
      actual.context.rip = client.returnTarget ∧
      actual.context.registers .rsp = client.entry.registers .rsp + 8

/-- A bounded actual runtime suffix ending at the original client's RET,
with RAM, all peers, and current admission resources retained. The bound counts
runtime transitions, not hardware instructions or elapsed cycles. No new
clobbers are demanded when the worker has already resumed or returned. -/
def CompletesWithin (limit : Nat) (cohort : Cohort) (worker : Nat) (expected : BitVec 32)
    (before after : State) : Prop :=
  ∃ actions observations actual client,
    Runtime.Trace cohort.profile before actions observations after ∧ actions.length ≤ limit ∧
    cohort.clients[worker]? = some client ∧ client.role = .wait expected ∧
    after.suspended.machine.workers[worker]? = some actual ∧ ReturnedWait client expected actual ∧
    after.suspended.pending worker = none ∧
    PrivateFrame worker before.suspended after.suspended ∧ Admitted cohort after

private theorem outcome_cast_raw {op other : Op} (same : op = other) (outcome : Outcome op) :
    (same ▸ outcome).raw = outcome.raw := by
  cases same
  rfl

theorem returned_wait_context {client : Client} {expected : BitVec 32} {actual : TSO.Worker}
    {outcome : Outcome client.operation} {flags rcx r11 : Word}
    (role : client.role = .wait expected)
    (context : actual.context = client.returned (client.resumed outcome.raw flags rcx r11))
    (done : actual.returned = true) (empty : actual.buffer = []) :
    ReturnedWait client expected actual := by
  have operation : client.operation = .wait expected := by simp [Client.operation, role]
  let result : Outcome (.wait expected) := operation ▸ outcome
  have raw : result.raw = outcome.raw := outcome_cast_raw operation outcome
  refine ⟨done, empty, result, flags, rcx, r11, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [raw] using context
  · simp [context, Client.returned, Client.resumed, raw]
  · cases result <;> simp [Outcome.raw]
  · simp [context, Client.returned]
  · simp [context, Client.returned, resumed_rsp]

/-- A returned current WAIT control yields the independent final contract.
The finite-control invariant supplies the actual historical private fields. -/
theorem returned_wait_of_control {client : Client} {expected : BitVec 32} {worker : Nat}
    {state : Suspend.State} {actual : TSO.Worker}
    (role : client.role = .wait expected) (control : WorkerControl client worker state actual)
    (done : actual.returned = true) :
    ReturnedWait client expected actual ∧ state.pending worker = none := by
  cases control with
  | running _ _ _ live _ _ => simp [done] at live
  | entered _ _ _ _ _ live _ _ => simp [done] at live
  | resumed _ _ _ _ _ _ live _ _ _ => simp [done] at live
  | returned outcome flags rcx r11 caller context _ free empty _ =>
    exact ⟨returned_wait_context role context done empty, free⟩
  | peerReturned peer _ _ _ _ => simp [role] at peer

theorem CompletesWithin.mono {cohort : Cohort} {before after : State}
    {worker limit larger : Nat} {expected : BitVec 32}
    (completed : CompletesWithin limit cohort worker expected before after) (bound : limit ≤ larger) :
    CompletesWithin larger cohort worker expected before after := by
  obtain ⟨actions, observations, actual, client, trace, short, rest⟩ := completed
  exact ⟨actions, observations, actual, client, trace, Nat.le_trans short bound, rest⟩

theorem CompletesWithin.prepend {cohort : Cohort} {before middle after : State}
    {worker limit : Nat} {expected : BitVec 32} {action : Runtime.Action}
    {observation : Runtime.Observation}
    (first : Runtime.step cohort.profile before action = .ok (middle, observation))
    (frame : PrivateFrame worker before.suspended middle.suspended)
    (tail : CompletesWithin limit cohort worker expected middle after) :
    CompletesWithin (limit + 1) cohort worker expected before after := by
  obtain ⟨actions, observations, actual, client, trace, short, member, role,
    found, returned, free, framed, valid⟩ := tail
  refine ⟨action :: actions, observation :: observations, actual, client, .cons first trace,
    ?_, member, role, found, returned, free, frame.trans framed, valid⟩
  simp only [List.length_cons]
  omega

/-- Prepending an actual private instruction or capture keeps every existing
pending completion guarantee, including the caller's full clobber choices. -/
theorem FinishesWithin.prepend {cohort : Cohort} {before middle after : State}
    {worker limit : Nat} {expected : BitVec 32} {flags rcx r11 : Word}
    {action : Runtime.Action} {observation : Runtime.Observation}
    (first : Runtime.step cohort.profile before action = .ok (middle, observation))
    (frame : PrivateFrame worker before.suspended middle.suspended)
    (tail : FinishesWithin limit cohort worker expected flags rcx r11 middle after) :
    FinishesWithin (limit + 1) cohort worker expected flags rcx r11 before after := by
  obtain ⟨actions, observations, actual, client, outcome, trace, short, member, role,
    found, done, empty, raw, target, stack, privateFlags, privateRcx, privateR11, memory, peers⟩ := tail
  have framed := frame.trans ⟨memory, peers⟩
  refine ⟨action :: actions, observation :: observations, actual, client, outcome, .cons first trace,
    ?_, member, role, found, done, empty, raw, target, stack, privateFlags, privateRcx, privateR11,
    framed.1, framed.2⟩
  simp only [List.length_cons]
  omega

/-- The stronger existing pending-only API embeds without changing it or
weakening its caller-chosen full private clobber guarantees. -/
theorem FinishesWithin.completes {cohort : Cohort} {before after : State}
    {worker limit : Nat} {expected : BitVec 32} {flags rcx r11 : Word}
    (finished : FinishesWithin limit cohort worker expected flags rcx r11 before after)
    (admitted : Admitted cohort after) :
    CompletesWithin limit cohort worker expected before after := by
  obtain ⟨actions, observations, actual, client, outcome, trace, short, member, role,
    found, done, _, _, _, _, _, _, _, memory, peers⟩ := finished
  obtain ⟨controlled, atClient, control⟩ := admitted.control _ _ found
  have same : controlled = client := Option.some.inj (atClient.symm.trans member)
  subst controlled
  obtain ⟨returned, free⟩ := returned_wait_of_control role control done
  exact ⟨actions, observations, actual, client, trace, short, member, role, found,
    returned, free, ⟨memory, peers⟩, admitted⟩

/-- A worker which has already returned needs zero further transitions. -/
theorem returned_completes {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {expected : BitVec 32} {actual : TSO.Worker}
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (role : client.role = .wait expected)
    (found : state.suspended.machine.workers[worker]? = some actual)
    (done : actual.returned = true) : CompletesWithin 0 cohort worker expected state state := by
  obtain ⟨controlled, atClient, control⟩ := admitted.control _ _ found
  have same : controlled = client := Option.some.inj (atClient.symm.trans member)
  subst controlled
  obtain ⟨returned, free⟩ := returned_wait_of_control role control done
  exact ⟨[], [], actual, client, .nil, by simp, member, role, found,
    returned, free, .refl _ _, admitted⟩

end EDSL.OS.Futex.Clients.Notification
