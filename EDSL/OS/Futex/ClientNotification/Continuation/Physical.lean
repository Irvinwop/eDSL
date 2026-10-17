/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientNotification.Trace
import EDSL.OS.Futex.ClientNotification.Completion

set_option warningAsError true

namespace EDSL.OS.Futex.Clients.Notification
open X86

/-- A suffix leaves RAM and every other worker's complete private machine and
pending invocation unchanged. Other workers may have nonempty FIFOs. -/
def PrivateFrame (worker : Nat) (before after : Suspend.State) : Prop :=
  after.machine.memory = before.machine.memory ∧
    ∀ query, query ≠ worker →
      after.machine.workers[query]? = before.machine.workers[query]? ∧
      after.pending query = before.pending query

theorem PrivateFrame.refl (worker : Nat) (state : Suspend.State) :
    PrivateFrame worker state state := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem PrivateFrame.trans {worker : Nat} {before middle after : Suspend.State}
    (first : PrivateFrame worker before middle) (last : PrivateFrame worker middle after) :
    PrivateFrame worker before after := by
  refine ⟨last.1.trans first.1, ?_⟩
  intro query different
  exact ⟨(last.2 query different).1.trans (first.2 query different).1,
    (last.2 query different).2.trans (first.2 query different).2⟩

/-- Concrete current running control, without any future-execution premise. -/
def RunningAt (client : Client) (worker : Nat) (state : Suspend.State) (stage : Stage) : Prop :=
  ∃ actual, state.machine.workers[worker]? = some actual ∧
    actual.context = stage.context client ∧ actual.returned = false ∧
    state.pending worker = none ∧ actual.buffer = []

/-- The shared decoder and the actual ordinary MOV semantics construct a
retiring physical step. Current cohort resources then enable its managed lift. -/
theorem running_mov_enabled {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {stage : Stage} {destination : Register} {value : BitVec 32}
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (supported : stage.Valid client.role)
    (instruction : stage.instruction client.role = .mov32 destination value)
    (running : RunningAt client worker state.suspended stage) :
    ∃ after, Runtime.step cohort.profile state (.issue worker) =
        .ok (after, .physical (.machine (.retired worker none))) ∧
      Admitted cohort after ∧ RunningAt client worker after.suspended (stage.next client.role) ∧
      PrivateFrame worker state.suspended after.suspended := by
  obtain ⟨actual, atWorker, context, live, free, empty⟩ := running
  have decoded : decodeAt (TSO.sharedState state.suspended.machine actual) =
      .ok (.mov32 destination value) := by
    rw [TSO.sharedState, context, ← instruction]
    exact decode_stage _ _ _ supported (admitted.protected _ _ member).2.2.1
  let output := executeMov32 (TSO.localState state.suspended.machine actual) destination value
  let physical : Suspend.State := {state.suspended with machine :=
    (TSO.install state.suspended.machine worker state.suspended.machine.memory
      (Threads.Context.ofState output) false [])}
  have issued : Suspend.issue state.suspended worker =
      .ok (physical, .machine (.retired worker none)) := by
    simp only [Suspend.issue, atWorker, live, Bool.false_eq_true, ↓reduceIte, free,
      decoded, Except.mapError, ok_bind]
    simp [Suspend.execute, TSO.execute,
      TSO.pendingStore, TSO.locked, TSO.loadAddress, executeInstruction, Except.mapError,
      empty, physical, output]
  obtain ⟨after, lifted, same, valid⟩ := issue_lift admitted issued
  have nextContext : Threads.Context.ofState output = (stage.next client.role).context client := by
    simpa only [output, TSO.localState, context] using
      (stage_mov supported instruction (StoreBuffer.view state.suspended.machine.memory actual.buffer)).2
  refine ⟨after, by simp [Runtime.step, lifted], valid, ?_, ?_⟩
  · rw [same]
    refine ⟨_, List.getElem?_set_self (List.getElem_of_getElem? atWorker).1,
      nextContext, rfl, free, rfl⟩
  · rw [same]
    refine ⟨rfl, ?_⟩
    intro query different
    exact ⟨List.getElem?_set_ne different.symm, rfl⟩

/-- Exact WAIT operation control executes SYSCALL and captures its own fresh
invocation. Classification and resource pinning are derived by `issue_lift`. -/
theorem running_wait_capture_enabled {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {expected : BitVec 32}
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (role : client.role = .wait expected)
    (running : RunningAt client worker state.suspended .operation) :
    ∃ after saved, Runtime.step cohort.profile state (.issue worker) =
        .ok (after, .physical (.entered worker state.suspended.nextCall)) ∧
      Admitted cohort after ∧ after.suspended.pending worker = some saved ∧
      saved.identifier = state.suspended.nextCall ∧ saved.worker = worker ∧
      client.Family saved.request ∧ PrivateFrame worker state.suspended after.suspended := by
  obtain ⟨actual, atWorker, context, live, free, empty⟩ := running
  have callContext : Stage.operation.context client = client.callContext := by
    simp [Client.callContext, Client.callStage, role]
  have decoded : decodeAt (TSO.sharedState state.suspended.machine actual) = .ok .syscall := by
    rw [TSO.sharedState, context]
    simpa only [Stage.instruction, role] using decode_stage client .operation _
      (by simp [Stage.Valid, role]) (admitted.protected _ _ member).2.2.1
  let request := client.request state.suspended.machine.memory
  let physical := Suspend.capture state.suspended worker request
  have issued : Suspend.issue state.suspended worker =
      .ok (physical, .entered worker state.suspended.nextCall) := by
    simp only [Suspend.issue, atWorker, live, Bool.false_eq_true, ↓reduceIte, free,
      decoded, Except.mapError, ok_bind]
    simp [Suspend.execute, empty,
      executeInstruction, TSO.sharedState, context, callContext, Except.mapError,
      physical, request, Client.request, MachineThreads.contextState]
  obtain ⟨after, lifted, same, valid⟩ := issue_lift admitted issued
  refine ⟨after, ⟨state.suspended.nextCall, worker, request⟩,
    by simp [Runtime.step, lifted], valid, ?_, rfl, rfl, ?_, ?_⟩
  · simp [same, physical, Suspend.capture]
  · exact ⟨by simp [role], rfl⟩
  · rw [same]
    refine ⟨rfl, ?_⟩
    intro query different
    exact ⟨rfl, by simp [physical, Suspend.capture, different]⟩

/-- An already resumed client executes the decoded RET using its current
protected stack. Its historical raw result and full private context survive. -/
theorem resumed_ret_enabled {cohort : Cohort} {state : State} {worker : Nat}
    {client : Client} {actual : TSO.Worker} {outcome : Outcome client.operation}
    {flags rcx r11 : Word}
    (admitted : Admitted cohort state) (member : cohort.clients[worker]? = some client)
    (atWorker : state.suspended.machine.workers[worker]? = some actual)
    (caller : client.role ≠ .payloadPeer)
    (context : actual.context = client.resumed outcome.raw flags rcx r11)
    (live : actual.returned = false) (free : state.suspended.pending worker = none)
    (empty : actual.buffer = []) :
    ∃ after returned, Runtime.step cohort.profile state (.issue worker) =
        .ok (after, .physical (.machine (.retired worker none))) ∧
      Admitted cohort after ∧ after.suspended.machine.workers[worker]? = some returned ∧
      returned.context = client.returned actual.context ∧ returned.returned = true ∧
      returned.buffer = [] ∧ PrivateFrame worker state.suspended after.suspended := by
  obtain ⟨_, _, code, stack, canonical, _, _⟩ := admitted.protected _ _ member
  have decoded : decodeAt (TSO.sharedState state.suspended.machine actual) = .ok .ret := by
    rw [TSO.sharedState, context]
    exact decode_resumed _ _ _ _ _ _ caller code
  have currentStack : readWord (StoreBuffer.view state.suspended.machine.memory actual.buffer)
      (actual.context.registers .rsp) = .ok client.returnTarget := by
    simpa only [context, resumed_rsp] using admitted.stackViews _ _ _ atWorker member
  have executed : executeInstruction (TSO.localState state.suspended.machine actual) .ret =
      .ok (.returned (MachineThreads.contextState (client.returned actual.context)
        (StoreBuffer.view state.suspended.machine.memory actual.buffer))) :=
    ret_context client actual.context _ currentStack canonical
  let physical : Suspend.State := {state.suspended with machine :=
    (TSO.install state.suspended.machine worker state.suspended.machine.memory
      (client.returned actual.context) true [])}
  have issued : Suspend.issue state.suspended worker =
      .ok (physical, .machine (.retired worker none)) := by
    simp only [Suspend.issue, atWorker, live, Bool.false_eq_true, ↓reduceIte, free,
      decoded, Except.mapError, ok_bind]
    simp [Suspend.execute, TSO.execute,
      TSO.pendingStore, TSO.locked, TSO.loadAddress, executed, Except.mapError, empty,
      Threads.Context.ofState, MachineThreads.contextState, physical]
  obtain ⟨after, lifted, same, valid⟩ := issue_lift admitted issued
  refine ⟨after, ⟨client.returned actual.context, true, []⟩,
    by simp [Runtime.step, lifted], valid, ?_, rfl, rfl, rfl, ?_⟩
  · rw [same]
    exact List.getElem?_set_self (List.getElem_of_getElem? atWorker).1
  · rw [same]
    refine ⟨rfl, ?_⟩
    intro query different
    exact ⟨List.getElem?_set_ne different.symm, rfl⟩

end EDSL.OS.Futex.Clients.Notification
