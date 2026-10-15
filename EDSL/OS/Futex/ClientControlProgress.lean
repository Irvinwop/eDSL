/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientControlStages

set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

theorem WorkerControl.issue_selected {client : Client} {worker : Nat} {state after : Suspend.State}
    {before : TSO.Worker} {observation : Suspend.Observation}
    (control : WorkerControl client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (code : CodeAt state.machine.memory client.entry.rip client.role.bytes)
    (stack : readWord (StoreBuffer.view state.machine.memory before.buffer)
      (client.entry.registers .rsp) = .ok client.returnTarget)
    (canonical : X86.canonical client.returnTarget = true)
    (frame : client.Published state.machine.memory → client.Published after.machine.memory)
    (actual : Suspend.issue state worker = .ok (after, observation)) :
    ∃ selected, after.machine.workers[worker]? = some selected ∧ WorkerControl client worker after selected := by
  have bound := (List.getElem_of_getElem? atWorker).1
  cases control with
  | entered saved pending owner family context live empty published =>
    have same : (after, observation) = (state, .parked worker saved.identifier) := by
      simpa [Suspend.issue, atWorker, live, pending] using actual.symm
    cases same
    exact ⟨before, atWorker, .entered saved pending owner family context live empty published⟩
  | returned outcome flags rcx r11 caller context done free empty published =>
    simp [Suspend.issue, atWorker, done] at actual
  | peerReturned peer context done free fifo =>
    simp [Suspend.issue, atWorker, done] at actual
  | resumed outcome flags rcx r11 caller context live free empty published =>
    have decoded : decodeAt (TSO.sharedState state.machine before) = .ok .ret := by
      rw [TSO.sharedState, context]
      exact decode_resumed _ _ _ _ _ _ caller code
    have returned := ret_context client (client.resumed outcome.raw flags rcx r11)
      (StoreBuffer.view state.machine.memory before.buffer)
      (by simpa only [resumed_rsp] using stack) canonical
    have executed : executeInstruction (TSO.localState state.machine before) .ret = .ok
        (.returned (MachineThreads.contextState
          (client.returned (client.resumed outcome.raw flags rcx r11))
          (StoreBuffer.view state.machine.memory before.buffer))) := by
      simpa only [TSO.localState, context] using returned
    have same : (after, observation) =
        ({state with machine := (TSO.install state.machine worker state.machine.memory
          (client.returned (client.resumed outcome.raw flags rcx r11)) true [])}, .machine (.retired worker none)) := by
      simpa [Suspend.issue, atWorker, live, free, decoded, Suspend.execute, TSO.execute,
        TSO.pendingStore, TSO.locked, TSO.loadAddress, executed, Except.mapError, empty,
        Threads.Context.ofState, MachineThreads.contextState] using actual.symm
    cases same
    exact ⟨_, List.getElem?_set_self bound,
      .returned outcome flags rcx r11 caller rfl rfl free rfl published⟩
  | running stage supported context live free fifo =>
    have expected : decodeAt (TSO.sharedState state.machine before) = .ok (stage.instruction client.role) := by
      rw [TSO.sharedState, context]
      exact decode_stage _ _ _ supported code
    cases Suspend.issue_effect _ _ _ actual with
    | parked found running pending =>
      simp [free] at pending
    | @entered selected request found running pending decoded empty executed stepped user continuation =>
      have selectedEq := Option.some.inj (atWorker.symm.trans found)
      subst selected
      have syscall := Except.ok.inj (expected.symm.trans decoded)
      obtain ⟨caller, callContext⟩ := stage_syscall supported syscall
      have family : client.Family request := by
        refine ⟨caller, ?_⟩
        rw [Suspend.request_eq_entry user continuation]
        have memory : request.user.memory = state.machine.memory := congrArg X86.State.memory user
        simp only [Client.request, TSO.sharedState, context, callContext, memory, MachineThreads.contextState]
      refine ⟨before, atWorker, .entered ⟨state.nextCall, worker, request⟩
        (by simp [Suspend.capture]) rfl family (context.trans callContext) live empty ?_⟩
      exact stage_call_published supported syscall fifo
    | @machine machine observed pending issued =>
      obtain ⟨selected, instruction, found, running, decoded, issuedExecution, effect⟩ := TSO.issue_effect _ _ _ issued
      have selectedEq := Option.some.inj (atWorker.symm.trans found)
      subst selected
      have instructionEq := Except.ok.inj (decoded.symm.trans expected)
      subst instruction
      cases effect with
      | @queued store output intent aligned data executed writable exactOutput =>
        have phase := stage_store_phase supported (by simpa only [context] using intent)
        obtain ⟨producer, storeEq⟩ := stage_store supported (by simpa only [context] using intent)
        subst stage
        subst store
        have empty : before.buffer = [] := by
          rcases producer with role | role <;> simpa only [Stage.FIFO, Stage.bufferCondition, role] using fifo
        have nextSupported : Stage.stored.Valid client.role := by
          rcases producer with role | role <;> simp [Stage.Valid, role]
        have nextContext : Threads.Context.ofState output = Stage.stored.context client := by
          rw [exactOutput]
          simpa only [TSO.sharedState, context, Threads.Context.ofState, MachineThreads.contextState]
            using stage_store_context producer state.machine.memory
        refine ⟨_, List.getElem?_set_self bound, .running .stored nextSupported nextContext rfl free ?_⟩
        rcases producer with role | role
        · simp [Stage.FIFO, Stage.bufferCondition, role, StoreBuffer.enqueue, empty]
        · simp [Stage.FIFO, Stage.bufferCondition, role, StoreBuffer.enqueue, empty]
      | @ordinary output pending unlocked loads executed memory =>
        obtain ⟨destination, value, mov, outputEq⟩ := stage_ordinary supported
          (by simpa only [context] using pending) unlocked
          (by simpa only [TSO.localState, context] using executed)
        have next := stage_mov supported mov (StoreBuffer.view state.machine.memory before.buffer)
        have nextContext : Threads.Context.ofState output = (stage.next client.role).context client := by
          rw [outputEq]
          exact next.2
        exact ⟨_, List.getElem?_set_self bound,
          .running (stage.next client.role) next.1 nextContext rfl free (stage_mov_fifo supported mov fifo)⟩
      | @returned output pending unlocked instructionEq executed memory =>
        obtain ⟨peer, phase⟩ := stage_return supported instructionEq
        subst stage
        have returned := ret_context client (Stage.stored.context client)
          (StoreBuffer.view state.machine.memory before.buffer)
          (by simpa only [stage_rsp] using stack) canonical
        have outputEq : output = MachineThreads.contextState (client.returned (Stage.stored.context client))
            (StoreBuffer.view state.machine.memory before.buffer) := by
          rw [instructionEq, TSO.localState, context] at executed
          exact StepResult.returned.inj (Except.ok.inj (executed.symm.trans returned))
        refine ⟨_, List.getElem?_set_self bound, .peerReturned peer ?_ rfl free ?_⟩
        · rw [outputEq]; rfl
        · simpa only [Stage.FIFO, Stage.bufferCondition, peer] using fifo
      | @atomic event output pending locked empty data executed transition address accumulator =>
        obtain ⟨publisher, phase, _, _, insn⟩ := stage_locked supported locked
        subst stage
        have next := exchange_context publisher (by simpa only [TSO.sharedState, context, insn] using executed)
        have current : client.Published state.machine.memory := by
          simp only [Stage.FIFO, Stage.bufferCondition, publisher] at fifo
          rcases fifo with token | drained
          · simp [empty] at token
          · exact drained.2
        refine ⟨_, List.getElem?_set_self bound,
          .running (.exchanged event.before) (by simp [Stage.Valid, publisher]) next.1 rfl free ?_⟩
        simp only [Stage.FIFO, Stage.bufferCondition, publisher]
        exact ⟨trivial, frame current⟩
      | blocked pending locked nonempty =>
        exact ⟨before, atWorker, .running stage supported context live free fifo⟩

theorem drained_word {before after : Memory} {store : StoreBuffer.Store}
    (committed : storeDWord before store.address store.value = .ok after) :
    loadDWord after store.address = .ok store.value := by
  unfold storeDWord at committed
  split at committed
  next writable =>
    cases Except.ok.inj committed
    exact (store_sound before store.address store.value writable).2
  next => cases committed

theorem Stage.FIFO.drain {client : Client} {stage : Stage} {before after : Memory}
    {head : StoreBuffer.Store} {tail : StoreBuffer.Buffer}
    (supported : stage.Valid client.role) (fifo : stage.FIFO client before (head :: tail))
    (committed : storeDWord before head.address head.value = .ok after) :
    stage.FIFO client after tail := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.FIFO, Stage.bufferCondition, role] at supported fifo ⊢
  all_goals
    obtain ⟨rfl, rfl⟩ := fifo
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨rfl, fun _ => drained_word committed⟩

theorem WorkerControl.drain_selected {client : Client} {worker : Nat} {state after : Suspend.State}
    {before : TSO.Worker} {observation : Suspend.Observation}
    (control : WorkerControl client worker state before)
    (atWorker : state.machine.workers[worker]? = some before)
    (actual : Suspend.drain state worker = .ok (after, observation)) :
    ∃ selected, after.machine.workers[worker]? = some selected ∧ WorkerControl client worker after selected := by
  obtain ⟨machine, observed, drained, same⟩ := Suspend.drain_ok _ _ _ actual
  obtain ⟨selected, head, tail, memory, found, buffer, committed, installed⟩ := TSO.drain_ok _ _ _ drained
  have selectedEq := Option.some.inj (atWorker.symm.trans found)
  subst selected
  have machineEq := congrArg Prod.fst installed
  dsimp only at machineEq
  have stateEq := congrArg Prod.fst same
  dsimp only at stateEq
  rw [stateEq, machineEq]
  have bound := (List.getElem_of_getElem? atWorker).1
  refine ⟨_, List.getElem?_set_self bound, ?_⟩
  cases control with
  | running stage supported context live free fifo =>
    exact .running stage supported context live free (Stage.FIFO.drain supported (buffer ▸ fifo) committed)
  | entered saved pending owner family context live empty published => simp [empty] at buffer
  | resumed outcome flags rcx r11 caller context live free empty published => simp [empty] at buffer
  | returned outcome flags rcx r11 caller context done free empty published => simp [empty] at buffer
  | peerReturned peer context done free fifo =>
    have tailEmpty : tail = [] := by
      rcases fifo with empty | token
      · simp [empty] at buffer
      · simp [token] at buffer
        exact buffer.2
    exact .peerReturned peer context done free (Or.inl tailEmpty)

end EDSL.OS.Futex.Clients
