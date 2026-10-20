/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.Futex.ClientControlDecode

set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

namespace EDSL.OS.Futex.Clients
open X86 AddressSpace

theorem Stage.start_context (client : Client) : Stage.start.context client = client.entry := by
  cases client
  simp [Stage.context, Stage.offset]

theorem WorkerControl.initial (client : Client) (worker : Nat) (state : Suspend.State)
    (free : state.pending worker = none) :
    WorkerControl client worker state ⟨client.entry, false, []⟩ := by
  refine .running .start ?_ (Stage.start_context client).symm rfl free ?_
  · cases role : client.role <;> simp [Stage.Valid, role]
  · cases role : client.role <;> simp [Stage.FIFO, Stage.bufferCondition, role]

def Stage.next (role : Role) : Stage → Stage
  | .start => match role with | .wait _ => .number | _ => .payload
  | .payload => .stored
  | .stored => .exchange
  | .exchanged _ => .number
  | .number => .operation
  | .operation => .count
  | .exchange => .exchange
  | .count => .count

theorem stage_mov {client : Client} {stage : Stage} {destination : Register} {value : BitVec 32}
    (supported : stage.Valid client.role)
    (instruction : stage.instruction client.role = .mov32 destination value) (memory : Memory) :
    (stage.next client.role).Valid client.role ∧
    Threads.Context.ofState (executeMov32 (MachineThreads.contextState (stage.context client) memory)
      destination value) = (stage.next client.role).context client := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, role] at supported instruction
  all_goals
    obtain ⟨rfl, rfl⟩ := instruction
    constructor
    · simp [Stage.next, Stage.Valid, role]
    · simp [Stage.next, Stage.context, Stage.offset, Role.value, role,
        Threads.Context.ofState, MachineThreads.contextState, executeMov32,
        State.writeRegister, BitVec.add_assoc]
      all_goals
        funext register
        cases register <;> rfl

theorem stage_mov_fifo {client : Client} {stage : Stage} {destination : Register} {value : BitVec 32}
    {memory : Memory} {buffer : StoreBuffer.Buffer}
    (supported : stage.Valid client.role)
    (instruction : stage.instruction client.role = .mov32 destination value)
    (fifo : stage.FIFO client memory buffer) :
    (stage.next client.role).FIFO client memory buffer := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, role] at supported instruction
  all_goals simpa [Stage.FIFO, Stage.bufferCondition, Stage.next, role] using fifo

theorem stage_store_phase {client : Client} {stage : Stage} {store : StoreBuffer.Store}
    (supported : stage.Valid client.role)
    (intent : TSO.pendingStore (stage.context client) (stage.instruction client.role) = some store) :
    stage = .payload := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, TSO.pendingStore, role] at supported intent ⊢

theorem stage_store_context {client : Client} (producer : client.role = .publishPayloadWake ∨ client.role = .payloadPeer)
    (memory : Memory) :
    Threads.Context.ofState { MachineThreads.contextState (Stage.payload.context client) memory with
      rip := (Stage.payload.context client).rip + 2 } = Stage.stored.context client := by
  rcases producer with role | role <;>
    simp [Stage.context, Stage.offset, role, MachineThreads.contextState, Threads.Context.ofState,
      BitVec.add_assoc]

theorem stage_return {client : Client} {stage : Stage} (supported : stage.Valid client.role)
    (instruction : stage.instruction client.role = .ret) :
    client.role = .payloadPeer ∧ stage = .stored := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, role] at supported instruction ⊢

private theorem ret_not_next (input output : X86.State)
    (executed : executeInstruction input .ret = .ok (.next output)) : False := by
  cases returned : executeRet input <;> simp [executeInstruction, returned] at executed

theorem stage_ordinary {client : Client} {stage : Stage} {memory : Memory} {output : X86.State}
    (supported : stage.Valid client.role)
    (pending : TSO.pendingStore (stage.context client) (stage.instruction client.role) = none)
    (unlocked : TSO.locked (stage.instruction client.role) = false)
    (executed : executeInstruction (MachineThreads.contextState (stage.context client) memory)
      (stage.instruction client.role) = .ok (.next output)) :
    ∃ destination value, stage.instruction client.role = .mov32 destination value ∧
      output = executeMov32 (MachineThreads.contextState (stage.context client) memory) destination value := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, TSO.pendingStore, TSO.locked, role] at supported pending unlocked executed
  all_goals first
    | exact ⟨_, _, by simp [Stage.instruction, role], executed.symm⟩
    | exact (ret_not_next _ _ executed).elim

theorem stage_call_published {client : Client} {stage : Stage} {memory : Memory}
    {buffer : StoreBuffer.Buffer} (supported : stage.Valid client.role)
    (syscall : stage.instruction client.role = .syscall) (fifo : stage.FIFO client memory buffer) :
    client.Published memory := by
  cases role : client.role <;> cases stage <;>
    simp [Stage.Valid, Stage.instruction, role] at supported syscall
  · simp [Client.Published, role]
  · simp only [Stage.FIFO, Stage.bufferCondition, role] at fifo
    exact fifo.2

theorem ret_context (client : Client) (context : Threads.Context) (memory : Memory)
    (stack : readWord memory (context.registers .rsp) = .ok client.returnTarget)
    (canonical : X86.canonical client.returnTarget = true) :
    executeInstruction (MachineThreads.contextState context memory) .ret = .ok
      (.returned (MachineThreads.contextState (client.returned context) memory)) := by
  simp [executeInstruction, executeRet, MachineThreads.contextState, stack, canonical,
    Client.returned, State.writeRegister]

theorem stage_rsp (client : Client) (stage : Stage) :
    (stage.context client).registers .rsp = client.entry.registers .rsp := by
  simp [Stage.context]

theorem resumed_rsp (client : Client) (raw flags rcx r11 : Word) :
    (client.resumed raw flags rcx r11).registers .rsp = client.entry.registers .rsp := by
  simp [Client.resumed, Client.callContext, stage_rsp]

theorem exchange_context {client : Client} {memory : Memory} {event : AtomicEvent} {output : X86.State}
    (_publisher : client.role = .publishPayloadWake)
    (executed : executeInstruction (MachineThreads.contextState (Stage.exchange.context client) memory)
      .exchangeEaxRdi = .ok (.atomic event output)) :
    Threads.Context.ofState output = (Stage.exchanged event.before).context client ∧ event.after = 1 := by
  cases exchanged : exchangeDWord memory ((Stage.exchange.context client).registers .rdi)
      (((Stage.exchange.context client).registers .rax).setWidth 32) with
  | error fault =>
    simp only [executeInstruction, executeExchange, MachineThreads.contextState, exchanged, error_bind] at executed
    cases executed
  | ok result =>
    simp only [executeInstruction, executeExchange, MachineThreads.contextState, exchanged, ok_bind,
      Except.ok.injEq, StepResult.atomic.injEq] at executed
    obtain ⟨rfl, rfl⟩ := executed
    constructor
    · simp [Threads.Context.ofState, Stage.context, Stage.offset, State.writeRegister,
        BitVec.add_assoc]
      all_goals
        funext register
        cases register <;> rfl
    · simp [Stage.context]

end EDSL.OS.Futex.Clients
