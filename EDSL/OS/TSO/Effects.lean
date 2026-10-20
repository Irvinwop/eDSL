/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.TSO.Model
import EDSL.Audit

namespace EDSL.OS.TSO
open X86

theorem locked_eq_isLocked (instruction : Instruction) :
    locked instruction = instruction.isLocked := by
  cases instruction <;> rfl

theorem pendingStore_none_iff (context : Threads.Context) (memory : Memory)
    (instruction : Instruction) :
    pendingStore context instruction = none ↔
      instruction.storeIntent (MachineThreads.contextState context memory) = none := by
  cases instruction <;> simp [pendingStore, Instruction.storeIntent]

theorem pendingStore_some_intent {context : Threads.Context} {instruction : Instruction}
    {store : StoreBuffer.Store} (pending : pendingStore context instruction = some store)
    (memory : Memory) :
    instruction.storeIntent (MachineThreads.contextState context memory) =
      some (store.address, store.value) := by
  cases instruction <;> simp only [pendingStore, Option.some.injEq, reduceCtorEq] at pending
  all_goals subst store; rfl

private theorem returned_instruction {initial output : X86.State} {instruction : Instruction}
    (executed : executeInstruction initial instruction = .ok (.returned output)) :
    instruction = .ret := by
  cases instruction with
  | ret => rfl
  | leaEaxRdiDisp8 displacement | leaEaxRaxDisp8 displacement
  | movEaxEdi | movEaxEsi | cmpEaxZero | mov32 destination value | syscall =>
    simp [executeInstruction] at executed
  | exchangeEaxRdi =>
    cases result : executeExchange initial <;> simp [executeInstruction, result] at executed
  | fetchAddEaxRdi =>
    cases result : executeFetchAdd initial <;> simp [executeInstruction, result] at executed
  | jrcxz displacement =>
    cases result : executeJrcxz initial displacement <;> simp [executeInstruction, result] at executed
  | loopRcx displacement =>
    cases result : executeLoop initial displacement <;> simp [executeInstruction, result] at executed
  | jnz displacement =>
    cases result : executeJnz initial displacement <;> simp [executeInstruction, result] at executed
  | loadEaxRdi =>
    cases result : executeLoad initial <;> simp [executeInstruction, result] at executed
  | loadEaxRsi =>
    cases result : executeLoadRsi initial <;> simp [executeInstruction, result] at executed
  | storeEsiRdi =>
    cases result : executeStore initial <;> simp [executeInstruction, result] at executed
  | storeEaxRsi =>
    cases result : executeStoreRsi initial <;> simp [executeInstruction, result] at executed

/-- Exhaustive effects of the runtime's classified execution. Every retiring
case retains the successful architectural execution and the exact installed
state. Ordinary nonstores retain equality of the entire ignored memory,
including permissions, to the caller's forwarded view. -/
inductive ExecuteEffect (state : State) (identifier : Nat) (worker : Worker)
    (instruction : Instruction) : State × Observation → Prop where
  | queued {store output}
      (pending : pendingStore worker.context instruction = some store)
      (aligned : atomicAddressable store.address = true)
      (data : dataOnly state.memory store.address = true)
      (executed : executeInstruction (sharedState state worker) instruction = .ok (.next output))
      (writable : canStoreDWord state.memory store.address = true)
      (exactOutput : output = { sharedState state worker with
        memory := writeDWordUnchecked state.memory store.address store.value
        rip := worker.context.rip + 2 }) :
      ExecuteEffect state identifier worker instruction
        (install state identifier state.memory (.ofState output) false
          (StoreBuffer.enqueue worker.buffer store), .retired identifier none)
  | ordinary {output}
      (pending : pendingStore worker.context instruction = none)
      (unlocked : locked instruction = false)
      (loads : ∀ address, loadAddress worker.context instruction = some address →
        atomicAddressable address = true)
      (executed : executeInstruction (localState state worker) instruction = .ok (.next output))
      (memory : output.memory = (localState state worker).memory) :
      ExecuteEffect state identifier worker instruction
        (install state identifier state.memory (.ofState output) false worker.buffer,
          .retired identifier none)
  | returned {output}
      (pending : pendingStore worker.context instruction = none)
      (unlocked : locked instruction = false)
      (instructionEq : instruction = .ret)
      (executed : executeInstruction (localState state worker) instruction = .ok (.returned output))
      (memory : output.memory = (localState state worker).memory) :
      ExecuteEffect state identifier worker instruction
        (install state identifier state.memory (.ofState output) true worker.buffer,
          .retired identifier none)
  | atomic {event output}
      (pending : pendingStore worker.context instruction = none)
      (classified : locked instruction = true)
      (empty : worker.buffer = [])
      (data : dataOnly state.memory (worker.context.registers .rdi) = true)
      (executed : executeInstruction (sharedState state worker) instruction = .ok (.atomic event output))
      (transition : ExchangeTransition state.memory event output.memory)
      (address : event.address = worker.context.registers .rdi)
      (accumulator : output.registers .rax = event.before.setWidth 64) :
      ExecuteEffect state identifier worker instruction
        (install state identifier output.memory (.ofState output) false [],
          .retired identifier (some event))
  | blocked
      (pending : pendingStore worker.context instruction = none)
      (classified : locked instruction = true)
      (nonempty : worker.buffer ≠ []) :
      ExecuteEffect state identifier worker instruction (state, .blocked identifier)

theorem execute_effect (state : State) (identifier : Nat) (worker : Worker)
    (instruction : Instruction) (result : State × Observation)
    (success : execute state identifier worker instruction = .ok result) :
    ExecuteEffect state identifier worker instruction result := by
  cases pending : pendingStore worker.context instruction with
  | some store =>
    cases aligned : atomicAddressable store.address with
    | false => simp [execute, pending, aligned] at success
    | true =>
      cases data : dataOnly state.memory store.address with
      | false => simp [execute, pending, aligned, data] at success
      | true =>
        cases executed : executeInstruction (sharedState state worker) instruction with
        | error fault => simp [execute, pending, aligned, data, executed, Except.mapError] at success
        | ok outcome =>
          cases outcome with
          | next output =>
            simp [execute, pending, aligned, data, executed, Except.mapError] at success
            subst result
            have exactStore := (executeInstruction_storeIntent_next_iff
              (pendingStore_some_intent pending state.memory)).mp executed
            exact .queued pending aligned data executed exactStore.1 exactStore.2
          | returned output | atomic event output | syscall request =>
            simp [execute, pending, aligned, data, executed, Except.mapError] at success
  | none =>
    cases classified : locked instruction with
    | true =>
      cases empty : worker.buffer.isEmpty with
      | false =>
        simp [execute, pending, classified, empty] at success
        subst result
        exact .blocked pending classified (by intro same; simp [same] at empty)
      | true =>
        have empty' : worker.buffer = [] := List.isEmpty_iff.mp empty
        cases data : dataOnly state.memory (worker.context.registers .rdi) with
        | false => simp [execute, pending, classified, empty, data] at success
        | true =>
          cases executed : executeInstruction (sharedState state worker) instruction with
          | error fault =>
            simp [execute, pending, classified, empty, data, executed, Except.mapError] at success
          | ok outcome =>
            cases outcome with
            | atomic event output =>
              simp [execute, pending, classified, empty, data, executed, Except.mapError] at success
              subst result
              have sound := executeInstruction_atomic_transition executed
              exact .atomic pending classified empty' data executed sound.1 sound.2.1 sound.2.2
            | next output | returned output | syscall request =>
              simp [execute, pending, classified, empty, data, executed, Except.mapError] at success
    | false =>
      have loads : ∀ address, loadAddress worker.context instruction = some address →
          atomicAddressable address = true := by
        intro address found
        cases aligned : atomicAddressable address with
        | true => rfl
        | false => simp [execute, pending, classified, found, aligned] at success
      cases executed : executeInstruction (localState state worker) instruction with
      | error fault =>
        cases found : loadAddress worker.context instruction <;>
          simp [execute, pending, classified, found, loads, executed, Except.mapError] at success
      | ok outcome =>
        cases outcome with
        | next output =>
          have same : result = (install state identifier state.memory (.ofState output) false worker.buffer,
              .retired identifier none) := by
            cases found : loadAddress worker.context instruction <;>
              simpa [execute, pending, classified, found, loads, executed, Except.mapError] using success.symm
          rw [same]
          exact .ordinary pending classified loads executed (executeInstruction_next_memory
            ((pendingStore_none_iff _ _ _).mp pending) executed)
        | returned output =>
          have same : result = (install state identifier state.memory (.ofState output) true worker.buffer,
              .retired identifier none) := by
            cases found : loadAddress worker.context instruction <;>
              simpa [execute, pending, classified, found, loads, executed, Except.mapError] using success.symm
          rw [same]
          exact .returned pending classified (returned_instruction executed) executed
            (executeInstruction_returned_memory ((pendingStore_none_iff _ _ _).mp pending) executed)
        | atomic event output | syscall request =>
          cases found : loadAddress worker.context instruction <;>
            simp [execute, pending, classified, found, loads, executed, Except.mapError] at success

/-- Issue inversion starts with actual success: the worker is live, has not
returned, and shared instruction fetch selected the classified execution. -/
theorem issue_effect (state : State) (identifier : Nat) (result : State × Observation)
    (success : issue state identifier = .ok result) :
    ∃ worker instruction, state.workers[identifier]? = some worker ∧ worker.returned = false ∧
      decodeAt (sharedState state worker) = .ok instruction ∧
      execute state identifier worker instruction = .ok result ∧
      ExecuteEffect state identifier worker instruction result := by
  cases live : state.workers[identifier]? with
  | none => simp [issue, live] at success
  | some worker =>
    cases returned : worker.returned with
    | true => simp [issue, live, returned] at success
    | false =>
      cases decoded : decodeAt (sharedState state worker) with
      | error fault => simp [issue, live, returned, decoded, Except.mapError] at success
      | ok instruction =>
        have executed : execute state identifier worker instruction = .ok result := by
          simpa [issue, live, returned, decoded, Except.mapError] using success
        exact ⟨worker, instruction, rfl, returned, decoded, executed,
          execute_effect _ _ _ _ _ executed⟩

/-- The inversion describes precisely the executable successful outcomes. -/
theorem ExecuteEffect.success {state : State} {identifier : Nat} {worker : Worker}
    {instruction : Instruction} {result : State × Observation}
    (effect : ExecuteEffect state identifier worker instruction result) :
    execute state identifier worker instruction = .ok result := by
  cases effect with
  | queued pending aligned data executed writable exactOutput =>
    simp [execute, pending, aligned, data, executed, Except.mapError]
  | ordinary pending unlocked loads executed memory =>
    cases found : loadAddress worker.context instruction with
    | none => simp [execute, pending, unlocked, found, executed, Except.mapError]
    | some address =>
      simp [execute, pending, unlocked, found, loads address found, executed, Except.mapError]
  | returned pending unlocked instructionEq executed memory =>
    subst instruction
    simp [execute, pendingStore, locked, loadAddress, executed, Except.mapError]
  | atomic pending classified empty data executed transition address accumulator =>
    simp [execute, pending, classified, empty, data, executed, Except.mapError]
  | blocked pending classified nonempty =>
    have busy : worker.buffer.isEmpty = false := by
      cases buffer : worker.buffer with
      | nil => exact (nonempty buffer).elim
      | cons head tail => rfl
    simp [execute, pending, classified, busy]

theorem execute_effect_iff (state : State) (identifier : Nat) (worker : Worker)
    (instruction : Instruction) (result : State × Observation) :
    execute state identifier worker instruction = .ok result ↔
      ExecuteEffect state identifier worker instruction result :=
  ⟨execute_effect _ _ _ _ _, ExecuteEffect.success⟩

/-- Locked retirement drains no peers and requires exactly this worker's own
queue to be empty. Its event is an exact transition on full shared memory. -/
theorem issue_atomic_effect {state after : State} {identifier : Nat} {event : AtomicEvent}
    (success : issue state identifier = .ok (after, .retired identifier (some event))) :
    ∃ worker instruction output, state.workers[identifier]? = some worker ∧
      worker.returned = false ∧ decodeAt (sharedState state worker) = .ok instruction ∧
      locked instruction = true ∧ worker.buffer = [] ∧
      dataOnly state.memory event.address = true ∧
      executeInstruction (sharedState state worker) instruction = .ok (.atomic event output) ∧
      after = install state identifier output.memory (.ofState output) false [] ∧
      ExchangeTransition state.memory event after.memory ∧
      event.address = worker.context.registers .rdi ∧
      output.registers .rax = event.before.setWidth 64 := by
  obtain ⟨worker, instruction, live, returned, decoded, _, effect⟩ := issue_effect _ _ _ success
  cases effect with
  | @atomic event output pending classified empty data executed transition address accumulator =>
    exact ⟨worker, instruction, output, live, returned, decoded, classified, empty,
      by rw [address]; exact data, executed, rfl, transition, address, accumulator⟩

/-- A blocked issue leaves the entire scheduler state unchanged and retires
zero instructions. Decoding and classification still come from actual issue. -/
theorem issue_blocked_effect {state after : State} {identifier : Nat}
    (success : issue state identifier = .ok (after, .blocked identifier)) :
    ∃ worker instruction, state.workers[identifier]? = some worker ∧ worker.returned = false ∧
      decodeAt (sharedState state worker) = .ok instruction ∧ locked instruction = true ∧
      worker.buffer ≠ [] ∧ after = state ∧ retiredCount [.blocked identifier] = 0 := by
  obtain ⟨worker, instruction, live, returned, decoded, _, effect⟩ := issue_effect _ _ _ success
  cases effect with
  | blocked pending classified nonempty =>
    exact ⟨worker, instruction, live, returned, decoded, classified, nonempty, rfl, rfl⟩

end EDSL.OS.TSO

#audit_edsl
