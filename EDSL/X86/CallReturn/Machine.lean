/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.X86.CallReturn.Decode
import EDSL.X86.StackRead64

namespace EDSL.X86.CallReturn

/-- Ordinary RAM, four-level canonical addressing, no CET/AC/asynchronous
control state. This abstract profile checks branch canonicality before store
preflight; physical exception priority/delivery is not modeled. -/
def callState (state : State) (displacement : BitVec 32) (memory : Memory) : State :=
  { state.writeRegister .rsp (stackDestination state) with
    rip := callTarget state displacement, memory := memory }

def pushState (state : State) (prefixed : Bool) (memory : Memory) : State :=
  { state.writeRegister .rsp (stackDestination state) with
    rip := state.rip + BitVec.ofNat 64 (stackLength prefixed), memory := memory }

/-- Increment first, then write the destination: POP RSP ends at the loaded
value. The source is always the complete word at the OLD stack pointer. -/
def popState (state : State) (destination : Register) (prefixed : Bool) (value : Word) : State :=
  { (state.writeRegister .rsp (state.registers .rsp + 8)).writeRegister destination value with
    rip := state.rip + BitVec.ofNat 64 (stackLength prefixed) }

def leaState (state : State) (destination : Register) (address : Address) (displacement : Byte) : State :=
  { state.writeRegister destination ((address.displaced displacement).eval state) with
    rip := state.rip + BitVec.ofNat 64 (Instruction.leaDisp8 destination address displacement).length }

/-- Complete primitives are checked before a successful observation exists.
CALL checks only the target's canonicality; execution permission is checked by
its subsequent actual fetch, and the pushed return address need not be canonical. -/
def execute (state : State) (instruction : Instruction) (af : Bool) : Except Error Observation := do
  match instruction with
  | .sequential old => Sequential.execute state old af
  | .callRelative32 displacement =>
    let target := callTarget state displacement
    if !canonical target then throw (.noncanonicalBranch target)
    let memory ← storeQWord state.memory (stackDestination state) (returnAddress state)
    return ⟨.next (callState state displacement memory), []⟩
  | .push64 source prefixed =>
    let value := state.registers source
    let memory ← storeQWord state.memory (stackDestination state) value
    return ⟨.next (pushState state prefixed memory), []⟩
  | .pop64 destination prefixed =>
    let value ← readWord state.memory (state.registers .rsp)
    return ⟨.next (popState state destination prefixed value), instruction.operandReads state⟩
  | .leaDisp8 destination address displacement =>
    Sequential.execute state (.lea64 destination (address.displaced displacement)) af

/-- Raw RET observations are retained, including for an internal return. -/
def rawStep (af : Bool) (state : State) : Except Error Observation := do
  execute state (← decodeAt state) af

theorem rawStep_eq_execute {state : State} {instruction : Instruction} (af : Bool)
    (decoded : decodeAt state = .ok instruction) : rawStep af state = execute state instruction af := by
  simp [rawStep, decoded]

theorem rawStep_success_iff {state : State} {af : Bool} {observation : Observation} :
    rawStep af state = .ok observation ↔
    ∃ instruction, decodeAt state = .ok instruction ∧ execute state instruction af = .ok observation := by
  cases decoded : decodeAt state <;> simp [rawStep, decoded]

@[simp] theorem execute_sequential (state : State) (instruction : Sequential.Instruction) (af : Bool) :
    execute state (.sequential instruction) af = Sequential.execute state instruction af := rfl

/-- The compatibility mapping preserves the complete production observation. -/
theorem execute_liftSequential (state : State) (instruction : Sequential.Instruction) (af : Bool) :
    execute state (liftSequential instruction) af = Sequential.execute state instruction af := by
  cases instruction <;> try rfl
  rename_i address
  cases address <;> rfl

/-- Exact successful checked-store contract, before imposing any ownership or
ABI premise. Canonicality of the continuation is deliberately absent. -/
theorem execute_call_success_iff {state : State} {displacement : BitVec 32} {af : Bool}
    {observation : Observation} :
    execute state (.callRelative32 displacement) af = .ok observation ↔
    canonical (callTarget state displacement) = true ∧
    ∃ memory, storeQWord state.memory (stackDestination state) (returnAddress state) = .ok memory ∧
      observation = ⟨.next (callState state displacement memory), []⟩ := by
  cases target : canonical (callTarget state displacement) <;>
    cases stored : storeQWord state.memory (stackDestination state) (returnAddress state) <;>
    simp [execute, target, stored, eq_comm]

theorem execute_call (state : State) (displacement : BitVec 32) (af : Bool) (memory : Memory)
    (target : canonical (callTarget state displacement) = true)
    (stored : storeQWord state.memory (stackDestination state) (returnAddress state) = .ok memory) :
    execute state (.callRelative32 displacement) af = .ok ⟨.next (callState state displacement memory), []⟩ :=
  execute_call_success_iff.mpr ⟨target, memory, stored, rfl⟩

theorem execute_call_noncanonical (state : State) (displacement : BitVec 32) (af : Bool)
    (target : canonical (callTarget state displacement) = false) :
    execute state (.callRelative32 displacement) af = .error (.noncanonicalBranch (callTarget state displacement)) := by
  simp [execute, target]

theorem execute_call_store_fault (state : State) (displacement : BitVec 32) (af : Bool) (fault : Error)
    (target : canonical (callTarget state displacement) = true)
    (stored : storeQWord state.memory (stackDestination state) (returnAddress state) = .error fault) :
    execute state (.callRelative32 displacement) af = .error fault := by simp [execute, target, stored]

theorem execute_push_success_iff {state : State} {source : Register} {prefixed af : Bool}
    {observation : Observation} :
    execute state (.push64 source prefixed) af = .ok observation ↔
    ∃ memory, storeQWord state.memory (stackDestination state) (state.registers source) = .ok memory ∧
      observation = ⟨.next (pushState state prefixed memory), []⟩ := by
  cases stored : storeQWord state.memory (stackDestination state) (state.registers source) <;>
    simp [execute, stored, eq_comm]

theorem execute_push (state : State) (source : Register) (prefixed af : Bool) (memory : Memory)
    (stored : storeQWord state.memory (stackDestination state) (state.registers source) = .ok memory) :
    execute state (.push64 source prefixed) af = .ok ⟨.next (pushState state prefixed memory), []⟩ :=
  execute_push_success_iff.mpr ⟨memory, stored, rfl⟩

theorem execute_push_fault (state : State) (source : Register) (prefixed af : Bool) (fault : Error)
    (stored : storeQWord state.memory (stackDestination state) (state.registers source) = .error fault) :
    execute state (.push64 source prefixed) af = .error fault := by simp [execute, stored]

theorem execute_pop_success_iff {state : State} {destination : Register} {prefixed af : Bool}
    {observation : Observation} :
    execute state (.pop64 destination prefixed) af = .ok observation ↔
    ∃ value, readWord state.memory (state.registers .rsp) = .ok value ∧
      observation = ⟨.next (popState state destination prefixed value), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  cases loaded : readWord state.memory (state.registers .rsp) <;>
    simp [execute, loaded, Instruction.operandReads, eq_comm]

theorem execute_pop (state : State) (destination : Register) (prefixed af : Bool) (value : Word)
    (loaded : readWord state.memory (state.registers .rsp) = .ok value) :
    execute state (.pop64 destination prefixed) af =
      .ok ⟨.next (popState state destination prefixed value), [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  execute_pop_success_iff.mpr ⟨value, loaded, rfl⟩

theorem execute_pop_fault (state : State) (destination : Register) (prefixed af : Bool) (fault : Error)
    (loaded : readWord state.memory (state.registers .rsp) = .error fault) :
    execute state (.pop64 destination prefixed) af = .error fault := by simp [execute, loaded]

@[simp] theorem execute_lea (state : State) (destination : Register) (address : Address)
    (displacement : Byte) (af : Bool) :
    execute state (.leaDisp8 destination address displacement) af =
      .ok ⟨.next (leaState state destination address displacement), []⟩ := rfl

end EDSL.X86.CallReturn
