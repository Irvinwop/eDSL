/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemory64.Steps
import tests.fixtures.CallStack.State

set_option warningAsError true

namespace EDSL.CallMemory64.Compiler
open X86 OS

abbrev RegisterFrame := CallStack.Compiler.RegisterFrame
abbrev pushed := CallStack.Compiler.pushed
abbrev increment := CallStack.Compiler.increment
abbrev finish := CallStack.Compiler.finish

def called (state : State) : State :=
  CallReturn.callState state 5
    (writeQWordUnchecked state.memory (CallReturn.stackDestination state) (CallReturn.returnAddress state))

def stored (state : State) (world : Borrowing.State) : State :=
  WordResources64.storeAfterLength state world 3

def loaded (state : State) (value : Word) : State :=
  { state.writeRegister .rax value with rip := state.rip + 3 }

def popped (profile : Profile) (state : State) (value : Word) : State :=
  CallReturn.popState state (popDestination profile) false value

theorem frame_called (state : State) : RegisterFrame state (called state) :=
  CallStack.Compiler.frame_write state .rsp _ _ _ _ (by decide) rfl

theorem frame_stored (state : State) (world : Borrowing.State) :
    RegisterFrame state (stored state world) := ⟨fun _ _ => rfl, rfl⟩

theorem frame_loaded (state : State) (value : Word) : RegisterFrame state (loaded state value) :=
  CallStack.Compiler.frame_write state .rax _ _ _ _ (by decide) rfl

theorem frame_popped (profile : Profile) (state : State) (value : Word) :
    RegisterFrame state (popped profile state value) := by
  refine (CallStack.Compiler.frame_write state .rsp (state.registers .rsp + 8)
    state.rip state.flags state.memory (by decide) rfl).trans ?_
  exact CallStack.Compiler.frame_write _ (popDestination profile) _ _ _ _
    (by cases profile <;> decide) rfl

theorem popped_stack (profile : Profile) (state : State) (value : Word) :
    (popped profile state value).registers .rsp = state.registers .rsp + 8 := by
  cases profile <;> simp [popped, popDestination, CallReturn.popState, State.writeRegister]

theorem push_enabled {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .push))
    (slot : StackFrame.Slot descriptor.frame (CallReturn.stackDestination state)) (af : Bool) :
    ∃ evolved, OS.CallMemory64.CPU.Step descriptor shared evolved state (pushed state) af
        ⟨.next (pushed state), []⟩ ∧
      OS.CallMemory64.Current descriptor evolved (pushed state) := by
  have writable : canStoreQWord state.memory (CallReturn.stackDestination state) = true := by
    rw [current.coupled]
    exact (current.contract.stack.ready _ slot).writable
  have stored := (qword_store_sound state.memory _ (state.registers .rax) writable).1
  have actual := CallReturn.execute_push state .rax false af _ stored
  obtain ⟨evolved, success, _, _, _⟩ := StackFrame.CPU.push_current current.stack slot actual
  have step : OS.CallMemory64.CPU.Step descriptor shared evolved state (pushed state) af
      ⟨.next (pushed state), []⟩ := OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode (current_code current same) .push pc, actual, rfl, rfl,
      .push slot success, by simp⟩
  exact ⟨evolved, step, step.current current⟩

theorem call_enabled {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .call))
    (slot : StackFrame.Slot descriptor.frame (CallReturn.stackDestination state)) (af : Bool) :
    ∃ evolved, OS.CallMemory64.CPU.Step descriptor shared evolved state (called state) af
        ⟨.next (called state), []⟩ ∧
      OS.CallMemory64.Current descriptor evolved (called state) ∧
      readWord (called state).memory (CallReturn.stackDestination state) =
        .ok (CallReturn.returnAddress state) := by
  have writable : canStoreQWord state.memory (CallReturn.stackDestination state) = true := by
    rw [current.coupled]
    exact (current.contract.stack.ready _ slot).writable
  have stored := (qword_store_sound state.memory _ (CallReturn.returnAddress state) writable).1
  have actual := CallReturn.execute_call state 5 af _
    (call_addresses (current_code current same) pc).1 stored
  obtain ⟨evolved, success, _, _, effect⟩ := StackFrame.CPU.call_current current.stack slot actual
  have step : OS.CallMemory64.CPU.Step descriptor shared evolved state (called state) af
      ⟨.next (called state), []⟩ := OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode (current_code current same) .call pc, actual, rfl, rfl,
      .call slot success, by simp⟩
  have next := step.current current
  refine ⟨evolved, step, next, ?_⟩
  rw [next.coupled]
  exact readWord_of_loadQWord _ _ _ effect.readback

theorem store_enabled {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} {value : Word}
    (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .store))
    (pointer : state.registers .rdi = descriptor.target) (argument : state.registers .rsi = value)
    (af : Bool) :
    ∃ evolved, OS.CallMemory64.CPU.Step descriptor shared evolved state (stored state evolved) af
        ⟨.next (stored state evolved), []⟩ ∧
      OS.CallMemory64.Current descriptor evolved (stored state evolved) ∧
      Borrowing.StoreEffect64 shared evolved descriptor.target value ∧
      Borrowing.loadOwnedWord64 evolved descriptor.owner descriptor.ticket descriptor.target =
        .ok value := by
  have decoded : Sequential.decodeAt state = .ok (.storeMem64 address .rsi) :=
    decode_sequential (current_code current same) pc (by cases profile <;> rfl)
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 address .rsi) state =
      some (descriptor.target, value) := by
    simp [Sequential.Instruction.storeIntent64, address, Sequential.Address.eval, pointer, argument]
  obtain ⟨evolved, _, _, step, next, effect, readback⟩ :=
    OS.CallMemory64.CPU.data_store_step current decoded intent af
  exact ⟨evolved, step, next, effect, readback⟩

theorem load_step {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} {value : Word}
    (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .load))
    (pointer : state.registers .rdi = descriptor.target)
    (readback : Borrowing.loadOwnedWord64 shared descriptor.owner descriptor.ticket
      descriptor.target = .ok value) (af : Bool) :
    OS.CallMemory64.CPU.Step descriptor shared shared state (loaded state value) af
      ⟨.next (loaded state value), [⟨.data, descriptor.target, 8⟩]⟩ := by
  have decoded : Sequential.decodeAt state = .ok (.loadMem64 .rax address) :=
    decode_sequential (current_code current same) pc (by cases profile <;> rfl)
  have effective : address.eval state = descriptor.target := pointer
  obtain ⟨observed, owned, _, step, _, _⟩ :=
    OS.CallMemory64.CPU.data_load_step current decoded effective af
  have sameValue : observed = value := Except.ok.inj (owned.symm.trans readback)
  subst observed
  exact step

theorem increment_step {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .increment))
    (af : Bool) :
    OS.CallMemory64.CPU.Step descriptor shared shared state (increment state) af
      ⟨.next (increment state), []⟩ :=
  OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode (current_code current same) .increment pc, rfl, rfl, rfl,
      .unchanged rfl rfl, by simp [Sequential.Instruction.operandReads]⟩

theorem pop_step {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} {value : Word}
    (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .pop))
    (slot : StackFrame.Slot descriptor.frame (state.registers .rsp))
    (readback : readWord state.memory (state.registers .rsp) = .ok value) (af : Bool) :
    OS.CallMemory64.CPU.Step descriptor shared shared state (popped profile state value) af
      ⟨.next (popped profile state value), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  have actual := CallReturn.execute_pop state (popDestination profile) false af value readback
  have context := StackFrame.CPU.pop_current current.stack slot actual
  exact OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode (current_code current same) .pop pc, actual, rfl, rfl,
      .unchanged rfl rfl, context.2.2⟩

theorem inner_ret_step {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} {target : Word}
    (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .innerRet))
    (slot : StackFrame.Slot descriptor.frame (state.registers .rsp))
    (readback : readWord state.memory (state.registers .rsp) = .ok target)
    (canon : canonical target = true) (af : Bool) :
    OS.CallMemory64.CPU.Step descriptor shared shared state (finish state target) af
      ⟨.next (finish state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  have actual : CallReturn.execute state (.sequential (.legacy .ret)) af =
      .ok ⟨.returned (finish state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
    CallReturn.execute_ret_success_iff.mpr ⟨target, readback, canon, rfl, rfl⟩
  exact OS.CallMemory64.CPU.lift_stack (StackFrame.CPU.private_ret_step current.stack slot
    (decode (current_code current same) .innerRet pc) actual)

theorem root_ret_step {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} {profile : Profile} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (offset profile .ret))
    (original : state.registers .rsp = descriptor.frame.top) (af : Bool) :
    OS.CallMemory64.CPU.Step descriptor shared shared state
      (finish state descriptor.frame.call.returnAddress) af
      ⟨.returned (finish state descriptor.frame.call.returnAddress),
        [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  OS.CallMemory64.CPU.lift_stack (StackFrame.CPU.original_ret_step current.stack original af
    (decode (current_code current same) .ret pc))

end EDSL.CallMemory64.Compiler
