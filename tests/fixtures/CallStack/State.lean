/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallStack.Steps
import EDSL.OS.StackFrame.CPU

set_option warningAsError true

namespace EDSL.CallStack.Compiler
open X86 OS

def called (profile : Profile) (state : State) : State :=
  CallReturn.callState state (displacement profile)
    (writeQWordUnchecked state.memory (CallReturn.stackDestination state) (CallReturn.returnAddress state))

def pushed (state : State) : State :=
  CallReturn.pushState state false
    (writeQWordUnchecked state.memory (CallReturn.stackDestination state) (state.registers .rax))

def helper (state : State) : State := CallReturn.leaState state .rax (.plain .rdi) 1

def increment (state : State) : State :=
  { state.writeRegister .rax (state.registers .rax + 1) with
    rip := state.rip + 3, flags := Sequential.incFlags64 state.flags (state.registers .rax) }

def popped (profile : Profile) (state : State) (value : Word) : State :=
  CallReturn.popState state (popDestination profile) false value

theorem popped_stack (profile : Profile) (state : State) (value : Word) :
    (popped profile state value).registers .rsp = state.registers .rsp + 8 := by
  cases profile <;> simp [popped, popDestination, CallReturn.popState, State.writeRegister]

/-- Register and flag portions of the independent ABI contract. Memory effects
are supplied by the actual threaded CPU/OS history, separately. -/
structure RegisterFrame (initial final : State) : Prop where
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask =
    initial.flags &&& ~~~arithmeticFlagMask

theorem RegisterFrame.refl (state : State) : RegisterFrame state state := ⟨fun _ _ => rfl, rfl⟩
theorem RegisterFrame.trans {first middle final : State}
    (left : RegisterFrame first middle) (right : RegisterFrame middle final) : RegisterFrame first final :=
  ⟨fun r outside => (right.preserved r outside).trans (left.preserved r outside),
    right.flags.trans left.flags⟩

theorem frame_write (state : State) (destination : Register) (value pc flags : Word) (memory : Memory)
    (allowed : destination ∈ clobbers)
    (flagsFrame : flags &&& ~~~arithmeticFlagMask =
      state.flags &&& ~~~arithmeticFlagMask) :
    RegisterFrame state { state.writeRegister destination value with rip := pc, flags := flags, memory := memory } := by
  refine ⟨?_, flagsFrame⟩
  intro r outside
  have different : r ≠ destination := by intro same; subst r; exact outside allowed
  simp [State.writeRegister, different]

theorem frame_called (profile : Profile) (state : State) : RegisterFrame state (called profile state) :=
  frame_write state .rsp _ _ _ _ (by decide) rfl

theorem frame_pushed (state : State) : RegisterFrame state (pushed state) :=
  frame_write state .rsp _ _ _ _ (by decide) rfl

theorem frame_helper (state : State) : RegisterFrame state (helper state) :=
  frame_write state .rax _ _ _ _ (by decide) rfl

theorem frame_increment (state : State) : RegisterFrame state (increment state) :=
  frame_write state .rax _ _ _ _ (by decide) (Sequential.incFlags64_preserves ..)

theorem frame_finish (state : State) (target : Word) : RegisterFrame state (finish state target) :=
  frame_write state .rsp _ _ _ _ (by decide) rfl

theorem frame_popped (profile : Profile) (state : State) (value : Word) : RegisterFrame state (popped profile state value) := by
  refine (frame_write state .rsp (state.registers .rsp + 8) state.rip state.flags state.memory (by decide) rfl).trans ?_
  exact frame_write _ (popDestination profile) _ _ _ _ (by cases profile <;> decide) rfl

theorem current_code {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile) : CodeAt state.memory frame.call.code (bytes profile) := by
  rw [current.coupled, ← same]
  exact current.contract.pureCall.code

/-- The concrete CALL succeeds from present writable owner authority. Its
actual checked mutation supplies the evolved resource world and return word. -/
theorem call_enabled {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile .call))
    (slot : StackFrame.Slot frame (CallReturn.stackDestination state)) (af : Bool) :
    ∃ evolved, StackFrame.CPU.Step frame shared evolved state (called profile state) af
        ⟨.next (called profile state), []⟩ ∧
      StackFrame.Current frame evolved (called profile state) ∧
      readWord (called profile state).memory (CallReturn.stackDestination state) =
        .ok (CallReturn.returnAddress state) := by
  have allowed : canStoreQWord state.memory (CallReturn.stackDestination state) = true := by
    rw [current.coupled]
    exact (current.contract.ready _ slot).writable
  have stored := (qword_store_sound state.memory _ (CallReturn.returnAddress state) allowed).1
  have actual := CallReturn.execute_call state (displacement profile) af _
    (call_addresses (current_code current same) pc).1 stored
  obtain ⟨evolved, success, next, _, effect⟩ := StackFrame.CPU.call_current current slot actual
  refine ⟨evolved, ?_, next, ?_⟩
  · exact ⟨_, _, decode (current_code current same) .call rfl pc, actual, rfl, rfl,
      .call slot success, by simp⟩
  · have loaded := readWord_of_loadQWord _ _ _ effect.readback
    rw [← next.coupled] at loaded
    exact loaded

theorem helper_step {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile .helper)) (af : Bool) :
    StackFrame.CPU.Step frame shared shared state (helper state) af ⟨.next (helper state), []⟩ :=
  ⟨_, _, decode (current_code current same) .helper rfl pc, rfl, rfl, rfl,
    .unchanged rfl rfl, by simp [Sequential.Instruction.operandReads]⟩

theorem increment_step {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile .increment)) (af : Bool) :
    StackFrame.CPU.Step frame shared shared state (increment state) af ⟨.next (increment state), []⟩ :=
  ⟨_, _, decode (current_code current same) .increment rfl pc, rfl, rfl, rfl,
    .unchanged rfl rfl, by simp [Sequential.Instruction.operandReads]⟩

theorem push_enabled {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile) (present : active profile .push = true)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile .push))
    (slot : StackFrame.Slot frame (CallReturn.stackDestination state)) (af : Bool) :
    ∃ evolved, StackFrame.CPU.Step frame shared evolved state (pushed state) af
        ⟨.next (pushed state), []⟩ ∧
      StackFrame.Current frame evolved (pushed state) ∧
      readWord (pushed state).memory (CallReturn.stackDestination state) = .ok (state.registers .rax) := by
  have allowed : canStoreQWord state.memory (CallReturn.stackDestination state) = true := by
    rw [current.coupled]
    exact (current.contract.ready _ slot).writable
  have stored := (qword_store_sound state.memory _ (state.registers .rax) allowed).1
  have actual := CallReturn.execute_push state .rax false af _ stored
  obtain ⟨evolved, success, next, _, effect⟩ := StackFrame.CPU.push_current current slot actual
  refine ⟨evolved, ?_, next, ?_⟩
  · exact ⟨_, _, decode (current_code current same) .push present pc, actual, rfl, rfl,
      .push slot success, by simp⟩
  · have loaded := readWord_of_loadQWord _ _ _ effect.readback
    rw [← next.coupled] at loaded
    exact loaded

theorem pop_step {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} {value : Word} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile) (present : active profile .pop = true)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile .pop))
    (slot : StackFrame.Slot frame (state.registers .rsp))
    (loaded : readWord state.memory (state.registers .rsp) = .ok value) (af : Bool) :
    StackFrame.CPU.Step frame shared shared state (popped profile state value) af
      ⟨.next (popped profile state value), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  have actual := CallReturn.execute_pop state (popDestination profile) false af value loaded
  have context := StackFrame.CPU.pop_current current slot actual
  exact ⟨_, _, decode (current_code current same) .pop present pc, actual, rfl, rfl,
    .unchanged rfl rfl, context.2.2⟩

theorem inner_ret_step {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} {target : Word} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile .innerRet))
    (slot : StackFrame.Slot frame (state.registers .rsp))
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canon : canonical target = true) (af : Bool) :
    StackFrame.CPU.Step frame shared shared state (finish state target) af
      ⟨.next (finish state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  have actual : CallReturn.execute state (.sequential (.legacy .ret)) af =
      .ok ⟨.returned (finish state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
    CallReturn.execute_ret_success_iff.mpr ⟨target, loaded, canon, rfl, rfl⟩
  exact StackFrame.CPU.private_ret_step current slot (decode (current_code current same) .innerRet rfl pc) actual

theorem root_ret_step {frame : StackFrame.Descriptor} {shared : Borrowing.State} {state : State}
    {profile : Profile} (current : StackFrame.Current frame shared state)
    (same : frame.call.bytes = bytes profile)
    (pc : state.rip = frame.call.code + BitVec.ofNat 64 (offset profile .ret))
    (original : state.registers .rsp = frame.top) (af : Bool) :
    StackFrame.CPU.Step frame shared shared state (finish state frame.call.returnAddress) af
      ⟨.returned (finish state frame.call.returnAddress), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  exact StackFrame.CPU.original_ret_step current original af (decode (current_code current same) .ret rfl pc)

end EDSL.CallStack.Compiler
