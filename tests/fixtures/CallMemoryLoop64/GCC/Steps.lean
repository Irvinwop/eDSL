/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64Programs
import EDSL.OS.CallMemory64.Coverage
import EDSL.OS.CallMemory64.Private
import EDSL.CallStack.Geometry

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.GCC
open X86 OS

abbrev Descriptor := OS.CallMemory64.Descriptor
abbrev Shared := Borrowing.State
abbrev Current := OS.CallMemory64.Current
abbrev CoveredHistory := OS.CallMemory64.CoveredHistory
abbrev CoveredExecution := OS.CallMemory64.CoveredExecution
abbrev text := Compiler.bytes .gccSeparate

/-- A real continuing mixed instruction, including its complete fetch extent. -/
structure Next (descriptor : Descriptor) (shared evolved : Shared) (before after : State)
    (af : Bool) (reads : List CallReturn.Read := []) : Prop where
  step : OS.CallMemory64.CPU.Step descriptor shared evolved before after af ⟨.next after, reads⟩
  fetch : CallStack.FetchWithin descriptor.frame before

theorem Next.current {descriptor shared evolved before after af reads}
    (next : Next descriptor shared evolved before after af reads)
    (current : Current descriptor shared before) : Current descriptor evolved after :=
  next.step.current current

theorem current_code {descriptor shared state} (current : Current descriptor shared state)
    (same : descriptor.frame.call.bytes = text) :
    CodeAt state.memory descriptor.frame.call.code text := by
  rw [current.coupled, ← same]
  exact current.contract.stack.pureCall.code

theorem fetch {descriptor shared state offset instruction}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (member : (offset, instruction) ∈ Compiler.sites .gccSeparate)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset) :
    CallStack.FetchWithin descriptor.frame state :=
  Compiler.fetchWithin (current_code current same) same member pc

theorem decode {descriptor shared state offset instruction}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (member : (offset, instruction) ∈ Compiler.sites .gccSeparate)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset) :
    CallReturn.decodeAt state = .ok instruction :=
  Compiler.decode (current_code current same) member pc

theorem decode_sequential {descriptor shared state offset instruction}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (member : (offset, CallReturn.Instruction.sequential instruction) ∈ Compiler.sites .gccSeparate)
    (static : Sequential.decodeAt (Sequential.codeState text offset) = .ok instruction)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset) :
    Sequential.decodeAt state = .ok instruction := by
  exact Sequential.decodeAt_transport
    (Sequential.code_fetch_transport (current_code current same) (by decide)
      offset (Compiler.inside member) state rfl pc)
    static

def moved (state : State) (destination source : Register) : State :=
  { state.writeRegister destination (state.registers source) with rip := state.rip + 3 }

def pushed (state : State) (source : Register) : State :=
  CallReturn.pushState state false
    (writeQWordUnchecked state.memory (CallReturn.stackDestination state) (state.registers source))

def called (state : State) : State :=
  CallReturn.callState state 13
    (writeQWordUnchecked state.memory (CallReturn.stackDestination state) (CallReturn.returnAddress state))

def tested (state : State) (af : Bool) : State :=
  { state with
    rip := state.rip + 3
    flags := Sequential.logicalFlags64 state.flags (state.registers .rbx) af }

def decremented (state : State) : State :=
  { state.writeRegister .rbx (state.registers .rbx - 1) with
    rip := state.rip + 3, flags := Sequential.decFlags64 state.flags (state.registers .rbx) }

def atPC (state : State) (pc : Word) : State := { state with rip := pc }

def stored (state : State) (world : Shared) : State :=
  WordResources64.storeAfterLength state world 3

def loaded (state : State) (value : Word) : State :=
  { state.writeRegister .rax value with rip := state.rip + 3 }

def advanced (state : State) : State := CallReturn.leaState state .rsi (.plain .rax) 1

def popped (state : State) (destination : Register) (value : Word) : State :=
  CallReturn.popState state destination false value

def finished (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

theorem pure_next {descriptor shared state after offset instruction af}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (member : (offset, instruction) ∈ Compiler.sites .gccSeparate)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset)
    (actual : CallReturn.execute state instruction af = .ok ⟨.next after, []⟩)
    (noWrite : instruction.writeEffect state = none) (memory : after.memory = state.memory) :
    Next descriptor shared shared state after af :=
  ⟨OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode current same member pc, actual, rfl, rfl,
      .unchanged noWrite memory, by simp⟩,
    fetch current same member pc⟩

theorem move_next {descriptor shared state offset destination source}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (member : (offset, .sequential (.movReg64 destination source)) ∈ Compiler.sites .gccSeparate)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset) (af : Bool) :
    Next descriptor shared shared state (moved state destination source) af :=
  pure_next current same member pc rfl rfl rfl

theorem push_next {descriptor shared state offset source}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (member : (offset, .push64 source false) ∈ Compiler.sites .gccSeparate)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset)
    (slot : StackFrame.Slot descriptor.frame (CallReturn.stackDestination state)) (af : Bool) :
    ∃ evolved, Next descriptor shared evolved state (pushed state source) af ∧
      Borrowing.mutate shared (.store64 descriptor.owner descriptor.frame.ticket
        (CallReturn.stackDestination state) (state.registers source)) = .ok (evolved, none) ∧
      Borrowing.StoreEffect64 shared evolved (CallReturn.stackDestination state) (state.registers source) ∧
      readWord (pushed state source).memory (CallReturn.stackDestination state) = .ok (state.registers source) := by
  have writable : canStoreQWord state.memory (CallReturn.stackDestination state) = true := by
    rw [current.coupled]
    exact (current.contract.stack.ready _ slot).writable
  have write := (qword_store_sound state.memory _ (state.registers source) writable).1
  have actual := CallReturn.execute_push state source false af _ write
  obtain ⟨evolved, success, _, _, effect⟩ := StackFrame.CPU.push_current current.stack slot actual
  have next : Next descriptor shared evolved state (pushed state source) af :=
    ⟨OS.CallMemory64.CPU.lift_stack
      ⟨_, _, decode current same member pc, actual, rfl, rfl, .push slot success, by simp⟩,
      fetch current same member pc⟩
  refine ⟨evolved, next, success, effect, ?_⟩
  rw [(next.current current).coupled]
  exact readWord_of_loadQWord _ _ _ effect.readback

theorem test_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 9) (af : Bool) :
    Next descriptor shared shared state (tested state af) af :=
  pure_next current same (by decide : (9, .sequential (.test64 .rbx .rbx)) ∈ Compiler.sites .gccSeparate) pc
    (by simp only [CallReturn.execute_sequential, Sequential.execute_test64, BitVec.and_self, tested])
    rfl rfl

theorem guard_next {descriptor shared state} {zero : Bool}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 12)
    (flag : state.flags.getLsbD 6 = zero) (af : Bool) :
    Next descriptor shared shared state
      (atPC state (descriptor.frame.call.code + if zero then 31 else 14)) af := by
  refine pure_next (after := atPC state (descriptor.frame.call.code + if zero then 31 else 14))
    current same (by decide : (12, .sequential (.je 17)) ∈ Compiler.sites .gccSeparate) pc ?_ rfl rfl
  have displacement : (12 : Word) + 2 + (17 : Byte).signExtend 64 = 31 := by decide
  have canon : canonical (descriptor.frame.call.code + 31) = true :=
    Sequential.code_canonical_offset (current_code current same) 31 (by decide)
  rw [CallReturn.execute_sequential, Sequential.execute_je, flag]
  cases zero with
  | false => simp [executeShortBranch, pc, BitVec.add_assoc, atPC]
  | true =>
      simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement, atPC]
      rw [canon]
      rfl

theorem decrement_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 17) (af : Bool) :
    Next descriptor shared shared state (decremented state) af :=
  pure_next current same (by decide : (17, .sequential (.dec64 .rbx)) ∈ Compiler.sites .gccSeparate) pc rfl rfl rfl

theorem call_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 20)
    (slot : StackFrame.Slot descriptor.frame (CallReturn.stackDestination state)) (af : Bool) :
    ∃ evolved, Next descriptor shared evolved state (called state) af ∧
      Borrowing.mutate shared (.store64 descriptor.owner descriptor.frame.ticket
        (CallReturn.stackDestination state) (CallReturn.returnAddress state)) = .ok (evolved, none) ∧
      Borrowing.StoreEffect64 shared evolved (CallReturn.stackDestination state) (CallReturn.returnAddress state) ∧
      readWord (called state).memory (CallReturn.stackDestination state) = .ok (CallReturn.returnAddress state) := by
  have canon : canonical (CallReturn.callTarget state 13) = true := by
    have target : CallReturn.callTarget state 13 = descriptor.frame.call.code + 38 := by
      simp [CallReturn.callTarget, CallReturn.returnAddress, pc, BitVec.add_assoc]
    rw [target]
    exact Sequential.code_canonical_offset (current_code current same) 38 (by decide)
  have writable : canStoreQWord state.memory (CallReturn.stackDestination state) = true := by
    rw [current.coupled]
    exact (current.contract.stack.ready _ slot).writable
  have write := (qword_store_sound state.memory _ (CallReturn.returnAddress state) writable).1
  have actual := CallReturn.execute_call state 13 af _ canon write
  obtain ⟨evolved, success, _, _, effect⟩ := StackFrame.CPU.call_current current.stack slot actual
  have next : Next descriptor shared evolved state (called state) af :=
    ⟨OS.CallMemory64.CPU.lift_stack
      ⟨_, _, decode current same (by decide : (20, .callRelative32 13) ∈ Compiler.sites .gccSeparate) pc,
        actual, rfl, rfl, .call slot success, by simp⟩,
      fetch current same (by decide : (20, .callRelative32 13) ∈ Compiler.sites .gccSeparate) pc⟩
  refine ⟨evolved, next, success, effect, ?_⟩
  rw [(next.current current).coupled]
  exact readWord_of_loadQWord _ _ _ effect.readback

theorem store_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 38)
    (pointer : state.registers .rdi = descriptor.target) (af : Bool) :
    ∃ evolved, Next descriptor shared evolved state (stored state evolved) af ∧
      Borrowing.StoreEffect64 shared evolved descriptor.target (state.registers .rsi) ∧
      Borrowing.loadOwnedWord64 evolved descriptor.owner descriptor.ticket descriptor.target =
        .ok (state.registers .rsi) := by
  have decoded := decode_sequential current same (by decide :
    (38, .sequential (.storeMem64 (.base .rdi) .rsi)) ∈ Compiler.sites .gccSeparate) rfl pc
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rsi) state =
      some (descriptor.target, state.registers .rsi) := by
    simp [Sequential.Instruction.storeIntent64, Sequential.Address.eval, pointer]
  obtain ⟨evolved, _, _, step, _, effect, readback⟩ :=
    OS.CallMemory64.CPU.data_store_step current decoded intent af
  exact ⟨evolved, ⟨step, fetch current same (by decide :
    (38, .sequential (.storeMem64 (.base .rdi) .rsi)) ∈ Compiler.sites .gccSeparate) pc⟩, effect, readback⟩

theorem load_next {descriptor shared state value}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 41)
    (pointer : state.registers .rdi = descriptor.target)
    (readback : Borrowing.loadOwnedWord64 shared descriptor.owner descriptor.ticket descriptor.target = .ok value)
    (af : Bool) :
    Next descriptor shared shared state (loaded state value) af [⟨.data, descriptor.target, 8⟩] := by
  have decoded := decode_sequential current same (by decide :
    (41, .sequential (.loadMem64 .rax (.base .rdi))) ∈ Compiler.sites .gccSeparate) rfl pc
  obtain ⟨observed, owned, _, step, _, _⟩ :=
    OS.CallMemory64.CPU.data_load_step current decoded pointer af
  have sameValue := Except.ok.inj (owned.symm.trans readback)
  subst observed
  exact ⟨step, fetch current same (by decide :
    (41, .sequential (.loadMem64 .rax (.base .rdi))) ∈ Compiler.sites .gccSeparate) pc⟩

theorem inner_ret_next {descriptor shared state target}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 44)
    (slot : StackFrame.Slot descriptor.frame (state.registers .rsp))
    (readback : readWord state.memory (state.registers .rsp) = .ok target)
    (canon : canonical target = true) (af : Bool) :
    Next descriptor shared shared state (finished state target) af [⟨.stack, state.registers .rsp, 8⟩] := by
  have actual : CallReturn.execute state (.sequential (.legacy .ret)) af =
      .ok ⟨.returned (finished state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
    CallReturn.execute_ret_success_iff.mpr ⟨target, readback, canon, rfl, rfl⟩
  exact ⟨OS.CallMemory64.CPU.lift_stack (StackFrame.CPU.private_ret_step current.stack slot
    (decode current same (by decide : (44, .sequential (.legacy .ret)) ∈ Compiler.sites .gccSeparate) pc) actual),
      fetch current same (by decide : (44, .sequential (.legacy .ret)) ∈ Compiler.sites .gccSeparate) pc⟩

theorem advance_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 25) (af : Bool) :
    Next descriptor shared shared state (advanced state) af :=
  pure_next current same (by decide : (25, .leaDisp8 .rsi (.plain .rax) 1) ∈ Compiler.sites .gccSeparate) pc rfl rfl rfl

theorem back_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 29) (af : Bool) :
    Next descriptor shared shared state (atPC state (descriptor.frame.call.code + 9)) af := by
  refine pure_next (after := atPC state (descriptor.frame.call.code + 9)) current same
    (by decide : (29, .sequential (.jmp 234)) ∈ Compiler.sites .gccSeparate) pc ?_ rfl rfl
  have displacement : (29 : Word) + 2 + (234 : Byte).signExtend 64 = 9 := by decide
  have canon : canonical (descriptor.frame.call.code + 9) = true :=
    Sequential.code_canonical_offset (current_code current same) 9 (by decide)
  simp only [CallReturn.execute_sequential, Sequential.execute_jmp, executeShortBranch,
    ite_true, pc, BitVec.add_assoc, displacement, atPC]
  rw [canon]
  rfl

theorem pop_next {descriptor shared state offset destination value}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (member : (offset, .pop64 destination false) ∈ Compiler.sites .gccSeparate)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset)
    (slot : StackFrame.Slot descriptor.frame (state.registers .rsp))
    (readback : readWord state.memory (state.registers .rsp) = .ok value) (af : Bool) :
    Next descriptor shared shared state (popped state destination value) af [⟨.stack, state.registers .rsp, 8⟩] := by
  have actual := CallReturn.execute_pop state destination false af value readback
  have context := StackFrame.CPU.pop_current current.stack slot actual
  exact ⟨OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode current same member pc, actual, rfl, rfl, .unchanged rfl rfl, context.2.2⟩,
    fetch current same member pc⟩

theorem root_ret {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = text)
    (pc : state.rip = descriptor.frame.call.code + 37)
    (original : state.registers .rsp = descriptor.frame.top) (choices : CallReturn.Choices) :
    CoveredExecution descriptor choices shared state shared
      ⟨finished state descriptor.frame.call.returnAddress, 1, [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  .ret (OS.CallMemory64.CPU.lift_stack (StackFrame.CPU.original_ret_step current.stack original (choices 0)
    (decode current same (by decide : (37, .sequential (.legacy .ret)) ∈ Compiler.sites .gccSeparate) pc)))
    (fetch current same (by decide : (37, .sequential (.legacy .ret)) ∈ Compiler.sites .gccSeparate) pc)

end EDSL.CallMemoryLoop64.GCC
