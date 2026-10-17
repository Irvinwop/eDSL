/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.OS.CallMemory64.Coverage
import EDSL.CallMemory64.Domain
import EDSL.CallStack.Geometry
import EDSL.X86.CallReturn.DecodeTransport
import EDSL.Audit

set_option warningAsError true

namespace EDSL.Tests.CallMemory64CPU
open X86 OS OS.CallMemory64

-- Owned synthetic program: MOV [RDI],RSI; MOV RAX,[RDI]; CALL helper;
-- caller RET; helper RET. The DATA write precedes a real private CALL write.
-- Neither the expected loaded word nor the return target uses an encoder.
def bytes : List Byte := [0x48,0x89,0x37,0x48,0x8b,0x07,0xe8,1,0,0,0,0xc3,0xc3]

private theorem code {descriptor shared before}
    (current : Current descriptor shared before) (same : descriptor.frame.call.bytes = bytes) :
    CodeAt before.memory descriptor.frame.call.code bytes := by
  rw [current.coupled, ← same]
  exact current.contract.stack.pureCall.code

private theorem decoded {descriptor shared before instruction} {offset : Nat}
    (current : Current descriptor shared before) (same : descriptor.frame.call.bytes = bytes)
    (inside : offset < bytes.length)
    (pc : before.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset)
    (static : CallReturn.decodeAt (Sequential.codeState bytes offset) = .ok instruction) :
    CallReturn.decodeAt before = .ok instruction :=
  CallReturn.decodeAt_code (code current same) (by decide) inside before rfl pc static

private theorem seq_decoded {descriptor shared before instruction} {offset : Nat}
    (current : Current descriptor shared before) (same : descriptor.frame.call.bytes = bytes)
    (inside : offset < bytes.length)
    (pc : before.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset)
    (static : Sequential.decodeAt (Sequential.codeState bytes offset) = .ok instruction) :
    Sequential.decodeAt before = .ok instruction :=
  Sequential.decodeAt_transport
    (Sequential.code_fetch_transport (code current same) (by decide) offset inside before rfl pc) static

private theorem fetch {descriptor : Descriptor} {before : State}
    {instruction : CallReturn.Instruction} {offset : Nat}
    (same : descriptor.frame.call.bytes = bytes)
    (pc : before.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset)
    (actual : CallReturn.decodeAt before = .ok instruction)
    (bound : offset + instruction.length ≤ bytes.length) :
    EDSL.CallStack.FetchWithin descriptor.frame before :=
  ⟨offset, instruction, pc, actual, by rwa [same]⟩

/-- A real decoded mixed run, for arbitrary current memory, full64 input and
other registers/flags. Independent endpoint requirements exercise DATA
readback, private CALL authority, full RAM recoupling and BOTH actual RETs. -/
theorem mixed_run {descriptor : Descriptor} {shared : Shared} {initial : State}
    (current : Current descriptor shared initial) (same : descriptor.frame.call.bytes = bytes)
    (pc : initial.rip = descriptor.frame.call.code)
    (stack : initial.registers .rsp = descriptor.frame.top)
    (pointer : initial.registers .rdi = descriptor.target)
    (capacity : 8 ≤ descriptor.frame.capacity) (choices : CallReturn.Choices) :
    ∃ evolved result,
      CoveredExecution descriptor choices shared initial evolved result ∧
      CallReturn.runFrom descriptor.frame.top choices 5 initial = .ok result ∧
      result.instructions = 5 ∧ result.state.registers .rax = initial.registers .rsi ∧
      readWord result.state.memory descriptor.target = .ok (initial.registers .rsi) ∧
      result.state.rip = descriptor.frame.call.returnAddress ∧
      result.state.registers .rsp = descriptor.frame.top + 8 ∧
      result.state.flags = initial.flags ∧
      result.reads = [⟨.data,descriptor.target,8⟩,
        ⟨.stack,descriptor.frame.top - 8,8⟩,⟨.stack,descriptor.frame.top,8⟩] ∧
      Current descriptor evolved result.state ∧ Preservation descriptor shared evolved := by
  have pc0 : initial.rip = descriptor.frame.call.code + BitVec.ofNat 64 0 := by simpa using pc
  have storeDecoded := seq_decoded current same (offset := 0) (by decide) pc0
    (show Sequential.decodeAt (Sequential.codeState bytes 0) =
      .ok (.storeMem64 (.base .rdi) .rsi) by rfl)
  have intent : (Sequential.Instruction.storeMem64 (.base .rdi) .rsi).storeIntent64 initial =
      some (descriptor.target, initial.registers .rsi) := by
    simpa only [Sequential.Instruction.storeIntent64, Sequential.Address.eval] using
      congrArg (fun address => some (address, initial.registers .rsi)) pointer
  obtain ⟨dataWorld, stored, _, storeStep, storedCurrent, _, readback⟩ :=
    CPU.data_store_step current storeDecoded intent (choices 0)
  let storedCpu := WordResources64.storeAfterLength initial dataWorld 3
  change CPU.Step descriptor shared dataWorld initial storedCpu (choices 0)
    ⟨.next storedCpu, []⟩ at storeStep
  change Current descriptor dataWorld storedCpu at storedCurrent
  have storedPC : storedCpu.rip = descriptor.frame.call.code + 3 := by
    exact congrArg (· + 3) pc
  have storedPointer : storedCpu.registers .rdi = descriptor.target := pointer
  have loadDecoded := seq_decoded storedCurrent same (offset := 3) (by decide) storedPC
    (show Sequential.decodeAt (Sequential.codeState bytes 3) =
      .ok (.loadMem64 .rax (.base .rdi)) by rfl)
  obtain ⟨value, observed, _, loadStep, loadedCurrent, _⟩ :=
    CPU.data_load_step storedCurrent loadDecoded storedPointer ((choices.drop 1) 0)
  have valueEq : value = initial.registers .rsi := Except.ok.inj (observed.symm.trans readback)
  subst value
  let loadedCpu : State := { storedCpu.writeRegister .rax (initial.registers .rsi) with
    rip := storedCpu.rip + 3 }
  change CPU.Step descriptor dataWorld dataWorld storedCpu loadedCpu ((choices.drop 1) 0)
    ⟨.next loadedCpu, [⟨.data,descriptor.target,8⟩]⟩ at loadStep
  change Current descriptor dataWorld loadedCpu at loadedCurrent
  have loadedPC : loadedCpu.rip = descriptor.frame.call.code + 6 := by
    simp only [loadedCpu, storedPC, BitVec.add_assoc]
    rfl
  have loadedStack : loadedCpu.registers .rsp = descriptor.frame.top := by
    simpa [loadedCpu, State.writeRegister, storedCpu, WordResources64.storeAfterLength] using stack
  have callDecoded := decoded loadedCurrent same (offset := 6) (by decide) loadedPC
    (show CallReturn.decodeAt (Sequential.codeState bytes 6) = .ok (.callRelative32 1) by rfl)
  have slot : StackFrame.Slot descriptor.frame (CallReturn.stackDestination loadedCpu) := by
    rw [CallReturn.stackDestination, loadedStack]
    exact EDSL.CallStack.private_slot_at_depth loadedCurrent.contract.stack (by decide) capacity
  have target : CallReturn.callTarget loadedCpu 1 = descriptor.frame.call.code + 12 := by
    simp only [CallReturn.callTarget, CallReturn.returnAddress, loadedPC, BitVec.add_assoc]
    rfl
  have canon : canonical (CallReturn.callTarget loadedCpu 1) = true := by
    rw [target]
    exact Sequential.code_canonical_offset (code loadedCurrent same) 12 (by decide)
  obtain ⟨callWorld, _, privateStep, _, callStored⟩ :=
    StackFrame.CPU.call_enabled loadedCurrent.stack slot 1 (((choices.drop 1).drop 1) 0)
      callDecoded canon
  let calledCpu := CallReturn.callState loadedCpu 1 (AddressSpace.toMemory callWorld.resources.space)
  change Borrowing.mutate dataWorld (.store64 descriptor.frame.owner descriptor.frame.ticket
    (CallReturn.stackDestination loadedCpu) (CallReturn.returnAddress loadedCpu)) =
      .ok (callWorld, none) at callStored
  have callStep : CPU.Step descriptor dataWorld callWorld loadedCpu calledCpu
      (((choices.drop 1).drop 1) 0) ⟨.next calledCpu, []⟩ := CPU.lift_stack privateStep
  have calledCurrent := callStep.current loadedCurrent
  have calledPC : calledCpu.rip = descriptor.frame.call.code + 12 := target
  have calledStack : calledCpu.registers .rsp = descriptor.frame.top - 8 := by
    simp [calledCpu, CallReturn.callState, CallReturn.stackDestination, State.writeRegister, loadedStack]
  have continuation : CallReturn.returnAddress loadedCpu = descriptor.frame.call.code + 11 := by
    simp only [CallReturn.returnAddress, loadedPC, BitVec.add_assoc]
    rfl
  have loadedReturn : readWord calledCpu.memory (calledCpu.registers .rsp) =
      .ok (descriptor.frame.call.code + 11) := by
    change readWord (AddressSpace.toMemory callWorld.resources.space)
      (CallReturn.stackDestination loadedCpu) = .ok (descriptor.frame.call.code + 11)
    rw [← continuation]
    exact Borrowing.store64_readWord callStored
  have returnCanon : canonical (descriptor.frame.call.code + 11) = true :=
    Sequential.code_canonical_offset (code calledCurrent same) 11 (by decide)
  let resumed : State := { calledCpu.writeRegister .rsp (calledCpu.registers .rsp + 8) with
    rip := descriptor.frame.call.code + 11 }
  have retDecoded := decoded calledCurrent same (offset := 12) (by decide) calledPC
    (show CallReturn.decodeAt (Sequential.codeState bytes 12) = .ok (.sequential (.legacy .ret)) by rfl)
  have internalActual : CallReturn.execute calledCpu (.sequential (.legacy .ret))
      ((((choices.drop 1).drop 1).drop 1) 0) =
      .ok ⟨.returned resumed, [⟨.stack, calledCpu.registers .rsp, 8⟩]⟩ :=
    CallReturn.execute_ret_success_iff.mpr ⟨_, loadedReturn, returnCanon, rfl, rfl⟩
  have calledSlot : StackFrame.Slot descriptor.frame (calledCpu.registers .rsp) := slot
  have internalStep := CPU.lift_stack (descriptor := descriptor)
    (StackFrame.CPU.private_ret_step calledCurrent.stack calledSlot
      retDecoded internalActual)
  have resumedCurrent := internalStep.current calledCurrent
  have resumedStack : resumed.registers .rsp = descriptor.frame.top := by
    change calledCpu.registers .rsp + 8 = descriptor.frame.top
    rw [calledStack, BitVec.sub_add_cancel]
  have terminalDecoded := decoded resumedCurrent same (offset := 11) (by decide) rfl
    (show CallReturn.decodeAt (Sequential.codeState bytes 11) = .ok (.sequential (.legacy .ret)) by rfl)
  have terminalStep := CPU.lift_stack (descriptor := descriptor)
    (StackFrame.CPU.original_ret_step resumedCurrent.stack resumedStack
      (((((choices.drop 1).drop 1).drop 1).drop 1) 0) terminalDecoded)
  have covered := CoveredExecution.next storeStep
    (fetch same pc0 (CallReturn.decodeAt_sequential storeDecoded) (by decide))
    (CoveredExecution.next loadStep
      (fetch same storedPC (CallReturn.decodeAt_sequential loadDecoded) (by decide))
    (CoveredExecution.next callStep (fetch same loadedPC callDecoded (by decide))
    (CoveredExecution.next internalStep (fetch same calledPC retDecoded (by decide))
    (CoveredExecution.ret terminalStep (fetch same rfl terminalDecoded (by decide))))))
  have finalCurrent := covered.current current
  have retained := private_store64_preserves_data loadedCurrent.contract slot callStored observed
  refine ⟨callWorld, _, covered, covered.run (by change (5 : Nat) ≤ 5; decide), rfl,
    ?_, ?_, rfl, ?_, rfl, ?_,
    finalCurrent, covered.preserves⟩
  · change resumed.registers .rax = initial.registers .rsi
    simp [resumed, calledCpu, CallReturn.callState, loadedCpu, State.writeRegister]
  · rw [finalCurrent.coupled]
    exact Borrowing.loadOwnedWord64_readWord _ _ _ _ _ retained
  · change resumed.registers .rsp + 8 = descriptor.frame.top + 8
    rw [resumedStack]
  · simp only [Sequential.Result.prepend, List.nil_append, List.cons_append,
      calledStack, resumedStack]

/-- Instantiate the synthetic run in the real shared domain: target ticket 5
is allocated AFTER private ticket 4. Arbitrary old DATA contents and full64
inputs witness that the mixed execution premises are inhabited. -/
theorem concrete_mixed_run (input old : Word) (registers : Register → Word) (flags : Word)
    (choices : CallReturn.Choices) :
    ∃ result, CallReturn.run choices 5
        (EDSL.CallMemory64.Domain.initial ⟨bytes, 0⟩ input old registers flags) = .ok result ∧
      result.state.registers .rax = input ∧
      readWord result.state.memory EDSL.CallMemory64.Domain.target = .ok input ∧
      result.instructions = 5 ∧ result.state.flags = flags := by
  have current := EDSL.CallMemory64.Domain.current ⟨bytes, 0⟩ (by decide) (by decide)
    input old registers flags
  obtain ⟨world, result, _, ran, count, value, stored, _, _, flagsEq, _, _, _⟩ :=
    mixed_run current rfl (by simp [EDSL.CallMemory64.Domain.initial]) rfl rfl (by decide) choices
  exact ⟨result, ran, value, stored, count, flagsEq⟩

-- A readable word at another address cannot become a target observation, and
-- four-byte reads remain excluded even if the RAM primitive accepts them.
example {descriptor : Descriptor} {shared : Shared} {address : Word}
    (wrong : address ≠ descriptor.target) :
    ¬ReadAllowed descriptor shared ⟨.data,address,8⟩ := by
  intro allowed
  exact wrong (allowed.data_target rfl).1

example {descriptor : Descriptor} {shared : Shared} {address : Word} :
    ¬ReadAllowed descriptor shared ⟨.data,address,4⟩ := by
  intro allowed
  exact (by decide : (4 : Nat) ≠ 8) allowed.bytes

-- A store through another pointer cannot acquire the selected ticket's effect.
example {descriptor : Descriptor} {shared evolved : Shared} {before after : State}
    {address : Sequential.Address} {source : Register}
    (wrong : address.eval before ≠ descriptor.target) :
    ¬CPU.Effect descriptor shared evolved before after (.sequential (.storeMem64 address source)) := by
  intro effect
  exact wrong (effect.data64_checked rfl).1

example {descriptor : Descriptor} {shared evolved : Shared} {before after : State}
    {address : Sequential.Address} {source : Register} :
    ¬CPU.Effect descriptor shared evolved before after (.sequential (.storeMem32 address source)) := by
  intro effect
  exact effect.no_data32 rfl

end EDSL.Tests.CallMemory64CPU

#print axioms EDSL.OS.CallMemory64.CPU.data_store_step
#print axioms EDSL.OS.CallMemory64.CPU.current_target_read
#print axioms EDSL.OS.CallMemory64.CPU.lift_stack
#print axioms EDSL.OS.CallMemory64.CPU.Step.current
#print axioms EDSL.OS.CallMemory64.CPU.Step.unlocked
#print axioms EDSL.OS.CallMemory64.CPU.Step.no_syscall
#print axioms EDSL.OS.CallMemory64.CPU.Effect.data64_checked
#print axioms EDSL.OS.CallMemory64.CoveredExecution.machine
#print axioms EDSL.OS.CallMemory64.CoveredExecution.prefix_current
#print axioms EDSL.OS.CallMemory64.CoveredExecution.memory_frame
#print axioms EDSL.Tests.CallMemory64CPU.mixed_run
#print axioms EDSL.Tests.CallMemory64CPU.concrete_mixed_run
#audit_edsl
