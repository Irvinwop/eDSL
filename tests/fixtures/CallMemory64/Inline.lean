/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CallMemory64.Admission
import EDSL.X86.CallReturn.DecodeTransport

set_option warningAsError true

namespace EDSL.CallMemory64.Inline
open X86 OS

/-- Complete candidate text, entry zero: MOV [RDI],RSI; LEA RAX,[RSI+1]; RET. -/
def bytes : List Byte := [0x48,0x89,0x37,0x48,0x8d,0x46,0x01,0xc3]
def program : Program := ⟨bytes, 0⟩

def stored (initial : State) (evolved : Borrowing.State) : State :=
  WordResources64.storeAfterLength initial evolved 3

def increment (state : State) : State := CallReturn.leaState state .rax (.plain .rsi) 1

def finish (resource : Resources) (initial : State) (evolved : Borrowing.State) : State :=
  let before := increment (stored initial evolved)
  { before.writeRegister .rsp (before.registers .rsp + 8) with
    rip := resource.descriptor.frame.call.returnAddress }

def result (resource : Resources) (initial : State) (evolved : Borrowing.State) : CallReturn.Result :=
  ⟨finish resource initial evolved, 3, [⟨.stack, resource.descriptor.frame.top, 8⟩]⟩

theorem current_code {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes) :
    CodeAt state.memory descriptor.frame.call.code bytes := by
  rw [current.coupled, ← same]
  exact current.contract.stack.pureCall.code

theorem entry_pc {resource initial} (pre : ResourcePre program resource initial) :
    initial.rip = resource.descriptor.frame.call.code := by
  simpa only [program, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using pre.entry

theorem stored_pc {resource initial} (pre : ResourcePre program resource initial)
    (evolved : Borrowing.State) :
    (stored initial evolved).rip = resource.descriptor.frame.call.code + 3 := by
  change initial.rip + 3 = _
  rw [entry_pc pre]

theorem increment_pc {resource initial} (pre : ResourcePre program resource initial)
    (evolved : Borrowing.State) :
    (increment (stored initial evolved)).rip = resource.descriptor.frame.call.code + 7 := by
  change (stored initial evolved).rip + 4 = _
  rw [stored_pc pre]
  simp only [BitVec.add_assoc]
  rfl

theorem increment_stack {resource initial} (pre : ResourcePre program resource initial)
    (evolved : Borrowing.State) :
    (increment (stored initial evolved)).registers .rsp = resource.descriptor.frame.top := pre.stack

theorem decode_store {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes) (pc : state.rip = descriptor.frame.call.code) :
    Sequential.decodeAt state = .ok (.storeMem64 (.base .rdi) .rsi) :=
  Sequential.decodeAt_transport
    (Sequential.code_fetch_transport (current_code current same) (by decide)
      0 (by decide) state rfl (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using pc))
    (by rfl : Sequential.decodeAt (Sequential.codeState bytes 0) =
      .ok (.storeMem64 (.base .rdi) .rsi))

/-- Current owner authority derives the ordinary full-width store. Its CPU
state uses exactly the mutated world's complete RAM. -/
theorem store_enabled {resource initial} (pre : ResourcePre program resource initial)
    (af : Bool) :
    ∃ evolved,
      OS.CallMemory64.CPU.Step resource.descriptor resource.shared evolved initial
        (stored initial evolved) af ⟨.next (stored initial evolved), []⟩ ∧
      OS.CallMemory64.Current resource.descriptor evolved (stored initial evolved) ∧
      Borrowing.loadOwnedWord64 evolved resource.descriptor.owner resource.descriptor.ticket
        resource.descriptor.target = .ok resource.value := by
  have decoded := decode_store pre.current pre.code (entry_pc pre)
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rsi) initial =
      some (resource.descriptor.target, resource.value) := by
    simp only [Sequential.Instruction.storeIntent64, Sequential.Address.eval, pre.pointer, pre.argument]
  obtain ⟨evolved, _, _, step, current, _, readback⟩ :=
    OS.CallMemory64.CPU.data_store_step pre.current decoded intent af
  exact ⟨evolved, step, current, readback⟩

theorem store_fetch {resource initial} (pre : ResourcePre program resource initial) :
    CallStack.FetchWithin resource.descriptor.frame initial := by
  refine ⟨0, .sequential (.storeMem64 (.base .rdi) .rsi), pre.entry,
    CallReturn.decodeAt_sequential (decode_store pre.current pre.code (entry_pc pre)), ?_⟩
  rw [pre.code]
  decide

theorem decode_increment {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes)
    (pc : state.rip = descriptor.frame.call.code + 3) :
    CallReturn.decodeAt state = .ok (.leaDisp8 .rax (.plain .rsi) 1) :=
  CallReturn.decodeAt_code (current_code current same) (by decide)
    (by decide : 3 < bytes.length) state rfl pc rfl

theorem increment_step {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes)
    (pc : state.rip = descriptor.frame.call.code + 3) (af : Bool) :
    OS.CallMemory64.CPU.Step descriptor shared shared state (increment state) af
      ⟨.next (increment state), []⟩ :=
  OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode_increment current same pc, rfl, rfl, rfl, .unchanged rfl rfl,
      by simp [Sequential.Instruction.operandReads]⟩

theorem increment_fetch {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes)
    (pc : state.rip = descriptor.frame.call.code + 3) : CallStack.FetchWithin descriptor.frame state :=
  ⟨3, _, pc, decode_increment current same pc, by rw [same]; decide⟩

theorem decode_ret {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes)
    (pc : state.rip = descriptor.frame.call.code + 7) :
    CallReturn.decodeAt state = .ok (.sequential (.legacy .ret)) :=
  CallReturn.decodeAt_code (current_code current same) (by decide)
    (by decide : 7 < bytes.length) state rfl pc rfl

theorem ret_fetch {descriptor : OS.CallMemory64.Descriptor} {shared : Borrowing.State}
    {state : State} (current : OS.CallMemory64.Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes)
    (pc : state.rip = descriptor.frame.call.code + 7) : CallStack.FetchWithin descriptor.frame state :=
  ⟨7, _, pc, decode_ret current same pc, by rw [same]; decide⟩

/-- All three complete fetches and the original-slot RET belong to the same
actual mixed trace, for every admitted state and AF choice stream. -/
theorem covered {resource initial} (pre : ResourcePre program resource initial)
    (choices : CallReturn.Choices) {evolved : Borrowing.State}
    (first : OS.CallMemory64.CPU.Step resource.descriptor resource.shared evolved initial
      (stored initial evolved) (choices 0) ⟨.next (stored initial evolved), []⟩)
    (current : OS.CallMemory64.Current resource.descriptor evolved (stored initial evolved)) :
    OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial evolved
      (result resource initial evolved) := by
  have middle := increment_step current pre.code (stored_pc pre evolved) ((choices.drop 1) 0)
  have lastCurrent := middle.current current
  have decoded := decode_ret lastCurrent pre.code (increment_pc pre evolved)
  have last := OS.CallMemory64.CPU.lift_stack
    (StackFrame.CPU.original_ret_step lastCurrent.stack (increment_stack pre evolved)
      (((choices.drop 1).drop 1) 0) decoded)
  have trace := OS.CallMemory64.CoveredExecution.next first (store_fetch pre)
    (.next middle (increment_fetch current pre.code (stored_pc pre evolved))
      (.ret last (ret_fetch lastCurrent pre.code (increment_pc pre evolved))))
  simpa only [result, finish, Sequential.Result.prepend, List.nil_append, increment_stack pre] using trace

theorem preserved {resource initial evolved} (register : Register)
    (outside : register ∉ CallStack.clobbers) :
    (finish resource initial evolved).registers register = initial.registers register := by
  have notSP : register ≠ .rsp := by
    intro same
    subst register
    exact outside (by decide)
  have notAX : register ≠ .rax := by
    intro same
    subst register
    exact outside (by decide)
  simp only [finish, increment, CallReturn.leaState, State.writeRegister,
    ite_eq_right notSP, ite_eq_right notAX, stored, WordResources64.storeAfterLength]

theorem post {resource initial} (pre : ResourcePre program resource initial)
    {choices evolved}
    (trace : OS.CallMemory64.CoveredExecution resource.descriptor choices resource.shared initial
      evolved (result resource initial evolved))
    (readback : Borrowing.loadOwnedWord64 evolved resource.descriptor.owner resource.descriptor.ticket
      resource.descriptor.target = .ok resource.value) :
    Post (resourceInput resource) initial (result resource initial evolved).state := by
  have memory := trace.memory_frame pre.current
  refine ⟨?_, ?_, memory.1, memory.2.1, memory.2.2, rfl, ?_, preserved, rfl⟩
  · change (initial.registers .rsi + 1).toNat = resultNat resource.value
    rw [pre.argument]
    exact one_addition resource.value
  · exact Borrowing.loadOwnedWord64_readWord _ _ _ _ _ readback
  · change initial.registers .rsp + 8 = initial.registers .rsp + 8
    rfl

/-- Universal client proof of the existing independent semantic contract.
No CALL, reload, cost, compiler profile or future access enters admission. -/
theorem semantic_claim : SemanticClaim program := by
  intro resource initial pre choices
  obtain ⟨evolved, first, current, readback⟩ := store_enabled pre (choices 0)
  have trace := covered pre choices first current
  exact ⟨evolved, result resource initial evolved, trace, post pre trace readback⟩

/-- The independent reachable resource domain supplies useful admitted inputs. -/
theorem claim : Claim program :=
  ⟨semantic_claim, domain_nonvacuous program (by decide) (by decide)⟩

/-- Exact evaluator success, retaining the actual endpoint, both current
capabilities, union history, RAM frame and ABI through `Returned`. -/
theorem exact_three {resource initial} (pre : ResourcePre program resource initial)
    (choices : CallReturn.Choices) :
    ∃ evolved result, CallReturn.run choices 3 initial = .ok result ∧
      Returned resource initial choices evolved result ∧ result.instructions = 3 := by
  obtain ⟨evolved, first, current, readback⟩ := store_enabled pre (choices 0)
  have trace := covered pre choices first current
  have machine : CallReturn.Executes choices initial (result resource initial evolved) := by
    simpa only [CallReturn.Executes, pre.stack] using trace.machine
  exact ⟨evolved, result resource initial evolved,
    CallReturn.run_complete machine (Nat.le_refl _),
    Returned.of_covered pre trace (post pre trace readback), rfl⟩

end EDSL.CallMemory64.Inline
