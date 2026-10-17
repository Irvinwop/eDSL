/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64.ClosedForm.Code

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.ClosedForm
open X86 OS

abbrev Descriptor := OS.CallMemory64.Descriptor
abbrev Shared := Borrowing.State
abbrev Current := OS.CallMemory64.Current
abbrev CoveredHistory := OS.CallMemory64.CoveredHistory
abbrev CoveredExecution := OS.CallMemory64.CoveredExecution

/-- One actual read-free continuing instruction and its full fetch extent. -/
structure Next (descriptor : Descriptor) (shared evolved : Shared) (before after : State)
    (af : Bool) : Prop where
  step : OS.CallMemory64.CPU.Step descriptor shared evolved before after af ⟨.next after, []⟩
  fetch : CallStack.FetchWithin descriptor.frame before

theorem Next.current {descriptor shared evolved before after af}
    (next : Next descriptor shared evolved before after af)
    (current : Current descriptor shared before) : Current descriptor evolved after :=
  next.step.current current

theorem current_code {profile descriptor shared state} (current : Current descriptor shared state)
    (same : descriptor.frame.call.bytes = bytes profile) :
    CodeAt state.memory descriptor.frame.call.code (bytes profile) := by
  rw [current.coupled, ← same]
  exact current.contract.stack.pureCall.code

theorem fetch {profile descriptor shared state offset instruction}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (member : (offset, instruction) ∈ sites profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset) :
    CallStack.FetchWithin descriptor.frame state :=
  fetchWithin (current_code current same) same member pc

theorem decoded {profile descriptor shared state offset instruction}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (member : (offset, instruction) ∈ sites profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset) :
    CallReturn.decodeAt state = .ok instruction :=
  decode (current_code current same) member pc

def moved (state : State) : State :=
  { state.writeRegister .rax (state.registers .rsi) with rip := state.rip + 3 }

def added (state : State) : State :=
  { state.writeRegister .rax (state.registers .rax + state.registers .rdx) with
    rip := state.rip + 3
    flags := Sequential.addFlags64 state.flags (state.registers .rax) (state.registers .rdx) }

def summed (state : State) : State :=
  { state.writeRegister .rax (state.registers .rsi + state.registers .rdx) with rip := state.rip + 4 }

def tested (state : State) (af : Bool) : State :=
  { state with
    rip := state.rip + 3
    flags := Sequential.logicalFlags64 state.flags (state.registers .rdx &&& state.registers .rdx) af }

def jumped (state : State) (pc : Word) : State := { state with rip := pc }

def predecessor (profile : Profile) (state : State) : State :=
  CallReturn.leaState state (scratch profile) (.plain .rax) 0xff

def stored (state : State) (world : Shared) : State := WordResources64.storeAfterLength state world 3

def finished (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

/-- Caller-visible registers and nonarithmetic flags. No private RAM is
assumed immutable; memory framing comes from the mixed execution itself. -/
structure Frame (initial final : State) : Prop where
  preserved : ∀ register, register ∉ CallStack.clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.trans {first middle final : State} (left : Frame first middle) (right : Frame middle final) :
    Frame first final := ⟨fun r outside => (right.preserved r outside).trans (left.preserved r outside),
      right.flags.trans left.flags⟩

theorem frame_write (state : State) (destination : Register) (value pc flags : Word) (memory : Memory)
    (allowed : destination ∈ CallStack.clobbers)
    (preserved : flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask) :
    Frame state { state.writeRegister destination value with rip := pc, flags := flags, memory := memory } := by
  refine ⟨?_, preserved⟩
  intro register outside
  have different : register ≠ destination := fun same => outside (same ▸ allowed)
  simp [State.writeRegister, different]

theorem frame_moved (state : State) : Frame state (moved state) :=
  frame_write state .rax _ _ _ _ (by decide) rfl

theorem frame_added (state : State) : Frame state (added state) :=
  frame_write state .rax _ _ _ _ (by decide) (Sequential.addFlags64_preserves ..)

theorem frame_summed (state : State) : Frame state (summed state) :=
  frame_write state .rax _ _ _ _ (by decide) rfl

theorem frame_tested (state : State) (af : Bool) : Frame state (tested state af) :=
  ⟨fun _ _ => rfl, Sequential.logicalFlags64_preserves ..⟩

theorem frame_jumped (state : State) (pc : Word) : Frame state (jumped state pc) := ⟨fun _ _ => rfl, rfl⟩

theorem frame_predecessor (profile : Profile) (state : State) : Frame state (predecessor profile state) :=
  frame_write state (scratch profile) _ _ _ _ (by cases profile <;> decide) rfl

theorem frame_stored (state : State) (world : Shared) : Frame state (stored state world) :=
  ⟨fun _ _ => rfl, rfl⟩

theorem frame_finished (state : State) (target : Word) : Frame state (finished state target) :=
  frame_write state .rsp _ _ _ _ (by decide) rfl

theorem pure_next {profile descriptor shared state after offset instruction af}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (member : (offset, instruction) ∈ sites profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 offset)
    (actual : CallReturn.execute state instruction af = .ok ⟨.next after, []⟩)
    (noWrite : instruction.writeEffect state = none) (memory : after.memory = state.memory) :
    Next descriptor shared shared state after af :=
  ⟨OS.CallMemory64.CPU.unchanged_step (decoded current same member pc) actual rfl
      noWrite memory (by simp), fetch current same member pc⟩

theorem move_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes .clang)
    (pc : state.rip = descriptor.frame.call.code) (af : Bool) :
    Next descriptor shared shared state (moved state) af :=
  pure_next current same (by decide : (0, .sequential (.movReg64 .rax .rsi)) ∈ sites .clang)
    (by simpa using pc) rfl rfl rfl

theorem add_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes .clang)
    (pc : state.rip = descriptor.frame.call.code + 3) (af : Bool) :
    Next descriptor shared shared state (added state) af :=
  pure_next current same (by decide : (3, .sequential (.addReg64 .rax .rdx)) ∈ sites .clang)
    pc rfl rfl rfl

theorem sum_next {descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes .gcc)
    (pc : state.rip = descriptor.frame.call.code) (af : Bool) :
    Next descriptor shared shared state (summed state) af := by
  refine pure_next (after := summed state) current same
    (by decide : (0, .sequential (.lea64 .rax (.indexed .rsi .rdx 0))) ∈ sites .gcc)
    (by simpa using pc) ?_ rfl rfl
  rw [CallReturn.execute_sequential, Sequential.execute_lea64]
  change (Except.ok ⟨.next { state.writeRegister .rax
    (state.registers .rsi + (state.registers .rdx <<< (0 : Nat))) with rip := state.rip + 4 }, []⟩ :
      Except Error CallReturn.Observation) = _
  simp only [BitVec.shiftLeft_zero]
  rfl

theorem test_next {profile descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (testOffset profile)) (af : Bool) :
    Next descriptor shared shared state (tested state af) af :=
  pure_next current same (by cases profile <;> decide :
    (testOffset profile, .sequential (.test64 .rdx .rdx)) ∈ sites profile) pc rfl rfl rfl

theorem guard_next {profile descriptor shared state} {zero : Bool}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (guardOffset profile))
    (flag : state.flags.getLsbD 6 = zero) (af : Bool) :
    Next descriptor shared shared state
      (jumped state (descriptor.frame.call.code + BitVec.ofNat 64
        (if zero then retOffset profile else predOffset profile))) af := by
  have displacement : BitVec.ofNat 64 (guardOffset profile) + 2 + (7 : Byte).signExtend 64 =
      BitVec.ofNat 64 (retOffset profile) := by cases profile <;> decide
  have fallthrough : BitVec.ofNat 64 (guardOffset profile) + 2 =
      BitVec.ofNat 64 (predOffset profile) := by cases profile <;> decide
  have canon : canonical (descriptor.frame.call.code + BitVec.ofNat 64 (retOffset profile)) = true :=
    Sequential.code_canonical_offset (current_code current same) (retOffset profile)
      (by cases profile <;> decide)
  refine pure_next (after := jumped state (descriptor.frame.call.code + BitVec.ofNat 64
    (if zero then retOffset profile else predOffset profile))) current same
    (by cases profile <;> decide :
      (guardOffset profile, .sequential (.je 7)) ∈ sites profile) pc ?_ rfl rfl
  rw [CallReturn.execute_sequential, Sequential.execute_je, flag]
  cases zero with
  | false =>
    simp [executeShortBranch, jumped, pc, BitVec.add_assoc]
    exact fallthrough
  | true =>
    simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement, jumped]
    rw [canon]
    rfl

theorem predecessor_next {profile descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (predOffset profile)) (af : Bool) :
    Next descriptor shared shared state (predecessor profile state) af :=
  pure_next current same (by cases profile <;> decide :
    (predOffset profile, .leaDisp8 (scratch profile) (.plain .rax) 0xff) ∈ sites profile) pc rfl rfl rfl

theorem store_next {profile descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (storeOffset profile))
    (pointer : state.registers .rdi = descriptor.target) (af : Bool) :
    ∃ evolved, Next descriptor shared evolved state (stored state evolved) af ∧
      Borrowing.StoreEffect64 shared evolved descriptor.target (state.registers (scratch profile)) ∧
      Borrowing.loadOwnedWord64 evolved descriptor.owner descriptor.ticket descriptor.target =
        .ok (state.registers (scratch profile)) := by
  have member : (storeOffset profile, .sequential (.storeMem64 (.base .rdi) (scratch profile))) ∈
      sites profile := by cases profile <;> decide
  have sequential : Sequential.decodeAt state =
      .ok (.storeMem64 (.base .rdi) (scratch profile)) :=
    Sequential.decodeAt_transport
      (Sequential.code_fetch_transport (current_code current same) (decode_bound profile)
        _ (inside member) state rfl pc) (by cases profile <;> rfl)
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) (scratch profile)) state =
      some (descriptor.target, state.registers (scratch profile)) := by
    simp [Sequential.Instruction.storeIntent64, Sequential.Address.eval, pointer]
  obtain ⟨evolved, _, _, step, _, effect, owned⟩ :=
    OS.CallMemory64.CPU.data_store_step current sequential intent af
  exact ⟨evolved, ⟨step, fetch current same member pc⟩, effect, owned⟩

theorem root_ret {profile descriptor shared state}
    (current : Current descriptor shared state) (same : descriptor.frame.call.bytes = bytes profile)
    (pc : state.rip = descriptor.frame.call.code + BitVec.ofNat 64 (retOffset profile))
    (original : state.registers .rsp = descriptor.frame.top) (choices : CallReturn.Choices) :
    CoveredExecution descriptor choices shared state shared
      ⟨finished state descriptor.frame.call.returnAddress, 1, [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  .ret (OS.CallMemory64.CPU.lift_stack (StackFrame.CPU.original_ret_step current.stack original (choices 0)
    (decoded current same (by cases profile <;> decide :
      (retOffset profile, .sequential (.legacy .ret)) ∈ sites profile) pc)))
    (fetch current same (by cases profile <;> decide :
      (retOffset profile, .sequential (.legacy .ret)) ∈ sites profile) pc)

/-- Subtracting one after modular addition equals the independent natural
predecessor before reduction, including sums that wrap to zero. -/
theorem target_predecessor (value count : Word) (nonzero : count ≠ 0) :
    (value + count) + (0xff : Byte).signExtend 64 = targetWord value count := by
  have positive : 0 < count.toNat := by
    have notzero : count.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
    omega
  have natural : value.toNat + count.toNat - 1 + 1 = value.toNat + count.toNat := by omega
  have next : targetWord value count + 1 = value + count := by
    change BitVec.ofNat 64 (value.toNat + count.toNat - 1) + BitVec.ofNat 64 1 = value + count
    rw [BitVec.ofNat_add_ofNat, natural, BitVec.ofNat_add]
    simp
  rw [show (0xff : Byte).signExtend 64 = -(1 : Word) by decide, BitVec.add_neg_eq_sub]
  exact BitVec.sub_eq_iff_eq_add.mpr next.symm

end EDSL.CallMemoryLoop64.ClosedForm
