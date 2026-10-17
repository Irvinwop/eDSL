/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import tests.fixtures.CallMemoryLoop64Programs
import EDSL.CallMemoryLoop64.Admission
import EDSL.OS.CallMemory64.Private
import EDSL.CallStack.Geometry

set_option warningAsError true

namespace EDSL.CallMemoryLoop64.Clang
open X86 OS

abbrev text := Compiler.bytes Compiler.Profile.clangSeparate

def mov (s : State) (dst src : Register) : State :=
  { s.writeRegister dst (s.registers src) with rip := s.rip + 3 }

def test (s : State) (af : Bool) : State :=
  { s with
    rip := s.rip + 3
    flags := Sequential.logicalFlags64 s.flags (s.registers .rdx &&& s.registers .rdx) af }

def jump (s : State) (pc : Word) : State := { s with rip := pc }

def push (s : State) (src : Register) (rex : Bool) : State :=
  CallReturn.pushState s rex
    (writeQWordUnchecked s.memory (CallReturn.stackDestination s) (s.registers src))

def call (s : State) : State :=
  CallReturn.callState s 16
    (writeQWordUnchecked s.memory (CallReturn.stackDestination s) (CallReturn.returnAddress s))

def store (s : State) (world : Borrowing.State) : State :=
  WordResources64.storeAfterLength s world 3

def load (s : State) (value : Word) : State :=
  { s.writeRegister .rax value with rip := s.rip + 3 }

def ret (s : State) (target : Word) : State :=
  { s.writeRegister .rsp (s.registers .rsp + 8) with rip := target }

def inc (s : State) : State :=
  { s.writeRegister .rax (s.registers .rax + 1) with
    rip := s.rip + 3
    flags := Sequential.incFlags64 s.flags (s.registers .rax) }

def dec (s : State) : State :=
  { s.writeRegister .rbx (s.registers .rbx - 1) with
    rip := s.rip + 3
    flags := Sequential.decFlags64 s.flags (s.registers .rbx) }

def addsp (s : State) : State :=
  { s.writeRegister .rsp (s.registers .rsp + 8) with
    rip := s.rip + 4
    flags := Sequential.addFlags64 s.flags (s.registers .rsp) 8 }

def pop (s : State) (dst : Register) (rex : Bool) (value : Word) : State :=
  CallReturn.popState s dst rex value

def changed : List Register := [.rax, .rsp, .rdi, .rsi, .rbx, .r14]

/-- Registers outside the selected instructions' destinations and all
nonarithmetic flags are stable. RBX/R14 are restored separately from actual RAM. -/
structure Frame (initial final : State) : Prop where
  registers : ∀ r, r ∉ changed → final.registers r = initial.registers r
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.refl (s : State) : Frame s s := ⟨fun _ _ => rfl, rfl⟩
theorem Frame.trans {a b c : State} (first : Frame a b) (last : Frame b c) : Frame a c :=
  ⟨fun r h => (last.registers r h).trans (first.registers r h), last.flags.trans first.flags⟩

theorem frame_write (s : State) (dst : Register) (value pc flags : Word) (memory : Memory)
    (allowed : dst ∈ changed)
    (preserved : flags &&& ~~~arithmeticFlagMask = s.flags &&& ~~~arithmeticFlagMask) :
    Frame s { s.writeRegister dst value with rip := pc, flags := flags, memory := memory } := by
  refine ⟨?_, preserved⟩
  intro r outside
  have different : r ≠ dst := fun same => outside (same ▸ allowed)
  simp [State.writeRegister, different]

theorem frame_mov (s : State) (dst src : Register) (allowed : dst ∈ changed) :
    Frame s (mov s dst src) := frame_write s dst _ _ _ _ allowed rfl
theorem frame_test (s : State) (af : Bool) : Frame s (test s af) :=
  ⟨fun _ _ => rfl, Sequential.logicalFlags64_preserves ..⟩
theorem frame_jump (s : State) (pc : Word) : Frame s (jump s pc) := ⟨fun _ _ => rfl, rfl⟩
theorem frame_push (s : State) (src : Register) (rex : Bool) : Frame s (push s src rex) :=
  frame_write s .rsp _ _ _ _ (by decide) rfl
theorem frame_call (s : State) : Frame s (call s) :=
  frame_write s .rsp _ _ _ _ (by decide) rfl
theorem frame_store (s : State) (world : Borrowing.State) : Frame s (store s world) :=
  ⟨fun _ _ => rfl, rfl⟩
theorem frame_load (s : State) (value : Word) : Frame s (load s value) :=
  frame_write s .rax _ _ _ _ (by decide) rfl
theorem frame_ret (s : State) (target : Word) : Frame s (ret s target) :=
  frame_write s .rsp _ _ _ _ (by decide) rfl
theorem frame_inc (s : State) : Frame s (inc s) :=
  frame_write s .rax _ _ _ _ (by decide) (Sequential.incFlags64_preserves ..)
theorem frame_dec (s : State) : Frame s (dec s) :=
  frame_write s .rbx _ _ _ _ (by decide) (Sequential.decFlags64_preserves ..)
theorem frame_addsp (s : State) : Frame s (addsp s) :=
  frame_write s .rsp _ _ _ _ (by decide) (Sequential.addFlags64_preserves ..)
theorem frame_pop (s : State) (dst : Register) (rex : Bool) (value : Word)
    (allowed : dst ∈ changed) : Frame s (pop s dst rex value) := by
  exact (frame_write s .rsp _ s.rip s.flags s.memory (by decide) rfl).trans
    (frame_write _ dst _ _ _ _ allowed rfl)

theorem current_code {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text) :
    CodeAt s.memory d.frame.call.code text := by
  rw [current.coupled, ← same]
  exact current.contract.stack.pureCall.code

theorem fetch {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {off : Nat} {op : CallReturn.Instruction}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (member : (off, op) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off) : CallStack.FetchWithin d.frame s :=
  Compiler.fetchWithin (current_code current same) same member pc

theorem decode {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {off : Nat} {op : CallReturn.Instruction}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (member : (off, op) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off) : CallReturn.decodeAt s = .ok op :=
  Compiler.decode (current_code current same) member pc

theorem sequential_decode {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {off : Nat} {op : Sequential.Instruction}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (member : (off, .sequential op) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off)
    (checked : Sequential.decodeAt (Sequential.codeState text off) = .ok op) :
    Sequential.decodeAt s = .ok op :=
  Sequential.decodeAt_transport
    (Sequential.code_fetch_transport (current_code current same)
      (Compiler.decode_bound .clangSeparate) off (Compiler.inside member) s rfl pc) checked

/-- Only checked whole-text sites can instantiate this ordinary, read-free step. -/
theorem plain_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s t : State}
    {off : Nat} {op : CallReturn.Instruction} {af : Bool}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (member : (off, op) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off)
    (actual : CallReturn.execute s op af = .ok ⟨.next t, []⟩)
    (noWrite : op.writeEffect s = none) (memory : t.memory = s.memory) :
    OS.CallMemory64.CPU.Step d w w s t af ⟨.next t, []⟩ :=
  OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode current same member pc, actual, rfl, rfl,
      .unchanged noWrite memory, by simp⟩

theorem push_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {off : Nat} {src : Register} {rex : Bool}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (member : (off, .push64 src rex) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off)
    (slot : StackFrame.Slot d.frame (CallReturn.stackDestination s)) (af : Bool) :
    ∃ evolved, OS.CallMemory64.CPU.Step d w evolved s (push s src rex) af
        ⟨.next (push s src rex), []⟩ ∧
      Borrowing.StoreEffect64 w evolved (CallReturn.stackDestination s) (s.registers src) ∧
      readWord (push s src rex).memory (CallReturn.stackDestination s) = .ok (s.registers src) := by
  have writable : canStoreQWord s.memory (CallReturn.stackDestination s) = true := by
    rw [current.coupled]
    exact (current.contract.stack.ready _ slot).writable
  have stored := (qword_store_sound s.memory _ (s.registers src) writable).1
  have actual := CallReturn.execute_push s src rex af _ stored
  obtain ⟨evolved, success, _, _, effect⟩ := StackFrame.CPU.push_current current.stack slot actual
  have step : OS.CallMemory64.CPU.Step d w evolved s (push s src rex) af
      ⟨.next (push s src rex), []⟩ := OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode current same member pc, actual, rfl, rfl, .push slot success, by simp⟩
  refine ⟨evolved, step, effect, ?_⟩
  rw [(step.current current).coupled]
  exact readWord_of_loadQWord _ _ _ effect.readback

theorem call_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 24)
    (slot : StackFrame.Slot d.frame (CallReturn.stackDestination s)) (af : Bool) :
    ∃ evolved, OS.CallMemory64.CPU.Step d w evolved s (call s) af ⟨.next (call s), []⟩ ∧
      Borrowing.StoreEffect64 w evolved (CallReturn.stackDestination s) (CallReturn.returnAddress s) ∧
      readWord (call s).memory (CallReturn.stackDestination s) = .ok (CallReturn.returnAddress s) := by
  have target : CallReturn.callTarget s 16 = d.frame.call.code + 45 := by
    simp [CallReturn.callTarget, CallReturn.returnAddress, pc, BitVec.add_assoc]
  have canonicalTarget : canonical (CallReturn.callTarget s 16) = true := by
    rw [target]
    exact Sequential.code_canonical_offset (current_code current same) 45 (by decide)
  have writable : canStoreQWord s.memory (CallReturn.stackDestination s) = true := by
    rw [current.coupled]
    exact (current.contract.stack.ready _ slot).writable
  have actual := CallReturn.execute_call s 16 af _ canonicalTarget
    (qword_store_sound s.memory _ (CallReturn.returnAddress s) writable).1
  obtain ⟨evolved, success, _, _, effect⟩ := StackFrame.CPU.call_current current.stack slot actual
  have step : OS.CallMemory64.CPU.Step d w evolved s (call s) af ⟨.next (call s), []⟩ :=
    OS.CallMemory64.CPU.lift_stack
      ⟨_, _, decode current same (by decide : (24, .callRelative32 16) ∈ Compiler.sites .clangSeparate)
        pc, actual, rfl, rfl, .call slot success, by simp⟩
  refine ⟨evolved, step, effect, ?_⟩
  rw [(step.current current).coupled]
  exact readWord_of_loadQWord _ _ _ effect.readback

theorem store_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State} {v : Word}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 45) (pointer : s.registers .rdi = d.target)
    (argument : s.registers .rsi = v) (af : Bool) :
    ∃ evolved, OS.CallMemory64.CPU.Step d w evolved s (store s evolved) af
        ⟨.next (store s evolved), []⟩ ∧
      Borrowing.StoreEffect64 w evolved d.target v ∧
      Borrowing.loadOwnedWord64 evolved d.owner d.ticket d.target = .ok v := by
  have decoded := sequential_decode current same
    (by decide : (45, .sequential (.storeMem64 (.base .rdi) .rsi)) ∈ Compiler.sites .clangSeparate)
    pc rfl
  have intent : Sequential.Instruction.storeIntent64 (.storeMem64 (.base .rdi) .rsi) s =
      some (d.target, v) := by
    simp [Sequential.Instruction.storeIntent64, Sequential.Address.eval, pointer, argument]
  obtain ⟨evolved, _, _, step, _, effect, owned⟩ :=
    OS.CallMemory64.CPU.data_store_step current decoded intent af
  exact ⟨evolved, step, effect, owned⟩

theorem load_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State} {v : Word}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 48) (pointer : s.registers .rdi = d.target)
    (owned : Borrowing.loadOwnedWord64 w d.owner d.ticket d.target = .ok v) (af : Bool) :
    OS.CallMemory64.CPU.Step d w w s (load s v) af
      ⟨.next (load s v), [⟨.data, d.target, 8⟩]⟩ := by
  have decoded := sequential_decode current same
    (by decide : (48, .sequential (.loadMem64 .rax (.base .rdi))) ∈ Compiler.sites .clangSeparate) pc rfl
  obtain ⟨observed, actual, _, step, _, _⟩ :=
    OS.CallMemory64.CPU.data_load_step current decoded pointer af
  have sameValue : observed = v := Except.ok.inj (actual.symm.trans owned)
  subst observed
  exact step

theorem inner_ret_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 51)
    (slot : StackFrame.Slot d.frame (s.registers .rsp))
    (readback : readWord s.memory (s.registers .rsp) = .ok (d.frame.call.code + 29)) (af : Bool) :
    OS.CallMemory64.CPU.Step d w w s (ret s (d.frame.call.code + 29)) af
      ⟨.next (ret s (d.frame.call.code + 29)), [⟨.stack, s.registers .rsp, 8⟩]⟩ := by
  have actual : CallReturn.execute s (.sequential (.legacy .ret)) af =
      .ok ⟨.returned (ret s (d.frame.call.code + 29)), [⟨.stack, s.registers .rsp, 8⟩]⟩ :=
    CallReturn.execute_ret_success_iff.mpr ⟨_, readback,
      Sequential.code_canonical_offset (current_code current same) 29 (by decide), rfl, rfl⟩
  exact OS.CallMemory64.CPU.lift_stack (StackFrame.CPU.private_ret_step current.stack slot
    (decode current same (by decide : (51, .sequential (.legacy .ret)) ∈ Compiler.sites .clangSeparate) pc)
    actual)

theorem pop_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    {off : Nat} {dst : Register} {rex : Bool} {value : Word}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (member : (off, .pop64 dst rex) ∈ Compiler.sites .clangSeparate)
    (pc : s.rip = d.frame.call.code + BitVec.ofNat 64 off)
    (slot : StackFrame.Slot d.frame (s.registers .rsp))
    (readback : readWord s.memory (s.registers .rsp) = .ok value) (af : Bool) :
    OS.CallMemory64.CPU.Step d w w s (pop s dst rex value) af
      ⟨.next (pop s dst rex value), [⟨.stack, s.registers .rsp, 8⟩]⟩ := by
  have actual := CallReturn.execute_pop s dst rex af value readback
  have context := StackFrame.CPU.pop_current current.stack slot actual
  exact OS.CallMemory64.CPU.lift_stack
    ⟨_, _, decode current same member pc, actual, rfl, rfl, .unchanged rfl rfl, context.2.2⟩

theorem root_ret_step {d : OS.CallMemory64.Descriptor} {w : Borrowing.State} {s : State}
    (current : OS.CallMemory64.Current d w s) (same : d.frame.call.bytes = text)
    (pc : s.rip = d.frame.call.code + 44) (stack : s.registers .rsp = d.frame.top) (af : Bool) :
    OS.CallMemory64.CPU.Step d w w s (ret s d.frame.call.returnAddress) af
      ⟨.returned (ret s d.frame.call.returnAddress), [⟨.stack, s.registers .rsp, 8⟩]⟩ :=
  OS.CallMemory64.CPU.lift_stack (StackFrame.CPU.original_ret_step current.stack stack af
    (decode current same (by decide : (44, .sequential (.legacy .ret)) ∈ Compiler.sites .clangSeparate) pc))

end EDSL.CallMemoryLoop64.Clang
