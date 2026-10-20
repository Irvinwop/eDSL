/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Contract
import EDSL.X86.Sequential.CFGVerification

namespace EDSL.Pair32
open X86

inductive Loop where
  | first
  | second
  deriving DecidableEq

def Loop.counter : Loop → Register
  | .first => .rsi
  | .second => .rcx

def Loop.pointer : Loop → Register
  | .first => .rdi
  | .second => .rdx

def Loop.headerOffset : Loop → Nat
  | .first => 2
  | .second => 18

def Loop.bodyOffset : Loop → Nat
  | .first => 7
  | .second => 23

def Loop.backOffset : Loop → Nat
  | .first => 16
  | .second => 32

def Loop.exitOffset : Loop → Nat
  | .first => 18
  | .second => 34

@[simp] theorem Loop.counter_ne_rax (loop : Loop) : loop.counter ≠ .rax := by cases loop <;> decide
@[simp] theorem Loop.pointer_ne_rax (loop : Loop) : loop.pointer ≠ .rax := by cases loop <;> decide
@[simp] theorem Loop.counter_ne_rsp (loop : Loop) : loop.counter ≠ .rsp := by cases loop <;> decide
@[simp] theorem Loop.pointer_ne_rsp (loop : Loop) : loop.pointer ≠ .rsp := by cases loop <;> decide
@[simp] theorem Loop.counter_ne_pointer (loop : Loop) : loop.counter ≠ loop.pointer := by cases loop <;> decide
@[simp] theorem Loop.pointer_ne_counter (loop : Loop) : loop.pointer ≠ loop.counter := by cases loop <;> decide

def bytes : List Byte := [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0b,
  0x03, 0x07, 0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x04, 0xeb, 0xf0,
  0x48, 0x85, 0xc9, 0x74, 0x0b, 0x03, 0x02, 0x48, 0xff, 0xc9,
  0x48, 0x83, 0xc2, 0x04, 0xeb, 0xf0, 0xc3]

def graph : Sequential.CFG.Graph := ⟨[
  ⟨0, .xorSelf32 .rax, true, 14⟩,
  ⟨2, .test64 .rsi .rsi, true, 13⟩,
  ⟨5, .je 11, false, 12⟩,
  ⟨7, .addMem32 .rax (.base .rdi), false, 11⟩,
  ⟨9, .dec64 .rsi, false, 10⟩,
  ⟨12, .addImm64 .rdi 4, false, 9⟩,
  ⟨16, .jmp 240, false, 8⟩,
  ⟨18, .test64 .rcx .rcx, true, 7⟩,
  ⟨21, .je 11, false, 6⟩,
  ⟨23, .addMem32 .rax (.base .rdx), false, 5⟩,
  ⟨25, .dec64 .rcx, false, 4⟩,
  ⟨28, .addImm64 .rdx 4, false, 3⟩,
  ⟨32, .jmp 240, false, 2⟩,
  ⟨34, .legacy .ret, false, 1⟩], 14⟩

theorem valid : Sequential.CFG.Valid bytes graph := Sequential.CFG.check_sound (by decide)

abbrev Index := graph.Index

instance : NeZero graph.nodes.length := ⟨by decide⟩

/-- State framing before RET; the final postcondition advances RSP separately. -/
structure Frame (initial final : State) : Prop where
  memory : final.memory = initial.memory
  stack : final.registers .rsp = initial.registers .rsp
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.refl (state : State) : Frame state state := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem Frame.trans {first middle final : State} (left : Frame first middle)
    (right : Frame middle final) : Frame first final :=
  ⟨right.memory.trans left.memory, right.stack.trans left.stack,
    fun register outside => (right.preserved register outside).trans (left.preserved register outside),
    right.flags.trans left.flags⟩

def edit (state : State) (destination : Register) (value pc flags : Word) : State :=
  { state.writeRegister destination value with rip := pc, flags := flags }

theorem frame_edit (state : State) (destination : Register) (value pc flags : Word)
    (notStack : destination ≠ .rsp) (allowed : destination ∈ clobbers)
    (flagFrame : flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask) :
    Frame state (edit state destination value pc flags) := by
  refine ⟨rfl, ?_, ?_, flagFrame⟩
  · simp [edit, State.writeRegister, Ne.symm notStack]
  · intro register outside
    have different : register ≠ destination := by
      intro same
      subst register
      exact outside allowed
    simp [edit, State.writeRegister, different]

def atPC (state : State) (pc : Word) : State := { state with rip := pc }
def clear (state : State) (af : Bool) : State :=
  edit state .rax 0 (state.rip + 2) (Sequential.logicalFlags32 state.flags 0 af)
def test (loop : Loop) (state : State) (af : Bool) : State :=
  { state with
    rip := state.rip + 3
    flags := Sequential.logicalFlags64 state.flags (state.registers loop.counter) af }
def body (loop : Loop) (base : Word) (state : State) (af : Bool) : State :=
  atPC (test loop state af) (base + BitVec.ofNat 64 loop.bodyOffset)
def load (state : State) (value : BitVec 32) : State :=
  edit state .rax (((state.registers .rax).setWidth 32 + value).setWidth 64) (state.rip + 2)
    (addFlags32 state.flags ((state.registers .rax).setWidth 32) value)
def decrement (loop : Loop) (state : State) : State :=
  edit state loop.counter (state.registers loop.counter - 1) (state.rip + 3)
    (Sequential.decFlags64 state.flags (state.registers loop.counter))
def advance (loop : Loop) (state : State) : State :=
  edit state loop.pointer (state.registers loop.pointer + 4) (state.rip + 4)
    (Sequential.addFlags64 state.flags (state.registers loop.pointer) 4)

def cycleState (loop : Loop) (base : Word) (state : State) (af : Bool) (value : BitVec 32) : State :=
  atPC (advance loop (decrement loop (load (body loop base state af) value)))
    (base + BitVec.ofNat 64 loop.headerOffset)

def exitState (loop : Loop) (base : Word) (state : State) (af : Bool) : State :=
  atPC (test loop state af) (base + BitVec.ofNat 64 loop.exitOffset)

def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

theorem frame_atPC (state : State) (pc : Word) : Frame state (atPC state pc) :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl⟩
theorem frame_clear (state : State) (af : Bool) : Frame state (clear state af) :=
  frame_edit state .rax 0 _ _ (by decide) (by decide) (Sequential.logicalFlags32_preserves ..)
theorem frame_test (loop : Loop) (state : State) (af : Bool) : Frame state (test loop state af) :=
  ⟨rfl, rfl, fun _ _ => rfl, Sequential.logicalFlags64_preserves ..⟩
theorem frame_body (loop : Loop) (base : Word) (state : State) (af : Bool) :
    Frame state (body loop base state af) :=
  (frame_test loop state af).trans (frame_atPC _ _)
theorem frame_load (state : State) (value : BitVec 32) : Frame state (load state value) :=
  frame_edit state .rax _ _ _ (by decide) (by decide) (addFlags32_preserves ..)
theorem frame_decrement (loop : Loop) (state : State) : Frame state (decrement loop state) :=
  frame_edit state loop.counter _ _ _ (Loop.counter_ne_rsp loop)
    (by cases loop <;> decide) (Sequential.decFlags64_preserves ..)
theorem frame_advance (loop : Loop) (state : State) : Frame state (advance loop state) :=
  frame_edit state loop.pointer _ _ _ (Loop.pointer_ne_rsp loop)
    (by cases loop <;> decide) (Sequential.addFlags64_preserves ..)

theorem frame_cycle (loop : Loop) (base : Word) (state : State) (af : Bool) (value : BitVec 32) :
    Frame state (cycleState loop base state af value) :=
  ((((frame_body loop base state af).trans (frame_load _ value)).trans
    (frame_decrement loop _)).trans (frame_advance loop _)).trans (frame_atPC _ _)

theorem frame_exit (loop : Loop) (base : Word) (state : State) (af : Bool) :
    Frame state (exitState loop base state af) :=
  (frame_test loop state af).trans (frame_atPC _ _)

/-- A mathematical suffix invariant for the current phase. Current RAM and
pointer provenance are explicit; this data contains no future execution. -/
structure Header (initial : State) (valuesA valuesB : List (BitVec 32)) (loop : Loop)
    (state : State) where
  remaining : List (BitVec 32)
  count : Nat
  accumulator : BitVec 32
  consumed : Nat
  length : remaining.length = count
  countBound : count < 2^64
  counter : state.registers loop.counter = BitVec.ofNat 64 count
  pointer : state.registers loop.pointer = initial.registers loop.pointer + BitVec.ofNat 64 (4 * consumed)
  value : state.registers .rax = accumulator.setWidth 64
  array : ArrayAt state.memory (state.registers loop.pointer) remaining
  split : consumed + count = if loop = .first then valuesA.length else valuesB.length
  correct : accumulator + sum32 remaining + (if loop = .first then sum32 valuesB else 0) =
    pairSum valuesA valuesB
  frame : Frame initial state
  pc : state.rip = initial.rip + BitVec.ofNat 64 loop.headerOffset
  future : loop = .first → state.registers .rdx = initial.registers .rdx ∧
    state.registers .rcx = BitVec.ofNat 64 valuesB.length

structure Element {initial : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop} {state : State}
    (header : Header initial valuesA valuesB loop state) where
  first : BitVec 32
  tail : List (BitVec 32)
  rest : Nat
  count : header.count = rest + 1
  values : header.remaining = first :: tail

theorem Header.rank {initial : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop} {state : State}
    (header : Header initial valuesA valuesB loop state) :
    (state.registers loop.counter).toNat = header.count := by
  rw [header.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt header.countBound]

theorem Header.element {initial : State} {valuesA valuesB : List (BitVec 32)} {loop : Loop} {state : State}
    (header : Header initial valuesA valuesB loop state) (positive : 0 < header.count) :
    Nonempty (Element header) := by
  have length := header.length
  cases remaining : header.remaining with
  | nil => simp only [remaining, List.length_nil] at length; omega
  | cons first tail => exact ⟨⟨first, tail, header.count - 1, by omega, remaining⟩⟩

end EDSL.Pair32
