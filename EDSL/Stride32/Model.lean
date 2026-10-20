/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Stride32.Contract
import EDSL.X86.Sequential.CFGVerification

namespace EDSL.Stride32
open X86

def bytes : List Byte := [0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0b,
  0x03, 0x07, 0x48, 0xff, 0xce, 0x48, 0x83, 0xc7, 0x08, 0xeb, 0xf0, 0xc3]

def graph : Sequential.CFG.Graph := ⟨[
  ⟨0, .xorSelf32 .rax, true, 8⟩,
  ⟨2, .test64 .rsi .rsi, true, 7⟩,
  ⟨5, .je 11, false, 6⟩,
  ⟨7, .addMem32 .rax (.base .rdi), false, 5⟩,
  ⟨9, .dec64 .rsi, false, 4⟩,
  ⟨12, .addImm64 .rdi 8, false, 3⟩,
  ⟨16, .jmp 240, false, 2⟩,
  ⟨18, .legacy .ret, false, 1⟩], 8⟩

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
def test (state : State) (af : Bool) : State :=
  { state with
    rip := state.rip + 3
    flags := Sequential.logicalFlags64 state.flags (state.registers .rsi) af }
def body (base : Word) (state : State) (af : Bool) : State := atPC (test state af) (base + 7)
def load (state : State) (value : BitVec 32) : State :=
  edit state .rax (((state.registers .rax).setWidth 32 + value).setWidth 64) (state.rip + 2)
    (addFlags32 state.flags ((state.registers .rax).setWidth 32) value)
def decrement (state : State) : State :=
  edit state .rsi (state.registers .rsi - 1) (state.rip + 3)
    (Sequential.decFlags64 state.flags (state.registers .rsi))
def advance (state : State) : State :=
  edit state .rdi (state.registers .rdi + 8) (state.rip + 4)
    (Sequential.addFlags64 state.flags (state.registers .rdi) 8)

theorem frame_atPC (state : State) (pc : Word) : Frame state (atPC state pc) :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl⟩
theorem frame_clear (state : State) (af : Bool) : Frame state (clear state af) :=
  frame_edit state .rax 0 _ _ (by decide) (by decide) (Sequential.logicalFlags32_preserves ..)
theorem frame_test (state : State) (af : Bool) : Frame state (test state af) :=
  ⟨rfl, rfl, fun _ _ => rfl, Sequential.logicalFlags64_preserves ..⟩
theorem frame_body (base : Word) (state : State) (af : Bool) : Frame state (body base state af) :=
  (frame_test state af).trans (frame_atPC _ _)
theorem frame_load (state : State) (value : BitVec 32) : Frame state (load state value) :=
  frame_edit state .rax _ _ _ (by decide) (by decide) (addFlags32_preserves ..)
theorem frame_decrement (state : State) : Frame state (decrement state) :=
  frame_edit state .rsi _ _ _ (by decide) (by decide) (Sequential.decFlags64_preserves ..)
theorem frame_advance (state : State) : Frame state (advance state) :=
  frame_edit state .rdi _ _ _ (by decide) (by decide) (Sequential.addFlags64_preserves ..)

/-- A mathematical suffix invariant with explicit current RAM, full-width
counter and pointer provenance. No future execution is part of this data. -/
structure Header (initial : State) (values : List (BitVec 32)) (total : Nat)
    (state : State) where
  remaining : List (BitVec 32)
  count : Nat
  accumulator : BitVec 32
  consumed : Nat
  length : remaining.length = 2 * count
  countBound : count < 2^64
  counter : state.registers .rsi = BitVec.ofNat 64 count
  pointer : state.registers .rdi = initial.registers .rdi + BitVec.ofNat 64 (8 * consumed)
  value : state.registers .rax = accumulator.setWidth 64
  array : ArrayAt state.memory (state.registers .rdi) remaining
  split : consumed + count = total
  correct : accumulator + evenSum remaining count = evenSum values total
  frame : Frame initial state
  pc : state.rip = initial.rip + 2

structure Pair {initial : State} {values : List (BitVec 32)} {total : Nat} {state : State}
    (header : Header initial values total state) where
  first : BitVec 32
  second : BitVec 32
  tail : List (BitVec 32)
  rest : Nat
  count : header.count = rest + 1
  values : header.remaining = first :: second :: tail

theorem Header.rank {initial : State} {values : List (BitVec 32)} {total : Nat} {state : State}
    (header : Header initial values total state) : (state.registers .rsi).toNat = header.count := by
  rw [header.counter, BitVec.toNat_ofNat, Nat.mod_eq_of_lt header.countBound]

theorem Header.pair {initial : State} {values : List (BitVec 32)} {total : Nat} {state : State}
    (header : Header initial values total state) (positive : 0 < header.count) : Nonempty (Pair header) := by
  have length := header.length
  cases remaining : header.remaining with
  | nil => simp only [remaining, List.length_nil] at length; omega
  | cons first rest =>
    cases rest with
    | nil => simp only [remaining, List.length_cons, List.length_nil] at length; omega
    | cons second tail => exact ⟨⟨first, second, tail, header.count - 1, by omega, remaining⟩⟩

end EDSL.Stride32
