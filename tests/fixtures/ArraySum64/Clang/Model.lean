/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArraySum64.Contract
import EDSL.X86.Sequential.ShortBranch

set_option warningAsError true

namespace EDSL.ArraySum64.Clang
open X86 X86.Sequential

/-- Complete final linked Clang 18 -Os text, including the empty return path. -/
def bytes : List Byte := [0x48,0x85,0xf6,0x74,0x11,0x31,0xc9,0x31,0xc0,
  0x48,0x03,0x04,0xcf,0x48,0xff,0xc1,0x48,0x39,0xce,0x75,0xf4,0xc3,0x31,0xc0,0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0,.test64 .rsi .rsi,true,11⟩,
  ⟨3,.je 17,false,10⟩,
  ⟨5,.xorSelf32 .rcx,false,9⟩,
  ⟨7,.xorSelf32 .rax,false,8⟩,
  ⟨9,.addMem64 .rax (.indexed .rdi .rcx 3),true,7⟩,
  ⟨13,.inc64 .rcx,false,6⟩,
  ⟨16,.cmp64 .rsi .rcx,false,5⟩,
  ⟨19,.legacy (.jnz 244),false,4⟩,
  ⟨21,.legacy .ret,false,3⟩,
  ⟨22,.xorSelf32 .rax,false,2⟩,
  ⟨24,.legacy .ret,false,1⟩],25⟩

theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide)

abbrev Index := graph.Index

instance : NeZero graph.nodes.length := ⟨by decide⟩

/-- Complete RAM and permission maps, original RSP, registers outside the
independent clobber set, and all nonarithmetic flags before RET. -/
structure Frame (initial final : State) : Prop where
  memory : final.memory = initial.memory
  stack : final.registers .rsp = initial.registers .rsp
  preserved : ∀ register, register ∉ clobbers → final.registers register = initial.registers register
  flags : final.flags &&& ~~~arithmeticFlagMask = initial.flags &&& ~~~arithmeticFlagMask

theorem Frame.refl (state : State) : Frame state state := ⟨rfl,rfl,fun _ _ => rfl,rfl⟩

theorem Frame.trans {first middle final : State} (left : Frame first middle)
    (right : Frame middle final) : Frame first final :=
  ⟨right.memory.trans left.memory,right.stack.trans left.stack,
    fun register outside => (right.preserved register outside).trans (left.preserved register outside),
    right.flags.trans left.flags⟩

def edit (state : State) (destination : Register) (value pc flags : Word) : State :=
  { state.writeRegister destination value with rip := pc, flags := flags }

def atPC (state : State) (pc : Word) : State := { state with rip := pc }

def test (state : State) (af : Bool) : State :=
  { state with
    rip := state.rip + 3
    flags := logicalFlags64 state.flags (state.registers .rsi) af }

def clear (state : State) (destination : Register) (af : Bool) : State :=
  edit state destination 0 (state.rip + 2) (logicalFlags32 state.flags 0 af)

/-- Fused ADD consumes the qword from the original instruction pre-state;
the destination and flags are written only after that source has been read. -/
def add (state : State) (value : Word) : State :=
  edit state .rax (state.registers .rax + value) (state.rip + 4)
    (addFlags64 state.flags (state.registers .rax) value)

def increment (state : State) : State :=
  edit state .rcx (state.registers .rcx + 1) (state.rip + 3)
    (incFlags64 state.flags (state.registers .rcx))

def compareIndex (state : State) : State :=
  { state with
    rip := state.rip + 3
    flags := cmpFlags64 state.flags (state.registers .rsi) (state.registers .rcx) }

def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

def positiveState (initial : State) (af : Bool) : State := atPC (test initial af) (initial.rip + 5)
def indexState (initial : State) (testAF indexAF : Bool) : State :=
  clear (positiveState initial testAF) .rcx indexAF

def initializedState (initial : State) (testAF indexAF resultAF : Bool) : State :=
  clear (indexState initial testAF indexAF) .rax resultAF

def emptyState (initial : State) (af : Bool) : State := atPC (test initial af) (initial.rip + 22)
def emptyReturn (initial : State) (testAF resultAF : Bool) : State :=
  clear (emptyState initial testAF) .rax resultAF

def advanced (state : State) (value : Word) : State := increment (add state value)
def testedIndex (state : State) (value : Word) : State := compareIndex (advanced state value)

def loopOffset (remaining : List Word) : Nat := if remaining.isEmpty then 21 else 9

def cycleState (base : Word) (state : State) (value : Word) (rest : List Word) : State :=
  atPC (testedIndex state value) (base + BitVec.ofNat 64 (loopOffset rest))

theorem frame_edit (state : State) (destination : Register) (value pc flags : Word)
    (notStack : destination ≠ .rsp) (allowed : destination ∈ clobbers)
    (flagFrame : flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask) :
    Frame state (edit state destination value pc flags) := by
  refine ⟨rfl,?_,?_,flagFrame⟩
  · simp [edit,State.writeRegister,Ne.symm notStack]
  · intro register outside
    have different : register ≠ destination := by
      intro same; subst register; exact outside allowed
    simp [edit,State.writeRegister,different]

theorem frame_atPC (state : State) (pc : Word) : Frame state (atPC state pc) :=
  ⟨rfl,rfl,fun _ _ => rfl,rfl⟩
theorem frame_test (state : State) (af : Bool) : Frame state (test state af) :=
  ⟨rfl,rfl,fun _ _ => rfl,logicalFlags64_preserves ..⟩
theorem frame_clear (state : State) (destination : Register) (af : Bool)
    (notStack : destination ≠ .rsp) (allowed : destination ∈ clobbers) :
    Frame state (clear state destination af) :=
  frame_edit state destination _ _ _ notStack allowed (logicalFlags32_preserves ..)
theorem frame_add (state : State) (value : Word) : Frame state (add state value) :=
  frame_edit state .rax _ _ _ (by decide) (by decide) (addFlags64_preserves ..)
theorem frame_increment (state : State) : Frame state (increment state) :=
  frame_edit state .rcx _ _ _ (by decide) (by decide) (incFlags64_preserves ..)
theorem frame_compareIndex (state : State) : Frame state (compareIndex state) :=
  ⟨rfl,rfl,fun _ _ => rfl,cmpFlags64_preserves ..⟩

theorem frame_positive (initial : State) (af : Bool) : Frame initial (positiveState initial af) :=
  (frame_test initial af).trans (frame_atPC _ _)
theorem frame_index (initial : State) (testAF indexAF : Bool) :
    Frame initial (indexState initial testAF indexAF) :=
  (frame_positive ..).trans (frame_clear _ .rcx _ (by decide) (by decide))
theorem frame_initialized (initial : State) (testAF indexAF resultAF : Bool) :
    Frame initial (initializedState initial testAF indexAF resultAF) :=
  (frame_index ..).trans (frame_clear _ .rax _ (by decide) (by decide))
theorem frame_empty (initial : State) (af : Bool) : Frame initial (emptyState initial af) :=
  (frame_test initial af).trans (frame_atPC _ _)
theorem frame_emptyReturn (initial : State) (testAF resultAF : Bool) :
    Frame initial (emptyReturn initial testAF resultAF) :=
  (frame_empty ..).trans (frame_clear _ .rax _ (by decide) (by decide))

theorem frame_advanced (state : State) (value : Word) : Frame state (advanced state value) :=
  (frame_add ..).trans (frame_increment _)
theorem frame_testedIndex (state : State) (value : Word) : Frame state (testedIndex state value) :=
  (frame_advanced ..).trans (frame_compareIndex _)
theorem frame_cycle (base : Word) (state : State) (value : Word) (rest : List Word) :
    Frame state (cycleState base state value rest) :=
  (frame_testedIndex ..).trans (frame_atPC _ _)

/-- Current suffix and index, unchanged RAM, and the independent natural sum
modulo 2^64. The empty suffix is the actual RET at 21. No future run is assumed. -/
structure Header (initial : State) (values remaining : List Word) (consumed : Nat)
    (state : State) : Prop where
  length : consumed + remaining.length = values.length
  index : state.registers .rcx = BitVec.ofNat 64 consumed
  array : ArrayAt64 state.memory
    (initial.registers .rdi + BitVec.ofNat 64 (8 * consumed)) remaining
  correct : ((state.registers .rax).toNat + sumNat remaining) % 2^64 = sumMod values
  frame : Frame initial state
  pc : state.rip = initial.rip + BitVec.ofNat 64 (loopOffset remaining)

end EDSL.ArraySum64.Clang
