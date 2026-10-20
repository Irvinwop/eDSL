/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArrayMaximum64.Contract
import EDSL.X86.Sequential.ShortBranch

set_option warningAsError true

namespace EDSL.ArrayMaximum64.Clang
open X86 X86.Sequential

/-- Complete final linked Clang 18 text, including both return paths. -/
def bytes : List Byte := [0x48,0x85,0xf6,0x74,0x18,0x31,0xc9,0x31,0xc0,
  0x48,0x8b,0x14,0xcf,0x48,0x39,0xc2,0x48,0x0f,0x47,0xc2,0x48,0xff,
  0xc1,0x48,0x39,0xce,0x75,0xed,0xc3,0x31,0xc0,0xc3]

def graph : CFG.Graph := ⟨[
  ⟨0,.test64 .rsi .rsi,true,13⟩,
  ⟨3,.je 24,false,12⟩,
  ⟨5,.xorSelf32 .rcx,false,11⟩,
  ⟨7,.xorSelf32 .rax,false,10⟩,
  ⟨9,.loadMem64 .rdx (.indexed .rdi .rcx 3),true,9⟩,
  ⟨13,.cmp64 .rdx .rax,false,8⟩,
  ⟨16,.cmovReg64 .above .rax .rdx,false,7⟩,
  ⟨20,.inc64 .rcx,false,6⟩,
  ⟨23,.cmp64 .rsi .rcx,false,5⟩,
  ⟨26,.legacy (.jnz 237),false,4⟩,
  ⟨28,.legacy .ret,false,3⟩,
  ⟨29,.xorSelf32 .rax,false,2⟩,
  ⟨31,.legacy .ret,false,1⟩],32⟩

theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide)

abbrev Index := graph.Index

instance : NeZero graph.nodes.length := ⟨by decide⟩

/-- The pre-RET frame includes all RAM and permission maps, the original RSP,
all registers outside the shared clobber set, and every nonarithmetic flag. -/
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

def load (state : State) (value : Word) : State :=
  edit state .rdx value (state.rip + 4) state.flags

def compareValue (state : State) : State :=
  { state with
    rip := state.rip + 3
    flags := cmpFlags64 state.flags (state.registers .rdx) (state.registers .rax) }

def select (state : State) : State :=
  edit state .rax (if Condition.holds .above state.flags then state.registers .rdx
    else state.registers .rax) (state.rip + 4) state.flags

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

def emptyState (initial : State) (af : Bool) : State := atPC (test initial af) (initial.rip + 29)
def emptyReturn (initial : State) (testAF resultAF : Bool) : State :=
  clear (emptyState initial testAF) .rax resultAF

def compared (state : State) (value : Word) : State := compareValue (load state value)
def selected (state : State) (value : Word) : State := select (compared state value)
def advanced (state : State) (value : Word) : State := increment (selected state value)
def testedIndex (state : State) (value : Word) : State := compareIndex (advanced state value)

def loopOffset (remaining : List Word) : Nat := if remaining.isEmpty then 28 else 9

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
theorem frame_load (state : State) (value : Word) : Frame state (load state value) :=
  frame_edit state .rdx _ _ _ (by decide) (by decide) rfl
theorem frame_compareValue (state : State) : Frame state (compareValue state) :=
  ⟨rfl,rfl,fun _ _ => rfl,cmpFlags64_preserves ..⟩
theorem frame_select (state : State) : Frame state (select state) :=
  frame_edit state .rax _ _ _ (by decide) (by decide) rfl
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

theorem frame_compared (state : State) (value : Word) : Frame state (compared state value) :=
  (frame_load ..).trans (frame_compareValue _)
theorem frame_selected (state : State) (value : Word) : Frame state (selected state value) :=
  (frame_compared ..).trans (frame_select _)
theorem frame_advanced (state : State) (value : Word) : Frame state (advanced state value) :=
  (frame_selected ..).trans (frame_increment _)
theorem frame_testedIndex (state : State) (value : Word) : Frame state (testedIndex state value) :=
  (frame_advanced ..).trans (frame_compareIndex _)
theorem frame_cycle (base : Word) (state : State) (value : Word) (rest : List Word) :
    Frame state (cycleState base state value rest) :=
  (frame_testedIndex ..).trans (frame_atPC _ _)

/-- Current suffix, index, full memory and a mathematical maximum equation.
An empty suffix denotes the actual RET at 28, without another loop test. -/
structure Header (initial : State) (values remaining : List Word) (consumed : Nat)
    (state : State) : Prop where
  length : consumed + remaining.length = values.length
  index : state.registers .rcx = BitVec.ofNat 64 consumed
  array : ArrayAt64 state.memory
    (initial.registers .rdi + BitVec.ofNat 64 (8 * consumed)) remaining
  correct : maximumFrom (state.registers .rax).toNat remaining = maximumNat values
  frame : Frame initial state
  pc : state.rip = initial.rip + BitVec.ofNat 64 (loopOffset remaining)

end EDSL.ArrayMaximum64.Clang
