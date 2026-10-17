/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArraySum64.Contract
import EDSL.X86.Sequential.ShortBranch

set_option warningAsError true

namespace EDSL.ArraySum64.GCC
open X86 X86.Sequential

/-- Complete final-linked GCC13 Os text, including the result move and RET. -/
def bytes : List Byte := [0x31,0xc0,0x31,0xd2,0x48,0x39,0xf0,0x74,0x09,
  0x48,0x03,0x14,0xc7,0x48,0xff,0xc0,0xeb,0xf2,0x48,0x89,0xd0,0xc3]

/-- All nine decoded instructions; only entry and the loop header are cutpoints. -/
def graph : CFG.Graph := ⟨[
  ⟨0,.xorSelf32 .rax,true,9⟩,
  ⟨2,.xorSelf32 .rdx,false,8⟩,
  ⟨4,.cmp64 .rax .rsi,true,7⟩,
  ⟨7,.je 9,false,6⟩,
  ⟨9,.addMem64 .rdx (.indexed .rdi .rax 3),false,5⟩,
  ⟨13,.inc64 .rax,false,4⟩,
  ⟨16,.jmp 242,false,3⟩,
  ⟨18,.movReg64 .rax .rdx,false,2⟩,
  ⟨21,.legacy .ret,false,1⟩],9⟩

theorem valid : CFG.Valid bytes graph := CFG.check_sound (by decide)

inductive Node where
  | clearIndex | clearValue | header | guard | add | increment | back | move | ret
  deriving DecidableEq, Repr

def offset : Node → Nat
  | .clearIndex => 0 | .clearValue => 2 | .header => 4 | .guard => 7
  | .add => 9 | .increment => 13 | .back => 16 | .move => 18 | .ret => 21

def instruction : Node → Sequential.Instruction
  | .clearIndex => .xorSelf32 .rax
  | .clearValue => .xorSelf32 .rdx
  | .header => .cmp64 .rax .rsi
  | .guard => .je 9
  | .add => .addMem64 .rdx (.indexed .rdi .rax 3)
  | .increment => .inc64 .rax
  | .back => .jmp 242
  | .move => .movReg64 .rax .rdx
  | .ret => .legacy .ret

theorem inside (node : Node) : offset node < bytes.length := by cases node <;> decide

theorem static_decode (node : Node) :
    Sequential.decodeAt (codeState bytes (offset node)) = .ok (instruction node) := by
  cases node <;> rfl

/-- Decode the actual current RAM, transporting only the checked literal window. -/
theorem decode {state : State} {base : Word} (code : CodeAt state.memory base bytes)
    (node : Node) (pc : state.rip = base + BitVec.ofNat 64 (offset node)) :
    Sequential.decodeAt state = .ok (instruction node) :=
  decodeAt_transport
    (code_fetch_transport code (by decide) (offset node) (inside node) state rfl pc)
    (static_decode node)

theorem readOnly (node : Node) : CFG.readOnly (instruction node) = true := by
  cases node <;> rfl

/-- Pre-RET preservation of complete permission-bearing RAM, the original
caller slot, every register outside the task clobbers, and nonarithmetic flags. -/
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

theorem Frame.code {initial final : State} (frame : Frame initial final)
    (code : CodeAt initial.memory initial.rip bytes) : CodeAt final.memory initial.rip bytes := by
  rw [frame.memory]
  exact code

def edit (state : State) (destination : Register) (value pc flags : Word) : State :=
  { state.writeRegister destination value with rip := pc, flags := flags }

def atPC (state : State) (pc : Word) : State := { state with rip := pc }

def clear (state : State) (destination : Register) (af : Bool) : State :=
  edit state destination 0 (state.rip + 2) (logicalFlags32 state.flags 0 af)

def test (state : State) : State :=
  { state with
    rip := state.rip + 3
    flags := cmpFlags64 state.flags (state.registers .rax) (state.registers .rsi) }

def addOperand (state : State) (value : Word) : State :=
  edit state .rdx (state.registers .rdx + value) (state.rip + 4)
    (addFlags64 state.flags (state.registers .rdx) value)

def increment (state : State) : State :=
  edit state .rax (state.registers .rax + 1) (state.rip + 3)
    (incFlags64 state.flags (state.registers .rax))

def moveResult (state : State) : State :=
  edit state .rax (state.registers .rdx) (state.rip + 3) state.flags

def body (base : Word) (state : State) : State := atPC (test state) (base + 9)
def added (base : Word) (state : State) (value : Word) : State := addOperand (body base state) value
def advanced (base : Word) (state : State) (value : Word) : State := increment (added base state value)
def cycle (base : Word) (state : State) (value : Word) : State := atPC (advanced base state value) (base + 4)
def exiting (base : Word) (state : State) : State := atPC (test state) (base + 18)
def moved (base : Word) (state : State) : State := moveResult (exiting base state)
def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

theorem frame_edit (state : State) (destination : Register) (value pc flags : Word)
    (notStack : destination ≠ .rsp) (allowed : destination ∈ clobbers)
    (flagFrame : flags &&& ~~~arithmeticFlagMask = state.flags &&& ~~~arithmeticFlagMask) :
    Frame state (edit state destination value pc flags) := by
  refine ⟨rfl,?_,?_,flagFrame⟩
  · simp [edit,State.writeRegister,Ne.symm notStack]
  · intro register outside
    have different : register ≠ destination := by
      intro same
      subst register
      exact outside allowed
    simp [edit,State.writeRegister,different]

theorem frame_atPC (state : State) (pc : Word) : Frame state (atPC state pc) :=
  ⟨rfl,rfl,fun _ _ => rfl,rfl⟩

theorem frame_clear (state : State) (destination : Register) (af : Bool)
    (notStack : destination ≠ .rsp) (allowed : destination ∈ clobbers) :
    Frame state (clear state destination af) :=
  frame_edit state destination 0 _ _ notStack allowed (logicalFlags32_preserves ..)

theorem frame_test (state : State) : Frame state (test state) :=
  ⟨rfl,rfl,fun _ _ => rfl,cmpFlags64_preserves ..⟩

theorem frame_body (base : Word) (state : State) : Frame state (body base state) :=
  (frame_test state).trans (frame_atPC _ _)

theorem frame_added (base : Word) (state : State) (value : Word) : Frame state (added base state value) :=
  (frame_body base state).trans
    (frame_edit _ .rdx _ _ _ (by decide) (by decide) (addFlags64_preserves ..))

theorem frame_advanced (base : Word) (state : State) (value : Word) : Frame state (advanced base state value) :=
  (frame_added base state value).trans
    (frame_edit _ .rax _ _ _ (by decide) (by decide) (incFlags64_preserves ..))

theorem frame_cycle (base : Word) (state : State) (value : Word) : Frame state (cycle base state value) :=
  (frame_advanced base state value).trans (frame_atPC _ _)

theorem frame_exiting (base : Word) (state : State) : Frame state (exiting base state) :=
  (frame_test state).trans (frame_atPC _ _)

theorem frame_moved (base : Word) (state : State) : Frame state (moved base state) :=
  (frame_exiting base state).trans
    (frame_edit _ .rax _ _ _ (by decide) (by decide) rfl)

theorem execute_clear (state : State) (destination : Register) (af : Bool) :
    execute state (.xorSelf32 destination) af = .ok ⟨.next (clear state destination af),[]⟩ := rfl

theorem execute_test (state : State) (af : Bool) :
    execute state (instruction .header) af = .ok ⟨.next (test state),[]⟩ := rfl

theorem execute_increment (state : State) (af : Bool) :
    execute state (instruction .increment) af = .ok ⟨.next (increment state),[]⟩ := rfl

theorem execute_move (state : State) (af : Bool) :
    execute state (instruction .move) af = .ok ⟨.next (moveResult state),[]⟩ := rfl

theorem execute_add {state : State} {value : Word}
    (read : loadQWord state.memory ((Address.indexed .rdi .rax 3).eval state) = .ok value)
    (af : Bool) : execute state (instruction .add) af =
      .ok ⟨.next (addOperand state value),[⟨.data,(Address.indexed .rdi .rax 3).eval state,8⟩]⟩ := by
  simp only [instruction,execute_addMem64,read,ok_bind,pure_ok]
  rfl

theorem guard_exit {state : State} {base : Word} (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 7) (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 18)),[]⟩ := by
  have canonicalExit : canonical (base + 18) = true := code_canonical_offset code 18 (by decide)
  have displacement : (7 : Word) + 2 + (9 : Byte).signExtend 64 = 18 := by decide
  rw [instruction,execute_je,zero]
  simp only [executeShortBranch,ite_true,pc,BitVec.add_assoc,displacement,
    canonicalExit,ok_bind,pure_ok,atPC]

theorem guard_body {state : State} {base : Word}
    (pc : state.rip = base + 7) (nonzero : state.flags.getLsbD 6 = false) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 9)),[]⟩ := by
  have displacement : (7 : Word) + 2 = 9 := by decide
  rw [instruction,execute_je,nonzero]
  simp only [executeShortBranch,Bool.false_eq_true,ite_false,pc,BitVec.add_assoc,
    displacement,ok_bind,pure_ok,atPC]

theorem back_edge {state : State} {base : Word} (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 16) (af : Bool) :
    execute state (instruction .back) af = .ok ⟨.next (atPC state (base + 4)),[]⟩ := by
  have canonicalHeader : canonical (base + 4) = true := code_canonical_offset code 4 (by decide)
  have displacement : (16 : Word) + 2 + (242 : Byte).signExtend 64 = 4 := by decide
  rw [instruction,execute_jmp]
  simp only [executeShortBranch,ite_true,pc,BitVec.add_assoc,displacement,
    canonicalHeader,ok_bind,pure_ok,atPC]

theorem execute_ret {state : State} {target : Word}
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (af : Bool) :
    execute state (instruction .ret) af =
      .ok ⟨.returned (finish state target),[⟨.stack,state.registers .rsp,8⟩]⟩ := by
  simp only [instruction,execute,X86.executeInstruction,X86.executeRet,loaded,
    canonicalTarget,ite_true,ok_bind,pure_ok,Instruction.operandReads,finish]

theorem cycle_value (base : Word) (state : State) (value : Word) :
    (cycle base state value).registers .rdx = state.registers .rdx + value := rfl

end EDSL.ArraySum64.GCC
