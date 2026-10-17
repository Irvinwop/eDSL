/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.ArrayMaximum64.Contract
import EDSL.X86.Sequential.Code

set_option warningAsError true

namespace EDSL.ArrayMaximum64.GCC
open X86 X86.Sequential

/-- The complete final-linked GCC13 text, including the actual RET. -/
def bytes : List Byte := [0x31,0xd2,0x31,0xc0,0x48,0x39,0xf2,0x74,0x10,
  0x48,0x8b,0x0c,0xd7,0x48,0x39,0xc8,0x48,0x0f,0x42,0xc1,
  0x48,0xff,0xc2,0xeb,0xeb,0xc3]

inductive Node where
  | clearIndex | clearValue | header | guard | load | compare | select | increment | back | ret
  deriving DecidableEq, Repr

def offset : Node → Nat
  | .clearIndex => 0 | .clearValue => 2 | .header => 4 | .guard => 7
  | .load => 9 | .compare => 13 | .select => 16 | .increment => 20 | .back => 23 | .ret => 25

def instruction : Node → Sequential.Instruction
  | .clearIndex => .xorSelf32 .rdx
  | .clearValue => .xorSelf32 .rax
  | .header => .cmp64 .rdx .rsi
  | .guard => .je 16
  | .load => .loadMem64 .rcx (.indexed .rdi .rdx 3)
  | .compare => .cmp64 .rax .rcx
  | .select => .cmovReg64 .below .rax .rcx
  | .increment => .inc64 .rdx
  | .back => .jmp 235
  | .ret => .legacy .ret

theorem inside (node : Node) : offset node < bytes.length := by cases node <;> decide

theorem static_decode (node : Node) :
    Sequential.decodeAt (codeState bytes (offset node)) = .ok (instruction node) := by
  cases node <;> rfl

/-- Every actual decode is transported from the literal window to CURRENT RAM. -/
theorem decode {state : State} {base : Word} (code : CodeAt state.memory base bytes)
    (node : Node) (pc : state.rip = base + BitVec.ofNat 64 (offset node)) :
    Sequential.decodeAt state = .ok (instruction node) :=
  decodeAt_transport
    (code_fetch_transport code (by decide) (offset node) (inside node) state rfl pc)
    (static_decode node)

theorem readOnly (node : Node) : CFG.readOnly (instruction node) = true := by
  cases node <;> rfl

/-- State framing before RET, including the complete permission-bearing RAM. -/
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
    flags := cmpFlags64 state.flags (state.registers .rdx) (state.registers .rsi) }

def load (state : State) (value : Word) : State :=
  edit state .rcx value (state.rip + 4) state.flags

def compare (state : State) : State :=
  { state with
    rip := state.rip + 3
    flags := cmpFlags64 state.flags (state.registers .rax) (state.registers .rcx) }

def select (state : State) : State :=
  edit state .rax (if Condition.holds .below state.flags then state.registers .rcx
    else state.registers .rax) (state.rip + 4) state.flags

def increment (state : State) : State :=
  edit state .rdx (state.registers .rdx + 1) (state.rip + 3)
    (incFlags64 state.flags (state.registers .rdx))

def body (base : Word) (state : State) : State := atPC (test state) (base + 9)
def loaded (base : Word) (state : State) (value : Word) : State := load (body base state) value
def compared (base : Word) (state : State) (value : Word) : State := compare (loaded base state value)
def selected (base : Word) (state : State) (value : Word) : State := select (compared base state value)
def advanced (base : Word) (state : State) (value : Word) : State := increment (selected base state value)
def cycle (base : Word) (state : State) (value : Word) : State := atPC (advanced base state value) (base + 4)
def exiting (base : Word) (state : State) : State := atPC (test state) (base + 25)
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

theorem frame_loaded (base : Word) (state : State) (value : Word) : Frame state (loaded base state value) :=
  (frame_body base state).trans (frame_edit _ .rcx value _ _ (by decide) (by decide) rfl)

theorem frame_compared (base : Word) (state : State) (value : Word) : Frame state (compared base state value) :=
  (frame_loaded base state value).trans ⟨rfl,rfl,fun _ _ => rfl,cmpFlags64_preserves ..⟩

theorem frame_selected (base : Word) (state : State) (value : Word) : Frame state (selected base state value) :=
  (frame_compared base state value).trans (frame_edit _ .rax _ _ _ (by decide) (by decide) rfl)

theorem frame_advanced (base : Word) (state : State) (value : Word) : Frame state (advanced base state value) :=
  (frame_selected base state value).trans
    (frame_edit _ .rdx _ _ _ (by decide) (by decide) (incFlags64_preserves ..))

theorem frame_cycle (base : Word) (state : State) (value : Word) : Frame state (cycle base state value) :=
  (frame_advanced base state value).trans (frame_atPC _ _)

theorem frame_exiting (base : Word) (state : State) : Frame state (exiting base state) :=
  (frame_test state).trans (frame_atPC _ _)

theorem execute_clear (state : State) (destination : Register) (af : Bool) :
    execute state (.xorSelf32 destination) af = .ok ⟨.next (clear state destination af),[]⟩ := rfl

theorem execute_test (state : State) (af : Bool) :
    execute state (instruction .header) af = .ok ⟨.next (test state),[]⟩ := rfl

theorem execute_compare (state : State) (af : Bool) :
    execute state (instruction .compare) af = .ok ⟨.next (compare state),[]⟩ := rfl

theorem execute_select (state : State) (af : Bool) :
    execute state (instruction .select) af = .ok ⟨.next (select state),[]⟩ := rfl

theorem execute_increment (state : State) (af : Bool) :
    execute state (instruction .increment) af = .ok ⟨.next (increment state),[]⟩ := rfl

theorem execute_load {state : State} {value : Word}
    (read : loadQWord state.memory ((Address.indexed .rdi .rdx 3).eval state) = .ok value)
    (af : Bool) : execute state (instruction .load) af =
      .ok ⟨.next (load state value),[⟨.data,(Address.indexed .rdi .rdx 3).eval state,8⟩]⟩ := by
  simp only [instruction,execute_loadMem64,read,ok_bind,pure_ok]
  rfl

theorem guard_exit {state : State} {base : Word} (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 7) (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 25)),[]⟩ := by
  have canonicalExit : canonical (base + 25) = true := code_canonical_offset code 25 (by decide)
  have displacement : (7 : Word) + 2 + (16 : Byte).signExtend 64 = 25 := by decide
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
    (pc : state.rip = base + 23) (af : Bool) :
    execute state (instruction .back) af = .ok ⟨.next (atPC state (base + 4)),[]⟩ := by
  have canonicalHeader : canonical (base + 4) = true := code_canonical_offset code 4 (by decide)
  have displacement : (23 : Word) + 2 + (235 : Byte).signExtend 64 = 4 := by decide
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

/-- The full64 conditional move implements unsigned natural maximum. -/
theorem selected_value (base : Word) (state : State) (value : Word) :
    (selected base state value).registers .rax = selectMaximum (state.registers .rax) value := by
  simp only [selected,select,compared,compare,Condition.cmp_below,loaded,load,body,
    atPC,test,edit,State.writeRegister,reduceCtorEq,ite_true,ite_false,decide_eq_true_eq]
  rfl

theorem cycle_value (base : Word) (state : State) (value : Word) :
    (cycle base state value).registers .rax = selectMaximum (state.registers .rax) value := by
  simpa only [cycle,atPC,advanced,increment,edit,State.writeRegister,reduceCtorEq,ite_false]
    using selected_value base state value

end EDSL.ArrayMaximum64.GCC
