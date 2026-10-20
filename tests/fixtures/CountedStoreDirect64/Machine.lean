/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Frame

set_option warningAsError true

namespace EDSL.CountedStoreDirect64
open EDSL X86 X86.Sequential

inductive Variant where
  | gcc | clang
  deriving DecidableEq, Repr

/-- Complete owned compiler windows; source preservation is not assumed. -/
def bytes : Variant → List Byte
  | .gcc => [0x48,0x8d,0x04,0x16,0x48,0x85,0xd2,0x74,0x03,0x48,0x89,0x07,0xc3]
  | .clang => [0x48,0x89,0xf0,0x48,0x01,0xd0,0x48,0x85,0xd2,0x74,0x03,0x48,0x89,0x07,0xc3]

/-- Both compiler windows share the suffix after computing RAX. -/
inductive Stage where
  | test | guard | store | ret
  deriving DecidableEq, Repr

def testOffset : Variant → Nat | .gcc => 4 | .clang => 6
def prefixCost : Variant → Nat | .gcc => 1 | .clang => 2
def offset (variant : Variant) : Stage → Nat
  | .test => testOffset variant | .guard => testOffset variant + 3
  | .store => testOffset variant + 5 | .ret => testOffset variant + 8

def instruction : Stage → Sequential.Instruction
  | .test => .test64 .rdx .rdx
  | .guard => .je 3
  | .store => .storeMem64 (.base .rdi) .rax
  | .ret => .legacy .ret

def entryInstruction : Variant → Sequential.Instruction
  | .gcc => .lea64 .rax (.indexed .rsi .rdx 0)
  | .clang => .movReg64 .rax .rsi

def cost (variant : Variant) (count : Word) : Nat :=
  prefixCost variant + if count = 0 then 3 else 4

theorem inside (variant : Variant) (stage : Stage) : offset variant stage < (bytes variant).length := by
  cases variant <;> cases stage <;> decide

theorem span (variant : Variant) (stage : Stage) :
    offset variant stage + (instruction stage).length ≤ (bytes variant).length := by
  cases variant <;> cases stage <;> decide

theorem static_decode (variant : Variant) (stage : Stage) :
    Sequential.decodeAt (codeState (bytes variant) (offset variant stage)) = .ok (instruction stage) := by
  cases variant <;> cases stage <;> rfl

theorem static_entry (variant : Variant) :
    Sequential.decodeAt (codeState (bytes variant) 0) = .ok (entryInstruction variant) := by
  cases variant <;> rfl

theorem decode {variant : Variant} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes variant)) (stage : Stage)
    (pc : state.rip = base + BitVec.ofNat 64 (offset variant stage)) :
    Sequential.decodeAt state = .ok (instruction stage) :=
  decodeAt_transport (code_fetch_transport code (by cases variant <;> decide)
    (offset variant stage) (inside variant stage) state rfl pc) (static_decode variant stage)

theorem decode_entry {variant : Variant} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes variant)) (pc : state.rip = base) :
    Sequential.decodeAt state = .ok (entryInstruction variant) :=
  decodeAt_transport (code_fetch_transport code (by cases variant <;> decide)
    0 (by cases variant <;> decide) state rfl (by simpa using pc)) (static_entry variant)

theorem decode_add {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes .clang)) (pc : state.rip = base + 3) :
    Sequential.decodeAt state = .ok (.addReg64 .rax .rdx) :=
  decodeAt_transport (code_fetch_transport code (by decide) 3 (by decide) state rfl pc) rfl

theorem fetch_at {variant : Variant} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes variant)) (stage : Stage)
    (pc : state.rip = base + BitVec.ofNat 64 (offset variant stage)) :
    OS.Borrowing.Subregion ⟨state.rip,(instruction stage).length⟩ ⟨base,(bytes variant).length⟩ :=
  code_fetch_span code state (instruction stage) (offset variant stage) pc (span variant stage)

theorem fetch_entry {variant : Variant} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes variant)) (pc : state.rip = base) :
    OS.Borrowing.Subregion ⟨state.rip,(entryInstruction variant).length⟩ ⟨base,(bytes variant).length⟩ :=
  code_fetch_span code state (entryInstruction variant) 0
    (by simpa using pc) (by cases variant <;> decide)

theorem fetch_add {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes .clang)) (pc : state.rip = base + 3) :
    OS.Borrowing.Subregion ⟨state.rip,3⟩ ⟨base,(bytes .clang).length⟩ :=
  code_fetch_span code state (.addReg64 .rax .rdx) 3 pc (by decide)

abbrev atPC := CountedStore64.GCC.atPC
abbrev move := CountedStore64.GCC.move
abbrev test := CountedStore64.GCC.test
abbrev store := CountedStore64.GCC.store
abbrev finish := CountedStore64.GCC.finish

def lea (state : State) : State :=
  { state.writeRegister .rax (state.registers .rsi + state.registers .rdx) with rip := state.rip + 4 }

def add (state : State) : State :=
  { state.writeRegister .rax (state.registers .rax + state.registers .rdx) with
    rip := state.rip + 3, flags := addFlags64 state.flags (state.registers .rax) (state.registers .rdx) }

def ready (variant : Variant) (initial : State) : State :=
  match variant with | .gcc => lea initial | .clang => add (move initial)

def guard (variant : Variant) (initial : State) (af : Bool) : State := test (ready variant initial) af
def atStore (variant : Variant) (initial : State) (af : Bool) : State :=
  atPC (guard variant initial af) (initial.rip + BitVec.ofNat 64 (offset variant .store))
def atRet (variant : Variant) (initial : State) (af : Bool) : State :=
  atPC (guard variant initial af) (initial.rip + BitVec.ofNat 64 (offset variant .ret))
def beforeReturn (variant : Variant) (initial : State) (af : Bool) : State :=
  if initial.registers .rdx = 0 then atRet variant initial af else store (atStore variant initial af)
def finalState (variant : Variant) (initial : State) (target : Word) (af : Bool) : State :=
  finish (beforeReturn variant initial af) target

theorem ready_memory (variant : Variant) (initial : State) :
    (ready variant initial).memory = initial.memory := by cases variant <;> rfl

theorem ready_count (variant : Variant) (initial : State) :
    (ready variant initial).registers .rdx = initial.registers .rdx := by
  cases variant <;> simp [ready,lea,add,CountedStore64.GCC.move,State.writeRegister]

theorem ready_pc (variant : Variant) (initial : State) :
    (ready variant initial).rip = initial.rip + BitVec.ofNat 64 (offset variant .test) := by
  cases variant <;> simp only [ready,lea,add,CountedStore64.GCC.move,offset,testOffset,BitVec.add_assoc] <;> rfl

theorem guard_pc (variant : Variant) (initial : State) (af : Bool) :
    (guard variant initial af).rip = initial.rip + BitVec.ofNat 64 (offset variant .guard) := by
  cases variant <;> simp only [guard,ready,lea,add,CountedStore64.GCC.move,
    CountedStore64.GCC.test,offset,testOffset,BitVec.add_assoc] <;> rfl

theorem stored_pc (variant : Variant) (initial : State) (af : Bool) :
    (store (atStore variant initial af)).rip = initial.rip + BitVec.ofNat 64 (offset variant .ret) := by
  cases variant <;> simp only [atStore,CountedStore64.GCC.atPC,CountedStore64.GCC.store,
    offset,testOffset,BitVec.add_assoc] <;> rfl

theorem execute_lea (state : State) (af : Bool) :
    execute state (entryInstruction .gcc) af = .ok ⟨.next (lea state),[]⟩ := by
  have operand : (Address.indexed .rsi .rdx 0).eval state = state.registers .rsi + state.registers .rdx := by
    change state.registers .rsi + (state.registers .rdx <<< (0 : Nat)) = _
    rw [BitVec.shiftLeft_zero]
  rw [entryInstruction,execute_lea64,operand]
  rfl

theorem execute_move (state : State) (af : Bool) :
    execute state (entryInstruction .clang) af = .ok ⟨.next (move state),[]⟩ :=
  CountedStore64.GCC.execute_move state af

theorem execute_add (state : State) (af : Bool) :
    execute state (.addReg64 .rax .rdx) af = .ok ⟨.next (add state),[]⟩ := rfl

theorem execute_test (state : State) (af : Bool) :
    execute state (instruction .test) af = .ok ⟨.next (test state af),[]⟩ :=
  CountedStore64.GCC.execute_test state af

theorem tested_zero (state : State) (af : Bool) :
    (test state af).flags.getLsbD 6 = (state.registers .rdx == 0) :=
  CountedStore64.GCC.tested_zero state af

theorem guard_exit {variant : Variant} {state : State} {base : Word}
    (code : CodeAt state.memory base (bytes variant))
    (pc : state.rip = base + BitVec.ofNat 64 (offset variant .guard))
    (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .guard) af =
      .ok ⟨.next (atPC state (base + BitVec.ofNat 64 (offset variant .ret))),[]⟩ := by
  have canonicalExit := code_canonical_offset code (offset variant .ret) (inside variant .ret)
  have displacement : BitVec.ofNat 64 (offset variant .guard) + 2 + (3 : Byte).signExtend 64 =
      BitVec.ofNat 64 (offset variant .ret) := by cases variant <;> decide
  rw [instruction,execute_je,zero]
  simp only [executeShortBranch,ite_true,pc,BitVec.add_assoc,displacement,canonicalExit,
    ok_bind,pure_ok,CountedStore64.GCC.atPC]

theorem guard_body {variant : Variant} {state : State} {base : Word}
    (pc : state.rip = base + BitVec.ofNat 64 (offset variant .guard))
    (nonzero : state.flags.getLsbD 6 = false) (af : Bool) :
    execute state (instruction .guard) af =
      .ok ⟨.next (atPC state (base + BitVec.ofNat 64 (offset variant .store))),[]⟩ := by
  have displacement : BitVec.ofNat 64 (offset variant .guard) + 2 =
      BitVec.ofNat 64 (offset variant .store) := by cases variant <;> decide
  rw [instruction,execute_je,nonzero]
  simp only [executeShortBranch,Bool.false_eq_true,ite_false,pc,BitVec.add_assoc,displacement,
    ok_bind,pure_ok,CountedStore64.GCC.atPC]

theorem store_intent (state : State) :
    (instruction .store).storeIntent64 state = some (state.registers .rdi,state.registers .rax) := rfl

theorem execute_store (state : State) (af : Bool)
    (allowed : canStoreQWord state.memory (state.registers .rdi) = true) :
    execute state (instruction .store) af = .ok ⟨.next (store state),[]⟩ :=
  CountedStore64.GCC.execute_store state af allowed

theorem execute_ret {state : State} {target : Word}
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (af : Bool) :
    execute state (instruction .ret) af =
      .ok ⟨.returned (finish state target),[⟨.stack,state.registers .rsp,8⟩]⟩ :=
  CountedStore64.GCC.execute_ret loaded canonicalTarget af

end EDSL.CountedStoreDirect64
