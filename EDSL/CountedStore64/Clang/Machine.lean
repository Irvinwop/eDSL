/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.GCC

set_option warningAsError true

namespace EDSL.CountedStore64.Clang
open EDSL X86 X86.Sequential

/-- One exact Clang counted-store window. The bytes are the verification
input; this definition does not assert preservation from a source program. -/
def bytes : List Byte := [0x48, 0x89, 0xf0, 0x48, 0x85, 0xd2, 0x74, 0x0b,
  0x48, 0xff, 0xc0, 0x48, 0x89, 0x07, 0x48, 0xff, 0xca, 0x75, 0xf5, 0xc3]

inductive Node where
  | entry | test | guard | increment | store | decrement | back | ret
  deriving DecidableEq, Repr

def offset : Node → Nat
  | .entry => 0 | .test => 3 | .guard => 6 | .increment => 8
  | .store => 11 | .decrement => 14 | .back => 17 | .ret => 19

def instruction : Node → Sequential.Instruction
  | .entry => .movReg64 .rax .rsi
  | .test => .test64 .rdx .rdx
  | .guard => .je 11
  | .increment => .inc64 .rax
  | .store => .storeMem64 (.base .rdi) .rax
  | .decrement => .dec64 .rdx
  | .back => .legacy (.jnz 245)
  | .ret => .legacy .ret

def isCut : Node → Bool
  | .entry | .increment => true
  | _ => false

def depth : Node → Nat
  | .entry => 3 | .test => 2 | .guard => 1 | .increment => 4
  | .store => 3 | .decrement => 2 | .back => 1 | .ret => 0

inductive Edge : Node → Node → Prop where
  | entry : Edge .entry .test
  | test : Edge .test .guard
  | body : Edge .guard .increment
  | exit : Edge .guard .ret
  | increment : Edge .increment .store
  | store : Edge .store .decrement
  | decrement : Edge .decrement .back
  | back : Edge .back .increment
  | finish : Edge .back .ret

/-- The loop cutpoint is INC: the conditional back edge does not repeat the
initial TEST. Actual STORE successors remain explicit proof obligations. -/
def flow : Cutpoints.Layout Node where
  cutpoint := isCut
  depth := depth
  maxDepth := 4
  Edge := Edge
  depth_bound node := by cases node <;> decide
  depth_decrease edge notCut := by cases edge <;> simp_all [isCut, depth]

theorem inside (node : Node) : offset node < bytes.length := by cases node <;> decide

theorem span (node : Node) : offset node + (instruction node).length ≤ bytes.length := by
  cases node <;> decide

theorem static_decode (node : Node) :
    Sequential.decodeAt (codeState bytes (offset node)) = .ok (instruction node) := by
  cases node <;> rfl

/-- Current code bytes determine the instruction, independently of annotations. -/
theorem decode {state : State} {base : Word}
    (code : CodeAt state.memory base bytes) (node : Node)
    (pc : state.rip = base + BitVec.ofNat 64 (offset node)) :
    Sequential.decodeAt state = .ok (instruction node) :=
  decodeAt_transport
    (code_fetch_transport code (by decide) (offset node) (inside node) state rfl pc)
    (static_decode node)

theorem fetch_at {state : State} {base : Word}
    (code : CodeAt state.memory base bytes) (node : Node)
    (pc : state.rip = base + BitVec.ofNat 64 (offset node)) :
    OS.Borrowing.Subregion ⟨state.rip, (instruction node).length⟩ ⟨base, bytes.length⟩ :=
  code_fetch_span code state (instruction node) (offset node) pc (span node)

abbrev atPC := GCC.atPC
abbrev move := GCC.move
abbrev test := GCC.test
abbrev increment := GCC.increment
abbrev decrement := GCC.decrement
abbrev store := GCC.store
abbrev finish := GCC.finish

theorem execute_move (state : State) (af : Bool) :
    execute state (instruction .entry) af = .ok ⟨.next (move state), []⟩ :=
  GCC.execute_move state af

theorem execute_test (state : State) (af : Bool) :
    execute state (instruction .test) af = .ok ⟨.next (test state af), []⟩ :=
  GCC.execute_test state af

theorem execute_increment (state : State) (af : Bool) :
    execute state (instruction .increment) af = .ok ⟨.next (increment state), []⟩ :=
  GCC.execute_increment state af

theorem execute_decrement (state : State) (af : Bool) :
    execute state (instruction .decrement) af = .ok ⟨.next (decrement state), []⟩ :=
  GCC.execute_decrement state af

theorem store_intent (state : State) :
    (instruction .store).storeIntent64 state = some (state.registers .rdi, state.registers .rax) := rfl

theorem execute_store (state : State) (af : Bool)
    (allowed : canStoreQWord state.memory (state.registers .rdi) = true) :
    execute state (instruction .store) af = .ok ⟨.next (store state), []⟩ :=
  GCC.execute_store state af allowed

theorem tested_zero (state : State) (af : Bool) :
    (test state af).flags.getLsbD 6 = (state.registers .rdx == 0) :=
  GCC.tested_zero state af

/-- DEC's ZF describes the full counter already present in its successor.
The following JNZ does not inspect the entry TEST's flags or a low32 count. -/
theorem decremented_zero (state : State) :
    (decrement state).flags.getLsbD 6 = ((decrement state).registers .rdx == 0) := by
  simpa only [GCC.decrement, State.writeRegister, ite_true] using
    (decFlags64_bits state.flags (state.registers .rdx)).2.2.2.1

theorem guard_exit {state : State} {base : Word}
    (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 6) (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 19)), []⟩ := by
  have canonicalExit : canonical (base + 19) = true := code_canonical_offset code 19 (by decide)
  have displacement : (6 : Word) + 2 + (11 : Byte).signExtend 64 = 19 := by decide
  rw [instruction, execute_je, zero]
  simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement,
    canonicalExit, ok_bind, pure_ok, GCC.atPC]

theorem guard_body {state : State} {base : Word}
    (pc : state.rip = base + 6) (nonzero : state.flags.getLsbD 6 = false) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 8)), []⟩ :=
  GCC.guard_body pc nonzero af

/-- The signed JNZ displacement is measured from offset 19 and targets INC
at offset 8. Only the taken target needs a branch canonicality check. -/
theorem back_taken {state : State} {base : Word}
    (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 17) (nonzero : state.flags.getLsbD 6 = false) (af : Bool) :
    execute state (instruction .back) af = .ok ⟨.next (atPC state (base + 8)), []⟩ := by
  have canonicalBody : canonical (base + 8) = true := code_canonical_offset code 8 (by decide)
  have displacement : (17 : Word) + 2 + (245 : Byte).signExtend 64 = 8 := by decide
  simp only [instruction, execute, X86.executeInstruction, X86.executeJnz,
    executeShortBranch, nonzero, Bool.not_false, ite_true, pc, BitVec.add_assoc,
    displacement, canonicalBody, ok_bind, pure_ok, Instruction.operandReads, GCC.atPC]

theorem back_exit {state : State} {base : Word}
    (pc : state.rip = base + 17) (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .back) af = .ok ⟨.next (atPC state (base + 19)), []⟩ := by
  have displacement : (17 : Word) + 2 = 19 := by decide
  simp only [instruction, execute, X86.executeInstruction, X86.executeJnz,
    executeShortBranch, zero, Bool.not_true, Bool.false_eq_true, ite_false, pc,
    BitVec.add_assoc, displacement, ok_bind, pure_ok, Instruction.operandReads, GCC.atPC]

theorem execute_ret {state : State} {target : Word}
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (af : Bool) :
    execute state (instruction .ret) af =
      .ok ⟨.returned (finish state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  GCC.execute_ret loaded canonicalTarget af

end EDSL.CountedStore64.Clang
