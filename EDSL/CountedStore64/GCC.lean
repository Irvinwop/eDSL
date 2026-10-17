/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.Bridges
import EDSL.X86.Sequential.Code
import EDSL.X86.Sequential.Cutpoints

set_option warningAsError true

namespace EDSL.CountedStore64.GCC
open EDSL X86 X86.Sequential

/-- Exact GCC GNU-C loop with an explicit count-register barrier. These bytes
are the verification input; no source preservation claim is made here. -/
def bytes : List Byte := [0x48, 0x89, 0xf0, 0x48, 0x85, 0xd2, 0x74, 0x0b,
  0x48, 0xff, 0xc0, 0x48, 0xff, 0xca, 0x48, 0x89, 0x07, 0xeb, 0xf0, 0xc3]

inductive Node where
  | entry | header | guard | increment | decrement | store | back | ret
  deriving DecidableEq, Repr

def offset : Node → Nat
  | .entry => 0 | .header => 3 | .guard => 6 | .increment => 8
  | .decrement => 11 | .store => 14 | .back => 17 | .ret => 19

def instruction : Node → Sequential.Instruction
  | .entry => .movReg64 .rax .rsi
  | .header => .test64 .rdx .rdx
  | .guard => .je 11
  | .increment => .inc64 .rax
  | .decrement => .dec64 .rdx
  | .store => .storeMem64 (.base .rdi) .rax
  | .back => .jmp 240
  | .ret => .legacy .ret

def isCut : Node → Bool
  | .entry | .header => true
  | _ => false

def depth : Node → Nat
  | .entry => 0 | .header => 6 | .guard => 5 | .increment => 4
  | .decrement => 3 | .store => 2 | .back => 1 | .ret => 0

inductive Edge : Node → Node → Prop where
  | entry : Edge .entry .header
  | header : Edge .header .guard
  | body : Edge .guard .increment
  | exit : Edge .guard .ret
  | increment : Edge .increment .decrement
  | decrement : Edge .decrement .store
  | store : Edge .store .back
  | back : Edge .back .header

/-- Direct layout: ordinary STORE is deliberately outside the read-only CFG
checker, and each concrete successor must be discharged by machine semantics. -/
def flow : Cutpoints.Layout Node where
  cutpoint := isCut
  depth := depth
  maxDepth := 6
  Edge := Edge
  depth_bound node := by cases node <;> decide
  depth_decrease edge notCut := by cases edge <;> simp_all [isCut, depth]

theorem inside (node : Node) : offset node < bytes.length := by cases node <;> decide

theorem span (node : Node) : offset node + (instruction node).length ≤ bytes.length := by
  cases node <;> decide

theorem static_decode (node : Node) :
    Sequential.decodeAt (codeState bytes (offset node)) = .ok (instruction node) := by
  cases node <;> rfl

/-- Actual current code bytes determine every decoded instruction. -/
theorem decode {state : State} {base : Word}
    (code : CodeAt state.memory base bytes) (node : Node)
    (pc : state.rip = base + BitVec.ofNat 64 (offset node)) :
    Sequential.decodeAt state = .ok (instruction node) :=
  decodeAt_transport
    (code_fetch_transport code (by decide) (offset node) (inside node) state rfl pc)
    (static_decode node)

/-- Every actual instruction footprint remains within the admitted code loan. -/
theorem fetch_at {state : State} {base : Word}
    (code : CodeAt state.memory base bytes) (node : Node)
    (pc : state.rip = base + BitVec.ofNat 64 (offset node)) :
    OS.Borrowing.Subregion ⟨state.rip, (instruction node).length⟩ ⟨base, bytes.length⟩ :=
  code_fetch_span code state (instruction node) (offset node) pc (span node)

def atPC (state : State) (pc : Word) : State := { state with rip := pc }

def move (state : State) : State :=
  { state.writeRegister .rax (state.registers .rsi) with rip := state.rip + 3 }

def test (state : State) (af : Bool) : State :=
  { state with
    rip := state.rip + 3
    flags := logicalFlags64 state.flags (state.registers .rdx) af }

def increment (state : State) : State :=
  { state.writeRegister .rax (state.registers .rax + 1) with
    rip := state.rip + 3, flags := incFlags64 state.flags (state.registers .rax) }

def decrement (state : State) : State :=
  { state.writeRegister .rdx (state.registers .rdx - 1) with
    rip := state.rip + 3, flags := decFlags64 state.flags (state.registers .rdx) }

/-- Raw full64 STORE successor; enabledness remains an explicit premise. -/
def store (state : State) : State :=
  { state with
    memory := writeQWordUnchecked state.memory (state.registers .rdi) (state.registers .rax)
    rip := state.rip + 3 }

def finish (state : State) (target : Word) : State :=
  { state.writeRegister .rsp (state.registers .rsp + 8) with rip := target }

theorem execute_move (state : State) (af : Bool) :
    execute state (instruction .entry) af = .ok ⟨.next (move state), []⟩ := rfl

theorem execute_test (state : State) (af : Bool) :
    execute state (instruction .header) af = .ok ⟨.next (test state af), []⟩ := by
  simp only [instruction, execute_test64, BitVec.and_self, test]

theorem execute_increment (state : State) (af : Bool) :
    execute state (instruction .increment) af = .ok ⟨.next (increment state), []⟩ := rfl

theorem execute_decrement (state : State) (af : Bool) :
    execute state (instruction .decrement) af = .ok ⟨.next (decrement state), []⟩ := rfl

theorem store_intent (state : State) :
    (instruction .store).storeIntent64 state = some (state.registers .rdi, state.registers .rax) := rfl

theorem execute_store (state : State) (af : Bool)
    (allowed : canStoreQWord state.memory (state.registers .rdi) = true) :
    execute state (instruction .store) af = .ok ⟨.next (store state), []⟩ := by
  rw [execute_storeIntent64_checked af (store_intent state)]
  simp only [allowed, ↓reduceIte]
  rfl

theorem tested_zero (state : State) (af : Bool) :
    (test state af).flags.getLsbD 6 = (state.registers .rdx == 0) :=
  logicalFlags64_zero _ _ _

theorem guard_exit {state : State} {base : Word}
    (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 6) (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 19)), []⟩ := by
  have canonicalExit : canonical (base + 19) = true := code_canonical_offset code 19 (by decide)
  have displacement : (6 : Word) + 2 + (11 : Byte).signExtend 64 = 19 := by decide
  rw [instruction, execute_je, zero]
  simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement,
    canonicalExit, ok_bind, pure_ok, atPC]

theorem guard_body {state : State} {base : Word}
    (pc : state.rip = base + 6) (nonzero : state.flags.getLsbD 6 = false) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 8)), []⟩ := by
  have displacement : (6 : Word) + 2 = 8 := by decide
  rw [instruction, execute_je, nonzero]
  simp only [executeShortBranch, Bool.false_eq_true, ite_false, pc, BitVec.add_assoc,
    displacement, ok_bind, pure_ok, atPC]

theorem back_edge {state : State} {base : Word}
    (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 17) (af : Bool) :
    execute state (instruction .back) af = .ok ⟨.next (atPC state (base + 3)), []⟩ := by
  have canonicalHeader : canonical (base + 3) = true := code_canonical_offset code 3 (by decide)
  have displacement : (17 : Word) + 2 + (240 : Byte).signExtend 64 = 3 := by decide
  rw [instruction, execute_jmp]
  simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement,
    canonicalHeader, ok_bind, pure_ok, atPC]

theorem execute_ret {state : State} {target : Word}
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (af : Bool) :
    execute state (instruction .ret) af =
      .ok ⟨.returned (finish state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ := by
  simp only [instruction, execute, X86.executeInstruction, X86.executeRet,
    loaded, canonicalTarget, ite_true, ok_bind, pure_ok, Instruction.operandReads, finish]

end EDSL.CountedStore64.GCC
