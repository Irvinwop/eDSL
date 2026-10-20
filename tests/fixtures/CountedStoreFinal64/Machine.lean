/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.CountedStore64.GCC

set_option warningAsError true

namespace EDSL.CountedStoreFinal64
open EDSL X86 X86.Sequential

/-- The complete owned final-store fixture. Positive counts perform the
register loop before publishing its final value; zero skips the store. -/
def bytes : List Byte := [0x48, 0x89, 0xf0, 0x48, 0x85, 0xd2, 0x74, 0x0b,
  0x48, 0xff, 0xc0, 0x48, 0xff, 0xca, 0x75, 0xf8, 0x48, 0x89, 0x07, 0xc3]

inductive Node where
  | entry | test | guard | increment | decrement | back | store | ret
  deriving DecidableEq, Repr

def offset : Node → Nat
  | .entry => 0 | .test => 3 | .guard => 6 | .increment => 8
  | .decrement => 11 | .back => 14 | .store => 16 | .ret => 19

def instruction : Node → Sequential.Instruction
  | .entry => .movReg64 .rax .rsi
  | .test => .test64 .rdx .rdx
  | .guard => .je 11
  | .increment => .inc64 .rax
  | .decrement => .dec64 .rdx
  | .back => .legacy (.jnz 248)
  | .store => .storeMem64 (.base .rdi) .rax
  | .ret => .legacy .ret

def isCut : Node → Bool
  | .entry | .increment => true
  | _ => false

def depth : Node → Nat
  | .entry => 3 | .test => 2 | .guard => 1 | .increment => 4
  | .decrement => 3 | .back => 2 | .store => 1 | .ret => 0

inductive Edge : Node → Node → Prop where
  | entry : Edge .entry .test
  | test : Edge .test .guard
  | body : Edge .guard .increment
  | exit : Edge .guard .ret
  | increment : Edge .increment .decrement
  | decrement : Edge .decrement .back
  | back : Edge .back .increment
  | finish : Edge .back .store
  | store : Edge .store .ret

/-- Actual machine successors connect the initial guard, register-only loop,
single final STORE and caller RET. -/
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

/-- Literal decoding is checked against the exact candidate bytes. -/
theorem static_decode (node : Node) :
    Sequential.decodeAt (codeState bytes (offset node)) = .ok (instruction node) := by
  cases node <;> rfl

/-- Current literal code, rather than an annotation, determines each decode. -/
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

abbrev atPC := CountedStore64.GCC.atPC
abbrev move := CountedStore64.GCC.move
abbrev test := CountedStore64.GCC.test
abbrev increment := CountedStore64.GCC.increment
abbrev decrement := CountedStore64.GCC.decrement
abbrev store := CountedStore64.GCC.store
abbrev finish := CountedStore64.GCC.finish

theorem execute_move (state : State) (af : Bool) :
    execute state (instruction .entry) af = .ok ⟨.next (move state), []⟩ :=
  CountedStore64.GCC.execute_move state af

theorem execute_test (state : State) (af : Bool) :
    execute state (instruction .test) af = .ok ⟨.next (test state af), []⟩ :=
  CountedStore64.GCC.execute_test state af

theorem execute_increment (state : State) (af : Bool) :
    execute state (instruction .increment) af = .ok ⟨.next (increment state), []⟩ :=
  CountedStore64.GCC.execute_increment state af

theorem execute_decrement (state : State) (af : Bool) :
    execute state (instruction .decrement) af = .ok ⟨.next (decrement state), []⟩ :=
  CountedStore64.GCC.execute_decrement state af

theorem store_intent (state : State) :
    (instruction .store).storeIntent64 state = some (state.registers .rdi, state.registers .rax) := rfl

theorem execute_store (state : State) (af : Bool)
    (allowed : canStoreQWord state.memory (state.registers .rdi) = true) :
    execute state (instruction .store) af = .ok ⟨.next (store state), []⟩ :=
  CountedStore64.GCC.execute_store state af allowed

theorem tested_zero (state : State) (af : Bool) :
    (test state af).flags.getLsbD 6 = (state.registers .rdx == 0) :=
  CountedStore64.GCC.tested_zero state af

/-- The conditional back edge tests the complete already-decremented RDX. -/
theorem decremented_zero (state : State) :
    (decrement state).flags.getLsbD 6 = ((decrement state).registers .rdx == 0) := by
  simpa only [CountedStore64.GCC.decrement, State.writeRegister, ite_true] using
    (decFlags64_bits state.flags (state.registers .rdx)).2.2.2.1

theorem guard_exit {state : State} {base : Word}
    (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 6) (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 19)), []⟩ := by
  have canonicalExit : canonical (base + 19) = true := code_canonical_offset code 19 (by decide)
  have displacement : (6 : Word) + 2 + (11 : Byte).signExtend 64 = 19 := by decide
  rw [instruction, execute_je, zero]
  simp only [executeShortBranch, ite_true, pc, BitVec.add_assoc, displacement,
    canonicalExit, ok_bind, pure_ok, CountedStore64.GCC.atPC]

theorem guard_body {state : State} {base : Word}
    (pc : state.rip = base + 6) (nonzero : state.flags.getLsbD 6 = false) (af : Bool) :
    execute state (instruction .guard) af = .ok ⟨.next (atPC state (base + 8)), []⟩ :=
  CountedStore64.GCC.guard_body pc nonzero af

theorem back_taken {state : State} {base : Word}
    (code : CodeAt state.memory base bytes)
    (pc : state.rip = base + 14) (nonzero : state.flags.getLsbD 6 = false) (af : Bool) :
    execute state (instruction .back) af = .ok ⟨.next (atPC state (base + 8)), []⟩ := by
  have canonicalBody : canonical (base + 8) = true := code_canonical_offset code 8 (by decide)
  have displacement : (14 : Word) + 2 + (248 : Byte).signExtend 64 = 8 := by decide
  simp only [instruction, execute, X86.executeInstruction, X86.executeJnz,
    executeShortBranch, nonzero, Bool.not_false, ite_true, pc, BitVec.add_assoc,
    displacement, canonicalBody, ok_bind, pure_ok, Instruction.operandReads, CountedStore64.GCC.atPC]

/-- The completed positive loop falls through to the one final STORE. -/
theorem back_exit {state : State} {base : Word}
    (pc : state.rip = base + 14) (zero : state.flags.getLsbD 6 = true) (af : Bool) :
    execute state (instruction .back) af = .ok ⟨.next (atPC state (base + 16)), []⟩ := by
  have displacement : (14 : Word) + 2 = 16 := by decide
  simp only [instruction, execute, X86.executeInstruction, X86.executeJnz,
    executeShortBranch, zero, Bool.not_true, Bool.false_eq_true, ite_false, pc,
    BitVec.add_assoc, displacement, ok_bind, pure_ok, Instruction.operandReads, CountedStore64.GCC.atPC]

theorem execute_ret {state : State} {target : Word}
    (loaded : readWord state.memory (state.registers .rsp) = .ok target)
    (canonicalTarget : canonical target = true) (af : Bool) :
    execute state (instruction .ret) af =
      .ok ⟨.returned (finish state target), [⟨.stack, state.registers .rsp, 8⟩]⟩ :=
  CountedStore64.GCC.execute_ret loaded canonicalTarget af

end EDSL.CountedStoreFinal64
