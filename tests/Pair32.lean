/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Pair32.Correctness
import EDSL.X86.CodeCheck
import EDSL.Audit

namespace EDSL.Tests.Pair32
open X86
set_option maxRecDepth 100000

-- A wraps to 1; B wraps to 10. Unequal lengths expose a lost B counter or
-- an accidental reuse of the A counter when entering the second loop.
def valuesA (present : Bool) : List (BitVec 32) :=
  if present then [0xffffffff, 2] else []

def valuesB (present : Bool) : List (BitVec 32) :=
  if present then [0xfffffffe, 5, 7] else []

def memory : Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + EDSL.Pair32.bytes.length then
      EDSL.Pair32.bytes[address.toNat - 4096]?
    else if 12288 ≤ address.toNat ∧ address.toNat < 12296 then
      [0xff, 0xff, 0xff, 0xff, 2, 0, 0, 0][address.toNat - 12288]?
    else if 16384 ≤ address.toNat ∧ address.toNat < 16396 then
      [0xfe, 0xff, 0xff, 0xff, 5, 0, 0, 0, 7, 0, 0, 0][address.toNat - 16384]?
    else if 32768 ≤ address.toNat ∧ address.toNat < 32776 then
      [0, 0x20, 0, 0, 0, 0, 0, 0][address.toNat - 32768]?
    else none
  executable address := decide (4096 ≤ address.toNat ∧
    address.toNat < 4096 + EDSL.Pair32.bytes.length)

def initial (a b : Bool) (pointerA : Word := 12288) (pointerB : Word := 16384) : State where
  registers register := match register with
    | .rax => 0xfedcba9876543210
    | .rsi => BitVec.ofNat 64 (valuesA a).length
    | .rdi => pointerA
    | .rcx => BitVec.ofNat 64 (valuesB b).length
    | .rdx => pointerB
    | .rsp => 32768
    | .rbx => 0x1111222233334444
    | .rbp => 0x5555666677778888
    | .r8 => 0x8888888888888888
    | .r9 => 0x9999999999999999
    | .r10 => 0xaaaaaaaaaaaaaaaa
    | .r11 => 0xbbbbbbbbbbbbbbbb
    | .r12 => 0xcccccccccccccccc
    | .r13 => 0xdddddddddddddddd
    | .r14 => 0xeeeeeeeeeeeeeeee
    | .r15 => 0xffffffffffffffff
  rip := 4096
  flags := 0x602
  memory := memory

theorem code : CodeAt memory 4096 EDSL.Pair32.bytes :=
  checkCode_sound _ _ _ (by decide)

-- Exhibit current RAM for every combination, including the B array even
-- while phase A is active. No theorem below relies on an impossible Pre.
theorem admitted (a b : Bool) :
    EDSL.Pair32.Pre EDSL.Pair32.bytes (initial a b) (valuesA a) (valuesB b) 8192 := by
  refine ⟨code, ?_, ?_, ?_, ?_, rfl, rfl, ?_, by decide, ?_⟩
  · intro index value present
    cases a with
    | false => simp [valuesA] at present
    | true =>
      match index with
      | 0 | 1 => simp [valuesA] at present; subst value; rfl
      | index + 2 => simp [valuesA] at present
  · intro index value present
    cases b with
    | false => simp [valuesB] at present
    | true =>
      match index with
      | 0 | 1 | 2 => simp [valuesB] at present; subst value; rfl
      | index + 3 => simp [valuesB] at present
  · change (12288 : Word).toNat + 4 * (valuesA a).length ≤ 2^64
    cases a <;> decide
  · change (16384 : Word).toNat + 4 * (valuesB b).length ≤ 2^64
    cases b <;> decide
  · change readWord memory 32768 = .ok 8192
    rfl
  · change canonical ((32768 : Word) + 8) = true
    decide

theorem unused_pointers_admitted (pointerA pointerB : Word) :
    EDSL.Pair32.Pre EDSL.Pair32.bytes (initial false false pointerA pointerB) [] [] 8192 := by
  refine ⟨code, ArrayAt.nil _ _, ArrayAt.nil _ _, ?_, ?_, rfl, rfl, ?_, by decide, ?_⟩
  · change pointerA.toNat + 0 ≤ 2^64
    exact Nat.le_of_lt pointerA.isLt
  · change pointerB.toNat + 0 ≤ 2^64
    exact Nat.le_of_lt pointerB.isLt
  · change readWord memory 32768 = .ok 8192
    rfl
  · change canonical ((32768 : Word) + 8) = true
    decide

theorem first_unused_admitted (pointerA : Word) :
    EDSL.Pair32.Pre EDSL.Pair32.bytes (initial false true pointerA) [] (valuesB true) 8192 := by
  have pre := admitted false true
  refine ⟨code, ArrayAt.nil _ _, pre.arrayB, ?_, pre.boundB, rfl, rfl, ?_, by decide, ?_⟩
  · change pointerA.toNat + 0 ≤ 2^64
    exact Nat.le_of_lt pointerA.isLt
  · change readWord memory 32768 = .ok 8192
    rfl
  · change canonical ((32768 : Word) + 8) = true
    decide

theorem second_unused_admitted (pointerB : Word) :
    EDSL.Pair32.Pre EDSL.Pair32.bytes (initial true false 12288 pointerB) (valuesA true) [] 8192 := by
  have pre := admitted true false
  refine ⟨code, pre.arrayA, ArrayAt.nil _ _, pre.boundA, ?_, rfl, rfl, ?_, by decide, ?_⟩
  · change pointerB.toNat + 0 ≤ 2^64
    exact Nat.le_of_lt pointerB.isLt
  · change readWord memory 32768 = .ok 8192
    rfl
  · change canonical ((32768 : Word) + 8) = true
    decide

-- Full immutable aliasing needs no disjoint-input assumption: both views
-- describe the same two current words, and the answer must count them twice.
def aliased : State :=
  { initial true false with registers := fun register =>
      if register = .rdx then 12288 else if register = .rcx then 2
      else (initial true false).registers register }

theorem alias_admitted :
    EDSL.Pair32.Pre EDSL.Pair32.bytes aliased (valuesA true) (valuesA true) 8192 := by
  have pre := admitted true false
  exact ⟨code, pre.arrayA, pre.arrayA, pre.boundA, pre.boundA, rfl, rfl,
    rfl, by decide, by decide⟩

def expectedValue (a b : Bool) : Word :=
  match a, b with
  | false, false => 0
  | true, false => 1
  | false, true => 10
  | true, true => 11

def expectedInstructions (a b : Bool) : Nat :=
  match a, b with
  | false, false => 6
  | true, false => 18
  | false, true => 24
  | true, true => 36

def expectedReads (a b : Bool) : List Sequential.Read :=
  (if a then [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩] else []) ++
    (if b then [⟨.data, 16384, 4⟩, ⟨.data, 16388, 4⟩, ⟨.data, 16392, 4⟩] else []) ++
    [⟨.stack, 32768, 8⟩]

-- Closed answers, literal operand lists and independently counted costs are
-- required for EVERY AF stream, rather than one evaluator flag assignment.
theorem all_choices (a b : Bool) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices (expectedInstructions a b) (initial a b) = .ok result ∧
      result.state.registers .rax = expectedValue a b ∧ result.state.rip = 8192 ∧
      result.state.registers .rsp = 32776 ∧ result.state.memory = memory ∧
      result.state.flags &&& ~~~arithmeticFlagMask = (0x602 : Word) &&& ~~~arithmeticFlagMask ∧
      (∀ register ∈ [.rbx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15],
        result.state.registers register = (initial a b).registers register) ∧
      result.instructions = expectedInstructions a b ∧ result.reads = expectedReads a b := by
  obtain ⟨result, execution, post, cost, reads⟩ := EDSL.Pair32.exact_executes (admitted a b) choices
  have exactCost : result.instructions = expectedInstructions a b := by
    cases a <;> cases b <;> exact cost
  refine ⟨result, Sequential.run_complete execution (Nat.le_of_eq exactCost), ?_,
    post.returnAddress, post.stackPointer, post.memory, post.flags, ?_, exactCost, ?_⟩
  · cases a <;> cases b <;> exact post.value
  · intro register member
    apply post.preserved register
    cases register <;> simp_all [EDSL.Pair32.clobbers]
  · cases a <;> cases b <;> exact reads

theorem unused_pointers_all_choices (pointerA pointerB : Word) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 6 (initial false false pointerA pointerB) = .ok result ∧
      result.state.registers .rax = 0 ∧ result.instructions = 6 ∧
      result.reads = [⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, success, post, cost, reads⟩ :=
    EDSL.Pair32.exact_sound (unused_pointers_admitted pointerA pointerB) choices
  exact ⟨result, success, post.value, cost, reads⟩

theorem first_unused_all_choices (pointerA : Word) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 24 (initial false true pointerA) = .ok result ∧
      result.state.registers .rax = 10 ∧ result.instructions = 24 ∧
      result.reads = [⟨.data, 16384, 4⟩, ⟨.data, 16388, 4⟩, ⟨.data, 16392, 4⟩,
        ⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, success, post, cost, reads⟩ :=
    EDSL.Pair32.exact_sound (first_unused_admitted pointerA) choices
  exact ⟨result, success, post.value, cost, reads⟩

theorem second_unused_all_choices (pointerB : Word) (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 18 (initial true false 12288 pointerB) = .ok result ∧
      result.state.registers .rax = 1 ∧ result.instructions = 18 ∧
      result.reads = [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩, ⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, success, post, cost, reads⟩ :=
    EDSL.Pair32.exact_sound (second_unused_admitted pointerB) choices
  exact ⟨result, success, post.value, cost, reads⟩

theorem alias_all_choices (choices : Sequential.Choices) :
    ∃ result, Sequential.run choices 30 aliased = .ok result ∧
      result.state.registers .rax = 2 ∧ result.state.memory = memory ∧
      result.instructions = 30 ∧
      result.reads = [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩, ⟨.data, 12288, 4⟩,
        ⟨.data, 12292, 4⟩, ⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, success, post, cost, reads⟩ := EDSL.Pair32.exact_sound alias_admitted choices
  exact ⟨result, success, post.value, post.memory, cost, reads⟩

-- The claimed exact cost must denote actual retirement, not just a loose
-- bound: one fewer unit of evaluator fuel cannot already return.
theorem one_short_all_choices (a b : Bool) (choices : Sequential.Choices) :
    Sequential.run choices (expectedInstructions a b - 1) (initial a b) =
      .error .exhaustedFuel := by
  obtain ⟨result, execution, _, cost, _⟩ := EDSL.Pair32.exact_executes (admitted a b) choices
  apply Sequential.Executes.exhausted execution
  cases a <;> cases b <;> simp_all [expectedInstructions, valuesA, valuesB]

def observe (choices : Sequential.Choices) (fuel : Nat) (state : State) :
    Option (Word × Word × Word × Word × Nat × List Sequential.Read) := do
  let result ← (Sequential.run choices fuel state).toOption
  return (result.state.registers .rax, result.state.flags, result.state.rip,
    result.state.registers .rsp, result.instructions, result.reads)

-- These literal answers and operand addresses come from the mathematical
-- inputs, not from the proof's accounting functions or modeled loop states.
example : observe (fun _ => false) 6 (initial false false 0x800000000000 0xffffffffffffffff) =
    some (0, 0x646, 8192, 32776, 6, [⟨.stack, 32768, 8⟩]) := by rfl

example : observe (fun _ => false) 18 (initial true false 12288 0xffffffffffffffff) =
    some (1, 0x646, 8192, 32776, 18,
      [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩, ⟨.stack, 32768, 8⟩]) := by rfl

example : observe (fun _ => false) 24 (initial false true 0x800000000000 16384) =
    some (10, 0x646, 8192, 32776, 24,
      [⟨.data, 16384, 4⟩, ⟨.data, 16388, 4⟩, ⟨.data, 16392, 4⟩,
       ⟨.stack, 32768, 8⟩]) := by rfl

example : observe (fun _ => false) 36 (initial true true) =
    some (11, 0x646, 8192, 32776, 36,
      [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩, ⟨.data, 16384, 4⟩,
       ⟨.data, 16388, 4⟩, ⟨.data, 16392, 4⟩, ⟨.stack, 32768, 8⟩]) := by rfl

example : observe (fun _ => false) 30 aliased =
    some (2, 0x646, 8192, 32776, 30,
      [⟨.data, 12288, 4⟩, ⟨.data, 12292, 4⟩, ⟨.data, 12288, 4⟩,
       ⟨.data, 12292, 4⟩, ⟨.stack, 32768, 8⟩]) := by rfl

-- The caller-saved registers outside the actual instruction destinations
-- matter too. Different sentinels catch clobbering and register mixups.
def observeFrame (a b : Bool) : Option (Memory × List Word) := do
  let result ← (Sequential.run (fun _ => false) 36 (initial a b)).toOption
  return (result.state.memory,
    [.rbx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].map result.state.registers)

example (a b : Bool) : observeFrame a b = some (memory,
    [0x1111222233334444, 0x5555666677778888, 0x8888888888888888, 0x9999999999999999,
     0xaaaaaaaaaaaaaaaa, 0xbbbbbbbbbbbbbbbb, 0xcccccccccccccccc, 0xdddddddddddddddd,
     0xeeeeeeeeeeeeeeee, 0xffffffffffffffff]) := by
  cases a <;> cases b <;> rfl

-- Count dynamic instructions from the raw CFG: XOR, two A guards, six
-- instructions per consumed word, two B guards, RET. The last TEST is at
-- indices 3,15,21,33. JE and RET retire after it without replacing AF.
example : (observe (fun index => decide (index = 3)) 6 (initial false false)).map
    (fun result => result.2.1) = some 0x656 := by rfl

example : (observe (fun index => decide (index = 15)) 18 (initial true false)).map
    (fun result => result.2.1) = some 0x656 := by rfl

example : (observe (fun index => decide (index = 21)) 24 (initial false true)).map
    (fun result => result.2.1) = some 0x656 := by rfl

example : (observe (fun index => decide (index = 33)) 36 (initial true true)).map
    (fun result => result.2.1) = some 0x656 := by rfl

-- Adjacent choices must not be mistaken for TEST's choice: these catch
-- missing or double stream drops across either backedge or the A/B handoff.
example : (observe (fun index => decide (index = 32 ∨ index = 34)) 36 (initial true true)).map
    (fun result => result.2.1) = some 0x646 := by rfl

-- Changing currently needed B bytes must invalidate the original contract,
-- even though code, A, counts and the saved return slot still agree.
def missingB : State :=
  { initial true true with memory :=
      { memory with read := fun address => if address = 16388 then none else memory.read address } }

example : ¬EDSL.Pair32.Pre EDSL.Pair32.bytes missingB (valuesA true) (valuesB true) 8192 := by
  intro pre
  have current := pre.arrayB 1 5 rfl
  change (.error (.inaccessibleData 16388) : Except Error (BitVec 32)) = .ok 5 at current
  cases current

def staleB : State :=
  { initial true true with memory :=
      { memory with read := fun address => if address = 16388 then some 6 else memory.read address } }

example : ¬EDSL.Pair32.Pre EDSL.Pair32.bytes staleB (valuesA true) (valuesB true) 8192 := by
  intro pre
  have current := pre.arrayB 1 5 rfl
  change (.ok 6 : Except Error (BitVec 32)) = .ok 5 at current
  cases current

-- Counts are full 64-bit arguments, even when their low 32 bits match a
-- valid list length. A truncated argument check would accept either state.
def highA : State :=
  { initial true true with registers := fun register =>
      if register = .rsi then 0x100000002 else (initial true true).registers register }

example : ¬EDSL.Pair32.Pre EDSL.Pair32.bytes highA (valuesA true) (valuesB true) 8192 := by
  intro pre
  have count := pre.countA
  change (0x100000002 : Word) = 2 at count
  cases count

def highB : State :=
  { initial true true with registers := fun register =>
      if register = .rcx then 0x100000003 else (initial true true).registers register }

example : ¬EDSL.Pair32.Pre EDSL.Pair32.bytes highB (valuesA true) (valuesB true) 8192 := by
  intro pre
  have count := pre.countB
  change (0x100000003 : Word) = 3 at count
  cases count

end EDSL.Tests.Pair32

#audit_edsl
