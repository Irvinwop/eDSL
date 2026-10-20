/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Corpus.V1.PopcountBodies
import EDSL.Audit

set_option autoImplicit false
set_option warningAsError true

namespace EDSL.Tests.PopcountBodies
open X86 X86.Sequential Corpus.V1.PopcountBodies

/- Only exact code and the original return slot are mapped. Dirty counters,
scratch registers and flags challenge initialization and width assumptions. -/
private def memory (code : List Byte) : Memory where
  read address :=
    if 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length then
      code[address.toNat - 0x1000]?
    else if 0x2000 ≤ address.toNat ∧ address.toNat < 0x2008 then
      ([0, 0x30, 0, 0, 0, 0, 0, 0] : List Byte)[address.toNat - 0x2000]?
    else none
  executable address := decide (0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + code.length)

private def initial (code : List Byte) (value : Word) : State where
  registers register :=
    if register = .rsp then 0x2000
    else if register = .rdi then value
    else 0xfedcba9876543210
  rip := 0x1000
  flags := 0xfedcba9876542ad7
  memory := memory code

private theorem current_code (compiler : Compiler) :
    CodeAt (memory (bytes compiler)) 0x1000 (bytes compiler) := by
  have finite : ∀ index : Fin (bytes compiler).length,
      (match fetchByte (memory (bytes compiler)) (0x1000 + BitVec.ofNat 64 index.val) with
      | .ok observed => observed == (bytes compiler)[index]
      | .error _ => false) = true := by
    cases compiler <;> decide +kernel
  refine ⟨by cases compiler <;> decide +kernel, ?_⟩
  intro offset byte present
  obtain ⟨inside, same⟩ := List.getElem?_eq_some_iff.mp present
  have checked := finite ⟨offset, inside⟩
  change (match fetchByte (memory (bytes compiler)) (0x1000 + BitVec.ofNat 64 offset) with
    | .ok observed => observed == (bytes compiler)[offset]
    | .error _ => false) = true at checked
  rw [same] at checked
  cases fetched : fetchByte (memory (bytes compiler)) (0x1000 + BitVec.ofNat 64 offset) with
  | error fault => simp only [fetched, Bool.false_eq_true] at checked
  | ok observed =>
    simp only [fetched] at checked
    exact congrArg Except.ok (beq_iff_eq.mp checked)

/-- Construct actual current entries for every full64 word. In particular,
the corner executions below cannot hide behind an unsatisfied domain. -/
theorem all_full64_admitted (compiler : Compiler) (value : Word) :
    PureCall.Pre spec (bytes compiler) ⟨value, 0x3000⟩ (initial (bytes compiler) value) := by
  constructor
  · trivial
  · apply (Arithmetic64.populationCount_bound_iff value _).mpr
    rfl
  · exact current_code compiler
  · change readWord (memory (bytes compiler)) 0x2000 = .ok 0x3000
    cases compiler <;> rfl
  · change canonical (0x3000 : Word) = true
    decide +kernel
  · change (0x2000 : Word).toNat + 8 < 2^64
    decide +kernel
  · change canonical ((0x2000 : Word) + 8) = true
    decide +kernel

private theorem literal_result (compiler : Compiler) (value : Word) (expected : Nat)
    (mathematics : WordMath.cardinality value = expected) (choices : Choices) :
    ∃ result, Sequential.Executes choices (initial (bytes compiler) value) result ∧
      ((result.state.registers .rax).setWidth 32).toNat = expected ∧
      result.state.rip = 0x3000 ∧ result.state.registers .rsp = 0x2008 := by
  have claimed := (semantics compiler).machine ⟨value, 0x3000⟩
    (initial (bytes compiler) value) (all_full64_admitted compiler value)
  obtain ⟨result, actual, post⟩ := claimed.1 choices
  change PureCall.Post spec ⟨value, 0x3000⟩ (initial (bytes compiler) value) result.state at post
  have scalar := post.result
  change ((result.state.registers .rax).setWidth 32).toNat = WordMath.cardinality value at scalar
  exact ⟨result, actual, scalar.trans mathematics, post.returnAddress, post.stackPointer⟩

/-- Empty, highest-bit-only and all-set inputs give independently literal
answers through actual executions, for either compiler and every AF stream. -/
theorem full64_corners (compiler : Compiler) (choices : Choices) :
    (∃ result, Sequential.Executes choices (initial (bytes compiler) 0) result ∧
      ((result.state.registers .rax).setWidth 32).toNat = 0 ∧
      result.state.rip = 0x3000 ∧ result.state.registers .rsp = 0x2008) ∧
    (∃ result, Sequential.Executes choices (initial (bytes compiler) 0x8000000000000000) result ∧
      ((result.state.registers .rax).setWidth 32).toNat = 1 ∧
      result.state.rip = 0x3000 ∧ result.state.registers .rsp = 0x2008) ∧
    (∃ result, Sequential.Executes choices (initial (bytes compiler) 0xffffffffffffffff) result ∧
      ((result.state.registers .rax).setWidth 32).toNat = 64 ∧
      result.state.rip = 0x3000 ∧ result.state.registers .rsp = 0x2008) := by
  refine ⟨literal_result compiler 0 0 (WordMath.cardinality_zero 64) choices,
    literal_result compiler 0x8000000000000000 1 ?_ choices,
    literal_result compiler 0xffffffffffffffff 64 ?_ choices⟩
  · decide +kernel
  · change WordMath.cardinality (BitVec.allOnes 64) = 64
    exact WordMath.cardinality_allOnes 64

/-- Correct decoding and zero initialization do not invent a RET result when
the current original return slot has no readable backing. -/
theorem missing_return_slot (compiler : Compiler) (af : Bool) :
    Sequential.run (fun _ => af) 12
      { initial (bytes compiler) 0 with
        memory := { memory (bytes compiler) with
          read := fun address =>
            if address.toNat < 0x2000 then (memory (bytes compiler)).read address
            else none } } = .error (.inaccessibleStack 0x2000) := by
  cases compiler <;> cases af <;> rfl

end EDSL.Tests.PopcountBodies

#print axioms EDSL.Tests.PopcountBodies.full64_corners
#print axioms EDSL.Tests.PopcountBodies.missing_return_slot
#audit_edsl
