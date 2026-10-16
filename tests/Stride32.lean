/-
Copyright 2026 Irvinwop
SPDX-License-Identifier: Apache-2.0
-/
import EDSL.Stride32.Correctness
import EDSL.X86.CodeCheck
import EDSL.Audit

namespace EDSL.Tests.Stride32
open X86
set_option maxRecDepth 100000

-- Two different odd-word payloads accompany even words 0xffffffff and 2.
-- Nothing beyond the full sixteen-byte array is mapped.
def data (alternate : Bool) : List Byte :=
  [0xff, 0xff, 0xff, 0xff] ++
  (if alternate then [0, 0, 0, 0] else [0xef, 0xbe, 0xad, 0xde]) ++
  [2, 0, 0, 0] ++
  (if alternate then [0xff, 0xff, 0xff, 0xff] else [1, 0, 0, 0])

def values (alternate : Bool) : List (BitVec 32) :=
  [0xffffffff, if alternate then 0 else 0xdeadbeef, 2, if alternate then 0xffffffff else 1]

def memory (alternate : Bool) : Memory where
  read address :=
    if 4096 ≤ address.toNat ∧ address.toNat < 4096 + EDSL.Stride32.bytes.length then
      EDSL.Stride32.bytes[address.toNat - 4096]?
    else if 12288 ≤ address.toNat ∧ address.toNat < 12304 then
      (data alternate)[address.toNat - 12288]?
    else if 32768 ≤ address.toNat ∧ address.toNat < 32776 then
      [0, 0x20, 0, 0, 0, 0, 0, 0][address.toNat - 32768]?
    else none
  executable address := decide (4096 ≤ address.toNat ∧
    address.toNat < 4096 + EDSL.Stride32.bytes.length)

def initial (alternate : Bool) (pointer : Word) (count : Nat) : State where
  registers register := match register with
    | .rsi => BitVec.ofNat 64 count
    | .rdi => pointer
    | .rsp => 32768
    | _ => 0xfedcba9876543210
  rip := 4096
  flags := 0x602
  memory := memory alternate

theorem code (alternate : Bool) : CodeAt (memory alternate) 4096 EDSL.Stride32.bytes :=
  checkCode_sound _ _ _ (by cases alternate <;> decide)

-- The actual current memory is exhibited, so the universal theorem below
-- cannot pass merely because its input contract is contradictory.
theorem admitted (alternate : Bool) :
    EDSL.Stride32.Pre EDSL.Stride32.bytes (initial alternate 12288 2) (values alternate) 2 8192 := by
  refine ⟨code alternate, ?_, ?_, by cases alternate <;> rfl, rfl, ?_, by decide, ?_⟩
  · intro index value present
    match index with
    | 0 | 1 | 2 | 3 => simp [values] at present; subst value; cases alternate <;> rfl
    | index + 4 => simp [values] at present
  · change (12288 : Word).toNat + 4 * (values alternate).length ≤ 2^64
    cases alternate <;> decide
  · change readWord (memory alternate) 32768 = .ok 8192
    cases alternate <;> rfl
  · change canonical ((32768 : Word) + 8) = true
    decide

-- Independent expected result: 0xffffffff + 2 wraps to 1. Both choices of
-- ignored odd words and EVERY undefined-AF stream satisfy the same result.
theorem wrapping_all_choices (alternate : Bool) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices (initial alternate 12288 2) result ∧
      result.state.registers .rax = 1 ∧ result.state.rip = 8192 ∧
      result.state.registers .rsp = 32776 ∧ result.state.memory = memory alternate ∧
      result.state.registers .r15 = 0xfedcba9876543210 ∧ result.instructions = 16 ∧
      result.reads = [⟨.data, 12288, 4⟩, ⟨.data, 12296, 4⟩, ⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, execution, post, cost, reads⟩ := EDSL.Stride32.exact_executes (admitted alternate) choices
  refine ⟨result, execution, ?_, post.returnAddress, post.stackPointer, post.memory,
    post.preserved .r15 (by decide), cost, reads⟩
  cases alternate <;> exact post.value

theorem empty_admitted (pointer : Word) :
    EDSL.Stride32.Pre EDSL.Stride32.bytes (initial false pointer 0) [] 0 8192 := by
  refine ⟨code false, ArrayAt.nil _ _, OS.ArrayResources.arrayBound_nil pointer, rfl, rfl, ?_,
    by decide, ?_⟩
  · change readWord (memory false) 32768 = .ok 8192
    rfl
  · change canonical ((32768 : Word) + 8) = true
    decide

-- No input canonicality or readability is required when the count is zero.
theorem empty_all_choices (pointer : Word) (choices : Sequential.Choices) :
    ∃ result, Sequential.Executes choices (initial false pointer 0) result ∧
      result.state.registers .rax = 0 ∧ result.state.rip = 8192 ∧ result.instructions = 4 ∧
      result.reads = [⟨.stack, 32768, 8⟩] := by
  obtain ⟨result, execution, post, cost, reads⟩ := EDSL.Stride32.exact_executes (empty_admitted pointer) choices
  exact ⟨result, execution, post.value, post.returnAddress, cost, reads⟩

def observe (choices : Sequential.Choices) (fuel : Nat) (state : State) :
    Option (Word × Word × Word × Nat × List Sequential.Read) := do
  let result ← (Sequential.run choices fuel state).toOption
  return (result.state.registers .rax, result.state.flags, result.state.rip,
    result.instructions, result.reads)

-- TEST at dynamic instruction 13 supplies the final AF, after two six-step
-- bodies. The independently listed reads skip BOTH odd words and one-past.
example (alternate : Bool) :
    observe (fun index => decide (index = 13)) 16 (initial alternate 12288 2) =
      some (1, 0x656, 8192, 16,
        [⟨.data, 12288, 4⟩, ⟨.data, 12296, 4⟩, ⟨.stack, 32768, 8⟩]) := by
  cases alternate <;> rfl

example : observe (fun _ => false) 4 (initial false 0x800000000000 0) =
    some (0, 0x646, 8192, 4, [⟨.stack, 32768, 8⟩]) := by rfl

-- Changing a currently read even word invalidates the original precondition;
-- exact code equality alone must not certify stale data.
def missingEven : State :=
  { initial false 12288 2 with memory :=
    { memory false with read := fun address => if address = 12296 then none else (memory false).read address } }

example : ¬EDSL.Stride32.Pre EDSL.Stride32.bytes missingEven (values false) 2 8192 := by
  intro pre
  have current := pre.array 2 2 rfl
  change (.error (.inaccessibleData 12296) : Except Error (BitVec 32)) = .ok 2 at current
  cases current

end EDSL.Tests.Stride32

#audit_edsl
